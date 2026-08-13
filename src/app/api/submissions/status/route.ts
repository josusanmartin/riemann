import { getSession } from "@/auth";
import {
  killE2BSandbox,
  readE2BVerification,
} from "@/lib/e2b-verifier";
import {
  describePromotionError,
  isGitHubPromotionConfigured,
  PromotionRaceError,
} from "@/lib/github-promotion";
import {
  assertE2BResultMatchesJob,
  promoteE2BResult,
} from "@/lib/submission-finalization";
import {
  advanceVerificationQueue,
  assertQueueJobMatches,
  ensureQueuedJobRunning,
  reconcileQueuedJobPause,
  VerifierOccupiedByFlowTestError,
} from "@/lib/queue-orchestration";
import { verifySubmissionJob } from "@/lib/submission-jobs";
import {
  inspectVerificationJob,
  type QueueCompletionReceipt,
} from "@/lib/submission-queue";
import { describeVerifierRejection } from "@/lib/verifier-feedback";

export const runtime = "nodejs";
export const maxDuration = 60;

function noStore(status: number, body: object): Response {
  return Response.json(body, {
    status,
    headers: { "Cache-Control": "no-store" },
  });
}

function completedReceiptResponse(
  submissionId: string,
  expectedDigest: string,
  receipt: QueueCompletionReceipt,
): Response {
  if (receipt.proofDigest !== expectedDigest) {
    throw new Error("The durable queue receipt does not match the verification job");
  }
  if (receipt.outcome === "rejected") {
    const feedback =
      receipt.feedback ??
      describeVerifierRejection(
        "",
        receipt.message ?? "The formal verifier rejected this candidate.",
      );
    return noStore(200, {
      status: "rejected",
      submissionId,
      proofDigest: receipt.proofDigest,
      completedAt: receipt.completedAt,
      message: feedback.detail,
      feedback,
    });
  }
  return noStore(200, {
    status: "verified",
    submissionId,
    proofDigest: receipt.proofDigest,
    completedAt: receipt.completedAt,
    promotion:
      receipt.outcome === "superseded"
        ? {
            status: "superseded",
            message:
              receipt.message ??
              "Another verified record landed before this result was published.",
          }
        : {
            status: receipt.promotionStatus,
            evidenceUrl: receipt.evidenceUrl,
          },
  });
}

export async function GET(request: Request): Promise<Response> {
  const session = await getSession();
  const github = session?.user.githubLogin;
  if (!github) {
    return noStore(401, {
      error: "authentication_required",
      message: "Sign in with GitHub to inspect this verification job.",
    });
  }
  const secret = process.env.AUTH_SECRET;
  if (!secret) {
    return noStore(503, { error: "job_signing_unavailable" });
  }

  const token = new URL(request.url).searchParams.get("job");
  if (!token) {
    return noStore(400, {
      error: "job_required",
      message: "A signed verification job handle is required.",
    });
  }

  try {
    const job = verifySubmissionJob(token, secret);
    if (job.github.toLowerCase() !== github.toLowerCase()) {
      return noStore(403, {
        error: "job_owner_mismatch",
        message: "This verification job belongs to another GitHub account.",
      });
    }
    const queue = await inspectVerificationJob(job.jobId);
    if (queue.status === "completed") {
      return completedReceiptResponse(
        job.submissionId,
        job.proofDigest,
        queue.receipt,
      );
    }
    if (queue.status === "queued") {
      assertQueueJobMatches(queue.job, job);
      const latest = await reconcileQueuedJobPause(queue.job).catch((error) => {
        console.error("Unable to reaffirm a queued E2B pause", error);
        return queue;
      });
      if (latest.status === "active") {
        assertQueueJobMatches(latest.job, job);
        await ensureQueuedJobRunning(latest.job);
        return noStore(200, {
          status: "running",
          submissionId: job.submissionId,
          proofDigest: job.proofDigest,
        });
      }
      if (latest.status === "completed") {
        return completedReceiptResponse(
          job.submissionId,
          job.proofDigest,
          latest.receipt,
        );
      }
      return noStore(200, {
        status: "queued",
        submissionId: job.submissionId,
        proofDigest: job.proofDigest,
        queuePosition:
          latest.status === "queued" ? latest.position : queue.position,
      });
    }
    if (queue.status === "missing") {
      return noStore(410, {
        error: "job_not_admitted",
        message:
          "This signed verifier job is not present in the durable admission queue.",
      });
    }
    assertQueueJobMatches(queue.job, job);
    try {
      await ensureQueuedJobRunning(queue.job);
    } catch (error) {
      if (error instanceof VerifierOccupiedByFlowTestError) {
        return noStore(200, {
          status: "queued",
          submissionId: job.submissionId,
          proofDigest: job.proofDigest,
          queuePosition: 0,
          message:
            "An operator smoke replay is finishing before this proof starts.",
        });
      }
      throw error;
    }
    const result = await readE2BVerification(job.sandboxId, job.jobId);
    if (!result) {
      return noStore(200, {
        status: "running",
        submissionId: job.submissionId,
        proofDigest: job.proofDigest,
      });
    }
    assertE2BResultMatchesJob(job, result);
    if (result.status === "rejected") {
      const feedback = describeVerifierRejection(result.log, result.message);
      await advanceVerificationQueue(job.jobId, {
        outcome: "rejected",
        promotionStatus: null,
        message: feedback.detail,
        feedback,
        evidenceUrl: null,
        completedAt: result.completedAt,
      });
      await killE2BSandbox(job.sandboxId).catch(() => undefined);
      return noStore(200, {
        ...result,
        message: feedback.detail,
        feedback,
      });
    }
    if (!isGitHubPromotionConfigured()) {
      return noStore(200, {
        ...result,
        promotion: {
          status: "awaiting-configuration",
          message: "The proof passed, but durable publication is not configured.",
        },
      });
    }
    try {
      const promotion = await promoteE2BResult(job, result);
      await advanceVerificationQueue(job.jobId, {
        outcome: "promoted",
        promotionStatus: promotion.status,
        message: null,
        evidenceUrl: promotion.evidenceUrl,
        completedAt: result.completedAt,
      });
      await killE2BSandbox(job.sandboxId).catch(() => undefined);
      return noStore(200, { ...result, promotion });
    } catch (error) {
      if (error instanceof PromotionRaceError) {
        const message = describePromotionError(error);
        await advanceVerificationQueue(job.jobId, {
          outcome: "superseded",
          promotionStatus: null,
          message,
          evidenceUrl: null,
          completedAt: result.completedAt,
        });
        await killE2BSandbox(job.sandboxId).catch(() => undefined);
        return noStore(200, {
          ...result,
          promotion: {
            status: "superseded",
            message,
          },
        });
      }
      throw error;
    }
  } catch (error) {
    const { SandboxNotFoundError } = await import("e2b");
    if (error instanceof SandboxNotFoundError) {
      const feedback = describeVerifierRejection(
        "",
        "The isolated verifier expired before producing a result.",
      );
      let jobId: string | null = null;
      try {
        jobId = verifySubmissionJob(token, secret).jobId;
        const queue = await inspectVerificationJob(jobId);
        if (queue.status === "active") {
          await advanceVerificationQueue(jobId, {
            outcome: "rejected",
            promotionStatus: null,
            message: feedback.detail,
            feedback,
            evidenceUrl: null,
          });
        }
      } catch (queueError) {
        console.error("Unable to advance an expired queue job", queueError);
      }
      return noStore(410, {
        error: "job_expired",
        message: feedback.detail,
        feedback,
      });
    }
    const message = error instanceof Error ? error.message : "Invalid verification job.";
    if (message.includes("token") || message.includes("signature")) {
      return noStore(400, { error: "invalid_job", message });
    }
    console.error("Unable to read E2B verification", error);
    return noStore(502, {
      error: "verifier_status_failed",
      message: "The isolated verifier status is temporarily unavailable.",
    });
  }
}
