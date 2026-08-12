import { timingSafeEqual } from "node:crypto";
import {
  inspectE2BVerificationProgress,
  killE2BSandbox,
  listPausedE2BVerifications,
  readE2BVerification,
} from "@/lib/e2b-verifier";
import { readQueuedE2BJobMetadata } from "@/lib/e2b-queue";
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
} from "@/lib/queue-orchestration";
import {
  getActiveVerificationJob,
  type QueuedVerificationJob,
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

function authorized(request: Request): boolean {
  const secret = process.env.CRON_SECRET;
  const supplied = request.headers.get("authorization");
  if (!secret || !supplied) return false;
  const expected = Buffer.from(`Bearer ${secret}`, "utf8");
  const actual = Buffer.from(supplied, "utf8");
  return expected.length === actual.length && timingSafeEqual(expected, actual);
}

export async function GET(request: Request): Promise<Response> {
  if (!authorized(request)) return noStore(401, { error: "unauthorized" });
  if (!isGitHubPromotionConfigured()) {
    return noStore(503, { error: "promotion_not_configured" });
  }

  let activeQueueJob: QueuedVerificationJob | null = null;
  try {
    activeQueueJob = await getActiveVerificationJob();
    const queueManaged = Boolean(activeQueueJob);
    let job;
    if (activeQueueJob) {
      const metadata = await readQueuedE2BJobMetadata(activeQueueJob.sandboxId);
      assertQueueJobMatches(activeQueueJob, metadata);
      await ensureQueuedJobRunning(activeQueueJob);
      job = metadata;
    } else {
      [job] = await listPausedE2BVerifications(1);
    }
    if (!job) return noStore(200, { status: "idle" });
    const result = await readE2BVerification(job.sandboxId, job.jobId);
    if (!result) {
      const progress = await inspectE2BVerificationProgress(
        job.sandboxId,
        job.jobId,
      );
      console.info("E2B verification result not ready", {
        jobId: job.jobId,
        sandboxId: job.sandboxId,
        ...progress,
      });
      return noStore(503, {
        error: "result_not_ready",
        submissionId: job.submissionId,
        message: "The paused sandbox remains available for a later retry.",
      });
    }
    assertE2BResultMatchesJob(job, result);
    if (result.status === "rejected") {
      const feedback = describeVerifierRejection(result.log, result.message);
      if (queueManaged) {
        await advanceVerificationQueue(job.jobId, {
          outcome: "rejected",
          promotionStatus: null,
          message: feedback.detail,
          feedback,
          evidenceUrl: null,
          completedAt: result.completedAt,
        });
      }
      await killE2BSandbox(job.sandboxId).catch(() => undefined);
      return noStore(200, {
        status: "rejected-cleaned",
        submissionId: job.submissionId,
        feedbackCode: feedback.code,
      });
    }
    try {
      const promotion = await promoteE2BResult(job, result);
      if (queueManaged) {
        await advanceVerificationQueue(job.jobId, {
          outcome: "promoted",
          promotionStatus: promotion.status,
          message: null,
          evidenceUrl: promotion.evidenceUrl,
          completedAt: result.completedAt,
        });
      }
      await killE2BSandbox(job.sandboxId).catch(() => undefined);
      return noStore(200, { status: "promoted", promotion });
    } catch (error) {
      if (error instanceof PromotionRaceError) {
        const message = describePromotionError(error);
        if (queueManaged) {
          await advanceVerificationQueue(job.jobId, {
            outcome: "superseded",
            promotionStatus: null,
            message,
            evidenceUrl: null,
            completedAt: result.completedAt,
          });
        }
        await killE2BSandbox(job.sandboxId).catch(() => undefined);
        return noStore(200, {
          status: "superseded",
          message,
        });
      }
      throw error;
    }
  } catch (error) {
    const { SandboxNotFoundError } = await import("e2b");
    if (activeQueueJob && error instanceof SandboxNotFoundError) {
      const feedback = describeVerifierRejection(
        "",
        "The isolated verifier expired before producing a result.",
      );
      await advanceVerificationQueue(activeQueueJob.jobId, {
        outcome: "rejected",
        promotionStatus: null,
        message: feedback.detail,
        feedback,
        evidenceUrl: null,
      }).catch((queueError) => {
        console.error("Unable to advance an expired queue job", queueError);
      });
      return noStore(200, { status: "expired-advanced" });
    }
    console.error("Unable to sweep a paused E2B verification", error);
    return noStore(503, {
      error: "sweep_failed",
      message: "The paused verification remains available for a later retry.",
    });
  }
}
