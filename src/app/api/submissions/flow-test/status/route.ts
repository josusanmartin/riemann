import { getSession } from "@/auth";
import { compareRationals } from "@/lib/challenge";
import {
  inspectE2BVerificationProgress,
  killE2BSandbox,
  readE2BVerification,
} from "@/lib/e2b-verifier";
import {
  FLOW_TEST_BASELINE_ID,
  FLOW_TEST_SCORE,
} from "@/lib/flow-test";
import { assertE2BResultMatchesJob } from "@/lib/submission-finalization";
import { verifySubmissionJob } from "@/lib/submission-jobs";
import { describeVerifierRejection } from "@/lib/verifier-feedback";

export const runtime = "nodejs";
export const maxDuration = 60;

// The verifier process has its own 54-minute timeout. Enforce an independent
// job-age limit so a browser polling every few seconds cannot keep a stalled
// sandbox alive forever by repeatedly reconnecting to E2B.
const FLOW_TEST_OPERATIONAL_LIMIT_MS = 58 * 60 * 1_000;

function noStore(status: number, body: object): Response {
  return Response.json(body, {
    status,
    headers: { "Cache-Control": "no-store" },
  });
}

function formatElapsed(seconds: number): string {
  const wholeSeconds = Math.max(0, Math.floor(seconds));
  const minutes = Math.floor(wholeSeconds / 60);
  const remainder = wholeSeconds % 60;
  return minutes > 0 ? `${minutes}m ${remainder}s` : `${remainder}s`;
}

function progressMessage(
  progress: Awaited<ReturnType<typeof inspectE2BVerificationProgress>>,
  elapsedSeconds: number,
): { stage: string; message: string } {
  let stage = "starting";
  let detail = "The isolated verifier worker is starting.";
  if (progress.finalizerProcesses > 0 || progress.artifactBytes > 0) {
    stage = "finalizing";
    detail = "Both kernels finished; the verifier is sealing the result.";
  } else if (progress.nanodaProcesses > 0) {
    stage = "nanoda-kernel";
    detail = "Nanoda is independently replaying the exported proof.";
  } else if (progress.leanProcesses > 0) {
    stage = "lean-compilation";
    detail = "Lean is elaborating or replaying the candidate proof.";
  } else if (progress.verifierProcesses > 0 || progress.timeoutProcesses > 0) {
    stage = "comparator";
    detail = "Comparator is preparing statements, exports, or kernel checks.";
  } else if (progress.runnerLockHeld) {
    stage = "runner";
    detail = "The verifier runner is active between observable stages.";
  }

  const logSize =
    progress.logBytes > 0
      ? ` Verifier log: ${(progress.logBytes / 1_024).toFixed(1)} KB.`
      : "";
  return {
    stage,
    message: `${detail} ${formatElapsed(elapsedSeconds)} elapsed.${logSize}`,
  };
}

export async function GET(request: Request): Promise<Response> {
  const session = await getSession();
  const github = session?.user.githubLogin;
  if (!github) {
    return noStore(401, {
      error: "authentication_required",
      message: "Sign in with GitHub to inspect this flow test.",
    });
  }
  const secret = process.env.AUTH_SECRET;
  if (!secret) return noStore(503, { error: "job_signing_unavailable" });
  const token = new URL(request.url).searchParams.get("job");
  if (!token) {
    return noStore(400, {
      error: "job_required",
      message: "A signed flow-test job handle is required.",
    });
  }

  try {
    const job = verifySubmissionJob(token, secret);
    if (job.github.toLowerCase() !== github.toLowerCase()) {
      return noStore(403, {
        error: "job_owner_mismatch",
        message: "This flow test belongs to another GitHub account.",
      });
    }
    if (
      job.previousRecordId !== FLOW_TEST_BASELINE_ID ||
      !job.submissionId.startsWith("flow-test-")
    ) {
      return noStore(400, {
        error: "not_a_flow_test",
        message: "That signed handle is not a noncompetitive flow-test job.",
      });
    }

    const result = await readE2BVerification(job.sandboxId, job.jobId);
    if (!result) {
      const elapsedMs = Math.max(0, Date.now() - job.issuedAt);
      if (elapsedMs >= FLOW_TEST_OPERATIONAL_LIMIT_MS) {
        await killE2BSandbox(job.sandboxId).catch(() => undefined);
        return noStore(200, {
          status: "rejected",
          submissionId: job.submissionId,
          proofDigest: job.proofDigest,
          completedAt: new Date().toISOString(),
          log: "",
          message:
            "The flow-test worker exceeded its 58-minute operational deadline before producing a verdict.",
          feedback: {
            title: "Flow-test runtime expired",
            action:
              "This test did not produce a mathematical rejection. Send the digest to the maintainers so they can inspect verifier performance before retrying.",
            stage: "runtime",
            code: "verification-timeout",
          },
        });
      }
      const elapsedSeconds = Math.floor(elapsedMs / 1_000);
      const progress = await inspectE2BVerificationProgress(
        job.sandboxId,
        job.jobId,
      ).catch((error) => {
        console.warn("Unable to inspect flow-test verifier progress", error);
        return null;
      });
      const summary = progress
        ? progressMessage(progress, elapsedSeconds)
        : {
            stage: "running",
            message:
              "Comparator, Lean, and nanoda are replaying the test proof.",
          };
      if (progress && elapsedSeconds % 30 < 6) {
        console.info("Flow-test verifier progress", {
          proofDigest: job.proofDigest,
          stage: summary.stage,
          elapsedSeconds,
          runnerElapsedSeconds: progress.runnerElapsedSeconds,
          logBytes: progress.logBytes,
          logModifiedAtUnix: progress.logModifiedAtUnix,
          runnerLockHeld: progress.runnerLockHeld,
          leanProcesses: progress.leanProcesses,
          nanodaProcesses: progress.nanodaProcesses,
          verifierProcesses: progress.verifierProcesses,
          finalizerProcesses: progress.finalizerProcesses,
        });
      }
      return noStore(200, {
        status: "running",
        submissionId: job.submissionId,
        proofDigest: job.proofDigest,
        message: summary.message,
        progress: progress
          ? {
              stage: summary.stage,
              elapsedSeconds,
              runnerElapsedSeconds: progress.runnerElapsedSeconds,
              logBytes: progress.logBytes,
              logModifiedAtUnix: progress.logModifiedAtUnix,
            }
          : undefined,
      });
    }
    assertE2BResultMatchesJob(job, result);
    if (result.status === "rejected") {
      const feedback = describeVerifierRejection(result.log, result.message);
      await killE2BSandbox(job.sandboxId).catch(() => undefined);
      return noStore(200, {
        ...result,
        message: feedback.detail,
        feedback,
      });
    }
    if (
      result.attestation.previousRecordId !== FLOW_TEST_BASELINE_ID ||
      compareRationals(result.attestation.score, FLOW_TEST_SCORE) !== 0
    ) {
      throw new Error("The verifier returned an attestation for a different contract");
    }
    await killE2BSandbox(job.sandboxId).catch(() => undefined);
    return noStore(200, {
      ...result,
      message:
        "Flow test passed: Comparator matched all three statements, and Lean plus nanoda accepted the proof. Nothing was promoted.",
      promotion: { status: "test-only" },
    });
  } catch (error) {
    const { SandboxNotFoundError } = await import("e2b");
    if (error instanceof SandboxNotFoundError) {
      const feedback = describeVerifierRejection(
        "",
        "The flow-test sandbox expired before producing a result.",
      );
      return noStore(410, {
        error: "job_expired",
        message: feedback.detail,
        feedback,
      });
    }
    const message = error instanceof Error ? error.message : "Invalid flow-test job.";
    if (message.includes("token") || message.includes("signature")) {
      return noStore(400, { error: "invalid_job", message });
    }
    console.error("Unable to read verifier flow-test status", error);
    return noStore(502, {
      error: "flow_test_status_failed",
      message: "The isolated flow-test status is temporarily unavailable.",
    });
  }
}
