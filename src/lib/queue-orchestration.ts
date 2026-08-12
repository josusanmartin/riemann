import {
  launchQueuedE2BVerification,
  pauseQueuedE2BVerification,
} from "@/lib/e2b-queue";
import {
  completeVerificationJob,
  inspectVerificationJob,
  type QueueAdvance,
  type QueueCompletionInput,
  type QueueInspection,
  type QueuedVerificationJob,
} from "@/lib/submission-queue";
import { describeVerifierRejection } from "@/lib/verifier-feedback";

type QueueCoordinates = {
  sandboxId: string;
  jobId: string;
  proofDigest: string;
};

export function assertQueueJobMatches(
  queued: QueuedVerificationJob,
  coordinates: QueueCoordinates,
): void {
  if (
    queued.sandboxId !== coordinates.sandboxId ||
    queued.jobId !== coordinates.jobId ||
    queued.proofDigest !== coordinates.proofDigest
  ) {
    throw new Error("The durable queue entry does not match the verification job");
  }
}

export function ensureQueuedJobRunning(job: QueuedVerificationJob): Promise<void> {
  return launchQueuedE2BVerification(job);
}

export function ensureQueuedJobPaused(job: QueuedVerificationJob): Promise<void> {
  return pauseQueuedE2BVerification(job.sandboxId);
}

export async function reconcileQueuedJobPause(
  job: QueuedVerificationJob,
): Promise<QueueInspection> {
  await ensureQueuedJobPaused(job);
  const latest = await inspectVerificationJob(job.jobId);
  if (latest.status === "active") {
    assertQueueJobMatches(latest.job, job);
    await ensureQueuedJobRunning(latest.job);
  }
  return latest;
}

export async function advanceVerificationQueue(
  jobId: string,
  completion: QueueCompletionInput,
): Promise<QueueAdvance & { nextStarted: boolean }> {
  const advance = await completeVerificationJob(jobId, completion);
  let next = advance.next;
  for (let expiredJobs = 0; next && expiredJobs < 10; expiredJobs += 1) {
    try {
      await ensureQueuedJobRunning(next);
      return { ...advance, next, nextStarted: true };
    } catch (error) {
      const { SandboxNotFoundError } = await import("e2b");
      if (!(error instanceof SandboxNotFoundError)) {
        console.error("Unable to start the next durable verification job", error);
        return { ...advance, next, nextStarted: false };
      }
      console.error("Skipping an expired queued verification sandbox", {
        jobId: next.jobId,
      });
      const feedback = describeVerifierRejection(
        "",
        "The isolated verifier expired before producing a result.",
      );
      next = (
        await completeVerificationJob(next.jobId, {
          outcome: "rejected",
          promotionStatus: null,
          message: feedback.detail,
          feedback,
          evidenceUrl: null,
        })
      ).next;
    }
  }
  return { ...advance, next, nextStarted: false };
}
