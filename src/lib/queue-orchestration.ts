import {
  launchQueuedE2BVerification,
  pauseQueuedE2BVerification,
  readQueuedE2BJobMetadata,
  type QueuedE2BRunnerState,
} from "@/lib/e2b-queue";
import { killE2BSandbox } from "@/lib/e2b-verifier";
import {
  completeVerificationJob,
  inspectVerificationJob,
  readPublishedRecordId,
  type QueueAdvance,
  type QueueCompletionInput,
  type QueueInspection,
  type QueueAdmission,
  type QueuedVerificationJob,
} from "@/lib/submission-queue";
import {
  describeVerifierRejection,
  recordSupersededFeedback,
} from "@/lib/verifier-feedback";

type QueueCoordinates = {
  sandboxId: string;
  jobId: string;
  proofDigest: string;
};

export class VerifierOccupiedByFlowTestError extends Error {
  constructor() {
    super("The operator flow test currently owns the linear verifier");
    this.name = "VerifierOccupiedByFlowTestError";
  }
}

export function assertQueueJobMatches(
  queued: QueuedVerificationJob,
  coordinates: QueueCoordinates,
): void {
  if (
    queued.sandboxId !== coordinates.sandboxId ||
    queued.jobId !== coordinates.jobId ||
    queued.proofDigest !== coordinates.proofDigest
  ) {
    throw new Error(
      "The durable queue entry does not match the verification job",
    );
  }
}

export async function ensureQueuedJobRunning(
  job: QueuedVerificationJob,
): Promise<QueuedE2BRunnerState> {
  const { hasActiveE2BFlowTest } = await import("@/lib/e2b-flow-test");
  if (await hasActiveE2BFlowTest()) {
    throw new VerifierOccupiedByFlowTestError();
  }
  return launchQueuedE2BVerification(job);
}

export function ensureQueuedJobPaused(
  job: QueuedVerificationJob,
): Promise<void> {
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

type InitialQueueTransitionDependencies = {
  start: (job: QueuedVerificationJob) => Promise<unknown>;
  reconcile: (job: QueuedVerificationJob) => Promise<QueueInspection>;
};

export async function applyInitialQueueTransition(
  admission: QueueAdmission,
  dependencies: InitialQueueTransitionDependencies = {
    start: ensureQueuedJobRunning,
    reconcile: reconcileQueuedJobPause,
  },
): Promise<boolean> {
  if (admission.shouldStart) {
    await dependencies.start(admission.job);
    return true;
  }
  return (await dependencies.reconcile(admission.job)).status === "active";
}

// A queued proof is attested against the record that was current when it was
// admitted. Once another record lands, promotion is certain to fail, so running
// it would only hold the single verifier lane for up to an hour. Any lookup
// failure answers "not stale" so the job runs exactly as it would have before.
async function isSupersededBeforeStart(
  job: QueuedVerificationJob,
  publishedRecordId: string | null,
): Promise<boolean> {
  if (!publishedRecordId) return false;
  try {
    const metadata = await readQueuedE2BJobMetadata(job.sandboxId);
    if (metadata.jobId !== job.jobId) return false;
    return metadata.previousRecordId !== publishedRecordId;
  } catch {
    return false;
  }
}

export async function advanceVerificationQueue(
  jobId: string,
  completion: QueueCompletionInput,
  verifierLog?: string,
): Promise<QueueAdvance & { nextStarted: boolean }> {
  const advance = await completeVerificationJob(jobId, completion, {}, verifierLog);
  let next = advance.next;
  let publishedRecordId: string | null | undefined;
  for (let skippedJobs = 0; next && skippedJobs < 10; skippedJobs += 1) {
    if (publishedRecordId === undefined) {
      publishedRecordId = await readPublishedRecordId().catch((error) => {
        console.error("Unable to read the published record before starting a job", error);
        return null;
      });
    }
    if (await isSupersededBeforeStart(next, publishedRecordId)) {
      console.warn("Skipping a queued verification superseded by a new record", {
        jobId: next.jobId,
      });
      const stale = next;
      const feedback = recordSupersededFeedback();
      next = (
        await completeVerificationJob(stale.jobId, {
          outcome: "rejected",
          promotionStatus: null,
          message: feedback.detail,
          feedback,
          evidenceUrl: null,
        })
      ).next;
      await killE2BSandbox(stale.sandboxId).catch(() => undefined);
      continue;
    }
    try {
      await ensureQueuedJobRunning(next);
      return { ...advance, next, nextStarted: true };
    } catch (error) {
      const { SandboxNotFoundError } = await import("e2b");
      if (!(error instanceof SandboxNotFoundError)) {
        console.error(
          "Unable to start the next durable verification job",
          error,
        );
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
