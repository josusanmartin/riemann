import { isPublicationMismatch } from "./publication-feedback";
import { boatCompletionToken } from "./boat-completion-token";
import { after } from "next/server";
import { setTimeout as delay } from "node:timers/promises";
import { setupLimitMs, setupRetryMs, boatProgress } from "./boat-progress";
import { randomUUID } from "node:crypto";
import { computeDirectProofDigest } from "./direct-submission";
import { readSubmissionArchive } from "./submission-archive-store";
import { claimBoatSetup, getActiveVerificationJob, retryBoatAfterOom, updateBoatJob, type QueuedVerificationJob } from "./submission-queue";
import {
  BoatError,
  BoatIdentityMismatchError,
  assertBoatWorkerIdentity,
  activeBoatFlow,
  createBoatWorker,
  findCompetitiveWorker,
  readBoatFile,
  stageBoatFiles,
  boatResult,
  stopBoatWorker,
  workerLifetime,
} from "./boat-worker";
import {
  promoteVerifiedSubmission,
  UnpublishableResultError,
} from "./github-promotion";
import { describeVerifierRejection, kernelOomMessage } from "./verifier-feedback";
import {
  advanceVerificationQueue,
} from "./queue-orchestration";

export function reserveBoatJob(
  baseCommitSha: string,
  previousRecordId: string,
  issuedAt: number,
) {
  const jobId = randomUUID();
  return {
    jobId,
    sandboxId: `boat-${jobId}`,
    boat: { baseCommitSha, previousRecordId, issuedAt },
  };
}

async function archived(job: QueuedVerificationJob) {
  const entry = await readSubmissionArchive(job.boat?.memoryReplayOf ?? job.jobId);
  if (
    !entry ||
    entry.payload.proofDigest !== job.proofDigest ||
    computeDirectProofDigest(entry.payload.manifest, entry.payload.solution) !==
      job.proofDigest
  )
    throw new Error("Boat archive digest mismatch");
  return entry;
}

export async function boatMetadata(job: QueuedVerificationJob) {
  if (!job.boat) throw new Error("Missing Boat coordinates");
  const entry = await archived(job);
  return {
    ...job.boat,
    jobId: job.jobId,
    sandboxId: job.sandboxId,
    proofDigest: job.proofDigest,
    submissionId: entry.summary.submission.id,
    github: entry.summary.submission.author.github,
  };
}

class BoatSetupFinished extends Error {}

function setupIssue(error: unknown) {
  if (error instanceof BoatIdentityMismatchError) return "The worker did not match the pinned job, role or source revision";
  if (error instanceof Error && error.message === "Boat verifier checkout is still preparing") return "Waiting for the pinned verifier checkout";
  if (error instanceof BoatError && error.status === 402) return "Boat requires payment (HTTP 402)";
  if (error instanceof BoatError && [401, 403].includes(error.status)) return `Boat denied verifier access (HTTP ${error.status})`;
  if (error instanceof BoatError) return `Boat API returned HTTP ${error.status}`;
  if (error instanceof Error && ["TimeoutError", "AbortError"].includes(error.name)) return "Boat request timed out";
  if (error instanceof TypeError) return "Could not connect to Boat";
  return "The service could not complete the setup step";
}

async function finishSetupFailure(job: QueuedVerificationJob, message: string, issue?: string): Promise<never> {
  const b = job.boat!;
  const feedback = describeVerifierRejection("", message);
  const log = [
    `Queue admission: ${job.enqueuedAt}`,
    `Setup began: ${new Date(b.startedAt!).toISOString()}`,
    ...(b.assignedAt ? [`Worker assigned: ${new Date(b.assignedAt).toISOString()}`] : []),
    `Failure recorded: ${new Date().toISOString()}`,
    b.workerId ? "Worker assigned. Proof upload was not confirmed." : "No worker assignment was recorded.",
    issue ?? b.setupIssue ?? (b.lastProviderStatus ? `Boat API returned HTTP ${b.lastProviderStatus}` : "No provider response recorded."),
    message,
  ].join("\n");
  await advanceVerificationQueue(job.jobId, {
    outcome: "rejected", promotionStatus: null, message, feedback, evidenceUrl: null,
  }, log, b.setupLease);
  if (b.workerId) await stopBoatWorker(b.workerId).catch(() => undefined);
  throw new BoatSetupFinished(message);
}

export async function ensureBoatWorker(job: QueuedVerificationJob) {
  if (!job.boat) throw new Error("Missing Boat coordinates");
  if (job.boat.uploaded && job.boat.workerId) return job;
  if ((job.boat.retryAt ?? 0) > Date.now()) return job;
  const claim = await claimBoatSetup(job.jobId);
  let current = claim.job;
  if (!claim.claimed) return current;
  let b = current.boat!;
  const lease = b.setupLease!;
  const allocationExpired = !b.workerId && Date.now() - b.startedAt! >= setupLimitMs;
  if (b.workerId && Date.now() - b.startedAt! >= setupLimitMs) {
    // A lost acknowledgement after writing the final ready marker must not
    // turn a staged, potentially running proof into a setup failure.
    const ready = await readBoatFile(b.workerId, "riemann-incoming/ready", 10_000).catch(() => null);
    if (ready === current.proofDigest) {
      try {
        await assertBoatWorkerIdentity(b.workerId, { jobId: job.jobId, kind: "competitive", sha: b.baseCommitSha });
      } catch (error) {
        return finishSetupFailure(current, "Boat worker identity mismatch.", setupIssue(error));
      }
      return updateBoatJob(job.jobId, lease, { uploaded: true, setupIssue: undefined });
    }
    return finishSetupFailure(current, "Boat proof upload timed out.");
  }
  let operation = "Check worker allocation";
  try {
    if (!b.workerId) {
      let id;
      // Look up the original job before repeating an uncertain create.
      if (b.startedAt !== lease || allocationExpired) id = await findCompetitiveWorker(job.jobId);
      if (!id) {
        if (allocationExpired) return finishSetupFailure(current, "Boat worker allocation timed out.");
        if (await activeBoatFlow()) {
          return await updateBoatJob(job.jobId, lease, {
            startedAt: undefined, retryAt: Date.now() + setupRetryMs, setupIssue: "Waiting for an operator verification to finish",
          });
        }
        if (b.retiredWorkerId) await stopBoatWorker(b.retiredWorkerId);
        operation = "Create worker";
        id = await createBoatWorker(job.jobId, b.baseCommitSha, job.proofDigest, "competitive", Boolean(b.memoryReplayOf));
      }
      operation = "Save worker assignment";
      current = await updateBoatJob(job.jobId, lease, { workerId: id, assignedAt: Date.now(), retryAt: Date.now() + 90_000, setupIssue: undefined, lastProviderStatus: undefined });
      b = current.boat!;
    }
    operation = "Read archived proof";
    const entry = await archived(current);
    operation = "Transfer proof files";
    await stageBoatFiles(b.workerId!, entry.payload.manifest, entry.payload.solution, job.proofDigest,
      { jobId: job.jobId, kind: "competitive", sha: b.baseCommitSha }, {
      jobId: job.jobId,
      token: boatCompletionToken(job.jobId, job.proofDigest, process.env.AUTH_SECRET ?? ""),
    });
    operation = "Confirm proof transfer";
    return await updateBoatJob(job.jobId, lease, { uploaded: true, stagedAt: Date.now(), setupIssue: undefined, lastProviderStatus: undefined });
  } catch (error) {
    if (error instanceof BoatIdentityMismatchError) return finishSetupFailure(current, "Boat worker identity mismatch.", "The worker did not match the pinned job, role or source revision.");
    const issue = `${operation}: ${setupIssue(error)}`;
    const permanent = error instanceof BoatError && [400, 401, 402, 403, 422].includes(error.status);
    if (permanent) return finishSetupFailure(current, "Boat declined worker setup.", issue);
    if (!b.workerId && Date.now() - b.startedAt! >= setupLimitMs) {
      return finishSetupFailure(current, "Boat worker allocation timed out.", issue);
    }
    console.warn("Retrying Boat setup", { jobId: job.jobId, issue });
    return updateBoatJob(job.jobId, lease, {
      setupIssue: issue, lastProviderStatus: error instanceof BoatError ? error.status : undefined,
      retryAt: Date.now() + setupRetryMs,
    });
  }
}

// The admitted upload already has a signed handle. Keep provisioning on the
// server after replying, even when the submitter immediately closes the tab.
export function scheduleBoatSetup(job: QueuedVerificationJob) {
  after(async () => {
    const stopAt = Date.now() + 225_000;
    let current: QueuedVerificationJob | null = job;
    while (current?.jobId === job.jobId && !current.boat?.uploaded && Date.now() < stopAt) {
      try {
        current = await ensureBoatWorker(current);
        if (current.boat?.uploaded) return;
      } catch (error) {
        if (error instanceof BoatSetupFinished) return;
        console.error("Unable to persist Boat setup progress", { jobId: job.jobId });
      }
      await delay(setupRetryMs);
      try {
        current = await getActiveVerificationJob();
      } catch {
        // The next claim checks the live queue before touching the worker.
        console.warn("Unable to refresh Boat setup state", { jobId: job.jobId });
      }
    }
  });
}

export async function reconcileBoat(job: QueuedVerificationJob, receiptReady = false) {
  let active;
  try {
    active = await ensureBoatWorker(job);
  } catch (error) {
    if (error instanceof BoatSetupFinished) return { status: "rejected" as const, message: error.message };
    throw error;
  }
  if (!active.boat?.uploaded) return boatProgress(active);
  const { workerId, assignedAt, startedAt, previousRecordId, baseCommitSha, issuedAt } = active.boat;
  const result = await boatResult(
    workerId!,
    (assignedAt ?? startedAt!) + workerLifetime,
    async () => (await archived(active)).summary.submission.id,
    job.proofDigest,
    receiptReady,
  );
  if (!result) return boatProgress(active);
  const entry = await archived(active);
  const submission = entry.summary.submission;
  if (
    result.proofDigest !== job.proofDigest ||
    result.submissionId !== submission.id
  )
    throw new Error("Boat receipt identity mismatch");
  if (
    result.status === "rejected" &&
    result.message === kernelOomMessage &&
    !active.boat?.memoryReplayOf
  ) {
    const retry = await retryBoatAfterOom(
      active,
      randomUUID(),
      result.log,
      result.completedAt,
    );
    scheduleBoatSetup(retry);
    return {
      status: "running" as const,
      proofDigest: job.proofDigest,
      message:
        "The standard worker reached its memory limit. Retrying once on a 32 GB worker.",
    };
  }
  if (result.status === "rejected") {
    const feedback = describeVerifierRejection(result.log, result.message);
    await advanceVerificationQueue(
      job.jobId,
      {
        outcome: "rejected",
        promotionStatus: null,
        evidenceUrl: null,
        message: feedback.detail,
        feedback,
        completedAt: result.completedAt,
      },
      result.log,
    );
    await stopBoatWorker(workerId!).catch(() => undefined);
    return { ...result, feedback };
  }
  try {
    const promotion = await promoteVerifiedSubmission({
      baseCommitSha,
      previousRecordId,
      issuedAt,
      proofDigest: job.proofDigest,
      manifest: entry.payload.manifest,
      solution: entry.payload.solution,
      result: active.boat?.memoryReplayOf ? {
        ...result,
        log: `Original archive admission: ${entry.payload.submittedAt}\nOfficial memory retry: 28 GiB, same archived manifest and proof.\n${result.log}`,
      } : result,
    });
    await advanceVerificationQueue(
      job.jobId,
      {
        outcome: "promoted",
        promotionStatus: promotion.status,
        evidenceUrl: promotion.evidenceUrl,
        message: null,
        completedAt: result.completedAt,
      },
      result.log,
    );
    await stopBoatWorker(workerId!).catch(() => undefined);
    return { ...result, promotion };
  } catch (error) {
    if (!(error instanceof UnpublishableResultError)) throw error;
    await advanceVerificationQueue(
      job.jobId,
      {
        outcome: isPublicationMismatch(error.message) ? "publication-blocked" : "superseded",
        promotionStatus: null,
        evidenceUrl: null,
        message: error.message,
        completedAt: result.completedAt,
      },
      result.log,
    );
    await stopBoatWorker(workerId!).catch(() => undefined);
    return {
      ...result,
      promotion: { status: "superseded" as const, message: error.message },
    };
  }
}
