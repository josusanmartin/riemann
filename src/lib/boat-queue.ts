import { boatCompletionToken } from "./boat-completion-token";
import { randomUUID } from "node:crypto";
import { computeDirectProofDigest } from "./direct-submission";
import { readSubmissionArchive } from "./submission-archive-store";
import { updateBoatJob, type QueuedVerificationJob } from "./submission-queue";
import {
  activeBoatFlow,
  createBoatWorker,
  stageBoatFiles,
  boatResult,
  stopBoatWorker,
  workerLifetime,
} from "./boat-worker";
import {
  promoteVerifiedSubmission,
  UnpublishableResultError,
} from "./github-promotion";
import { describeVerifierRejection } from "./verifier-feedback";
import {
  advanceVerificationQueue,
  VerifierOccupiedByFlowTestError,
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
  const entry = await readSubmissionArchive(job.jobId);
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

export async function ensureBoatWorker(job: QueuedVerificationJob) {
  if (!job.boat) throw new Error("Missing Boat coordinates");
  if (job.boat.uploaded && job.boat.workerId) return job;
  if (!job.boat.startedAt && (await activeBoatFlow()))
    throw new VerifierOccupiedByFlowTestError();
  const reserved = job.boat.startedAt
    ? job
    : await updateBoatJob(job.jobId, { startedAt: Date.now() });
  const b = reserved.boat!;
  if (Date.now() - b.startedAt! >= workerLifetime)
    throw new Error("Boat launch expired");
  const id =
    b.workerId ??
    (await createBoatWorker(
      job.jobId,
      b.baseCommitSha,
      job.proofDigest,
      "competitive",
    ));
  if (!b.workerId) await updateBoatJob(job.jobId, { workerId: id });
  const entry = await archived(job);
  await stageBoatFiles(
    id,
    entry.payload.manifest,
    entry.payload.solution,
    job.proofDigest,
    {
      jobId: job.jobId,
      token: boatCompletionToken(
        job.jobId,
        job.proofDigest,
        process.env.AUTH_SECRET ?? "",
      ),
    },
  );
  return updateBoatJob(job.jobId, { uploaded: true });
}

export async function reconcileBoat(
  job: QueuedVerificationJob,
  receiptReady = false,
) {
  const b = job.boat!;
  if (
    !b.uploaded &&
    b.startedAt &&
    Date.now() - b.startedAt >= workerLifetime
  ) {
    await advanceVerificationQueue(job.jobId, {
      outcome: "rejected",
      message: "Boat worker provisioning expired.",
      completedAt: new Date().toISOString(),
      promotionStatus: null,
      evidenceUrl: null,
    });
    if (b.workerId) await stopBoatWorker(b.workerId).catch(() => undefined);
    return {
      status: "rejected" as const,
      message: "Boat worker provisioning expired.",
    };
  }
  let active;
  try {
    active = await ensureBoatWorker(job);
  } catch (error) {
    if (error instanceof VerifierOccupiedByFlowTestError)
      return { status: "running" as const, proofDigest: job.proofDigest };
    throw error;
  }
  const { workerId, startedAt, previousRecordId, baseCommitSha, issuedAt } =
    active.boat!;
  const result = await boatResult(
    workerId!,
    startedAt! + workerLifetime,
    async () => (await archived(active)).summary.submission.id,
    job.proofDigest,
    receiptReady,
  );
  if (!result)
    return { status: "running" as const, proofDigest: job.proofDigest };
  const entry = await archived(active);
  const submission = entry.summary.submission;
  if (
    result.proofDigest !== job.proofDigest ||
    result.submissionId !== submission.id
  )
    throw new Error("Boat receipt identity mismatch");
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
      result,
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
        outcome: "superseded",
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
