import { timingSafeEqual } from "node:crypto";
import { submissionSchema } from "@/lib/challenge";
import { computeDirectProofDigest } from "@/lib/direct-submission";
import {
  killE2BSandbox,
  readE2BSubmissionBundle,
} from "@/lib/e2b-verifier";
import {
  readQueuedE2BJobMetadata,
  stageE2BVerification,
} from "@/lib/e2b-queue";
import { ensureQueuedJobRunning } from "@/lib/queue-orchestration";
import { getCurrentRecord, records } from "@/lib/records";
import {
  getActiveVerificationJob,
  replaceActiveVerificationJob,
} from "@/lib/submission-queue";

export const runtime = "nodejs";
export const maxDuration = 60;

function authorized(request: Request): boolean {
  const secret = process.env.E2B_TEMPLATE_ADMIN_SECRET;
  const supplied = request.headers.get("authorization");
  if (!secret || secret.length < 32 || !supplied) return false;
  const expected = Buffer.from(`Bearer ${secret}`, "utf8");
  const actual = Buffer.from(supplied, "utf8");
  return expected.length === actual.length && timingSafeEqual(expected, actual);
}

function noStore(status: number, body: object): Response {
  return Response.json(body, {
    status,
    headers: { "Cache-Control": "no-store" },
  });
}

export async function POST(request: Request): Promise<Response> {
  if (!authorized(request)) return noStore(401, { error: "unauthorized" });

  let replacementSandboxId: string | undefined;
  let queueReplaced = false;
  try {
    const active = await getActiveVerificationJob();
    if (!active) {
      return noStore(409, { error: "no_active_verification" });
    }
    const metadata = await readQueuedE2BJobMetadata(active.sandboxId);
    if (
      metadata.jobId !== active.jobId ||
      metadata.proofDigest !== active.proofDigest
    ) {
      throw new Error("The active queue entry does not match its E2B metadata");
    }

    const bundle = await readE2BSubmissionBundle(active.sandboxId, active.jobId);
    const submission = submissionSchema.parse(JSON.parse(bundle.manifest));
    const proofDigest = computeDirectProofDigest(bundle.manifest, bundle.solution);
    if (proofDigest !== active.proofDigest) {
      throw new Error("The recovered source does not match its immutable digest");
    }
    const baseCommitSha = process.env.VERCEL_GIT_COMMIT_SHA;
    if (!baseCommitSha || !/^[0-9a-f]{40}$/.test(baseCommitSha)) {
      throw new Error("The recovery deployment has no immutable Git identity");
    }

    const issuedAt = Date.now();
    const currentRecord = getCurrentRecord();
    const staged = await stageE2BVerification({
      submission,
      manifest: bundle.manifest,
      solution: bundle.solution,
      recordsSnapshot: `${JSON.stringify(records, null, 2)}\n`,
      proofDigest,
      baseCommitSha,
      previousRecordId: currentRecord.id,
      issuedAt,
    });
    replacementSandboxId = staged.sandboxId;
    const recovered = await replaceActiveVerificationJob(active, {
      ...staged,
      proofDigest,
    });
    queueReplaced = true;
    await killE2BSandbox(active.sandboxId).catch(() => undefined);

    let running = true;
    try {
      await ensureQueuedJobRunning(recovered);
    } catch (error) {
      running = false;
      console.error("Recovered E2B job is queued but did not start yet", error);
    }
    return noStore(202, {
      status: running ? "running" : "queued",
      submissionId: submission.id,
      proofDigest,
      replacedJobId: active.jobId,
      jobId: recovered.jobId,
      sandboxId: recovered.sandboxId,
    });
  } catch (error) {
    if (replacementSandboxId && !queueReplaced) {
      await killE2BSandbox(replacementSandboxId).catch(() => undefined);
    }
    console.error("Unable to recover the active E2B verification", error);
    return noStore(502, {
      error: "active_verification_recovery_failed",
      message:
        error instanceof Error
          ? error.message
          : "The active verification could not be recovered",
    });
  }
}
