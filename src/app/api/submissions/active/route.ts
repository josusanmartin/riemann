import { getSession } from "@/auth";
import { readQueuedE2BJobMetadata } from "@/lib/e2b-queue";
import { assertQueueJobMatches } from "@/lib/queue-orchestration";
import { signSubmissionJob } from "@/lib/submission-jobs";
import { inspectVerificationJobForOwner } from "@/lib/submission-queue";

export const runtime = "nodejs";
export const maxDuration = 60;

const JOB_TOKEN_LIFETIME_MS = 7 * 24 * 60 * 60 * 1_000;

function noStore(status: number, body: object): Response {
  return Response.json(body, {
    status,
    headers: { "Cache-Control": "no-store" },
  });
}

export async function GET(): Promise<Response> {
  const session = await getSession();
  const github = session?.user.githubLogin;
  if (!github) {
    return noStore(401, {
      error: "authentication_required",
      message: "Sign in with GitHub to recover an active verification job.",
    });
  }
  const secret = process.env.AUTH_SECRET;
  if (!secret) {
    return noStore(503, { error: "job_signing_unavailable" });
  }

  try {
    const queue = await inspectVerificationJobForOwner(github);
    if (queue.status === "missing") {
      return noStore(200, { status: "none" });
    }
    const metadata = await readQueuedE2BJobMetadata(queue.job.sandboxId);
    assertQueueJobMatches(queue.job, metadata);
    if (metadata.github.toLowerCase() !== github.toLowerCase()) {
      throw new Error("The recovered queue job belongs to another GitHub account");
    }
    const jobToken = signSubmissionJob(
      {
        schemaVersion: 1,
        sandboxId: metadata.sandboxId,
        jobId: metadata.jobId,
        submissionId: metadata.submissionId,
        github,
        proofDigest: metadata.proofDigest,
        baseCommitSha: metadata.baseCommitSha,
        previousRecordId: metadata.previousRecordId,
        issuedAt: metadata.issuedAt,
        expiresAt: Date.now() + JOB_TOKEN_LIFETIME_MS,
      },
      secret,
    );
    return noStore(200, {
      status: queue.status === "active" ? "running" : "queued",
      submissionId: metadata.submissionId,
      proofDigest: metadata.proofDigest,
      jobToken,
      queuePosition: queue.position,
    });
  } catch (error) {
    console.error("Unable to recover the user's verification job", error);
    return noStore(502, {
      error: "job_recovery_failed",
      message: "The active verification job could not be recovered yet.",
    });
  }
}
