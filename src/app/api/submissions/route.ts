import { ZodError } from "zod";
import { getSession } from "@/auth";
import { records } from "@/lib/records";
import { prepareDirectSubmission } from "@/lib/direct-submission";
import {
  hasActiveE2BJob,
  startE2BVerification,
} from "@/lib/e2b-verifier";
import { isE2BConfigured } from "@/lib/e2b-config";
import {
  ensureE2BWebhook,
  isE2BWebhookConfigured,
} from "@/lib/e2b-webhooks";
import { isGitHubPromotionConfigured } from "@/lib/github-promotion";
import { getCurrentRecord } from "@/lib/records";
import { signSubmissionJob } from "@/lib/submission-jobs";

export const runtime = "nodejs";
export const maxDuration = 60;

function noStore(status: number, body: object): Response {
  return Response.json(body, {
    status,
    headers: { "Cache-Control": "no-store" },
  });
}

export async function POST(request: Request): Promise<Response> {
  const session = await getSession();
  const github = session?.user.githubLogin;
  if (!github) {
    return noStore(401, {
      error: "authentication_required",
      message: "Sign in with GitHub before submitting a formal proof.",
    });
  }
  if (!isE2BConfigured()) {
    return noStore(503, {
      error: "verifier_unavailable",
      message: "The E2B verifier is not configured for this deployment.",
    });
  }
  if (!isGitHubPromotionConfigured() || !isE2BWebhookConfigured()) {
    return noStore(503, {
      error: "automation_unavailable",
      message:
        "Automatic evidence publication is not configured for this deployment.",
    });
  }

  const contentLength = Number(request.headers.get("content-length") ?? "0");
  if (Number.isFinite(contentLength) && contentLength > 2_100_000) {
    return noStore(413, {
      error: "submission_too_large",
      message: "The direct submission exceeds the 2 MB source limit.",
    });
  }

  try {
    const currentRecord = getCurrentRecord();
    const prepared = prepareDirectSubmission(
      await request.json(),
      github,
      currentRecord,
    );
    if (records.some((record) => record.id === prepared.submission.id)) {
      return noStore(409, {
        error: "submission_exists",
        message: "That submission identifier is already part of the public record.",
      });
    }
    if (await hasActiveE2BJob(github)) {
      return noStore(429, {
        error: "verification_in_progress",
        message: "This GitHub account already has a proof verification running.",
      });
    }

    const baseCommitSha =
      process.env.VERCEL_GIT_COMMIT_SHA ?? process.env.RIEMANN_BASE_COMMIT_SHA;
    if (!baseCommitSha || !/^[0-9a-f]{40}$/.test(baseCommitSha)) {
      return noStore(503, {
        error: "deployment_identity_unavailable",
        message: "The verifier cannot bind this upload to an immutable deployment.",
      });
    }
    const secret = process.env.AUTH_SECRET;
    if (!secret) {
      return noStore(503, {
        error: "job_signing_unavailable",
        message: "Submission job signing is unavailable.",
      });
    }

    await ensureE2BWebhook();
    const issuedAt = Date.now();
    const job = await startE2BVerification({
      ...prepared,
      recordsSnapshot: `${JSON.stringify(records, null, 2)}\n`,
      baseCommitSha,
      previousRecordId: currentRecord.id,
      issuedAt,
    });
    const jobToken = signSubmissionJob(
      {
        schemaVersion: 1,
        sandboxId: job.sandboxId,
        jobId: job.jobId,
        submissionId: prepared.submission.id,
        github,
        proofDigest: prepared.proofDigest,
        baseCommitSha,
        previousRecordId: currentRecord.id,
        issuedAt,
        expiresAt: issuedAt + 24 * 60 * 60 * 1_000,
      },
      secret,
    );

    return noStore(202, {
      status: "queued",
      submissionId: prepared.submission.id,
      proofDigest: prepared.proofDigest,
      jobToken,
    });
  } catch (error) {
    if (error instanceof ZodError || error instanceof SyntaxError) {
      return noStore(400, {
        error: "invalid_submission",
        message: "The submission fields do not match the formal input schema.",
      });
    }
    const message = error instanceof Error ? error.message : "Verification could not start.";
    if (
      message.includes("strictly exceed") ||
      message.includes("cannot exceed one") ||
      message.includes("2 MB")
    ) {
      return noStore(400, { error: "invalid_submission", message });
    }
    console.error("Unable to start E2B verification", error);
    return noStore(502, {
      error: "verifier_start_failed",
      message: "The isolated verifier could not be started. Please retry shortly.",
    });
  }
}
