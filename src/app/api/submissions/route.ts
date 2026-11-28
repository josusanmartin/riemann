import { publicationReady } from "@/lib/publication-material";
import { compactRuntimePinned } from "@/lib/compact-runtime";
import { deploymentVerifierCommit } from "@/lib/verifier-identity";
import { guardUserApi } from "@/lib/api-guard";
import { boatSelected, boatConfigured } from "@/lib/boat-worker";
import { boatProgress } from "@/lib/boat-progress";
import { reserveBoatJob } from "@/lib/boat-queue";
import { ZodError } from "zod";
import { getSubmissionSession } from "@/lib/submission-session";
import { prepareDirectSubmission } from "@/lib/direct-submission";
import { isGitHubPromotionConfigured } from "@/lib/github-promotion";
import {
  applyInitialQueueTransition,
} from "@/lib/queue-orchestration";
import { getCurrentRecord, records } from "@/lib/records";
import { signSubmissionJob } from "@/lib/submission-jobs";
import { readBoundedJson, RequestBodyTooLargeError } from "@/lib/request-json";
import {
  DailySubmissionLimitError,
  enqueueVerificationJob,
  getDailySubmissionUsage,
  isSubmissionQueueConfigured,
  QueueCommitUncertainError,
  SubmissionAlreadyQueuedError,
  SubmissionQueueFullError,
} from "@/lib/submission-queue";

export const runtime = "nodejs";

export const maxDuration = 300;

function noStore(status: number, body: object): Response {
  return Response.json(body, {
    status,
    headers: { "Cache-Control": "no-store" },
  });
}

export async function POST(request: Request): Promise<Response> {
  const denied = guardUserApi(request, "upload");
  if (denied) return denied;
  const track = new URL(request.url).searchParams.get("track");
  if (track && track !== "critical-line") return noStore(503, {
    error: "verifier_unavailable", message: "This leaderboard has not opened for ranked uploads. No slot was used.",
  });
  // Operator switch for verifier upgrades: refuse new uploads before any
  // worker or daily slot is touched. In-flight proofs are unaffected.
  if (process.env.SUBMISSIONS_PAUSED === "1") {
    return noStore(503, {
      error: "submissions_paused",
      message:
        process.env.SITE_NOTICE?.trim() ||
        "Submissions are briefly paused for verifier maintenance. No daily slot was used; please try again shortly.",
    });
  }
  const session = await getSubmissionSession(request);
  const github = session?.user.githubLogin;
  if (!github) {
    return noStore(401, {
      error: "authentication_required",
      message: "Sign in with GitHub before submitting a formal proof.",
    });
  }
  const githubId = session?.user.githubId;
  if (!githubId) return noStore(401, {
    error: "sign_in_again",
    message: "Refresh your GitHub sign-in on the submission page before uploading.",
  });
  if (!boatSelected() || !boatConfigured() || !compactRuntimePinned() || !(await publicationReady())) {
    return noStore(503, {
      error: "verifier_unavailable",
      message: "The verifier is not configured for this deployment.",
    });
  }
  if (
    !isGitHubPromotionConfigured() ||
    !isSubmissionQueueConfigured()
  ) {
    return noStore(503, {
      error: "automation_unavailable",
      message:
        "Automatic evidence publication is not configured for this deployment.",
    });
  }

  try {
    const currentRecord = getCurrentRecord();
    let prepared;
    try {
      prepared = prepareDirectSubmission(await readBoundedJson(request), github, currentRecord);
    } catch (error) {
      if (error instanceof SyntaxError) return noStore(400, {
        error: "invalid_submission_json", message: "Send valid UTF-8 JSON with Content-Type: application/json. No slot was used.",
      });
      if (error instanceof ZodError) {
        const fields: Record<string, string> = {
          id: "Use 1–80 lowercase letters, digits or hyphens, starting with a letter or digit.",
          displayName: "Provide a display name of 1–100 characters.",
          score: "Provide an exact numerator and denominator.",
          "score.numerator": "Use a positive integer string of at most 200 digits.",
          "score.denominator": "Use a positive integer string of at most 200 digits.",
          method: "Describe your method in 3–200 characters.",
          summary: "Describe your result in 20–1,000 characters.",
          model: "Use 1–80 characters, null, or omit this field.",
          harness: "Use 1–80 characters, null, or omit this field.",
          solution: "Provide one non-empty UTF-8 Lean source file of at most 2 MB.",
          acceptLicense: "Set acceptLicense to true to authorize publication under Apache-2.0.",
        };
        const issues = error.issues.slice(0, 12).map(issue => {
          const path = issue.path.join(".");
          const field = Object.hasOwn(fields, path) ? path : "request";
          const message = issue.code === "unrecognized_keys" ? "Remove unsupported fields." :
            fields[field] ?? "Send a submission object with the fields listed in the agent guide.";
          return { field, message };
        });
        return noStore(400, {
          error: "invalid_submission", issues,
          message: issues.map(issue => `${issue.field}: ${issue.message}`).join(" ") + " No slot was used.",
        });
      }
      throw error;
    }
    if (records.some((record) => record.id === prepared.submission.id)) {
      return noStore(409, {
        error: "submission_exists",
        message: "That submission identifier is already part of the public record.",
      });
    }
    const dailyUsage = await getDailySubmissionUsage(github, { githubId });
    if (dailyUsage.used >= dailyUsage.limit) {
      return noStore(429, {
        error: "daily_submission_limit",
        message: `This GitHub account may submit at most ${dailyUsage.limit} proofs per UTC day.`,
        dailyUsed: dailyUsage.used,
        dailyLimit: dailyUsage.limit,
        retryAt: dailyUsage.retryAt,
      });
    }

    const baseCommitSha = deploymentVerifierCommit();
    if (!baseCommitSha) {
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

    const issuedAt = Date.now();
    const job = reserveBoatJob(baseCommitSha, currentRecord.id, issuedAt);
    const admission = await enqueueVerificationJob(
      { ...job, proofDigest: prepared.proofDigest, submissionId: prepared.submission.id },
      github,
      { manifest: prepared.manifest, solution: prepared.solution },
      { githubId },
    );

    let verificationRunning = false;
    try {
      verificationRunning = await applyInitialQueueTransition(admission);
    } catch (error) {
      // Admission is already durable. Status polling and the cron backstop can
      // safely retry this idempotent transition without losing the upload.
      console.error("Unable to apply the initial verifier queue state", error);
    }
    const jobToken = signSubmissionJob(
      {
        schemaVersion: 1,
        sandboxId: admission.job.sandboxId,
        jobId: admission.job.jobId,
        submissionId: prepared.submission.id,
        github, githubId,
        proofDigest: prepared.proofDigest,
        baseCommitSha,
        previousRecordId: currentRecord.id,
        issuedAt,
        expiresAt: issuedAt + 7 * 24 * 60 * 60 * 1_000,
      },
      secret,
    );

    console.info("Submission admitted", {
      jobId: job.jobId, proofDigest: prepared.proofDigest, queuePosition: admission.position,
    });
    return noStore(202, {
      jobId: job.jobId,
      status: verificationRunning ? "running" : "queued",
      ...(verificationRunning && admission.job.boat ? boatProgress(admission.job) : {}),
      submissionId: prepared.submission.id,
      proofDigest: prepared.proofDigest,
      jobToken,
      queuePosition: verificationRunning ? 0 : admission.position,
      dailyUsed: admission.dailyUsed,
      dailyLimit: admission.dailyLimit,
    });
  } catch (error) {
    if (error instanceof RequestBodyTooLargeError) {
      return noStore(413, { error: "submission_too_large", message: error.message });
    }
    if (error instanceof QueueCommitUncertainError) {
      return noStore(503, { error: "queue_admission_uncertain", message: error.message });
    }
    if (error instanceof DailySubmissionLimitError) {
      return noStore(429, {
        error: "daily_submission_limit",
        message: error.message,
        dailyLimit: error.limit,
        retryAt: error.retryAt,
      });
    }
    if (error instanceof SubmissionQueueFullError) {
      return noStore(503, { error: "verification_queue_full", message: error.message });
    }
    if (error instanceof SubmissionAlreadyQueuedError) {
      return noStore(409, { error: "submission_already_queued", message: error.message });
    }
    const message = error instanceof Error ? error.message : "Verification could not start.";
    if (message.includes("strictly exceed")) {
      const current = getCurrentRecord();
      return noStore(400, {
        error: "invalid_submission", message: `${message}. Check record ${current.id} before submitting. No slot was used.`,
        currentRecord: { id: current.id, score: current.exactRational },
      });
    }
    if (
      message.includes("cannot exceed one") ||
      message.includes("2 MB")
    ) {
      return noStore(400, { error: "invalid_submission", message });
    }
    console.error("Unable to start verification", error);
    return noStore(502, {
      error: "verifier_start_failed",
      message: "The isolated verifier could not be started. Please retry shortly.",
    });
  }
}
