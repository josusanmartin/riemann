import { ZodError } from "zod";
import { getSession } from "@/auth";
import {
  hasActiveE2BFlowTest,
  startE2BFlowTest,
} from "@/lib/e2b-flow-test";
import { isE2BConfigured } from "@/lib/e2b-config";
import { hasActiveE2BJob } from "@/lib/e2b-verifier";
import {
  FLOW_TEST_BASELINE_ID,
  flowTestRecord,
  isFlowTestOperator,
} from "@/lib/flow-test";
import { prepareFlowTestSubmission } from "@/lib/flow-test-server";
import { signSubmissionJob } from "@/lib/submission-jobs";
import { getActiveVerificationJob } from "@/lib/submission-queue";

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
      message: "Sign in with GitHub before running the verifier flow test.",
    });
  }
  if (!isFlowTestOperator(github)) {
    return noStore(403, {
      error: "flow_test_operator_required",
      message: "The noncompetitive flow test is currently restricted to site operators.",
    });
  }
  if (!isE2BConfigured()) {
    return noStore(503, {
      error: "verifier_unavailable",
      message: "The E2B verifier is not configured for this deployment.",
    });
  }
  const contentLength = Number(request.headers.get("content-length") ?? "0");
  if (Number.isFinite(contentLength) && contentLength > 2_100_000) {
    return noStore(413, {
      error: "submission_too_large",
      message: "The flow-test source exceeds the 2 MB limit.",
    });
  }

  try {
    const [competitiveJob, flowTestActive, ownerJobActive] = await Promise.all([
      getActiveVerificationJob(),
      hasActiveE2BFlowTest(),
      hasActiveE2BJob(github),
    ]);
    if (competitiveJob || flowTestActive || ownerJobActive) {
      return noStore(409, {
        error: "verifier_busy",
        message:
          "The linear verifier is already occupied. Wait for the active proof to finish, then run the flow test.",
      });
    }

    const baseCommitSha =
      process.env.VERCEL_GIT_COMMIT_SHA ?? process.env.RIEMANN_BASE_COMMIT_SHA;
    if (!baseCommitSha || !/^[0-9a-f]{40}$/.test(baseCommitSha)) {
      return noStore(503, {
        error: "deployment_identity_unavailable",
        message: "The flow test cannot bind this run to an immutable deployment.",
      });
    }
    const secret = process.env.AUTH_SECRET;
    if (!secret) {
      return noStore(503, {
        error: "job_signing_unavailable",
        message: "Flow-test job signing is unavailable.",
      });
    }

    const issuedAt = Date.now();
    const prepared = prepareFlowTestSubmission(
      await request.json(),
      github,
      session.user.name ?? github,
      issuedAt,
    );
    const job = await startE2BFlowTest({
      ...prepared,
      recordsSnapshot: `${JSON.stringify([flowTestRecord], null, 2)}\n`,
      baseCommitSha,
      previousRecordId: FLOW_TEST_BASELINE_ID,
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
        previousRecordId: FLOW_TEST_BASELINE_ID,
        issuedAt,
        expiresAt: issuedAt + 24 * 60 * 60 * 1_000,
      },
      secret,
    );

    return noStore(202, {
      status: "running",
      submissionId: prepared.submission.id,
      proofDigest: prepared.proofDigest,
      jobToken,
      message:
        "The noncompetitive Anthropic replay is running in the production verifier image.",
    });
  } catch (error) {
    if (error instanceof ZodError || error instanceof SyntaxError) {
      return noStore(400, {
        error: "invalid_flow_test",
        message: "Upload one valid UTF-8 Lean source file no larger than 2 MB.",
      });
    }
    console.error("Unable to start the verifier flow test", error);
    return noStore(502, {
      error: "flow_test_start_failed",
      message: "The isolated flow test could not start. Please retry shortly.",
    });
  }
}
