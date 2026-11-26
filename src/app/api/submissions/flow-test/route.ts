import { deploymentVerifierCommit } from "@/lib/verifier-identity";
import { guardUserApi } from "@/lib/api-guard";
import { boatSelected,boatConfigured,activeBoatFlow,startBoatFlow,stopBoatWorker,flowWorkerId } from "@/lib/boat-worker";
import { ZodError } from "zod";
import { VerifierTemplateMismatchError } from "@/lib/verifier-readiness";
import { readBoundedJson, RequestBodyTooLargeError } from "@/lib/request-json";
import { getSession } from "@/auth";
import {
  hasActiveE2BFlowTest,
  startE2BFlowTest,
} from "@/lib/e2b-flow-test";
import { isE2BConfigured } from "@/lib/e2b-config";
import { hasActiveE2BJob, killE2BSandbox } from "@/lib/e2b-verifier";
import {
  FLOW_TEST_BASELINE_ID,
  flowTestRecord,
  isFlowTestOperator,
} from "@/lib/flow-test";
import { prepareFlowTestSubmission } from "@/lib/flow-test-server";
import { signSubmissionJob } from "@/lib/submission-jobs";
import { getActiveVerificationJob } from "@/lib/submission-queue";

function stopFlow(handle:string) { return handle.startsWith("boat-") ? stopBoatWorker(flowWorkerId(handle)) : killE2BSandbox(handle); }

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
  const session = await getSession(request);
  const github = session?.user.githubLogin;
  if (!github) {
    return noStore(401, {
      error: "authentication_required",
      message: "Sign in with GitHub before running the verifier flow test.",
    });
  }
  if (!isFlowTestOperator(github, session?.user.githubId)) {
    return noStore(403, {
      error: "flow_test_operator_required",
      message: "The noncompetitive flow test is currently restricted to site operators.",
    });
  }
  if (boatSelected() ? !boatConfigured() : !isE2BConfigured()) {
    return noStore(503, {
      error: "verifier_unavailable",
      message: "The E2B verifier is not configured for this deployment.",
    });
  }

  let startedSandboxId: string | undefined;
  try {
    const [competitiveJob, flowTestActive, ownerJobActive] = await Promise.all([
      getActiveVerificationJob(),
      boatSelected() ? activeBoatFlow() : hasActiveE2BFlowTest(),
      boatSelected() ? false : hasActiveE2BJob(github),
    ]);
    if (competitiveJob || flowTestActive || ownerJobActive) {
      return noStore(409, {
        error: "verifier_busy",
        message:
          "The linear verifier is already occupied. Wait for the active proof to finish, then run the flow test.",
      });
    }

    const baseCommitSha = deploymentVerifierCommit();
    if (!baseCommitSha) {
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
      await readBoundedJson(request),
      github,
      session.user.name ?? github,
      issuedAt,
    );
    const start = boatSelected() ? startBoatFlow : startE2BFlowTest;
    const job = await start({
      ...prepared,
      recordsSnapshot: `${JSON.stringify([flowTestRecord], null, 2)}\n`,
      baseCommitSha,
      previousRecordId: FLOW_TEST_BASELINE_ID,
      issuedAt,
    });
    startedSandboxId = job.sandboxId;
    const competitiveJobAfterStart = await getActiveVerificationJob();
    if (competitiveJobAfterStart) {
      await stopFlow(job.sandboxId).catch(() => undefined);
      startedSandboxId = undefined;
      return noStore(409, {
        error: "verifier_busy",
        message:
          "A competitive proof entered the durable queue first, so the operator flow test was stopped.",
      });
    }
    const jobToken = signSubmissionJob(
      {
        schemaVersion: 1,
        sandboxId: job.sandboxId,
        jobId: job.jobId,
        submissionId: prepared.submission.id,
        github, githubId: session?.user.githubId,
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
    if (startedSandboxId) {
      await stopFlow(startedSandboxId).catch(() => undefined);
    }
    if (error instanceof VerifierTemplateMismatchError) {
      return noStore(503, { error: "verifier_template_stale", message: error.message });
    }
    if (error instanceof RequestBodyTooLargeError) {
      return noStore(413, { error: "submission_too_large", message: error.message });
    }
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
