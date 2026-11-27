import { publicationReady } from "@/lib/publication-material";
import { compactRuntimePinned } from "@/lib/compact-runtime";
import { deploymentVerifierCommit } from "@/lib/verifier-identity";
import { guardUserApi } from "@/lib/api-guard";
import { boatSelected,boatConfigured,activeBoatFlow,startBoatFlow,stopBoatWorker,flowWorkerId } from "@/lib/boat-worker";
import { ZodError } from "zod";
import { readBoundedJson, RequestBodyTooLargeError } from "@/lib/request-json";
import { getSession } from "@/auth";
import {
  FLOW_TEST_BASELINE_ID,
  isFlowTestOperator,
} from "@/lib/flow-test";
import { prepareFlowTestSubmission } from "@/lib/flow-test-server";
import { signSubmissionJob } from "@/lib/submission-jobs";
import { getActiveVerificationJob } from "@/lib/submission-queue";

function stopFlow(handle: string) { return stopBoatWorker(flowWorkerId(handle)); }

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
  if (!boatSelected() || !boatConfigured() || !compactRuntimePinned() || !(await publicationReady())) {
    return noStore(503, {
      error: "verifier_unavailable",
      message: "The compact Boat verifier is unavailable on this deployment.",
    });
  }

  let startedSandboxId: string | undefined;
  try {
    const [competitiveJob, flowTestActive] = await Promise.all([
      getActiveVerificationJob(),
      activeBoatFlow(),
    ]);
    if (competitiveJob || flowTestActive) {
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
    const job = await startBoatFlow({ ...prepared, baseCommitSha });
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
