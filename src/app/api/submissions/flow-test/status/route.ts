import { getSession } from "@/auth";
import { compareRationals } from "@/lib/challenge";
import {
  killE2BSandbox,
  readE2BVerification,
} from "@/lib/e2b-verifier";
import {
  FLOW_TEST_BASELINE_ID,
  FLOW_TEST_SCORE,
} from "@/lib/flow-test";
import { assertE2BResultMatchesJob } from "@/lib/submission-finalization";
import { verifySubmissionJob } from "@/lib/submission-jobs";
import { describeVerifierRejection } from "@/lib/verifier-feedback";

export const runtime = "nodejs";
export const maxDuration = 60;

function noStore(status: number, body: object): Response {
  return Response.json(body, {
    status,
    headers: { "Cache-Control": "no-store" },
  });
}

export async function GET(request: Request): Promise<Response> {
  const session = await getSession();
  const github = session?.user.githubLogin;
  if (!github) {
    return noStore(401, {
      error: "authentication_required",
      message: "Sign in with GitHub to inspect this flow test.",
    });
  }
  const secret = process.env.AUTH_SECRET;
  if (!secret) return noStore(503, { error: "job_signing_unavailable" });
  const token = new URL(request.url).searchParams.get("job");
  if (!token) {
    return noStore(400, {
      error: "job_required",
      message: "A signed flow-test job handle is required.",
    });
  }

  try {
    const job = verifySubmissionJob(token, secret);
    if (job.github.toLowerCase() !== github.toLowerCase()) {
      return noStore(403, {
        error: "job_owner_mismatch",
        message: "This flow test belongs to another GitHub account.",
      });
    }
    if (
      job.previousRecordId !== FLOW_TEST_BASELINE_ID ||
      !job.submissionId.startsWith("flow-test-")
    ) {
      return noStore(400, {
        error: "not_a_flow_test",
        message: "That signed handle is not a noncompetitive flow-test job.",
      });
    }

    const result = await readE2BVerification(job.sandboxId, job.jobId);
    if (!result) {
      return noStore(200, {
        status: "running",
        submissionId: job.submissionId,
        proofDigest: job.proofDigest,
        message: "Comparator, Lean, and nanoda are replaying the test proof.",
      });
    }
    assertE2BResultMatchesJob(job, result);
    if (result.status === "rejected") {
      const feedback = describeVerifierRejection(result.log, result.message);
      await killE2BSandbox(job.sandboxId).catch(() => undefined);
      return noStore(200, {
        ...result,
        message: feedback.detail,
        feedback,
      });
    }
    if (
      result.attestation.previousRecordId !== FLOW_TEST_BASELINE_ID ||
      compareRationals(result.attestation.score, FLOW_TEST_SCORE) !== 0
    ) {
      throw new Error("The verifier returned an attestation for a different contract");
    }
    await killE2BSandbox(job.sandboxId).catch(() => undefined);
    return noStore(200, {
      ...result,
      message:
        "Flow test passed: Comparator matched all three statements, and Lean plus nanoda accepted the proof. Nothing was promoted.",
      promotion: { status: "test-only" },
    });
  } catch (error) {
    const { SandboxNotFoundError } = await import("e2b");
    if (error instanceof SandboxNotFoundError) {
      const feedback = describeVerifierRejection(
        "",
        "The flow-test sandbox expired before producing a result.",
      );
      return noStore(410, {
        error: "job_expired",
        message: feedback.detail,
        feedback,
      });
    }
    const message = error instanceof Error ? error.message : "Invalid flow-test job.";
    if (message.includes("token") || message.includes("signature")) {
      return noStore(400, { error: "invalid_job", message });
    }
    console.error("Unable to read verifier flow-test status", error);
    return noStore(502, {
      error: "flow_test_status_failed",
      message: "The isolated flow-test status is temporarily unavailable.",
    });
  }
}
