import { getSession } from "@/auth";
import {
  killE2BSandbox,
  readE2BVerification,
} from "@/lib/e2b-verifier";
import {
  describePromotionError,
  isGitHubPromotionConfigured,
  PromotionRaceError,
} from "@/lib/github-promotion";
import {
  assertE2BResultMatchesJob,
  promoteE2BResult,
} from "@/lib/submission-finalization";
import { verifySubmissionJob } from "@/lib/submission-jobs";

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
      message: "Sign in with GitHub to inspect this verification job.",
    });
  }
  const secret = process.env.AUTH_SECRET;
  if (!secret) {
    return noStore(503, { error: "job_signing_unavailable" });
  }

  const token = new URL(request.url).searchParams.get("job");
  if (!token) {
    return noStore(400, {
      error: "job_required",
      message: "A signed verification job handle is required.",
    });
  }

  try {
    const job = verifySubmissionJob(token, secret);
    if (job.github.toLowerCase() !== github.toLowerCase()) {
      return noStore(403, {
        error: "job_owner_mismatch",
        message: "This verification job belongs to another GitHub account.",
      });
    }
    const result = await readE2BVerification(job.sandboxId, job.jobId);
    if (!result) {
      return noStore(200, {
        status: "running",
        submissionId: job.submissionId,
        proofDigest: job.proofDigest,
      });
    }
    assertE2BResultMatchesJob(job, result);
    if (result.status === "rejected") {
      await killE2BSandbox(job.sandboxId).catch(() => undefined);
      return noStore(200, result);
    }
    if (!isGitHubPromotionConfigured()) {
      return noStore(200, {
        ...result,
        promotion: {
          status: "awaiting-configuration",
          message: "The proof passed, but durable publication is not configured.",
        },
      });
    }
    try {
      const promotion = await promoteE2BResult(job, result);
      await killE2BSandbox(job.sandboxId).catch(() => undefined);
      return noStore(200, { ...result, promotion });
    } catch (error) {
      if (error instanceof PromotionRaceError) {
        await killE2BSandbox(job.sandboxId).catch(() => undefined);
        return noStore(200, {
          ...result,
          promotion: {
            status: "superseded",
            message: describePromotionError(error),
          },
        });
      }
      throw error;
    }
  } catch (error) {
    const { SandboxNotFoundError } = await import("e2b");
    if (error instanceof SandboxNotFoundError) {
      return noStore(410, {
        error: "job_expired",
        message: "This verification sandbox expired before a result was collected.",
      });
    }
    const message = error instanceof Error ? error.message : "Invalid verification job.";
    if (message.includes("token") || message.includes("signature")) {
      return noStore(400, { error: "invalid_job", message });
    }
    console.error("Unable to read E2B verification", error);
    return noStore(502, {
      error: "verifier_status_failed",
      message: "The isolated verifier status is temporarily unavailable.",
    });
  }
}
