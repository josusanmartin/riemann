import { timingSafeEqual } from "node:crypto";
import {
  killE2BSandbox,
  listPausedE2BVerifications,
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

export const runtime = "nodejs";
export const maxDuration = 60;

function noStore(status: number, body: object): Response {
  return Response.json(body, {
    status,
    headers: { "Cache-Control": "no-store" },
  });
}

function authorized(request: Request): boolean {
  const secret = process.env.CRON_SECRET;
  const supplied = request.headers.get("authorization");
  if (!secret || !supplied) return false;
  const expected = Buffer.from(`Bearer ${secret}`, "utf8");
  const actual = Buffer.from(supplied, "utf8");
  return expected.length === actual.length && timingSafeEqual(expected, actual);
}

export async function GET(request: Request): Promise<Response> {
  if (!authorized(request)) return noStore(401, { error: "unauthorized" });
  if (!isGitHubPromotionConfigured()) {
    return noStore(503, { error: "promotion_not_configured" });
  }

  try {
    const [job] = await listPausedE2BVerifications(1);
    if (!job) return noStore(200, { status: "idle" });
    const result = await readE2BVerification(job.sandboxId, job.jobId);
    if (!result) {
      return noStore(503, {
        error: "result_not_ready",
        submissionId: job.submissionId,
        message: "The paused sandbox remains available for a later retry.",
      });
    }
    assertE2BResultMatchesJob(job, result);
    if (result.status === "rejected") {
      await killE2BSandbox(job.sandboxId).catch(() => undefined);
      return noStore(200, {
        status: "rejected-cleaned",
        submissionId: job.submissionId,
      });
    }
    try {
      const promotion = await promoteE2BResult(job, result);
      await killE2BSandbox(job.sandboxId).catch(() => undefined);
      return noStore(200, { status: "promoted", promotion });
    } catch (error) {
      if (error instanceof PromotionRaceError) {
        await killE2BSandbox(job.sandboxId).catch(() => undefined);
        return noStore(200, {
          status: "superseded",
          message: describePromotionError(error),
        });
      }
      throw error;
    }
  } catch (error) {
    console.error("Unable to sweep a paused E2B verification", error);
    return noStore(503, {
      error: "sweep_failed",
      message: "The paused verification remains available for a later retry.",
    });
  }
}
