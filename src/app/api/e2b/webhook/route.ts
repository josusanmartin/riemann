import {
  e2bWebhookEventSchema,
  verifyE2BWebhookSignature,
} from "@/lib/e2b-webhooks";
import {
  killE2BSandbox,
  readE2BVerification,
} from "@/lib/e2b-verifier";
import {
  describePromotionError,
  isGitHubPromotionConfigured,
  PromotionRaceError,
} from "@/lib/github-promotion";
import { e2bJobMetadataSchema } from "@/lib/submission-jobs";
import {
  assertE2BResultMatchesJob,
  promoteE2BResult,
  type VerificationJobCoordinates,
} from "@/lib/submission-finalization";
import {
  advanceVerificationQueue,
  assertQueueJobMatches,
  ensureQueuedJobRunning,
} from "@/lib/queue-orchestration";
import { inspectVerificationJob } from "@/lib/submission-queue";
import { describeVerifierRejection } from "@/lib/verifier-feedback";

export const runtime = "nodejs";
export const maxDuration = 60;

function noStore(status: number, body: object): Response {
  return Response.json(body, {
    status,
    headers: { "Cache-Control": "no-store" },
  });
}

export async function POST(request: Request): Promise<Response> {
  const contentLength = Number(request.headers.get("content-length") ?? "0");
  if (Number.isFinite(contentLength) && contentLength > 65_536) {
    return noStore(413, { error: "webhook_too_large" });
  }
  const rawBody = await request.text();
  if (Buffer.byteLength(rawBody, "utf8") > 65_536) {
    return noStore(413, { error: "webhook_too_large" });
  }
  if (
    !verifyE2BWebhookSignature(
      rawBody,
      request.headers.get("e2b-signature"),
      request.headers.get("e2b-signature-version"),
    )
  ) {
    return noStore(401, { error: "invalid_webhook_signature" });
  }

  try {
    const event = e2bWebhookEventSchema.parse(JSON.parse(rawBody));
    if (event.type !== "sandbox.lifecycle.paused") {
      return noStore(202, { status: "ignored", eventId: event.id });
    }
    const rawMetadata = event.event_data.sandbox_metadata;
    if (
      rawMetadata.app !== "riemann-fail" ||
      rawMetadata.kind !== "formal-verification"
    ) {
      return noStore(202, { status: "ignored", eventId: event.id });
    }
    const metadata = e2bJobMetadataSchema.parse(rawMetadata);
    const job: VerificationJobCoordinates = {
      sandboxId: event.sandbox_id,
      jobId: metadata.job,
      submissionId: metadata.submission,
      github: metadata.github,
      proofDigest: metadata.proofDigest,
      baseCommitSha: metadata.baseCommitSha,
      previousRecordId: metadata.previousRecordId,
      issuedAt: Number(metadata.issuedAt),
    };
    const queue = await inspectVerificationJob(job.jobId);
    if (queue.status === "completed") {
      return noStore(200, {
        status: "already-processed",
        outcome: queue.receipt.outcome,
        submissionId: job.submissionId,
      });
    }
    if (queue.status === "queued") {
      assertQueueJobMatches(queue.job, job);
      return noStore(202, {
        status: "queued",
        queuePosition: queue.position,
        submissionId: job.submissionId,
      });
    }
    const queueManaged = queue.status === "active";
    if (queue.status === "active") {
      assertQueueJobMatches(queue.job, job);
      await ensureQueuedJobRunning(queue.job);
    }
    const result = await readE2BVerification(job.sandboxId, job.jobId);
    if (!result) {
      return noStore(503, {
        error: "result_not_ready",
        submissionId: job.submissionId,
        message: "The paused sandbox result is not readable yet; retry this event.",
      });
    }
    assertE2BResultMatchesJob(job, result);
    if (result.status === "rejected") {
      const feedback = describeVerifierRejection(result.log, result.message);
      if (queueManaged) {
        await advanceVerificationQueue(job.jobId, {
          outcome: "rejected",
          promotionStatus: null,
          message: feedback.detail,
          feedback,
          evidenceUrl: null,
          completedAt: result.completedAt,
        });
      }
      await killE2BSandbox(job.sandboxId).catch(() => undefined);
      return noStore(200, {
        status: "rejected-cleaned",
        submissionId: job.submissionId,
        feedbackCode: feedback.code,
      });
    }
    if (!isGitHubPromotionConfigured()) {
      return noStore(503, { error: "promotion_not_configured" });
    }
    try {
      const promotion = await promoteE2BResult(job, result);
      if (queueManaged) {
        await advanceVerificationQueue(job.jobId, {
          outcome: "promoted",
          promotionStatus: promotion.status,
          message: null,
          evidenceUrl: promotion.evidenceUrl,
          completedAt: result.completedAt,
        });
      }
      await killE2BSandbox(job.sandboxId).catch(() => undefined);
      return noStore(200, { status: "promoted", promotion });
    } catch (error) {
      if (error instanceof PromotionRaceError) {
        const message = describePromotionError(error);
        if (queueManaged) {
          await advanceVerificationQueue(job.jobId, {
            outcome: "superseded",
            promotionStatus: null,
            message,
            evidenceUrl: null,
            completedAt: result.completedAt,
          });
        }
        await killE2BSandbox(job.sandboxId).catch(() => undefined);
        return noStore(200, {
          status: "superseded",
          message,
        });
      }
      throw error;
    }
  } catch (error) {
    console.error("Unable to process E2B lifecycle webhook", error);
    return noStore(503, {
      error: "webhook_processing_failed",
      message: "The verifier event will be retried.",
    });
  }
}
