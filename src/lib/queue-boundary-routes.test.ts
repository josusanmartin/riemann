import { afterEach, beforeEach, describe, expect, it, vi } from "vitest";
import { SandboxNotFoundError } from "e2b";

vi.mock("e2b", () => ({ SandboxNotFoundError: class extends Error {} }));

const mocks = vi.hoisted(() => ({
  getSession: vi.fn(),
  ensureQueuedJobRunning: vi.fn(),
  reconcileQueuedJobPause: vi.fn(),
  inspectVerificationJob: vi.fn(),
  getActiveVerificationJob: vi.fn(),
  readE2BVerification: vi.fn(),
  readQueuedE2BJobMetadata: vi.fn(),
  verifySubmissionJob: vi.fn(),
  verifyE2BWebhookSignature: vi.fn(),
  advanceVerificationQueue: vi.fn(),
  promoteE2BResult: vi.fn(),
  readVerifierLog: vi.fn(),
}));
vi.mock("@/lib/submission-archive-store", () => ({ readVerifierLog: mocks.readVerifierLog }));
const promotionErrors = vi.hoisted(() => {
  class UnpublishableResultError extends Error {}
  class PromotionRaceError extends UnpublishableResultError {}
  return { UnpublishableResultError, PromotionRaceError };
});

vi.mock("@/auth", () => ({ getSession: mocks.getSession }));
vi.mock("@/lib/e2b-verifier", () => ({
  inspectE2BVerificationProgress: vi.fn(),
  killE2BSandbox: vi.fn(async () => undefined),
  readE2BVerification: mocks.readE2BVerification,
}));
vi.mock("@/lib/e2b-queue", () => ({
  readQueuedE2BJobMetadata: mocks.readQueuedE2BJobMetadata,
}));
vi.mock("@/lib/e2b-webhooks", async (importOriginal) => {
  const original = await importOriginal<typeof import("@/lib/e2b-webhooks")>();
  return {
    ...original,
    verifyE2BWebhookSignature: mocks.verifyE2BWebhookSignature,
  };
});
vi.mock("@/lib/submission-jobs", async (importOriginal) => {
  const original = await importOriginal<typeof import("@/lib/submission-jobs")>();
  return { ...original, verifySubmissionJob: mocks.verifySubmissionJob };
});
vi.mock("@/lib/submission-queue", () => ({
  getActiveVerificationJob: mocks.getActiveVerificationJob,
  inspectVerificationJob: mocks.inspectVerificationJob,
}));
vi.mock("@/lib/queue-orchestration", () => ({
  advanceVerificationQueue: mocks.advanceVerificationQueue,
  assertQueueJobMatches: vi.fn(),
  ensureQueuedJobRunning: mocks.ensureQueuedJobRunning,
  reconcileQueuedJobPause: mocks.reconcileQueuedJobPause,
  VerifierOccupiedByFlowTestError: class extends Error {},
}));
vi.mock("@/lib/github-promotion", () => ({
  ...promotionErrors,
  describePromotionError: vi.fn((error: Error) => error.message),
  isGitHubPromotionConfigured: vi.fn(() => true),
}));
vi.mock("@/lib/submission-finalization", () => ({
  assertE2BResultMatchesJob: vi.fn(),
  promoteE2BResult: mocks.promoteE2BResult,
}));

import { GET as statusRequest } from "@/app/api/submissions/status/route";
import { POST as webhookRequest } from "@/app/api/e2b/webhook/route";
import { GET as sweepRequest } from "@/app/api/e2b/sweep/route";

const job = {
  schemaVersion: 1 as const,
  sandboxId: "sandbox-1234567890",
  jobId: "4d664a5f-65f8-40c9-a641-6bb9eb77ef6b",
  submissionId: "durable-proof",
  github: "actual-solver",
  proofDigest: "a".repeat(64),
  baseCommitSha: "b".repeat(40),
  previousRecordId: "current-record",
  issuedAt: Date.parse("2026-08-13T12:00:00.000Z"),
  expiresAt: Date.parse("2026-08-20T12:00:00.000Z"),
};

const originalAuthSecret = process.env.AUTH_SECRET;
const originalCronSecret = process.env.CRON_SECRET;

beforeEach(() => {
  vi.clearAllMocks();
  process.env.AUTH_SECRET = "test-auth-secret";
  process.env.CRON_SECRET = "test-cron-secret";
  mocks.getSession.mockResolvedValue({
    user: { githubLogin: job.github, name: "Actual Solver" },
  });
  mocks.verifySubmissionJob.mockReturnValue(job);
  mocks.verifyE2BWebhookSignature.mockReturnValue(true);
  mocks.inspectVerificationJob.mockResolvedValue({ status: "missing" });
  mocks.getActiveVerificationJob.mockResolvedValue(null);
  mocks.ensureQueuedJobRunning.mockResolvedValue("running");
});

afterEach(() => {
  if (originalAuthSecret === undefined) delete process.env.AUTH_SECRET;
  else process.env.AUTH_SECRET = originalAuthSecret;
  if (originalCronSecret === undefined) delete process.env.CRON_SECRET;
  else process.env.CRON_SECRET = originalCronSecret;
});

describe("durable queue finalization boundary", () => {
  it("returns the durable verdict when another poll already removed the sandbox", async () => {
    mocks.inspectVerificationJob
      .mockResolvedValueOnce({ status: "active", position: 0, job })
      .mockResolvedValueOnce({
        status: "completed",
        receipt: {
          jobId: job.jobId, proofDigest: job.proofDigest,
          outcome: "promoted", promotionStatus: "promoted", message: null,
          evidenceUrl: "https://github.com/josusanmartin/riemann", completedAt: "2026-08-13T12:30:00Z",
        },
      });
    mocks.ensureQueuedJobRunning.mockRejectedValueOnce(new SandboxNotFoundError("Already finalized"));
    const response = await statusRequest(new Request("https://www.riemannzeta.fun/api/submissions/status?job=token"));
    expect(response.status).toBe(200);
    expect(await response.json()).toMatchObject({ status: "verified", promotion: { status: "promoted" } });
  });

  it("returns the retained log with a finished job's verdict", async () => {
    mocks.inspectVerificationJob.mockResolvedValue({
      status: "completed",
      receipt: {
        jobId: job.jobId, proofDigest: job.proofDigest,
        outcome: "rejected", promotionStatus: null, message: "Lean could not elaborate",
        evidenceUrl: null, completedAt: "2026-08-13T12:30:00Z", logArchived: true,
      },
    });
    mocks.readVerifierLog.mockResolvedValue({ jobId: job.jobId, proofDigest: job.proofDigest, omittedBytes: 0, log: "error: boom\n" });

    const response = await statusRequest(new Request("https://www.riemannzeta.fun/api/submissions/status?job=token"));

    expect(response.status).toBe(200);
    await expect(response.json()).resolves.toMatchObject({ status: "rejected", log: "error: boom\n" });
    expect(mocks.readVerifierLog).toHaveBeenCalledWith(job.jobId, job.proofDigest);

    // An unreadable log never hides the verdict.
    mocks.readVerifierLog.mockRejectedValue(new Error("GitHub unavailable"));
    vi.spyOn(console, "error").mockImplementation(() => undefined);
    const degraded = await statusRequest(new Request("https://www.riemannzeta.fun/api/submissions/status?job=token"));
    expect(degraded.status).toBe(200);
    const body = await degraded.json();
    expect(body).toMatchObject({ status: "rejected" });
    expect(body.log).toBeUndefined();
  });

  it("closes the job when a verified result can never be published", async () => {
    mocks.inspectVerificationJob.mockResolvedValue({ status: "active", position: 0, job });
    mocks.ensureQueuedJobRunning.mockResolvedValue("paused");
    mocks.readE2BVerification.mockResolvedValue({
      status: "verified",
      submissionId: job.submissionId,
      proofDigest: job.proofDigest,
      completedAt: "2026-08-13T12:30:00Z",
      log: "Lean and nanoda accepted the solution\n",
    });
    mocks.promoteE2BResult.mockRejectedValue(
      new promotionErrors.UnpublishableResultError("Verifier template is stale"),
    );

    const response = await statusRequest(
      new Request("https://www.riemannzeta.fun/api/submissions/status?job=token"),
    );

    expect(response.status).toBe(200);
    await expect(response.json()).resolves.toMatchObject({
      promotion: { status: "superseded", message: "Verifier template is stale" },
    });
    expect(mocks.advanceVerificationQueue).toHaveBeenCalledWith(
      job.jobId,
      expect.objectContaining({ outcome: "superseded" }),
      "Lean and nanoda accepted the solution\n",
    );
  });

  it("follows an admin recovery alias only to the same submitter's same proof", async () => {
    const recovered = {
      ...job,
      sandboxId: "sandbox-recovered-01",
      jobId: "7d664a5f-65f8-40c9-a641-6bb9eb77ef6b",
    };
    mocks.inspectVerificationJob.mockResolvedValue({
      status: "active",
      position: 0,
      job: recovered,
    });
    mocks.readQueuedE2BJobMetadata.mockResolvedValue({ ...recovered, state: "running" });

    const response = await statusRequest(
      new Request("https://www.riemannzeta.fun/api/submissions/status?job=token"),
    );
    expect(response.status).toBe(200);
    await expect(response.json()).resolves.toMatchObject({ status: "running" });
    expect(mocks.readQueuedE2BJobMetadata).toHaveBeenCalledWith(recovered.sandboxId);

    mocks.readQueuedE2BJobMetadata.mockResolvedValue({
      ...recovered,
      proofDigest: "f".repeat(64),
      state: "running",
    });
    const mismatch = await statusRequest(
      new Request("https://www.riemannzeta.fun/api/submissions/status?job=token"),
    );
    expect(mismatch.status).not.toBe(200);
  });

  it("observes a waiting job without repeatedly pausing or launching it", async () => {
    mocks.inspectVerificationJob.mockResolvedValue({
      status: "queued",
      position: 2,
      job,
    });

    const response = await statusRequest(
      new Request("https://www.riemannzeta.fun/api/submissions/status?job=token"),
    );

    expect(response.status).toBe(200);
    await expect(response.json()).resolves.toMatchObject({
      status: "queued",
      queuePosition: 2,
    });
    expect(mocks.reconcileQueuedJobPause).not.toHaveBeenCalled();
    expect(mocks.ensureQueuedJobRunning).not.toHaveBeenCalled();
    expect(mocks.readE2BVerification).not.toHaveBeenCalled();
  });

  it("returns a running heartbeat without reopening a result file", async () => {
    mocks.inspectVerificationJob.mockResolvedValue({
      status: "active",
      position: 0,
      job,
    });

    const response = await statusRequest(
      new Request("https://www.riemannzeta.fun/api/submissions/status?job=token"),
    );

    expect(response.status).toBe(200);
    await expect(response.json()).resolves.toMatchObject({ status: "running" });
    expect(mocks.ensureQueuedJobRunning).toHaveBeenCalledOnce();
    expect(mocks.readE2BVerification).not.toHaveBeenCalled();
  });

  it("does not let a signed but unadmitted status token reach E2B", async () => {
    const response = await statusRequest(
      new Request("https://www.riemannzeta.fun/api/submissions/status?job=token"),
    );

    expect(response.status).toBe(410);
    await expect(response.json()).resolves.toMatchObject({
      error: "job_not_admitted",
    });
    expect(mocks.readE2BVerification).not.toHaveBeenCalled();
  });

  it("ignores a valid E2B event whose job was never durably admitted", async () => {
    const body = JSON.stringify({
      id: "event-1",
      version: "v2",
      type: "sandbox.lifecycle.paused",
      timestamp: "2026-08-13T12:30:00Z",
      event_data: {
        sandbox_metadata: {
          app: "riemann-fail",
          kind: "formal-verification",
          github: job.github,
          submission: job.submissionId,
          job: job.jobId,
          proofDigest: job.proofDigest,
          baseCommitSha: job.baseCommitSha,
          previousRecordId: job.previousRecordId,
          issuedAt: String(job.issuedAt),
        },
      },
      sandbox_id: job.sandboxId,
      sandbox_template_id: "riemann-fail-verifier:immutable-build",
    });
    const response = await webhookRequest(
      new Request("https://www.riemannzeta.fun/api/e2b/webhook", {
        method: "POST",
        body,
        headers: {
          "Content-Type": "application/json",
          "e2b-signature": "valid",
          "e2b-signature-version": "v1",
        },
      }),
    );

    expect(response.status).toBe(202);
    await expect(response.json()).resolves.toMatchObject({ status: "untracked" });
    expect(mocks.readE2BVerification).not.toHaveBeenCalled();
  });

  it("does not discover and promote paused sandboxes outside the FIFO", async () => {
    const response = await sweepRequest(
      new Request("https://www.riemannzeta.fun/api/e2b/sweep", {
        headers: { Authorization: "Bearer test-cron-secret" },
      }),
    );

    expect(response.status).toBe(200);
    await expect(response.json()).resolves.toEqual({ status: "idle" });
    expect(mocks.readQueuedE2BJobMetadata).not.toHaveBeenCalled();
    expect(mocks.readE2BVerification).not.toHaveBeenCalled();
  });
});
