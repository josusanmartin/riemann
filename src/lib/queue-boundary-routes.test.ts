import { afterEach, beforeEach, describe, expect, it, vi } from "vitest";

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
}));

vi.mock("@/auth", () => ({ getSession: mocks.getSession }));
vi.mock("@/lib/e2b-verifier", () => ({
  inspectE2BVerificationProgress: vi.fn(),
  killE2BSandbox: vi.fn(),
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
  advanceVerificationQueue: vi.fn(),
  assertQueueJobMatches: vi.fn(),
  ensureQueuedJobRunning: mocks.ensureQueuedJobRunning,
  reconcileQueuedJobPause: mocks.reconcileQueuedJobPause,
  VerifierOccupiedByFlowTestError: class extends Error {},
}));
vi.mock("@/lib/github-promotion", () => ({
  describePromotionError: vi.fn(),
  isGitHubPromotionConfigured: vi.fn(() => true),
  PromotionRaceError: class extends Error {},
}));
vi.mock("@/lib/submission-finalization", () => ({
  assertE2BResultMatchesJob: vi.fn(),
  promoteE2BResult: vi.fn(),
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
