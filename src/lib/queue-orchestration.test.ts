import { describe, expect, it, vi } from "vitest";

const mocks = vi.hoisted(() => ({
  flowTestActive: vi.fn(),
  launch: vi.fn(),
}));

vi.mock("@/lib/e2b-flow-test", () => ({
  hasActiveE2BFlowTest: mocks.flowTestActive,
}));
vi.mock("@/lib/e2b-queue", () => ({
  launchQueuedE2BVerification: mocks.launch,
  pauseQueuedE2BVerification: vi.fn(),
}));

import {
  applyInitialQueueTransition,
  ensureQueuedJobRunning,
  VerifierOccupiedByFlowTestError,
} from "@/lib/queue-orchestration";
import type {
  QueueAdmission,
  QueueInspection,
  QueuedVerificationJob,
} from "@/lib/submission-queue";

const job: QueuedVerificationJob = {
  sandboxId: "sandbox-1234567890",
  jobId: "4d664a5f-65f8-40c9-a641-6bb9eb77ef6b",
  proofDigest: "a".repeat(64),
  ownerKey: "b".repeat(64),
  submissionKey: "c".repeat(64),
  enqueuedAt: "2026-08-13T12:00:00.000Z",
};

function admission(shouldStart: boolean): QueueAdmission {
  return {
    job,
    position: shouldStart ? 0 : 1,
    dailyUsed: 1,
    dailyLimit: 3,
    shouldStart,
  };
}

describe("initial verification queue transition", () => {
  it("reports running only after the active sandbox launch succeeds", async () => {
    const start = vi.fn(async () => undefined);
    const reconcile =
      vi.fn<(queued: QueuedVerificationJob) => Promise<QueueInspection>>();

    await expect(
      applyInitialQueueTransition(admission(true), { start, reconcile }),
    ).resolves.toBe(true);
    expect(start).toHaveBeenCalledWith(job);
    expect(reconcile).not.toHaveBeenCalled();
  });

  it("does not turn a failed active launch into a running response", async () => {
    const start = vi.fn(async () => {
      throw new Error("temporary E2B launch failure");
    });
    const reconcile =
      vi.fn<(queued: QueuedVerificationJob) => Promise<QueueInspection>>();

    await expect(
      applyInitialQueueTransition(admission(true), { start, reconcile }),
    ).rejects.toThrow("temporary E2B launch failure");
  });

  it("reports a waiting job as running only when reconciliation made it active", async () => {
    const start = vi.fn(async () => undefined);
    const queued = vi.fn(async (): Promise<QueueInspection> => ({
      status: "queued",
      position: 1,
      job,
    }));
    const active = vi.fn(async (): Promise<QueueInspection> => ({
      status: "active",
      position: 0,
      job,
    }));

    await expect(
      applyInitialQueueTransition(admission(false), {
        start,
        reconcile: queued,
      }),
    ).resolves.toBe(false);
    await expect(
      applyInitialQueueTransition(admission(false), {
        start,
        reconcile: active,
      }),
    ).resolves.toBe(true);
  });

  it("does not run a competitive proof beside an operator flow test", async () => {
    mocks.flowTestActive.mockResolvedValueOnce(true);

    await expect(ensureQueuedJobRunning(job)).rejects.toBeInstanceOf(
      VerifierOccupiedByFlowTestError,
    );
    expect(mocks.launch).not.toHaveBeenCalled();

    mocks.flowTestActive.mockResolvedValueOnce(false);
    mocks.launch.mockResolvedValueOnce("running");
    await expect(ensureQueuedJobRunning(job)).resolves.toBe("running");
    expect(mocks.launch).toHaveBeenCalledWith(job);
  });
});
