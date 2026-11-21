import { afterEach, beforeEach, describe, expect, it, vi } from "vitest";
import { computeDirectProofDigest } from "./direct-submission";
import type { QueuedVerificationJob } from "./submission-queue";
import { ensureBoatWorker, reconcileBoat, reserveBoatJob } from "./boat-queue";

const m = vi.hoisted(() => ({
  update: vi.fn(),
  archive: vi.fn(),
  create: vi.fn(),
  upload: vi.fn(),
  result: vi.fn(),
  stop: vi.fn(),
  advance: vi.fn(),
  promote: vi.fn(),
  flow: vi.fn(),
}));
vi.mock("./submission-queue", () => ({ updateBoatJob: m.update }));
vi.mock("./submission-archive-store", () => ({
  readSubmissionArchive: m.archive,
}));
vi.mock("./boat-worker", () => ({
  activeBoatFlow: m.flow,
  createBoatWorker: m.create,
  stageBoatFiles: m.upload,
  boatResult: m.result,
  stopBoatWorker: m.stop,
  workerLifetime: 7200000,
}));
vi.mock("./queue-orchestration", () => ({
  advanceVerificationQueue: m.advance,
  VerifierOccupiedByFlowTestError: class extends Error {},
}));
vi.mock("./github-promotion", () => ({
  promoteVerifiedSubmission: m.promote,
  UnpublishableResultError: class extends Error {},
}));

const manifest = "test manifest",
  solution = "test proof";
const proofDigest = computeDirectProofDigest(manifest, solution);
const id = "bx_23456789";
let job: QueuedVerificationJob;
afterEach(() => vi.unstubAllEnvs());
beforeEach(() => {
  vi.stubEnv("AUTH_SECRET", "test-only-key");
  vi.resetAllMocks();
  job = {
    ...reserveBoatJob("a".repeat(40), "previous", Date.now()),
    proofDigest,
    ownerKey: "c".repeat(64),
    submissionKey: "d".repeat(64),
    enqueuedAt: new Date().toISOString(),
  };
  m.update.mockImplementation(async (jobId, update) => {
    expect(jobId).toBe(job.jobId);
    job = { ...job, boat: { ...job.boat!, ...update } };
    return job;
  });
  m.archive.mockResolvedValue({
    payload: { manifest, solution, proofDigest },
    summary: { submission: { id: "candidate" } },
  });
  m.create.mockResolvedValue(id);
  m.flow.mockResolvedValue(false);
  m.stop.mockResolvedValue(undefined);
});
describe("competitive Boat queue", () => {
  it("reserves the active job before provisioning, stages once and reuses the persisted worker", async () => {
    await ensureBoatWorker(job);
    await ensureBoatWorker(job);
    expect(m.create).toHaveBeenCalledTimes(1);
    expect(m.update.mock.calls[0][1]).toHaveProperty("startedAt");
    expect(m.update.mock.calls[1][1]).toEqual({ workerId: id });
    expect(m.upload).toHaveBeenCalledExactlyOnceWith(
      id,
      manifest,
      solution,
      proofDigest,
      { jobId: job.jobId, token: expect.stringMatching(/^[0-9a-f]{64}$/) },
    );
    expect(job.boat?.uploaded).toBe(true);
  });
  it("recovers a failed upload on the same worker", async () => {
    m.upload.mockRejectedValueOnce(new Error("network"));
    await expect(ensureBoatWorker(job)).rejects.toThrow("network");
    await ensureBoatWorker(job);
    expect(m.create).toHaveBeenCalledTimes(1);
    expect(m.upload).toHaveBeenCalledTimes(2);
  });
  it("withholds source whose archive digest differs", async () => {
    m.archive.mockResolvedValue({
      payload: { manifest, solution: "changed", proofDigest },
    });
    await expect(ensureBoatWorker(job)).rejects.toThrow("digest");
    expect(m.upload).not.toHaveBeenCalled();
  });
  it("records a rejection before stopping, without entering the promotion path", async () => {
    await ensureBoatWorker(job);
    m.result.mockResolvedValue({
      status: "rejected",
      submissionId: "candidate",
      proofDigest,
      log: "error",
      message: "Proof failed",
      completedAt: new Date().toISOString(),
    });
    await reconcileBoat(job);
    expect(m.advance).toHaveBeenCalledWith(
      job.jobId,
      expect.objectContaining({ outcome: "rejected" }),
      "error",
    );
    expect(m.stop).toHaveBeenCalledWith(id);
    expect(m.promote).not.toHaveBeenCalled();
  });
  it("requires the existing publication gate to accept the archived submission", async () => {
    await ensureBoatWorker(job);
    m.result.mockResolvedValue({
      status: "verified",
      submissionId: "candidate",
      proofDigest,
      log: "ok",
      completedAt: new Date().toISOString(),
    });
    m.promote.mockRejectedValue(new Error("attestation failed"));
    await expect(reconcileBoat(job)).rejects.toThrow("attestation failed");
    expect(m.advance).not.toHaveBeenCalled();
  });
});
