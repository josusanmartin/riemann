import { afterEach, beforeEach, describe, expect, it, vi } from "vitest";
import { BoatError } from "./boat-worker";
import { kernelOomMessage } from "./verifier-feedback";
import { computeDirectProofDigest } from "./direct-submission";
import type { QueuedVerificationJob } from "./submission-queue";
import { ensureBoatWorker, reconcileBoat, reserveBoatJob, scheduleBoatSetup } from "./boat-queue";

const m = vi.hoisted(() => ({
  wait: vi.fn(), update: vi.fn(), claim: vi.fn(), find: vi.fn(), after: vi.fn(), active: vi.fn(),
  retry: vi.fn(),
  archive: vi.fn(),
  create: vi.fn(),
  upload: vi.fn(),
  result: vi.fn(),
  stop: vi.fn(),
  advance: vi.fn(),
  promote: vi.fn(),
  flow: vi.fn(), read: vi.fn(), identity: vi.fn(),
}));
vi.mock("node:timers/promises", () => ({ setTimeout: m.wait }));
vi.mock("next/server", () => ({ after: m.after }));
vi.mock("./submission-queue", () => ({ claimBoatSetup: m.claim, getActiveVerificationJob: m.active, updateBoatJob: m.update, retryBoatAfterOom: m.retry }));
vi.mock("./submission-archive-store", () => ({
  readSubmissionArchive: m.archive,
}));
vi.mock("./boat-worker", () => ({
  BoatIdentityMismatchError: class extends Error {},
  assertBoatWorkerIdentity: m.identity,
  BoatError: class extends Error { constructor(readonly status: number, readonly code: string) { super(code); } },
  findCompetitiveWorker: m.find,
  readBoatFile: m.read,
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
  m.claim.mockImplementation(async () => {
    const now = Date.now();
    if (job.boat!.uploaded || (job.boat!.retryAt ?? 0) > now) return { job, claimed: false };
    job = { ...job, boat: { ...job.boat!, startedAt: job.boat!.startedAt ?? now, setupLease: now, retryAt: now + 90_000 } };
    return { job, claimed: true };
  });
  m.update.mockImplementation(async (jobId, lease, update) => {
    expect(lease).toBe(job.boat!.setupLease);
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
    expect(m.claim).toHaveBeenCalledTimes(1);
    expect(m.update.mock.calls[0][2]).toMatchObject({ workerId: id, assignedAt: expect.any(Number) });
    expect(m.upload).toHaveBeenCalledExactlyOnceWith(
      id,
      manifest,
      solution,
      proofDigest,
      { jobId: job.jobId, kind: "competitive", sha: "a".repeat(40) },
      { jobId: job.jobId, token: expect.stringMatching(/^[0-9a-f]{64}$/) },
    );
    expect(job.boat?.uploaded).toBe(true);
  });
  it("records a setup expiry with its phase and last provider status", async () => {
    job.boat!.startedAt = Date.now() - 180_001;
    job.boat!.lastProviderStatus = 503;
    await reconcileBoat(job);
    expect(m.advance).toHaveBeenCalledWith(job.jobId, expect.objectContaining({
      feedback: expect.objectContaining({ stage: "infrastructure", retryable: true }),
    }), expect.stringContaining("HTTP 503"), expect.any(Number));
    expect(m.result).not.toHaveBeenCalled();
  });
  it("retries a temporary outage after admission without a browser poll", async () => {
    m.create.mockRejectedValueOnce(new BoatError(503, "fixture")).mockResolvedValue(id);
    m.wait.mockImplementation(async () => { job.boat!.retryAt = 0; job.boat!.startedAt = Date.now() - 10_000; });
    m.active.mockImplementation(async () => job);
    scheduleBoatSetup(job);
    expect(m.create).not.toHaveBeenCalled();
    await m.after.mock.calls[0][0]();
    expect(m.create).toHaveBeenCalledTimes(2);
    expect(m.create.mock.calls[0]).toEqual(m.create.mock.calls[1]);
    expect(job.boat?.uploaded).toBe(true);
  });
  it("adopts the original worker if the launch reply was lost", async () => {
    m.create.mockRejectedValueOnce(new TypeError("fetch failed"));
    await expect(reconcileBoat(job)).resolves.toMatchObject({ stage: "allocation", message: expect.stringContaining("Could not connect") });
    job.boat!.retryAt = 0;
    job.boat!.startedAt = Date.now() - 15_000;
    m.find.mockResolvedValue(id);
    expect((await ensureBoatWorker(job)).boat?.uploaded).toBe(true);
    expect(m.create).toHaveBeenCalledTimes(1);
  });
  it("records a definitive provider refusal without waiting for the deadline", async () => {
    m.create.mockRejectedValueOnce(new BoatError(402, "fixture"));
    expect((await reconcileBoat(job)).status).toBe("rejected");
    expect(m.advance).toHaveBeenCalledWith(job.jobId, expect.objectContaining({ message: "Boat declined worker setup." }),
      expect.stringContaining("402"), expect.any(Number));
    expect(m.upload).not.toHaveBeenCalled();
  });
  it("reports transfer while another caller owns staging and checks only after upload", async () => {
    Object.assign(job.boat!, { startedAt: Date.now(), workerId: id, assignedAt: Date.now(), retryAt: Date.now() + 90_000 });
    expect(await reconcileBoat(job)).toMatchObject({ stage: "staging" });
    expect(m.result).not.toHaveBeenCalled();
    job.boat!.uploaded = true;
    expect(await reconcileBoat(job)).toMatchObject({ stage: "checking", message: expect.stringContaining("compact RH proof") });
  });
  it("recovers a failed upload on the same worker", async () => {
    m.upload.mockRejectedValueOnce(new Error("network"));
    expect((await ensureBoatWorker(job)).boat?.uploaded).toBeUndefined();
    job.boat!.retryAt = 0;
    await ensureBoatWorker(job);
    expect(m.create).toHaveBeenCalledTimes(1);
    expect(m.upload).toHaveBeenCalledTimes(2);
  });
  it("recovers a staged proof after its last acknowledgement was lost", async () => {
    Object.assign(job.boat!, { startedAt: Date.now() - 181_000, assignedAt: Date.now() - 179_000, workerId: id });
    m.read.mockResolvedValue(proofDigest);
    expect((await ensureBoatWorker(job)).boat?.uploaded).toBe(true);
    expect(m.identity).toHaveBeenCalledWith(id, { jobId: job.jobId, kind: "competitive", sha: job.boat!.baseCommitSha });
    expect(m.advance).not.toHaveBeenCalled();
    expect(m.create).not.toHaveBeenCalled();
  });
  it("withholds source whose archive digest differs", async () => {
    m.archive.mockResolvedValue({
      payload: { manifest, solution: "changed", proofDigest },
    });
    expect((await ensureBoatWorker(job)).boat?.uploaded).toBeUndefined();
    expect(m.upload).not.toHaveBeenCalled();
  });
  it("records a rejection before stopping, without entering the promotion path", async () => {
    await ensureBoatWorker(job);
    m.result.mockResolvedValue({
      status: "rejected",
      submissionId: "candidate",
      proofDigest,
      log: "Finished with result: oom-kill",
      message: "Proof failed",
      completedAt: new Date().toISOString(),
    });
    await reconcileBoat(job);
    expect(m.advance).toHaveBeenCalledWith(
      job.jobId,
      expect.objectContaining({ outcome: "rejected" }),
      "Finished with result: oom-kill",
    );
    expect(m.retry).not.toHaveBeenCalled();
    expect(m.stop).toHaveBeenCalledWith(id);
    expect(m.promote).not.toHaveBeenCalled();
  });
  it("loads the admitted archive and caps a publication recovery at one standard worker", async () => {
    const originalId = "2358d6d0-79e1-4645-a0c0-cccce9a374aa";
    job.boat!.publicationReplayOf = originalId;
    await ensureBoatWorker(job);
    expect(m.archive).toHaveBeenCalledWith(originalId);
    expect(m.create.mock.calls.map(call => call[4])).toEqual([false]);
    m.result.mockResolvedValue({status:"rejected", submissionId:"candidate", proofDigest, log:"OOM",
      message:kernelOomMessage, completedAt:new Date().toISOString()});
    await reconcileBoat(job);
    expect(m.retry).not.toHaveBeenCalled();
    expect(m.stop).toHaveBeenCalledWith(id);
  });
  it("replays only a trusted OOM receipt, once, using the original archive", async () => {
    await ensureBoatWorker(job);
    const original = job;
    m.result.mockResolvedValue({
      status: "rejected",
      submissionId: "candidate",
      proofDigest,
      log: "diagnostic",
      message: kernelOomMessage,
      completedAt: new Date().toISOString(),
    });
    m.retry.mockImplementation(async (old, nextId) => {
      const boat = old.boat;
      job = {
        ...old,
        jobId: nextId,
        sandboxId: `boat-${nextId}`,
        boat: {
          baseCommitSha: boat.baseCommitSha,
          previousRecordId: boat.previousRecordId,
          issuedAt: boat.issuedAt,
          memoryReplayOf: old.jobId,
          retiredWorkerId: boat.workerId,
        },
      };
      return job;
    });
    const reply = await reconcileBoat(original);
    expect(reply.status).toBe("running");
    await m.after.mock.calls[0][0]();
    expect(m.create.mock.calls.map((call) => call[4])).toEqual([false, true]);
    expect(m.archive).toHaveBeenLastCalledWith(original.jobId);
    expect(m.advance).not.toHaveBeenCalled();
    await reconcileBoat(job);
    expect(m.retry).toHaveBeenCalledTimes(1);
    expect(m.advance).toHaveBeenCalledWith(
      job.jobId,
      expect.objectContaining({
        outcome: "rejected",
        feedback: expect.objectContaining({
          code: "verification-out-of-memory",
        }),
      }),
      "diagnostic",
    );
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
