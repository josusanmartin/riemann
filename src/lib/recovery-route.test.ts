import { readFileSync } from "node:fs";
import { afterEach, beforeEach, describe, expect, it, vi } from "vitest";
import { computeDirectProofDigest } from "./direct-submission";

const mocks = vi.hoisted(() => ({
  active: vi.fn(), metadata: vi.fn(), bundle: vi.fn(), stage: vi.fn(),
  replace: vi.fn(), kill: vi.fn(), run: vi.fn(),
}));
vi.mock("@/lib/e2b-verifier", () => ({
  killE2BSandbox: mocks.kill, readE2BSubmissionBundle: mocks.bundle,
}));
vi.mock("@/lib/e2b-queue", () => ({
  readQueuedE2BJobMetadata: mocks.metadata, stageE2BVerification: mocks.stage,
}));
vi.mock("@/lib/queue-orchestration", () => ({ ensureQueuedJobRunning: mocks.run }));
vi.mock("@/lib/submission-queue", async (original) => ({
  ...await original<typeof import("./submission-queue")>(),
  getActiveVerificationJob: mocks.active, replaceActiveVerificationJob: mocks.replace,
}));

import { QueueCommitUncertainError } from "./submission-queue";
import { POST } from "@/app/api/admin/e2b-recover/route";

const manifest = readFileSync("submissions/flow-test/submission.json", "utf8");
const solution = readFileSync("submissions/flow-test/proof/Solution.lean", "utf8");
const proofDigest = computeDirectProofDigest(manifest, solution);
const active = { sandboxId: "old-worker", jobId: "old-job", proofDigest };
const replacement = { sandboxId: "new-worker", jobId: "new-job", proofDigest };
const secret = "recovery-test-secret-".repeat(3);
const request = () => new Request("https://example.com/api/admin/e2b-recover", {
  method: "POST", headers: { Authorization: `Bearer ${secret}` },
});

beforeEach(() => {
  vi.resetAllMocks();
  vi.stubEnv("E2B_TEMPLATE_ADMIN_SECRET", secret);
  vi.stubEnv("VERCEL_GIT_COMMIT_SHA", undefined);
  vi.stubEnv("RIEMANN_BASE_COMMIT_SHA", "a".repeat(40));
  mocks.active.mockResolvedValue(active);
  mocks.metadata.mockResolvedValue(active);
  mocks.bundle.mockResolvedValue({ manifest, solution });
  mocks.stage.mockResolvedValue(replacement);
  mocks.replace.mockResolvedValue(replacement);
  mocks.kill.mockResolvedValue(undefined);
  mocks.run.mockResolvedValue("running");
});
afterEach(() => { vi.unstubAllEnvs(); vi.restoreAllMocks(); });

describe("operator recovery boundary", () => {
  it("supports exact-SHA CLI deployments and only kills the old worker after commit", async () => {
    expect((await POST(request())).status).toBe(202);
    expect(mocks.stage).toHaveBeenCalledWith(expect.objectContaining({ baseCommitSha: "a".repeat(40) }));
    expect(mocks.kill).toHaveBeenCalledExactlyOnceWith("old-worker");
    expect(mocks.replace.mock.invocationCallOrder[0]).toBeLessThan(mocks.kill.mock.invocationCallOrder[0]);
  });

  it("preserves both workers when the replacement commit acknowledgement is uncertain", async () => {
    mocks.replace.mockRejectedValue(new QueueCommitUncertainError());
    const response = await POST(request());
    expect(response.status).toBe(503);
    expect(await response.json()).toMatchObject({ error: "recovery_commit_uncertain" });
    expect(mocks.kill).not.toHaveBeenCalled();
    expect(mocks.run).not.toHaveBeenCalled();
  });

  it("cleans up an uncommitted replacement after an ordinary failure", async () => {
    vi.spyOn(console, "error").mockImplementation(() => {});
    mocks.replace.mockRejectedValue(new Error("queue changed before replacement"));
    expect((await POST(request())).status).toBe(502);
    expect(mocks.kill).toHaveBeenCalledExactlyOnceWith("new-worker");
  });
});
