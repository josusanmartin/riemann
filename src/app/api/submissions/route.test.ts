import { beforeEach, afterEach, describe, expect, it, vi } from "vitest";

const mocks = vi.hoisted(() => ({
  session: vi.fn(), stage: vi.fn(), kill: vi.fn(), enqueue: vi.fn(), usage: vi.fn(), start: vi.fn(),
}));
vi.mock("@/auth", () => ({ getSession: mocks.session }));
vi.mock("@/lib/e2b-config", () => ({ isE2BConfigured: () => true }));
vi.mock("@/lib/e2b-queue", () => ({ stageE2BVerification: mocks.stage }));
vi.mock("@/lib/e2b-verifier", () => ({ killE2BSandbox: mocks.kill }));
vi.mock("@/lib/e2b-webhooks", () => ({ isE2BWebhookConfigured: () => true, ensureE2BWebhook: vi.fn() }));
vi.mock("@/lib/queue-orchestration", () => ({ applyInitialQueueTransition: mocks.start }));
vi.mock("@/lib/submission-queue", async (original) => ({
  ...await original<typeof import("@/lib/submission-queue")>(),
  isSubmissionQueueConfigured: () => true,
  enqueueVerificationJob: mocks.enqueue,
  getDailySubmissionUsage: mocks.usage,
}));
import { POST } from "./route";
import { QueueCommitUncertainError, DailySubmissionLimitError } from "@/lib/submission-queue";
import { VerifierTemplateMismatchError } from "@/lib/verifier-readiness";

const job = { jobId: "00000000-0000-4000-8000-000000000001", sandboxId: "sandbox-1234567890" };
const input = {
  id: "audit-proof", displayName: "Audit Solver", score: { numerator: "672500704", denominator: "1000000000" },
  summary: "An explicitly noncompetitive audit fixture.", method: "Audit fixture", solution: "-- source", acceptLicense: true,
};
function request(body: unknown = input) {
  return new Request("https://www.riemannzeta.fun/api/submissions", {
    method: "POST", headers: { "Content-Type": "application/json" }, body: JSON.stringify(body),
  });
}
beforeEach(() => {
  vi.clearAllMocks();
  vi.stubEnv("GITHUB_RECORDS_TOKEN", "test-token");
  vi.stubEnv("AUTH_SECRET", "test-auth-secret");
  vi.stubEnv("RIEMANN_BASE_COMMIT_SHA", "a".repeat(40));
  vi.stubEnv("VERCEL_GIT_COMMIT_SHA", "a".repeat(40));
  mocks.session.mockResolvedValue({ user: { githubLogin: "solver" } });
  mocks.stage.mockResolvedValue(job);
  mocks.kill.mockResolvedValue(undefined);
  mocks.usage.mockResolvedValue({ used: 0, limit: 3, retryAt: "2026-09-08T00:00:00.000Z" });
  mocks.enqueue.mockResolvedValue({ job, position: 0, dailyUsed: 1, dailyLimit: 3, shouldStart: true });
  mocks.start.mockResolvedValue(true);
});
afterEach(() => vi.unstubAllEnvs());

describe("official submission admission", () => {
  it("requires authentication before allocating any worker", async () => {
    mocks.session.mockResolvedValue(null);
    expect((await POST(request())).status).toBe(401);
    expect(mocks.stage).not.toHaveBeenCalled();
  });
  it("archives the exact submitted source before reporting admission", async () => {
    const response = await POST(request());
    expect(response.status).toBe(202);
    expect(mocks.enqueue).toHaveBeenCalledWith(expect.objectContaining(job), "solver", expect.objectContaining({ solution: input.solution }));
    expect(await response.json()).toMatchObject({ status: "running", dailyUsed: 1, dailyLimit: 3 });
  });
  it("does not allocate a worker for the fourth admitted upload", async () => {
    mocks.usage.mockResolvedValue({ used: 3, limit: 3, retryAt: "2026-09-08T00:00:00.000Z" });
    expect((await POST(request())).status).toBe(429);
    expect(mocks.stage).not.toHaveBeenCalled();
  });
  it("preserves the sandbox after an uncertain queue commit", async () => {
    mocks.enqueue.mockRejectedValueOnce(new QueueCommitUncertainError());
    const response = await POST(request());
    expect(response.status).toBe(503);
    expect(await response.json()).toMatchObject({ error: "queue_admission_uncertain" });
    expect(mocks.kill).not.toHaveBeenCalled();
  });
  it("cleans up a definitively rejected concurrent admission", async () => {
    mocks.enqueue.mockRejectedValueOnce(new DailySubmissionLimitError("2026-09-08T00:00:00.000Z"));
    expect((await POST(request())).status).toBe(429);
    expect(mocks.kill).toHaveBeenCalledWith(job.sandboxId);
  });
  it("rejects an incompatible image before queue admission", async () => {
    mocks.stage.mockRejectedValueOnce(new VerifierTemplateMismatchError());
    const response = await POST(request());
    expect(response.status).toBe(503);
    expect(await response.json()).toMatchObject({ error: "verifier_template_stale" });
    expect(mocks.enqueue).not.toHaveBeenCalled();
  });
  it("rejects oversized unannounced bodies and forged manifest fields", async () => {
    expect((await POST(request({ ...input, solution: "x".repeat(4_000_001) }))).status).toBe(413);
    expect((await POST(request({ ...input, author: { github: "someone-else" } }))).status).toBe(400);
    expect(mocks.stage).not.toHaveBeenCalled();
  });
});
