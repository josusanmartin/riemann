import { createHash, randomBytes } from "node:crypto";
import { approveCli, cliBearerPrefix } from "@/lib/cli-login";
import { beforeEach, afterEach, describe, expect, it, vi } from "vitest";

const mocks = vi.hoisted(() => ({
  published: vi.fn(), session: vi.fn(), stage: vi.fn(), pinned: vi.fn(), enqueue: vi.fn(), usage: vi.fn(), start: vi.fn(),
}));
vi.mock("@/auth", () => ({ getSession: mocks.session }));
vi.mock("@/lib/compact-runtime", () => ({ compactRuntimePinned: mocks.pinned }));
vi.mock("@/lib/boat-queue", () => ({ reserveBoatJob: mocks.stage }));
vi.mock("@/lib/queue-orchestration", () => ({ applyInitialQueueTransition: mocks.start }));
vi.mock("@/lib/submission-queue", async (original) => ({
  ...await original<typeof import("@/lib/submission-queue")>(),
  isSubmissionQueueConfigured: () => true,
  enqueueVerificationJob: mocks.enqueue,
  readPublishedRecordId: mocks.published,
  getDailySubmissionUsage: mocks.usage,
}));
import { POST } from "./route";
import { QueueCommitUncertainError, DailySubmissionLimitError } from "@/lib/submission-queue";
import { competitionIncumbent, type CompetitionTrack } from "@/lib/challenge";
import { getCurrentRecord, records } from "@/lib/records";

const job = { jobId: "00000000-0000-4000-8000-000000000001", sandboxId: "sandbox-1234567890" };
// Production promotions append to data/records.json, so derive a score that
// strictly beats the current record instead of hardcoding one that goes stale.
const currentRational = getCurrentRecord().exactRational;
const score = currentRational
  ? {
    numerator: (BigInt(currentRational.numerator) * 10n + 1n).toString(),
    denominator: (BigInt(currentRational.denominator) * 10n).toString(),
  }
  : { numerator: "672500704", denominator: "1000000000" };
const input = {
  id: "audit-proof", displayName: "Audit Solver", score,
  summary: "An explicitly noncompetitive audit fixture.", method: "Audit fixture", solution: "-- source", acceptLicense: true,
};
function request(body: unknown = input, query = "") {
  return new Request("https://www.riemannzeta.fun/api/submissions" + query, {
    method: "POST", headers: { "Content-Type": "application/json" }, body: JSON.stringify(body),
  });
}
beforeEach(() => {
  vi.clearAllMocks();
  vi.stubEnv("GITHUB_RECORDS_TOKEN", "test-token");
  vi.stubEnv("AUTH_SECRET", "test-auth-secret");
  vi.stubEnv("RIEMANN_BASE_COMMIT_SHA", "a".repeat(40));
  vi.stubEnv("VERCEL_GIT_COMMIT_SHA", "a".repeat(40));
  mocks.session.mockResolvedValue({ user: { githubLogin: "solver", githubId: "123" } });
  vi.stubEnv("RIEMANN_VERIFIER_PROVIDER", "boat");
  vi.stubEnv("RIEMANN_BOAT_API_KEY", "test-key");
  mocks.stage.mockReturnValue(job);
  mocks.pinned.mockReturnValue(true);
  mocks.published.mockImplementation(async (_options, track: CompetitionTrack) => competitionIncumbent(records, track).id);
  mocks.usage.mockResolvedValue({ used: 4, limit: 5, retryAt: "2026-09-08T00:00:00.000Z" });
  mocks.enqueue.mockResolvedValue({ job, position: 0, dailyUsed: 5, dailyLimit: 5, shouldStart: true });
  mocks.start.mockResolvedValue(true);
});
afterEach(() => vi.unstubAllEnvs());

describe("official submission admission", () => {
  it("refuses uploads while an operator has paused submissions", async () => {
    vi.stubEnv("SUBMISSIONS_PAUSED", "1");
    vi.stubEnv("SITE_NOTICE", "Verifier upgrade in progress.");
    const response = await POST(request());
    expect(response.status).toBe(503);
    expect(await response.json()).toMatchObject({
      error: "submissions_paused",
      message: "Verifier upgrade in progress.",
    });
    expect(mocks.usage).not.toHaveBeenCalled();
    expect(mocks.stage).not.toHaveBeenCalled();
  });
  it("requires authentication before allocating any worker", async () => {
    mocks.session.mockResolvedValue(null);
    expect((await POST(request())).status).toBe(401);
    expect(mocks.stage).not.toHaveBeenCalled();
  });
  it("admits a browser-approved CLI session under its immutable account ID", async () => {
    const verifier = randomBytes(32).toString("base64url");
    const challenge = createHash("sha256").update(verifier).digest("base64url");
    const approval = await approveCli({ challenge, until: String(Date.now() + 600000) }, {
      githubId: "456", githubLogin: "cli-solver",
    });
    const req = request();
    req.headers.set("Authorization", cliBearerPrefix + verifier + "~" + approval);
    expect((await POST(req)).status).toBe(202);
    expect(mocks.enqueue).toHaveBeenCalledWith(expect.anything(), "cli-solver", expect.anything(), { githubId: "456" });
    expect(mocks.session).not.toHaveBeenCalled();
  });
  it("archives the exact submitted source before reporting admission", async () => {
    const response = await POST(request());
    expect(response.status).toBe(202);
    expect(mocks.enqueue).toHaveBeenCalledWith(expect.objectContaining(job), "solver", expect.objectContaining({ solution: input.solution }), { githubId: "123" });
    expect(await response.json()).toMatchObject({ status: "running", dailyUsed: 5, dailyLimit: 5 });
  });
  it("does not allocate a worker for the sixth upload", async () => {
    mocks.usage.mockResolvedValue({ used: 5, limit: 5, retryAt: "2026-09-08T00:00:00.000Z" });
    expect((await POST(request())).status).toBe(429);
    expect(mocks.stage).not.toHaveBeenCalled();
  });
  it("leaves an uncertain queue commit to recovery", async () => {
    mocks.enqueue.mockRejectedValueOnce(new QueueCommitUncertainError());
    const response = await POST(request());
    expect(response.status).toBe(503);
    expect(await response.json()).toMatchObject({ error: "queue_admission_uncertain" });
    expect(mocks.start).not.toHaveBeenCalled();
  });
  it("returns the quota error without starting a worker on a concurrent admission", async () => {
    mocks.enqueue.mockRejectedValueOnce(new DailySubmissionLimitError("2026-09-08T00:00:00.000Z", 5));
    expect((await POST(request())).status).toBe(429);
    expect(mocks.start).not.toHaveBeenCalled();
  });
  it("rejects a missing runtime pin before queue admission", async () => {
    mocks.pinned.mockReturnValue(false);
    const response = await POST(request());
    expect(response.status).toBe(503);
    expect(await response.json()).toMatchObject({ error: "verifier_unavailable" });
    expect(mocks.enqueue).not.toHaveBeenCalled();
  });
  it("names each invalid input field without echoing the uploaded source", async () => {
    const response = await POST(request({ ...input, solution: "private fixture", summary: "tiny", score: { numerator: 42, denominator: "0" } }));
    const body = await response.json();
    expect(response.status).toBe(400);
    expect(body.issues.map((issue: { field: string }) => issue.field).sort()).toEqual(["score.denominator", "score.numerator", "summary"]);
    expect(body.message).not.toContain("private fixture");
    expect(mocks.enqueue).not.toHaveBeenCalled();
  });
  it("uses no slot when a record was published during deployment", async () => {
    mocks.published.mockResolvedValueOnce("new-record");
    const response = await POST(request());
    expect(response.status).toBe(409);
    expect(await response.json()).toMatchObject({ error: "record_changed", currentRecordId: "new-record" });
    expect(mocks.enqueue).not.toHaveBeenCalled();
    expect(mocks.stage).not.toHaveBeenCalled();
  });
  it("archives the selected simple-zero target and uses the shared quota", async () => {
    const response = await POST(request(input, "?track=simple-zeros"));
    expect(response.ok).toBe(true);
    const [job, , archive] = mocks.enqueue.mock.calls[0];
    expect(job.boat.track).toBe("simple-zeros");
    expect(JSON.parse(archive.manifest).track).toBe("simple-zeros");
    expect(mocks.usage).toHaveBeenCalledWith("solver", { githubId: "123" });
  });
  it("rejects an unknown target before queue admission", async () => {
    expect((await POST(request(input, "?track=typo"))).status).toBe(400);
    expect(mocks.enqueue).not.toHaveBeenCalled();
  });
  it("rejects oversized unannounced bodies and forged manifest fields", async () => {
    expect((await POST(request({ ...input, solution: "x".repeat(4_000_001) }))).status).toBe(413);
    expect((await POST(request({ ...input, author: { github: "someone-else" } }))).status).toBe(400);
    expect(mocks.stage).not.toHaveBeenCalled();
  });
});
