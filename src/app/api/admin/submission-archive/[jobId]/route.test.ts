import { beforeEach, describe, expect, it, vi } from "vitest";

const mocks = vi.hoisted(() => ({
  getSession: vi.fn(),
  isSubmissionArchiveMaintainer: vi.fn(),
  readSubmissionArchive: vi.fn(),
}));

vi.mock("@/auth", () => ({ getSession: mocks.getSession }));
vi.mock("@/lib/submission-archive-store", () => ({
  isSubmissionArchiveMaintainer: mocks.isSubmissionArchiveMaintainer,
  readSubmissionArchive: mocks.readSubmissionArchive,
}));

import { GET } from "@/app/api/admin/submission-archive/[jobId]/route";

const jobId = "7e4f3b7e-3cb7-4f37-8328-69a685bc1808";

beforeEach(() => {
  vi.clearAllMocks();
  mocks.getSession.mockResolvedValue({
    user: { githubLogin: "josusanmartin" },
  });
  mocks.isSubmissionArchiveMaintainer.mockReturnValue(true);
  mocks.readSubmissionArchive.mockResolvedValue({
    payload: { proofDigest: "a".repeat(64), solution: "theorem retained : True := by trivial\n" },
    summary: { submission: { id: "retained-proof" } },
  });
});

describe("maintainer source archive route", () => {
  it("fails closed for a non-maintainer without touching the archive", async () => {
    mocks.isSubmissionArchiveMaintainer.mockReturnValue(false);
    const response = await GET(
      new Request(`https://www.riemannzeta.fun/api/admin/submission-archive/${jobId}`),
      { params: Promise.resolve({ jobId }) },
    );

    expect(response.status).toBe(404);
    expect(mocks.readSubmissionArchive).not.toHaveBeenCalled();
  });

  it("returns the exact source privately for an authenticated maintainer", async () => {
    const response = await GET(
      new Request(`https://www.riemannzeta.fun/api/admin/submission-archive/${jobId}`),
      { params: Promise.resolve({ jobId }) },
    );

    expect(response.status).toBe(200);
    await expect(response.text()).resolves.toBe(
      "theorem retained : True := by trivial\n",
    );
    expect(response.headers.get("cache-control")).toContain("no-store");
    expect(response.headers.get("content-disposition")).toBe(
      'inline; filename="retained-proof-Solution.lean"',
    );
    expect(response.headers.get("x-riemann-proof-digest")).toBe("a".repeat(64));
  });

  it("offers an attachment download without changing the source", async () => {
    const response = await GET(
      new Request(
        `https://www.riemannzeta.fun/api/admin/submission-archive/${jobId}?download=1`,
      ),
      { params: Promise.resolve({ jobId }) },
    );

    expect(response.headers.get("content-disposition")).toBe(
      'attachment; filename="retained-proof-Solution.lean"',
    );
  });
});
