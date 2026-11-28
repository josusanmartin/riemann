import { createEmptyQueueState, historyOwnerKey } from "./submission-queue";
import { afterEach, describe, expect, it, vi } from "vitest";
import { computeDirectProofDigest } from "@/lib/direct-submission";
import {
  sealSubmissionArchive,
  sealVerifierLog, verifierLogPath,
  submissionArchivePath,
} from "@/lib/submission-archive";
import {
  isSubmissionArchiveMaintainer,
  listSubmissionArchive,
  readOwnerHistory,
  readVerificationDesk,
  readSubmissionArchive,
} from "@/lib/submission-archive-store";

const archiveKey = Buffer.alloc(32, 11).toString("base64");
const jobId = "7e4f3b7e-3cb7-4f37-8328-69a685bc1808";
const submittedAt = "2026-08-13T18:30:00.000Z";
const solution = "import Challenge\n\n-- exact retained source\n";
const manifest = `${JSON.stringify(
  {
    schemaVersion: 1,
    id: "store-proof",
    track: "critical-line",
    author: { github: "store-solver", displayName: "Store Solver" },
    score: { numerator: "672500704", denominator: "1000000000" },
    proof: {
      solution: "proof/Solution.lean",
      theorem: "candidate_critical_line_bound",
      cumulativeTheorem: "candidate_critical_line_bound_cumulative",
      improvementTheorem: "candidate_strict_improvement",
    },
    summary: "A complete formal source archive store integration test.",
    method: "Archive store integration test",
    model: null,
    harness: null,
    license: "Apache-2.0",
  },
  null,
  2,
)}\n`;
const proofDigest = computeDirectProofDigest(manifest, solution);
const envelope = sealSubmissionArchive(
  {
    schemaVersion: 1,
    jobId,
    proofDigest,
    submittedAt,
    manifest,
    solution,
  },
  archiveKey,
  Buffer.alloc(12, 13),
);
const path = submissionArchivePath(jobId, proofDigest, submittedAt);

function fakeArchiveGitHub(): typeof fetch {
  return async (request) => {
    const url = new URL(
      typeof request === "string" ? request : request.toString(),
    );
    const response = (value: unknown) =>
      new Response(JSON.stringify(value), {
        status: 200,
        headers: { "Content-Type": "application/json" },
      });
    if (url.pathname.endsWith("/git/ref/heads/automation-queue")) {
      return response({ object: { sha: "a".repeat(40) } });
    }
    if (url.pathname.endsWith(`/git/commits/${"a".repeat(40)}`)) {
      return response({ tree: { sha: "b".repeat(40) } });
    }
    if (url.pathname.endsWith(`/git/trees/${"b".repeat(40)}`)) {
      return response({
        truncated: false,
        tree: [
          { path: "runtime/submission-queue.json", type: "blob", sha: "c".repeat(40), size: 50 },
          { path, type: "blob", sha: "d".repeat(40), size: 900 },
        ],
      });
    }
    if (url.pathname.endsWith(`/git/blobs/${"d".repeat(40)}`)) {
      return response({
        encoding: "base64",
        content: Buffer.from(`${JSON.stringify(envelope)}\n`, "utf8").toString(
          "base64",
        ),
      });
    }
    return new Response("not found", { status: 404 });
  };
}

describe("maintainer submission archive store", () => {
  it("lists immutable metadata without downloading source blobs", async () => {
    let requests = 0;
    const underlying = fakeArchiveGitHub();
    const fetchImplementation: typeof fetch = async (...args) => {
      requests += 1;
      return underlying(...args);
    };
    await expect(
      listSubmissionArchive({ token: "test-token", fetchImplementation }),
    ).resolves.toEqual([
      {
        path,
        blobSha: "d".repeat(40),
        encryptedBytes: 900,
        jobId,
        proofDigest,
        submittedAt,
      },
    ]);
    expect(requests).toBe(3);
  });

  it("authenticates, decrypts, and rehashes one selected archive", async () => {
    await expect(
      readSubmissionArchive(jobId, {
        token: "test-token",
        archiveKey,
        fetchImplementation: fakeArchiveGitHub(),
      }),
    ).resolves.toMatchObject({
      payload: { jobId, proofDigest, submittedAt, manifest, solution },
      summary: {
        jobId,
        proofDigest,
        submittedAt,
        submission: { id: "store-proof", author: { github: "store-solver" } },
      },
    });
    expect(isSubmissionArchiveMaintainer("josusanmartin", "5554649")).toBe(true);
    expect(isSubmissionArchiveMaintainer("josusanmartin", "123")).toBe(false);
    expect(isSubmissionArchiveMaintainer("josusanmartin")).toBe(false);
    expect(isSubmissionArchiveMaintainer("another-user")).toBe(false);
  });
});

afterEach(() => vi.unstubAllEnvs());

it("exposes retained output only to the GitHub account that admitted the job", async () => {
  vi.stubEnv("AUTH_SECRET", "fixture-owner-key");
  const receipt = {
    jobId, proofDigest, completedAt: submittedAt, outcome: "rejected",
    promotionStatus: null, evidenceUrl: null, message: "Worker failed", logArchived: true,
  };
  const log = sealVerifierLog({ jobId, proofDigest, completedAt: submittedAt, log: "private diagnostic" }, archiveKey);
  const files = [
    { path: "runtime/submission-queue.json", value: createEmptyQueueState("2026-08-13") },
    { path: `runtime/history/${historyOwnerKey("store-solver")}/${submittedAt}_rejected_${proofDigest}_${jobId}.json`, value: receipt },
    { path: verifierLogPath(jobId), value: log },
  ].map((file, index) => ({ ...file, sha: String(index + 1).repeat(40), type: "blob" }));
  const fetchImplementation: typeof fetch = async (request) => {
    const url = String(request);
    if (url.includes("/git/ref/")) return Response.json({ object: { sha: "a".repeat(40) } });
    if (url.includes("/git/commits/")) return Response.json({ tree: { sha: "b".repeat(40) } });
    if (url.includes("/git/trees/")) return Response.json({ tree: files.map(({ path, sha, type }) => ({ path, sha, type })) });
    const file = files.find(entry => url.endsWith("/git/blobs/" + entry.sha));
    if (!file) throw new Error("Unexpected history request");
    return Response.json({ encoding: "base64", content: Buffer.from(JSON.stringify(file.value)).toString("base64") });
  };
  const options = { fetchImplementation, archiveKey, token: "fixture" };
  const desk = await readVerificationDesk("josusanmartin", "5554649", options);
  expect(desk.attempts).toMatchObject([{ jobId, digest: proofDigest, status: "rejected", hasLog: true }]);
  expect(JSON.stringify(desk)).not.toContain("private diagnostic");
  const own = await readOwnerHistory("Store-Solver", jobId, options);
  expect(own.detail?.logs.map(entry => entry.log)).toEqual(["private diagnostic"]);
  expect(await readOwnerHistory("another-solver", jobId, options)).toEqual({ active: [], completed: [], detail: null });
});

it("denies non-maintainers before reading the shared dashboard", async () => {
  const fetchImplementation = vi.fn();
  for (const [login, id] of [["solver", "123"], ["josusanmartin", "123"], ["josusanmartin", undefined]]) {
    await expect(readVerificationDesk(login!, id, { token: "fixture", fetchImplementation })).rejects.toThrow("Maintainer access required");
  }
  expect(fetchImplementation).not.toHaveBeenCalled();
});
