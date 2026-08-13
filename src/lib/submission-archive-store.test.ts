import { describe, expect, it } from "vitest";
import { computeDirectProofDigest } from "@/lib/direct-submission";
import {
  sealSubmissionArchive,
  submissionArchivePath,
} from "@/lib/submission-archive";
import {
  isSubmissionArchiveMaintainer,
  listSubmissionArchive,
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
    expect(isSubmissionArchiveMaintainer("josusanmartin")).toBe(true);
    expect(isSubmissionArchiveMaintainer("another-user")).toBe(false);
  });
});
