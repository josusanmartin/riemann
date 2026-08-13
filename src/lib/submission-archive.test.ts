import { describe, expect, it } from "vitest";
import { computeDirectProofDigest } from "@/lib/direct-submission";
import {
  openSubmissionArchive,
  parseSubmissionArchivePath,
  sealSubmissionArchive,
  submissionArchivePath,
  summarizeSubmissionArchive,
} from "@/lib/submission-archive";

const archiveKey = Buffer.alloc(32, 7).toString("base64");
const manifest = `${JSON.stringify(
  {
    schemaVersion: 1,
    id: "archived-proof",
    track: "critical-line",
    author: { github: "example-solver", displayName: "Example Solver" },
    score: { numerator: "672500704", denominator: "1000000000" },
    proof: {
      solution: "proof/Solution.lean",
      theorem: "candidate_critical_line_bound",
      cumulativeTheorem: "candidate_critical_line_bound_cumulative",
      improvementTheorem: "candidate_strict_improvement",
    },
    summary: "A complete formal proof submitted for archive testing.",
    method: "Archive round-trip test",
    model: null,
    harness: null,
    license: "Apache-2.0",
  },
  null,
  2,
)}\n`;
const solution = "import Challenge\n\ntheorem example : True := by trivial\n";
const jobId = "c66df896-f127-4875-9192-17e905fdcf53";
const submittedAt = "2026-08-13T17:00:00.000Z";
const proofDigest = computeDirectProofDigest(manifest, solution);

describe("encrypted submission archive", () => {
  it("round-trips and summarizes an exact source bundle", () => {
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
      Buffer.alloc(12, 3),
    );

    expect(JSON.stringify(envelope)).not.toContain(solution);
    expect(envelope).toMatchObject({
      schemaVersion: 1,
      algorithm: "aes-256-gcm",
      compression: "gzip",
      jobId,
      proofDigest,
      createdAt: submittedAt,
    });
    const opened = openSubmissionArchive(envelope, archiveKey);
    expect(opened).toEqual({
      schemaVersion: 1,
      jobId,
      proofDigest,
      submittedAt,
      manifest,
      solution,
    });
    expect(summarizeSubmissionArchive(opened)).toMatchObject({
      jobId,
      proofDigest,
      submittedAt,
      sourceBytes: Buffer.byteLength(solution),
      submission: { id: "archived-proof", author: { github: "example-solver" } },
    });
    const path = submissionArchivePath(jobId, proofDigest, submittedAt);
    expect(path).toBe(
      `runtime/submission-archive/2026-08-13/${Date.parse(submittedAt)}-${jobId}-${proofDigest}.json`,
    );
    expect(parseSubmissionArchivePath(path)).toEqual({
      path,
      jobId,
      proofDigest,
      submittedAt,
    });
    expect(parseSubmissionArchivePath("runtime/submission-archive/not-valid.json")).toBeNull();
  });

  it("rejects ciphertext or metadata tampering", () => {
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
      Buffer.alloc(12, 5),
    );
    const ciphertext = Buffer.from(envelope.ciphertext, "base64");
    ciphertext[0] ^= 1;
    expect(() =>
      openSubmissionArchive(
        { ...envelope, ciphertext: ciphertext.toString("base64") },
        archiveKey,
      ),
    ).toThrow();
    expect(() =>
      openSubmissionArchive({ ...envelope, proofDigest: "a".repeat(64) }, archiveKey),
    ).toThrow();
  });

  it("rejects malformed keys and digest mismatches", () => {
    expect(() =>
      sealSubmissionArchive(
        {
          schemaVersion: 1,
          jobId,
          proofDigest: "b".repeat(64),
          submittedAt,
          manifest,
          solution,
        },
        archiveKey,
      ),
    ).toThrow("does not match its proof digest");
    expect(() =>
      sealSubmissionArchive(
        {
          schemaVersion: 1,
          jobId,
          proofDigest,
          submittedAt,
          manifest,
          solution,
        },
        "not-a-key",
      ),
    ).toThrow("exactly 32 bytes");
  });
});
