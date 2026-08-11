import { describe, expect, it } from "vitest";
import { prepareDirectSubmission } from "@/lib/direct-submission";
import type { RecordEntry } from "@/lib/challenge";

const currentRecord: RecordEntry = {
  id: "current",
  track: "critical-line",
  date: "2026-08-11",
  author: "Current Author",
  github: null,
  title: "Current exact record",
  method: "Current method",
  scoreDecimal: "0.672500703679411645734379790803",
  scorePercent: "67.2500703679411645734379790803",
  exactRational: {
    numerator: "672500703679411645734379790803",
    denominator: "1000000000000000000000000000000",
  },
  exactExpression:
    "(672500703679411645734379790803 : ℝ) / 1000000000000000000000000000000",
  status: "kernel-verified",
  formalVerification: true,
  independentReview: null,
  sourceUrl: "https://example.com/current",
  proofUrl: "https://example.com/current/proof",
  pullRequestUrl: null,
  summary: "Current formally verified record used by the direct-upload tests.",
};

const input = {
  id: "direct-proof",
  displayName: "Direct Solver",
  score: {
    numerator: "672500703679411645734379790804",
    denominator: "1000000000000000000000000000000",
  },
  summary: "A complete direct-upload candidate with an exact rational score.",
  method: "A formal refinement",
  solution: "import ChallengeDeps\n-- complete declarations\n",
  acceptLicense: true,
};

describe("direct submissions", () => {
  it("derives all trusted manifest fields from the authenticated session", () => {
    const prepared = prepareDirectSubmission(input, "actual-solver", currentRecord);

    expect(prepared.submission.author.github).toBe("actual-solver");
    expect(prepared.submission.proof.solution).toBe("proof/Solution.lean");
    expect(prepared.submission.license).toBe("Apache-2.0");
    expect(prepared.proofDigest).toMatch(/^[0-9a-f]{64}$/);
  });

  it("rejects a score that does not strictly improve the exact record", () => {
    expect(() =>
      prepareDirectSubmission(
        { ...input, score: currentRecord.exactRational },
        "actual-solver",
        currentRecord,
      ),
    ).toThrow("strictly exceed");
  });

  it("defers an irrational baseline comparison to the Lean theorem", () => {
    const prepared = prepareDirectSubmission(
      input,
      "actual-solver",
      { ...currentRecord, exactRational: null, exactExpression: "2 - 1 / cMT" },
    );

    expect(prepared.submission.score).toEqual(input.score);
  });

  it("does not accept browser-supplied author or theorem fields", () => {
    expect(() =>
      prepareDirectSubmission(
        { ...input, author: { github: "impersonated" } },
        "actual-solver",
        currentRecord,
      ),
    ).toThrow();
  });
});
