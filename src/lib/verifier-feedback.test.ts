import { describe, expect, it } from "vitest";
import { describeVerifierRejection } from "@/lib/verifier-feedback";

describe("human-readable verifier feedback", () => {
  it.each([
    {
      expected: "lean-parse-failed",
      log: "error: Solution/Candidate.lean:8:2: unexpected token 'end'",
    },
    {
      expected: "lean-elaboration-failed",
      log: "error: Solution/Candidate.lean:9:4: unknown identifier 'privateLemma'",
    },
    {
      expected: "required-theorem-missing",
      log: "Const not found in solution: 'candidate_critical_line_bound'",
    },
    {
      expected: "theorem-contract-mismatch",
      log: "Challenge and solution theorem statement do not match: 'candidate_strict_improvement'",
    },
    {
      expected: "unpermitted-axiom",
      log: "Illegal axiom detected: 'mySecretAxiom'",
    },
    {
      expected: "nanoda-rejected",
      log: "Running nanoda kernel on solution\nNanoda kernel rejected the solution",
    },
    {
      expected: "lean-kernel-rejected",
      log: "Lean default kernel rejects the solution",
    },
    {
      expected: "verification-timeout",
      log: "",
      message: "The formal verifier exceeded its runtime limit.",
    },
    {
      // Exact message written by scripts/finalize-e2b-job.ts on exit 124/137.
      expected: "verification-timeout",
      log: "",
      message: "The verifier exceeded its isolated runtime limit.",
    },
    {
      // Inner comparator timeout surfaced by scripts/verify-submission.ts.
      expected: "verification-timeout",
      log: "Running comparator\nbash exited with 124",
    },
    {
      expected: "sandbox-expired",
      log: "",
      message: "The isolated verifier expired before producing a result.",
    },
    {
      expected: "verifier-infrastructure",
      log: "Building Solution.Candidate\nEACCES: verifier runtime unavailable\nChild exited with 1",
    },
    {
      expected: "verifier-infrastructure",
      log: "Error while interacting with nanoda: broken pipe",
    },
  ])("classifies $expected", ({ expected, log, message = "status 1" }) => {
    expect(describeVerifierRejection(log, message).code).toBe(expected);
  });

  it("never copies untrusted log content into a durable diagnosis", () => {
    const diagnosis = describeVerifierRejection(
      "error: /home/riemann/jobs/secret/Solution.lean:9:4: unknown identifier 'doNotPublishMe'",
      "The formal verifier exited with status 1.",
    );
    const serialized = JSON.stringify(diagnosis);

    expect(diagnosis.code).toBe("lean-elaboration-failed");
    expect(diagnosis.location).toEqual({
      file: "Solution.lean",
      line: 9,
      column: 4,
    });
    expect(serialized).not.toContain("doNotPublishMe");
    expect(serialized).not.toContain("/home/riemann");
    expect(serialized).not.toContain("Solution.lean:9:4");
  });

  it("points to the compiler error when an earlier warning also cites a line", () => {
    const diagnosis = describeVerifierRejection("warning: Solution.lean:3:1: unused variable\nerror: Solution.lean:19:4: unknown identifier 'fixture'", "Proof failed");
    expect(diagnosis.location).toMatchObject({ line: 19, column: 4 });
  });

  it("marks an unrecognized status-one failure without inventing a cause", () => {
    const diagnosis = describeVerifierRejection(
      "opaque failure text",
      "The formal verifier exited with status 1.",
    );

    expect(diagnosis).toMatchObject({
      code: "unclassified-rejection",
      stage: "unknown",
      retryable: false,
    });
  });
});

it("identifies a nanoda process abort in retained logs even with an older Lean diagnosis", () => {
  const earlier = describeVerifierRejection("Solution/Candidate.lean:2:3: error: unknown identifier 'x'", "Failed");
  const log = "thread '<unnamed>' has overflowed its stack\nfatal runtime error: stack overflow\n" +
    "/opt/site/boat/compact/check-export.sh: line 29: 123 Aborted (core dumped) nanoda_bin nanoda.json\n" +
    "2026-11-27T22:50:52Z  check-proof  exit=134";
  expect(describeVerifierRejection(log, "Failed", earlier)).toMatchObject({
    code: "nanoda-stack-overflow", stage: "nanoda-kernel",
  });
  expect(describeVerifierRejection("stack overflow", "Failed", earlier)).toEqual(earlier);
});
