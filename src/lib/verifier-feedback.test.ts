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
