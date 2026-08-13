import { readFile } from "node:fs/promises";
import { resolve } from "node:path";
import { describe, expect, it } from "vitest";
import {
  FLOW_TEST_BASELINE_ID,
  FLOW_TEST_SCORE,
  flowTestRecord,
  flowTestSolutionSource,
} from "@/lib/flow-test";
import { prepareFlowTestSubmission } from "@/lib/flow-test-server";

const repositoryRoot = resolve(import.meta.dirname, "../..");

describe("official verifier flow test", () => {
  it("keeps the downloadable full proof and controlled record fixture synchronized", async () => {
    const [proof, records] = await Promise.all([
      readFile(
        resolve(repositoryRoot, "submissions/flow-test/proof/Solution.lean"),
        "utf8",
      ),
      readFile(resolve(repositoryRoot, "challenge/flow-test-records.json"), "utf8"),
    ]);

    expect(flowTestSolutionSource).toBe(proof);
    expect(`${JSON.stringify([flowTestRecord], null, 2)}\n`).toBe(records);
    expect(flowTestSolutionSource).not.toMatch(/\bsorry\b/);
  });

  it("builds a test-only 2/3 manifest over the isolated 1/3 baseline", () => {
    const prepared = prepareFlowTestSubmission(
      { solution: flowTestSolutionSource },
      "josusanmartin",
      "Josu San Martin",
      1_786_579_200_000,
    );

    expect(prepared.submission.id).toBe("flow-test-1786579200000");
    expect(prepared.submission.score).toEqual(FLOW_TEST_SCORE);
    expect(prepared.submission.author.github).toBe("josusanmartin");
    expect(flowTestRecord.id).toBe(FLOW_TEST_BASELINE_ID);
    expect(flowTestRecord.exactRational).toEqual({
      numerator: "1",
      denominator: "3",
    });
    expect(prepared.proofDigest).toMatch(/^[0-9a-f]{64}$/);
  });
});
