import { readFile } from "node:fs/promises";
import { resolve } from "node:path";
import { describe, expect, it } from "vitest";
import { contract } from "@/lib/records";
import { submissionStarterSource } from "@/lib/submission-starter";

const repositoryRoot = resolve(import.meta.dirname, "../..");

describe("public submission starter", () => {
  it("stays synchronized with the repository example and trusted statements", async () => {
    const [repositoryExample, trustedTemplate] = await Promise.all([
      readFile(
        resolve(repositoryRoot, "submissions/example/proof/Solution.lean"),
        "utf8",
      ),
      readFile(
        resolve(repositoryRoot, "challenge/templates/Challenge.Candidate.lean"),
        "utf8",
      ),
    ]);

    expect(submissionStarterSource).toBe(repositoryExample);
    expect(submissionStarterSource.endsWith(trustedTemplate)).toBe(true);
  });

  it("contains every locked theorem and exactly three visible proof placeholders", () => {
    for (const theoremName of Object.values(contract.theorems)) {
      expect(submissionStarterSource).toContain(`theorem ${theoremName} :`);
    }
    expect(submissionStarterSource.match(/^  sorry$/gm)).toHaveLength(3);
  });
});
