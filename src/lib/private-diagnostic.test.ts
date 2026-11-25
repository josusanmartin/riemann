import { expect, it } from "vitest";
import { privateDiagnostic } from "./private-diagnostic";

it("selects the candidate error ahead of wrapper errors, keeps brief context, and stops at the next diagnostic", () => {
  expect(privateDiagnostic("error: build failed\nerror: /work/Solution/Candidate.lean:17:4: type mismatch\n  term has type P\n  expected Q\nwarning: later warning"))
    .toBe("error: /work/Solution/Candidate.lean:17:4: type mismatch\n  term has type P\n  expected Q");
  expect(privateDiagnostic("Solution.lean:8:2: error: unknown identifier")).toContain("8:2");
  expect(privateDiagnostic("Create worker: Boat requires payment (HTTP 402)")).toContain("402");
  expect(privateDiagnostic("ordinary progress")).toBeUndefined();
  expect(privateDiagnostic("error: " + "x".repeat(3000))?.length).toBe(1200);
});
