import { expect, it } from "vitest";
import { getRecords, records } from "./records";
import { competitionIncumbent } from "./challenge";
import { assertCurrentRecord, buildRecordEntry } from "./github-promotion";
import { prepareDirectSubmission } from "./direct-submission";
import { GET } from "../app/api/leaderboard/route";
import { readFileSync } from "node:fs";
import { assertValidAttestation } from "./attestation";
import { contract } from "./records";
import { verificationAttestationSchema } from "./challenge";

it("keeps the opening threshold separate from accepted records and defaults legacy queries to distinct", async () => {
  const query = (suffix: string) => GET(new Request("https://example.test/api/leaderboard" + suffix));
  const simple = await query("?track=simple-zeros").json();
  expect(simple.records.every((r: { track: string }) => r.track === "simple-zeros")).toBe(true);
  expect(simple.current?.id ?? null).toBe(getRecords("simple-zeros").at(-1)?.id ?? null);
  expect(simple.entryThreshold).toEqual(competitionIncumbent(records, "simple-zeros").exactRational);
  expect((await query("").json()).track).toBe("critical-line");
  expect(query("?track=typo").status).toBe(400);
});

it("binds the proof digest, attestation and incumbent to the selected challenge", () => {
  const distinct = getRecords();
  const opening = competitionIncumbent(distinct, "simple-zeros");
  const input = { id: "simple-controls", displayName: "Tester", method: "Control",
    summary: "Bound on the number of simple zeros.", score: { numerator: "3", denominator: "4" },
    solution: "-- test fixture", acceptLicense: true };
  const simple = prepareDirectSubmission(input, "tester", opening, "simple-zeros");
  const other = prepareDirectSubmission(input, "tester", opening, "critical-line");
  expect(simple.proofDigest).not.toBe(other.proofDigest);
  const evidence = verificationAttestationSchema.parse(JSON.parse(readFileSync(
    "submissions/devine-xu-joint-certificate-855579/verification/attestation.json", "utf8")));
  expect(() => assertValidAttestation(simple.submission, evidence, contract, "", "")).toThrow("different challenge");
  expect(() => assertCurrentRecord(distinct, simple.submission, opening.id)).not.toThrow();
  const first = buildRecordEntry(simple.submission, evidence, { sourceUrl: "https://example.test", proofUrl: "https://example.test" });
  expect(first.track).toBe("simple-zeros");
  const both = [...distinct, first];
  expect(competitionIncumbent(both, "critical-line")).toEqual(competitionIncumbent(distinct, "critical-line"));
  expect(() => assertCurrentRecord(both, {...simple.submission, id: "later"}, opening.id)).toThrow();
  expect(() => prepareDirectSubmission(input, "tester", first, "simple-zeros")).toThrow("strictly exceed");
});

it("generates different trusted Lean statements from the same claimed score", async () => {
  const { execFileSync } = await import("node:child_process");
  const { mkdtempSync, mkdirSync, writeFileSync, rmSync } = await import("node:fs");
  const { tmpdir } = await import("node:os");
  const { join, resolve } = await import("node:path");
  const root = mkdtempSync(join(tmpdir(), "riemann-tracks-"));
  try {
    for (const track of ["critical-line", "simple-zeros"] as const) {
      const dir = join(root, track);
      const out = join(dir, "out");
      mkdirSync(join(dir, "proof"), { recursive: true });
      mkdirSync(join(out, "comparator"), { recursive: true });
      const incumbent = competitionIncumbent(records, track);
      const candidate = prepareDirectSubmission({ id: "bound", displayName: "Test", method: "generation",
        summary: "Check both interval declarations in the trusted reference.", score: { numerator: "1", denominator: "1" },
        solution: "-- fixture", acceptLicense: true }, "tester", incumbent, track);
      writeFileSync(join(dir, "submission.json"), candidate.manifest);
      writeFileSync(join(dir, "proof/Solution.lean"), candidate.solution);
      execFileSync(resolve("node_modules/.bin/tsx"), ["scripts/prepare-candidate.ts", dir, out]);
      const reference = readFileSync(join(out, "comparator/Challenge/Candidate.lean"), "utf8");
      const meta = JSON.parse(readFileSync(join(out, "verification-artifacts/bound.prepared.json"), "utf8"));
      expect(meta).toMatchObject({ track, previousRecordId: incumbent.id });
      const count = track === "simple-zeros" ? "Zeta23.Nsimple" : "N0star";
      expect(reference).toContain("≤ " + count + " T (2 * T)");
      expect(reference).toContain("≤ " + count + " 0 T");
    }
  } finally { rmSync(root, { recursive: true, force: true }); }
});
