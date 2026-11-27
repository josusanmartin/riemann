import { execFileSync } from "node:child_process";
import { mkdtempSync, readFileSync, rmSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { expect, it } from "vitest";
import { computeTrustedMaterialDigest, computeVerifierTemplateDigest } from "../../scripts/trusted-material";
import { readReleaseMaterial } from "./publication-material";
import { flowTestRecord } from "./flow-test";
import contract from "../../challenge/contract.json";

it("matches the worker checkout for competitive and flow receipts and refuses unpinned material", async () => {
  const dir = mkdtempSync(join(tmpdir(), "publication-material-"));
  try {
    const rev = execFileSync("git", ["rev-parse", "HEAD"], { encoding: "utf8" }).trim();
    const file = join(dir, "release.bin");
    const pin = execFileSync("python3", ["scripts/package-publication-material.py", rev, file], { encoding: "utf8" }).trim();
    const bytes = readFileSync(file);
    const digests = readReleaseMaterial(bytes, rev, pin);
    expect(digests().template).toBe(await computeVerifierTemplateDigest(process.cwd(), contract.trustedPaths));
    for (const snapshot of [undefined, JSON.stringify([flowTestRecord], null, 2) + "\n"]) {
      expect(digests(snapshot).challenge).toBe(await computeTrustedMaterialDigest(process.cwd(), contract.trustedPaths,
        snapshot === undefined ? {} : { "data/records.json": snapshot }));
    }
    expect(() => readReleaseMaterial(bytes, "0".repeat(40), pin)).toThrow("another deployment");
    expect(() => readReleaseMaterial(bytes, rev, undefined)).toThrow("release pin");
    expect(() => readReleaseMaterial(Buffer.concat([bytes, Buffer.from(" ")]), rev, pin)).toThrow("release pin");
  } finally {
    rmSync(dir, { recursive: true, force: true });
  }
});
