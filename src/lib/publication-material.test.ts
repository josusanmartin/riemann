import { execFileSync } from "node:child_process";
import { mkdirSync, mkdtempSync, readFileSync, rmSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { expect, it, vi } from "vitest";
import { computeTrustedMaterialDigest, computeVerifierTemplateDigest } from "../../scripts/trusted-material";
import { publicationDigests, readReleaseMaterial } from "./publication-material";
import { flowTestRecord } from "./flow-test";
import contract from "../../challenge/contract.json";

it("matches the worker checkout for competitive and flow receipts and refuses unpinned material", async () => {
  const dir = mkdtempSync(join(tmpdir(), "publication-material-"));
  try {
    const rev = execFileSync("git", ["rev-parse", "HEAD"], { encoding: "utf8" }).trim();
    const file = join(dir, "publication-material.bin");
    const checkout = join(dir, "checkout");
    mkdirSync(checkout);
    const tape = execFileSync("git", ["archive", rev, "--", ...contract.trustedPaths], { maxBuffer: 8_000_000 });
    execFileSync("tar", ["-xf", "-", "-C", checkout], { input: tape });
    const pin = execFileSync("python3", ["scripts/package-publication-material.py", rev, file], { encoding: "utf8" }).trim();
    const bytes = readFileSync(file);
    const digests = readReleaseMaterial(bytes, rev, pin);
    expect(digests().template).toBe(await computeVerifierTemplateDigest(checkout, contract.trustedPaths));
    for (const snapshot of [undefined, JSON.stringify([flowTestRecord], null, 2) + "\n"]) {
      expect(digests(snapshot).challenge).toBe(await computeTrustedMaterialDigest(checkout, contract.trustedPaths,
        snapshot === undefined ? {} : { "data/records.json": snapshot }));
    }
    expect(() => readReleaseMaterial(bytes, "0".repeat(40), pin)).toThrow("another deployment");
    expect(() => readReleaseMaterial(bytes, rev, undefined)).toThrow("release pin");
    expect(() => readReleaseMaterial(Buffer.concat([bytes, Buffer.from(" ")]), rev, pin)).toThrow("release pin");
    vi.spyOn(process, "cwd").mockReturnValue(dir);
    vi.stubEnv("VERCEL_ENV", "production");
    vi.stubEnv("VERCEL_GIT_COMMIT_SHA", rev);
    vi.stubEnv("RIEMANN_BASE_COMMIT_SHA", rev);
    vi.stubEnv("RIEMANN_PUBLICATION_MATERIAL_SHA256", pin);
    expect(await publicationDigests()).toEqual(digests());
    vi.stubEnv("RIEMANN_PUBLICATION_MATERIAL_SHA256", "f".repeat(64));
    await expect(publicationDigests()).rejects.toThrow("pinned to its deployment");
  } finally {
    vi.restoreAllMocks();
    vi.unstubAllEnvs();
    rmSync(dir, { recursive: true, force: true });
  }
});
