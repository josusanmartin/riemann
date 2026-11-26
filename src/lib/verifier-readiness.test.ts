import { execFile } from "node:child_process";
import { promisify } from "node:util";
import { afterEach, describe, expect, it, vi } from "vitest";
import { contract } from "./records";
import { assertVerifierReady, verifierDigestCommand } from "./verifier-readiness";
import { computeVerifierTemplateDigest } from "../../scripts/trusted-material";

afterEach(() => vi.unstubAllEnvs());

describe("sealed verifier identity", () => {
  it("requires the declared and measured E2B digests to match the deployed verifier", async () => {
    const expected = await computeVerifierTemplateDigest(process.cwd(), contract.trustedPaths);
    const run = vi.fn().mockResolvedValue({ stdout: expected });
    const sandbox = { commands: { run } } as unknown as Parameters<typeof assertVerifierReady>[0];
    vi.stubEnv("E2B_TEMPLATE_DIGEST", "");
    await expect(assertVerifierReady(sandbox)).rejects.toThrow("does not match");
    vi.stubEnv("E2B_TEMPLATE_DIGEST", expected);
    await expect(assertVerifierReady(sandbox)).resolves.toBeUndefined();
    run.mockResolvedValue({ stdout: "0".repeat(64) });
    await expect(assertVerifierReady(sandbox)).rejects.toThrow("does not match");
  });

  it("uses exactly the same framed hash as the publication gate", async () => {
    const { stdout } = await promisify(execFile)("bash", ["-c", verifierDigestCommand(process.cwd())]);
    expect(stdout.trim()).toBe(await computeVerifierTemplateDigest(process.cwd(), contract.trustedPaths));
  });
});
