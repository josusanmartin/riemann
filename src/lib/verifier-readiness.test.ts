import { execFile } from "node:child_process";
import { promisify } from "node:util";
import { describe, expect, it } from "vitest";
import { contract } from "./records";
import { verifierDigestCommand } from "./verifier-readiness";
import { computeVerifierTemplateDigest } from "../../scripts/trusted-material";

describe("sealed verifier identity", () => {
  it("uses exactly the same framed hash as the publication gate", async () => {
    const { stdout } = await promisify(execFile)("bash", ["-c", verifierDigestCommand(process.cwd())]);
    expect(stdout.trim()).toBe(await computeVerifierTemplateDigest(process.cwd(), contract.trustedPaths));
  });
});
