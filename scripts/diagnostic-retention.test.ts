import { spawnSync } from "node:child_process";
import { mkdtempSync, readFileSync, rmSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { expect, it } from "vitest";
import { computeDirectProofDigest } from "../src/lib/direct-submission";

it("retains early Lean errors and the final failure in a large worker log", () => {
  const dir = mkdtempSync(join(tmpdir(), "riemann-output-"));
  try {
    const example = "submissions/example";
    const digest = computeDirectProofDigest(readFileSync(example + "/submission.json", "utf8"), readFileSync(example + "/proof/Solution.lean", "utf8"));
    writeFileSync(join(dir, "log"), "error: Solution.lean:20:3: unknown identifier\n" + "worker progress\n".repeat(40000) + "exit status 7\n");
    const processResult = spawnSync(process.execPath, ["--import", "tsx", "scripts/finalize-e2b-job.ts", example, join(dir, "unused"), join(dir, "log"), join(dir, "result"), digest, "7"], { encoding: "utf8" });
    expect(processResult.status, processResult.stderr).toBe(0);
    const result = JSON.parse(readFileSync(join(dir, "result"), "utf8"));
    expect(result.status).toBe("rejected");
    expect(result.log).toContain("Solution.lean:20:3");
    expect(result.log).toContain("middle of verifier output omitted");
    expect(result.log).toContain("exit status 7");
    expect(result.log.length).toBeLessThanOrEqual(100000);
  } finally { rmSync(dir, { recursive: true, force: true }); }
});
