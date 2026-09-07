import { spawnSync } from "node:child_process";
import { mkdtemp, readFile, rm, writeFile } from "node:fs/promises";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { describe, expect, it } from "vitest";
import {
  queuedVerificationRunnerCommand,
  queuedVerificationRunnerProbeCommand,
} from "@/lib/e2b-queue";

const jobId = "4d664a5f-65f8-40c9-a641-6bb9eb77ef6b";
const proofDigest = "a".repeat(64);

describe("queued E2B runner recovery", () => {
  it("bounds recovery by first launch and never discards a ready result", async () => {
    const directory = await mkdtemp(join(tmpdir(), "riemann-runner-deadline-"));
    try {
      const command = queuedVerificationRunnerProbeCommand(jobId)
        .replaceAll(`/var/lib/riemann/jobs/${jobId}`, directory);
      const probe = () => spawnSync("bash", ["-c", command], { encoding: "utf8" });
      const initial = probe();
      expect(initial.status).toBe(0);
      expect(initial.stdout).toBe("recover");
      const started = await readFile(join(directory, "started-at"), "utf8");
      expect(probe().stdout).toBe("recover");
      expect(await readFile(join(directory, "started-at"), "utf8")).toBe(started);
      await writeFile(join(directory, "started-at"), "1\n");
      expect(probe().stdout).toBe("expired");
      await writeFile(join(directory, "result.json"), "{}\n");
      expect(probe().stdout).toBe("result-ready");
    } finally {
      await rm(directory, { recursive: true, force: true });
    }
  });

  it("uses one lock and finalizes an existing proof artifact before rerunning", () => {
    const command = queuedVerificationRunnerCommand(jobId, proofDigest);

    expect(command).toContain(`/var/lib/riemann/jobs/${jobId}/runner.lock`);
    expect(command).toContain(
      `if [[ -s /var/lib/riemann/jobs/${jobId}/result.json ]]`,
    );
    expect(command).toContain(
      `if [[ -s /home/riemann/jobs/${jobId}/output/attestation.json ]]`,
    );
    expect(command).toContain("finalize-e2b-job.mjs");
    expect(command).toContain("result.json.tmp.stranded.$(date +%s%N)");
    expect(command).toContain("attestation.json.stranded.$(date +%s%N)");
    expect(command).toContain("then exit 0; fi");
    expect(command).toContain("run-verification-job.sh");
    expect(spawnSync("bash", ["-n", "-c", command]).status).toBe(0);
  });

  it("rejects job coordinates before constructing a shell command", () => {
    expect(() =>
      queuedVerificationRunnerCommand(
        `${jobId}; touch /tmp/injected`,
        proofDigest,
      ),
    ).toThrow();
    expect(() =>
      queuedVerificationRunnerCommand(jobId, `${proofDigest}; true`),
    ).toThrow();
    expect(() =>
      queuedVerificationRunnerProbeCommand(`${jobId}; touch /tmp/injected`),
    ).toThrow();
  });

  it("probes completed and active runners without preparing the workspace", () => {
    const command = queuedVerificationRunnerProbeCommand(jobId);

    expect(command).toContain("printf result-ready");
    expect(command).toContain("printf recover");
    expect(command).toContain("printf running");
    expect(command).toContain("-E 75");
    expect(command).toContain("else exit $lock_status");
    expect(command).toContain(`/var/lib/riemann/jobs/${jobId}/runner.lock`);
    expect(command).not.toContain("prepare-candidate");
    expect(spawnSync("bash", ["-n", "-c", command]).status).toBe(0);
  });
});
