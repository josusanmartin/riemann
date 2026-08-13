import "server-only";

import { randomUUID } from "node:crypto";
import { z } from "zod";
import type { PreparedDirectSubmission } from "@/lib/direct-submission";
import { getE2BApiKey, getE2BTemplate } from "@/lib/e2b-config";
import { prepareE2BWorkspaceCopySource } from "@/lib/e2b-workspace-compat";

// The sealed verifier itself permits 54 minutes. Leave a small window for
// result finalization; the status route separately enforces a wall-clock
// deadline that cannot be extended by repeated E2B reconnects.
const FLOW_TEST_TIMEOUT_MS = 60 * 60 * 1_000;
const E2B_JOB_ROOT = "/var/lib/riemann/jobs";
const E2B_UPLOAD_ROOT = "/home/riemann/jobs";
const sandboxIdSchema = z
  .string()
  .min(10)
  .max(160)
  .regex(/^[A-Za-z0-9-]+$/);
const jobIdSchema = z.string().uuid();
const digestSchema = z.string().regex(/^[0-9a-f]{64}$/);

type StartFlowTestInput = PreparedDirectSubmission & {
  recordsSnapshot: string;
  baseCommitSha: string;
  previousRecordId: string;
  issuedAt: number;
};

function requireApiKey(): string {
  const apiKey = getE2BApiKey();
  if (!apiKey) throw new Error("E2B verification is not configured");
  return apiKey;
}

export async function hasActiveE2BFlowTest(): Promise<boolean> {
  const { Sandbox } = await import("e2b");
  const paginator = Sandbox.list({
    apiKey: requireApiKey(),
    limit: 1,
    query: {
      metadata: { app: "riemann-fail", kind: "flow-test" },
      state: ["running", "paused"],
    },
  });
  return (await paginator.nextItems()).length > 0;
}

export async function startE2BFlowTest(input: StartFlowTestInput): Promise<{
  sandboxId: string;
  jobId: string;
}> {
  const { Sandbox } = await import("e2b");
  const jobId = randomUUID();
  const uploadDirectory = `${E2B_UPLOAD_ROOT}/${jobId}/submission`;
  const jobDirectory = `${E2B_JOB_ROOT}/${jobId}`;
  const sandbox = await Sandbox.create({
    apiKey: requireApiKey(),
    template: getE2BTemplate(),
    timeoutMs: FLOW_TEST_TIMEOUT_MS,
    secure: true,
    allowInternetAccess: false,
    network: {
      allowPublicTraffic: false,
      denyOut: ["0.0.0.0/0"],
    },
    lifecycle: { onTimeout: { action: "kill" }, autoResume: false },
    metadata: {
      app: "riemann-fail",
      kind: "flow-test",
      github: input.submission.author.github.toLowerCase(),
      submission: input.submission.id,
      job: jobId,
      proofDigest: input.proofDigest,
      baseCommitSha: input.baseCommitSha,
      previousRecordId: input.previousRecordId,
      issuedAt: String(input.issuedAt),
    },
  });

  try {
    const info = await sandbox.getInfo();
    if (
      info.allowInternetAccess !== false ||
      !info.network?.denyOut?.includes("0.0.0.0/0")
    ) {
      throw new Error("E2B did not confirm the deny-all outbound rule");
    }
    await prepareE2BWorkspaceCopySource(sandbox);
    await sandbox.commands.run(
      `install -d -o riemann -g riemann -m 0700 ${uploadDirectory}/proof && ` +
        `install -d -o root -g root -m 0755 ${jobDirectory}`,
      { user: "root", timeoutMs: 30_000 },
    );
    await sandbox.files.write(
      [
        { path: `${uploadDirectory}/submission.json`, data: input.manifest },
        { path: `${uploadDirectory}/proof/Solution.lean`, data: input.solution },
        {
          path: `${uploadDirectory}/trusted-records.json`,
          data: input.recordsSnapshot,
        },
      ],
      { user: "riemann", gzip: true, requestTimeoutMs: 60_000 },
    );
    await sandbox.commands.run(
      `chown -R root:root ${uploadDirectory} && ` +
        `find ${uploadDirectory} -type d -exec chmod 0555 {} + && ` +
        `find ${uploadDirectory} -type f -exec chmod 0444 {} +`,
      { user: "root", timeoutMs: 30_000 },
    );
    await sandbox.commands.run(
      `/usr/bin/flock -n ${jobDirectory}/runner.lock /bin/bash -c ` +
        `'exec /opt/riemann/e2b/run-verification-job.sh ` +
        `${uploadDirectory} ${jobDirectory} ${input.proofDigest} ` +
        `>${jobDirectory}/runner-wrapper.log 2>&1'`,
      { user: "root", background: true, timeoutMs: 30_000 },
    );
    return { sandboxId: sandbox.sandboxId, jobId };
  } catch (error) {
    await sandbox.kill().catch(() => undefined);
    throw error;
  }
}

/**
 * Re-run only the sealed result finalizer after a successful proof artifact
 * exists and the original runner has disappeared. The trusted finalizer
 * recomputes the upload digest and validates the attestation before it writes
 * result.json; this helper cannot turn an invalid artifact into a pass.
 */
export async function finalizeStrandedE2BFlowTest(input: {
  sandboxId: string;
  jobId: string;
  proofDigest: string;
}): Promise<void> {
  const sandboxId = sandboxIdSchema.parse(input.sandboxId);
  const jobId = jobIdSchema.parse(input.jobId);
  const proofDigest = digestSchema.parse(input.proofDigest);
  const submissionDirectory = `${E2B_UPLOAD_ROOT}/${jobId}/submission`;
  const jobDirectory = `${E2B_JOB_ROOT}/${jobId}`;
  const artifactPath = `${E2B_UPLOAD_ROOT}/${jobId}/output/attestation.json`;
  const logPath = `${jobDirectory}/verifier.log`;
  const resultPath = `${jobDirectory}/result.json`;
  const temporaryResultPath = `${resultPath}.tmp`;
  const { Sandbox } = await import("e2b");
  const sandbox = await Sandbox.connect(sandboxId, {
    apiKey: requireApiKey(),
    timeoutMs: FLOW_TEST_TIMEOUT_MS,
    requestTimeoutMs: 30_000,
  });

  await sandbox.commands.run(
    `set -euo pipefail
exec 9>${jobDirectory}/finalizer-recovery.lock
flock -w 20 9
if [[ -s ${resultPath} ]]; then exit 0; fi
test -s ${artifactPath}
if [[ -e ${temporaryResultPath} ]]; then
  mv ${temporaryResultPath} ${temporaryResultPath}.stranded.$(date +%s%N)
fi
/usr/local/bin/node /opt/riemann/.runtime/finalize-e2b-job.mjs \
  ${submissionDirectory} ${artifactPath} ${logPath} ${resultPath} \
  ${proofDigest} 0
test -s ${resultPath}
chmod 0444 ${logPath} ${resultPath}`,
    { user: "root", timeoutMs: 30_000 },
  );
}
