import "server-only";

import { randomUUID } from "node:crypto";
import type { PreparedDirectSubmission } from "@/lib/direct-submission";
import { getE2BApiKey, getE2BTemplate } from "@/lib/e2b-config";

const FLOW_TEST_TIMEOUT_MS = 20 * 60 * 1_000;
const E2B_JOB_ROOT = "/var/lib/riemann/jobs";
const E2B_UPLOAD_ROOT = "/home/riemann/jobs";

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
    network: { allowPublicTraffic: false },
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
    if (info.allowInternetAccess !== false) {
      throw new Error("E2B did not confirm that internet access is disabled");
    }
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
      `/opt/riemann/e2b/run-verification-job.sh ${uploadDirectory} ${jobDirectory} ${input.proofDigest}`,
      { user: "root", background: true, timeoutMs: 30_000 },
    );
    return { sandboxId: sandbox.sandboxId, jobId };
  } catch (error) {
    await sandbox.kill().catch(() => undefined);
    throw error;
  }
}
