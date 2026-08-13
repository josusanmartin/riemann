import { randomUUID } from "node:crypto";
import { z } from "zod";
import type { Submission } from "@/lib/challenge";
import { getE2BApiKey, getE2BTemplate } from "@/lib/e2b-config";
import { e2bJobMetadataSchema } from "@/lib/submission-jobs";
import { prepareE2BWorkspaceCopySource } from "@/lib/e2b-workspace-compat";

// Admission and scheduling deliberately live outside the frozen verifier
// module. Queue changes therefore cannot change the attested proof checker or
// invalidate an already smoke-tested immutable E2B template.
// E2B's `timeoutMs` is the sandbox lifetime, including on `connect`; it is not
// a client connection timeout. Keep it comfortably beyond the verifier's
// 54-minute hard limit so the result finalizer has time to write its durable
// receipt. E2B caps this account's sandbox lifetime at exactly one hour.
const E2B_JOB_TIMEOUT_MS = 60 * 60 * 1_000;
const E2B_JOB_ROOT = "/var/lib/riemann/jobs";
const E2B_UPLOAD_ROOT = "/home/riemann/jobs";
const E2B_TSX_RUNTIME_SHIM = `import { pathToFileURL } from "node:url";

const target = new Map([
  ["/opt/riemann/scripts/verify-submission.ts", "/opt/riemann/.runtime/verify-submission.mjs"],
  ["/opt/riemann/scripts/prepare-candidate.ts", "/opt/riemann/.runtime/prepare-candidate.mjs"],
  ["/opt/riemann/scripts/finalize-e2b-job.ts", "/opt/riemann/.runtime/finalize-e2b-job.mjs"],
]).get(process.argv[2]);

if (!target) throw new Error("Unsupported sealed TypeScript entrypoint");
process.argv = [process.argv[0], target, ...process.argv.slice(3)];
await import(pathToFileURL(target).href);
`;

const sandboxIdSchema = z
  .string()
  .min(10)
  .max(160)
  .regex(/^[A-Za-z0-9-]+$/);
const jobIdSchema = z.string().uuid();
const digestSchema = z.string().regex(/^[0-9a-f]{64}$/);

type StageVerificationInput = {
  submission: Submission;
  manifest: string;
  solution: string;
  recordsSnapshot: string;
  proofDigest: string;
  baseCommitSha: string;
  previousRecordId: string;
  issuedAt: number;
};

export type StagedE2BVerification = {
  sandboxId: string;
  jobId: string;
};

export type E2BQueuedJobMetadata = {
  sandboxId: string;
  jobId: string;
  submissionId: string;
  github: string;
  proofDigest: string;
  baseCommitSha: string;
  previousRecordId: string;
  issuedAt: number;
  state: "running" | "paused";
};

function requireApiKey(): string {
  const apiKey = getE2BApiKey();
  if (!apiKey) throw new Error("E2B verification is not configured");
  return apiKey;
}

function paths(jobId: string) {
  const parsedJobId = jobIdSchema.parse(jobId);
  return {
    uploadDirectory: `${E2B_UPLOAD_ROOT}/${parsedJobId}/submission`,
    jobDirectory: `${E2B_JOB_ROOT}/${parsedJobId}`,
  };
}

export async function stageE2BVerification(
  input: StageVerificationInput,
): Promise<StagedE2BVerification> {
  const apiKey = requireApiKey();
  const proofDigest = digestSchema.parse(input.proofDigest);
  const { Sandbox } = await import("e2b");
  const jobId = randomUUID();
  const { uploadDirectory, jobDirectory } = paths(jobId);
  const sandbox = await Sandbox.create({
    apiKey,
    template: getE2BTemplate(),
    timeoutMs: E2B_JOB_TIMEOUT_MS,
    secure: true,
    allowInternetAccess: false,
    network: {
      allowPublicTraffic: false,
      denyOut: ["0.0.0.0/0"],
    },
    lifecycle: {
      onTimeout: { action: "pause", keepMemory: false },
      autoResume: false,
    },
    metadata: e2bJobMetadataSchema.parse({
      app: "riemann-fail",
      kind: "formal-verification",
      github: input.submission.author.github.toLowerCase(),
      submission: input.submission.id,
      job: jobId,
      proofDigest,
      baseCommitSha: input.baseCommitSha,
      previousRecordId: input.previousRecordId,
      issuedAt: String(input.issuedAt),
    }),
  });

  try {
    const info = await sandbox.getInfo();
    if (
      info.allowInternetAccess !== false ||
      !info.network?.denyOut?.includes("0.0.0.0/0")
    ) {
      throw new Error("E2B did not confirm the deny-all outbound rule");
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
    return { sandboxId: sandbox.sandboxId, jobId };
  } catch (error) {
    await sandbox.kill().catch(() => undefined);
    throw error;
  }
}

export async function pauseQueuedE2BVerification(
  sandboxId: string,
): Promise<void> {
  const { Sandbox } = await import("e2b");
  await Sandbox.pause(sandboxIdSchema.parse(sandboxId), {
    apiKey: requireApiKey(),
    keepMemory: false,
    requestTimeoutMs: 30_000,
  });
}

export async function launchQueuedE2BVerification(input: {
  sandboxId: string;
  jobId: string;
  proofDigest: string;
}): Promise<void> {
  const sandboxId = sandboxIdSchema.parse(input.sandboxId);
  const jobId = jobIdSchema.parse(input.jobId);
  const proofDigest = digestSchema.parse(input.proofDigest);
  const { uploadDirectory, jobDirectory } = paths(jobId);
  const { Sandbox } = await import("e2b");
  const sandbox = await Sandbox.connect(sandboxId, {
    apiKey: requireApiKey(),
    timeoutMs: E2B_JOB_TIMEOUT_MS,
    requestTimeoutMs: 30_000,
  });
  const info = await sandbox.getInfo();
  if (
    info.allowInternetAccess !== false ||
    !info.network?.denyOut?.includes("0.0.0.0/0")
  ) {
    throw new Error("E2B did not confirm the deny-all outbound rule");
  }

  await prepareE2BWorkspaceCopySource(sandbox);

  const resultPath = `${jobDirectory}/result.json`;
  const lockPath = `${jobDirectory}/runner.lock`;
  const precompiledRuntime = await sandbox.commands.run(
    `if grep -Fq '/opt/riemann/.runtime/verify-submission.mjs' ` +
      `/opt/riemann/e2b/run-verification-job.sh && ` +
      `test -r /opt/riemann/.runtime/verify-submission.mjs && ` +
      `test -r /opt/riemann/.runtime/prepare-candidate.mjs && ` +
      `test -r /opt/riemann/.runtime/finalize-e2b-job.mjs; then ` +
      `printf precompiled; else printf legacy; fi`,
    { user: "root", timeoutMs: 30_000 },
  );

  if (precompiledRuntime.stdout.trim() === "precompiled") {
    console.info("E2B verifier is using its sealed precompiled runtime", {
      sandboxId,
    });
  } else {
    // Compatibility repair for immutable templates created before the
    // verifier runtime was precompiled at image-build time. Never rewrite a
    // current image's sealed runtime while a proof may be importing it.
    const packagedEsbuild =
      "/opt/riemann/node_modules/@esbuild/linux-x64/bin/esbuild";
    const executableEsbuild = "/usr/local/bin/riemann-esbuild";
    const runtime = await sandbox.commands.run(
      `if [[ ! -L ${packagedEsbuild} ]]; then ` +
        `install -o root -g root -m 0555 ${packagedEsbuild} ${executableEsbuild} && ` +
        `rm -f ${packagedEsbuild} && ln -s ${executableEsbuild} ${packagedEsbuild}; ` +
        `fi && chmod 0555 ${executableEsbuild} && ` +
        `runuser -u riemann -- ${executableEsbuild} --version`,
      { user: "root", timeoutMs: 30_000 },
    );
    console.info("E2B verifier JavaScript runtime is executable", {
      sandboxId,
      esbuildVersion: runtime.stdout.trim(),
    });
    await sandbox.commands.run(
      `install -d -o root -g root -m 0755 /opt/riemann/.runtime && ` +
        `cd /opt/riemann && ${executableEsbuild} ` +
        `scripts/verify-submission.ts scripts/prepare-candidate.ts ` +
        `scripts/finalize-e2b-job.ts --bundle --platform=node --format=esm ` +
        `--outdir=/opt/riemann/.runtime --out-extension:.js=.mjs && ` +
        `chmod 0644 /opt/riemann/node_modules/tsx/dist/cli.mjs`,
      { user: "root", timeoutMs: 30_000 },
    );
    await sandbox.files.write(
      "/opt/riemann/node_modules/tsx/dist/cli.mjs",
      E2B_TSX_RUNTIME_SHIM,
      { user: "root", requestTimeoutMs: 30_000 },
    );
    await sandbox.commands.run(
      `chmod 0444 /opt/riemann/.runtime/*.mjs ` +
        `/opt/riemann/node_modules/tsx/dist/cli.mjs && ` +
        `runuser -u riemann -- env -i HOME=/home/riemann ` +
        `PATH=/usr/local/bin:/usr/bin:/bin /usr/local/bin/node ` +
        `/opt/riemann/node_modules/tsx/dist/cli.mjs ` +
        `/opt/riemann/scripts/verify-submission.ts 2>&1 | ` +
        `grep -q 'Usage: verify-submission.ts'`,
      { user: "root", timeoutMs: 30_000 },
    );
  }
  await sandbox.commands.run(
    `/usr/bin/flock -n ${lockPath} /bin/bash -c ` +
      `'if [[ ! -s ${resultPath} ]]; then exec ` +
      `/opt/riemann/e2b/run-verification-job.sh ${uploadDirectory} ` +
      `${jobDirectory} ${proofDigest}; fi'`,
    { user: "root", background: true, timeoutMs: 30_000 },
  );
}

export async function readQueuedE2BJobMetadata(
  sandboxId: string,
): Promise<E2BQueuedJobMetadata> {
  const parsedSandboxId = sandboxIdSchema.parse(sandboxId);
  const { Sandbox } = await import("e2b");
  const info = await Sandbox.getInfo(parsedSandboxId, {
    apiKey: requireApiKey(),
    requestTimeoutMs: 30_000,
  });
  const metadata = e2bJobMetadataSchema.parse(info.metadata);
  return {
    sandboxId: parsedSandboxId,
    jobId: metadata.job,
    submissionId: metadata.submission,
    github: metadata.github,
    proofDigest: metadata.proofDigest,
    baseCommitSha: metadata.baseCommitSha,
    previousRecordId: metadata.previousRecordId,
    issuedAt: Number(metadata.issuedAt),
    state: info.state,
  };
}
