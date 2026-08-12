import { randomUUID } from "node:crypto";
import { z } from "zod";
import {
  verificationAttestationSchema,
  isoDateTimeStringSchema,
  type Submission,
} from "@/lib/challenge";
import { getE2BApiKey, getE2BTemplate } from "@/lib/e2b-config";
import { e2bJobMetadataSchema } from "@/lib/submission-jobs";

// E2B's `timeoutMs` is the sandbox lifetime, including on `connect`; it is not
// a client connection timeout. Keep every create/read/finalize connection
// comfortably beyond the verifier's 54-minute hard limit.
const E2B_JOB_TIMEOUT_MS = 65 * 60 * 1_000;
const E2B_JOB_ROOT = "/var/lib/riemann/jobs";
const E2B_UPLOAD_ROOT = "/home/riemann/jobs";

const commonResultSchema = z.object({
  schemaVersion: z.literal(1),
  submissionId: z.string().max(80).regex(/^[a-z0-9][a-z0-9-]*$/),
  proofDigest: z.string().regex(/^[0-9a-f]{64}$/),
  completedAt: isoDateTimeStringSchema,
  log: z.string().max(100_000),
});

export const e2bVerificationResultSchema = z.discriminatedUnion("status", [
  commonResultSchema
    .extend({
      status: z.literal("verified"),
      attestation: verificationAttestationSchema,
    })
    .strict(),
  commonResultSchema
    .extend({
      status: z.literal("rejected"),
      message: z.string().min(1).max(2_000),
    })
    .strict(),
]);

export type E2BVerificationResult = z.infer<
  typeof e2bVerificationResultSchema
>;

export type StartedE2BVerification = {
  sandboxId: string;
  jobId: string;
};

type StartVerificationInput = {
  submission: Submission;
  manifest: string;
  solution: string;
  recordsSnapshot: string;
  proofDigest: string;
  baseCommitSha: string;
  previousRecordId: string;
  issuedAt: number;
};

export type E2BSubmissionBundle = {
  manifest: string;
  solution: string;
};

export type PausedE2BVerification = {
  sandboxId: string;
  jobId: string;
  submissionId: string;
  github: string;
  proofDigest: string;
  baseCommitSha: string;
  previousRecordId: string;
  issuedAt: number;
};

function requireApiKey(): string {
  const apiKey = getE2BApiKey();
  if (!apiKey) {
    throw new Error("E2B verification is not configured");
  }
  return apiKey;
}

function resultPath(jobId: string): string {
  return `${E2B_JOB_ROOT}/${jobId}/result.json`;
}

export async function hasActiveE2BJob(github: string): Promise<boolean> {
  const apiKey = requireApiKey();
  const { Sandbox } = await import("e2b");
  const paginator = Sandbox.list({
    apiKey,
    limit: 2,
    query: {
      metadata: { app: "riemann-fail", github: github.toLowerCase() },
      state: ["running", "paused"],
    },
  });
  return (await paginator.nextItems()).length > 0;
}

export async function startE2BVerification(
  input: StartVerificationInput,
): Promise<StartedE2BVerification> {
  const apiKey = requireApiKey();
  const { Sandbox } = await import("e2b");
  const jobId = randomUUID();
  const uploadDirectory = `${E2B_UPLOAD_ROOT}/${jobId}/submission`;
  const jobDirectory = `${E2B_JOB_ROOT}/${jobId}`;
  const sandbox = await Sandbox.create({
    apiKey,
    template: getE2BTemplate(),
    timeoutMs: E2B_JOB_TIMEOUT_MS,
    secure: true,
    allowInternetAccess: false,
    network: { allowPublicTraffic: false },
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
      proofDigest: input.proofDigest,
      baseCommitSha: input.baseCommitSha,
      previousRecordId: input.previousRecordId,
      issuedAt: String(input.issuedAt),
    }),
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

export async function readE2BVerification(
  sandboxId: string,
  jobId: string,
): Promise<E2BVerificationResult | null> {
  const apiKey = requireApiKey();
  const { FileNotFoundError, Sandbox } = await import("e2b");
  const sandbox = await Sandbox.connect(sandboxId, {
    apiKey,
    timeoutMs: E2B_JOB_TIMEOUT_MS,
    requestTimeoutMs: 30_000,
  });
  try {
    const raw = await sandbox.files.read(resultPath(jobId), {
      user: "root",
      requestTimeoutMs: 30_000,
    });
    return e2bVerificationResultSchema.parse(JSON.parse(raw));
  } catch (error) {
    if (error instanceof FileNotFoundError) return null;
    throw error;
  }
}

export async function readE2BSubmissionBundle(
  sandboxId: string,
  jobId: string,
): Promise<E2BSubmissionBundle> {
  const parsedJobId = z.string().uuid().parse(jobId);
  const apiKey = requireApiKey();
  const { Sandbox } = await import("e2b");
  const sandbox = await Sandbox.connect(sandboxId, {
    apiKey,
    timeoutMs: E2B_JOB_TIMEOUT_MS,
    requestTimeoutMs: 30_000,
  });
  const submissionRoot = `${E2B_UPLOAD_ROOT}/${parsedJobId}/submission`;
  const [manifest, solution] = await Promise.all([
    sandbox.files.read(`${submissionRoot}/submission.json`, {
      user: "root",
      requestTimeoutMs: 30_000,
    }),
    sandbox.files.read(`${submissionRoot}/proof/Solution.lean`, {
      user: "root",
      requestTimeoutMs: 30_000,
    }),
  ]);
  if (Buffer.byteLength(manifest, "utf8") > 100_000) {
    throw new Error("E2B submission manifest exceeds the trusted size limit");
  }
  if (Buffer.byteLength(solution, "utf8") > 2_000_000) {
    throw new Error("E2B Lean source exceeds the trusted size limit");
  }
  return { manifest, solution };
}

export async function killE2BSandbox(sandboxId: string): Promise<void> {
  const { Sandbox } = await import("e2b");
  await Sandbox.kill(sandboxId, { apiKey: requireApiKey() });
}

export async function listPausedE2BVerifications(
  limit = 1,
): Promise<PausedE2BVerification[]> {
  const apiKey = requireApiKey();
  const { Sandbox } = await import("e2b");
  const paginator = Sandbox.list({
    apiKey,
    limit,
    query: {
      metadata: { app: "riemann-fail", kind: "formal-verification" },
      state: ["paused"],
    },
  });
  return (await paginator.nextItems()).map((sandbox) => {
    const metadata = e2bJobMetadataSchema.parse(sandbox.metadata);
    return {
      sandboxId: sandbox.sandboxId,
      jobId: metadata.job,
      submissionId: metadata.submission,
      github: metadata.github,
      proofDigest: metadata.proofDigest,
      baseCommitSha: metadata.baseCommitSha,
      previousRecordId: metadata.previousRecordId,
      issuedAt: Number(metadata.issuedAt),
    };
  });
}
