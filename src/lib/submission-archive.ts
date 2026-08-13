import {
  createCipheriv,
  createDecipheriv,
  createHash,
  randomBytes,
} from "node:crypto";
import { gunzipSync, gzipSync } from "node:zlib";
import { z } from "zod";
import { submissionSchema, type Submission } from "@/lib/challenge";
import {
  computeDirectProofDigest,
  MAX_DIRECT_SOLUTION_BYTES,
} from "@/lib/direct-submission";

export const SUBMISSION_ARCHIVE_DIRECTORY = "runtime/submission-archive";
const ARCHIVE_CONTEXT = "riemann-fail-submission-archive-v1";
const MAX_ARCHIVE_PAYLOAD_BYTES = MAX_DIRECT_SOLUTION_BYTES * 6 + 250_000;

const sha256Schema = z.string().regex(/^[0-9a-f]{64}$/);
const base64Schema = z.string().regex(/^[A-Za-z0-9+/]*={0,2}$/);

export const submissionArchiveEnvelopeSchema = z
  .object({
    schemaVersion: z.literal(1),
    algorithm: z.literal("aes-256-gcm"),
    compression: z.literal("gzip"),
    keyId: z.string().regex(/^[0-9a-f]{16}$/),
    jobId: z.string().uuid(),
    proofDigest: sha256Schema,
    createdAt: z.string().datetime({ offset: true }),
    nonce: base64Schema.max(24),
    authenticationTag: base64Schema.max(24),
    ciphertext: base64Schema.max(20_000_000),
  })
  .strict();

export type SubmissionArchiveEnvelope = z.infer<
  typeof submissionArchiveEnvelopeSchema
>;

export const submissionArchivePayloadSchema = z
  .object({
    schemaVersion: z.literal(1),
    jobId: z.string().uuid(),
    proofDigest: sha256Schema,
    submittedAt: z.string().datetime({ offset: true }),
    manifest: z.string().min(1).max(200_000),
    solution: z.string().min(1).max(MAX_DIRECT_SOLUTION_BYTES),
  })
  .strict();

export type SubmissionArchivePayload = z.infer<
  typeof submissionArchivePayloadSchema
>;

export type SubmissionArchiveSummary = {
  jobId: string;
  proofDigest: string;
  submittedAt: string;
  sourceBytes: number;
  submission: Submission;
};

function decodeArchiveKey(encoded: string): Buffer {
  const normalized = encoded.trim();
  const key = Buffer.from(normalized, "base64");
  if (key.length !== 32 || key.toString("base64") !== normalized) {
    throw new Error(
      "SUBMISSION_ARCHIVE_KEY must be exactly 32 bytes encoded as canonical base64",
    );
  }
  return key;
}

function archiveKeyId(key: Buffer): string {
  return createHash("sha256").update(key).digest("hex").slice(0, 16);
}

function archiveAad(jobId: string, proofDigest: string): Buffer {
  return Buffer.from(`${ARCHIVE_CONTEXT}\0${jobId}\0${proofDigest}`, "utf8");
}

export function submissionArchivePath(
  jobId: string,
  proofDigest: string,
  submittedAt: string,
): string {
  const parsedJobId = z.string().uuid().parse(jobId);
  const parsedDigest = sha256Schema.parse(proofDigest);
  const parsedSubmittedAt = z.string().datetime({ offset: true }).parse(submittedAt);
  const timestamp = Date.parse(parsedSubmittedAt);
  if (!Number.isSafeInteger(timestamp) || timestamp < 0) {
    throw new Error("The archive timestamp is outside the supported range");
  }
  return (
    `${SUBMISSION_ARCHIVE_DIRECTORY}/${parsedSubmittedAt.slice(0, 10)}/` +
    `${timestamp}-${parsedJobId}-${parsedDigest}.json`
  );
}

export function parseSubmissionArchivePath(path: string): {
  path: string;
  jobId: string;
  proofDigest: string;
  submittedAt: string;
} | null {
  const match = path.match(
    /^runtime\/submission-archive\/(\d{4}-\d{2}-\d{2})\/(\d{13})-([0-9a-f-]{36})-([0-9a-f]{64})\.json$/,
  );
  if (!match) return null;
  const submittedAt = new Date(Number(match[2])).toISOString();
  if (submittedAt.slice(0, 10) !== match[1]) return null;
  try {
    return {
      path,
      jobId: z.string().uuid().parse(match[3]),
      proofDigest: sha256Schema.parse(match[4]),
      submittedAt,
    };
  } catch {
    return null;
  }
}

export function isSubmissionArchiveConfigured(): boolean {
  const value = process.env.SUBMISSION_ARCHIVE_KEY;
  if (!value) return false;
  try {
    decodeArchiveKey(value);
    return true;
  } catch {
    return false;
  }
}

export function sealSubmissionArchive(
  input: SubmissionArchivePayload,
  encodedKey: string,
  nonce = randomBytes(12),
): SubmissionArchiveEnvelope {
  const payload = submissionArchivePayloadSchema.parse(input);
  const submission = submissionSchema.parse(JSON.parse(payload.manifest));
  if (submission.proof.solution !== "proof/Solution.lean") {
    throw new Error("The archived manifest has an unexpected proof path");
  }
  const actualDigest = computeDirectProofDigest(payload.manifest, payload.solution);
  if (actualDigest !== payload.proofDigest) {
    throw new Error("The archived source does not match its proof digest");
  }
  if (Buffer.byteLength(payload.solution, "utf8") > MAX_DIRECT_SOLUTION_BYTES) {
    throw new Error("The archived Lean source exceeds the 2 MB limit");
  }
  if (nonce.length !== 12) {
    throw new Error("Submission archive nonces must be exactly 12 bytes");
  }

  const key = decodeArchiveKey(encodedKey);
  const cipher = createCipheriv("aes-256-gcm", key, nonce);
  cipher.setAAD(archiveAad(payload.jobId, payload.proofDigest));
  const compressed = gzipSync(Buffer.from(JSON.stringify(payload), "utf8"), {
    level: 9,
  });
  const ciphertext = Buffer.concat([cipher.update(compressed), cipher.final()]);

  return submissionArchiveEnvelopeSchema.parse({
    schemaVersion: 1,
    algorithm: "aes-256-gcm",
    compression: "gzip",
    keyId: archiveKeyId(key),
    jobId: payload.jobId,
    proofDigest: payload.proofDigest,
    createdAt: payload.submittedAt,
    nonce: nonce.toString("base64"),
    authenticationTag: cipher.getAuthTag().toString("base64"),
    ciphertext: ciphertext.toString("base64"),
  });
}

export function openSubmissionArchive(
  rawEnvelope: unknown,
  encodedKey: string,
): SubmissionArchivePayload {
  const envelope = submissionArchiveEnvelopeSchema.parse(rawEnvelope);
  const key = decodeArchiveKey(encodedKey);
  if (archiveKeyId(key) !== envelope.keyId) {
    throw new Error("The submission archive was encrypted with another key");
  }

  const decipher = createDecipheriv(
    "aes-256-gcm",
    key,
    Buffer.from(envelope.nonce, "base64"),
  );
  decipher.setAAD(archiveAad(envelope.jobId, envelope.proofDigest));
  decipher.setAuthTag(Buffer.from(envelope.authenticationTag, "base64"));
  const compressed = Buffer.concat([
    decipher.update(Buffer.from(envelope.ciphertext, "base64")),
    decipher.final(),
  ]);
  const rawPayload = gunzipSync(compressed, {
    maxOutputLength: MAX_ARCHIVE_PAYLOAD_BYTES,
  }).toString("utf8");
  const payload = submissionArchivePayloadSchema.parse(JSON.parse(rawPayload));
  if (
    payload.jobId !== envelope.jobId ||
    payload.proofDigest !== envelope.proofDigest ||
    payload.submittedAt !== envelope.createdAt
  ) {
    throw new Error("The submission archive envelope does not match its payload");
  }
  const actualDigest = computeDirectProofDigest(payload.manifest, payload.solution);
  if (actualDigest !== payload.proofDigest) {
    throw new Error("The decrypted source does not match its proof digest");
  }
  if (Buffer.byteLength(payload.solution, "utf8") > MAX_DIRECT_SOLUTION_BYTES) {
    throw new Error("The decrypted Lean source exceeds the 2 MB limit");
  }
  return payload;
}

export function summarizeSubmissionArchive(
  payload: SubmissionArchivePayload,
): SubmissionArchiveSummary {
  return {
    jobId: payload.jobId,
    proofDigest: payload.proofDigest,
    submittedAt: payload.submittedAt,
    sourceBytes: Buffer.byteLength(payload.solution, "utf8"),
    submission: submissionSchema.parse(JSON.parse(payload.manifest)),
  };
}

export function requireSubmissionArchiveKey(): string {
  const value = process.env.SUBMISSION_ARCHIVE_KEY;
  if (!value) throw new Error("The encrypted submission archive is not configured");
  decodeArchiveKey(value);
  return value;
}
