import { createHmac, timingSafeEqual } from "node:crypto";
import { z } from "zod";
import { githubLoginSchema } from "@/lib/challenge";

const sha256Schema = z.string().regex(/^[0-9a-f]{64}$/);

export const e2bJobMetadataSchema = z
  .object({
    app: z.literal("riemann-fail"),
    kind: z.literal("formal-verification"),
    github: githubLoginSchema.transform((value) => value.toLowerCase()),
    submission: z.string().max(80).regex(/^[a-z0-9][a-z0-9-]*$/),
    job: z.string().uuid(),
    proofDigest: sha256Schema,
    baseCommitSha: z.string().regex(/^[0-9a-f]{40}$/),
    previousRecordId: z.string().min(1).max(160),
    issuedAt: z.string().regex(/^\d{13}$/),
  })
  .strict();

export type E2BJobMetadata = z.infer<typeof e2bJobMetadataSchema>;

export const submissionJobTokenSchema = z
  .object({
    schemaVersion: z.literal(1),
    sandboxId: z.string().min(10).max(160).regex(/^[A-Za-z0-9-]+$/),
    jobId: z.string().uuid(),
    submissionId: z.string().max(80).regex(/^[a-z0-9][a-z0-9-]*$/),
    github: githubLoginSchema,
    proofDigest: sha256Schema,
    baseCommitSha: z.string().regex(/^[0-9a-f]{40}$/),
    previousRecordId: z.string().min(1).max(160),
    issuedAt: z.number().int().nonnegative(),
    expiresAt: z.number().int().positive(),
  })
  .strict();

export type SubmissionJobToken = z.infer<typeof submissionJobTokenSchema>;

function signature(payload: string, secret: string): Buffer {
  return createHmac("sha256", secret).update(payload).digest();
}

export function signSubmissionJob(
  payload: SubmissionJobToken,
  secret: string,
): string {
  const parsed = submissionJobTokenSchema.parse(payload);
  if (parsed.expiresAt <= parsed.issuedAt) {
    throw new Error("Submission job expiry must follow its issue time");
  }
  const encoded = Buffer.from(JSON.stringify(parsed)).toString("base64url");
  return `${encoded}.${signature(encoded, secret).toString("base64url")}`;
}

export function verifySubmissionJob(
  token: string,
  secret: string,
  now = Date.now(),
): SubmissionJobToken {
  if (token.length > 2_048) {
    throw new Error("Submission job token is too large");
  }
  const [encoded, suppliedSignature, extra] = token.split(".");
  if (!encoded || !suppliedSignature || extra) {
    throw new Error("Malformed submission job token");
  }

  const expected = signature(encoded, secret);
  let supplied: Buffer;
  try {
    supplied = Buffer.from(suppliedSignature, "base64url");
  } catch {
    throw new Error("Malformed submission job signature");
  }
  if (supplied.length !== expected.length || !timingSafeEqual(supplied, expected)) {
    throw new Error("Invalid submission job signature");
  }

  let value: unknown;
  try {
    value = JSON.parse(Buffer.from(encoded, "base64url").toString("utf8"));
  } catch {
    throw new Error("Malformed submission job payload");
  }
  const payload = submissionJobTokenSchema.parse(value);
  if (payload.expiresAt <= now) {
    throw new Error("Submission job token has expired");
  }
  return payload;
}
