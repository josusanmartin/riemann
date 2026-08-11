import type { E2BVerificationResult } from "@/lib/e2b-verifier";
import { readE2BSubmissionBundle } from "@/lib/e2b-verifier";
import {
  promoteVerifiedSubmission,
  type PromotionResult,
} from "@/lib/github-promotion";

export type VerificationJobCoordinates = {
  sandboxId: string;
  jobId: string;
  submissionId: string;
  github: string;
  proofDigest: string;
  baseCommitSha: string;
  previousRecordId: string;
  issuedAt: number;
};

export function assertE2BResultMatchesJob(
  job: VerificationJobCoordinates,
  result: E2BVerificationResult,
): void {
  if (
    result.submissionId !== job.submissionId ||
    result.proofDigest !== job.proofDigest
  ) {
    throw new Error("E2B result does not match the trusted job coordinates");
  }
  if (
    result.status === "verified" &&
    result.attestation.author.github.toLowerCase() !== job.github.toLowerCase()
  ) {
    throw new Error("E2B attestation belongs to another GitHub identity");
  }
}

export async function promoteE2BResult(
  job: VerificationJobCoordinates,
  result: Extract<E2BVerificationResult, { status: "verified" }>,
): Promise<PromotionResult> {
  assertE2BResultMatchesJob(job, result);
  const bundle = await readE2BSubmissionBundle(job.sandboxId, job.jobId);
  return promoteVerifiedSubmission({
    baseCommitSha: job.baseCommitSha,
    previousRecordId: job.previousRecordId,
    proofDigest: job.proofDigest,
    issuedAt: job.issuedAt,
    manifest: bundle.manifest,
    solution: bundle.solution,
    result,
  });
}
