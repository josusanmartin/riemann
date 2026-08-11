import { createHash } from "node:crypto";
import {
  compareRationals,
  directSubmissionInputSchema,
  githubLoginSchema,
  submissionSchema,
  type DirectSubmissionInput,
  type RecordEntry,
  type Submission,
} from "@/lib/challenge";

export const MAX_DIRECT_SOLUTION_BYTES = 2_000_000;

export type PreparedDirectSubmission = {
  submission: Submission;
  manifest: string;
  solution: string;
  proofDigest: string;
};

export function computeDirectProofDigest(
  manifest: string,
  solution: string,
): string {
  return createHash("sha256")
    .update("submission.json\0")
    .update(manifest)
    .update("proof/Solution.lean\0")
    .update(solution)
    .digest("hex");
}

export function prepareDirectSubmission(
  rawInput: unknown,
  authenticatedGithub: string,
  currentRecord: RecordEntry,
): PreparedDirectSubmission {
  const input: DirectSubmissionInput = directSubmissionInputSchema.parse(rawInput);
  const github = githubLoginSchema.parse(authenticatedGithub);
  const solutionBytes = Buffer.byteLength(input.solution, "utf8");
  if (solutionBytes > MAX_DIRECT_SOLUTION_BYTES) {
    throw new Error("Solution.lean exceeds the 2 MB source limit");
  }
  if (compareRationals(input.score, { numerator: "1", denominator: "1" }) > 0) {
    throw new Error("A critical-line proportion cannot exceed one");
  }
  // The immutable Zeta23 baseline is an exact Lean expression involving cMT,
  // not a rational. Lean's candidate_strict_improvement theorem is therefore
  // the authority for the first direct submission. Once a rational candidate
  // has been promoted, this inexpensive exact precheck rejects stale scores
  // before spending an E2B verification slot.
  if (
    currentRecord.exactRational &&
    compareRationals(input.score, currentRecord.exactRational) <= 0
  ) {
    throw new Error("The submitted rational must strictly exceed the current record");
  }

  const submission = submissionSchema.parse({
    schemaVersion: 1,
    id: input.id,
    track: "critical-line",
    author: { github, displayName: input.displayName },
    score: input.score,
    proof: {
      solution: "proof/Solution.lean",
      theorem: "candidate_critical_line_bound",
      cumulativeTheorem: "candidate_critical_line_bound_cumulative",
      improvementTheorem: "candidate_strict_improvement",
    },
    summary: input.summary,
    method: input.method,
    model: input.model,
    harness: input.harness,
    license: "Apache-2.0",
  });
  const manifest = `${JSON.stringify(submission, null, 2)}\n`;
  const proofDigest = computeDirectProofDigest(manifest, input.solution);

  return { submission, manifest, solution: input.solution, proofDigest };
}
