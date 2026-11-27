import { assertValidAttestation } from "./attestation";
import { submissionSchema } from "./challenge";
import { computeDirectProofDigest } from "./direct-submission";
import type { E2BSubmissionBundle, E2BVerificationResult } from "./e2b-verifier";
import { flowTestRecord } from "./flow-test";
import { contract } from "./records";
import { publicationDigests } from "./publication-material";

/** The test-only lane must exercise the same attestation gate as publication. */
export async function validateFlowTestAttestation(
  result: Extract<E2BVerificationResult, { status: "verified" }>,
  bundle: E2BSubmissionBundle,
) {
  const submission = submissionSchema.parse(JSON.parse(bundle.manifest));
  if (computeDirectProofDigest(bundle.manifest, bundle.solution) !== result.proofDigest) {
    throw new Error("Flow-test source does not match the submitted digest");
  }
  const { challenge: challengeDigest, template: templateDigest } = await publicationDigests(
    `${JSON.stringify([flowTestRecord], null, 2)}\n`,
  );
  assertValidAttestation(submission, result.attestation, contract, challengeDigest, templateDigest);
}
