import {
  compareRationals,
  rationalToDecimal,
  type ChallengeContract,
  type Submission,
  type VerificationAttestation,
} from "@/lib/challenge";

export function assertValidAttestation(
  submission: Submission,
  attestation: VerificationAttestation,
  contract: ChallengeContract,
  challengeDigest: string,
  verifierTemplateDigest: string,
): void {
  if (attestation.submissionId !== submission.id) {
    throw new Error("Attestation belongs to a different submission");
  }
  if (
    attestation.author.github.toLowerCase() !==
      submission.author.github.toLowerCase() ||
    attestation.author.displayName !== submission.author.displayName
  ) {
    throw new Error("Attested author differs from the authenticated submission");
  }
  if (attestation.upstreamCommit !== contract.trustedUpstream.commit) {
    throw new Error("Attestation used a different trusted upstream commit");
  }
  if (
    JSON.stringify(attestation.theoremNames) !==
    JSON.stringify([
      contract.theorems.strictImprovement,
      contract.theorems.dyadicBound,
      contract.theorems.cumulativeBound,
    ])
  ) {
    throw new Error("Attestation theorem set differs from the current contract");
  }
  if (
    JSON.stringify(attestation.permittedAxioms) !==
    JSON.stringify(contract.permittedAxioms)
  ) {
    throw new Error("Attestation axiom policy differs from the current contract");
  }
  if (compareRationals(attestation.score, submission.score) !== 0) {
    throw new Error("Attested score differs from submission score");
  }
  if (
    attestation.scoreDecimal !==
    rationalToDecimal(
      submission.score.numerator,
      submission.score.denominator,
      30,
    )
  ) {
    throw new Error("Attested decimal differs from the exact submission score");
  }
  if (attestation.verifierTemplateDigest !== verifierTemplateDigest) {
    throw new Error(
      "Verifier template is stale; rebuild the pinned E2B template before accepting submissions",
    );
  }
  if (attestation.challengeDigest !== challengeDigest) {
    throw new Error("Trusted challenge material changed after verification");
  }
}
