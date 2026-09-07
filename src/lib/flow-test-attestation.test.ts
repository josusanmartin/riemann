import { describe, expect, it } from "vitest";
import { validateFlowTestAttestation } from "./flow-test-attestation";
import { prepareFlowTestSubmission } from "./flow-test-server";
import { flowTestRecord, flowTestSolutionSource } from "./flow-test";
import { contract } from "./records";
import { rationalToDecimal } from "./challenge";
import type { E2BVerificationResult } from "./e2b-verifier";
import { computeTrustedMaterialDigest, computeVerifierTemplateDigest } from "../../scripts/trusted-material";

describe("flow-test publication gate", () => {
  it("checks the exact source and both fingerprints, not just the score", async () => {
    const prepared = prepareFlowTestSubmission({ solution: flowTestSolutionSource }, "solver", "Solver");
    const result: Extract<E2BVerificationResult, { status: "verified" }> = {
      schemaVersion: 1, status: "verified", submissionId: prepared.submission.id,
      proofDigest: prepared.proofDigest, completedAt: new Date().toISOString(), log: "",
      attestation: {
        schemaVersion: 1, result: "kernel-verified", submissionId: prepared.submission.id,
        author: prepared.submission.author, model: prepared.submission.model, harness: prepared.submission.harness,
        score: prepared.submission.score, scoreDecimal: rationalToDecimal("2", "3", 30),
        previousRecordId: flowTestRecord.id, upstreamCommit: contract.trustedUpstream.commit,
        theoremNames: [contract.theorems.strictImprovement, contract.theorems.dyadicBound, contract.theorems.cumulativeBound],
        verifiedAt: new Date().toISOString(), kernels: ["lean", "nanoda"], permittedAxioms: contract.permittedAxioms,
        challengeDigest: await computeTrustedMaterialDigest(process.cwd(), contract.trustedPaths, {
          "data/records.json": `${JSON.stringify([flowTestRecord], null, 2)}\n`,
        }),
        verifierTemplateDigest: await computeVerifierTemplateDigest(process.cwd(), contract.trustedPaths),
      },
    };
    await expect(validateFlowTestAttestation(result, prepared)).resolves.toBeUndefined();
    await expect(validateFlowTestAttestation(result, { ...prepared, solution: prepared.solution + "\n" })).rejects.toThrow("digest");
    await expect(validateFlowTestAttestation({ ...result, attestation: { ...result.attestation, verifierTemplateDigest: "0".repeat(64) } }, prepared)).rejects.toThrow("stale");
    await expect(validateFlowTestAttestation({ ...result, attestation: { ...result.attestation, challengeDigest: "0".repeat(64) } }, prepared)).rejects.toThrow("changed");
  });
});
