import { chmod, readFile, rename, writeFile } from "node:fs/promises";
import { resolve } from "node:path";
import contractJson from "../challenge/contract.json";
import {
  contractSchema,
  submissionSchema,
  verificationAttestationSchema,
} from "../src/lib/challenge";
import { assertValidAttestation } from "../src/lib/attestation";
import { computeDirectProofDigest } from "../src/lib/direct-submission";
import {
  computeTrustedMaterialDigest,
  computeVerifierTemplateDigest,
} from "./trusted-material";

const [
  submissionArgument,
  artifactArgument,
  logArgument,
  resultArgument,
  expectedDigest,
  exitCodeArgument,
] = process.argv.slice(2);

if (
  !submissionArgument ||
  !artifactArgument ||
  !logArgument ||
  !resultArgument ||
  !expectedDigest ||
  !exitCodeArgument
) {
  throw new Error(
    "Usage: finalize-e2b-job.ts <submission-dir> <attestation> <log> <result> <proof-digest> <exit-code>",
  );
}
if (!/^[0-9a-f]{64}$/.test(expectedDigest)) {
  throw new Error("Expected proof digest must be SHA-256");
}
if (!/^\d{1,3}$/.test(exitCodeArgument)) {
  throw new Error("Verifier exit code is invalid");
}

const repositoryRoot = resolve(import.meta.dirname, "..");
const submissionDirectory = resolve(submissionArgument);
const resultPath = resolve(resultArgument);
const temporaryResultPath = `${resultPath}.tmp`;
const manifest = await readFile(
  resolve(submissionDirectory, "submission.json"),
  "utf8",
);
const submission = submissionSchema.parse(JSON.parse(manifest));
const solution = await readFile(
  resolve(submissionDirectory, submission.proof.solution),
  "utf8",
);
const actualDigest = computeDirectProofDigest(manifest, solution);
if (actualDigest !== expectedDigest) {
  throw new Error("The immutable uploaded source no longer matches its digest");
}

const log = (await readFile(resolve(logArgument), "utf8").catch(() => ""))
  .replace(/\u0000/g, "")
  .slice(-100_000);
const completedAt = new Date().toISOString();
const exitCode = Number(exitCodeArgument);
let result: object;

if (exitCode === 0) {
  const contract = contractSchema.parse(contractJson);
  const attestation = verificationAttestationSchema.parse(
    JSON.parse(await readFile(resolve(artifactArgument), "utf8")),
  );
  const [challengeDigest, verifierTemplateDigest] = await Promise.all([
    computeTrustedMaterialDigest(repositoryRoot, contract.trustedPaths, {
      "data/records.json": await readFile(
        resolve(submissionDirectory, "trusted-records.json"),
      ),
    }),
    computeVerifierTemplateDigest(repositoryRoot, contract.trustedPaths),
  ]);
  assertValidAttestation(
    submission,
    attestation,
    contract,
    challengeDigest,
    verifierTemplateDigest,
  );
  result = {
    schemaVersion: 1,
    status: "verified",
    submissionId: submission.id,
    proofDigest: actualDigest,
    completedAt,
    log,
    attestation,
  };
} else {
  result = {
    schemaVersion: 1,
    status: "rejected",
    submissionId: submission.id,
    proofDigest: actualDigest,
    completedAt,
    log,
    message:
      exitCode === 124 || exitCode === 137
        ? "The verifier exceeded its isolated runtime limit."
        : `The formal verifier exited with status ${exitCode}.`,
  };
}

await writeFile(temporaryResultPath, `${JSON.stringify(result, null, 2)}\n`, {
  flag: "wx",
  mode: 0o400,
});
await rename(temporaryResultPath, resultPath);
await chmod(resultPath, 0o444);
