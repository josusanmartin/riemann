import { readFile, writeFile } from "node:fs/promises";
import { join, resolve } from "node:path";
import contractJson from "../challenge/contract.json";
import {
  compareRationals,
  contractSchema,
  rationalToDecimal,
  recordsSchema,
  submissionSchema,
  verificationAttestationSchema,
} from "../src/lib/challenge";
import {
  computeTrustedMaterialDigest,
  computeVerifierTemplateDigest,
} from "./trusted-material";
import { assertValidAttestation } from "../src/lib/attestation";

const [submissionArgument, artifactArgument, sourceUrl, proofUrl] =
  process.argv.slice(2);
if (!submissionArgument || !artifactArgument || !sourceUrl || !proofUrl) {
  throw new Error(
    "Usage: promote-record.ts <submission-dir> <attestation.json> <source-url> <proof-url>",
  );
}

const submissionDirectory = resolve(submissionArgument);
const repositoryRoot = resolve(import.meta.dirname, "..");
const contract = contractSchema.parse(contractJson);
const submission = submissionSchema.parse(
  JSON.parse(await readFile(resolve(submissionDirectory, "submission.json"), "utf8")),
);
const attestation = verificationAttestationSchema.parse(
  JSON.parse(await readFile(resolve(artifactArgument), "utf8")),
);
if (
  compareRationals(submission.score, { numerator: "1", denominator: "1" }) > 0
) {
  throw new Error("A critical-line proportion cannot exceed one");
}

for (const url of [sourceUrl, proofUrl]) {
  new URL(url);
}

const recordsPath = join(repositoryRoot, "data", "records.json");
const [challengeDigest, verifierTemplateDigest] = await Promise.all([
  computeTrustedMaterialDigest(repositoryRoot, contract.trustedPaths),
  computeVerifierTemplateDigest(repositoryRoot, contract.trustedPaths),
]);
assertValidAttestation(
  submission,
  attestation,
  contract,
  challengeDigest,
  verifierTemplateDigest,
);
const records = recordsSchema.parse(
  JSON.parse(await readFile(recordsPath, "utf8")),
);
if (records.some((record) => record.id === submission.id)) {
  throw new Error(`Record already exists: ${submission.id}`);
}
const current = records
  .filter((record) => record.status === "kernel-verified")
  .at(-1);
if (!current || current.id !== attestation.previousRecordId) {
  throw new Error("The formal record changed after verification; re-run the verifier");
}
if (
  current.exactRational &&
  compareRationals(submission.score, current.exactRational) <= 0
) {
  throw new Error("The submitted rational does not strictly exceed the current exact record");
}

const scoreDecimal = rationalToDecimal(
  submission.score.numerator,
  submission.score.denominator,
  30,
);
const scorePercent = rationalToDecimal(
  (BigInt(submission.score.numerator) * 100n).toString(),
  submission.score.denominator,
  28,
);
records.push({
  id: submission.id,
  track: submission.track,
  date: attestation.verifiedAt.slice(0, 10),
  author: submission.author.displayName,
  github: submission.author.github,
  title: `Certified critical-line bound ${scoreDecimal}`,
  method: submission.method,
  scoreDecimal,
  scorePercent,
  exactRational: submission.score,
  exactExpression: `(${submission.score.numerator} : ℝ) / ${submission.score.denominator}`,
  status: "kernel-verified",
  formalVerification: true,
  independentReview: null,
  sourceUrl,
  proofUrl,
  pullRequestUrl: null,
  summary: submission.summary,
});

await writeFile(recordsPath, `${JSON.stringify(records, null, 2)}\n`);
console.log(`Promoted ${submission.id} to ${scoreDecimal}.`);
