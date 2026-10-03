import { readFile, writeFile } from "node:fs/promises";
import { join, resolve } from "node:path";
import contractJson from "../challenge/contract.json";
import {
  compareRationals,
  contractSchema,
  recordsSchema,
  submissionSchema,
  verificationAttestationSchema,
} from "../src/lib/challenge";
import {
  assertCurrentRecord,
  buildRecordEntry,
} from "../src/lib/github-promotion";
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
// Same record shape and current-record checks as automatic promotion, so the
// manual and automatic paths cannot drift apart.
assertCurrentRecord(records, submission, attestation.previousRecordId);
const record = buildRecordEntry(submission, attestation, { sourceUrl, proofUrl });
records.push(record);

await writeFile(recordsPath, `${JSON.stringify(records, null, 2)}\n`);
console.log(`Promoted ${submission.id} to ${record.scoreDecimal}.`);
