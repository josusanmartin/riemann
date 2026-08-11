import { readFile, writeFile } from "node:fs/promises";
import { join, resolve } from "node:path";
import { z } from "zod";
import contractJson from "../challenge/contract.json";
import {
  compareRationals,
  contractSchema,
  rationalToDecimal,
  recordsSchema,
  submissionSchema,
} from "../src/lib/challenge";
import { computeTrustedMaterialDigest } from "./trusted-material";

const [submissionArgument, artifactArgument, sourceUrl, proofUrl, pullRequestUrl] =
  process.argv.slice(2);
if (!submissionArgument || !artifactArgument || !sourceUrl || !proofUrl) {
  throw new Error(
    "Usage: promote-record.ts <submission-dir> <attestation.json> <source-url> <proof-url> [pull-request-url]",
  );
}

const attestationSchema = z.object({
  schemaVersion: z.literal(1),
  submissionId: z.string(),
  score: z.object({ numerator: z.string(), denominator: z.string() }),
  previousRecordId: z.string(),
  upstreamCommit: z.string().regex(/^[0-9a-f]{40}$/),
  theoremNames: z.array(z.string()).length(3),
  result: z.literal("kernel-verified"),
  verifiedAt: z.string().datetime(),
  challengeDigest: z.string().regex(/^[0-9a-f]{64}$/),
  kernels: z.tuple([z.literal("lean"), z.literal("nanoda")]),
  permittedAxioms: z.array(z.string()),
});

const submissionDirectory = resolve(submissionArgument);
const repositoryRoot = resolve(import.meta.dirname, "..");
const contract = contractSchema.parse(contractJson);
const submission = submissionSchema.parse(
  JSON.parse(await readFile(resolve(submissionDirectory, "submission.json"), "utf8")),
);
const attestation = attestationSchema.parse(
  JSON.parse(await readFile(resolve(artifactArgument), "utf8")),
);
if (attestation.submissionId !== submission.id) {
  throw new Error("Attestation belongs to a different submission");
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
if (
  compareRationals(attestation.score, submission.score) !== 0
) {
  throw new Error("Attested score differs from submission score");
}
if (
  compareRationals(submission.score, { numerator: "1", denominator: "1" }) > 0
) {
  throw new Error("A critical-line proportion cannot exceed one");
}

for (const url of [sourceUrl, proofUrl, pullRequestUrl].filter(Boolean)) {
  new URL(url);
}

const recordsPath = join(repositoryRoot, "data", "records.json");
const challengeDigest = await computeTrustedMaterialDigest(
  repositoryRoot,
  contract.trustedPaths,
);
if (challengeDigest !== attestation.challengeDigest) {
  throw new Error("Trusted challenge material changed after verification");
}
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
  sourceUrl,
  proofUrl,
  pullRequestUrl: pullRequestUrl || null,
  summary: submission.summary,
});

await writeFile(recordsPath, `${JSON.stringify(records, null, 2)}\n`);
console.log(`Promoted ${submission.id} to ${scoreDecimal}.`);
