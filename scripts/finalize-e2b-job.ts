import { kernelOomMessage } from "../src/lib/verifier-feedback";
import { constants } from "node:fs";
import { chmod, open, readFile, rename, writeFile } from "node:fs/promises";
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

// Read from one open descriptor. The diagnostic tail is bounded even if the
// checker wrote a very large log, and the attestation must fit its size limit.
async function readVerifierFile(path: string, maxBytes: number, tail = false) {
  const file = await open(resolve(path), constants.O_RDONLY | constants.O_NOFOLLOW | constants.O_NONBLOCK);
  try {
    const info = await file.stat();
    if (!info.isFile() || (!tail && info.size > maxBytes)) throw new Error("Invalid verifier output file");
    const buffer = Buffer.alloc(Math.min(info.size, maxBytes));
    let read = 0;
    const start = tail ? info.size - buffer.length : 0;
    while (read < buffer.length) {
      const { bytesRead } = await file.read(buffer, read, buffer.length - read, start + read);
      if (!bytesRead) break;
      read += bytesRead;
    }
    return buffer.toString("utf8", 0, read);
  } finally {
    await file.close();
  }
}
const log = (await readVerifierFile(logArgument, 400_000, true).catch(() => ""))
  .replace(/\u0000/g, "")
  .slice(-100_000);
const completedAt = new Date().toISOString();
const exitCode = Number(exitCodeArgument);
let result: object;

if (exitCode === 0) {
  const contract = contractSchema.parse(contractJson);
  const attestation = verificationAttestationSchema.parse(
    JSON.parse(await readVerifierFile(artifactArgument, 65_536)),
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
      process.env.RIEMANN_KERNEL_OOM === "1"
        ? kernelOomMessage
        : exitCode === 124 || exitCode === 137
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
