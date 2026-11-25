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

// Bound diagnostic reads even when the checker generated a very large file.
async function readVerifierFile(path: string, maxBytes: number, mode: "file" | "tail" | "rejection" = "file") {
  const file = await open(resolve(path), constants.O_RDONLY | constants.O_NOFOLLOW | constants.O_NONBLOCK);
  try {
    const info = await file.stat();
    if (!info.isFile() || (mode === "file" && info.size > maxBytes)) throw new Error("Invalid verifier output file");
    async function range(start: number, size: number) {
      const buffer = Buffer.alloc(size);
      let read = 0;
      while (read < size) {
        const { bytesRead } = await file.read(buffer, read, size - read, start + read);
        if (!bytesRead) break;
        read += bytesRead;
      }
      return buffer.toString("utf8", 0, read);
    }
    if (mode === "file") return await range(0, info.size);
    const clean = (value: string) => value.replace(/\u0000/g, "");
    const size = Math.min(info.size, maxBytes);
    const marker = "\n[... middle of verifier output omitted ...]\n";
    if (mode === "rejection" && info.size > maxBytes) {
      const first = clean(await range(0, 100_000)).slice(0, 20_000);
      const last = clean(await range(info.size - 300_000, 300_000));
      return first + marker + last.slice(-(100_000 - first.length - marker.length));
    }
    const output = clean(await range(info.size - size, size));
    if (mode === "rejection" && output.length > 100_000) {
      return output.slice(0, 20_000) + marker + output.slice(-(80_000 - marker.length));
    }
    return output.slice(-100_000);
  } finally {
    await file.close();
  }
}
const exitCode = Number(exitCodeArgument);
const log = await readVerifierFile(logArgument, 400_000, exitCode === 0 ? "tail" : "rejection").catch(() => "");
const completedAt = new Date().toISOString();
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
