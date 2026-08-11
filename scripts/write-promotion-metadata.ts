import { mkdir, writeFile } from "node:fs/promises";
import { dirname, resolve } from "node:path";
import { promotionMetadataSchema } from "../src/lib/challenge";

const [outputArgument] = process.argv.slice(2);
if (!outputArgument) {
  throw new Error("Usage: write-promotion-metadata.ts <output.json>");
}

const metadata = promotionMetadataSchema.parse({
  schemaVersion: 1,
  workflowRunId: process.env.WORKFLOW_RUN_ID,
  pullRequestNumber: Number(process.env.PR_NUMBER),
  headSha: process.env.HEAD_SHA,
  headRepository: process.env.HEAD_REPOSITORY,
  headRef: process.env.HEAD_REF,
  baseSha: process.env.BASE_SHA,
  baseRepository: process.env.BASE_REPOSITORY,
  baseRef: process.env.BASE_REF,
});

const outputPath = resolve(outputArgument);
await mkdir(dirname(outputPath), { recursive: true });
await writeFile(outputPath, `${JSON.stringify(metadata, null, 2)}\n`, {
  flag: "wx",
});

console.log(
  `Recorded immutable metadata for PR #${metadata.pullRequestNumber} at ${metadata.headSha}.`,
);
