import { appendFile, lstat, readFile } from "node:fs/promises";
import { resolve } from "node:path";
import {
  githubRefSchema,
  githubRepositorySchema,
  promotionMetadataSchema,
} from "../src/lib/challenge";
import {
  githubPullRequestSchema,
  validatePromotionCoordinates,
} from "./promotion-coordinates";

const [metadataArgument] = process.argv.slice(2);
if (!metadataArgument) {
  throw new Error("Usage: resolve-promotion-pr.ts <promotion-metadata.json>");
}

function requiredEnvironment(name: string): string {
  const value = process.env[name];
  if (!value) throw new Error(`${name} is required`);
  return value;
}

const repository = githubRepositorySchema.parse(
  requiredEnvironment("GITHUB_REPOSITORY"),
);
const token = requiredEnvironment("GITHUB_TOKEN");
const outputPath = resolve(requiredEnvironment("GITHUB_OUTPUT"));
const triggerRunId = requiredEnvironment("TRIGGER_WORKFLOW_RUN_ID");
const triggerHeadRepository = githubRepositorySchema.parse(
  requiredEnvironment("TRIGGER_HEAD_REPOSITORY"),
);
const triggerHeadRef = githubRefSchema.parse(
  requiredEnvironment("TRIGGER_HEAD_REF"),
);
const triggerPullRequest = process.env.TRIGGER_PR_NUMBER?.trim();
if (triggerPullRequest && !/^\d+$/.test(triggerPullRequest)) {
  throw new Error("TRIGGER_PR_NUMBER must be an integer when present");
}

const metadataPath = resolve(metadataArgument);
const metadataInfo = await lstat(metadataPath);
if (!metadataInfo.isFile() || metadataInfo.isSymbolicLink() || metadataInfo.size > 4096) {
  throw new Error("Promotion metadata must be one regular JSON file no larger than 4 KiB");
}
const metadata = promotionMetadataSchema.parse(
  JSON.parse(await readFile(metadataPath, "utf8")),
);

const [owner, name] = repository.split("/").map(encodeURIComponent);
const response = await fetch(
  `https://api.github.com/repos/${owner}/${name}/pulls/${metadata.pullRequestNumber}`,
  {
    headers: {
      Accept: "application/vnd.github+json",
      Authorization: `Bearer ${token}`,
      "User-Agent": "riemann-fail-promotion",
      "X-GitHub-Api-Version": "2022-11-28",
    },
  },
);
if (!response.ok) {
  throw new Error(
    `GitHub pull-request lookup failed with ${response.status} ${response.statusText}`,
  );
}

const pullRequest = githubPullRequestSchema.parse(await response.json());
validatePromotionCoordinates(
  metadata,
  {
    workflowRunId: triggerRunId,
    pullRequestNumber: triggerPullRequest ? Number(triggerPullRequest) : undefined,
    headRepository: triggerHeadRepository,
    headRef: triggerHeadRef,
    repository,
  },
  pullRequest,
);

await appendFile(
  outputPath,
  [
    `pr_number=${pullRequest.number}`,
    `head_sha=${pullRequest.head.sha}`,
    `head_repository=${pullRequest.head.repo.full_name}`,
    `base_sha=${pullRequest.base.sha}`,
    `author_login=${pullRequest.user.login}`,
  ].join("\n") + "\n",
);

console.log(
  `Resolved open PR #${pullRequest.number} at exact head ${pullRequest.head.sha}.`,
);
