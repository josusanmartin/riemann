import { z } from "zod";
import {
  githubRefSchema,
  githubLoginSchema,
  githubRepositorySchema,
  gitShaSchema,
  type PromotionMetadata,
} from "../src/lib/challenge";

export const githubPullRequestSchema = z.object({
  number: z.number().int().positive(),
  state: z.literal("open"),
  draft: z.boolean(),
  user: z.object({ login: githubLoginSchema }),
  head: z.object({
    sha: gitShaSchema,
    ref: githubRefSchema,
    repo: z.object({ full_name: githubRepositorySchema }),
  }),
  base: z.object({
    sha: gitShaSchema,
    ref: githubRefSchema,
    repo: z.object({ full_name: githubRepositorySchema }),
  }),
});

export type GitHubPullRequest = z.infer<typeof githubPullRequestSchema>;

export type PromotionTrigger = {
  workflowRunId: string;
  pullRequestNumber?: number;
  headRepository: string;
  headRef: string;
  repository: string;
};

function sameRepository(left: string, right: string): boolean {
  return left.toLowerCase() === right.toLowerCase();
}

export function validatePromotionCoordinates(
  metadata: PromotionMetadata,
  trigger: PromotionTrigger,
  pullRequest: GitHubPullRequest,
): void {
  if (metadata.workflowRunId !== trigger.workflowRunId) {
    throw new Error("Promotion metadata belongs to a different workflow run");
  }
  if (
    trigger.pullRequestNumber !== undefined &&
    metadata.pullRequestNumber !== trigger.pullRequestNumber
  ) {
    throw new Error("Promotion metadata names a different pull request than workflow_run");
  }
  if (!sameRepository(metadata.headRepository, trigger.headRepository)) {
    throw new Error("Promotion metadata names a different head repository than workflow_run");
  }
  if (metadata.headRef !== trigger.headRef) {
    throw new Error("Promotion metadata names a different head ref than workflow_run");
  }
  if (
    !sameRepository(metadata.baseRepository, trigger.repository) ||
    metadata.baseRef !== "main"
  ) {
    throw new Error("Promotion metadata does not target this repository's main branch");
  }
  if (pullRequest.number !== metadata.pullRequestNumber) {
    throw new Error("GitHub returned a different pull request");
  }
  if (pullRequest.draft) {
    throw new Error("Draft submissions are not promoted; mark the pull request ready first");
  }
  if (
    pullRequest.head.sha !== metadata.headSha ||
    pullRequest.head.ref !== metadata.headRef ||
    !sameRepository(pullRequest.head.repo.full_name, metadata.headRepository)
  ) {
    throw new Error("The pull-request head changed after formal verification");
  }
  if (
    pullRequest.base.sha !== metadata.baseSha ||
    pullRequest.base.ref !== metadata.baseRef ||
    !sameRepository(pullRequest.base.repo.full_name, metadata.baseRepository)
  ) {
    throw new Error(
      "The pull-request base changed after formal verification; update the branch and rerun CI",
    );
  }
}
