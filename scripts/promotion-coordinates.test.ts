import { describe, expect, it } from "vitest";
import type { PromotionMetadata } from "../src/lib/challenge";
import {
  type GitHubPullRequest,
  validatePromotionCoordinates,
} from "./promotion-coordinates";

const metadata: PromotionMetadata = {
  schemaVersion: 1,
  workflowRunId: "31415926535",
  pullRequestNumber: 42,
  headSha: "a".repeat(40),
  headRepository: "outside-solver/riemann",
  headRef: "proof/better-bound",
  baseSha: "b".repeat(40),
  baseRepository: "josusanmartin/riemann",
  baseRef: "main",
};

const trigger = {
  workflowRunId: metadata.workflowRunId,
  headRepository: metadata.headRepository,
  headRef: metadata.headRef,
  repository: metadata.baseRepository,
};

const pullRequest: GitHubPullRequest = {
  number: metadata.pullRequestNumber,
  state: "open",
  draft: false,
  user: { login: "outside-solver" },
  head: {
    sha: metadata.headSha,
    ref: metadata.headRef,
    repo: { full_name: metadata.headRepository },
  },
  base: {
    sha: metadata.baseSha,
    ref: metadata.baseRef,
    repo: { full_name: metadata.baseRepository },
  },
};

describe("privileged promotion coordinates", () => {
  it("accepts an exact external-fork head even when workflow_run omits its PR array", () => {
    expect(() => validatePromotionCoordinates(metadata, trigger, pullRequest)).not.toThrow();
  });

  it("rejects a head swap after the unprivileged verifier succeeds", () => {
    expect(() =>
      validatePromotionCoordinates(metadata, trigger, {
        ...pullRequest,
        head: { ...pullRequest.head, sha: "c".repeat(40) },
      }),
    ).toThrow("head changed");
  });

  it("rejects draft and non-main promotion targets", () => {
    expect(() =>
      validatePromotionCoordinates(metadata, trigger, {
        ...pullRequest,
        draft: true,
      }),
    ).toThrow("Draft submissions");

    expect(() =>
      validatePromotionCoordinates(
        { ...metadata, baseRef: "release" },
        trigger,
        { ...pullRequest, base: { ...pullRequest.base, ref: "release" } },
      ),
    ).toThrow("main branch");
  });
});
