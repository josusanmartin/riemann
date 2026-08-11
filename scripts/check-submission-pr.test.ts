import { execFileSync, spawnSync } from "node:child_process";
import { mkdir, mkdtemp, rm, writeFile } from "node:fs/promises";
import { tmpdir } from "node:os";
import { join, resolve } from "node:path";
import { afterAll, beforeAll, describe, expect, it } from "vitest";

let repository = "";
let baseSha = "";
let candidateSha = "";

function git(...args: string[]): string {
  return execFileSync("git", args, { cwd: repository, encoding: "utf8" }).trim();
}

function runScope(headSha: string, expectedLogin: string) {
  const result = spawnSync(
    process.execPath,
    [
      resolve("node_modules/tsx/dist/cli.mjs"),
      resolve("scripts/check-submission-pr.ts"),
      repository,
      baseSha,
      headSha,
      expectedLogin,
    ],
    { encoding: "utf8" },
  );
  return {
    status: result.status,
    stdout: result.stdout.trim(),
    stderr: result.stderr.trim(),
  };
}

beforeAll(async () => {
  repository = await mkdtemp(join(tmpdir(), "riemann-scope-test-"));
  git("init", "--quiet", "--initial-branch=main");
  git("config", "user.name", "Riemann Test");
  git("config", "user.email", "test@riemann.invalid");
  await writeFile(join(repository, "README.md"), "trusted base\n");
  git("add", "README.md");
  git("commit", "--quiet", "-m", "base");
  const commonBase = git("rev-parse", "HEAD");

  git("switch", "--quiet", "-c", "candidate");
  const submissionRoot = join(repository, "submissions", "fork-proof");
  await mkdir(join(submissionRoot, "proof"), { recursive: true });
  await writeFile(
    join(submissionRoot, "submission.json"),
    `${JSON.stringify(
      {
        schemaVersion: 1,
        id: "fork-proof",
        track: "critical-line",
        author: { github: "outside-solver", displayName: "Outside Solver" },
        score: { numerator: "672500704", denominator: "1000000000" },
        proof: {
          solution: "proof/Solution.lean",
          theorem: "candidate_critical_line_bound",
          cumulativeTheorem: "candidate_critical_line_bound_cumulative",
          improvementTheorem: "candidate_strict_improvement",
        },
        summary: "A test-only manifest for immutable pull-request scope validation.",
        method: "Test fixture",
        license: "Apache-2.0",
      },
      null,
      2,
    )}\n`,
  );
  await writeFile(join(submissionRoot, "proof", "Solution.lean"), "-- test proof\n");
  git("add", "submissions/fork-proof");
  git("commit", "--quiet", "-m", "candidate");
  candidateSha = git("rev-parse", "HEAD");

  git("switch", "--quiet", "main");
  await writeFile(join(repository, "README.md"), "trusted base advanced\n");
  git("add", "README.md");
  git("commit", "--quiet", "-m", "advance base");
  baseSha = git("rev-parse", "HEAD");
  expect(git("merge-base", baseSha, candidateSha)).toBe(commonBase);
  git("switch", "--quiet", "candidate");
});

afterAll(async () => {
  if (repository) await rm(repository, { recursive: true, force: true });
});

describe("submission pull-request scope", () => {
  it("accepts only the fork's additions when the trusted base has advanced", () => {
    const result = runScope(candidateSha, "outside-solver");
    expect(result.status).toBe(0);
    expect(result.stdout).toBe(
      join(repository, "submissions", "fork-proof"),
    );
  });

  it("binds manifest attribution to the authenticated pull-request author", () => {
    const result = runScope(candidateSha, "different-user");
    expect(result.status).not.toBe(0);
    expect(result.stderr).toContain("submission.author.github must match");
  });

  it("rejects a candidate that also changes a trusted path", async () => {
    await writeFile(join(repository, "README.md"), "candidate changed trusted data\n");
    git("add", "README.md");
    git("commit", "--quiet", "-m", "out-of-scope change");
    const badHead = git("rev-parse", "HEAD");
    const result = runScope(badHead, "outside-solver");
    expect(result.status).not.toBe(0);
    expect(result.stderr).toContain("Submission PRs may only add files");
  });
});
