import { execFileSync } from "node:child_process";
import { lstat, readFile } from "node:fs/promises";
import { dirname, join, posix, resolve } from "node:path";
import { githubLoginSchema, submissionSchema } from "../src/lib/challenge";

const [checkoutArgument, baseSha, headSha, expectedGitHubArgument] =
  process.argv.slice(2);
if (!checkoutArgument || !baseSha || !headSha) {
  throw new Error(
    "Usage: check-submission-pr.ts <candidate-checkout> <base-sha> <head-sha> [expected-github-login]",
  );
}
if (!/^[0-9a-f]{40}$/.test(baseSha) || !/^[0-9a-f]{40}$/.test(headSha)) {
  throw new Error("Base and head revisions must be full Git commit hashes");
}

const checkout = resolve(checkoutArgument);
const checkedOutHead = execFileSync("git", ["rev-parse", "HEAD"], {
  cwd: checkout,
  encoding: "utf8",
}).trim();
if (checkedOutHead !== headSha) {
  throw new Error(
    `Candidate checkout mismatch: expected ${headSha}, received ${checkedOutHead}`,
  );
}
const mergeBase = execFileSync("git", ["merge-base", baseSha, headSha], {
  cwd: checkout,
  encoding: "utf8",
}).trim();
if (!/^[0-9a-f]{40}$/.test(mergeBase)) {
  throw new Error("Unable to resolve the pull request's merge base");
}
const output = execFileSync(
  "git",
  ["diff", "--name-status", "-z", mergeBase, headSha, "--"],
  { cwd: checkout },
);
const fields = output.toString("utf8").split("\0").filter(Boolean);
const changedFiles: Array<{ status: string; path: string }> = [];

for (let index = 0; index < fields.length; ) {
  const status = fields[index++];
  if (status.startsWith("R") || status.startsWith("C")) {
    index += 1;
    const destination = fields[index++];
    changedFiles.push({ status, path: destination });
  } else {
    changedFiles.push({ status, path: fields[index++] });
  }
}

const manifests = changedFiles.filter(
  (file) =>
    file.status === "A" &&
    /^submissions\/[a-z0-9][a-z0-9-]*\/submission\.json$/.test(file.path),
);
if (manifests.length !== 1) {
  throw new Error("A submission PR must add exactly one submissions/<id>/submission.json");
}

const submissionRoot = posix.dirname(manifests[0].path);
if (submissionRoot === "submissions/example") {
  throw new Error("The documentation example cannot be submitted");
}
if (changedFiles.length > 257) {
  throw new Error("A submission may add at most 256 Lean files and one manifest");
}

let totalBytes = 0;
for (const file of changedFiles) {
  if (file.status !== "A") {
    throw new Error(`Submission PRs may only add files; found ${file.status} ${file.path}`);
  }
  if (!file.path.startsWith(`${submissionRoot}/`)) {
    throw new Error(`Submission PR changed an out-of-scope file: ${file.path}`);
  }
  const isManifest = file.path === `${submissionRoot}/submission.json`;
  const isLeanProof = new RegExp(
    `^${submissionRoot.replace(/[.*+?^${}()|[\]\\]/g, "\\$&")}/proof/(?:[A-Za-z][A-Za-z0-9_]*/)*[A-Za-z][A-Za-z0-9_]*\\.lean$`,
  ).test(file.path);
  if (!isManifest && !isLeanProof) {
    throw new Error(`Only submission.json and regular Lean files under proof/ are accepted: ${file.path}`);
  }
  const info = await lstat(join(checkout, file.path));
  if (!info.isFile() || info.isSymbolicLink()) {
    throw new Error(`Submission entries must be regular files: ${file.path}`);
  }
  if (isLeanProof && info.size > 2_000_000) {
    throw new Error(`Lean source file exceeds the 2 MB limit: ${file.path}`);
  }
  totalBytes += info.size;
}
if (totalBytes > 20_100_000) {
  throw new Error("A submission may contain at most 20 MB of source and manifest data");
}

const submission = submissionSchema.parse(
  JSON.parse(await readFile(join(checkout, manifests[0].path), "utf8")),
);
if (expectedGitHubArgument) {
  const expectedGitHub = githubLoginSchema.parse(expectedGitHubArgument);
  if (submission.author.github.toLowerCase() !== expectedGitHub.toLowerCase()) {
    throw new Error(
      `submission.author.github must match the pull-request author @${expectedGitHub}`,
    );
  }
}
if (dirname(manifests[0].path) !== `submissions/${submission.id}`) {
  throw new Error("submission.id must match its directory name");
}
if (!changedFiles.some((file) => file.path === `${submissionRoot}/${submission.proof.solution}`)) {
  throw new Error("The manifest's proof.solution must be added in the same pull request");
}

process.stdout.write(join(checkout, submissionRoot));
