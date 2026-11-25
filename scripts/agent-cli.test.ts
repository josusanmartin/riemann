import { spawnSync } from "node:child_process";
import { mkdtempSync, readFileSync, rmSync, statSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { join, resolve } from "node:path";
import { afterEach, beforeEach, expect, it } from "vitest";

const cli = resolve("public/cli/riemann.mjs");
const metadata = resolve("public/cli/candidate.example.json");
const digest = "a".repeat(64);
const fixture = { status: "queued", jobToken: "private-job", submissionId: "my-critical-line-bound", proofDigest: digest };
let dir: string;
let proof: string;
let receipt: string;
beforeEach(() => {
  dir = mkdtempSync(join(tmpdir(), "riemann-cli-"));
  proof = join(dir, "Solution.lean");
  receipt = join(dir, "job.json");
  writeFileSync(proof, "-- UTF-8 fixture ∀ ε\r\n");
});
afterEach(() => rmSync(dir, { recursive: true, force: true }));

function run(args: string[], url?: string, response?: object, httpStatus = 200) {
  const preload = join(dir, "mock.mjs");
  writeFileSync(preload, `
    import assert from "node:assert/strict";
    import { appendFileSync } from "node:fs";
    globalThis.fetch = async (url, init) => {
      assert.equal(url, ${JSON.stringify("https://www.riemannzeta.fun" + url)});
      assert.equal(init.redirect, "error");
      assert.equal(init.headers.Authorization, "Bearer private-identity");
      appendFileSync(${JSON.stringify(join(dir, "requests.jsonl"))}, JSON.stringify(init) + "\\n");
      return Response.json(${JSON.stringify(response ?? {})}, { status: ${httpStatus} });
    };
  `);
  return spawnSync(process.execPath, ["--import", preload, cli, ...args], {
    encoding: "utf8", env: { ...process.env, RIEMANN_GITHUB_TOKEN: "private-identity" },
  });
}
const submitArgs = () => ["submit", proof, "--metadata", metadata, "--receipt", receipt];

it("validates exact source and metadata offline and requires explicit licensing before submission", () => {
  const dry = run([...submitArgs(), "--dry-run"]);
  expect(dry.status).toBe(0);
  expect(JSON.parse(dry.stdout)).toMatchObject({ status: "validated-locally", sourceBytes: statSync(proof).size });
  const missingLicense = run(submitArgs());
  expect(missingLicense.status).toBe(1);
  expect(missingLicense.stderr).toContain("--accept-license");
  const invalid = join(dir, "invalid.json");
  writeFileSync(invalid, JSON.stringify({ ...JSON.parse(readFileSync(metadata, "utf8")), score: { numerator: 1, denominator: 2 } }));
  expect(run(["submit", proof, "--metadata", invalid, "--dry-run"]).status).toBe(1);
});

it("submits once, saves a private receipt and reads the terminal verdict with a header", () => {
  const submit = run([...submitArgs(), "--accept-license"], "/api/submissions", fixture, 202);
  expect(submit.status, submit.stderr).toBe(0);
  expect(JSON.parse(submit.stdout)).toMatchObject({ receipt, proofDigest: digest, status: "queued" });
  expect(submit.stdout + submit.stderr).not.toMatch(/private-job|private-identity/);
  expect(statSync(receipt).mode & 0o777).toBe(0o600);
  const post = JSON.parse(readFileSync(join(dir, "requests.jsonl"), "utf8"));
  expect(post.method).toBe("POST");
  expect(JSON.parse(post.body)).toMatchObject({ solution: readFileSync(proof, "utf8"), acceptLicense: true, score: { numerator: "669", denominator: "800" } });
  const check = run(["status", receipt, "--wait"], "/api/submissions/status", {
    status: "verified", submissionId: fixture.submissionId, proofDigest: digest, promotion: { status: "promoted", evidenceUrl: "https://example.org/proof" },
  });
  expect(check.status, check.stderr).toBe(0);
  const get = JSON.parse(readFileSync(join(dir, "requests.jsonl"), "utf8").trim().split("\n")[1]);
  expect(get.headers["X-Verification-Job"]).toBe("private-job");
  expect(run([...submitArgs(), "--accept-license"]).status).toBe(1);
  expect(readFileSync(join(dir, "requests.jsonl"), "utf8").trim().split("\n")).toHaveLength(2);
});

it("recovers an active receipt and distinguishes rejection from an API error", () => {
  expect(run(["active", "--receipt", receipt], "/api/submissions/active", fixture).status).toBe(0);
  const rejected = run(["status", receipt, "--log"], "/api/submissions/status", { status: "rejected", proofDigest: digest, log: "Lean diagnostic" });
  expect(rejected.status).toBe(2);
  expect(JSON.parse(rejected.stdout).log).toBe("Lean diagnostic");
  const limited = run(["status", receipt], "/api/submissions/status", { error: "daily_submission_limit", retryAt: "00:00 UTC" }, 429);
  expect(limited.status).toBe(1);
  expect(JSON.parse(limited.stderr)).toMatchObject({ httpStatus: 429, retryAt: "00:00 UTC" });
});

it("keeps a headless website login private, uses it for whoami and clears it on logout", () => {
  const preload = join(dir, "login-service.mjs");
  const approval = "a".repeat(120);
  writeFileSync(preload, `
    import assert from "node:assert/strict";
    import { createHash } from "node:crypto";
    import { readFileSync } from "node:fs";
    globalThis.fetch = async (url, init) => {
      assert.equal(url, "https://www.riemannzeta.fun/api/cli/session");
      const [verifier, approval] = init.headers.Authorization.slice("Bearer rcli1_".length).split("~");
      assert.equal(approval, ${JSON.stringify(approval)});
      const challenge = createHash("sha256").update(verifier).digest("base64url");
      assert.equal(challenge, readFileSync(${JSON.stringify(join(dir, "challenge"))}, "utf8"));
      return Response.json({ githubLogin: "cli-solver", source: "website-login", expires: new Date(Date.now() + 86400000).toISOString() });
    };
  `);
  function command(args: string[], input?: string) {
    return spawnSync(process.execPath, ["--import", preload, cli, ...args], {
      input, encoding: "utf8", env: { ...process.env, RIEMANN_CONFIG_DIR: dir, RIEMANN_GITHUB_TOKEN: "" },
    });
  }
  const start = JSON.parse(command(["login", "--manual"]).stdout);
  const challenge = new URL(start.url).searchParams.get("challenge")!;
  expect(start.code).toBe(challenge.slice(0, 8));
  expect(start.verifier).toBeUndefined();
  writeFileSync(join(dir, "challenge"), challenge);
  const finish = command(["login", "--finish"], approval + "\n");
  expect(finish.status, finish.stderr).toBe(0);
  expect(finish.stdout + finish.stderr).not.toContain(approval);
  expect(statSync(join(dir, "session.json")).mode & 0o777).toBe(0o600);
  expect(JSON.parse(command(["whoami"]).stdout).githubLogin).toBe("cli-solver");
  expect(command(["logout"]).status).toBe(0);
  expect(command(["whoami"]).status).toBe(1);
});

it("traces HTTP failures with field advice without logging credentials, signed handles or source", () => {
  const error = { error: "invalid_submission", message: "Check the summary", issues: [{ field: "summary", message: "Too short" }] };
  const result = run([...submitArgs(), "--accept-license", "--verbose"], "/api/submissions", error, 400);
  const lines = result.stderr.trim().split("\n").map(line => JSON.parse(line));
  expect(lines[0]).toMatchObject({ event: "request", method: "POST", path: "/api/submissions" });
  expect(lines[1]).toMatchObject({ event: "response", httpStatus: 400, elapsedMs: expect.any(Number) });
  expect(lines[2]).toMatchObject({ issues: error.issues });
  expect(result.stderr).not.toMatch(/private-identity|private-job|UTF-8 fixture/);
});
