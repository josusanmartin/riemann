#!/usr/bin/env node
// Riemann proof submission CLI. Requires Node.js 22 or later; no dependencies.
import { constants, mkdir, open, unlink } from "node:fs/promises";
import { homedir } from "node:os";
import { join, resolve } from "node:path";
import { randomUUID } from "node:crypto";
import { setTimeout as sleep } from "node:timers/promises";
import { parseArgs } from "node:util";

const origin = "https://www.riemannzeta.fun";
const help = `Riemann proof submissions · Node.js 22+
  node riemann.mjs record
  node riemann.mjs submit Solution.lean --metadata candidate.json --dry-run
  node riemann.mjs submit Solution.lean --metadata candidate.json --accept-license [--receipt FILE]
  node riemann.mjs status RECEIPT [--wait] [--log]
  node riemann.mjs active [--receipt FILE]

Set RIEMANN_GITHUB_TOKEN to a dedicated GitHub user token for submit, status and active.
Receipts are private files under ~/.riemannzeta/jobs/. See ${origin}/submit/agent`;

const print = data => console.log(JSON.stringify(data));
const fail = message => { throw new Error(message); };

class ApiError extends Error {
  constructor(status, data, retryAfter) {
    super(data.message || data.error || `HTTP ${status}`);
    this.status = status;
    this.code = data.error;
    this.retryAt = data.retryAt;
    this.retryAfter = retryAfter;
  }
}

async function api(path, { authenticated = true, body, jobToken } = {}) {
  const headers = { Accept: "application/json" };
  if (authenticated) {
    const token = process.env.RIEMANN_GITHUB_TOKEN;
    if (!token) fail("Set RIEMANN_GITHUB_TOKEN in the agent's environment.");
    headers.Authorization = "Bearer " + token;
  }
  if (jobToken) headers["X-Verification-Job"] = jobToken;
  if (body !== undefined) headers["Content-Type"] = "application/json";
  const res = await fetch(origin + path, {
    headers, method: body === undefined ? "GET" : "POST", body,
    redirect: "error", signal: AbortSignal.timeout(300_000),
  });
  const data = await res.json().catch(() => null);
  if (!res.ok) throw new ApiError(res.status, data ?? {}, res.headers.get("retry-after"));
  if (!data || typeof data !== "object") fail("The site returned an invalid API response.");
  return data;
}

async function utf8(path, limit) {
  const file = await open(path, constants.O_RDONLY | constants.O_NONBLOCK);
  try {
    const stat = await file.stat();
    if (!stat.isFile() || stat.size > limit) fail(`Expected a regular file of at most ${limit} bytes: ${path}`);
    const bytes = Buffer.alloc(limit + 1);
    let size = 0;
    while (size < bytes.length) {
      const { bytesRead } = await file.read(bytes, size, bytes.length - size);
      if (!bytesRead) break;
      size += bytesRead;
    }
    if (size > limit) fail(`File exceeds ${limit} bytes: ${path}`);
    return new TextDecoder("utf-8", { fatal: true, ignoreBOM: true }).decode(bytes.subarray(0, size));
  } finally {
    await file.close();
  }
}

async function buildSubmission(solutionFile, metadataFile) {
  const m = JSON.parse(await utf8(metadataFile, 32_000));
  const allowed = ["id", "displayName", "score", "summary", "method", "model", "harness"];
  if (!m || Array.isArray(m) || typeof m !== "object" || Object.keys(m).some(k => !allowed.includes(k))) fail("Unexpected metadata fields. See the agent guide.");
  if (typeof m.id !== "string" || !/^[a-z0-9][a-z0-9-]{0,79}$/.test(m.id)) fail("Invalid submission id.");
  for (const [key, min, max] of [["displayName", 1, 100], ["summary", 20, 1000], ["method", 3, 200], ["model", 1, 80], ["harness", 1, 80]]) {
    if ((key === "model" || key === "harness") && m[key] == null) continue;
    if (typeof m[key] !== "string" || m[key].trim().length < min || m[key].trim().length > max) fail(`${key} must have ${min}–${max} characters.`);
  }
  const { numerator, denominator } = m.score ?? {};
  if (!m.score || Object.keys(m.score).length !== 2 || [numerator, denominator].some(v => typeof v !== "string" || !/^[1-9]\d{0,199}$/.test(v))) fail("score requires positive numerator and denominator strings of at most 200 digits.");
  if (BigInt(numerator) > BigInt(denominator)) fail("The bound cannot exceed one.");
  const solution = await utf8(solutionFile, 2_000_000);
  if (!solution.trim()) fail("The Lean file is empty.");
  const body = JSON.stringify({ ...m, solution, acceptLicense: true });
  if (Buffer.byteLength(body) > 4_000_000) fail("The encoded request exceeds 4 MB.");
  return { id: m.id, body, score: m.score, sourceBytes: Buffer.byteLength(solution) };
}

async function newReceipt(customPath) {
  let path;
  if (customPath) {
    path = resolve(customPath);
  } else {
    const dir = join(homedir(), ".riemannzeta", "jobs");
    await mkdir(dir, { recursive: true, mode: 0o700 });
    path = join(dir, randomUUID() + ".json");
  }
  return { path, file: await open(path, "wx", 0o600) };
}

async function closeReceipt(receipt) {
  try {
    if ((await receipt.file.stat()).size === 0) await unlink(receipt.path);
  } finally { await receipt.file.close(); }
}

async function saveReceipt(receipt, result) {
  const { jobToken, ...summary } = result;
  if (typeof jobToken !== "string" || !jobToken) fail("No job handle returned. Use active or check your submission history.");
  await receipt.file.writeFile(JSON.stringify({ submissionId: result.submissionId, proofDigest: result.proofDigest, jobToken }));
  await receipt.file.sync();
  return { ...summary, receipt: receipt.path };
}

async function submit(solution, opts) {
  if (!opts.metadata) fail("Pass --metadata candidate.json.");
  const prepared = await buildSubmission(solution, opts.metadata);
  if (opts["dry-run"]) {
    return { status: "validated-locally", submissionId: prepared.id, score: prepared.score, sourceBytes: prepared.sourceBytes };
  }
  if (!opts["accept-license"]) fail("Publishing accepted source requires --accept-license (Apache-2.0).");
  if (!process.env.RIEMANN_GITHUB_TOKEN) fail("Set RIEMANN_GITHUB_TOKEN.");
  const receipt = await newReceipt(opts.receipt);
  try {
    const result = await api("/api/submissions", { body: prepared.body });
    return await saveReceipt(receipt, result);
  } catch (error) {
    if (!(error instanceof ApiError) || error.status >= 500) {
      console.error(JSON.stringify({ message: "Admission is uncertain. Check active and your submission history before trying again.", submissionId: prepared.id }));
    }
    throw error;
  } finally { await closeReceipt(receipt); }
}

async function status(path, wait, includeLog) {
  let saved;
  try { saved = JSON.parse(await utf8(path, 16_384)); }
  catch { fail("Cannot read this receipt. Use active to recover an in-flight job."); }
  const { jobToken, submissionId, proofDigest } = saved ?? {};
  if (typeof jobToken !== "string" || !jobToken || jobToken.length > 2048) fail("Invalid receipt. Use active to recover an in-flight job.");
  let retry = 5000;
  for (;;) {
    let result;
    try {
      result = await api("/api/submissions/status", { jobToken });
    } catch (error) {
      const transient = error instanceof ApiError ? error.status === 429 || error.status >= 500 : error instanceof TypeError || error.name === "TimeoutError";
      if (!wait || !transient) throw error;
      const requested = Number(error.retryAfter) * 1000;
      const delay = Math.max(retry, Number.isFinite(requested) ? requested : 0);
      console.error(JSON.stringify({ status: "reconnecting", retryInSeconds: Math.ceil(delay / 1000) }));
      await sleep(delay);
      retry = Math.min(60_000, retry * 2);
      continue;
    }
    retry = 5000;
    if ((result.proofDigest && result.proofDigest !== proofDigest) || (result.submissionId && result.submissionId !== submissionId)) fail("The status response does not match this receipt.");
    if (!["queued", "running", "verified", "rejected"].includes(result.status)) fail("Unknown verifier status.");
    if (!wait || result.status === "verified" || result.status === "rejected") {
      if (!includeLog) delete result.log;
      return result;
    }
    console.error(JSON.stringify({ status: result.status, stage: result.stage, queuePosition: result.queuePosition, message: result.message }));
    await sleep(result.status === "queued" ? 30_000 : 10_000);
  }
}

async function main() {
  const [cmd, ...args] = process.argv.slice(2);
  if (!cmd || cmd === "--help" || cmd === "help" || args.includes("--help")) { console.log(help); return; }
  const options = cmd === "submit" ? { metadata: { type: "string" }, receipt: { type: "string" }, "dry-run": { type: "boolean" }, "accept-license": { type: "boolean" } }
    : cmd === "status" ? { wait: { type: "boolean" }, log: { type: "boolean" } }
    : cmd === "active" ? { receipt: { type: "string" } } : {};
  const { values, positionals } = parseArgs({ args, options, allowPositionals: true });
  if (positionals.length !== (["submit", "status"].includes(cmd) ? 1 : 0)) fail("Unexpected arguments. Run with --help.");
  let result;
  if (cmd === "record") result = (await api("/api/leaderboard", { authenticated: false })).current;
  else if (cmd === "submit") result = await submit(positionals[0], values);
  else if (cmd === "status") result = await status(positionals[0], values.wait, values.log);
  else if (cmd === "active") {
    result = await api("/api/submissions/active");
    if (result.status !== "none") {
      const receipt = await newReceipt(values.receipt);
      try { result = await saveReceipt(receipt, result); } finally { await closeReceipt(receipt); }
    }
  } else fail("Unknown command. Run with --help.");
  print(result);
  if (result.status === "rejected" || result.promotion?.status === "superseded") process.exitCode = 2;
}

main().catch(error => {
  console.error(JSON.stringify({ error: error.code ?? "cli_error", message: error.message, httpStatus: error.status, retryAt: error.retryAt, retryAfter: error.retryAfter }));
  process.exitCode = 1;
});
