#!/usr/bin/env node
/* SPDX-License-Identifier: MIT
 * MIT License
 *
 * Copyright (c) 2026 Riemann.fail contributors
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy
 * of this software and associated documentation files (the "Software"), to deal
 * in the Software without restriction, including without limitation the rights
 * to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
 * copies of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
 * AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
 * OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
 * SOFTWARE.
 */
// Riemann proof submission CLI. Requires Node.js 22 or later; no dependencies.
import { constants, mkdir, open, rename, rm, unlink } from "node:fs/promises";
import { homedir } from "node:os";
import { join, resolve } from "node:path";
import { createServer } from "node:http";
import { spawn } from "node:child_process";
import { createInterface } from "node:readline";
import { randomBytes, createHash, randomUUID } from "node:crypto";
import { setTimeout as sleep } from "node:timers/promises";
import { parseArgs } from "node:util";

const origin = "https://www.riemannzeta.fun";
const help = `Riemann proof submissions · Node.js 22+
  node riemann.mjs login [--manual | --finish]
  node riemann.mjs whoami
  node riemann.mjs logout
  node riemann.mjs record
  node riemann.mjs submit Solution.lean --metadata candidate.json --dry-run
  node riemann.mjs submit Solution.lean --metadata candidate.json --accept-license [--receipt FILE]
  node riemann.mjs status RECEIPT [--wait] [--log]
  node riemann.mjs active [--receipt FILE]

Add --verbose to trace API calls and retry timing on stderr.
Login opens the website. Use --manual for a remote agent. RIEMANN_GITHUB_TOKEN is an optional override.
Receipts are private files under ~/.riemannzeta/jobs/. See ${origin}/submit/agent`;

let verbose = false;
function trace(event, fields) {
  if (verbose) console.error(JSON.stringify({ time: new Date().toISOString(), event, ...fields }));
}

const print = data => console.log(JSON.stringify(data));
const fail = message => { throw new Error(message); };

class ApiError extends Error {
  constructor(status, data, retryAfter, requestId) {
    super(data.message || data.error || `HTTP ${status}`);
    this.status = status;
    this.code = data.error ?? "http_error";
    this.retryAt = data.retryAt;
    this.retryAfter = retryAfter;
    this.requestId = requestId || undefined;
    this.issues = data.issues;
    this.currentRecord = data.currentRecord;
    this.dailyUsed = data.dailyUsed;
    this.dailyLimit = data.dailyLimit;
    if (data.error === "github_identity_unavailable") this.action = "Check the environment token or unset RIEMANN_GITHUB_TOKEN to use the saved website login.";
    else if (status === 401) this.action = "Run riemann login to refresh the website login.";
    else if (["invalid_job", "job_expired", "job_not_admitted"].includes(data.error)) this.action = "Use riemann active to recover an in-flight job, or open your submission history.";
    else if (data.error === "queue_admission_uncertain") this.action = "Check riemann active and your submission history before uploading again.";
  }
}

async function api(path, { authenticated = true, body, jobToken, credential } = {}) {
  const headers = { Accept: "application/json" };
  if (authenticated) {
    const token = credential ?? await currentCredential();
    headers.Authorization = "Bearer " + token;
  }
  if (jobToken) headers["X-Verification-Job"] = jobToken;
  if (body !== undefined) headers["Content-Type"] = "application/json";
  const method = body === undefined ? "GET" : "POST";
  const started = Date.now();
  trace("request", { method, path });
  let res;
  try {
    res = await fetch(origin + path, { headers, method, body, redirect: "error", signal: AbortSignal.timeout(300_000) });
  } catch (error) {
    const timedOut = error.name === "TimeoutError";
    const reason = /^[A-Z][A-Z_0-9]{1,60}$/.test(error.cause?.code ?? "") ? error.cause.code : undefined;
    const code = timedOut ? "request_timeout" : "connection_failed";
    trace(code, { method, path, elapsedMs: Date.now() - started, reason });
    const networkError = new TypeError(timedOut
      ? `${method} ${path} timed out after five minutes.`
      : `Could not reach riemannzeta.fun for ${method} ${path}${reason ? " (" + reason + ")" : ""}.`);
    networkError.code = code;
    throw networkError;
  }
  const requestId = res.headers.get("x-vercel-id");
  trace("response", { method, path, httpStatus: res.status, elapsedMs: Date.now() - started, requestId });
  const data = await res.json().catch(() => null);
  if (!res.ok) throw new ApiError(res.status, data ?? {}, res.headers.get("retry-after"), requestId);
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
  const raw = await utf8(metadataFile, 32_000);
  let m;
  try { m = JSON.parse(raw); } catch { fail("The metadata file must contain valid JSON. Check its quotes, commas and brackets."); }
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
  await receipt.file.writeFile(JSON.stringify({ jobId: result.jobId, submissionId: result.submissionId, proofDigest: result.proofDigest, jobToken }));
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
  const credential = await currentCredential();
  const receipt = await newReceipt(opts.receipt);
  try {
    const result = await api("/api/submissions", { body: prepared.body, credential });
    return await saveReceipt(receipt, result);
  } catch (error) {
    const beforeAdmission = ["submissions_paused", "verifier_unavailable", "automation_unavailable",
      "deployment_identity_unavailable", "job_signing_unavailable", "verifier_template_stale", "verification_queue_full"];
    if (!(error instanceof ApiError) || (error.status >= 500 && !beforeAdmission.includes(error.code))) {
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
      console.error(JSON.stringify({ time: new Date().toISOString(), status: "reconnecting", reason: error.code ?? error.name, httpStatus: error.status, requestId: error.requestId, retryInSeconds: Math.ceil(delay / 1000) }));
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
    console.error(JSON.stringify({ time: new Date().toISOString(), status: result.status, stage: result.stage, stageStartedAt: result.stageStartedAt, submissionId, queuePosition: result.queuePosition, message: result.message }));
    await sleep(result.status === "queued" ? 30_000 : 10_000);
  }
}

function configDir() {
  return process.env.RIEMANN_CONFIG_DIR || join(homedir(), ".riemannzeta");
}

async function storePrivate(name, data) {
  const dir = configDir();
  await mkdir(dir, { recursive: true, mode: 0o700 });
  const tmp = join(dir, "." + randomUUID());
  const file = await open(tmp, "wx", 0o600);
  try {
    try { await file.writeFile(JSON.stringify(data)); await file.sync(); }
    finally { await file.close(); }
    await rename(tmp, join(dir, name));
  } finally { await rm(tmp, { force: true }); }
}

async function currentCredential() {
  if (process.env.RIEMANN_GITHUB_TOKEN) return process.env.RIEMANN_GITHUB_TOKEN;
  let session;
  try { session = JSON.parse(await utf8(join(configDir(), "session.json"), 8192)); } catch { /* no saved login */ }
  if (!session?.credential || !(Date.parse(session.expires) > Date.now())) fail("Run riemann login to sign in.");
  return session.credential;
}

function pairingLink(pending, port) {
  const url = new URL("/cli/login", origin);
  url.searchParams.set("challenge", pending.challenge);
  url.searchParams.set("until", String(pending.until));
  if (port) url.searchParams.set("port", String(port));
  return url.href;
}

async function finishLogin(pending, approval) {
  if (pending.until <= Date.now()) fail("Login request expired. Run login again.");
  if (!/^[A-Za-z0-9_.-]{80,3000}$/.test(approval)) fail("Invalid approval. Copy the complete approval from the website.");
  const credential = `rcli1_${pending.verifier}~${approval}`;
  const identity = await api("/api/cli/session", { credential });
  if (identity.source !== "website-login" || !identity.githubLogin || !(Date.parse(identity.expires) > Date.now())) fail("The website could not confirm this login.");
  if (pending.until <= Date.now()) fail("Login request expired. Run login again.");
  await storePrivate("session.json", { credential, expires: identity.expires });
  return { status: "signed-in", ...identity, environmentOverride: Boolean(process.env.RIEMANN_GITHUB_TOKEN) };
}

function openBrowser(url) {
  const [command, args] = process.platform === "darwin" ? ["open", [url]]
    : process.platform === "win32" ? ["rundll32.exe", ["url.dll,FileProtocolHandler", url]] : ["xdg-open", [url]];
  const child = spawn(command, args, { detached: true, stdio: "ignore" });
  const manualHint = () => console.error("Could not open the browser. Open the printed link on this machine, or use riemann login --manual.");
  child.on("error", manualHint);
  child.on("exit", code => { if (code !== null && code !== 0) manualHint(); });
  child.unref();
}

// The browser posts the challenge-bound approval from its URL fragment.
// The secret verifier never leaves the CLI except over HTTPS to Riemann.
async function browserLogin(pending) {
  const server = createServer();
  let done, abort;
  const result = new Promise((resolve, reject) => { done = resolve; abort = reject; });
  server.headersTimeout = 10_000;
  server.requestTimeout = 15_000;
  await new Promise((resolve, reject) => {
    server.once("error", reject);
    server.listen(0, "127.0.0.1", resolve);
  });
  const port = server.address().port;
  const local = "http://127.0.0.1:" + port;
  const url = pairingLink(pending, port);
  const timeout = setTimeout(() => abort(new Error("Login timed out. Run login again.")), pending.until - Date.now());
  let completing = false;
  server.on("request", async (req, res) => {
    res.setHeader("Cache-Control", "no-store");
    res.setHeader("Referrer-Policy", "no-referrer");
    res.setHeader("X-Content-Type-Options", "nosniff");
    try {
      if (req.headers.host !== "127.0.0.1:" + port || req.url !== "/callback?state=" + pending.challenge) {
        res.writeHead(404).end(); return;
      }
      if (req.method === "GET") {
        const nonce = randomBytes(16).toString("base64");
        res.setHeader("Content-Security-Policy", `default-src 'none'; script-src 'nonce-${nonce}'; connect-src 'self'; frame-ancestors 'none'; base-uri 'none'`);
        res.writeHead(200, { "Content-Type": "text/html; charset=utf-8" }).end(`<!doctype html>
<meta charset="utf-8"><title>Riemann CLI login</title>
<p>Finishing CLI login…</p>
<script nonce="${nonce}">
(async () => {
  const code = new URLSearchParams(location.hash.slice(1)).get("approval");
  history.replaceState(null, "", location.pathname + location.search);
  const message = document.querySelector("p");
  try {
    const result = await fetch(location.href, {
      method: "POST", headers: { "Content-Type": "text/plain" }, body: code || ""
    });
    message.textContent = await result.text();
  } catch {
    message.textContent = "Check the terminal for your login result.";
  }
})();
</script>`);
        return;
      }
      if (req.method !== "POST" || req.headers.origin !== local) { res.writeHead(403).end(); return; }
      let size = 0;
      const chunks = [];
      for await (const chunk of req) {
        size += chunk.length;
        if (size > 3000) { res.writeHead(413).end(); return; }
        chunks.push(chunk);
      }
      if (completing) { res.writeHead(409).end("Approval already in progress."); return; }
      completing = true;
      let identity;
      try {
        identity = await finishLogin(pending, Buffer.concat(chunks).toString("utf8"));
      } catch (error) {
        res.once("finish", () => abort(error));
        res.writeHead(400, { "Content-Type": "text/plain; charset=utf-8" })
          .end("CLI login failed. Check the terminal for the cause and next step.");
        return;
      }
      res.once("finish", () => done(identity));
      res.writeHead(200, { "Content-Type": "text/plain; charset=utf-8" }).end(`Signed in as @${identity.githubLogin}. You can close this tab.`);
    } catch {
      res.writeHead(400).end("Login could not be confirmed. Return to the terminal and start a new login.");
    }
  });
  console.error(`Open ${url}\nMatch this code before approving: ${pending.challenge.slice(0, 8)}`);
  try { openBrowser(url); return await result; }
  finally { clearTimeout(timeout); server.close(); server.closeAllConnections(); }
}

async function login({ manual, finish }) {
  if (manual && finish) fail("Choose either --manual or --finish.");
  if (finish) {
    let pending;
    try { pending = JSON.parse(await utf8(join(configDir(), "pending.json"), 2048)); }
    catch { fail("Run login --manual on this machine first."); }
    if (!(pending.until > Date.now())) fail("Login request expired. Run login --manual again.");
    console.error("Paste the approval from the Riemann website and press Enter:");
    const lines = createInterface({ input: process.stdin, terminal: false });
    try {
      for await (const line of lines) {
        const identity = await finishLogin(pending, line.trim());
        await rm(join(configDir(), "pending.json"), { force: true });
        return identity;
      }
    } finally { lines.close(); }
    fail("No approval was received.");
  }
  const verifier = randomBytes(32).toString("base64url");
  const challenge = createHash("sha256").update(verifier).digest("base64url");
  const pending = { verifier, challenge, until: Date.now() + 10 * 60_000 };
  if (!manual) return browserLogin(pending);
  await storePrivate("pending.json", pending);
  return { status: "approval-required", url: pairingLink(pending), code: challenge.slice(0, 8), next: "riemann login --finish" };
}

async function main() {
  const [cmd, ...args] = process.argv.slice(2);
  if (!cmd || cmd === "--help" || cmd === "help" || args.includes("--help")) { console.log(help); return; }
  const options = cmd === "login" ? { manual: { type: "boolean" }, finish: { type: "boolean" } }
    : cmd === "submit" ? { metadata: { type: "string" }, receipt: { type: "string" }, "dry-run": { type: "boolean" }, "accept-license": { type: "boolean" } }
    : cmd === "status" ? { wait: { type: "boolean" }, log: { type: "boolean" } }
    : cmd === "active" ? { receipt: { type: "string" } } : {};
  const { values, positionals } = parseArgs({ args, options: { ...options, verbose: { type: "boolean" } }, allowPositionals: true });
  verbose = Boolean(values.verbose);
  if (positionals.length !== (["submit", "status"].includes(cmd) ? 1 : 0)) fail("Unexpected arguments. Run with --help.");
  let result;
  if (cmd === "login") result = await login(values);
  else if (cmd === "whoami") result = await api("/api/cli/session");
  else if (cmd === "logout") {
    await Promise.all(["session.json", "pending.json"].map(name => rm(join(configDir(), name), { force: true })));
    result = { status: "local-login-cleared", environmentOverride: Boolean(process.env.RIEMANN_GITHUB_TOKEN) };
  }
  else if (cmd === "record") result = (await api("/api/leaderboard", { authenticated: false })).current;
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
  console.error(JSON.stringify({ error: error.code ?? "cli_error", message: error.message, httpStatus: error.status, issues: error.issues, currentRecord: error.currentRecord, action: error.action, requestId: error.requestId, dailyUsed: error.dailyUsed, dailyLimit: error.dailyLimit, retryAt: error.retryAt, retryAfter: error.retryAfter }));
  process.exitCode = 1;
});
