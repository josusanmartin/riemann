/** Real authenticated HTTP test; never bypasses the queue or mathematical judge.
 * npx tsx scripts/test-production-flow.ts [--negative-control]
 * The optional negative control consumes ONE of the caller's three daily slots.
 * Requires the maintainer's GitHub login for the positive operator-only replay.
 */
import { execFileSync } from "node:child_process";
import { readFile, mkdtemp, writeFile } from "node:fs/promises";
import { tmpdir } from "node:os";
import { join } from "node:path";

const site = "https://www.riemannzeta.fun";
const source = await readFile(new URL("../submissions/flow-test/proof/Solution.lean", import.meta.url), "utf8");
const negative = process.argv.includes("--negative-control");
const deployment = process.argv.find(arg => arg.startsWith("--deployment="))?.slice("--deployment=".length);
if (deployment) {
  const url = new URL(deployment);
  if (url.protocol !== "https:" || url.username || url.password || url.port ||
      !/^riemann-fail-[a-z0-9]+-josus-projects-42b794d2\.vercel\.app$/.test(url.hostname) ||
      url.pathname !== "/" || url.search || url.hash) {
    throw new Error("Only this project's explicit HTTPS deployment URL is accepted");
  }
  console.log("Testing the production backend via authenticated Vercel deployment access; this does not test the public-domain firewall or browser OAuth.");
}
const token = process.env.RIEMANN_TEST_GITHUB_TOKEN ?? (() => {
  try {
    const credentials = execFileSync("gh", ["auth", "git-credential", "get"], {
      input: "protocol=https\nhost=github.com\n\n", encoding: "utf8", stdio: ["pipe", "pipe", "pipe"],
    });
    return credentials.match(/^password=(.+)$/m)?.[1];
  } catch { return undefined; }
})();
if (!token) throw new Error("Sign in to gh or set RIEMANN_TEST_GITHUB_TOKEN (never commit it)");

async function rawRequest(path: string, body?: unknown): Promise<{ status: number; text: string }> {
  if (deployment) {
    const config = [
      `header = ${JSON.stringify(`Authorization: Bearer ${token}`)}`,
      'header = "Content-Type: application/json"',
      `request = "${body === undefined ? "GET" : "POST"}"`,
      ...(body === undefined ? [] : [`data-binary = ${JSON.stringify(JSON.stringify(body))}`]),
    ].join("\n") + "\n";
    let out: string;
    try {
      out = execFileSync("vercel", ["curl", path, "--deployment", deployment, "--",
        "--silent", "--show-error", "--max-time", "315", "--config", "-", "--write-out", "\n%{http_code}"], {
        input: config, encoding: "utf8", stdio: ["pipe", "pipe", "pipe"], maxBuffer: 5_000_000,
      });
    } catch {
      throw new Error("Authenticated Vercel request failed; no verdict inferred");
    }
    const separator = out.lastIndexOf("\n");
    return { status: Number(out.slice(separator + 1)), text: out.slice(0, separator) };
  }
  const response = await fetch(`${site}${path}`, {
    method: body === undefined ? "GET" : "POST", redirect: "error",
    headers: { Authorization: `Bearer ${token}`, "Content-Type": "application/json" },
    body: body === undefined ? undefined : JSON.stringify(body), signal: AbortSignal.timeout(body === undefined ? 90_000 : 315_000),
  });
  return { status: response.status, text: await response.text() };
}

async function request(path: string, body?: unknown): Promise<Record<string, unknown>> {
  const response = await rawRequest(path, body);
  let data: Record<string, unknown>;
  try { data = JSON.parse(response.text) as Record<string, unknown>; } catch {
    throw new Error(`HTTP ${response.status}: non-JSON response (possibly the Vercel security checkpoint). No verdict inferred.`);
  }
  if (response.status < 200 || response.status >= 300) throw new Error(`HTTP ${response.status}: ${String(data.error)} — ${String(data.message ?? "")}`);
  return data;
}

const before = await request("/api/leaderboard");
const health = await request("/api/health");
if (!health.verifierTemplateIdentityConfigured) {
  throw new Error("The matching verifier image has not been pinned; do not consume a submission slot");
}
const output = await mkdtemp(join(tmpdir(), "riemann-production-e2e-"));
console.log(`Private test receipts: ${output}`);

async function run(kind: "negative" | "positive") {
  const flow = kind === "positive";
  const path = flow ? "/api/submissions/flow-test" : "/api/submissions";
  const input = flow ? { solution: source } : {
    id: `e2e-negative-${Date.now()}`, displayName: "Riemann.fail E2E audit",
    score: { numerator: "672500704", denominator: "1000000000" },
    summary: "Explicit negative control: the two-thirds proof does not prove a new record. Expected mathematical rejection.",
    method: "Negative-control audit, not a claimed improvement", model: null, harness: "Production E2E test",
    solution: source, acceptLicense: true,
  };
  const started = await request(path, input);
  if (typeof started.jobToken !== "string") throw new Error("Admission returned no signed job handle");
  await writeFile(join(output, `${kind}-job.json`), JSON.stringify(started, null, 2), { mode: 0o600, flag: "wx" });
  console.log(JSON.stringify({ kind, status: started.status, digest: started.proofDigest }));
  const deadline = Date.now() + 59 * 60_000;
  while (Date.now() < deadline) {
    await new Promise(resolve => setTimeout(resolve, 15_000));
    const result = await request(`${path}/status?job=${encodeURIComponent(started.jobToken)}`);
    console.log(JSON.stringify({ kind, status: result.status, message: result.message, digest: result.proofDigest }));
    if (result.status === "running" || result.status === "queued") continue;
    await writeFile(join(output, `${kind}-result.json`), JSON.stringify(result, null, 2), { mode: 0o600, flag: "wx" });
    if (result.proofDigest !== started.proofDigest) throw new Error("Verdict digest changed");
    if (flow) {
      if (result.status !== "verified" || (result.promotion as { status?: string })?.status !== "test-only") {
        throw new Error("Positive replay did not pass the full attestation gate");
      }
    } else {
      const feedback = result.feedback as { retryable?: boolean; code?: string } | undefined;
      if (result.status !== "rejected" || !feedback || feedback.retryable || feedback.code === "verifier-infrastructure") {
        throw new Error("Negative control did not receive a mathematical rejection");
      }
      const job = JSON.parse(Buffer.from(started.jobToken.split(".")[0], "base64url").toString()) as { jobId: string };
      const archived = await rawRequest(`/api/admin/submission-archive/${job.jobId}`);
      if (archived.status !== 200 || archived.text !== source) throw new Error("Encrypted archive did not round-trip the exact source");
    }
    return;
  }
  throw new Error("No final verdict within the test deadline; saved job handle remains recoverable");
}

if (negative) await run("negative");
await run("positive");
const after = await request("/api/leaderboard");
if (JSON.stringify(before.current) !== JSON.stringify(after.current)) {
  throw new Error("The public record changed during a noncompetitive test; inspect before claiming success");
}
console.log("PASS: real HTTP verdicts received, publication fingerprint checked, public record unchanged.");
