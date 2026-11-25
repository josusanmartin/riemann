import { readBoundedText } from "./request-json";
import { randomUUID } from "node:crypto";
import { z } from "zod";
import { e2bVerificationResultSchema } from "./e2b-verifier";
import type { PreparedDirectSubmission } from "./direct-submission";

export function boatSelected() {
  return process.env.RIEMANN_VERIFIER_PROVIDER === "boat";
}
export function boatConfigured() {
  return !!process.env.RIEMANN_BOAT_API_KEY;
}
export const workerId = z
  .string()
  .regex(/^bx_[23456789abcdefghjkmnpqrstuvwxyz]{8}$/);
export const workerLifetime = 2 * 60 * 60 * 1000;
const commit = z.string().regex(/^[0-9a-f]{40}$/);
const digest = z.string().regex(/^[0-9a-f]{64}$/);

export class BoatError extends Error {
  constructor(
    readonly status: number,
    readonly code: string,
  ) {
    super(`Boat returned ${status} (${code})`);
  }
}

async function api(
  path: string,
  method = "GET",
  body?: unknown,
  idempotencyKey?: string,
  timeoutMs = 75_000,
) {
  const key = process.env.RIEMANN_BOAT_API_KEY;
  if (!key) throw new Error("Boat verification is not configured");
  const response = await fetch(`https://boat.dev/api/v1${path}`, {
    method,
    cache: "no-store",
    redirect: "error",
    signal: AbortSignal.timeout(timeoutMs),
    headers: {
      Authorization: `Bearer ${key}`,
      "Content-Type": "application/json",
      ...(idempotencyKey ? { "Idempotency-Key": idempotencyKey } : {}),
    },
    body: body === undefined ? undefined : JSON.stringify(body),
  });
  // File reads can contain output from the submitted proof. Cap the transfer
  // before decoding JSON, including when the provider omits Content-Length.
  const data = await readBoundedText(response, 1_500_000)
    .then(text => JSON.parse(text))
    .catch(() => null);
  if (!response.ok || data?.ok !== true)
    throw new BoatError(
      response.status,
      String(data?.code ?? "unknown").slice(0, 100),
    );
  return data;
}

export async function createBoatWorker(
  jobId: string,
  sha: string,
  proofDigest: string,
  kind: "flow" | "competitive",
  highMemory = false,
) {
  z.string().uuid().parse(jobId);
  commit.parse(sha);
  digest.parse(proofDigest);
  const setupScript = `set -euo pipefail
cd "$HOME"
git init -q riemann-site
git -C riemann-site fetch --quiet --depth=1 https://github.com/josusanmartin/riemann.git ${sha}
git -C riemann-site checkout --quiet --detach FETCH_HEAD
exec bash riemann-site/boat/verify-job.sh ${proofDigest} ${kind} ${highMemory ? "28G" : "12G"}`;
  const data = await api(
    "/sandboxes",
    "POST",
    {
      type: highMemory ? "xlarge" : "large",
      name: `Riemann ${kind} ${jobId}`,
      org: "personal",
      environment: "riemann-production",
      visibility: "private",
      noEnv: true,
      snapshots: false,
      monitoring: false,
      ttlSeconds: workerLifetime / 1000,
      labels: { service: "riemann", kind, job: jobId },
      setupScript,
    },
    jobId,
    20_000,
  );
  return workerId.parse(data.sandbox?.id);
}

/** Recover an allocation whose POST response or queue commit was lost. */
export async function findCompetitiveWorker(jobId: string) {
  z.string().uuid().parse(jobId);
  const label = encodeURIComponent(`job=${jobId}`);
  const data = await api(`/sandboxes?label=${label}`, "GET", undefined, undefined, 15_000);
  const matches = z.array(z.object({
    id: workerId, state: z.string(), labels: z.record(z.string(), z.string()),
  })).parse(data.sandboxes).filter(box => box.labels.job === jobId &&
    box.labels.service === "riemann" && box.labels.kind === "competitive" &&
    !["stopped", "archived", "deleted", "error"].includes(box.state));
  if (matches.length > 1) throw new Error("Ambiguous Boat allocation");
  return matches[0]?.id;
}

export async function stopBoatWorker(id: string) {
  try {
    await api(`/sandboxes/${workerId.parse(id)}/stop`, "POST", {});
  } catch (error) {
    if (error instanceof BoatError && error.status === 404) return;
    if (error instanceof BoatError && error.status === 409) {
      const info = (await api(`/sandboxes/${workerId.parse(id)}`)).sandbox;
      if (["stopped", "archived", "deleted"].includes(info?.state)) return;
    }
    throw error;
  }
}

export async function stageBoatFiles(
  id: string,
  manifest: string,
  solution: string,
  proofDigest: string,
  notification?: { jobId: string; token: string },
) {
  const worker = `/sandboxes/${workerId.parse(id)}`;
  const info = (await api(worker, "GET", undefined, undefined, 15_000)).sandbox;
  if (
    info.environment !== "riemann-production" ||
    info.holdsCreatorLogins !== false ||
    info.snapshots !== false ||
    info.labels?.service !== "riemann"
  ) {
    throw new Error("Boat worker isolation check failed");
  }
  const path = `${worker}/files`;
  for (const [file, content] of [
    ["manifest", manifest],
    ["solution", solution],
    ...(notification ? [["notification", JSON.stringify(notification)]] : []),
    ["ready", proofDigest],
  ]) {
    await api(path, "PUT", {
      path: `riemann-incoming/${file}`,
      content,
      encoding: "utf8",
    }, undefined, 15_000);
  }
}

export async function readBoatFile(id: string, file: string, timeoutMs = 75_000): Promise<string> {
  const data = await api(
    `/sandboxes/${workerId.parse(id)}/files?path=${encodeURIComponent(file)}&encoding=utf8`,
    "GET", undefined, undefined, timeoutMs,
  );
  return z.string().parse(data.content);
}

async function withWorkerTimeline(id: string, log: string) {
  const raw = await readBoatFile(id, "riemann-stages.tsv", 5000).catch(() => "");
  const phases = new Set(["workspace", "lean-toolchain", "foundation", "node-dependencies",
    "wait-verifier-tools", "wait-zeta-runtime", "prepare-worker", "check-upload", "isolate-proof", "check-proof", "seal-receipt"]);
  const entries = raw.slice(0, 4096).split("\n").flatMap(line => {
    const parts = line.split("\t");
    if (parts.length !== 3) return [];
    const [time, phase, event] = parts;
    if (!/^\d{4}-\d{2}-\d{2}T\d{2}:\d{2}:\d{2}Z$/.test(time) || !phases.has(phase) || !/^(start|exit=\d{1,3})$/.test(event)) return [];
    return [`${time}  ${phase}  ${event}`];
  });
  if (!entries.length) return log;
  const timeline = "\n\nWorker stages (UTC)\n" + entries.join("\n");
  const room = 100_000 - timeline.length;
  if (log.length <= room) return log + timeline;
  const marker = "\n[... verifier output omitted ...]\n";
  return log.slice(0, 20_000) + marker + log.slice(-(room - 20_000 - marker.length)) + timeline;
}

export async function boatResult(
  id: string,
  expires: number,
  submissionId: string | (() => Promise<string>),
  proofDigest: string,
  receiptReady = false,
) {
  const unavailable = async (message: string, log = "") => ({
    schemaVersion: 1 as const,
    status: "rejected" as const,
    submissionId:
      typeof submissionId === "string" ? submissionId : await submissionId(),
    proofDigest,
    completedAt: new Date().toISOString(),
    log,
    message,
  });
  let info;
  try {
    info = (await api(`/sandboxes/${workerId.parse(id)}`)).sandbox;
  } catch (error) {
    if (error instanceof BoatError && error.status === 404)
      return unavailable("The Boat worker expired before returning a receipt.");
    throw error;
  }
  const stopped = info.setupStatus === "failed" || info.state === "error" || info.state === "archived";
  if (!stopped && (receiptReady || info.setupStatus === "done")) {
    const result = e2bVerificationResultSchema.parse(JSON.parse(await readBoatFile(id, "riemann-receipt.json")));
    if (result.status === "rejected") result.log = await withWorkerTimeline(id, result.log);
    return result;
  }
  if (stopped || Date.now() >= expires) {
    const message = stopped
      ? "The Boat worker stopped before sealing a verification result."
      : "The Boat worker reached its operational time limit.";
    // Only the isolated proof process output is suitable for submitters.
    const output = await readBoatFile(id, "riemann-proof.log").catch(() => "");
    return unavailable(message, await withWorkerTimeline(id, output ? output.slice(-100_000) : message));
  }
  return null;
}

export async function activeBoatFlow() {
  const data = await api("/sandboxes?label=kind%3Dflow", "GET", undefined, undefined, 15_000);
  return z
    .array(
      z.object({
        state: z.string(),
        setupStatus: z.string().nullable().optional(),
        labels: z.record(z.string(), z.string()),
      }),
    )
    .parse(data.sandboxes)
    .some(
      (s) =>
        s.labels.service === "riemann" &&
        s.labels.kind === "flow" &&
        s.setupStatus !== "done" &&
        s.setupStatus !== "failed" &&
        !["archived", "error", "deleted"].includes(s.state),
    );
}

export async function startBoatFlow(
  input: PreparedDirectSubmission & { baseCommitSha: string },
) {
  const jobId = randomUUID();
  const id = await createBoatWorker(
    jobId,
    input.baseCommitSha,
    input.proofDigest,
    "flow",
  );
  try {
    await stageBoatFiles(id, input.manifest, input.solution, input.proofDigest);
  } catch (error) {
    await stopBoatWorker(id).catch(() => undefined);
    throw error;
  }
  return { jobId, sandboxId: `boat-${id.slice(3)}` };
}
export function flowWorkerId(handle: string) {
  return workerId.parse(`bx_${handle.slice(5)}`);
}
