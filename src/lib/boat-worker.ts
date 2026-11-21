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

class BoatError extends Error {
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
) {
  const key = process.env.RIEMANN_BOAT_API_KEY;
  if (!key) throw new Error("Boat verification is not configured");
  const response = await fetch(`https://boat.dev/api/v1${path}`, {
    method,
    cache: "no-store",
    redirect: "error",
    signal: AbortSignal.timeout(75_000),
    headers: {
      Authorization: `Bearer ${key}`,
      "Content-Type": "application/json",
      ...(idempotencyKey ? { "Idempotency-Key": idempotencyKey } : {}),
    },
    body: body === undefined ? undefined : JSON.stringify(body),
  });
  const data = await response.json();
  if (!response.ok || data.ok !== true)
    throw new BoatError(
      response.status,
      String(data.code ?? "unknown").slice(0, 100),
    );
  return data;
}

export async function createBoatWorker(
  jobId: string,
  sha: string,
  proofDigest: string,
  kind: "flow" | "competitive",
) {
  z.string().uuid().parse(jobId);
  commit.parse(sha);
  digest.parse(proofDigest);
  const setupScript = `set -euo pipefail
cd "$HOME"
git init -q riemann-site
git -C riemann-site fetch --quiet --depth=1 https://github.com/josusanmartin/riemann.git ${sha}
git -C riemann-site checkout --quiet --detach FETCH_HEAD
exec bash riemann-site/boat/verify-job.sh ${proofDigest} ${kind}`;
  const data = await api(
    "/sandboxes",
    "POST",
    {
      type: "large",
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
  );
  return workerId.parse(data.sandbox?.id);
}

export async function stopBoatWorker(id: string) {
  try {
    await api(`/sandboxes/${workerId.parse(id)}/stop`, "POST", {});
  } catch (error) {
    if (!(error instanceof BoatError && error.status === 404)) throw error;
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
  const info = (await api(worker)).sandbox;
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
    });
  }
}

export async function readBoatFile(id: string, file: string): Promise<string> {
  const data = await api(
    `/sandboxes/${workerId.parse(id)}/files?path=${encodeURIComponent(file)}&encoding=utf8`,
  );
  return z.string().parse(data.content);
}

export async function boatResult(
  id: string,
  expires: number,
  submissionId: string | (() => Promise<string>),
  proofDigest: string,
  receiptReady = false,
) {
  const unavailable = async (message: string) => ({
    schemaVersion: 1 as const,
    status: "rejected" as const,
    submissionId:
      typeof submissionId === "string" ? submissionId : await submissionId(),
    proofDigest,
    completedAt: new Date().toISOString(),
    log: "",
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
  if (
    info.setupStatus === "failed" ||
    info.state === "error" ||
    info.state === "archived"
  )
    return unavailable(
      "The Boat worker stopped before sealing a verification result.",
    );
  if (receiptReady || info.setupStatus === "done")
    return e2bVerificationResultSchema.parse(
      JSON.parse(await readBoatFile(id, "riemann-receipt.json")),
    );
  if (Date.now() >= expires)
    return unavailable("The Boat worker reached its operational time limit.");
  return null;
}

export async function activeBoatFlow() {
  const data = await api("/sandboxes?label=kind%3Dflow");
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
