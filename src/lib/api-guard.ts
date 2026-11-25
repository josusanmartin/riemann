import { isIP } from "node:net";

const windowMs = 60_000;
const budgets = { upload: 20, poll: 120 };
const buckets = new Map<string, { count: number; until: number }>();

function reject(status: number, message: string, retryAfter?: number) {
  const headers = new Headers({ "Cache-Control": "private, no-store" });
  if (retryAfter) headers.set("Retry-After", String(retryAfter));
  return Response.json({ message }, { status, headers });
}

/** Cheap checks before authenticating against GitHub or reading the queue.
 * Per-instance burst protection complements the durable per-account quota. */
export function guardUserApi(request: Request, kind: keyof typeof budgets, now = Date.now()) {
  if (kind === "upload") {
    const origin = request.headers.get("origin");
    if ((origin !== null && origin !== new URL(request.url).origin) ||
        request.headers.get("sec-fetch-site") === "cross-site") {
      return reject(403, "Submit from this site or use the authenticated CLI.");
    }
    if (request.headers.get("content-type")?.split(";")[0].trim().toLowerCase() !== "application/json") {
      return reject(415, "Send the submission as application/json.");
    }
  }
  if (process.env.VERCEL !== "1") return null;
  const ip = request.headers.get("x-vercel-forwarded-for")?.trim();
  if (!ip || !isIP(ip)) return null;
  const key = `${kind}:${ip}`;
  let bucket = buckets.get(key);
  if (!bucket || now >= bucket.until) {
    if (!bucket && buckets.size >= 4096) buckets.delete(buckets.keys().next().value!);
    bucket = { count: 0, until: now + windowMs };
    buckets.set(key, bucket);
  }
  if (++bucket.count > budgets[kind]) {
    return reject(429, "Too many requests. Please retry shortly.", Math.ceil((bucket.until - now) / 1000));
  }
  return null;
}
