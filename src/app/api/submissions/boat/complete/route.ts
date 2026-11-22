import { validBoatCompletion } from "@/lib/boat-completion-token";
import { reconcileBoat } from "@/lib/boat-queue";
import { inspectVerificationJob } from "@/lib/submission-queue";

export const runtime = "nodejs";
export const maxDuration = 300;

// A worker can announce only its own job. The server reads the actual receipt
// from Boat and uses the ordinary archive and promotion gates.
export async function POST(request: Request) {
  const jobId = request.headers.get("x-riemann-job") ?? "";
  const digest = request.headers.get("x-riemann-digest") ?? "";
  const token = request.headers.get("x-riemann-notification") ?? "";
  if (!validBoatCompletion(jobId, digest, token))
    return new Response(null, { status: 401 });
  const current = await inspectVerificationJob(jobId);
  if (current.status === "completed" && current.receipt.proofDigest === digest)
    return new Response(null, { status: 204 });
  if (current.status !== "active" || current.job.proofDigest !== digest)
    return new Response(null, { status: 409 });
  // Duplicate notification from the first VM after its replacement was bound.
  if (current.job.jobId !== jobId) return new Response(null, { status: 204 });
  if (!current.job.boat?.uploaded) return new Response(null, { status: 409 });
  const result = await reconcileBoat(current.job, true);
  return new Response(null, {
    status: result.status === "running" ? 503 : 204,
  });
}
