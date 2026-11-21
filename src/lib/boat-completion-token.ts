import { createHmac, timingSafeEqual } from "node:crypto";

export function boatCompletionToken(
  jobId: string,
  digest: string,
  secret: string,
) {
  if (!secret) throw new Error("Verifier completion signing is not configured");
  return createHmac("sha256", secret)
    .update(`riemann/boat/receipt/v1\0${jobId}\0${digest}`)
    .digest("hex");
}

export function validBoatCompletion(
  jobId: string,
  digest: string,
  supplied: string,
) {
  const secret = process.env.AUTH_SECRET;
  if (
    !secret ||
    !/^[0-9a-f]{8}-(?:[0-9a-f]{4}-){3}[0-9a-f]{12}$/.test(jobId) ||
    !/^[0-9a-f]{64}$/.test(digest) ||
    !/^[0-9a-f]{64}$/.test(supplied)
  )
    return false;
  return timingSafeEqual(
    Buffer.from(supplied, "hex"),
    Buffer.from(boatCompletionToken(jobId, digest, secret), "hex"),
  );
}
