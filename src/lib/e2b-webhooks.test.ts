import { createHash } from "node:crypto";
import { afterEach, describe, expect, it } from "vitest";
import { verifyE2BWebhookSignature } from "@/lib/e2b-webhooks";

const originalSecret = process.env.E2B_WEBHOOK_SECRET;

afterEach(() => {
  if (originalSecret === undefined) delete process.env.E2B_WEBHOOK_SECRET;
  else process.env.E2B_WEBHOOK_SECRET = originalSecret;
});

describe("E2B webhook authentication", () => {
  it("accepts only the documented v1 signature over the exact raw body", () => {
    const secret = "test-webhook-secret-that-is-at-least-32-bytes";
    const body = '{"type":"sandbox.lifecycle.paused"}';
    process.env.E2B_WEBHOOK_SECRET = secret;
    const signature = createHash("sha256")
      .update(secret)
      .update(body)
      .digest("base64")
      .replace(/=+$/, "");

    expect(verifyE2BWebhookSignature(body, signature, "v1")).toBe(true);
    expect(verifyE2BWebhookSignature(`${body}\n`, signature, "v1")).toBe(false);
    expect(verifyE2BWebhookSignature(body, signature, "v2")).toBe(false);
  });
});
