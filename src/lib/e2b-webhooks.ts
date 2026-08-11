import { createHash, timingSafeEqual } from "node:crypto";
import { z } from "zod";
import { getE2BApiKey } from "@/lib/e2b-config";
import { siteUrl } from "@/lib/site";
import { isoDateTimeStringSchema } from "@/lib/challenge";

const E2B_WEBHOOKS_API = "https://api.e2b.app/events/webhooks";
const E2B_WEBHOOK_NAME = "riemann-fail-production";
const E2B_PAUSED_EVENT = "sandbox.lifecycle.paused";

const webhookSchema = z
  .object({
    id: z.string().min(1),
    name: z.string().min(1),
    url: z.string().url(),
    enabled: z.boolean(),
    events: z.array(z.string()),
  })
  .passthrough();

export const e2bWebhookEventSchema = z
  .object({
    id: z.string().min(1).max(300),
    version: z.string().min(1).max(30),
    type: z.string().min(1).max(100),
    timestamp: isoDateTimeStringSchema,
    event_data: z
      .object({ sandbox_metadata: z.record(z.string(), z.string()).default({}) })
      .passthrough(),
    sandbox_id: z.string().min(10).max(160).regex(/^[A-Za-z0-9-]+$/),
    sandbox_template_id: z.string().min(1).max(300),
  })
  .passthrough();

export type E2BWebhookEvent = z.infer<typeof e2bWebhookEventSchema>;

export function getE2BWebhookSecret(): string | undefined {
  return process.env.E2B_WEBHOOK_SECRET;
}

export function isE2BWebhookConfigured(): boolean {
  return (getE2BWebhookSecret()?.length ?? 0) >= 32;
}

function webhookUrl(): string {
  const url = new URL("/api/e2b/webhook", siteUrl);
  if (url.protocol !== "https:") {
    throw new Error("NEXT_PUBLIC_SITE_URL must be HTTPS before E2B webhooks can be registered");
  }
  return url.toString();
}

async function e2bWebhookRequest(
  path = "",
  init: RequestInit = {},
): Promise<Response> {
  const apiKey = getE2BApiKey();
  if (!apiKey) throw new Error("E2B verification is not configured");
  const response = await fetch(`${E2B_WEBHOOKS_API}${path}`, {
    ...init,
    cache: "no-store",
    headers: {
      "Content-Type": "application/json",
      "X-API-Key": apiKey,
      ...init.headers,
    },
  });
  if (!response.ok) {
    const detail = (await response.text()).slice(0, 500).replace(/\s+/g, " ");
    throw new Error(
      `E2B webhook API ${response.status}: ${detail || response.statusText}`,
    );
  }
  return response;
}

function webhookList(raw: unknown): Array<z.infer<typeof webhookSchema>> {
  const candidate = Array.isArray(raw)
    ? raw
    : raw && typeof raw === "object" && "webhooks" in raw
      ? (raw as { webhooks: unknown }).webhooks
      : raw && typeof raw === "object" && "items" in raw
        ? (raw as { items: unknown }).items
        : [];
  return z.array(webhookSchema).parse(candidate);
}

/** Register or repair the one project-wide pause webhook before accepting work. */
export async function ensureE2BWebhook(): Promise<void> {
  const signatureSecret = getE2BWebhookSecret();
  if (!signatureSecret || signatureSecret.length < 32) {
    throw new Error("E2B_WEBHOOK_SECRET must contain at least 32 characters");
  }
  const url = webhookUrl();
  const hooks = webhookList(await (await e2bWebhookRequest()).json());
  const existing = hooks.find((hook) => hook.name === E2B_WEBHOOK_NAME);
  const body = JSON.stringify({
    name: E2B_WEBHOOK_NAME,
    url,
    enabled: true,
    events: [E2B_PAUSED_EVENT],
    signatureSecret,
  });
  if (existing) {
    // The API never returns the signature secret, so replace the complete
    // configuration to repair a rotated secret as well as URL/event drift.
    await e2bWebhookRequest(`/${encodeURIComponent(existing.id)}`, {
      method: "PATCH",
      body,
    });
    return;
  }
  await e2bWebhookRequest("", { method: "POST", body });
}

export function verifyE2BWebhookSignature(
  rawBody: string,
  suppliedSignature: string | null,
  signatureVersion: string | null,
): boolean {
  const secret = getE2BWebhookSecret();
  if (!secret || !suppliedSignature || signatureVersion !== "v1") return false;
  // E2B v1 deliberately specifies SHA-256(secret || raw body), not HMAC.
  // Keep this byte-for-byte aligned with the lifecycle-webhook documentation.
  const expected = createHash("sha256")
    .update(secret)
    .update(rawBody)
    .digest("base64")
    .replace(/=+$/, "");
  const left = Buffer.from(expected, "utf8");
  const right = Buffer.from(suppliedSignature, "utf8");
  return left.length === right.length && timingSafeEqual(left, right);
}
