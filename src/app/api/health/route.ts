import { NextResponse } from "next/server";
import { getCurrentRecord } from "@/lib/records";
import { getE2BTemplate, isE2BConfigured } from "@/lib/e2b-config";
import { isE2BWebhookConfigured } from "@/lib/e2b-webhooks";
import { isGitHubPromotionConfigured } from "@/lib/github-promotion";

export function GET(): NextResponse {
  const current = getCurrentRecord();
  const e2bConfigured = isE2BConfigured();
  const e2bWebhookConfigured = isE2BWebhookConfigured();
  const promotionConfigured = isGitHubPromotionConfigured();
  return NextResponse.json({
    status: "ok",
    service: "riemann-fail",
    recordId: current.id,
    record: current.scoreDecimal,
    authConfigured: Boolean(
      process.env.AUTH_GITHUB_ID &&
        process.env.AUTH_GITHUB_SECRET &&
        process.env.AUTH_SECRET,
    ),
    e2bConfigured,
    e2bTemplate: getE2BTemplate(),
    e2bWebhookConfigured,
    promotionConfigured,
    cronBackstopConfigured: Boolean(process.env.CRON_SECRET),
    directSubmissionsConfigured:
      e2bConfigured && e2bWebhookConfigured && promotionConfigured,
  });
}
