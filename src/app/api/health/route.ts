import { NextResponse } from "next/server";
import { contract, getCurrentRecord } from "@/lib/records";
import { getE2BTemplate, isE2BConfigured } from "@/lib/e2b-config";
import { isE2BWebhookConfigured } from "@/lib/e2b-webhooks";
import { isGitHubPromotionConfigured } from "@/lib/github-promotion";
import { isSubmissionQueueConfigured } from "@/lib/submission-queue";
import { isSubmissionArchiveConfigured } from "@/lib/submission-archive";
import { computeTrustedMaterialDigest } from "../../../../scripts/trusted-material";

export async function GET(): Promise<NextResponse> {
  const current = getCurrentRecord();
  const e2bConfigured = isE2BConfigured();
  const e2bWebhookConfigured = isE2BWebhookConfigured();
  const promotionConfigured = isGitHubPromotionConfigured();
  const submissionQueueConfigured = isSubmissionQueueConfigured();
  const submissionArchiveConfigured = isSubmissionArchiveConfigured();
  const trustedMaterialAvailable = await computeTrustedMaterialDigest(
    process.cwd(),
    contract.trustedPaths,
  )
    .then(() => true)
    .catch(() => false);
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
    submissionQueueConfigured,
    submissionArchiveConfigured,
    cronBackstopConfigured: Boolean(process.env.CRON_SECRET),
    directSubmissionsConfigured:
      e2bConfigured &&
      e2bWebhookConfigured &&
      promotionConfigured &&
      submissionQueueConfigured &&
      trustedMaterialAvailable,
    trustedMaterialAvailable,
    deploymentIdentityConfigured: Boolean(
      process.env.VERCEL_GIT_COMMIT_SHA ?? process.env.RIEMANN_BASE_COMMIT_SHA,
    ),
  });
}
