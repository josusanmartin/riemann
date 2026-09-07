import { NextResponse } from "next/server";
import { contract, getCurrentRecord } from "@/lib/records";
import { getE2BTemplate, isE2BConfigured } from "@/lib/e2b-config";
import { isE2BWebhookConfigured } from "@/lib/e2b-webhooks";
import { isGitHubPromotionConfigured } from "@/lib/github-promotion";
import { isSubmissionQueueConfigured } from "@/lib/submission-queue";
import { isSubmissionArchiveConfigured } from "@/lib/submission-archive";
import { computeTrustedMaterialDigest, computeVerifierTemplateDigest } from "../../../../scripts/trusted-material";

export async function GET(): Promise<NextResponse> {
  const current = getCurrentRecord();
  const e2bConfigured = isE2BConfigured();
  const e2bWebhookConfigured = isE2BWebhookConfigured();
  const promotionConfigured = isGitHubPromotionConfigured();
  const submissionQueueConfigured = isSubmissionQueueConfigured();
  const submissionArchiveConfigured = isSubmissionArchiveConfigured();
  const expectedVerifierTemplateDigest = await computeVerifierTemplateDigest(
    process.cwd(), contract.trustedPaths,
  ).catch(() => null);
  const verifierTemplateIdentityConfigured = Boolean(
    expectedVerifierTemplateDigest &&
    process.env.E2B_TEMPLATE_DIGEST === expectedVerifierTemplateDigest,
  );
  const trustedMaterialAvailable = await computeTrustedMaterialDigest(
    process.cwd(),
    contract.trustedPaths,
  )
    .then(() => true)
    .catch(() => false);
  const deploymentIdentityConfigured = /^[0-9a-f]{40}$/.test(
    process.env.VERCEL_GIT_COMMIT_SHA ?? process.env.RIEMANN_BASE_COMMIT_SHA ?? "",
  );
  const directSubmissionsConfigured = Boolean(
    e2bConfigured && e2bWebhookConfigured && promotionConfigured &&
    submissionQueueConfigured && trustedMaterialAvailable &&
    verifierTemplateIdentityConfigured && deploymentIdentityConfigured && process.env.AUTH_SECRET,
  );
  return NextResponse.json({
    status: directSubmissionsConfigured ? "ok" : "degraded",
    checkScope: "configuration-only; each upload checks the actual sandbox identity before admission",
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
    expectedVerifierTemplateDigest,
    verifierTemplateIdentityConfigured,
    e2bWebhookConfigured,
    promotionConfigured,
    submissionQueueConfigured,
    submissionArchiveConfigured,
    cronBackstopConfigured: Boolean(process.env.CRON_SECRET),
    directSubmissionsConfigured,
    trustedMaterialAvailable,
    deploymentIdentityConfigured,
  });
}
