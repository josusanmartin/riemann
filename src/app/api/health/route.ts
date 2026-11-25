import { boatSelected,boatConfigured } from "@/lib/boat-worker";
import { NextResponse } from "next/server";
import { contract, getCurrentRecord } from "@/lib/records";
import { getE2BTemplate, isE2BConfigured } from "@/lib/e2b-config";
import { isE2BWebhookConfigured } from "@/lib/e2b-webhooks";
import { isGitHubPromotionConfigured } from "@/lib/github-promotion";
import { isSubmissionQueueConfigured } from "@/lib/submission-queue";
import { isSubmissionArchiveConfigured } from "@/lib/submission-archive";
import { computeTrustedMaterialDigest, computeVerifierTemplateDigest } from "../../../../scripts/trusted-material";

// Trusted files are immutable within a deployment. Share in-flight hash work
// across probes, with a short retry interval if a filesystem check fails.
let cachedChecks: { expires: number; value: Promise<[string | null, boolean]> } | undefined;
function checkTrustedFiles() {
  if (!cachedChecks || cachedChecks.expires <= Date.now()) {
    const value = Promise.all([
      computeVerifierTemplateDigest(process.cwd(), contract.trustedPaths).catch(() => null),
      computeTrustedMaterialDigest(process.cwd(), contract.trustedPaths).then(() => true, () => false),
    ] as const);
    cachedChecks = { expires: Date.now() + 60_000, value };
  }
  return cachedChecks.value;
}

export async function GET(): Promise<NextResponse> {
  const current = getCurrentRecord();
  const e2bConfigured = isE2BConfigured();
  const e2bWebhookConfigured = isE2BWebhookConfigured();
  const promotionConfigured = isGitHubPromotionConfigured();
  const submissionQueueConfigured = isSubmissionQueueConfigured();
  const submissionArchiveConfigured = isSubmissionArchiveConfigured();
  const [expectedVerifierTemplateDigest, trustedMaterialAvailable] = await checkTrustedFiles();
  const verifierTemplateIdentityConfigured = Boolean(
    expectedVerifierTemplateDigest &&
    process.env.E2B_TEMPLATE_DIGEST === expectedVerifierTemplateDigest,
  );
  const deploymentIdentityConfigured = /^[0-9a-f]{40}$/.test(
    process.env.VERCEL_GIT_COMMIT_SHA ?? process.env.RIEMANN_BASE_COMMIT_SHA ?? "",
  );
  const directSubmissionsConfigured = Boolean(
    (boatSelected() ? boatConfigured() : e2bConfigured && e2bWebhookConfigured && verifierTemplateIdentityConfigured) && promotionConfigured &&
    submissionQueueConfigured && trustedMaterialAvailable &&
    deploymentIdentityConfigured && process.env.AUTH_SECRET,
  );
  return NextResponse.json({
    status: directSubmissionsConfigured ? "ok" : "degraded",
    checkScope: boatSelected() ? "configuration-only; the active FIFO job checks its Boat worker before source transfer" : "configuration-only; each upload checks the actual sandbox identity before admission",
    service: "riemann-fail",
    verificationPolicyVersion: contract.schemaVersion,
    leanToolchain: contract.trustedUpstream.leanToolchain,
    rhFoundationCommit: contract.trustedUpstream.rh.commit,
    recordId: current.id,
    record: current.scoreDecimal,
    authConfigured: Boolean(
      process.env.AUTH_GITHUB_ID &&
        process.env.AUTH_GITHUB_SECRET &&
        process.env.AUTH_SECRET,
    ),
    verifierProvider: boatSelected() ? "boat" : "e2b",
    boatConfigured: boatConfigured(),
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
  }, { headers: { "Cache-Control": "public, max-age=0, s-maxage=30" } });
}
