import timeLimits from "../../../../boat/compact/time-limits.json";
import nanodaRelease from "../../../../boat/compact/nanoda-release.json";
import { compactRuntimePinned } from "@/lib/compact-runtime";
import { deploymentVerifierCommit, e2bTemplatePinMatches } from "@/lib/verifier-identity";
import { boatSelected, boatConfigured } from "@/lib/boat-worker";
import { NextResponse } from "next/server";
import { contract, getCurrentRecord } from "@/lib/records";
import { getE2BTemplate, isE2BConfigured } from "@/lib/e2b-config";
import { isE2BWebhookConfigured } from "@/lib/e2b-webhooks";
import { isGitHubPromotionConfigured } from "@/lib/github-promotion";
import { isSubmissionQueueConfigured } from "@/lib/submission-queue";
import { isSubmissionArchiveConfigured } from "@/lib/submission-archive";
import { publicationDigests } from "@/lib/publication-material";

// Trusted files are immutable within a deployment. Share in-flight hash work
// across probes, with a short retry interval if a filesystem check fails.
let cachedChecks: { expires: number; value: Promise<[string | null, string | null]> } | undefined;
function checkTrustedFiles() {
  if (!cachedChecks || cachedChecks.expires <= Date.now()) {
    const value = publicationDigests().then(({ template, challenge }): [string, string] => [template, challenge])
      .catch((): [null, null] => [null, null]);
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
  const [expectedVerifierTemplateDigest, expectedChallengeDigest] = await checkTrustedFiles();
  const trustedMaterialAvailable = Boolean(expectedChallengeDigest);
  const isBoat = boatSelected();
  const sourceCommit = deploymentVerifierCommit();
  const deploymentIdentityConfigured = sourceCommit !== null;
  const e2bTemplateIdentityConfigured = e2bTemplatePinMatches(expectedVerifierTemplateDigest);
  const verifierIdentity = isBoat
    ? { provider: "boat", pinType: "git-commit", expectedCommit: sourceCommit,
        configured: Boolean(sourceCommit && expectedVerifierTemplateDigest && trustedMaterialAvailable) }
    : { provider: "e2b", pinType: "template-digest", expectedDigest: expectedVerifierTemplateDigest,
        configured: e2bTemplateIdentityConfigured };
  const directSubmissionsConfigured = Boolean(
    isBoat && boatConfigured() && compactRuntimePinned() && verifierIdentity.configured &&
    promotionConfigured && submissionQueueConfigured && trustedMaterialAvailable &&
    deploymentIdentityConfigured && process.env.AUTH_SECRET,
  );
  return NextResponse.json({
    status: directSubmissionsConfigured ? "ok" : "degraded",
    admissionsPaused: process.env.SUBMISSIONS_PAUSED === "1",
    acceptingSubmissions: directSubmissionsConfigured && process.env.SUBMISSIONS_PAUSED !== "1",
    checkScope: isBoat ? "configuration-only; each Boat job checks its worker identity and checked-out source revision before proof transfer, and its attestation digest before publication" : "configuration-only; each upload checks the actual sandbox identity before admission",
    service: "riemann-fail",
    verificationPolicyVersion: contract.schemaVersion,
    ...(isBoat && timeLimits),
    nanodaVersion: nanodaRelease.version,
    nanodaSourceCommit: nanodaRelease.revision,
    nanodaBinarySha256: nanodaRelease.linuxX64Sha256,
    leanToolchain: contract.trustedUpstream.leanToolchain,
    compactRuntimePinned: compactRuntimePinned(),
    permittedAxioms: contract.permittedAxioms,
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
    expectedChallengeDigest,
    verifierIdentity,
    // Backward-compatible active-provider signal for existing monitors.
    verifierTemplateIdentityConfigured: verifierIdentity.configured,
    e2bTemplateIdentityConfigured,
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
