import type { RecordEntry } from "./challenge";

// Supplementary evidence for the same record. Its original admission receipt is versioned separately.
export const compactReplay = {
  recordId: "knausgard-rh-reflected-kernel-8542",
  foundationCommit: "72fead102f663d5c7a407964a13dc0cf9d977207",
  releaseUrl: "https://github.com/josusanmartin/riemann/releases/tag/compact-rh-854225-v1",
} as const;

export function compactCertificateUrl(record: RecordEntry): string | undefined {
  if (record.id === compactReplay.recordId) return compactReplay.releaseUrl;
  if (record.rhFoundationCommit === compactReplay.foundationCommit && record.sourceUrl.endsWith("/submission.json")) {
    return new URL("verification/attestation.json", record.sourceUrl).href;
  }
}
