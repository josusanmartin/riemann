import { readFileSync } from "node:fs";
import { join } from "node:path";
import type { RecordEntry } from "@/lib/challenge";

// Records store only a date, and adding a field would change the trusted
// ledger schema. Kernel-verified submissions already archive an attestation
// with the exact verification time, so read it from the evidence directory.
export function recordVerifiedAt(record: RecordEntry): string | null {
  if (record.status !== "kernel-verified") return null;
  try {
    const attestation = JSON.parse(
      readFileSync(
        join(process.cwd(), "submissions", record.id, "verification", "attestation.json"),
        "utf8",
      ),
    ) as { verifiedAt?: unknown };
    return typeof attestation.verifiedAt === "string" ? attestation.verifiedAt : null;
  } catch {
    return null;
  }
}

const dateFormat = new Intl.DateTimeFormat("en-US", {
  month: "short",
  day: "numeric",
  year: "numeric",
  timeZone: "UTC",
});
const timeFormat = new Intl.DateTimeFormat("en-US", {
  hour: "2-digit",
  minute: "2-digit",
  hourCycle: "h23",
  timeZone: "UTC",
});

/** "Oct 4, 2026 · 05:32 UTC", "Aug 10, 2026", or "1974" for year-only papers. */
export function formatRecordTime(record: RecordEntry, verifiedAt: string | null): string {
  if (verifiedAt) {
    const at = new Date(verifiedAt);
    return `${dateFormat.format(at)} · ${timeFormat.format(at)} UTC`;
  }
  // Historical papers carry a placeholder January 1 date; only the year is real.
  if (record.status === "published" && record.date.endsWith("-01-01")) {
    return record.date.slice(0, 4);
  }
  return dateFormat.format(new Date(`${record.date}T00:00:00Z`));
}

/** Titles carry a 30-digit decimal; trailing zeros add width, not precision. */
export function displayRecordTitle(record: RecordEntry): string {
  return record.title.replace(/(\.\d*?[1-9])0+$/, "$1");
}
