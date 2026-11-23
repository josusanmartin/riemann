import type { RecordEntry } from "@/lib/challenge";
import { truncateDecimalString } from "@/components/format";

export function recordPresentation(record: RecordEntry) {
  const score = truncateDecimalString(record.scorePercent, 6) + "%";
  const heading = record.title.startsWith("Certified critical-line bound ")
    ? "Distinct zeros on the critical line"
    : record.title;
  const status = record.formalVerification
    ? "Kernel-verified lower bound"
    : "Published lower bound";
  return { score, heading, status };
}
