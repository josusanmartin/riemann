import contractJson from "../../challenge/contract.json";
import recordsJson from "../../data/records.json";
import {
  contractSchema,
  recordsSchema,
  type RecordEntry,
  type Track,
} from "@/lib/challenge";

export const contract = contractSchema.parse(contractJson);
export const records = recordsSchema.parse(recordsJson);

export function getRecords(track: Track = "critical-line"): RecordEntry[] {
  return records.filter((record) => record.track === track);
}

export function getCurrentRecord(track: Track = "critical-line"): RecordEntry {
  const trackRecords = getRecords(track);
  const current =
    trackRecords.filter((record) => record.status === "kernel-verified").at(-1) ??
    trackRecords.filter((record) => record.status === "published").at(-1);

  if (!current) {
    throw new Error(`No eligible record for track ${track}`);
  }

  return current;
}

export function getRecord(id: string): RecordEntry | undefined {
  return records.find((record) => record.id === id);
}
