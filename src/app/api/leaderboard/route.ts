import { NextResponse } from "next/server";
import { contract, getCurrentRecord, records } from "@/lib/records";

export function GET(): NextResponse {
  return NextResponse.json(
    {
      schemaVersion: 1,
      track: contract.track,
      direction: contract.direction,
      current: getCurrentRecord(),
      records,
    },
    {
      headers: {
        "Cache-Control": "public, max-age=60, s-maxage=300, stale-while-revalidate=3600",
      },
    },
  );
}
