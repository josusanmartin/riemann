import { NextResponse } from "next/server";
import { competitionIncumbent, competitionTrackSchema } from "@/lib/challenge";
import { getRecords } from "@/lib/records";

export function GET(request: Request): NextResponse {
  const track = competitionTrackSchema.safeParse(new URL(request.url).searchParams.get("track") ?? "critical-line");
  if (!track.success) return NextResponse.json({ error: "invalid_track" }, { status: 400 });
  const records = getRecords(track.data);
  const incumbent = competitionIncumbent(records, track.data);
  return NextResponse.json(
    {
      schemaVersion: 1,
      track: track.data,
      direction: "higher",
      current: records.find(record => record.id === incumbent.id) ?? null,
      entryThreshold: incumbent.exactRational,
      records,
    },
    {
      headers: {
        "Cache-Control": "public, max-age=60, s-maxage=300, stale-while-revalidate=3600",
      },
    },
  );
}
