import { NextResponse } from "next/server";
import { getCurrentRecord } from "@/lib/records";

export function GET(): NextResponse {
  const current = getCurrentRecord();
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
  });
}
