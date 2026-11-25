import { NextResponse, type NextRequest } from "next/server";
import { contentPolicy } from "./lib/content-policy";

export function proxy(request: NextRequest) {
  const policy = contentPolicy(Buffer.from(crypto.randomUUID()).toString("base64"));
  const headers = new Headers(request.headers);
  // Next reads the request policy when adding nonces to its own scripts.
  headers.set("Content-Security-Policy", policy);
  const response = NextResponse.next({ request: { headers } });
  response.headers.set("Content-Security-Policy", policy);
  response.headers.set("Cache-Control", "private, no-store");
  return response;
}

export const config = { matcher: ["/submit", "/submit/history", "/admin/:path*", "/signin"] };
