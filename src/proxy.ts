import { NextResponse, type NextRequest } from "next/server";
import { contentPolicy } from "./lib/content-policy";

export function proxy(request: NextRequest) {
  const path = request.nextUrl.pathname.replace(/\/$/, "");
  if (path.startsWith("/api/")) {
    const hasHeader = (name: string) => Boolean(request.headers.get(name));
    let admitted: boolean;
    if (path === "/api/submissions/sweep" || path === "/api/e2b/sweep") {
      admitted = hasHeader("authorization");
    } else if (path === "/api/submissions/boat/complete") {
      admitted = hasHeader("x-riemann-notification");
    } else if (path === "/api/e2b/webhook") {
      admitted = hasHeader("e2b-signature") && request.headers.get("e2b-signature-version") === "v1";
    } else {
      // Auth.js may split a session cookie into numbered chunks. Presence
      // only admits a request to the handler, which still verifies identity.
      admitted = hasHeader("authorization") || request.cookies.getAll().some(cookie =>
        /^(?:__Secure-)?authjs\.session-token(?:\.\d+)?$/.test(cookie.name) && Boolean(cookie.value));
    }
    if (admitted) return NextResponse.next();
    const status = path.startsWith("/api/admin/submission-archive/") ? 404 : 401;
    return NextResponse.json({ error: status === 404 ? "not_found" : "unauthorized" }, {
      status,
      headers: { "Cache-Control": "private, no-store", "X-Riemann-Request-Guard": "routing" },
    });
  }
  const policy = contentPolicy(Buffer.from(crypto.randomUUID()).toString("base64"));
  const headers = new Headers(request.headers);
  // Next reads the request policy when adding nonces to its own scripts.
  headers.set("Content-Security-Policy", policy);
  const response = NextResponse.next({ request: { headers } });
  response.headers.set("Content-Security-Policy", policy);
  response.headers.set("Cache-Control", "private, no-store");
  return response;
}

export const config = {
  matcher: [
    "/submit", "/submit/history", "/admin/:path*", "/signin",
    "/api/submissions/:path*", "/api/e2b/sweep", "/api/e2b/webhook", "/api/admin/submission-archive/:path*",
  ],
};
