import { afterEach, expect, it, vi } from "vitest";
import { guardUserApi } from "./api-guard";

const url = "https://www.riemannzeta.fun/api/submissions";
afterEach(() => vi.unstubAllEnvs());

it("preserves JSON clients while rejecting cross-origin browser writes and simple form posts", () => {
  for (const origin of [undefined, new URL(url).origin]) {
    const headers = new Headers({ "content-type": "application/json" });
    if (origin) headers.set("origin", origin);
    expect(guardUserApi(new Request(url, { headers }), "upload")).toBeNull();
  }
  expect(guardUserApi(new Request(url), "upload")?.status).toBe(415);
  expect(guardUserApi(new Request(url, { headers: { origin: "https://example.org", "content-type": "application/json" } }), "upload")?.status).toBe(403);
});

it("applies a bounded burst window per platform-supplied IP and operation", () => {
  vi.stubEnv("VERCEL", "1");
  const req = new Request(url, { headers: { "content-type": "application/json", "x-vercel-forwarded-for": "192.0.2.1" } });
  for (let i = 0; i < 20; i++) expect(guardUserApi(req, "upload", 1000)).toBeNull();
  const limited = guardUserApi(req, "upload", 2000);
  expect(limited?.status).toBe(429);
  expect(limited?.headers.get("retry-after")).toBe("59");
  expect(guardUserApi(req, "poll", 2000)).toBeNull();
  expect(guardUserApi(req, "upload", 61_000)).toBeNull();
});
