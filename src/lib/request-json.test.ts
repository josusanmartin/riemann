import { describe, expect, it } from "vitest";
import { readBoundedJson, RequestBodyTooLargeError } from "./request-json";

function request(body: BodyInit, headers?: HeadersInit) {
  return new Request("https://example.com/submit", {
    method: "POST", body, headers, duplex: "half",
  } as RequestInit);
}

describe("bounded request parsing", () => {
  it("accepts valid UTF-8 JSON up to the actual byte limit", async () => {
    const body = JSON.stringify({ solution: "∀ ε" });
    await expect(readBoundedJson(request(body), Buffer.byteLength(body)))
      .resolves.toEqual({ solution: "∀ ε" });
  });
  it.each([undefined, { "content-length": "1" }])("bounds absent or lying length headers: %s", async (headers) => {
    await expect(readBoundedJson(request('"abcdef"', headers), 4))
      .rejects.toBeInstanceOf(RequestBodyTooLargeError);
  });
  it("cancels oversized chunked bodies", async () => {
    let cancelled = false;
    const stream = new ReadableStream({
      pull(controller) { controller.enqueue(new Uint8Array(3)); },
      cancel() { cancelled = true; },
    });
    await expect(readBoundedJson(request(stream), 4)).rejects.toThrow("4 MB");
    expect(cancelled).toBe(true);
  });
  it("rejects malformed JSON and invalid UTF-8 without silently replacing source", async () => {
    await expect(readBoundedJson(request("{"))).rejects.toBeInstanceOf(SyntaxError);
    await expect(readBoundedJson(request(new Uint8Array([34, 255, 34]))))
      .rejects.toBeInstanceOf(SyntaxError);
  });
});
