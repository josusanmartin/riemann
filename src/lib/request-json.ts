// Bound the bytes actually received, not just an optional, untrusted header.
// Allow JSON escaping overhead while staying below Vercel's request limit.
export const MAX_SUBMISSION_REQUEST_BYTES = 4_000_000;

export class RequestBodyTooLargeError extends Error {
  constructor() {
    super("The encoded submission request exceeds the 4 MB limit (Lean source: 2 MB).");
    this.name = "RequestBodyTooLargeError";
  }
}

export async function readBoundedJson(
  request: Request,
  limit = MAX_SUBMISSION_REQUEST_BYTES,
): Promise<unknown> {
  if (Number(request.headers.get("content-length")) > limit) {
    throw new RequestBodyTooLargeError();
  }
  if (!request.body) throw new SyntaxError("A JSON request body is required");
  const reader = request.body.getReader();
  const chunks: Uint8Array[] = [];
  let size = 0;
  try {
    for (;;) {
      const { done, value } = await reader.read();
      if (done) break;
      size += value.byteLength;
      if (size > limit) {
        await reader.cancel().catch(() => undefined);
        throw new RequestBodyTooLargeError();
      }
      chunks.push(value);
    }
  } finally {
    reader.releaseLock();
  }
  let text: string;
  try {
    text = new TextDecoder("utf-8", { fatal: true }).decode(Buffer.concat(chunks));
  } catch {
    throw new SyntaxError("Request body is not valid UTF-8");
  }
  return JSON.parse(text);
}
