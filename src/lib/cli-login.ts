import { createHash, timingSafeEqual } from "node:crypto";
import { decode, encode } from "next-auth/jwt";
import { z } from "zod";
import { githubLoginSchema } from "./challenge";

const audience = "riemann-submission-cli-v1";
const salt = "riemann-cli-approval-v1";
const secretPattern = /^[A-Za-z0-9_-]{43}$/;
const lifetime = 24 * 60 * 60;
export const cliBearerPrefix = "Bearer rcli1_";

export const pairingSchema = z.object({
  challenge: z.string().regex(secretPattern),
  until: z.string().regex(/^\d{13}$/),
  port: z.string().regex(/^[1-9]\d{3,4}$/).refine(p => +p >= 1024 && +p <= 65535).optional(),
}).strict();

export type Pairing = z.infer<typeof pairingSchema>;
export function validPairing(input: unknown, now = Date.now()): Pairing | null {
  const parsed = pairingSchema.safeParse(input);
  if (!parsed.success) return null;
  const remaining = Number(parsed.data.until) - now;
  return remaining > 0 && remaining <= 11 * 60_000 ? parsed.data : null;
}

export function pairingPath(pairing: Pairing) {
  return "/cli/login?" + new URLSearchParams(Object.entries(pairing).filter((v): v is [string, string] => v[1] !== undefined)).toString();
}

const identity = z.object({
  githubLogin: githubLoginSchema,
  githubId: z.string().regex(/^[1-9]\d{0,19}$/),
});

export async function approveCli(pairing: Pairing, user: unknown) {
  const secret = process.env.AUTH_SECRET;
  if (!secret || !validPairing(pairing)) throw new Error("Start a new CLI login.");
  // The browser sees only this encrypted approval and the public challenge.
  // Both the approval and the locally held 256-bit verifier are required.
  return encode({ secret, salt, maxAge: lifetime,
    token: { aud: audience, challenge: pairing.challenge, ...identity.parse(user) } });
}

export async function cliSession(authorization: string) {
  const secret = process.env.AUTH_SECRET;
  if (!secret || !authorization.startsWith(cliBearerPrefix) || authorization.length > 4096) return null;
  const [verifier, approval, extra] = authorization.slice(cliBearerPrefix.length).split("~");
  if (!secretPattern.test(verifier) || !approval || extra !== undefined) return null;
  try {
    const payload = await decode({ secret, salt, token: approval });
    if (!payload || payload.aud !== audience || typeof payload.exp !== "number" || payload.exp <= Date.now() / 1000) return null;
    const user = identity.parse(payload);
    const challenge = createHash("sha256").update(verifier).digest("base64url");
    if (typeof payload.challenge !== "string" || !secretPattern.test(payload.challenge) ||
        !timingSafeEqual(Buffer.from(challenge), Buffer.from(payload.challenge))) return null;
    return { user: { ...user, name: user.githubLogin }, expires: new Date(payload.exp * 1000).toISOString() };
  } catch { return null; }
}
