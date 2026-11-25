import { createHash, randomBytes } from "node:crypto";
import { afterEach, expect, it, vi } from "vitest";
import { encode } from "next-auth/jwt";
import { approveCli, cliBearerPrefix, cliSession, validPairing, pairingPath } from "./cli-login";
import { githubApiIdentity } from "./github-api-identity";

afterEach(() => vi.unstubAllEnvs());
const secret = "cli-test-only-encryption-secret";
const verifier = randomBytes(32).toString("base64url");
const challenge = createHash("sha256").update(verifier).digest("base64url");
const user = { githubId: "123", githubLogin: "fixture-solver" };

it("issues a time-limited CLI session only for the approving account and the matching verifier", async () => {
  vi.stubEnv("AUTH_SECRET", secret);
  const approval = await approveCli({ challenge, until: String(Date.now() + 600000) }, user);
  const authorization = cliBearerPrefix + verifier + "~" + approval;
  const verified = await cliSession(authorization);
  expect(verified?.user).toMatchObject(user);
  expect(Math.abs(Date.parse(verified!.expires) - Date.now() - 86400000)).toBeLessThan(2000);
  expect(await cliSession(cliBearerPrefix + challenge + "~" + approval)).toBeNull();
  expect(await cliSession(cliBearerPrefix + verifier + "~" + approval + "x")).toBeNull();
  const fetcher = vi.fn();
  expect(await githubApiIdentity(new Request("https://example.com", { headers: { authorization } }), fetcher)).toBeNull();
  expect(fetcher).not.toHaveBeenCalled();
});

it("rejects expired approvals and tokens issued for browser sessions", async () => {
  vi.stubEnv("AUTH_SECRET", secret);
  for (const [salt, age] of [["riemann-cli-approval-v1", -2], ["authjs.session-token", 300]] as const) {
    const token = await encode({ secret, salt, maxAge: age, token: { aud: "riemann-submission-cli-v1", ...user, challenge } });
    expect(await cliSession(cliBearerPrefix + verifier + "~" + token)).toBeNull();
  }
});

it("accepts only short-lived requests and numeric loopback ports", () => {
  const req = { challenge, until: String(Date.now() + 600000), port: "34567" };
  expect(validPairing(req)).toEqual(req);
  expect(pairingPath(req)).toMatch(/^\/cli\/login\?/);
  expect(validPairing({ ...req, until: String(Date.now() - 1) })).toBeNull();
  expect(validPairing({ ...req, port: "65536" })).toBeNull();
  expect(validPairing({ ...req, redirectTo: "https://example.org" })).toBeNull();
});
