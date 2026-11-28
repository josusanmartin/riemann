import { afterEach, expect, it, vi } from "vitest";
import { GET } from "./route";

afterEach(() => vi.unstubAllEnvs());

it("reports the active Boat source pin separately from a stale E2B template", async () => {
  const sha = "a".repeat(40);
  vi.stubEnv("RIEMANN_VERIFIER_PROVIDER", "boat");
  vi.stubEnv("VERCEL_GIT_COMMIT_SHA", sha);
  vi.stubEnv("RIEMANN_BASE_COMMIT_SHA", sha);
  vi.stubEnv("E2B_TEMPLATE_DIGEST", "b".repeat(64));
  const health = await (await GET()).json();
  expect(health).toMatchObject({
    verificationSeconds: 10800, workerLifetimeSeconds: 12000,
    verifierIdentity: { provider: "boat", pinType: "git-commit", expectedCommit: sha, configured: true },
    e2bTemplateIdentityConfigured: false, verifierTemplateIdentityConfigured: true,
  });
  vi.stubEnv("RIEMANN_BASE_COMMIT_SHA", "c".repeat(40));
  expect(await (await GET()).json()).toMatchObject({ status: "degraded", directSubmissionsConfigured: false, verifierTemplateIdentityConfigured: false });
});

it("requires a matching digest when E2B is active", async () => {
  vi.stubEnv("RIEMANN_VERIFIER_PROVIDER", "e2b");
  vi.stubEnv("E2B_TEMPLATE_DIGEST", "");
  const missing = await (await GET()).json();
  expect(missing).toMatchObject({ verifierIdentity: { provider: "e2b", pinType: "template-digest", configured: false }, directSubmissionsConfigured: false });
  vi.stubEnv("E2B_TEMPLATE_DIGEST", missing.expectedVerifierTemplateDigest);
  expect(await (await GET()).json()).toMatchObject({ verifierTemplateIdentityConfigured: true, e2bTemplateIdentityConfigured: true });
});
