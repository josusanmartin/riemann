import { afterEach, beforeEach, expect, it, vi } from "vitest";
import { boatResult, createBoatWorker, stageBoatFiles } from "./boat-worker";

const job = "12345678-1234-4123-8123-123456789abc",
  box = "bx_23456789",
  sha = "a".repeat(40),
  digest = "b".repeat(64);
const mockedFetch = vi.fn();
beforeEach(() => {
  vi.stubEnv("RIEMANN_BOAT_API_KEY", "fixture");
  vi.stubGlobal("fetch", mockedFetch);
});
afterEach(() => {
  vi.resetAllMocks();
  vi.unstubAllEnvs();
  vi.unstubAllGlobals();
});

it("uses one idempotency key per reserved job and isolates account data", async () => {
  mockedFetch.mockResolvedValueOnce(
    Response.json({ ok: true, sandbox: { id: box } }),
  );
  expect(await createBoatWorker(job, sha, digest, "competitive")).toBe(box);
  const [url, init] = mockedFetch.mock.calls[0];
  expect(url).toBe("https://boat.dev/api/v1/sandboxes");
  expect(init.headers["Idempotency-Key"]).toBe(job);
  expect(JSON.parse(init.body)).toMatchObject({
    noEnv: true,
    monitoring: false,
    snapshots: false,
    environment: "riemann-production",
    ttlSeconds: 7200,
  });
  expect(JSON.parse(init.body).setupScript).toContain(sha);
});

it("validates the commit before issuing a provider request", async () => {
  await expect(createBoatWorker(job, "main", digest, "flow")).rejects.toThrow();
  expect(mockedFetch).not.toHaveBeenCalled();
});

it("publishes the ready marker only after both files have been uploaded", async () => {
  mockedFetch.mockImplementation(async () => Response.json({ ok: true }));
  mockedFetch.mockResolvedValueOnce(
    Response.json({
      ok: true,
      sandbox: {
        environment: "riemann-production",
        holdsCreatorLogins: false,
        snapshots: false,
        labels: { service: "riemann" },
      },
    }),
  );
  await stageBoatFiles(box, "manifest", "solution", digest);
  expect(
    mockedFetch.mock.calls
      .slice(1)
      .map(([, init]) => JSON.parse(init.body).path),
  ).toEqual([
    "riemann-incoming/manifest",
    "riemann-incoming/solution",
    "riemann-incoming/ready",
  ]);
});

it("keeps running jobs separate from infrastructure failures", async () => {
  mockedFetch.mockResolvedValueOnce(
    Response.json({
      ok: true,
      sandbox: { state: "idle", setupStatus: "running" },
    }),
  );
  expect(await boatResult(box, Date.now() + 60000, "test", digest)).toBeNull();
  mockedFetch.mockResolvedValueOnce(
    Response.json({ ok: false, code: "not_found" }, { status: 404 }),
  );
  expect(
    (await boatResult(box, Date.now() + 60000, "test", digest))?.status,
  ).toBe("rejected");
});

it("does not transfer sources if the workspace received creator logins", async () => {
  mockedFetch.mockResolvedValueOnce(
    Response.json({
      ok: true,
      sandbox: { environment: "riemann-production", holdsCreatorLogins: true },
    }),
  );
  await expect(
    stageBoatFiles(box, "manifest", "solution", digest),
  ).rejects.toThrow("isolation");
  expect(mockedFetch).toHaveBeenCalledTimes(1);
});
