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
    type: "large",
    noEnv: true,
    monitoring: false,
    snapshots: false,
    environment: "riemann-production",
    ttlSeconds: 7200,
  });
  expect(JSON.parse(init.body).labels).toMatchObject({ job, kind: "competitive", revision: sha });
  expect(JSON.parse(init.body).setupScript).toContain('test "$actual" = ' + sha);
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
        labels: { service: "riemann", job, kind: "competitive", revision: sha },
      },
    }),
  );
  mockedFetch.mockResolvedValueOnce(Response.json({ ok: true, content: sha + "\n" }));
  await stageBoatFiles(box, "manifest", "solution", digest, { jobId: job, kind: "competitive", sha });
  expect(
    mockedFetch.mock.calls
      .slice(2)
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
    stageBoatFiles(box, "manifest", "solution", digest, { jobId: job, kind: "competitive", sha }),
  ).rejects.toThrow("isolation");
  expect(mockedFetch).toHaveBeenCalledTimes(1);
});

it("allocates the larger worker and limit for an operator replay", async () => {
  mockedFetch.mockResolvedValueOnce(Response.json({ ok: true, sandbox: { id: box } }));
  await createBoatWorker(job, sha, digest, "competitive", true);
  const request = JSON.parse(mockedFetch.mock.calls[0][1].body);
  expect(request.type).toBe("xlarge");
  expect(request.setupScript).toContain(`${digest} competitive 28G`);
});

it("retains fixed supervisor stages on failure without disclosing raw bootstrap content", async () => {
  mockedFetch.mockResolvedValueOnce(Response.json({ ok: true, sandbox: { state: "error", setupStatus: "failed" } }));
  mockedFetch.mockResolvedValueOnce(Response.json({ ok: true, content: "" }));
  mockedFetch.mockResolvedValueOnce(Response.json({ ok: true, content: "2026-11-25T19:00:00Z\twait-zeta-runtime\texit=1\nprivate fixture text\n2026-11-25T19:00:00Z\tprivate-command\tstart" }));
  const result = await boatResult(box, Date.now() + 10000, "test", digest);
  expect(result?.log).toContain("wait-zeta-runtime  exit=1");
  expect(result?.log).not.toContain("private");
});

it.each(["job", "kind", "revision", "checkout", "legacy-checkout"])("refuses to transfer source on a %s mismatch", async field => {
  const labels: Record<string, string> = { service: "riemann", job, kind: "competitive", revision: sha };
  if (field === "legacy-checkout") delete labels.revision;
  else if (field !== "checkout") labels[field] = "different";
  mockedFetch.mockResolvedValueOnce(Response.json({ ok: true, sandbox: {
    environment: "riemann-production", holdsCreatorLogins: false, snapshots: false, labels,
  } })).mockResolvedValueOnce(Response.json({ ok: true, content: "e".repeat(40) }));
  await expect(stageBoatFiles(box, "manifest", "solution", digest, { jobId: job, kind: "competitive", sha })).rejects.toThrow("identity");
  expect(mockedFetch.mock.calls.some(([, init]) => init.method === "PUT")).toBe(false);
});
