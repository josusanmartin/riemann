import { afterEach, beforeEach, describe, expect, it, vi } from "vitest";

vi.mock("server-only", () => ({}));
const { getSession } = vi.hoisted(() => ({ getSession: vi.fn() }));
vi.mock("@/auth", () => ({ getSession }));

import { POST } from "./route";

const call = () => POST(new Request("https://example.com/api/admin/boat-smoke", {
  method: "POST", headers: { "Content-Type": "application/json" },
}));
const fetchBoat = vi.fn();

beforeEach(() => {
  vi.stubEnv("RIEMANN_FLOW_TEST_GITHUB", "operator:123");
  vi.stubEnv("RIEMANN_BOAT_SANDBOX_ID", "bx_23456789");
  vi.stubEnv("BOAT_API_KEY", "fixture");
  vi.stubGlobal("fetch", fetchBoat);
  getSession.mockResolvedValue({ user: { githubLogin: "operator", githubId: "123" } });
});

afterEach(() => {
  vi.clearAllMocks();
  vi.unstubAllGlobals();
  vi.unstubAllEnvs();
});

describe("Boat operator test", () => {
  it("requires an allowed operator before calling Boat", async () => {
    getSession.mockResolvedValue({ user: { githubLogin: "guest" } });
    expect((await call()).status).toBe(403);
    expect(fetchBoat).not.toHaveBeenCalled();
  });

  it.each([
    [{ success: true, exitCode: 0, stdout: "BOAT_SMOKE_OK\n" }, 200],
    [{ success: true, exitCode: 0, stdout: "only one control passed" }, 422],
    [{ success: false, exitCode: 1, stdout: "BOAT_SMOKE_OK" }, 422],
    [{ success: false, exitCode: 75 }, 409],
    [{ success: true, exitCode: 0, timedOut: true, stdout: "BOAT_SMOKE_OK" }, 422],
  ])("checks both the command outcome and its completion marker", async (result, status) => {
    fetchBoat.mockResolvedValue(Response.json({ ok: true, type: "command.finished", ...result }));
    expect((await call()).status).toBe(status);
  });
});
