import { describe, expect, it, vi } from "vitest";
import { githubApiIdentity } from "./github-api-identity";

const request = new Request("https://www.riemannzeta.fun/api/submissions", {
  headers: { Authorization: `Bearer ${"x".repeat(30)}` },
});
describe("GitHub CLI identity", () => {
  it("uses only GitHub's authenticated identity with no caching or redirects", async () => {
    const fetcher = vi.fn().mockResolvedValue(Response.json({ id: 1, login: "solver", name: null, type: "User" }));
    await expect(githubApiIdentity(request, fetcher)).resolves.toMatchObject({ login: "solver", id: 1 });
    expect(fetcher).toHaveBeenCalledWith("https://api.github.com/user", expect.objectContaining({ cache: "no-store", redirect: "error" }));
  });
  it("fails closed for invalid tokens, malformed identities and upstream failure", async () => {
    for (const response of [Response.json({}, { status: 401 }), Response.json({ login: "solver" })]) {
      expect(await githubApiIdentity(request, vi.fn().mockResolvedValue(response))).toBeNull();
    }
    expect(await githubApiIdentity(request, vi.fn().mockRejectedValue(new Error("network")))).toBeNull();
    const fetcher = vi.fn();
    expect(await githubApiIdentity(new Request(request.url), fetcher)).toBeNull();
    expect(fetcher).not.toHaveBeenCalled();
  });
});
