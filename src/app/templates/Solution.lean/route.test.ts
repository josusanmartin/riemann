import { describe, expect, it } from "vitest";
import { GET } from "@/app/templates/Solution.lean/route";
import { submissionStarterSource } from "@/lib/submission-starter";

describe("Solution.lean starter download", () => {
  it("serves the canonical source as a named plain-text attachment", async () => {
    const response = GET();

    expect(response.status).toBe(200);
    expect(response.headers.get("content-type")).toBe(
      "text/plain; charset=utf-8",
    );
    expect(response.headers.get("content-disposition")).toBe(
      'attachment; filename="Solution.lean"',
    );
    await expect(response.text()).resolves.toBe(submissionStarterSource);
  });
});
