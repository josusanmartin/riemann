import { describe, expect, it } from "vitest";
import { flowTestSolutionSource } from "@/lib/flow-test";
import { GET } from "./route";

describe("GET /templates/FlowTest.lean", () => {
  it("downloads the complete official flow-test proof", async () => {
    const response = GET();
    expect(response.status).toBe(200);
    expect(response.headers.get("content-disposition")).toContain("Solution.lean");
    expect(await response.text()).toBe(flowTestSolutionSource);
  });
});
