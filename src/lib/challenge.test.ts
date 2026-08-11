import { describe, expect, it } from "vitest";
import {
  compareDecimalStrings,
  compareRationals,
  decimalToPercent,
  rationalToDecimal,
  submissionSchema,
} from "@/lib/challenge";

describe("challenge primitives", () => {
  it("compares arbitrarily large rational scores exactly", () => {
    expect(
      compareRationals(
        { numerator: "672500704", denominator: "1000000000" },
        { numerator: "672500703", denominator: "1000000000" },
      ),
    ).toBe(1);
  });

  it("renders a rational without floating point rounding", () => {
    expect(rationalToDecimal("1", "3", 8)).toBe("0.33333333");
  });

  it("compares display decimals without IEEE-754 precision loss", () => {
    expect(
      compareDecimalStrings(
        "0.672500703679411645734379790804",
        "0.672500703679411645734379790803",
      ),
    ).toBe(1);
    expect(compareDecimalStrings("1.0", "0.999999999999999999999999999999")).toBe(1);
  });

  it("derives the displayed percentage without floating-point arithmetic", () => {
    expect(decimalToPercent("0.672500703679411645734379790803")).toBe(
      "67.2500703679411645734379790803",
    );
    expect(decimalToPercent("1.0")).toBe("100.0");
  });

  it("rejects a floating-point score", () => {
    const result = submissionSchema.safeParse({
      schemaVersion: 1,
      id: "invalid",
      track: "critical-line",
      author: { github: "solver", displayName: "Solver" },
      score: { numerator: "0.7", denominator: "1" },
      proof: {
        solution: "proof/Solution.lean",
        theorem: "candidate_critical_line_bound",
        cumulativeTheorem: "candidate_critical_line_bound_cumulative",
        improvementTheorem: "candidate_strict_improvement",
      },
      summary: "A candidate that should fail schema validation.",
      method: "invalid",
      license: "Apache-2.0",
    });

    expect(result.success).toBe(false);
  });

  it("rejects undeclared submission fields", () => {
    const result = submissionSchema.safeParse({
      schemaVersion: 1,
      id: "extra-field",
      track: "critical-line",
      author: { github: "solver", displayName: "Solver" },
      score: { numerator: "7", denominator: "10", rounded: 0.7 },
      proof: {
        solution: "proof/Solution.lean",
        theorem: "candidate_critical_line_bound",
        cumulativeTheorem: "candidate_critical_line_bound_cumulative",
        improvementTheorem: "candidate_strict_improvement",
      },
      summary: "A candidate containing an undeclared score field.",
      method: "invalid extras",
      license: "Apache-2.0",
    });

    expect(result.success).toBe(false);
  });
});
