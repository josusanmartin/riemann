import {
  recordSchema,
  type RecordEntry,
} from "@/lib/challenge";
import { repository } from "@/lib/site";

export const FLOW_TEST_BASELINE_ID = "riemann-fail-flow-test-one-third";
export const FLOW_TEST_SCORE = { numerator: "2", denominator: "3" } as const;
export const FLOW_TEST_GIST_URL =
  "https://gist.github.com/josusanmartin/15f310b66c7e41ed11698133e731bd4d";
export const FLOW_TEST_DOWNLOAD_PATH = "/templates/FlowTest.lean";

export const flowTestRecord: RecordEntry = recordSchema.parse({
  id: FLOW_TEST_BASELINE_ID,
  track: "critical-line",
  date: "2026-08-13",
  author: "Riemann.fail test fixture",
  github: "josusanmartin",
  title: "Noncompetitive verifier flow baseline",
  method: "Controlled one-third baseline for an Anthropic theorem replay",
  model: null,
  harness: null,
  scoreDecimal: "0.333333333333333333333333333333",
  scorePercent: "33.3333333333333333333333333333",
  exactRational: { numerator: "1", denominator: "3" },
  exactExpression: "1 / 3",
  status: "kernel-verified",
  formalVerification: true,
  independentReview: null,
  sourceUrl: "https://www.anthropic.com/research/riemann-zeta",
  proofUrl: "https://github.com/anthropics/zeta-23-lean",
  pullRequestUrl: null,
  summary:
    "An isolated test-only baseline used to exercise the verifier without changing the competitive record.",
});

export const flowTestSolutionSource = `/-
Riemann.fail official flow-test proof

This is a complete proof for the NONCOMPETITIVE verifier-flow contract, whose
controlled baseline is 1/3 and candidate is 2/3. It replays the unconditional
theorems from Anthropic's pinned Zeta23 formalization. It cannot be submitted
as a live leaderboard improvement: the live record is already strictly above
2/3, at 2 - 1 / cMT.
-/

import ChallengeDeps.CandidateSpec
import Zeta23.Unconditional

noncomputable section

theorem candidate_strict_improvement :
    currentRecordKappa < candidateKappa := by
  norm_num [currentRecordKappa, candidateKappa]

theorem candidate_critical_line_bound :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (candidateKappa - ε) * (Ncount T (2 * T) : ℝ) ≤ N0star T (2 * T) := by
  exact Zeta23.thmA₀

theorem candidate_critical_line_bound_cumulative :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (candidateKappa - ε) * (Ncount 0 T : ℝ) ≤ N0star 0 T := by
  exact Zeta23.thmA₀_cumulative

end
`;

/** Keep the costly noncompetitive lane operator-only unless explicitly configured. */
export function isFlowTestOperator(github: string): boolean {
  const repositoryOwner = repository.split("/")[0] ?? "";
  const configured = process.env.RIEMANN_FLOW_TEST_GITHUB ?? repositoryOwner;
  const login = github.toLowerCase();
  return configured
    .split(",")
    .map((value) => value.trim().toLowerCase())
    .filter(Boolean)
    .includes(login);
}
