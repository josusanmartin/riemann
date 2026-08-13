/-
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
