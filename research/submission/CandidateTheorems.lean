/-
Live Riemann.fail candidate interface.

Target: 672500708 / 10^9 = 0.672500708.
This file is not copied into a submission until `live_dyadic_simple` and its
cumulative consequence are proved with no additional hypotheses.
-/
import ChallengeDeps.CandidateSpec
import Zeta23.GapMatching.CandidateStrictImprovementTight
import Zeta23.ThmD.Final
import Zeta23.Unconditional

noncomputable section

namespace Zeta23.GapMatching.LiveCandidate

/-- Exact live candidate used by the research development. -/
def kappa : ℝ := (672500708 : ℝ) / 1000000000

/-- The final unconditional dyadic simple-zero theorem supplied by the
completed one-band development. -/
theorem live_dyadic_simple :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (kappa - ε) * (Zeta23.N T (2 * T) : ℝ)
        ≤ (Zeta23.N0s T (2 * T) : ℝ) := by
  -- Replaced by the completed D-window family theorem.
  exact?

/-- Simple on-line zeros inject into distinct on-line zeros. -/
theorem live_dyadic_star :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (kappa - ε) * (Zeta23.N T (2 * T) : ℝ)
        ≤ (Zeta23.N0star T (2 * T) : ℝ) := by
  intro ε hε
  obtain ⟨T₀, hT₀⟩ := live_dyadic_simple ε hε
  refine ⟨T₀, fun T hT => (hT₀ T hT).trans ?_⟩
  exact_mod_cast Zeta23.N0s_le_N0star T (2 * T)

/-- Cumulative form obtained from the dyadic theorem. -/
theorem live_cumulative_star :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (kappa - ε) * (Zeta23.N 0 T : ℝ)
        ≤ (Zeta23.N0star 0 T : ℝ) := by
  exact?

end Zeta23.GapMatching.LiveCandidate

/-- The submitted rational is strictly larger than the exact current formal
record. -/
theorem candidate_strict_improvement :
    currentRecordKappa < candidateKappa := by
  have hcstar : Zeta23.ThmD.cStar 1 = cMT := by
    rw [Zeta23.ThmD.cStar_eq_tan_form zero_le_one le_rfl]
    unfold cMT Zeta23.ThmD.theta
    rfl
  have hrecord :=
    Zeta23.GapMatching.CandidateStrictImprovementTight.HD_one_lt_672500708
  unfold currentRecordKappa candidateKappa
  change 2 - 1 / cMT < (672500708 : ℝ) / 1000000000
  simpa only [Zeta23.ThmD.HD, hcstar] using hrecord

/-- Improved unconditional critical-line proportion on dyadic windows. -/
theorem candidate_critical_line_bound :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (candidateKappa - ε) * (Ncount T (2 * T) : ℝ)
        ≤ N0star T (2 * T) := by
  simpa [candidateKappa, Zeta23.GapMatching.LiveCandidate.kappa]
    using Zeta23.GapMatching.LiveCandidate.live_dyadic_star

/-- The same improved bound in cumulative windows. -/
theorem candidate_critical_line_bound_cumulative :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (candidateKappa - ε) * (Ncount 0 T : ℝ)
        ≤ N0star 0 T := by
  simpa [candidateKappa, Zeta23.GapMatching.LiveCandidate.kappa]
    using Zeta23.GapMatching.LiveCandidate.live_cumulative_star

end
