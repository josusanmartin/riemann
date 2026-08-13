/-
Squeeze a nonnegative error budget between zero and two envelopes tending to
zero.
-/
import Mathlib

open Filter Topology

noncomputable section

namespace Zeta23.GapMatching.VanishingBudgetByEnvelope

/-- A nonnegative function bounded by a function tending to zero also tends
to zero. -/
theorem tendsto_zero_of_nonneg_of_le
    (f g : ℝ → ℝ)
    (hf0 : ∀ᶠ T in atTop, 0 ≤ f T)
    (hfg : ∀ᶠ T in atTop, f T ≤ g T)
    (hg : Tendsto g atTop (𝓝 0)) :
    Tendsto f atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop] at hg ⊢
  intro ε hε
  obtain ⟨a, ha⟩ := hg ε hε
  refine ⟨a, fun b hb => ?_⟩
  have h0 := (hf0.and_eventually (hfg.and_eventually
    (eventually_ge_atTop a))).self_of_nhds
  filter_upwards [hf0, hfg] with T hfT hle
  intro _
  have hgT := ha T hb
  rw [Real.dist_eq] at hgT ⊢
  have habs : |f T| = f T := abs_of_nonneg hfT
  rw [habs]
  exact hle.trans_lt (by simpa [Real.dist_eq] using hgT)

/-- Sum of two nonnegative vanishing errors vanishes. -/
theorem tendsto_add_zero
    (f g : ℝ → ℝ)
    (hf : Tendsto f atTop (𝓝 0))
    (hg : Tendsto g atTop (𝓝 0)) :
    Tendsto (fun T => f T + g T) atTop (𝓝 0) := by
  simpa using hf.add hg

end Zeta23.GapMatching.VanishingBudgetByEnvelope
