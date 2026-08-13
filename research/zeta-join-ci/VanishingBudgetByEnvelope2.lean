/-
Order-theoretic squeeze lemmas for nonnegative overlap-error envelopes.
-/
import Mathlib

open Filter Topology

noncomputable section

namespace Zeta23.GapMatching.VanishingBudgetByEnvelope2

/-- A nonnegative function eventually bounded above by a function tending to
zero also tends to zero. -/
theorem tendsto_zero_of_nonneg_of_le
    (f g : ℝ → ℝ)
    (hf0 : ∀ᶠ T in atTop, 0 ≤ f T)
    (hfg : ∀ᶠ T in atTop, f T ≤ g T)
    (hg : Tendsto g atTop (𝓝 0)) :
    Tendsto f atTop (𝓝 0) := by
  rw [tendsto_order]
  constructor
  · intro a ha
    have ha0 : a < 0 := by simpa using ha
    filter_upwards [hf0] with T hT
    exact ha0.trans_le hT
  · intro b hb
    have hgb : ∀ᶠ T in atTop, g T < b :=
      (tendsto_order.1 hg).2 b hb
    filter_upwards [hfg, hgb] with T hle hlt
    exact hle.trans_lt hlt

/-- Sum of two functions tending to zero tends to zero. -/
theorem tendsto_add_zero
    (f g : ℝ → ℝ)
    (hf : Tendsto f atTop (𝓝 0))
    (hg : Tendsto g atTop (𝓝 0)) :
    Tendsto (fun T => f T + g T) atTop (𝓝 0) := by
  simpa using hf.add hg

end Zeta23.GapMatching.VanishingBudgetByEnvelope2
