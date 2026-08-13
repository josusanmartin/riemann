/-
A scalar error budget tending to zero is eventually below every positive
profile tolerance.
-/
import Mathlib

open Filter Topology

noncomputable section

namespace Zeta23.GapMatching.VanishingOverlapBudget

/-- Eventual comparison with a fixed positive tolerance. -/
theorem eventually_le_of_tendsto_zero
    (error : ℝ → ℝ) {tol : ℝ}
    (htol : 0 < tol)
    (herr : Tendsto error atTop (𝓝 0)) :
    ∀ᶠ T in atTop, error T ≤ tol := by
  have hmem : Set.Iio tol ∈ 𝓝 (0 : ℝ) :=
    Set.Iio_mem_nhds htol
  filter_upwards [herr.eventually hmem] with T hT
  exact hT.le

end Zeta23.GapMatching.VanishingOverlapBudget
