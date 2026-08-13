/-
A fixed finite endpoint loss is little-o of any nonnegative count tending to
infinity.
-/
import Mathlib

open Filter Asymptotics Topology

noncomputable section

namespace Zeta23.GapMatching.ConstantOverCount

/-- Constant functions are little-o of a nonnegative function tending to
`+∞`. -/
theorem const_isLittleO_of_tendsto_atTop
    (c : ℝ) (N : ℝ → ℝ)
    (hN0 : ∀ᶠ T in atTop, 0 ≤ N T)
    (hNtop : Tendsto N atTop atTop) :
    (fun _ : ℝ => c) =o[atTop] N := by
  exact?

end Zeta23.GapMatching.ConstantOverCount
