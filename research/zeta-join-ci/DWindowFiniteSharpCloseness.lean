/-
The elementary triangle bridge between a finite Gram overlap, its exact full
Poisson overlap, and the sharp Montgomery--Taylor profile.
-/
import Mathlib

noncomputable section

namespace Zeta23.GapMatching.DWindowFiniteSharpCloseness

/-- Finite/full and full/sharp errors add. -/
theorem abs_finite_sub_sharp_le
    {finite full sharp tailError rampError : ℝ}
    (hfinite : |finite - full| ≤ tailError)
    (hramp : |full - sharp| ≤ rampError) :
    |finite - sharp| ≤ tailError + rampError := by
  calc
    |finite - sharp|
        = |(finite - full) + (full - sharp)| := by ring_nf
    _ ≤ |finite - full| + |full - sharp| := abs_add_le _ _
    _ ≤ tailError + rampError := add_le_add hfinite hramp

/-- Symmetric specialization with one advertised error budget. -/
theorem abs_finite_sub_sharp_le_of_sum
    {finite full sharp tailError rampError eps : ℝ}
    (hfinite : |finite - full| ≤ tailError)
    (hramp : |full - sharp| ≤ rampError)
    (hsum : tailError + rampError ≤ eps) :
    |finite - sharp| ≤ eps :=
  (abs_finite_sub_sharp_le hfinite hramp).trans hsum

end Zeta23.GapMatching.DWindowFiniteSharpCloseness
