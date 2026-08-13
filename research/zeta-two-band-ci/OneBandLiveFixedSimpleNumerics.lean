/-
Exact live target arithmetic with the fixed coefficient 0.499.  The existing
unconditional half-simple theorem supplies this coefficient by taking its
epsilon equal to 0.001, so no diagonal error function is required.
-/
import Zeta23.GapMatching.OneBandPotentialSafeNumerics

noncomputable section

namespace Zeta23.GapMatching.OneBandLiveFixedSimpleNumerics

open Zeta23.GapMatching.OneBandPotentialSafeNumerics

def distinctLower : ℝ := 0.67250069
def simpleLower : ℝ := 0.499
def candidate : ℝ := 0.672500708

theorem candidate_lt_additive_bound :
    candidate < distinctLower + A * simpleLower - B := by
  norm_num [candidate, distinctLower, simpleLower,
    A, B, p, j, badLeft]

theorem additive_gain_pos : 0 < A * simpleLower - B := by
  norm_num [simpleLower, A, B, p, j, badLeft]

end Zeta23.GapMatching.OneBandLiveFixedSimpleNumerics
