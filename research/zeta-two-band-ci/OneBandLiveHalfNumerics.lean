/-
Exact target arithmetic using only the unconditional one-half simple-zero
bound.  This avoids any additional transcendental certification for the path
vertex density.
-/
import Zeta23.GapMatching.OneBandPotentialSafeNumerics

noncomputable section

namespace Zeta23.GapMatching.OneBandLiveHalfNumerics

open Zeta23.GapMatching.OneBandPotentialSafeNumerics

/-- Safe fixed-window lower bound for the pre-existing distinct on-line
certificate. -/
def distinctLower : ℝ := 0.67250069

/-- The unconditional simple critical-line theorem supplies one half. -/
def simpleLower : ℝ := 1 / 2

/-- Exact live leaderboard target. -/
def candidate : ℝ := 0.672500708

/-- After the retuning `p = 6.2e-6`, `j = 2.1e-6`, the path bonus from only
the one-half simple density already clears the live target. -/
theorem candidate_lt_additive_bound :
    candidate < distinctLower + A * simpleLower - B := by
  norm_num [candidate, distinctLower, simpleLower,
    A, B, p, j, badLeft]

/-- The additive gain is strictly positive. -/
theorem additive_gain_pos : 0 < A * simpleLower - B := by
  norm_num [simpleLower, A, B, p, j, badLeft]

end Zeta23.GapMatching.OneBandLiveHalfNumerics
