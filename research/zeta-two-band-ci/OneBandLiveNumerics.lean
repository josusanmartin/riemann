/-
Exact arithmetic for the corrected live one-band strategy.

The path vertices are simple critical-line zeros.  Therefore the matching
bonus improves the distinct critical-line count by

  A * (simple density) - B,

rather than by the previously considered fixed-point term involving the
distinct density itself.
-/
import Zeta23.GapMatching.OneBandPotentialSafeNumerics

noncomputable section

namespace Zeta23.GapMatching.OneBandLiveNumerics

open Zeta23.GapMatching.OneBandPotentialSafeNumerics

/-- Safe fixed-lambda lower bound for the distinct critical-line density. -/
def distinctLower : ℝ := 0.67250069

/-- The corresponding safe simple-zero density obtained from the same window
constant: if `D = 2 - 1/c`, then `S = 2c - 1 = 2/(2-D)-1`. -/
def simpleLower : ℝ := 2 / (2 - distinctLower) - 1

/-- Exact live target. -/
def candidate : ℝ := 0.672500708

/-- The retuned one-band constants leave strict additive headroom above the
live target. -/
theorem candidate_lt_additive_bound :
    candidate < distinctLower + A * simpleLower - B := by
  norm_num [candidate, distinctLower, simpleLower,
    A, B, p, j, badLeft]

/-- The denominator used to derive the simple coefficient is positive. -/
theorem two_sub_distinctLower_pos : 0 < 2 - distinctLower := by
  norm_num [distinctLower]

/-- Algebraic conversion from a lower bound on `D = 2 - 1/c` to the
corresponding lower bound on `S = 2c - 1`. -/
theorem simpleLower_le_of_distinctLower_le
    {c : ℝ} (hc : 0 < c)
    (hD : distinctLower ≤ 2 - 1 / c) :
    simpleLower ≤ 2 * c - 1 := by
  have hden : 0 < 2 - distinctLower := two_sub_distinctLower_pos
  have hcInv : 1 / c ≤ 2 - distinctLower := by linarith
  have hcinvpos : 0 < 1 / c := one_div_pos.mpr hc
  have hcLower : 1 / (2 - distinctLower) ≤ c := by
    rw [one_div_le hc hden]
    nlinarith
  unfold simpleLower
  nlinarith

end Zeta23.GapMatching.OneBandLiveNumerics
