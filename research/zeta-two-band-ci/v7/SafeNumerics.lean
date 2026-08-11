/-
Copyright (c) 2026.
SPDX-License-Identifier: Apache-2.0

Exact rational post-processing for a guarded gap-matching refinement of the
Montgomery--Taylor window at lambda = 0.999999.

The four transcendental profile inequalities and the baseline inequality
`HD(0.999999) > deltaLower` are checked by the companion interval certificate.
This file formalizes every numerical step after those five enclosures.
-/
import Mathlib

noncomputable section

namespace Zeta23.GapMatching.SafeNumerics

/-- Fixed Montgomery--Taylor bandwidth parameter. -/
def lam : ℝ := 0.999999

/-- The four gap cutoffs. -/
def a : ℝ := 1.02340
def b : ℝ := 1.03338
def c : ℝ := 1.48331
def d : ℝ := 1.99351

/-- Safe outward-rounded squared-overlap lower bounds. -/
def ga : ℝ := 0.00095015
def gb : ℝ := 0.00046305
def gh : ℝ := 0.00024450
def gj : ℝ := 0.00022815

/-- Rectangle multiplier and fixed-point span. -/
def beta : ℝ := gj / (d - b)
def span : ℝ := d + b

/-- Safe lower bound for `HD 0.999999` and the advertised improvement. -/
def deltaLower : ℝ := 0.67250001
def advertised : ℝ := 0.6725084

/-- Exact positivity margins used in the four-rectangle elimination. -/
theorem rectangle_margins :
    (0.000002 : ℝ) < ga - 2 * beta * d ∧
    (0.000002 : ℝ) < gb - 2 * beta * (d - a) ∧
    (0.000002 : ℝ) < gh - 2 * beta * (d - c) ∧
    0 < 1 - beta * span := by
  norm_num [a, b, c, d, ga, gb, gh, gj, beta, span]

/-- The exact rational fixed-point coefficient is strictly above the displayed
`0.6725084`. -/
theorem advertised_lt_exact :
    advertised < (deltaLower - 2 * beta) / (1 - beta * span) := by
  have hden : 0 < 1 - beta * span := rectangle_margins.2.2.2
  rw [lt_div_iff₀ hden]
  norm_num [advertised, deltaLower, beta, span, gj, d, b]

/-- Fixed-point rearrangement in the exact form consumed by the asymptotic
zeta seam.  The normalized total gap length is bounded by `N + o(N)`, hence
the coefficient multiplying `N` here is one. -/
theorem fixed_point_improves
    {sigma : ℝ}
    (h : deltaLower + beta * (span * sigma - 2) ≤ sigma) :
    advertised < sigma := by
  have hden : 0 < 1 - beta * span := rectangle_margins.2.2.2
  have hrearrange :
      (deltaLower - 2 * beta) / (1 - beta * span) ≤ sigma := by
    rw [div_le_iff₀ hden]
    nlinarith
  exact advertised_lt_exact.trans_le hrearrange

/-- Literal decimal wrapper. -/
theorem fixed_point_decimal
    {sigma : ℝ}
    (h : (0.67250001 : ℝ)
      + (0.00022815 / (1.99351 - 1.03338))
          * ((1.99351 + 1.03338) * sigma - 2) ≤ sigma) :
    (0.6725084 : ℝ) < sigma := by
  simpa [deltaLower, beta, span, gj, d, b] using fixed_point_improves h

end Zeta23.GapMatching.SafeNumerics
