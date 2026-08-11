/-
Copyright (c) 2026.
SPDX-License-Identifier: Apache-2.0

A fully symbolic upper enclosure for the Montgomery--Taylor record constant.
No numerical oracle is used: the proof derives fifth- and sixth-order Taylor
bounds from Mathlib's cubic sine bound and the derivative test.
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Zeta23.ThmD.Functional

open Set Real

noncomputable section

namespace Zeta23.GapMatching.CandidateStrictImprovement

/-- `cos x` lies below its alternating quartic Taylor truncation for `x ≥ 0`. -/
theorem cos_le_quartic {x : ℝ} (hx : 0 ≤ x) :
    Real.cos x ≤ 1 - x ^ 2 / 2 + x ^ 4 / 24 := by
  let f : ℝ → ℝ := fun t => 1 - t ^ 2 / 2 + t ^ 4 / 24 - Real.cos t
  have hderiv : ∀ t : ℝ,
      deriv f t = -t + t ^ 3 / 6 + Real.sin t := by
    intro t
    simp (disch := fun_prop) [f]
    ring
  have hmono : MonotoneOn f (Set.Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0) (by fun_prop)
    intro t ht
    rw [interior_Ici] at ht
    rw [hderiv]
    nlinarith [Real.sin_ge_sub_cube ht.le]
  have h := hmono (by simp) hx
  simpa [f] using h

/-- Fifth-order upper Taylor bound for sine on the nonnegative half-line. -/
theorem sin_le_quintic {x : ℝ} (hx : 0 ≤ x) :
    Real.sin x ≤ x - x ^ 3 / 6 + x ^ 5 / 120 := by
  let f : ℝ → ℝ := fun t =>
    t - t ^ 3 / 6 + t ^ 5 / 120 - Real.sin t
  have hderiv : ∀ t : ℝ,
      deriv f t = 1 - t ^ 2 / 2 + t ^ 4 / 24 - Real.cos t := by
    intro t
    simp (disch := fun_prop) [f]
    ring
  have hmono : MonotoneOn f (Set.Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0) (by fun_prop)
    intro t ht
    rw [interior_Ici] at ht
    rw [hderiv]
    exact cos_le_quartic ht.le
  have h := hmono (by simp) hx
  simpa [f] using h

/-- Sixth-order lower Taylor bound for cosine on the nonnegative half-line. -/
theorem cos_ge_sextic {x : ℝ} (hx : 0 ≤ x) :
    1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720 ≤ Real.cos x := by
  let f : ℝ → ℝ := fun t =>
    Real.cos t - (1 - t ^ 2 / 2 + t ^ 4 / 24 - t ^ 6 / 720)
  have hderiv : ∀ t : ℝ,
      deriv f t = -Real.sin t + t - t ^ 3 / 6 + t ^ 5 / 120 := by
    intro t
    simp (disch := fun_prop) [f]
    ring
  have hmono : MonotoneOn f (Set.Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0) (by fun_prop)
    intro t ht
    rw [interior_Ici] at ht
    rw [hderiv]
    nlinarith [sin_le_quintic ht.le]
  have h := hmono (by simp) hx
  simpa [f] using h

private def theta0 : ℝ := 1 / Real.sqrt 2

private theorem sqrt_two_pos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)

private theorem sqrt_two_sq : Real.sqrt 2 ^ 2 = 2 :=
  Real.sq_sqrt (by norm_num)

private theorem theta0_pos : 0 < theta0 := by
  unfold theta0
  positivity

private theorem theta0_lt_one : theta0 < 1 := by
  have hs : 1 < Real.sqrt 2 := by
    nlinarith [sqrt_two_sq, Real.sqrt_nonneg 2]
  rw [theta0, div_lt_one sqrt_two_pos]
  exact hs

private theorem theta0_lt_pi : theta0 < Real.pi :=
  theta0_lt_one.trans Real.one_lt_pi

private theorem sqrt_mul_theta0 : Real.sqrt 2 * theta0 = 1 := by
  unfold theta0
  field_simp [ne_of_gt sqrt_two_pos]

private theorem theta0_sq : theta0 ^ 2 = 1 / 2 := by
  unfold theta0
  field_simp [ne_of_gt sqrt_two_pos]
  nlinarith [sqrt_two_sq]

private theorem scaled_sin_upper :
    Real.sqrt 2 * Real.sin theta0 ≤ 147 / 160 := by
  have hs := sin_le_quintic theta0_pos.le
  have hscale := mul_le_mul_of_nonneg_left hs (Real.sqrt_nonneg 2)
  calc
    Real.sqrt 2 * Real.sin theta0
        ≤ Real.sqrt 2 *
            (theta0 - theta0 ^ 3 / 6 + theta0 ^ 5 / 120) := hscale
    _ = 147 / 160 := by
      have hsq := theta0_sq
      have hmul := sqrt_mul_theta0
      nlinarith [sq_nonneg theta0]

private theorem cos_lower :
    4379 / 5760 ≤ Real.cos theta0 := by
  have hc := cos_ge_sextic theta0_pos.le
  calc
    4379 / 5760
        = 1 - theta0 ^ 2 / 2 + theta0 ^ 4 / 24
            - theta0 ^ 6 / 720 := by
              have hsq := theta0_sq
              nlinarith [sq_nonneg (theta0 ^ 2)]
    _ ≤ Real.cos theta0 := hc

private theorem scaled_sin_pos :
    0 < Real.sqrt 2 * Real.sin theta0 := by
  have hsin : 0 < Real.sin theta0 :=
    Real.sin_pos_of_pos_of_lt_pi theta0_pos theta0_lt_pi
  exact mul_pos sqrt_two_pos hsin

private theorem cosine_ratio_lower :
    4379 / 5292 ≤
      Real.cos theta0 / (Real.sqrt 2 * Real.sin theta0) := by
  rw [le_div_iff₀ scaled_sin_pos]
  calc
    (4379 / 5292) * (Real.sqrt 2 * Real.sin theta0)
        ≤ (4379 / 5292) * (147 / 160) := by
          exact mul_le_mul_of_nonneg_left scaled_sin_upper (by norm_num)
    _ = 4379 / 5760 := by norm_num
    _ ≤ Real.cos theta0 := cos_lower

/-- Exact rational upper enclosure for the baseline density. -/
theorem HD_one_le_rational :
    Zeta23.ThmD.HD 1 ≤ 3559 / 5292 := by
  have hsine_ne : Real.sqrt 2 * Real.sin theta0 ≠ 0 :=
    ne_of_gt scaled_sin_pos
  have hinv :
      (Zeta23.ThmD.cStar 1)⁻¹
        = 1 / 2
          + Real.cos theta0 /
              (Real.sqrt 2 * Real.sin theta0) := by
    unfold Zeta23.ThmD.cStar Zeta23.ThmD.theta theta0
    rw [inv_div]
    field_simp [hsine_ne, ne_of_gt sqrt_two_pos]
    ring
  rw [Zeta23.ThmD.HD, hinv]
  nlinarith [cosine_ratio_lower]

/-- The proposed rational score is strictly above the current exact record. -/
theorem HD_one_lt_6725391 :
    Zeta23.ThmD.HD 1 < (6725391 : ℝ) / 10000000 := by
  exact HD_one_le_rational.trans_lt (by norm_num)

end Zeta23.GapMatching.CandidateStrictImprovement
