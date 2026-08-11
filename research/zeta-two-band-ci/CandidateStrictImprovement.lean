/-
Copyright (c) 2026.
SPDX-License-Identifier: Apache-2.0

A fully symbolic upper enclosure for the Montgomery--Taylor record constant.
No numerical oracle is used: the proof derives fifth- and sixth-order Taylor
bounds from Mathlib's cubic sine bound and the derivative test.
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Real.Pi.Bounds
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
  have hdiff : Differentiable ℝ f := by
    dsimp [f]
    fun_prop
  have hmono : MonotoneOn f (Set.Ici 0) :=
    monotoneOn_of_deriv_nonneg (convex_Ici 0)
      hdiff.continuous.continuousOn hdiff.differentiableOn
      (by
        intro t ht
        rw [interior_Ici] at ht
        rw [hderiv]
        nlinarith [Real.sin_ge_sub_cube ht.le])
  have h0 : f 0 ≤ f x := hmono (by simp) hx hx
  simpa [f] using h0

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
  have hdiff : Differentiable ℝ f := by
    dsimp [f]
    fun_prop
  have hmono : MonotoneOn f (Set.Ici 0) :=
    monotoneOn_of_deriv_nonneg (convex_Ici 0)
      hdiff.continuous.continuousOn hdiff.differentiableOn
      (by
        intro t ht
        rw [interior_Ici] at ht
        rw [hderiv]
        nlinarith [cos_le_quartic ht.le])
  have h0 : f 0 ≤ f x := hmono (by simp) hx hx
  simpa [f] using h0

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
  have hdiff : Differentiable ℝ f := by
    dsimp [f]
    fun_prop
  have hmono : MonotoneOn f (Set.Ici 0) :=
    monotoneOn_of_deriv_nonneg (convex_Ici 0)
      hdiff.continuous.continuousOn hdiff.differentiableOn
      (by
        intro t ht
        rw [interior_Ici] at ht
        rw [hderiv]
        nlinarith [sin_le_quintic ht.le])
  have h0 : f 0 ≤ f x := hmono (by simp) hx hx
  simpa [f] using h0

private def theta0 : ℝ := 1 / Real.sqrt 2

private theorem sqrt_two_pos : 0 < Real.sqrt 2 :=
  Real.sqrt_pos.2 (by norm_num)

private theorem sqrt_two_ne : Real.sqrt 2 ≠ 0 := ne_of_gt sqrt_two_pos

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

private theorem theta0_lt_pi : theta0 < Real.pi := by
  have hpi : (1 : ℝ) < Real.pi := by
    linarith [Real.pi_gt_three]
  exact theta0_lt_one.trans hpi

private theorem sqrt_mul_theta0 : Real.sqrt 2 * theta0 = 1 := by
  unfold theta0
  field_simp [sqrt_two_ne]

private theorem theta0_sq : theta0 ^ 2 = 1 / 2 := by
  unfold theta0
  field_simp [sqrt_two_ne]
  nlinarith [sqrt_two_sq]

private theorem theta0_four : theta0 ^ 4 = 1 / 4 := by
  calc
    theta0 ^ 4 = (theta0 ^ 2) ^ 2 := by ring
    _ = (1 / 2 : ℝ) ^ 2 := by rw [theta0_sq]
    _ = 1 / 4 := by norm_num

private theorem theta0_six : theta0 ^ 6 = 1 / 8 := by
  calc
    theta0 ^ 6 = (theta0 ^ 2) ^ 3 := by ring
    _ = (1 / 2 : ℝ) ^ 3 := by rw [theta0_sq]
    _ = 1 / 8 := by norm_num

private theorem theta0_div_sqrt_two :
    theta0 / Real.sqrt 2 = 1 / 2 := by
  unfold theta0
  field_simp [sqrt_two_ne]
  nlinarith [sqrt_two_sq]

private theorem half_sqrt_two_eq_theta0 :
    (1 / 2 : ℝ) * Real.sqrt 2 = theta0 := by
  unfold theta0
  apply (eq_div_iff sqrt_two_ne).2
  nlinarith [sqrt_two_sq]

private theorem scaled_sin_upper :
    Real.sqrt 2 * Real.sin theta0 ≤ 147 / 160 := by
  have hs := sin_le_quintic theta0_pos.le
  have hscale := mul_le_mul_of_nonneg_left hs (Real.sqrt_nonneg 2)
  calc
    Real.sqrt 2 * Real.sin theta0
        ≤ Real.sqrt 2 *
            (theta0 - theta0 ^ 3 / 6 + theta0 ^ 5 / 120) := hscale
    _ = (Real.sqrt 2 * theta0)
          * (1 - theta0 ^ 2 / 6 + theta0 ^ 4 / 120) := by ring
    _ = 147 / 160 := by
      rw [sqrt_mul_theta0, theta0_sq, theta0_four]
      norm_num

private theorem cos_lower :
    4379 / 5760 ≤ Real.cos theta0 := by
  have hc := cos_ge_sextic theta0_pos.le
  calc
    4379 / 5760
        = 1 - theta0 ^ 2 / 2 + theta0 ^ 4 / 24
            - theta0 ^ 6 / 720 := by
              rw [theta0_sq, theta0_four, theta0_six]
              norm_num
    _ ≤ Real.cos theta0 := hc

private theorem sin_theta0_pos : 0 < Real.sin theta0 :=
  Real.sin_pos_of_pos_of_lt_pi theta0_pos theta0_lt_pi

private theorem scaled_sin_pos :
    0 < Real.sqrt 2 * Real.sin theta0 :=
  mul_pos sqrt_two_pos sin_theta0_pos

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
  have hinv :
      (Zeta23.ThmD.cStar 1)⁻¹
        = 1 / 2
          + Real.cos theta0 /
              (Real.sqrt 2 * Real.sin theta0) := by
    change
      (Real.sqrt 2 * Real.sin theta0 /
          (Real.cos theta0 + theta0 * Real.sin theta0))⁻¹
        = 1 / 2
          + Real.cos theta0 /
              (Real.sqrt 2 * Real.sin theta0)
    rw [inv_div]
    rw [div_eq_iff (ne_of_gt scaled_sin_pos)]
    calc
      Real.cos theta0 + theta0 * Real.sin theta0
          = (1 / 2 : ℝ) * (Real.sqrt 2 * Real.sin theta0)
              + Real.cos theta0 := by
                rw [← mul_assoc, half_sqrt_two_eq_theta0]
                ring
      _ = (1 / 2
            + Real.cos theta0 /
                (Real.sqrt 2 * Real.sin theta0))
              * (Real.sqrt 2 * Real.sin theta0) := by
            rw [add_mul,
              div_mul_cancel₀ _ (ne_of_gt scaled_sin_pos)]
  unfold Zeta23.ThmD.HD
  rw [one_div, hinv]
  nlinarith [cosine_ratio_lower]

/-- The proposed rational score is strictly above the current exact record. -/
theorem HD_one_lt_6725391 :
    Zeta23.ThmD.HD 1 < (6725391 : ℝ) / 10000000 := by
  exact HD_one_le_rational.trans_lt (by norm_num)

end Zeta23.GapMatching.CandidateStrictImprovement
