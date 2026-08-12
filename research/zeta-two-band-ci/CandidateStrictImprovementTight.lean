/-
Copyright (c) 2026.
SPDX-License-Identifier: Apache-2.0

A tight, entirely symbolic upper enclosure for the Montgomery--Taylor record.
Alternating Taylor bounds through sine degree nine and cosine degree ten give

  HD(1) <= 71744971 / 106683860
        = 0.6725007044177067...

which is strictly below the conservative candidate 0.672500708.
-/
import Zeta23.GapMatching.CandidateStrictImprovement

open Set Real

noncomputable section

namespace Zeta23.GapMatching.CandidateStrictImprovementTight

open Zeta23.GapMatching.CandidateStrictImprovement

/-- Seventh-order lower Taylor bound for sine on the nonnegative half-line. -/
theorem sin_ge_septic {x : ℝ} (hx : 0 ≤ x) :
    x - x ^ 3 / 6 + x ^ 5 / 120 - x ^ 7 / 5040 ≤ Real.sin x := by
  let f : ℝ → ℝ := fun t =>
    Real.sin t - (t - t ^ 3 / 6 + t ^ 5 / 120 - t ^ 7 / 5040)
  have hderiv : ∀ t : ℝ,
      deriv f t = Real.cos t -
        (1 - t ^ 2 / 2 + t ^ 4 / 24 - t ^ 6 / 720) := by
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
        nlinarith [cos_ge_sextic ht.le])
  have h0 : f 0 ≤ f x := hmono (by simp) hx hx
  simpa [f] using h0

/-- Eighth-order upper Taylor bound for cosine. -/
theorem cos_le_octic {x : ℝ} (hx : 0 ≤ x) :
    Real.cos x ≤
      1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720
        + x ^ 8 / 40320 := by
  let f : ℝ → ℝ := fun t =>
    1 - t ^ 2 / 2 + t ^ 4 / 24 - t ^ 6 / 720
      + t ^ 8 / 40320 - Real.cos t
  have hderiv : ∀ t : ℝ,
      deriv f t =
        -t + t ^ 3 / 6 - t ^ 5 / 120 + t ^ 7 / 5040
          + Real.sin t := by
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
        nlinarith [sin_ge_septic ht.le])
  have h0 : f 0 ≤ f x := hmono (by simp) hx hx
  simpa [f] using h0

/-- Ninth-order upper Taylor bound for sine. -/
theorem sin_le_nonic {x : ℝ} (hx : 0 ≤ x) :
    Real.sin x ≤
      x - x ^ 3 / 6 + x ^ 5 / 120 - x ^ 7 / 5040
        + x ^ 9 / 362880 := by
  let f : ℝ → ℝ := fun t =>
    t - t ^ 3 / 6 + t ^ 5 / 120 - t ^ 7 / 5040
      + t ^ 9 / 362880 - Real.sin t
  have hderiv : ∀ t : ℝ,
      deriv f t =
        1 - t ^ 2 / 2 + t ^ 4 / 24 - t ^ 6 / 720
          + t ^ 8 / 40320 - Real.cos t := by
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
        nlinarith [cos_le_octic ht.le])
  have h0 : f 0 ≤ f x := hmono (by simp) hx hx
  simpa [f] using h0

/-- Tenth-order lower Taylor bound for cosine. -/
theorem cos_ge_decic {x : ℝ} (hx : 0 ≤ x) :
    1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720
        + x ^ 8 / 40320 - x ^ 10 / 3628800
      ≤ Real.cos x := by
  let f : ℝ → ℝ := fun t =>
    Real.cos t -
      (1 - t ^ 2 / 2 + t ^ 4 / 24 - t ^ 6 / 720
        + t ^ 8 / 40320 - t ^ 10 / 3628800)
  have hderiv : ∀ t : ℝ,
      deriv f t =
        -Real.sin t + t - t ^ 3 / 6 + t ^ 5 / 120
          - t ^ 7 / 5040 + t ^ 9 / 362880 := by
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
        nlinarith [sin_le_nonic ht.le])
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

private theorem theta0_eight : theta0 ^ 8 = 1 / 16 := by
  calc
    theta0 ^ 8 = (theta0 ^ 2) ^ 4 := by ring
    _ = (1 / 2 : ℝ) ^ 4 := by rw [theta0_sq]
    _ = 1 / 16 := by norm_num

private theorem theta0_ten : theta0 ^ 10 = 1 / 32 := by
  calc
    theta0 ^ 10 = (theta0 ^ 2) ^ 5 := by ring
    _ = (1 / 2 : ℝ) ^ 5 := by rw [theta0_sq]
    _ = 1 / 32 := by norm_num

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

private theorem scaled_sin_upper_tight :
    Real.sqrt 2 * Real.sin theta0 ≤ 5334193 / 5806080 := by
  have hs := sin_le_nonic theta0_pos.le
  have hscale := mul_le_mul_of_nonneg_left hs (Real.sqrt_nonneg 2)
  calc
    Real.sqrt 2 * Real.sin theta0
        ≤ Real.sqrt 2 *
          (theta0 - theta0 ^ 3 / 6 + theta0 ^ 5 / 120
            - theta0 ^ 7 / 5040 + theta0 ^ 9 / 362880) := hscale
    _ = (Real.sqrt 2 * theta0) *
          (1 - theta0 ^ 2 / 6 + theta0 ^ 4 / 120
            - theta0 ^ 6 / 5040 + theta0 ^ 8 / 362880) := by
          ring
    _ = 5334193 / 5806080 := by
          rw [sqrt_mul_theta0, theta0_sq, theta0_four,
            theta0_six, theta0_eight]
          norm_num

private theorem cos_lower_tight :
    88280819 / 116121600 ≤ Real.cos theta0 := by
  have hc := cos_ge_decic theta0_pos.le
  calc
    88280819 / 116121600
        = 1 - theta0 ^ 2 / 2 + theta0 ^ 4 / 24
            - theta0 ^ 6 / 720 + theta0 ^ 8 / 40320
            - theta0 ^ 10 / 3628800 := by
          rw [theta0_sq, theta0_four, theta0_six,
            theta0_eight, theta0_ten]
          norm_num
    _ ≤ Real.cos theta0 := hc

private theorem sin_theta0_pos : 0 < Real.sin theta0 :=
  Real.sin_pos_of_pos_of_lt_pi theta0_pos theta0_lt_pi

private theorem scaled_sin_pos :
    0 < Real.sqrt 2 * Real.sin theta0 :=
  mul_pos sqrt_two_pos sin_theta0_pos

private theorem cosine_ratio_lower_tight :
    88280819 / 106683860 ≤
      Real.cos theta0 / (Real.sqrt 2 * Real.sin theta0) := by
  rw [le_div_iff₀ scaled_sin_pos]
  calc
    (88280819 / 106683860) *
        (Real.sqrt 2 * Real.sin theta0)
      ≤ (88280819 / 106683860) *
          (5334193 / 5806080) := by
        exact mul_le_mul_of_nonneg_left scaled_sin_upper_tight
          (by norm_num)
    _ = 88280819 / 116121600 := by norm_num
    _ ≤ Real.cos theta0 := cos_lower_tight

/-- Exact tight rational upper enclosure for the current record. -/
theorem HD_one_le_tight :
    Zeta23.ThmD.HD 1 ≤ 71744971 / 106683860 := by
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
          = (1 / 2 : ℝ) *
              (Real.sqrt 2 * Real.sin theta0)
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
  nlinarith [cosine_ratio_lower_tight]

/-- The conservative score is strictly above the exact current record. -/
theorem HD_one_lt_672500708 :
    Zeta23.ThmD.HD 1 < (672500708 : ℝ) / 1000000000 := by
  exact HD_one_le_tight.trans_lt (by norm_num)

end Zeta23.GapMatching.CandidateStrictImprovementTight
