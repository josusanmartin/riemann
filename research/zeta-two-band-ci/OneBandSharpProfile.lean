/-
Copyright (c) 2026.
SPDX-License-Identifier: Apache-2.0

Coarse, entirely symbolic lower bounds for the sharp Montgomery--Taylor
Fourier profile.  The bounds are intentionally much weaker than the true
values; their large slack makes the final finite-grid argument robust.
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Real.Pi.Bounds
import Zeta23.GapMatching.CandidateStrictImprovement
import Zeta23.GapMatching.DWindowProfileAlgebra
import Zeta23.GapMatching.OneBandPotentialSafeNumerics

open Set Real

noncomputable section

namespace Zeta23.GapMatching.OneBandSharpProfile

open Zeta23
open Zeta23.ThmD
open Zeta23.GapMatching.CandidateStrictImprovement
open Zeta23.GapMatching.DWindowProfileAlgebra
open Zeta23.GapMatching.OneBandPotentialSafeNumerics

/-- The scale-free sharp profile. -/
def profile (x : ℝ) : ℝ :=
  sharpOverlap lam 1 (2 * Real.pi * x)

private def alpha : ℝ := Real.sqrt 2 * lam
private def theta : ℝ := alpha / 2
private def beta (x : ℝ) : ℝ := 2 * Real.pi * x
private def numer (x : ℝ) : ℝ :=
  alpha * Real.sin theta * Real.cos (Real.pi * x)
    - beta x * Real.cos theta * Real.sin (Real.pi * x)

private theorem lam_pos : 0 < lam := by norm_num [lam]
private theorem lam_nonneg : 0 ≤ lam := lam_pos.le
private theorem lam_le_one : lam ≤ 1 := by norm_num [lam]

private theorem sqrt_two_sq : Real.sqrt 2 ^ 2 = 2 :=
  Real.sq_sqrt (by norm_num)

private theorem sqrt_two_pos : 0 < Real.sqrt 2 := by positivity

private theorem alpha_pos : 0 < alpha := by
  unfold alpha
  positivity

private theorem alpha_lower : (7 / 5 : ℝ) ≤ alpha := by
  have hsqrt : (7071 / 5000 : ℝ) ≤ Real.sqrt 2 := by
    nlinarith [sqrt_two_sq, Real.sqrt_nonneg 2]
  unfold alpha lam
  nlinarith

private theorem alpha_upper : alpha ≤ (14143 / 10000 : ℝ) := by
  have hsqrt : Real.sqrt 2 ≤ (14143 / 10000 : ℝ) := by
    nlinarith [sqrt_two_sq, Real.sqrt_nonneg 2]
  unfold alpha
  have hlam0 : 0 ≤ lam := lam_nonneg
  have hlam1 : lam ≤ 1 := lam_le_one
  nlinarith [mul_le_mul_of_nonneg_left hlam1 (Real.sqrt_nonneg 2)]

private theorem alpha_lt_two : alpha < 2 := by
  linarith [alpha_upper]

private theorem theta_eq : theta = Zeta23.ThmD.theta lam := by
  unfold theta alpha Zeta23.ThmD.theta
  have hsne : Real.sqrt 2 ≠ 0 := ne_of_gt sqrt_two_pos
  field_simp [hsne]
  nlinarith [sqrt_two_sq]

private theorem theta_nonneg : 0 ≤ theta := by
  unfold theta
  positivity

private theorem theta_lower : (7 / 10 : ℝ) ≤ theta := by
  unfold theta
  linarith [alpha_lower]

private theorem theta_upper : theta ≤ (14143 / 20000 : ℝ) := by
  unfold theta
  linarith [alpha_upper]

private theorem theta_sq_le_half : theta ^ 2 ≤ (1 / 2 : ℝ) := by
  rw [theta_eq]
  exact Zeta23.ThmD.theta_sq_le lam_nonneg lam_le_one

private theorem sin_theta_pos : 0 < Real.sin theta := by
  rw [theta_eq]
  exact Zeta23.ThmD.sin_theta_pos lam_pos lam_le_one

private theorem sin_theta_lower : (3 / 5 : ℝ) ≤ Real.sin theta := by
  have hs := Real.sin_ge_sub_cube theta_nonneg
  have hcube : theta ^ 3 ≤ (14143 / 20000 : ℝ) ^ 3 :=
    pow_le_pow_left₀ theta_nonneg theta_upper 3
  nlinarith [theta_lower]

private theorem sin_theta_upper : Real.sin theta ≤ (3 / 4 : ℝ) := by
  exact (Real.sin_le theta_nonneg).trans (theta_upper.trans (by norm_num))

private theorem cos_theta_nonneg : 0 ≤ Real.cos theta := by
  rw [theta_eq]
  exact (Zeta23.ThmD.cos_theta_pos lam_nonneg lam_le_one).le

private theorem cos_theta_lower : (19 / 25 : ℝ) ≤ Real.cos theta := by
  have hc := cos_ge_sextic theta_nonneg
  set y : ℝ := theta ^ 2 with hy
  have hy0 : 0 ≤ y := by simp only [hy]; positivity
  have hy1 : y ≤ 1 / 2 := by simpa only [hy] using theta_sq_le_half
  have hquad : 0 ≤ 4 * y ^ 2 - 118 * y + 1381 := by
    nlinarith [sq_nonneg y]
  have hpoly :
      (4379 / 5760 : ℝ)
        ≤ 1 - y / 2 + y ^ 2 / 24 - y ^ 3 / 720 := by
    have hid :
        (1 - y / 2 + y ^ 2 / 24 - y ^ 3 / 720)
            - 4379 / 5760
          = (1 - 2 * y) * (4 * y ^ 2 - 118 * y + 1381) / 5760 := by
      ring
    rw [← sub_nonneg, hid]
    positivity
  have hrewrite :
      theta ^ 4 = y ^ 2 ∧ theta ^ 6 = y ^ 3 := by
    constructor <;> simp only [hy] <;> ring
  rcases hrewrite with ⟨h4, h6⟩
  rw [h4, h6] at hc
  exact (by norm_num : (19 / 25 : ℝ) ≤ 4379 / 5760).trans
    (hpoly.trans hc)

private theorem cos_theta_le_one : Real.cos theta ≤ 1 :=
  Real.cos_le_one theta

private theorem pi_lower : (6283 / 2000 : ℝ) ≤ Real.pi := by
  have h := Real.pi_gt_d20
  norm_num at h ⊢
  linarith

private theorem pi_upper : Real.pi ≤ (22 / 7 : ℝ) := by
  exact Real.pi_le_22_div_7

private theorem beta_pos {x : ℝ} (hx : 0 < x) : 0 < beta x := by
  unfold beta
  positivity

private theorem beta_gt_alpha {x : ℝ} (hx : 1 ≤ x) : alpha < beta x := by
  have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
  unfold beta
  nlinarith [alpha_lt_two]

private theorem denom_pos {x : ℝ} (hx : 1 ≤ x) :
    0 < Real.sin theta * (beta x ^ 2 - alpha ^ 2) := by
  have hb := beta_gt_alpha hx
  have hb0 := beta_pos (lt_of_lt_of_le zero_lt_one hx)
  have ha0 := alpha_pos
  have hsq : alpha ^ 2 < beta x ^ 2 :=
    pow_lt_pow_left₀ hb ha0.le (by norm_num)
  exact mul_pos sin_theta_pos (sub_pos.mpr hsq)

private theorem integral_product_closed {x : ℝ} (hx : 1 ≤ x) :
    (∫ s in (-(1 : ℝ) / 2)..(1 / 2),
      vStar lam s * Real.cos (beta x * s))
      = Real.sin ((alpha - beta x) / 2) / (alpha - beta x)
          + Real.sin ((alpha + beta x) / 2) / (alpha + beta x) := by
  have hminus : alpha - beta x ≠ 0 := by
    linarith [beta_gt_alpha hx]
  have hplus : alpha + beta x ≠ 0 := by
    have := beta_pos (lt_of_lt_of_le zero_lt_one hx)
    linarith [alpha_pos]
  let F : ℝ → ℝ := fun s =>
    Real.sin ((alpha - beta x) * s) / (2 * (alpha - beta x))
      + Real.sin ((alpha + beta x) * s) / (2 * (alpha + beta x))
  have hF : ∀ s : ℝ,
      HasDerivAt F
        (vStar lam s * Real.cos (beta x * s)) s := by
    intro s
    have hlin1 : HasDerivAt (fun y : ℝ => (alpha - beta x) * y)
        (alpha - beta x) s := (hasDerivAt_id s).const_mul _
    have hlin2 : HasDerivAt (fun y : ℝ => (alpha + beta x) * y)
        (alpha + beta x) s := (hasDerivAt_id s).const_mul _
    have h1 := ((Real.hasDerivAt_sin _).comp s hlin1).div_const
      (2 * (alpha - beta x))
    have h2 := ((Real.hasDerivAt_sin _).comp s hlin2).div_const
      (2 * (alpha + beta x))
    have hsum := h1.add h2
    refine hsum.congr_deriv ?_
    unfold F vStar alpha
    have hprod :
        Real.cos (Real.sqrt 2 * lam * s) * Real.cos (beta x * s)
          = (Real.cos ((alpha - beta x) * s)
              + Real.cos ((alpha + beta x) * s)) / 2 := by
      rw [Real.cos_sub, Real.cos_add]
      ring
    rw [hprod]
    field_simp [hminus, hplus]
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s _ => hF s)
    (Continuous.intervalIntegrable (by unfold vStar; fun_prop) _ _)]
  unfold F
  rw [show (alpha - beta x) * (-(1 : ℝ) / 2)
      = -((alpha - beta x) / 2) by ring,
    show (alpha + beta x) * (-(1 : ℝ) / 2)
      = -((alpha + beta x) / 2) by ring,
    Real.sin_neg]
  field_simp [hminus, hplus]
  ring

private theorem profile_eq_ratio {x : ℝ} (hx : 1 ≤ x) :
    profile x =
      alpha * numer x /
        (Real.sin theta * (alpha ^ 2 - beta x ^ 2)) := by
  unfold profile sharpOverlap
  rw [show (1 : ℝ) / 2 = 1 / 2 by rfl]
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (-(1 : ℝ) / 2) ≤ 1 / 2)]
  change
    (∫ s in (-(1 : ℝ) / 2)..(1 / 2),
      vStar lam s * Real.cos (beta x * s)) / (aStar lam * 1)
      = _
  rw [integral_product_closed hx, aStar_eq lam_pos]
  have hminus : alpha - beta x ≠ 0 := by linarith [beta_gt_alpha hx]
  have hplus : alpha + beta x ≠ 0 := by
    have := beta_pos (lt_of_lt_of_le zero_lt_one hx)
    linarith [alpha_pos]
  have htheta : alpha / 2 = theta := rfl
  have hbeta : beta x / 2 = Real.pi * x := by
    unfold beta
    ring
  rw [show (alpha - beta x) / 2 = theta - Real.pi * x by
      rw [← htheta, ← hbeta]; ring,
    show (alpha + beta x) / 2 = theta + Real.pi * x by
      rw [← htheta, ← hbeta]; ring,
    Real.sin_sub, Real.sin_add]
  unfold numer
  have hs2ne : Real.sqrt 2 ≠ 0 := ne_of_gt sqrt_two_pos
  have hsinne : Real.sin theta ≠ 0 := ne_of_gt sin_theta_pos
  have hane : alpha ≠ 0 := ne_of_gt alpha_pos
  field_simp [hminus, hplus, hs2ne, hsinne, hane]
  unfold alpha theta
  nlinarith [sqrt_two_sq]

private theorem profile_eq_positive_ratio {x : ℝ} (hx : 1 ≤ x) :
    profile x =
      alpha * (-numer x) /
        (Real.sin theta * (beta x ^ 2 - alpha ^ 2)) := by
  rw [profile_eq_ratio hx]
  ring

private theorem neg_profile_eq_positive_ratio {x : ℝ} (hx : 1 ≤ x) :
    -profile x =
      alpha * numer x /
        (Real.sin theta * (beta x ^ 2 - alpha ^ 2)) := by
  rw [profile_eq_ratio hx]
  ring

private theorem ratio_lower
    {x m betaMax : ℝ} (hx : 1 ≤ x)
    (hm : m ≤ -numer x)
    (hm0 : 0 ≤ m)
    (hbeta : beta x ≤ betaMax)
    (hbetaMax0 : 0 ≤ betaMax)
    (harith : (1 / 300 : ℝ) * betaMax ^ 2
      ≤ (7 / 5 : ℝ) * m) :
    (1 / 300 : ℝ) ≤ profile x := by
  rw [profile_eq_positive_ratio hx]
  have hden := denom_pos hx
  rw [le_div_iff₀ hden]
  have hsin : Real.sin theta ≤ 1 := Real.sin_le_one theta
  have hbeta0 : 0 ≤ beta x := (beta_pos (lt_of_lt_of_le zero_lt_one hx)).le
  have hsqBeta : beta x ^ 2 ≤ betaMax ^ 2 :=
    pow_le_pow_left₀ hbeta0 hbeta 2
  have hdenUpper :
      Real.sin theta * (beta x ^ 2 - alpha ^ 2)
        ≤ betaMax ^ 2 := by
    have hdiff0 : 0 ≤ beta x ^ 2 - alpha ^ 2 :=
      (sub_nonneg.mpr (le_of_lt (pow_lt_pow_left₀
        (beta_gt_alpha hx) alpha_pos.le (by norm_num))))
    calc
      Real.sin theta * (beta x ^ 2 - alpha ^ 2)
          ≤ 1 * (beta x ^ 2 - alpha ^ 2) :=
        mul_le_mul_of_nonneg_right hsin hdiff0
      _ ≤ beta x ^ 2 := by nlinarith [sq_nonneg alpha]
      _ ≤ betaMax ^ 2 := hsqBeta
  calc
    (1 / 300 : ℝ) *
        (Real.sin theta * (beta x ^ 2 - alpha ^ 2))
        ≤ (1 / 300 : ℝ) * betaMax ^ 2 :=
      mul_le_mul_of_nonneg_left hdenUpper (by norm_num)
    _ ≤ (7 / 5 : ℝ) * m := harith
    _ ≤ alpha * (-numer x) :=
      mul_le_mul alpha_lower hm hm0 (by positivity)

private theorem neg_ratio_lower
    {x m betaMax : ℝ} (hx : 1 ≤ x)
    (hm : m ≤ numer x)
    (hm0 : 0 ≤ m)
    (hbeta : beta x ≤ betaMax)
    (hbetaMax0 : 0 ≤ betaMax)
    (harith : (1 / 300 : ℝ) * betaMax ^ 2
      ≤ (7 / 5 : ℝ) * m) :
    (1 / 300 : ℝ) ≤ -profile x := by
  rw [neg_profile_eq_positive_ratio hx]
  have hden := denom_pos hx
  rw [le_div_iff₀ hden]
  have hsin : Real.sin theta ≤ 1 := Real.sin_le_one theta
  have hbeta0 : 0 ≤ beta x := (beta_pos (lt_of_lt_of_le zero_lt_one hx)).le
  have hsqBeta : beta x ^ 2 ≤ betaMax ^ 2 :=
    pow_le_pow_left₀ hbeta0 hbeta 2
  have hdenUpper :
      Real.sin theta * (beta x ^ 2 - alpha ^ 2)
        ≤ betaMax ^ 2 := by
    have hdiff0 : 0 ≤ beta x ^ 2 - alpha ^ 2 :=
      (sub_nonneg.mpr (le_of_lt (pow_lt_pow_left₀
        (beta_gt_alpha hx) alpha_pos.le (by norm_num))))
    calc
      Real.sin theta * (beta x ^ 2 - alpha ^ 2)
          ≤ 1 * (beta x ^ 2 - alpha ^ 2) :=
        mul_le_mul_of_nonneg_right hsin hdiff0
      _ ≤ beta x ^ 2 := by nlinarith [sq_nonneg alpha]
      _ ≤ betaMax ^ 2 := hsqBeta
  calc
    (1 / 300 : ℝ) *
        (Real.sin theta * (beta x ^ 2 - alpha ^ 2))
        ≤ (1 / 300 : ℝ) * betaMax ^ 2 :=
      mul_le_mul_of_nonneg_left hdenUpper (by norm_num)
    _ ≤ (7 / 5 : ℝ) * m := harith
    _ ≤ alpha * numer x :=
      mul_le_mul alpha_lower hm hm0 (by positivity)

private theorem trig_shift_one (t : ℝ) :
    Real.cos (Real.pi * (1 + t)) = -Real.cos (Real.pi * t) ∧
    Real.sin (Real.pi * (1 + t)) = -Real.sin (Real.pi * t) := by
  constructor
  · rw [mul_add, mul_one, Real.cos_add, Real.cos_pi, Real.sin_pi]
    ring
  · rw [mul_add, mul_one, Real.sin_add, Real.cos_pi, Real.sin_pi]
    ring

private theorem trig_shift_two (t : ℝ) :
    Real.cos (Real.pi * (2 + t)) = Real.cos (Real.pi * t) ∧
    Real.sin (Real.pi * (2 + t)) = Real.sin (Real.pi * t) := by
  constructor
  · rw [mul_add, show Real.pi * 2 = Real.pi + Real.pi by ring,
      Real.cos_add, Real.cos_add, Real.cos_pi, Real.sin_pi]
    ring
  · rw [mul_add, show Real.pi * 2 = Real.pi + Real.pi by ring,
      Real.sin_add, Real.cos_add, Real.cos_pi, Real.sin_pi]
    ring

private theorem left_numer_bound {x : ℝ}
    (hx1 : 1 ≤ x) (hx2 : x ≤ badLeft) :
    (125007 / 627200 : ℝ) ≤ -numer x := by
  set t := x - 1 with ht
  have ht0 : 0 ≤ t := by linarith
  have ht1 : t ≤ 1 / 32 := by
    unfold badLeft at hx2
    linarith
  have hz0 : 0 ≤ Real.pi * t := mul_nonneg Real.pi_pos.le ht0
  have hzUpper : Real.pi * t ≤ (22 / 7 : ℝ) * (1 / 32) := by
    exact mul_le_mul pi_upper ht1 ht0 (by norm_num)
  have hcos := Real.one_sub_sq_div_two_le_cos (x := Real.pi * t)
  have hsin := Real.sin_le hz0
  have hbeta : beta x ≤ 2 * (22 / 7 : ℝ) * (33 / 32) := by
    unfold beta badLeft
    exact mul_le_mul (mul_le_mul_of_nonneg_left pi_upper (by norm_num)) hx2
      (by positivity) (by positivity)
  have htrig := trig_shift_one t
  have hx : x = 1 + t := by simp only [ht]; ring
  rw [hx, htrig.1, htrig.2]
  unfold numer
  have hs0 := sin_theta_lower
  have hc1 := cos_theta_le_one
  have haL := alpha_lower
  have hcost :
      1 - ((22 / 7 : ℝ) * (1 / 32)) ^ 2 / 2
        ≤ Real.cos (Real.pi * t) := by
    calc
      1 - ((22 / 7 : ℝ) * (1 / 32)) ^ 2 / 2
          ≤ 1 - (Real.pi * t) ^ 2 / 2 := by
        nlinarith [pow_le_pow_left₀ hz0 hzUpper 2]
      _ ≤ Real.cos (Real.pi * t) := hcos
  have hsint : Real.sin (Real.pi * t)
      ≤ (22 / 7 : ℝ) * (1 / 32) := hsin.trans hzUpper
  have hcosNonneg : 0 ≤ Real.cos (Real.pi * t) := by
    have : (0 : ℝ) ≤ 1 - ((22 / 7 : ℝ) * (1 / 32)) ^ 2 / 2 := by norm_num
    linarith
  have hsinNonneg : 0 ≤ Real.sin (Real.pi * t) :=
    Real.sin_nonneg_of_nonneg_of_le_pi hz0
      (by nlinarith [ht1, Real.pi_pos])
  have hfirst := mul_le_mul
    (mul_le_mul haL hs0 (by norm_num) (by positivity))
    hcost (by norm_num) (by positivity)
  have hsecond := mul_le_mul hbeta
    (mul_le_mul hc1 hsint hsinNonneg cos_theta_nonneg)
    (by positivity) (by positivity)
  norm_num at hfirst hsecond ⊢
  nlinarith

private theorem sin_pi_t_lower {t : ℝ}
    (ht0 : 3 / 32 ≤ t) (ht1 : t ≤ 1 / 2) :
    (9 / 32 : ℝ) ≤ Real.sin (Real.pi * t) := by
  have hzlo0 : 0 ≤ Real.pi * (3 / 32 : ℝ) := by positivity
  have hzlohi : Real.pi * (3 / 32 : ℝ) ≤ Real.pi / 2 := by
    nlinarith [Real.pi_pos]
  have hz0 : -(Real.pi / 2) ≤ Real.pi * (3 / 32 : ℝ) := by positivity
  have hz1 : Real.pi * t ≤ Real.pi / 2 := by
    nlinarith [Real.pi_pos]
  have hmono := Real.sin_le_sin_of_le_of_le_pi_div_two
    hz0 hz1 (mul_le_mul_of_nonneg_left ht0 Real.pi_pos.le)
  have hcubic := Real.sin_ge_sub_cube hzlo0
  have hpiL := pi_lower
  have hpiU := pi_upper
  have hlow :
      (9 / 32 : ℝ)
        ≤ (6283 / 2000 : ℝ) * (3 / 32)
          - ((22 / 7 : ℝ) * (3 / 32)) ^ 3 / 6 := by norm_num
  have hcube :
      (Real.pi * (3 / 32 : ℝ)) ^ 3
        ≤ ((22 / 7 : ℝ) * (3 / 32)) ^ 3 := by
    apply pow_le_pow_left₀ (by positivity)
    exact mul_le_mul_of_nonneg_right hpiU (by norm_num)
  have hlinear :
      (6283 / 2000 : ℝ) * (3 / 32)
        ≤ Real.pi * (3 / 32) :=
    mul_le_mul_of_nonneg_right hpiL (by norm_num)
  nlinarith

private theorem right_first_numer_bound {x : ℝ}
    (hx1 : badRight ≤ x) (hx2 : x ≤ 3 / 2) :
    (2089839 / 5120000 : ℝ) ≤ numer x := by
  set t := x - 1 with ht
  have ht0 : 3 / 32 ≤ t := by
    unfold badRight at hx1
    linarith
  have ht1 : t ≤ 1 / 2 := by linarith
  have hsin := sin_pi_t_lower ht0 ht1
  have hcos : Real.cos (Real.pi * t) ≤ 1 := Real.cos_le_one _
  have hsin0 : 0 ≤ Real.sin (Real.pi * t) := by
    exact le_trans (by norm_num : (0 : ℝ) ≤ 9 / 32) hsin
  have hbeta : 2 * (6283 / 2000 : ℝ) * (35 / 32)
      ≤ beta x := by
    unfold beta badRight
    have hmul := mul_le_mul pi_lower hx1 (by norm_num) Real.pi_pos.le
    nlinarith
  have htrig := trig_shift_one t
  have hx : x = 1 + t := by simp only [ht]; ring
  rw [hx, htrig.1, htrig.2]
  unfold numer
  have hpositive := mul_le_mul
    (mul_le_mul hbeta cos_theta_lower (by norm_num) (by positivity))
    hsin (by norm_num) (by positivity)
  have hnegative := mul_le_mul alpha_upper sin_theta_upper
    (by positivity) (by positivity)
  have hnegative2 := mul_le_mul hnegative hcos
    (by positivity) (by positivity)
  norm_num at hpositive hnegative2 ⊢
  nlinarith

private theorem right_second_numer_bound {x : ℝ}
    (hx1 : 3 / 2 ≤ x) (hx2 : x ≤ 2) :
    (21 / 25 : ℝ) ≤ numer x := by
  set u := 2 - x with hu
  have hu0 : 0 ≤ u := by linarith
  have hu1 : u ≤ 1 / 2 := by linarith
  have hz0 : 0 ≤ Real.pi * u := mul_nonneg Real.pi_pos.le hu0
  have hz1 : Real.pi * u ≤ Real.pi / 2 := by
    nlinarith [Real.pi_pos]
  have hsin : 2 * u ≤ Real.sin (Real.pi * u) := by
    have h := Real.mul_le_sin hz0 hz1
    have hpi0 : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
    convert h using 1 <;> field_simp [hpi0]
  have hcos : 1 - 2 * u ≤ Real.cos (Real.pi * u) := by
    have h := Real.one_sub_mul_le_cos hz0 hz1
    have hpi0 : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
    convert h using 1 <;> field_simp [hpi0]
  have hbeta : 3 * (6283 / 2000 : ℝ) ≤ beta x := by
    unfold beta
    have hmul := mul_le_mul pi_lower hx1 (by norm_num) Real.pi_pos.le
    nlinarith
  have htrig :
      Real.cos (Real.pi * x) = Real.cos (Real.pi * u) ∧
      Real.sin (Real.pi * x) = -Real.sin (Real.pi * u) := by
    have hx : x = 2 - u := by simp only [hu]; ring
    rw [hx]
    constructor
    · rw [mul_sub, show Real.pi * 2 = Real.pi + Real.pi by ring,
        Real.cos_sub, Real.cos_add, Real.cos_pi, Real.sin_pi]
      ring
    · rw [mul_sub, show Real.pi * 2 = Real.pi + Real.pi by ring,
        Real.sin_sub, Real.sin_add, Real.cos_pi, Real.sin_pi]
      ring
  rw [htrig.1, htrig.2]
  unfold numer
  have hsin0 : 0 ≤ Real.sin (Real.pi * u) :=
    Real.sin_nonneg_of_nonneg_of_le_pi hz0
      (hz1.trans (by nlinarith [Real.pi_pos]))
  have hcos0 : 0 ≤ Real.cos (Real.pi * u) :=
    Real.cos_nonneg_of_mem_Icc ⟨by nlinarith [Real.pi_pos], hz1⟩
  have hterm1 := mul_le_mul
    (mul_le_mul hbeta cos_theta_lower (by norm_num) (by positivity))
    hsin (by positivity) (by positivity)
  have hterm2 := mul_le_mul
    (mul_le_mul alpha_lower sin_theta_lower (by norm_num) (by positivity))
    hcos (by norm_num) (by positivity)
  norm_num at hterm1 hterm2 ⊢
  nlinarith

private theorem long_numer_bound {x : ℝ}
    (hx1 : 33 / 16 ≤ x) (hx2 : x ≤ 35 / 16) :
    (1 : ℝ) ≤ -numer x := by
  set t := x - 2 with ht
  have ht0 : 1 / 16 ≤ t := by linarith
  have ht1 : t ≤ 3 / 16 := by linarith
  have hz0 : -(Real.pi / 2) ≤ Real.pi * (1 / 16 : ℝ) := by positivity
  have hz1 : Real.pi * t ≤ Real.pi / 2 := by
    nlinarith [Real.pi_pos]
  have hmono := Real.sin_le_sin_of_le_of_le_pi_div_two
    hz0 hz1 (mul_le_mul_of_nonneg_left ht0 Real.pi_pos.le)
  have hcubic := Real.sin_ge_sub_cube
    (by positivity : (0 : ℝ) ≤ Real.pi * (1 / 16 : ℝ))
  have hsinBase : (19 / 100 : ℝ)
      ≤ Real.sin (Real.pi * (1 / 16 : ℝ)) := by
    have hcube :
        (Real.pi * (1 / 16 : ℝ)) ^ 3
          ≤ ((22 / 7 : ℝ) * (1 / 16)) ^ 3 := by
      apply pow_le_pow_left₀ (by positivity)
      exact mul_le_mul_of_nonneg_right pi_upper (by norm_num)
    have hlinear :
        (6283 / 2000 : ℝ) * (1 / 16)
          ≤ Real.pi * (1 / 16) :=
      mul_le_mul_of_nonneg_right pi_lower (by norm_num)
    norm_num at hcube hlinear ⊢
    nlinarith
  have hsin : (19 / 100 : ℝ) ≤ Real.sin (Real.pi * t) :=
    hsinBase.trans hmono
  have hsin0 : 0 ≤ Real.sin (Real.pi * t) :=
    (by norm_num : (0 : ℝ) ≤ 19 / 100).trans hsin
  have hcos : Real.cos (Real.pi * t) ≤ 1 := Real.cos_le_one _
  have hbeta : 2 * (6283 / 2000 : ℝ) * (33 / 16)
      ≤ beta x := by
    unfold beta
    have hmul := mul_le_mul pi_lower hx1 (by norm_num) Real.pi_pos.le
    nlinarith
  have htrig := trig_shift_two t
  have hx : x = 2 + t := by simp only [ht]; ring
  rw [hx, htrig.1, htrig.2]
  unfold numer
  have hpositive := mul_le_mul
    (mul_le_mul hbeta cos_theta_lower (by norm_num) (by positivity))
    hsin (by norm_num) (by positivity)
  have hnegative := mul_le_mul alpha_upper sin_theta_upper
    (by positivity) (by positivity)
  have hnegative2 := mul_le_mul hnegative hcos
    (by positivity) (by positivity)
  norm_num at hpositive hnegative2 ⊢
  nlinarith

private theorem beta_upper_left {x : ℝ} (hx : x ≤ badLeft) :
    beta x ≤ 2 * (22 / 7 : ℝ) * (33 / 32) := by
  unfold beta badLeft
  exact mul_le_mul (mul_le_mul_of_nonneg_left pi_upper (by norm_num)) hx
    (by positivity) (by positivity)

private theorem beta_upper_two {x : ℝ} (hx : x ≤ 2) :
    beta x ≤ 4 * (22 / 7 : ℝ) := by
  unfold beta
  nlinarith [mul_le_mul pi_upper hx (by norm_num) Real.pi_pos.le]

private theorem beta_upper_long {x : ℝ} (hx : x ≤ 35 / 16) :
    beta x ≤ 2 * (22 / 7 : ℝ) * (35 / 16) := by
  unfold beta
  exact mul_le_mul (mul_le_mul_of_nonneg_left pi_upper (by norm_num)) hx
    (by positivity) (by positivity)

/-- Sharp short overlap on the left of the bad interval. -/
theorem profile_left_floor {x : ℝ}
    (hx1 : 1 ≤ x) (hx2 : x ≤ badLeft) :
    sharpAbsFloor ≤ profile x := by
  have hm := left_numer_bound hx1 hx2
  apply ratio_lower hx1 hm (by norm_num)
    (beta_upper_left hx2) (by norm_num)
  norm_num [sharpAbsFloor]

/-- Sharp short overlap to the right of the bad interval and below length 2. -/
theorem profile_right_floor {x : ℝ}
    (hx1 : badRight ≤ x) (hx2 : x ≤ 2) :
    sharpAbsFloor ≤ -profile x := by
  by_cases hxmid : x ≤ 3 / 2
  · have hm := right_first_numer_bound hx1 hxmid
    apply neg_ratio_lower (by linarith [hx1]) hm (by norm_num)
      (beta_upper_two hx2) (by norm_num)
    norm_num [sharpAbsFloor]
  · have hm := right_second_numer_bound (by linarith) hx2
    apply neg_ratio_lower (by linarith [hx1]) hm (by norm_num)
      (beta_upper_two hx2) (by norm_num)
    norm_num [sharpAbsFloor]

/-- Sharp long overlap for two consecutive bad gaps. -/
theorem profile_long_floor {x : ℝ}
    (hx1 : 33 / 16 ≤ x) (hx2 : x ≤ 35 / 16) :
    sharpAbsFloor ≤ profile x := by
  have hm := long_numer_bound hx1 hx2
  apply ratio_lower (by linarith) hm (by norm_num)
    (beta_upper_long hx2) (by norm_num)
  norm_num [sharpAbsFloor]

/-- The sharp profile is monotone decreasing on `[0,1]`. -/
theorem profile_one_le {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    profile 1 ≤ profile x := by
  unfold profile sharpOverlap
  have hmass : 0 < aStar lam := by
    rw [aStar_eq lam_pos]
    positivity
  have hden : 0 < aStar lam * 1 := by positivity
  apply (div_le_div_iff₀ hden hden).2
  simp only [mul_one]
  apply MeasureTheory.setIntegral_mono_on
  · exact (by
      have : Continuous (fun s : ℝ =>
          vStar lam s * Real.cos (2 * Real.pi * 1 * s)) := by
        unfold vStar
        fun_prop
      exact this.continuousOn.integrableOn_compact isCompact_Icc)
  · exact (by
      have : Continuous (fun s : ℝ =>
          vStar lam s * Real.cos (2 * Real.pi * x * s)) := by
        unfold vStar
        fun_prop
      exact this.continuousOn.integrableOn_compact isCompact_Icc)
  · exact measurableSet_Icc
  · intro s hs
    have hsabs : |s| ≤ 1 / 2 := abs_le.mpr hs
    have hvnonneg : 0 ≤ vStar lam s := by
      have h := cos_factor_ge
        (lam := lam) (L := (1 : ℝ)) lam_pos lam_le_one one_pos
        (u := s) (by simpa using hsabs)
      linarith
    have harg0 : 0 ≤ |2 * Real.pi * x * s| := abs_nonneg _
    have hargle : |2 * Real.pi * x * s| ≤ |2 * Real.pi * 1 * s| := by
      rw [abs_mul, abs_mul, abs_mul, abs_mul,
        abs_of_nonneg hx0, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)]
      nlinarith [abs_nonneg (2 * Real.pi), abs_nonneg s]
    have hargpi : |2 * Real.pi * 1 * s| ≤ Real.pi := by
      rw [abs_mul, abs_mul, abs_mul,
        abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1), abs_of_pos Real.pi_pos]
      nlinarith [hsabs, Real.pi_pos, abs_of_nonneg (show 0 ≤ (2 : ℝ) from by norm_num)]
    have hcos := Real.cos_le_cos_of_nonneg_of_le_pi
      harg0 hargpi hargle
    rw [← Real.cos_abs, ← Real.cos_abs] at hcos
    exact mul_le_mul_of_nonneg_left hcos hvnonneg

/-- Coarse floor on every short gap at most one. -/
theorem profile_zero_one_floor {x : ℝ}
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    sharpAbsFloor ≤ profile x := by
  exact (profile_left_floor (x := 1) le_rfl (by norm_num [badLeft])).trans
    (profile_one_le hx0 hx1)

/-- Every good short gap below the length threshold has the required floor. -/
theorem good_short_floor {x : ℝ}
    (hx0 : 0 ≤ x)
    (hgood : ¬(badLeft ≤ x ∧ x ≤ badRight))
    (hx2 : x ≤ lengthThreshold) :
    sharpAbsFloor ≤ |profile x| := by
  by_cases hx1 : x ≤ 1
  · exact (profile_zero_one_floor hx0 hx1).trans (le_abs_self _)
  · have hx1' : 1 ≤ x := by linarith
    rcases not_and_or.mp hgood with hleft | hright
    · have h := profile_left_floor hx1' (by linarith)
      exact h.trans (le_abs_self _)
    · have h := profile_right_floor (by linarith) (by
        simpa [lengthThreshold] using hx2)
      rw [abs_neg] at h
      exact h

/-- Two consecutive bad gaps land in the certified long-overlap interval. -/
theorem bad_bad_long_floor {x y : ℝ}
    (hx : badLeft ≤ x ∧ x ≤ badRight)
    (hy : badLeft ≤ y ∧ y ≤ badRight) :
    sharpAbsFloor ≤ |profile (x + y)| := by
  have h := profile_long_floor
    (x := x + y) (by
      unfold badLeft badRight at hx hy ⊢
      linarith) (by
      unfold badLeft badRight at hx hy ⊢
      linarith)
  exact h.trans (le_abs_self _)

/-- Global sharp-profile bound used by the square perturbation lemma. -/
theorem abs_profile_le_one (x : ℝ) : |profile x| ≤ 1 := by
  unfold profile
  have hmass : 0 < aStar lam := by
    rw [aStar_eq lam_pos]
    positivity
  apply abs_sharpOverlap_le_one one_pos hmass
  simpa using abs_sharp_numerator_le lam_pos lam_le_one one_pos

end Zeta23.GapMatching.OneBandSharpProfile
