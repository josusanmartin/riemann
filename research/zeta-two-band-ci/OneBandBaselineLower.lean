/-
Copyright (c) 2026.
SPDX-License-Identifier: Apache-2.0

A symbolic lower enclosure for the fixed one-band Montgomery--Taylor
baseline.  This is the lower-bound companion to
`CandidateStrictImprovementTight`.
-/
import Zeta23.GapMatching.CandidateStrictImprovementTight
import Zeta23.GapMatching.OneBandPotentialSafeNumerics

open Set Real

noncomputable section

namespace Zeta23.GapMatching.OneBandBaselineLower

open Zeta23
open Zeta23.ThmD
open Zeta23.GapMatching.CandidateStrictImprovementTight
open Zeta23.GapMatching.OneBandPotentialSafeNumerics

/-- Eleventh-order lower Taylor bound for sine. -/
theorem sin_ge_undecic {x : ℝ} (hx : 0 ≤ x) :
    x - x ^ 3 / 6 + x ^ 5 / 120 - x ^ 7 / 5040
        + x ^ 9 / 362880 - x ^ 11 / 39916800
      ≤ Real.sin x := by
  let f : ℝ → ℝ := fun t =>
    Real.sin t -
      (t - t ^ 3 / 6 + t ^ 5 / 120 - t ^ 7 / 5040
        + t ^ 9 / 362880 - t ^ 11 / 39916800)
  have hderiv : ∀ t : ℝ,
      deriv f t = Real.cos t -
        (1 - t ^ 2 / 2 + t ^ 4 / 24 - t ^ 6 / 720
          + t ^ 8 / 40320 - t ^ 10 / 3628800) := by
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
        nlinarith [cos_ge_decic ht.le])
  have h0 : f 0 ≤ f x := hmono (by simp) hx hx
  simpa [f] using h0

/-- Twelfth-order upper Taylor bound for cosine. -/
theorem cos_le_duodecic {x : ℝ} (hx : 0 ≤ x) :
    Real.cos x ≤
      1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720
        + x ^ 8 / 40320 - x ^ 10 / 3628800
        + x ^ 12 / 479001600 := by
  let f : ℝ → ℝ := fun t =>
    1 - t ^ 2 / 2 + t ^ 4 / 24 - t ^ 6 / 720
      + t ^ 8 / 40320 - t ^ 10 / 3628800
      + t ^ 12 / 479001600 - Real.cos t
  have hderiv : ∀ t : ℝ,
      deriv f t =
        -t + t ^ 3 / 6 - t ^ 5 / 120 + t ^ 7 / 5040
          - t ^ 9 / 362880 + t ^ 11 / 39916800
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
        nlinarith [sin_ge_undecic ht.le])
  have h0 : f 0 ≤ f x := hmono (by simp) hx hx
  simpa [f] using h0

private theorem sqrt_two_pos : 0 < Real.sqrt 2 := by positivity
private theorem sqrt_two_ne : Real.sqrt 2 ≠ 0 := ne_of_gt sqrt_two_pos
private theorem sqrt_two_sq : Real.sqrt 2 ^ 2 = 2 :=
  Real.sq_sqrt (by norm_num)

private theorem lam_pos : 0 < lam := by norm_num [lam]
private theorem lam_nonneg : 0 ≤ lam := lam_pos.le
private theorem lam_le_one : lam ≤ 1 := by norm_num [lam]

private theorem sqrt_two_mul_theta :
    Real.sqrt 2 * theta lam = lam := by
  unfold theta
  field_simp [sqrt_two_ne]

private theorem theta_sq : theta lam ^ 2 = lam ^ 2 / 2 := by
  unfold theta
  rw [div_pow, sqrt_two_sq]

private def sinLower : ℝ :=
  lam - lam ^ 3 / 12 + lam ^ 5 / 480 - lam ^ 7 / 40320
    + lam ^ 9 / 5806080 - lam ^ 11 / 1277337600

private def cosUpper : ℝ :=
  1 - lam ^ 2 / 4 + lam ^ 4 / 96 - lam ^ 6 / 5760
    + lam ^ 8 / 645120 - lam ^ 10 / 116121600
    + lam ^ 12 / 30656102400

private def ratioUpper : ℝ := 2 - lam / 2 - deltaLower

private theorem scaled_sin_lower :
    sinLower ≤ Real.sqrt 2 * Real.sin (theta lam) := by
  have hs := sin_ge_undecic (theta_nonneg lam_nonneg)
  have hscaled := mul_le_mul_of_nonneg_left hs (Real.sqrt_nonneg 2)
  have heq :
      Real.sqrt 2 *
        (theta lam - theta lam ^ 3 / 6 + theta lam ^ 5 / 120
          - theta lam ^ 7 / 5040 + theta lam ^ 9 / 362880
          - theta lam ^ 11 / 39916800) = sinLower := by
    calc
      Real.sqrt 2 *
          (theta lam - theta lam ^ 3 / 6 + theta lam ^ 5 / 120
            - theta lam ^ 7 / 5040 + theta lam ^ 9 / 362880
            - theta lam ^ 11 / 39916800)
        = (Real.sqrt 2 * theta lam) *
          (1 - theta lam ^ 2 / 6 + (theta lam ^ 2) ^ 2 / 120
            - (theta lam ^ 2) ^ 3 / 5040
            + (theta lam ^ 2) ^ 4 / 362880
            - (theta lam ^ 2) ^ 5 / 39916800) := by ring
      _ = lam *
          (1 - (lam ^ 2 / 2) / 6 + (lam ^ 2 / 2) ^ 2 / 120
            - (lam ^ 2 / 2) ^ 3 / 5040
            + (lam ^ 2 / 2) ^ 4 / 362880
            - (lam ^ 2 / 2) ^ 5 / 39916800) := by
          rw [sqrt_two_mul_theta, theta_sq]
      _ = sinLower := by
        unfold sinLower
        ring
  rw [← heq]
  exact hscaled

private theorem cosine_upper : Real.cos (theta lam) ≤ cosUpper := by
  have hc := cos_le_duodecic (theta_nonneg lam_nonneg)
  calc
    Real.cos (theta lam)
      ≤ 1 - theta lam ^ 2 / 2 + theta lam ^ 4 / 24
          - theta lam ^ 6 / 720 + theta lam ^ 8 / 40320
          - theta lam ^ 10 / 3628800
          + theta lam ^ 12 / 479001600 := hc
    _ = 1 - (theta lam ^ 2) / 2 + (theta lam ^ 2) ^ 2 / 24
          - (theta lam ^ 2) ^ 3 / 720
          + (theta lam ^ 2) ^ 4 / 40320
          - (theta lam ^ 2) ^ 5 / 3628800
          + (theta lam ^ 2) ^ 6 / 479001600 := by ring
    _ = 1 - (lam ^ 2 / 2) / 2 + (lam ^ 2 / 2) ^ 2 / 24
          - (lam ^ 2 / 2) ^ 3 / 720
          + (lam ^ 2 / 2) ^ 4 / 40320
          - (lam ^ 2 / 2) ^ 5 / 3628800
          + (lam ^ 2 / 2) ^ 6 / 479001600 := by rw [theta_sq]
    _ = cosUpper := by
      unfold cosUpper
      ring

private theorem ratio_arithmetic :
    cosUpper ≤ ratioUpper * sinLower := by
  norm_num [cosUpper, ratioUpper, sinLower, lam, deltaLower]

private theorem scaled_sin_pos :
    0 < Real.sqrt 2 * Real.sin (theta lam) := by
  exact mul_pos sqrt_two_pos (sin_theta_pos lam_pos lam_le_one)

private theorem cosine_ratio_upper :
    Real.cos (theta lam) /
        (Real.sqrt 2 * Real.sin (theta lam))
      ≤ ratioUpper := by
  rw [div_le_iff₀ scaled_sin_pos]
  calc
    Real.cos (theta lam) ≤ cosUpper := cosine_upper
    _ ≤ ratioUpper * sinLower := ratio_arithmetic
    _ ≤ ratioUpper *
        (Real.sqrt 2 * Real.sin (theta lam)) := by
          apply mul_le_mul_of_nonneg_left scaled_sin_lower
          norm_num [ratioUpper, lam, deltaLower]

private theorem theta_eq_half_lam_sqrt_two :
    theta lam = lam / 2 * Real.sqrt 2 := by
  unfold theta
  apply (div_eq_iff sqrt_two_ne).2
  rw [mul_assoc, ← pow_two, sqrt_two_sq]
  ring

private theorem cStar_inv_identity :
    (cStar lam)⁻¹ = lam / 2 +
      Real.cos (theta lam) /
        (Real.sqrt 2 * Real.sin (theta lam)) := by
  change
    (Real.sqrt 2 * Real.sin (theta lam) /
      (Real.cos (theta lam) + theta lam * Real.sin (theta lam)))⁻¹
      = _
  rw [inv_div]
  rw [div_eq_iff (ne_of_gt scaled_sin_pos)]
  calc
    Real.cos (theta lam) + theta lam * Real.sin (theta lam)
      = Real.cos (theta lam) +
          (lam / 2 * Real.sqrt 2) * Real.sin (theta lam) := by
            rw [theta_eq_half_lam_sqrt_two]
    _ = (lam / 2 +
          Real.cos (theta lam) /
            (Real.sqrt 2 * Real.sin (theta lam)))
          * (Real.sqrt 2 * Real.sin (theta lam)) := by
            rw [add_mul,
              div_mul_cancel₀ _ (ne_of_gt scaled_sin_pos)]
            ring

/-- The fixed one-band baseline dominates the conservative rational value
used by the fixed-point certificate. -/
theorem deltaLower_le_HD_lam :
    deltaLower ≤ HD lam := by
  unfold HD
  rw [one_div, cStar_inv_identity]
  have h := cosine_ratio_upper
  unfold ratioUpper at h
  linarith

end Zeta23.GapMatching.OneBandBaselineLower
