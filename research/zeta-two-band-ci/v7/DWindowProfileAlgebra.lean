/-
Copyright (c) 2026.
SPDX-License-Identifier: Apache-2.0

Algebraic normalization for the Montgomery--Taylor profile comparison.

If

* the actual and sharp Fourier numerators differ by at most `2w`;
* the actual and sharp mass normalizations differ by at most `4w/L`;
* both normalizations are at least `1/2`;
* the sharp numerator has absolute value at most `aStar*L`;

then the two normalized overlaps differ by at most `12w/L`.

The first two bullets are the two-ramp estimates in upstream
`ThmD/Window.lean`; this file isolates the denominator algebra so that the
remaining analytic proof does not have to repeat it for every gap range.
-/
import Zeta23.ThmD.Window
import Zeta23.GapMatching.DWindowOverlap
import Zeta23.GapMatching.DWindowRampEstimate

open Real

noncomputable section

namespace Zeta23.GapMatching.DWindowProfileAlgebra

open Zeta23
open Zeta23.ThmD
open Zeta23.GapMatching.DWindowOverlap
open Zeta23.GapMatching.DWindowRampEstimate

/-- Sharp-cutoff normalized overlap at physical frequency `r`. -/
def sharpOverlap (lam L r : ℝ) : ℝ :=
  (∫ u in Set.Icc (-(L / 2)) (L / 2),
      vStar lam (u / L) * Real.cos (r * u)) /
    (aStar lam * L)

/-- Pure ratio perturbation estimate. -/
theorem normalized_overlap_close
    {actualNumerator sharpNumerator actualA sharpA L w : ℝ}
    (hL : 0 < L)
    (hw : 0 ≤ w)
    (hactualA : 1 / 2 ≤ actualA)
    (hsharpA : 1 / 2 ≤ sharpA)
    (hAclose : |actualA - sharpA| ≤ 4 * w / L)
    (hNumClose : |actualNumerator - sharpNumerator| ≤ 2 * w)
    (hSharpNum : |sharpNumerator| ≤ sharpA * L) :
    |actualNumerator / (actualA * L)
        - sharpNumerator / (sharpA * L)|
      ≤ 12 * w / L := by
  have hactualPos : 0 < actualA := by linarith
  have hsharpPos : 0 < sharpA := by linarith
  have hactualL : 0 < actualA * L := mul_pos hactualPos hL
  have hsharpL : 0 < sharpA * L := mul_pos hsharpPos hL
  have hwL : 0 ≤ w / L := div_nonneg hw hL.le

  have hsplit :
      actualNumerator / (actualA * L)
          - sharpNumerator / (sharpA * L)
        = (actualNumerator - sharpNumerator) / (actualA * L)
          + sharpNumerator * (sharpA - actualA)
              / (actualA * sharpA * L) := by
    field_simp [hactualPos.ne', hsharpPos.ne', hL.ne']
    ring

  rw [hsplit]
  calc
    |(actualNumerator - sharpNumerator) / (actualA * L)
        + sharpNumerator * (sharpA - actualA)
            / (actualA * sharpA * L)|
        ≤ |(actualNumerator - sharpNumerator) / (actualA * L)|
          + |sharpNumerator * (sharpA - actualA)
              / (actualA * sharpA * L)| := abs_add_le _ _
    _ = |actualNumerator - sharpNumerator| / (actualA * L)
          + |sharpNumerator| * |sharpA - actualA|
              / (actualA * sharpA * L) := by
          rw [abs_div, abs_div, abs_mul,
            abs_of_pos hactualL,
            abs_of_pos (by positivity : 0 < actualA * sharpA * L)]
    _ ≤ (2 * w) / ((1 / 2) * L)
          + (sharpA * L) * (4 * w / L)
              / ((1 / 2) * sharpA * L) := by
          gcongr
          · exact hNumClose
          · exact mul_le_mul_of_nonneg_right hactualA hL.le
          · exact hSharpNum
          · simpa [abs_sub_comm] using hAclose
          · exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right hactualA hsharpPos.le)
              hL.le
    _ = 12 * w / L := by
          field_simp [hL.ne', hsharpPos.ne']
          ring

/-- The sharp profile is bounded by one whenever its numerator is bounded by
its positive mass denominator. -/
theorem abs_sharpOverlap_le_one
    {lam L r : ℝ}
    (hL : 0 < L)
    (ha : 0 < aStar lam)
    (hnum :
      |∫ u in Set.Icc (-(L / 2)) (L / 2),
          vStar lam (u / L) * Real.cos (r * u)|
        ≤ aStar lam * L) :
    |sharpOverlap lam L r| ≤ 1 := by
  unfold sharpOverlap
  rw [abs_div, abs_of_pos (mul_pos ha hL), div_le_one (mul_pos ha hL)]
  exact hnum


/-- Normalized overlap written directly as the real cosine integral of the
actual squared D-window. -/
def integralOverlapD
    (P : Params) (T tau tau' : ℝ) : ℝ :=
  (∫ u, P.phiD T u ^ 2 * Real.cos ((tau - tau') * u)) /
    (AdmWindow.av (P.phiD T) (P.L T) * P.L T)

/-- The public two-ramp estimate, together with the normalization algebra,
puts the actual D-window cosine integral within `12w/L` of the sharp profile.
The only separate bridge to `fullGridOverlap` is the standard real-Fourier
identity `VPhiR = ∫ v² cos`. -/
theorem integralOverlapD_close_sharp
    {P : Params} {T tau tau' : ℝ}
    (hP : P.Valid)
    (h8 : 8 * P.w ≤ P.L T)
    (haActual : 1 / 2 ≤ AdmWindow.av (P.phiD T) (P.L T))
    (haSharp : 1 / 2 ≤ aStar P.lam)
    (hAclose :
      |AdmWindow.av (P.phiD T) (P.L T) - aStar P.lam|
        ≤ 4 * P.w / P.L T)
    (hSharpNum :
      |∫ u in Set.Icc (-(P.L T / 2)) (P.L T / 2),
          vStar P.lam (u / P.L T)
            * Real.cos ((tau - tau') * u)|
        ≤ aStar P.lam * P.L T) :
    |integralOverlapD P T tau tau'
        - sharpOverlap P.lam (P.L T) (tau - tau')|
      ≤ 12 * P.w / P.L T := by
  have hL : 0 < P.L T := by
    linarith [hP.one_le_w]
  have hNumClose := phiD_sq_cos_integral_close
    (rho := P.ϱ) (lam := P.lam) (L := P.L T)
    (w := P.w) (r := tau - tau')
    hP.taper hP.lam_pos hP.lam_le_one hP.one_le_w h8
  unfold integralOverlapD sharpOverlap
  exact normalized_overlap_close hL (by positivity)
    haActual haSharp hAclose hNumClose hSharpNum


/-- The Poisson numerator `VPhiR` is exactly the cosine integral used in
`integralOverlapD`. -/
theorem fullGridOverlap_eq_integralOverlapD
    {P : Params} {T tau tau' : ℝ}
    (hP : P.Valid)
    (h8 : 8 * P.w ≤ P.L T) :
    fullGridOverlap (P.phiD T) (P.L T) tau tau'
      = integralOverlapD P T tau tau' := by
  unfold fullGridOverlap integralOverlapD
  rw [VPhiR_eq_cos_integral (admWindow_params hP h8)]

/-- Full-grid profile comparison with the Fourier/cosine and two-ramp steps
fully discharged. -/
theorem fullGridOverlapD_close_sharp_from_ramps
    {P : Params} {T tau tau' : ℝ}
    (hP : P.Valid)
    (h8 : 8 * P.w ≤ P.L T)
    (haActual : 1 / 2 ≤ AdmWindow.av (P.phiD T) (P.L T))
    (haSharp : 1 / 2 ≤ aStar P.lam)
    (hAclose :
      |AdmWindow.av (P.phiD T) (P.L T) - aStar P.lam|
        ≤ 4 * P.w / P.L T)
    (hSharpNum :
      |∫ u in Set.Icc (-(P.L T / 2)) (P.L T / 2),
          vStar P.lam (u / P.L T)
            * Real.cos ((tau - tau') * u)|
        ≤ aStar P.lam * P.L T) :
    |fullGridOverlap (P.phiD T) (P.L T) tau tau'
        - sharpOverlap P.lam (P.L T) (tau - tau')|
      ≤ 12 * P.w / P.L T := by
  rw [fullGridOverlap_eq_integralOverlapD hP h8]
  exact integralOverlapD_close_sharp hP h8
    haActual haSharp hAclose hSharpNum


/-- The sharp Montgomery--Taylor mass is uniformly bounded below on
`0 < lambda <= 1`. -/
theorem three_quarters_le_aStar
    {lam : ℝ} (h0 : 0 < lam) (h1 : lam ≤ 1) :
    (3 / 4 : ℝ) ≤ aStar lam := by
  unfold aStar
  have hconst :
      ∫ s in (-(1 : ℝ) / 2)..(1 / 2), (3 / 4 : ℝ)
        = 3 / 4 := by norm_num
  rw [← hconst]
  apply intervalIntegral.integral_mono_on
    (by norm_num : (-(1 : ℝ) / 2) ≤ 1 / 2)
    (Continuous.intervalIntegrable continuous_const _ _)
    (Continuous.intervalIntegrable
      (by unfold vStar; fun_prop) _ _)
  intro s hs
  rw [Set.uIcc_of_le (by norm_num)] at hs
  have h := cos_factor_ge
    (lam := lam) (L := (1 : ℝ)) h0 h1 one_pos
    (u := s) (by
      rw [abs_le]
      exact hs)
  simpa using h

/-- Public scale substitution for the sharp profile mass. -/
theorem sharp_mass_integral
    {lam L : ℝ} (hL : 0 < L) :
    ∫ u in Set.Icc (-(L / 2)) (L / 2),
        vStar lam (u / L)
      = aStar lam * L := by
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le
      (by linarith : -(L / 2) ≤ L / 2),
    intervalIntegral.integral_comp_div
      (f := vStar lam) hL.ne', smul_eq_mul]
  have hlo : -(L / 2) / L = -(1 : ℝ) / 2 := by
    field_simp [hL.ne']
    ring
  have hhi : (L / 2) / L = (1 : ℝ) / 2 := by
    field_simp [hL.ne']
    ring
  rw [hlo, hhi]
  unfold aStar
  ring

/-- Absolute value of the sharp Fourier numerator is bounded by its mass. -/
theorem abs_sharp_numerator_le
    {lam L r : ℝ}
    (h0 : 0 < lam) (h1 : lam ≤ 1)
    (hL : 0 < L) :
    |∫ u in Set.Icc (-(L / 2)) (L / 2),
        vStar lam (u / L) * Real.cos (r * u)|
      ≤ aStar lam * L := by
  have hvintegrable : MeasureTheory.IntegrableOn
      (fun u => vStar lam (u / L))
      (Set.Icc (-(L / 2)) (L / 2)) :=
    (by
      have : Continuous (fun u => vStar lam (u / L)) := by
        unfold vStar
        fun_prop
      exact this.continuousOn.integrableOn_compact isCompact_Icc)
  have hfintegrable : MeasureTheory.IntegrableOn
      (fun u => vStar lam (u / L) * Real.cos (r * u))
      (Set.Icc (-(L / 2)) (L / 2)) :=
    (by
      have : Continuous
          (fun u => vStar lam (u / L) * Real.cos (r * u)) := by
        unfold vStar
        fun_prop
      exact this.continuousOn.integrableOn_compact isCompact_Icc)
  calc
    |∫ u in Set.Icc (-(L / 2)) (L / 2),
        vStar lam (u / L) * Real.cos (r * u)|
        ≤ ∫ u in Set.Icc (-(L / 2)) (L / 2),
            |vStar lam (u / L) * Real.cos (r * u)| :=
          MeasureTheory.abs_integral_le_integral_abs
    _ ≤ ∫ u in Set.Icc (-(L / 2)) (L / 2),
            vStar lam (u / L) := by
          apply MeasureTheory.setIntegral_mono_on
            hfintegrable.abs hvintegrable measurableSet_Icc
          intro u hu
          have huabs : |u| ≤ L / 2 := by
            exact abs_le.mpr hu
          have hvnonneg : 0 ≤ vStar lam (u / L) := by
            linarith [cos_factor_ge h0 h1 hL huabs]
          rw [abs_mul, abs_of_nonneg hvnonneg]
          exact mul_le_of_le_one_right hvnonneg
            (Real.abs_cos_le_one _)
    _ = aStar lam * L := sharp_mass_integral hL

/-- Canonical full-grid profile comparison: all mass, Fourier/cosine and ramp
hypotheses are discharged from the standard D-window assumptions. -/
theorem fullGridOverlapD_close_sharp_canonical
    {P : Params} {T tau tau' : ℝ}
    (hP : P.Valid)
    (h8 : 8 * P.w ≤ P.L T)
    (h4pi : 4 * Real.pi * P.w ≤ P.L T) :
    |fullGridOverlap (P.phiD T) (P.L T) tau tau'
        - sharpOverlap P.lam (P.L T) (tau - tau')|
      ≤ 12 * P.w / P.L T := by
  have hL : 0 < P.L T := by
    linarith [hP.one_le_w]
  have haActual0 := (aD_range_of hP h8 h4pi).1
  have haActual :
      1 / 2 ≤ AdmWindow.av (P.phiD T) (P.L T) := by
    simpa [atD_a_eq_av hP T] using haActual0
  have haSharp : 1 / 2 ≤ aStar P.lam := by
    exact (by linarith [three_quarters_le_aStar
      hP.lam_pos hP.lam_le_one])
  have hAclose :
      |AdmWindow.av (P.phiD T) (P.L T) - aStar P.lam|
        ≤ 4 * P.w / P.L T := by
    simpa [AdmWindow.av] using
      (aD_close hP.taper hP.lam_pos hP.lam_le_one
        hP.one_le_w h8)
  have hSharpNum := abs_sharp_numerator_le
    hP.lam_pos hP.lam_le_one hL
    (r := tau - tau')
  exact fullGridOverlapD_close_sharp_from_ramps
    hP h8 haActual haSharp hAclose hSharpNum

/-- D-window specialization once the two public ramp estimates are supplied.
This theorem is the exact interface consumed by the finite-grid tail proof. -/
theorem fullGridOverlapD_close_sharp
    {P : Params} {T tau tau' : ℝ}
    (hL : 0 < P.L T)
    (haActual : 1 / 2 ≤ AdmWindow.av (P.phiD T) (P.L T))
    (haSharp : 1 / 2 ≤ aStar P.lam)
    (hAclose :
      |AdmWindow.av (P.phiD T) (P.L T) - aStar P.lam|
        ≤ 4 * P.w / P.L T)
    (hNumClose :
      |AdmWindow.VPhiR (P.phiD T) (tau - tau')
          - ∫ u in Set.Icc (-(P.L T / 2)) (P.L T / 2),
              vStar P.lam (u / P.L T)
                * Real.cos ((tau - tau') * u)|
        ≤ 2 * P.w)
    (hSharpNum :
      |∫ u in Set.Icc (-(P.L T / 2)) (P.L T / 2),
          vStar P.lam (u / P.L T)
            * Real.cos ((tau - tau') * u)|
        ≤ aStar P.lam * P.L T) :
    |fullGridOverlap (P.phiD T) (P.L T) tau tau'
        - sharpOverlap P.lam (P.L T) (tau - tau')|
      ≤ 12 * P.w / P.L T := by
  unfold fullGridOverlap sharpOverlap
  exact normalized_overlap_close hL (by positivity)
    haActual haSharp hAclose hNumClose hSharpNum

end Zeta23.GapMatching.DWindowProfileAlgebra
