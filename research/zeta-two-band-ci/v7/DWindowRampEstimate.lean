/-
Copyright (c) 2026.
SPDX-License-Identifier: Apache-2.0

Public two-ramp estimate for the Montgomery--Taylor overlap numerator.

Upstream `ThmD/Window.lean` contains the same finite-measure argument as a
private helper for the moment computations.  The gap-matching proof needs the
estimate at nonzero Fourier frequency, so this file republishes the generic
lemma and specializes it to

  vStar(lambda,u/L) * cos(r u)

multiplied by the squared ramp taper.  The resulting numerator error is at
most `2w`, uniformly in the real frequency `r`.
-/
import Zeta23.ThmD.Window
import Zeta23.ThmD.WindowCore

open Real Set MeasureTheory

noncomputable section

namespace Zeta23.GapMatching.DWindowRampEstimate

open Zeta23
open Zeta23.ThmD

/-- Public version of the two-ramp integral estimate. -/
theorem edge_estimate_public
    {h p : ℝ → ℝ} {L w : ℝ}
    (_hL : 0 < L) (hw0 : 0 < w)
    (hwL : 2 * w ≤ L)
    (hh : ∀ u, |h u| ≤ 1)
    (hp0 : ∀ u, 0 ≤ p u)
    (hp1 : ∀ u, p u ≤ 1)
    (hpl : ∀ u : ℝ, |u| ≤ L / 2 - w → p u = 1)
    (hsupp : ∀ u : ℝ, L / 2 ≤ |u| → p u = 0)
    (hpc : Continuous p)
    (hhc : Continuous h) :
    |(∫ u, h u * p u)
        - ∫ u in Set.Icc (-(L / 2)) (L / 2), h u|
      ≤ 2 * w := by
  have hrestr :
      ∫ u, h u * p u
        = ∫ u in Set.Icc (-(L / 2)) (L / 2), h u * p u := by
    rw [MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero]
    intro x hx
    rw [Set.mem_Icc, not_and_or, not_le, not_le] at hx
    have hxabs : L / 2 ≤ |x| := by
      rcases hx with hx | hx
      · rw [abs_of_neg (by linarith : x < 0)]
        linarith
      · rw [abs_of_pos (by linarith : 0 < x)]
        linarith
    rw [hsupp x hxabs, mul_zero]

  have hIhp :
      MeasureTheory.IntegrableOn (fun u => h u * p u)
        (Set.Icc (-(L / 2)) (L / 2)) :=
    ((hhc.mul hpc).continuousOn).integrableOn_compact isCompact_Icc
  have hIh :
      MeasureTheory.IntegrableOn h
        (Set.Icc (-(L / 2)) (L / 2)) :=
    hhc.continuousOn.integrableOn_compact isCompact_Icc
  have hsub :
      (∫ u, h u * p u)
          - ∫ u in Set.Icc (-(L / 2)) (L / 2), h u
        = ∫ u in Set.Icc (-(L / 2)) (L / 2),
            (h u * p u - h u) := by
    rw [hrestr, ← MeasureTheory.integral_sub hIhp hIh]
  rw [hsub]

  set majorant : ℝ → ℝ := fun u =>
    (Set.Icc (-(L / 2)) (-(L / 2) + w)).indicator
        (1 : ℝ → ℝ) u
      + (Set.Icc (L / 2 - w) (L / 2)).indicator
        (1 : ℝ → ℝ) u with hmajorant

  have hImajorant : Integrable majorant := by
    apply Integrable.add
    · exact
        (MeasureTheory.integrable_indicator_iff measurableSet_Icc).mpr
          (MeasureTheory.integrableOn_const
            (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top))
    · exact
        (MeasureTheory.integrable_indicator_iff measurableSet_Icc).mpr
          (MeasureTheory.integrableOn_const
            (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top))

  have hindicator_nonneg :
      ∀ (s : Set ℝ) (u : ℝ),
        0 ≤ s.indicator (1 : ℝ → ℝ) u :=
    fun s u => Set.indicator_nonneg (fun _ _ => zero_le_one) u

  have hpointwise :
      ∀ u ∈ Set.Icc (-(L / 2)) (L / 2),
        |h u * p u - h u| ≤ majorant u := by
    intro u hu
    have hmajorant0 : 0 ≤ majorant u := by
      rw [hmajorant]
      exact add_nonneg
        (hindicator_nonneg _ u)
        (hindicator_nonneg _ u)
    rcases le_or_gt |u| (L / 2 - w) with hplateau | hedge
    · rw [hpl u hplateau, mul_one, sub_self, abs_zero]
      exact hmajorant0
    · have hbound : |h u * p u - h u| ≤ 1 := by
        have heq : h u * p u - h u = h u * (p u - 1) := by
          ring
        rw [heq, abs_mul]
        calc
          |h u| * |p u - 1| ≤ 1 * 1 := by
            apply mul_le_mul (hh u) ?_
              (abs_nonneg _) zero_le_one
            rw [abs_le]
            exact ⟨by linarith [hp0 u], by linarith [hp1 u]⟩
          _ = 1 := mul_one 1
      have hone : 1 ≤ majorant u := by
        rw [hmajorant]
        dsimp only
        rcases le_or_gt u 0 with hneg | hpos
        · have hu1 :
              u ∈ Set.Icc (-(L / 2)) (-(L / 2) + w) := by
            refine ⟨hu.1, ?_⟩
            have habs : |u| = -u := abs_of_nonpos hneg
            rw [habs] at hedge
            linarith
          have hother :=
            hindicator_nonneg (Set.Icc (L / 2 - w) (L / 2)) u
          change 1 ≤
            (Set.Icc (-(L / 2)) (-(L / 2) + w)).indicator
                (1 : ℝ → ℝ) u
              + (Set.Icc (L / 2 - w) (L / 2)).indicator
                (1 : ℝ → ℝ) u
          rw [Set.indicator_of_mem hu1, Pi.one_apply]
          linarith
        · have hu1 :
              u ∈ Set.Icc (L / 2 - w) (L / 2) := by
            refine ⟨?_, hu.2⟩
            have habs : |u| = u := abs_of_pos hpos
            rw [habs] at hedge
            linarith
          have hother :=
            hindicator_nonneg
              (Set.Icc (-(L / 2)) (-(L / 2) + w)) u
          change 1 ≤
            (Set.Icc (-(L / 2)) (-(L / 2) + w)).indicator
                (1 : ℝ → ℝ) u
              + (Set.Icc (L / 2 - w) (L / 2)).indicator
                (1 : ℝ → ℝ) u
          rw [Set.indicator_of_mem hu1, Pi.one_apply]
          linarith
      linarith

  calc
    |∫ u in Set.Icc (-(L / 2)) (L / 2),
        (h u * p u - h u)|
        ≤ ∫ u in Set.Icc (-(L / 2)) (L / 2),
            |h u * p u - h u| :=
          MeasureTheory.abs_integral_le_integral_abs
    _ ≤ ∫ u in Set.Icc (-(L / 2)) (L / 2), majorant u := by
          have hIabs :
              MeasureTheory.IntegrableOn
                (fun u => |h u * p u - h u|)
                (Set.Icc (-(L / 2)) (L / 2)) := by
            change MeasureTheory.Integrable
              (fun u => |h u * p u - h u|)
              (MeasureTheory.volume.restrict
                (Set.Icc (-(L / 2)) (L / 2)))
            simpa only [Pi.sub_apply] using (hIhp.sub hIh).abs
          exact MeasureTheory.setIntegral_mono_on hIabs
            hImajorant.integrableOn measurableSet_Icc hpointwise
    _ ≤ ∫ u, majorant u :=
          MeasureTheory.setIntegral_le_integral hImajorant
            (MeasureTheory.ae_of_all _ fun u => by
              rw [hmajorant]
              exact add_nonneg
                (Set.indicator_nonneg
                  (fun _ _ => zero_le_one) u)
                (Set.indicator_nonneg
                  (fun _ _ => zero_le_one) u))
    _ = 2 * w := by
          rw [hmajorant]
          rw [MeasureTheory.integral_add
            ((MeasureTheory.integrable_indicator_iff measurableSet_Icc).mpr
              (MeasureTheory.integrableOn_const
                (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)))
            ((MeasureTheory.integrable_indicator_iff measurableSet_Icc).mpr
              (MeasureTheory.integrableOn_const
                (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)))]
          rw [MeasureTheory.integral_indicator_one measurableSet_Icc,
            MeasureTheory.integral_indicator_one measurableSet_Icc,
            MeasureTheory.measureReal_def, MeasureTheory.measureReal_def,
            Real.volume_Icc, Real.volume_Icc,
            ENNReal.toReal_ofReal (by linarith),
            ENNReal.toReal_ofReal (by linarith)]
          ring

/-- Real Fourier transform of the squared admissible window is its cosine
integral.  Evenness is not needed for this real-part identity. -/
theorem VPhiR_eq_cos_integral
    {v : ℝ → ℝ} {L w c r : ℝ}
    (hW : AdmWindow v L w c) :
    AdmWindow.VPhiR v r
      = ∫ u, v u ^ 2 * Real.cos (r * u) := by
  have hexp : Continuous
      (fun u : ℝ => Complex.exp
        (Complex.I * (r : ℂ) * (u : ℂ))) := by
    fun_prop
  have hcont : Continuous
      (fun u : ℝ => (((v u) ^ 2 : ℝ) : ℂ)
        * Complex.exp (Complex.I * (r : ℂ) * (u : ℂ))) :=
    hW.vSqC_continuous.mul hexp
  have hint : Integrable
      (fun u : ℝ => (((v u) ^ 2 : ℝ) : ℂ)
        * Complex.exp (Complex.I * (r : ℂ) * (u : ℂ))) :=
    hcont.integrable_of_hasCompactSupport
      hW.vSqC_hasCompactSupport.mul_right
  unfold AdmWindow.VPhiR AdmWindow.VPhi
  rw [paperFT_def]
  calc
    (∫ u, (((v u) ^ 2 : ℝ) : ℂ)
        * Complex.exp (Complex.I * (r : ℂ) * (u : ℂ))).re
        = ∫ u, ((((v u) ^ 2 : ℝ) : ℂ)
          * Complex.exp (Complex.I * (r : ℂ) * (u : ℂ))).re := by
            exact (integral_re hint).symm
    _ = ∫ u, v u ^ 2 * Real.cos (r * u) := by
      refine integral_congr_ae ?_
      filter_upwards with u
      simp [Complex.mul_re, Complex.exp_re]

/-- Frequency-uniform two-ramp comparison for the squared D-window. -/
theorem ramp_cos_integral_close
    {rho : ℝ → ℝ} {lam L w r : ℝ}
    (hrho : TaperProfile rho)
    (hw : 1 ≤ w)
    (hwL : 8 * w ≤ L) :
    |(∫ u,
        (vStar lam (u / L) * Real.cos (r * u))
          * Taper.phi rho L w u ^ 2)
        - ∫ u in Set.Icc (-(L / 2)) (L / 2),
            vStar lam (u / L) * Real.cos (r * u)|
      ≤ 2 * w := by
  have hw0 : 0 < w := by linarith
  have hL : 0 < L := by linarith
  have h2w : 2 * w ≤ L := by linarith
  apply edge_estimate_public hL hw0 h2w
  · intro u
    rw [abs_mul]
    calc
      |vStar lam (u / L)| * |Real.cos (r * u)|
          ≤ 1 * 1 := by
            apply mul_le_mul
              (by unfold vStar; exact Real.abs_cos_le_one _)
              (Real.abs_cos_le_one _)
              (abs_nonneg _) zero_le_one
      _ = 1 := mul_one 1
  · intro u
    positivity
  · intro u
    calc
      Taper.phi rho L w u ^ 2 ≤ 1 ^ 2 :=
        pow_le_pow_left₀
          (Taper.phi_nonneg hrho u)
          (Taper.phi_le_one hrho u) 2
      _ = 1 := one_pow 2
  · intro u hu
    rw [Taper.phi_eq_one hrho hw0 hu, one_pow]
  · intro u hu
    rw [Taper.phi_eq_zero hrho hw0 hu,
      zero_pow two_ne_zero]
  · exact (Taper.phi_continuous hrho hw0 h2w).pow 2
  · unfold vStar
    fun_prop

/-- Same estimate written with the actual D-window squared. -/
theorem phiD_sq_cos_integral_close
    {rho : ℝ → ℝ} {lam L w r : ℝ}
    (hrho : TaperProfile rho)
    (hlam0 : 0 < lam)
    (hlam1 : lam ≤ 1)
    (hw : 1 ≤ w)
    (hwL : 8 * w ≤ L) :
    |(∫ u, phiD rho lam L w u ^ 2 * Real.cos (r * u))
        - ∫ u in Set.Icc (-(L / 2)) (L / 2),
            vStar lam (u / L) * Real.cos (r * u)|
      ≤ 2 * w := by
  have hw0 : 0 < w := by linarith
  have h2w : 2 * w ≤ L := by linarith
  have hsq := phiD_sq_eq hrho hlam0 hlam1 hw0 h2w
  have hfun :
      (fun u => phiD rho lam L w u ^ 2 * Real.cos (r * u))
        = fun u =>
            (vStar lam (u / L) * Real.cos (r * u))
              * Taper.phi rho L w u ^ 2 := by
    funext u
    rw [congrFun hsq u]
    ring
  rw [hfun]
  exact ramp_cos_integral_close hrho hw hwL

end Zeta23.GapMatching.DWindowRampEstimate
