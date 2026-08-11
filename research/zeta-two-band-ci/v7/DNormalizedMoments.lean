/-
Copyright (c) 2026.
SPDX-License-Identifier: Apache-2.0

Normalized first- and second-moment bounds for the height-dependent
Montgomery--Taylor family `P.atD T`.

The upstream `thmD_mult2_abstract` proves these estimates internally.  This
module exports them as a reusable interface so an additive gap-matching bonus
can be passed through a separate scalar certificate without pretending that
`P.atD T` is one fixed `Params` object.
-/
import Zeta23.ThmD.Mult

open Filter Asymptotics Topology Real RHLinalg

noncomputable section

namespace Zeta23.GapMatching.DNormalizedMoments

open Zeta23
open Zeta23.Assembly
open Zeta23.ThmD

/-- The D-trace package and its ratio limit give normalized trace and
Frobenius bounds with limiting second-moment constant `c⁻¹`. -/
theorem normalized_moment_bounds
    (Z : ZeroConfig) (H : PaperInputs Z)
    (P : Params) (hP : P.Valid) (hlam : P.lam < 1)
    (aT bT JT trG trG2 : ℝ → ℝ)
    (hTr : TracesBoundsD P aT bT JT trG trG2
      (fun T => (Z.N T (2 * T) : ℝ)))
    {c : ℝ} (hc0 : 0 < c)
    (hc : Tendsto
      (fun T => cRatio (P.lam1 T) (aT T) (bT T) (JT T))
      atTop (𝓝 c))
    (ha : ∀ᶠ T in atTop, 1 / 2 ≤ aT T ∧ aT T ≤ 1)
    (hcalE : Tendsto P.calE atTop (𝓝 0)) :
    (∀ δ > (0 : ℝ), ∀ᶠ T in atTop,
      (1 - δ) * (Z.N T (2 * T) : ℝ)
        ≤ (aT T * P.L T)⁻¹ * trG T) ∧
    (∀ δ > (0 : ℝ), ∀ᶠ T in atTop,
      ((aT T * P.L T)⁻¹) ^ 2 * trG2 T
        ≤ (c⁻¹ + δ) * (Z.N T (2 * T) : ℝ)) := by
  have hlam0 := hP.lam_pos
  have hlam1 : P.lam ≤ 1 := hlam.le
  obtain ⟨C₁, hC₁, T₁, htr1⟩ := hTr.tr1
  obtain ⟨C₂, hC₂, T₂, hfr2⟩ := hTr.frhat

  set N : ℝ → ℝ := fun T => (Z.N T (2 * T) : ℝ) with hNdef
  set cinv : ℝ → ℝ :=
    fun T => (cRatio (P.lam1 T) (aT T) (bT T) (JT T))⁻¹
    with hcinv
  set R₁ : ℝ → ℝ :=
    fun T => C₁ * Real.sqrt (P.X T) / aT T
    with hR₁
  set R₂ : ℝ → ℝ :=
    fun T => C₂ * P.calE T * (cinv T * N T)
    with hR₂

  have hNtop : Tendsto N atTop atTop := tendsto_N_atTop Z H.RvM
  have hcinv_to : Tendsto cinv atTop (𝓝 c⁻¹) := hc.inv₀ hc0.ne'

  have o1 : R₁ =o[atTop] N := by
    have hbd : (fun T => C₁ / aT T) =O[atTop] (fun _ => (1 : ℝ)) := by
      refine isBigO_one_of_abs_le (C := 2 * C₁) ?_
      filter_upwards [ha] with T haT
      rw [abs_of_nonneg (div_nonneg hC₁.le (by linarith [haT.1]))]
      rw [div_le_iff₀ (by linarith [haT.1])]
      nlinarith [haT.1]
    have h := isLittleO_of_bdd_mul hbd
      (isLittleO_N_of_isLittleO_Tl Z H.RvM
        (isLittleO_sqrtX_Tl P hlam0 hlam1))
    exact h.congr_left fun T => by
      simp only [hR₁]
      ring

  have htrace : ∀ δ > (0 : ℝ), ∀ᶠ T in atTop,
      (1 - δ) * N T ≤ (aT T * P.L T)⁻¹ * trG T := by
    intro δ hδ
    have hsmall := o1.def hδ
    filter_upwards [ha, eventually_ge_atTop T₁, hsmall,
      hNtop.eventually_ge_atTop 0, eventually_l_pos]
      with T haT hT₁ hsmallT hNT hlT
    have hapos : 0 < aT T := by linarith [haT.1]
    have hLpos : 0 < P.L T := by
      simp only [Params.L]
      positivity
    have htr :
        |(aT T * P.L T)⁻¹ * trG T - N T| ≤ R₁ T :=
      trGhat_sub_N_le hapos hLpos
        (by simpa only [hNdef] using htr1 T hT₁)
    have hRnonneg : 0 ≤ R₁ T := by
      simp only [hR₁]
      positivity
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg hRnonneg, abs_of_nonneg hNT] at hsmallT
    have hlow := (abs_le.mp htr).1
    simp only [hNdef] at hlow hsmallT ⊢
    nlinarith

  have hcinv_bd : ∀ᶠ T in atTop,
      0 ≤ cinv T ∧ cinv T ≤ 2 * c⁻¹ := by
    have hcpos : (0 : ℝ) < c⁻¹ := inv_pos.mpr hc0
    filter_upwards [
      hcinv_to.eventually (eventually_ge_nhds hcpos),
      hcinv_to.eventually
        (eventually_le_nhds (show c⁻¹ < 2 * c⁻¹ by linarith))]
      with T hlo hhi
    exact ⟨hlo, hhi⟩

  have hcinvO : cinv =O[atTop] (fun _ => (1 : ℝ)) := by
    refine isBigO_one_of_abs_le (C := 2 * c⁻¹) ?_
    filter_upwards [hcinv_bd] with T hT
    rw [abs_of_nonneg hT.1]
    exact hT.2

  have o2 : R₂ =o[atTop] N := by
    have hcE0 : Tendsto (fun T => C₂ * P.calE T) atTop (𝓝 0) := by
      simpa using hcalE.const_mul C₂
    have i1 : (fun T => cinv T * N T) =O[atTop] N := by
      have h := hcinvO.mul (isBigO_refl N atTop)
      simpa using h
    have h := ((isLittleO_one_iff ℝ).2 hcE0).mul_isBigO i1
    refine (h.congr_left fun T => ?_).congr_right fun T => by simp
    simp only [hR₂]

  have hfrob : ∀ δ > (0 : ℝ), ∀ᶠ T in atTop,
      ((aT T * P.L T)⁻¹) ^ 2 * trG2 T
        ≤ (c⁻¹ + δ) * N T := by
    intro δ hδ
    set η : ℝ := δ / 2 with hηdef
    have hη : 0 < η := by
      simp only [hηdef]
      linarith

    have hclose : ∀ᶠ T in atTop, |cinv T - c⁻¹| ≤ η := by
      filter_upwards [
        hcinv_to.eventually
          (eventually_ge_nhds
            (show c⁻¹ - η < c⁻¹ by linarith)),
        hcinv_to.eventually
          (eventually_le_nhds
            (show c⁻¹ < c⁻¹ + η by linarith))]
        with T hlo hhi
      rw [abs_le]
      constructor <;> linarith

    have hRsmall := o2.def hη
    filter_upwards [ha, eventually_ge_atTop T₂, hclose, hRsmall,
      hNtop.eventually_ge_atTop 0, hcinv_bd,
      eventually_calE_nonneg P hlam0
        (zero_le_one.trans hP.one_le_w), eventually_l_pos]
      with T haT hT₂ hcloseT hRsmallT hNT hcinvT hE0 hlT

    have hapos : 0 < aT T := by linarith [haT.1]
    have hLpos : 0 < P.L T := by
      simp only [Params.L]
      positivity

    have hfrb :
        ((aT T * P.L T)⁻¹) ^ 2 * trG2 T
          ≤ cinv T * N T + R₂ T := by
      have h := hfr2 T hT₂
      simp only at h
      have h1 :
          trG2 T / (aT T * P.L T) ^ 2 - cinv T * N T
            ≤ C₂ * P.calE T * (cinv T * N T) := by
        rw [← mul_assoc] at h
        exact le_trans
          (le_trans (le_max_left _ 0) (le_abs_self _)) h
      have heq :
          ((aT T * P.L T)⁻¹) ^ 2 * trG2 T
            = trG2 T / (aT T * P.L T) ^ 2 := by
        rw [inv_pow, div_eq_inv_mul]
      rw [heq]
      simp only [hR₂]
      linarith

    have hRnonneg : 0 ≤ R₂ T := by
      simp only [hR₂]
      have hcinvN : 0 ≤ cinv T * N T :=
        mul_nonneg hcinvT.1 hNT
      exact mul_nonneg (mul_nonneg hC₂.le hE0) hcinvN
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg hRnonneg, abs_of_nonneg hNT] at hRsmallT

    have hcinvle : cinv T ≤ c⁻¹ + η := by
      have := (abs_le.mp hcloseT).2
      linarith
    have hmul := mul_le_mul_of_nonneg_right hcinvle hNT
    have htarget :
        cinv T * N T + R₂ T ≤ (c⁻¹ + δ) * N T := by
      simp only [hηdef] at hmul hRsmallT ⊢
      nlinarith
    exact hfrb.trans htarget

  exact ⟨by simpa only [hNdef] using htrace,
    by simpa only [hNdef] using hfrob⟩

end Zeta23.GapMatching.DNormalizedMoments
