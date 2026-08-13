/-
Copyright (c) 2026.
SPDX-License-Identifier: Apache-2.0

Scale and parity identities connecting the physical D-window separation to
the dimensionless one-band Montgomery--Taylor profile.
-/
import Zeta23.GapMatching.OneBandSharpProfile

open Set Real MeasureTheory

noncomputable section

namespace Zeta23.GapMatching.OneBandSharpScaling

open Zeta23
open Zeta23.ThmD
open Zeta23.GapMatching.DWindowProfileAlgebra
open Zeta23.GapMatching.OneBandSharpProfile
open Zeta23.GapMatching.OneBandPotentialSafeNumerics

/-- The sharp overlap is even in its frequency argument. -/
theorem sharpOverlap_neg (lam L r : ℝ) :
    sharpOverlap lam L (-r) = sharpOverlap lam L r := by
  unfold sharpOverlap
  congr 1
  apply MeasureTheory.setIntegral_congr_fun measurableSet_Icc
  intro u hu
  rw [neg_mul, Real.cos_neg]

/-- Scaling the physical support interval to `[-1/2,1/2]` turns frequency
`r` into the dimensionless frequency `L*r`. -/
theorem sharpOverlap_scale
    {lam L r : ℝ} (hL : 0 < L) :
    sharpOverlap lam L r = sharpOverlap lam 1 (L * r) := by
  unfold sharpOverlap
  have hab : -(L / 2) ≤ L / 2 := by linarith
  have hscaled :
      (∫ u in Set.Icc (-(L / 2)) (L / 2),
          vStar lam (u / L) * Real.cos (r * u))
        = L *
          ∫ s in Set.Icc (-(1 / 2 : ℝ)) (1 / 2),
            vStar lam s * Real.cos ((L * r) * s) := by
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le hab]
    have hcomp := intervalIntegral.integral_comp_div
      (f := fun s : ℝ =>
        vStar lam s * Real.cos ((L * r) * s)) hL.ne'
    rw [smul_eq_mul] at hcomp
    have hlo : -(L / 2) / L = -(1 / 2 : ℝ) := by
      field_simp [hL.ne']
      ring
    have hhi : (L / 2) / L = (1 / 2 : ℝ) := by
      field_simp [hL.ne']
      ring
    rw [hlo, hhi] at hcomp
    convert hcomp using 1
    · apply intervalIntegral.integral_congr
      intro u hu
      congr 1
      ring
    · ring
  rw [hscaled]
  field_simp [hL.ne']
  ring

/-- Physical separation corresponding to a normalized positive gap `x`. -/
theorem sharpOverlap_physical_gap
    {L x : ℝ} (hL : 0 < L) :
    sharpOverlap lam L (-(2 * Real.pi * x) / L) = profile x := by
  rw [sharpOverlap_neg, sharpOverlap_scale hL]
  unfold profile
  congr 2
  field_simp [hL.ne']
  ring

end Zeta23.GapMatching.OneBandSharpScaling
