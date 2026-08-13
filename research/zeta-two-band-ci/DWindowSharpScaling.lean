/-
Copyright (c) 2026.
SPDX-License-Identifier: Apache-2.0

Scale invariance of the sharp Montgomery--Taylor overlap.
-/
import Zeta23.GapMatching.DWindowProfileAlgebra

open Real Set

noncomputable section

namespace Zeta23.GapMatching.DWindowSharpScaling

open Zeta23
open Zeta23.ThmD
open Zeta23.GapMatching.DWindowProfileAlgebra

/-- Rescaling the sharp window to unit support multiplies the physical
frequency by the support length. -/
theorem sharpOverlap_scale
    {lam L r : ℝ} (hL : 0 < L) :
    sharpOverlap lam L r = sharpOverlap lam 1 (r * L) := by
  unfold sharpOverlap
  have hnum :
      (∫ u in Set.Icc (-(L / 2)) (L / 2),
          vStar lam (u / L) * Real.cos (r * u))
        = L * ∫ s in Set.Icc (-(1 : ℝ) / 2) (1 / 2),
            vStar lam s * Real.cos ((r * L) * s) := by
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le
        (by linarith : -(L / 2) ≤ L / 2)]
    have hchange := intervalIntegral.integral_comp_div
      (f := fun s : ℝ =>
        vStar lam s * Real.cos ((r * L) * s))
      (a := -(L / 2)) (b := L / 2) hL.ne'
    simp only [smul_eq_mul] at hchange
    have hlo : -(L / 2) / L = -(1 : ℝ) / 2 := by
      field_simp [hL.ne']
    have hhi : (L / 2) / L = (1 : ℝ) / 2 := by
      field_simp [hL.ne']
    rw [hlo, hhi] at hchange
    calc
      (∫ u in -(L / 2)..L / 2,
          vStar lam (u / L) * Real.cos (r * u))
          = ∫ u in -(L / 2)..L / 2,
              (fun s : ℝ =>
                vStar lam s * Real.cos ((r * L) * s)) (u / L) := by
              apply intervalIntegral.integral_congr
              intro u
              dsimp
              congr 1
              have hr : (r * L) * (u / L) = r * u := by
                field_simp [hL.ne']
              rw [hr]
      _ = L * ∫ s in -(1 : ℝ) / 2..(1 / 2),
              vStar lam s * Real.cos ((r * L) * s) := hchange
      _ = L * ∫ s in Set.Icc (-(1 : ℝ) / 2) (1 / 2),
              vStar lam s * Real.cos ((r * L) * s) := by
              congr 1
              rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
                ← intervalIntegral.integral_of_le
                  (by norm_num : (-(1 : ℝ) / 2) ≤ 1 / 2)]
  rw [hnum]
  field_simp [hL.ne']
  ring

/-- The sharp overlap is even in physical frequency. -/
theorem sharpOverlap_neg
    (lam L r : ℝ) :
    sharpOverlap lam L (-r) = sharpOverlap lam L r := by
  unfold sharpOverlap
  congr 2
  apply MeasureTheory.setIntegral_congr_fun measurableSet_Icc
  intro u hu
  rw [neg_mul, Real.cos_neg]

end Zeta23.GapMatching.DWindowSharpScaling
