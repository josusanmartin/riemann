/-
Copyright (c) 2026.
SPDX-License-Identifier: Apache-2.0

Quantitative comparison of a finite admissible-window Gram overlap with its
full Poisson sum, under explicit left and right guard assumptions.
-/
import Zeta23.GapMatching.DWindowFourierTail
import Zeta23.GapMatching.FiniteBlockApproximation
import Zeta23.ThmD.WindowCore

open Finset Real

noncomputable section

namespace Zeta23.GapMatching.DWindowFiniteGridApprox

open Zeta23
open Zeta23.AdmWindow
open Zeta23.GapMatching.DWindowFourierTail
open Zeta23.GapMatching.FiniteGridTailAlgebra
open Zeta23.GapMatching.FiniteBlockApproximation

/-- One normalized term of the integer Gabor overlap. -/
def normalizedTerm
    (v : ℝ → ℝ) (L T tau tau' : ℝ) (k : ℤ) : ℝ :=
  (av v L * L ^ 2)⁻¹ *
    (vHatR v (tau - (T + k * (2 * Real.pi / L)))
      * vHatR v (tau' - (T + k * (2 * Real.pi / L))))

/-- The exact normalized full-grid value in the form produced by Poisson. -/
def normalizedFullOverlap
    (v : ℝ → ℝ) (L tau tau' : ℝ) : ℝ :=
  (av v L * L ^ 2)⁻¹ * (L * VPhiR v (tau - tau'))

/-- The normalized finite block `k = 0, ..., d-1`. -/
def finiteNormalizedOverlap
    (v : ℝ → ℝ) (L T : ℝ) (d : ℕ)
    (tau tau' : ℝ) : ℝ :=
  finiteBlock (normalizedTerm v L T tau tau') d

/-- Raw square-tail majorant supplied by inverse-fourth Fourier decay. -/
def rawTailMajorant (c w D h : ℝ) : ℝ :=
  (c / w) ^ 2 * ((D ^ 4)⁻¹ + (D ^ 3)⁻¹ / (3 * h))

/-- The full Poisson identity for `normalizedTerm`. -/
theorem hasSum_normalizedTerm
    {v : ℝ → ℝ} {L w c : ℝ}
    (hW : AdmWindow v L w c)
    (T tau tau' : ℝ) :
    HasSum (normalizedTerm v L T tau tau')
      (normalizedFullOverlap v L tau tau') := by
  have hraw := hW.hasSum_vHatR_mul T tau tau'
  have hscaled :
      HasSum
        (fun k : ℤ =>
          (av v L * L ^ 2)⁻¹ •
            (vHatR v (tau - (T + k * (2 * Real.pi / L)))
              * vHatR v (tau' - (T + k * (2 * Real.pi / L)))))
        ((av v L * L ^ 2)⁻¹ •
          (L * VPhiR v (tau - tau'))) :=
    HasSum.const_smul (av v L * L ^ 2)⁻¹ hraw
  simpa only [normalizedTerm, normalizedFullOverlap, smul_eq_mul]
    using hscaled

/-- A finite normalized overlap is close to the full Poisson overlap whenever
both evaluation points are at least `D` from each omitted side of the grid. -/
theorem finiteNormalizedOverlap_close
    {v : ℝ → ℝ} {L w c T tau tau' D : ℝ} {d : ℕ}
    (hW : AdmWindow v L w c)
    (ha : 0 < av v L)
    (hD : 0 < D)
    (hleftTau : T + D ≤ tau)
    (hleftTau' : T + D ≤ tau')
    (hrightTau : tau + D ≤ T + d * (2 * Real.pi / L))
    (hrightTau' : tau' + D ≤ T + d * (2 * Real.pi / L)) :
    |finiteNormalizedOverlap v L T d tau tau'
        - normalizedFullOverlap v L tau tau'|
      ≤ 2 * ((av v L * L ^ 2)⁻¹
        * rawTailMajorant c w D (2 * Real.pi / L)) := by
  let h : ℝ := 2 * Real.pi / L
  have hh : 0 < h := by
    dsimp [h]
    positivity
  let scale : ℝ := (av v L * L ^ 2)⁻¹
  have hscale : 0 ≤ scale := by
    dsimp [scale]
    positivity
  let q : ℝ := rawTailMajorant c w D h

  let xLeft : ℕ → ℝ := fun n =>
    vHatR v (tau - (T - (n + 1) * h))
  let yLeft : ℕ → ℝ := fun n =>
    vHatR v (tau' - (T - (n + 1) * h))
  have hxLeftArg : ∀ n, D + n * h ≤
      |tau - (T - (n + 1) * h)| :=
    left_argument_lower hD.le hh.le hleftTau
  have hyLeftArg : ∀ n, D + n * h ≤
      |tau' - (T - (n + 1) * h)| :=
    left_argument_lower hD.le hh.le hleftTau'
  have hxLeft : Summable (fun n => xLeft n ^ 2) :=
    summable_vHatR_sq hW hD hh _ hxLeftArg
  have hyLeft : Summable (fun n => yLeft n ^ 2) :=
    summable_vHatR_sq hW hD hh _ hyLeftArg
  have hxLeftQ : ∑' n, xLeft n ^ 2 ≤ q := by
    simpa [xLeft, q, rawTailMajorant] using
      (tsum_vHatR_sq_le hW hD hh _ hxLeftArg)
  have hyLeftQ : ∑' n, yLeft n ^ 2 ≤ q := by
    simpa [yLeft, q, rawTailMajorant] using
      (tsum_vHatR_sq_le hW hD hh _ hyLeftArg)
  have hleftRaw :
      |∑' n, scale * (xLeft n * yLeft n)| ≤ scale * q := by
    simpa only [Real.norm_eq_abs] using
      (norm_tsum_const_mul_mul_le_same scale hscale
        xLeft yLeft hxLeft hyLeft hxLeftQ hyLeftQ)

  let xRight : ℕ → ℝ := fun n =>
    vHatR v (tau - (T + (d + n) * h))
  let yRight : ℕ → ℝ := fun n =>
    vHatR v (tau' - (T + (d + n) * h))
  have hxRightArg : ∀ n, D + n * h ≤
      |tau - (T + (d + n) * h)| :=
    right_argument_lower hD.le hh.le hrightTau
  have hyRightArg : ∀ n, D + n * h ≤
      |tau' - (T + (d + n) * h)| :=
    right_argument_lower hD.le hh.le hrightTau'
  have hxRight : Summable (fun n => xRight n ^ 2) :=
    summable_vHatR_sq hW hD hh _ hxRightArg
  have hyRight : Summable (fun n => yRight n ^ 2) :=
    summable_vHatR_sq hW hD hh _ hyRightArg
  have hxRightQ : ∑' n, xRight n ^ 2 ≤ q := by
    simpa [xRight, q, rawTailMajorant] using
      (tsum_vHatR_sq_le hW hD hh _ hxRightArg)
  have hyRightQ : ∑' n, yRight n ^ 2 ≤ q := by
    simpa [yRight, q, rawTailMajorant] using
      (tsum_vHatR_sq_le hW hD hh _ hyRightArg)
  have hrightRaw :
      |∑' n, scale * (xRight n * yRight n)| ≤ scale * q := by
    simpa only [Real.norm_eq_abs] using
      (norm_tsum_const_mul_mul_le_same scale hscale
        xRight yRight hxRight hyRight hxRightQ hyRightQ)

  let f : ℤ → ℝ := normalizedTerm v L T tau tau'
  have hfull : HasSum f (normalizedFullOverlap v L tau tau') :=
    hasSum_normalizedTerm hW T tau tau'
  have hleft :
      |∑' n : ℕ, f (-((n : ℤ) + 1))| ≤ scale * q := by
    simpa [f, normalizedTerm, scale, xLeft, yLeft, h] using hleftRaw
  have hright :
      |∑' n : ℕ, f ((n + d : ℕ) : ℤ)| ≤ scale * q := by
    simpa [f, normalizedTerm, scale, xRight, yRight, h,
      Nat.cast_add, Nat.cast_ofNat] using hrightRaw

  have hfinite := abs_finiteBlock_sub_le_same hfull d hleft hright
  simpa [finiteNormalizedOverlap, f, scale, q, h,
    rawTailMajorant] using hfinite

end Zeta23.GapMatching.DWindowFiniteGridApprox
