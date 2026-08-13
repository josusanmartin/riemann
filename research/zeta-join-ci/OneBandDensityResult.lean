/-
Copyright (c) 2026.
SPDX-License-Identifier: Apache-2.0

Conservative fixed-point conclusion for the one-band word family.
-/
import Zeta23.GapMatching.OneBandPotentialAnalyticBridge
import Zeta23.GapMatching.CandidateStrictImprovementTight

open Filter Asymptotics Topology Real RHLinalg

noncomputable section

namespace Zeta23.GapMatching.OneBandDensityResult

open Zeta23
open Zeta23.Assembly
open Zeta23.GapMatching.GapMatchingZetaSeam
open Zeta23.GapMatching.OneBandPotentialSafeNumerics
open Zeta23.GapMatching.OneBandPotentialAnalyticBridge

/-- Rational baseline safely below the exact Montgomery--Taylor limit. -/
def baseline : ℝ := 0.67250069

/-- Live candidate targeted by the conservative proof. -/
def candidate : ℝ := 0.672500708

/-- Exact rational fixed-point headroom. -/
theorem candidate_lt_fixed_point :
    candidate < (baseline - B) / (1 - A) := by
  have hden : 0 < 1 - A := by
    nlinarith [parameter_ranges.1, parameter_ranges.2.1]
  rw [lt_div_iff₀ hden]
  norm_num [candidate, baseline, A, B, p, j, badLeft]

/-- A one-band word family improves the simple critical-line density beyond
`candidate`. -/
theorem simple_density_candidate
    (Z : ZeroConfig) (P : Params)
    (energy error theta0 : ℝ → ℝ)
    (hwords : OneBandWordFamily Z P energy error)
    (hTail : ∀ᶠ T in atTop, TailInputs Z P T (theta0 T))
    (ha : ∀ᶠ T in atTop, 0 < P.a T)
    (hL : ∀ᶠ T in atTop, 0 < P.L T)
    (hB0 : ∀ᶠ T in atTop, 0 ≤ theta0 T / (P.a T * P.L T))
    (hBto : Tendsto (fun T => theta0 T / (P.a T * P.L T)) atTop (𝓝 0))
    (hNII_o : (fun T => (NII Z T : ℝ))
      =o[atTop] (fun T => (Z.N T (2 * T) : ℝ)))
    (hNtop : Tendsto (fun T => (Z.N T (2 * T) : ℝ)) atTop atTop)
    (htrace : ∀ delta > (0 : ℝ), ∀ᶠ T in atTop,
      (1 - delta) * (Z.N T (2 * T) : ℝ)
        ≤ rtrace (P.hat T (Z.Gz P T)))
    (hfrob : ∀ delta > (0 : ℝ), ∀ᶠ T in atTop,
      frobSq (P.hat T (Z.Gz P T))
        ≤ ((2 - baseline) + delta) * (Z.N T (2 * T) : ℝ)) :
    ∀ epsilon > 0, ∃ T0 : ℝ, ∀ T ≥ T0,
      (candidate - epsilon) * (Z.N T (2 * T) : ℝ)
        ≤ (Z.N0s T (2 * T) : ℝ) := by
  have hden : A * 1 < 1 := by
    simpa using parameter_ranges.2.1
  have hmain := simple_density_fixed_point
    Z P (2 - baseline) energy error theta0
    A 1 (B / (2 * A)) hwords.toAnalyticInput
    hTail ha hL hB0 hBto hNII_o hNtop htrace hfrob hden
  intro epsilon hepsilon
  obtain ⟨T0, hT0⟩ := hmain epsilon hepsilon
  refine ⟨T0, fun T hT => ?_⟩
  have h := hT0 T hT
  have hN : 0 ≤ (Z.N T (2 * T) : ℝ) := Nat.cast_nonneg _
  have hcoef :
      candidate - epsilon
        ≤ (((baseline - B) / (1 - A)) - epsilon) := by
    exact sub_le_sub_right candidate_lt_fixed_point.le epsilon
  have hA : A ≠ 0 := ne_of_gt parameter_ranges.1
  have hform :
      ((baseline - 2 * A * (B / (2 * A))) / (1 - A * 1))
        = (baseline - B) / (1 - A) := by
    field_simp [hA]
    ring
  rw [hform] at h
  exact (mul_le_mul_of_nonneg_right hcoef hN).trans h

end Zeta23.GapMatching.OneBandDensityResult
