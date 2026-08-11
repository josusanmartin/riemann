/-
Copyright (c) 2026.
SPDX-License-Identifier: Apache-2.0

Error-explicit zeta seam for the two-band, three-state gap potential.
-/
import Zeta23.GapMatching.FiniteStateGapPotential
import Zeta23.GapMatching.TwoBandPotentialSafeNumerics
import Zeta23.GapMatching.GapMatchingZetaSeam

open Filter Asymptotics Topology Real RHLinalg

noncomputable section

namespace Zeta23.GapMatching.TwoBandPotentialAnalyticBridge

open Zeta23
open Zeta23.Assembly
open Zeta23.GapMatching.FiniteStateGapPotential
open Zeta23.GapMatching.TwoBandPotentialSafeNumerics
open Zeta23.GapMatching.GapMatchingZetaSeam

structure TwoBandWordAt (Z : ZeroConfig) (T : ℝ) where
  gaps : List (GapDatum State)
  centralSimple : ℝ
  W : ℝ
  guardError : ℝ
  countError : ℝ
  lengthError : ℝ
  valid : ValidPath A B State.good phi State.good gaps
  guard_lower :
    (Z.N0s T (2 * T) : ℝ) - guardError ≤ centralSimple
  count_lower : centralSimple - countError ≤ (gaps.length : ℝ)
  length_upper : totalLength gaps ≤
    (Z.N T (2 * T) : ℝ) + lengthError
  candidate_le : candidateWeight State.good State.good gaps ≤ W

def wordError {Z : ZeroConfig} {T : ℝ} (G : TwoBandWordAt Z T) : ℝ :=
  A * G.guardError + A * G.countError + B * G.lengthError + boundary

theorem word_weight_lower
    {Z : ZeroConfig} {T : ℝ} (G : TwoBandWordAt Z T) :
    A * (Z.N0s T (2 * T) : ℝ)
        - B * (Z.N T (2 * T) : ℝ) - wordError G
      ≤ G.W := by
  have hA0 : 0 ≤ A := parameter_ranges.1.le
  have hB0 : 0 ≤ B := parameter_ranges.2.2.1
  have hmain := candidateWeight_lower_with_errors
    (State := State)
    State.good phi hA0 hB0 rfl potential_boundary
    G.gaps G.valid rfl G.guard_lower G.count_lower
    G.length_upper G.candidate_le
  simpa [wordError] using hmain

/-- This package contains actual paths, so it lives in `Type`, not `Prop`. -/
structure TwoBandWordFamily (Z : ZeroConfig) (P : Params)
    (energy error : ℝ → ℝ) where
  data : ∀ T, TwoBandWordAt Z T
  core : ∀ᶠ T in atTop, MatchingCoreAt Z P T (energy T)
  selected : ∀ᶠ T in atTop, (data T).W ≤ 2 * energy T
  error_eq : ∀ T, error T = wordError (data T)
  error_small : error =o[atTop] (fun T => (Z.N T (2 * T) : ℝ))

theorem TwoBandWordFamily.toAnalyticInput
    {Z : ZeroConfig} {P : Params} {energy error : ℝ → ℝ}
    (H : TwoBandWordFamily Z P energy error) :
    GapMatchingAnalyticInput Z P energy error A 1 (B / (2 * A)) where
  core := H.core
  energy_lower := by
    have hA : A ≠ 0 := ne_of_gt parameter_ranges.1
    filter_upwards [H.selected] with T hselected
    rw [H.error_eq T]
    have hlower := word_weight_lower (H.data T)
    have hid :
        A * (1 * (Z.N0s T (2 * T) : ℝ)
            - 2 * (B / (2 * A)) * (Z.N T (2 * T) : ℝ))
          = A * (Z.N0s T (2 * T) : ℝ)
            - B * (Z.N T (2 * T) : ℝ) := by
      field_simp [hA]
      ring
    rw [hid]
    exact hlower.trans hselected
  error_small := H.error_small

theorem simple_density_6725391
    (Z : ZeroConfig) (P : Params)
    (energy error theta0 : ℝ → ℝ)
    (hwords : TwoBandWordFamily Z P energy error)
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
        ≤ ((2 - deltaLower) + delta) * (Z.N T (2 * T) : ℝ)) :
    ∀ epsilon > 0, ∃ T0 : ℝ, ∀ T ≥ T0,
      (advertised - epsilon) * (Z.N T (2 * T) : ℝ)
        ≤ (Z.N0s T (2 * T) : ℝ) := by
  have hA0 : 0 < A := parameter_ranges.1
  have hden : A * 1 < 1 := by simpa using parameter_ranges.2.1
  have hmain := simple_density_fixed_point
    Z P (2 - deltaLower) energy error theta0
    A 1 (B / (2 * A)) hwords.toAnalyticInput
    hTail ha hL hB0 hBto hNII_o hNtop htrace hfrob hden
  intro epsilon hepsilon
  obtain ⟨T0, hT0⟩ := hmain epsilon hepsilon
  refine ⟨T0, fun T hT => ?_⟩
  have h := hT0 T hT
  have hN : 0 ≤ (Z.N T (2 * T) : ℝ) := Nat.cast_nonneg _
  have hcoef :
      advertised - epsilon
        ≤ (((deltaLower - B) / (1 - A)) - epsilon) := by
    exact sub_le_sub_right advertised_lt_exact.le epsilon
  have hform :
      ((deltaLower - 2 * A * (B / (2 * A))) / (1 - A * 1))
        = (deltaLower - B) / (1 - A) := by
    field_simp [ne_of_gt hA0]
    ring
  rw [hform] at h
  exact (mul_le_mul_of_nonneg_right hcoef hN).trans h

end Zeta23.GapMatching.TwoBandPotentialAnalyticBridge
