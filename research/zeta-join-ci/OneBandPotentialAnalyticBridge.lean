/-
Copyright (c) 2026.
SPDX-License-Identifier: Apache-2.0

Error-explicit zeta seam for the conservative one-band potential.
-/
import Zeta23.GapMatching.FiniteStateGapPotential
import Zeta23.GapMatching.OneBandPotentialSafeNumerics
import Zeta23.GapMatching.GapMatchingZetaSeam

open Filter Asymptotics Topology Real RHLinalg

noncomputable section

namespace Zeta23.GapMatching.OneBandPotentialAnalyticBridge

open Zeta23
open Zeta23.Assembly
open Zeta23.GapMatching.FiniteStateGapPotential
open Zeta23.GapMatching.OneBandPotentialSafeNumerics
open Zeta23.GapMatching.GapMatchingZetaSeam

structure OneBandWordAt (Z : ZeroConfig) (T : ℝ) where
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

def wordError {Z : ZeroConfig} {T : ℝ} (G : OneBandWordAt Z T) : ℝ :=
  A * G.guardError + A * G.countError + B * G.lengthError + boundary

theorem word_weight_lower
    {Z : ZeroConfig} {T : ℝ} (G : OneBandWordAt Z T) :
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

structure OneBandWordFamily (Z : ZeroConfig) (P : Params)
    (energy error : ℝ → ℝ) : Prop where
  data : ∀ T, OneBandWordAt Z T
  core : ∀ᶠ T in atTop, MatchingCoreAt Z P T (energy T)
  selected : ∀ᶠ T in atTop, (data T).W ≤ 2 * energy T
  error_eq : ∀ T, error T = wordError (data T)
  error_small : error =o[atTop] (fun T => (Z.N T (2 * T) : ℝ))

theorem OneBandWordFamily.toAnalyticInput
    {Z : ZeroConfig} {P : Params} {energy error : ℝ → ℝ}
    (H : OneBandWordFamily Z P energy error) :
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

end Zeta23.GapMatching.OneBandPotentialAnalyticBridge
