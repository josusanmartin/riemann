/-
Package large-height central-word witnesses into the all-height function shape
required by the asymptotic seam.  Witness-bearing structures live in `Type`,
not `Prop`, so no proof-irrelevance elimination is used.
-/
import Zeta23.GapMatching.OneBandCentralFamilyD

open Filter Asymptotics

noncomputable section

namespace Zeta23.GapMatching.EventualCentralFamilyD

open Zeta23
open Zeta23.GapMatching.FiniteStateGapPotential
open Zeta23.GapMatching.OneBandPotentialSafeNumerics
open Zeta23.GapMatching.OneBandCentralWordD
open Zeta23.GapMatching.OneBandCentralFamilyD
open Zeta23.GapMatching.GapMatchingZetaSeam

/-- Word/core witness at one large height. -/
structure HeightBundle (Z : ZeroConfig) (P : Params) (T : ℝ) where
  energy : ℝ
  word : CentralWordAt Z T
  core : MatchingCoreAt Z P T energy
  selected : word.W ≤ 2 * energy

/-- Trivial finite word used only below the large-height threshold. -/
def trivialWordAt (Z : ZeroConfig) (T : ℝ) : CentralWordAt Z T where
  gaps := []
  centralSimple := 0
  W := 0
  countError := 0
  lengthError := 0
  valid := by simp [ValidPath]
  count_lower := by simp
  length_upper := by simp
  candidate_le := by simp [candidateWeight]

/-- Large-height witness family plus exactly the asymptotic facts needed by
the additive endgame. -/
structure EventualCentralConstruction (Z : ZeroConfig) (P : Params)
    (simpleLower : ℝ) where
  threshold : ℝ
  bundle : ∀ T, threshold ≤ T → HeightBundle Z P T
  central_lower : ∀ᶠ T in atTop,
    simpleLower * (Z.N T (2 * T) : ℝ)
      ≤ (bundle T (by assumption)).word.centralSimple
  wordError_small :
    (fun T => if h : threshold ≤ T
      then wordError (bundle T h).word else 0)
      =o[atTop] (fun T => (Z.N T (2 * T) : ℝ))

/-- All-height selected energy. -/
def selectedEnergy
    {Z : ZeroConfig} {P : Params} {simpleLower : ℝ}
    (H : EventualCentralConstruction Z P simpleLower) (T : ℝ) : ℝ :=
  if h : H.threshold ≤ T then (H.bundle T h).energy else 0

/-- All-height word, trivial below the threshold. -/
def selectedWord
    {Z : ZeroConfig} {P : Params} {simpleLower : ℝ}
    (H : EventualCentralConstruction Z P simpleLower) (T : ℝ) :
    CentralWordAt Z T :=
  if h : H.threshold ≤ T then (H.bundle T h).word else trivialWordAt Z T

/-- All-height error attached to the selected word. -/
def selectedError
    {Z : ZeroConfig} {P : Params} {simpleLower : ℝ}
    (H : EventualCentralConstruction Z P simpleLower) (T : ℝ) : ℝ :=
  wordError (selectedWord H T)

/-- Convert eventual witness data to the abstract central family. -/
theorem EventualCentralConstruction.toCentralWordFamily
    {Z : ZeroConfig} {P : Params} {simpleLower : ℝ}
    (H : EventualCentralConstruction Z P simpleLower) :
    CentralWordFamily Z P
      (selectedEnergy H) (selectedError H) simpleLower where
  data := selectedWord H
  core := by
    filter_upwards [eventually_ge_atTop H.threshold] with T hT
    simp [selectedEnergy, hT]
    exact (H.bundle T hT).core
  selected := by
    filter_upwards [eventually_ge_atTop H.threshold] with T hT
    simp [selectedEnergy, selectedWord, hT]
    exact (H.bundle T hT).selected
  central_lower := by
    filter_upwards [H.central_lower, eventually_ge_atTop H.threshold]
      with T hcentral hT
    simpa [selectedWord, hT] using hcentral
  error_eq := by
    intro T
    rfl
  error_small := by
    have heq : selectedError H =
        (fun T => if h : H.threshold ≤ T
          then wordError (H.bundle T h).word else 0) := by
      funext T
      by_cases hT : H.threshold ≤ T
      · simp [selectedError, selectedWord, hT]
      · simp [selectedError, selectedWord, hT, trivialWordAt, wordError,
          boundary, phi, A, B, p, j, badLeft]
    rw [heq]
    exact H.wordError_small

end Zeta23.GapMatching.EventualCentralFamilyD
