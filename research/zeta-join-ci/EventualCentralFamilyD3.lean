/-
Final eventual-witness packaging.  Below-threshold data are arbitrary; the
error comparison is therefore stated by eventual equality rather than global
function equality.
-/
import Zeta23.GapMatching.OneBandCentralFamilyD

open Filter Asymptotics

noncomputable section

namespace Zeta23.GapMatching.EventualCentralFamilyD3

open Zeta23
open Zeta23.GapMatching.FiniteStateGapPotential
open Zeta23.GapMatching.OneBandPotentialSafeNumerics
open Zeta23.GapMatching.OneBandCentralWordD
open Zeta23.GapMatching.OneBandCentralFamilyD
open Zeta23.GapMatching.GapMatchingZetaSeam

structure HeightBundle (Z : ZeroConfig) (P : Params) (T : ℝ) where
  energy : ℝ
  word : CentralWordAt Z T
  core : MatchingCoreAt Z P T energy
  selected : word.W ≤ 2 * energy

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

structure EventualCentralConstruction (Z : ZeroConfig) (P : Params)
    (simpleLower : ℝ) where
  threshold : ℝ
  bundle : ∀ T, threshold ≤ T → HeightBundle Z P T
  central_lower : ∀ᶠ T in atTop,
    ∀ hT : threshold ≤ T,
      simpleLower * (Z.N T (2 * T) : ℝ)
        ≤ (bundle T hT).word.centralSimple
  largeError : ℝ → ℝ
  largeError_eq : ∀ T (hT : threshold ≤ T),
    largeError T = wordError (bundle T hT).word
  largeError_small : largeError =o[atTop]
    (fun T => (Z.N T (2 * T) : ℝ))

def selectedEnergy
    {Z : ZeroConfig} {P : Params} {simpleLower : ℝ}
    (H : EventualCentralConstruction Z P simpleLower) (T : ℝ) : ℝ :=
  if h : H.threshold ≤ T then (H.bundle T h).energy else 0

def selectedWord
    {Z : ZeroConfig} {P : Params} {simpleLower : ℝ}
    (H : EventualCentralConstruction Z P simpleLower) (T : ℝ) :
    CentralWordAt Z T :=
  if h : H.threshold ≤ T then (H.bundle T h).word else trivialWordAt Z T

def selectedError
    {Z : ZeroConfig} {P : Params} {simpleLower : ℝ}
    (H : EventualCentralConstruction Z P simpleLower) (T : ℝ) : ℝ :=
  wordError (selectedWord H T)

theorem EventualCentralConstruction.toCentralWordFamily
    {Z : ZeroConfig} {P : Params} {simpleLower : ℝ}
    (H : EventualCentralConstruction Z P simpleLower) :
    CentralWordFamily Z P
      (selectedEnergy H) (selectedError H) simpleLower where
  data := selectedWord H
  core := by
    filter_upwards [eventually_ge_atTop H.threshold] with T hT
    simpa [selectedEnergy, hT] using (H.bundle T hT).core
  selected := by
    filter_upwards [eventually_ge_atTop H.threshold] with T hT
    simpa [selectedEnergy, selectedWord, hT] using (H.bundle T hT).selected
  central_lower := by
    filter_upwards [H.central_lower, eventually_ge_atTop H.threshold]
      with T hcentral hT
    simpa [selectedWord, hT] using hcentral hT
  error_eq := by intro T; rfl
  error_small := by
    have heq : selectedError H =ᶠ[atTop] H.largeError := by
      filter_upwards [eventually_ge_atTop H.threshold] with T hT
      simp [selectedError, selectedWord, hT, H.largeError_eq T hT]
    exact H.largeError_small.congr' heq.symm

end Zeta23.GapMatching.EventualCentralFamilyD3
