/-
A fixed eventual lower bound for the simple path count converts the word
potential directly into a constant matching gain, without introducing a
second asymptotic error function.
-/
import Zeta23.GapMatching.ConstantGainMatchingInput

open Filter Asymptotics

noncomputable section

namespace Zeta23.GapMatching.FixedSimpleBaselineToConstantGain

open Zeta23
open Zeta23.GapMatching.GapMatchingZetaSeam
open Zeta23.GapMatching.ConstantGainMatchingInput

structure FixedSimplePathFamily (Z : ZeroConfig) (P : Params)
    (simpleCount energy wordError : ℝ → ℝ)
    (A B simpleLower : ℝ) : Prop where
  A_nonneg : 0 ≤ A
  core : ∀ᶠ T in atTop, MatchingCoreAt Z P T (energy T)
  word_gain : ∀ᶠ T in atTop,
    A * simpleCount T - B * (Z.N T (2 * T) : ℝ) - wordError T
      ≤ 2 * energy T
  simple_lower : ∀ᶠ T in atTop,
    simpleLower * (Z.N T (2 * T) : ℝ) ≤ simpleCount T
  wordError_small : wordError =o[atTop]
    (fun T => (Z.N T (2 * T) : ℝ))

theorem FixedSimplePathFamily.toConstantGainFamily
    {Z : ZeroConfig} {P : Params}
    {simpleCount energy wordError : ℝ → ℝ}
    {A B simpleLower : ℝ}
    (H : FixedSimplePathFamily Z P simpleCount energy
      wordError A B simpleLower) :
    ConstantGainFamily Z P energy wordError (A * simpleLower - B) where
  core := H.core
  energy_lower := by
    filter_upwards [H.word_gain, H.simple_lower] with T hword hsimple
    have hmul := mul_le_mul_of_nonneg_left hsimple H.A_nonneg
    nlinarith
  error_small := H.wordError_small

end Zeta23.GapMatching.FixedSimpleBaselineToConstantGain
