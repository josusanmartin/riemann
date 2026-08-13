/-
Convert a path-energy lower bound in terms of the simple critical-line count
into a constant linear matching gain using an independent simple-zero density
bound.
-/
import Zeta23.GapMatching.ConstantGainMatchingInput

open Filter Asymptotics

noncomputable section

namespace Zeta23.GapMatching.SimpleBaselineToConstantGain

open Zeta23
open Zeta23.GapMatching.GapMatchingZetaSeam
open Zeta23.GapMatching.ConstantGainMatchingInput

/-- Error-explicit ingredients before eliminating the simple-zero count. -/
structure SimplePathFamily (Z : ZeroConfig) (P : Params)
    (simpleCount energy wordError simpleError : ℝ → ℝ)
    (A B simpleLower : ℝ) : Prop where
  A_nonneg : 0 ≤ A
  core : ∀ᶠ T in atTop, MatchingCoreAt Z P T (energy T)
  word_gain : ∀ᶠ T in atTop,
    A * simpleCount T - B * (Z.N T (2 * T) : ℝ) - wordError T
      ≤ 2 * energy T
  simple_lower : ∀ᶠ T in atTop,
    simpleLower * (Z.N T (2 * T) : ℝ) - simpleError T
      ≤ simpleCount T
  wordError_small : wordError =o[atTop]
    (fun T => (Z.N T (2 * T) : ℝ))
  simpleError_small : simpleError =o[atTop]
    (fun T => (Z.N T (2 * T) : ℝ))

/-- Combined asymptotic error. -/
def combinedError
    (A : ℝ) (wordError simpleError : ℝ → ℝ) (T : ℝ) : ℝ :=
  wordError T + A * simpleError T

/-- Eliminate the simple count and obtain the additive gain
`A * simpleLower - B`. -/
theorem SimplePathFamily.toConstantGainFamily
    {Z : ZeroConfig} {P : Params}
    {simpleCount energy wordError simpleError : ℝ → ℝ}
    {A B simpleLower : ℝ}
    (H : SimplePathFamily Z P simpleCount energy
      wordError simpleError A B simpleLower) :
    ConstantGainFamily Z P energy
      (combinedError A wordError simpleError)
      (A * simpleLower - B) where
  core := H.core
  energy_lower := by
    filter_upwards [H.word_gain, H.simple_lower] with T hword hsimple
    have hmul := mul_le_mul_of_nonneg_left hsimple H.A_nonneg
    unfold combinedError
    nlinarith
  error_small := by
    have hscaled : (fun T => A * simpleError T)
        =o[atTop] (fun T => (Z.N T (2 * T) : ℝ)) :=
      H.simpleError_small.const_mul_left A
    simpa [combinedError] using H.wordError_small.add hscaled

end Zeta23.GapMatching.SimpleBaselineToConstantGain
