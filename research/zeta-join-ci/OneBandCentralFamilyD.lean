/-
Asymptotic family of guarded central words.  A fixed lower bound for the
central path cardinality converts the finite word potential into the additive
matching gain used by the live theorem.
-/
import Zeta23.GapMatching.OneBandCentralWordD
import Zeta23.GapMatching.FixedSimpleBaselineToConstantGain

open Filter Asymptotics

noncomputable section

namespace Zeta23.GapMatching.OneBandCentralFamilyD

open Zeta23
open Zeta23.GapMatching.OneBandPotentialSafeNumerics
open Zeta23.GapMatching.OneBandCentralWordD
open Zeta23.GapMatching.FixedSimpleBaselineToConstantGain
open Zeta23.GapMatching.GapMatchingZetaSeam

/-- A full asymptotic family of central words and selected matchings. -/
structure CentralWordFamily (Z : ZeroConfig) (P : Params)
    (energy error : ℝ → ℝ) (simpleLower : ℝ) : Prop where
  data : ∀ T, CentralWordAt Z T
  core : ∀ᶠ T in atTop, MatchingCoreAt Z P T (energy T)
  selected : ∀ᶠ T in atTop, (data T).W ≤ 2 * energy T
  central_lower : ∀ᶠ T in atTop,
    simpleLower * (Z.N T (2 * T) : ℝ) ≤ (data T).centralSimple
  error_eq : ∀ T, error T = wordError (data T)
  error_small : error =o[atTop]
    (fun T => (Z.N T (2 * T) : ℝ))

/-- Convert the central family into the generic fixed-simple path family. -/
theorem CentralWordFamily.toFixedSimplePathFamily
    {Z : ZeroConfig} {P : Params} {energy error : ℝ → ℝ}
    {simpleLower : ℝ}
    (H : CentralWordFamily Z P energy error simpleLower) :
    FixedSimplePathFamily Z P
      (fun T => (H.data T).centralSimple)
      energy error A B simpleLower where
  A_nonneg := parameter_ranges.1.le
  core := H.core
  word_gain := by
    filter_upwards [H.selected] with T hselected
    rw [H.error_eq T]
    exact (word_weight_lower (H.data T)).trans hselected
  simple_lower := H.central_lower
  wordError_small := H.error_small

end Zeta23.GapMatching.OneBandCentralFamilyD
