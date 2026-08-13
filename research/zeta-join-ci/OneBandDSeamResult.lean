/-
Plug the corrected constant-gain analytic input into the existing D-window
trace/Frobenius seam and weaken the result to the live rational target.
-/
import Zeta23.GapMatching.GapDSeamAPI
import Zeta23.GapMatching.OneBandCentralFamilyD
import Zeta23.GapMatching.FixedSimpleBaselineToConstantGain
import Zeta23.GapMatching.OneBandLiveFixedSimpleNumerics
import Zeta23.GapMatching.FixedLambdaBaselineD

noncomputable section

namespace Zeta23.GapMatching.OneBandDSeamResult

open Zeta23
open Zeta23.GapMatching.GapDSeamAPI
open Zeta23.GapMatching.OneBandCentralFamilyD
open Zeta23.GapMatching.FixedSimpleBaselineToConstantGain
open Zeta23.GapMatching.ConstantGainMatchingInput
open Zeta23.GapMatching.OneBandLiveFixedSimpleNumerics
open Zeta23.GapMatching.FixedLambdaBaselineD

/-- A complete corrected central family yields the live distinct critical-line
coefficient through the existing D-window endgame. -/
theorem candidate_of_centralFamily
    (Z : ZeroConfig) (P : Params)
    (energy error : ℝ → ℝ)
    (H : CentralWordFamily Z P energy error simpleLower) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (candidate - ε) * (Z.N T (2 * T) : ℝ)
        ≤ (Z.N0s T (2 * T) : ℝ) := by
  have hconstant := H.toFixedSimplePathFamily.toConstantGainFamily
  have hinput := hconstant.toAnalyticInput
  have hseam := gapDSeam
  exact?

end Zeta23.GapMatching.OneBandDSeamResult
