/-
A constant linear matching gain can be represented in the existing
`GapMatchingAnalyticInput` interface by setting the feedback coefficient to
zero and using a negative offset parameter.  This is the correct seam once the
path energy has first been lower-bounded using the independent simple-zero
density theorem.
-/
import Zeta23.GapMatching.GapMatchingZetaSeam

open Filter Asymptotics

noncomputable section

namespace Zeta23.GapMatching.ConstantGainMatchingInput

open Zeta23
open Zeta23.GapMatching.GapMatchingZetaSeam

/-- Matching core with an additive gain `gain * N`, up to an `o(N)` error. -/
structure ConstantGainFamily (Z : ZeroConfig) (P : Params)
    (energy error : ℝ → ℝ) (gain : ℝ) : Prop where
  core : ∀ᶠ T in atTop, MatchingCoreAt Z P T (energy T)
  energy_lower : ∀ᶠ T in atTop,
    gain * (Z.N T (2 * T) : ℝ) - error T ≤ 2 * energy T
  error_small : error =o[atTop] (fun T => (Z.N T (2 * T) : ℝ))

/-- Re-encode the additive gain in the pre-existing analytic-input schema. -/
theorem ConstantGainFamily.toAnalyticInput
    {Z : ZeroConfig} {P : Params} {energy error : ℝ → ℝ} {gain : ℝ}
    (H : ConstantGainFamily Z P energy error gain) :
    GapMatchingAnalyticInput Z P energy error 1 0 (-gain / 2) where
  core := H.core
  energy_lower := by
    filter_upwards [H.energy_lower] with T hT
    have hid :
        (1 : ℝ) *
            (0 * (Z.N0s T (2 * T) : ℝ)
              - 2 * (-gain / 2) * (Z.N T (2 * T) : ℝ))
          = gain * (Z.N T (2 * T) : ℝ) := by ring
    rw [hid]
    exact hT
  error_small := H.error_small

/-- The fixed-point expression of the seam reduces exactly to baseline plus
constant gain. -/
theorem constant_gain_fixed_point_identity
    {baseline gain : ℝ} :
    (baseline - 2 * (1 : ℝ) * (-gain / 2)) /
        (1 - (1 : ℝ) * 0)
      = baseline + gain := by
  ring

end Zeta23.GapMatching.ConstantGainMatchingInput
