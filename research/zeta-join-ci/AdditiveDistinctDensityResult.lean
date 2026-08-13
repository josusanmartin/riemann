/-
Generic additive distinct-critical-line consequence of a constant matching
energy gain.
-/
import Zeta23.GapMatching.ConstantGainMatchingInput

open Filter Asymptotics Topology Real RHLinalg

noncomputable section

namespace Zeta23.GapMatching.AdditiveDistinctDensityResult

open Zeta23
open Zeta23.Assembly
open Zeta23.GapMatching.GapMatchingZetaSeam
open Zeta23.GapMatching.ConstantGainMatchingInput

/-- Existing trace/Frobenius asymptotics plus a constant linear matching gain
improve the distinct critical-line density from `baseline` to
`baseline + gain`. -/
theorem distinct_density_of_constant_gain
    (Z : ZeroConfig) (P : Params)
    (energy error theta0 : ℝ → ℝ)
    {baseline gain : ℝ}
    (hfamily : ConstantGainFamily Z P energy error gain)
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
      (baseline + gain - epsilon) * (Z.N T (2 * T) : ℝ)
        ≤ (Z.N0s T (2 * T) : ℝ) := by
  have hden : (1 : ℝ) * 0 < 1 := by norm_num
  have hmain := simple_density_fixed_point
    Z P (2 - baseline) energy error theta0
    1 0 (-gain / 2) hfamily.toAnalyticInput
    hTail ha hL hB0 hBto hNII_o hNtop htrace hfrob hden
  simpa [constant_gain_fixed_point_identity]
    using hmain

end Zeta23.GapMatching.AdditiveDistinctDensityResult
