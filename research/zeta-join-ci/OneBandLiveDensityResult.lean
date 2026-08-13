/-
Corrected live density theorem: the one-band path is built from simple
critical-line zeros, its fixed 0.499 density yields an additive matching gain,
and that gain improves the distinct critical-line count.
-/
import Zeta23.GapMatching.OneBandCentralFamilyD
import Zeta23.GapMatching.AdditiveDistinctDensityResult
import Zeta23.GapMatching.OneBandLiveFixedSimpleNumerics

open Filter Asymptotics Topology Real RHLinalg

noncomputable section

namespace Zeta23.GapMatching.OneBandLiveDensityResult

open Zeta23
open Zeta23.Assembly
open Zeta23.GapMatching.OneBandPotentialSafeNumerics
open Zeta23.GapMatching.OneBandCentralFamilyD
open Zeta23.GapMatching.FixedSimpleBaselineToConstantGain
open Zeta23.GapMatching.AdditiveDistinctDensityResult
open Zeta23.GapMatching.OneBandLiveFixedSimpleNumerics

/-- A complete central-word family improves the distinct critical-line
coefficient beyond the exact live candidate. -/
theorem distinct_density_candidate
    (Z : ZeroConfig) (P : Params)
    (energy error theta0 : ℝ → ℝ)
    (hfamily : CentralWordFamily Z P energy error simpleLower)
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
        ≤ ((2 - distinctLower) + delta) *
          (Z.N T (2 * T) : ℝ)) :
    ∀ epsilon > 0, ∃ T0 : ℝ, ∀ T ≥ T0,
      (candidate - epsilon) * (Z.N T (2 * T) : ℝ)
        ≤ (Z.N0s T (2 * T) : ℝ) := by
  have hconstant :=
    hfamily.toFixedSimplePathFamily.toConstantGainFamily
  have hmain := distinct_density_of_constant_gain
    Z P energy error theta0 hconstant
    hTail ha hL hB0 hBto hNII_o hNtop htrace hfrob
  intro epsilon hepsilon
  obtain ⟨T0, hT0⟩ := hmain epsilon hepsilon
  refine ⟨T0, fun T hT => ?_⟩
  have h := hT0 T hT
  have hN : 0 ≤ (Z.N T (2 * T) : ℝ) := Nat.cast_nonneg _
  have hcoef :
      candidate - epsilon ≤
        distinctLower + (A * simpleLower - B) - epsilon := by
    exact sub_le_sub_right candidate_lt_additive_bound.le epsilon
  exact (mul_le_mul_of_nonneg_right hcoef hN).trans h

end Zeta23.GapMatching.OneBandLiveDensityResult
