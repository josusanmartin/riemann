/-
Assemble the one-band uniform overlap package from finite/full and full/sharp
bounds on every retained short and long edge.
-/
import Zeta23.GapMatching.OneBandUniformOverlapD
import Zeta23.GapMatching.DWindowFiniteSharpCloseness

noncomputable section

namespace Zeta23.GapMatching.OneBandUniformCloseFromBounds

open Zeta23
open Zeta23.GapMatching.OneBandPotentialSafeNumerics
open Zeta23.GapMatching.OneBandActualWordDCore
open Zeta23.GapMatching.OneBandUniformOverlapD
open Zeta23.GapMatching.DWindowFiniteSharpCloseness
open Zeta23.GapMatching.CentralPathConstructionD
open Zeta23.GapMatching.CentralGapGeometryD
open Zeta23.GapMatching.CanonicalOneBandPathD
open Zeta23.GapMatching.OneBandSharpProfileAPI

variable {Z : ZeroConfig} {P : Params} {T : ℝ}

/-- Uniform short/long error bounds, before adding their two components. -/
structure Components
    (V : OrderedCentralVerticesD Z P T)
    (tailError rampError : ℝ) : Prop where
  short_finite_full : ∀ i : Fin V.n,
    ∃ full : ℝ,
      |shortOverlapNat V i - full| ≤ tailError ∧
      |full - sharpProfile (gapAtNat V i)| ≤ rampError
  long_finite_full : ∀ i : Fin V.n,
    ∃ full : ℝ,
      |longOverlapNat V i - full| ≤ tailError ∧
      |full - sharpProfile
        (gapAtNat V i + gapAtNat V (i + 1))| ≤ rampError

/-- Component bounds imply the complete uniform perturbation package. -/
theorem uniformOverlapApprox_of_components
    (V : OrderedCentralVerticesD Z P T)
    {tailError rampError eps : ℝ}
    (H : Components V tailError rampError)
    (hsum : tailError + rampError ≤ eps)
    (heps : eps ≤ overlapTolerance) :
    UniformOverlapApprox V eps := by
  apply uniformOverlapApprox_of_close V heps
  · intro i
    obtain ⟨full, hfinite, hsharp⟩ := H.short_finite_full i
    exact abs_finite_sub_sharp_le_of_sum hfinite hsharp hsum
  · intro i
    obtain ⟨full, hfinite, hsharp⟩ := H.long_finite_full i
    exact abs_finite_sub_sharp_le_of_sum hfinite hsharp hsum

end Zeta23.GapMatching.OneBandUniformCloseFromBounds
