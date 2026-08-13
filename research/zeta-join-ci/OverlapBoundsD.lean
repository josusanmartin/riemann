/-
Unit bounds needed by the finite-to-sharp square perturbation lemma.
-/
import Zeta23.GapMatching.DWindowGramIdentity
import Zeta23.GapMatching.OneBandSharpProfileAPI
import Zeta23.GapMatching.GapMatchingBlockSpecialization

open RHLinalg

noncomputable section

namespace Zeta23.GapMatching.OverlapBoundsD

open Zeta23
open Zeta23.GapMatching.GapMatchingBlockSpecialization
open Zeta23.GapMatching.DWindowGramIdentity
open Zeta23.GapMatching.OneBandSharpProfileAPI

variable {Z : ZeroConfig} {P : Params} {T : ℝ}

/-- Every real Gram overlap between normalized simple D-window vectors has
absolute value at most one. -/
theorem abs_gramOverlap_le_one
    (z z' : dSimpleOnLine Z P T) :
    |gramOverlap z z'| ≤ 1 := by
  unfold gramOverlap
  calc
    |RCLike.re (inner (dSimpleVector Z P T z)
        (dSimpleVector Z P T z'))|
      ≤ ‖inner (dSimpleVector Z P T z)
          (dSimpleVector Z P T z')‖ := by
        exact RCLike.abs_re_le_norm _
    _ ≤ ‖dSimpleVector Z P T z‖ *
          ‖dSimpleVector Z P T z'‖ := norm_inner_le_norm _ _
    _ ≤ 1 := by
      have hz := dSimple_xsq_le_one Z P T z
      have hz' := dSimple_xsq_le_one Z P T z'
      unfold xsq at hz hz'
      nlinarith [sq_nonneg (‖dSimpleVector Z P T z‖ -
        ‖dSimpleVector Z P T z'‖), norm_nonneg (dSimpleVector Z P T z),
        norm_nonneg (dSimpleVector Z P T z')]

/-- The normalized sharp Montgomery--Taylor profile has modulus at most one. -/
theorem abs_sharpProfile_le_one (x : ℝ) :
    |sharpProfile x| ≤ 1 := by
  exact?

end Zeta23.GapMatching.OverlapBoundsD
