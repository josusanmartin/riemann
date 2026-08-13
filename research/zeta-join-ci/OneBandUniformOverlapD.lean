/-
Uniform-overlap package constructor.  Actual and sharp unit bounds are proved
once; the eventual analytic theorem only has to supply the two closeness
inequalities and an error below the certified tolerance.
-/
import Zeta23.GapMatching.OneBandActualWordDCore
import Zeta23.GapMatching.OverlapBoundsD

noncomputable section

namespace Zeta23.GapMatching.OneBandUniformOverlapD

open Zeta23
open Zeta23.GapMatching.OneBandPotentialSafeNumerics
open Zeta23.GapMatching.OneBandActualWordDCore
open Zeta23.GapMatching.OverlapBoundsD
open Zeta23.GapMatching.CentralPathConstructionD
open Zeta23.GapMatching.CentralGapGeometryD
open Zeta23.GapMatching.CanonicalOneBandPathD

variable {Z : ZeroConfig} {P : Params} {T : ℝ}

/-- Uniform finite-versus-sharp closeness on every retained short and long
edge produces the complete perturbation package. -/
theorem uniformOverlapApprox_of_close
    (V : OrderedCentralVerticesD Z P T)
    {eps : ℝ}
    (heps : eps ≤ overlapTolerance)
    (hshort : ∀ i : Fin V.n,
      |shortOverlapNat V i - sharpProfile (gapAtNat V i)| ≤ eps)
    (hlong : ∀ i : Fin V.n,
      |longOverlapNat V i
        - sharpProfile (gapAtNat V i + gapAtNat V (i + 1))| ≤ eps) :
    UniformOverlapApprox V eps where
  eps_le := heps
  short_actual_bound := by
    intro i
    unfold shortOverlapNat shortOverlap
    simp only [dif_pos (by omega)]
    exact abs_gramOverlap_le_one _ _
  short_profile_bound := by
    intro i
    exact abs_sharpProfile_le_one _
  short_close := hshort
  long_actual_bound := by
    intro i
    unfold longOverlapNat longOverlap
    simp only [dif_pos i.isLt]
    exact abs_gramOverlap_le_one _ _
  long_profile_bound := by
    intro i
    exact abs_sharpProfile_le_one _
  long_close := hlong

end Zeta23.GapMatching.OneBandUniformOverlapD
