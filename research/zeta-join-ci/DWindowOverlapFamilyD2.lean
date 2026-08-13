/-
Thresholded form of the D-window overlap family; no ordered path is required
at small heights.
-/
import Zeta23.GapMatching.DWindowOverlapFamilyD

open Filter Topology

noncomputable section

namespace Zeta23.GapMatching.DWindowOverlapFamilyD2

open Zeta23
open Zeta23.GapMatching.DWindowConcreteIdentification
open Zeta23.GapMatching.DWindowActualComponentsD
open Zeta23.GapMatching.OneBandUniformCloseFromBounds
open Zeta23.GapMatching.OneBandActualWordDCore
open Zeta23.GapMatching.OneBandPotentialSafeNumerics
open Zeta23.GapMatching.VanishingOverlapBudget
open Zeta23.GapMatching.CentralPathConstructionD
open Zeta23.GapMatching.DWindowOverlapFamilyD

/-- Uniform overlap package for an ordered path supplied only beyond a fixed
threshold. -/
theorem eventually_uniformOverlapApprox
    {Z : ZeroConfig} {P : Params}
    (H : PackageFamily Z P)
    (threshold : ℝ)
    (V : ∀ T, threshold ≤ T → OrderedCentralVerticesD Z P T) :
    ∀ᶠ T in atTop,
      ∀ hT : threshold ≤ T,
        UniformOverlapApprox (V T hT)
          (tailBudget (H.Q T) + rampBudget (H.Q T)) := by
  have htol : 0 < overlapTolerance := by
    norm_num [overlapTolerance]
  have hbudget := eventually_le_of_tendsto_zero
    (fun T => tailBudget (H.Q T) + rampBudget (H.Q T))
    htol H.budget_tendsto
  filter_upwards [H.phiHatReal, H.T_pos, H.grid_span, hbudget]
    with T hreal hT hspan hsum
  intro hthreshold
  exact uniformOverlapApprox_of_components (V T hthreshold)
    (components hreal (H.Q T) (V T hthreshold) hT hspan)
    le_rfl hsum

end Zeta23.GapMatching.DWindowOverlapFamilyD2
