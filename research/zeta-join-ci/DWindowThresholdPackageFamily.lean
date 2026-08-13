/-
Thresholded D-window package family and its uniform overlap consequence.
-/
import Zeta23.GapMatching.DWindowActualComponentsD
import Zeta23.GapMatching.OneBandUniformCloseFromBounds
import Zeta23.GapMatching.VanishingOverlapBudget

open Filter Topology

noncomputable section

namespace Zeta23.GapMatching.DWindowThresholdPackageFamily

open Zeta23
open Zeta23.GapMatching.DWindowConcreteIdentification
open Zeta23.GapMatching.DWindowActualComponentsD
open Zeta23.GapMatching.OneBandUniformCloseFromBounds
open Zeta23.GapMatching.OneBandActualWordDCore
open Zeta23.GapMatching.OneBandPotentialSafeNumerics
open Zeta23.GapMatching.VanishingOverlapBudget
open Zeta23.GapMatching.CentralPathConstructionD

structure ThresholdPackageFamily (Z : ZeroConfig) (P : Params) where
  threshold : ℝ
  Q : ∀ T, threshold ≤ T → Package Z P T
  phiHatReal : ∀ᶠ T in atTop,
    ∀ hT : threshold ≤ T, PhiHatReal T (P.atD T)
  T_pos : ∀ᶠ T in atTop, 0 < T
  grid_span : ∀ᶠ T in atTop,
    ∀ hT : threshold ≤ T,
      2 * T ≤ T + ((P.atD T).d T) *
        (2 * Real.pi / (Q T hT).L)
  budget_tendsto : Tendsto
    (fun T => if hT : threshold ≤ T
      then tailBudget (Q T hT) + rampBudget (Q T hT) else 0)
    atTop (𝓝 0)

/-- Error selected at every height, zero below the threshold. -/
def error
    {Z : ZeroConfig} {P : Params}
    (H : ThresholdPackageFamily Z P) (T : ℝ) : ℝ :=
  if hT : H.threshold ≤ T
    then tailBudget (H.Q T hT) + rampBudget (H.Q T hT)
    else 0

/-- The thresholded package supplies uniform overlap control for every
large-height ordered path. -/
theorem eventually_uniformOverlapApprox
    {Z : ZeroConfig} {P : Params}
    (H : ThresholdPackageFamily Z P)
    (V : ∀ T, H.threshold ≤ T → OrderedCentralVerticesD Z P T) :
    ∀ᶠ T in atTop,
      ∀ hT : H.threshold ≤ T,
        UniformOverlapApprox (V T hT) (error H T) := by
  have htol : 0 < overlapTolerance := by
    norm_num [overlapTolerance]
  have hbudget := eventually_le_of_tendsto_zero (error H) htol
    (by simpa [error] using H.budget_tendsto)
  filter_upwards [H.phiHatReal, H.T_pos, H.grid_span, hbudget]
    with T hreal hTpos hspan hsum
  intro hthreshold
  have hcomponents := components
    (hreal hthreshold) (H.Q T hthreshold) (V T hthreshold)
    hTpos (hspan hthreshold)
  simpa [error, hthreshold] using
    (uniformOverlapApprox_of_components (V T hthreshold)
      hcomponents le_rfl hsum)

end Zeta23.GapMatching.DWindowThresholdPackageFamily
