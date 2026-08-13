/-
Strong thresholded D-window package: all pointwise properties hold at every
height beyond one common threshold.
-/
import Zeta23.GapMatching.DWindowActualComponentsD
import Zeta23.GapMatching.OneBandUniformCloseFromBounds
import Zeta23.GapMatching.VanishingOverlapBudget

open Filter Topology

noncomputable section

namespace Zeta23.GapMatching.DWindowStrongPackageFamily

open Zeta23
open Zeta23.GapMatching.DWindowConcreteIdentification
open Zeta23.GapMatching.DWindowActualComponentsD
open Zeta23.GapMatching.OneBandUniformCloseFromBounds
open Zeta23.GapMatching.OneBandActualWordDCore
open Zeta23.GapMatching.OneBandPotentialSafeNumerics
open Zeta23.GapMatching.VanishingOverlapBudget
open Zeta23.GapMatching.CentralPathConstructionD

structure StrongPackageFamily (Z : ZeroConfig) (P : Params) where
  threshold : ℝ
  Q : ∀ T, threshold ≤ T → Package Z P T
  phiHatReal : ∀ T (hT : threshold ≤ T), PhiHatReal T (P.atD T)
  T_pos : ∀ T, threshold ≤ T → 0 < T
  grid_span : ∀ T (hT : threshold ≤ T),
    2 * T ≤ T + ((P.atD T).d T) *
      (2 * Real.pi / (Q T hT).L)
  budget : ℝ → ℝ
  budget_eq : ∀ T (hT : threshold ≤ T),
    budget T = tailBudget (Q T hT) + rampBudget (Q T hT)
  budget_tendsto : Tendsto budget atTop (𝓝 0)
  budget_le_tolerance : ∀ T, threshold ≤ T →
    budget T ≤ overlapTolerance

/-- Uniform overlap control at every height beyond the common threshold. -/
theorem uniformOverlapApprox
    {Z : ZeroConfig} {P : Params}
    (H : StrongPackageFamily Z P)
    (V : ∀ T, H.threshold ≤ T → OrderedCentralVerticesD Z P T)
    (T : ℝ) (hT : H.threshold ≤ T) :
    UniformOverlapApprox (V T hT) (H.budget T) := by
  have hcomponents := components
    (H.phiHatReal T hT) (H.Q T hT) (V T hT)
    (H.T_pos T hT) (H.grid_span T hT)
  rw [H.budget_eq T hT]
  exact uniformOverlapApprox_of_components (V T hT)
    hcomponents le_rfl
    (by simpa [H.budget_eq T hT] using H.budget_le_tolerance T hT)

end Zeta23.GapMatching.DWindowStrongPackageFamily
