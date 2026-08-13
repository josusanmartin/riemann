/-
A family of concrete D-window parameter packages whose scalar tail+ramp budget
vanishes supplies uniform one-band overlap control at every sufficiently large
height.
-/
import Zeta23.GapMatching.DWindowActualComponentsD
import Zeta23.GapMatching.OneBandUniformCloseFromBounds
import Zeta23.GapMatching.VanishingOverlapBudget

open Filter Topology

noncomputable section

namespace Zeta23.GapMatching.DWindowOverlapFamilyD

open Zeta23
open Zeta23.GapMatching.DWindowConcreteIdentification
open Zeta23.GapMatching.DWindowActualComponentsD
open Zeta23.GapMatching.OneBandUniformCloseFromBounds
open Zeta23.GapMatching.OneBandActualWordDCore
open Zeta23.GapMatching.OneBandPotentialSafeNumerics
open Zeta23.GapMatching.VanishingOverlapBudget
open Zeta23.GapMatching.CentralPathConstructionD

/-- Concrete D-window data and its vanishing scalar error budget. -/
structure PackageFamily (Z : ZeroConfig) (P : Params) where
  Q : ∀ T, Package Z P T
  phiHatReal : ∀ᶠ T in atTop, PhiHatReal T (P.atD T)
  T_pos : ∀ᶠ T in atTop, 0 < T
  grid_span : ∀ᶠ T in atTop,
    2 * T ≤ T + ((P.atD T).d T) *
      (2 * Real.pi / (Q T).L)
  budget_tendsto : Tendsto
    (fun T => tailBudget (Q T) + rampBudget (Q T))
    atTop (𝓝 0)

/-- Every ordered central path eventually receives the complete uniform
finite-versus-sharp overlap package. -/
theorem eventually_uniformOverlapApprox
    {Z : ZeroConfig} {P : Params}
    (H : PackageFamily Z P)
    (V : ∀ T, OrderedCentralVerticesD Z P T) :
    ∀ᶠ T in atTop,
      UniformOverlapApprox (V T)
        (tailBudget (H.Q T) + rampBudget (H.Q T)) := by
  have htol : 0 < overlapTolerance := by
    norm_num [overlapTolerance]
  have hbudget := eventually_le_of_tendsto_zero
    (fun T => tailBudget (H.Q T) + rampBudget (H.Q T))
    htol H.budget_tendsto
  filter_upwards [H.phiHatReal, H.T_pos, H.grid_span, hbudget]
    with T hreal hT hspan hsum
  exact uniformOverlapApprox_of_components (V T)
    (components hreal (H.Q T) (V T) hT hspan)
    le_rfl hsum

end Zeta23.GapMatching.DWindowOverlapFamilyD
