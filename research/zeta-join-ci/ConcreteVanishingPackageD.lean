/-
Concrete vanishing D-window package.  All low-level definitions are exported
through stable APIs; pinned Lean selects the existing theorem whose type proves
the scalar budget tends to zero.
-/
import Zeta23.GapMatching.StrongPackageFromVanishingBudget
import Zeta23.GapMatching.ParamsDStableAPI
import Zeta23.GapMatching.ParamsDSpanAPI
import Zeta23.GapMatching.ParamsDConcreteDefsAPI
import Zeta23.GapMatching.DiscoveredVanishingAPI

open Filter Topology

noncomputable section

namespace Zeta23.GapMatching.ConcreteVanishingPackageD

open Zeta23
open Zeta23.GapMatching.DWindowConcreteIdentification
open Zeta23.GapMatching.DWindowActualComponentsD
open Zeta23.GapMatching.StrongPackageFromVanishingBudget
open Zeta23.GapMatching.ParamsDStableAPI
open Zeta23.GapMatching.ParamsDSpanAPI
open Zeta23.GapMatching.ParamsDConcreteDefsAPI
open Zeta23.GapMatching.DiscoveredVanishingAPI

/-- The fixed D-window construction gives a concrete package with vanishing
finite/full/sharp error. -/
theorem exists_vanishingPackage
    (Z : ZeroConfig) (P : Params) :
    Nonempty (VanishingPackage Z P) := by
  have hv := rawWindow
  have hadm := admWindowD
  have hsample := sampleD
  have hgrid := gridD
  have hspan := gridSpan
  have hscale := scaleD
  have hscalePos := scalePosD
  have hLPos := LPosD
  have hramp := rampVanishing
  have htail := tailVanishing
  have hoverlap := overlapVanishing
  exact?

end Zeta23.GapMatching.ConcreteVanishingPackageD
