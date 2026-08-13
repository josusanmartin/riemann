/-
Corrected end-to-end construction of the abstract central-word family.
-/
import Zeta23.GapMatching.OneBandAnalyticConstructionD2

noncomputable section

namespace Zeta23.GapMatching.OneBandCompleteFamilyD2

open Zeta23
open Zeta23.GapMatching.OneBandAnalyticConstructionD2
open Zeta23.GapMatching.EventualCentralFamilyD3
open Zeta23.GapMatching.OneBandCentralFamilyD

/-- Concrete analytic inputs give the full central-word family. -/
theorem centralWordFamily
    {Z : ZeroConfig} {P : Params} {simpleLower : ℝ}
    (H : AnalyticInputs Z P simpleLower) :
    CentralWordFamily Z P
      (selectedEnergy H.toEventualCentralConstruction)
      (selectedError H.toEventualCentralConstruction)
      simpleLower :=
  H.toEventualCentralConstruction.toCentralWordFamily

end Zeta23.GapMatching.OneBandCompleteFamilyD2
