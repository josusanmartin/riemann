/-
End-to-end construction of the abstract central-word family from a strong
D-window package and a strong central path.
-/
import Zeta23.GapMatching.OneBandStrongAnalyticInputsD
import Zeta23.GapMatching.OneBandAnalyticConstructionD
import Zeta23.GapMatching.EventualCentralFamilyD2

open Filter Topology

noncomputable section

namespace Zeta23.GapMatching.OneBandCompleteFamilyD

open Zeta23
open Zeta23.GapMatching.DWindowStrongPackageFamily
open Zeta23.GapMatching.OneBandStrongAnalyticInputsD
open Zeta23.GapMatching.OneBandAnalyticConstructionD
open Zeta23.GapMatching.EventualCentralFamilyD2
open Zeta23.GapMatching.OneBandCentralFamilyD

/-- Strong package + strong path + zero-count growth give the full central-word
family consumed by the additive density theorem. -/
theorem centralWordFamily
    {Z : ZeroConfig} {P : Params} {simpleLower : ℝ}
    (H : StrongPackageFamily Z P)
    (V : StrongCentralPath Z P H simpleLower)
    (hN0 : ∀ᶠ T in atTop, 0 ≤ (Z.N T (2 * T) : ℝ))
    (hNtop : Tendsto (fun T => (Z.N T (2 * T) : ℝ)) atTop atTop) :
    CentralWordFamily Z P
      (selectedEnergy
        ((assemble H V hN0 hNtop).toEventualCentralConstruction))
      (selectedError
        ((assemble H V hN0 hNtop).toEventualCentralConstruction))
      simpleLower := by
  exact
    ((assemble H V hN0 hNtop).toEventualCentralConstruction)
      .toCentralWordFamily

end Zeta23.GapMatching.OneBandCompleteFamilyD
