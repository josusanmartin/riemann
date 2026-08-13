/-
Concrete zeta inputs for the strong central path: half-simple theorem, guard
loss, count growth, and total normalized span.
-/
import Zeta23.GapMatching.ConcreteDAPI
import Zeta23.GapMatching.ConcreteStrongCentralPathD2
import Zeta23.GapMatching.CentralGuardAPI
import Zeta23.GapMatching.DWindowLength
import Zeta23.Unconditional

open Filter Asymptotics Topology

noncomputable section

namespace Zeta23.GapMatching.ZetaCentralPathInputsD

open Zeta23
open Zeta23.GapMatching.ConcreteDAPI
open Zeta23.GapMatching.ConcreteStrongCentralPathD2
open Zeta23.GapMatching.CentralGuardAPI

/-- Concrete central-path inputs for the pinned zeta configuration and
D-window parameter object. -/
theorem inputs
    (H : DWindowStrongPackageFamily.StrongPackageFamily
      zeroConfig params) :
    Inputs zeroConfig params H := by
  have hhalf := Zeta23.thmB₀ (ε := (0.0005 : ℝ)) (by norm_num)
  have hguardSmall := guardSmall
  have hcentralLoss := centralLoss
  exact?

end Zeta23.GapMatching.ZetaCentralPathInputsD
