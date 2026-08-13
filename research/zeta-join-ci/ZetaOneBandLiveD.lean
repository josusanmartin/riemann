/-
Concrete zeta assembly of the corrected one-band live improvement.
-/
import Zeta23.GapMatching.ConcreteDAPI
import Zeta23.GapMatching.ConcreteVanishingPackageD
import Zeta23.GapMatching.StrongPackageFromVanishingBudget
import Zeta23.GapMatching.ZetaCentralPathInputsD
import Zeta23.GapMatching.ConcreteStrongCentralPathD2
import Zeta23.GapMatching.OneBandStrongAnalyticInputsD2
import Zeta23.GapMatching.OneBandCompleteFamilyD2
import Zeta23.GapMatching.OneBandDSeamResult
import Zeta23.GapMatching.OneBandLiveFixedSimpleNumerics

noncomputable section

namespace Zeta23.GapMatching.ZetaOneBandLiveD

open Zeta23
open Zeta23.GapMatching.ConcreteDAPI
open Zeta23.GapMatching.ConcreteVanishingPackageD
open Zeta23.GapMatching.StrongPackageFromVanishingBudget
open Zeta23.GapMatching.ZetaCentralPathInputsD
open Zeta23.GapMatching.ConcreteStrongCentralPathD2
open Zeta23.GapMatching.OneBandStrongAnalyticInputsD2
open Zeta23.GapMatching.OneBandCompleteFamilyD2
open Zeta23.GapMatching.OneBandDSeamResult
open Zeta23.GapMatching.OneBandLiveFixedSimpleNumerics

/-- The corrected one-band construction proves the real live dyadic
improvement for the concrete zeta zero configuration. -/
theorem dyadic :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (candidate - ε) * (zeroConfig.N T (2 * T) : ℝ)
        ≤ (zeroConfig.N0s T (2 * T) : ℝ) := by
  obtain ⟨Hvanish⟩ := exists_vanishingPackage zeroConfig params
  obtain ⟨Hstrong⟩ := exists_strongPackageFamily Hvanish
  obtain ⟨V⟩ := exists_strongCentralPath Hstrong (inputs Hstrong)
  let Hanalytic := assemble Hstrong V
    (inputs Hstrong).N_nonneg (inputs Hstrong).N_top
  let Hfamily := centralWordFamily Hanalytic
  exact candidate_of_centralFamily zeroConfig params _ _ Hfamily

end Zeta23.GapMatching.ZetaOneBandLiveD
