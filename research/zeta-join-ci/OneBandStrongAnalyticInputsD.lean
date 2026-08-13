/-
Assembly of the strong D-window overlap package, ordered central path, central
cardinality lower bound, and total-length bound into the exact analytic input
structure consumed by the one-band family.
-/
import Zeta23.GapMatching.OneBandAnalyticConstructionD
import Zeta23.GapMatching.DWindowStrongPackageFamily
import Zeta23.GapMatching.ConstantOverCount

open Filter Asymptotics Topology

noncomputable section

namespace Zeta23.GapMatching.OneBandStrongAnalyticInputsD

open Zeta23
open Zeta23.GapMatching.OneBandPotentialSafeNumerics
open Zeta23.GapMatching.OneBandAnalyticConstructionD
open Zeta23.GapMatching.DWindowStrongPackageFamily
open Zeta23.GapMatching.ConstantOverCount
open Zeta23.GapMatching.OneBandActualWordDCore
open Zeta23.GapMatching.OneBandWordEnergyD
open Zeta23.GapMatching.CentralPathConstructionD

/-- A central ordered path family sharing the overlap package threshold. -/
structure StrongCentralPath (Z : ZeroConfig) (P : Params)
    (H : StrongPackageFamily Z P) (simpleLower : ℝ) where
  vertices : ∀ T, H.threshold ≤ T → OrderedCentralVerticesD Z P T
  central_lower : ∀ᶠ T in atTop,
    ∀ hT : H.threshold ≤ T,
      simpleLower * (Z.N T (2 * T) : ℝ)
        ≤ ((vertices T hT).n + 2 : ℕ)
  length : ∀ T (hT : H.threshold ≤ T),
    totalLength (actualWord (vertices T hT))
      ≤ (Z.N T (2 * T) : ℝ)

/-- The strong overlap and path packages supply all analytic inputs. -/
theorem assemble
    {Z : ZeroConfig} {P : Params} {simpleLower : ℝ}
    (H : StrongPackageFamily Z P)
    (V : StrongCentralPath Z P H simpleLower)
    (hN0 : ∀ᶠ T in atTop, 0 ≤ (Z.N T (2 * T) : ℝ))
    (hNtop : Tendsto (fun T => (Z.N T (2 * T) : ℝ)) atTop atTop) :
    AnalyticInputs Z P simpleLower where
  threshold := H.threshold
  vertices := V.vertices
  eps := H.budget
  phiHatReal := H.phiHatReal
  scale_pos := fun T hT => (H.Q T hT).scale_pos
  L_nonneg := fun T hT => (H.Q T hT).L_pos.le.trans_eq (H.Q T hT).L_eq
  overlap := fun T hT => uniformOverlapApprox H V.vertices T hT
  length := V.length
  central_lower := V.central_lower
  wordError_small := by
    have hconst := const_isLittleO_of_tendsto_atTop
      (A * 2 + boundary)
      (fun T => (Z.N T (2 * T) : ℝ)) hN0 hNtop
    have heq :
        (fun T => if hT : H.threshold ≤ T then A * 2 + boundary else 0)
          =ᶠ[atTop] (fun _ : ℝ => A * 2 + boundary) := by
      filter_upwards [eventually_ge_atTop H.threshold] with T hT
      simp [hT]
    exact hconst.congr' heq.symm

end Zeta23.GapMatching.OneBandStrongAnalyticInputsD
