/-
Corrected assembly of strong D-window overlap and central-path data into the
final analytic input structure.
-/
import Zeta23.GapMatching.OneBandAnalyticConstructionD2
import Zeta23.GapMatching.DWindowStrongPackageFamily
import Zeta23.GapMatching.ConstantOverCount

open Filter Asymptotics Topology

noncomputable section

namespace Zeta23.GapMatching.OneBandStrongAnalyticInputsD2

open Zeta23
open Zeta23.GapMatching.OneBandPotentialSafeNumerics
open Zeta23.GapMatching.OneBandAnalyticConstructionD2
open Zeta23.GapMatching.DWindowStrongPackageFamily
open Zeta23.GapMatching.ConstantOverCount
open Zeta23.GapMatching.OneBandActualWordDCore
open Zeta23.GapMatching.OneBandWordEnergyD
open Zeta23.GapMatching.CentralPathConstructionD

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
  L_nonneg := by
    intro T hT
    rw [← (H.Q T hT).L_eq]
    exact (H.Q T hT).L_pos.le
  overlap := fun T hT => uniformOverlapApprox H V.vertices T hT
  length := V.length
  central_lower := V.central_lower
  constantError_small :=
    const_isLittleO_of_tendsto_atTop
      (A * 2 + boundary)
      (fun T => (Z.N T (2 * T) : ℝ)) hN0 hNtop

end Zeta23.GapMatching.OneBandStrongAnalyticInputsD2
