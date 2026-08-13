/-
Construction of the strong ordered central path from a fixed central-cardinality
lower bound and the existing central-set sorter.
-/
import Zeta23.GapMatching.OneBandStrongAnalyticInputsD
import Zeta23.GapMatching.CentralSimpleLowerAlgebra
import Zeta23.GapMatching.ActualWordLengthD
import Zeta23.GapMatching.CentralGuardAPI
import Zeta23.Unconditional

open Filter Asymptotics Topology

noncomputable section

namespace Zeta23.GapMatching.ConcreteStrongCentralPathD

open Zeta23
open Zeta23.GapMatching.OneBandStrongAnalyticInputsD
open Zeta23.GapMatching.DWindowStrongPackageFamily
open Zeta23.GapMatching.CentralSimpleLowerAlgebra
open Zeta23.GapMatching.ActualWordLengthD
open Zeta23.GapMatching.CentralGuardAPI
open Zeta23.GapMatching.CentralPathConstructionD
open Zeta23.GapMatching.CentralGapGeometryD

/-- Abstract inputs that identify the global simple count and guard loss with
the concrete ordered central set. -/
structure Inputs (Z : ZeroConfig) (P : Params)
    (H : StrongPackageFamily Z P) where
  globalSimple : ℝ → ℝ
  guard : ℝ → ℝ
  global_simple_4995 : ∀ᶠ T in atTop,
    (0.4995 : ℝ) * (Z.N T (2 * T) : ℝ) ≤ globalSimple T
  central_loss : ∀ᶠ T in atTop,
    globalSimple T - guard T ≤
      ((centralSimpleSet Z T).ncard : ℝ)
  guard_small : guard =o[atTop]
    (fun T => (Z.N T (2 * T) : ℝ))
  N_nonneg : ∀ᶠ T in atTop, 0 ≤ (Z.N T (2 * T) : ℝ)
  N_top : Tendsto (fun T => (Z.N T (2 * T) : ℝ)) atTop atTop
  full_length : ∀ᶠ T in atTop,
    ∀ (V : OrderedCentralVerticesD Z P T),
      (normalizedGapList V).sum ≤ (Z.N T (2 * T) : ℝ)

/-- The inputs produce a common-threshold strong central path retaining
coefficient `0.499`. -/
theorem exists_strongCentralPath
    {Z : ZeroConfig} {P : Params}
    (H : StrongPackageFamily Z P)
    (I : Inputs Z P H) :
    Nonempty (StrongCentralPath Z P H 0.499) := by
  have hcentral : ∀ᶠ T in atTop,
      (0.499 : ℝ) * (Z.N T (2 * T) : ℝ)
        ≤ ((centralSimpleSet Z T).ncard : ℝ) :=
    eventually_central_499
      (fun T => (Z.N T (2 * T) : ℝ))
      I.globalSimple
      (fun T => ((centralSimpleSet Z T).ncard : ℝ))
      I.guard I.global_simple_4995 I.central_loss
      I.guard_small I.N_nonneg
  exact?

end Zeta23.GapMatching.ConcreteStrongCentralPathD
