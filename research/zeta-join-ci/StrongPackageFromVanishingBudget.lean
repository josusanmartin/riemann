/-
Choose one common large-height threshold from a concrete D-window package and
a scalar overlap budget tending to zero.
-/
import Zeta23.GapMatching.DWindowStrongPackageFamily
import Zeta23.GapMatching.VanishingOverlapBudget

open Filter Topology

noncomputable section

namespace Zeta23.GapMatching.StrongPackageFromVanishingBudget

open Zeta23
open Zeta23.GapMatching.DWindowConcreteIdentification
open Zeta23.GapMatching.DWindowActualComponentsD
open Zeta23.GapMatching.DWindowStrongPackageFamily
open Zeta23.GapMatching.OneBandPotentialSafeNumerics
open Zeta23.GapMatching.VanishingOverlapBudget

/-- Concrete package at every height above an initial threshold, with a
vanishing scalar budget. -/
structure VanishingPackage (Z : ZeroConfig) (P : Params) where
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

/-- Raise the initial threshold so the budget is uniformly below the profile
tolerance. -/
theorem exists_strongPackageFamily
    {Z : ZeroConfig} {P : Params}
    (H : VanishingPackage Z P) :
    Nonempty (StrongPackageFamily Z P) := by
  have htol : 0 < overlapTolerance := by
    norm_num [overlapTolerance]
  have hevent := eventually_le_of_tendsto_zero
    H.budget htol H.budget_tendsto
  rw [eventually_atTop.1] at hevent
  obtain ⟨Ttol, hTtol⟩ := hevent
  let threshold := max H.threshold Ttol
  refine ⟨{
    threshold := threshold
    Q := fun T hT => H.Q T (le_trans (le_max_left _ _) hT)
    phiHatReal := fun T hT =>
      H.phiHatReal T (le_trans (le_max_left _ _) hT)
    T_pos := fun T hT => H.T_pos T (le_trans (le_max_left _ _) hT)
    grid_span := fun T hT =>
      H.grid_span T (le_trans (le_max_left _ _) hT)
    budget := H.budget
    budget_eq := fun T hT =>
      H.budget_eq T (le_trans (le_max_left _ _) hT)
    budget_tendsto := H.budget_tendsto
    budget_le_tolerance := fun T hT =>
      hTtol T (le_trans (le_max_right _ _) hT)
  }⟩

end Zeta23.GapMatching.StrongPackageFromVanishingBudget
