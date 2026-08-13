/-
Corrected eventual central construction using the final eventual-equality
packaging.
-/
import Zeta23.GapMatching.EventualCentralFamilyD3
import Zeta23.GapMatching.OneBandCentralPackageAtD

open Filter Asymptotics

noncomputable section

namespace Zeta23.GapMatching.OneBandAnalyticConstructionD2

open Zeta23
open Zeta23.GapMatching.OneBandPotentialSafeNumerics
open Zeta23.GapMatching.OneBandActualWordDCore
open Zeta23.GapMatching.OneBandCentralWordD
open Zeta23.GapMatching.OneBandCentralPackageAtD
open Zeta23.GapMatching.EventualCentralFamilyD3
open Zeta23.GapMatching.CentralPathConstructionD

structure AnalyticInputs (Z : ZeroConfig) (P : Params)
    (simpleLower : ℝ) where
  threshold : ℝ
  vertices : ∀ T, threshold ≤ T → OrderedCentralVerticesD Z P T
  eps : ℝ → ℝ
  phiHatReal : ∀ T, threshold ≤ T → PhiHatReal T (P.atD T)
  scale_pos : ∀ T, threshold ≤ T → 0 < dScale P T
  L_nonneg : ∀ T, threshold ≤ T → 0 ≤ P.L T
  overlap : ∀ T (hT : threshold ≤ T),
    UniformOverlapApprox (vertices T hT) (eps T)
  length : ∀ T (hT : threshold ≤ T),
    totalLength (actualWord (vertices T hT))
      ≤ (Z.N T (2 * T) : ℝ)
  central_lower : ∀ᶠ T in atTop,
    ∀ hT : threshold ≤ T,
      simpleLower * (Z.N T (2 * T) : ℝ)
        ≤ ((vertices T hT).n + 2 : ℕ)
  constantError_small :
    (fun _ : ℝ => A * 2 + boundary)
      =o[atTop] (fun T => (Z.N T (2 * T) : ℝ))

def heightBundle
    {Z : ZeroConfig} {P : Params} {simpleLower : ℝ}
    (H : AnalyticInputs Z P simpleLower)
    (T : ℝ) (hT : H.threshold ≤ T) :
    HeightBundle Z P T := by
  obtain ⟨energy, hword, hcore, hselected⟩ :=
    exists_centralWord_core_at
      (H.phiHatReal T hT) (H.scale_pos T hT)
      (H.L_nonneg T hT) (H.vertices T hT)
      (H.overlap T hT) (H.length T hT)
  exact { energy := energy, word := hword,
    core := hcore, selected := hselected }

theorem AnalyticInputs.toEventualCentralConstruction
    {Z : ZeroConfig} {P : Params} {simpleLower : ℝ}
    (H : AnalyticInputs Z P simpleLower) :
    EventualCentralConstruction Z P simpleLower where
  threshold := H.threshold
  bundle := heightBundle H
  central_lower := by
    filter_upwards [H.central_lower] with T hcentral
    intro hT
    simpa [heightBundle] using hcentral hT
  largeError := fun _ => A * 2 + boundary
  largeError_eq := by
    intro T hT
    simp [heightBundle, wordError]
  largeError_small := H.constantError_small

end Zeta23.GapMatching.OneBandAnalyticConstructionD2
