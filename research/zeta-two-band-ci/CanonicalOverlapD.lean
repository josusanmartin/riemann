/-
Copyright (c) 2026.
SPDX-License-Identifier: Apache-2.0

Identification of a canonical path edge with the finite normalized
Montgomery--Taylor Gram overlap.
-/
import Zeta23.GapMatching.CanonicalOneBandPathD
import Zeta23.GapMatching.DWindowFiniteGridApprox
import Zeta23.ThmD.ZeroSideD

noncomputable section

open Matrix Finset Real
open scoped BigOperators ComplexOrder

namespace Zeta23.GapMatching.CanonicalOverlapD

open Zeta23
open Zeta23.ZeroSide
open Zeta23.ZeroSide.RankTraceMult
open Zeta23.ThmD
open Zeta23.AdmWindow
open Zeta23.GapMatching.CentralPathConstructionD
open Zeta23.GapMatching.CentralGapGeometryD
open Zeta23.GapMatching.CanonicalOneBandPathD
open Zeta23.GapMatching.DWindowFiniteGridApprox
open Zeta23.GapMatching.FiniteBlockApproximation
open Zeta23.GapMatching.GapMatchingBlockSpecialization
open Zeta23.GapMatching.PathForestMatching
open Zeta23.GapMatching.DistinctGapMatchingPipeline
open Zeta23.GapMatching.TwoBandGapMatchingDPath

variable {Z : ZeroConfig} {P : Params} {T : ℝ}

/-- The signed finite normalized overlap of two canonical vertices. -/
def finiteOverlap
    (V : OrderedCentralVerticesD Z P T)
    (i j : Fin (V.n + 2)) : ℝ :=
  finiteNormalizedOverlap (P.phiD T) (P.L T) T
    ((P.atD T).d T) (ordinate V i) (ordinate V j)

private theorem vertex_gamma
    (V : OrderedCentralVerticesD Z P T)
    (i : Fin (V.n + 2)) :
    gammaOf (((V.vertices i).1.1 : ZeroSide.ZI Z T) : ℂ)
      = (ordinate V i : ℂ) := by
  apply gammaOf_of_re_eq_half
  exact (V.central_mem i).1.2

/-- The unit-weight Gram entry of two normalized canonical evaluation
vectors is the real finite Poisson overlap. -/
theorem gramEntry_eq_finiteOverlap
    (hP : P.Valid)
    (h8 : 8 * P.w ≤ P.L T)
    (h4pi : 4 * Real.pi * P.w ≤ P.L T)
    (V : OrderedCentralVerticesD Z P T)
    (i j : Fin (V.n + 2)) :
    let W := Wmat
      (fun _ : dSimpleOnLine Z P T => (1 : ℝ))
      (dSimpleVector Z P T)
    (Wᴴ * W) (V.vertices i) (V.vertices j)
      = (finiteOverlap V i j : ℂ) := by
  classical
  dsimp only
  rw [Matrix.mul_apply]
  simp only [Matrix.conjTranspose_apply, Wmat, Real.sqrt_one,
    RCLike.ofReal_one, one_mul, RCLike.star_def]
  change
    (∑ k : Fin ((P.atD T).d T),
      starRingEnd ℂ (dSimpleVector Z P T (V.vertices i) k) *
        dSimpleVector Z P T (V.vertices j) k)
      = (finiteOverlap V i j : ℂ)
  have hL : 0 < P.L T := by
    linarith [hP.one_le_w]
  have ha : 0 < (P.atD T).a T := by
    linarith [(aD_range_of hP h8 h4pi).1]
  have hc : 0 < dScale P T := by
    unfold dScale
    exact mul_pos ha (pow_pos hL 2)
  have hsqrtC :
      ((Real.sqrt (dScale P T) : ℂ)) ^ 2 = (dScale P T : ℂ) := by
    exact_mod_cast Real.sq_sqrt hc.le
  unfold finiteOverlap finiteNormalizedOverlap finiteBlock normalizedTerm
  rw [Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro k hk
  simp only [dSimpleVector, simpleVhat, ZeroBlockData.vhat,
    blockData, mkData_v, evalVec]
  rw [vertex_gamma V i, vertex_gamma V j]
  rw [GzGp.phiHat_ofReal, GzGp.phiHat_ofReal]
  rw [atD_phiHatR hP, atD_phiHatR hP]
  rw [atD_tau_eq, atD_tau_eq]
  rw [map_div₀, Complex.conj_ofReal]
  change
    ((vHatR (P.phiD T)
          (ordinate V i - (T + (k : ℤ) * (2 * Real.pi / P.L T))) : ℂ)
        / (Real.sqrt (dScale P T) : ℂ)) *
      ((vHatR (P.phiD T)
          (ordinate V j - (T + (k : ℤ) * (2 * Real.pi / P.L T))) : ℂ)
        / (Real.sqrt (dScale P T) : ℂ))
      = _
  rw [div_mul_div_comm, ← sq, hsqrtC]
  rw [dScale, atD_a_eq_av hP, Params.atD_L]
  push_cast
  ring

/-- Squared form consumed by the path energy. -/
theorem edgeEnergy_eq_finiteOverlap_sq
    (hP : P.Valid)
    (h8 : 8 * P.w ≤ P.L T)
    (h4pi : 4 * Real.pi * P.w ≤ P.L T)
    (V : OrderedCentralVerticesD Z P T)
    (i : Fin V.n) :
    edgeEnergy (canonicalPathData V) i
      = finiteOverlap V (leftVertex i)
          (rightVertex (shortFlag V) i) ^ 2 := by
  change
    ‖((Wmat (fun _ : dSimpleOnLine Z P T => (1 : ℝ))
        (dSimpleVector Z P T))ᴴ *
      Wmat (fun _ : dSimpleOnLine Z P T => (1 : ℝ))
        (dSimpleVector Z P T))
      (V.vertices (leftVertex i))
      (V.vertices (rightVertex (shortFlag V) i))‖ ^ 2
      = finiteOverlap V (leftVertex i)
          (rightVertex (shortFlag V) i) ^ 2
  rw [gramEntry_eq_finiteOverlap hP h8 h4pi V]
  simp [sq_abs]

end Zeta23.GapMatching.CanonicalOverlapD
