/-
Copyright (c) 2026.
SPDX-License-Identifier: Apache-2.0

Identification of a canonical path edge with the finite normalized
Montgomery--Taylor Gram overlap.
-/
import Zeta23.GapMatching.CanonicalOneBandPathD
import Zeta23.GapMatching.DWindowFiniteGridApprox
import Zeta23.GapMatching.DWindowGramIdentity

noncomputable section

open Matrix Finset Real
open scoped BigOperators ComplexOrder

namespace Zeta23.GapMatching.CanonicalOverlapD

open Zeta23
open Zeta23.ZeroSide
open Zeta23.ThmD
open Zeta23.AdmWindow
open Zeta23.GapMatching.CentralPathConstructionD
open Zeta23.GapMatching.CanonicalOneBandPathD
open Zeta23.GapMatching.DWindowFiniteGridApprox
open Zeta23.GapMatching.DWindowGramIdentity
open Zeta23.GapMatching.PathForestMatching
open Zeta23.GapMatching.TwoBandGapMatchingDPath

variable {Z : ZeroConfig} {P : Params} {T : ℝ}

/-- The signed finite normalized overlap of two canonical vertices. -/
def finiteOverlap
    (V : OrderedCentralVerticesD Z P T)
    (i j : Fin (V.n + 2)) : ℝ :=
  finiteNormalizedOverlap (P.phiD T) (P.L T) T
    ((P.atD T).d T) (ordinate V i) (ordinate V j)

@[simp] theorem atomOrdinate_vertex
    (V : OrderedCentralVerticesD Z P T)
    (i : Fin (V.n + 2)) :
    atomOrdinate (V.vertices i) = ordinate V i := rfl

/-- The finite Fourier expression is the finite normalized overlap. -/
theorem finFourierOverlap_eq_finiteOverlap
    (hP : P.Valid)
    (V : OrderedCentralVerticesD Z P T)
    (i j : Fin (V.n + 2)) :
    finFourierOverlap (V.vertices i) (V.vertices j)
      = finiteOverlap V i j := by
  unfold finFourierOverlap finiteOverlap finiteNormalizedOverlap finiteBlock
  rw [dScale, atD_a_eq_av hP, Params.atD_L]
  simp_rw [atD_phiHatR hP, atD_tau_eq]
  rw [Fin.sum_univ_eq_sum_range]
  unfold normalizedTerm
  ring

/-- The Gram inner product of two canonical vertices is their real finite
normalized overlap. -/
theorem inner_eq_finiteOverlap
    (hP : P.Valid)
    (h8 : 8 * P.w ≤ P.L T)
    (h4pi : 4 * Real.pi * P.w ≤ P.L T)
    (V : OrderedCentralVerticesD Z P T)
    (i j : Fin (V.n + 2)) :
    inner (dSimpleVector Z P T (V.vertices i))
        (dSimpleVector Z P T (V.vertices j))
      = (finiteOverlap V i j : ℂ) := by
  have ha : 0 < (P.atD T).a T := by
    linarith [(aD_range_of hP h8 h4pi).1]
  have hL : 0 < P.L T := by linarith [hP.one_le_w]
  have hc : 0 < dScale P T := by
    unfold dScale
    exact mul_pos ha (pow_pos hL 2)
  rw [inner_eq_finFourierOverlap
    (fun r => GzGp.phiHat_ofReal _ T r) hc]
  exact_mod_cast finFourierOverlap_eq_finiteOverlap hP V i j

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
  unfold edgeEnergy embeddedCandidateEdgeEnergy
  rw [inner_eq_finiteOverlap hP h8 h4pi V]
  simp [sq_abs]

end Zeta23.GapMatching.CanonicalOverlapD
