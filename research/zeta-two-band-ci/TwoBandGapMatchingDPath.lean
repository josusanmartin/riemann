/-
Copyright (c) 2026.
SPDX-License-Identifier: Apache-2.0

Construct the D-window matching core from an explicit ordered path of simple
critical-line atoms.

This module removes the matrix-core field from the analytic input.  Once an
injection of path vertices into the simple on-line subtype is supplied, the
path-forest theorem chooses a half-weight matching, the embedding theorem
turns it into disjoint pair slots, and the existing multiplicity-aware block
specialization proves the strengthened zero-side inequality.
-/
import Zeta23.GapMatching.TwoBandGapMatchingD
import Zeta23.GapMatching.GapMatchingBlockSpecialization
import Zeta23.GapMatching.DistinctGapMatchingPipeline
import Zeta23.GapMatching.PathForestMatching

noncomputable section
set_option linter.unusedSectionVars false

open Matrix Finset RHLinalg Filter
open scoped ComplexOrder BigOperators

namespace Zeta23.GapMatching.TwoBandGapMatchingDPath

open Zeta23
open Zeta23.ZeroSide
open Zeta23.ThmD
open Zeta23.GapMatching.TwoBandGapMatchingD
open Zeta23.GapMatching.GapMatchingBlockSpecialization
open Zeta23.GapMatching.PartialMatchingBonus
open Zeta23.GapMatching.PathForestMatching
open Zeta23.GapMatching.DistinctGapMatchingPipeline

/-- Canonical conjugation proof for the D-window at height `T`. -/
def dConj (P : Params) (T : ℝ) : PhiHatConj T (P.atD T) :=
  fun z => GzGp.phiHat_conj (P.atD T) T z

/-- The concrete block data for the actual height-dependent D-window. -/
abbrev dBlock (Z : ZeroConfig) (P : Params) (T : ℝ) :=
  blockData Z T (P.atD T) (dConj P T)

/-- Its subtype of simple critical-line atoms. -/
abbrev dSimpleOnLine (Z : ZeroConfig) (P : Params) (T : ℝ) :=
  SimpleOnLine (dBlock Z P T)

/-- The normalizing constant `a_D(T) L(T)^2`. -/
def dScale (P : Params) (T : ℝ) : ℝ :=
  (P.atD T).a T * (P.atD T).L T ^ 2

/-- Normalized evaluation vectors of the simple on-line atoms. -/
def dSimpleVector (Z : ZeroConfig) (P : Params) (T : ℝ) :
    dSimpleOnLine Z P T → Fin ((P.atD T).d T) → ℂ :=
  simpleVhat (dBlock Z P T) (dScale P T)

/-- A finite path of simple on-line D-window atoms.  Candidate starts are
`Fin n`; the vertex type `Fin (n+2)` permits both short edges `i -> i+1`
and long U-U edges `i -> i+2`. -/
structure PathDataD (Z : ZeroConfig) (P : Params) (T : ℝ) where
  n : ℕ
  U : ℕ → Bool
  short : ℕ → Bool
  disjoint : ∀ i, short i = true → U i = false
  vertices : Fin (n + 2) ↪ dSimpleOnLine Z P T

/-- Squared Gram overlap attached to one candidate edge. -/
def edgeEnergy
    {Z : ZeroConfig} {P : Params} {T : ℝ}
    (F : PathDataD Z P T) (i : Fin F.n) : ℝ :=
  embeddedCandidateEdgeEnergy F.short F.vertices
    (dSimpleVector Z P T) i

/-- Total energy of every active candidate before choosing a matching. -/
def candidateEnergy
    {Z : ZeroConfig} {P : Params} {T : ℝ}
    (F : PathDataD Z P T) : ℝ :=
  ∑ i ∈ activeEdges F.n F.U F.short, edgeEnergy F i

/-- The selected matching, chosen from the explicit two-colouring theorem. -/
noncomputable def selectedMatching
    {Z : ZeroConfig} {P : Params} {T : ℝ}
    (F : PathDataD Z P T) : Finset (Fin F.n) :=
  Classical.choose
    (exists_matching_half_weight F.disjoint (edgeEnergy F))

/-- Full specification of the selected matching. -/
theorem selectedMatching_spec
    {Z : ZeroConfig} {P : Params} {T : ℝ}
    (F : PathDataD Z P T) :
    selectedMatching F ⊆ activeEdges F.n F.U F.short ∧
      IsCandidateMatching F.short (selectedMatching F) ∧
      (1 / 2 : ℝ) * candidateEnergy F
        ≤ ∑ i ∈ selectedMatching F, edgeEnergy F i := by
  simpa [selectedMatching, candidateEnergy] using
    Classical.choose_spec
      (exists_matching_half_weight F.disjoint (edgeEnergy F))

/-- Energy presented by the selected disjoint pair slots. -/
def selectedEnergy
    {Z : ZeroConfig} {P : Params} {T : ℝ}
    (F : PathDataD Z P T) : ℝ :=
  embeddedCandidateMatchingEnergy F.short F.vertices
    (selectedMatching F) (dSimpleVector Z P T)

/-- The selected embedded-pair energy is definitionally the finite sum used
by `partialMatchingEnergyOfEmbedding`. -/
theorem partialMatchingEnergy_matchingEmbeddingInto
    {𝕜 : Type*} [RCLike 𝕜]
    {n : ℕ} {ι d : Type*}
    [Fintype ι] [DecidableEq ι]
    [Fintype d] [DecidableEq d]
    (short : ℕ → Bool)
    (z : Fin (n + 2) ↪ ι)
    (M : Finset (Fin n))
    (hM : IsCandidateMatching short M)
    (v : ι → d → 𝕜) :
    partialMatchingEnergyOfEmbedding (matchingEmbeddingInto z hM) v
      = embeddedCandidateMatchingEnergy short z M v := by
  simpa only [partialMatchingEnergyOfEmbedding,
    matchingEmbeddingInto_apply, pairSlotVertex_zero,
    pairSlotVertex_one, embeddedCandidateMatchingEnergy,
    embeddedCandidateEdgeEnergy, Finset.univ_eq_attach] using
    (Finset.sum_attach M (embeddedCandidateEdgeEnergy short z v))

/-- The path-selection theorem captures at least half of all active candidate
energy. -/
theorem candidateEnergy_le_two_selectedEnergy
    {Z : ZeroConfig} {P : Params} {T : ℝ}
    (F : PathDataD Z P T) :
    candidateEnergy F ≤ 2 * selectedEnergy F := by
  have hhalf := (selectedMatching_spec F).2.2
  simp only [selectedEnergy, embeddedCandidateMatchingEnergy,
    edgeEnergy] at hhalf ⊢
  nlinarith

/-- A fixed selected path matching yields the exact D-window matrix core. -/
theorem matchingCoreDAt_of_pathMatching
    {Z : ZeroConfig} {P : Params} {T : ℝ}
    (F : PathDataD Z P T)
    (M : Finset (Fin F.n))
    (hM : IsCandidateMatching F.short M)
    (hreal : PhiHatReal T (P.atD T))
    (hPois : PoissonSq T (P.atD T))
    (hc : 0 < dScale P T) :
    MatchingCoreDAt Z P T
      (embeddedCandidateMatchingEnergy F.short F.vertices M
        (dSimpleVector Z P T)) := by
  unfold MatchingCoreDAt
  rw [← partialMatchingEnergy_matchingEmbeddingInto
    F.short F.vertices M hM (dSimpleVector Z P T)]
  exact matchingCoreAt_of_embedding
    (Z := Z) (P := P.atD T) (T := T)
    (hconj := dConj P T) (hreal := hreal)
    (hPois := hPois) (hc := hc)
    (p := matchingEmbeddingInto F.vertices hM)

/-- For an admissible D-window, the selected matching core is automatic at
all heights where the standard D-window range hypotheses hold. -/
theorem selectedCore
    {Z : ZeroConfig} {P : Params} {T : ℝ}
    (hP : P.Valid)
    (h8 : 8 * P.w ≤ P.L T)
    (h4pi : 4 * Real.pi * P.w ≤ P.L T)
    (F : PathDataD Z P T) :
    MatchingCoreDAt Z P T (selectedEnergy F) := by
  have hL : 0 < P.L T := by
    linarith [hP.one_le_w]
  have hLD : 0 < (P.atD T).L T := by simpa using hL
  have haD : 0 < (P.atD T).a T := by
    linarith [(aD_range_of hP h8 h4pi).1]
  have hc : 0 < dScale P T := by
    unfold dScale
    exact mul_pos haD (pow_pos hLD 2)
  have hM := (selectedMatching_spec F).2.1
  exact matchingCoreDAt_of_pathMatching F (selectedMatching F) hM
    (fun r => GzGp.phiHat_ofReal (P.atD T) T r)
    (poissonSqD hP h8) hc

end Zeta23.GapMatching.TwoBandGapMatchingDPath
