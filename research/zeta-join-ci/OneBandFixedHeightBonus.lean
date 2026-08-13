/-
Copyright (c) 2026.
SPDX-License-Identifier: Apache-2.0

Finite one-band theorem: local gap certificates imply a lower bound for the
full active candidate-edge energy, with the sole endpoint loss made explicit.
-/
import Zeta23.GapMatching.OneBandGapWord
import Zeta23.GapMatching.OneBandPathWeightIdentity
import Zeta23.GapMatching.FiniteStatePathWeight

noncomputable section

namespace Zeta23.GapMatching.OneBandFixedHeightBonus

open Zeta23.GapMatching.FiniteStateGapPotential
open Zeta23.GapMatching.FiniteStatePathWeight
open Zeta23.GapMatching.OneBandGapWord
open Zeta23.GapMatching.OneBandPathWeightIdentity
open Zeta23.GapMatching.OneBandPotentialSafeNumerics
open Zeta23.GapMatching.PathForestMatching

/-- Extend the `n` genuine candidate energies by the harmless endpoint short
weight `p`.  Values after the endpoint are also `p`; they are never read by
the finite word but make the global recursive certificate convenient. -/
def edgeExtension {n : ℕ} (edge : Fin n → ℝ) (i : ℕ) : ℝ :=
  if hi : i < n then edge ⟨i, hi⟩ else p

/-- Extend the `n+1` genuine gaps by the safe length threshold. -/
def lengthExtension (n : ℕ) (length : ℕ → ℝ) (i : ℕ) : ℝ :=
  if i < n + 1 then length i else lengthThreshold

/-- Total energy over every active candidate start. -/
def activeEnergy (n : ℕ) (U : ℕ → Bool)
    (edge : Fin n → ℝ) : ℝ :=
  ∑ i ∈ activeEdges n U (shortOf U), edge i

/-- The recursive word attached to `n+1` gaps. -/
def gapWord {n : ℕ} (U : ℕ → Bool)
    (length : ℕ → ℝ) (edge : Fin n → ℝ) :
    List (GapDatum State) :=
  word U (lengthExtension n length)
    (edgeExtension edge) (edgeExtension edge) (n + 1)

@[simp] theorem gapWord_length {n : ℕ} (U : ℕ → Bool)
    (length : ℕ → ℝ) (edge : Fin n → ℝ) :
    (gapWord U length edge).length = n + 1 := by
  simp [gapWord]

/-- On a genuine candidate start, the extension is the original energy. -/
@[simp] theorem edgeExtension_apply {n : ℕ} (edge : Fin n → ℝ)
    (i : Fin n) :
    edgeExtension edge i = edge i := by
  simp [edgeExtension, i.isLt]

/-- The endpoint extension is exactly `p`. -/
@[simp] theorem edgeExtension_endpoint {n : ℕ} (edge : Fin n → ℝ) :
    edgeExtension edge n = p := by
  simp [edgeExtension]

/-- The path-start weight is exactly the active candidate energy. -/
theorem pathWeight_gapWord_eq_activeEnergy
    {n : ℕ} (U : ℕ → Bool)
    (length : ℕ → ℝ) (edge : Fin n → ℝ) :
    pathWeight State.good (gapWord U length edge)
      = activeEnergy n U edge := by
  rw [show gapWord U length edge =
      word U (lengthExtension n length)
        (edgeExtension edge) (edgeExtension edge) (n + 1) by rfl]
  rw [pathWeight_word]
  rw [sum_activeEdges_eq]
  apply Finset.sum_congr rfl
  intro i hi
  have hin : i < n := Finset.mem_range.mp hi
  unfold startWeight
  split <;> simp [edgeExtension, hin]

/-- Total word length is the sum of the `n+1` genuine normalized gaps. -/
theorem totalLength_gapWord
    {n : ℕ} (U : ℕ → Bool)
    (length : ℕ → ℝ) (edge : Fin n → ℝ) :
    totalLength (gapWord U length edge)
      = ∑ i ∈ Finset.range (n + 1), length i := by
  rw [show gapWord U length edge =
      word U (lengthExtension n length)
        (edgeExtension edge) (edgeExtension edge) (n + 1) by rfl]
  rw [totalLength_word]
  apply Finset.sum_congr rfl
  intro i hi
  have hin : i < n + 1 := Finset.mem_range.mp hi
  simp [lengthExtension, hin]

/-- A convenient global local-certificate extension.  The substantive local
input is needed only on the genuine `n+1` gaps; after that the word is padded
by a good gap of length two and short weight `p`. -/
theorem valid_gapWord
    {n : ℕ} (U : ℕ → Bool)
    (length : ℕ → ℝ) (edge : Fin n → ℝ)
    (hUtail : ∀ i, n + 1 ≤ i → U i = false)
    (hlocal : ∀ i, i < n + 1 →
      LocalCertificate A B State.good phi
        (previousState U i)
        (datumAt U (lengthExtension n length)
          (edgeExtension edge) (edgeExtension edge) i)) :
    ValidPath A B State.good phi State.good
      (gapWord U length edge) := by
  apply valid_word U (lengthExtension n length)
    (edgeExtension edge) (edgeExtension edge) phi
  intro i
  by_cases hi : i < n + 1
  · exact hlocal i hi
  · have hcur : U i = false := hUtail i (not_lt.mp hi)
    have hprev : previousState U i = State.good := by
      rcases i with _ | i
      · simp [previousState]
      · have hle : n + 1 ≤ i + 1 := not_lt.mp hi
        have hprevFalse : U i = false := by
          apply hUtail i
          omega
        simp [previousState, stateOf, hprevFalse]
    have hstate : stateOf U i = State.good := by
      simp [stateOf, hcur]
    apply localCertificate_of_dominates
    simp [datumAt, lengthExtension, edgeExtension, hi,
      hcur, hprev, hstate, physicalFloor, lengthFloor,
      shortFloor, longFloor, stepCost, stepWeight]
    norm_num [B, p, lengthThreshold]

/-- Every short weight in the padded finite word is at most one. -/
theorem gapWord_shortWeight_le_one
    {n : ℕ} (U : ℕ → Bool)
    (length : ℕ → ℝ) (edge : Fin n → ℝ)
    (hedge : ∀ i, edge i ≤ 1) :
    ∀ g ∈ gapWord U length edge, g.shortWeight ≤ 1 := by
  intro g hg
  rw [show gapWord U length edge =
      word U (lengthExtension n length)
        (edgeExtension edge) (edgeExtension edge) (n + 1) by rfl] at hg
  simp only [word, List.mem_ofFn] at hg
  -- `wordFrom` is recursive rather than `ofFn`; recover the originating
  -- index by induction over the finite word.
  induction n with
  | zero =>
      simp [word, wordFrom, datumAt, edgeExtension] at hg ⊢
      rcases hg with rfl
      norm_num [p]
  | succ n ih =>
      simp only [word, wordFrom, List.mem_cons] at hg
      rcases hg with rfl | hg
      · simp [datumAt, edgeExtension]
        split
        · exact hedge _
        · norm_num [p]
      · -- The tail consists of the same bounded extension starting at one.
        -- A direct membership induction avoids changing the extension origin.
        clear ih
        generalize hcount : n + 1 = count at hg
        generalize hstart : 1 = start at hg
        induction count generalizing start with
        | zero => simp [wordFrom] at hg
        | succ count iht =>
            simp only [wordFrom, List.mem_cons] at hg
            rcases hg with rfl | hg
            · simp [datumAt, edgeExtension]
              split
              · exact hedge _
              · norm_num [p]
            · exact iht (start + 1) hg

/-- **Finite one-band bonus.**  Once each genuine gap has its local
certificate, the active candidate energy receives the full potential reward,
up to the exact endpoint constant `boundary + 1`. -/
theorem activeEnergy_lower
    {n : ℕ} (U : ℕ → Bool)
    (length : ℕ → ℝ) (edge : Fin n → ℝ)
    (hUtail : ∀ i, n + 1 ≤ i → U i = false)
    (hlocal : ∀ i, i < n + 1 →
      LocalCertificate A B State.good phi
        (previousState U i)
        (datumAt U (lengthExtension n length)
          (edgeExtension edge) (edgeExtension edge) i))
    (hedge : ∀ i, edge i ≤ 1) :
    A * ((n + 1 : ℕ) : ℝ) - boundary
        - B * (∑ i ∈ Finset.range (n + 1), length i) - 1
      ≤ activeEnergy n U edge := by
  let gaps := gapWord U length edge
  have hvalid := valid_gapWord U length edge hUtail hlocal
  have hword := candidateWeight_lower
    State.good phi rfl potential_boundary gaps hvalid
  have hendpoint := candidateWeight_le_path_add_one
    State.good gaps (gapWord_shortWeight_le_one U length edge hedge)
  rw [gapWord_length, totalLength_gapWord,
    pathWeight_gapWord_eq_activeEnergy] at hword hendpoint
  nlinarith

end Zeta23.GapMatching.OneBandFixedHeightBonus
