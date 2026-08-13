/-
Copyright (c) 2026.
SPDX-License-Identifier: Apache-2.0

Finite one-band theorem: local gap certificates imply a lower bound for the
full active candidate-edge energy, with the exact padded endpoint loss.
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
weight `p`. -/
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
  unfold activeEnergy
  rw [sum_activeEdges_eq]
  apply Finset.sum_congr rfl
  intro i hi
  have hin : i < n := Finset.mem_range.mp hi
  by_cases hactive : Active U (shortOf U) i
  · simp [startWeight, hactive, edgeExtension, hin]
  · simp [startWeight, hactive]

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

/-- The only endpoint correction is the padded final short edge of weight
exactly `p`. -/
theorem finalShort_gapWord_le_p
    {n : ℕ} (U : ℕ → Bool)
    (length : ℕ → ℝ) (edge : Fin n → ℝ) :
    finalShort State.good (gapWord U length edge) ≤ p := by
  rw [show gapWord U length edge =
      word U (lengthExtension n length)
        (edgeExtension edge) (edgeExtension edge) (n + 1) by rfl]
  rw [finalShort_word]
  simp only [edgeExtension_endpoint]
  split <;> norm_num [p]

/-- Endpoint comparison with the exact padded weight. -/
theorem candidateWeight_gapWord_le_path_add_p
    {n : ℕ} (U : ℕ → Bool)
    (length : ℕ → ℝ) (edge : Fin n → ℝ) :
    candidateWeight State.good State.good (gapWord U length edge)
      ≤ pathWeight State.good (gapWord U length edge) + p := by
  rw [candidateWeight_eq_path_add_final]
  have hfinal := finalShort_gapWord_le_p U length edge
  linarith

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
  · have hle : n + 1 ≤ i := not_lt.mp hi
    have hcur : U i = false := hUtail i hle
    have hien : ¬ i < n := by omega
    have hi0 : i ≠ 0 := by omega
    apply localCertificate_of_dominates
    cases hprev : previousState U i <;>
      simp [datumAt, stateOf, hcur, lengthExtension, hi,
        edgeExtension, hien, hi0, hprev, physicalFloor,
        lengthFloor, shortFloor, longFloor, stepCost, stepWeight]
    all_goals norm_num [B, p, lengthThreshold]

/-- **Finite one-band bonus.**  Once each genuine gap has its local
certificate, the active candidate energy receives the full potential reward,
up to the exact endpoint constant `boundary + p`. -/
theorem activeEnergy_lower
    {n : ℕ} (U : ℕ → Bool)
    (length : ℕ → ℝ) (edge : Fin n → ℝ)
    (hUtail : ∀ i, n + 1 ≤ i → U i = false)
    (hlocal : ∀ i, i < n + 1 →
      LocalCertificate A B State.good phi
        (previousState U i)
        (datumAt U (lengthExtension n length)
          (edgeExtension edge) (edgeExtension edge) i)) :
    A * ((n + 1 : ℕ) : ℝ) - boundary
        - B * (∑ i ∈ Finset.range (n + 1), length i) - p
      ≤ activeEnergy n U edge := by
  have hvalid := valid_gapWord U length edge hUtail hlocal
  have hword := candidateWeight_lower
    State.good phi rfl potential_boundary
      (gapWord U length edge) hvalid
  rw [gapWord_length, totalLength_gapWord] at hword
  have hendpoint := candidateWeight_gapWord_le_path_add_p U length edge
  rw [pathWeight_gapWord_eq_activeEnergy] at hendpoint
  nlinarith

end Zeta23.GapMatching.OneBandFixedHeightBonus
