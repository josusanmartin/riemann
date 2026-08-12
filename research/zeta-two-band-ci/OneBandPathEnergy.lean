/-
Copyright (c) 2026.
SPDX-License-Identifier: Apache-2.0

Exact comparison between the recursive one-band word weight and the active
candidate energy of the canonical path.
-/
import Zeta23.GapMatching.OneBandGapWord
import Zeta23.GapMatching.FiniteStatePathWeight
import Zeta23.GapMatching.CanonicalOneBandPathD

noncomputable section

open scoped BigOperators

namespace Zeta23.GapMatching.OneBandPathEnergy

open Zeta23
open Zeta23.GapMatching.FiniteStateGapPotential
open Zeta23.GapMatching.FiniteStatePathWeight
open Zeta23.GapMatching.OneBandGapWord
open Zeta23.GapMatching.OneBandPotentialSafeNumerics
open Zeta23.GapMatching.CanonicalOneBandPathD
open Zeta23.GapMatching.CentralPathConstructionD
open Zeta23.GapMatching.PathForestMatching
open Zeta23.GapMatching.TwoBandGapMatchingDPath

/-- Candidate contribution beginning at one gap. -/
def startWeight
    (U : ℕ → Bool) (shortWeight longWeight : ℕ → ℝ)
    (i : ℕ) : ℝ :=
  if U i = false then shortWeight i
  else if U (i + 1) = true then longWeight i else 0

/-- The path-start weight of a word with `count+1` gaps is the sum of the
first `count` explicit start contributions. -/
theorem pathWeight_wordFrom_succ
    (U : ℕ → Bool)
    (length shortWeight longWeight : ℕ → ℝ) :
    ∀ start count,
      pathWeight State.good
          (wordFrom U length shortWeight longWeight start (count + 1))
        = ∑ j ∈ Finset.range count,
            startWeight U shortWeight longWeight (start + j) := by
  intro start count
  induction count generalizing start with
  | zero =>
      simp [wordFrom, pathWeight]
  | succ count ih =>
      rw [Finset.sum_range_succ']
      simp only [wordFrom, pathWeight]
      have htail := ih (start + 1)
      have hshift :
          (∑ j ∈ Finset.range count,
              startWeight U shortWeight longWeight (start + 1 + j))
            = ∑ j ∈ Finset.range count,
                startWeight U shortWeight longWeight (start + (j + 1)) := by
        apply Finset.sum_congr rfl
        intro j hj
        congr 1
        omega
      rw [htail, hshift]
      cases h0 : U start <;> cases h1 : U (start + 1) <;>
        simp [datumAt, stateOf, startWeight, h0, h1,
          Nat.add_assoc] <;> ring

/-- Full-word version. -/
theorem pathWeight_word_succ
    (U : ℕ → Bool)
    (length shortWeight longWeight : ℕ → ℝ)
    (count : ℕ) :
    pathWeight State.good
        (word U length shortWeight longWeight (count + 1))
      = ∑ i ∈ Finset.range count,
          startWeight U shortWeight longWeight i := by
  simpa [word] using
    pathWeight_wordFrom_succ U length shortWeight longWeight 0 count

variable {Z : ZeroConfig} {P : Params} {T : ℝ}

/-- Total natural-number extension of the canonical candidate edge energy. -/
def edgeAtNat (V : OrderedCentralVerticesD Z P T) (i : ℕ) : ℝ :=
  if hi : i < V.n then
    edgeEnergy (canonicalPathData V) ⟨i, hi⟩
  else 0

@[simp] theorem edgeAtNat_fin
    (V : OrderedCentralVerticesD Z P T) (i : Fin V.n) :
    edgeAtNat V i = edgeEnergy (canonicalPathData V) i := by
  simp only [edgeAtNat, dif_pos i.isLt]
  congr

/-- On a genuine candidate start, the word contribution is exactly the
candidate edge energy; otherwise it vanishes. -/
theorem startWeight_edgeAtNat
    (V : OrderedCentralVerticesD Z P T)
    (i : Fin V.n) :
    startWeight (badFlag V) (edgeAtNat V) (edgeAtNat V) i
      = if Active (badFlag V) (shortFlag V) i then
          edgeEnergy (canonicalPathData V) i
        else 0 := by
  cases h0 : badFlag V i <;> cases h1 : badFlag V (i + 1) <;>
    simp [startWeight, Active, shortFlag, h0, h1]

/-- The recursive path weight is exactly the total active candidate energy. -/
theorem pathWeight_eq_candidateEnergy
    (V : OrderedCentralVerticesD Z P T)
    (length : ℕ → ℝ) :
    pathWeight State.good
        (word (badFlag V) length (edgeAtNat V) (edgeAtNat V)
          (V.n + 1))
      = candidateEnergy (canonicalPathData V) := by
  rw [pathWeight_word_succ]
  rw [Finset.sum_range]
  unfold candidateEnergy activeEdges
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i hi
  exact startWeight_edgeAtNat V i

/-- The full finite-state candidate weight differs from the candidate energy
by at most the sole omitted final short edge. -/
theorem candidateWeight_le_candidateEnergy_add_one
    (V : OrderedCentralVerticesD Z P T)
    (length : ℕ → ℝ)
    (hshort : ∀ i, edgeAtNat V i ≤ 1) :
    candidateWeight State.good State.good
        (word (badFlag V) length (edgeAtNat V) (edgeAtNat V)
          (V.n + 1))
      ≤ candidateEnergy (canonicalPathData V) + 1 := by
  have hendpoint := candidateWeight_le_path_add_one State.good
    (word (badFlag V) length (edgeAtNat V) (edgeAtNat V)
      (V.n + 1))
    (by
      intro g hg
      simp only [word, wordFrom] at hg
      induction V.n generalizing g with
      | zero =>
          simp [wordFrom, datumAt] at hg
          rcases hg with rfl
          exact hshort 0
      | succ n ih =>
          simp [wordFrom] at hg
          rcases hg with rfl | hg
          · exact hshort 0
          · exact hshort _)
  rw [pathWeight_eq_candidateEnergy V length] at hendpoint
  exact hendpoint

end Zeta23.GapMatching.OneBandPathEnergy