/-
Copyright (c) 2026.
SPDX-License-Identifier: Apache-2.0

A recursive one-band gap word.  This is the finite combinatorial bridge
between Boolean bad-gap flags and the generic finite-state potential theorem.
-/
import Zeta23.GapMatching.FiniteStateGapPotential
import Zeta23.GapMatching.FiniteStatePathWeight
import Zeta23.GapMatching.OneBandPotentialSafeNumerics

noncomputable section

namespace Zeta23.GapMatching.OneBandGapWord

open Zeta23.GapMatching.FiniteStateGapPotential
open Zeta23.GapMatching.FiniteStatePathWeight
open Zeta23.GapMatching.OneBandPotentialSafeNumerics

/-- Interpret a Boolean bad-gap flag as a one-band state. -/
def stateOf (U : ℕ → Bool) (i : ℕ) : State :=
  if U i = true then .bad else .good

/-- State immediately before gap `i`; the word begins in the good state. -/
def previousState (U : ℕ → Bool) (i : ℕ) : State :=
  if i = 0 then .good else stateOf U (i - 1)

/-- One gap datum.  The long-edge weight attached to gap `i` is the edge
starting at `i-1`; no long edge enters the first gap. -/
def datumAt
    (U : ℕ → Bool)
    (length shortWeight longWeight : ℕ → ℝ)
    (i : ℕ) : GapDatum State where
  state := stateOf U i
  length := length i
  shortWeight := shortWeight i
  longFromPrev := if i = 0 then 0 else longWeight (i - 1)

/-- Consecutive gap data beginning at index `start`. -/
def wordFrom
    (U : ℕ → Bool)
    (length shortWeight longWeight : ℕ → ℝ) :
    ℕ → ℕ → List (GapDatum State)
  | _, 0 => []
  | start, count + 1 =>
      datumAt U length shortWeight longWeight start ::
        wordFrom U length shortWeight longWeight (start + 1) count

/-- The full word of `count` gaps. -/
def word
    (U : ℕ → Bool)
    (length shortWeight longWeight : ℕ → ℝ)
    (count : ℕ) : List (GapDatum State) :=
  wordFrom U length shortWeight longWeight 0 count

@[simp] theorem wordFrom_length
    (U : ℕ → Bool)
    (length shortWeight longWeight : ℕ → ℝ)
    (start count : ℕ) :
    (wordFrom U length shortWeight longWeight start count).length = count := by
  induction count generalizing start with
  | zero => simp [wordFrom]
  | succ count ih =>
      simp [wordFrom, ih]

@[simp] theorem word_length
    (U : ℕ → Bool)
    (length shortWeight longWeight : ℕ → ℝ)
    (count : ℕ) :
    (word U length shortWeight longWeight count).length = count := by
  simp [word]

@[simp] theorem previousState_zero (U : ℕ → Bool) :
    previousState U 0 = .good := by
  simp [previousState]

@[simp] theorem previousState_succ (U : ℕ → Bool) (i : ℕ) :
    previousState U (i + 1) = stateOf U i := by
  simp [previousState]

/-- Pointwise local certificates imply validity of every consecutive subword. -/
theorem valid_wordFrom
    {A B : ℝ}
    (U : ℕ → Bool)
    (length shortWeight longWeight : ℕ → ℝ)
    (phi : State → ℝ)
    (hlocal : ∀ i,
      LocalCertificate A B State.good phi
        (previousState U i)
        (datumAt U length shortWeight longWeight i)) :
    ∀ start count,
      ValidPath A B State.good phi (previousState U start)
        (wordFrom U length shortWeight longWeight start count) := by
  intro start count
  induction count generalizing start with
  | zero => simp [wordFrom, ValidPath]
  | succ count ih =>
      simp only [wordFrom, ValidPath]
      refine ⟨hlocal start, ?_⟩
      simpa [datumAt] using ih (start + 1)

/-- Pointwise local certificates imply validity of the full word. -/
theorem valid_word
    {A B : ℝ}
    (U : ℕ → Bool)
    (length shortWeight longWeight : ℕ → ℝ)
    (phi : State → ℝ)
    (hlocal : ∀ i,
      LocalCertificate A B State.good phi
        (previousState U i)
        (datumAt U length shortWeight longWeight i))
    (count : ℕ) :
    ValidPath A B State.good phi State.good
      (word U length shortWeight longWeight count) := by
  simpa [word] using
    valid_wordFrom U length shortWeight longWeight phi hlocal 0 count

/-- The sole endpoint term omitted by `pathWeight` is the short weight of the
last gap in a nonempty consecutive word. -/
theorem finalShort_wordFrom
    (U : ℕ → Bool)
    (length shortWeight longWeight : ℕ → ℝ) :
    ∀ start count,
      finalShort State.good
          (wordFrom U length shortWeight longWeight start (count + 1))
        = if stateOf U (start + count) = State.good then
            shortWeight (start + count) else 0 := by
  intro start count
  induction count generalizing start with
  | zero =>
      simp [wordFrom, finalShort, datumAt]
  | succ count ih =>
      simp only [wordFrom, finalShort]
      change finalShort State.good
          (wordFrom U length shortWeight longWeight
            (start + 1) (count + 1))
        = if stateOf U (start + (count + 1)) = State.good then
            shortWeight (start + (count + 1)) else 0
      simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
        using ih (start + 1)

/-- Full-word endpoint specialization. -/
theorem finalShort_word
    (U : ℕ → Bool)
    (length shortWeight longWeight : ℕ → ℝ)
    (count : ℕ) :
    finalShort State.good
        (word U length shortWeight longWeight (count + 1))
      = if stateOf U count = State.good then shortWeight count else 0 := by
  simpa [word] using
    finalShort_wordFrom U length shortWeight longWeight 0 count

/-- Local candidate contribution read directly from the Boolean word. -/
def localWeight
    (U : ℕ → Bool)
    (shortWeight longWeight : ℕ → ℝ)
    (i : ℕ) : ℝ :=
  (if U i = false then shortWeight i else 0) +
    (if i = 0 then 0
     else if U (i - 1) = false then 0
     else if U i = false then 0
     else longWeight (i - 1))

/-- The generic `stepWeight` is exactly `localWeight`. -/
theorem stepWeight_datumAt
    (U : ℕ → Bool)
    (length shortWeight longWeight : ℕ → ℝ)
    (i : ℕ) :
    stepWeight State.good (previousState U i)
      (datumAt U length shortWeight longWeight i)
      = localWeight U shortWeight longWeight i := by
  rcases i with _ | i
  · cases hU : U 0 <;>
      simp [stateOf, previousState, datumAt, localWeight, stepWeight, hU]
  · cases hprev : U i <;> cases hcur : U (i + 1) <;>
      simp [stateOf, previousState, datumAt, localWeight, stepWeight,
        hprev, hcur]

/-- Candidate weight of a consecutive subword is the corresponding finite
sum of explicit local contributions. -/
theorem candidateWeight_wordFrom
    (U : ℕ → Bool)
    (length shortWeight longWeight : ℕ → ℝ) :
    ∀ start count,
      candidateWeight State.good (previousState U start)
        (wordFrom U length shortWeight longWeight start count)
        = ∑ j ∈ Finset.range count,
            localWeight U shortWeight longWeight (start + j) := by
  intro start count
  induction count generalizing start with
  | zero => simp [wordFrom, candidateWeight]
  | succ count ih =>
      rw [Finset.sum_range_succ']
      simp only [wordFrom, candidateWeight]
      rw [stepWeight_datumAt]
      have htail :
          candidateWeight State.good
              (datumAt U length shortWeight longWeight start).state
              (wordFrom U length shortWeight longWeight (start + 1) count)
            = ∑ j ∈ Finset.range count,
                localWeight U shortWeight longWeight (start + 1 + j) := by
        simpa [datumAt] using ih (start + 1)
      rw [htail]
      have hshift :
          (∑ j ∈ Finset.range count,
              localWeight U shortWeight longWeight (start + 1 + j))
            = ∑ j ∈ Finset.range count,
                localWeight U shortWeight longWeight (start + (j + 1)) := by
        apply Finset.sum_congr rfl
        intro j hj
        congr 1
        omega
      rw [hshift]
      simp only [Nat.add_zero]
      ring

/-- Candidate weight of the full word. -/
theorem candidateWeight_word
    (U : ℕ → Bool)
    (length shortWeight longWeight : ℕ → ℝ)
    (count : ℕ) :
    candidateWeight State.good State.good
      (word U length shortWeight longWeight count)
      = ∑ i ∈ Finset.range count,
          localWeight U shortWeight longWeight i := by
  simpa [word] using
    candidateWeight_wordFrom U length shortWeight longWeight 0 count

/-- Total length of a consecutive subword is the corresponding finite sum. -/
theorem totalLength_wordFrom
    (U : ℕ → Bool)
    (length shortWeight longWeight : ℕ → ℝ) :
    ∀ start count,
      totalLength (wordFrom U length shortWeight longWeight start count)
        = ∑ j ∈ Finset.range count, length (start + j) := by
  intro start count
  induction count generalizing start with
  | zero => simp [wordFrom, totalLength]
  | succ count ih =>
      rw [Finset.sum_range_succ']
      simp only [wordFrom, totalLength]
      rw [ih (start + 1)]
      change length start +
          (∑ j ∈ Finset.range count, length (start + 1 + j))
        = (∑ j ∈ Finset.range count, length (start + (j + 1)))
          + length (start + 0)
      have hshift :
          (∑ j ∈ Finset.range count, length (start + 1 + j))
            = ∑ j ∈ Finset.range count, length (start + (j + 1)) := by
        apply Finset.sum_congr rfl
        intro j hj
        congr 1
        omega
      rw [hshift]
      simp only [Nat.add_zero]
      ring

/-- Total length of the full word. -/
theorem totalLength_word
    (U : ℕ → Bool)
    (length shortWeight longWeight : ℕ → ℝ)
    (count : ℕ) :
    totalLength (word U length shortWeight longWeight count)
      = ∑ i ∈ Finset.range count, length i := by
  simpa [word] using
    totalLength_wordFrom U length shortWeight longWeight 0 count

end Zeta23.GapMatching.OneBandGapWord
