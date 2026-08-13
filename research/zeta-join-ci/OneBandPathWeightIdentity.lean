/-
Copyright (c) 2026.
SPDX-License-Identifier: Apache-2.0

Exact identification of the recursive one-band word weight with the finite
candidate-start energy used by the path-forest matching theorem.
-/
import Zeta23.GapMatching.OneBandGapWord
import Zeta23.GapMatching.FiniteStatePathWeight
import Zeta23.GapMatching.PathForestMatching

noncomputable section

namespace Zeta23.GapMatching.OneBandPathWeightIdentity

open Zeta23.GapMatching.FiniteStateGapPotential
open Zeta23.GapMatching.FiniteStatePathWeight
open Zeta23.GapMatching.OneBandGapWord
open Zeta23.GapMatching.OneBandPotentialSafeNumerics
open Zeta23.GapMatching.PathForestMatching

/-- Complementary short flag attached to a Boolean bad-gap sequence. -/
def shortOf (U : ℕ → Bool) (i : ℕ) : Bool := !(U i)

@[simp] theorem shortOf_true_iff (U : ℕ → Bool) (i : ℕ) :
    shortOf U i = true ↔ U i = false := by
  cases h : U i <;> simp [shortOf, h]

/-- Numerical contribution of candidate start `i`. -/
def startWeight
    (U : ℕ → Bool) (edge : ℕ → ℝ) (i : ℕ) : ℝ :=
  if Active U (shortOf U) i then edge i else 0

/-- The local recursive path contribution is exactly the corresponding active
candidate-start contribution. -/
theorem local_path_contribution
    (U : ℕ → Bool) (length edge : ℕ → ℝ) (i : ℕ) :
    (if (datumAt U length edge edge i).state = State.good then
        (datumAt U length edge edge i).shortWeight else 0)
      + (if (datumAt U length edge edge i).state = State.good then 0
         else if (datumAt U length edge edge (i + 1)).state = State.good
           then 0
         else (datumAt U length edge edge (i + 1)).longFromPrev)
      = startWeight U edge i := by
  cases hi : U i <;> cases hj : U (i + 1) <;>
    simp [datumAt, stateOf, startWeight, Active, shortOf, hi, hj]

/-- A subword of `count+1` gaps contains exactly `count` candidate starts. -/
theorem pathWeight_wordFrom
    (U : ℕ → Bool) (length edge : ℕ → ℝ) :
    ∀ start count,
      pathWeight State.good
        (wordFrom U length edge edge start (count + 1))
        = ∑ j ∈ Finset.range count,
            startWeight U edge (start + j) := by
  intro start count
  induction count generalizing start with
  | zero =>
      simp [wordFrom, pathWeight]
  | succ count ih =>
      rw [Finset.sum_range_succ']
      simp only [wordFrom, pathWeight]
      rw [local_path_contribution]
      rw [ih (start + 1)]
      apply congrArg (fun x : ℝ => startWeight U edge start + x)
      apply Finset.sum_congr rfl
      intro j hj
      congr 1
      omega

/-- Full-word specialization. -/
theorem pathWeight_word
    (U : ℕ → Bool) (length edge : ℕ → ℝ) (n : ℕ) :
    pathWeight State.good (word U length edge edge (n + 1))
      = ∑ i ∈ Finset.range n, startWeight U edge i := by
  simpa [word] using pathWeight_wordFrom U length edge 0 n

/-- Rewrite a finite active-edge sum as the range sum of `startWeight`. -/
theorem sum_activeEdges_eq
    (U : ℕ → Bool) (edge : Fin n → ℝ) :
    ∑ i ∈ activeEdges n U (shortOf U), edge i
      = ∑ i ∈ Finset.range n,
          startWeight U (fun j =>
            if hj : j < n then edge ⟨j, hj⟩ else 0) i := by
  classical
  rw [activeEdges]
  simp only [Finset.sum_filter, Finset.sum_range]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hactive : Active U (shortOf U) i
  · simp [startWeight, hactive]
  · simp [startWeight, hactive]

end Zeta23.GapMatching.OneBandPathWeightIdentity
