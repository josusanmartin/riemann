/-
Bounded recursion for `OneBandGapWord.word`.  Unlike the convenience theorem
in the base module, this version asks for local certificates only at indices
which actually occur in the finite word.
-/
import Zeta23.GapMatching.OneBandGapWord

noncomputable section

namespace Zeta23.GapMatching.OneBandGapWordBounded

open Zeta23.GapMatching.FiniteStateGapPotential
open Zeta23.GapMatching.OneBandGapWord
open Zeta23.GapMatching.OneBandPotentialSafeNumerics

/-- Pointwise certificates on the used interval imply validity of one
consecutive subword. -/
theorem valid_wordFrom_bounded
    {A B : ℝ}
    (U : ℕ → Bool)
    (length shortWeight longWeight : ℕ → ℝ)
    (phi : State → ℝ) :
    ∀ start count,
      (∀ i, start ≤ i → i < start + count →
        LocalCertificate A B State.good phi
          (previousState U i)
          (datumAt U length shortWeight longWeight i)) →
      ValidPath A B State.good phi (previousState U start)
        (wordFrom U length shortWeight longWeight start count) := by
  intro start count
  induction count generalizing start with
  | zero => simp [wordFrom, ValidPath]
  | succ count ih =>
      intro hlocal
      simp only [wordFrom, ValidPath]
      refine ⟨hlocal start (by omega) (by omega), ?_⟩
      apply ih (start + 1)
      intro i hlo hhi
      exact hlocal i (by omega) (by omega)

/-- Bounded validity for the full word. -/
theorem valid_word_bounded
    {A B : ℝ}
    (U : ℕ → Bool)
    (length shortWeight longWeight : ℕ → ℝ)
    (phi : State → ℝ)
    (count : ℕ)
    (hlocal : ∀ i, i < count →
      LocalCertificate A B State.good phi
        (previousState U i)
        (datumAt U length shortWeight longWeight i)) :
    ValidPath A B State.good phi State.good
      (word U length shortWeight longWeight count) := by
  simpa [word] using
    valid_wordFrom_bounded U length shortWeight longWeight phi 0 count
      (by
        intro i hlo hhi
        exact hlocal i (by omega))

end Zeta23.GapMatching.OneBandGapWordBounded
