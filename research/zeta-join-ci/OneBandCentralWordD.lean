/-
Error-explicit one-band word package stated directly in terms of the guarded
simple-path cardinality.  No global zero-count field is overloaded in this
interface.
-/
import Zeta23.GapMatching.FiniteStateGapPotential
import Zeta23.GapMatching.OneBandPotentialSafeNumerics

noncomputable section

namespace Zeta23.GapMatching.OneBandCentralWordD

open Zeta23
open Zeta23.GapMatching.FiniteStateGapPotential
open Zeta23.GapMatching.OneBandPotentialSafeNumerics

/-- One finite guarded word at height `T`. -/
structure CentralWordAt (Z : ZeroConfig) (T : ℝ) where
  gaps : List (GapDatum State)
  centralSimple : ℝ
  W : ℝ
  countError : ℝ
  lengthError : ℝ
  valid : ValidPath A B State.good phi State.good gaps
  count_lower : centralSimple - countError ≤ (gaps.length : ℝ)
  length_upper : totalLength gaps ≤
    (Z.N T (2 * T) : ℝ) + lengthError
  candidate_le : candidateWeight State.good State.good gaps ≤ W

/-- The only word-level asymptotic error: endpoint count, normalized length,
and the bounded state-potential endpoint. -/
def wordError {Z : ZeroConfig} {T : ℝ}
    (G : CentralWordAt Z T) : ℝ :=
  A * G.countError + B * G.lengthError + boundary

/-- Exact finite word-energy lower bound. -/
theorem word_weight_lower
    {Z : ZeroConfig} {T : ℝ} (G : CentralWordAt Z T) :
    A * G.centralSimple
        - B * (Z.N T (2 * T) : ℝ) - wordError G
      ≤ G.W := by
  have hA0 : 0 ≤ A := parameter_ranges.1.le
  have hB0 : 0 ≤ B := parameter_ranges.2.2.1
  have hmain := candidateWeight_lower_with_errors
    (State := State)
    State.good phi hA0 hB0 rfl potential_boundary
    G.gaps G.valid rfl
    (guardError := 0)
    (fullSimple := G.centralSimple)
    (centralSimple := G.centralSimple)
    (by linarith)
    G.count_lower G.length_upper G.candidate_le
  simpa [wordError] using hmain

end Zeta23.GapMatching.OneBandCentralWordD
