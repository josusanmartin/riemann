/-
The retained actual word uses the first `n` of the `n+1` consecutive central
gaps, so its total normalized length is bounded by the full central path.
-/
import Zeta23.GapMatching.OneBandActualWordDCore
import Zeta23.GapMatching.CentralGapGeometryD

noncomputable section

namespace Zeta23.GapMatching.ActualWordLengthD

open Zeta23
open Zeta23.GapMatching.FiniteStateGapPotential
open Zeta23.GapMatching.OneBandGapWord
open Zeta23.GapMatching.OneBandActualWordDCore
open Zeta23.GapMatching.CentralGapGeometryD
open Zeta23.GapMatching.CanonicalOneBandPathD

variable {Z : ZeroConfig} {P : Params} {T : ℝ}

/-- Finite retained-word length is no larger than the full central gap list. -/
theorem totalLength_actualWord_le_normalizedGapList
    (V : OrderedCentralVerticesD Z P T)
    (hL : 0 ≤ P.L T) :
    totalLength
        (word (badFlag V) (gapAtNat V)
          (fun i => shortOverlapNat V i ^ 2)
          (fun i => longOverlapNat V i ^ 2) V.n)
      ≤ (normalizedGapList V).sum := by
  rw [totalLength_word]
  exact?

/-- Any available full-path length bound transfers to the retained word. -/
theorem totalLength_actualWord_le_count
    (V : OrderedCentralVerticesD Z P T)
    (hL : 0 ≤ P.L T)
    (hfull : (normalizedGapList V).sum
      ≤ (Z.N T (2 * T) : ℝ)) :
    totalLength
        (word (badFlag V) (gapAtNat V)
          (fun i => shortOverlapNat V i ^ 2)
          (fun i => longOverlapNat V i ^ 2) V.n)
      ≤ (Z.N T (2 * T) : ℝ) :=
  (totalLength_actualWord_le_normalizedGapList V hL).trans hfull

end Zeta23.GapMatching.ActualWordLengthD
