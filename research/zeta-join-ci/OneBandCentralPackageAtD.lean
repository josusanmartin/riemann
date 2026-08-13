/-
One-height assembly of the guarded central one-band word and selected D-window
matching core.
-/
import Zeta23.GapMatching.OneBandWordEnergyD
import Zeta23.GapMatching.OneBandCentralWordD
import Zeta23.GapMatching.PathDataDCoreAdapter

noncomputable section

namespace Zeta23.GapMatching.OneBandCentralPackageAtD

open Zeta23
open Zeta23.GapMatching.FiniteStateGapPotential
open Zeta23.GapMatching.OneBandActualWordDCore
open Zeta23.GapMatching.OneBandWordEnergyD
open Zeta23.GapMatching.OneBandCentralWordD
open Zeta23.GapMatching.CanonicalOneBandPathD
open Zeta23.GapMatching.PathDataDCoreAdapter
open Zeta23.GapMatching.GapMatchingZetaSeam

variable {Z : ZeroConfig} {P : Params} {T : ℝ}

/-- At one height, uniform overlap control gives both the finite central word
and an endpoint-disjoint matching core. -/
theorem exists_centralWord_core_at
    (hreal : PhiHatReal T (P.atD T))
    (hc : 0 < dScale P T)
    (hL : 0 ≤ P.L T)
    (V : OrderedCentralVerticesD Z P T)
    {eps : ℝ}
    (Hoverlap : UniformOverlapApprox V eps)
    (hlength : totalLength (actualWord V)
      ≤ (Z.N T (2 * T) : ℝ)) :
    ∃ energy : ℝ,
      CentralWordAt Z T ∧
      MatchingCoreAt Z P T energy ∧
      activeEnergy (canonicalPathData V) ≤ 2 * energy := by
  obtain ⟨energy, hcore, hselected⟩ :=
    exists_matchingCore_half (canonicalPathData V)
  refine ⟨energy, ?_, hcore, hselected⟩
  refine
    { gaps := actualWord V
      centralSimple := (V.n + 2 : ℕ)
      W := activeEnergy (canonicalPathData V)
      countError := 2
      lengthError := 0
      valid := valid_actual_word V Hoverlap hL
      count_lower := ?_
      length_upper := ?_
      candidate_le := candidateWeight_actualWord_le_activeEnergy
        hreal hc V }
  · simp [actualWord, word_length]
  · simpa using hlength

end Zeta23.GapMatching.OneBandCentralPackageAtD
