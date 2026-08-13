/-
One-height assembly of the actual one-band word and the selected D-window
matching core.  Guard and total-length inequalities are explicit inputs so the
remaining asymptotic module can discharge them independently.
-/
import Zeta23.GapMatching.OneBandWordEnergyD
import Zeta23.GapMatching.OneBandPotentialAnalyticBridge

open Filter

noncomputable section

namespace Zeta23.GapMatching.OneBandPackageAtD

open Zeta23
open Zeta23.GapMatching.FiniteStateGapPotential
open Zeta23.GapMatching.OneBandPotentialSafeNumerics
open Zeta23.GapMatching.OneBandActualWordDCore
open Zeta23.GapMatching.OneBandWordEnergyD
open Zeta23.GapMatching.CanonicalOneBandPathD
open Zeta23.GapMatching.PathDataDCoreAdapter
open Zeta23.GapMatching.OneBandPotentialAnalyticBridge

variable {Z : ZeroConfig} {P : Params} {T : ℝ}

/-- At one height, a canonical path with uniform overlap control produces both
an error-explicit word package and an endpoint-disjoint matching core. -/
theorem exists_word_core_at
    (hreal : PhiHatReal T (P.atD T))
    (hc : 0 < dScale P T)
    (hL : 0 ≤ P.L T)
    (V : OrderedCentralVerticesD Z P T)
    {eps guardError : ℝ}
    (Hoverlap : UniformOverlapApprox V eps)
    (hguard :
      (Z.N0s T (2 * T) : ℝ) - guardError ≤ (V.n + 2 : ℕ))
    (hlength : totalLength (actualWord V)
      ≤ (Z.N T (2 * T) : ℝ)) :
    ∃ energy : ℝ,
      OneBandWordAt Z T ∧
      MatchingCoreAt Z P T energy ∧
      activeEnergy (canonicalPathData V) ≤ 2 * energy := by
  obtain ⟨energy, hcore, hselected⟩ :=
    exists_matchingCore_half (canonicalPathData V)
  refine ⟨energy, ?_, hcore, hselected⟩
  refine
    { gaps := actualWord V
      centralSimple := (V.n + 2 : ℕ)
      W := activeEnergy (canonicalPathData V)
      guardError := guardError
      countError := 2
      lengthError := 0
      valid := valid_actual_word V Hoverlap hL
      guard_lower := hguard
      count_lower := ?_
      length_upper := ?_
      candidate_le := candidateWeight_actualWord_le_activeEnergy
        hreal hc V }
  · simp [actualWord, word_length]
  · simpa using hlength

end Zeta23.GapMatching.OneBandPackageAtD
