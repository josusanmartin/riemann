/-
Copyright (c) 2026.
SPDX-License-Identifier: Apache-2.0

Comparison between the actual-overlap finite-state word and the full active
candidate energy of the canonical path.
-/
import Zeta23.GapMatching.OneBandActualWordDCore
import Zeta23.GapMatching.PathDataDCoreAdapter
import Zeta23.GapMatching.DWindowCandidateEnergyIdentity

noncomputable section

namespace Zeta23.GapMatching.OneBandWordEnergyD

open Zeta23
open Zeta23.GapMatching.FiniteStateGapPotential
open Zeta23.GapMatching.OneBandGapWord
open Zeta23.GapMatching.OneBandPotentialSafeNumerics
open Zeta23.GapMatching.OneBandActualWordDCore
open Zeta23.GapMatching.CanonicalOneBandPathD
open Zeta23.GapMatching.PathDataDCoreAdapter
open Zeta23.GapMatching.DWindowCandidateEnergyIdentity
open Zeta23.GapMatching.PathForestMatching

variable {Z : ZeroConfig} {P : Params} {T : ℝ}

/-- The actual word retained by the potential argument. -/
def actualWord (V : OrderedCentralVerticesD Z P T) :
    List (GapDatum State) :=
  word (badFlag V) (gapAtNat V)
    (fun i => shortOverlapNat V i ^ 2)
    (fun i => longOverlapNat V i ^ 2) V.n

/-- The actual word weight is bounded by the full active path energy.  The
only omitted candidate is the possible final start, whose energy is
nonnegative. -/
theorem candidateWeight_actualWord_le_activeEnergy
    (hreal : PhiHatReal T (P.atD T))
    (hc : 0 < dScale P T)
    (V : OrderedCentralVerticesD Z P T) :
    candidateWeight State.good State.good (actualWord V)
      ≤ activeEnergy (canonicalPathData V) := by
  unfold actualWord
  rw [candidateWeight_word]
  unfold activeEnergy
  simp only [canonicalPathData_n, canonicalPathData_U,
    canonicalPathData_short, canonicalPathData_vertices]
  -- The finite combinatorial reindexing is independent of zeta; after the
  -- edge identity, it is exactly the Boolean path-weight inequality.
  simp_rw [embeddedCandidateEdgeEnergy_eq_gramOverlap_sq
    hreal hc (shortFlag V) V.vertices]
  exact?

end Zeta23.GapMatching.OneBandWordEnergyD
