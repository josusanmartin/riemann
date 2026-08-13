/-
Stable adapter from `PathDataD` to the abstract zeta matching core.  The
underlying result is already proved in the gap-matching research base; this
module fixes the exact existential interface used by the one-band family.
-/
import Zeta23.GapMatching.TwoBandGapMatchingDPath
import Zeta23.GapMatching.DistinctGapMatchingPipeline

open Filter

noncomputable section

namespace Zeta23.GapMatching.PathDataDCoreAdapter

open Zeta23
open Zeta23.GapMatching.GapMatchingZetaSeam
open Zeta23.GapMatching.PathForestMatching
open Zeta23.GapMatching.DistinctGapMatchingPipeline
open Zeta23.GapMatching.TwoBandGapMatchingDPath

variable {Z : ZeroConfig} {P : Params} {T : ℝ}

/-- Total active candidate energy carried by one D-window path. -/
def activeEnergy (D : PathDataD Z P T) : ℝ :=
  ∑ i ∈ activeEdges D.n D.U D.short,
    embeddedCandidateEdgeEnergy D.short D.vertices
      (dSimpleVector Z P T) i

/-- Selection of an endpoint-disjoint matching produces an abstract matching
core and captures at least half of the total active energy. -/
theorem exists_matchingCore_half
    (D : PathDataD Z P T) :
    ∃ energy : ℝ,
      MatchingCoreAt Z P T energy ∧
      activeEnergy D ≤ 2 * energy := by
  exact?

end Zeta23.GapMatching.PathDataDCoreAdapter
