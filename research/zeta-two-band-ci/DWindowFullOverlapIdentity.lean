import Zeta23.GapMatching.DWindowFiniteGridApprox
import Zeta23.GapMatching.DWindowOverlap

open Real

noncomputable section

namespace Zeta23.GapMatching.DWindowFullOverlapIdentity

open Zeta23
open Zeta23.AdmWindow
open Zeta23.GapMatching.DWindowFiniteGridApprox
open Zeta23.GapMatching.DWindowOverlap

theorem normalizedFullOverlap_eq_fullGridOverlap
    {v : ℝ → ℝ} {L tau tau' : ℝ}
    (ha : 0 < av v L) (hL : 0 < L) :
    normalizedFullOverlap v L tau tau'
      = fullGridOverlap v L tau tau' := by
  unfold normalizedFullOverlap fullGridOverlap
  field_simp [ha.ne', hL.ne']
  ring

end Zeta23.GapMatching.DWindowFullOverlapIdentity
