import Zeta23.GapMatching.DWindowFiniteGridApprox
import Zeta23.GapMatching.DWindowOverlap
import Zeta23.GapMatching.DWindowSharpScaling
import Zeta23.GapMatching.CentralGapGeometryD
import Zeta23.GapMatching.OneBandSharpProfile

open Real

noncomputable section

namespace Zeta23.GapMatching.DWindowFullOverlapIdentity

open Zeta23
open Zeta23.AdmWindow
open Zeta23.GapMatching.CentralPathConstructionD
open Zeta23.GapMatching.CentralGapGeometryD
open Zeta23.GapMatching.DWindowFiniteGridApprox
open Zeta23.GapMatching.DWindowOverlap
open Zeta23.GapMatching.DWindowSharpScaling
open Zeta23.GapMatching.OneBandPotentialSafeNumerics
open Zeta23.GapMatching.OneBandSharpProfile

theorem normalizedFullOverlap_eq_fullGridOverlap
    {v : ℝ → ℝ} {L tau tau' : ℝ}
    (ha : 0 < av v L) (hL : 0 < L) :
    normalizedFullOverlap v L tau tau'
      = fullGridOverlap v L tau tau' := by
  unfold normalizedFullOverlap fullGridOverlap
  field_simp [ha.ne', hL.ne']
  ring

theorem finiteNormalizedOverlap_close_fullGrid
    {v : ℝ → ℝ} {L w c T tau tau' D : ℝ} {d : ℕ}
    (hW : AdmWindow v L w c)
    (ha : 0 < av v L)
    (hD : 0 < D)
    (hleftTau : T + D ≤ tau)
    (hleftTau' : T + D ≤ tau')
    (hrightTau : tau + D ≤ T + d * (2 * Real.pi / L))
    (hrightTau' : tau' + D ≤ T + d * (2 * Real.pi / L)) :
    |finiteNormalizedOverlap v L T d tau tau'
        - fullGridOverlap v L tau tau'|
      ≤ 2 * ((av v L * L ^ 2)⁻¹
        * rawTailMajorant c w D (2 * Real.pi / L)) := by
  rw [← normalizedFullOverlap_eq_fullGridOverlap ha hW.L_pos]
  exact finiteNormalizedOverlap_close hW ha hD
    hleftTau hleftTau' hrightTau hrightTau'

variable {Z : ZeroConfig} {P : Params} {T : ℝ}

theorem sharpOverlap_vertices_eq_profile
    (hL : 0 < P.L T)
    (hlam : P.lam = lam)
    (V : OrderedCentralVerticesD Z P T)
    (i j : Fin (V.n + 2)) :
    Zeta23.GapMatching.DWindowProfileAlgebra.sharpOverlap
        P.lam (P.L T) (ordinate V i - ordinate V j)
      = profile (gapScale P T * (ordinate V j - ordinate V i)) := by
  unfold profile
  rw [sharpOverlap_scale hL, hlam]
  have harg :
      (ordinate V i - ordinate V j) * P.L T
        = -(2 * Real.pi *
            (gapScale P T * (ordinate V j - ordinate V i))) := by
    unfold gapScale
    field_simp [Real.pi_ne_zero]
    ring
  rw [harg, sharpOverlap_neg]

end Zeta23.GapMatching.DWindowFullOverlapIdentity
