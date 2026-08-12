#!/usr/bin/env python3
"""Second-stage elaboration fixes after patch_ci_sources.py."""

from __future__ import annotations

import sys
from pathlib import Path


def replace_once(path: Path, old: str, new: str) -> None:
    text = path.read_text(encoding="utf-8")
    if old not in text:
        raise RuntimeError(f"expected source fragment not found in {path}")
    path.write_text(text.replace(old, new, 1), encoding="utf-8")


def main() -> None:
    if len(sys.argv) != 2:
        raise SystemExit("usage: patch_ci_sources_v2.py <zeta23-workspace>")

    gap = Path(sys.argv[1]) / "Zeta23" / "GapMatching"

    # Force HasSum scalar multiplication rather than Tendsto dot notation.
    replace_once(
        gap / "DWindowOverlap.lean",
        """  have hraw := hW.hasSum_vHatR_mul T tau tau'
  rw [show fullGridOverlap v L tau tau' =
      (av v L * L ^ 2)⁻¹ * (L * VPhiR v (tau - tau')) by
    unfold fullGridOverlap
    field_simp [ha.ne', hW.L_pos.ne']]
  simpa only [Finset.mul_sum] using
    hraw.const_mul (av v L * L ^ 2)⁻¹""",
        """  have hraw := hW.hasSum_vHatR_mul T tau tau'
  have hscaled :
      HasSum
        (fun k : ℤ =>
          (av v L * L ^ 2)⁻¹ •
            (vHatR v (tau - (T + k * (2 * Real.pi / L)))
              * vHatR v (tau' - (T + k * (2 * Real.pi / L)))))
        ((av v L * L ^ 2)⁻¹ •
          (L * VPhiR v (tau - tau'))) :=
    HasSum.const_smul (av v L * L ^ 2)⁻¹ hraw
  rw [show fullGridOverlap v L tau tau' =
      (av v L * L ^ 2)⁻¹ * (L * VPhiR v (tau - tau')) by
    unfold fullGridOverlap
    field_simp [ha.ne', hW.L_pos.ne']]
  simpa only [smul_eq_mul] using hscaled""",
    )

    # Make the restricted measure explicit and use integral_re propositionally.
    replace_once(
        gap / "DWindowRampEstimate.lean",
        """          have hIabs :
              MeasureTheory.IntegrableOn
                (fun u => |h u * p u - h u|)
                (Set.Icc (-(L / 2)) (L / 2)) := by
            simpa only [Pi.sub_apply] using (hIhp.sub hIh).abs
          exact MeasureTheory.setIntegral_mono_on hIabs
            hImajorant.integrableOn measurableSet_Icc hpointwise""",
        """          have hIabs :
              MeasureTheory.IntegrableOn
                (fun u => |h u * p u - h u|)
                (Set.Icc (-(L / 2)) (L / 2)) := by
            change MeasureTheory.Integrable
              (fun u => |h u * p u - h u|)
              (MeasureTheory.volume.restrict
                (Set.Icc (-(L / 2)) (L / 2)))
            simpa only [Pi.sub_apply] using (hIhp.sub hIh).abs
          exact MeasureTheory.setIntegral_mono_on hIabs
            hImajorant.integrableOn measurableSet_Icc hpointwise""",
    )
    replace_once(
        gap / "DWindowRampEstimate.lean",
        """  unfold AdmWindow.VPhiR AdmWindow.VPhi
  rw [paperFT_def, ← integral_re hint]
  apply integral_congr_ae""",
        """  unfold AdmWindow.VPhiR AdmWindow.VPhi
  rw [paperFT_def]
  calc
    (∫ u, (((v u) ^ 2 : ℝ) : ℂ)
        * Complex.exp (Complex.I * (r : ℂ) * (u : ℂ))).re
        = (∫ u, ((((v u) ^ 2 : ℝ) : ℂ)
          * Complex.exp (Complex.I * (r : ℂ) * (u : ℂ))).re) := by
            simpa using (integral_re hint).symm
    _ = ∫ u, v u ^ 2 * Real.cos (r * u) := by
      apply integral_congr_ae""",
    )

    geom = gap / "CentralGapGeometryD.lean"
    replace_once(
        geom,
        """    hpwlt.imp fun _ _ h => h.le""",
        """    hpwlt.imp (fun a b (h : a < b) => le_of_lt h)""",
    )
    replace_once(
        geom,
        """  have hmem := V.central_mem 0
  exact le_of_lt (hmem.1.2.1.trans' (lt_add_of_pos_right _
    (Real.sqrt_pos.2 (by
      have h := hmem.1.2.1
      have hs := Real.sqrt_nonneg T
      linarith))))""",
        """  have hmem := V.central_mem 0
  have hs := Real.sqrt_nonneg T
  linarith [hmem.1.1.2.1]""",
    )
    replace_once(
        geom,
        """  have hmem := V.central_mem 0
  have hs := Real.sqrt_nonneg T
  linarith [hmem.1.2.1]""",
        """  have hmem := V.central_mem 0
  have hs := Real.sqrt_nonneg T
  linarith [hmem.1.1.2.1]""",
    )
    replace_once(
        geom,
        """  have hmem := V.central_mem i
  have hs := Real.sqrt_nonneg T
  linarith [hmem.1.2.2]""",
        """  have hmem := V.central_mem i
  have hs := Real.sqrt_nonneg T
  linarith [hmem.1.1.2.2]""",
    )
    replace_once(
        geom,
        """  apply normalizedGaps_sum_le
    (endpoint := 2 * T) (total := (Z.N T (2 * T) : ℝ))
    (error := 0)""",
        """  unfold normalizedGapList
  apply normalizedGaps_sum_le
    (endpoint := 2 * T) (total := (Z.N T (2 * T) : ℝ))
    (error := 0)""",
    )
    replace_once(
        geom,
        """  have hL : 0 ≤ P.L T := by
    unfold Params.L
    positivity
  exact normalizedGapList_sum_le_count V hT hL hspan""",
        """  have hLpos : 0 < P.L T := by
    unfold Params.L
    exact mul_pos hP.lam_pos hlT
  exact normalizedGapList_sum_le_count V hT hLpos.le hspan""",
    )

    guard = gap / "CentralGuardCountD.lean"
    replace_once(
        guard,
        """  unfold innerGuard
  linarith""",
        """  unfold innerGuard
  dsimp [D0] at hlo hhi ⊢
  linarith""",
    )


if __name__ == "__main__":
    main()
