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

    # Force HasSum scalar multiplication rather than ambiguous Tendsto dot notation.
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

    # Make the restricted measure explicit.  The Fourier real-part proof from
    # stage one is already correctly indented and is left unchanged here.
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

    # The conservative one-band inequalities are elementary, but nonlinear
    # automation did not infer all sign facts.  State each monotonicity step.
    overlap = gap / "OneBandPotentialOverlap.lean"
    replace_once(
        overlap,
        """  rw [← floor_arithmetic.2.1]
  nlinarith [sq_nonneg (|x| - sharpAbsFloor), sq_abs x]""",
        """  rw [← floor_arithmetic.2.1]
  have h0 : 0 ≤ sharpAbsFloor := by
    norm_num [sharpAbsFloor]
  have hs := pow_le_pow_left₀ h0 h 2
  simpa [sq_abs] using hs""",
    )
    replace_once(
        overlap,
        """  rcases hprofile with ⟨hlength0, hbadRange, hgoodShort, hbadLong⟩
  cases previous <;> cases current
  · have hphysical :
        p ≤ B * length + actualShort ^ 2 := by
      rcases hgoodShort rfl with hlength | hoverlap
      · have hB : 0 ≤ B := parameter_ranges.2.2.1
        have hcharge := mul_le_mul_of_nonneg_left hlength hB
        have hBthreshold : B * lengthThreshold = p := by
          norm_num [B, lengthThreshold, p]
        rw [hBthreshold] at hcharge
        nlinarith [sq_nonneg actualShort]
      · have hsquare := hshortFloor_of_overlap hoverlap
        have hp := floor_arithmetic.2.2.1
        nlinarith
    simp [physicalFloor, lengthFloor, shortFloor, longFloor,
      phi, stepCost, stepWeight, ofOverlaps]
    nlinarith
  · rcases hbadRange rfl with ⟨hlow, _⟩
    simp [physicalFloor, lengthFloor, shortFloor, longFloor,
      phi, stepCost, stepWeight, ofOverlaps]
    nlinarith
  · have hphysical :
        p ≤ B * length + actualShort ^ 2 := by
      rcases hgoodShort rfl with hlength | hoverlap
      · have hB : 0 ≤ B := parameter_ranges.2.2.1
        have hcharge := mul_le_mul_of_nonneg_left hlength hB
        have hBthreshold : B * lengthThreshold = p := by
          norm_num [B, lengthThreshold, p]
        rw [hBthreshold] at hcharge
        nlinarith [sq_nonneg actualShort]
      · have hsquare := hshortFloor_of_overlap hoverlap
        have hp := floor_arithmetic.2.2.1
        nlinarith
    simp [physicalFloor, lengthFloor, shortFloor, longFloor,
      phi, stepCost, stepWeight, ofOverlaps]
    nlinarith
  · rcases hbadRange rfl with ⟨hlow, _⟩
    have hlongMag := hbadLong rfl rfl
    have hlongSquare := hlongFloor_of_overlap hlongMag
    have hj := floor_arithmetic.2.2.2
    simp [physicalFloor, lengthFloor, shortFloor, longFloor,
      phi, stepCost, stepWeight, ofOverlaps]
    nlinarith""",
        """  rcases hprofile with ⟨hlength0, hbadRange, hgoodShort, hbadLong⟩
  have hB0 : 0 ≤ B := parameter_ranges.2.2.1
  have hcharge0 : 0 ≤ B * length := mul_nonneg hB0 hlength0
  cases previous <;> cases current
  · have hphysical :
        p ≤ B * length + actualShort ^ 2 := by
      rcases hgoodShort rfl with hlength | hoverlap
      · have hcharge := mul_le_mul_of_nonneg_left hlength hB0
        have hBthreshold : B * lengthThreshold = p := by
          norm_num [B, lengthThreshold, p]
        calc
          p = B * lengthThreshold := hBthreshold.symm
          _ ≤ B * length := hcharge
          _ ≤ B * length + actualShort ^ 2 := by
            nlinarith [sq_nonneg actualShort]
      · have hsquare := hshortFloor_of_overlap hoverlap
        have hp := floor_arithmetic.2.2.1
        calc
          p ≤ finiteSqFloor := hp
          _ ≤ actualShort ^ 2 := hsquare
          _ ≤ B * length + actualShort ^ 2 := by linarith
    simpa [physicalFloor, lengthFloor, shortFloor, longFloor,
      stepCost, stepWeight, ofOverlaps] using hphysical
  · rcases hbadRange rfl with ⟨hlow, _⟩
    have hcharge := mul_le_mul_of_nonneg_left hlow hB0
    simpa [physicalFloor, lengthFloor, shortFloor, longFloor,
      stepCost, stepWeight, ofOverlaps] using hcharge
  · have hphysical :
        p ≤ B * length + actualShort ^ 2 := by
      rcases hgoodShort rfl with hlength | hoverlap
      · have hcharge := mul_le_mul_of_nonneg_left hlength hB0
        have hBthreshold : B * lengthThreshold = p := by
          norm_num [B, lengthThreshold, p]
        calc
          p = B * lengthThreshold := hBthreshold.symm
          _ ≤ B * length := hcharge
          _ ≤ B * length + actualShort ^ 2 := by
            nlinarith [sq_nonneg actualShort]
      · have hsquare := hshortFloor_of_overlap hoverlap
        have hp := floor_arithmetic.2.2.1
        calc
          p ≤ finiteSqFloor := hp
          _ ≤ actualShort ^ 2 := hsquare
          _ ≤ B * length + actualShort ^ 2 := by linarith
    simpa [physicalFloor, lengthFloor, shortFloor, longFloor,
      stepCost, stepWeight, ofOverlaps] using hphysical
  · rcases hbadRange rfl with ⟨hlow, _⟩
    have hcharge := mul_le_mul_of_nonneg_left hlow hB0
    have hlongMag := hbadLong rfl rfl
    have hlongSquare := hlongFloor_of_overlap hlongMag
    have hj := floor_arithmetic.2.2.2
    have hphysical :
        B * badLeft + j ≤ B * length + actualLong ^ 2 :=
      add_le_add hcharge (hj.trans hlongSquare)
    simpa [physicalFloor, lengthFloor, shortFloor, longFloor,
      stepCost, stepWeight, ofOverlaps] using hphysical""",
    )

    # Ordered geometry: unfold the ordinate abbreviations and telescope directly.
    geom = gap / "CentralGapGeometryD.lean"
    replace_once(
        geom,
        """    hpwlt.imp fun _ _ h => h.le""",
        """    hpwlt.imp fun h => h.le""",
    )
    replace_once(
        geom,
        """theorem firstOrdinate_ge
    (V : OrderedCentralVerticesD Z P T) :
    T ≤ firstOrdinate V := by
  have hmem := V.central_mem 0
  exact le_of_lt (hmem.1.2.1.trans' (lt_add_of_pos_right _
    (Real.sqrt_pos.2 (by
      have h := hmem.1.2.1
      have hs := Real.sqrt_nonneg T
      linarith))))""",
        """theorem firstOrdinate_ge
    (V : OrderedCentralVerticesD Z P T) :
    T ≤ firstOrdinate V := by
  have hmem := V.central_mem 0
  have hlow := hmem.1.1.2.1
  dsimp [D0] at hlow
  unfold firstOrdinate ordinate
  nlinarith [hlow, Real.sqrt_nonneg T]""",
    )
    replace_once(
        geom,
        """theorem firstOrdinate_ge_of_nonneg
    (V : OrderedCentralVerticesD Z P T) (hT : 0 ≤ T) :
    T ≤ firstOrdinate V := by
  have hmem := V.central_mem 0
  have hs := Real.sqrt_nonneg T
  linarith [hmem.1.2.1]""",
        """theorem firstOrdinate_ge_of_nonneg
    (V : OrderedCentralVerticesD Z P T) (_hT : 0 ≤ T) :
    T ≤ firstOrdinate V :=
  firstOrdinate_ge V""",
    )
    replace_once(
        geom,
        """theorem ordinate_le_two_mul
    (V : OrderedCentralVerticesD Z P T)
    (i : Fin (V.n + 2)) :
    ordinate V i ≤ 2 * T := by
  have hmem := V.central_mem i
  have hs := Real.sqrt_nonneg T
  linarith [hmem.1.2.2]""",
        """theorem ordinate_le_two_mul
    (V : OrderedCentralVerticesD Z P T)
    (i : Fin (V.n + 2)) :
    ordinate V i ≤ 2 * T := by
  have hmem := V.central_mem i
  have hhigh := hmem.1.1.2.2
  dsimp [D0] at hhigh
  unfold ordinate
  nlinarith [hhigh, Real.sqrt_nonneg T]""",
    )
    replace_once(
        geom,
        """theorem normalizedGapList_sum_le_count
    (V : OrderedCentralVerticesD Z P T)
    (hT : 0 ≤ T)
    (hL : 0 ≤ P.L T)
    (hspan : P.L T * T / (2 * Real.pi)
      ≤ (Z.N T (2 * T) : ℝ)) :
    (normalizedGapList V).sum ≤ (Z.N T (2 * T) : ℝ) := by
  apply normalizedGaps_sum_le
    (endpoint := 2 * T) (total := (Z.N T (2 * T) : ℝ))
    (error := 0)
  · exact lastFrom_le_two_mul V
  · unfold gapScale
    positivity
  · have hfirst := firstOrdinate_ge_of_nonneg V hT
    have hscale : 0 ≤ gapScale P T := by
      unfold gapScale
      positivity
    have hdiff : 2 * T - firstOrdinate V ≤ T := by
      linarith
    have hmul := mul_le_mul_of_nonneg_left hdiff hscale
    unfold gapScale at hmul ⊢
    have heq :
        P.L T / (2 * Real.pi) * T
          = P.L T * T / (2 * Real.pi) := by ring
    rw [heq] at hmul
    nlinarith""",
        """theorem normalizedGapList_sum_le_count
    (V : OrderedCentralVerticesD Z P T)
    (hT : 0 ≤ T)
    (hL : 0 ≤ P.L T)
    (hspan : P.L T * T / (2 * Real.pi)
      ≤ (Z.N T (2 * T) : ℝ)) :
    (normalizedGapList V).sum ≤ (Z.N T (2 * T) : ℝ) := by
  unfold normalizedGapList
  rw [normalizedGaps_sum]
  have hlast := lastFrom_le_two_mul V
  have hfirst := firstOrdinate_ge_of_nonneg V hT
  have hscale : 0 ≤ gapScale P T := by
    unfold gapScale
    exact div_nonneg hL (by positivity)
  calc
    gapScale P T *
        (lastFrom (firstOrdinate V) (remainingOrdinates V)
          - firstOrdinate V)
      ≤ gapScale P T * (2 * T - firstOrdinate V) := by
        exact mul_le_mul_of_nonneg_left (by linarith) hscale
    _ ≤ gapScale P T * T := by
        exact mul_le_mul_of_nonneg_left (by linarith) hscale
    _ = P.L T * T / (2 * Real.pi) := by
        unfold gapScale
        ring
    _ ≤ (Z.N T (2 * T) : ℝ) := hspan""",
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
