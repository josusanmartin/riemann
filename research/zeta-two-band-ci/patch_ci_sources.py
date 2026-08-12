#!/usr/bin/env python3
"""Apply small elaboration fixes to copied research modules before CI build."""

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
        raise SystemExit("usage: patch_ci_sources.py <zeta23-workspace>")

    workspace = Path(sys.argv[1])
    gap_dir = workspace / "Zeta23" / "GapMatching"

    replace_once(
        gap_dir / "GuardedWindowCount.lean",
        "          _ = |left| + j := by rw [abs_of_nonneg (Nat.cast_nonneg j)]",
        """          _ = |left| + j := by
            rw [show |(j : ℝ)| = (j : ℝ) from
              abs_of_nonneg (Nat.cast_nonneg j)]""",
    )

    seam = gap_dir / "TwoBandGapMatchingD.lean"
    replace_once(
        seam,
        """  have hden : Acoef < 1 := parameter_ranges.2.1

  exact fixed_point_certificate""",
        """  have hden : Acoef < 1 := parameter_ranges.2.1
  have hden' : Acoef * 1 < 1 := by simpa using hden
  have hAne : Acoef ≠ 0 := ne_of_gt parameter_ranges.1
  have hgain : ∀ᶠ T in atTop,
      Acoef * (1 * (Z.N0s T (2 * T) : ℝ)
        - 2 * (Bcoef / (2 * Acoef)) * N T)
        - error T ≤ 2 * energy T := by
    filter_upwards [hgap.gain] with T hT
    have hid :
        Acoef * (1 * (Z.N0s T (2 * T) : ℝ)
          - 2 * (Bcoef / (2 * Acoef)) * N T)
          = Acoef * (Z.N0s T (2 * T) : ℝ) - Bcoef * N T := by
      field_simp [hAne]
    rw [hid]
    simpa only [hNdef] using hT

  exact fixed_point_certificate""",
    )
    replace_once(
        seam,
        "    hN0 hcert hgap.gain hgap.error_small hden",
        "    hN0 hcert hgain hgap.error_small hden'",
    )

    overlap = gap_dir / "DWindowOverlap.lean"
    replace_once(
        overlap,
        """  have hraw := hW.hasSum_vHatR_mul T tau tau'
  have hscaled := hraw.const_mul (av v L * L ^ 2)⁻¹
  convert hscaled using 1
  · funext k
    ring
  · unfold fullGridOverlap
    field_simp [ha.ne', hW.L_pos.ne']
    ring""",
        """  have hraw := hW.hasSum_vHatR_mul T tau tau'
  rw [show fullGridOverlap v L tau tau' =
      (av v L * L ^ 2)⁻¹ * (L * VPhiR v (tau - tau')) by
    unfold fullGridOverlap
    field_simp [ha.ne', hW.L_pos.ne']]
  simpa only [Finset.mul_sum] using
    hraw.const_mul (av v L * L ^ 2)⁻¹""",
    )
    replace_once(
        overlap,
        """  have hcross : -2 * eps ≤ 2 * y * (x - y) := by
    exact (neg_le_of_abs_le habsMul)""",
        """  have hcross : -2 * eps ≤ 2 * y * (x - y) := by
    have h := neg_le_of_abs_le habsMul
    linarith""",
    )

    ramp = gap_dir / "DWindowRampEstimate.lean"
    replace_once(
        ramp,
        "import Zeta23.ThmD.Window\n",
        "import Zeta23.ThmD.Window\nimport Zeta23.ThmD.WindowCore\n",
    )
    replace_once(
        ramp,
        """      have hone : 1 ≤ majorant u := by
        rw [hmajorant]
        rcases le_or_gt u 0 with hneg | hpos""",
        """      have hone : 1 ≤ majorant u := by
        rw [hmajorant]
        dsimp only
        rcases le_or_gt u 0 with hneg | hpos""",
    )
    replace_once(
        ramp,
        """          rw [Set.indicator_of_mem hu1, Pi.one_apply]
          linarith""",
        """          change 1 ≤
            (Set.Icc (-(L / 2)) (-(L / 2) + w)).indicator
                (1 : ℝ → ℝ) u
              + (Set.Icc (L / 2 - w) (L / 2)).indicator
                (1 : ℝ → ℝ) u
          rw [Set.indicator_of_mem hu1, Pi.one_apply]
          linarith""",
    )
    replace_once(
        ramp,
        """          rw [Set.indicator_of_mem hu1, Pi.one_apply]
          linarith""",
        """          change 1 ≤
            (Set.Icc (-(L / 2)) (-(L / 2) + w)).indicator
                (1 : ℝ → ℝ) u
              + (Set.Icc (L / 2 - w) (L / 2)).indicator
                (1 : ℝ → ℝ) u
          rw [Set.indicator_of_mem hu1, Pi.one_apply]
          linarith""",
    )
    replace_once(
        ramp,
        """          apply MeasureTheory.setIntegral_mono_on
            (((hhc.mul hpc).sub hhc).abs.continuousOn
              .integrableOn_compact isCompact_Icc)
            hImajorant.integrableOn measurableSet_Icc hpointwise""",
        """          have hIabs :
              MeasureTheory.IntegrableOn
                (fun u => |h u * p u - h u|)
                (Set.Icc (-(L / 2)) (L / 2)) := by
            simpa only [Pi.sub_apply] using (hIhp.sub hIh).abs
          exact MeasureTheory.setIntegral_mono_on hIabs
            hImajorant.integrableOn measurableSet_Icc hpointwise""",
    )
    replace_once(
        ramp,
        """  have hint : Integrable
      (fun u : ℝ => (((v u) ^ 2 : ℝ) : ℂ)
        * Complex.exp (Complex.I * (r : ℂ) * (u : ℂ))) :=
    (hW.vSqC_continuous.mul (by fun_prop))
      .integrable_of_hasCompactSupport
        hW.vSqC_hasCompactSupport.mul_right
  unfold AdmWindow.VPhiR AdmWindow.VPhi
  rw [paperFT_def, integral_re_C hint]""",
        """  have hexp : Continuous
      (fun u : ℝ => Complex.exp
        (Complex.I * (r : ℂ) * (u : ℂ))) := by
    fun_prop
  have hcont : Continuous
      (fun u : ℝ => (((v u) ^ 2 : ℝ) : ℂ)
        * Complex.exp (Complex.I * (r : ℂ) * (u : ℂ))) :=
    hW.vSqC_continuous.mul hexp
  have hint : Integrable
      (fun u : ℝ => (((v u) ^ 2 : ℝ) : ℂ)
        * Complex.exp (Complex.I * (r : ℂ) * (u : ℂ))) :=
    hcont.integrable_of_hasCompactSupport
      hW.vSqC_hasCompactSupport.mul_right
  unfold AdmWindow.VPhiR AdmWindow.VPhi
  rw [paperFT_def, ← integral_re hint]""",
    )

    one_band = gap_dir / "OneBandPotentialSafeNumerics.lean"
    replace_once(
        one_band,
        """def transitionFloor (previous current : State) : ℝ :=
  B * lengthFloor current
    + shortFloor current
    + longFloor previous current
    + phi previous - phi current""",
        """def physicalFloor (previous current : State) : ℝ :=
  B * lengthFloor current
    + shortFloor current
    + longFloor previous current

def transitionFloor (previous current : State) : ℝ :=
  physicalFloor previous current + phi previous - phi current""",
    )
    replace_once(
        one_band,
        """    norm_num [A, B, p, j, badLeft, transitionFloor,
      lengthFloor, shortFloor, longFloor, phi]""",
        """    norm_num [A, B, p, j, badLeft, transitionFloor,
      physicalFloor, lengthFloor, shortFloor, longFloor, phi]""",
    )
    replace_once(
        one_band,
        """theorem localCertificate_of_dominates
    (previous : State) (g : GapDatum State)
    (h : transitionFloor previous g.state
      ≤ stepCost B State.good previous g) :
    LocalCertificate A B State.good phi previous g :=
  (transition_certificate previous g.state).trans h""",
        """theorem localCertificate_of_dominates
    (previous : State) (g : GapDatum State)
    (h : physicalFloor previous g.state
      ≤ stepCost B State.good previous g) :
    LocalCertificate A B State.good phi previous g := by
  unfold LocalCertificate
  calc
    A ≤ transitionFloor previous g.state :=
      transition_certificate previous g.state
    _ = physicalFloor previous g.state
          + phi previous - phi g.state := rfl
    _ ≤ stepCost B State.good previous g
          + phi previous - phi g.state := by
      nlinarith""",
    )

    one_overlap = gap_dir / "OneBandPotentialOverlap.lean"
    replace_once(
        one_overlap,
        """    transitionFloor previous current ≤
      stepCost B State.good previous""",
        """    physicalFloor previous current ≤
      stepCost B State.good previous""",
    )
    for _ in range(4):
        replace_once(
            one_overlap,
            """simp [transitionFloor, lengthFloor, shortFloor, longFloor,""",
            """simp [physicalFloor, lengthFloor, shortFloor, longFloor,""",
        )

    central = gap_dir / "CentralPathConstructionD.lean"
    replace_once(
        central,
        """  · have hsqrt := Real.sqrt_nonneg T
    linarith
  · have hsqrt := Real.sqrt_nonneg T
    linarith""",
        """  · dsimp [D0] at hlow ⊢
    nlinarith [Real.sqrt_nonneg T]
  · dsimp [D0] at hhigh ⊢
    nlinarith [Real.sqrt_nonneg T]""",
    )
    replace_once(
        central,
        """    change (blockData Z T (P.atD T) (dConj P T)).σ zi = zi
    rw [mkData_σ_eq_iff]
    exact z.2.1.2""",
        """    apply Subtype.ext
    change reflect (zi : ℂ) = (zi : ℂ)
    exact (reflect_eq_self_iff (zi : ℂ)).2 z.2.1.2""",
    )
    replace_once(
        central,
        """    have hz : z ∈ (Finset.univ : Finset (centralSimpleSet Z T)) := by simp
    rw [← Finset.range_orderEmbOfFin
      (Finset.univ : Finset (centralSimpleSet Z T))
      (by simpa [k] using hkn)] at hz
    rcases hz with ⟨i, hi⟩""",
        """    have hz : z ∈ Set.range ordered := by
      rw [Finset.range_orderEmbOfFin
        (Finset.univ : Finset (centralSimpleSet Z T))
        (by simpa [k] using hkn)]
      simp
    rcases hz with ⟨i, hi⟩""",
    )
    replace_once(
        central,
        """    change ((centralEmbedding (ordered i)).1.1 : ℂ) = rho
    simpa [z] using congrArg Subtype.val hi""",
        """    change ((ordered i).1 : ℂ) = rho
    simpa [z] using congrArg Subtype.val hi""",
    )


if __name__ == "__main__":
    main()
