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
      ring
    rw [hid]
    simpa only [hNdef] using hT

  exact fixed_point_certificate""",
    )
    replace_once(
        seam,
        "    hN0 hcert hgap.gain hgap.error_small hden",
        "    hN0 hcert hgain hgap.error_small hden",
    )


if __name__ == "__main__":
    main()
