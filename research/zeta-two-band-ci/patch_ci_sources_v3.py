#!/usr/bin/env python3
"""Final local elaboration fix for the ramp Fourier real-part identity."""

from __future__ import annotations

import sys
from pathlib import Path


def main() -> None:
    if len(sys.argv) != 2:
        raise SystemExit("usage: patch_ci_sources_v3.py <zeta23-workspace>")

    path = Path(sys.argv[1]) / "Zeta23" / "GapMatching" / "DWindowRampEstimate.lean"
    text = path.read_text(encoding="utf-8")
    old = """      apply integral_congr_ae
  filter_upwards with u
  have hexponent :
      Complex.I * (r : ℂ) * (u : ℂ)
        = ((r * u : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [hexponent, Complex.exp_mul_I]
  simp [Complex.mul_re]"""
    new = """      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun u => by
        have hexponent :
            Complex.I * (r : ℂ) * (u : ℂ)
              = ((r * u : ℝ) : ℂ) * Complex.I := by
          push_cast
          ring
        rw [hexponent, Complex.exp_mul_I]
        simp [Complex.mul_re])"""
    if old not in text:
        raise RuntimeError(f"expected ramp proof fragment not found in {path}")
    path.write_text(text.replace(old, new, 1), encoding="utf-8")


if __name__ == "__main__":
    main()
