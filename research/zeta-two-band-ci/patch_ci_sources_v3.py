#!/usr/bin/env python3
"""Final local elaboration fix for the ramp Fourier real-part identity."""

from __future__ import annotations

import shutil
import sys
from pathlib import Path


def main() -> None:
    if len(sys.argv) != 2:
        raise SystemExit("usage: patch_ci_sources_v3.py <zeta23-workspace>")

    workspace = Path(sys.argv[1])
    gap = workspace / "Zeta23" / "GapMatching"
    path = gap / "DWindowRampEstimate.lean"
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
    new = """      refine integral_congr_ae ?_
      filter_upwards with u
      change
        ((↑(v u ^ 2) *
            Complex.exp (Complex.I * ↑r * ↑u)).re)
          = v u ^ 2 * Real.cos (r * u)
      have hexponent :
          Complex.I * (r : ℂ) * (u : ℂ)
            = ((r * u : ℝ) : ℂ) * Complex.I := by
        push_cast
        ring
      rw [hexponent, Complex.exp_mul_I]
      simp only [Complex.mul_re, Complex.add_re, Complex.add_im,
        Complex.ofReal_re, Complex.ofReal_im,
        Complex.cos_ofReal_re, Complex.cos_ofReal_im,
        Complex.sin_ofReal_re, Complex.sin_ofReal_im,
        Complex.I_re, Complex.I_im, mul_one, mul_zero, zero_mul,
        add_zero, zero_add, sub_zero]"""
    if old not in text:
        raise RuntimeError(f"expected ramp proof fragment not found in {path}")
    path.write_text(text.replace(old, new, 1), encoding="utf-8")

    scaling_source = Path(__file__).with_name("DWindowSharpScaling.lean")
    shutil.copyfile(scaling_source, gap / scaling_source.name)


if __name__ == "__main__":
    main()
