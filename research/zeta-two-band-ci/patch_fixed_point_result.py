#!/usr/bin/env python3
"""Normalize the algebraic coefficient in the copied D-window seam."""

from __future__ import annotations

import sys
from pathlib import Path


if len(sys.argv) != 2:
    raise SystemExit("usage: patch_fixed_point_result.py <zeta23-workspace>")

path = Path(sys.argv[1]) / "Zeta23" / "GapMatching" / "TwoBandGapMatchingD.lean"
text = path.read_text(encoding="utf-8")
old = """  exact fixed_point_certificate
    (N := N)"""
new = """  have hcoef : 2 * Acoef * (Bcoef / (2 * Acoef)) = Bcoef := by
    field_simp [hAne]

  simpa only [hNdef, hcoef, mul_one] using
    fixed_point_certificate
    (N := N)"""
if old not in text:
    raise RuntimeError(f"expected fixed-point block not found in {path}")
path.write_text(text.replace(old, new, 1), encoding="utf-8")
