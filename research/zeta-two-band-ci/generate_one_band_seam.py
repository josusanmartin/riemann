#!/usr/bin/env python3
"""Generate OneBandGapMatchingD.lean from the proven D-window seam."""

from pathlib import Path

root = Path(__file__).resolve().parent
source = (root / "TwoBandGapMatchingD.lean").read_text(encoding="utf-8")

text = source
text = text.replace(
    "import Zeta23.GapMatching.TwoBandPotentialSafeNumerics",
    "import Zeta23.GapMatching.OneBandPotentialSafeNumerics",
)
text = text.replace(
    "namespace Zeta23.GapMatching.TwoBandGapMatchingD",
    "namespace Zeta23.GapMatching.OneBandGapMatchingD",
)
text = text.replace(
    "open Zeta23.GapMatching.TwoBandPotentialSafeNumerics",
    "open Zeta23.GapMatching.OneBandPotentialSafeNumerics",
)
text = text.replace("EventualTwoBandBonusD", "EventualOneBandBonusD")
text = text.replace("two-band", "one-band").replace("Two-band", "One-band")

# Normalize the gain into the generic fixed-point shape.  This is the same
# correction already exercised by the pinned CI patch on the source seam.
old = """  have hden : Acoef < 1 := parameter_ranges.2.1

  exact fixed_point_certificate
    (N := N)
    (lower := fun T => (Z.N0s T (2 * T) : ℝ))
    (bonus := fun T => 2 * energy T)
    (error := error)
    (delta := 2 - c⁻¹)
    (beta := Acoef)
    (span := 1)
    (lam := Bcoef / (2 * Acoef))
    hN0 hcert hgap.gain hgap.error_small hden"""
new = """  have hden : Acoef < 1 := parameter_ranges.2.1
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

  exact fixed_point_certificate
    (N := N)
    (lower := fun T => (Z.N0s T (2 * T) : ℝ))
    (bonus := fun T => 2 * energy T)
    (error := error)
    (delta := 2 - c⁻¹)
    (beta := Acoef)
    (span := 1)
    (lam := Bcoef / (2 * Acoef))
    hN0 hcert hgain hgap.error_small hden'"""
if old not in text:
    raise RuntimeError("fixed-point source block not found")
text = text.replace(old, new, 1)

(root / "OneBandGapMatchingD.lean").write_text(text, encoding="utf-8")
