#!/usr/bin/env python3
"""Generate the one-band D-window fixed-point seam from the generic two-band file."""

from __future__ import annotations

import sys
from pathlib import Path


def main() -> None:
    if len(sys.argv) != 2:
        raise SystemExit("usage: generate_one_band_d.py <zeta23-workspace>")
    gap = Path(sys.argv[1]) / "Zeta23" / "GapMatching"
    src = (gap / "TwoBandGapMatchingD.lean").read_text(encoding="utf-8")
    replacements = [
        ("two-band", "one-band"),
        ("TwoBandPotentialSafeNumerics", "OneBandPotentialSafeNumerics"),
        ("TwoBandGapMatchingD", "OneBandGapMatchingD"),
        ("EventualTwoBandBonusD", "EventualOneBandBonusD"),
    ]
    for old, new in replacements:
        src = src.replace(old, new)
    (gap / "OneBandGapMatchingD.lean").write_text(src, encoding="utf-8")


if __name__ == "__main__":
    main()
