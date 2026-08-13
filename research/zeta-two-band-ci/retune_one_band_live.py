#!/usr/bin/env python3
"""Retune the one-band physical floors for a valid live improvement.

Only `p` and `j` are raised.  The generated sharp-profile proof is then
recompiled from scratch; the branch is updated only if every exact transition,
profile, and additive-target theorem passes the pinned kernel.
"""
from __future__ import annotations
import re
import sys
from pathlib import Path

REPLACEMENTS = {
    "p": "0.0000062",
    "j": "0.0000021",
}


def main():
    path=Path(sys.argv[1]); text=path.read_text()
    for name,value in REPLACEMENTS.items():
        pattern=rf"(?m)^def {name} : ℝ := .*?$"
        replacement=f"def {name} : ℝ := {value}"
        text,count=re.subn(pattern,replacement,text,count=1)
        if count != 1:
            raise RuntimeError(f"expected exactly one definition of {name}")
    path.write_text(text)

if __name__=="__main__": main()
