#!/usr/bin/env python3
"""Append extra stable aliases to OneBandSharpProfile.lean."""
from __future__ import annotations
import re
import sys
from pathlib import Path


def blocks(text: str):
    pat = re.compile(r"(?m)^(?:private\s+)?(?:theorem|lemma|def|abbrev)\s+([A-Za-z0-9_']+)")
    ms = list(pat.finditer(text))
    for i, m in enumerate(ms):
        end = ms[i + 1].start() if i + 1 < len(ms) else len(text)
        yield m.group(1), text[m.start():end]


def choose(items, score):
    ranked = [(score(name, block), name) for name, block in items]
    ranked = [x for x in ranked if x[0] > 0]
    if not ranked:
        return None
    return max(ranked)[1]


def main():
    path = Path(sys.argv[1])
    text = path.read_text()
    marker = "-- stable-api-export-extra: one-band-sharp-profile"
    if marker in text:
        return
    items = list(blocks(text))
    lam = choose(items, lambda n,b: 20 if ("def " in b and "lam" in n.lower()) else 0)
    baseline = choose(items, lambda n,b:
        (30 if ("theorem " in b or "lemma " in b) and "ThmD.HD" in b else 0)
        + (10 if "672500" in b else 0)
        + (5 if "baseline" in n.lower() else 0))
    unit = choose(items, lambda n,b:
        (25 if ("theorem " in b or "lemma " in b) and "profile" in b.lower() else 0)
        + (15 if "≤ 1" in b or "<= 1" in b else 0)
        + (5 if "abs" in n.lower() or "bound" in n.lower() else 0))
    namespaces = re.findall(r"(?m)^namespace\s+([A-Za-z0-9_.']+)\s*$", text)
    ns = namespaces[-1] if namespaces else "Zeta23.GapMatching.OneBandSharpProfile"
    lines = ["", marker, f"namespace {ns}", ""]
    if lam:
        lines += [f"abbrev exportedLambda := {lam}", ""]
    if baseline:
        lines += [f"abbrev exportedBaselineCertificate := @{baseline}", ""]
    if unit:
        lines += [f"abbrev exportedSharpProfileUnitCertificate := @{unit}", ""]
    lines += [f"end {ns}", ""]
    path.write_text(text + "\n".join(lines))
    print({"lambda": lam, "baseline": baseline, "unit": unit})


if __name__ == "__main__":
    main()
