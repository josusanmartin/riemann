#!/usr/bin/env python3
"""Append a stable alias for the strongest ramp-to-sharp comparison theorem."""
from __future__ import annotations
import re
import sys
from pathlib import Path


def blocks(text: str):
    pat = re.compile(r"(?m)^(?:private\s+)?(?:theorem|lemma|def|abbrev)\s+([A-Za-z0-9_']+)")
    ms = list(pat.finditer(text))
    for i,m in enumerate(ms):
        end = ms[i+1].start() if i+1 < len(ms) else len(text)
        yield m.group(1), text[m.start():end]


def main():
    path=Path(sys.argv[1]); text=path.read_text()
    marker="-- stable-api-export: d-window-ramp"
    if marker in text: return
    candidates=[]
    for name,block in blocks(text):
        if not ("theorem " in block or "lemma " in block): continue
        score=0
        low=(name+" "+block).lower()
        if "vphir" in low: score+=20
        if "sharp" in low: score+=20
        if "abs" in low or "|" in block: score+=8
        if "12" in block: score+=10
        if "integral" in low: score+=3
        if "≤" in block or "<=" in block: score+=5
        if score: candidates.append((score,name,block[:500]))
    if not candidates: raise RuntimeError("no ramp-comparison theorem found")
    score,name,_=max(candidates)
    namespaces=re.findall(r"(?m)^namespace\s+([A-Za-z0-9_.']+)\s*$",text)
    ns=namespaces[-1] if namespaces else "Zeta23.GapMatching.DWindowRampEstimate"
    appendix=f"\n\n{marker}\nnamespace {ns}\n\nabbrev exportedRampComparison := @{name}\n\nend {ns}\n"
    path.write_text(text+appendix)
    print({"theorem":name,"score":score})

if __name__=="__main__": main()
