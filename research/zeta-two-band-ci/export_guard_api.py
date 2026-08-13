#!/usr/bin/env python3
"""Append stable aliases for central guard-cardinality and little-o theorems."""
from __future__ import annotations
import re,sys
from pathlib import Path


def blocks(text):
    pat=re.compile(r"(?m)^(?:private\s+)?(?:theorem|lemma|def|abbrev)\s+([A-Za-z0-9_']+)")
    ms=list(pat.finditer(text))
    for i,m in enumerate(ms):
        end=ms[i+1].start() if i+1<len(ms) else len(text)
        yield m.group(1),text[m.start():end]


def best(items, scorer):
    vals=[(scorer(n,b),n) for n,b in items]
    vals=[x for x in vals if x[0]>0]
    return max(vals)[1] if vals else None


def main():
    path=Path(sys.argv[1]); text=path.read_text(); marker="-- stable-api-export: central-guard"
    if marker in text:return
    items=list(blocks(text))
    small=best(items,lambda n,b:
        (30 if "=o[" in b or "IsLittleO" in b else 0)
        +(15 if "guard" in (n+b).lower() else 0)
        +(8 if "sqrt" in b.lower() else 0))
    loss=best(items,lambda n,b:
        (25 if ("ncard" in b or "card" in b.lower()) else 0)
        +(20 if "guard" in (n+b).lower() else 0)
        +(10 if "N0" in b or "simple" in b.lower() else 0)
        +(5 if "≤" in b else 0))
    defs=[]
    for n,b in items:
        low=(n+b).lower()
        if ("def " in b or "abbrev " in b) and "guard" in low:
            defs.append(n)
    guarddef=defs[-1] if defs else None
    namespaces=re.findall(r"(?m)^namespace\s+([A-Za-z0-9_.']+)\s*$",text)
    ns=namespaces[-1] if namespaces else "Zeta23.GapMatching.CentralGuardCountD"
    lines=["",marker,f"namespace {ns}",""]
    if guarddef:lines += [f"abbrev exportedGuardCount := {guarddef}",""]
    if small:lines += [f"abbrev exportedGuardSmall := @{small}",""]
    if loss:lines += [f"abbrev exportedCentralLoss := @{loss}",""]
    lines += [f"end {ns}",""]
    path.write_text(text+"\n".join(lines))
    print({"guard":guarddef,"small":small,"loss":loss})

if __name__=="__main__":main()
