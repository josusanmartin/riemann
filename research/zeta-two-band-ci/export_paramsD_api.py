#!/usr/bin/env python3
"""Append stable aliases for useful declarations in ThmD/ParamsD.lean."""
from __future__ import annotations
import re,sys
from pathlib import Path


def blocks(text):
    pat=re.compile(r"(?m)^(?:private\s+)?(?:theorem|lemma|def|abbrev)\s+([A-Za-z0-9_']+)")
    ms=list(pat.finditer(text))
    for i,m in enumerate(ms):
        end=ms[i+1].start() if i+1<len(ms) else len(text)
        yield m.group(1),text[m.start():end]


def choose(items, scorer):
    vals=[(scorer(n,b),n) for n,b in items]
    vals=[x for x in vals if x[0]>0]
    return max(vals)[1] if vals else None


def main():
    path=Path(sys.argv[1]);text=path.read_text();marker="-- stable-api-export: paramsD"
    if marker in text:return
    items=list(blocks(text))
    v=choose(items,lambda n,b: (30 if ("def " in b or "abbrev " in b) and "vd" in n.lower() else 0)+(5 if "ℝ → ℝ" in b else 0))
    adm=choose(items,lambda n,b:(35 if "AdmWindow" in b else 0)+(15 if "atD" in b else 0)+(5 if "theorem " in b else 0))
    sample=choose(items,lambda n,b:(30 if "phiHatR" in b and "vHatR" in b else 0)+(10 if "atD" in b else 0))
    grid=choose(items,lambda n,b:(30 if ".tau" in b or "tau" in n.lower() else 0)+(15 if "2 * Real.pi" in b or "2 * π" in b else 0)+(10 if "atD" in b else 0))
    scale=choose(items,lambda n,b:(30 if "dScale" in b else 0)+(20 if "av" in b and "^ 2" in b else 0))
    apos=choose(items,lambda n,b:(25 if "0 <" in b and ("aD" in b or "dScale" in b) else 0)+(10 if "pos" in n.lower() else 0))
    lpos=choose(items,lambda n,b:(25 if "0 <" in b and ".L" in b else 0)+(10 if "pos" in n.lower() else 0))
    ns="Zeta23.ThmD"
    lines=["",marker,f"namespace {ns}",""]
    for alias,name in [("exportedVD",v),("exportedAdmWindowD",adm),("exportedSampleD",sample),("exportedGridD",grid),("exportedScaleD",scale),("exportedScalePosD",apos),("exportedLPosD",lpos)]:
        if name:lines += [f"abbrev {alias} := @{name}" if alias!="exportedVD" else f"abbrev {alias} := {name}",""]
    lines += [f"end {ns}",""]
    path.write_text(text+"\n".join(lines));print({"v":v,"adm":adm,"sample":sample,"grid":grid,"scale":scale,"apos":apos,"lpos":lpos})

if __name__=="__main__":main()
