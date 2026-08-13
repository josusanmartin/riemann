#!/usr/bin/env python3
"""Append stable aliases for the strongest D-window profile-algebra lemmas."""
from __future__ import annotations
import re,sys
from pathlib import Path


def blocks(text):
    pat=re.compile(r"(?m)^(?:private\s+)?(?:theorem|lemma|def|abbrev)\s+([A-Za-z0-9_']+)")
    ms=list(pat.finditer(text))
    for i,m in enumerate(ms):
        end=ms[i+1].start() if i+1<len(ms) else len(text)
        yield m.group(1),text[m.start():end]


def best(items,words):
    vals=[]
    for n,b in items:
        if not ("theorem " in b or "lemma " in b):continue
        low=(n+" "+b).lower(); score=sum(w in low for w in words)
        if "≤" in b or "<=" in b:score+=1
        if "abs" in low or "|" in b:score+=1
        vals.append((score,n))
    return max(vals)[1] if vals and max(vals)[0]>0 else None


def main():
    path=Path(sys.argv[1]);text=path.read_text();marker="-- stable-api-export: d-window-profile-algebra"
    if marker in text:return
    items=list(blocks(text))
    finite=best(items,["finite","full","overlap","error"])
    sharp=best(items,["full","sharp","profile","error"])
    normalized=best(items,["normalized","profile","overlap"])
    namespaces=re.findall(r"(?m)^namespace\s+([A-Za-z0-9_.']+)\s*$",text)
    ns=namespaces[-1] if namespaces else "Zeta23.GapMatching.DWindowProfileAlgebra"
    lines=["",marker,f"namespace {ns}",""]
    if finite:lines += [f"abbrev exportedFiniteFull := @{finite}",""]
    if sharp:lines += [f"abbrev exportedFullSharp := @{sharp}",""]
    if normalized:lines += [f"abbrev exportedNormalizedProfile := @{normalized}",""]
    lines += [f"end {ns}",""]
    path.write_text(text+"\n".join(lines));print({"finite":finite,"sharp":sharp,"normalized":normalized})

if __name__=="__main__":main()
