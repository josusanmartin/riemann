#!/usr/bin/env python3
"""Append a stable alias for the strongest D-window analytic-input theorem."""
from __future__ import annotations
import re,sys
from pathlib import Path

def blocks(t):
 p=re.compile(r"(?m)^(?:private\s+)?(?:theorem|lemma)\s+([A-Za-z0-9_']+)");ms=list(p.finditer(t))
 for i,m in enumerate(ms):yield m.group(1),t[m.start():(ms[i+1].start() if i+1<len(ms) else len(t))]

def main():
 path=Path(sys.argv[1]);t=path.read_text();marker="-- stable-api-export: gap-D-seam"
 if marker in t:return
 vals=[]
 for n,b in blocks(t):
  low=(n+b).lower();s=0
  if "gapmatchinganalyticinput" in low:s+=30
  if "epsilon" in low or "ε" in b:s+=10
  if "n0s" in low:s+=10
  if "atd" in low:s+=10
  if "fixed" in low or "density" in low:s+=5
  if s:vals.append((s,n))
 if not vals:raise RuntimeError("no D-window gap seam theorem found")
 s,n=max(vals);namespaces=re.findall(r"(?m)^namespace\s+([A-Za-z0-9_.']+)\s*$",t);ns=namespaces[-1] if namespaces else "Zeta23.GapMatching.TwoBandGapMatchingD"
 t+=f"\n\n{marker}\nnamespace {ns}\n\nabbrev exportedDGapSeam := @{n}\n\nend {ns}\n";path.write_text(t);print(n,s)
if __name__=="__main__":main()
