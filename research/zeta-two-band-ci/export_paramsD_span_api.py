#!/usr/bin/env python3
from __future__ import annotations
import re,sys
from pathlib import Path

def blocks(t):
 p=re.compile(r"(?m)^(?:private\s+)?(?:theorem|lemma|def|abbrev)\s+([A-Za-z0-9_']+)");ms=list(p.finditer(t))
 for i,m in enumerate(ms):yield m.group(1),t[m.start():(ms[i+1].start() if i+1<len(ms) else len(t))]

def main():
 path=Path(sys.argv[1]);t=path.read_text();marker="-- stable-api-export: paramsD-span"
 if marker in t:return
 cand=[]
 for n,b in blocks(t):
  if not("theorem " in b or "lemma " in b):continue
  low=(n+b).lower();s=0
  if ".d" in b or " d " in b:s+=15
  if "tau" in low or "grid" in low:s+=12
  if "2 * t" in low or "2*t" in low:s+=12
  if "real.pi" in low or "π" in b:s+=5
  if "≤" in b:s+=5
  if s:cand.append((s,n))
 if not cand:raise RuntimeError("no span theorem found")
 s,n=max(cand);t+=f"\n\n{marker}\nnamespace Zeta23.ThmD\n\nabbrev exportedGridSpanD := @{n}\n\nend Zeta23.ThmD\n";path.write_text(t);print(n,s)
if __name__=="__main__":main()
