#!/usr/bin/env python3
"""Export all likely scalar D-window definitions under stable descriptive aliases."""
from __future__ import annotations
import re,sys
from pathlib import Path

def defs(text):
 p=re.compile(r"(?m)^(?:private\s+)?(?:def|abbrev)\s+([A-Za-z0-9_']+)")
 ms=list(p.finditer(text))
 for i,m in enumerate(ms):yield m.group(1),text[m.start():(ms[i+1].start() if i+1<len(ms) else len(text))]

def choose(items,tokens):
 vals=[]
 for n,b in items:
  low=n.lower();score=0
  for token,weight in tokens:
   if token in low:score+=weight
  if "ℝ" in b:score+=2
  if score:vals.append((score,n))
 return max(vals)[1] if vals else None

def main():
 path=Path(sys.argv[1]);text=path.read_text();marker="-- stable-api-export: all-paramsD-defs"
 if marker in text:return
 items=list(defs(text))
 picks={
  "exportedRawWindowD":choose(items,[("vd",30),("window",5)]),
  "exportedRampWidthD":choose(items,[("wd",30),("width",10),("ramp",5)]),
  "exportedDecayConstD":choose(items,[("cd",30),("decay",10),("const",3)]),
  "exportedAverageD":choose(items,[("ad",25),("average",10)]),
  "exportedLengthD":choose(items,[("ld",25),("length",8)]),
  "exportedScaleDefD":choose(items,[("dscale",40),("scale",15)]),
 }
 lines=["",marker,"namespace Zeta23.ThmD",""]
 for alias,name in picks.items():
  if name:lines += [f"abbrev {alias} := {name}",""]
 lines += ["end Zeta23.ThmD",""]
 path.write_text(text+"\n".join(lines));print(picks)
if __name__=="__main__":main()
