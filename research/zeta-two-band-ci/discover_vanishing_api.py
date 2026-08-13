#!/usr/bin/env python3
"""Generate Lean aliases for likely existing vanishing-error theorems."""
from __future__ import annotations
import re,sys
from pathlib import Path

DECL=re.compile(r"(?m)^(?:private\s+)?(?:theorem|lemma)\s+([A-Za-z0-9_']+)")
NS=re.compile(r"(?m)^namespace\s+([A-Za-z0-9_.']+)\s*$")

def scan(path):
 text=path.read_text();namespaces=NS.findall(text);ns=namespaces[-1] if namespaces else ""
 ms=list(DECL.finditer(text));out=[]
 for i,m in enumerate(ms):
  end=ms[i+1].start() if i+1<len(ms) else len(text)
  block=text[m.start():end];name=m.group(1);full=f"{ns}.{name}" if ns else name
  out.append((full,block,path.name))
 return out

def score(block,kind):
 low=block.lower();s=0
 if "tendsto" in low:s+=25
 if "=o[" in block or "islittleo" in low:s+=25
 if "𝓝 0" in block or "nhds 0" in low:s+=15
 if kind in low:s+=20
 if "error" in low:s+=10
 if "overlap" in low:s+=8
 if "tail" in low and kind!="tail":s+=3
 if "ramp" in low and kind!="ramp":s+=3
 return s

def main():
 if len(sys.argv)<3:raise SystemExit("usage: discover_vanishing_api.py OUTPUT INPUT...")
 out=Path(sys.argv[1]);decls=[]
 for arg in sys.argv[2:]:decls.extend(scan(Path(arg)))
 picks={}
 for kind in ("ramp","tail","profile","overlap"):
  ranked=sorted([(score(b,kind),n,f) for n,b,f in decls],reverse=True)
  if ranked and ranked[0][0]>20:picks[kind]=ranked[0]
 lines=["/- Generated aliases for discovered existing vanishing theorems. -/","import Mathlib",""]
 # Import source modules based on file stems.
 stems=sorted({Path(f).stem for _,_,f in picks.values()})
 lines=[f"import Zeta23.GapMatching.{s}" for s in stems]+["","noncomputable section","","namespace Zeta23.GapMatching.DiscoveredVanishingAPI",""]
 for kind,(s,n,f) in picks.items():lines += [f"abbrev {kind}Vanishing := @{n}",""]
 lines += ["end Zeta23.GapMatching.DiscoveredVanishingAPI",""]
 out.write_text("\n".join(lines));print(picks)
if __name__=="__main__":main()
