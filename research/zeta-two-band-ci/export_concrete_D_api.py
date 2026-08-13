#!/usr/bin/env python3
"""Generate stable aliases for concrete Theorem-D objects across source files."""
from __future__ import annotations
import re,sys
from pathlib import Path
DECL=re.compile(r"(?m)^(?:private\s+)?(?:theorem|lemma|def|abbrev)\s+([A-Za-z0-9_']+)")
NS=re.compile(r"(?m)^namespace\s+([A-Za-z0-9_.']+)\s*$")

def scan(path):
 t=path.read_text();nss=NS.findall(t);ns=nss[-1] if nss else "";ms=list(DECL.finditer(t));out=[]
 for i,m in enumerate(ms):
  end=ms[i+1].start() if i+1<len(ms) else len(t);name=m.group(1);out.append((f"{ns}.{name}" if ns else name,t[m.start():end],path.stem))
 return out

def choose(ds,scorer):
 vals=[(scorer(n,b),n,f) for n,b,f in ds];vals=[x for x in vals if x[0]>0];return max(vals) if vals else None

def main():
 if len(sys.argv)<3:raise SystemExit("usage: export_concrete_D_api.py OUTPUT INPUT...")
 out=Path(sys.argv[1]);ds=[]
 for x in sys.argv[2:]:ds+=scan(Path(x))
 z=choose(ds,lambda n,b:(30 if "ZeroConfig" in b else 0)+(12 if "zeta" in (n+b).lower() else 0)+(5 if "def " in b else 0))
 p=choose(ds,lambda n,b:(30 if ": Params" in b or "Params :=" in b else 0)+(12 if "param" in (n+b).lower() else 0)+(8 if "def " in b else 0))
 fixed=choose(ds,lambda n,b:(25 if "HD" in b else 0)+(15 if "epsilon" in b.lower() or "ε" in b else 0)+(10 if "N0" in b else 0)+(8 if "thmD" in (n+b) else 0))
 modules=sorted({f for x in (z,p,fixed) if x for f in [x[2]]})
 lines=[f"import Zeta23.ThmD.{m}" for m in modules]+["","noncomputable section","","namespace Zeta23.GapMatching.ConcreteDAPI",""]
 for alias,x in [("zeroConfig",z),("params",p),("fixedTheorem",fixed)]:
  if x:lines += [f"abbrev {alias} := @{x[1]}" if alias=="fixedTheorem" else f"abbrev {alias} := {x[1]}",""]
 lines += ["end Zeta23.GapMatching.ConcreteDAPI",""]
 out.write_text("\n".join(lines));print({"zero":z,"params":p,"fixed":fixed})
if __name__=="__main__":main()
