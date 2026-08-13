#!/usr/bin/env python3
"""Choose the strongest live-valid one-band retuning accepted by pinned Lean."""
from __future__ import annotations
import argparse,re,shutil,subprocess
from pathlib import Path

P_CANDIDATES=["0.0000062","0.00000615","0.0000061","0.00000605","0.0000060","0.00000595","0.0000059"]
J_CANDIDATES=["0.0000021","0.00000205","0.0000020"]


def replace_def(text,name,value):
    pattern=rf"(?m)^def {name} : ℝ := .*?$"
    out,n=re.subn(pattern,f"def {name} : ℝ := {value}",text,count=1)
    if n!=1: raise RuntimeError(f"definition {name} not found uniquely")
    return out


def build(workspace:Path)->tuple[bool,str]:
    modules=[
      "Zeta23.GapMatching.OneBandPotentialSafeNumerics",
      "Zeta23.GapMatching.OneBandPotentialOverlap",
      "Zeta23.GapMatching.OneBandSharpProfile",
      "Zeta23.GapMatching.OneBandLiveFixedSimpleNumerics",
    ]
    proc=subprocess.run(["lake","build",*modules],cwd=workspace,
      stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
    return proc.returncode==0,proc.stdout


def main():
    ap=argparse.ArgumentParser();ap.add_argument("workspace",type=Path);ap.add_argument("source",type=Path);ap.add_argument("report",type=Path)
    a=ap.parse_args(); original=a.source.read_text(); report=[]
    for p in P_CANDIDATES:
      for j in J_CANDIDATES:
        a.source.write_text(replace_def(replace_def(original,"p",p),"j",j))
        ok,log=build(a.workspace)
        report.append(f"p={p} j={j} status={'PASS' if ok else 'FAIL'}")
        if ok:
          a.report.parent.mkdir(parents=True,exist_ok=True);a.report.write_text("\n".join(report)+"\n")
          print(report[-1]);return
        report.append(log[-3000:])
    a.source.write_text(original)
    a.report.parent.mkdir(parents=True,exist_ok=True);a.report.write_text("\n".join(report)+"\n")
    raise SystemExit("no candidate retuning passed")

if __name__=="__main__":main()
