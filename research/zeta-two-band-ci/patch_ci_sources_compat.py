#!/usr/bin/env python3
"""Run the legacy CI patcher while preserving the now-fixed one-band source."""

from __future__ import annotations

import subprocess
import sys
from pathlib import Path


def main() -> None:
    if len(sys.argv) != 2:
        raise SystemExit("usage: patch_ci_sources_compat.py <zeta23-workspace>")

    workspace = Path(sys.argv[1])
    path = workspace / "Zeta23/GapMatching/OneBandPotentialSafeNumerics.lean"
    fixed = path.read_text(encoding="utf-8")
    already_fixed = "def physicalFloor" in fixed

    if already_fixed:
        old = fixed
        old = old.replace(
            """/-- The actual length/edge charge, before adding the telescoping potential. -/
def physicalFloor (previous current : State) : ℝ :=
  B * lengthFloor current
    + shortFloor current
    + longFloor previous current

/-- Physical charge plus the potential difference. -/
def transitionFloor (previous current : State) : ℝ :=
  physicalFloor previous current + phi previous - phi current""",
            """def transitionFloor (previous current : State) : ℝ :=
  B * lengthFloor current
    + shortFloor current
    + longFloor previous current
    + phi previous - phi current""",
        )
        old = old.replace(
            """    norm_num [A, B, p, j, badLeft, transitionFloor, physicalFloor,
      lengthFloor, shortFloor, longFloor, phi]""",
            """    norm_num [A, B, p, j, badLeft, transitionFloor,
      lengthFloor, shortFloor, longFloor, phi]""",
        )
        old = old.replace(
            """/-- A step whose physical cost dominates the exact physical floor gives the
abstract local certificate after adding the telescoping potential once. -/
theorem localCertificate_of_dominates
    (previous : State) (g : GapDatum State)
    (h : physicalFloor previous g.state
      ≤ stepCost B State.good previous g) :
    LocalCertificate A B State.good phi previous g := by
  unfold LocalCertificate
  calc
    A ≤ transitionFloor previous g.state :=
      transition_certificate previous g.state
    _ = physicalFloor previous g.state
          + phi previous - phi g.state := rfl
    _ ≤ stepCost B State.good previous g
          + phi previous - phi g.state := by
      nlinarith""",
            """/-- A step whose physical cost dominates the exact transition floor gives the
abstract local certificate. -/
theorem localCertificate_of_dominates
    (previous : State) (g : GapDatum State)
    (h : transitionFloor previous g.state
      ≤ stepCost B State.good previous g) :
    LocalCertificate A B State.good phi previous g :=
  (transition_certificate previous g.state).trans h""",
        )
        path.write_text(old, encoding="utf-8")

    try:
        subprocess.run(
            [sys.executable,
             str(Path(__file__).with_name("patch_ci_sources.py")),
             str(workspace)],
            check=True,
        )
    finally:
        if already_fixed:
            path.write_text(fixed, encoding="utf-8")


if __name__ == "__main__":
    main()
