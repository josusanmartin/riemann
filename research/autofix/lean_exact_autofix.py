#!/usr/bin/env python3
"""Replace `exact?` holes with Lean's own pinned-toolchain suggestions.

The script runs `lake env lean` on one module, parses the first `Try this:`
suggestion attached to an `exact?`, patches the first remaining hole, and
repeats.  It refuses suggestions containing `sorry`, `admit`, or new axioms.
"""
from __future__ import annotations

import argparse
import re
import subprocess
from pathlib import Path

FORBIDDEN = ("sorry", "admit", "axiom", "unsafe")


def run_lean(workspace: Path, source: Path) -> tuple[int, str]:
    proc = subprocess.run(
        ["lake", "env", "lean", str(source)],
        cwd=workspace,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        text=True,
    )
    return proc.returncode, proc.stdout


def extract_suggestion(log: str) -> str | None:
    # Lean 4 emits either `Try this: exact ...` or a multiline indented block.
    inline = re.findall(r"Try this:\s*(exact\s+[^\n]+)", log)
    if inline:
        return inline[-1].strip()
    lines = log.splitlines()
    for idx in range(len(lines) - 1, -1, -1):
        if "Try this:" not in lines[idx]:
            continue
        collected: list[str] = []
        for line in lines[idx + 1:]:
            stripped = re.sub(r"^.*?\] ?", "", line).rstrip()
            if not stripped.strip():
                if collected:
                    break
                continue
            body = stripped.lstrip()
            if body.startswith(("exact ", "simpa ", "apply ", "refine ", "aesop", "omega", "linarith", "nlinarith")):
                collected.append(body)
                continue
            if collected and (line.startswith("  ") or line.startswith("\t")):
                collected.append(body)
                continue
            if collected:
                break
        if collected:
            return "\n".join(collected)
    return None


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("workspace", type=Path)
    parser.add_argument("source", type=Path)
    parser.add_argument("--max-rounds", type=int, default=12)
    parser.add_argument("--report", type=Path)
    args = parser.parse_args()

    report: list[str] = []
    for round_no in range(args.max_rounds):
        text = args.source.read_text(encoding="utf-8")
        if "exact?" not in text:
            report.append("no exact? holes remain")
            break
        status, log = run_lean(args.workspace, args.source)
        suggestion = extract_suggestion(log)
        report.append(f"round {round_no}: lean_status={status}")
        if suggestion is None:
            report.append("no exact suggestion found")
            report.append(log[-12000:])
            break
        if any(word in suggestion for word in FORBIDDEN):
            raise RuntimeError(f"refusing forbidden suggestion: {suggestion}")
        report.append(f"suggestion: {suggestion}")
        args.source.write_text(text.replace("exact?", suggestion, 1), encoding="utf-8")
    else:
        report.append("maximum rounds reached")

    final_status, final_log = run_lean(args.workspace, args.source)
    report.append(f"final_status={final_status}")
    if final_status != 0:
        report.append(final_log[-16000:])
    output = "\n".join(report) + "\n"
    if args.report:
        args.report.parent.mkdir(parents=True, exist_ok=True)
        args.report.write_text(output, encoding="utf-8")
    print(output)


if __name__ == "__main__":
    main()
