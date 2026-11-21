#!/usr/bin/env python3
"""Align the pinned Zeta23 source with the RH release's Lean and Mathlib."""
import hashlib
import json
from pathlib import Path
import subprocess
import sys


def configure(zeta: Path) -> None:
    root = Path(__file__).resolve().parents[1]
    pins = json.loads((root / "challenge/contract.json").read_text())["trustedUpstream"]
    release = (root / "challenge/foundation/lake-manifest.json").read_bytes()
    if hashlib.sha256(release).hexdigest() != pins["rh"]["dependencyManifestSha256"]:
        raise ValueError("RH release dependency manifest digest mismatch")
    mathlib = next(p for p in json.loads(release)["packages"] if p["name"] == "mathlib")
    if mathlib["rev"] != pins["mathlibCommit"]:
        raise ValueError("RH release and competition Mathlib revisions differ")

    def git(*args: str) -> str:
        return subprocess.check_output(["git", "-C", zeta, *args], text=True).strip()

    if git("rev-parse", "HEAD") != pins["commit"]:
        raise ValueError("Unexpected Zeta23 source revision")
    orig = json.loads(git("show", "HEAD:lake-manifest.json"))
    old_rev = next(p["rev"] for p in orig["packages"] if p["name"] == "mathlib")
    lakefile = git("show", "HEAD:lakefile.toml")
    old = f'rev = "{old_rev}"'
    if lakefile.count(old) != 1:
        raise ValueError("Unexpected upstream Lake configuration")
    (zeta / "lakefile.toml").write_text(lakefile.replace(old, f'rev = "{mathlib["rev"]}"') + "\n")
    (zeta / "lake-manifest.json").write_bytes(release)
    (zeta / "lean-toolchain").write_text(pins["leanToolchain"] + "\n")


if __name__ == "__main__":
    if len(sys.argv) != 2:
        raise SystemExit("Usage: prepare-rh-foundation.py <pinned-zeta23-checkout>")
    configure(Path(sys.argv[1]))
