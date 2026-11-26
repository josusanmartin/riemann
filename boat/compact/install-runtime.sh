#!/usr/bin/env bash
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
destination=${1:?fresh runtime directory}
manifest=${2:?pinned build manifest}
work=$(mktemp -d)
trap 'rm -rf -- "$work"' EXIT
cd "$work"
python3 - "$manifest" <<'PY'
import hashlib, json, pathlib, re, sys, urllib.request
pins = json.loads(pathlib.Path(sys.argv[1]).read_text())
tag = pins["release"]
if not re.fullmatch(r"compact-runtime-build-[a-zA-Z0-9.-]+", tag):
    raise ValueError("Invalid verifier runtime release")
parts = pins["parts"]
if not 1 <= len(parts) <= 12:
    raise ValueError("Unexpected runtime part count")
for index, checksum in enumerate(parts):
    if not re.fullmatch(r"[a-f0-9]{64}", checksum):
        raise ValueError("Invalid part checksum")
    name = f"compact-runtime.tar.zst.part{index:02d}"
    req = f"https://github.com/josusanmartin/riemann/releases/download/{tag}/{name}"
    digest = hashlib.sha256()
    with urllib.request.urlopen(req, timeout=90) as src, open(name, "xb") as dst:
        while chunk := src.read(1024 * 1024):
            digest.update(chunk)
            dst.write(chunk)
    if digest.hexdigest() != checksum:
        raise ValueError(f"Worker runtime checksum mismatch for {name}")
PY
mkdir "$destination"
cat compact-runtime.tar.zst.part* | zstd -dc | tar -xf - -C "$destination" --no-same-owner
test -s "$destination/foundation/Main.olean"
test -x "$destination/checker/matchrunner"
