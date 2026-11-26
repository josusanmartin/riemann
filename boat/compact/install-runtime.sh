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
def fetch(release, name, checksum):
    if not re.fullmatch(r"[a-f0-9]{64}", checksum):
        raise ValueError("Invalid runtime checksum")
    req = f"https://github.com/josusanmartin/riemann/releases/download/{release}/{name}"
    digest = hashlib.sha256()
    with urllib.request.urlopen(req, timeout=90) as src, open(name, "xb") as dst:
        while chunk := src.read(1024 * 1024):
            digest.update(chunk)
            dst.write(chunk)
    if digest.hexdigest() != checksum:
        raise ValueError(f"Worker runtime checksum mismatch for {name}")
for index, checksum in enumerate(parts):
    fetch(tag, f"compact-runtime.tar.zst.part{index:02d}", checksum)
zeta = pins["zeta"]
if not re.fullmatch(r"compact-zeta-build-[a-zA-Z0-9.-]+", zeta["release"]):
    raise ValueError("Invalid Zeta23 release")
fetch(zeta["release"], "zeta-objects.tar.zst", zeta["sha256"])
PY
mkdir "$destination"
cat compact-runtime.tar.zst.part* | zstd -dc | tar -xf - -C "$destination" --no-same-owner
mkdir "$destination/deps/zeta"
tar --zstd -xf zeta-objects.tar.zst -C "$destination/deps/zeta" --no-same-owner
test -s "$destination/deps/zeta/ChallengeDeps.olean"
test -s "$destination/foundation/Main.olean"
test -x "$destination/checker/matchrunner"
