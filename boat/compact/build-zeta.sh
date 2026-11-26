#!/usr/bin/env bash
# Compile the entire published Zeta23 library with the same Mathlib as compact RH.
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
site=$(cd "$here/../.." && pwd)
project=$(realpath -m "${1:?fresh build directory}")
packages=$(realpath "${2:?pinned Lake packages directory}")
git init -q "$project"
git -C "$project" fetch -q --depth=1 https://github.com/anthropics/formal-math.git 3635e74826a4c1fcece7d1cd2b6fa75e43a00510
git -C "$project" checkout -q --detach FETCH_HEAD
cd "$project"
[[ $(git rev-parse HEAD) == 3635e74826a4c1fcece7d1cd2b6fa75e43a00510 ]]
[[ $(lean --githash) == eb6cafb7290e8bd5f2937522d8d804f58f02bafc ]]
git apply "$here/zeta35.patch"
mkdir -p Zeta23/Compat .lake
cp "$here/LinearCombinationPrime.lean" Zeta23/Compat/
ln -s "$packages" .lake/packages
cp "$site/challenge/foundation/lake-manifest.json" lake-manifest.json
printf 'leanprover/lean4:v4.35.0\n' > lean-toolchain
sed -i 's/51e6992efd06126df61a496bebf8f49482a4e129/56a005855ea17e0b0958f73ec801ae140b0a1679/' lakefile.toml
python3 - <<'PY'
import pathlib, subprocess
modules = sorted("+" + ".".join(p.with_suffix("").parts) + ":olean" for p in pathlib.Path("Zeta23").rglob("*.lean"))
subprocess.run(["lake", "--no-ansi", "build", "+ChallengeDeps:olean", "+Zeta23:olean", *modules], check=True)
PY
