#!/usr/bin/env bash
# Build only trusted, pinned source in a fresh Linux workspace. No submitted source runs here.
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
site=$(cd "$here/../.." && pwd)
out=$(realpath -m "${1:?fresh output directory}")
mkdir "$out"
work=$(mktemp -d)
trap 'rm -rf -- "$work"' EXIT
cd "$work"
[[ $(lean --githash) == eb6cafb7290e8bd5f2937522d8d804f58f02bafc ]]
export LEAN_NUM_THREADS=2 LEAN_ABORT_ON_PANIC=1
fetch() {
  git init --quiet "$1"
  git -C "$1" remote add origin "$2"
  git -C "$1" fetch --quiet --depth=1 origin "$3"
  git -C "$1" checkout --quiet --detach FETCH_HEAD
  [[ $(git -C "$1" rev-parse HEAD) == "$3" ]]
}
if [[ -n ${RIEMANN_COMPACT_SOURCE:-} ]]; then
  compact=$(realpath "$RIEMANN_COMPACT_SOURCE")
  [[ $(git -C "$compact" rev-parse HEAD) == 72fead102f663d5c7a407964a13dc0cf9d977207 ]]
  test -s "$compact/.lake/build/lib/lean/Main.olean"
else
  fetch grh https://github.com/lsernau/grh-lean.git 72fead102f663d5c7a407964a13dc0cf9d977207
  compact="$work/grh/grh-compact"
  (cd "$compact" && python3 "$here/fetch-deps.py" && lake exe cache get && lake --no-ansi build +Main:olean)
fi
if [[ ${RIEMANN_EXTERNAL_ZETA:-0} == 1 ]]; then
  # Production installs the separately pinned Zeta23 library into deps/zeta.
  fetch zeta https://github.com/anthropics/formal-math.git 3635e74826a4c1fcece7d1cd2b6fa75e43a00510
  git -C zeta apply --check "$here/zeta35.patch"
else
  bash "$here/build-zeta.sh" "$work/zeta" "$compact/.lake/packages"
fi
mkdir -p "$out"/{interface,foundation,compat,deps,licenses,checker}
cp "$compact"/{LICENSE,NOTICE,ATTRIBUTION.md} "$out/licenses/"
cp zeta/NOTICE "$out/licenses/Zeta23-NOTICE"
# Preserve package search order. Keep compiled module data and interpreted tactic IR.
modules() {
  local from="$1" dest="$2"
  mkdir -p "$dest"
  (cd "$from" && find . -type f \( -name '*.olean' -o -name '*.olean.private' -o -name '*.olean.server' -o -name '*.ir' -o -name '*.ir.sig' -o -name '*.so' \) -print0 |
    tar -cf - --null -T -) | tar -xf - -C "$dest"
}
for pkg in Cli batteries Qq aesop proofwidgets importGraph LeanSearchClient plausible mathlib; do
  path="$compact/.lake/packages/$pkg/.lake/build/lib/lean"
  [[ ! -d "$path" ]] || modules "$path" "$out/deps/$pkg"
done
if [[ ${RIEMANN_EXTERNAL_ZETA:-0} != 1 ]]; then
  modules "$work/zeta/.lake/build/lib/lean" "$out/deps/zeta"
fi
modules "$compact/.lake/build/lib/lean" "$out/deps/compact"
prefix=$(lean --print-prefix)
export LEAN_PATH=$(find "$out/deps" -mindepth 1 -maxdepth 1 -type d | sort | paste -sd:):"$prefix/lib/lean"
(cd "$here" && lean -j1 -o "$out/foundation/Main.olean" Main.lean && lean -j1 -o "$out/compat/LegacyFinsetSyntax.olean" LegacyFinsetSyntax.lean)
(cd "$site/challenge/templates" && lean -j1 -o "$out/interface/Main.olean" Main.lean)
mkdir matcher
cp "$here/CompareOnly.lean" matcher/
cp "$here/matchrunner.toml" matcher/lakefile.toml
(cd matcher && lake build matchrunner)
cp matcher/.lake/build/bin/matchrunner "$out/checker/"
