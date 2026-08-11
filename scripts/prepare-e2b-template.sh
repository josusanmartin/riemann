#!/usr/bin/env bash
set -euo pipefail

repository_root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
contract_path="$repository_root/challenge/contract.json"
zeta_dir="$repository_root/zeta23"
tools_dir="$repository_root/tools"
mathlib_cache_dir="/tmp/riemann-mathlib-cache"

mapfile -t trusted_upstream < <(
  node -e '
    const fs = require("node:fs");
    const contract = JSON.parse(fs.readFileSync(process.argv[1], "utf8"));
    console.log(contract.trustedUpstream.repository);
    console.log(contract.trustedUpstream.commit);
    console.log(contract.trustedUpstream.leanToolchain);
    console.log(contract.trustedUpstream.mathlibCommit);
  ' "$contract_path"
)
if [[ "${#trusted_upstream[@]}" -ne 4 ]]; then
  printf 'Unable to read the trusted upstream pins.\n' >&2
  exit 1
fi

upstream_repository="${trusted_upstream[0]}"
upstream_commit="${trusted_upstream[1]}"
lean_toolchain="${trusted_upstream[2]}"
mathlib_commit="${trusted_upstream[3]}"

"$repository_root/scripts/install-lean-toolchain.sh"
export PATH="$HOME/.elan/bin:$PATH"
elan toolchain install "$lean_toolchain"

git clone --quiet --filter=blob:none --no-checkout \
  "https://github.com/$upstream_repository.git" "$zeta_dir"
git -C "$zeta_dir" checkout --quiet --detach "$upstream_commit"
if [[ "$(git -C "$zeta_dir" rev-parse HEAD)" != "$upstream_commit" ]]; then
  printf 'Pinned Zeta23 checkout verification failed.\n' >&2
  exit 1
fi
if [[ "$(tr -d '\r\n' < "$zeta_dir/lean-toolchain")" != "$lean_toolchain" ]]; then
  printf 'Pinned Lean toolchain verification failed.\n' >&2
  exit 1
fi
actual_mathlib="$({
  node -e '
    const fs = require("node:fs");
    const manifest = JSON.parse(fs.readFileSync(process.argv[1], "utf8"));
    process.stdout.write(manifest.packages.find((item) => item.name === "mathlib")?.rev ?? "");
  ' "$zeta_dir/lake-manifest.json"
})"
if [[ "$actual_mathlib" != "$mathlib_commit" ]]; then
  printf 'Pinned Mathlib checkout verification failed.\n' >&2
  exit 1
fi

(
  cd "$zeta_dir"
  MATHLIB_CACHE_DIR="$mathlib_cache_dir" lake exe cache get
  MATHLIB_CACHE_DIR="$mathlib_cache_dir" lake exe cache clean!
)
"$repository_root/scripts/install-verifier-tools.sh" "$tools_dir"

runtime_tools_dir="$tools_dir/bin"
mkdir -p "$runtime_tools_dir"
install -m 0755 "$tools_dir/comparator/.lake/build/bin/comparator" \
  "$runtime_tools_dir/comparator"
install -m 0755 \
  "$tools_dir/comparator/.lake/packages/lean4export/.lake/build/bin/lean4export" \
  "$runtime_tools_dir/lean4export"
install -m 0755 "$tools_dir/landrun/landrun" "$runtime_tools_dir/landrun"
install -m 0755 "$tools_dir/nanoda/target/release/nanoda_bin" \
  "$runtime_tools_dir/nanoda_bin"
rm -rf "$tools_dir/comparator" "$tools_dir/landrun" "$tools_dir/nanoda"

printf 'Pinned E2B verifier assets prepared.\n'
