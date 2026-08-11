#!/usr/bin/env bash
set -euo pipefail

if [[ $# -ne 1 ]]; then
  echo "Usage: install-verifier-tools.sh <empty-tools-directory>" >&2
  exit 2
fi

tools_dir="$1"
if [[ -e "$tools_dir" ]] && [[ -n "$(find "$tools_dir" -mindepth 1 -maxdepth 1 -print -quit)" ]]; then
  echo "Tools directory must be empty: $tools_dir" >&2
  exit 2
fi
mkdir -p "$tools_dir"

script_dir="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
contract_path="$script_dir/../challenge/contract.json"
mapfile -t verifier_config < <(
  node -e '
    const fs = require("node:fs");
    const contract = JSON.parse(fs.readFileSync(process.argv[1], "utf8"));
    console.log(contract.verifier.comparatorCommit);
    console.log(contract.verifier.landrunCommit);
    console.log(contract.verifier.nanodaCommit);
    console.log(contract.verifier.lean4exportCommit);
    console.log(contract.trustedUpstream.leanToolchain);
  ' "$contract_path"
)
if [[ "${#verifier_config[@]}" -ne 5 ]]; then
  echo "Unable to read verifier pins from $contract_path" >&2
  exit 1
fi
comparator_commit="${verifier_config[0]}"
landrun_commit="${verifier_config[1]}"
nanoda_commit="${verifier_config[2]}"
lean4export_commit="${verifier_config[3]}"
lean_toolchain="${verifier_config[4]}"

assert_commit() {
  local repository="$1"
  local expected="$2"
  local actual
  actual="$(git -C "$repository" rev-parse HEAD)"
  if [[ "$actual" != "$expected" ]]; then
    printf 'Pinned checkout mismatch in %s: expected %s, got %s\n' "$repository" "$expected" "$actual" >&2
    exit 1
  fi
}

clone_with_retry() {
  local repository="$1"
  local destination="$2"
  local attempt
  for attempt in 1 2 3; do
    if git clone --quiet "$repository" "$destination"; then
      return 0
    fi
    rm -rf -- "$destination"
    if [[ "$attempt" -lt 3 ]]; then
      printf 'Clone failed; retrying %s (%d/3)\n' "$repository" "$((attempt + 1))" >&2
      sleep "$((attempt * 5))"
    fi
  done
  printf 'Unable to clone %s after three attempts\n' "$repository" >&2
  return 1
}

clone_with_retry https://github.com/leanprover/comparator.git "$tools_dir/comparator"
git -C "$tools_dir/comparator" checkout --quiet --detach "$comparator_commit"
assert_commit "$tools_dir/comparator" "$comparator_commit"
(
  cd "$tools_dir/comparator"
  elan override set "$lean_toolchain"
  lake build comparator lean4export
)
assert_commit "$tools_dir/comparator/.lake/packages/lean4export" "$lean4export_commit"

clone_with_retry https://github.com/Zouuup/landrun.git "$tools_dir/landrun"
git -C "$tools_dir/landrun" checkout --quiet --detach "$landrun_commit"
assert_commit "$tools_dir/landrun" "$landrun_commit"
(
  cd "$tools_dir/landrun"
  go build -trimpath -o landrun ./cmd/landrun
)

clone_with_retry https://github.com/ammkrn/nanoda_lib.git "$tools_dir/nanoda"
git -C "$tools_dir/nanoda" checkout --quiet --detach "$nanoda_commit"
assert_commit "$tools_dir/nanoda" "$nanoda_commit"
cargo build --quiet --release --manifest-path "$tools_dir/nanoda/Cargo.toml"

printf '%s\n' "Verifier tools installed in $tools_dir"
