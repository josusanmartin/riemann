#!/usr/bin/env bash
set -euo pipefail

if [[ $# -ne 1 ]]; then
  printf 'Usage: smoke-verifier.sh <installed-tools-directory>\n' >&2
  exit 2
fi

repository_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
tools_dir="$(realpath "$1")"
comparator_bin="$tools_dir/comparator/.lake/build/bin/comparator"
landrun_bin="$tools_dir/landrun/landrun"
lean4export_bin="$tools_dir/comparator/.lake/packages/lean4export/.lake/build/bin/lean4export"
nanoda_bin="$tools_dir/nanoda/target/release/nanoda_bin"

for required_bin in "$comparator_bin" "$landrun_bin" "$lean4export_bin" "$nanoda_bin"; do
  if [[ ! -x "$required_bin" ]]; then
    printf 'Missing verifier binary: %s\n' "$required_bin" >&2
    exit 1
  fi
done

smoke_workspace="$(mktemp -d /tmp/riemann-verifier-smoke.XXXXXX)"
trap 'rm -rf -- "$smoke_workspace"' EXIT
cp -R "$repository_root/challenge/smoke/." "$smoke_workspace/"

systemd-run \
  --property=RestrictAddressFamilies=~AF_UNIX \
  --property=SystemCallFilter=~@network-io \
  --property=PrivateNetwork=yes \
  --property=MemoryMax=2G \
  --property=TasksMax=128 \
  --property=RuntimeMaxSec=600 \
  --property=LimitFSIZE=1073741824 \
  --property=NoNewPrivileges=yes \
  --user \
  --pipe \
  --wait \
  --working-directory="$smoke_workspace" \
  --setenv=PATH="${PATH:-}" \
  --setenv=COMPARATOR_LANDRUN="$landrun_bin" \
  --setenv=COMPARATOR_LEAN4EXPORT="$lean4export_bin" \
  --setenv=COMPARATOR_NANODA="$nanoda_bin" \
  -- \
  bash "$repository_root/scripts/run-comparator-sandbox.sh" \
  "$comparator_bin" config.json
