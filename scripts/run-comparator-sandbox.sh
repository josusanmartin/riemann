#!/usr/bin/env bash
set -euo pipefail

if [[ $# -ne 2 ]]; then
  printf 'Usage: run-comparator-sandbox.sh <comparator-binary> <config-path>\n' >&2
  exit 2
fi
: "${COMPARATOR_LANDRUN:?COMPARATOR_LANDRUN is required}"
if [[ ! -x "$COMPARATOR_LANDRUN" ]]; then
  printf 'COMPARATOR_LANDRUN is not executable: %s\n' "$COMPARATOR_LANDRUN" >&2
  exit 2
fi
if ! command -v python3 >/dev/null 2>&1; then
  printf 'Refusing to run: python3 is required for the network isolation probe.\n' >&2
  exit 96
fi

set +e
python3 -c 'import socket; socket.socket(socket.AF_INET, socket.SOCK_STREAM)' \
  >/dev/null 2>&1
inet_probe_status=$?
python3 -c 'import socket; socket.socketpair()' >/dev/null 2>&1
unix_probe_status=$?
set -e
if [[ "$inet_probe_status" -eq 0 ]] || [[ "$unix_probe_status" -eq 0 ]]; then
  printf 'Refusing to run: the outer network syscall filter is not active.\n' >&2
  exit 97
fi

landrun_probe_dir="$(mktemp -d /tmp/riemann-landrun-probe.XXXXXX)"
landrun_probe_file="$landrun_probe_dir/probe"
trap 'rm -rf -- "$landrun_probe_dir"' EXIT
set +e
"$COMPARATOR_LANDRUN" \
  --best-effort \
  --ro / \
  --rw /dev \
  --ldd \
  --add-exec \
  -- \
  /usr/bin/touch "$landrun_probe_file" \
  >/dev/null 2>&1
filesystem_probe_status=$?
set -e
if [[ -e "$landrun_probe_file" ]] || [[ "$filesystem_probe_status" -eq 0 ]]; then
  printf 'Refusing to run: Landlock filesystem restrictions are unavailable.\n' >&2
  exit 98
fi

rm -rf -- "$landrun_probe_dir"
trap - EXIT

exec lake env "$1" "$2"
