#!/usr/bin/env bash
set -euo pipefail

real_lean=$(/home/riemann/.elan/bin/elan which lean)
real_lake="$(dirname -- "$real_lean")/lake"
if [[ ! -x "$real_lake" ]]; then
  printf 'The pinned Lake runtime is unavailable.\n' >&2
  exit 1
fi

if [[ "${1:-}" == "build" ]]; then
  exec /opt/riemann/scripts/run-lake-build-bounded-disk.sh \
    "$PWD" "$real_lake" "$@"
fi
exec "$real_lake" "$@"
