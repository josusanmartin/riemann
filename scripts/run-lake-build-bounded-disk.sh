#!/usr/bin/env bash
set -euo pipefail

if [[ $# -lt 3 ]]; then
  printf 'Usage: run-lake-build-bounded-disk.sh <workspace> <real-lake> <lake-arguments...>\n' >&2
  exit 2
fi

workspace="$(cd -- "$1" && pwd -P)"
real_lake="$2"
shift 2

if [[ ! -x "$real_lake" ]] || [[ ! -f "$workspace/lakefile.toml" ]]; then
  printf 'The bounded Lake build received an invalid workspace or Lake binary.\n' >&2
  exit 2
fi

setup_root="$workspace/.lake/build/ir"
olean_root="$workspace/.lake/build/lib/lean"
grace_seconds="${RIEMANN_SETUP_PRUNE_GRACE_SECONDS:-5}"
if [[ ! "$grace_seconds" =~ ^[0-9]{1,3}$ ]]; then
  printf 'RIEMANN_SETUP_PRUNE_GRACE_SECONDS must be an integer.\n' >&2
  exit 2
fi

prune_completed_setup_files() {
  local now relative module_path olean_path modified setup_path
  now=$(date +%s)
  [[ -d "$setup_root" ]] || return 0
  while IFS= read -r -d '' setup_path; do
    relative="${setup_path#"$setup_root"/}"
    module_path="${relative%.setup.json}"
    olean_path="$olean_root/$module_path.olean"
    [[ -s "$olean_path" ]] || continue
    modified=$(stat -c %Y -- "$setup_path" 2>/dev/null) || continue
    if (( now - modified >= grace_seconds )); then
      rm -f -- "$setup_path"
    fi
  done < <(find "$setup_root" -type f -name '*.setup.json' -print0)
}

(
  cd "$workspace"
  "$real_lake" "$@"
) &
lake_pid=$!
while kill -0 "$lake_pid" 2>/dev/null; do
  prune_completed_setup_files
  sleep 1
done

lake_status=0
wait "$lake_pid" || lake_status=$?
if [[ "$lake_status" -eq 0 && -d "$setup_root" ]]; then
  find "$setup_root" -type f -name '*.setup.json' -delete
fi
exit "$lake_status"
