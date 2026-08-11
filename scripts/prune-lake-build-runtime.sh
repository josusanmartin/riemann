#!/usr/bin/env bash
set -euo pipefail

if [[ $# -ne 2 ]]; then
  printf 'Usage: prune-lake-build-runtime.sh <lake-workspace> <module-prefix>\n' >&2
  exit 2
fi

workspace="$(cd -- "$1" && pwd -P)"
module_prefix="$2"
if [[ ! "$module_prefix" =~ ^[A-Z][A-Za-z0-9_]*(\.[A-Z][A-Za-z0-9_]*)*$ ]]; then
  printf 'Invalid trusted module prefix: %s\n' "$module_prefix" >&2
  exit 2
fi
for required_path in \
  "$workspace/.git" \
  "$workspace/lean-toolchain" \
  "$workspace/.lake/build/lib/lean" \
  "$workspace/.lake/build/ir"; do
  if [[ ! -e "$required_path" ]]; then
    printf 'Pinned Lake workspace is incomplete: %s\n' "$required_path" >&2
    exit 1
  fi
done

module_path="${module_prefix//./\/}"
lib_root="$workspace/.lake/build/lib/lean"
ir_root="$workspace/.lake/build/ir"
module_lib_dir="$lib_root/$module_path"
module_ir_dir="$ir_root/$module_path"
if [[ ! -f "$module_lib_dir/Unconditional.olean" ]]; then
  printf 'Trusted Zeta runtime witness is missing: %s\n' \
    "$module_lib_dir/Unconditional.olean" >&2
  exit 1
fi

before_kib=$(du -sk "$workspace/.lake/build" | cut -f1)
mapfile -d '' editor_outputs < <(
  find "$module_lib_dir" -type f -name '*.ilean' -print0
  if [[ -f "$lib_root/$module_path.ilean" ]]; then
    printf '%s\0' "$lib_root/$module_path.ilean"
  fi
)
mapfile -d '' native_outputs < <(
  find "$module_ir_dir" -type f -name '*.c' -print0
  if [[ -f "$ir_root/$module_path.c" ]]; then
    printf '%s\0' "$ir_root/$module_path.c"
  fi
)
if [[ "${#editor_outputs[@]}" -eq 0 || "${#native_outputs[@]}" -eq 0 ]]; then
  printf 'Expected Lake editor/native outputs were not produced for %s.\n' \
    "$module_prefix" >&2
  exit 1
fi

# Keep the paths and their trusted `.hash` files so Lake recognizes each module
# job as complete, but discard payloads the verifier never reads. `lean` imports
# oleans and interpreter IR; it does not consume these editor indexes or C files.
for output in "${editor_outputs[@]}" "${native_outputs[@]}"; do
  hash_path="$output.hash"
  if [[ ! -f "$hash_path" ]]; then
    printf 'Trusted Lake output hash is missing: %s\n' "$hash_path" >&2
    exit 1
  fi
  truncate -s 0 -- "$output"
  touch -- "$hash_path"
done

after_kib=$(du -sk "$workspace/.lake/build" | cut -f1)
printf 'Replaced %d editor and %d native outputs for %s; %s KiB -> %s KiB.\n' \
  "${#editor_outputs[@]}" "${#native_outputs[@]}" "$module_prefix" \
  "$before_kib" "$after_kib"
