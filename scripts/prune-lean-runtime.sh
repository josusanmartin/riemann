#!/usr/bin/env bash
set -euo pipefail

if [[ $# -ne 1 ]]; then
  printf 'Usage: prune-lean-runtime.sh <elan-toolchain-directory>\n' >&2
  exit 2
fi

toolchain_dir="$(cd -- "$1" && pwd -P)"
case "$toolchain_dir" in
  "$HOME/.elan/toolchains/"*) ;;
  *)
    printf 'Refusing to prune a directory outside the current user elan toolchains: %s\n' \
      "$toolchain_dir" >&2
    exit 2
    ;;
esac

for required_path in \
  "$toolchain_dir/bin/lean" \
  "$toolchain_dir/bin/lake" \
  "$toolchain_dir/bin/leantar" \
  "$toolchain_dir/lib/lean"; do
  if [[ ! -e "$required_path" ]]; then
    printf 'Pinned Lean toolchain is incomplete: %s\n' "$required_path" >&2
    exit 1
  fi
done

before_kib=$(du -sk "$toolchain_dir" | cut -f1)

# The production verifier elaborates Lean and replays exported proof objects;
# it never asks Lean to compile or link native code. Retain public/private
# oleans, Lean IR, and the shared runtime used by tactics, while dropping
# editor indexes, duplicate sources, static archives, and compiler/linker
# assets after every trusted executable has already been built.
find "$toolchain_dir/lib/lean" -type f \
  \( -name '*.ilean' -o -name '*.lean' \) \
  -delete
find "$toolchain_dir/lib" -type f -name '*.a' -delete
find "$toolchain_dir/lib" -maxdepth 1 \
  \( -type f -o -type l \) \
  \( -name 'libLLVM*' -o -name 'libclang-cpp*' \) \
  -delete
rm -rf \
  "$toolchain_dir/include" \
  "$toolchain_dir/src" \
  "$toolchain_dir/lib/clang"
rm -f \
  "$toolchain_dir/bin/clang" \
  "$toolchain_dir/bin/ld.lld" \
  "$toolchain_dir/bin/leanc" \
  "$toolchain_dir/bin/leanmake" \
  "$toolchain_dir/bin/llvm-ar"

"$toolchain_dir/bin/lean" --version
"$toolchain_dir/bin/lake" --version
after_kib=$(du -sk "$toolchain_dir" | cut -f1)
printf 'Pruned pinned Lean runtime from %s KiB to %s KiB.\n' \
  "$before_kib" "$after_kib"
