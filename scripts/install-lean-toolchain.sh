#!/usr/bin/env bash
set -euo pipefail

if command -v elan >/dev/null 2>&1; then
  elan_bin_dir="$(dirname "$(command -v elan)")"
  if [[ -n "${GITHUB_PATH:-}" ]]; then
    printf '%s\n' "$elan_bin_dir" >> "$GITHUB_PATH"
  fi
  elan --version
  exit 0
fi

if [[ "$(uname -s)" != "Linux" ]] || [[ "$(uname -m)" != "x86_64" ]]; then
  printf 'The pinned CI bootstrap currently supports Linux x86_64 only.\n' >&2
  exit 1
fi

archive_sha256="f81c2e48c1588d4612cd2c8851947898a45ac8d72748a07dff3a5694f1cf589b"
archive_url="https://github.com/leanprover/elan/releases/download/v4.1.2/elan-x86_64-unknown-linux-gnu.tar.gz"
bootstrap_dir="$(mktemp -d /tmp/riemann-elan.XXXXXX)"
trap 'rm -rf -- "$bootstrap_dir"' EXIT

curl --fail --location --silent --show-error --retry 3 \
  --output "$bootstrap_dir/elan.tar.gz" "$archive_url"
printf '%s  %s\n' "$archive_sha256" "$bootstrap_dir/elan.tar.gz" | sha256sum --check --status
tar -xzf "$bootstrap_dir/elan.tar.gz" -C "$bootstrap_dir"
"$bootstrap_dir/elan-init" -y --default-toolchain none --no-modify-path

user_home_dir="$(getent passwd "$(id -u)" | cut -d: -f6)"
elan_bin_dir="${ELAN_HOME:-$user_home_dir/.elan}/bin"
if [[ -n "${GITHUB_PATH:-}" ]]; then
  printf '%s\n' "$elan_bin_dir" >> "$GITHUB_PATH"
fi
"$elan_bin_dir/elan" --version
