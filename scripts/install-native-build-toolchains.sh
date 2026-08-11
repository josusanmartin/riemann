#!/usr/bin/env bash
set -euo pipefail

if [[ "$(uname -s)" != "Linux" ]] || [[ "$(uname -m)" != "x86_64" ]]; then
  printf 'The pinned native build toolchains currently support Linux x86_64 only.\n' >&2
  exit 1
fi

toolchains_dir="${RIEMANN_BUILD_TOOLCHAINS_DIR:-$HOME/.riemann-build-toolchains}"
if [[ "$toolchains_dir" != "$HOME/"* ]]; then
  printf 'Build toolchains must be installed below the current user home.\n' >&2
  exit 1
fi
if [[ -e "$toolchains_dir" ]] && \
  [[ -n "$(find "$toolchains_dir" -mindepth 1 -maxdepth 1 -print -quit)" ]]; then
  printf 'Build toolchains directory must be empty: %s\n' "$toolchains_dir" >&2
  exit 1
fi

go_version="1.26.5"
go_archive_sha256="5c2c3b16caefa1d968a94c1daca04a7ca301a496d9b086e17ad77bb81393f053"
rust_toolchain="1.97.1"
rustup_version="1.28.2"
rustup_sha256="20a06e644b0d9bd2fbdbfd52d42540bdde820ea7df86e92e533c073da0cdd43c"

bootstrap_dir="$(mktemp -d /tmp/riemann-native-toolchains.XXXXXX)"
trap 'rm -rf -- "$bootstrap_dir"' EXIT
mkdir -p "$toolchains_dir"

go_archive="$bootstrap_dir/go${go_version}.linux-amd64.tar.gz"
curl --proto '=https' --tlsv1.2 --fail --location --silent --show-error \
  --retry 3 --output "$go_archive" \
  "https://go.dev/dl/go${go_version}.linux-amd64.tar.gz"
printf '%s  %s\n' "$go_archive_sha256" "$go_archive" | \
  sha256sum --check --status
tar -xzf "$go_archive" -C "$toolchains_dir"

rustup_init="$bootstrap_dir/rustup-init"
curl --proto '=https' --tlsv1.2 --fail --location --silent --show-error \
  --retry 3 --output "$rustup_init" \
  "https://static.rust-lang.org/rustup/archive/$rustup_version/x86_64-unknown-linux-gnu/rustup-init"
printf '%s  %s\n' "$rustup_sha256" "$rustup_init" | \
  sha256sum --check --status
chmod 0755 "$rustup_init"

export CARGO_HOME="$toolchains_dir/cargo"
export RUSTUP_HOME="$toolchains_dir/rustup"
"$rustup_init" -y --no-modify-path --profile minimal \
  --default-host x86_64-unknown-linux-gnu \
  --default-toolchain "$rust_toolchain"

if [[ "$("$toolchains_dir/go/bin/go" env GOVERSION)" != "go$go_version" ]]; then
  printf 'Pinned Go toolchain verification failed.\n' >&2
  exit 1
fi
if [[ "$("$CARGO_HOME/bin/rustc" --version | cut -d' ' -f2)" != "$rust_toolchain" ]]; then
  printf 'Pinned Rust toolchain verification failed.\n' >&2
  exit 1
fi

if [[ -n "${GITHUB_PATH:-}" ]]; then
  printf '%s\n' "$toolchains_dir/go/bin" "$CARGO_HOME/bin" >> "$GITHUB_PATH"
fi
if [[ -n "${GITHUB_ENV:-}" ]]; then
  printf 'CARGO_HOME=%s\n' "$CARGO_HOME" >> "$GITHUB_ENV"
  printf 'RUSTUP_HOME=%s\n' "$RUSTUP_HOME" >> "$GITHUB_ENV"
  printf 'GOPATH=%s\n' "$toolchains_dir/gopath" >> "$GITHUB_ENV"
  printf 'GOCACHE=%s\n' "$toolchains_dir/go-cache" >> "$GITHUB_ENV"
fi

"$toolchains_dir/go/bin/go" version
"$CARGO_HOME/bin/cargo" --version
