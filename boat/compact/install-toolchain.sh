#!/usr/bin/env bash
set -euo pipefail
destination=${1:?fresh Lean installation directory}
[[ $(uname -ms) == 'Linux x86_64' ]]
archive=$(mktemp)
trap 'rm -f -- "$archive"' EXIT
curl --fail --silent --show-error --location --retry 3 \
  https://github.com/leanprover/lean4/releases/download/v4.35.0/lean-4.35.0-linux.tar.zst -o "$archive"
echo "7289597a44543246c9227b8cae501767e095ce17f6d448b95fc4a8dc97268f6d  $archive" | sha256sum -c -
mkdir "$destination"
tar --zstd -xf "$archive" --strip-components=1 -C "$destination"
[[ $("$destination/bin/lean" --githash) == eb6cafb7290e8bd5f2937522d8d804f58f02bafc ]]
python3 "$(dirname "$0")/nanoda.py" install "$destination"
