#!/usr/bin/env bash
# Render exactly the same candidate data and trusted reference as the website's admission code.
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
site=$(cd "$here/../.." && pwd)
submission=$(realpath "${1:?submission directory}")
workspace=$(realpath -m "${2:?fresh prepared workspace}")
mkdir "$workspace"
mkdir -p "$workspace/comparator"
touch "$workspace/lakefile.toml"
cd "$site"
./node_modules/.bin/tsx scripts/prepare-candidate.ts "$submission" "$workspace"
