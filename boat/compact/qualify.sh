#!/usr/bin/env bash
# Recreate the standard Boat inbox using an archived, digest-checked submission.
set -euo pipefail
site=$(cd "$(dirname "$0")/../.." && pwd)
cd "$site"
record=knausgard-rh-reflected-kernel-8542
file="submissions/$record/proof/Solution.lean"
echo "57ee6e4def6c05145ce8196f49ce6302b211a24fa4feb091afbd732db93a12f3  $file" | sha256sum -c -
inbox="$HOME/riemann-incoming"
install -d -m 700 "$inbox"
cp "submissions/$record/submission.json" "$inbox/manifest"
cp "$file" "$inbox/solution"
digest=$({ printf 'submission.json\0'; cat "$inbox/manifest"; printf 'proof/Solution.lean\0'; cat "$inbox/solution"; } | sha256sum | cut -d' ' -f1)
printf '%s\n' "$digest" > "$inbox/ready"
bash boat/verify-job.sh "$digest" qualification 12G
python3 - "$HOME/riemann-receipt.json" "$HOME/canary-attestation.json" "$digest" <<'PY'
import json
from pathlib import Path
import sys
receipt = json.loads(Path(sys.argv[1]).read_text())
if receipt["status"] != "verified" or receipt["proofDigest"] != sys.argv[3]:
    raise ValueError("Production verifier did not issue a verified receipt for the archived upload")
Path(sys.argv[2]).write_text(json.dumps(receipt["attestation"], indent=2) + "\n")
PY
