#!/usr/bin/env bash
# Offline score replay of a real, immutable accepted upload against its recorded incumbent.
set -euo pipefail
umask 022
site=$(cd "$(dirname "$0")/../.." && pwd)
root=/opt/riemann-qualification
sudo install -d -o "$(id -un)" -g "$(id -gn)" "$root"
cp -R "$site" "$root/site"
cd "$root/site"
source "$HOME/.nvm/nvm.sh" --no-use
nvm install 22
nvm use 22
npm ci --no-audit --no-fund
bash boat/compact/install-toolchain.sh "$root/lean"
bash boat/compact/install-runtime.sh "$root/runtime" "$root/site/challenge/compact-runtime.json"
record=knausgard-rh-reflected-kernel-8542
echo "57ee6e4def6c05145ce8196f49ce6302b211a24fa4feb091afbd732db93a12f3  submissions/$record/proof/Solution.lean" | sha256sum -c -
python3 - "$record" "$root/incumbent.json" <<'PY'
import json, pathlib, sys
entries = json.loads(pathlib.Path("data/records.json").read_text())
receipt = json.loads(pathlib.Path(f"submissions/{sys.argv[1]}/verification/attestation.json").read_text())
index = next(i for i, entry in enumerate(entries) if entry["id"] == receipt["previousRecordId"])
pathlib.Path(sys.argv[2]).write_text(json.dumps(entries[:index+1], indent=2, ensure_ascii=False) + "\n")
PY
export RIEMANN_RECORDS_PATH="$root/incumbent.json"
bash boat/compact/prepare-job.sh "submissions/$record" "$root/prepared"
sudo useradd --create-home --shell /usr/sbin/nologin proofcheck
sudo useradd --create-home --shell /usr/sbin/nologin referee
sudo chmod -R a+rX,go-w "$root"
sudo chown -R root:root "$root"
sudo bash boat/compact/run-job.sh "$root/prepared" "$root/runtime" "$root/lean" 28G "$root/export-receipt.json"
./node_modules/.bin/tsx boat/compact/seal-attestation.ts "$root/prepared/verification-artifacts/$record.prepared.json" \
  "$root/export-receipt.json" "$RIEMANN_RECORDS_PATH" "$HOME/canary-attestation.json"
