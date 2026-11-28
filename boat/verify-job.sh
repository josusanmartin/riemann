#!/usr/bin/env bash
# One fresh, account-isolated Boat VM. Only the pinned verifier runs submitted Lean.
set -euo pipefail
umask 022
site="$(cd "$(dirname "$0")/.." && pwd)"
root=/opt/riemann-boat
inbox="$HOME/riemann-incoming"
receipt="$HOME/riemann-receipt.json"
digest="${1:?proof digest}"
kind="${2:?job kind}"
memory_limit="${3:-12G}"
[[ "$memory_limit" == 12G || "$memory_limit" == 28G ]]
[[ "$digest" =~ ^[0-9a-f]{64}$ && "$kind" =~ ^(competitive|flow|qualification)$ ]]
# This submitter-visible journal records only fixed phase names, UTC times,
# and numeric exit statuses. Bootstrap command output stays with the operator.
stage_file="$HOME/riemann-stages.tsv"
(umask 077; : > "$stage_file") || true
stage=workspace
stage_event() {
  printf '%s\t%s\t%s\n' "$(date -u +%FT%TZ)" "$stage" "$1" >> "$stage_file" || true
}
enter_stage() {
  stage="$1"
  stage_event start
}
trap 'stage_event "exit=$?"' EXIT
enter_stage workspace
sudo install -d -o "$(id -un)" -g "$(id -gn)" "$root"
cp -R "$site" "$root/site"
cd "$root/site"
exec > "$HOME/riemann-bootstrap.log" 2>&1
umask 077
export LEAN_NUM_THREADS=2
enter_stage lean-toolchain
bash boat/compact/install-toolchain.sh "$root/lean"
enter_stage foundation
bash boat/compact/install-runtime.sh "$root/runtime" "$root/site/challenge/compact-runtime.json"
enter_stage node-dependencies
source "$HOME/.nvm/nvm.sh" --no-use
nvm install 22
nvm use 22
npm ci --no-audit --no-fund
enter_stage prepare-worker
sudo useradd --create-home --shell /usr/sbin/nologin proofcheck
sudo useradd --create-home --shell /usr/sbin/nologin referee
# File content is data; no submission text appears in shell commands or Boat history.
mkdir -p "$root/input/proof"
enter_stage check-upload
staged=false
for _ in $(seq 1 90); do
  if [[ -f "$inbox/ready" ]] && cp "$inbox/manifest" "$root/input/submission.json" && cp "$inbox/solution" "$root/input/proof/Solution.lean"; then
    actual="$({ printf 'submission.json\0'; cat "$root/input/submission.json"; printf 'proof/Solution.lean\0'; cat "$root/input/proof/Solution.lean"; } | sha256sum | cut -d' ' -f1)"
    if [[ "$actual" == "$digest" ]]; then staged=true; break; fi
  fi
  sleep 2
done
[[ "$staged" == true ]]
if [[ "$kind" == qualification ]]; then
  python3 boat/compact/records-at-admission.py knausgard-rh-reflected-kernel-8542 "$root/input/trusted-records.json"
elif [[ "$kind" == flow ]]; then
  cp challenge/flow-test-records.json "$root/input/trusted-records.json"
else
  ./node_modules/.bin/tsx -e 'import {records} from "./src/lib/records";process.stdout.write(JSON.stringify(records,null,2)+"\n")' > "$root/input/trusted-records.json"
fi
enter_stage isolate-proof
export RIEMANN_RECORDS_PATH="$root/input/trusted-records.json"
bash boat/compact/prepare-job.sh "$root/input" "$root/prepared"
id=$(node -p "require('$root/input/submission.json').id")
[[ $id =~ ^[a-z0-9][a-z0-9-]{0,79}$ ]]
sudo chown -R root:root "$root"
sudo chmod -R a+rX,go-w "$root"
sudo chmod 0700 "$HOME"
enter_stage check-proof
status=0
verification_seconds=$(python3 -c 'import json; print(json.load(open("boat/compact/time-limits.json"))["verificationSeconds"])')
sudo timeout -k 15s "${verification_seconds}s" bash boat/compact/run-job.sh "$root/prepared" "$root/runtime" "$root/lean" \
  "$memory_limit" "$root/kernel-receipt.json" > "$HOME/riemann-proof.log" 2>&1 || status=$?
stage_event "exit=$status"
enter_stage seal-receipt
if (( status == 0 )); then
  ./node_modules/.bin/tsx boat/compact/seal-attestation.ts "$root/prepared/verification-artifacts/$id.prepared.json" \
    "$root/kernel-receipt.json" "$RIEMANN_RECORDS_PATH" "$HOME/compact-attestation.json"
fi
kernel_oom=0
if sudo test -f "$root/kernel-receipt.json.oom"; then kernel_oom=1; fi
RIEMANN_KERNEL_OOM="$kernel_oom" ./node_modules/.bin/tsx scripts/finalize-e2b-job.ts "$root/input" \
  "$HOME/compact-attestation.json" "$HOME/riemann-proof.log" "$receipt" "$digest" "$status"

# Only the supervisor can read this job-specific wake-up token. A notification
# never supplies a verdict. The website fetches the receipt using its own key.
if [[ "$kind" == competitive && -f "$inbox/notification" ]]; then
  python3 - "$inbox/notification" "$digest" <<'PY' || true
import json, re, sys, time, urllib.request
with open(sys.argv[1]) as file:
    notice = json.load(file)
if not re.fullmatch(r'[0-9a-f-]{36}', notice["jobId"]) or not re.fullmatch(r'[0-9a-f]{64}', notice["token"]):
    raise ValueError("Invalid notification coordinates")
class NoRedirect(urllib.request.HTTPRedirectHandler):
    def redirect_request(self, *args, **kwargs):
        return None
opener = urllib.request.build_opener(NoRedirect())
request = urllib.request.Request("https://www.riemannzeta.fun/api/submissions/boat/complete", method="POST",
    headers={"X-Riemann-Job":notice["jobId"], "X-Riemann-Digest":sys.argv[2], "X-Riemann-Notification":notice["token"]})
for delay in (0, 5, 20):
    time.sleep(delay)
    try:
        with opener.open(request, timeout=45) as response:
            if response.status == 204: break
    except OSError:
        continue
PY
fi
