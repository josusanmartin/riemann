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
[[ "$digest" =~ ^[0-9a-f]{64}$ && "$kind" =~ ^(competitive|flow)$ ]]
sudo install -d -o "$(id -un)" -g "$(id -gn)" "$root"
cp -R "$site" "$root/site"
cd "$root/site"
exec > "$HOME/riemann-bootstrap.log" 2>&1
umask 077
export LEAN_NUM_THREADS=2
bash scripts/install-lean-toolchain.sh
export PATH="$HOME/.elan/bin:$PATH"
upstream="$(node -p "require('./challenge/contract.json').trustedUpstream.commit")"
git init -q "$root/zeta"
git -C "$root/zeta" fetch -q --depth=1 https://github.com/anthropics/formal-math.git "$upstream"
git -C "$root/zeta" checkout -q --detach FETCH_HEAD
(cd "$root/zeta" && lean --version)
(
  bash scripts/install-native-build-toolchains.sh
  export CARGO_HOME="$HOME/.riemann-build-toolchains/cargo" RUSTUP_HOME="$HOME/.riemann-build-toolchains/rustup"
  export PATH="$HOME/.riemann-build-toolchains/go/bin:$CARGO_HOME/bin:$PATH"
  bash scripts/install-verifier-tools.sh "$root/tools"
) > "$HOME/riemann-tools.log" 2>&1 &
tools_pid=$!
(
  cd "$root/zeta"
  python3 - <<'PY'
import concurrent.futures, pathlib, subprocess, json
def checkout(p):
    path=pathlib.Path('.lake/packages')/p['name'];path.mkdir(parents=True,exist_ok=True)
    for args in [['init','-q'],['remote','add','origin',p['url']],['fetch','-q','--depth=1','origin',p['rev']],['checkout','-q','--detach','FETCH_HEAD']]:
        subprocess.run(['git','-C',str(path),*args],check=True)
with concurrent.futures.ThreadPoolExecutor(4) as pool:
    list(pool.map(checkout,json.load(open('lake-manifest.json'))['packages']))
PY
  lake exe cache get
  lake build +Zeta23.Unconditional:olean +Zeta23.ThmD.Mult:olean
) > "$HOME/riemann-zeta.log" 2>&1 &
zeta_pid=$!
source "$HOME/.nvm/nvm.sh" --no-use
nvm install 22
nvm use 22
npm ci --no-audit --no-fund
wait "$tools_pid"
wait "$zeta_pid"
prefix="$(cd "$root/zeta" && lean --print-prefix)"
mkdir -p "$root/bin"
cp -a "$prefix" "$root/lean"
install -m 0755 "$(command -v node)" "$root/bin/node"
# NSS may try a socket while Bash starts. Return EPERM for denied network
# syscalls so the shell can fall back. Both network-denial probes still run.
cat > "$root/bin/systemd-run" <<'WRAPPER'
#!/bin/sh
exec /usr/bin/systemd-run --property=SystemCallErrorNumber=EPERM "$@"
WRAPPER
chmod 0755 "$root/bin/systemd-run"
export PATH="$root/bin:$root/lean/bin:/usr/local/bin:/usr/bin:/bin"
sudo useradd --create-home --shell /usr/sbin/nologin proofcheck
# File content is data; no submission text appears in shell commands or Boat history.
mkdir -p "$root/input/proof"
staged=false
for _ in $(seq 1 90); do
  if [[ -f "$inbox/ready" ]] && cp "$inbox/manifest" "$root/input/submission.json" && cp "$inbox/solution" "$root/input/proof/Solution.lean"; then
    actual="$({ printf 'submission.json\0'; cat "$root/input/submission.json"; printf 'proof/Solution.lean\0'; cat "$root/input/proof/Solution.lean"; } | sha256sum | cut -d' ' -f1)"
    if [[ "$actual" == "$digest" ]]; then staged=true; break; fi
  fi
  sleep 2
done
[[ "$staged" == true ]]
if [[ "$kind" == flow ]]; then
  cp challenge/flow-test-records.json "$root/input/trusted-records.json"
else
  ./node_modules/.bin/tsx -e 'import {records} from "./src/lib/records";process.stdout.write(JSON.stringify(records,null,2)+"\n")' > "$root/input/trusted-records.json"
fi
# Keep the source, toolchain, and verifier immutable to the isolated proof account.
sudo chown -R root:root "$root"
sudo chmod -R a+rX,go-w "$root"
sudo chmod 0700 "$HOME"
sudo git config --system --add safe.directory "$root/zeta"
find "$root/zeta/.lake/packages" -mindepth 2 -maxdepth 2 -name .git -type d -printf '%h\n' | while read -r repo; do sudo git config --system --add safe.directory "$repo"; done
sudo loginctl enable-linger proofcheck
uid="$(id -u proofcheck)"
sudo systemctl start "user@$uid.service"
set +e
sudo -u proofcheck env -i HOME=/home/proofcheck XDG_RUNTIME_DIR="/run/user/$uid" DBUS_SESSION_BUS_ADDRESS="unix:path=/run/user/$uid/bus" \
  PATH="$PATH" LEAN_NUM_THREADS=2 RIEMANN_PREBUILT_ZETA23="$root/zeta" RIEMANN_RECORDS_PATH="$root/input/trusted-records.json" \
  COMPARATOR_BIN="$root/tools/comparator/.lake/build/bin/comparator" COMPARATOR_LANDRUN="$root/tools/landrun/landrun" \
  COMPARATOR_LEAN4EXPORT="$root/tools/comparator/.lake/packages/lean4export/.lake/build/bin/lean4export" COMPARATOR_NANODA="$root/tools/nanoda/target/release/nanoda_bin" \
  timeout -k 15s 5800s ./node_modules/.bin/tsx scripts/verify-submission.ts "$root/input" --mode=full --artifact=/home/proofcheck/attestation.json \
  > "$HOME/riemann-proof.log" 2>&1
status=$?
set -e
# Stop the proof account and its remaining processes before reading its artifact.
sudo loginctl terminate-user proofcheck || true
sudo pkill -KILL -u proofcheck 2>/dev/null || true
if [[ $status == 0 ]]; then
  sudo test -f /home/proofcheck/attestation.json
  sudo test ! -L /home/proofcheck/attestation.json
  sudo install -m 0644 /home/proofcheck/attestation.json "$root/attestation.json"
fi
./node_modules/.bin/tsx scripts/finalize-e2b-job.ts "$root/input" "$root/attestation.json" "$HOME/riemann-proof.log" "$receipt" "$digest" "$status"

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
