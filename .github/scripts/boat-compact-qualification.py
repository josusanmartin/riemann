"""Run one archived-source qualification in a disposable Boat worker, without a leaderboard write."""
import json
import os
from pathlib import Path
import re
import time
import urllib.error
import urllib.request

base = "https://boat.dev/api/v1"
revision = os.environ["GITHUB_SHA"]
if not re.fullmatch(r"[a-f0-9]{40}", revision):
    raise ValueError("Invalid verifier revision")
token = os.environ["BOAT_TEST_KEY"]

def api(path, method="GET", data=None, idempotency=None):
    headers = {"Authorization": "Bearer " + token, "Content-Type": "application/json"}
    if idempotency:
        headers["Idempotency-Key"] = idempotency
    request = urllib.request.Request(base + path, method=method, headers=headers,
                                     data=None if data is None else json.dumps(data).encode())
    for attempt in range(4):
        try:
            with urllib.request.urlopen(request, timeout=45) as response:
                result = json.load(response)
            break
        except urllib.error.HTTPError as error:
            if error.code not in (429, 500, 502, 503, 504) or attempt == 3:
                raise
        except (TimeoutError, urllib.error.URLError):
            if attempt == 3:
                raise
        time.sleep(2 ** attempt)
    if result.get("ok") is not True:
        raise RuntimeError("Boat did not confirm " + path)
    return result

# Two hours on the normal 16 GB worker at $0.072/hour plus one start surcharge of at most $0.07.
# No API key, organization environment, snapshot or forwarding is copied into the guest.
setup = f"""set -euo pipefail
cd "$HOME"
git init -q judge
git -C judge fetch -q --depth=1 https://github.com/josusanmartin/riemann.git {revision}
git -C judge checkout -q --detach FETCH_HEAD
test "$(git -C judge rev-parse HEAD)" = {revision}
status=0
bash judge/boat/compact/qualify.sh > qualification.log 2>&1 || status=$?
for file in qualification.log riemann-bootstrap.log riemann-proof.log; do
    if test -f "$file"; then tail -c 2000 "$file"; fi
done > qualification-diagnostic.txt
exit "$status" """
request = {"type": "large", "name": "Compact RH qualification", "org": "personal",
           "environment": "riemann-production", "visibility": "private", "noEnv": True,
           "snapshots": False, "monitoring": False, "ttlSeconds": 7200,
           "labels": {"service": "riemann", "kind": "qualification", "revision": revision}, "setupScript": setup}
worker = api("/sandboxes", "POST", request, "compact-qualification-" + os.environ["GITHUB_RUN_ID"])["sandbox"]["id"]
if not re.fullmatch(r"bx_[23456789abcdefghjkmnpqrstuvwxyz]{8}", worker):
    raise ValueError("Missing Boat worker identity")
endpoint = "/sandboxes/" + worker
print("Qualification worker", worker, flush=True)
try:
    for _ in range(240):
        box = api(endpoint)["sandbox"]
        if box.get("holdsCreatorLogins") is not False or box.get("snapshots") is not False or box.get("environment") != "riemann-production":
            raise RuntimeError("Qualification worker isolation differs from production")
        if box["state"] in ("stopped", "archived", "error") or box.get("setupStatus") == "failed":
            # Read the trusted setup log tail. Keep it bounded and print raw output as plain text.
            try:
                diagnostic = api(endpoint + "/files?path=qualification-diagnostic.txt&encoding=utf8")
                for line in diagnostic.get("content", "").splitlines():
                    print("worker |", line[:400], flush=True)
            except urllib.error.HTTPError:
                pass
            raise RuntimeError("Qualification failed before issuing a receipt")
        if box.get("setupStatus") == "done":
            raw = api(endpoint + "/files?path=canary-attestation.json&encoding=utf8")["content"]
            data = json.loads(raw)
            if (data.get("result") != "kernel-verified" or data.get("score") != {"numerator": "854225", "denominator": "1000000"}
                or data.get("submissionId") != "knausgard-rh-reflected-kernel-8542"
                or data.get("kernels") != ["lean", "nanoda"]
                or set(data.get("permittedAxioms", [])) != {"propext", "Classical.choice", "Quot.sound"}
                or data.get("compactReplay", {}).get("policyVersion") != 3):
                raise RuntimeError("Qualification receipt differs from the archived record")
            Path("canary-attestation.json").write_text(json.dumps(data, indent=2) + "\n")
            print("Verified", data["compactReplay"], flush=True)
            break
        time.sleep(30)
    else:
        raise TimeoutError("Boat qualification reached its time limit")
finally:
    try:
        try:
            journal = api(endpoint + "/files?path=riemann-stages.tsv&encoding=utf8")["content"]
            Path("canary-stages.tsv").write_text(journal[:8192])
        except (KeyError, urllib.error.HTTPError):
            pass
        usage = api(endpoint + "/usage")
        fields = ("sandboxType", "since", "until", "seconds", "secondsPerDollar", "billingMultiplier", "dollars", "running")
        Path("canary-usage.json").write_text(json.dumps({k: usage.get(k) for k in fields}, indent=2) + "\n")
        print("Boat reported machine usage in dollars:", usage.get("dollars"), flush=True)
    except urllib.error.HTTPError as error:
        if error.code not in (403, 404):
            raise
        print("Usage is unavailable to the scoped key. The two-hour worker TTL applies.", flush=True)
    finally:
        try:
            api(endpoint + "/stop", "POST", {})
        except urllib.error.HTTPError as error:
            if error.code != 409:
                raise
        for _ in range(12):
            if api(endpoint)["sandbox"]["state"] in ("stopped", "archived", "deleted"):
                print("Boat shutdown confirmed", flush=True)
                break
            time.sleep(5)
        else:
            raise RuntimeError("Boat shutdown has not yet been confirmed")
