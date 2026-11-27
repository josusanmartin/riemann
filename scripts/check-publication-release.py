"""Check that the live publisher resolves the same digests as the release checkout."""
import base64
import hashlib
import json
from pathlib import Path
import sys
import time
import urllib.error
import urllib.request

bundle = json.loads(Path(sys.argv[1]).read_bytes())
prefix, records, suffix = (base64.b64decode(bundle[key], validate=True) for key in ("before", "records", "after"))
ledger = b"data/records.json\0" + str(len(records)).encode() + b"\0" + records + b"\0"
template = hashlib.sha256(prefix + suffix).hexdigest()
challenge = hashlib.sha256(prefix + ledger + suffix).hexdigest()
for attempt in range(18):
    try:
        query = f'https://www.riemannzeta.fun/api/health?release={bundle["revision"]}&attempt={attempt}'
        with urllib.request.urlopen(query, timeout=12) as response:
            health = json.load(response)
        if (health.get("verifierIdentity", {}).get("expectedCommit") == bundle["revision"]
            and health.get("expectedVerifierTemplateDigest") == template
            and health.get("expectedChallengeDigest") == challenge):
            print("Verified both production publisher fingerprints for", bundle["revision"])
            break
    except (urllib.error.URLError, TimeoutError, ValueError):
        pass
    time.sleep(5)
else:
    raise SystemExit("The live publisher did not confirm both fingerprints for this deployment")
