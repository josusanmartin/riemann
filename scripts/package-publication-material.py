"""Build the publisher's fingerprint inputs from the immutable Git deployment revision."""
import base64
import hashlib
import json
from pathlib import Path
import subprocess
import sys


def git(*args):
    return subprocess.check_output(["git", *args])


def package(revision):
    rev = git("rev-parse", "--verify", revision + "^{commit}").decode().strip()
    policy = json.loads(git("show", f"{rev}:challenge/contract.json"))
    ledger = "data/records.json"
    before = bytearray(b"riemann.fail/trusted-material/v1\0")
    after = bytearray()
    records = None
    seen = set()
    files = []
    for path in policy["trustedPaths"]:
        entries = git("ls-tree", "-rz", rev, "--", path).split(b"\0")
        if entries == [b""]:
            raise ValueError(f"Missing trusted path: {path}")
        for entry in filter(None, entries):
            metadata, name = entry.split(b"\t", 1)
            mode, kind, oid = metadata.split()
            if mode not in (b"100644", b"100755") or kind != b"blob" or name in seen:
                raise ValueError(f"Invalid or duplicate trusted file: {name!r}")
            seen.add(name)
            files.append((name, oid))
    for name, oid in sorted(files):
        content = git("cat-file", "blob", oid)
        if name == ledger.encode():
            records = content
        else:
            part = before if records is None else after
            part.extend(name + b"\0" + str(len(content)).encode() + b"\0" + content + b"\0")
    if records is None:
        raise ValueError("Missing record ledger")
    def encode(value):
        return base64.b64encode(value).decode("ascii")
    return json.dumps(dict(revision=rev, before=encode(before), after=encode(after),
                           records=encode(records)), separators=(",", ":")).encode()


if __name__ == "__main__":
    bundle = package(sys.argv[1])
    Path(sys.argv[2]).write_bytes(bundle)
    print(hashlib.sha256(bundle).hexdigest())
