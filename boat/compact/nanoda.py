"""Install or verify the independently pinned checker inside the Lean prefix."""
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile


def check(binary, pins):
    digest = hashlib.sha256()
    with binary.open("rb") as src:
        while chunk := src.read(1024 * 1024):
            digest.update(chunk)
    if digest.hexdigest() != pins["linuxX64Sha256"]:
        raise ValueError("nanoda binary checksum mismatch")
    banner = subprocess.check_output([str(binary), "--help"], text=True).splitlines()[0]
    if banner != "nanoda_bin " + pins["version"]:
        raise ValueError("nanoda binary version mismatch")
    print(f"{banner} (upstream {pins['revision']})", flush=True)


def main():
    mode, prefix = sys.argv[1:]
    pins = json.loads(Path(__file__).with_name("nanoda-release.json").read_text())
    binary = Path(prefix).resolve() / "bin/nanoda_bin"
    if mode == "check":
        check(binary, pins)
    elif mode == "install":
        with tempfile.TemporaryDirectory(dir=binary.parent) as work:
            staged = Path(work) / "nanoda_bin"
            subprocess.run(["curl", "--fail", "--silent", "--show-error", "--location",
                            "--retry", "3", "--output", str(staged), pins["url"]], check=True)
            staged.chmod(0o755)
            check(staged, pins)
            os.replace(staged, binary)
    else:
        raise ValueError("Expected install or check")


if __name__ == "__main__":
    main()
