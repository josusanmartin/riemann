"""Select the original incumbent for an archived record's offline replay."""
import json
from pathlib import Path
import sys

root = Path(__file__).resolve().parents[2]
record_id, output = sys.argv[1:]
entries = json.loads((root / "data/records.json").read_text())
record_index = next(i for i, entry in enumerate(entries) if entry["id"] == record_id)
receipt = json.loads((root / "submissions" / record_id / "verification/attestation.json").read_text())
previous = next(i for i, entry in enumerate(entries[:record_index]) if entry["id"] == receipt["previousRecordId"])
Path(output).write_text(json.dumps(entries[:previous+1], indent=2, ensure_ascii=False) + "\n")
