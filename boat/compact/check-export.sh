#!/usr/bin/env bash
# Run as the independent checker, with immutable exports and a trusted matchrunner.
set -euo pipefail
reference=$(realpath "${1:?reference export}")
solution=$(realpath "${2:?solution export}")
matcher=$(realpath "${3:?matchrunner binary}")
[[ $(lean --githash) == eb6cafb7290e8bd5f2937522d8d804f58f02bafc ]]
export LEAN_ABORT_ON_PANIC=1 LEAN_NUM_THREADS=2
unset LEAN_PATH LEAN_SRC_PATH
ulimit -s unlimited
work=$(mktemp -d)
trap 'rm -rf -- "$work"' EXIT
cd "$work"
prefix=$(lean --print-prefix)
LD_LIBRARY_PATH="$prefix/lib/lean:$prefix/lib" "$matcher" "$reference" "$solution" \
  riemannHypothesis candidate_strict_improvement candidate_critical_line_bound candidate_critical_line_bound_cumulative
python3 - "$solution" <<'PY'
import json
import sys
with open("nanoda.json", "x") as output:
    json.dump({
        "export_file_path": sys.argv[1], "use_stdin": False,
        "permitted_axioms": ["propext", "Classical.choice", "Quot.sound"],
        "unpermitted_axiom_hard_error": True, "num_threads": 4,
        "nat_extension": True, "string_extension": True,
        "pp_to_stdout": True, "print_axioms": True, "print_success_message": True,
    }, output)
PY
nanoda_bin nanoda.json
leanchecker --from-export "$solution"
sha256sum "$reference" "$solution"
