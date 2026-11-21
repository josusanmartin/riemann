#!/usr/bin/env bash
set -euo pipefail

root="$HOME/.local/share/riemann-boat"
tools="$root/tools"
site="$root/site"
export PATH="$HOME/.elan/bin:$PATH"

# Only the repository-owned fixtures run on this reusable operator sandbox.
# Use the same isolation, statement comparison and two kernels as the CI smoke test.
exec 9>"$root/smoke.lock"
flock -n 9 || exit 75
work="$(mktemp -d)"
trap 'rm -rf -- "$work"' EXIT
if ! bash "$site/scripts/smoke-verifier.sh" "$tools" > "$work/valid.log" 2>&1; then
  tail -n 15 "$work/valid.log" >&2
  exit 1
fi
grep -Fq 'Nanoda kernel accepts the solution' "$work/valid.log"
grep -Fq 'Lean default kernel accepts the solution' "$work/valid.log"

mkdir -p "$work/scripts" "$work/challenge"
cp "$site/scripts/"{smoke-verifier,run-comparator-sandbox}.sh "$work/scripts/"
cp -R "$site/challenge/smoke" "$work/challenge/"
cat > "$work/challenge/smoke/Solution.lean" <<'LEAN'
theorem verifier_smoke (left right : Nat) : left + right = left + right := rfl
LEAN
if bash "$work/scripts/smoke-verifier.sh" "$tools" > "$work/mismatch.log" 2>&1; then
  echo 'Comparator accepted a different statement' >&2
  exit 1
fi
if ! grep -Fq "Challenge and solution theorem statement do not match: 'verifier_smoke'" "$work/mismatch.log"; then
  echo 'The mismatch control failed for an unexpected reason' >&2
  tail -n 15 "$work/mismatch.log" >&2
  exit 1
fi
echo 'BOAT_SMOKE_OK'
