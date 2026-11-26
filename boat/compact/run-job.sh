#!/usr/bin/env bash
# The supervisor owns inputs and both exports. Only the independent data checker can authorize success.
set -euo pipefail
umask 022
[[ $EUID == 0 ]]
prepared=$(realpath "${1:?prepared submission workspace}")
runtime=$(realpath "${2:?immutable worker runtime}")
prefix=$(realpath "${3:?Lean installation}")
memory=${4:?memory ceiling}
[[ "$memory" == 12G || "$memory" == 28G ]]
receipt=$(realpath -m "${5:?supervisor-owned receipt destination}")
here=$(cd "$(dirname "$0")" && pwd)
export PATH="$prefix/bin:/usr/bin:/bin"
[[ $(lean --githash) == eb6cafb7290e8bd5f2937522d8d804f58f02bafc ]]
work=$(mktemp -d /var/lib/riemann-compact.XXXXXXXX)
jail=$(mktemp -d /var/lib/riemann-compact-root.XXXXXXXX)
active_unit=
cleanup() {
  if [[ -n "$active_unit" ]]; then systemctl stop "$active_unit.service" 2>/dev/null || true; fi
  rm -rf -- "$jail" "$work"
}
trap cleanup EXIT
trap 'exit 124' TERM INT
chmod 755 "$jail"
mkdir -p "$jail"/{dev,etc,proc,run,sys,tmp,usr,var/tmp}
chmod 1777 "$jail"/{tmp,var/tmp}
# Preserve the host's merged-/usr layout for the dynamic loader and shell.
for name in bin sbin lib lib64; do
  if [[ -L "/$name" ]]; then ln -s "$(readlink "/$name")" "$jail/$name"; fi
done
chmod 755 "$work"
install -d -m 755 "$work"/{spec/ChallengeDeps,ref,input/Solution}
install -d -m 700 -o proofcheck "$work/candidate"
install -m 444 "$prepared/comparator/Solution/Candidate.lean" "$work/input/Solution/Candidate.lean"
# Each module namespace must be rooted in one search directory for the Lean loader.
ln -s "$runtime/deps/zeta/ChallengeDeps.olean" "$work/spec/ChallengeDeps.olean"
{ echo 'import LegacyFinsetSyntax'; cat "$prepared/comparator/ChallengeDeps/CandidateSpec.lean"; } > "$work/spec/ChallengeDeps/CandidateSpec.lean"
install -m 444 "$prepared/comparator/Challenge/Candidate.lean" "$work/ref/Reference.lean"
base="$runtime/compat:$(find "$runtime/deps" -mindepth 1 -maxdepth 1 -type d | sort | paste -sd:):$prefix/lib/lean"
clean="$work/spec:$runtime/interface:$base"
# Build the independent reference before any candidate code executes.
(cd "$work/spec" && LEAN_PATH="$clean" lean -j2 -o ChallengeDeps/CandidateSpec.olean ChallengeDeps/CandidateSpec.lean)
read -ra primitives < "$here/required-targets.txt"
targets=(riemannHypothesis candidate_strict_improvement candidate_critical_line_bound candidate_critical_line_bound_cumulative)
(cd "$work/ref" && LEAN_PATH="$clean" lean -j2 -o Reference.olean Reference.lean)
(cd "$work/ref" && LEAN_PATH="$work/ref:$clean" leanexport Reference -- "${primitives[@]}" "${targets[@]}") > "$work/reference.ndjson"

isolated() {
  local user=$1 directory=$2
  shift 2
  local unit="riemann-compact-$(cat /proc/sys/kernel/random/uuid)"
  local status=0
  active_unit=$unit
  systemd-run --unit="$unit" --quiet --wait --pipe --service-type=exec --uid="$user" \
    --working-directory="$directory" --setenv=PATH="$PATH" --setenv=LEAN_NUM_THREADS=2 --setenv=LEAN_ABORT_ON_PANIC=1 \
    -p "RootDirectory=$jail" -p MountAPIVFS=yes \
    -p "BindReadOnlyPaths=/usr -/etc/ld.so.cache $prefix $runtime $here $work" \
    -p PrivateNetwork=yes -p RestrictAddressFamilies=AF_UNIX -p 'SystemCallFilter=~@network-io' \
    -p SystemCallArchitectures=native -p SystemCallErrorNumber=EPERM -p NoNewPrivileges=yes -p ProtectSystem=strict -p ProtectHome=yes \
    -p PrivateTmp=yes -p PrivateDevices=yes -p ProtectProc=invisible -p ProtectControlGroups=yes \
    -p ProtectKernelTunables=yes -p RestrictSUIDSGID=yes -p KillMode=control-group -p UMask=0077 \
    -p "MemoryMax=$memory" -p MemorySwapMax=0 -p TasksMax=512 -p LimitFSIZE=8589934592 -p LimitSTACK=infinity \
    -p RuntimeMaxSec=5800 -p OOMPolicy=kill "$@" || status=$?
  if (( status != 0 )) && [[ $(systemctl show "$unit.service" -p Result --value) == oom-kill ]]; then
    touch "$receipt.oom"
  fi
  active_unit=
  return "$status"
}
# This directory is the only persistent write destination of the submitted Lean program.
echo 'Compiling the submitted source against the RH interface.'
isolated proofcheck "$work/input" -p "BindPaths=$work/candidate" -p "ReadWritePaths=$work/candidate" -- \
  env LEAN_PATH="$clean" lean -j2 --tstack=400000 -o "$work/candidate/Uploaded.olean" Solution/Candidate.lean
# lean encodes the input module name in its olean. Keep its name and expose only that regular file.
install -d -m 755 "$work/link/Solution"
[[ -f "$work/candidate/Uploaded.olean" && ! -L "$work/candidate/Uploaded.olean" ]]
install -m 444 "$work/candidate/Uploaded.olean" "$work/link/Solution/Candidate.olean"
printf 'import Main\nimport Solution.Candidate\n' > "$work/link/Bundle.lean"
# Untrusted olean initialization is isolated too. Its output is only certificate data.
install -d -m 700 -o proofcheck "$work/bundle"
linked="$runtime/foundation:$work/link:$work/spec:$base"
echo 'Linking the compact proof of RH.'
isolated proofcheck "$work/link" -p "BindPaths=$work/bundle" -p "ReadWritePaths=$work/bundle" -- \
  env LEAN_PATH="$linked" lean -j1 -o "$work/bundle/Bundle.olean" Bundle.lean
[[ -f "$work/bundle/Bundle.olean" && ! -L "$work/bundle/Bundle.olean" ]]
install -m 444 "$work/bundle/Bundle.olean" "$work/link/Bundle.olean"
isolated proofcheck "$work/link" -- env LEAN_PATH="$linked" leanexport Bundle -- \
  "${primitives[@]}" "${targets[@]}" > "$work/solution.ndjson"
chmod 444 "$work"/*.ndjson
echo 'Comparing both interval statements and replaying the sealed proof with nanoda and Lean.'
isolated referee "$work" -- /bin/bash "$here/check-export.sh" \
  "$work/reference.ndjson" "$work/solution.ndjson" "$runtime/checker/matchrunner"
python3 - "$work" "$receipt" <<'PYTHON'
import hashlib, json, pathlib, sys
work = pathlib.Path(sys.argv[1])
def digest(name):
    with (work / name).open("rb") as file:
        checksum = hashlib.sha256()
        while block := file.read(1024 * 1024):
            checksum.update(block)
        return checksum.hexdigest()
with open(sys.argv[2], "x") as out:
    json.dump({"policyVersion": 3, "referenceSha256": digest("reference.ndjson"),
               "solutionSha256": digest("solution.ndjson")}, out)
PYTHON
