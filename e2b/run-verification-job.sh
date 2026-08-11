#!/usr/bin/env bash
set -uo pipefail

if [[ "$(id -u)" -ne 0 ]] || [[ $# -ne 3 ]]; then
  printf 'Usage (as root): run-verification-job.sh <submission-dir> <result-dir> <proof-digest>\n' >&2
  exit 2
fi

submission_dir="$1"
result_dir="$2"
proof_digest="$3"
job_pattern='[0-9a-f]{8}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{12}'
if [[ ! "$submission_dir" =~ ^/home/riemann/jobs/($job_pattern)/submission$ ]]; then
  printf 'Invalid E2B submission path.\n' >&2
  exit 2
fi
job_id="${BASH_REMATCH[1]}"
if [[ "$result_dir" != "/var/lib/riemann/jobs/$job_id" ]] ||
   [[ ! "$proof_digest" =~ ^[0-9a-f]{64}$ ]]; then
  printf 'Invalid E2B job coordinates.\n' >&2
  exit 2
fi

result_path="$result_dir/result.json"
log_path="$result_dir/verifier.log"
output_dir="/home/riemann/jobs/$job_id/output"
artifact_path="$output_dir/attestation.json"
install -d -o riemann -g riemann -m 0700 "$output_dir" /home/riemann/tmp
install -o root -g root -m 0600 /dev/null "$log_path"

set +e
timeout --signal=TERM --kill-after=15s 3240s \
  runuser -u riemann -- \
  env -i \
    HOME=/home/riemann \
    TMPDIR=/home/riemann/tmp \
    PATH=/home/riemann/.elan/bin:/usr/local/bin:/usr/bin:/bin \
    E2B_SANDBOX="${E2B_SANDBOX:-true}" \
    RIEMANN_E2B_NETWORK_DISABLED=1 \
    RIEMANN_OUTER_SANDBOX=e2b \
    RIEMANN_PREBUILT_ZETA23=/opt/riemann/zeta23 \
    RIEMANN_RECORDS_PATH="$submission_dir/trusted-records.json" \
    COMPARATOR_BIN=/opt/riemann/tools/bin/comparator \
    COMPARATOR_LANDRUN=/opt/riemann/tools/bin/landrun \
    COMPARATOR_LEAN4EXPORT=/opt/riemann/tools/bin/lean4export \
    COMPARATOR_NANODA=/opt/riemann/tools/bin/nanoda_bin \
    /usr/local/bin/node /opt/riemann/node_modules/tsx/dist/cli.mjs \
      /opt/riemann/scripts/verify-submission.ts \
      "$submission_dir" --mode=full --artifact="$artifact_path" \
      >"$log_path" 2>&1
verifier_status=$?
set -e

/usr/local/bin/node /opt/riemann/node_modules/tsx/dist/cli.mjs \
  /opt/riemann/scripts/finalize-e2b-job.ts \
  "$submission_dir" "$artifact_path" "$log_path" "$result_path" \
  "$proof_digest" "$verifier_status"

chmod 0444 "$log_path"
exit 0
