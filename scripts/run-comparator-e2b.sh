#!/usr/bin/env bash
set -euo pipefail

if [[ $# -ne 2 ]]; then
  printf 'Usage: run-comparator-e2b.sh <comparator-binary> <config-path>\n' >&2
  exit 2
fi
: "${COMPARATOR_LANDRUN:?COMPARATOR_LANDRUN is required}"
: "${RIEMANN_E2B_NETWORK_DISABLED:?RIEMANN_E2B_NETWORK_DISABLED is required}"
if [[ "${E2B_SANDBOX:-}" != "true" ]] ||
   [[ "$RIEMANN_E2B_NETWORK_DISABLED" != "1" ]]; then
  printf 'Refusing to run outside the expected E2B isolation boundary.\n' >&2
  exit 96
fi
if [[ -n "${E2B_API_KEY:-}" ]] || [[ -n "${E2B:-}" ]] ||
   [[ -n "${AUTH_SECRET:-}" ]] || [[ -n "${GITHUB_RECORDS_TOKEN:-}" ]] ||
   [[ -n "${SUBMISSION_ARCHIVE_KEY:-}" ]]; then
  printf 'Refusing to run with an orchestrator secret in the sandbox environment.\n' >&2
  exit 96
fi
if [[ ! -x "$COMPARATOR_LANDRUN" ]] || ! command -v python3 >/dev/null 2>&1; then
  printf 'Required E2B isolation probes are unavailable.\n' >&2
  exit 96
fi

set +e
python3 - <<'PY'
import socket
import ssl
import sys

socket.setdefaulttimeout(3.0)


def tls_data_reachable():
    try:
        with socket.create_connection(("1.1.1.1", 443), timeout=3.0) as raw:
            with ssl.create_default_context().wrap_socket(
                raw,
                server_hostname="one.one.one.one",
            ) as stream:
                stream.settimeout(3.0)
                stream.sendall(
                    b"HEAD / HTTP/1.0\r\nHost: one.one.one.one\r\n\r\n"
                )
                return bool(stream.recv(1))
    except OSError:
        return False


def http_data_reachable():
    try:
        with socket.create_connection(("1.1.1.1", 80), timeout=3.0) as stream:
            stream.sendall(
                b"HEAD / HTTP/1.0\r\nHost: one.one.one.one\r\n\r\n"
            )
            stream.settimeout(3.0)
            return bool(stream.recv(1))
    except OSError:
        return False


sys.exit(97 if tls_data_reachable() or http_data_reachable() else 0)
PY
network_probe_status=$?
set -e
if [[ "$network_probe_status" -ne 0 ]]; then
  printf 'Refusing to run: E2B outbound network isolation is not active.\n' >&2
  exit 97
fi

landrun_probe_dir="$(mktemp -d /tmp/riemann-landrun-probe.XXXXXX)"
landrun_probe_file="$landrun_probe_dir/probe"
trap 'rm -rf -- "$landrun_probe_dir"' EXIT
set +e
"$COMPARATOR_LANDRUN" \
  --best-effort \
  --ro / \
  --rw /dev \
  --ldd \
  --add-exec \
  -- \
  /usr/bin/touch "$landrun_probe_file" \
  >/dev/null 2>&1
filesystem_probe_status=$?
set -e
if [[ -e "$landrun_probe_file" ]] || [[ "$filesystem_probe_status" -eq 0 ]]; then
  printf 'Refusing to run: Landlock filesystem restrictions are unavailable.\n' >&2
  exit 98
fi
rm -rf -- "$landrun_probe_dir"
trap - EXIT

ulimit -f 8388608
ulimit -u 512
exec timeout --signal=TERM --kill-after=15s 3200s \
  /opt/riemann/tools/bin/lake env "$1" "$2"
