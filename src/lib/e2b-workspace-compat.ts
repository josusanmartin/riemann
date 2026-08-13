import type { Sandbox } from "e2b";

// The immutable E2B image is root-owned. Its non-build Zeta source is copied
// by the unprivileged verifier into a disposable workspace before candidate
// preparation. Node preserves source mode bits during that copy, so the
// source must be owner-writable even though it remains unwritable to the
// `riemann` user while it is sealed under /opt.
//
// Templates built before this compatibility step used 0555/0444 modes. Fix
// only mode bits (never contents or ownership), leave the large shared .lake
// tree sealed, then prove that a copied ChallengeDeps directory is writable
// by the verifier user. Content-based verifier attestations are unchanged.
export async function prepareE2BWorkspaceCopySource(
  sandbox: Pick<Sandbox, "commands">,
): Promise<void> {
  await sandbox.commands.run(
    `set -euo pipefail
source_root=/opt/riemann/zeta23
test "$(stat -c '%U:%G' "$source_root")" = root:root
if find "$source_root" -path "$source_root/.lake" -prune -o ! -user root -print -quit | grep -q .; then
  echo 'Unsealed owner found in the trusted Zeta source' >&2
  exit 1
fi
find "$source_root" -path "$source_root/.lake" -prune -o -type d -exec chmod 0755 {} + -o -type f -exec chmod 0644 {} +
runuser -u riemann -- test ! -w "$source_root"
runuser -u riemann -- test ! -w "$source_root/lakefile.toml"
install -d -o riemann -g riemann -m 0700 /home/riemann/tmp
probe=$(mktemp -d /home/riemann/tmp/workspace-copy-mode-XXXXXX)
trap 'rm -rf "$probe"' EXIT
chown riemann:riemann "$probe"
runuser -u riemann -- cp -R "$source_root/comparator/ChallengeDeps" "$probe/ChallengeDeps"
runuser -u riemann -- touch "$probe/ChallengeDeps/CandidateSpec.lean"
runuser -u riemann -- test -w "$probe/ChallengeDeps/CandidateSpec.lean"`,
    { user: "root", timeoutMs: 30_000 },
  );
}
