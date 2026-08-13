# Security policy

## Reporting

Please report verifier escapes, theorem-contract weaknesses, authentication defects, and disclosure vulnerabilities privately to the repository owner through GitHub's private vulnerability reporting feature. Do not demonstrate a sandbox escape against public CI.

## Untrusted proof model

All submission files are hostile input. Lean macros, elaborators, tactics, build scripts, and imported native code can execute during compilation. The formal verifier therefore follows these rules:

- no secrets are exposed to the proof-verification job;
- outbound network access is disabled during the untrusted build;
- E2B disables sandbox internet and public traffic before source is uploaded, and the job fails closed unless a live outbound probe confirms that boundary;
- Comparator's Landlock layer is independently probed before the proof runs; local full-verifier runs add systemd socket-family, syscall, and private-network restrictions;
- the challenge import closure and toolchain come from a root-owned, non-writable, pinned E2B template whose runtime artifacts remain readable by the unprivileged verifier;
- a root-owned system Git configuration enumerates the pinned checkout and each sealed dependency repository exactly, permitting Lake to inspect trusted metadata after ownership sealing without trusting arbitrary repositories;
- candidate source cannot supply compiled `.olean` files;
- CPU, memory, disk, process count, and wall time are bounded;
- Comparator builds and exports the trusted challenge before the candidate solution;
- accepted theorems are replayed by Lean and nanoda;
- record promotion occurs outside E2B in a separate credentialed server path.

Before promotion, the server downloads the exact manifest and `Solution.lean` from the sandbox, recomputes their signed digest, validates the attestation against both the deployed contract and a separate immutable verifier-template digest, and reads the record ledger at the signed `main` commit. It creates immutable evidence and ledger commits but exposes them through one `force: false` reference update. A changed record therefore fails closed without overwriting or displaying a stale result, while an outdated E2B template produces an explicit rebuild error.

The E2B sandbox receives no OAuth, session-signing, webhook, GitHub, Vercel, or E2B API credential. The browser receives only an HMAC-signed opaque job handle. The GitHub write credential is fine-grained to repository Contents and exists only in trusted promotion and queue-coordination functions.

Queue coordination uses an automation-only Git branch and non-forced compare-and-swap updates, so only one proof job is active at a time. Its public control ledger contains HMAC-pseudonymous ownership counters, sandbox/job identifiers, digests, and bounded terminal receipts. Every admitted manifest and Lean source is additionally gzip-compressed and sealed with AES-256-GCM in the same compare-and-swap commit. The branch therefore contains encrypted source ciphertext but never GitHub usernames, rejected Lean source, or rejected verifier logs in plaintext. Waiting source also remains inside paused, no-egress E2B filesystems until verification.

`SUBMISSION_ARCHIVE_KEY` is a dedicated 32-byte server-only key and must never be sent to E2B, the browser, GitHub Actions, or application logs. The maintainer archive route requires both a configured allowlisted GitHub identity and the deployment-held key, returns `no-store` responses, and rechecks the authenticated envelope, immutable path metadata, manifest, and proof digest before releasing source. Losing or rotating the key without migration makes prior ciphertext unrecoverable.

`--mode=quick` deliberately omits the adversarial sandbox and must never be used on unknown Lean source.

## Web application

GitHub authentication requests read-only identity scopes. OAuth credentials, `AUTH_SECRET`, `E2B_API_KEY`, `E2B_WEBHOOK_SECRET`, `GITHUB_RECORDS_TOKEN`, and `SUBMISSION_ARCHIVE_KEY` belong only in encrypted deployment variables. The site uses signed JWT sessions, accepts one bounded Lean source upload, retains every admitted source under the disclosed encrypted policy, and publishes accepted exact bytes plus the two-kernel attestation as immutable Git evidence.
