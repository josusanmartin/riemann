# Security policy

## Reporting

Please report verifier escapes, theorem-contract weaknesses, authentication defects, and disclosure vulnerabilities privately to the repository owner through GitHub's private vulnerability reporting feature. Do not demonstrate a sandbox escape against public CI.

## Untrusted proof model

All submission files are hostile input. Lean macros, elaborators, tactics, build scripts, and imported native code can execute during compilation. The formal verifier therefore follows these rules:

- no secrets are exposed to the proof-verification job;
- outbound network access is disabled during the untrusted build;
- independent filesystem and socket probes confirm the readonly mounts and disabled IPv4 and Unix sockets before source elaboration;
- the worker checks SHA-256 digests for the Lean toolchain and all runtime cache parts, which become root-owned before the submission runs;
- the proof account sees the toolchain, dependency cache and its per-job workspace inside a restricted filesystem root;
- candidate source cannot supply compiled `.olean` files;
- CPU, memory, disk, process count, and wall time are bounded;
- Comparator builds and exports the trusted challenge before the candidate solution;
- accepted theorems are replayed by Lean and nanoda;
- record promotion occurs outside the Boat worker in a separate credentialed server path.

Before promotion, the server downloads the exact manifest and `Solution.lean` from the sandbox, recomputes their signed digest, validates the attestation against both the deployed contract and a separate immutable verifier-template digest, and reads the record ledger at the signed `main` commit. It creates immutable evidence and ledger commits but exposes them through one `force: false` reference update. A changed record therefore fails closed without overwriting or displaying a stale result, and a receipt for a different verifier revision cannot authorize promotion.

The Boat proof account receives no OAuth, session-signing, webhook, GitHub, Vercel, or E2B API credential. The browser receives only an HMAC-signed opaque job handle. The GitHub write credential is fine-grained to repository Contents and exists only in trusted promotion and queue-coordination functions.

Queue coordination uses an automation-only Git branch and non-forced compare-and-swap updates, so only one proof job is active at a time. Its public control ledger contains HMAC-pseudonymous ownership counters, sandbox/job identifiers, digests, and bounded terminal receipts. Every admitted manifest and Lean source is additionally gzip-compressed and sealed with AES-256-GCM in the same compare-and-swap commit. The branch therefore contains encrypted source ciphertext but never GitHub usernames, rejected Lean source, or rejected verifier logs in plaintext. The FIFO head receives its disposable worker when verification begins.

`SUBMISSION_ARCHIVE_KEY` is a dedicated 32-byte server-only key and must never be sent to E2B, the browser, GitHub Actions, or application logs. The maintainer archive route requires both a configured allowlisted GitHub identity and the deployment-held key, returns `no-store` responses, and rechecks the authenticated envelope, immutable path metadata, manifest, and proof digest before releasing source. Losing or rotating the key without migration makes prior ciphertext unrecoverable.

`--mode=quick` deliberately omits the adversarial sandbox and must never be used on unknown Lean source.

## Web application

GitHub authentication requests read-only identity scopes. OAuth credentials, `AUTH_SECRET`, `E2B_API_KEY`, `E2B_WEBHOOK_SECRET`, `GITHUB_RECORDS_TOKEN`, and `SUBMISSION_ARCHIVE_KEY` belong only in encrypted deployment variables. The site uses signed JWT sessions, accepts one bounded Lean source upload, retains every admitted source under the disclosed encrypted policy, and publishes accepted exact bytes plus the two-kernel attestation as immutable Git evidence.

The active production verifier uses a disposable Boat worker. The proof process runs under a separate account with systemd network, memory, task and time limits. The web service enforces a durable five-admission daily GitHub quota and a single competitive worker lane. Warm function instances also throttle upload and status bursts before GitHub authentication. The hosting provider handles distributed network traffic upstream.

Private submission, sign-in and admin pages use per-response script nonces. Browser clients send verification handles in a request header. The legacy query parameter is supported for existing CLI clients. Maintainer access to the archive and the operator flow test requires a matching immutable GitHub account ID. New competitive jobs and their private histories use a separate ownership key derived from the immutable GitHub account ID. Legacy histories retain their original login-based ownership key. Users with older browser sessions must sign out and back in to refresh the ID claim before a new upload. Additional authorized accounts use the format `login:numeric-id` in their role allowlist.

Production deployment depends on the Linux application checks and high-severity dependency audit of both npm lockfiles.

The health endpoint's `verifierIdentity` describes the active provider. Boat uses the immutable source commit assigned at admission. Before transferring proof files the service checks the provider-reported job and role, worker isolation, and a checkout marker written only after the worker verifies its detached Git HEAD. Legacy workers without the marker must expose the matching detached HEAD. Publication independently checks the verifier-material digest. This pins verifier source; the underlying Boat VM image is provider-managed. E2B uses a template-content digest: the configured digest and measured sandbox digest must both match the deployment's expected digest. The legacy `verifierTemplateIdentityConfigured` boolean reports the active provider's pin. `e2bTemplateIdentityConfigured` reports the separate E2B configuration. Health is a configuration check; it does not allocate a worker.
