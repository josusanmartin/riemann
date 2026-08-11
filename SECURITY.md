# Security policy

## Reporting

Please report verifier escapes, theorem-contract weaknesses, authentication defects, and disclosure vulnerabilities privately to the repository owner through GitHub's private vulnerability reporting feature. Do not demonstrate a sandbox escape against public CI.

## Untrusted proof model

All submission files are hostile input. Lean macros, elaborators, tactics, build scripts, and imported native code can execute during compilation. The formal verifier therefore follows these rules:

- no secrets are exposed to the proof-verification job;
- outbound network access is disabled during the untrusted build;
- the verifier fails closed unless its outer network-syscall filter and Landlock filesystem restrictions pass live probes;
- the challenge import closure and toolchain come from the protected base branch;
- candidate source cannot supply compiled `.olean` files;
- CPU, memory, disk, process count, and wall time are bounded;
- Comparator builds and exports the trusted challenge before the candidate solution;
- accepted theorems are replayed by Lean and nanoda;
- record promotion occurs in a separate trusted workflow.

`--mode=quick` deliberately omits the adversarial sandbox and must never be used on an unknown pull request.

## Web application

GitHub authentication requests read-only identity scopes. OAuth credentials and `AUTH_SECRET` belong only in encrypted deployment variables. The site uses signed JWT sessions, does not accept proof uploads, and sends contributors to GitHub pull requests so the verification boundary remains auditable.
