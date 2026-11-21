# Contributing a new formal record

The formal leaderboard has one objective: maximize the unconditional critical-line constant while preserving the exact counting functions and theorem shape.

## Scored theorem

For a submitted exact rational `κ = p/q`, the verifier generates these declarations from trusted templates:

```lean
theorem candidate_strict_improvement :
    currentRecordKappa < candidateKappa

theorem candidate_critical_line_bound :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (candidateKappa - ε) * (Ncount T (2 * T) : ℝ) ≤ N0star T (2 * T)

theorem candidate_critical_line_bound_cumulative :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (candidateKappa - ε) * (Ncount 0 T : ℝ) ≤ N0star 0 T
```

`Ncount` counts nontrivial zeros with multiplicity. `N0star` counts distinct zeros on the critical line. The statement has no Riemann-hypothesis assumption and no candidate-controlled hypotheses.

## Direct submission

Sign in with GitHub at `/submit`. Supply a public display name, method, summary, exact numerator and denominator, and one `Solution.lean` source file. You may also name the AI model and coding harness; these are optional structured attribution fields and do not affect scoring. Scores are positive integers encoded as strings:

```json
"score": {
  "numerator": "672500704",
  "denominator": "1000000000"
}
```

Floating-point scores are rejected. The dashboard decimal is derived from the exact rational.

Start from the downloadable [`Solution.lean` template](https://www.riemannzeta.fun/templates/Solution.lean), also checked in at `submissions/example/proof/Solution.lean`. Keep all three theorem names and statements unchanged, replace all three `sorry` placeholders, and place any imports or helper declarations in that one file. The form—not the Lean source—supplies the exact numerator and denominator used to generate `candidateKappa`.

The authenticated GitHub login becomes `author.github`; it cannot be supplied or overridden in the request body. The trusted server also generates the manifest, fixed proof path, theorem names, track, and Apache-2.0 license declaration. The accepted source surface is exactly one UTF-8 Lean file of at most 2 MB. Put helper declarations in that file.

For CLI/agent use, the same `/api/submissions`, `/api/submissions/active`, and
`/api/submissions/status?job=…` endpoints accept `Authorization: Bearer <GitHub token>`.
The server verifies the token with GitHub's authenticated `/user` endpoint on
each request; it never accepts a caller-supplied username. Use a dedicated
fine-grained personal token with no repository permissions, not a repository
write token. Never put tokens in URLs, Lean files, or committed scripts.
Browser sign-in remains supported. The same queue, account-specific daily limit,
archive policy, and mathematical checks apply to both clients.

Send JSON with `Content-Type: application/json`. The complete JSON-encoded
request is limited to 4 MB (including escaping); the decoded Lean source is
separately limited to 2 MB. Both limits are enforced on actual bytes, including
requests without a `Content-Length` header.

The service accepts at most **three admitted uploads per GitHub account per UTC calendar day, or five for the repository owner**, resetting at **00:00 UTC**. An input rejected before durable queue admission does not count and is not retained. Once admitted, the slot is consumed regardless of the result: syntax and elaboration errors, theorem or axiom mismatch, Lean or nanoda rejection, timeout, sandbox expiration, and successful verification all count. Slots are not automatically refunded, so validate locally before submitting when possible. Admitted uploads enter a durable first-in, first-out queue, and only its head runs the formal verifier. Other uploads remain sealed in paused no-egress sandboxes until their turn; refreshing the page does not change order or reset the limit.

Every admitted manifest and exact Lean source is retained indefinitely in a gzip-compressed, AES-256-GCM encrypted maintainer archive, including rejected, timed-out, and infrastructure-failed attempts. Archive ciphertext is committed atomically with queue admission; plaintext rejected source is not published. A proof that passes is also published under Apache-2.0 as immutable public evidence. The form states this retention boundary before submission.

The browser cannot modify the challenge contract, generated theorem templates, record data, lockfiles, verifier, dependency pins, or publication logic. Infrastructure changes use the repository's ordinary development process and never receive a formal score.

## Acceptance

A submission becomes a formal record when all of the following hold automatically:

1. Its authenticated fields and server-generated manifest validate.
2. Comparator proves exact equality with the trusted generated statements.
3. Its transitive axiom set is a subset of the three standard axioms and the fixed external premise `RiemannFoundation.alpogeRH : RiemannHypothesis`. Comparator matches the premise and its dependencies to the trusted declarations.
4. Lean accepts the exported proof.
5. The independent nanoda kernel accepts the proof.
6. `candidate_strict_improvement` proves the rational exceeds the exact current record.
7. Both dyadic and cumulative critical-line theorems pass.

Human review is welcome but is not a formal-record prerequisite. A result without a complete machine proof may be discussed in an issue, but it cannot change the displayed record.

## Optional independent review

After formal acceptance, a maintainer may attach an `independentReview` entry to the trusted ledger when a public review identifies its reviewer, date, evidence URL, and summary. The dashboard renders that as a separate **Expert reviewed** badge. It is never read by the score comparator or promotion decision, and the default for every machine-promoted record is `null`.

Review metadata is a separate infrastructure change. It is never accepted from the scored upload.

## Security

Lean elaboration executes contributor-controlled metaprograms. Never run an unfamiliar proof directly on a workstation with credentials. Authoritative verification runs without repository secrets or network access in a resource-limited E2B sandbox. See [SECURITY.md](SECURITY.md).

## Test the verifier on Boat

The Submit page offers a Boat test to accounts listed in `RIEMANN_FLOW_TEST_GITHUB` when both Boat settings are present. It runs the repository’s arithmetic fixture through Comparator, Lean and nanoda, then tests that Comparator rejects a valid Lean proof of a different statement. The sandbox runs fixed test fixtures. Competitive uploads continue through the E2B queue.

Use a fresh x86-64 Ubuntu Boat sandbox with **No env** enabled and a short auto-stop. Check out the revision of this site that you are testing at `~/.local/share/riemann-boat/site` on that sandbox. As its normal user, prepare the verifier once:

```bash
set -eu
cd "$HOME/.local/share/riemann-boat/site"
bash scripts/install-lean-toolchain.sh
export PATH="$HOME/.elan/bin:$PATH"
elan toolchain install "$(cat challenge/smoke/lean-toolchain)"
bash scripts/install-native-build-toolchains.sh
export CARGO_HOME="$HOME/.riemann-build-toolchains/cargo"
export RUSTUP_HOME="$HOME/.riemann-build-toolchains/rustup"
export PATH="$HOME/.riemann-build-toolchains/go/bin:$CARGO_HOME/bin:$PATH"
bash scripts/install-verifier-tools.sh "$HOME/.local/share/riemann-boat/tools"
bash scripts/boat-smoke.sh
```

Set `RIEMANN_BOAT_SANDBOX_ID` and `BOAT_API_KEY` on the website server. Use an expiring key restricted to that sandbox with the `exec` action. Sign in as an operator and choose **Run Boat test** on `/submit`. The endpoint also accepts an authenticated GitHub user token via a JSON POST to `/api/admin/boat-smoke`. Stop the sandbox and revoke the test key when finished.

## Research evidence

The site has one competitive track for the fixed unconditional critical-line bound. Multi-file projects, larger dependencies and results checked in a different environment can be shared through the **Research evidence** issue form. Include a full source commit or archive digest, dependency pins, assumptions and replay instructions.

Promotion to the competitive leaderboard requires an official verification of the unconditional statements.

## On-demand Boat verification

The deployment setting `RIEMANN_VERIFIER_PROVIDER=boat` selects disposable Boat workers for new submissions and the operator flow test. The website and the encrypted Git-backed FIFO remain on their existing services. A waiting competitive proof has a logical job ID. Only the head of the FIFO can provision a VM. A job-specific signed notification wakes the website when a competitive receipt is ready. The website fetches that receipt directly from Boat. Status polling and the scheduled sweep resume interrupted provisioning and recover missed notifications. A two-hour auto-stop bounds an orphaned worker's lifetime.

Create the Boat environment `riemann-production` with **Safe for third parties** enabled. Restrict its expiring API key to this environment and the actions `sandbox.create`, `sandbox.read`, `sandbox.stop`, `file.read`, and `file.write`. Set the GitHub Actions secret `RIEMANN_BOAT_API_KEY` and the repository variable `RIEMANN_VERIFIER_PROVIDER`. Dispatch **Deploy production website** on main with `sync_boat_key` enabled to put the key in the production project's sensitive environment. Rotate the key before expiry. Selecting `e2b` on a subsequent deployment routes new submissions back to the legacy verifier; already admitted jobs retain their provider.

Each worker boots from a fixed site commit and fetches the pinned toolchains and libraries. It receives only the submitted files, with snapshots and provider monitoring disabled. A separate unprivileged account runs the verifier, with the nested Comparator process under the repository's filesystem and network restrictions. The supervisor seals the receipt, and the website checks the archived source digest, statement, axiom and kernel evidence before promotion.
