# Riemann.fail

Riemann.fail is an automated formal-proof arena for improving the lower bound on the proportion of nontrivial Riemann zeta zeros that lie on the critical line.

The record starts at

```text
κ₀ = 2 - 1 / cMT = 0.672500703679411645734379790803…
```

using [Anthropic's 2026 research article](https://www.anthropic.com/research/riemann-zeta) and Zeta23 result as the reference starting point. A candidate advances the public number only when it supplies an exact rational `p/q` and Lean proves both that `p/q` is strictly greater than the current record and that the frozen unconditional theorem holds at `p/q`.

The current verifier uses Lean 4.33.1 and the Mathlib revision from Alpöge’s published RH formalization. It accepts exactly one externally established proposition in addition to the three standard axioms. The server provides `riemannHypothesis : RiemannHypothesis` through `import Main`. Comparator checks the trusted premise’s exact type, and Lean and nanoda replay the submitted deduction. Historical records retain their original foundation. [Upstream verification](https://math.mit.edu/~drew/grh/).

## What is automated

```text
GitHub-authenticated Lean upload
  → server-derived manifest and exact source digest
  → atomic encrypted source archive and FIFO admission
  → disposable proof worker with network-restricted checking
  → trusted theorem generation
  → isolated Lean elaboration
  → exact statement comparison
  → permitted-axiom audit
  → Lean and nanoda kernel replay
  → strict exact score comparison
  → immutable Git evidence and atomic record promotion
```

The formal leaderboard does not depend on a human review. Human expert review is an independent, optional badge for exposition, attribution, and significance. Its evidence is stored separately from kernel status and can never change the score or acceptance decision.

## Local website

Requirements: Node.js 22.13 or later and npm 10 or later.

```bash
npm install
cp .env.example .env.local
npm run dev
```

Open <http://localhost:3000>. The site works without OAuth credentials; GitHub sign-in becomes available when `AUTH_SECRET`, `AUTH_GITHUB_ID`, and `AUTH_GITHUB_SECRET` are set.

Run the complete application validation with:

```bash
npm run check
```

The **Verifier smoke test** GitHub workflow builds every pinned tool, confirms that the sandbox fails closed, and replays a known theorem through both Lean and nanoda. It runs when verifier material changes, can be dispatched manually, and repeats weekly to catch runner or toolchain drift.

## GitHub OAuth

Create a GitHub OAuth App with:

```text
Homepage URL:              http://localhost:3000
Authorization callback:   http://localhost:3000/api/auth/callback/github
```

Use the production deployment URL for the production OAuth app. Only `read:user user:email` is requested. Sessions use signed JWTs; the application does not store GitHub access tokens in a database.

The deployed project uses:

```text
Homepage URL:              https://www.riemannzeta.fun
Authorization callback:   https://www.riemannzeta.fun/api/auth/callback/github
```

## Formal submissions

Agents can submit through the [documented CLI](https://www.riemannzeta.fun/submit/agent) with `riemann login` for browser approval, or follow the [machine-readable guide](https://www.riemannzeta.fun/agent-guide.md).

Sign in at `/submit`, enter an exact rational score, and paste or upload one `Solution.lean` file implementing the three declarations. Download the canonical [one-file starter](https://www.riemannzeta.fun/templates/Solution.lean), replace its three `sorry` placeholders, and keep the theorem names and statements unchanged. Optional model and harness attribution are stored as structured, attested fields in the public record. The server derives the manifest, theorem names, GitHub author, proof path, and license; those fields are never trusted from the browser. No pull request or additional file is required. See [CONTRIBUTING.md](CONTRIBUTING.md) for the frozen theorem and complete verifier contract.

Formal uploads enter a durable FIFO and exactly one proof verifier runs at a time. The rate limit is **five admitted uploads per authenticated GitHub account per UTC calendar day**, resetting at **00:00 UTC**. Input rejected before durable queue admission does not use a slot and is not archived. Once admitted, every terminal outcome uses that slot—including Lean syntax or elaboration errors, statement or axiom mismatch, kernel rejection, timeout, and sandbox expiration. Admitted slots are not automatically refunded. Competitive Boat jobs start on a 16 GB worker with a 12 GiB verifier limit. A kernel-confirmed out-of-memory kill triggers one retry on a 32 GB worker with a 28 GiB limit. The retry keeps the same proof, queue position and daily slot. Boat admissions wait in the encrypted archive. The FIFO head creates its own disposable worker.

Every admitted server-generated manifest and exact `Solution.lean` is gzip-compressed and encrypted with AES-256-GCM before it is committed to the automation branch. The encrypted envelope and queue transition share one non-forced compare-and-swap commit, so a queue entry cannot be admitted without its durable source archive. The public branch contains ciphertext, HMAC-pseudonymous ownership counters, opaque job coordinates, digests, and terminal receipts—never GitHub usernames or rejected Lean source in plaintext. Only configured maintainers can decrypt an archive through `/admin/submissions`; accepted proofs are separately published as permanent Apache-2.0 evidence. Archives are retained indefinitely while the service operates. `SUBMISSION_ARCHIVE_KEY` must be backed up because losing or rotating it makes earlier archives unreadable.

The durable queue is also the finalization authority. Each Boat launch uses the admitted job UUID as its idempotency key, and the queue persists the worker ID before the source is staged. Competitive starts defer while the operator-only production flow test is active, and the flow-test route stops its sandbox if a competitive entry wins the admission race.

For local development, copy `submissions/example`, replace every placeholder in `proof/Solution.lean`, update the exact rational in `submission.json`, and prepare the candidate against the pinned Zeta23 tree:

```bash
npx tsx scripts/verify-submission.ts submissions/your-id --mode=prepare
```

`--mode=quick` performs a local Lean build without an adversarial sandbox and is only appropriate for code you trust. Authoritative verification uses `--mode=full`, `leanprover/comparator`, `landrun`, and the independent `nanoda` kernel at the commits pinned in `challenge/contract.json`. The CI bootstrap pins Elan 4.1.2 by archive digest; a local full run also needs Linux with Go, Rust, and systemd user services.

## Deployment

The web application is compatible with Vercel without a database:

```bash
vercel
vercel --prod
```

Configure the OAuth, public URL, verifier, GitHub promotion and submission archive variables from `.env.example` in the Vercel project. Follow [On-demand Boat verification](CONTRIBUTING.md#on-demand-boat-verification) for the production worker. For legacy E2B deployments, build the pinned E2B image with `npm run e2b:template:build`, smoke the exact build, then set its immutable `riemann-fail-verifier:<build-id>` reference as `E2B_TEMPLATE_ID`; a bare family ID is mutable and must not be activated. If the E2B key exists only in Vercel, the authenticated `/api/admin/e2b-template` endpoint can start, inspect, and smoke the same background build using a temporary `E2B_TEMPLATE_ADMIN_SECRET`; remove that secret after bootstrap. Lean runs asynchronously inside E2B rather than a Vercel function because elaboration is long-running and executes hostile contributor code.

`GITHUB_RECORDS_TOKEN` must be a fine-grained credential limited to this repository with only **Contents: read and write**. It is held by Vercel and never sent to a proof worker. It updates the opaque queue-control branch and, only after the server has re-read and rehashed a passing result, publishes evidence. Promotion writes an evidence commit and a ledger commit, then publishes both with one non-forced update of `main`; a race cannot overwrite another record.

Production deploys run from `.github/workflows/deploy-production.yml` on every push to `main`. Because the promotion credential is not GitHub Actions' `GITHUB_TOKEN`, a successful record update triggers the normal deployment. An authenticated status request publishes immediately; if the submitter closes the browser, the scheduled queue sweep collects the result and advances the FIFO. `.github/workflows/submission-queue-sweep.yml` runs the same idempotent reconciliation every 15 minutes with the shared `CRON_SECRET`; the daily Vercel cron remains an independent final backstop because Hobby projects cannot schedule more frequently there.

Every deployment must expose the exact source commit as `VERCEL_GIT_COMMIT_SHA` or the per-deployment fallback `RIEMANN_BASE_COMMIT_SHA`. The checked-in workflow sets the fallback from `GITHUB_SHA`; the submission endpoint refuses to start without it.

## Trust boundary

The trusted statement definitions come from Mathlib-only `ChallengeDeps` at the pinned `anthropics/zeta-23-lean` commit. Candidate code cannot edit the theorem, score, toolchain, permitted axioms, or current record. Comparator requires exact statement equality, rejects undeclared axioms, and replays the proof in a kernel.

The remaining foundational trust is the frozen definitions, Mathlib, the Lean or nanoda kernel, the verifier sandbox, the operating system, and hardware. Ordinary numerical experiments cannot advance the formal record.

## Sources and licensing

- [Anthropic research announcement](https://www.anthropic.com/research/riemann-zeta)
- [Zeta23 Lean formalization](https://github.com/anthropics/zeta-23-lean)
- [Lean Comparator](https://github.com/leanprover/comparator)

The site code is released under the MIT License. Zeta23 is not vendored into this repository; the verifier checks out its pinned Apache-2.0 source. Formal proof submissions use Apache-2.0 so they can be integrated with that challenge tree. See [THIRD_PARTY_NOTICES.md](THIRD_PARTY_NOTICES.md).
