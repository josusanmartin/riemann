# Riemann.fail

Riemann.fail is an automated formal-proof arena for improving the unconditional lower bound on the proportion of nontrivial Riemann zeta zeros that lie on the critical line.

The record starts at

```text
κ₀ = 2 - 1 / cMT = 0.672500703679411645734379790803…
```

using [Anthropic's 2026 research article](https://www.anthropic.com/research/riemann-zeta) and Zeta23 result as the reference starting point. A candidate advances the public number only when it supplies an exact rational `p/q` and Lean proves both that `p/q` is strictly greater than the current record and that the frozen unconditional theorem holds at `p/q`.

## What is automated

```text
GitHub-authenticated Lean upload
  → server-derived manifest and exact source digest
  → private no-egress E2B sandbox
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

Sign in at `/submit`, enter an exact rational score, and paste or upload one `Solution.lean` file implementing the three declarations. Optional model and harness attribution are stored as structured, attested fields in the public record. The server derives the manifest, theorem names, GitHub author, proof path, and license; those fields are never trusted from the browser. No pull request or additional file is required. See [CONTRIBUTING.md](CONTRIBUTING.md) for the frozen theorem and complete verifier contract.

Formal uploads enter a durable FIFO and exactly one proof verifier runs at a time. Each authenticated GitHub account may enter at most three uploads per UTC day. Waiting proofs are sealed in paused, no-egress E2B sandboxes; advancing the queue resumes only its head. The automation-only `automation-queue` branch stores HMAC-pseudonymous ownership counters, opaque job coordinates, and terminal receipts—not GitHub usernames or Lean source. Non-forced Git reference updates serialize concurrent admissions.

For local development, copy `submissions/example` and prepare a candidate against the pinned Zeta23 tree:

Prepare a candidate against the pinned Zeta23 tree:

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

Configure the OAuth, public URL, E2B, webhook, and GitHub promotion variables from `.env.example` in the Vercel project. Build the pinned E2B image with `npm run e2b:template:build`, smoke the exact build, then set its immutable `riemann-fail-verifier:<build-id>` reference as `E2B_TEMPLATE_ID`; a bare family ID is mutable and must not be activated. If the E2B key exists only in Vercel, the authenticated `/api/admin/e2b-template` endpoint can start, inspect, and smoke the same background build using a temporary `E2B_TEMPLATE_ADMIN_SECRET`; remove that secret after bootstrap. Lean runs asynchronously inside E2B rather than a Vercel function because elaboration is long-running and executes hostile contributor code.

`GITHUB_RECORDS_TOKEN` must be a fine-grained credential limited to this repository with only **Contents: read and write**. It is held by Vercel and never sent to E2B. It updates the opaque queue-control branch and, only after the server has re-read and rehashed a passing result, publishes evidence. Promotion writes an evidence commit and a ledger commit, then publishes both with one non-forced update of `main`; a race cannot overwrite another record.

Production deploys run from `.github/workflows/deploy-production.yml` on every push to `main`. Because the promotion credential is not GitHub Actions' `GITHUB_TOKEN`, a successful record update triggers the normal deployment. An authenticated status request publishes immediately; if the submitter closes the browser, a signed E2B pause webhook resumes the preserved sandbox, completes the same idempotent publication path, and advances the next FIFO entry. A daily `CRON_SECRET`-protected sweep is the final backstop for a missed webhook or interrupted queue transition.

Every deployment must expose the exact source commit as `VERCEL_GIT_COMMIT_SHA` or the per-deployment fallback `RIEMANN_BASE_COMMIT_SHA`. The checked-in workflow sets the fallback from `GITHUB_SHA`; the submission endpoint refuses to start without it.

## Trust boundary

The trusted statement definitions come from Mathlib-only `ChallengeDeps` at the pinned `anthropics/zeta-23-lean` commit. Candidate code cannot edit the theorem, score, toolchain, permitted axioms, or current record. Comparator requires exact statement equality, rejects undeclared axioms, and replays the proof in a kernel.

The remaining foundational trust is the frozen definitions, Mathlib, the Lean or nanoda kernel, the verifier sandbox, the operating system, and hardware. Ordinary numerical experiments cannot advance the formal record.

## Sources and licensing

- [Anthropic research announcement](https://www.anthropic.com/research/riemann-zeta)
- [Zeta23 Lean formalization](https://github.com/anthropics/zeta-23-lean)
- [Lean Comparator](https://github.com/leanprover/comparator)

The site code is released under the MIT License. Zeta23 is not vendored into this repository; the verifier checks out its pinned Apache-2.0 source. Formal proof submissions use Apache-2.0 so they can be integrated with that challenge tree. See [THIRD_PARTY_NOTICES.md](THIRD_PARTY_NOTICES.md).
