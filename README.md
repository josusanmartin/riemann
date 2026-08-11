# Riemann.fail

Riemann.fail is an automated formal-proof arena for improving the unconditional lower bound on the proportion of nontrivial Riemann zeta zeros that lie on the critical line.

The record starts at

```text
κ₀ = 2 - 1 / cMT = 0.672500703679411645734379790803…
```

from Anthropic's 2026 Zeta23 result. A candidate advances the public number only when it supplies an exact rational `p/q` and Lean proves both that `p/q` is strictly greater than the current record and that the frozen unconditional theorem holds at `p/q`.

## What is automated

```text
Pull request
  → schema and scope checks
  → trusted theorem generation
  → isolated Lean build
  → exact statement comparison
  → permitted-axiom audit
  → Lean and nanoda kernel replay
  → strict exact score comparison
  → formal record promotion
```

The formal leaderboard does not depend on a human review. Human expert review is an independent badge for exposition, attribution, and significance.

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

The manual **Verifier smoke test** GitHub workflow builds every pinned tool, confirms that the sandbox fails closed, and replays a known theorem through both Lean and nanoda.

## GitHub OAuth

Create a GitHub OAuth App with:

```text
Homepage URL:              http://localhost:3000
Authorization callback:   http://localhost:3000/api/auth/callback/github
```

Use the production deployment URL for the production OAuth app. Only `read:user user:email` is requested. Sessions use signed JWTs; the application does not store GitHub access tokens in a database.

## Formal submissions

Copy `submissions/example`, choose an exact rational score, and implement the three declarations in `proof/Solution.lean`. See [CONTRIBUTING.md](CONTRIBUTING.md) for the frozen theorem and complete verifier contract.

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

Configure the OAuth and public URL variables from `.env.example` in the Vercel project. Formal proof verification runs in isolated CI rather than inside a Vercel function because Lean builds are long-running and execute untrusted elaborator code.

## Trust boundary

The trusted statement definitions come from Mathlib-only `ChallengeDeps` at the pinned `anthropics/zeta-23-lean` commit. Candidate code cannot edit the theorem, score, toolchain, permitted axioms, or current record. Comparator requires exact statement equality, rejects undeclared axioms, and replays the proof in a kernel.

The remaining foundational trust is the frozen definitions, Mathlib, the Lean or nanoda kernel, the verifier sandbox, the operating system, and hardware. Ordinary numerical experiments cannot advance the formal record.

## Sources and licensing

- [Anthropic research announcement](https://www.anthropic.com/research/riemann-zeta)
- [Zeta23 Lean formalization](https://github.com/anthropics/zeta-23-lean)
- [Lean Comparator](https://github.com/leanprover/comparator)

The site code is released under the MIT License. Zeta23 is not vendored into this repository; the verifier checks out its pinned Apache-2.0 source. Formal proof submissions use Apache-2.0 so they can be integrated with that challenge tree. See [THIRD_PARTY_NOTICES.md](THIRD_PARTY_NOTICES.md).
