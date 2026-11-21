# Third-party notices

Riemann.fail interoperates with, but does not vendor, the following projects:

- **Zeta23**, Anthropic, PBC — Apache License 2.0. The verifier checks out commit `3635e74826a4c1fcece7d1cd2b6fa75e43a00510` from <https://github.com/anthropics/zeta-23-lean>.
- **Mathlib** — Apache License 2.0. The joint verifier pins commit `0df444a360eaa60ab8c11dca51a86af692955474` from the RH release.
- **Lean Comparator**, Lean FRO — see <https://github.com/leanprover/comparator> for its license and notices.
- **landrun** and **nanoda** — used by the isolated verification environment; see their upstream repositories for licenses and notices.

The historical summaries and mathematical notation on the website are original summaries linked to their primary sources.

- **RH foundation** — Levent Alpöge’s published proof, pinned in `challenge/contract.json`. The verifier exposes its Mathlib statement as a trusted external premise. [Source and verification](https://math.mit.edu/~drew/grh/).
