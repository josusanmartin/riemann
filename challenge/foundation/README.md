# Published RH foundation

Policy v2 accepts Alpöge’s published Lean theorem `riemannHypothesis : RiemannHypothesis` as an external foundation. Each user can import `Main`. Its compact interface in `challenge/templates/Main.lean` represents the external proof by one explicitly permitted axiom, `RiemannFoundation.alpogeRH : RiemannHypothesis`. The verifier's own reference declarations import the same interface. Comparator compares allowed axioms, including their types and referenced definitions, against that reference; Lean and nanoda replay the submitted derivation. The upstream proof body is outside the per-job replay.

The contract pins the RH source commit and tree, the release's dependency manifest, and the public reference and solution export hashes. The included Lake manifest is byte-identical to the RH release at the pinned revision. Zeta23 uses its original theorem sources with that Lean and Mathlib configuration. A policy-v2 record includes the RH commit and is labeled “RH foundation” even if the submission did not need the optional theorem.

[Alpöge's release](https://github.com/leanprover-community/riemann-hypothesis/tree/2f097b744a6460c73f3e4cc550baa83698409876) · [Independent checks and exports](https://math.mit.edu/~drew/grh/)
