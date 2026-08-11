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

## Submission layout

```text
submissions/<id>/
├── submission.json
└── proof/
    ├── Solution.lean
    └── AdditionalLemma.lean
```

Use `submissions/example/submission.json` as the manifest template. Scores are positive integers encoded as strings:

```json
"score": {
  "numerator": "672500704",
  "denominator": "1000000000"
}
```

Floating-point scores are rejected. The dashboard decimal is derived from the exact rational.

`author.github` must match the GitHub account that opens the pull request. Both verification stages obtain that identity from GitHub rather than trusting the manifest alone; `author.displayName` may name the individual or research team credited in the ledger.

Additional files under `proof/` must be Lean source files no larger than 2 MB each. They are copied under the `Candidate` module namespace, so `proof/AdditionalLemma.lean` is imported as `Candidate.AdditionalLemma`.

## Pull-request scope

A record PR may add one new submission directory only. It may not modify:

- `challenge/contract.json` or the generated theorem templates;
- existing record data;
- package or Lean lockfiles;
- verifier scripts or workflows;
- the pinned Zeta23, Mathlib, Comparator, landrun, or nanoda commits.

Infrastructure changes belong in separate PRs and never receive a formal score.

## Acceptance

A submission becomes a formal record when all of the following hold automatically:

1. Its manifest and PR scope validate.
2. Comparator proves exact equality with the trusted generated statements.
3. Its transitive axiom set is exactly a subset of `propext`, `Quot.sound`, and `Classical.choice`.
4. Lean accepts the exported proof.
5. The independent nanoda kernel accepts the proof.
6. `candidate_strict_improvement` proves the rational exceeds the exact current record.
7. Both dyadic and cumulative critical-line theorems pass.

Human review is welcome but is not a formal-record prerequisite. A result without a complete machine proof may be discussed in an issue, but it cannot change the displayed record.

## Optional independent review

After formal acceptance, a maintainer may attach an `independentReview` entry to the trusted ledger when a public review identifies its reviewer, date, evidence URL, and summary. The dashboard renders that as a separate **Expert reviewed** badge. It is never read by the score comparator or promotion decision, and the default for every machine-promoted record is `null`.

Review metadata belongs in a separate infrastructure pull request. It must not be included in a scored submission PR.

## Security

Lean elaboration executes contributor-controlled metaprograms. Never run an unfamiliar proof directly on a workstation with credentials. Authoritative CI runs without repository secrets or network access in a resource-limited sandbox. See [SECURITY.md](SECURITY.md).
