# Compact RH foundation

Policy v3 uses Lean 4.35.0, Zeta23 and the compact proof from lsernau/grh-lean. The contract pins the upstream revisions, Mathlib manifest and official compiler release. The worker checks a SHA-256 for every part of its runtime before any submitted code runs.

The submission imports the existing Main interface. At export, the worker loads the proven implementation of RiemannFoundation.alpogeRH from boat/compact/Main.lean. This keeps the compact library’s tactic and notation extensions out of the submitted source. The submitted module is handled in an isolated account in both phases. A separate account operates on immutable kernel data. It compares the trusted RH statement, strict improvement and both counting statements, audits their axiom dependencies, and checks the same solution bytes with nanoda and the Lean kernel. Each new receipt includes the reference and solution SHA-256 values.

Earlier receipts retain the verification policy in force when the record was admitted. The 85.4225% record also has a separately published compact replay.

[Pinned foundation](https://github.com/lsernau/grh-lean/tree/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact) · [Independent checks](https://math.mit.edu/~drew/shortgrh/)
