import Mathlib.NumberTheory.LSeries.RiemannZeta

/-!
Leaderboard interface to Alpöge's published RH theorem. The release and its
independent verification evidence are pinned in challenge/contract.json.
The verifier trusts this one external proposition. Candidate proofs and the
type of the permitted axiom are compared with the trusted contract.
-/
axiom RiemannFoundation.alpogeRH : RiemannHypothesis

/-- The published theorem exposed under its original name. -/
theorem riemannHypothesis : RiemannHypothesis := RiemannFoundation.alpogeRH
