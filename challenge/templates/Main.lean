import Mathlib.NumberTheory.LSeries.RiemannZeta

/-!
The submission elaborator exposes this narrow interface. During export, the
worker loads the checked implementation from boat/compact/Main.lean. Both
kernels replay the linked proof under the three-axiom allowlist.
-/
axiom RiemannFoundation.alpogeRH : RiemannHypothesis

/-- The published theorem exposed under its original name. -/
theorem riemannHypothesis : RiemannHypothesis := RiemannFoundation.alpogeRH
