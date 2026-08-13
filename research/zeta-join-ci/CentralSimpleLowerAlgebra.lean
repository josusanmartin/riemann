/-
Generic algebra for retaining a fixed central simple-zero density after
removing a guard set of little-o size.
-/
import Mathlib

open Filter Asymptotics

noncomputable section

namespace Zeta23.GapMatching.CentralSimpleLowerAlgebra

/-- If the global simple count is eventually at least `upper*N`, the central
count loses at most `guard`, and `guard=o(N)`, then every smaller coefficient
`lower<upper` is eventually retained centrally. -/
theorem eventually_central_lower
    (N globalSimple central guard : ℝ → ℝ)
    {lower upper : ℝ}
    (hgap : lower < upper)
    (hglobal : ∀ᶠ T in atTop,
      upper * N T ≤ globalSimple T)
    (hcentral : ∀ᶠ T in atTop,
      globalSimple T - guard T ≤ central T)
    (hguard : guard =o[atTop] N)
    (hN0 : ∀ᶠ T in atTop, 0 ≤ N T) :
    ∀ᶠ T in atTop, lower * N T ≤ central T := by
  have hdelta : 0 < upper - lower := sub_pos.mpr hgap
  have hguardBound : ∀ᶠ T in atTop,
      |guard T| ≤ (upper - lower) * |N T| :=
    (isLittleO_iff.1 hguard) (upper - lower) hdelta
  filter_upwards [hglobal, hcentral, hguardBound, hN0]
    with T hG hC hB hN
  rw [abs_of_nonneg hN] at hB
  have hguardUpper : guard T ≤ (upper - lower) * N T :=
    (le_abs_self _).trans hB
  nlinarith

/-- Numerical specialization used by the live proof. -/
theorem eventually_central_499
    (N globalSimple central guard : ℝ → ℝ)
    (hglobal : ∀ᶠ T in atTop,
      (0.4995 : ℝ) * N T ≤ globalSimple T)
    (hcentral : ∀ᶠ T in atTop,
      globalSimple T - guard T ≤ central T)
    (hguard : guard =o[atTop] N)
    (hN0 : ∀ᶠ T in atTop, 0 ≤ N T) :
    ∀ᶠ T in atTop, (0.499 : ℝ) * N T ≤ central T := by
  exact eventually_central_lower N globalSimple central guard
    (by norm_num) hglobal hcentral hguard hN0

end Zeta23.GapMatching.CentralSimpleLowerAlgebra
