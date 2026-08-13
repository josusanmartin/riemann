/-
Parameter-transparent bridge from the D-window Gram Fourier sum to the generic
finite Poisson block.
-/
import Zeta23.GapMatching.DWindowGramIdentity
import Zeta23.GapMatching.DWindowFiniteGridApprox

noncomputable section

namespace Zeta23.GapMatching.GramToFinitePoisson

open Zeta23
open Zeta23.GapMatching.DWindowGramIdentity
open Zeta23.GapMatching.DWindowFiniteGridApprox

variable {Z : ZeroConfig} {P : Params} {T : ℝ}

/-- Three definitional identities needed to recognize the generic finite
Poisson block inside the D-window Gram sum. -/
structure Identification
    (v : ℝ → ℝ) (L : ℝ) : Prop where
  sample : ∀ x, (P.atD T).phiHatR T x = AdmWindow.vHatR v x
  grid : ∀ k : Fin ((P.atD T).d T),
    (P.atD T).tau T k = T + (k : ℝ) * (2 * Real.pi / L)
  scale : dScale P T = AdmWindow.av v L * L ^ 2

/-- The explicit `Fin` Fourier sum is the generic integer finite block. -/
theorem finFourierOverlap_eq_finiteNormalizedOverlap
    (v : ℝ → ℝ) (L : ℝ)
    (H : Identification (Z := Z) (P := P) (T := T) v L)
    (z z' : dSimpleOnLine Z P T) :
    finFourierOverlap z z' =
      finiteNormalizedOverlap v L T ((P.atD T).d T)
        (atomOrdinate z) (atomOrdinate z') := by
  unfold finFourierOverlap finiteNormalizedOverlap
  unfold FiniteBlockApproximation.finiteBlock normalizedTerm
  rw [H.scale]
  simp_rw [H.sample, H.grid]
  exact?

/-- Gram overlap equals the generic finite Poisson block. -/
theorem gramOverlap_eq_finiteNormalizedOverlap
    (hreal : PhiHatReal T (P.atD T))
    (hc : 0 < dScale P T)
    (v : ℝ → ℝ) (L : ℝ)
    (H : Identification (Z := Z) (P := P) (T := T) v L)
    (z z' : dSimpleOnLine Z P T) :
    gramOverlap z z' =
      finiteNormalizedOverlap v L T ((P.atD T).d T)
        (atomOrdinate z) (atomOrdinate z') := by
  rw [gramOverlap_eq_finFourierOverlap hreal hc]
  exact finFourierOverlap_eq_finiteNormalizedOverlap v L H z z'

end Zeta23.GapMatching.GramToFinitePoisson
