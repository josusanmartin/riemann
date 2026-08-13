/-
Guarded finite/full Poisson error transferred to the real D-window Gram
overlap through the parameter-transparent identification.
-/
import Zeta23.GapMatching.GramToFinitePoisson

noncomputable section

namespace Zeta23.GapMatching.GramFiniteFullBound

open Zeta23
open Zeta23.AdmWindow
open Zeta23.GapMatching.DWindowGramIdentity
open Zeta23.GapMatching.DWindowFiniteGridApprox
open Zeta23.GapMatching.GramToFinitePoisson

variable {Z : ZeroConfig} {P : Params} {T : ℝ}

/-- Explicit finite/full bound for a pair of guarded simple atoms. -/
theorem abs_gramOverlap_sub_full_le
    (hreal : PhiHatReal T (P.atD T))
    (hc : 0 < dScale P T)
    {v : ℝ → ℝ} {L w c D : ℝ}
    (Hid : Identification (Z := Z) (P := P) (T := T) v L)
    (hW : AdmWindow v L w c)
    (ha : 0 < av v L)
    (hD : 0 < D)
    (z z' : dSimpleOnLine Z P T)
    (hleftZ : T + D ≤ atomOrdinate z)
    (hleftZ' : T + D ≤ atomOrdinate z')
    (hrightZ : atomOrdinate z + D
      ≤ T + ((P.atD T).d T) * (2 * Real.pi / L))
    (hrightZ' : atomOrdinate z' + D
      ≤ T + ((P.atD T).d T) * (2 * Real.pi / L)) :
    |gramOverlap z z' -
        normalizedFullOverlap v L (atomOrdinate z) (atomOrdinate z')|
      ≤ 2 * ((av v L * L ^ 2)⁻¹
        * rawTailMajorant c w D (2 * Real.pi / L)) := by
  rw [gramOverlap_eq_finiteNormalizedOverlap hreal hc v L Hid]
  exact finiteNormalizedOverlap_close hW ha hD
    hleftZ hleftZ' hrightZ hrightZ'

end Zeta23.GapMatching.GramFiniteFullBound
