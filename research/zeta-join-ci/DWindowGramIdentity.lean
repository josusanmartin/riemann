/-
Copyright (c) 2026.
SPDX-License-Identifier: Apache-2.0

Exact identification of the normalized D-window evaluation vectors with the
real Fourier samples used by the finite-grid Poisson comparison.
-/
import Zeta23.GapMatching.TwoBandGapMatchingDPath
import Zeta23.GapMatching.DWindowFiniteGridApprox
import Zeta23.ThmD.ParamsD

open Matrix Finset RHLinalg
open scoped ComplexOrder BigOperators

noncomputable section

namespace Zeta23.GapMatching.DWindowGramIdentity

open Zeta23
open Zeta23.ZeroSide
open Zeta23.GzGp
open Zeta23.GapMatching.GapMatchingBlockSpecialization
open Zeta23.GapMatching.TwoBandGapMatchingDPath
open Zeta23.GapMatching.DWindowFiniteGridApprox

variable {Z : ZeroConfig} {P : Params} {T : ℝ}

/-- Ordinate of a simple on-line atom in the D-window block. -/
def atomOrdinate (z : dSimpleOnLine Z P T) : ℝ :=
  (((z.1.1 : ZeroSide.ZI Z T) : ℂ)).im

/-- Each normalized evaluation-vector coordinate is the corresponding real
Fourier sample divided by the square-root Gram scale. -/
theorem dSimpleVector_apply
    (hreal : PhiHatReal T (P.atD T))
    (z : dSimpleOnLine Z P T)
    (k : Fin ((P.atD T).d T)) :
    dSimpleVector Z P T z k =
      ((P.atD T).phiHatR T
          (atomOrdinate z - (P.atD T).tau T k) : ℂ)
        / (Real.sqrt (dScale P T) : ℂ) := by
  have hz' :
      (((z.1.1 : ZeroSide.ZI Z T) : ℂ)).re = 1 / 2 := by
    exact (mkData_σ_eq_iff Z T _ _ z.1.1).mp z.1.2
  simp only [dSimpleVector, simpleVhat, ZeroBlockData.vhat,
    dBlock, blockData, mkData_v, evalVec, atomOrdinate]
  rw [gammaOf_of_re_eq_half hz', ← Complex.ofReal_sub, hreal]

/-- The real part of the normalized Gram overlap, before rewriting the finite
`Fin` sum as an integer-grid block. -/
def gramOverlap
    (z z' : dSimpleOnLine Z P T) : ℝ :=
  RCLike.re (inner
    (dSimpleVector Z P T z)
    (dSimpleVector Z P T z'))

/-- Explicit finite real Fourier sum on the `Fin d` grid. -/
def finFourierOverlap
    (z z' : dSimpleOnLine Z P T) : ℝ :=
  (dScale P T)⁻¹ *
    ∑ k : Fin ((P.atD T).d T),
      (P.atD T).phiHatR T
          (atomOrdinate z - (P.atD T).tau T k)
        * (P.atD T).phiHatR T
          (atomOrdinate z' - (P.atD T).tau T k)

/-- Exact Gram/sampled-Fourier identity. -/
theorem gramOverlap_eq_finFourierOverlap
    (hreal : PhiHatReal T (P.atD T))
    (hc : 0 < dScale P T)
    (z z' : dSimpleOnLine Z P T) :
    gramOverlap z z' = finFourierOverlap z z' := by
  unfold gramOverlap finFourierOverlap
  rw [PiLp.inner_apply, map_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [RCLike.inner_apply]
  simp_rw [dSimpleVector_apply hreal]
  have hsqrt : Real.sqrt (dScale P T) ^ 2 = dScale P T :=
    Real.sq_sqrt hc.le
  simp only [map_div₀, Complex.conj_ofReal,
    Complex.conj_div, Complex.ofReal_mul, Complex.ofReal_re]
  push_cast
  field_simp [hc.ne', Real.sqrt_pos.2 hc, hsqrt]
  ring

end Zeta23.GapMatching.DWindowGramIdentity
