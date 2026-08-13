/-
Copyright (c) 2026.
SPDX-License-Identifier: Apache-2.0

Exact identification of normalized D-window evaluation vectors with the real
Fourier samples used by the finite-grid Poisson comparison.  This module is
intentionally independent of the later fixed-point seam.
-/
import Zeta23.GapMatching.GapMatchingBlockSpecialization
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
open Zeta23.GapMatching.DWindowFiniteGridApprox

variable {Z : ZeroConfig} {P : Params} {T : ℝ}

/-- Canonical Fourier-conjugation proof for the D-window at height `T`. -/
def gramConj (P : Params) (T : ℝ) : PhiHatConj T (P.atD T) :=
  fun z => GzGp.phiHat_conj (P.atD T) T z

/-- The actual D-window block, independent of any matching construction. -/
abbrev gramBlock (Z : ZeroConfig) (P : Params) (T : ℝ) :=
  blockData Z T (P.atD T) (gramConj P T)

/-- Simple critical-line atoms in the D-window block. -/
abbrev gramSimpleOnLine (Z : ZeroConfig) (P : Params) (T : ℝ) :=
  SimpleOnLine (gramBlock Z P T)

/-- D-window Gram normalization `a_D(T) L(T)^2`. -/
def gramScale (P : Params) (T : ℝ) : ℝ :=
  (P.atD T).a T * (P.atD T).L T ^ 2

/-- Their normalized evaluation vectors. -/
def gramSimpleVector (Z : ZeroConfig) (P : Params) (T : ℝ) :
    gramSimpleOnLine Z P T → Fin ((P.atD T).d T) → ℂ :=
  simpleVhat (gramBlock Z P T) (gramScale P T)

/-- Ordinate of a simple on-line atom in the D-window block. -/
def atomOrdinate (z : gramSimpleOnLine Z P T) : ℝ :=
  (((z.1.1 : ZeroSide.ZI Z T) : ℂ)).im

/-- Each normalized evaluation-vector coordinate is the corresponding real
Fourier sample divided by the square-root Gram scale. -/
theorem gramSimpleVector_apply
    (hreal : PhiHatReal T (P.atD T))
    (z : gramSimpleOnLine Z P T)
    (k : Fin ((P.atD T).d T)) :
    gramSimpleVector Z P T z k =
      ((P.atD T).phiHatR T
          (atomOrdinate z - (P.atD T).tau T k) : ℂ)
        / (Real.sqrt (gramScale P T) : ℂ) := by
  have hz' :
      (((z.1.1 : ZeroSide.ZI Z T) : ℂ)).re = 1 / 2 := by
    exact (mkData_σ_eq_iff Z T _ _ z.1.1).mp z.1.2
  simp only [gramSimpleVector, simpleVhat, ZeroBlockData.vhat,
    gramBlock, blockData, mkData_v, evalVec, atomOrdinate, gramScale]
  rw [gammaOf_of_re_eq_half hz', ← Complex.ofReal_sub, hreal]

/-- The real part of the normalized Gram overlap. -/
def gramOverlap
    (z z' : gramSimpleOnLine Z P T) : ℝ :=
  RCLike.re (inner
    (gramSimpleVector Z P T z)
    (gramSimpleVector Z P T z'))

/-- Explicit finite real Fourier sum on the `Fin d` grid. -/
def finFourierOverlap
    (z z' : gramSimpleOnLine Z P T) : ℝ :=
  (gramScale P T)⁻¹ *
    ∑ k : Fin ((P.atD T).d T),
      (P.atD T).phiHatR T
          (atomOrdinate z - (P.atD T).tau T k)
        * (P.atD T).phiHatR T
          (atomOrdinate z' - (P.atD T).tau T k)

/-- Exact Gram/sampled-Fourier identity. -/
theorem gramOverlap_eq_finFourierOverlap
    (hreal : PhiHatReal T (P.atD T))
    (hc : 0 < gramScale P T)
    (z z' : gramSimpleOnLine Z P T) :
    gramOverlap z z' = finFourierOverlap z z' := by
  unfold gramOverlap finFourierOverlap
  rw [PiLp.inner_apply, map_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [RCLike.inner_apply]
  simp_rw [gramSimpleVector_apply hreal]
  have hsqrt : Real.sqrt (gramScale P T) ^ 2 = gramScale P T :=
    Real.sq_sqrt hc.le
  simp only [map_div₀, Complex.conj_ofReal,
    Complex.conj_div, Complex.ofReal_mul, Complex.ofReal_re]
  push_cast
  field_simp [hc.ne', Real.sqrt_pos.2 hc, hsqrt]
  ring

end Zeta23.GapMatching.DWindowGramIdentity
