/-
Copyright (c) 2026.
SPDX-License-Identifier: Apache-2.0

Exact real Fourier representation of the normalized D-window Gram entry.
-/
import Zeta23.GapMatching.TwoBandGapMatchingDPath
import Zeta23.ThmD.ZeroSideD

noncomputable section

open Matrix Finset Real
open scoped BigOperators ComplexOrder

namespace Zeta23.GapMatching.DWindowGramIdentity

open Zeta23
open Zeta23.ZeroSide
open Zeta23.ZeroSide.RankTraceMult
open Zeta23.ThmD
open Zeta23.GapMatching.GapMatchingBlockSpecialization
open Zeta23.GapMatching.TwoBandGapMatchingDPath

variable {Z : ZeroConfig} {P : Params} {T : ℝ}

/-- The ordinate of one simple critical-line atom. -/
def atomOrdinate (z : dSimpleOnLine Z P T) : ℝ :=
  (((z.1.1 : ZeroSide.ZI Z T) : ℂ)).im

/-- Coordinate formula for the normalized simple-zero vector. -/
theorem dSimpleVector_apply
    (hreal : PhiHatReal T (P.atD T))
    (z : dSimpleOnLine Z P T)
    (k : Fin ((P.atD T).d T)) :
    dSimpleVector Z P T z k =
      ((P.atD T).phiHatR T
          (atomOrdinate z - (P.atD T).tau T k) : ℂ)
        / (Real.sqrt (dScale P T) : ℂ) := by
  have hzfixed : (dBlock Z P T).σ z.1.1 = z.1.1 :=
    ((dBlock Z P T).mem_onLine).mp z.1.2
  have hz' :
      (((z.1.1 : ZeroSide.ZI Z T) : ℂ)).re = 1 / 2 := by
    exact (mkData_σ_eq_iff Z T _ _ z.1.1).mp hzfixed
  simp only [dSimpleVector, simpleVhat, ZeroBlockData.vhat,
    dBlock, blockData, mkData_v, evalVec, atomOrdinate]
  rw [gammaOf_of_re_eq_half hz', ← Complex.ofReal_sub, hreal]

/-- Real finite Fourier overlap in the exact normalization of `dSimpleVector`. -/
def finFourierOverlap
    (z z' : dSimpleOnLine Z P T) : ℝ :=
  (dScale P T)⁻¹ *
    ∑ k : Fin ((P.atD T).d T),
      (P.atD T).phiHatR T
          (atomOrdinate z - (P.atD T).tau T k)
        * (P.atD T).phiHatR T
          (atomOrdinate z' - (P.atD T).tau T k)

/-- The finite Gram sum is the real finite Fourier overlap. -/
theorem gramSum_eq_finFourierOverlap
    (hreal : PhiHatReal T (P.atD T))
    (hc : 0 < dScale P T)
    (z z' : dSimpleOnLine Z P T) :
    (∑ k : Fin ((P.atD T).d T),
      starRingEnd ℂ (dSimpleVector Z P T z k) *
        dSimpleVector Z P T z' k)
      = (finFourierOverlap z z' : ℂ) := by
  unfold finFourierOverlap
  push_cast
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  try rw [RCLike.inner_apply]
  simp_rw [dSimpleVector_apply hreal]
  have hsqrt : Real.sqrt (dScale P T) ^ 2 = dScale P T :=
    Real.sq_sqrt hc.le
  simp only [map_div₀, Complex.conj_ofReal,
    Complex.conj_div, Complex.ofReal_mul]
  push_cast
  field_simp [hc.ne', Real.sqrt_pos.2 hc, hsqrt]
  ring

end Zeta23.GapMatching.DWindowGramIdentity
