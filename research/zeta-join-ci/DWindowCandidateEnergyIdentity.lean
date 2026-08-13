/-
Copyright (c) 2026.
SPDX-License-Identifier: Apache-2.0

Identification of the concrete path-candidate energy with squared real
D-window overlaps.
-/
import Zeta23.GapMatching.DWindowGramIdentity
import Zeta23.GapMatching.DistinctGapMatchingPipeline
import Zeta23.GapMatching.CanonicalOneBandPathD

open Matrix Finset RHLinalg
open scoped ComplexOrder BigOperators

noncomputable section

namespace Zeta23.GapMatching.DWindowCandidateEnergyIdentity

open Zeta23
open Zeta23.GzGp
open Zeta23.GapMatching.GapMatchingBlockSpecialization
open Zeta23.GapMatching.DistinctGapMatchingPipeline
open Zeta23.GapMatching.PathForestMatching
open Zeta23.GapMatching.DWindowGramIdentity
open Zeta23.GapMatching.CanonicalOneBandPathD

variable {Z : ZeroConfig} {P : Params} {T : ℝ}

/-- The full complex inner product is the real finite Fourier overlap. -/
theorem inner_dSimpleVector_eq_finFourierOverlap
    (hreal : PhiHatReal T (P.atD T))
    (hc : 0 < dScale P T)
    (z z' : dSimpleOnLine Z P T) :
    inner (dSimpleVector Z P T z) (dSimpleVector Z P T z')
      = (finFourierOverlap z z' : ℂ) := by
  rw [PiLp.inner_apply]
  apply Complex.ext
  · rw [map_sum]
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
  · rw [map_sum]
    apply Finset.sum_eq_zero
    intro k hk
    rw [RCLike.inner_apply]
    simp_rw [dSimpleVector_apply hreal]
    simp

/-- Unit-weight `Wmat` Gram entries are ordinary inner products. -/
theorem unitWmat_gram_apply
    {ι d : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype d] [DecidableEq d]
    (v : ι → d → ℂ) (i j : ι) :
    ((Wmat (fun _ : ι => (1 : ℝ)) v)ᴴ *
        Wmat (fun _ : ι => (1 : ℝ)) v) i j
      = inner (v i) (v j) := by
  simp [Wmat, Matrix.mul_apply, PiLp.inner_apply,
    RCLike.inner_apply]

/-- Embedded candidate energy is the square of the real overlap on its two
path endpoints. -/
theorem embeddedCandidateEdgeEnergy_eq_gramOverlap_sq
    (hreal : PhiHatReal T (P.atD T))
    (hc : 0 < dScale P T)
    {n : ℕ} (short : ℕ → Bool)
    (vertices : Fin (n + 2) ↪ dSimpleOnLine Z P T)
    (i : Fin n) :
    embeddedCandidateEdgeEnergy short vertices
        (dSimpleVector Z P T) i
      = gramOverlap
          (vertices (leftVertex i))
          (vertices (rightVertex short i)) ^ 2 := by
  unfold embeddedCandidateEdgeEnergy gramOverlap
  rw [unitWmat_gram_apply]
  rw [inner_dSimpleVector_eq_finFourierOverlap hreal hc]
  simp [Complex.norm_real, sq_abs]

end Zeta23.GapMatching.DWindowCandidateEnergyIdentity
