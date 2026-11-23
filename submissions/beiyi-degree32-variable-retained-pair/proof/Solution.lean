/-
Apache-2.0 §4(b) change notice. 贝奕 (Bei Yi), 2026-11-23 UTC+08:00.
T052 replaces the fixed per-triple payment with a gap-dependent two-tier
retained-pair payment. Disjoint residue classes are selected by total payment,
and an affine bound carries the payment through Gram and zero counting.
Michael Devine's degree-32 window, retained-pair framework and prior attribution
are retained below, including Kristian Muri Knausgård's third-moment framework.
SPDX-License-Identifier: Apache-2.0
-/
/-
Michael Devine <mike@circumjovial.com>. Further retained-pair refinement of Bei Yi's octic-window proof, using the shifted-cubic method of Kristian Muri Knausgård. New degree-32 window, longer triple span, revised Fourier overlap, Taylor enclosures and shift. Numerical and Lean assistance from OpenAI GPT-6.2 Astra. Original credits below. SPDX-License-Identifier: Apache-2.0

Author's note (Michael Devine): I welcome extensions of this work. I object to leaderboard
submissions whose only change is a minor retuning of the shift or window coefficients.
If you build on this proof, please credit the earlier work and say exactly what you changed.
-/
/-
Retained pair energy and distinct critical-line zeros under RH

Copyright (c) 2026 Michael Devine <mike@circumjovial.com> (retained-pair extension).
Models used for this extension: GPT-6.2 Astra and Claude Opus 5.5.
This extension builds on Kristian Muri Knausgård's quartic-window proof.
SPDX-License-Identifier: Apache-2.0
-/

import ChallengeDeps.CandidateSpec
import Zeta23.Statement.SeamClosed
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.Complex.Order
import Mathlib.Data.Complex.BigOperators
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Data.Set.Card
import Mathlib.Tactic
import Zeta23.Final
import Mathlib.Analysis.Fourier.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Zeta23.Poisson.PaperFT
import Zeta23.FromPNTPlus.Fourier
import Mathlib.Topology.ContinuousMap.Weierstrass
import Mathlib.Analysis.Calculus.ContDiff.Polynomial
import Main
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Sort

section Src_Devine_KnausgardTraceBase


















/-
Candidate 504678117694414992253315078804551328482467/598826272881181027171250673799386945725202 = 0.8427788501... (Kristian Muri Knausgård, 22 November 2026).

Under the Riemann hypothesis the third moment of the multiplicities of the zeta zeros is bounded:
for every bounded window g >= 0 on [-1/2, 1/2] with integral 1 and every t >= 0, the sum of m (m - t)_+^2 over
the distinct zeros in (T, 2T] is at most (C3(g) - 2 t C2(g) + t^2 + o(1)) N(T, 2T), with C2, C3 the second and
third trace constants of g.  Hence N_d >= (1 - K_t/(2 (2-t)^2) - o(1)) N.  Here: the window v(u) = 1 - (14768021/10000000)u^2 + (5894147/5000000)u^4 on [-1/2, 1/2], normalised (the quartic window that is optimal for this bound, to 6e-18), at the exact optimal shift t = (4 C2 - 2 C3)/(4 - 2 C2),
which gives 504678117694414992253315078804551328482467/598826272881181027171250673799386945725202; under RH every zero is on the line, so N0star = N_d.

The proof is formalised here from Mathlib's `RiemannHypothesis` and the library Zeta23 (explicit formula,
Riemann-von Mangoldt, Gamma estimates, Chebyshev-Mertens): kernel identity, Gram matrix of the zeros,
second and third traces by exact matching of prime packets, height weights by convolution.
Paper (not published yet, draft title): K. M. Knausgård, "Distinct zeros of the Riemann zeta function and the third moment of multiplicities"
(the cubic certificate is due to Alpöge and Furman, arXiv:2608.13637, Section 7.3; the shifted form appears in
J. San Martin's note of 21 November 2026; the packet method follows rStation paper 155).
Drafted with Claude (Anthropic).  SPDX-License-Identifier: Apache-2.0
-/

section Src_ThirdMoment
/-
Written for Kristian Muri Knausgård, drafted with Claude (Anthropic), 22 November 2026.

ThirdMoment.lean — distinct zeros of the Riemann zeta function from the third moment of multiplicities.

Content (everything is checked by the Lean kernel; no `sorry`, no extra axioms):
  1. the weight Φ_t(x) = x (x - t)_+^2 and the integer inequality
       m - 1 ≤ A_t m + B_t Φ_t(m)   (m ≥ 2 a natural number, 1 ≤ t < 2),
     with B_t = 1/(6(5 - 2t)), A_t = 1/2 - B_t (2 - t)^2;
  2. for a positive semidefinite complex matrix W:  Σ_a Φ_t(W_aa) ≤ tr W^3 - 2t tr W^2 + t^2 tr W
     (a tangent-line argument for the cubic x (x - t)^2; the spectral theorem is not used);
  3. the counting inequality  A_t #{m = 1} + (1 - A_t) Σ m - B_t Σ Φ_t(m) ≤ #S  for a finite set with
     multiplicities m ≥ 1;
  4. the same for the nontrivial zeros of ζ in a window (definitions of `Zeta23` used verbatim), and the
     asymptotic forms on dyadic windows, the two analytic inputs (third-moment budget K, proportion s₀
     of simple zeros) being explicit hypotheses `Budget t K`, `SimpleLower s₀`;
  5. the exact rational value of the constant at t = 1037/1000, s₀ = 19/27 and the window constants
     C2w, C3w:  9206426916034466876368351 / 10819864495774716474708000 > 0.8508819.
-/

open scoped BigOperators ComplexOrder
open Matrix

noncomputable section

namespace ThirdMoment

/-! ## Definitions -/

/-- Φ_t(x) = x (x - t)_+^2 -/
def phi (t x : ℝ) : ℝ := x * (max (x - t) 0) ^ 2

/-- B_t = 1 / (6 (5 - 2t)) -/
def Bc (t : ℝ) : ℝ := 1 / (6 * (5 - 2 * t))

/-- A_t = 1/2 - B_t (2 - t)^2 -/
def Ac (t : ℝ) : ℝ := 1 / 2 - Bc t * (2 - t) ^ 2

/-! ## Part 1: elementary facts -/

theorem phi_nonneg {t x : ℝ} (hx : 0 ≤ x) : 0 ≤ phi t x :=
  mul_nonneg hx (sq_nonneg _)

/-- Φ_t is nondecreasing on [0, ∞). (The hypothesis `0 ≤ t` is not needed for the proof.) -/
theorem phi_mono {t x y : ℝ} (_ht : 0 ≤ t) (hx : 0 ≤ x) (hxy : x ≤ y) : phi t x ≤ phi t y := by
  unfold phi
  have h1 : max (x - t) 0 ≤ max (y - t) 0 := max_le_max (by linarith) le_rfl
  have h0 : 0 ≤ max (x - t) 0 := le_max_right _ _
  have h2 : (max (x - t) 0) ^ 2 ≤ (max (y - t) 0) ^ 2 := pow_le_pow_left₀ h0 h1 2
  exact mul_le_mul hxy h2 (sq_nonneg _) (hx.trans hxy)

theorem phi_one {t : ℝ} (ht : 1 ≤ t) : phi t 1 = 0 := by
  unfold phi
  rw [max_eq_right (by linarith)]
  norm_num

theorem phi_of_le {t x : ℝ} (h : t ≤ x) : phi t x = x * (x - t) ^ 2 := by
  unfold phi
  rw [max_eq_left (by linarith)]

theorem phi_of_ge {t x : ℝ} (h : x ≤ t) : phi t x = 0 := by
  unfold phi
  rw [max_eq_right (by linarith)]
  ring

theorem Bc_pos {t : ℝ} (ht2 : t < 2) : 0 < Bc t := by
  unfold Bc
  exact one_div_pos.mpr (by linarith)

theorem Bc_mul {t : ℝ} (ht2 : t < 2) : Bc t * (6 * (5 - 2 * t)) = 1 := by
  unfold Bc
  exact one_div_mul_cancel (ne_of_gt (by linarith))

theorem Bc_le {t : ℝ} (ht2 : t < 2) : Bc t ≤ 1 / 6 := by
  have h := Bc_mul ht2
  have hp := Bc_pos ht2
  nlinarith

/-- 1 - 2 A_t = 2 B_t (2 - t)^2 -/
theorem one_sub_two_Ac (t : ℝ) : 1 - 2 * Ac t = 2 * Bc t * (2 - t) ^ 2 := by
  unfold Ac
  ring

theorem Ac_le_half {t : ℝ} (ht2 : t < 2) : Ac t ≤ 1 / 2 := by
  have h := one_sub_two_Ac t
  have hp : 0 ≤ 2 * Bc t * (2 - t) ^ 2 := by
    have := Bc_pos ht2
    positivity
  linarith

theorem Ac_ge_third {t : ℝ} (ht1 : 1 ≤ t) (ht2 : t < 2) : 1 / 3 ≤ Ac t := by
  have h := one_sub_two_Ac t
  have hB := Bc_le ht2
  have hp := Bc_pos ht2
  have hsq : (2 - t) ^ 2 ≤ 1 := by nlinarith
  have hsq0 : 0 ≤ (2 - t) ^ 2 := sq_nonneg _
  have : Bc t * (2 - t) ^ 2 ≤ 1 / 6 * 1 := mul_le_mul hB hsq hsq0 (by norm_num)
  linarith

/-- the integer inequality: m - 1 ≤ A_t m + B_t Φ_t(m) for natural numbers m ≥ 2 and 1 ≤ t < 2;
the difference is B_t (m - 2)(m - 3)(m + 5 - 2t). -/
theorem int_ineq {t : ℝ} (_ht1 : 1 ≤ t) (ht2 : t < 2) (m : ℕ) (hm : 2 ≤ m) :
    (m : ℝ) - 1 ≤ Ac t * m + Bc t * phi t m := by
  have hm' : (2 : ℝ) ≤ m := by exact_mod_cast hm
  rw [phi_of_le (by linarith)]
  have hB := Bc_mul ht2
  have hBpos := Bc_pos ht2
  have key : Ac t * m + Bc t * ((m : ℝ) * ((m : ℝ) - t) ^ 2) - ((m : ℝ) - 1)
      = Bc t * (((m : ℝ) - 2) * ((m : ℝ) - 3) * ((m : ℝ) + 5 - 2 * t)) := by
    unfold Ac
    linear_combination (((m : ℝ) - 2) / 2) * hB
  have h23 : 0 ≤ ((m : ℝ) - 2) * ((m : ℝ) - 3) := by
    rcases Nat.eq_or_lt_of_le hm with h | h
    · subst h
      norm_num
    · have h3 : (3 : ℝ) ≤ m := by exact_mod_cast h
      exact mul_nonneg (by linarith) (by linarith)
  have hnn : 0 ≤ Bc t * (((m : ℝ) - 2) * ((m : ℝ) - 3) * ((m : ℝ) + 5 - 2 * t)) :=
    mul_nonneg hBpos.le (mul_nonneg h23 (by linarith))
  linarith

/-- the pointwise inequality behind the counting bound -/
theorem pointwise {t : ℝ} (ht1 : 1 ≤ t) (ht2 : t < 2) (m : ℕ) (hm : 1 ≤ m) :
    Ac t * (if m = 1 then 1 else 0) + (1 - Ac t) * m - Bc t * phi t m ≤ 1 := by
  rcases Nat.eq_or_lt_of_le hm with h | h
  · subst h
    simp [phi_one ht1]
  · have hne : m ≠ 1 := by omega
    have h2 := int_ineq ht1 ht2 m h
    rw [if_neg hne]
    linarith

/-! ## Part 2: the positive-semidefinite matrix step -/

section Psd

/-- the cubic identity  x (x - s)^2 = (x - c)(x + 2c - 2s)(x - c) + (c - s)(3c - s)(x - c) + c (c - s)^2
in any complex algebra (the scalars are central). -/
theorem cubic_identity {A : Type*} [Ring A] [Algebra ℂ A] (x : A) (s c : ℂ) :
    x * (x - s • 1) * (x - s • 1) =
      (x - c • 1) * (x + (2 * c - 2 * s) • 1) * (x - c • 1)
        + ((c - s) * (3 * c - s)) • (x - c • 1) + (c * (c - s) ^ 2) • 1 := by
  simp only [mul_sub, sub_mul, mul_add, add_mul, smul_mul_assoc, mul_smul_comm, mul_one, one_mul,
    smul_sub, smul_add, smul_smul, mul_assoc]
  module

/-- x (x - s)^2 = x^3 - 2s x^2 + s^2 x in any complex algebra. -/
theorem cubic_expand {A : Type*} [Ring A] [Algebra ℂ A] (x : A) (s : ℂ) :
    x * (x - s • 1) * (x - s • 1) = x ^ 3 - (2 * s) • x ^ 2 + (s ^ 2) • x := by
  simp only [mul_sub, sub_mul, smul_mul_assoc, mul_smul_comm, mul_one, one_mul,
    smul_sub, smul_smul, mul_assoc, pow_succ, pow_zero]
  module

/-- W - r·1 is Hermitian when W is and r is real. -/
theorem conjTranspose_sub_real {n : Type*} [DecidableEq n] {W : Matrix n n ℂ} (hW : W.IsHermitian)
    (r : ℝ) :
    (W - (r : ℂ) • (1 : Matrix n n ℂ))ᴴ = W - (r : ℂ) • (1 : Matrix n n ℂ) := by
  rw [conjTranspose_sub, conjTranspose_smul, conjTranspose_one, hW.eq]
  simp

/-- the real part of a diagonal entry of a positive semidefinite matrix is nonnegative. -/
theorem re_diag_nonneg {n : Type*} {M : Matrix n n ℂ} (hM : M.PosSemidef) (a : n) :
    0 ≤ (M a a).re :=
  (Complex.nonneg_iff.mp (hM.diag_nonneg (i := a))).1

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Φ_t of a diagonal entry of a positive semidefinite matrix is at most the diagonal entry of
W (W - t)^2. (The hypothesis `0 ≤ t` is not needed for the proof.) -/
theorem phi_diag_le {W : Matrix n n ℂ} {t : ℝ} (hW : W.PosSemidef) (_ht : 0 ≤ t) (a : n) :
    phi t (W a a).re ≤ ((W * (W - (t : ℂ) • 1) * (W - (t : ℂ) • 1)) a a).re := by
  have hdiag := Complex.nonneg_iff.mp (hW.diag_nonneg (i := a))
  have hWaa : W a a = (((W a a).re : ℝ) : ℂ) := by
    apply Complex.ext
    · simp
    · simpa using hdiag.2.symm
  generalize (W a a).re = c at hdiag hWaa ⊢
  have hc0 : 0 ≤ c := hdiag.1
  by_cases hct : c ≤ t
  · -- Φ_t(c) = 0 and W S S = Sᴴ W S is positive semidefinite
    rw [phi_of_ge hct]
    have hSH := conjTranspose_sub_real hW.isHermitian t
    have hcomm : W * (W - (t : ℂ) • (1 : Matrix n n ℂ)) = (W - (t : ℂ) • (1 : Matrix n n ℂ)) * W := by
      simp [mul_sub, sub_mul]
    have hpsd := hW.conjTranspose_mul_mul_same (W - (t : ℂ) • (1 : Matrix n n ℂ))
    rw [hSH, ← hcomm] at hpsd
    exact re_diag_nonneg hpsd a
  · -- tangent line at c
    have hct' : t < c := not_le.mp hct
    rw [phi_of_le hct'.le]
    have hDH := conjTranspose_sub_real hW.isHermitian c
    have hQpsd : (W + (2 * (c : ℂ) - 2 * (t : ℂ)) • (1 : Matrix n n ℂ)).PosSemidef := by
      refine hW.add ?_
      rw [smul_one_eq_diagonal]
      refine PosSemidef.diagonal fun i => ?_
      have h : (2 * (c : ℂ) - 2 * (t : ℂ)) = ((2 * c - 2 * t : ℝ) : ℂ) := by
        push_cast
        ring
      show (0 : ℂ) ≤ 2 * (c : ℂ) - 2 * (t : ℂ)
      rw [h]
      exact Complex.zero_le_real.mpr (by linarith)
    have hpsd := hQpsd.conjTranspose_mul_mul_same (W - (c : ℂ) • (1 : Matrix n n ℂ))
    rw [hDH] at hpsd
    have hnn := re_diag_nonneg hpsd a
    have hDaa : (W - (c : ℂ) • (1 : Matrix n n ℂ)) a a = 0 := by
      simp [hWaa]
    have hentry : (W * (W - (t : ℂ) • 1) * (W - (t : ℂ) • 1)) a a
        = ((W - (c : ℂ) • (1 : Matrix n n ℂ)) * (W + (2 * (c : ℂ) - 2 * (t : ℂ)) • (1 : Matrix n n ℂ))
            * (W - (c : ℂ) • (1 : Matrix n n ℂ))) a a + (c : ℂ) * ((c : ℂ) - (t : ℂ)) ^ 2 := by
      rw [cubic_identity W (t : ℂ) (c : ℂ), Matrix.add_apply, Matrix.add_apply, Matrix.smul_apply,
        Matrix.smul_apply, hDaa]
      simp
    have hre : ((c : ℂ) * ((c : ℂ) - (t : ℂ)) ^ 2).re = c * (c - t) ^ 2 := by
      have h : (c : ℂ) * ((c : ℂ) - (t : ℂ)) ^ 2 = ((c * (c - t) ^ 2 : ℝ) : ℂ) := by
        push_cast
        ring
      rw [h, Complex.ofReal_re]
    rw [hentry, Complex.add_re, hre]
    linarith

/-- Σ_a Φ_t(W_aa) ≤ tr W^3 - 2t tr W^2 + t^2 tr W for positive semidefinite W. -/
theorem sum_phi_diag_le {W : Matrix n n ℂ} {t : ℝ} (hW : W.PosSemidef) (ht : 0 ≤ t) :
    ∑ a, phi t (W a a).re
      ≤ (Matrix.trace (W ^ 3) - 2 * t * Matrix.trace (W ^ 2) + t ^ 2 * Matrix.trace W).re := by
  have h1 : ∑ a, phi t (W a a).re
      ≤ ∑ a, ((W * (W - (t : ℂ) • 1) * (W - (t : ℂ) • 1)) a a).re :=
    Finset.sum_le_sum fun a _ => phi_diag_le hW ht a
  have h2 : ∑ a, ((W * (W - (t : ℂ) • 1) * (W - (t : ℂ) • 1)) a a).re
      = (Matrix.trace (W * (W - (t : ℂ) • 1) * (W - (t : ℂ) • 1))).re := by
    rw [Matrix.trace, Complex.re_sum]
    rfl
  rw [h2, cubic_expand W (t : ℂ), trace_add, trace_sub, trace_smul, trace_smul, smul_eq_mul,
    smul_eq_mul] at h1
  exact h1

end Psd

/-! ## Part 3: counting for a finite set with multiplicities -/

theorem card_ge {α : Type*} (S : Finset α) (m : α → ℕ) (hm : ∀ ρ ∈ S, 1 ≤ m ρ) {t : ℝ}
    (ht1 : 1 ≤ t) (ht2 : t < 2) :
    Ac t * ((S.filter (fun ρ => m ρ = 1)).card : ℝ) + (1 - Ac t) * (∑ ρ ∈ S, (m ρ : ℝ))
        - Bc t * (∑ ρ ∈ S, phi t (m ρ))
      ≤ (S.card : ℝ) := by
  have h := Finset.sum_le_sum (fun ρ hρ => pointwise ht1 ht2 (m ρ) (hm ρ hρ))
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    ← Finset.mul_sum, Finset.sum_boole] at h
  simpa using h

/-! ## Part 4: the zeros of zeta -/

/-- Σ over the distinct zeros ρ in the window of Φ_t(m_ρ) -/
def phiSum (t T₁ T₂ : ℝ) : ℝ := ∑ᶠ ρ ∈ Zeta23.zerosIn T₁ T₂, phi t (Zeta23.zeroMult ρ)

/-- the window of zeros as a `Finset` -/
def zerosFinset (T₁ T₂ : ℝ) : Finset ℂ := (Zeta23.zerosIn_finite T₁ T₂).toFinset

theorem mem_zerosFinset {T₁ T₂ : ℝ} {ρ : ℂ} :
    ρ ∈ zerosFinset T₁ T₂ ↔ ρ ∈ Zeta23.zerosIn T₁ T₂ :=
  Set.Finite.mem_toFinset _

theorem coe_zerosFinset (T₁ T₂ : ℝ) : (zerosFinset T₁ T₂ : Set ℂ) = Zeta23.zerosIn T₁ T₂ :=
  Set.Finite.coe_toFinset _

theorem one_le_mult_of_mem {T₁ T₂ : ℝ} {ρ : ℂ} (hρ : ρ ∈ zerosFinset T₁ T₂) :
    1 ≤ Zeta23.zeroMult ρ :=
  Zeta23.zetaSeam.one_le_mult ρ (mem_zerosFinset.mp hρ).1

theorem phiSum_eq (t T₁ T₂ : ℝ) :
    phiSum t T₁ T₂ = ∑ ρ ∈ zerosFinset T₁ T₂, phi t (Zeta23.zeroMult ρ) :=
  finsum_mem_eq_finite_toFinset_sum _ (Zeta23.zerosIn_finite T₁ T₂)

theorem Ncount_eq (T₁ T₂ : ℝ) :
    (Zeta23.Ncount T₁ T₂ : ℝ) = ∑ ρ ∈ zerosFinset T₁ T₂, (Zeta23.zeroMult ρ : ℝ) := by
  unfold Zeta23.Ncount
  rw [finsum_mem_eq_finite_toFinset_sum _ (Zeta23.zerosIn_finite T₁ T₂), Nat.cast_sum]
  rfl

theorem Ndist_eq (T₁ T₂ : ℝ) : Zeta23.Ndist T₁ T₂ = (zerosFinset T₁ T₂).card := by
  unfold Zeta23.Ndist
  rw [← coe_zerosFinset, Set.ncard_coe_finset]

theorem Nsimple_eq (T₁ T₂ : ℝ) :
    Zeta23.Nsimple T₁ T₂ = ((zerosFinset T₁ T₂).filter (fun ρ => Zeta23.zeroMult ρ = 1)).card := by
  unfold Zeta23.Nsimple
  rw [← Set.ncard_coe_finset]
  congr 1
  ext ρ
  simp [mem_zerosFinset]

/-- exact finite inequality on any window -/
theorem window_ineq {t : ℝ} (ht1 : 1 ≤ t) (ht2 : t < 2) (T₁ T₂ : ℝ) :
    Ac t * (Zeta23.Nsimple T₁ T₂ : ℝ) + (1 - Ac t) * (Zeta23.Ncount T₁ T₂ : ℝ)
        - Bc t * phiSum t T₁ T₂
      ≤ (Zeta23.Ndist T₁ T₂ : ℝ) := by
  rw [Nsimple_eq, Ncount_eq, phiSum_eq, Ndist_eq]
  exact card_ge (zerosFinset T₁ T₂) Zeta23.zeroMult (fun ρ hρ => one_le_mult_of_mem hρ) ht1 ht2

/-- trivial upper bound  2 N_d ≤ N + N_s -/
theorem two_Ndist_le (T₁ T₂ : ℝ) :
    2 * (Zeta23.Ndist T₁ T₂ : ℝ) ≤ (Zeta23.Ncount T₁ T₂ : ℝ) + (Zeta23.Nsimple T₁ T₂ : ℝ) := by
  rw [Ndist_eq, Ncount_eq, Nsimple_eq]
  have h : ∀ ρ ∈ zerosFinset T₁ T₂,
      (2 : ℝ) ≤ (Zeta23.zeroMult ρ : ℝ) + (if Zeta23.zeroMult ρ = 1 then 1 else 0) := by
    intro ρ hρ
    have h1 := one_le_mult_of_mem hρ
    split_ifs with h
    · rw [h]
      norm_num
    · have h2 : 2 ≤ Zeta23.zeroMult ρ := by omega
      have h2' : (2 : ℝ) ≤ Zeta23.zeroMult ρ := by exact_mod_cast h2
      linarith
  have hsum := Finset.sum_le_sum h
  rw [Finset.sum_add_distrib, Finset.sum_boole, Finset.sum_const, nsmul_eq_mul] at hsum
  linarith

/-- (2 - t)^2 (N - N_s) ≤ Σ Φ_t(m_ρ): every zero of multiplicity m ≥ 2 has Φ_t(m) ≥ m (2 - t)^2. -/
theorem nonsimple_le_phiSum {t : ℝ} (ht1 : 1 ≤ t) (ht2 : t < 2) (T₁ T₂ : ℝ) :
    (2 - t) ^ 2 * ((Zeta23.Ncount T₁ T₂ : ℝ) - (Zeta23.Nsimple T₁ T₂ : ℝ)) ≤ phiSum t T₁ T₂ := by
  rw [Ncount_eq, Nsimple_eq, phiSum_eq]
  have h : ∀ ρ ∈ zerosFinset T₁ T₂,
      (2 - t) ^ 2 * ((Zeta23.zeroMult ρ : ℝ) - (if Zeta23.zeroMult ρ = 1 then 1 else 0))
        ≤ phi t (Zeta23.zeroMult ρ) := by
    intro ρ hρ
    have h1 := one_le_mult_of_mem hρ
    split_ifs with h
    · rw [h, Nat.cast_one, phi_one ht1]
      norm_num
    · have h2 : 2 ≤ Zeta23.zeroMult ρ := by omega
      have h2' : (2 : ℝ) ≤ Zeta23.zeroMult ρ := by exact_mod_cast h2
      rw [phi_of_le (by linarith), sub_zero, mul_comm]
      have hsq : (2 - t) ^ 2 ≤ ((Zeta23.zeroMult ρ : ℝ) - t) ^ 2 :=
        pow_le_pow_left₀ (by linarith) (by linarith) 2
      exact mul_le_mul_of_nonneg_left hsq (by linarith)
  have hsum := Finset.sum_le_sum h
  rw [← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_boole] at hsum
  exact hsum

/-- from a PSD matrix whose diagonal dominates the multiplicities on the window to the third-moment
budget -/
theorem phiSum_le_of_psd {n : Type*} [Fintype n] [DecidableEq n] {t : ℝ} (ht : 0 ≤ t) (T₁ T₂ : ℝ)
    (W : Matrix n n ℂ) (hW : W.PosSemidef) (f : ℂ → n) (hf : Set.InjOn f (Zeta23.zerosIn T₁ T₂))
    (hdiag : ∀ ρ ∈ Zeta23.zerosIn T₁ T₂, (Zeta23.zeroMult ρ : ℝ) ≤ (W (f ρ) (f ρ)).re) :
    phiSum t T₁ T₂
      ≤ (Matrix.trace (W ^ 3) - 2 * t * Matrix.trace (W ^ 2) + t ^ 2 * Matrix.trace W).re := by
  have hf' : Set.InjOn f (zerosFinset T₁ T₂ : Set ℂ) := by
    rw [coe_zerosFinset]
    exact hf
  calc phiSum t T₁ T₂
      = ∑ ρ ∈ zerosFinset T₁ T₂, phi t (Zeta23.zeroMult ρ) := phiSum_eq t T₁ T₂
    _ ≤ ∑ ρ ∈ zerosFinset T₁ T₂, phi t (W (f ρ) (f ρ)).re :=
        Finset.sum_le_sum fun ρ hρ =>
          phi_mono ht (Nat.cast_nonneg _) (hdiag ρ (mem_zerosFinset.mp hρ))
    _ = ∑ a ∈ (zerosFinset T₁ T₂).image f, phi t (W a a).re :=
        (Finset.sum_image (f := fun a => phi t (W a a).re) hf').symm
    _ ≤ ∑ a, phi t (W a a).re :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          fun a _ _ => phi_nonneg (re_diag_nonneg hW a)
    _ ≤ _ := sum_phi_diag_le hW ht

/-- hypothesis: third-moment budget with constant K on dyadic windows -/
def Budget (t K : ℝ) : Prop :=
  ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, phiSum t T (2 * T) ≤ (K + ε) * (Zeta23.Ncount T (2 * T) : ℝ)

/-- hypothesis: proportion s₀ of simple zeros on dyadic windows -/
def SimpleLower (s₀ : ℝ) : Prop :=
  ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
    (s₀ - ε) * (Zeta23.Ncount T (2 * T) : ℝ) ≤ (Zeta23.Nsimple T (2 * T) : ℝ)

/-- N_d ≥ (A_t s₀ + 1 - A_t - B_t K - o(1)) N from a third-moment budget and a proportion of simple
zeros. -/
theorem distinct_of_budget_simple {t K s₀ : ℝ} (ht1 : 1 ≤ t) (ht2 : t < 2) (hB : Budget t K)
    (hS : SimpleLower s₀) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (Ac t * s₀ + 1 - Ac t - Bc t * K - ε) * (Zeta23.Ncount T (2 * T) : ℝ)
        ≤ (Zeta23.Ndist T (2 * T) : ℝ) := by
  intro ε hε
  obtain ⟨Ta, ha⟩ := hB ε hε
  obtain ⟨Tb, hb⟩ := hS ε hε
  refine ⟨max Ta Tb, fun T hT => ?_⟩
  have hbud := ha T (le_trans (le_max_left _ _) hT)
  have hsim := hb T (le_trans (le_max_right _ _) hT)
  have hw := window_ineq ht1 ht2 T (2 * T)
  have hA0 : 0 ≤ Ac t := by
    have := Ac_ge_third ht1 ht2
    linarith
  have hB0 : 0 ≤ Bc t := (Bc_pos ht2).le
  have hAB : 0 ≤ 1 - Ac t - Bc t := by
    have h1 := Ac_le_half ht2
    have h2 := Bc_le ht2
    linarith
  have hN : (0 : ℝ) ≤ Zeta23.Ncount T (2 * T) := Nat.cast_nonneg _
  have e1 := mul_le_mul_of_nonneg_left hsim hA0
  have e2 := mul_le_mul_of_nonneg_left hbud hB0
  have e3 : 0 ≤ ε * (1 - Ac t - Bc t) * (Zeta23.Ncount T (2 * T) : ℝ) :=
    mul_nonneg (mul_nonneg hε.le hAB) hN
  nlinarith

/-- N_d ≥ (1 - K / (2 (2 - t)^2) - o(1)) N from a third-moment budget alone. -/
theorem distinct_of_budget {t K : ℝ} (ht1 : 1 ≤ t) (ht2 : t < 2) (hB : Budget t K) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (1 - K / (2 * (2 - t) ^ 2) - ε) * (Zeta23.Ncount T (2 * T) : ℝ)
        ≤ (Zeta23.Ndist T (2 * T) : ℝ) := by
  intro ε hε
  have hd : 0 < 2 * (2 - t) ^ 2 := by
    have : 0 < 2 - t := by linarith
    positivity
  obtain ⟨T₀, h₀⟩ := hB (ε * (2 * (2 - t) ^ 2)) (mul_pos hε hd)
  refine ⟨T₀, fun T hT => ?_⟩
  have hbud := h₀ T hT
  have hw := window_ineq ht1 ht2 T (2 * T)
  have h2 := two_Ndist_le T (2 * T)
  have hA := one_sub_two_Ac t
  have hBpos := Bc_pos ht2
  have hA0 : 0 ≤ Ac t := by
    have := Ac_ge_third ht1 ht2
    linarith
  -- (1 - 2 A) N_d ≥ (1 - 2 A) N - B Φ
  have e1 : (1 - 2 * Ac t) * (Zeta23.Ncount T (2 * T) : ℝ) - Bc t * phiSum t T (2 * T)
      ≤ (1 - 2 * Ac t) * (Zeta23.Ndist T (2 * T) : ℝ) := by
    have := mul_le_mul_of_nonneg_left h2 hA0
    nlinarith
  rw [hA] at e1
  -- divide by B_t
  have e2 : 2 * (2 - t) ^ 2 * (Zeta23.Ncount T (2 * T) : ℝ) - phiSum t T (2 * T)
      ≤ 2 * (2 - t) ^ 2 * (Zeta23.Ndist T (2 * T) : ℝ) := by
    by_contra hcon
    have hcon' := not_le.mp hcon
    have := mul_lt_mul_of_pos_left hcon' hBpos
    nlinarith
  have e3 : (2 * (2 - t) ^ 2) * ((1 - K / (2 * (2 - t) ^ 2) - ε) * (Zeta23.Ncount T (2 * T) : ℝ))
      = 2 * (2 - t) ^ 2 * (Zeta23.Ncount T (2 * T) : ℝ)
        - (K + ε * (2 * (2 - t) ^ 2)) * (Zeta23.Ncount T (2 * T) : ℝ) := by
    have hne : (2 : ℝ) - t ≠ 0 := ne_of_gt (by linarith)
    field_simp
    ring
  have e4 : (2 * (2 - t) ^ 2) * ((1 - K / (2 * (2 - t) ^ 2) - ε) * (Zeta23.Ncount T (2 * T) : ℝ))
      ≤ (2 * (2 - t) ^ 2) * (Zeta23.Ndist T (2 * T) : ℝ) := by
    rw [e3]
    linarith
  exact le_of_mul_le_mul_left e4 hd

/-- N_s ≥ (1 - K / (2 - t)^2 - o(1)) N from a third-moment budget alone. -/
theorem simple_of_budget {t K : ℝ} (ht1 : 1 ≤ t) (ht2 : t < 2) (hB : Budget t K) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (1 - K / (2 - t) ^ 2 - ε) * (Zeta23.Ncount T (2 * T) : ℝ)
        ≤ (Zeta23.Nsimple T (2 * T) : ℝ) := by
  intro ε hε
  have hd : 0 < (2 - t) ^ 2 := by
    have : 0 < 2 - t := by linarith
    positivity
  obtain ⟨T₀, h₀⟩ := hB (ε * (2 - t) ^ 2) (mul_pos hε hd)
  refine ⟨T₀, fun T hT => ?_⟩
  have hbud := h₀ T hT
  have hns := nonsimple_le_phiSum ht1 ht2 T (2 * T)
  have e3 : (2 - t) ^ 2 * ((1 - K / (2 - t) ^ 2 - ε) * (Zeta23.Ncount T (2 * T) : ℝ))
      = (2 - t) ^ 2 * (Zeta23.Ncount T (2 * T) : ℝ)
        - (K + ε * (2 - t) ^ 2) * (Zeta23.Ncount T (2 * T) : ℝ) := by
    have hne : (2 : ℝ) - t ≠ 0 := ne_of_gt (by linarith)
    field_simp
    ring
  have e4 : (2 - t) ^ 2 * ((1 - K / (2 - t) ^ 2 - ε) * (Zeta23.Ncount T (2 * T) : ℝ))
      ≤ (2 - t) ^ 2 * (Zeta23.Nsimple T (2 * T) : ℝ) := by
    rw [e3]
    linarith
  exact le_of_mul_le_mul_left e4 hd

/-- **Theorem 1.2, lower bound, on dyadic windows**, from the budget alone:
A_t N_s + (1 - A_t - B_t K - ε) N ≤ N_d. -/
theorem lower_of_budget {t K : ℝ} (ht1 : 1 ≤ t) (ht2 : t < 2) (hB : Budget t K) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      Ac t * (Zeta23.Nsimple T (2 * T) : ℝ)
          + (1 - Ac t - Bc t * K - ε) * (Zeta23.Ncount T (2 * T) : ℝ)
        ≤ (Zeta23.Ndist T (2 * T) : ℝ) := by
  intro ε hε
  obtain ⟨T₀, h₀⟩ := hB ε hε
  refine ⟨T₀, fun T hT => ?_⟩
  have h1 := window_ineq ht1 ht2 T (2 * T)
  have h2 := h₀ T hT
  have hB0 : 0 < Bc t := Bc_pos ht2
  have hB1 : Bc t ≤ 1 / 6 := Bc_le ht2
  have hN : (0 : ℝ) ≤ (Zeta23.Ncount T (2 * T) : ℝ) := Nat.cast_nonneg _
  have h3 : Bc t * phiSum t T (2 * T) ≤ Bc t * ((K + ε) * (Zeta23.Ncount T (2 * T) : ℝ)) :=
    mul_le_mul_of_nonneg_left h2 hB0.le
  have h4 : Bc t * (ε * (Zeta23.Ncount T (2 * T) : ℝ)) ≤ ε * (Zeta23.Ncount T (2 * T) : ℝ) :=
    mul_le_of_le_one_left (mul_nonneg hε.le hN) (by linarith)
  nlinarith [h1, h3, h4]

/-- the zeros of the window whose multiplicity is at least `j`, counted with multiplicity -/
def highMult (j : ℕ) (T₁ T₂ : ℝ) : ℝ :=
  ∑ᶠ ρ ∈ Zeta23.zerosIn T₁ T₂, (if j ≤ Zeta23.zeroMult ρ then (Zeta23.zeroMult ρ : ℝ) else 0)

theorem highMult_eq (j : ℕ) (T₁ T₂ : ℝ) :
    highMult j T₁ T₂
      = ∑ ρ ∈ zerosFinset T₁ T₂, (if j ≤ Zeta23.zeroMult ρ then (Zeta23.zeroMult ρ : ℝ) else 0) :=
  finsum_mem_eq_finite_toFinset_sum _ (Zeta23.zerosIn_finite T₁ T₂)

/-- (j - t)^2 · #{zeros of multiplicity ≥ j, with multiplicity} ≤ Σ Φ_t(m_ρ), for 0 ≤ t < j. -/
theorem highMult_le_phiSum {t : ℝ} (j : ℕ) (htj : t < j) (T₁ T₂ : ℝ) :
    ((j : ℝ) - t) ^ 2 * highMult j T₁ T₂ ≤ phiSum t T₁ T₂ := by
  rw [highMult_eq, phiSum_eq, Finset.mul_sum]
  refine Finset.sum_le_sum fun ρ _ => ?_
  split_ifs with h
  · have hj : (j : ℝ) ≤ (Zeta23.zeroMult ρ : ℝ) := by exact_mod_cast h
    rw [phi_of_le (by linarith), mul_comm]
    have hsq : ((j : ℝ) - t) ^ 2 ≤ ((Zeta23.zeroMult ρ : ℝ) - t) ^ 2 :=
      pow_le_pow_left₀ (by linarith) (by linarith) 2
    exact mul_le_mul_of_nonneg_left hsq (Nat.cast_nonneg _)
  · rw [mul_zero]
    exact phi_nonneg (Nat.cast_nonneg _)

/-- **Corollary 1.5 on dyadic windows**: zeros of multiplicity ≥ j carry at most
(K/(j - t)^2 + ε) N, from the budget. -/
theorem highMult_of_budget {t K : ℝ} (j : ℕ) (htj : t < j) (hB : Budget t K) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      highMult j T (2 * T) ≤ (K / ((j : ℝ) - t) ^ 2 + ε) * (Zeta23.Ncount T (2 * T) : ℝ) := by
  intro ε hε
  have hd : 0 < ((j : ℝ) - t) ^ 2 := by
    have : 0 < (j : ℝ) - t := by linarith
    positivity
  obtain ⟨T₀, h₀⟩ := hB (ε * ((j : ℝ) - t) ^ 2) (mul_pos hε hd)
  refine ⟨T₀, fun T hT => ?_⟩
  have hbud := h₀ T hT
  have hh := highMult_le_phiSum j htj T (2 * T)
  have e : ((j : ℝ) - t) ^ 2 * ((K / ((j : ℝ) - t) ^ 2 + ε) * (Zeta23.Ncount T (2 * T) : ℝ))
      = (K + ε * ((j : ℝ) - t) ^ 2) * (Zeta23.Ncount T (2 * T) : ℝ) := by
    have hne : (j : ℝ) - t ≠ 0 := ne_of_gt (by linarith)
    field_simp
  have e2 : ((j : ℝ) - t) ^ 2 * highMult j T (2 * T)
      ≤ ((j : ℝ) - t) ^ 2 * ((K / ((j : ℝ) - t) ^ 2 + ε) * (Zeta23.Ncount T (2 * T) : ℝ)) := by
    rw [e]
    linarith
  exact le_of_mul_le_mul_left e2 hd

/-! ## Part 5: the numbers -/

/-- C₂ of the window v = 1 - (743/500) u² + (1197/1000) u⁴ -/
def C2w : ℚ := 4677629393520 / 3522041957357

/-- C₃ of the window v = 1 - (743/500) u² + (1197/1000) u⁴ -/
def C3w : ℚ := 1484618890495233180 / 753262635461898947

theorem kappa_value :
    Ac (1037 / 1000) * (19 / 27) + 1 - Ac (1037 / 1000)
        - Bc (1037 / 1000) * ((C3w : ℝ) - 2 * (1037 / 1000) * (C2w : ℝ) + (1037 / 1000) ^ 2)
      = 9206426916034466876368351 / 10819864495774716474708000 := by
  unfold Ac Bc C2w C3w
  push_cast
  norm_num

theorem kappa_gt :
    (8508819 : ℝ) / 10 ^ 7 < 9206426916034466876368351 / 10819864495774716474708000 := by
  norm_num

/-- The final corollary: with the third-moment budget K = C₃ - 2 t C₂ + t² at t = 1037/1000 and the
proportion 19/27 of simple zeros, the proportion of distinct zeros on dyadic windows is at least
9206426916034466876368351 / 10819864495774716474708000 - o(1)  ( > 0.8508819 ). -/
theorem distinct_proportion
    (hB : Budget (1037 / 1000)
      ((C3w : ℝ) - 2 * (1037 / 1000) * (C2w : ℝ) + (1037 / 1000) ^ 2))
    (hS : SimpleLower (19 / 27)) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (9206426916034466876368351 / 10819864495774716474708000 - ε)
          * (Zeta23.Ncount T (2 * T) : ℝ)
        ≤ (Zeta23.Ndist T (2 * T) : ℝ) := by
  have h := distinct_of_budget_simple (t := 1037 / 1000) (by norm_num) (by norm_num) hB hS
  rw [kappa_value] at h
  exact h

end ThirdMoment

end
end Src_ThirdMoment

section Src_TMA_Basic
/-
Written for Kristian Muri Knausgård, drafted with Claude (Anthropic), 22 November 2026.

TMA/Basic.lean — definitions for the formal proof of the third-moment bound
(Theorem 1.1 of "Distinct zeros of the Riemann zeta function and the third moment of multiplicities").

Conventions (they differ from the paper by a change of scale; see BLUEPRINT.md):
* the window `gwin` lives on [-1/2, 1/2]; the bandwidth parameter `σ ∈ (0,1)` enters through the phases
  `exp (i σ (log T) γ x)`;
* `A = T σ log T`;  a packet with centre `lam` is `x ↦ T · k (-(A (x - lam)))`;
* the explicit formula of Zeta23 is `EF.EF_lit`:  Σ_ρ m_ρ (paperFT k)(γ_ρ) = literatureRHS k, with
  `paperFT k z = ∫ k(u) e^{izu} du`.
-/

open MeasureTheory Complex
open scoped BigOperators ArithmeticFunction Real

noncomputable section

namespace TMA

/-! ## The window -/

/-- parameter of the quadratic window -/
def alpha : ℝ := 4 / 3

/-- the window `g(u) = 1 + α (1/12 - u²)` on `[-1/2, 1/2]`, zero outside; `∫ g = 1`. -/
def gwin (u : ℝ) : ℝ := if |u| ≤ 1 / 2 then 1 + alpha * (1 / 12 - u ^ 2) else 0

/-- autocorrelation `a_g(r) = ∫ g(u) g(u+r) du` -/
def ag (r : ℝ) : ℝ := ∫ u, gwin u * gwin (u + r)

/-- triple correlation `G(r,s) = ∫ g(u) g(u+r) g(u+r+s) du` -/
def Gg (r s : ℝ) : ℝ := ∫ u, gwin u * gwin (u + r) * gwin (u + r + s)

/-- `b_g(s) = G(0,s) = ∫ g(u)² g(u+s) du` -/
def bg (s : ℝ) : ℝ := Gg 0 s

/-- `ĝ(x) = ∫ g(u) e^{ixu} du` -/
def ghat (x : ℝ) : ℂ := ∫ u, (gwin u : ℂ) * Complex.exp (Complex.I * x * u)

def I2 : ℝ := ag 0
def I3 : ℝ := Gg 0 0
def J2 : ℝ := 2 * ∫ r in (0 : ℝ)..1, r * ag r
def J3 : ℝ := ∫ r in (0 : ℝ)..1, r * (bg r + bg (-r))

/-- second-trace constant at bandwidth σ:  `C₂ = (1/σ) ∫g² + σ ∬ |u-v| g g` -/
def C2 (σ : ℝ) : ℝ := I2 / σ + σ * J2

/-- third-trace constant at bandwidth σ:  `C₃ = (1/σ²) ∫g³ + 3 ∬ |u-v| g² g` -/
def C3 (σ : ℝ) : ℝ := I3 / σ ^ 2 + 3 * J3

/-! ## Height weights -/

/-- `ω_T(x) = ½ log (x² + T⁻²)`, so that `log (T/2π) + ω_T(x) = ½ log (T²x² + 1) - log 2π`. -/
def omegaT (T x : ℝ) : ℝ := (1 / 2) * Real.log (x ^ 2 + 1 / T ^ 2)

/-- A height weight: a nonnegative function `h` on ℝ, at least 1 on `[1,2]`, vanishing at 0, whose
transform `k` (`paperFT k = h` on ℝ) is `C²` with compact support. The remaining fields are the
Fourier-inversion identities and the two regularity bounds used for the Gamma term. -/
structure HeightWeight where
  k : ℝ → ℂ
  h : ℝ → ℝ
  kappa : ℝ
  kappa_pos : 0 < kappa
  k_contDiff : ContDiff ℝ 2 k
  k_supp : ∀ u, k u ≠ 0 → |u| ≤ kappa
  h_eq : ∀ x : ℝ, Zeta23.paperFT k (x : ℂ) = (h x : ℂ)
  h_nonneg : ∀ x, 0 ≤ h x
  h_ge_one : ∀ x, 1 ≤ x → x ≤ 2 → 1 ≤ h x
  h_cont : Continuous h
  h_int : Integrable h
  /-- `h(0) = 0`, in the form `∫ k = 0` -/
  k_integral_zero : ∫ u, k u = 0
  /-- `h(x) ≤ B x²` near 0 -/
  h_small : ∃ B : ℝ, ∀ x, |x| ≤ 1 → h x ≤ B * x ^ 2
  /-- Fourier inversion: `(1/2π) ∫ h(s) e^{isy} ds = k(-y)` -/
  inv : ∀ y : ℝ, (1 / (2 * π) : ℂ) * ∫ s, (h s : ℂ) * Complex.exp (Complex.I * s * y) = k (-y)
  /-- Plancherel: `∫ |k|² = (1/2π) ∫ h²` -/
  inv2 : ∫ y, ‖k y‖ ^ 2 = (1 / (2 * π)) * ∫ x, h x ^ 2
  /-- `∬ k(y₁) k(y₂) k(-y₁-y₂) = (1/2π) ∫ h³` -/
  inv3 : ∫ y₁, ∫ y₂, k y₁ * k y₂ * k (-y₁ - y₂) = ((1 / (2 * π)) * ∫ x, h x ^ 3 : ℝ)
  /-- the transform of `h · ω_T` decays like `1/(1+y²)`, uniformly in `T ≥ 2` -/
  gammaBound : ∃ C : ℝ, ∀ T : ℝ, 2 ≤ T → ∀ y : ℝ,
    ‖(1 / (2 * π) : ℂ) * ∫ s, (h s : ℂ) * (omegaT T s : ℂ) * Complex.exp (Complex.I * s * y)‖
      ≤ C / (1 + y ^ 2)

namespace HeightWeight

/-- `κ_j = ∫ h^j` -/
def kap1 (w : HeightWeight) : ℝ := ∫ x, w.h x
def kap2 (w : HeightWeight) : ℝ := ∫ x, w.h x ^ 2
def kap3 (w : HeightWeight) : ℝ := ∫ x, w.h x ^ 3

end HeightWeight

/-! ## Kernels -/

/-- `A = T σ log T` -/
def Asc (T σ : ℝ) : ℝ := T * (σ * Real.log T)

/-- `D = T log T / 2π` -/
def Dsc (T : ℝ) : ℝ := T * Real.log T / (2 * π)

/-- the packet with centre `lam`:  `x ↦ T k(-(A (x - lam)))` -/
def packet (k : ℝ → ℂ) (T σ lam x : ℝ) : ℂ := (T : ℂ) * k (-(Asc T σ * (x - lam)))

/-- centre of the packets of the integer `n`:  `log n / (σ log T)` -/
def lamOf (T σ : ℝ) (n : ℕ) : ℝ := Real.log n / (σ * Real.log T)

/-- the integers that can occur for `|x| ≤ 1`:  `n ≤ 2 T^σ` -/
def Nmax (T σ : ℝ) : ℕ := ⌊2 * T ^ σ⌋₊

/-- coefficient `Λ(n)/√n` -/
def lamCoeff (n : ℕ) : ℝ := Λ n / Real.sqrt n

/-- the prime-side kernel: the packet at 0 with weight `log (T/2π)` and the packets at `±log n/(σ log T)`
with weights `-Λ(n)/√n`. -/
def K0 (k : ℝ → ℂ) (T σ x : ℝ) : ℂ :=
  (Real.log (T / (2 * π)) : ℂ) * packet k T σ 0 x
    - ∑ n ∈ Finset.Icc 2 (Nmax T σ),
        (lamCoeff n : ℂ) * (packet k T σ (lamOf T σ n) x + packet k T σ (-(lamOf T σ n)) x)

/-- weight of a zero: `m_ρ h(γ_ρ / T)` -/
def cw (h : ℝ → ℝ) (T : ℝ) (ρ : ℂ) : ℝ := (Zeta23.zeroMult ρ : ℝ) * h (ρ.im / T)

/-- phase of a zero at `x`:  `exp (i σ (log T) γ x)` -/
def phase (T σ : ℝ) (ρ : ℂ) (x : ℝ) : ℂ :=
  Complex.exp (Complex.I * ((σ * Real.log T * ρ.im * x : ℝ) : ℂ))

/-- the zero-side kernel `K_T(x) = Σ_ρ m_ρ h(γ_ρ/T) e^{i σ (log T) γ_ρ x}` over all nontrivial zeros -/
def Kfull (h : ℝ → ℝ) (T σ x : ℝ) : ℂ :=
  ∑' ρ : Zeta23.zetaZeroConfig.carrier, (cw h T ρ : ℂ) * phase T σ ρ x

/-- the same kernel over a finite set of zeros -/
def Kfin (h : ℝ → ℝ) (T σ : ℝ) (S : Finset ℂ) (x : ℝ) : ℂ :=
  ∑ ρ ∈ S, (cw h T ρ : ℂ) * phase T σ ρ x

/-- second trace as a functional of the kernel:  `∫_{-1}^{1} a_g(x) |K(x)|² dx` -/
def t2 (K : ℝ → ℂ) : ℝ := ∫ x in (-1 : ℝ)..1, ag x * ‖K x‖ ^ 2

/-- third trace as a functional of the kernel:  `∬ G(x,y) K(x) K(y) K(-x-y) dx dy` -/
def t3 (K : ℝ → ℂ) : ℂ :=
  ∫ x in (-1 : ℝ)..1, ∫ y in (-1 : ℝ)..1, (Gg x y : ℂ) * (K x * K y * K (-x - y))

end TMA
end
end Src_TMA_Basic

section Src_TMA_Window
/-
Written for Kristian Muri Knausgård, drafted with Claude (Anthropic), 22 November 2026.

TMA/Window.lean — the quadratic window `gwin`, its correlations `ag`, `Gg`, `bg`, the Fourier identities that
link the Gram matrix of the zeros to the kernel functionals `t2`, `t3`, and the exact constants.
STATUS: all statements proved.  See BLUEPRINT.md, module "Window".
Helper lemmas live in the namespace `TMA.Win`; the exported interface is in `TMA`.
-/

open MeasureTheory Complex
open scoped BigOperators Real ComplexConjugate ComplexOrder

noncomputable section
namespace TMA

/-! ### helpers: integrals of polynomials -/
namespace Win

theorem hasDerivAt_poly (c0 c1 c2 c3 c4 c5 c6 c7 c8 u : ℝ) :
    HasDerivAt (fun u : ℝ => c0 * u + c1 / 2 * u ^ 2 + c2 / 3 * u ^ 3 + c3 / 4 * u ^ 4 + c4 / 5 * u ^ 5
        + c5 / 6 * u ^ 6 + c6 / 7 * u ^ 7 + c7 / 8 * u ^ 8 + c8 / 9 * u ^ 9)
      (c0 + c1 * u + c2 * u ^ 2 + c3 * u ^ 3 + c4 * u ^ 4 + c5 * u ^ 5 + c6 * u ^ 6 + c7 * u ^ 7
        + c8 * u ^ 8) u := by
  have h := ((((((((((hasDerivAt_id' u).const_mul c0).add
    ((hasDerivAt_pow 2 u).const_mul (c1 / 2))).add
    ((hasDerivAt_pow 3 u).const_mul (c2 / 3))).add
    ((hasDerivAt_pow 4 u).const_mul (c3 / 4))).add
    ((hasDerivAt_pow 5 u).const_mul (c4 / 5))).add
    ((hasDerivAt_pow 6 u).const_mul (c5 / 6))).add
    ((hasDerivAt_pow 7 u).const_mul (c6 / 7))).add
    ((hasDerivAt_pow 8 u).const_mul (c7 / 8))).add
    ((hasDerivAt_pow 9 u).const_mul (c8 / 9)))
  refine h.congr_deriv ?_
  norm_num
  ring

/-- the integral of a polynomial of degree at most 8 with explicit coefficients -/
theorem integral_poly (c0 c1 c2 c3 c4 c5 c6 c7 c8 a b : ℝ) :
    ∫ u in a..b, (c0 + c1 * u + c2 * u ^ 2 + c3 * u ^ 3 + c4 * u ^ 4 + c5 * u ^ 5 + c6 * u ^ 6
        + c7 * u ^ 7 + c8 * u ^ 8)
      = c0 * (b - a) + c1 / 2 * (b ^ 2 - a ^ 2) + c2 / 3 * (b ^ 3 - a ^ 3) + c3 / 4 * (b ^ 4 - a ^ 4)
        + c4 / 5 * (b ^ 5 - a ^ 5) + c5 / 6 * (b ^ 6 - a ^ 6) + c6 / 7 * (b ^ 7 - a ^ 7)
        + c7 / 8 * (b ^ 8 - a ^ 8) + c8 / 9 * (b ^ 9 - a ^ 9) := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ => hasDerivAt_poly c0 c1 c2 c3 c4 c5 c6 c7 c8 x)
    (Continuous.intervalIntegrable (by fun_prop) _ _)]
  ring

/-- the polynomial that `gwin` equals on `[-1/2, 1/2]` -/
def pw (u : ℝ) : ℝ := 10 / 9 - 4 / 3 * u ^ 2

theorem gwin_of_mem {u : ℝ} (h : |u| ≤ 1 / 2) : gwin u = pw u := by
  unfold gwin alpha pw
  rw [if_pos h]
  ring

theorem sq_le_of_abs {u : ℝ} (h : |u| ≤ 1 / 2) : u ^ 2 ≤ 1 / 4 := by
  have h0 := abs_nonneg u
  nlinarith [sq_abs u]

end Win

open Win

/-! ### the window -/
theorem gwin_eq_zero {u : ℝ} (h : 1 / 2 < |u|) : gwin u = 0 := by
  unfold gwin
  rw [if_neg (not_le.mpr h)]

theorem gwin_nonneg (u : ℝ) : 0 ≤ gwin u := by
  by_cases h : |u| ≤ 1 / 2
  · rw [gwin_of_mem h]
    unfold pw
    linarith [sq_le_of_abs h]
  · rw [gwin_eq_zero (not_le.mp h)]

theorem gwin_le (u : ℝ) : gwin u ≤ 10 / 9 := by
  by_cases h : |u| ≤ 1 / 2
  · rw [gwin_of_mem h]
    unfold pw
    linarith [sq_nonneg u]
  · rw [gwin_eq_zero (not_le.mp h)]
    norm_num

namespace Win

theorem gwin_eq_indicator : gwin = Set.indicator (Set.Icc (-(1 / 2)) (1 / 2)) pw := by
  funext u
  by_cases h : |u| ≤ 1 / 2
  · rw [gwin_of_mem h, Set.indicator_of_mem (Set.mem_Icc.mpr (abs_le.mp h))]
  · rw [gwin_eq_zero (not_le.mp h),
      Set.indicator_of_notMem (fun h' => h (abs_le.mpr (Set.mem_Icc.mp h')))]

theorem continuous_pw : Continuous pw := by
  unfold pw
  fun_prop

theorem measurable_gwin : Measurable gwin := by
  rw [gwin_eq_indicator]
  exact continuous_pw.measurable.indicator measurableSet_Icc

theorem norm_gwin_le (u : ℝ) : ‖gwin u‖ ≤ 10 / 9 := by
  rw [Real.norm_eq_abs, abs_of_nonneg (gwin_nonneg u)]
  exact gwin_le u

theorem gwin_neg (u : ℝ) : gwin (-u) = gwin u := by
  unfold gwin
  rw [abs_neg, neg_sq]

/-- two points at distance more than 1 cannot both lie in the support -/
theorem gwin_mul_eq_zero {u v : ℝ} (h : 1 < |u - v|) : gwin u * gwin v = 0 := by
  by_cases hu : |u| ≤ 1 / 2
  · have hv : 1 / 2 < |v| := by
      by_contra hc
      have hv' := abs_le.mp (not_lt.mp hc)
      have hu' := abs_le.mp hu
      have : |u - v| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
      linarith
    rw [gwin_eq_zero hv, mul_zero]
  · rw [gwin_eq_zero (not_le.mp hu), zero_mul]

end Win

theorem integrable_gwin : Integrable gwin := by
  rw [gwin_eq_indicator, integrable_indicator_iff measurableSet_Icc]
  exact continuous_pw.integrableOn_Icc

theorem integral_gwin : ∫ u, gwin u = 1 := by
  rw [gwin_eq_indicator, integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num)]
  have h : ∀ u : ℝ, pw u = 10 / 9 + 0 * u + (-(4 / 3)) * u ^ 2 + 0 * u ^ 3 + 0 * u ^ 4 + 0 * u ^ 5
      + 0 * u ^ 6 + 0 * u ^ 7 + 0 * u ^ 8 := by
    intro u
    unfold pw
    ring
  simp_rw [h]
  rw [integral_poly]
  norm_num

namespace Win

theorem integrable_gg (t : ℝ) : Integrable (fun u => gwin u * gwin (u + t)) :=
  (integrable_gwin.comp_add_right t).bdd_mul (c := 10 / 9) measurable_gwin.aestronglyMeasurable
    (ae_of_all _ norm_gwin_le)

theorem integrable_ggg (r s : ℝ) : Integrable (fun u => gwin u * gwin (u + r) * gwin (u + r + s)) :=
  (integrable_gg r).mul_bdd (c := 10 / 9)
    (show Measurable fun u : ℝ => gwin (u + r + s) from
      measurable_gwin.comp ((measurable_id.add_const r).add_const s)).aestronglyMeasurable
    (ae_of_all _ fun _ => norm_gwin_le _)

end Win

/-! ### the autocorrelation -/
theorem ag_nonneg (r : ℝ) : 0 ≤ ag r :=
  integral_nonneg fun u => mul_nonneg (gwin_nonneg u) (gwin_nonneg _)

theorem ag_le (r : ℝ) : ag r ≤ 10 / 9 := by
  have h : ag r ≤ ∫ u, gwin u * (10 / 9) :=
    integral_mono (integrable_gg r) (integrable_gwin.mul_const _)
      (fun u => mul_le_mul_of_nonneg_left (gwin_le _) (gwin_nonneg u))
  rw [integral_mul_const, integral_gwin] at h
  linarith

theorem ag_neg (r : ℝ) : ag (-r) = ag r := by
  unfold ag
  rw [← integral_add_right_eq_self (fun u => gwin u * gwin (u + -r)) r]
  refine integral_congr_ae (ae_of_all _ fun u => ?_)
  simp only [add_neg_cancel_right]
  ring

theorem ag_eq_zero {r : ℝ} (h : 1 < |r|) : ag r = 0 := by
  unfold ag
  have h0 : ∀ u, gwin u * gwin (u + r) = 0 := fun u =>
    gwin_mul_eq_zero (by rw [show u - (u + r) = -r by ring, abs_neg]; exact h)
  simp_rw [h0]
  exact integral_zero _ _

namespace Win

/-- pointwise bound for a shift of the window by `d ≥ 0` -/
theorem gwin_shift_bound {d : ℝ} (hd : 0 ≤ d) (u : ℝ) :
    |gwin (u + d) - gwin u| ≤
      Set.indicator (Set.Icc (-(1 / 2)) (1 / 2)) (fun _ => 4 / 3 * d) u
        + Set.indicator (Set.Ioc (1 / 2 - d) (1 / 2)) (fun _ => (10 / 9 : ℝ)) u
        + Set.indicator (Set.Ico (-(1 / 2) - d) (-(1 / 2))) (fun _ => (10 / 9 : ℝ)) u := by
  have n1 : 0 ≤ Set.indicator (Set.Icc (-(1 / 2)) (1 / 2)) (fun _ => 4 / 3 * d) u :=
    Set.indicator_nonneg (fun _ _ => by positivity) u
  have n2 : 0 ≤ Set.indicator (Set.Ioc (1 / 2 - d) (1 / 2)) (fun _ => (10 / 9 : ℝ)) u :=
    Set.indicator_nonneg (fun _ _ => by norm_num) u
  have n3 : 0 ≤ Set.indicator (Set.Ico (-(1 / 2) - d) (-(1 / 2))) (fun _ => (10 / 9 : ℝ)) u :=
    Set.indicator_nonneg (fun _ _ => by norm_num) u
  by_cases hu : |u| ≤ 1 / 2
  · have hu' := abs_le.mp hu
    have e1 : Set.indicator (Set.Icc (-(1 / 2)) (1 / 2)) (fun _ => 4 / 3 * d) u = 4 / 3 * d :=
      Set.indicator_of_mem (Set.mem_Icc.mpr hu') _
    by_cases hv : |u + d| ≤ 1 / 2
    · have hv' := abs_le.mp hv
      rw [gwin_of_mem hu, gwin_of_mem hv, e1]
      have h1 : pw (u + d) - pw u = -(4 / 3 * d * (2 * u + d)) := by unfold pw; ring
      have h2 : |2 * u + d| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
      rw [h1, abs_neg, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 4 / 3 * d)]
      nlinarith [abs_nonneg (2 * u + d)]
    · have hv' : 1 / 2 < u + d := by
        by_contra hc
        exact hv (abs_le.mpr ⟨by linarith, not_lt.mp hc⟩)
      have e2 : Set.indicator (Set.Ioc (1 / 2 - d) (1 / 2)) (fun _ => (10 / 9 : ℝ)) u = 10 / 9 :=
        Set.indicator_of_mem (Set.mem_Ioc.mpr ⟨by linarith, hu'.2⟩) _
      rw [gwin_eq_zero (not_le.mp hv), zero_sub, abs_neg, abs_of_nonneg (gwin_nonneg u), e1, e2]
      have := gwin_le u
      have : 0 ≤ 4 / 3 * d := by positivity
      linarith
  · by_cases hv : |u + d| ≤ 1 / 2
    · have hv' := abs_le.mp hv
      have hu' : u < -(1 / 2) := by
        by_contra hc
        exact hu (abs_le.mpr ⟨not_lt.mp hc, by linarith⟩)
      have e3 : Set.indicator (Set.Ico (-(1 / 2) - d) (-(1 / 2))) (fun _ => (10 / 9 : ℝ)) u
          = 10 / 9 :=
        Set.indicator_of_mem (Set.mem_Ico.mpr ⟨by linarith, hu'⟩) _
      rw [gwin_eq_zero (not_le.mp hu), sub_zero, abs_of_nonneg (gwin_nonneg _), e3]
      have := gwin_le (u + d)
      linarith
    · rw [gwin_eq_zero (not_le.mp hu), gwin_eq_zero (not_le.mp hv), sub_zero, abs_zero]
      linarith

theorem integrable_abs_shift (a b : ℝ) : Integrable (fun u => |gwin (u + a) - gwin (u + b)|) :=
  ((integrable_gwin.comp_add_right a).sub (integrable_gwin.comp_add_right b)).abs

/-- `L¹` modulus of continuity of the window, shift `d ≥ 0` -/
theorem transL1_nonneg {d : ℝ} (hd : 0 ≤ d) : ∫ u, |gwin (u + d) - gwin u| ≤ 32 / 9 * d := by
  have i1 : Integrable (Set.indicator (Set.Icc (-(1 / 2 : ℝ)) (1 / 2)) (fun _ => 4 / 3 * d)) :=
    (integrable_indicator_iff measurableSet_Icc).mpr (integrableOn_const (by simp))
  have i2 : Integrable (Set.indicator (Set.Ioc (1 / 2 - d) (1 / 2 : ℝ)) (fun _ => (10 / 9 : ℝ))) :=
    (integrable_indicator_iff measurableSet_Ioc).mpr (integrableOn_const (by simp))
  have i3 : Integrable
      (Set.indicator (Set.Ico (-(1 / 2 : ℝ) - d) (-(1 / 2))) (fun _ => (10 / 9 : ℝ))) :=
    (integrable_indicator_iff measurableSet_Ico).mpr (integrableOn_const (by simp))
  have i0 : Integrable (fun u => |gwin (u + d) - gwin u|) := by
    have := integrable_abs_shift d 0
    simpa using this
  have h := integral_mono i0 ((i1.add i2).add i3) (fun u => gwin_shift_bound hd u)
  have e : ∫ u, ((Set.indicator (Set.Icc (-(1 / 2 : ℝ)) (1 / 2)) (fun _ => 4 / 3 * d)
        + Set.indicator (Set.Ioc (1 / 2 - d) (1 / 2 : ℝ)) (fun _ => (10 / 9 : ℝ)))
        + Set.indicator (Set.Ico (-(1 / 2 : ℝ) - d) (-(1 / 2))) (fun _ => (10 / 9 : ℝ))) u
      = 32 / 9 * d := by
    rw [integral_add' (i1.add i2) i3, integral_add' i1 i2, integral_indicator_const _ measurableSet_Icc,
      integral_indicator_const _ measurableSet_Ioc, integral_indicator_const _ measurableSet_Ico,
      Real.volume_real_Icc_of_le (by norm_num), Real.volume_real_Ioc_of_le (by linarith),
      Real.volume_real_Ico_of_le (by linarith)]
    simp only [smul_eq_mul]
    ring
  rw [e] at h
  exact h

/-- `L¹` modulus of continuity of the window -/
theorem transL1 (a b : ℝ) : ∫ u, |gwin (u + a) - gwin (u + b)| ≤ 32 / 9 * |a - b| := by
  wlog h : b ≤ a generalizing a b
  · have h' := this b a (le_of_not_ge h)
    rw [abs_sub_comm a b]
    refine le_of_eq_of_le ?_ h'
    refine integral_congr_ae (ae_of_all _ fun u => ?_)
    exact abs_sub_comm _ _
  · have e : ∫ u, |gwin (u + a) - gwin (u + b)| = ∫ v, |gwin (v + (a - b)) - gwin v| := by
      rw [← integral_add_right_eq_self (fun v => |gwin (v + (a - b)) - gwin v|) b]
      refine integral_congr_ae (ae_of_all _ fun u => ?_)
      simp only [add_add_sub_cancel]
    rw [e, abs_of_nonneg (sub_nonneg.mpr h)]
    exact transL1_nonneg (sub_nonneg.mpr h)

end Win

theorem ag_lipschitz (r r' : ℝ) : |ag r - ag r'| ≤ 5 * |r - r'| := by
  have h1 : ag r - ag r' = ∫ u, gwin u * (gwin (u + r) - gwin (u + r')) := by
    unfold ag
    rw [← integral_sub (integrable_gg r) (integrable_gg r')]
    refine integral_congr_ae (ae_of_all _ fun u => ?_)
    simp only
    ring
  rw [h1]
  calc |∫ u, gwin u * (gwin (u + r) - gwin (u + r'))|
      ≤ ∫ u, |gwin u * (gwin (u + r) - gwin (u + r'))| := abs_integral_le_integral_abs
    _ ≤ ∫ u, 10 / 9 * |gwin (u + r) - gwin (u + r')| :=
        integral_mono_of_nonneg (ae_of_all _ fun u => abs_nonneg _)
          ((integrable_abs_shift r r').const_mul _)
          (ae_of_all _ fun u => by
            simp only
            rw [abs_mul, abs_of_nonneg (gwin_nonneg u)]
            exact mul_le_mul_of_nonneg_right (gwin_le u) (abs_nonneg _))
    _ = 10 / 9 * ∫ u, |gwin (u + r) - gwin (u + r')| := integral_const_mul _ _
    _ ≤ 10 / 9 * (32 / 9 * |r - r'|) :=
        mul_le_mul_of_nonneg_left (transL1 r r') (by norm_num)
    _ ≤ 5 * |r - r'| := by nlinarith [abs_nonneg (r - r')]

theorem continuous_ag : Continuous ag := by
  have h : LipschitzWith 5 ag := by
    refine LipschitzWith.of_dist_le_mul fun r r' => ?_
    simp only [Real.dist_eq]
    exact_mod_cast ag_lipschitz r r'
  exact h.continuous

/-! ### the triple correlation -/
theorem Gg_nonneg (r s : ℝ) : 0 ≤ Gg r s :=
  integral_nonneg fun u => mul_nonneg (mul_nonneg (gwin_nonneg u) (gwin_nonneg _)) (gwin_nonneg _)

theorem Gg_le (r s : ℝ) : Gg r s ≤ 2 := by
  have h : Gg r s ≤ ∫ u, gwin u * (10 / 9) * (10 / 9) :=
    integral_mono (integrable_ggg r s) ((integrable_gwin.mul_const _).mul_const _)
      (fun u => mul_le_mul (mul_le_mul_of_nonneg_left (gwin_le _) (gwin_nonneg u)) (gwin_le _)
        (gwin_nonneg _) (mul_nonneg (gwin_nonneg u) (by norm_num)))
  rw [integral_mul_const, integral_mul_const, integral_gwin] at h
  linarith

theorem Gg_eq_zero {r s : ℝ} (h : 1 < |r| ∨ 1 < |s| ∨ 1 < |r + s|) : Gg r s = 0 := by
  unfold Gg
  have h0 : ∀ u, gwin u * gwin (u + r) * gwin (u + r + s) = 0 := by
    intro u
    rcases h with h | h | h
    · rw [gwin_mul_eq_zero (by rw [show u - (u + r) = -r by ring, abs_neg]; exact h), zero_mul]
    · rw [mul_assoc, gwin_mul_eq_zero (u := u + r) (v := u + r + s)
        (by rw [show u + r - (u + r + s) = -s by ring, abs_neg]; exact h), mul_zero]
    · rw [mul_right_comm, gwin_mul_eq_zero (u := u) (v := u + r + s)
        (by rw [show u - (u + r + s) = -(r + s) by ring, abs_neg]; exact h), zero_mul]
  simp_rw [h0]
  exact integral_zero _ _

theorem Gg_lipschitz (r s r' s' : ℝ) : |Gg r s - Gg r' s'| ≤ 10 * (|r - r'| + |s - s'|) := by
  have h1 : Gg r s - Gg r' s' = ∫ u, (gwin u * (gwin (u + r) - gwin (u + r')) * gwin (u + r + s)
      + gwin u * gwin (u + r') * (gwin (u + (r + s)) - gwin (u + (r' + s')))) := by
    unfold Gg
    rw [← integral_sub (integrable_ggg r s) (integrable_ggg r' s')]
    refine integral_congr_ae (ae_of_all _ fun u => ?_)
    simp only [← add_assoc]
    ring
  have hb : ∀ u, |gwin u * (gwin (u + r) - gwin (u + r')) * gwin (u + r + s)
      + gwin u * gwin (u + r') * (gwin (u + (r + s)) - gwin (u + (r' + s')))|
      ≤ 100 / 81 * |gwin (u + r) - gwin (u + r')|
        + 100 / 81 * |gwin (u + (r + s)) - gwin (u + (r' + s'))| := by
    intro u
    have g0 := gwin_nonneg u
    have g1 := gwin_le u
    have g2 := gwin_nonneg (u + r')
    have g3 := gwin_le (u + r')
    have g4 := gwin_nonneg (u + r + s)
    have g5 := gwin_le (u + r + s)
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [abs_mul, abs_mul, abs_of_nonneg g0, abs_of_nonneg g4]
      have hA := abs_nonneg (gwin (u + r) - gwin (u + r'))
      calc gwin u * |gwin (u + r) - gwin (u + r')| * gwin (u + r + s)
          ≤ 10 / 9 * |gwin (u + r) - gwin (u + r')| * (10 / 9) :=
            mul_le_mul (mul_le_mul_of_nonneg_right g1 hA) g5 g4 (by positivity)
        _ = 100 / 81 * |gwin (u + r) - gwin (u + r')| := by ring
    · rw [abs_mul, abs_mul, abs_of_nonneg g0, abs_of_nonneg g2]
      have hA := abs_nonneg (gwin (u + (r + s)) - gwin (u + (r' + s')))
      calc gwin u * gwin (u + r') * |gwin (u + (r + s)) - gwin (u + (r' + s'))|
          ≤ 10 / 9 * (10 / 9) * |gwin (u + (r + s)) - gwin (u + (r' + s'))| :=
            mul_le_mul_of_nonneg_right (mul_le_mul g1 g3 g2 (by norm_num)) hA
        _ = 100 / 81 * |gwin (u + (r + s)) - gwin (u + (r' + s'))| := by ring
  rw [h1]
  have t1 := transL1 r r'
  have t2 := transL1 (r + s) (r' + s')
  have hd : |r + s - (r' + s')| ≤ |r - r'| + |s - s'| := by
    rw [show r + s - (r' + s') = (r - r') + (s - s') by ring]
    exact abs_add_le _ _
  calc |∫ u, (gwin u * (gwin (u + r) - gwin (u + r')) * gwin (u + r + s)
        + gwin u * gwin (u + r') * (gwin (u + (r + s)) - gwin (u + (r' + s'))))|
      ≤ ∫ u, |gwin u * (gwin (u + r) - gwin (u + r')) * gwin (u + r + s)
        + gwin u * gwin (u + r') * (gwin (u + (r + s)) - gwin (u + (r' + s')))| :=
        abs_integral_le_integral_abs
    _ ≤ ∫ u, (100 / 81 * |gwin (u + r) - gwin (u + r')|
        + 100 / 81 * |gwin (u + (r + s)) - gwin (u + (r' + s'))|) :=
        integral_mono_of_nonneg (ae_of_all _ fun u => abs_nonneg _)
          (((integrable_abs_shift r r').const_mul _).add
            ((integrable_abs_shift (r + s) (r' + s')).const_mul _))
          (ae_of_all _ hb)
    _ = 100 / 81 * (∫ u, |gwin (u + r) - gwin (u + r')|)
        + 100 / 81 * ∫ u, |gwin (u + (r + s)) - gwin (u + (r' + s'))| := by
        rw [integral_add ((integrable_abs_shift r r').const_mul _)
          ((integrable_abs_shift (r + s) (r' + s')).const_mul _), integral_const_mul,
          integral_const_mul]
    _ ≤ 100 / 81 * (32 / 9 * |r - r'|) + 100 / 81 * (32 / 9 * |r + s - (r' + s')|) :=
        add_le_add (mul_le_mul_of_nonneg_left t1 (by norm_num))
          (mul_le_mul_of_nonneg_left t2 (by norm_num))
    _ ≤ 10 * (|r - r'| + |s - s'|) := by
        nlinarith [abs_nonneg (r - r'), abs_nonneg (s - s'), abs_nonneg (r + s - (r' + s'))]

/-- `G(s,0) = ∫ g(u) g(u+s)² du = b_g(-s)` -/
theorem Gg_right_zero (s : ℝ) : Gg s 0 = bg (-s) := by
  unfold bg Gg
  rw [← integral_add_right_eq_self (fun u => gwin u * gwin (u + 0) * gwin (u + 0 + -s)) s]
  refine integral_congr_ae (ae_of_all _ fun u => ?_)
  simp only [add_zero, add_neg_cancel_right]
  ring

/-- `G(s,-s) = ∫ g(u)² g(u+s) du = b_g(s)` -/
theorem Gg_neg (s : ℝ) : Gg s (-s) = bg s := by
  unfold bg Gg
  refine integral_congr_ae (ae_of_all _ fun u => ?_)
  simp only [add_zero, add_neg_cancel_right]
  ring

theorem continuous_Gg : Continuous (fun p : ℝ × ℝ => Gg p.1 p.2) := by
  have h : LipschitzWith 20 (fun p : ℝ × ℝ => Gg p.1 p.2) := by
    refine LipschitzWith.of_dist_le_mul fun p q => ?_
    have h1 := Gg_lipschitz p.1 p.2 q.1 q.2
    have h2 : |p.1 - q.1| ≤ dist p q := by
      rw [← Real.dist_eq, Prod.dist_eq]
      exact le_max_left _ _
    have h3 : |p.2 - q.2| ≤ dist p q := by
      rw [← Real.dist_eq, Prod.dist_eq]
      exact le_max_right _ _
    have h4 : |Gg p.1 p.2 - Gg q.1 q.2| ≤ 20 * dist p q := by linarith
    simp only [Real.dist_eq]
    exact_mod_cast h4
  exact h.continuous

/-! ### Fourier identities -/
namespace Win

/-- the modulated window `g(u) e^{itu}`; `ghat t = ∫ gk t` -/
def gk (t u : ℝ) : ℂ := (gwin u : ℂ) * Complex.exp (Complex.I * t * u)

theorem ghat_eq (t : ℝ) : ghat t = ∫ u, gk t u := rfl

theorem norm_gk (t u : ℝ) : ‖gk t u‖ = gwin u := by
  unfold gk
  rw [norm_mul, show Complex.I * (t : ℂ) * (u : ℂ) = ((t * u : ℝ) : ℂ) * Complex.I by
    push_cast; ring, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (gwin_nonneg u)]

theorem measurable_gk (t : ℝ) : Measurable (gk t) := by
  unfold gk
  exact (Complex.measurable_ofReal.comp measurable_gwin).mul (Continuous.measurable (by fun_prop))

theorem integrable_gk (t : ℝ) : Integrable (gk t) :=
  integrable_gwin.mono' (measurable_gk t).aestronglyMeasurable
    (ae_of_all _ fun u => (norm_gk t u).le)

theorem conj_gk (t u : ℝ) : conj (gk t u) = gk (-t) u := by
  unfold gk
  rw [map_mul, Complex.conj_ofReal, ← Complex.exp_conj]
  congr 2
  simp only [map_mul, Complex.conj_I, Complex.conj_ofReal, Complex.ofReal_neg]
  ring

/-- Fubini and translation invariance: `∫∫ F(u) G(u+x) du dx = (∫F)(∫G)` -/
theorem conv_eq (F G : ℝ → ℂ) (hF : Integrable F) (hG : Integrable G) :
    ∫ x, ∫ u, F u * G (u + x) = (∫ u, F u) * ∫ v, G v := by
  have hint : Integrable (fun z : ℝ × ℝ => F z.1 * G (z.1 + z.2)) (volume.prod volume) :=
    (measurePreserving_prod_add volume volume).integrable_comp_of_integrable (hF.mul_prod hG)
  calc ∫ x, ∫ u, F u * G (u + x)
      = ∫ z : ℝ × ℝ, F z.1 * G (z.1 + z.2) ∂(volume.prod volume) :=
        (integral_prod_symm (fun z : ℝ × ℝ => F z.1 * G (z.1 + z.2)) hint).symm
    _ = ∫ u, ∫ x, F u * G (u + x) :=
        integral_prod (fun z : ℝ × ℝ => F z.1 * G (z.1 + z.2)) hint
    _ = ∫ u, F u * ∫ v, G v := by
        refine integral_congr_ae (ae_of_all _ fun u => ?_)
        simp only
        rw [integral_const_mul, integral_add_left_eq_self]
    _ = (∫ u, F u) * ∫ v, G v := integral_mul_const _ _

/-- an integral over `[-1,1]` of a function vanishing outside is the integral over `ℝ` -/
theorem intervalIntegral_eq_integral {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} (h : ∀ x, 1 < |x| → f x = 0) : ∫ x in (-1 : ℝ)..1, f x = ∫ x, f x := by
  rw [intervalIntegral.integral_of_le (by norm_num), ← integral_Icc_eq_integral_Ioc]
  refine setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => h x ?_
  rw [Set.mem_Icc, not_and_or, not_le, not_le] at hx
  rcases hx with hx | hx
  · exact lt_abs.mpr (Or.inr (by linarith))
  · exact lt_abs.mpr (Or.inl hx)

/-- the trigonometric sum of the positivity argument -/
def Ssum {ι : Type*} [Fintype ι] (x : ι → ℝ) (z : ι → ℂ) (u : ℝ) : ℂ :=
  ∑ b, z b * Complex.exp (-(Complex.I * x b * u))

theorem sum_gk_eq {ι : Type*} [Fintype ι] (x : ι → ℝ) (z : ι → ℂ) (u : ℝ) :
    ∑ a, ∑ b, conj (z a) * gk (x a - x b) u * z b = ((gwin u * ‖Ssum x z u‖ ^ 2 : ℝ) : ℂ) := by
  have hS : conj (Ssum x z u) = ∑ a, conj (z a) * Complex.exp (Complex.I * x a * u) := by
    unfold Ssum
    rw [map_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [map_mul, ← Complex.exp_conj]
    congr 2
    simp only [map_neg, map_mul, Complex.conj_I, Complex.conj_ofReal]
    ring
  have hn : ((‖Ssum x z u‖ ^ 2 : ℝ) : ℂ) = conj (Ssum x z u) * Ssum x z u := by
    rw [Complex.conj_mul']
    push_cast
    rfl
  rw [Complex.ofReal_mul, hn, hS]
  unfold Ssum
  rw [Finset.sum_mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  unfold gk
  rw [show Complex.I * ((x a - x b : ℝ) : ℂ) * (u : ℂ)
      = Complex.I * (x a : ℂ) * (u : ℂ) + -(Complex.I * (x b : ℂ) * (u : ℂ)) by push_cast; ring,
    Complex.exp_add]
  ring

end Win

theorem norm_ghat_le (x : ℝ) : ‖ghat x‖ ≤ 1 := by
  calc ‖ghat x‖ ≤ ∫ u, ‖gk x u‖ := norm_integral_le_integral_norm _
    _ = ∫ u, gwin u := by simp_rw [norm_gk]
    _ = 1 := integral_gwin

theorem ghat_zero : ghat 0 = 1 := by
  unfold ghat
  simp only [Complex.ofReal_zero, mul_zero, zero_mul, Complex.exp_zero, mul_one]
  rw [integral_complex_ofReal, integral_gwin, Complex.ofReal_one]

theorem ghat_neg (x : ℝ) : ghat (-x) = conj (ghat x) := by
  rw [ghat_eq, ghat_eq, ← integral_conj]
  simp_rw [conj_gk]

/-- positive definiteness: `(ĝ(x_a - x_b))_{a,b}` is a positive semidefinite matrix
(`Σ conj z_a z_b ĝ(x_a - x_b) = ∫ g(u) |Σ_b z_b e^{-i x_b u}|² du`). -/
theorem ghat_posSemidef {ι : Type*} [Fintype ι] [DecidableEq ι] (x : ι → ℝ) :
    (Matrix.of fun a b : ι => ghat (x a - x b)).PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
  · refine Matrix.IsHermitian.ext fun i j => ?_
    simp only [Matrix.of_apply]
    rw [show x i - x j = -(x j - x i) by ring, ghat_neg]
    rfl
  · intro z
    have key : dotProduct (star z) (Matrix.mulVec (Matrix.of fun a b : ι => ghat (x a - x b)) z)
        = ((∫ u, gwin u * ‖Ssum x z u‖ ^ 2 : ℝ) : ℂ) := by
      rw [← integral_complex_ofReal]
      simp_rw [← sum_gk_eq]
      rw [integral_finsetSum _ (fun a _ => integrable_finsetSum _
        (fun b _ => ((integrable_gk _).const_mul _).mul_const _))]
      simp only [dotProduct, Matrix.mulVec, Matrix.of_apply, Pi.star_apply, Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [integral_finsetSum _ (fun b _ => ((integrable_gk _).const_mul _).mul_const _)]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [integral_mul_const, integral_const_mul, ← ghat_eq, mul_assoc]
      rfl
    rw [key, Complex.zero_le_real]
    exact integral_nonneg fun u => mul_nonneg (gwin_nonneg u) (by positivity)

/-- `|ĝ(x)|² = ∫_{-1}^{1} a_g(w) e^{ixw} dw` -/
theorem ghat_normSq (x : ℝ) :
    ((‖ghat x‖ ^ 2 : ℝ) : ℂ) = ∫ w in (-1 : ℝ)..1, (ag w : ℂ) * Complex.exp (Complex.I * x * w) := by
  rw [intervalIntegral_eq_integral (fun w hw => by rw [ag_eq_zero hw, Complex.ofReal_zero, zero_mul])]
  have h1 : ∀ w : ℝ, (ag w : ℂ) * Complex.exp (Complex.I * x * w)
      = ∫ u, gk (-x) u * gk x (u + w) := by
    intro w
    unfold ag
    rw [← integral_complex_ofReal, ← integral_mul_const]
    refine integral_congr_ae (ae_of_all _ fun u => ?_)
    simp only [gk]
    push_cast
    rw [show Complex.I * (x : ℂ) * (w : ℂ)
        = Complex.I * -(x : ℂ) * (u : ℂ) + Complex.I * (x : ℂ) * ((u : ℂ) + (w : ℂ)) by ring,
      Complex.exp_add]
    ring
  simp_rw [h1]
  rw [conv_eq _ _ (integrable_gk (-x)) (integrable_gk x), ← ghat_eq, ← ghat_eq, ghat_neg,
    Complex.conj_mul']
  push_cast
  rfl

/-- `ĝ(a-b) ĝ(b-c) ĝ(c-a) = ∬ G(x,y) e^{i(bx + cy - a(x+y))} dy dx` -/
theorem ghat_triple (a b c : ℝ) :
    ghat (a - b) * ghat (b - c) * ghat (c - a)
      = ∫ x in (-1 : ℝ)..1, ∫ y in (-1 : ℝ)..1,
          (Gg x y : ℂ) * Complex.exp (Complex.I * (b * x + c * y - a * (x + y))) := by
  have hin : ∀ x : ℝ, ∫ y in (-1 : ℝ)..1,
      (Gg x y : ℂ) * Complex.exp (Complex.I * (b * x + c * y - a * (x + y)))
      = ∫ y, (Gg x y : ℂ) * Complex.exp (Complex.I * (b * x + c * y - a * (x + y))) := fun x =>
    intervalIntegral_eq_integral (fun y hy => by
      rw [Gg_eq_zero (Or.inr (Or.inl hy)), Complex.ofReal_zero, zero_mul])
  simp_rw [hin]
  rw [intervalIntegral_eq_integral (fun x hx => by
    have h0 : ∀ y : ℝ, (Gg x y : ℂ) * Complex.exp (Complex.I * (b * x + c * y - a * (x + y))) = 0 :=
      fun y => by rw [Gg_eq_zero (Or.inl hx), Complex.ofReal_zero, zero_mul]
    simp_rw [h0]
    exact integral_zero _ _)]
  have h1 : ∀ x y : ℝ, (Gg x y : ℂ) * Complex.exp (Complex.I * (b * x + c * y - a * (x + y)))
      = ∫ u, (gk (a - b) u * gk (b - c) (u + x)) * gk (c - a) (u + (x + y)) := by
    intro x y
    unfold Gg
    rw [← integral_complex_ofReal, ← integral_mul_const]
    refine integral_congr_ae (ae_of_all _ fun u => ?_)
    simp only [gk]
    rw [add_assoc u x y]
    push_cast
    rw [show Complex.I * ((b : ℂ) * (x : ℂ) + (c : ℂ) * (y : ℂ) - (a : ℂ) * ((x : ℂ) + (y : ℂ)))
        = Complex.I * ((a : ℂ) - (b : ℂ)) * (u : ℂ)
          + Complex.I * ((b : ℂ) - (c : ℂ)) * ((u : ℂ) + (x : ℂ))
          + Complex.I * ((c : ℂ) - (a : ℂ)) * ((u : ℂ) + ((x : ℂ) + (y : ℂ))) by ring,
      Complex.exp_add, Complex.exp_add]
    ring
  simp_rw [h1]
  have h2 : ∀ x : ℝ, ∫ y, ∫ u, (gk (a - b) u * gk (b - c) (u + x)) * gk (c - a) (u + (x + y))
      = (∫ u, gk (a - b) u * gk (b - c) (u + x)) * ghat (c - a) := by
    intro x
    have hFx : Integrable (fun u => gk (a - b) u * gk (b - c) (u + x)) :=
      (integrable_gk (a - b)).mul_bdd (c := 10 / 9)
        ((measurable_gk (b - c)).comp (measurable_id.add_const x)).aestronglyMeasurable
        (ae_of_all _ fun u => by
          show ‖gk (b - c) (u + x)‖ ≤ 10 / 9
          rw [norm_gk]
          exact gwin_le _)
    exact (integral_add_left_eq_self
      (fun y => ∫ u, (gk (a - b) u * gk (b - c) (u + x)) * gk (c - a) (u + y)) x).trans
      (conv_eq _ _ hFx (integrable_gk (c - a)))
  simp_rw [h2]
  rw [integral_mul_const, conv_eq _ _ (integrable_gk (a - b)) (integrable_gk (b - c))]
  rfl

/-! ### regularity on [0,1] and exact constants -/
namespace Win

/-- for `0 ≤ r`, `g(u)^(n+1) g(u+r)` is a polynomial on `[-1/2, 1/2 - r]` and zero outside -/
theorem gpow_mul_shift (n : ℕ) {r : ℝ} (hr : 0 ≤ r) (u : ℝ) :
    gwin u ^ (n + 1) * gwin (u + r)
      = Set.indicator (Set.Icc (-(1 / 2)) (1 / 2 - r)) (fun u => pw u ^ (n + 1) * pw (u + r)) u := by
  by_cases hu : u ∈ Set.Icc (-(1 / 2)) (1 / 2 - r)
  · rw [Set.indicator_of_mem hu]
    have h := Set.mem_Icc.mp hu
    rw [gwin_of_mem (abs_le.mpr ⟨h.1, by linarith [h.2]⟩),
      gwin_of_mem (abs_le.mpr ⟨by linarith [h.1], by linarith [h.2]⟩)]
  · rw [Set.indicator_of_notMem hu]
    rw [Set.mem_Icc, not_and_or, not_le, not_le] at hu
    rcases hu with h | h
    · rw [gwin_eq_zero (lt_abs.mpr (Or.inr (by linarith))), zero_pow (Nat.succ_ne_zero n), zero_mul]
    · rw [gwin_eq_zero (u := u + r) (lt_abs.mpr (Or.inl (by linarith))), mul_zero]

theorem integral_gpow_mul_shift (n : ℕ) {r : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1) :
    ∫ u, gwin u ^ (n + 1) * gwin (u + r)
      = ∫ u in (-(1 / 2))..(1 / 2 - r), pw u ^ (n + 1) * pw (u + r) := by
  simp_rw [gpow_mul_shift n hr]
  rw [integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith)]

/-- `a_g` on `[0,1]` -/
def agP (r : ℝ) : ℝ := 409 / 405 - 49 / 81 * r - 4 / 3 * r ^ 2 + 80 / 81 * r ^ 3 - 8 / 135 * r ^ 5

/-- `b_g` on `[0,1]` -/
def bgP (r : ℝ) : ℝ :=
  5251 / 5103 - 343 / 729 * r - 2126 / 1215 * r ^ 2 + 196 / 243 * r ^ 3 + 8 / 9 * r ^ 4
    - 128 / 243 * r ^ 5 + 64 / 2835 * r ^ 7

theorem ag_eq_agP {r : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1) : ag r = agP r := by
  have h0 : ag r = ∫ u, gwin u ^ (0 + 1) * gwin (u + r) := by
    unfold ag
    simp only [zero_add, pow_one]
  rw [h0, integral_gpow_mul_shift 0 hr hr1]
  have h : ∀ u : ℝ, pw u ^ (0 + 1) * pw (u + r)
      = (100 / 81 - 40 / 27 * r ^ 2) + (-(80 / 27) * r) * u + (-(80 / 27) + 16 / 9 * r ^ 2) * u ^ 2
        + (32 / 9 * r) * u ^ 3 + 16 / 9 * u ^ 4 + 0 * u ^ 5 + 0 * u ^ 6 + 0 * u ^ 7 + 0 * u ^ 8 := by
    intro u
    unfold pw
    ring
  simp_rw [h]
  rw [integral_poly]
  unfold agP
  ring

theorem bg_eq_bgP {r : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1) : bg r = bgP r := by
  have h0 : bg r = ∫ u, gwin u ^ (1 + 1) * gwin (u + r) := by
    unfold bg Gg
    refine integral_congr_ae (ae_of_all _ fun u => ?_)
    simp only [add_zero]
    ring
  rw [h0, integral_gpow_mul_shift 1 hr hr1]
  have h : ∀ u : ℝ, pw u ^ (1 + 1) * pw (u + r)
      = (1000 / 729 - 400 / 243 * r ^ 2) + (-(800 / 243) * r) * u
        + (-(400 / 81) + 320 / 81 * r ^ 2) * u ^ 2 + (640 / 81 * r) * u ^ 3
        + (160 / 27 - 64 / 27 * r ^ 2) * u ^ 4 + (-(128 / 27) * r) * u ^ 5 + (-(64 / 27)) * u ^ 6
        + 0 * u ^ 7 + 0 * u ^ 8 := by
    intro u
    unfold pw
    ring
  simp_rw [h]
  rw [integral_poly]
  unfold bgP
  ring

/-- `b_g` is even (the window is even) -/
theorem bg_neg (s : ℝ) : bg (-s) = bg s := by
  unfold bg Gg
  rw [← integral_neg_eq_self (fun u => gwin u * gwin (u + 0) * gwin (u + 0 + s)) volume]
  refine integral_congr_ae (ae_of_all _ fun u => ?_)
  simp only [add_zero]
  rw [gwin_neg, show -u + s = -(u + -s) by ring, gwin_neg]

theorem J2_eq : J2 = 541 / 1701 := by
  unfold J2
  have h : ∫ r in (0 : ℝ)..1, r * ag r = ∫ r in (0 : ℝ)..1, (0 + 409 / 405 * r + (-(49 / 81)) * r ^ 2
      + (-(4 / 3)) * r ^ 3 + 80 / 81 * r ^ 4 + 0 * r ^ 5 + (-(8 / 135)) * r ^ 6 + 0 * r ^ 7
      + 0 * r ^ 8) := by
    refine intervalIntegral.integral_congr fun r hr => ?_
    rw [Set.uIcc_of_le zero_le_one] at hr
    rw [ag_eq_agP hr.1 hr.2]
    unfold agP
    ring
  rw [h, integral_poly]
  norm_num

theorem J3_eq : J3 = 24026 / 76545 := by
  unfold J3
  have h : ∫ r in (0 : ℝ)..1, r * (bg r + bg (-r)) = ∫ r in (0 : ℝ)..1, (0 + 10502 / 5103 * r
      + (-(686 / 729)) * r ^ 2 + (-(4252 / 1215)) * r ^ 3 + 392 / 243 * r ^ 4 + 16 / 9 * r ^ 5
      + (-(256 / 243)) * r ^ 6 + 0 * r ^ 7 + 128 / 2835 * r ^ 8) := by
    refine intervalIntegral.integral_congr fun r hr => ?_
    rw [Set.uIcc_of_le zero_le_one] at hr
    rw [bg_neg, bg_eq_bgP hr.1 hr.2]
    unfold bgP
    ring
  rw [h, integral_poly]
  norm_num

end Win

/-- on `[0,1]` the autocorrelation is a polynomial -/
theorem ag_smooth_on : ∃ F : ℝ → ℝ, ContDiff ℝ 1 F ∧ ∀ r ∈ Set.Icc (0 : ℝ) 1, ag r = F r := by
  refine ⟨agP, ?_, fun r hr => ag_eq_agP hr.1 hr.2⟩
  unfold agP
  fun_prop

/-- on `[0,1]`, `r ↦ b_g(r) + b_g(-r)` is a polynomial -/
theorem bgsum_smooth_on :
    ∃ F : ℝ → ℝ, ContDiff ℝ 1 F ∧ ∀ r ∈ Set.Icc (0 : ℝ) 1, bg r + bg (-r) = F r := by
  refine ⟨fun r => 2 * bgP r, ?_, fun r hr => ?_⟩
  · unfold bgP
    fun_prop
  · simp only
    rw [bg_neg, bg_eq_bgP hr.1 hr.2]
    ring

theorem I2_eq : I2 = 409 / 405 := by
  unfold I2
  rw [ag_eq_agP le_rfl zero_le_one]
  unfold agP
  norm_num

theorem I3_eq : I3 = 5251 / 5103 := by
  have h : I3 = bg 0 := rfl
  rw [h, bg_eq_bgP le_rfl zero_le_one]
  unfold bgP
  norm_num

theorem J2_nonneg : 0 ≤ J2 := by
  rw [J2_eq]
  norm_num

theorem J3_nonneg : 0 ≤ J3 := by
  rw [J3_eq]
  norm_num

/-- `C₂(1) = ∫ g² + ∬ |u-v| g g = 11294/8505` -/
theorem C2_one : C2 1 = 11294 / 8505 := by
  unfold C2
  rw [I2_eq, J2_eq]
  norm_num

/-- `C₃(1) = ∫ g³ + 3 ∬ |u-v| g² g = 7183/3645` -/
theorem C3_one : C3 1 = 7183 / 3645 := by
  unfold C3
  rw [I3_eq, J3_eq]
  norm_num


end TMA
end
end Src_TMA_Window

section Src_TMA_PrimeSum
/-
Written for Kristian Muri Knausgård, drafted with Claude (Anthropic), 22 November 2026.

TMA/PrimeSum.lean — sums over prime powers with weights Λ(n)²/n (from Zeta23's Chebyshev–Mertens estimate
`cheb2a` by Abel summation), and the bound for the three-prime term.
STATUS: complete, every statement proved.  See BLUEPRINT.md, module "PrimeSum".
-/

open MeasureTheory
open scoped BigOperators ArithmeticFunction Real

noncomputable section
namespace TMA

/-! Helper lemmas live in the namespace `TMA.PrimeSum`; the exported statements are `TMA.primeSum_upper`,
`TMA.primeSum_asymp`, `TMA.triplePrime_bound`. -/

namespace PrimeSum

/-! ## Index sets -/

/-- a sum over `0 ≤ n ≤ N` of a sequence vanishing at 0 and 1 is the sum over `2 ≤ n ≤ N` -/
theorem sum_Icc_zero_eq_sum_Icc_two (g : ℕ → ℝ) (h0 : g 0 = 0) (h1 : g 1 = 0) (N : ℕ) :
    ∑ n ∈ Finset.Icc 0 N, g n = ∑ n ∈ Finset.Icc 2 N, g n := by
  symm
  apply Finset.sum_subset
  · intro n hn
    simp only [Finset.mem_Icc] at hn ⊢
    omega
  · intro n hn hn'
    simp only [Finset.mem_Icc] at hn hn'
    have h : n = 0 ∨ n = 1 := by omega
    rcases h with rfl | rfl <;> assumption

/-- a sum over `0 < n ≤ N` of a sequence vanishing at 1 is the sum over `2 ≤ n ≤ N` -/
theorem sum_Ioc_zero_eq_sum_Icc_two (g : ℕ → ℝ) (h1 : g 1 = 0) (N : ℕ) :
    ∑ n ∈ Finset.Ioc 0 N, g n = ∑ n ∈ Finset.Icc 2 N, g n := by
  symm
  apply Finset.sum_subset
  · intro n hn
    simp only [Finset.mem_Icc, Finset.mem_Ioc] at hn ⊢
    omega
  · intro n hn hn'
    simp only [Finset.mem_Icc, Finset.mem_Ioc] at hn hn'
    have h : n = 1 := by omega
    subst h
    exact h1

/-! ## The coefficients `Λ(n)²/n` and their summatory function -/

/-- the coefficients `Λ(n)²/n` -/
def cf (n : ℕ) : ℝ := Λ n ^ 2 / n

theorem cf_zero : cf 0 = 0 := by simp [cf]

theorem cf_one : cf 1 = 0 := by simp [cf]

/-- `|Σ_{n ≤ t} Λ(n)²/n - log² t / 2| ≤ C log t` for all `t ≥ 1` (from `cheb2a` for `t ≥ 2`; for
`1 ≤ t < 2` the sum is empty and `log² t / 2 ≤ log t`). -/
theorem cf_sum_bound : ∃ C : ℝ, 1 ≤ C ∧ ∀ t : ℝ, 1 ≤ t →
    |∑ n ∈ Finset.Icc 0 ⌊t⌋₊, cf n - Real.log t ^ 2 / 2| ≤ C * Real.log t := by
  obtain ⟨C, hC⟩ := Zeta23.Cheb.chebyshevMertens.cheb2a
  refine ⟨max C 1, le_max_right _ _, fun t ht => ?_⟩
  have hlog : 0 ≤ Real.log t := Real.log_nonneg ht
  rcases lt_or_ge t 2 with h2 | h2
  · have hfl : ⌊t⌋₊ = 1 := by
      rw [Nat.floor_eq_iff (by linarith)]
      constructor
      · simpa using ht
      · norm_num
        linarith
    have hsum : ∑ n ∈ Finset.Icc 0 ⌊t⌋₊, cf n = 0 := by
      rw [hfl, sum_Icc_zero_eq_sum_Icc_two cf cf_zero cf_one]
      rfl
    have hl2 : Real.log t ≤ 1 := by
      have h := Real.log_le_log (by linarith) h2.le
      linarith [Real.log_two_lt_d9]
    rw [hsum, zero_sub, abs_neg, abs_of_nonneg (by positivity)]
    have h1 : 1 * Real.log t ≤ max C 1 * Real.log t :=
      mul_le_mul_of_nonneg_right (le_max_right _ _) hlog
    have h3 : Real.log t ^ 2 ≤ Real.log t := by
      calc Real.log t ^ 2 = Real.log t * Real.log t := sq _
        _ ≤ Real.log t * 1 := mul_le_mul_of_nonneg_left hl2 hlog
        _ = Real.log t := mul_one _
    linarith
  · have h := hC t h2
    have hsum : ∑ n ∈ Finset.Icc 0 ⌊t⌋₊, cf n = ∑ n ∈ Finset.Ioc 0 ⌊t⌋₊, Λ n ^ 2 / n := by
      rw [sum_Icc_zero_eq_sum_Icc_two cf cf_zero cf_one,
        sum_Ioc_zero_eq_sum_Icc_two (fun n : ℕ => Λ n ^ 2 / (n : ℝ)) (by simp)]
      rfl
    rw [hsum]
    exact h.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hlog)

end PrimeSum

open PrimeSum

/-- `Σ_{2 ≤ n ≤ X} Λ(n)²/n ≤ C log² X` -/
theorem primeSum_upper :
    ∃ C : ℝ, ∀ X : ℝ, 2 ≤ X → ∑ n ∈ Finset.Icc 2 ⌊X⌋₊, Λ n ^ 2 / n ≤ C * Real.log X ^ 2 := by
  obtain ⟨C, hC1, hC⟩ := cf_sum_bound
  refine ⟨1 / 2 + C / Real.log 2, fun X hX => ?_⟩
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hL : Real.log 2 ≤ Real.log X := Real.log_le_log (by norm_num) hX
  have h := hC X (by linarith)
  rw [sum_Icc_zero_eq_sum_Icc_two cf cf_zero cf_one] at h
  have h' := (abs_le.mp h).2
  have h2 : C * Real.log X ≤ C / Real.log 2 * Real.log X ^ 2 := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hlog2]
    have h3 : 0 ≤ C * Real.log X := mul_nonneg (by linarith) (by linarith)
    calc C * Real.log X * Real.log 2 ≤ C * Real.log X * Real.log X :=
          mul_le_mul_of_nonneg_left hL h3
      _ = C * Real.log X ^ 2 := by ring
  show ∑ n ∈ Finset.Icc 2 ⌊X⌋₊, cf n ≤ _
  have h4 : (1 / 2 + C / Real.log 2) * Real.log X ^ 2
      = Real.log X ^ 2 / 2 + C / Real.log 2 * Real.log X ^ 2 := by ring
  linarith

/-! ## Abel summation -/

namespace PrimeSum

/-- core of `primeSum_asymp`, with explicit constants -/
theorem primeSum_asymp_aux (F : ℝ → ℝ) (hF : ContDiff ℝ 1 F) {C D : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ t : ℝ, 1 ≤ t →
      |∑ n ∈ Finset.Icc 0 ⌊t⌋₊, cf n - Real.log t ^ 2 / 2| ≤ C * Real.log t)
    (hD : ∀ u ∈ Set.Icc (0 : ℝ) 1, ‖deriv F u‖ ≤ D) (X : ℝ) (hX : 2 ≤ X) :
    |∑ n ∈ Finset.Icc 2 ⌊X⌋₊, Λ n ^ 2 / n * F (Real.log n / Real.log X)
        - Real.log X ^ 2 * ∫ r in (0 : ℝ)..1, r * F r| ≤ (|F 1| + D) * C * Real.log X := by
  have hF'c : Continuous (deriv F) := hF.continuous_deriv le_rfl
  have hFd : Differentiable ℝ F := hF.differentiable one_ne_zero
  have hD0 : 0 ≤ D := (norm_nonneg _).trans (hD 0 (by simp))
  have hX1 : (1 : ℝ) ≤ X := by linarith
  have hXpos : 0 < X := by linarith
  have hL : 0 < Real.log X := Real.log_pos (by linarith)
  set L := Real.log X with hLdef
  -- the test function `f t = F (log t / L)` and its derivative
  set f : ℝ → ℝ := fun t => F (Real.log t / L) with hf
  set f' : ℝ → ℝ := fun t => deriv F (Real.log t / L) * (t⁻¹ / L) with hf'
  have hfd : ∀ t : ℝ, 0 < t → HasDerivAt f (f' t) t := by
    intro t ht
    have h1 : HasDerivAt (fun t => Real.log t / L) (t⁻¹ / L) t :=
      (Real.hasDerivAt_log ht.ne').div_const L
    exact (hFd (Real.log t / L)).hasDerivAt.comp t h1
  have hderiv : ∀ t : ℝ, 0 < t → deriv f t = f' t := fun t ht => (hfd t ht).deriv
  have hlogc : ContinuousOn Real.log (Set.Icc 1 X) :=
    Real.continuousOn_log.mono (fun t ht => by
      have : (0 : ℝ) < t := by linarith [ht.1]
      exact this.ne')
  have hinvc : ContinuousOn (fun t : ℝ => t⁻¹) (Set.Icc 1 X) :=
    continuousOn_inv₀.mono (fun t ht => by
      have : (0 : ℝ) < t := by linarith [ht.1]
      exact this.ne')
  have hf'cont : ContinuousOn f' (Set.Icc 1 X) :=
    (hF'c.comp_continuousOn (hlogc.div_const L)).mul (hinvc.div_const L)
  have hf_diff : ∀ t ∈ Set.Icc 1 X, DifferentiableAt ℝ f t :=
    fun t ht => (hfd t (by linarith [ht.1])).differentiableAt
  have hderiv_Icc : ∀ t ∈ Set.Icc 1 X, deriv f t = f' t :=
    fun t ht => hderiv t (by linarith [ht.1])
  have hf_int : IntegrableOn (deriv f) (Set.Icc 1 X) :=
    hf'cont.integrableOn_Icc.congr_fun (fun t ht => (hderiv_Icc t ht).symm) measurableSet_Icc
  -- Abel summation
  have abel := sum_mul_eq_sub_integral_mul₀ cf cf_zero X hf_diff hf_int
  have hfX : f X = F 1 := by
    simp only [hf]
    rw [div_self hL.ne']
  have hsumeq : ∑ n ∈ Finset.Icc 2 ⌊X⌋₊, Λ n ^ 2 / n * F (Real.log n / L)
      = ∑ k ∈ Finset.Icc 0 ⌊X⌋₊, f k * cf k := by
    rw [sum_Icc_zero_eq_sum_Icc_two (fun k : ℕ => f k * cf k) (by simp [cf_zero])
      (by simp [cf_one])]
    refine Finset.sum_congr rfl (fun n _ => ?_)
    simp only [hf, cf]
    ring
  -- split the summatory function
  set S : ℝ → ℝ := fun t => ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, cf k with hS
  have h_int_S : IntegrableOn (fun t => deriv f t * S t) (Set.Ioc 1 X) :=
    (integrableOn_mul_sum_Icc cf zero_le_one hf_int).mono_set Set.Ioc_subset_Icc_self
  have h_int_main : IntegrableOn (fun t => deriv f t * (Real.log t ^ 2 / 2)) (Set.Ioc 1 X) := by
    have hc : ContinuousOn (fun t => f' t * (Real.log t ^ 2 / 2)) (Set.Icc 1 X) :=
      hf'cont.mul ((hlogc.pow 2).div_const 2)
    refine (hc.integrableOn_Icc.congr_fun (fun t ht => ?_) measurableSet_Icc).mono_set
      Set.Ioc_subset_Icc_self
    show f' t * (Real.log t ^ 2 / 2) = deriv f t * (Real.log t ^ 2 / 2)
    rw [hderiv_Icc t ht]
  have hsplit : ∫ t in Set.Ioc 1 X, deriv f t * S t
      = (∫ t in Set.Ioc 1 X, deriv f t * (Real.log t ^ 2 / 2))
        + ∫ t in Set.Ioc 1 X, deriv f t * (S t - Real.log t ^ 2 / 2) := by
    have h := integral_sub h_int_S h_int_main
    have h2 : ∫ t in Set.Ioc 1 X, deriv f t * (S t - Real.log t ^ 2 / 2)
        = ∫ t in Set.Ioc 1 X, (deriv f t * S t - deriv f t * (Real.log t ^ 2 / 2)) := by
      congr 1
      ext t
      ring
    rw [h2, h]
    ring
  -- main term: change of variables `u = log t / L`
  have hcv : ∫ t in (1 : ℝ)..X, ((fun u => u ^ 2 * deriv F u) ∘ (fun t => Real.log t / L)) t
        * (t⁻¹ / L) = ∫ u in (0 : ℝ)..1, u ^ 2 * deriv F u := by
    have h := intervalIntegral.integral_comp_mul_deriv (a := 1) (b := X)
      (f := fun t => Real.log t / L) (f' := fun t => t⁻¹ / L) (g := fun u => u ^ 2 * deriv F u)
      (fun t ht => by
        rw [Set.uIcc_of_le hX1] at ht
        exact (Real.hasDerivAt_log (by linarith [ht.1] : t ≠ 0)).div_const L)
      (by
        rw [Set.uIcc_of_le hX1]
        exact hinvc.div_const L)
      ((continuous_id.pow 2).mul hF'c)
    rw [h]
    simp only [Real.log_one, zero_div]
    rw [div_self hL.ne']
  have hmain : ∫ t in Set.Ioc 1 X, deriv f t * (Real.log t ^ 2 / 2)
      = L ^ 2 / 2 * ∫ u in (0 : ℝ)..1, u ^ 2 * deriv F u := by
    rw [← hcv, ← intervalIntegral.integral_of_le hX1, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr (fun t ht => ?_)
    rw [Set.uIcc_of_le hX1] at ht
    simp only [Function.comp]
    rw [hderiv_Icc t ht]
    simp only [hf']
    field_simp
  -- integration by parts
  have hparts : ∫ u in (0 : ℝ)..1, u ^ 2 * deriv F u
      = F 1 - 2 * ∫ u in (0 : ℝ)..1, u * F u := by
    have h := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := 0) (b := 1)
      (u := fun u : ℝ => u ^ 2) (v := F) (u' := fun u : ℝ => 2 * u) (v' := deriv F)
      (fun x _ => by simpa using hasDerivAt_pow 2 x)
      (fun x _ => (hFd x).hasDerivAt)
      ((continuous_const.mul continuous_id).intervalIntegrable _ _)
      (hF'c.intervalIntegrable _ _)
    rw [h, ← intervalIntegral.integral_const_mul]
    have h2 : ∫ x in (0 : ℝ)..1, 2 * x * F x = ∫ x in (0 : ℝ)..1, 2 * (x * F x) := by
      congr 1
      ext x
      ring
    rw [h2]
    ring
  -- error term
  have herr : ‖∫ t in Set.Ioc 1 X, deriv f t * (S t - Real.log t ^ 2 / 2)‖ ≤ D * C * L := by
    have hbound_int : IntegrableOn (fun t : ℝ => D * C * t⁻¹) (Set.Ioc 1 X) :=
      ((continuousOn_const.mul hinvc).integrableOn_Icc).mono_set Set.Ioc_subset_Icc_self
    have hae : ∀ᵐ t ∂(volume.restrict (Set.Ioc 1 X)),
        ‖deriv f t * (S t - Real.log t ^ 2 / 2)‖ ≤ D * C * t⁻¹ := by
      refine (ae_restrict_mem measurableSet_Ioc).mono (fun t ht => ?_)
      have ht1 : 1 ≤ t := ht.1.le
      have htpos : 0 < t := by linarith
      have hlt0 : 0 ≤ Real.log t := Real.log_nonneg ht1
      have hltL : Real.log t ≤ L := Real.log_le_log htpos ht.2
      have hu : Real.log t / L ∈ Set.Icc (0 : ℝ) 1 :=
        ⟨div_nonneg hlt0 hL.le, (div_le_one hL).mpr hltL⟩
      have hE := hC t ht1
      rw [hderiv t htpos, norm_mul, Real.norm_eq_abs (S t - Real.log t ^ 2 / 2)]
      simp only [hf', norm_mul, norm_div, norm_inv, Real.norm_eq_abs, abs_of_pos htpos,
        abs_of_pos hL]
      have h1 : |deriv F (Real.log t / L)| ≤ D := hD _ hu
      have htinv : 0 < t⁻¹ := inv_pos.mpr htpos
      calc |deriv F (Real.log t / L)| * (t⁻¹ / L) * |S t - Real.log t ^ 2 / 2|
          ≤ D * (t⁻¹ / L) * (C * Real.log t) := by
            apply mul_le_mul _ hE (abs_nonneg _) (by positivity)
            exact mul_le_mul_of_nonneg_right h1 (by positivity)
        _ = D * C * t⁻¹ * (Real.log t / L) := by ring
        _ ≤ D * C * t⁻¹ * 1 := by
            apply mul_le_mul_of_nonneg_left hu.2
            positivity
        _ = D * C * t⁻¹ := by ring
    calc ‖∫ t in Set.Ioc 1 X, deriv f t * (S t - Real.log t ^ 2 / 2)‖
        ≤ ∫ t in Set.Ioc 1 X, D * C * t⁻¹ := norm_integral_le_of_norm_le hbound_int hae
      _ = D * C * L := by
          rw [← intervalIntegral.integral_of_le hX1, intervalIntegral.integral_const_mul,
            integral_inv_of_pos one_pos hXpos, div_one]
  -- assemble
  have hEX := hC X hX1
  rw [hsumeq, abel, hfX, hsplit, hmain, hparts]
  have hid : F 1 * ∑ k ∈ Finset.Icc 0 ⌊X⌋₊, cf k
        - (L ^ 2 / 2 * (F 1 - 2 * ∫ u in (0 : ℝ)..1, u * F u)
          + ∫ t in Set.Ioc 1 X, deriv f t * (S t - Real.log t ^ 2 / 2))
        - L ^ 2 * ∫ r in (0 : ℝ)..1, r * F r
      = F 1 * (∑ k ∈ Finset.Icc 0 ⌊X⌋₊, cf k - L ^ 2 / 2)
        - ∫ t in Set.Ioc 1 X, deriv f t * (S t - Real.log t ^ 2 / 2) := by ring
  rw [hid]
  calc |F 1 * (∑ k ∈ Finset.Icc 0 ⌊X⌋₊, cf k - L ^ 2 / 2)
          - ∫ t in Set.Ioc 1 X, deriv f t * (S t - Real.log t ^ 2 / 2)|
      ≤ |F 1 * (∑ k ∈ Finset.Icc 0 ⌊X⌋₊, cf k - L ^ 2 / 2)|
          + |∫ t in Set.Ioc 1 X, deriv f t * (S t - Real.log t ^ 2 / 2)| := abs_sub _ _
    _ ≤ |F 1| * (C * L) + D * C * L := by
        rw [abs_mul]
        exact add_le_add (mul_le_mul_of_nonneg_left hEX (abs_nonneg _)) herr
    _ = (|F 1| + D) * C * L := by ring

end PrimeSum

/-- For `F ∈ C¹`:  `Σ_{2 ≤ n ≤ X} Λ(n)²/n · F(log n / log X) = log² X · ∫₀¹ r F(r) dr + O(log X)`. -/
theorem primeSum_asymp (F : ℝ → ℝ) (hF : ContDiff ℝ 1 F) :
    ∃ C : ℝ, ∀ X : ℝ, 2 ≤ X →
      |∑ n ∈ Finset.Icc 2 ⌊X⌋₊, Λ n ^ 2 / n * F (Real.log n / Real.log X)
          - Real.log X ^ 2 * ∫ r in (0 : ℝ)..1, r * F r| ≤ C * Real.log X := by
  obtain ⟨C, hC1, hC⟩ := cf_sum_bound
  have hF'c : Continuous (deriv F) := hF.continuous_deriv le_rfl
  obtain ⟨D, hD⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hF'c.continuousOn (s := Set.Icc (0 : ℝ) 1))
  exact ⟨(|F 1| + D) * C, fun X hX => primeSum_asymp_aux F hF (by linarith) hC hD X hX⟩

/-! ## The three-prime sum -/

namespace PrimeSum

/-- if `Λ(b) ≠ 0` and `Λ(p^i b) ≠ 0` then `b` is a power of `p` -/
theorem triple_structure {p i b : ℕ} (hp : p.Prime) (hi : 0 < i) (hb : Λ b ≠ 0)
    (hab : Λ (p ^ i * b) ≠ 0) : ∃ j : ℕ, 0 < j ∧ b = p ^ j := by
  rw [ArithmeticFunction.vonMangoldt_ne_zero_iff, isPrimePow_nat_iff] at hb hab
  obtain ⟨q, j, hq, hj, rfl⟩ := hb
  obtain ⟨r, k, hr, hk, hrk⟩ := hab
  have hpr : p = r := by
    have h : p ∣ r ^ k := by
      rw [hrk]
      exact Dvd.dvd.mul_right (dvd_pow_self p hi.ne') _
    exact (Nat.prime_dvd_prime_iff_eq hp hr).mp (hp.dvd_of_dvd_pow h)
  have hqr : q = r := by
    have h : q ∣ r ^ k := by
      rw [hrk]
      exact Dvd.dvd.mul_left (dvd_pow_self q hj.ne') _
    exact (Nat.prime_dvd_prime_iff_eq hq hr).mp (hq.dvd_of_dvd_pow h)
  exact ⟨j, hj, by rw [hqr, hpr]⟩

/-- a sum whose positive terms sit at points `φ j`, `j ∈ J`, with `f (φ j) ≤ g j` -/
theorem sum_le_sum_of_param {s J : Finset ℕ} (φ : ℕ → ℕ) (f g : ℕ → ℝ) (hg : ∀ j ∈ J, 0 ≤ g j)
    (hf : ∀ b ∈ s, f b ≤ 0 ∨ ∃ j ∈ J, b = φ j ∧ f b ≤ g j) :
    ∑ b ∈ s, f b ≤ ∑ j ∈ J, g j := by
  calc ∑ b ∈ s, f b ≤ ∑ b ∈ s, ∑ j ∈ J, (if φ j = b then g j else 0) := by
        apply Finset.sum_le_sum
        intro b hb
        have hnn : ∀ j ∈ J, 0 ≤ (if φ j = b then g j else 0) := by
          intro j hj
          split_ifs
          · exact hg j hj
          · exact le_rfl
        rcases hf b hb with h | ⟨j, hj, rfl, hfg⟩
        · exact h.trans (Finset.sum_nonneg hnn)
        · calc f (φ j) ≤ g j := hfg
            _ = (if φ j = φ j then g j else 0) := by simp
            _ ≤ _ := Finset.single_le_sum hnn hj
    _ = ∑ j ∈ J, ∑ b ∈ s, (if φ j = b then g j else 0) := Finset.sum_comm
    _ ≤ ∑ j ∈ J, g j := by
        apply Finset.sum_le_sum
        intro j hj
        rw [Finset.sum_ite_eq s (φ j) (fun _ => g j)]
        split_ifs
        · exact le_rfl
        · exact hg j hj

/-- for fixed `a`, the terms with `a ≤ b` sum to at most `2 Λ(a)³/a²` (geometric series) -/
theorem triple_inner (a M : ℕ) :
    ∑ b ∈ Finset.Icc 2 M, (if a ≤ b then Λ a * Λ b * Λ (a * b) / ((a : ℝ) * b) else 0)
      ≤ 2 * (Λ a ^ 3 / (a : ℝ) ^ 2) := by
  by_cases ha : Λ a = 0
  · simp [ha]
  obtain ⟨p, i, hp, hi, rfl⟩ :=
    (isPrimePow_nat_iff _).mp (ArithmeticFunction.vonMangoldt_ne_zero_iff.mp ha)
  have hΛ : ∀ j : ℕ, 0 < j → Λ (p ^ j) = Real.log p := fun j hj => by
    rw [ArithmeticFunction.vonMangoldt_apply_pow hj.ne',
      ArithmeticFunction.vonMangoldt_apply_prime hp]
  have hlogp : 0 ≤ Real.log p := Real.log_natCast_nonneg p
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hppos : (0 : ℝ) < p := by linarith
  have hApos : (0 : ℝ) < (p : ℝ) ^ i := by positivity
  have hcast : ((p ^ i : ℕ) : ℝ) = (p : ℝ) ^ i := by push_cast; rfl
  rw [hcast, hΛ i hi]
  calc ∑ b ∈ Finset.Icc 2 M,
          (if p ^ i ≤ b then Real.log p * Λ b * Λ (p ^ i * b) / ((p : ℝ) ^ i * b) else 0)
      ≤ ∑ k ∈ Finset.range (M + 1), Real.log p ^ 3 / ((p : ℝ) ^ i) ^ 2 * (1 / 2) ^ k := by
        apply sum_le_sum_of_param (fun k => p ^ (i + k))
        · intro k _
          positivity
        · intro b hb
          by_cases hab : p ^ i ≤ b
          swap
          · left
            simp [hab]
          by_cases hb0 : Λ b = 0
          · left
            simp [hb0]
          by_cases hab0 : Λ (p ^ i * b) = 0
          · left
            simp [hab0]
          right
          obtain ⟨j, hj, rfl⟩ := triple_structure hp hi hb0 hab0
          have hij : i ≤ j := (Nat.pow_le_pow_iff_right hp.one_lt).mp hab
          refine ⟨j - i, ?_, ?_, ?_⟩
          · have h1 : j < p ^ j := Nat.lt_pow_self hp.one_lt
            have h2 := (Finset.mem_Icc.mp hb).2
            rw [Finset.mem_range]
            omega
          · show p ^ j = p ^ (i + (j - i))
            congr 1
            omega
          · rw [if_pos hab, hΛ j hj, ← pow_add, hΛ (i + j) (by omega)]
            have hjsplit : ((p ^ j : ℕ) : ℝ) = (p : ℝ) ^ i * (p : ℝ) ^ (j - i) := by
              push_cast
              rw [← pow_add]
              congr 1
              omega
            have h2pow : (2 : ℝ) ^ (j - i) ≤ (p : ℝ) ^ (j - i) :=
              pow_le_pow_left₀ (by norm_num) hp2 _
            have h2pos : (0 : ℝ) < 2 ^ (j - i) := by positivity
            rw [hjsplit]
            have e1 : Real.log p * Real.log p * Real.log p
                / ((p : ℝ) ^ i * ((p : ℝ) ^ i * (p : ℝ) ^ (j - i)))
                = Real.log p ^ 3 / ((p : ℝ) ^ i) ^ 2 * (1 / (p : ℝ) ^ (j - i)) := by
              field_simp
            have e2 : (1 / 2 : ℝ) ^ (j - i) = 1 / (2 : ℝ) ^ (j - i) := by
              rw [one_div, inv_pow, one_div]
            rw [e1, e2]
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            exact one_div_le_one_div_of_le h2pos h2pow
    _ = Real.log p ^ 3 / ((p : ℝ) ^ i) ^ 2 * ∑ k ∈ Finset.range (M + 1), (1 / 2 : ℝ) ^ k := by
        rw [Finset.mul_sum]
    _ ≤ Real.log p ^ 3 / ((p : ℝ) ^ i) ^ 2 * 2 :=
        mul_le_mul_of_nonneg_left (sum_geometric_two_le _) (by positivity)
    _ = 2 * (Real.log p ^ 3 / ((p : ℝ) ^ i) ^ 2) := by ring

/-- `Λ(a)³/a² ≤ 216 / a^{3/2}` -/
theorem vonMangoldt_cube_div_sq_le (a : ℕ) (ha : 1 ≤ a) :
    Λ a ^ 3 / (a : ℝ) ^ 2 ≤ 216 * (1 / (a : ℝ) ^ (3 / 2 : ℝ)) := by
  have hapos : (0 : ℝ) < a := by exact_mod_cast ha
  have h1 : Λ a ≤ 6 * (a : ℝ) ^ (1 / 6 : ℝ) := by
    have h := Real.log_le_rpow_div hapos.le (by norm_num : (0 : ℝ) < 1 / 6)
    have h2 := ArithmeticFunction.vonMangoldt_le_log (n := a)
    have h3 : (a : ℝ) ^ (1 / 6 : ℝ) / (1 / 6) = 6 * (a : ℝ) ^ (1 / 6 : ℝ) := by ring
    linarith
  have h3 : Λ a ^ 3 ≤ 216 * (a : ℝ) ^ (1 / 2 : ℝ) := by
    calc Λ a ^ 3 ≤ (6 * (a : ℝ) ^ (1 / 6 : ℝ)) ^ 3 :=
          pow_le_pow_left₀ ArithmeticFunction.vonMangoldt_nonneg h1 3
      _ = 216 * ((a : ℝ) ^ (1 / 6 : ℝ)) ^ (3 : ℕ) := by ring
      _ = 216 * (a : ℝ) ^ (1 / 2 : ℝ) := by
          rw [← Real.rpow_mul_natCast hapos.le]
          norm_num
  have h4 : (a : ℝ) ^ 2 = (a : ℝ) ^ (1 / 2 : ℝ) * (a : ℝ) ^ (3 / 2 : ℝ) := by
    rw [← Real.rpow_add hapos, ← Real.rpow_two]
    norm_num
  have hpos1 : (0 : ℝ) < (a : ℝ) ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hapos _
  have hpos2 : (0 : ℝ) < (a : ℝ) ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos hapos _
  rw [h4, div_le_iff₀ (mul_pos hpos1 hpos2)]
  calc Λ a ^ 3 ≤ 216 * (a : ℝ) ^ (1 / 2 : ℝ) := h3
    _ = 216 * (1 / (a : ℝ) ^ (3 / 2 : ℝ)) * ((a : ℝ) ^ (1 / 2 : ℝ) * (a : ℝ) ^ (3 / 2 : ℝ)) := by
        field_simp

end PrimeSum

/-- the three-prime sum is bounded: if `Λ(a) Λ(b) Λ(ab) ≠ 0` then `a`, `b` are powers of one prime. -/
theorem triplePrime_bound :
    ∃ C : ℝ, ∀ M : ℕ,
      ∑ a ∈ Finset.Icc 2 M, ∑ b ∈ Finset.Icc 2 M, Λ a * Λ b * Λ (a * b) / ((a : ℝ) * b) ≤ C := by
  have hsum : Summable (fun n : ℕ => 1 / (n : ℝ) ^ (3 / 2 : ℝ)) :=
    Real.summable_one_div_nat_rpow.mpr (by norm_num)
  refine ⟨4 * (216 * ∑' n : ℕ, 1 / (n : ℝ) ^ (3 / 2 : ℝ)), fun M => ?_⟩
  set t : ℕ → ℕ → ℝ := fun a b => Λ a * Λ b * Λ (a * b) / ((a : ℝ) * b) with ht
  have ht0 : ∀ a b, 0 ≤ t a b := fun a b =>
    div_nonneg (mul_nonneg (mul_nonneg ArithmeticFunction.vonMangoldt_nonneg
      ArithmeticFunction.vonMangoldt_nonneg) ArithmeticFunction.vonMangoldt_nonneg)
      (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  have hsymm : ∀ a b, t a b = t b a := by
    intro a b
    simp only [ht]
    rw [mul_comm b a]
    ring
  have hsplit : ∀ a b, t a b ≤ (if a ≤ b then t a b else 0) + (if b ≤ a then t b a else 0) := by
    intro a b
    rcases le_total a b with h | h
    · have h0 : 0 ≤ (if b ≤ a then t b a else 0) := by
        split_ifs
        · exact ht0 _ _
        · exact le_rfl
      rw [if_pos h]
      linarith
    · have h0 : 0 ≤ (if a ≤ b then t a b else 0) := by
        split_ifs
        · exact ht0 _ _
        · exact le_rfl
      rw [if_pos h, hsymm b a]
      linarith
  have hinner : ∀ a ∈ Finset.Icc 2 M, ∑ b ∈ Finset.Icc 2 M, (if a ≤ b then t a b else 0)
      ≤ 2 * (216 * (1 / (a : ℝ) ^ (3 / 2 : ℝ))) := by
    intro a ha
    have h1 := triple_inner a M
    have h2 := vonMangoldt_cube_div_sq_le a (by have := (Finset.mem_Icc.mp ha).1; omega)
    exact h1.trans (by linarith)
  calc ∑ a ∈ Finset.Icc 2 M, ∑ b ∈ Finset.Icc 2 M, t a b
      ≤ ∑ a ∈ Finset.Icc 2 M, ∑ b ∈ Finset.Icc 2 M,
          ((if a ≤ b then t a b else 0) + (if b ≤ a then t b a else 0)) :=
        Finset.sum_le_sum (fun a _ => Finset.sum_le_sum (fun b _ => hsplit a b))
    _ = ∑ a ∈ Finset.Icc 2 M, ∑ b ∈ Finset.Icc 2 M, (if a ≤ b then t a b else 0)
          + ∑ a ∈ Finset.Icc 2 M, ∑ b ∈ Finset.Icc 2 M, (if b ≤ a then t b a else 0) := by
        simp only [Finset.sum_add_distrib]
    _ = 2 * ∑ a ∈ Finset.Icc 2 M, ∑ b ∈ Finset.Icc 2 M, (if a ≤ b then t a b else 0) := by
        rw [Finset.sum_comm (f := fun a b => if b ≤ a then t b a else 0)]
        ring
    _ ≤ 2 * ∑ a ∈ Finset.Icc 2 M, 2 * (216 * (1 / (a : ℝ) ^ (3 / 2 : ℝ))) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum hinner) (by norm_num)
    _ = 4 * (216 * ∑ a ∈ Finset.Icc 2 M, 1 / (a : ℝ) ^ (3 / 2 : ℝ)) := by
        rw [← Finset.mul_sum, ← Finset.mul_sum]
        ring
    _ ≤ 4 * (216 * ∑' n : ℕ, 1 / (n : ℝ) ^ (3 / 2 : ℝ)) := by
        have h := hsum.sum_le_tsum (Finset.Icc 2 M) (fun n _ => by positivity)
        linarith

end TMA

end
end Src_TMA_PrimeSum

section Src_TMA_Kernel
/-
Written for Kristian Muri Knausgård, drafted with Claude (Anthropic), 22 November 2026.

TMA/Kernel.lean — the kernel identity: under RH, for |x| ≤ 1 the zero-side kernel `Kfull` equals the
prime-side kernel `K0` up to an error that is small in three norms (from Zeta23's explicit formula
`EF_lit_zetaZeroConfig` and its Gamma estimates).
STATUS: complete (all proofs supplied).  See BLUEPRINT.md, module "Kernel".

Plan of the proof (helper lemmas live in the namespace `TMA.Kernel`):
* test function `F_x(u) = T k(T (u - σ L x))`, `L = log T`; `paperFT F_x z = e^{i z σ L x} paperFT k (z/T)`;
* under RH the zero sum of `EF_lit` for `F_x` is `Kfull w.h T σ x`, so `Kfull = literatureRHS F_x`;
* for `|x| ≤ 1`, `T ≥ max 3 (κ / log 2)`: the prime sum of `literatureRHS F_x` is the finite sum in `K0`;
  the Gamma integral is `ℓ · packet 0 + T k_ω(A x) + R(A x)` (`Ω(Ts) = ℓ + ω_T(s) + ρ(Ts)`,
  `|ρ(r)| ≤ C/(1+r²)`); so `Kfull - K0 = poles + T k_ω(A x) + R(A x)` and
  `‖Kfull - K0‖ ≤ c₀ / L + T C_g / (1 + (A x)²)`.
-/

open MeasureTheory Complex
open scoped BigOperators ArithmeticFunction Real

noncomputable section
namespace TMA

theorem cw_nonneg (w : HeightWeight) (T : ℝ) (ρ : ℂ) : 0 ≤ cw w.h T ρ :=
  mul_nonneg (Nat.cast_nonneg _) (w.h_nonneg _)

theorem norm_phase (T σ : ℝ) (ρ : ℂ) (x : ℝ) : ‖phase T σ ρ x‖ = 1 := by
  unfold phase
  rw [mul_comm]
  exact Complex.norm_exp_ofReal_mul_I _

namespace Kernel

/-! ## The test function -/

/-- the test function `F_x(u) = T k(T (u - σ (log T) x))` -/
def Fx (w : HeightWeight) (T σ x : ℝ) (u : ℝ) : ℂ :=
  (T : ℂ) * w.k (T * (u - σ * Real.log T * x))

theorem Fx_contDiff (w : HeightWeight) (T σ x : ℝ) : ContDiff ℝ 2 (Fx w T σ x) := by
  unfold Fx
  exact contDiff_const.mul (w.k_contDiff.comp (by fun_prop))

theorem k_hasCompactSupport (w : HeightWeight) : HasCompactSupport w.k :=
  Zeta23.hasCompactSupport_of_support_subset_abs w.k_supp

theorem k_integrable (w : HeightWeight) : Integrable w.k :=
  w.k_contDiff.continuous.integrable_of_hasCompactSupport (k_hasCompactSupport w)

theorem Fx_hasCompactSupport (w : HeightWeight) {T : ℝ} (hT : 0 < T) (σ x : ℝ) :
    HasCompactSupport (Fx w T σ x) := by
  have key : ∀ u, Fx w T σ x u ≠ 0 → |u| ≤ w.kappa / T + |σ * Real.log T * x| := by
    intro u hu
    have hk : w.k (T * (u - σ * Real.log T * x)) ≠ 0 := by
      intro h0; apply hu; unfold Fx; rw [h0, mul_zero]
    have h1 := w.k_supp _ hk
    rw [abs_mul, abs_of_pos hT] at h1
    have h2 : |u - σ * Real.log T * x| ≤ w.kappa / T := by
      rw [le_div_iff₀ hT]; linarith [mul_comm T |u - σ * Real.log T * x|]
    calc |u| = |(u - σ * Real.log T * x) + σ * Real.log T * x| := by ring_nf
      _ ≤ |u - σ * Real.log T * x| + |σ * Real.log T * x| := abs_add_le _ _
      _ ≤ _ := by linarith
  exact Zeta23.hasCompactSupport_of_support_subset_abs key

/-- `paperFT F_x z = e^{i z σ L x} paperFT k (z / T)` -/
theorem paperFT_Fx (w : HeightWeight) {T : ℝ} (hT : 0 < T) (σ x : ℝ) (z : ℂ) :
    Zeta23.paperFT (Fx w T σ x) z
      = Complex.exp (Complex.I * z * ((σ * Real.log T * x : ℝ) : ℂ)) * Zeta23.paperFT w.k (z / T) := by
  set c : ℝ := σ * Real.log T * x with hc
  have hT0 : (T : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hT.ne'
  set G : ℝ → ℂ :=
    fun v => (T : ℂ) * (w.k v * Complex.exp (Complex.I * z * ((v / T + c : ℝ) : ℂ))) with hG
  have h1 : Zeta23.paperFT (Fx w T σ x) z = ∫ u : ℝ, G (T * (u - c)) := by
    unfold Zeta23.paperFT Fx
    congr 1; ext u
    simp only [hG]
    have : T * (u - c) / T + c = u := by field_simp; ring
    rw [this]; ring
  rw [h1, integral_sub_right_eq_self (fun u : ℝ => G (T * u)) c,
    Measure.integral_comp_mul_left G T, abs_of_pos (inv_pos.mpr hT)]
  simp only [hG]
  rw [Zeta23.integral_const_mul_C, Complex.real_smul, ← mul_assoc]
  have : ((T⁻¹ : ℝ) : ℂ) * (T : ℂ) = 1 := by
    rw [Complex.ofReal_inv]; exact inv_mul_cancel₀ hT0
  rw [this, one_mul]
  unfold Zeta23.paperFT
  rw [← Zeta23.integral_const_mul_C]
  congr 1; ext v
  rw [mul_left_comm, ← Complex.exp_add]
  congr 2
  push_cast
  field_simp
  ring

/-! ## The zero side -/

theorem gammaOf_eq_im (hRH : RiemannHypothesis) {ρ : ℂ} (hρ : Zeta23.IsNontrivialZero ρ) :
    Zeta23.gammaOf ρ = (ρ.im : ℂ) := by
  have hre := Zeta23.RH_implies_on_line hRH hρ
  unfold Zeta23.gammaOf
  rw [div_eq_iff Complex.I_ne_zero]
  apply Complex.ext <;> simp [hre]

theorem zero_term (hRH : RiemannHypothesis) (w : HeightWeight) {T : ℝ} (hT : 0 < T) (σ x : ℝ)
    (ρ : Zeta23.zetaZeroConfig.carrier) :
    (Zeta23.zetaZeroConfig.mult ρ : ℂ) * Zeta23.paperFT (Fx w T σ x) (Zeta23.gammaOf ρ)
      = (cw w.h T ρ : ℂ) * phase T σ ρ x := by
  have hρ : Zeta23.IsNontrivialZero (ρ : ℂ) := ρ.2
  rw [gammaOf_eq_im hRH hρ, paperFT_Fx w hT]
  have h1 : (((ρ : ℂ).im : ℝ) : ℂ) / (T : ℂ) = (((ρ : ℂ).im / T : ℝ) : ℂ) := by push_cast; rfl
  have h2 : Complex.I * (((ρ : ℂ).im : ℝ) : ℂ) * ((σ * Real.log T * x : ℝ) : ℂ)
      = Complex.I * ((σ * Real.log T * (ρ : ℂ).im * x : ℝ) : ℂ) := by push_cast; ring
  rw [h1, w.h_eq, h2]
  unfold cw phase
  rw [Zeta23.zetaZeroConfig_mult]
  push_cast
  ring

theorem summable_cw_phase (hRH : RiemannHypothesis) (w : HeightWeight) {T : ℝ} (hT : 0 < T)
    (σ x : ℝ) :
    Summable (fun ρ : Zeta23.zetaZeroConfig.carrier => (cw w.h T ρ : ℂ) * phase T σ ρ x) := by
  have h := (Zeta23.WeilEF.EF_lit_zetaZeroConfig (Fx w T σ x) (Fx_contDiff w T σ x)
    (Fx_hasCompactSupport w hT σ x)).1
  exact h.congr (fun ρ => zero_term hRH w hT σ x ρ)

theorem Kfull_eq_literatureRHS (hRH : RiemannHypothesis) (w : HeightWeight) {T : ℝ} (hT : 0 < T)
    (σ x : ℝ) : Kfull w.h T σ x = Zeta23.EF.literatureRHS (Fx w T σ x) := by
  rw [← (Zeta23.WeilEF.EF_lit_zetaZeroConfig (Fx w T σ x) (Fx_contDiff w T σ x)
    (Fx_hasCompactSupport w hT σ x)).2]
  unfold Kfull
  exact tsum_congr (fun ρ => (zero_term hRH w hT σ x ρ).symm)

theorem phase_zero (T σ : ℝ) (ρ : ℂ) : phase T σ ρ 0 = 1 := by simp [phase]

end Kernel

/-- under RH the weights of the zeros are summable -/
theorem summable_cw (hRH : RiemannHypothesis) (w : HeightWeight) {T : ℝ} (hT : 0 < T) :
    Summable (fun ρ : Zeta23.zetaZeroConfig.carrier => cw w.h T ρ) := by
  have h := Kernel.summable_cw_phase hRH w hT 0 0
  simp only [Kernel.phase_zero, mul_one] at h
  exact Complex.summable_ofReal.mp h

theorem Kfull_zero (w : HeightWeight) (T σ : ℝ) :
    Kfull w.h T σ 0 = ((∑' ρ : Zeta23.zetaZeroConfig.carrier, cw w.h T ρ : ℝ) : ℂ) := by
  unfold Kfull
  simp only [Kernel.phase_zero, mul_one]
  exact (Complex.ofReal_tsum _).symm

theorem continuous_Kfull (hRH : RiemannHypothesis) (w : HeightWeight) {T : ℝ} (hT : 0 < T) (σ : ℝ) :
    Continuous (Kfull w.h T σ) := by
  show Continuous (fun x => ∑' ρ : Zeta23.zetaZeroConfig.carrier, (cw w.h T ρ : ℂ) * phase T σ ρ x)
  refine continuous_tsum (u := fun ρ : Zeta23.zetaZeroConfig.carrier => cw w.h T ρ) (fun ρ => ?_)
    (summable_cw hRH w hT) (fun ρ x => ?_)
  · unfold phase; fun_prop
  · rw [norm_mul, norm_phase, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (cw_nonneg w T ρ)]

namespace Kernel

theorem continuous_packet (w : HeightWeight) (T σ lam : ℝ) : Continuous (packet w.k T σ lam) := by
  have hk := w.k_contDiff.continuous
  unfold packet
  fun_prop

end Kernel

theorem continuous_K0 (w : HeightWeight) (T σ : ℝ) : Continuous (K0 w.k T σ) := by
  unfold K0
  refine (continuous_const.mul (Kernel.continuous_packet w T σ 0)).sub ?_
  refine continuous_finsetSum _ (fun n _ => ?_)
  exact continuous_const.mul
    ((Kernel.continuous_packet w T σ _).add (Kernel.continuous_packet w T σ _))

namespace Kernel

/-! ## The prime sum -/

theorem Fx_log (w : HeightWeight) {T σ : ℝ} (hσL : σ * Real.log T ≠ 0) (x : ℝ) (n : ℕ) :
    Fx w T σ x (Real.log n) = packet w.k T σ (lamOf T σ n) x := by
  have hσ0 : σ ≠ 0 := left_ne_zero_of_mul hσL
  have hL0 : Real.log T ≠ 0 := right_ne_zero_of_mul hσL
  unfold Fx packet lamOf Asc
  congr 2
  field_simp
  ring

theorem Fx_neg_log (w : HeightWeight) {T σ : ℝ} (hσL : σ * Real.log T ≠ 0) (x : ℝ) (n : ℕ) :
    Fx w T σ x (-Real.log n) = packet w.k T σ (-(lamOf T σ n)) x := by
  have hσ0 : σ ≠ 0 := left_ne_zero_of_mul hσL
  have hL0 : Real.log T ≠ 0 := right_ne_zero_of_mul hσL
  unfold Fx packet lamOf Asc
  congr 2
  field_simp
  ring

theorem k_eq_zero_of_lt (w : HeightWeight) {u : ℝ} (hu : w.kappa < |u|) : w.k u = 0 := by
  by_contra h
  exact absurd (w.k_supp u h) (not_le.mpr hu)

theorem prime_tsum (w : HeightWeight) {T σ : ℝ} (hT : 1 < T) (hTκ : w.kappa ≤ T * Real.log 2)
    (hσ : 0 < σ) {x : ℝ} (hx : |x| ≤ 1) :
    ∑' n : ℕ, ((Λ n / Real.sqrt n : ℝ) : ℂ)
        * (Fx w T σ x (Real.log n) + Fx w T σ x (-Real.log n))
      = ∑ n ∈ Finset.Icc 2 (Nmax T σ), (lamCoeff n : ℂ)
        * (packet w.k T σ (lamOf T σ n) x + packet w.k T σ (-(lamOf T σ n)) x) := by
  have hT0 : 0 < T := by linarith
  have hL : 0 < Real.log T := Real.log_pos hT
  have hσL : σ * Real.log T ≠ 0 := (mul_pos hσ hL).ne'
  rw [tsum_eq_sum (s := Finset.Icc 2 (Nmax T σ))]
  · refine Finset.sum_congr rfl fun n _ => ?_
    rw [Fx_log w hσL, Fx_neg_log w hσL]
    rfl
  · intro n hn
    rw [Finset.mem_Icc, not_and_or, not_le, not_le] at hn
    rcases hn with hn | hn
    · have h0 : (Λ n : ℝ) = 0 := by
        interval_cases n
        · simp
        · exact ArithmeticFunction.vonMangoldt_apply_one
      rw [h0]; simp
    · have hpow : 0 < T ^ σ := Real.rpow_pos_of_pos hT0 σ
      have hn' : 2 * T ^ σ < (n : ℝ) := (Nat.floor_lt (by positivity)).mp hn
      have hlog : Real.log 2 + σ * Real.log T < Real.log n := by
        have := Real.log_lt_log (by positivity) hn'
        rwa [Real.log_mul (by norm_num) hpow.ne', Real.log_rpow hT0] at this
      obtain ⟨hx1, hx2⟩ := abs_le.mp hx
      have hc1 : σ * Real.log T * x ≤ σ * Real.log T := by
        nlinarith [mul_pos hσ hL]
      have hc2 : -(σ * Real.log T) ≤ σ * Real.log T * x := by
        nlinarith [mul_pos hσ hL]
      have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
      have h1 : Fx w T σ x (Real.log n) = 0 := by
        unfold Fx
        rw [k_eq_zero_of_lt w, mul_zero]
        have : T * Real.log 2 < T * (Real.log n - σ * Real.log T * x) :=
          mul_lt_mul_of_pos_left (by linarith) hT0
        exact lt_of_lt_of_le (by linarith) (le_abs_self _)
      have h2 : Fx w T σ x (-Real.log n) = 0 := by
        unfold Fx
        rw [k_eq_zero_of_lt w, mul_zero]
        have : T * (-Real.log n - σ * Real.log T * x) < T * (-Real.log 2) :=
          mul_lt_mul_of_pos_left (by linarith) hT0
        exact lt_of_lt_of_le (by linarith) (neg_le_abs _)
      rw [h1, h2, add_zero, mul_zero]

/-! ## The Gamma term -/

/-- the Stirling remainder `ρ(r) = Ω(r) - ½ log (r² + 1) + log 2π`, `Ω = gammaBracket` -/
def rho (r : ℝ) : ℝ :=
  Zeta23.EF.gammaBracket r - (1 / 2) * Real.log (r ^ 2 + 1) + Real.log (2 * π)

theorem gammaBracket_eq_mu (r : ℝ) : Zeta23.EF.gammaBracket r = 2 * π * Zeta23.mu r := by
  unfold Zeta23.EF.gammaBracket Zeta23.mu
  field_simp

theorem continuous_gammaBracket : Continuous Zeta23.EF.gammaBracket := by
  have : Zeta23.EF.gammaBracket = fun r => 2 * π * Zeta23.mu r := funext gammaBracket_eq_mu
  rw [this]
  exact continuous_const.mul Zeta23.gammaFacts.smooth.continuous

theorem continuous_rho : Continuous rho := by
  unfold rho
  refine (continuous_gammaBracket.sub (continuous_const.mul ?_)).add continuous_const
  exact Continuous.log (by fun_prop) (fun r => by positivity)

theorem rho_bound : ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, |rho r| ≤ C / (1 + r ^ 2) := by
  obtain ⟨C, hC⟩ := Zeta23.gammaFacts.stirling
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (continuous_rho.continuousOn (s := Set.Icc (-1 : ℝ) 1))
  have hπ := Real.pi_pos
  have hM0 : 0 ≤ max M 0 := le_max_right _ _
  refine ⟨2 * (max M 0 + (2 * π * |C| + 1 / 2)), by positivity, fun r => ?_⟩
  rw [le_div_iff₀ (by positivity)]
  rcases le_or_gt |r| 1 with hr | hr
  · have h1 := hM r (abs_le.mp hr)
    rw [Real.norm_eq_abs] at h1
    have hr2 : r ^ 2 ≤ 1 := by rw [← sq_abs]; nlinarith [abs_nonneg r]
    have h2 : |rho r| ≤ max M 0 := h1.trans (le_max_left _ _)
    have h3 : 0 ≤ 2 * π * |C| + 1 / 2 := by positivity
    calc |rho r| * (1 + r ^ 2) ≤ max M 0 * 2 :=
          mul_le_mul h2 (by linarith) (by positivity) hM0
      _ ≤ _ := by linarith
  · have hst := hC r hr.le
    have hr2 : 1 < r ^ 2 := by rw [← sq_abs]; nlinarith [abs_nonneg r]
    have hr2pos : 0 < r ^ 2 := by linarith
    have habs : 0 < |r| := by linarith
    have hlogsq : Real.log (r ^ 2) = 2 * Real.log |r| := by
      rw [← sq_abs, Real.log_pow]; norm_num
    have hsplit : Real.log (r ^ 2 + 1) = Real.log (r ^ 2) + Real.log (1 + 1 / r ^ 2) := by
      rw [← Real.log_mul hr2pos.ne' (by positivity)]
      congr 1
      rw [mul_add, mul_one, mul_one_div_cancel hr2pos.ne']
    have key : rho r = 2 * π * (Zeta23.mu r - 1 / (2 * π) * Real.log (|r| / (2 * π)))
        - (1 / 2) * Real.log (1 + 1 / r ^ 2) := by
      unfold rho
      rw [gammaBracket_eq_mu, hsplit, hlogsq, Real.log_div habs.ne' (by positivity)]
      field_simp
      ring
    have hl0 : 0 ≤ Real.log (1 + 1 / r ^ 2) := Real.log_nonneg (by
      have : 0 ≤ 1 / r ^ 2 := by positivity
      linarith)
    have hl1 : Real.log (1 + 1 / r ^ 2) ≤ 1 / r ^ 2 := by
      have := Real.log_le_sub_one_of_pos (show 0 < 1 + 1 / r ^ 2 by positivity)
      linarith
    have hCle : C / r ^ 2 ≤ |C| / r ^ 2 := by gcongr; exact le_abs_self C
    have h5 : |rho r| ≤ (2 * π * |C| + 1 / 2) / r ^ 2 := by
      rw [key]
      calc |2 * π * (Zeta23.mu r - 1 / (2 * π) * Real.log (|r| / (2 * π)))
              - (1 / 2) * Real.log (1 + 1 / r ^ 2)|
          ≤ |2 * π * (Zeta23.mu r - 1 / (2 * π) * Real.log (|r| / (2 * π)))|
              + |(1 / 2) * Real.log (1 + 1 / r ^ 2)| := abs_sub _ _
        _ = 2 * π * |Zeta23.mu r - 1 / (2 * π) * Real.log (|r| / (2 * π))|
              + (1 / 2) * Real.log (1 + 1 / r ^ 2) := by
            rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * π),
              abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / 2 * Real.log (1 + 1 / r ^ 2))]
        _ ≤ 2 * π * (|C| / r ^ 2) + (1 / 2) * (1 / r ^ 2) := by
            gcongr
            exact hst.trans hCle
        _ = (2 * π * |C| + 1 / 2) / r ^ 2 := by ring
    have h3 : 0 ≤ 2 * π * |C| + 1 / 2 := by positivity
    calc |rho r| * (1 + r ^ 2) ≤ (2 * π * |C| + 1 / 2) / r ^ 2 * (1 + r ^ 2) := by gcongr
      _ = (2 * π * |C| + 1 / 2) * ((1 + r ^ 2) / r ^ 2) := by ring
      _ ≤ (2 * π * |C| + 1 / 2) * 2 := by
          gcongr
          rw [div_le_iff₀ hr2pos]; linarith
      _ ≤ _ := by linarith

/-- `k_ω(y) = (1/2π) ∫ h(s) ω_T(s) e^{isy} ds` -/
def komega (w : HeightWeight) (T y : ℝ) : ℂ :=
  (1 / (2 * π) : ℂ) * ∫ s, (w.h s : ℂ) * (omegaT T s : ℂ) * Complex.exp (Complex.I * s * y)

/-- the remainder of the Gamma term: `(T/2π) ∫ h(s) ρ(Ts) e^{isy} ds` -/
def Rterm (w : HeightWeight) (T y : ℝ) : ℂ :=
  ((T : ℂ) / (2 * π)) * ∫ s, (w.h s : ℂ) * (rho (T * s) : ℂ) * Complex.exp (Complex.I * s * y)

theorem omega_split {T : ℝ} (hT : 0 < T) (s : ℝ) :
    Zeta23.EF.gammaBracket (T * s) = Real.log (T / (2 * π)) + omegaT T s + rho (T * s) := by
  unfold rho omegaT
  have h1 : s ^ 2 + 1 / T ^ 2 = ((T * s) ^ 2 + 1) / T ^ 2 := by field_simp
  rw [h1, Real.log_div hT.ne' (by positivity), Real.log_div (by positivity) (by positivity),
    Real.log_pow]
  push_cast; ring

theorem norm_cexp_I_real (s y : ℝ) : ‖Complex.exp (Complex.I * s * y)‖ = 1 := by
  rw [Complex.norm_exp]; simp

theorem integrable_h_exp (w : HeightWeight) (y : ℝ) :
    Integrable (fun s : ℝ => (w.h s : ℂ) * Complex.exp (Complex.I * s * y)) := by
  refine (w.h_int.ofReal).mul_bdd (c := 1) (Continuous.aestronglyMeasurable (by fun_prop))
    (Filter.Eventually.of_forall fun s => ?_)
  rw [norm_cexp_I_real]

theorem integrable_h_rho_exp (w : HeightWeight) (T y : ℝ) :
    Integrable (fun s : ℝ =>
      (w.h s : ℂ) * (rho (T * s) : ℂ) * Complex.exp (Complex.I * s * y)) := by
  obtain ⟨C, hC0, hC⟩ := rho_bound
  have h1 : Integrable (fun s : ℝ => (w.h s : ℂ) * (rho (T * s) : ℂ)) := by
    refine (w.h_int.ofReal).mul_bdd (c := C) ?_ (Filter.Eventually.of_forall fun s => ?_)
    · exact (Complex.continuous_ofReal.comp
        (continuous_rho.comp (by fun_prop))).aestronglyMeasurable
    · rw [Complex.norm_real, Real.norm_eq_abs]
      exact (hC _).trans (div_le_self hC0 (by nlinarith [sq_nonneg (T * s)]))
  refine h1.mul_bdd (c := 1) (Continuous.aestronglyMeasurable (by fun_prop))
    (Filter.Eventually.of_forall fun s => ?_)
  rw [norm_cexp_I_real]

theorem integrable_total (w : HeightWeight) {T : ℝ} (hT : 0 < T) (σ x : ℝ) :
    Integrable (fun s : ℝ => Zeta23.paperFT (Fx w T σ x) ((T * s : ℝ) : ℂ)
      * (Zeta23.EF.gammaBracket (T * s) : ℂ)) := by
  have h := Zeta23.EF.integrable_paperFT_mul_mu (Fx_contDiff w T σ x)
    (Fx_hasCompactSupport w hT σ x) Zeta23.gammaFacts
  have h2 : Integrable (fun τ : ℝ =>
      Zeta23.paperFT (Fx w T σ x) (τ : ℂ) * (Zeta23.EF.gammaBracket τ : ℂ)) := by
    refine (h.const_mul (2 * π : ℂ)).congr (Filter.Eventually.of_forall fun τ => ?_)
    simp only [gammaBracket_eq_mu]; push_cast; ring
  exact h2.comp_mul_left' hT.ne'

theorem paperFT_Fx_scaled (w : HeightWeight) {T : ℝ} (hT : 0 < T) (σ x s : ℝ) :
    Zeta23.paperFT (Fx w T σ x) ((T * s : ℝ) : ℂ)
      = (w.h s : ℂ) * Complex.exp (Complex.I * s * ((Asc T σ * x : ℝ) : ℂ)) := by
  have hT0 : (T : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hT.ne'
  rw [paperFT_Fx w hT]
  have h1 : ((T * s : ℝ) : ℂ) / (T : ℂ) = (s : ℂ) := by push_cast; field_simp
  rw [h1, w.h_eq, mul_comm]
  congr 2
  unfold Asc; push_cast; ring

theorem gamma_split (w : HeightWeight) {T : ℝ} (hT : 0 < T) (σ x : ℝ) :
    (1 / (2 * π) : ℂ) * ∫ r : ℝ, Zeta23.paperFT (Fx w T σ x) r * (Zeta23.EF.gammaBracket r : ℂ)
      = (Real.log (T / (2 * π)) : ℂ) * packet w.k T σ 0 x
        + (T : ℂ) * komega w T (Asc T σ * x) + Rterm w T (Asc T σ * x) := by
  have hsub : ∫ r : ℝ, Zeta23.paperFT (Fx w T σ x) r * (Zeta23.EF.gammaBracket r : ℂ)
      = (T : ℂ) * ∫ s : ℝ, Zeta23.paperFT (Fx w T σ x) ((T * s : ℝ) : ℂ)
          * (Zeta23.EF.gammaBracket (T * s) : ℂ) := by
    rw [Measure.integral_comp_mul_left
      (fun r : ℝ => Zeta23.paperFT (Fx w T σ x) r * (Zeta23.EF.gammaBracket r : ℂ)) T,
      abs_of_pos (inv_pos.mpr hT), Complex.real_smul, ← mul_assoc, Complex.ofReal_inv,
      mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr hT.ne'), one_mul]
  have hI1 := integrable_h_exp w (Asc T σ * x)
  have hI3 := integrable_h_rho_exp w T (Asc T σ * x)
  have hItot := integrable_total w hT σ x
  have hpt : ∀ s : ℝ, Zeta23.paperFT (Fx w T σ x) ((T * s : ℝ) : ℂ)
        * (Zeta23.EF.gammaBracket (T * s) : ℂ)
      = ((Real.log (T / (2 * π)) : ℂ)
            * ((w.h s : ℂ) * Complex.exp (Complex.I * s * ((Asc T σ * x : ℝ) : ℂ)))
          + (w.h s : ℂ) * (omegaT T s : ℂ) * Complex.exp (Complex.I * s * ((Asc T σ * x : ℝ) : ℂ)))
        + (w.h s : ℂ) * (rho (T * s) : ℂ) * Complex.exp (Complex.I * s * ((Asc T σ * x : ℝ) : ℂ)) := by
    intro s
    rw [paperFT_Fx_scaled w hT, omega_split hT s]
    push_cast; ring
  have hb : Integrable (fun s : ℝ =>
      (w.h s : ℂ) * (omegaT T s : ℂ) * Complex.exp (Complex.I * s * ((Asc T σ * x : ℝ) : ℂ))) := by
    refine ((hItot.sub (hI1.const_mul (Real.log (T / (2 * π)) : ℂ))).sub hI3).congr
      (Filter.Eventually.of_forall fun s => ?_)
    simp only [Pi.sub_apply]
    rw [hpt s]; ring
  have hint : ∫ s : ℝ, Zeta23.paperFT (Fx w T σ x) ((T * s : ℝ) : ℂ)
        * (Zeta23.EF.gammaBracket (T * s) : ℂ)
      = (Real.log (T / (2 * π)) : ℂ)
            * (∫ s : ℝ, (w.h s : ℂ) * Complex.exp (Complex.I * s * ((Asc T σ * x : ℝ) : ℂ)))
          + (∫ s : ℝ, (w.h s : ℂ) * (omegaT T s : ℂ)
              * Complex.exp (Complex.I * s * ((Asc T σ * x : ℝ) : ℂ)))
          + ∫ s : ℝ, (w.h s : ℂ) * (rho (T * s) : ℂ)
              * Complex.exp (Complex.I * s * ((Asc T σ * x : ℝ) : ℂ)) := by
    have hA : Integrable (fun s : ℝ => (Real.log (T / (2 * π)) : ℂ)
        * ((w.h s : ℂ) * Complex.exp (Complex.I * s * ((Asc T σ * x : ℝ) : ℂ)))) :=
      hI1.const_mul _
    have hAB : Integrable (fun s : ℝ => (Real.log (T / (2 * π)) : ℂ)
          * ((w.h s : ℂ) * Complex.exp (Complex.I * s * ((Asc T σ * x : ℝ) : ℂ)))
        + (w.h s : ℂ) * (omegaT T s : ℂ)
          * Complex.exp (Complex.I * s * ((Asc T σ * x : ℝ) : ℂ))) := hA.add hb
    rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_add hAB hI3,
      integral_add hA hb, Zeta23.integral_const_mul_C]
  have hinv := w.inv (Asc T σ * x)
  rw [hsub, hint]
  unfold komega Rterm packet
  rw [sub_zero, ← hinv]
  ring

/-! ## Bounds for the three error terms -/

theorem norm_Rterm_le (w : HeightWeight) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 1 ≤ T → ∀ y : ℝ, ‖Rterm w T y‖ ≤ C / T := by
  obtain ⟨Cρ, hC0, hCρ⟩ := rho_bound
  obtain ⟨B, hB⟩ := w.h_small
  have hB' : 0 ≤ max B 0 := le_max_right _ _
  have hind_int : Integrable (Set.indicator (Set.Icc (-1 : ℝ) 1) (fun _ : ℝ => (1 : ℝ))) :=
    (integrable_indicator_iff measurableSet_Icc).mpr (integrableOn_const (by simp))
  have hind0 : ∀ s : ℝ, 0 ≤ Set.indicator (Set.Icc (-1 : ℝ) 1) (fun _ : ℝ => (1 : ℝ)) s :=
    fun s => Set.indicator_nonneg (fun _ _ => zero_le_one) s
  have hg_int : Integrable (fun s : ℝ =>
      max B 0 * Set.indicator (Set.Icc (-1 : ℝ) 1) (fun _ : ℝ => (1 : ℝ)) s + w.h s) :=
    (hind_int.const_mul _).add w.h_int
  have hJ0 : 0 ≤ ∫ s : ℝ,
      (max B 0 * Set.indicator (Set.Icc (-1 : ℝ) 1) (fun _ : ℝ => (1 : ℝ)) s + w.h s) :=
    integral_nonneg fun s => add_nonneg (mul_nonneg hB' (hind0 s)) (w.h_nonneg s)
  refine ⟨Cρ * (∫ s : ℝ, (max B 0 * Set.indicator (Set.Icc (-1 : ℝ) 1) (fun _ : ℝ => (1 : ℝ)) s
      + w.h s)) / (2 * π), by positivity, fun T hT y => ?_⟩
  have hT0 : 0 < T := by linarith
  have key : ∀ s : ℝ, ‖(w.h s : ℂ) * (rho (T * s) : ℂ) * Complex.exp (Complex.I * s * y)‖
      ≤ Cρ / T ^ 2 * (max B 0 * Set.indicator (Set.Icc (-1 : ℝ) 1) (fun _ : ℝ => (1 : ℝ)) s
          + w.h s) := by
    intro s
    rw [norm_mul, norm_mul, norm_cexp_I_real, mul_one, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (w.h_nonneg s)]
    have hh := w.h_nonneg s
    have h2 : w.h s / (1 + (T * s) ^ 2)
        ≤ (max B 0 * Set.indicator (Set.Icc (-1 : ℝ) 1) (fun _ : ℝ => (1 : ℝ)) s + w.h s)
          / T ^ 2 := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      by_cases hs : |s| ≤ 1
      · rw [Set.indicator_of_mem (show s ∈ Set.Icc (-1 : ℝ) 1 from abs_le.mp hs)]
        have h3 : w.h s ≤ max B 0 * s ^ 2 :=
          (hB s hs).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg s))
        have h4 : w.h s * T ^ 2 ≤ max B 0 * s ^ 2 * T ^ 2 :=
          mul_le_mul_of_nonneg_right h3 (by positivity)
        nlinarith [mul_nonneg hh (sq_nonneg (T * s))]
      · rw [Set.indicator_of_notMem (show s ∉ Set.Icc (-1 : ℝ) 1 from fun h => hs (abs_le.mpr h))]
        have hs2 : 1 ≤ s ^ 2 := by
          rw [← sq_abs]; nlinarith [not_le.mp hs]
        have h5 : T ^ 2 ≤ (T * s) ^ 2 := by
          rw [mul_pow]; nlinarith [sq_nonneg T]
        nlinarith
    calc w.h s * |rho (T * s)| ≤ w.h s * (Cρ / (1 + (T * s) ^ 2)) := by
          gcongr; exact hCρ _
      _ = Cρ * (w.h s / (1 + (T * s) ^ 2)) := by ring
      _ ≤ Cρ * ((max B 0 * Set.indicator (Set.Icc (-1 : ℝ) 1) (fun _ : ℝ => (1 : ℝ)) s + w.h s)
            / T ^ 2) := by gcongr
      _ = _ := by ring
  have hbd := norm_integral_le_of_norm_le (hg_int.const_mul (Cρ / T ^ 2))
    (Filter.Eventually.of_forall key)
  rw [integral_const_mul] at hbd
  unfold Rterm
  rw [norm_mul]
  have hn : ‖(T : ℂ) / (2 * π)‖ = T / (2 * π) := by
    have : (T : ℂ) / (2 * π) = ((T / (2 * π) : ℝ) : ℂ) := by push_cast; ring
    rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  rw [hn]
  calc T / (2 * π) * ‖∫ s : ℝ, (w.h s : ℂ) * (rho (T * s) : ℂ) * Complex.exp (Complex.I * s * y)‖
      ≤ T / (2 * π) * (Cρ / T ^ 2 * ∫ s : ℝ,
          (max B 0 * Set.indicator (Set.Icc (-1 : ℝ) 1) (fun _ : ℝ => (1 : ℝ)) s + w.h s)) := by
        gcongr
    _ = _ := by field_simp

theorem norm_paperFT_k_le (w : HeightWeight) {z : ℂ} (hz : ‖z‖ * w.kappa ≤ 1) :
    ‖Zeta23.paperFT w.k z‖ ≤ 2 * ‖z‖ * w.kappa * ∫ u, ‖w.k u‖ := by
  have hk := k_integrable w
  have hke : Integrable (fun u : ℝ => w.k u * Complex.exp (Complex.I * z * u)) :=
    (w.k_contDiff.continuous.mul (by fun_prop)).integrable_of_hasCompactSupport
      (k_hasCompactSupport w).mul_right
  have h1 : Zeta23.paperFT w.k z
      = ∫ u : ℝ, w.k u * (Complex.exp (Complex.I * z * u) - 1) := by
    unfold Zeta23.paperFT
    have : ∫ u : ℝ, w.k u * (Complex.exp (Complex.I * z * u) - 1)
        = (∫ u : ℝ, w.k u * Complex.exp (Complex.I * z * u)) - ∫ u, w.k u := by
      rw [← integral_sub hke hk]; congr 1; ext u; ring
    rw [this, w.k_integral_zero, sub_zero]
  rw [h1]
  have hbd := norm_integral_le_of_norm_le (hk.norm.const_mul (2 * ‖z‖ * w.kappa))
    (f := fun u : ℝ => w.k u * (Complex.exp (Complex.I * z * u) - 1))
    (Filter.Eventually.of_forall fun u => ?_)
  · rwa [integral_const_mul] at hbd
  · rw [norm_mul]
    by_cases hu : w.k u = 0
    · simp [hu]
    · have hκ := w.k_supp u hu
      have hn : ‖Complex.I * z * (u : ℂ)‖ = ‖z‖ * |u| := by
        rw [norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
      have hle : ‖Complex.I * z * (u : ℂ)‖ ≤ 1 := by
        rw [hn]; exact (mul_le_mul_of_nonneg_left hκ (norm_nonneg z)).trans hz
      have h3 := Complex.norm_exp_sub_one_le hle
      rw [mul_comm]
      gcongr
      calc ‖Complex.exp (Complex.I * z * u) - 1‖ ≤ 2 * ‖Complex.I * z * u‖ := h3
        _ = 2 * (‖z‖ * |u|) := by rw [hn]
        _ ≤ 2 * (‖z‖ * w.kappa) := by gcongr
        _ = _ := by ring

theorem norm_pole_le (w : HeightWeight) {T σ : ℝ} (hT : 1 < T) (hTκ : w.kappa ≤ T)
    (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) {x : ℝ} (hx : |x| ≤ 1) {ε : ℂ} (hε : ‖ε‖ = 1 / 2) :
    ‖Zeta23.paperFT (Fx w T σ x) ε‖ ≤ 2 * (w.kappa * ∫ u, ‖w.k u‖) / Real.log T := by
  have hT0 : 0 < T := by linarith
  have hL : 0 < Real.log T := Real.log_pos hT
  rw [paperFT_Fx w hT0, norm_mul]
  have hc : |σ * Real.log T * x| ≤ Real.log T := by
    rw [abs_mul, abs_mul, abs_of_nonneg hσ0, abs_of_pos hL]
    calc σ * Real.log T * |x| ≤ 1 * Real.log T * 1 := by gcongr
      _ = Real.log T := by ring
  have hexp : ‖Complex.exp (Complex.I * ε * ((σ * Real.log T * x : ℝ) : ℂ))‖
      ≤ Real.exp (Real.log T / 2) := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    calc (Complex.I * ε * ((σ * Real.log T * x : ℝ) : ℂ)).re
        ≤ ‖Complex.I * ε * ((σ * Real.log T * x : ℝ) : ℂ)‖ := Complex.re_le_norm _
      _ = 1 / 2 * |σ * Real.log T * x| := by
          rw [norm_mul, norm_mul, Complex.norm_I, one_mul, hε, Complex.norm_real,
            Real.norm_eq_abs]
      _ ≤ Real.log T / 2 := by linarith
  have hzn : ‖ε / (T : ℂ)‖ = 1 / (2 * T) := by
    rw [norm_div, hε, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hT0]; ring
  have hsmall : ‖ε / (T : ℂ)‖ * w.kappa ≤ 1 := by
    rw [hzn, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    linarith [w.kappa_pos]
  have hk := norm_paperFT_k_le w hsmall
  rw [hzn] at hk
  have hI0 : 0 ≤ ∫ u, ‖w.k u‖ := integral_nonneg (fun _ => norm_nonneg _)
  have hCp0 : 0 ≤ w.kappa * ∫ u, ‖w.k u‖ := mul_nonneg w.kappa_pos.le hI0
  have hk' : ‖Zeta23.paperFT w.k (ε / T)‖ ≤ (w.kappa * ∫ u, ‖w.k u‖) / T := by
    refine hk.trans (le_of_eq ?_)
    field_simp
  have he : 0 < Real.exp (Real.log T / 2) := Real.exp_pos _
  have hE : Real.exp (Real.log T / 2) * Real.exp (Real.log T / 2) = T := by
    rw [← Real.exp_add, add_halves, Real.exp_log hT0]
  have hE2 : Real.log T / 2 ≤ Real.exp (Real.log T / 2) := by
    linarith [Real.add_one_le_exp (Real.log T / 2)]
  have h1 : Real.exp (Real.log T / 2) / T = 1 / Real.exp (Real.log T / 2) := by
    rw [div_eq_div_iff hT0.ne' he.ne']; linarith
  have h2 : 1 / Real.exp (Real.log T / 2) ≤ 2 / Real.log T := by
    rw [div_le_div_iff₀ he hL]; linarith
  calc ‖Complex.exp (Complex.I * ε * ((σ * Real.log T * x : ℝ) : ℂ))‖
        * ‖Zeta23.paperFT w.k (ε / T)‖
      ≤ Real.exp (Real.log T / 2) * ((w.kappa * ∫ u, ‖w.k u‖) / T) := by gcongr
    _ = (w.kappa * ∫ u, ‖w.k u‖) * (Real.exp (Real.log T / 2) / T) := by ring
    _ = (w.kappa * ∫ u, ‖w.k u‖) * (1 / Real.exp (Real.log T / 2)) := by rw [h1]
    _ ≤ (w.kappa * ∫ u, ‖w.k u‖) * (2 / Real.log T) := by gcongr
    _ = _ := by ring

/-! ## The kernel identity -/

/-- for `|x| ≤ 1` and `T` large the difference `Kfull - K0` is the sum of the two pole terms, the
`ω_T` part of the Gamma term and the Stirling remainder -/
theorem E_eq (hRH : RiemannHypothesis) (w : HeightWeight) {T σ : ℝ} (hT : 1 < T)
    (hTκ : w.kappa ≤ T * Real.log 2) (hσ : 0 < σ) {x : ℝ} (hx : |x| ≤ 1) :
    Kfull w.h T σ x - K0 w.k T σ x
      = Zeta23.paperFT (Fx w T σ x) (Complex.I / 2)
        + Zeta23.paperFT (Fx w T σ x) (-Complex.I / 2)
        + (T : ℂ) * komega w T (Asc T σ * x) + Rterm w T (Asc T σ * x) := by
  have hT0 : 0 < T := by linarith
  rw [Kfull_eq_literatureRHS hRH w hT0]
  unfold Zeta23.EF.literatureRHS
  rw [prime_tsum w hT hTκ hσ hx, gamma_split w hT0]
  unfold K0
  ring

theorem integral_inv_one_add_sq_scaled_le {A : ℝ} (hA : 0 < A) :
    ∫ x in (-1 : ℝ)..1, (1 + (A * x) ^ 2)⁻¹ ≤ π / A := by
  have h := intervalIntegral.integral_comp_mul_left (a := -1) (b := 1)
    (fun y : ℝ => (1 + y ^ 2)⁻¹) hA.ne'
  rw [h, integral_inv_one_add_sq, smul_eq_mul, div_eq_inv_mul]
  have hA' : 0 ≤ A⁻¹ := (inv_pos.mpr hA).le
  apply mul_le_mul_of_nonneg_left _ hA'
  linarith [Real.arctan_lt_pi_div_two (A * 1), Real.neg_pi_div_two_lt_arctan (A * -1)]

end Kernel

/-- **Kernel identity with error bounds.** For `|x| ≤ 1` and `T` large, `Kfull = K0 + E` with
`|E| ≤ C T`, `∫_{-1}^{1} |E| ≤ C / log T`, `∫_{-1}^{1} |E|² ≤ C T / log T`. -/
theorem kernel_error (hRH : RiemannHypothesis) (w : HeightWeight) {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ < 1) :
    ∃ C T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T →
      (∀ x : ℝ, |x| ≤ 1 → ‖Kfull w.h T σ x - K0 w.k T σ x‖ ≤ C * T) ∧
      (∫ x in (-1 : ℝ)..1, ‖Kfull w.h T σ x - K0 w.k T σ x‖) ≤ C / Real.log T ∧
      (∫ x in (-1 : ℝ)..1, ‖Kfull w.h T σ x - K0 w.k T σ x‖ ^ 2) ≤ C * T / Real.log T := by
  obtain ⟨Cg, hCg⟩ := w.gammaBound
  obtain ⟨CR, hCR0, hCR⟩ := Kernel.norm_Rterm_le w
  have hπ := Real.pi_pos
  have hCg0 : 0 ≤ Cg := by
    have h := hCg 2 le_rfl 0
    have h1 : Cg / (1 + (0 : ℝ) ^ 2) = Cg := by norm_num
    rw [h1] at h
    exact (norm_nonneg _).trans h
  have hCp0 : 0 ≤ w.kappa * ∫ u, ‖w.k u‖ :=
    mul_nonneg w.kappa_pos.le (integral_nonneg fun _ => norm_nonneg _)
  obtain ⟨c₀, hc₀⟩ : ∃ c₀ : ℝ, c₀ = 4 * (w.kappa * ∫ u, ‖w.k u‖) + CR := ⟨_, rfl⟩
  have hc₀0 : 0 ≤ c₀ := by rw [hc₀]; positivity
  have hC1 : 0 ≤ c₀ + Cg := by positivity
  have hC2 : 0 ≤ 2 * c₀ + Cg * π / σ := by positivity
  have hC3 : 0 ≤ 4 * c₀ ^ 2 + 2 * Cg ^ 2 * π / σ := by positivity
  refine ⟨(c₀ + Cg) + (2 * c₀ + Cg * π / σ) + (4 * c₀ ^ 2 + 2 * Cg ^ 2 * π / σ),
    max 3 (w.kappa / Real.log 2), fun T hT => ?_⟩
  have hT3 : 3 ≤ T := (le_max_left _ _).trans hT
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hTκ : w.kappa ≤ T * Real.log 2 := by
    have := (le_max_right _ _).trans hT
    rwa [div_le_iff₀ hlog2] at this
  have hT1 : 1 < T := by linarith
  have hT0 : 0 < T := by linarith
  have hlog2le : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num); linarith
  have hTκ' : w.kappa ≤ T := hTκ.trans (by nlinarith)
  have hL1 : 1 ≤ Real.log T := by
    have h3 : Real.exp 1 ≤ 3 := by linarith [Real.exp_one_lt_d9]
    calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ ≤ Real.log 3 := Real.log_le_log (Real.exp_pos 1) h3
      _ ≤ Real.log T := Real.log_le_log (by norm_num) hT3
  have hL0 : 0 < Real.log T := by linarith
  have hLT : Real.log T ≤ T := by linarith [Real.log_le_sub_one_of_pos hT0]
  have hA : 0 < Asc T σ := by unfold Asc; positivity
  have hu0 : ∀ x : ℝ, 0 ≤ (1 + (Asc T σ * x) ^ 2)⁻¹ := fun x => by positivity
  have hu1 : ∀ x : ℝ, (1 + (Asc T σ * x) ^ 2)⁻¹ ≤ 1 := fun x =>
    inv_le_one_of_one_le₀ (by nlinarith [sq_nonneg (Asc T σ * x)])
  have hu_cont : Continuous (fun x : ℝ => (1 + (Asc T σ * x) ^ 2)⁻¹) :=
    Continuous.inv₀ (by fun_prop) (fun x => by positivity)
  -- the pointwise bound
  have hPB : ∀ x : ℝ, |x| ≤ 1 → ‖Kfull w.h T σ x - K0 w.k T σ x‖
      ≤ c₀ / Real.log T + T * (Cg * (1 + (Asc T σ * x) ^ 2)⁻¹) := by
    intro x hx
    rw [Kernel.E_eq hRH w hT1 hTκ hσ hx]
    have hp1 := Kernel.norm_pole_le w hT1 hTκ' hσ.le hσ1.le hx (ε := Complex.I / 2) (by simp)
    have hp2 := Kernel.norm_pole_le w hT1 hTκ' hσ.le hσ1.le hx (ε := -Complex.I / 2) (by simp)
    have hk : ‖Kernel.komega w T (Asc T σ * x)‖ ≤ Cg / (1 + (Asc T σ * x) ^ 2) :=
      hCg T (by linarith) (Asc T σ * x)
    have hR := hCR T (by linarith) (Asc T σ * x)
    have hR' : CR / T ≤ CR / Real.log T := div_le_div_of_nonneg_left hCR0 hL0 hLT
    have hkT : ‖(T : ℂ) * Kernel.komega w T (Asc T σ * x)‖
        ≤ T * (Cg * (1 + (Asc T σ * x) ^ 2)⁻¹) := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hT0, ← div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_left hk hT0.le
    calc ‖Zeta23.paperFT (Kernel.Fx w T σ x) (Complex.I / 2)
          + Zeta23.paperFT (Kernel.Fx w T σ x) (-Complex.I / 2)
          + (T : ℂ) * Kernel.komega w T (Asc T σ * x) + Kernel.Rterm w T (Asc T σ * x)‖
        ≤ ‖Zeta23.paperFT (Kernel.Fx w T σ x) (Complex.I / 2)‖
          + ‖Zeta23.paperFT (Kernel.Fx w T σ x) (-Complex.I / 2)‖
          + ‖(T : ℂ) * Kernel.komega w T (Asc T σ * x)‖ + ‖Kernel.Rterm w T (Asc T σ * x)‖ :=
          norm_add₄_le
      _ ≤ 2 * (w.kappa * ∫ u, ‖w.k u‖) / Real.log T + 2 * (w.kappa * ∫ u, ‖w.k u‖) / Real.log T
          + T * (Cg * (1 + (Asc T σ * x) ^ 2)⁻¹) + CR / Real.log T := by
          linarith
      _ = c₀ / Real.log T + T * (Cg * (1 + (Asc T σ * x) ^ 2)⁻¹) := by rw [hc₀]; ring
  have hEcont : Continuous (fun x : ℝ => ‖Kfull w.h T σ x - K0 w.k T σ x‖) :=
    ((continuous_Kfull hRH w hT0 σ).sub (continuous_K0 w T σ)).norm
  have hIcc : ∀ x ∈ Set.Icc (-1 : ℝ) 1, |x| ≤ 1 := fun x hx => abs_le.mpr hx
  have hU := Kernel.integral_inv_one_add_sq_scaled_le hA
  refine ⟨fun x hx => ?_, ?_, ?_⟩
  · -- sup bound
    have h1 : c₀ / Real.log T ≤ c₀ * T :=
      (div_le_self hc₀0 hL1).trans (le_mul_of_one_le_right hc₀0 hT1.le)
    have h2 : T * (Cg * (1 + (Asc T σ * x) ^ 2)⁻¹) ≤ Cg * T := by
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_right (mul_le_of_le_one_right hCg0 (hu1 x)) hT0.le
    have h3 : (c₀ + Cg) * T
        ≤ ((c₀ + Cg) + (2 * c₀ + Cg * π / σ) + (4 * c₀ ^ 2 + 2 * Cg ^ 2 * π / σ)) * T :=
      mul_le_mul_of_nonneg_right (by linarith) hT0.le
    linarith [hPB x hx]
  · -- L¹ bound
    have hg_cont : Continuous (fun x : ℝ => c₀ / Real.log T + T * (Cg * (1 + (Asc T σ * x) ^ 2)⁻¹)) :=
      continuous_const.add (continuous_const.mul (continuous_const.mul hu_cont))
    have h1 : ∫ x in (-1 : ℝ)..1, ‖Kfull w.h T σ x - K0 w.k T σ x‖
        ≤ ∫ x in (-1 : ℝ)..1, (c₀ / Real.log T + T * (Cg * (1 + (Asc T σ * x) ^ 2)⁻¹)) :=
      intervalIntegral.integral_mono_on (by norm_num) (hEcont.intervalIntegrable _ _)
        (hg_cont.intervalIntegrable _ _) (fun x hx => hPB x (hIcc x hx))
    have h2 : ∫ x in (-1 : ℝ)..1, (c₀ / Real.log T + T * (Cg * (1 + (Asc T σ * x) ^ 2)⁻¹))
        = 2 * (c₀ / Real.log T) + T * (Cg * ∫ x in (-1 : ℝ)..1, (1 + (Asc T σ * x) ^ 2)⁻¹) := by
      have hi1 : IntervalIntegrable (fun _ : ℝ => c₀ / Real.log T) volume (-1) 1 :=
        continuous_const.intervalIntegrable _ _
      have hi2 : IntervalIntegrable (fun x : ℝ => T * (Cg * (1 + (Asc T σ * x) ^ 2)⁻¹))
          volume (-1) 1 :=
        (continuous_const.mul (continuous_const.mul hu_cont)).intervalIntegrable _ _
      rw [intervalIntegral.integral_add hi1 hi2,
        intervalIntegral.integral_const, intervalIntegral.integral_const_mul,
        intervalIntegral.integral_const_mul, smul_eq_mul]
      norm_num
    have h3 : T * (Cg * ∫ x in (-1 : ℝ)..1, (1 + (Asc T σ * x) ^ 2)⁻¹)
        ≤ T * (Cg * (π / Asc T σ)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hU hCg0) hT0.le
    have h4 : 2 * (c₀ / Real.log T) + T * (Cg * (π / Asc T σ))
        = (2 * c₀ + Cg * π / σ) / Real.log T := by
      unfold Asc; field_simp
    have h5 : (2 * c₀ + Cg * π / σ) / Real.log T
        ≤ ((c₀ + Cg) + (2 * c₀ + Cg * π / σ) + (4 * c₀ ^ 2 + 2 * Cg ^ 2 * π / σ)) / Real.log T :=
      div_le_div_of_nonneg_right (by linarith) hL0.le
    linarith
  · -- L² bound
    have hg_cont : Continuous (fun x : ℝ =>
        2 * (c₀ / Real.log T) ^ 2 + 2 * T ^ 2 * Cg ^ 2 * (1 + (Asc T σ * x) ^ 2)⁻¹) :=
      continuous_const.add (continuous_const.mul hu_cont)
    have hpt : ∀ x ∈ Set.Icc (-1 : ℝ) 1, ‖Kfull w.h T σ x - K0 w.k T σ x‖ ^ 2
        ≤ 2 * (c₀ / Real.log T) ^ 2 + 2 * T ^ 2 * Cg ^ 2 * (1 + (Asc T σ * x) ^ 2)⁻¹ := by
      intro x hx
      have hb := hPB x (hIcc x hx)
      have ha0 : 0 ≤ c₀ / Real.log T := div_nonneg hc₀0 hL0.le
      have hsq : ‖Kfull w.h T σ x - K0 w.k T σ x‖ ^ 2
          ≤ (c₀ / Real.log T + T * (Cg * (1 + (Asc T σ * x) ^ 2)⁻¹)) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hb 2
      have huu : ((1 + (Asc T σ * x) ^ 2)⁻¹) ^ 2 ≤ (1 + (Asc T σ * x) ^ 2)⁻¹ := by
        have := mul_le_mul_of_nonneg_left (hu1 x) (hu0 x)
        rw [mul_one] at this
        rw [sq]; exact this
      have hb2 : (T * (Cg * (1 + (Asc T σ * x) ^ 2)⁻¹)) ^ 2
          ≤ T ^ 2 * Cg ^ 2 * (1 + (Asc T σ * x) ^ 2)⁻¹ := by
        rw [mul_pow, mul_pow, ← mul_assoc]
        exact mul_le_mul_of_nonneg_left huu (by positivity)
      nlinarith [sq_nonneg (c₀ / Real.log T - T * (Cg * (1 + (Asc T σ * x) ^ 2)⁻¹))]
    have h1 : ∫ x in (-1 : ℝ)..1, ‖Kfull w.h T σ x - K0 w.k T σ x‖ ^ 2
        ≤ ∫ x in (-1 : ℝ)..1,
          (2 * (c₀ / Real.log T) ^ 2 + 2 * T ^ 2 * Cg ^ 2 * (1 + (Asc T σ * x) ^ 2)⁻¹) :=
      intervalIntegral.integral_mono_on (by norm_num) ((hEcont.pow 2).intervalIntegrable _ _)
        (hg_cont.intervalIntegrable _ _) hpt
    have h2 : ∫ x in (-1 : ℝ)..1,
          (2 * (c₀ / Real.log T) ^ 2 + 2 * T ^ 2 * Cg ^ 2 * (1 + (Asc T σ * x) ^ 2)⁻¹)
        = 4 * (c₀ / Real.log T) ^ 2
          + 2 * T ^ 2 * Cg ^ 2 * ∫ x in (-1 : ℝ)..1, (1 + (Asc T σ * x) ^ 2)⁻¹ := by
      have hi1 : IntervalIntegrable (fun _ : ℝ => 2 * (c₀ / Real.log T) ^ 2) volume (-1) 1 :=
        continuous_const.intervalIntegrable _ _
      have hi2 : IntervalIntegrable
          (fun x : ℝ => 2 * T ^ 2 * Cg ^ 2 * (1 + (Asc T σ * x) ^ 2)⁻¹) volume (-1) 1 :=
        (continuous_const.mul hu_cont).intervalIntegrable _ _
      rw [intervalIntegral.integral_add hi1 hi2,
        intervalIntegral.integral_const, intervalIntegral.integral_const_mul, smul_eq_mul]
      norm_num
      ring
    have h3 : 2 * T ^ 2 * Cg ^ 2 * ∫ x in (-1 : ℝ)..1, (1 + (Asc T σ * x) ^ 2)⁻¹
        ≤ 2 * T ^ 2 * Cg ^ 2 * (π / Asc T σ) :=
      mul_le_mul_of_nonneg_left hU (by positivity)
    have h4 : 2 * T ^ 2 * Cg ^ 2 * (π / Asc T σ) = (2 * Cg ^ 2 * π / σ) * T / Real.log T := by
      unfold Asc; field_simp
    have h5 : 4 * (c₀ / Real.log T) ^ 2 ≤ (4 * c₀ ^ 2) * T / Real.log T := by
      have h6 : (c₀ / Real.log T) ^ 2 ≤ c₀ ^ 2 :=
        pow_le_pow_left₀ (div_nonneg hc₀0 hL0.le) (div_le_self hc₀0 hL1) 2
      have h7 : c₀ ^ 2 ≤ c₀ ^ 2 * T / Real.log T := by
        rw [le_div_iff₀ hL0]
        exact mul_le_mul_of_nonneg_left hLT (sq_nonneg _)
      calc 4 * (c₀ / Real.log T) ^ 2 ≤ 4 * (c₀ ^ 2 * T / Real.log T) := by linarith
        _ = (4 * c₀ ^ 2) * T / Real.log T := by ring
    have h8 : (4 * c₀ ^ 2) * T / Real.log T + (2 * Cg ^ 2 * π / σ) * T / Real.log T
        ≤ ((c₀ + Cg) + (2 * c₀ + Cg * π / σ) + (4 * c₀ ^ 2 + 2 * Cg ^ 2 * π / σ)) * T
          / Real.log T := by
      rw [← add_div, ← add_mul]
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith) hT0.le) hL0.le
    linarith

end TMA

end
end Src_TMA_Kernel

section Src_TMA_Packets
/-
Written for Kristian Muri Knausgård, drafted with Claude (Anthropic), 22 November 2026.

TMA/Packets.lean — elementary facts about the packets: support, separation of the centres for large T.
STATUS: complete, every statement proved.  See BLUEPRINT.md, module "Packets".
-/

open MeasureTheory Complex
open scoped BigOperators ArithmeticFunction Real

noncomputable section
namespace TMA

theorem HeightWeight.continuous_k (w : HeightWeight) : Continuous w.k := w.k_contDiff.continuous

/-- the transform `k` of a height weight has compact support (helper) -/
theorem Packets.hasCompactSupport_k (w : HeightWeight) : HasCompactSupport w.k := by
  refine HasCompactSupport.intro (isCompact_Icc (a := -w.kappa) (b := w.kappa)) ?_
  intro x hx
  by_contra h
  exact hx (abs_le.mp (w.k_supp x h))

theorem HeightWeight.integrable_k (w : HeightWeight) : Integrable w.k :=
  w.continuous_k.integrable_of_hasCompactSupport (Packets.hasCompactSupport_k w)

theorem HeightWeight.exists_k_bound (w : HeightWeight) : ∃ M : ℝ, 0 ≤ M ∧ ∀ y, ‖w.k y‖ ≤ M := by
  obtain ⟨C, hC⟩ := w.continuous_k.bounded_above_of_compact_support (Packets.hasCompactSupport_k w)
  exact ⟨C, (norm_nonneg _).trans (hC 0), hC⟩

/-- a packet vanishes at distance more than `κ/A` from its centre -/
theorem packet_eq_zero (w : HeightWeight) {T σ lam x : ℝ} (hA : 0 < Asc T σ)
    (h : w.kappa / Asc T σ < |x - lam|) : packet w.k T σ lam x = 0 := by
  unfold packet
  have hk : w.k (-(Asc T σ * (x - lam))) = 0 := by
    by_contra hne
    have h1 := w.k_supp _ hne
    rw [abs_neg, abs_mul, abs_of_pos hA] at h1
    rw [div_lt_iff₀ hA] at h
    linarith [mul_comm (Asc T σ) |x - lam|]
  rw [hk, mul_zero]

/-- logarithms of distinct positive integers `n < n'` differ by at least `1/n'` (helper) -/
theorem Packets.one_div_le_log_sub_log {n n' : ℕ} (hn : 1 ≤ n) (hnn' : n < n') :
    1 / (n' : ℝ) ≤ Real.log n' - Real.log n := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hn'pos : (0 : ℝ) < n' := by exact_mod_cast (show 0 < n' by omega)
  have h1 : 1 - ((n' : ℝ) / n)⁻¹ ≤ Real.log ((n' : ℝ) / n) :=
    Real.one_sub_inv_le_log_of_pos (div_pos hn'pos hnpos)
  rw [Real.log_div hn'pos.ne' hnpos.ne'] at h1
  have h2 : (1 : ℝ) / n' ≤ 1 - ((n' : ℝ) / n)⁻¹ := by
    rw [inv_div]
    have h3 : (n : ℝ) + 1 ≤ n' := by exact_mod_cast hnn'
    have h4 : 1 - (n : ℝ) / n' = ((n' : ℝ) - n) / n' := by
      field_simp
    rw [h4]
    exact div_le_div_of_nonneg_right (by linarith) hn'pos.le
  linarith

/-- **Separation.** For `T` large (depending on `σ < 1` and `κ`):
* `T ≥ 2`, `A > 0`, `3κ/T < log 2`;
* the packets of an integer `n > Nmax` vanish on `[-1,1]`;
* distinct positive integers `≤ 4 T^σ` have logarithms that differ by more than `3κ/T`. -/
theorem separation (w : HeightWeight) {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ < 1) :
    ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T →
      2 ≤ T ∧ 0 < Asc T σ ∧ 3 * w.kappa / T < Real.log 2 ∧
      (∀ n : ℕ, Nmax T σ < n → ∀ x : ℝ, |x| ≤ 1 →
        packet w.k T σ (lamOf T σ n) x = 0 ∧ packet w.k T σ (-(lamOf T σ n)) x = 0) ∧
      (∀ n n' : ℕ, 1 ≤ n → 1 ≤ n' → (n : ℝ) ≤ 4 * T ^ σ → (n' : ℝ) ≤ 4 * T ^ σ → n ≠ n' →
        3 * w.kappa / T < |Real.log n - Real.log n'|) := by
  have hκ := w.kappa_pos
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hev : ∀ᶠ T : ℝ in Filter.atTop, 12 * w.kappa < T ^ (1 - σ) :=
    (tendsto_rpow_atTop (by linarith : 0 < 1 - σ)).eventually_gt_atTop _
  obtain ⟨T₁, hT₁⟩ := Filter.eventually_atTop.mp hev
  refine ⟨max (max 2 T₁) (3 * w.kappa / Real.log 2 + 1), fun T hT => ?_⟩
  have hT2 : 2 ≤ T := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hT
  have hTT1 : T₁ ≤ T := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hT
  have hT3 : 3 * w.kappa / Real.log 2 + 1 ≤ T := le_trans (le_max_right _ _) hT
  have hTpos : 0 < T := by linarith
  have hL : 0 < Real.log T := Real.log_pos (by linarith)
  have hσL : 0 < σ * Real.log T := mul_pos hσ hL
  have hA : 0 < Asc T σ := mul_pos hTpos hσL
  have hTσ : 0 < T ^ σ := Real.rpow_pos_of_pos hTpos σ
  have h3T : 3 * w.kappa < Real.log 2 * T := by
    have h : 3 * w.kappa / Real.log 2 < T := by linarith
    rw [div_lt_iff₀ hlog2] at h
    linarith [mul_comm T (Real.log 2)]
  have h3 : 3 * w.kappa / T < Real.log 2 := by
    rw [div_lt_iff₀ hTpos]
    exact h3T
  refine ⟨hT2, hA, h3, ?_, ?_⟩
  · intro n hn x hx
    have hn' : 2 * T ^ σ < (n : ℝ) := Nat.lt_of_floor_lt hn
    have hlogn : Real.log 2 + σ * Real.log T < Real.log n := by
      have h := Real.log_lt_log (by positivity) hn'
      rwa [Real.log_mul (by norm_num) hTσ.ne', Real.log_rpow hTpos] at h
    have hlam : 1 + Real.log 2 / (σ * Real.log T) < lamOf T σ n := by
      unfold lamOf
      rw [lt_div_iff₀ hσL]
      have h : (1 + Real.log 2 / (σ * Real.log T)) * (σ * Real.log T)
          = σ * Real.log T + Real.log 2 := by
        field_simp
      linarith
    have hκA : w.kappa / Asc T σ ≤ Real.log 2 / (σ * Real.log T) := by
      unfold Asc
      rw [div_le_div_iff₀ (mul_pos hTpos hσL) hσL]
      have h : w.kappa ≤ Real.log 2 * T := by linarith
      calc w.kappa * (σ * Real.log T) ≤ (Real.log 2 * T) * (σ * Real.log T) :=
            mul_le_mul_of_nonneg_right h hσL.le
        _ = Real.log 2 * (T * (σ * Real.log T)) := by ring
    have hx' := abs_le.mp hx
    constructor
    · apply packet_eq_zero w hA
      calc w.kappa / Asc T σ ≤ Real.log 2 / (σ * Real.log T) := hκA
        _ < lamOf T σ n - x := by linarith [hx'.2]
        _ ≤ |x - lamOf T σ n| := by rw [abs_sub_comm]; exact le_abs_self _
    · apply packet_eq_zero w hA
      calc w.kappa / Asc T σ ≤ Real.log 2 / (σ * Real.log T) := hκA
        _ < x + lamOf T σ n := by linarith [hx'.1]
        _ ≤ |x - -lamOf T σ n| := by rw [sub_neg_eq_add]; exact le_abs_self _
  · have key : ∀ n n' : ℕ, 1 ≤ n → n < n' → (n' : ℝ) ≤ 4 * T ^ σ →
        3 * w.kappa / T < Real.log n' - Real.log n := by
      intro n n' hn hnn' hn'
      have hn'pos : (0 : ℝ) < n' := by exact_mod_cast (show 0 < n' by omega)
      have h1 := Packets.one_div_le_log_sub_log hn hnn'
      have h2 : 3 * w.kappa / T < 1 / (n' : ℝ) := by
        rw [div_lt_div_iff₀ hTpos hn'pos]
        have hTsplit : T = T ^ σ * T ^ (1 - σ) := by
          rw [← Real.rpow_add hTpos]
          simp
        have h12 := hT₁ T hTT1
        calc 3 * w.kappa * (n' : ℝ) ≤ 3 * w.kappa * (4 * T ^ σ) :=
              mul_le_mul_of_nonneg_left hn' (by positivity)
          _ = T ^ σ * (12 * w.kappa) := by ring
          _ < T ^ σ * T ^ (1 - σ) := mul_lt_mul_of_pos_left h12 hTσ
          _ = 1 * T := by rw [← hTsplit, one_mul]
      linarith
    intro n n' hn hn' hnb hn'b hne
    rcases lt_or_gt_of_ne hne with h | h
    · have h1 := key n n' hn h hn'b
      rw [abs_sub_comm]
      exact lt_of_lt_of_le h1 (le_abs_self _)
    · have h1 := key n' n hn' h hnb
      exact lt_of_lt_of_le h1 (le_abs_self _)

end TMA

end
end Src_TMA_Packets

section Src_TMA_WeightAux1
/-
Written for Kristian Muri Knausgård, drafted with Claude (Anthropic), 22 November 2026.

TMA/WeightAux1.lean — auxiliary file for TMA/Weight.lean.
The paper transform `Zeta23.paperFT f z = ∫ f(u) e^{izu} du` on Schwartz functions:
* `PF f` : the function `x ↦ paperFT f x` (real `x`) as a Schwartz map;
* `conv f g` : convolution of Schwartz maps, `paperFT (conv f g) = paperFT f * paperFT g`;
* scaling, inversion, Plancherel and the triple-product identity.
-/

open MeasureTheory Complex
open scoped Real FourierTransform SchwartzMap Convolution

noncomputable section
namespace TMA
namespace WeightAux

open Zeta23

/-! ### Scaling -/

/-- the map `x ↦ x * c` as a continuous linear equivalence of `ℝ` -/
def scaleCLE (c : ℝ) (hc : c ≠ 0) : ℝ ≃L[ℝ] ℝ :=
  ContinuousLinearEquiv.unitsEquivAut ℝ (Units.mk0 c hc)

@[simp] lemma scaleCLE_apply (c : ℝ) (hc : c ≠ 0) (x : ℝ) : scaleCLE c hc x = x * c := rfl

/-- `x ↦ f (x * c)` as a Schwartz map -/
def sScale (c : ℝ) (hc : c ≠ 0) (f : 𝓢(ℝ, ℂ)) : 𝓢(ℝ, ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (scaleCLE c hc) f

@[simp] lemma sScale_apply (c : ℝ) (hc : c ≠ 0) (f : 𝓢(ℝ, ℂ)) (x : ℝ) :
    sScale c hc f x = f (x * c) := rfl

lemma two_pi_inv_ne : (-(2 * π)⁻¹ : ℝ) ≠ 0 := by
  have : (0 : ℝ) < (2 * π)⁻¹ := by positivity
  linarith

/-- The paper transform of a Schwartz function, restricted to the real line, as a Schwartz map. -/
def PF (f : 𝓢(ℝ, ℂ)) : 𝓢(ℝ, ℂ) := sScale (-(2 * π)⁻¹) two_pi_inv_ne (𝓕 f)

lemma PF_apply (f : 𝓢(ℝ, ℂ)) (x : ℝ) : PF f x = paperFT f x := by
  have hx : x * (-(2 * π)⁻¹) = -x / (2 * π) := by
    rw [div_eq_mul_inv]; ring
  rw [paperFT_ofReal_eq_fourier, ← hx]
  change (𝓕 f) (x * (-(2 * π)⁻¹)) = _
  rw [SchwartzMap.fourier_coe]

lemma PF_apply' (f : 𝓢(ℝ, ℂ)) (x : ℝ) : PF f x = 𝓕 (f : ℝ → ℂ) (x * (-(2 * π)⁻¹)) := by
  change (𝓕 f) (x * (-(2 * π)⁻¹)) = _
  rw [SchwartzMap.fourier_coe]

lemma paperFT_eq_fourier_mul (f : ℝ → ℂ) (x : ℝ) :
    paperFT f x = 𝓕 f (x * (-(2 * π)⁻¹)) := by
  have hx : x * (-(2 * π)⁻¹) = -x / (2 * π) := by
    rw [div_eq_mul_inv]; ring
  rw [paperFT_ofReal_eq_fourier, ← hx]

lemma paperFT_zero (f : ℝ → ℂ) : paperFT f ((0 : ℝ) : ℂ) = ∫ u, f u := by
  rw [paperFT_def]
  congr 1
  funext u
  simp

/-- change of variables `v = s * (-(2π)⁻¹)` -/
lemma integral_scale (G : ℝ → ℂ) :
    ∫ v, G v = (1 / (2 * π) : ℂ) * ∫ s : ℝ, G (s * (-(2 * π)⁻¹)) := by
  have h := MeasureTheory.Measure.integral_comp_mul_right G (-(2 * π)⁻¹)
  rw [h]
  have hpi : (0 : ℝ) < 2 * π := by positivity
  have h2 : |(-(2 * π)⁻¹ : ℝ)⁻¹| = 2 * π := by
    rw [inv_neg, inv_inv, abs_neg, abs_of_pos hpi]
  rw [h2, Complex.real_smul]
  push_cast
  have : (2 * (π : ℂ)) ≠ 0 := by
    exact_mod_cast hpi.ne'
  field_simp

lemma integral_scale_real (G : ℝ → ℝ) :
    ∫ v, G v = (1 / (2 * π)) * ∫ s : ℝ, G (s * (-(2 * π)⁻¹)) := by
  have h := MeasureTheory.Measure.integral_comp_mul_right G (-(2 * π)⁻¹)
  rw [h]
  have hpi : (0 : ℝ) < 2 * π := by positivity
  have h2 : |(-(2 * π)⁻¹ : ℝ)⁻¹| = 2 * π := by
    rw [inv_neg, inv_inv, abs_neg, abs_of_pos hpi]
  rw [h2, smul_eq_mul]
  field_simp

/-! ### Convolution -/

/-- convolution of Schwartz functions on `ℝ` -/
def conv (f g : 𝓢(ℝ, ℂ)) : 𝓢(ℝ, ℂ) :=
  SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ) f g

lemma conv_apply (f g : 𝓢(ℝ, ℂ)) (x : ℝ) : conv f g x = ∫ t, f t * g (x - t) := by
  unfold conv
  rw [SchwartzMap.convolution_apply, convolution_def]
  rfl

lemma fourier_conv (f g : 𝓢(ℝ, ℂ)) (ξ : ℝ) :
    𝓕 (conv f g : ℝ → ℂ) ξ = 𝓕 (f : ℝ → ℂ) ξ * 𝓕 (g : ℝ → ℂ) ξ := by
  have h := SchwartzMap.fourier_convolution (ContinuousLinearMap.mul ℂ ℂ) f g
  have h2 := congrArg (fun F : 𝓢(ℝ, ℂ) => F ξ) h
  simp only [SchwartzMap.pairing_apply_apply, ContinuousLinearMap.mul_apply'] at h2
  rw [← SchwartzMap.fourier_coe, ← SchwartzMap.fourier_coe, ← SchwartzMap.fourier_coe]
  exact h2

lemma paperFT_conv (f g : 𝓢(ℝ, ℂ)) (x : ℝ) :
    paperFT (conv f g) x = paperFT f x * paperFT g x := by
  rw [paperFT_eq_fourier_mul, paperFT_eq_fourier_mul, paperFT_eq_fourier_mul, fourier_conv]

/-- support of a convolution -/
lemma conv_supp {f g : 𝓢(ℝ, ℂ)} {a b : ℝ} (hf : ∀ u, f u ≠ 0 → |u| ≤ a)
    (hg : ∀ u, g u ≠ 0 → |u| ≤ b) : ∀ u, conv f g u ≠ 0 → |u| ≤ a + b := by
  intro u hu
  by_contra hcon
  apply hu
  rw [conv_apply]
  have : ∀ t : ℝ, f t * g (u - t) = 0 := by
    intro t
    by_contra h
    have h1 : f t ≠ 0 := fun h0 => h (by rw [h0, zero_mul])
    have h2 : g (u - t) ≠ 0 := fun h0 => h (by rw [h0, mul_zero])
    have h3 := hf t h1
    have h4 := hg (u - t) h2
    apply hcon
    calc |u| = |t + (u - t)| := by ring_nf
      _ ≤ |t| + |u - t| := abs_add_le _ _
      _ ≤ a + b := add_le_add h3 h4
  simp only [this, integral_zero]

/-! ### Inversion, Plancherel, triple product -/

/-- Fourier inversion in the paper normalisation. -/
lemma paperFT_inv (f : 𝓢(ℝ, ℂ)) (y : ℝ) :
    (1 / (2 * π) : ℂ) * ∫ s : ℝ, paperFT f s * Complex.exp (Complex.I * s * y) = f (-y) := by
  have h1 : 𝓕⁻ (𝓕 f) = f := FourierTransform.fourierInv_fourier_eq f
  have h2 : f (-y) = 𝓕⁻ ((𝓕 f : 𝓢(ℝ, ℂ)) : ℝ → ℂ) (-y) := by
    rw [← SchwartzMap.fourierInv_coe, h1]
  rw [h2, Real.fourierInv_eq']
  symm
  refine (integral_scale _).trans ?_
  congr 1
  apply integral_congr_ae
  filter_upwards with s
  have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  rw [smul_eq_mul, paperFT_eq_fourier_mul, SchwartzMap.fourier_coe, mul_comm, Real.inner_apply]
  congr 2
  push_cast
  field_simp

/-- Plancherel in the paper normalisation. -/
lemma paperFT_plancherel (f : 𝓢(ℝ, ℂ)) :
    ∫ y, ‖f y‖ ^ 2 = (1 / (2 * π)) * ∫ x : ℝ, ‖paperFT f x‖ ^ 2 := by
  rw [← SchwartzMap.integral_norm_sq_fourier f, integral_scale_real]
  congr 1
  apply integral_congr_ae
  filter_upwards with s
  rw [← PF_apply, PF_apply', SchwartzMap.fourier_coe]

/-- value at `0` of the inverse transform -/
lemma eval_zero_eq_integral_fourier (g : 𝓢(ℝ, ℂ)) : g 0 = ∫ v, 𝓕 (g : ℝ → ℂ) v := by
  have h1 : 𝓕⁻ (𝓕 g) = g := FourierTransform.fourierInv_fourier_eq g
  have h2 : g 0 = 𝓕⁻ ((𝓕 g : 𝓢(ℝ, ℂ)) : ℝ → ℂ) 0 := by
    rw [← SchwartzMap.fourierInv_coe, h1]
  rw [h2, Real.fourierInv_eq']
  apply integral_congr_ae
  filter_upwards with v
  simp [SchwartzMap.fourier_coe]

/-- `∬ f(y₁) f(y₂) f(-y₁-y₂) = (1/2π) ∫ (paperFT f)³`. -/
lemma paperFT_triple (f : 𝓢(ℝ, ℂ)) :
    ∫ y₁, ∫ y₂, f y₁ * f y₂ * f (-y₁ - y₂) = (1 / (2 * π) : ℂ) * ∫ x : ℝ, paperFT f x ^ 3 := by
  have hin : ∀ y₁ : ℝ, ∫ y₂, f y₁ * f y₂ * f (-y₁ - y₂) = f y₁ * conv f f (0 - y₁) := by
    intro y₁
    rw [conv_apply, ← integral_const_mul_C]
    congr 1
    funext y₂
    rw [zero_sub, mul_assoc]
  simp only [hin]
  rw [← conv_apply f (conv f f) 0, eval_zero_eq_integral_fourier, integral_scale]
  congr 1
  apply integral_congr_ae
  filter_upwards with s
  rw [fourier_conv, fourier_conv, paperFT_eq_fourier_mul]
  ring

end WeightAux
end TMA
end
end Src_TMA_WeightAux1

section Src_TMA_WeightAuxGamma
/-
Written for Kristian Muri Knausgård, drafted with Claude (Anthropic), 22 November 2026.

TMA/WeightAuxGamma.lean — auxiliary file for TMA/Weight.lean.
For a Schwartz function `H` on ℝ with `H 0 = 0` and `H' 0 = 0`:
* `quadratic_bound`: `‖H x‖ ≤ B x²` and `‖H' x‖ ≤ B |x|`;
* `gamma_bound`: the transform of `H · ω_T` is `O(1/(1+y²))`, uniformly in `T ≥ 2`
  (`ω_T(s) = ½ log (s² + T⁻²)`).

Proof of `gamma_bound`: with `c = T⁻² ∈ (0, 1/4]` and `F = H · ω`, the functions `F, F', F''`
are dominated, away from `s = 0`, by a fixed integrable function (`gamDom`, a multiple of
`1_{[-1,1]} (1 + |log s|) + 1/(1+s²)`), uniformly in `c`; two integrations by parts
(`fourierIntegral_self_add_deriv_deriv`) then give `(1 + u²) ‖𝓕 F u‖ ≤ 2 ∫ gamDom`.
All helper declarations are `private`; the interface consists of the two theorems.
-/

open MeasureTheory Complex
open scoped Real FourierTransform SchwartzMap

noncomputable section
namespace TMA
namespace WeightAux

/-! ## Schwartz bounds and the quadratic bound -/

/-- Uniform decay of a Schwartz function. -/
private lemma schwartz_decay3 (G : 𝓢(ℝ, ℂ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, ‖G x‖ * (1 + |x|) ^ 3 ≤ C := by
  refine ⟨2 ^ 3 * (Finset.Iic ((3, 0) : ℕ × ℕ)).sup
    (fun m => SchwartzMap.seminorm ℝ m.1 m.2) G, by positivity, fun x => ?_⟩
  have h := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := ((3, 0) : ℕ × ℕ))
    (k := 3) (n := 0) le_rfl le_rfl G x
  rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at h
  rw [mul_comm]
  exact h

/-- A Schwartz function vanishing to second order at `0` is `O(x²)`, its derivative is `O(|x|)`. -/
theorem quadratic_bound (H : 𝓢(ℝ, ℂ)) (hH0 : H 0 = 0) (hH1 : deriv (⇑H) 0 = 0) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x : ℝ, ‖H x‖ ≤ B * x ^ 2 ∧ ‖deriv (⇑H) x‖ ≤ B * |x| := by
  set H1 : 𝓢(ℝ, ℂ) := SchwartzMap.derivCLM ℝ ℂ H with hH1def
  set H2 : 𝓢(ℝ, ℂ) := SchwartzMap.derivCLM ℝ ℂ H1 with hH2def
  have e1 : ∀ x, H1 x = deriv (⇑H) x := fun x => rfl
  have e2 : ∀ x, H2 x = deriv (⇑H1) x := fun x => rfl
  obtain ⟨C2, hC2, hC2b⟩ := schwartz_decay3 H2
  have hH2le : ∀ x, ‖deriv (⇑H1) x‖ ≤ C2 := by
    intro x
    rw [← e2]
    have h1 : (1 : ℝ) ≤ (1 + |x|) ^ 3 := one_le_pow₀ (by linarith [abs_nonneg x])
    calc ‖H2 x‖ = ‖H2 x‖ * 1 := (mul_one _).symm
      _ ≤ ‖H2 x‖ * (1 + |x|) ^ 3 := mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
      _ ≤ C2 := hC2b x
  have hd1 : ∀ x : ℝ, ‖deriv (⇑H) x‖ ≤ C2 * |x| := by
    intro x
    have h := Convex.norm_image_sub_le_of_norm_deriv_le (f := ⇑H1) (s := Set.univ) (C := C2)
      (fun t _ => H1.differentiableAt) (fun t _ => hH2le t) convex_univ
      (Set.mem_univ (0 : ℝ)) (Set.mem_univ x)
    rw [e1 0, hH1, sub_zero, sub_zero, Real.norm_eq_abs] at h
    exact h
  refine ⟨C2, hC2, fun x => ⟨?_, hd1 x⟩⟩
  have hconv : Convex ℝ (Set.Icc (-|x|) |x|) := convex_Icc _ _
  have h := Convex.norm_image_sub_le_of_norm_deriv_le (f := ⇑H) (s := Set.Icc (-|x|) |x|)
    (C := C2 * |x|) (fun t _ => H.differentiableAt)
    (fun t ht => (hd1 t).trans
      (mul_le_mul_of_nonneg_left (abs_le.mpr ⟨ht.1, ht.2⟩) hC2)) hconv
    (x := 0) (y := x) ⟨by linarith [abs_nonneg x], abs_nonneg x⟩
    ⟨neg_abs_le x, le_abs_self x⟩
  rw [hH0, sub_zero, sub_zero, Real.norm_eq_abs] at h
  calc ‖H x‖ ≤ C2 * |x| * |x| := h
    _ = C2 * x ^ 2 := by rw [mul_assoc, ← pow_two, sq_abs]

/-! ## The weight `ω(s) = ½ log (s² + c)` and its derivatives -/

/-- `ω(s) = ½ log (s² + c)` (so `omegaT T = gamOm (1 / T ^ 2)`). -/
private def gamOm (c s : ℝ) : ℝ := (1 / 2) * Real.log (s ^ 2 + c)

/-- first derivative of `gamOm c` -/
private def gamOm1 (c s : ℝ) : ℝ := s / (s ^ 2 + c)

/-- second derivative of `gamOm c` -/
private def gamOm2 (c s : ℝ) : ℝ := (c - s ^ 2) / (s ^ 2 + c) ^ 2

private lemma hasDerivAt_sq_add (c s : ℝ) : HasDerivAt (fun t : ℝ => t ^ 2 + c) (2 * s) s := by
  have h := ((hasDerivAt_id s).pow 2).add_const c
  simpa using h

private lemma hasDerivAt_gamOm {c : ℝ} (hc : 0 < c) (s : ℝ) :
    HasDerivAt (gamOm c) (gamOm1 c s) s := by
  have hpos : 0 < s ^ 2 + c := by positivity
  have h2 := ((hasDerivAt_sq_add c s).log hpos.ne').const_mul (1 / 2 : ℝ)
  have e : gamOm1 c s = 1 / 2 * (2 * s / (s ^ 2 + c)) := by
    unfold gamOm1; field_simp
  rw [e]
  exact h2

private lemma hasDerivAt_gamOm1 {c : ℝ} (hc : 0 < c) (s : ℝ) :
    HasDerivAt (gamOm1 c) (gamOm2 c s) s := by
  have hpos : 0 < s ^ 2 + c := by positivity
  have h2 := (hasDerivAt_id s).div (hasDerivAt_sq_add c s) hpos.ne'
  have e : gamOm2 c s = (1 * (s ^ 2 + c) - id s * (2 * s)) / (s ^ 2 + c) ^ 2 := by
    unfold gamOm2; simp only [id]; congr 1; ring
  rw [e]
  exact h2

private lemma abs_gamOm1_mul_le {c : ℝ} (hc : 0 < c) (s : ℝ) : |gamOm1 c s| * |s| ≤ 1 := by
  have hpos : 0 < s ^ 2 + c := by positivity
  unfold gamOm1
  rw [abs_div, abs_of_pos hpos, div_mul_eq_mul_div, div_le_one hpos, abs_mul_abs_self]
  nlinarith [sq_nonneg s]

private lemma abs_gamOm2_mul_le {c : ℝ} (hc : 0 < c) (s : ℝ) : |gamOm2 c s| * s ^ 2 ≤ 1 := by
  have hpos : 0 < s ^ 2 + c := by positivity
  have habs : |c - s ^ 2| ≤ s ^ 2 + c := by
    rw [abs_le]; constructor <;> nlinarith [sq_nonneg s]
  unfold gamOm2
  rw [abs_div, abs_of_pos (pow_pos hpos 2), div_mul_eq_mul_div, div_le_one (pow_pos hpos 2)]
  calc |c - s ^ 2| * s ^ 2 ≤ (s ^ 2 + c) * (s ^ 2 + c) :=
        mul_le_mul habs (by linarith) (sq_nonneg s) hpos.le
    _ = (s ^ 2 + c) ^ 2 := by ring

private lemma abs_gamOm_le {c : ℝ} (hc : 0 < c) (hc4 : c ≤ 1 / 4) {s : ℝ} (hs : s ≠ 0) :
    |gamOm c s| ≤ 1 + |Real.log s| := by
  have hs2 : 0 < s ^ 2 := by positivity
  have hpos : 0 < s ^ 2 + c := by positivity
  have ht : 0 ≤ |Real.log s| := abs_nonneg _
  have hlog2 : Real.log (s ^ 2) = 2 * Real.log s := by
    rw [Real.log_pow]; norm_num
  -- lower bound
  have hlow : 2 * Real.log s ≤ Real.log (s ^ 2 + c) := by
    rw [← hlog2]; exact Real.log_le_log hs2 (by linarith)
  -- upper bound
  have hs2le : s ^ 2 ≤ Real.exp (2 * |Real.log s|) := by
    calc s ^ 2 = Real.exp (Real.log (s ^ 2)) := (Real.exp_log hs2).symm
      _ ≤ Real.exp (2 * |Real.log s|) := by
        rw [hlog2]; exact Real.exp_le_exp.mpr (by linarith [le_abs_self (Real.log s)])
  have hexp1 : (2 : ℝ) ≤ Real.exp 1 := by
    have := Real.add_one_le_exp (1 : ℝ); linarith
  have hexp2 : (1 : ℝ) ≤ Real.exp (2 * |Real.log s|) := Real.one_le_exp (by linarith)
  have hup : Real.log (s ^ 2 + c) ≤ 2 * |Real.log s| + 1 := by
    have h1 : s ^ 2 + c ≤ Real.exp (2 * |Real.log s| + 1) := by
      rw [Real.exp_add]
      nlinarith [Real.exp_pos (2 * |Real.log s|)]
    calc Real.log (s ^ 2 + c) ≤ Real.log (Real.exp (2 * |Real.log s| + 1)) :=
          Real.log_le_log hpos h1
      _ = 2 * |Real.log s| + 1 := Real.log_exp _
  unfold gamOm
  rw [abs_le]
  constructor
  · linarith [neg_abs_le (Real.log s)]
  · linarith

/-- the dominating function (independent of `T`) -/
private def gamDom (s : ℝ) : ℝ :=
  Set.indicator (Set.Icc (-1) 1) (fun s => 1 + |Real.log s|) s + 1 / (1 + s ^ 2)

private lemma integrable_gamDom : Integrable gamDom := by
  have h1 : IntegrableOn (fun s : ℝ => 1 + |Real.log s|) (Set.Icc (-1) 1) := by
    have hlog : IntervalIntegrable Real.log volume (-1) 1 :=
      intervalIntegral.intervalIntegrable_log'
    have h2 : IntervalIntegrable (fun s : ℝ => 1 + |Real.log s|) volume (-1) 1 :=
      intervalIntegrable_const.add hlog.abs
    exact (intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num)).mp h2
  have h3 : Integrable (Set.indicator (Set.Icc (-1) 1) (fun s : ℝ => 1 + |Real.log s|)) :=
    (integrable_indicator_iff measurableSet_Icc).mpr h1
  have h4 : Integrable (fun s : ℝ => 1 / (1 + s ^ 2)) := by
    simpa only [one_div] using integrable_inv_one_add_sq
  exact h3.add h4

private lemma contDiff_gamOm {c : ℝ} (hc : 0 < c) : ContDiff ℝ 2 (gamOm c) := by
  unfold gamOm
  exact contDiff_const.mul (((contDiff_id.pow 2).add contDiff_const).log
    (fun s => (by positivity : (0 : ℝ) < s ^ 2 + c).ne'))

/-! ## Pointwise domination -/

/-- real inequalities near zero (`a = |s| ≤ 1`, `L = |log s|`) -/
private lemma key_near {B CH a L w w1 w2 h0 h1 h2 : ℝ} (hB : 0 ≤ B) (hCH : 0 ≤ CH)
    (ha : 0 ≤ a) (ha1 : a ≤ 1) (hL : 0 ≤ L) (haL : a * L ≤ 1)
    (nw : 0 ≤ w) (nw1 : 0 ≤ w1) (nw2 : 0 ≤ w2)
    (hw : w ≤ 1 + L) (hw1 : w1 * a ≤ 1) (hw2 : w2 * a ^ 2 ≤ 1)
    (q0 : h0 ≤ B * a ^ 2) (q1 : h1 ≤ B * a) (h2le : h2 ≤ CH) :
    h0 * w ≤ 2 * B ∧ h1 * w ≤ 2 * B ∧ h0 * w1 ≤ B ∧ h1 * w1 ≤ B ∧ h0 * w2 ≤ B ∧
      h2 * w ≤ CH * (1 + L) := by
  have haa : a * a ≤ 1 := mul_le_one₀ ha1 ha ha1
  have haaL : a * (a * L) ≤ 1 := mul_le_one₀ ha1 (mul_nonneg ha hL) haL
  have e0 : a ^ 2 * (1 + L) ≤ 2 := by
    have : a ^ 2 * (1 + L) = a * a + a * (a * L) := by ring
    linarith
  have e1 : a * (1 + L) ≤ 2 := by
    have : a * (1 + L) = a + a * L := by ring
    linarith
  have e2 : a * (w1 * a) ≤ 1 := mul_le_one₀ ha1 (mul_nonneg nw1 ha) hw1
  have hBa2 : 0 ≤ B * a ^ 2 := by positivity
  have hBa : 0 ≤ B * a := by positivity
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · calc h0 * w ≤ B * a ^ 2 * (1 + L) := mul_le_mul q0 hw nw hBa2
      _ = B * (a ^ 2 * (1 + L)) := by ring
      _ ≤ B * 2 := mul_le_mul_of_nonneg_left e0 hB
      _ = 2 * B := by ring
  · calc h1 * w ≤ B * a * (1 + L) := mul_le_mul q1 hw nw hBa
      _ = B * (a * (1 + L)) := by ring
      _ ≤ B * 2 := mul_le_mul_of_nonneg_left e1 hB
      _ = 2 * B := by ring
  · calc h0 * w1 ≤ B * a ^ 2 * w1 := mul_le_mul_of_nonneg_right q0 nw1
      _ = B * (a * (w1 * a)) := by ring
      _ ≤ B * 1 := mul_le_mul_of_nonneg_left e2 hB
      _ = B := mul_one B
  · calc h1 * w1 ≤ B * a * w1 := mul_le_mul_of_nonneg_right q1 nw1
      _ = B * (w1 * a) := by ring
      _ ≤ B * 1 := mul_le_mul_of_nonneg_left hw1 hB
      _ = B := mul_one B
  · calc h0 * w2 ≤ B * a ^ 2 * w2 := mul_le_mul_of_nonneg_right q0 nw2
      _ = B * (w2 * a ^ 2) := by ring
      _ ≤ B * 1 := mul_le_mul_of_nonneg_left hw2 hB
      _ = B := mul_one B
  · exact mul_le_mul h2le hw nw hCH

/-- one product away from zero (`a = |s| ≥ 1`) -/
private lemma key_far_one {CH a g v : ℝ} (ha1 : 1 ≤ a) (ng : 0 ≤ g) (hv : v ≤ 1 + a)
    (d : g * (1 + a) ^ 3 ≤ CH) : g * v ≤ CH * (1 / (1 + a ^ 2)) := by
  have hpos : 0 < 1 + a ^ 2 := by positivity
  rw [mul_one_div, le_div_iff₀ hpos]
  have h1 : (1 + a) * (1 + a ^ 2) ≤ (1 + a) ^ 3 := by
    have : (1 + a) ^ 3 = (1 + a) * (1 + a ^ 2) + (1 + a) * (2 * a) := by ring
    have : 0 ≤ (1 + a) * (2 * a) := by positivity
    linarith
  calc g * v * (1 + a ^ 2) ≤ g * (1 + a) * (1 + a ^ 2) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hv ng) hpos.le
    _ = g * ((1 + a) * (1 + a ^ 2)) := by ring
    _ ≤ g * (1 + a) ^ 3 := mul_le_mul_of_nonneg_left h1 ng
    _ ≤ CH := d

/-- The pointwise real inequalities behind the domination of `F, F', F''`. -/
private lemma key_bound {B CH c s h0 h1 h2 : ℝ} (hB : 0 ≤ B) (hCH : 0 ≤ CH) (hc : 0 < c)
    (hc4 : c ≤ 1 / 4) (hs : s ≠ 0) (n0 : 0 ≤ h0) (n1 : 0 ≤ h1) (n2 : 0 ≤ h2)
    (q0 : h0 ≤ B * s ^ 2) (q1 : h1 ≤ B * |s|)
    (d0 : h0 * (1 + |s|) ^ 3 ≤ CH) (d1 : h1 * (1 + |s|) ^ 3 ≤ CH)
    (d2 : h2 * (1 + |s|) ^ 3 ≤ CH) :
    h0 * |gamOm c s| ≤ (4 * CH + 3 * B) * gamDom s ∧
    h1 * |gamOm c s| + h0 * |gamOm1 c s| ≤ (4 * CH + 3 * B) * gamDom s ∧
    h2 * |gamOm c s| + h1 * |gamOm1 c s| + (h1 * |gamOm1 c s| + h0 * |gamOm2 c s|)
      ≤ (4 * CH + 3 * B) * gamDom s := by
  have ha : 0 < |s| := abs_pos.mpr hs
  have hw := abs_gamOm_le hc hc4 hs
  have hw1 := abs_gamOm1_mul_le hc s
  have hw2 := abs_gamOm2_mul_le hc s
  rw [← sq_abs s] at hw2 q0
  have hL : 0 ≤ |Real.log s| := abs_nonneg _
  have nw : 0 ≤ |gamOm c s| := abs_nonneg _
  have nw1 : 0 ≤ |gamOm1 c s| := abs_nonneg _
  have nw2 : 0 ≤ |gamOm2 c s| := abs_nonneg _
  have hK : 0 ≤ 4 * CH + 3 * B := by positivity
  by_cases ha1 : |s| ≤ 1
  · -- near zero
    have hG : 1 + |Real.log s| ≤ gamDom s := by
      unfold gamDom
      rw [Set.indicator_of_mem (by rw [Set.mem_Icc, ← abs_le]; exact ha1)]
      have : 0 < 1 / (1 + s ^ 2) := by positivity
      linarith
    have haL : |s| * |Real.log s| ≤ 1 := by
      have h := Real.abs_log_mul_self_lt |s| ha ha1
      rw [Real.log_abs, abs_mul, abs_abs, mul_comm] at h
      exact h.le
    have h2le : h2 ≤ CH := by
      have h1' : (1 : ℝ) ≤ (1 + |s|) ^ 3 := one_le_pow₀ (by linarith)
      calc h2 = h2 * 1 := (mul_one _).symm
        _ ≤ h2 * (1 + |s|) ^ 3 := mul_le_mul_of_nonneg_left h1' n2
        _ ≤ CH := d2
    obtain ⟨p0, p1, p2, p3, p4, p5⟩ :=
      key_near hB hCH ha.le ha1 hL haL nw nw1 nw2 hw hw1 hw2 q0 q1 h2le
    have hbig : (4 * CH + 3 * B) * (1 + |Real.log s|) ≤ (4 * CH + 3 * B) * gamDom s :=
      mul_le_mul_of_nonneg_left hG hK
    have hexp : (4 * CH + 3 * B) * (1 + |Real.log s|)
        = CH * (1 + |Real.log s|) + 3 * B + (3 * CH * (1 + |Real.log s|)
          + 3 * B * |Real.log s|) := by ring
    have hrest : 0 ≤ 3 * CH * (1 + |Real.log s|) + 3 * B * |Real.log s| := by positivity
    have hCL : 0 ≤ CH * (1 + |Real.log s|) := by positivity
    refine ⟨by linarith, by linarith, by linarith⟩
  · -- away from zero
    have ha1' : 1 ≤ |s| := (not_le.mp ha1).le
    have hG : gamDom s = 1 / (1 + |s| ^ 2) := by
      unfold gamDom
      rw [Set.indicator_of_notMem (by rw [Set.mem_Icc, ← abs_le]; exact ha1), zero_add, sq_abs]
    have hwa : |gamOm c s| ≤ 1 + |s| := by
      have h1 : Real.log |s| ≤ |s| - 1 := Real.log_le_sub_one_of_pos ha
      have h2 : |Real.log s| = Real.log |s| := by
        rw [← Real.log_abs s]; exact abs_of_nonneg (Real.log_nonneg ha1')
      linarith
    have hw1' : |gamOm1 c s| ≤ 1 + |s| := by
      have : |gamOm1 c s| * 1 ≤ |gamOm1 c s| * |s| := mul_le_mul_of_nonneg_left ha1' nw1
      linarith
    have hw2' : |gamOm2 c s| ≤ 1 + |s| := by
      have h1 : (1 : ℝ) ≤ |s| ^ 2 := one_le_pow₀ ha1'
      have : |gamOm2 c s| * 1 ≤ |gamOm2 c s| * |s| ^ 2 := mul_le_mul_of_nonneg_left h1 nw2
      linarith
    have p0 := key_far_one ha1' n0 hwa d0
    have p1 := key_far_one ha1' n1 hwa d1
    have p2 := key_far_one ha1' n2 hwa d2
    have p3 := key_far_one ha1' n0 hw1' d0
    have p4 := key_far_one ha1' n1 hw1' d1
    have p5 := key_far_one ha1' n0 hw2' d0
    rw [hG]
    have hR : 0 < 1 / (1 + |s| ^ 2) := by positivity
    have hexp : (4 * CH + 3 * B) * (1 / (1 + |s| ^ 2))
        = 4 * (CH * (1 / (1 + |s| ^ 2))) + 3 * B * (1 / (1 + |s| ^ 2)) := by ring
    have hrest : 0 ≤ 3 * B * (1 / (1 + |s| ^ 2)) := by positivity
    have hCR : 0 ≤ CH * (1 / (1 + |s| ^ 2)) := by positivity
    refine ⟨by linarith, by linarith, by linarith⟩

/-! ## Fourier decay -/

/-- Analytic core: a `C²` function with `F, F', F''` dominated a.e. by an integrable `G`
has `(1 + u²) ‖𝓕 F u‖ ≤ 2 ∫ G`. -/
private lemma fourier_bound_of_dominated {F : ℝ → ℂ} (hF : ContDiff ℝ 2 F) {G : ℝ → ℝ}
    (hG : Integrable G) (h0 : ∀ᵐ s, ‖F s‖ ≤ G s) (h1 : ∀ᵐ s, ‖deriv F s‖ ≤ G s)
    (h2 : ∀ᵐ s, ‖deriv (deriv F) s‖ ≤ G s) (u : ℝ) :
    (1 + u ^ 2) * ‖𝓕 F u‖ ≤ 2 * ∫ s, G s := by
  have e1 : iteratedDeriv 1 F = deriv F := iteratedDeriv_one
  have e2 : iteratedDeriv 2 F = deriv (deriv F) := by
    rw [iteratedDeriv_succ, iteratedDeriv_one]
  have c1 : Continuous (deriv F) := e1 ▸ hF.continuous_iteratedDeriv 1 (by norm_num)
  have c2 : Continuous (deriv (deriv F)) := e2 ▸ hF.continuous_iteratedDeriv 2 le_rfl
  let f : W21 := ⟨F, hF, fun k hk => by
    interval_cases k
    · rw [iteratedDeriv_zero]; exact hG.mono' hF.continuous.aestronglyMeasurable h0
    · rw [e1]; exact hG.mono' c1.aestronglyMeasurable h1
    · rw [e2]; exact hG.mono' c2.aestronglyMeasurable h2⟩
  have key := fourierIntegral_self_add_deriv_deriv f u
  have hpi : 1 / (4 * π ^ 2) ≤ (1 : ℝ) := by
    have h3 : (3 : ℝ) < π := Real.pi_gt_three
    rw [div_le_one (by positivity)]
    nlinarith
  set g : ℝ → ℂ := fun v : ℝ => F v - (1 / (4 * π ^ 2)) * deriv (deriv F) v with hg
  have hnorm : ‖𝓕 g u‖ ≤ ∫ v, ‖g v‖ :=
    VectorFourier.norm_fourierIntegral_le_integral_norm 𝐞 volume (innerₗ ℝ) g u
  have hmono : ∫ v, ‖g v‖ ≤ ∫ v, 2 * G v := by
    refine integral_mono_of_nonneg (ae_of_all _ fun _ => norm_nonneg _) (hG.const_mul 2) ?_
    filter_upwards [h0, h2] with v hv0 hv2
    have hcn : ‖(1 / (4 * (π : ℂ) ^ 2))‖ ≤ 1 := by
      have : (1 / (4 * (π : ℂ) ^ 2)) = ((1 / (4 * π ^ 2) : ℝ) : ℂ) := by push_cast; rfl
      rw [this, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
      exact hpi
    calc ‖g v‖ ≤ ‖F v‖ + ‖(1 / (4 * (π : ℂ) ^ 2)) * deriv (deriv F) v‖ :=
          norm_sub_le _ _
      _ ≤ ‖F v‖ + 1 * ‖deriv (deriv F) v‖ := by
        rw [norm_mul]
        gcongr
      _ ≤ 2 * G v := by linarith
  rw [integral_const_mul] at hmono
  have hL : ‖((1 : ℂ) + (u : ℂ) ^ 2) * 𝓕 F u‖ = (1 + u ^ 2) * ‖𝓕 F u‖ := by
    have : ((1 : ℂ) + (u : ℂ) ^ 2) = ((1 + u ^ 2 : ℝ) : ℂ) := by push_cast; rfl
    rw [norm_mul, this, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  rw [← hL]
  have key' : ((1 : ℂ) + (u : ℂ) ^ 2) * 𝓕 F u = 𝓕 g u := key
  rw [key']
  exact hnorm.trans hmono

/-- The transform of `H · ω_T` decays like `1/(1+y²)`, uniformly in `T ≥ 2`. -/
theorem gamma_bound (H : 𝓢(ℝ, ℂ)) (hH0 : H 0 = 0) (hH1 : deriv (⇑H) 0 = 0) :
    ∃ C : ℝ, ∀ T : ℝ, 2 ≤ T → ∀ y : ℝ,
      ‖(1 / (2 * π) : ℂ) * ∫ s, H s * (omegaT T s : ℂ) * Complex.exp (Complex.I * s * y)‖
        ≤ C / (1 + y ^ 2) := by
  obtain ⟨B, hB, hBq⟩ := quadratic_bound H hH0 hH1
  set H1 : 𝓢(ℝ, ℂ) := SchwartzMap.derivCLM ℝ ℂ H with hH1def
  set H2 : 𝓢(ℝ, ℂ) := SchwartzMap.derivCLM ℝ ℂ H1 with hH2def
  have e1 : ∀ x, deriv (⇑H) x = H1 x := fun x => rfl
  obtain ⟨K0, hK0, hK0b⟩ := schwartz_decay3 H
  obtain ⟨K1, hK1, hK1b⟩ := schwartz_decay3 H1
  obtain ⟨K2, hK2, hK2b⟩ := schwartz_decay3 H2
  set CH : ℝ := K0 + K1 + K2 with hCH
  have hCH0 : 0 ≤ CH := by positivity
  set Cs : ℝ := 4 * CH + 3 * B with hCs
  set M : ℝ := Cs * ∫ s, gamDom s with hM
  refine ⟨4 * π * M, fun T hT y => ?_⟩
  -- the parameter `c = 1 / T ^ 2`
  set c : ℝ := 1 / T ^ 2 with hc
  have hc0 : 0 < c := by positivity
  have hc4 : c ≤ 1 / 4 := by
    rw [hc]
    have : (4 : ℝ) ≤ T ^ 2 := by nlinarith
    exact one_div_le_one_div_of_le (by norm_num) this
  -- the function and its two derivatives
  set F : ℝ → ℂ := fun s => H s * (gamOm c s : ℂ) with hFdef
  set F1 : ℝ → ℂ := fun s => H1 s * (gamOm c s : ℂ) + H s * (gamOm1 c s : ℂ) with hF1def
  set F2 : ℝ → ℂ := fun s => H2 s * (gamOm c s : ℂ) + H1 s * (gamOm1 c s : ℂ)
    + (H1 s * (gamOm1 c s : ℂ) + H s * (gamOm2 c s : ℂ)) with hF2def
  have hF : ContDiff ℝ 2 F :=
    (H.smooth 2).mul (Complex.ofRealCLM.contDiff.comp (contDiff_gamOm hc0))
  have hd1 : ∀ s, HasDerivAt F (F1 s) s := fun s =>
    (H.hasDerivAt s).mul (hasDerivAt_gamOm hc0 s).ofReal_comp
  have hd2 : ∀ s, HasDerivAt F1 (F2 s) s := fun s =>
    ((H1.hasDerivAt s).mul (hasDerivAt_gamOm hc0 s).ofReal_comp).add
      ((H.hasDerivAt s).mul (hasDerivAt_gamOm1 hc0 s).ofReal_comp)
  have ed1 : deriv F = F1 := funext fun s => (hd1 s).deriv
  have ed2 : deriv (deriv F) = F2 := by rw [ed1]; exact funext fun s => (hd2 s).deriv
  -- domination almost everywhere
  have hae : ∀ᵐ s : ℝ, s ≠ 0 := by
    have : ({0}ᶜ : Set ℝ) ∈ ae (volume : Measure ℝ) :=
      compl_mem_ae_iff.mpr (measure_singleton 0)
    exact this
  have hkey : ∀ s : ℝ, s ≠ 0 →
      ‖F s‖ ≤ Cs * gamDom s ∧ ‖F1 s‖ ≤ Cs * gamDom s ∧
        ‖F2 s‖ ≤ Cs * gamDom s := by
    intro s hs
    have hpow : 0 ≤ (1 + |s|) ^ 3 := by positivity
    have d0 : ‖H s‖ * (1 + |s|) ^ 3 ≤ CH := by
      have := hK0b s; rw [hCH]; linarith
    have d1 : ‖H1 s‖ * (1 + |s|) ^ 3 ≤ CH := by
      have := hK1b s; rw [hCH]; linarith
    have d2 : ‖H2 s‖ * (1 + |s|) ^ 3 ≤ CH := by
      have := hK2b s; rw [hCH]; linarith
    have q1 : ‖H1 s‖ ≤ B * |s| := by rw [← e1]; exact (hBq s).2
    obtain ⟨b0, b1, b2⟩ := key_bound hB hCH0 hc0 hc4 hs (norm_nonneg (H s))
      (norm_nonneg (H1 s)) (norm_nonneg (H2 s)) (hBq s).1 q1 d0 d1 d2
    have nr : ∀ r : ℝ, ‖(r : ℂ)‖ = |r| := fun r => by
      rw [Complex.norm_real, Real.norm_eq_abs]
    refine ⟨?_, ?_, ?_⟩
    · calc ‖F s‖ = ‖H s‖ * |gamOm c s| := by rw [hFdef]; simp only [norm_mul, nr]
        _ ≤ Cs * gamDom s := b0
    · calc ‖F1 s‖ ≤ ‖H1 s * (gamOm c s : ℂ)‖ + ‖H s * (gamOm1 c s : ℂ)‖ :=
            norm_add_le _ _
        _ = ‖H1 s‖ * |gamOm c s| + ‖H s‖ * |gamOm1 c s| := by simp only [norm_mul, nr]
        _ ≤ Cs * gamDom s := b1
    · calc ‖F2 s‖ ≤ ‖H2 s * (gamOm c s : ℂ) + H1 s * (gamOm1 c s : ℂ)‖
            + ‖H1 s * (gamOm1 c s : ℂ) + H s * (gamOm2 c s : ℂ)‖ := norm_add_le _ _
        _ ≤ (‖H2 s * (gamOm c s : ℂ)‖ + ‖H1 s * (gamOm1 c s : ℂ)‖)
            + (‖H1 s * (gamOm1 c s : ℂ)‖ + ‖H s * (gamOm2 c s : ℂ)‖) :=
          add_le_add (norm_add_le _ _) (norm_add_le _ _)
        _ = ‖H2 s‖ * |gamOm c s| + ‖H1 s‖ * |gamOm1 c s|
            + (‖H1 s‖ * |gamOm1 c s| + ‖H s‖ * |gamOm2 c s|) := by simp only [norm_mul, nr]
        _ ≤ Cs * gamDom s := b2
  have hG : Integrable (fun s => Cs * gamDom s) := integrable_gamDom.const_mul Cs
  have a0 : ∀ᵐ s, ‖F s‖ ≤ Cs * gamDom s := hae.mono fun s hs => (hkey s hs).1
  have a1 : ∀ᵐ s, ‖deriv F s‖ ≤ Cs * gamDom s := by
    rw [ed1]; exact hae.mono fun s hs => (hkey s hs).2.1
  have a2 : ∀ᵐ s, ‖deriv (deriv F) s‖ ≤ Cs * gamDom s := by
    rw [ed2]; exact hae.mono fun s hs => (hkey s hs).2.2
  have key := fourier_bound_of_dominated hF hG a0 a1 a2 (-y / (2 * π))
  rw [integral_const_mul, ← hM] at key
  -- identify the integral with the Fourier transform
  have hint : ∫ s, H s * (omegaT T s : ℂ) * Complex.exp (Complex.I * s * y)
      = 𝓕 F (-y / (2 * π)) := by
    rw [← Zeta23.paperFT_ofReal_eq_fourier, Zeta23.paperFT_def]
    refine integral_congr_ae (ae_of_all _ fun s => ?_)
    show H s * (omegaT T s : ℂ) * Complex.exp (Complex.I * s * y)
      = H s * (gamOm c s : ℂ) * Complex.exp (Complex.I * y * s)
    rw [mul_right_comm Complex.I (s : ℂ) (y : ℂ)]
    rfl
  rw [hint]
  set N : ℝ := ‖𝓕 F (-y / (2 * π))‖ with hN
  have hN0 : 0 ≤ N := norm_nonneg _
  have hpi : 0 < π := Real.pi_pos
  have hnc : ‖(1 / (2 * π) : ℂ)‖ = 1 / (2 * π) := by
    have : (1 / (2 * π) : ℂ) = ((1 / (2 * π) : ℝ) : ℂ) := by push_cast; rfl
    rw [this, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  rw [norm_mul, hnc, ← hN, le_div_iff₀ (by positivity)]
  have hu : 1 + y ^ 2 ≤ 4 * π ^ 2 * (1 + (-y / (2 * π)) ^ 2) := by
    have e : 4 * π ^ 2 * (1 + (-y / (2 * π)) ^ 2) = 4 * π ^ 2 + y ^ 2 := by
      field_simp
      ring
    rw [e]
    nlinarith [Real.pi_gt_three]
  calc 1 / (2 * π) * N * (1 + y ^ 2)
      ≤ 1 / (2 * π) * N * (4 * π ^ 2 * (1 + (-y / (2 * π)) ^ 2)) :=
        mul_le_mul_of_nonneg_left hu (by positivity)
    _ = 2 * π * ((1 + (-y / (2 * π)) ^ 2) * N) := by
        field_simp
        ring
    _ ≤ 2 * π * (2 * M) := mul_le_mul_of_nonneg_left key (by positivity)
    _ = 4 * π * M := by ring

end WeightAux
end TMA

end
end Src_TMA_WeightAuxGamma

section Src_TMA_WeightAux2
/-
Written for Kristian Muri Knausgård, drafted with Claude (Anthropic), 22 November 2026.

TMA/WeightAux2.lean — auxiliary file for TMA/Weight.lean.
Assembly: from a compactly supported Schwartz function `k0` whose paper transform is a real function
`q` with `q 0 = 0` and `q ≥ 1` on `[1,2]`, the pair `k = k0 ⋆ k0`, `h = q²` is a height weight.
-/

open MeasureTheory Complex
open scoped Real FourierTransform SchwartzMap

noncomputable section
namespace TMA
namespace WeightAux

open Zeta23

/-- The height weight `k = k0 ⋆ k0`, `h = q²`. -/
theorem exists_heightWeight_of_sqrt (k0 : 𝓢(ℝ, ℂ)) (q : ℝ → ℝ) (Λ : ℝ) (hΛ : 0 < Λ)
    (hsupp : ∀ u, k0 u ≠ 0 → |u| ≤ Λ)
    (hq : ∀ x : ℝ, paperFT k0 (x : ℂ) = (q x : ℂ))
    (hq0 : q 0 = 0)
    (hq1 : ∀ x, 1 ≤ x → x ≤ 2 → 1 ≤ q x) :
    ∃ w : HeightWeight, w.h = fun x => q x ^ 2 := by
  -- the transform of `k = k0 ⋆ k0`
  have hk : ∀ x : ℝ, paperFT (conv k0 k0) (x : ℂ) = ((q x ^ 2 : ℝ) : ℂ) := by
    intro x
    rw [paperFT_conv, hq]
    push_cast
    ring
  have hPF : ∀ x : ℝ, PF (conv k0 k0) x = ((q x ^ 2 : ℝ) : ℂ) := by
    intro x
    rw [PF_apply, hk]
  have hqre : q = fun x => (PF k0 x).re := by
    funext x
    rw [PF_apply, hq, ofReal_re]
  have hqcont : Continuous q := by
    rw [hqre]
    exact Complex.continuous_re.comp (PF k0).continuous
  have hH0 : PF (conv k0 k0) 0 = 0 := by
    rw [hPF, hq0]
    simp
  have hH1 : deriv (⇑(PF (conv k0 k0))) 0 = 0 := by
    have hfun : (⇑(PF (conv k0 k0)) : ℝ → ℂ) = fun x => PF k0 x * PF k0 x := by
      funext x
      rw [PF_apply, PF_apply, paperFT_conv]
    have hd : HasDerivAt (⇑(PF k0)) (deriv (⇑(PF k0)) 0) 0 :=
      (PF k0).differentiableAt.hasDerivAt
    have h0 : PF k0 0 = 0 := by
      rw [PF_apply, hq, hq0]
      simp
    have := (hd.mul hd).deriv
    rw [hfun]
    rw [h0, mul_zero, zero_mul, add_zero] at this
    exact this
  obtain ⟨B, hB0, hB⟩ := quadratic_bound (PF (conv k0 k0)) hH0 hH1
  obtain ⟨C, hC⟩ := gamma_bound (PF (conv k0 k0)) hH0 hH1
  refine ⟨{
    k := conv k0 k0
    h := fun x => q x ^ 2
    kappa := Λ + Λ
    kappa_pos := by linarith
    k_contDiff := (conv k0 k0).smooth 2
    k_supp := conv_supp hsupp hsupp
    h_eq := hk
    h_nonneg := fun x => sq_nonneg _
    h_ge_one := fun x hx1 hx2 => by
      have := hq1 x hx1 hx2
      nlinarith
    h_cont := hqcont.pow 2
    h_int := by
      have h1 : Integrable (fun x => (PF (conv k0 k0) x).re) := (PF (conv k0 k0)).integrable.re
      have h2 : (fun x => (PF (conv k0 k0) x).re) = fun x => q x ^ 2 := by
        funext x
        rw [hPF, ofReal_re]
      rw [h2] at h1
      exact h1
    k_integral_zero := by
      rw [← paperFT_zero, hk, hq0]
      simp
    h_small := by
      refine ⟨B, fun x _ => ?_⟩
      have h1 := (hB x).1
      rw [hPF, Complex.norm_real, Real.norm_eq_abs] at h1
      exact (le_abs_self _).trans h1
    inv := by
      intro y
      rw [← paperFT_inv (conv k0 k0) y]
      congr 2
      funext s
      rw [hk]
    inv2 := by
      rw [paperFT_plancherel (conv k0 k0)]
      congr 2
      funext x
      rw [hk, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    inv3 := by
      rw [paperFT_triple (conv k0 k0)]
      have h1 : (fun x : ℝ => paperFT (conv k0 k0) (x : ℂ) ^ 3)
          = fun x : ℝ => (((q x ^ 2) ^ 3 : ℝ) : ℂ) := by
        funext x
        rw [hk]
        push_cast
        ring
      rw [h1, integral_complex_ofReal]
      push_cast
      ring
    gammaBound := by
      refine ⟨C, fun T hT y => ?_⟩
      have h1 := hC T hT y
      have h2 : (fun s : ℝ => PF (conv k0 k0) s * (omegaT T s : ℂ) * Complex.exp (Complex.I * s * y))
          = fun s : ℝ => ((q s ^ 2 : ℝ) : ℂ) * (omegaT T s : ℂ) * Complex.exp (Complex.I * s * y) := by
        funext s
        rw [hPF]
      rw [h2] at h1
      exact h1 }, rfl⟩

end WeightAux
end TMA
end
end Src_TMA_WeightAux2

section Src_TMA_WeightAux3
/-
Written for Kristian Muri Knausgård, drafted with Claude (Anthropic), 22 November 2026.

TMA/WeightAux3.lean — auxiliary file for TMA/Weight.lean.
The mollifier: with a smooth bump `b` (support in `[-2,2]`), `β = paperFT b` is real,
`B = b ⋆ b` has transform `β² ≥ 0`, and `p_K(x) = K β(Kx)²/c` (`c = ∫ β²`) is a nonnegative
approximate identity whose inverse transform `P_K(u) = B(u/K)/c` is smooth with support in `[-4K, 4K]`.
-/

open MeasureTheory Complex Filter Topology
open scoped Real FourierTransform SchwartzMap

noncomputable section
namespace TMA
namespace WeightAux

open Zeta23

/-! ### Schwartz maps from bump functions -/

/-- complexification of a real bump function, as a Schwartz map -/
def bumpS {c : ℝ} (f : ContDiffBump c) : 𝓢(ℝ, ℂ) :=
  HasCompactSupport.toSchwartzMap (f := fun u => ((f u : ℝ) : ℂ))
    (f.hasCompactSupport.comp_left Complex.ofReal_zero)
    (Complex.ofRealCLM.contDiff.comp f.contDiff)

lemma bumpS_apply {c : ℝ} (f : ContDiffBump c) (u : ℝ) : bumpS f u = ((f u : ℝ) : ℂ) := rfl

lemma ssmul_apply (a : ℂ) (f : 𝓢(ℝ, ℂ)) (u : ℝ) : (a • f) u = a * f u := rfl

lemma ssub_apply (f g : 𝓢(ℝ, ℂ)) (u : ℝ) : (f - g) u = f u - g u := rfl

lemma paperFT_smul (a : ℂ) (f : 𝓢(ℝ, ℂ)) (z : ℂ) :
    paperFT ((a • f : 𝓢(ℝ, ℂ)) : ℝ → ℂ) z = a * paperFT f z := by
  rw [paperFT_def, paperFT_def, ← integral_const_mul_C]
  congr 1
  funext u
  rw [ssmul_apply, mul_assoc]

/-- scaling: the transform of `f(u/K)` is `K f^(Kx)` -/
lemma paperFT_scale (f : 𝓢(ℝ, ℂ)) {K : ℝ} (hK : 0 < K) (x : ℝ) :
    paperFT (sScale K⁻¹ (inv_ne_zero hK.ne') f) (x : ℂ) = K * paperFT f ((K * x : ℝ) : ℂ) := by
  have hK' : (K : ℂ) ≠ 0 := by exact_mod_cast hK.ne'
  rw [paperFT_def, paperFT_def]
  have h := MeasureTheory.Measure.integral_comp_mul_right
    (fun v : ℝ => f v * cexp (I * ((K * x : ℝ) : ℂ) * v)) K⁻¹
  rw [inv_inv, abs_of_pos hK, Complex.real_smul] at h
  rw [← h]
  congr 1
  funext u
  simp only [sScale_apply]
  congr 2
  push_cast
  field_simp

/-! ### The basic bump and its transform -/

/-- the basic bump function: `1` on `[-1,1]`, support `(-2,2)` -/
def bump0 : ContDiffBump (0 : ℝ) := ⟨1, 2, zero_lt_one, one_lt_two⟩

/-- `β(x) = ∫ b(u) e^{ixu} du` (a real number) -/
def beta (x : ℝ) : ℝ := (paperFT (bumpS bump0) (x : ℂ)).re

lemma paperFT_bump (x : ℝ) : paperFT (bumpS bump0) (x : ℂ) = (beta x : ℂ) := by
  have hconj : (starRingEnd ℂ) (paperFT (bumpS bump0) (x : ℂ)) = paperFT (bumpS bump0) (x : ℂ) := by
    rw [paperFT_def, ← integral_conj]
    refine Eq.trans ?_
      (integral_neg_eq_self (fun u : ℝ => bumpS bump0 u * cexp (I * x * u)) volume)
    congr 1
    funext u
    change (starRingEnd ℂ) (bumpS bump0 u * cexp (I * x * u))
      = bumpS bump0 (-u) * cexp (I * x * ((-u : ℝ) : ℂ))
    rw [map_mul, bumpS_apply, bumpS_apply, Complex.conj_ofReal, ← Complex.exp_conj, bump0.neg]
    congr 2
    simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
    push_cast
    ring
  have him : (paperFT (bumpS bump0) (x : ℂ)).im = 0 := Complex.conj_eq_iff_im.mp hconj
  apply Complex.ext
  · simp [beta]
  · simp [him]

lemma bump0_supp : ∀ u, bumpS bump0 u ≠ 0 → |u| ≤ 2 := by
  intro u hu
  have h1 : u ∈ Function.support (bump0 : ℝ → ℝ) := by
    rw [Function.mem_support]
    intro h
    apply hu
    rw [bumpS_apply, h, Complex.ofReal_zero]
  rw [bump0.support_eq, Metric.mem_ball, Real.dist_eq, sub_zero] at h1
  exact h1.le

lemma beta_zero : beta 0 = ∫ u, bump0 u := by
  have h := paperFT_zero (bumpS bump0)
  unfold beta
  rw [h]
  have h2 : (fun u => bumpS bump0 u) = fun u => ((bump0 u : ℝ) : ℂ) := rfl
  rw [h2, integral_complex_ofReal, ofReal_re]

lemma beta_zero_pos : 0 < beta 0 := by
  rw [beta_zero]
  exact bump0.integral_pos

lemma abs_beta_le (x : ℝ) : |beta x| ≤ beta 0 := by
  have h1 : ‖paperFT (bumpS bump0) (x : ℂ)‖ ≤ ∫ u, ‖bumpS bump0 u‖ := by
    have := norm_paperFT_le (bumpS bump0).integrable bump0_supp (x : ℂ)
    simpa using this
  rw [paperFT_bump, Complex.norm_real, Real.norm_eq_abs] at h1
  refine h1.trans (le_of_eq ?_)
  rw [beta_zero]
  congr 1
  funext u
  rw [bumpS_apply, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg bump0.nonneg]

lemma beta_continuous : Continuous beta := by
  have : beta = fun x => (PF (bumpS bump0) x).re := by
    funext x
    rw [PF_apply]
    rfl
  rw [this]
  exact Complex.continuous_re.comp (PF _).continuous

/-! ### The autocorrelation -/

/-- `B = b ⋆ b` -/
def BS : 𝓢(ℝ, ℂ) := conv (bumpS bump0) (bumpS bump0)

lemma BS_supp : ∀ u, BS u ≠ 0 → |u| ≤ 4 := by
  intro u hu
  have := conv_supp bump0_supp bump0_supp u hu
  linarith

lemma paperFT_BS (x : ℝ) : paperFT BS (x : ℂ) = ((beta x ^ 2 : ℝ) : ℂ) := by
  unfold BS
  rw [paperFT_conv, paperFT_bump]
  push_cast
  ring

lemma beta_sq_integrable : Integrable (fun x => beta x ^ 2) := by
  have h1 : Integrable (fun x => (PF BS x).re) := (PF BS).integrable.re
  have h2 : (fun x => (PF BS x).re) = fun x => beta x ^ 2 := by
    funext x
    rw [PF_apply, paperFT_BS, ofReal_re]
  rwa [h2] at h1

/-- `c = ∫ β²` -/
def cpsi : ℝ := ∫ x, beta x ^ 2

lemma cpsi_pos : 0 < cpsi :=
  integral_pos_of_integrable_nonneg_nonzero (x := 0) (beta_continuous.pow 2) beta_sq_integrable
    (fun x => sq_nonneg (beta x)) (pow_ne_zero 2 beta_zero_pos.ne')

/-- the normalised mollifier `p₁ = β²/c`, with `∫ p₁ = 1` -/
def p1 (x : ℝ) : ℝ := beta x ^ 2 / cpsi

lemma p1_nonneg (x : ℝ) : 0 ≤ p1 x := div_nonneg (sq_nonneg _) cpsi_pos.le

lemma p1_le (x : ℝ) : p1 x ≤ p1 0 := by
  unfold p1
  have h := abs_le.mp (abs_beta_le x)
  exact div_le_div_of_nonneg_right (sq_le_sq' h.1 h.2) cpsi_pos.le

lemma p1_zero_pos : 0 < p1 0 := div_pos (pow_pos beta_zero_pos 2) cpsi_pos

lemma p1_integrable : Integrable p1 := beta_sq_integrable.div_const _

lemma p1_continuous : Continuous p1 := (beta_continuous.pow 2).div_const _

lemma p1_integral : ∫ x, p1 x = 1 := by
  unfold p1
  rw [integral_div]
  exact div_self cpsi_pos.ne'

lemma tendsto_p1_tail : Tendsto (fun R : ℝ => ∫ z in (-R)..R, p1 z) atTop (𝓝 1) := by
  have := intervalIntegral_tendsto_integral p1_integrable tendsto_neg_atTop_atBot tendsto_id
  rw [p1_integral] at this
  exact this

/-! ### The scaled mollifier -/

/-- `P_K(u) = B(u/K)/c` -/
def PK (K : ℝ) (hK : 0 < K) : 𝓢(ℝ, ℂ) :=
  sScale K⁻¹ (inv_ne_zero hK.ne') (((1 / cpsi : ℝ) : ℂ) • BS)

/-- `p_K(x) = K p₁(Kx)` -/
def pK (K : ℝ) (x : ℝ) : ℝ := K * p1 (K * x)

lemma paperFT_PK {K : ℝ} (hK : 0 < K) (x : ℝ) : paperFT (PK K hK) (x : ℂ) = (pK K x : ℂ) := by
  unfold PK pK p1
  rw [paperFT_scale _ hK, paperFT_smul, paperFT_BS]
  push_cast
  ring

lemma PK_supp {K : ℝ} (hK : 0 < K) : ∀ u, PK K hK u ≠ 0 → |u| ≤ 4 * K := by
  intro u hu
  have h1 : BS (u * K⁻¹) ≠ 0 := by
    intro h
    apply hu
    change (((1 / cpsi : ℝ) : ℂ) • BS) (u * K⁻¹) = 0
    rw [ssmul_apply, h, mul_zero]
  have h2 := BS_supp _ h1
  rw [abs_mul, abs_inv, abs_of_pos hK, ← div_eq_mul_inv, div_le_iff₀ hK] at h2
  exact h2

lemma pK_integral {K : ℝ} (hK : 0 < K) : ∫ x, pK K x = 1 := by
  unfold pK
  rw [integral_const_mul, MeasureTheory.Measure.integral_comp_mul_left p1 K, abs_of_pos (inv_pos.mpr hK),
    smul_eq_mul, p1_integral, mul_one]
  exact mul_inv_cancel₀ hK.ne'

lemma pK_interval {K : ℝ} (δ : ℝ) :
    ∫ z in (-δ)..δ, pK K z = ∫ z in (-(K * δ))..(K * δ), p1 z := by
  unfold pK
  rw [intervalIntegral.integral_const_mul, intervalIntegral.mul_integral_comp_mul_left, mul_neg]

/-- **The mollifier.** For `δ, η > 0` there is a nonnegative `p` with `∫ p = 1`, with all but `η`
(and all but `η p(0)`) of its mass in `[-δ, δ]`, which is the transform of a compactly supported
Schwartz function `P`. -/
theorem exists_mollifier {δ η : ℝ} (hδ : 0 < δ) (hη : 0 < η) :
    ∃ (P : 𝓢(ℝ, ℂ)) (p : ℝ → ℝ) (Λ : ℝ), 0 < Λ ∧ (∀ u, P u ≠ 0 → |u| ≤ Λ) ∧
      (∀ x : ℝ, paperFT P (x : ℂ) = (p x : ℂ)) ∧ (∀ x, 0 ≤ p x) ∧ (∀ x, p x ≤ p 0) ∧ 0 < p 0 ∧
      Integrable p ∧ Continuous p ∧ ∫ x, p x = 1 ∧
      1 - η ≤ ∫ z in (-δ)..δ, p z ∧ 1 - η * p 0 ≤ ∫ z in (-δ)..δ, p z := by
  have hη'pos : 0 < min η (η * p1 0) := lt_min hη (mul_pos hη p1_zero_pos)
  have ht : Tendsto (fun K : ℝ => ∫ z in (-(K * δ))..(K * δ), p1 z) atTop (𝓝 1) :=
    tendsto_p1_tail.comp (tendsto_id.atTop_mul_const hδ)
  have hev : ∀ᶠ K : ℝ in atTop, 1 - min η (η * p1 0) < ∫ z in (-(K * δ))..(K * δ), p1 z :=
    ht.eventually (lt_mem_nhds (by linarith))
  obtain ⟨K, hK, hK1⟩ := (hev.and (eventually_ge_atTop 1)).exists
  have hKpos : 0 < K := by linarith
  have hp0 : pK K 0 = K * p1 0 := by
    unfold pK
    rw [mul_zero]
  refine ⟨PK K hKpos, pK K, 4 * K, by positivity, PK_supp hKpos, paperFT_PK hKpos, ?_, ?_, ?_, ?_, ?_,
    pK_integral hKpos, ?_, ?_⟩
  · intro x
    exact mul_nonneg hKpos.le (p1_nonneg _)
  · intro x
    rw [hp0]
    exact mul_le_mul_of_nonneg_left (p1_le _) hKpos.le
  · rw [hp0]
    exact mul_pos hKpos p1_zero_pos
  · exact (p1_integrable.comp_mul_left' hKpos.ne').const_mul K
  · exact continuous_const.mul (p1_continuous.comp (continuous_const.mul continuous_id))
  · rw [pK_interval]
    have := min_le_left η (η * p1 0)
    linarith
  · rw [pK_interval, hp0]
    have h1 := min_le_right η (η * p1 0)
    have h2 : η * p1 0 ≤ η * (K * p1 0) := by
      have : p1 0 ≤ K * p1 0 := le_mul_of_one_le_left p1_zero_pos.le hK1
      exact mul_le_mul_of_nonneg_left this hη.le
    linarith

end WeightAux
end TMA
end
end Src_TMA_WeightAux3

section Src_TMA_WeightAux4
/-
Written for Kristian Muri Knausgård, drafted with Claude (Anthropic), 22 November 2026.

TMA/WeightAux4.lean — auxiliary file for TMA/Weight.lean.
The square root of the weight: for a plateau function `χ` of `[1,2]` and the mollifier `p` of
`WeightAux3`, `m = χ ⋆ p` and `q = m - (m(0)/p(0)) p`. Then `q(0) = 0`, `q ≥ 1 - 2η` on `[1,2]`,
`|q| ≤ g := m + (m(0)/p(0)) p ≤ 1 + η`, `∫ g ≤ 1 + 2η`, and `q` is the paper transform of a
compactly supported Schwartz function.
-/

open MeasureTheory Complex Filter Topology
open scoped Real FourierTransform SchwartzMap Convolution

noncomputable section
namespace TMA
namespace WeightAux

open Zeta23

/-! ### Linearity and the product formula for the paper transform -/

lemma integrable_mul_cexp (f : 𝓢(ℝ, ℂ)) (x : ℝ) :
    Integrable (fun u : ℝ => f u * cexp (I * (x : ℂ) * u)) := by
  refine f.integrable.mul_bdd (c := 1) (Continuous.aestronglyMeasurable (by fun_prop)) ?_
  filter_upwards with u
  rw [norm_cexp_I_mul]
  simp

lemma paperFT_sub (f g : 𝓢(ℝ, ℂ)) (x : ℝ) :
    paperFT ((f - g : 𝓢(ℝ, ℂ)) : ℝ → ℂ) (x : ℂ) = paperFT f (x : ℂ) - paperFT g (x : ℂ) := by
  rw [paperFT_def, paperFT_def, paperFT_def,
    ← integral_sub (integrable_mul_cexp f x) (integrable_mul_cexp g x)]
  congr 1
  funext u
  rw [ssub_apply, sub_mul]

/-- Fubini: the transform of `f(u) · g^(-u)` is `∫ g(y) f^(x - y) dy`. -/
lemma paperFT_mul_check (f g : 𝓢(ℝ, ℂ)) (x : ℝ) :
    paperFT (fun u : ℝ => f u * paperFT g ((u * (-1) : ℝ) : ℂ)) (x : ℂ)
      = ∫ y : ℝ, g y * paperFT f ((x - y : ℝ) : ℂ) := by
  simp only [paperFT_def]
  have h1 : ∀ u : ℝ,
      f u * (∫ y : ℝ, g y * cexp (I * ((u * (-1) : ℝ) : ℂ) * y)) * cexp (I * x * u)
        = ∫ y : ℝ, f u * g y * cexp (I * ((x - y : ℝ) : ℂ) * u) := by
    intro u
    rw [← integral_const_mul_C, ← integral_mul_const_C]
    congr 1
    funext y
    have he : cexp (I * ((u * (-1) : ℝ) : ℂ) * y) * cexp (I * x * u)
        = cexp (I * ((x - y : ℝ) : ℂ) * u) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    rw [← he]
    ring
  have h2 : ∀ y : ℝ, g y * (∫ u : ℝ, f u * cexp (I * ((x - y : ℝ) : ℂ) * u))
      = ∫ u : ℝ, f u * g y * cexp (I * ((x - y : ℝ) : ℂ) * u) := by
    intro y
    rw [← integral_const_mul_C]
    congr 1
    funext u
    ring
  simp only [h1, h2]
  refine integral_integral_swap ?_
  have hfg : Integrable (fun z : ℝ × ℝ => f z.1 * g z.2) (volume.prod volume) :=
    f.integrable.mul_prod g.integrable
  refine hfg.norm.mono' ?_ ?_
  · have hc : Continuous
        (Function.uncurry fun (u y : ℝ) => f u * g y * cexp (I * ((x - y : ℝ) : ℂ) * u)) := by
      change Continuous fun z : ℝ × ℝ => f z.1 * g z.2 * cexp (I * ((x - z.2 : ℝ) : ℂ) * z.1)
      fun_prop
    exact hc.aestronglyMeasurable
  · filter_upwards with z
    change ‖f z.1 * g z.2 * cexp (I * ((x - z.2 : ℝ) : ℂ) * z.1)‖ ≤ ‖f z.1 * g z.2‖
    rw [norm_mul, norm_cexp_I_mul]
    simp

/-! ### The plateau function -/

/-- the plateau function of `[1,2]`: equal to `1` on `[1-δ, 2+δ]`, support `(1-2δ, 2+2δ)` -/
def chiB (δ : ℝ) (hδ : 0 < δ) : ContDiffBump (3 / 2 : ℝ) :=
  ⟨1 / 2 + δ, 1 / 2 + 2 * δ, by linarith, by linarith⟩

lemma chiB_one {δ : ℝ} (hδ : 0 < δ) {y : ℝ} (h1 : 1 - δ ≤ y) (h2 : y ≤ 2 + δ) :
    chiB δ hδ y = 1 := by
  apply (chiB δ hδ).one_of_mem_closedBall
  rw [Metric.mem_closedBall, Real.dist_eq]
  change |y - 3 / 2| ≤ 1 / 2 + δ
  rw [abs_le]
  constructor <;> linarith

lemma chiB_zero {δ : ℝ} (hδ : 0 < δ) {y : ℝ} (h : y ≤ 1 - 2 * δ) : chiB δ hδ y = 0 := by
  apply (chiB δ hδ).zero_of_le_dist
  rw [Real.dist_eq]
  change 1 / 2 + 2 * δ ≤ |y - 3 / 2|
  rw [le_abs]
  right
  linarith

lemma chiB_integral_le {δ : ℝ} (hδ : 0 < δ) : ∫ y, chiB δ hδ y ≤ 1 + 4 * δ := by
  have h := (chiB δ hδ).integral_le_measure_closedBall (μ := volume)
  have h2 : (volume : Measure ℝ).real (Metric.closedBall (3 / 2 : ℝ) (chiB δ hδ).rOut) = 1 + 4 * δ := by
    rw [Measure.real, Real.volume_closedBall]
    change (ENNReal.ofReal (2 * (1 / 2 + 2 * δ))).toReal = 1 + 4 * δ
    rw [ENNReal.toReal_ofReal (by linarith)]
    ring
  rw [h2] at h
  exact h

/-! ### The mollified plateau -/

/-- `m = χ ⋆ p` -/
def mfun (χ p : ℝ → ℝ) (x : ℝ) : ℝ := ∫ y, χ y * p (x - y)

lemma mfun_eq (χ p : ℝ → ℝ) (x : ℝ) : mfun χ p x = ∫ z, χ (x - z) * p z := by
  unfold mfun
  have h := integral_sub_left_eq_self (fun y => χ y * p (x - y)) volume x
  rw [← h]
  congr 1
  funext z
  rw [sub_sub_cancel]

section mollified

variable {χ p : ℝ → ℝ} {δ : ℝ}

lemma integrable_chi_mul (hχc : Continuous χ) (hχ0 : ∀ y, 0 ≤ χ y) (hχ1 : ∀ y, χ y ≤ 1)
    (hpi : Integrable p) (x : ℝ) : Integrable (fun z => χ (x - z) * p z) := by
  refine hpi.bdd_mul (c := 1) (Continuous.aestronglyMeasurable (by fun_prop)) ?_
  filter_upwards with z
  rw [Real.norm_eq_abs, abs_of_nonneg (hχ0 _)]
  exact hχ1 _

lemma mfun_nonneg (hχ0 : ∀ y, 0 ≤ χ y) (hp0 : ∀ x, 0 ≤ p x) (x : ℝ) : 0 ≤ mfun χ p x :=
  integral_nonneg fun y => mul_nonneg (hχ0 y) (hp0 _)

lemma mfun_le_one (hχc : Continuous χ) (hχ0 : ∀ y, 0 ≤ χ y) (hχ1 : ∀ y, χ y ≤ 1)
    (hp0 : ∀ x, 0 ≤ p x) (hpi : Integrable p) (hp1 : ∫ x, p x = 1) (x : ℝ) : mfun χ p x ≤ 1 := by
  rw [mfun_eq, ← hp1]
  exact integral_mono (integrable_chi_mul hχc hχ0 hχ1 hpi x) hpi
    (fun z => mul_le_of_le_one_left (hp0 z) (hχ1 _))

lemma mfun_lower (hχc : Continuous χ) (hχ0 : ∀ y, 0 ≤ χ y) (hχ1 : ∀ y, χ y ≤ 1)
    (hχone : ∀ y, 1 - δ ≤ y → y ≤ 2 + δ → χ y = 1)
    (hp0 : ∀ x, 0 ≤ p x) (hpi : Integrable p) (hδ : 0 < δ) {x : ℝ} (hx1 : 1 ≤ x) (hx2 : x ≤ 2) :
    ∫ z in (-δ)..δ, p z ≤ mfun χ p x := by
  rw [mfun_eq, intervalIntegral.integral_of_le (by linarith), ← integral_indicator measurableSet_Ioc]
  refine integral_mono (hpi.indicator measurableSet_Ioc) (integrable_chi_mul hχc hχ0 hχ1 hpi x) ?_
  intro z
  by_cases hz : z ∈ Set.Ioc (-δ) δ
  · rw [Set.indicator_of_mem hz]
    change p z ≤ χ (x - z) * p z
    rw [hχone (x - z) (by linarith [hz.2]) (by linarith [hz.1]), one_mul]
  · rw [Set.indicator_of_notMem hz]
    exact mul_nonneg (hχ0 _) (hp0 _)

lemma mfun_zero_le (hχc : Continuous χ) (hχ0 : ∀ y, 0 ≤ χ y) (hχ1 : ∀ y, χ y ≤ 1)
    (hχzero : ∀ y, y ≤ 1 - 2 * δ → χ y = 0)
    (hp0 : ∀ x, 0 ≤ p x) (hpi : Integrable p) (hp1 : ∫ x, p x = 1) (hδ : 0 < δ) (hδ' : δ ≤ 1 / 4) :
    mfun χ p 0 ≤ 1 - ∫ z in (-δ)..δ, p z := by
  rw [mfun_eq, intervalIntegral.integral_of_le (by linarith), ← integral_indicator measurableSet_Ioc,
    ← hp1, ← integral_sub hpi (hpi.indicator measurableSet_Ioc)]
  refine integral_mono (integrable_chi_mul hχc hχ0 hχ1 hpi 0)
    (hpi.sub (hpi.indicator measurableSet_Ioc)) ?_
  intro z
  change χ (0 - z) * p z ≤ p z - (Set.Ioc (-δ) δ).indicator p z
  by_cases hz : z ∈ Set.Ioc (-δ) δ
  · rw [Set.indicator_of_mem hz, hχzero (0 - z) (by linarith [hz.1]), zero_mul, sub_self]
  · rw [Set.indicator_of_notMem hz, sub_zero]
    exact mul_le_of_le_one_left (hp0 z) (hχ1 _)

lemma mfun_eq_convolution (χ p : ℝ → ℝ) :
    mfun χ p = (χ ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] p) := by
  funext x
  rfl

lemma mfun_integrable (hχi : Integrable χ) (hpi : Integrable p) : Integrable (mfun χ p) := by
  rw [mfun_eq_convolution]
  exact hχi.integrable_convolution (ContinuousLinearMap.mul ℝ ℝ) hpi

lemma mfun_integral (hχi : Integrable χ) (hpi : Integrable p) (hp1 : ∫ x, p x = 1) :
    ∫ x, mfun χ p x = ∫ y, χ y := by
  rw [mfun_eq_convolution, integral_convolution (ContinuousLinearMap.mul ℝ ℝ) hχi hpi, hp1]
  simp

end mollified

/-! ### The square root of the weight -/

/-- For `0 < η ≤ 1` there is a compactly supported Schwartz function `k0` whose paper transform is a
real function `q` with `q(0) = 0`, `q ≥ 1 - 2η` on `[1,2]`, dominated by an integrable `g ≤ 1 + η`
with `∫ g ≤ 1 + 2η`. -/
theorem exists_sqrt_weight {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) :
    ∃ (k0 : 𝓢(ℝ, ℂ)) (q g : ℝ → ℝ) (Λ : ℝ), 0 < Λ ∧ (∀ u, k0 u ≠ 0 → |u| ≤ Λ) ∧
      (∀ x : ℝ, paperFT k0 (x : ℂ) = (q x : ℂ)) ∧ q 0 = 0 ∧
      (∀ x, 1 ≤ x → x ≤ 2 → 1 - 2 * η ≤ q x) ∧
      Integrable g ∧ (∀ x, |q x| ≤ g x) ∧ (∀ x, g x ≤ 1 + η) ∧ ∫ x, g x ≤ 1 + 2 * η := by
  have hδ : (0 : ℝ) < η / 4 := by positivity
  have hδ' : η / 4 ≤ 1 / 4 := by linarith
  obtain ⟨P, p, Λ, hΛ, hPs, hPp, hp0, hple, hp0pos, hpi, hpc, hp1, ht1, ht2⟩ :=
    exists_mollifier hδ hη
  -- the plateau
  set χ : ℝ → ℝ := fun y => chiB (η / 4) hδ y with hχdef
  have hχc : Continuous χ := (chiB (η / 4) hδ).continuous
  have hχ0 : ∀ y, 0 ≤ χ y := fun y => (chiB (η / 4) hδ).nonneg
  have hχ1 : ∀ y, χ y ≤ 1 := fun y => (chiB (η / 4) hδ).le_one
  have hχone : ∀ y, 1 - η / 4 ≤ y → y ≤ 2 + η / 4 → χ y = 1 := fun y h1 h2 => chiB_one hδ h1 h2
  have hχzero : ∀ y, y ≤ 1 - 2 * (η / 4) → χ y = 0 := fun y h => chiB_zero hδ h
  have hχi : Integrable χ := (chiB (η / 4) hδ).integrable
  have hχint : ∫ y, χ y ≤ 1 + 4 * (η / 4) := chiB_integral_le hδ
  -- the mollified plateau and its inverse transform
  set m : ℝ → ℝ := mfun χ p with hmdef
  set km : 𝓢(ℝ, ℂ) := SchwartzMap.pairing (ContinuousLinearMap.mul ℂ ℂ) P
    (sScale (-1) (by norm_num) (PF (bumpS (chiB (η / 4) hδ)))) with hkmdef
  have hkm_apply : ∀ u : ℝ, km u = P u * paperFT (bumpS (chiB (η / 4) hδ)) ((u * (-1) : ℝ) : ℂ) := by
    intro u
    rw [hkmdef, SchwartzMap.pairing_apply_apply, ContinuousLinearMap.mul_apply', sScale_apply,
      PF_apply]
  have hkm : ∀ x : ℝ, paperFT km (x : ℂ) = (m x : ℂ) := by
    intro x
    have hfun : (km : ℝ → ℂ)
        = fun u : ℝ => P u * paperFT (bumpS (chiB (η / 4) hδ)) ((u * (-1) : ℝ) : ℂ) :=
      funext hkm_apply
    rw [hfun, paperFT_mul_check, hmdef]
    unfold mfun
    rw [← integral_complex_ofReal]
    congr 1
    funext y
    rw [hPp, bumpS_apply]
    push_cast
    rfl
  -- basic estimates
  have hm0 : ∀ x, 0 ≤ m x := mfun_nonneg hχ0 hp0
  have hm1 : ∀ x, m x ≤ 1 := mfun_le_one hχc hχ0 hχ1 hp0 hpi hp1
  have hmlow : ∀ x, 1 ≤ x → x ≤ 2 → ∫ z in (-(η / 4))..(η / 4), p z ≤ m x :=
    fun x hx1 hx2 => mfun_lower hχc hχ0 hχ1 hχone hp0 hpi hδ hx1 hx2
  have hmzero : m 0 ≤ 1 - ∫ z in (-(η / 4))..(η / 4), p z :=
    mfun_zero_le hχc hχ0 hχ1 hχzero hp0 hpi hp1 hδ hδ'
  have hmi : Integrable m := mfun_integrable hχi hpi
  have hmint : ∫ x, m x = ∫ y, χ y := mfun_integral hχi hpi hp1
  -- the correction
  set c1 : ℝ := m 0 / p 0 with hc1def
  have hc1nn : 0 ≤ c1 := div_nonneg (hm0 0) hp0pos.le
  have hc1p : c1 * p 0 = m 0 := div_mul_cancel₀ _ hp0pos.ne'
  have hc1η : c1 ≤ η := by
    rw [hc1def, div_le_iff₀ hp0pos]
    linarith
  have hm0η : m 0 ≤ η := by linarith
  have hcp : ∀ x, c1 * p x ≤ m 0 := by
    intro x
    rw [← hc1p]
    exact mul_le_mul_of_nonneg_left (hple x) hc1nn
  have hcp0 : ∀ x, 0 ≤ c1 * p x := fun x => mul_nonneg hc1nn (hp0 x)
  refine ⟨km - (c1 : ℂ) • P, fun x => m x - c1 * p x, fun x => m x + c1 * p x, Λ, hΛ, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_⟩
  · intro u hu
    apply hPs
    intro h
    apply hu
    rw [ssub_apply, ssmul_apply, hkm_apply, h, zero_mul, mul_zero, sub_zero]
  · intro x
    rw [paperFT_sub, paperFT_smul, hkm, hPp]
    push_cast
    ring
  · change m 0 - c1 * p 0 = 0
    rw [hc1p, sub_self]
  · intro x hx1 hx2
    have h1 := hmlow x hx1 hx2
    have h2 := hcp x
    change 1 - 2 * η ≤ m x - c1 * p x
    linarith
  · exact hmi.add (hpi.const_mul c1)
  · intro x
    change |m x - c1 * p x| ≤ m x + c1 * p x
    rw [abs_le]
    constructor <;> linarith [hm0 x, hcp0 x]
  · intro x
    change m x + c1 * p x ≤ 1 + η
    linarith [hm1 x, hcp x]
  · have h1 : ∫ x, (m x + c1 * p x) = (∫ x, m x) + c1 * ∫ x, p x := by
      rw [integral_add hmi (hpi.const_mul c1), integral_const_mul]
    rw [h1, hmint, hp1]
    linarith

end WeightAux
end TMA
end
end Src_TMA_WeightAux4

section Src_TMA_Weight
/-
Written for Kristian Muri Knausgård, drafted with Claude (Anthropic), 22 November 2026.

TMA/Weight.lean — existence of height weights approximating the indicator of [1,2] from above.
See BLUEPRINT.md, module "Weight".  The construction is in the auxiliary files
`TMA/WeightAux1.lean` (paper transform on Schwartz functions: convolution, inversion, Plancherel),
`TMA/WeightAuxGamma.lean` (the decay bound for the transform of `h · ω_T`),
`TMA/WeightAux2.lean` (assembly: `k = k0 ⋆ k0`, `h = q²`),
`TMA/WeightAux3.lean` (the nonnegative mollifier), `TMA/WeightAux4.lean` (the square root `q`).
-/

open MeasureTheory Complex Filter Topology
open scoped BigOperators Real

noncomputable section
namespace TMA

private lemma HeightWeight.k_integrable (w : HeightWeight) : Integrable w.k :=
  w.k_contDiff.continuous.integrable_of_hasCompactSupport
    (Zeta23.hasCompactSupport_of_support_subset_abs w.k_supp)

/-- `h` is bounded by `∫ ‖k‖`. -/
private lemma HeightWeight.h_le (w : HeightWeight) (x : ℝ) : w.h x ≤ ∫ u, ‖w.k u‖ := by
  have h1 := Zeta23.norm_paperFT_le w.k_integrable w.k_supp (x : ℂ)
  rw [w.h_eq, Complex.norm_real, Real.norm_eq_abs] at h1
  have h2 : Real.exp (|(x : ℂ).im| * w.kappa) = 1 := by simp
  rw [h2, one_mul] at h1
  exact (le_abs_self _).trans h1

private lemma HeightWeight.h_sq_integrable (w : HeightWeight) : Integrable (fun x => w.h x ^ 2) := by
  refine Integrable.mono' (w.h_int.const_mul (∫ u, ‖w.k u‖))
    (w.h_cont.pow 2).aestronglyMeasurable ?_
  filter_upwards with x
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), pow_two]
  exact mul_le_mul_of_nonneg_right (w.h_le x) (w.h_nonneg x)

/-- `∫ h² ≥ 1`, because `h ≥ 1` on `[1,2]` and `h ≥ 0`. -/
theorem HeightWeight.one_le_kap2 (w : HeightWeight) : 1 ≤ w.kap2 := by
  unfold HeightWeight.kap2
  have h1 : ∫ x, (Set.Icc (1 : ℝ) 2).indicator (fun _ => (1 : ℝ)) x = 1 := by
    rw [integral_indicator measurableSet_Icc, setIntegral_const, smul_eq_mul, mul_one,
      Measure.real, Real.volume_Icc, ENNReal.toReal_ofReal (by norm_num)]
    norm_num
  rw [← h1]
  refine integral_mono ?_ w.h_sq_integrable ?_
  · exact (integrable_indicator_iff measurableSet_Icc).mpr continuous_const.integrableOn_Icc
  · intro x
    by_cases hx : x ∈ Set.Icc (1 : ℝ) 2
    · rw [Set.indicator_of_mem hx]
      have := w.h_ge_one x hx.1 hx.2
      change (1 : ℝ) ≤ w.h x ^ 2
      nlinarith
    · rw [Set.indicator_of_notMem hx]
      exact sq_nonneg _

theorem HeightWeight.kap1_nonneg (w : HeightWeight) : 0 ≤ w.kap1 :=
  integral_nonneg w.h_nonneg

theorem HeightWeight.kap3_nonneg (w : HeightWeight) : 0 ≤ w.kap3 :=
  integral_nonneg fun x => pow_nonneg (w.h_nonneg x) 3

/-- For every `ε > 0` there is a height weight with `∫ h ≤ 1 + ε` and `∫ h³ ≤ 1 + ε`. -/
theorem exists_heightWeight {ε : ℝ} (hε : 0 < ε) :
    ∃ w : HeightWeight, w.kap1 ≤ 1 + ε ∧ w.kap3 ≤ 1 + ε := by
  -- the small parameter
  obtain ⟨η, hη0, hη1, hηε⟩ :
      ∃ η : ℝ, 0 < η ∧ η < 1 / 4 ∧ ((1 + 2 * η) / (1 - 2 * η)) ^ 6 ≤ 1 + ε := by
    have hcont : ContinuousAt (fun η : ℝ => ((1 + 2 * η) / (1 - 2 * η)) ^ 6) 0 :=
      ContinuousAt.pow (ContinuousAt.div (by fun_prop) (by fun_prop) (by norm_num)) 6
    have h1 : ∀ᶠ η in 𝓝 (0 : ℝ), ((1 + 2 * η) / (1 - 2 * η)) ^ 6 < 1 + ε :=
      hcont.eventually (gt_mem_nhds (by norm_num; exact hε))
    have h2 : ∀ᶠ η in 𝓝[>] (0 : ℝ), η ∈ Set.Ioo (0 : ℝ) (1 / 4) :=
      Ioo_mem_nhdsGT (by norm_num)
    obtain ⟨η, hη, hη'⟩ := ((h1.filter_mono nhdsWithin_le_nhds).and h2).exists
    exact ⟨η, hη'.1, hη'.2, hη.le⟩
  obtain ⟨k0, q, g, Λ, hΛ, hsupp, hq, hq0, hq1, hgi, hqg, hg1, hgint⟩ :=
    WeightAux.exists_sqrt_weight hη0 (by linarith)
  -- normalisation
  have ha : 0 < 1 - 2 * η := by linarith
  set b : ℝ := (1 - 2 * η)⁻¹ with hbdef
  have hb1 : 1 ≤ b := by
    rw [hbdef]
    exact (one_le_inv₀ ha).mpr (by linarith)
  have hb0 : 0 < b := by linarith
  obtain ⟨w, hw⟩ := WeightAux.exists_heightWeight_of_sqrt ((b : ℂ) • k0) (fun x => b * q x) Λ hΛ
    (by
      intro u hu
      apply hsupp
      intro h
      apply hu
      rw [WeightAux.ssmul_apply, h, mul_zero])
    (by
      intro x
      rw [WeightAux.paperFT_smul, hq]
      push_cast
      ring)
    (by
      rw [hq0, mul_zero])
    (by
      intro x hx1 hx2
      have h1 := hq1 x hx1 hx2
      change 1 ≤ b * q x
      rw [hbdef, ← div_eq_inv_mul, le_div_iff₀ ha]
      linarith)
  -- pointwise bounds
  have hg0 : ∀ x, 0 ≤ g x := fun x => (abs_nonneg _).trans (hqg x)
  have hqsq : ∀ x, q x ^ 2 ≤ g x ^ 2 := by
    intro x
    rw [← sq_abs (q x)]
    exact pow_le_pow_left₀ (abs_nonneg _) (hqg x) 2
  set t : ℝ := 1 + 2 * η with htdef
  set s : ℝ := 1 + η with hsdef
  have hs1 : 1 ≤ s := by linarith
  have hst : s ≤ t := by linarith
  have ht1 : 1 ≤ t := by linarith
  have hρ : (t * b) ^ 6 ≤ 1 + ε := by
    have : t * b = (1 + 2 * η) / (1 - 2 * η) := by
      rw [htdef, hbdef, div_eq_mul_inv]
    rw [this]
    exact hηε
  have hgint' : ∫ x, g x ≤ t := hgint
  have hg1' : ∀ x, g x ≤ s := hg1
  refine ⟨w, ?_, ?_⟩
  · -- `∫ h ≤ b² s t ≤ (t b)⁶`
    unfold HeightWeight.kap1
    rw [hw]
    have hpt : ∀ x, (b * q x) ^ 2 ≤ b ^ 2 * s * g x := by
      intro x
      have h1 : g x ^ 2 ≤ s * g x := by
        rw [pow_two]
        exact mul_le_mul_of_nonneg_right (hg1' x) (hg0 x)
      calc (b * q x) ^ 2 = b ^ 2 * q x ^ 2 := by ring
        _ ≤ b ^ 2 * (s * g x) := mul_le_mul_of_nonneg_left ((hqsq x).trans h1) (by positivity)
        _ = b ^ 2 * s * g x := by ring
    have h1 : ∫ x, (b * q x) ^ 2 ≤ ∫ x, b ^ 2 * s * g x :=
      integral_mono_of_nonneg (Eventually.of_forall fun x => sq_nonneg _) (hgi.const_mul _)
        (Eventually.of_forall hpt)
    rw [integral_const_mul] at h1
    have h2 : b ^ 2 * s * ∫ x, g x ≤ b ^ 2 * s * t :=
      mul_le_mul_of_nonneg_left hgint' (by positivity)
    have h3 : b ^ 2 * s * t ≤ (t * b) ^ 6 := by
      have e1 : b ^ 2 ≤ b ^ 6 := pow_le_pow_right₀ hb1 (by norm_num)
      have e2 : s * t ≤ t ^ 6 := by
        calc s * t ≤ t * t := mul_le_mul_of_nonneg_right hst (by linarith)
          _ = t ^ 2 := by ring
          _ ≤ t ^ 6 := pow_le_pow_right₀ ht1 (by norm_num)
      calc b ^ 2 * s * t = b ^ 2 * (s * t) := by ring
        _ ≤ b ^ 6 * t ^ 6 := mul_le_mul e1 e2 (by positivity) (by positivity)
        _ = (t * b) ^ 6 := by ring
    linarith
  · -- `∫ h³ ≤ b⁶ s⁵ t ≤ (t b)⁶`
    unfold HeightWeight.kap3
    rw [hw]
    have hpt : ∀ x, ((b * q x) ^ 2) ^ 3 ≤ b ^ 6 * s ^ 5 * g x := by
      intro x
      have h1 : (q x ^ 2) ^ 3 ≤ (g x ^ 2) ^ 3 := pow_le_pow_left₀ (sq_nonneg _) (hqsq x) 3
      have h2 : g x ^ 5 ≤ s ^ 5 := pow_le_pow_left₀ (hg0 x) (hg1' x) 5
      calc ((b * q x) ^ 2) ^ 3 = b ^ 6 * (q x ^ 2) ^ 3 := by ring
        _ ≤ b ^ 6 * (g x ^ 2) ^ 3 := mul_le_mul_of_nonneg_left h1 (by positivity)
        _ = b ^ 6 * (g x ^ 5 * g x) := by ring
        _ ≤ b ^ 6 * (s ^ 5 * g x) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h2 (hg0 x)) (by positivity)
        _ = b ^ 6 * s ^ 5 * g x := by ring
    have h1 : ∫ x, ((b * q x) ^ 2) ^ 3 ≤ ∫ x, b ^ 6 * s ^ 5 * g x :=
      integral_mono_of_nonneg (Eventually.of_forall fun x => by positivity) (hgi.const_mul _)
        (Eventually.of_forall hpt)
    rw [integral_const_mul] at h1
    have h2 : b ^ 6 * s ^ 5 * ∫ x, g x ≤ b ^ 6 * s ^ 5 * t :=
      mul_le_mul_of_nonneg_left hgint' (by positivity)
    have h3 : b ^ 6 * s ^ 5 * t ≤ (t * b) ^ 6 := by
      have e2 : s ^ 5 * t ≤ t ^ 6 := by
        calc s ^ 5 * t ≤ t ^ 5 * t :=
              mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by linarith) hst 5) (by linarith)
          _ = t ^ 6 := by ring
      calc b ^ 6 * s ^ 5 * t = b ^ 6 * (s ^ 5 * t) := by ring
        _ ≤ b ^ 6 * t ^ 6 := mul_le_mul_of_nonneg_left e2 (by positivity)
        _ = (t * b) ^ 6 := by ring
    linarith

end TMA

end
end Src_TMA_Weight

section Src_TMA_Traces
/-
Written for Kristian Muri Knausgård, drafted with Claude (Anthropic), 22 November 2026.

TMA/Traces.lean — the first and the second trace: upper bound for the first, lower bound for the second.
STATUS: `t1_upper` and `t2_lower` are proved from the interface statements of `TMA/Window.lean`,
`TMA/PrimeSum.lean`, `TMA/Kernel.lean`, `TMA/Packets.lean` (no `sorry` in this file).
See BLUEPRINT.md, module "T1T2".  The helper lemmas live in the namespace `TMA.T12`.

Outline of `t2_lower`.  Write `E = Kfull - K0`.
1. `t2 Kfull ≥ (1 - 1/L) t2 K0 - L (10/9) ∫_{-1}^{1} ‖E‖²`  (`T12.t2_perturb`), `L = log T`.
2. For `T` large the packets of `K0` have disjoint supports (`T12.K0_norm_sq`), so `t2 K0` is a sum of
   masses of single packets (`T12.t2_K0_eq`).
3. The mass of the packet with centre `lam` is `(T²/A) ∫ ag(lam - y/A) ‖k y‖² dy` (`T12.Ipk_eq`), between
   `(T²/A)(ag lam - 5κ/A) κ₂/2π` and `(T²/A)(10/9) κ₂/2π`  (`T12.Ipk_ge`, `T12.Ipk_le`).
4. Sum over the integers with `primeSum_asymp` and `primeSum_upper`:
   `D C₂(σ) κ₂ - C T ≤ t2 K0 ≤ C T L`  (`T12.t2_K0_ge`, `T12.t2_K0_le`).
-/

open MeasureTheory Complex
open scoped BigOperators ArithmeticFunction Real

noncomputable section
namespace TMA

namespace T12

/-! ### elementary lemmas -/

/-- If at most one term of a finite sum of complex numbers is nonzero, then the squared norm of the
sum is the sum of the squared norms. -/
theorem sq_norm_sum_of_disjoint {ι : Type*} (s : Finset ι) (f : ι → ℂ)
    (h : ∀ i ∈ s, ∀ j ∈ s, f i ≠ 0 → f j ≠ 0 → i = j) :
    ‖∑ i ∈ s, f i‖ ^ 2 = ∑ i ∈ s, ‖f i‖ ^ 2 := by
  classical
  by_cases h0 : ∃ i ∈ s, f i ≠ 0
  · obtain ⟨i0, hi0, hne⟩ := h0
    have h1 : ∀ j ∈ s, j ≠ i0 → f j = 0 := by
      intro j hj hji
      by_contra hfj
      exact hji (h j hj i0 hi0 hfj hne)
    rw [Finset.sum_eq_single i0 h1 (fun hni => absurd hi0 hni),
      Finset.sum_eq_single i0
        (fun j hj hji => by rw [h1 j hj hji, norm_zero, zero_pow two_ne_zero])
        (fun hni => absurd hi0 hni)]
  · have h0' : ∀ i ∈ s, f i = 0 := fun i hi => by
      by_contra hfi
      exact h0 ⟨i, hi, hfi⟩
    rw [Finset.sum_eq_zero h0',
      Finset.sum_eq_zero (fun i hi => by rw [h0' i hi, norm_zero, zero_pow two_ne_zero]),
      norm_zero, zero_pow two_ne_zero]

/-- `‖a + e‖² ≥ (1 - 1/L) ‖a‖² - L ‖e‖²` -/
theorem norm_add_sq_ge (a e : ℂ) {L : ℝ} (hL : 0 < L) :
    ‖a‖ ^ 2 - (1 / L) * ‖a‖ ^ 2 - L * ‖e‖ ^ 2 ≤ ‖a + e‖ ^ 2 := by
  have h1 := norm_add_sq_real a e
  have h2 := abs_real_inner_le_norm a e
  have h3 : -(‖a‖ * ‖e‖) ≤ inner ℝ a e := by
    have := neg_abs_le (inner ℝ a e)
    linarith
  have h4 : 2 * (‖a‖ * ‖e‖) ≤ (1 / L) * ‖a‖ ^ 2 + L * ‖e‖ ^ 2 := by
    have h5 : 0 ≤ (‖a‖ - L * ‖e‖) ^ 2 / L := by positivity
    have h6 : (‖a‖ - L * ‖e‖) ^ 2 / L
        = (1 / L) * ‖a‖ ^ 2 - 2 * (‖a‖ * ‖e‖) + L * ‖e‖ ^ 2 := by
      field_simp
      ring
    linarith
  rw [h1]
  linarith [sq_nonneg ‖e‖]

/-- since `ag` vanishes outside `[-1,1]`, integrals against `ag` over `[-1,1]` are integrals over `ℝ` -/
theorem integral_ag_mul (f : ℝ → ℝ) :
    ∫ x in (-1 : ℝ)..1, ag x * f x = ∫ x, ag x * f x := by
  rw [intervalIntegral.integral_of_le (by norm_num), ← integral_Icc_eq_integral_Ioc]
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro x hx
  have hx1 : 1 < |x| := lt_of_not_ge fun hcon =>
    hx ⟨by linarith [neg_abs_le x], by linarith [le_abs_self x]⟩
  rw [ag_eq_zero hx1, zero_mul]

/-! ### a single packet -/

theorem norm_packet_sq (k : ℝ → ℂ) (T σ lam x : ℝ) :
    ‖packet k T σ lam x‖ ^ 2 = T ^ 2 * ‖k (-(Asc T σ * (x - lam)))‖ ^ 2 := by
  unfold packet
  rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]

theorem continuous_packet (w : HeightWeight) (T σ lam : ℝ) :
    Continuous (packet w.k T σ lam) := by
  show Continuous (fun x : ℝ => (T : ℂ) * w.k (-(Asc T σ * (x - lam))))
  exact continuous_const.mul (w.continuous_k.comp (by fun_prop))

theorem continuous_ag_mul_packet (w : HeightWeight) (T σ lam : ℝ) :
    Continuous (fun x : ℝ => ag x * ‖packet w.k T σ lam x‖ ^ 2) :=
  continuous_ag.mul ((continuous_packet w T σ lam).norm.pow 2)

/-- the weighted `L²` mass of one packet -/
def Ipk (w : HeightWeight) (T σ lam : ℝ) : ℝ :=
  ∫ x in (-1 : ℝ)..1, ag x * ‖packet w.k T σ lam x‖ ^ 2

theorem Ipk_nonneg (w : HeightWeight) (T σ lam : ℝ) : 0 ≤ Ipk w T σ lam := by
  apply intervalIntegral.integral_nonneg (by norm_num)
  intro x _
  exact mul_nonneg (ag_nonneg x) (sq_nonneg _)

theorem integrable_k_sq (w : HeightWeight) : Integrable (fun y : ℝ => ‖w.k y‖ ^ 2) := by
  obtain ⟨M, hM0, hM⟩ := w.exists_k_bound
  refine Integrable.mono' (w.integrable_k.norm.const_mul M)
    (w.continuous_k.norm.pow 2).aestronglyMeasurable (Filter.Eventually.of_forall fun y => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), sq]
  exact mul_le_mul_of_nonneg_right (hM y) (norm_nonneg _)

theorem integrable_ag_mul_k_sq (w : HeightWeight) (lam A : ℝ) :
    Integrable (fun y : ℝ => ag (lam - y / A) * ‖w.k y‖ ^ 2) := by
  refine Integrable.bdd_mul (c := 10 / 9) (integrable_k_sq w)
    (continuous_ag.comp (by fun_prop)).aestronglyMeasurable (Filter.Eventually.of_forall fun y => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (ag_nonneg _)]
  exact ag_le _

/-- substitution `y = -(A (x - lam))` in the mass of a packet -/
theorem Ipk_eq (w : HeightWeight) {T σ : ℝ} (hA : 0 < Asc T σ) (lam : ℝ) :
    Ipk w T σ lam = T ^ 2 / Asc T σ * ∫ y, ag (lam - y / Asc T σ) * ‖w.k y‖ ^ 2 := by
  unfold Ipk
  rw [integral_ag_mul]
  have h1 : ∀ x : ℝ, ag x * ‖packet w.k T σ lam x‖ ^ 2
      = T ^ 2 * (fun x : ℝ => (fun y : ℝ => ag (lam - y / Asc T σ) * ‖w.k y‖ ^ 2)
          (-(Asc T σ) * x)) (x - lam) := by
    intro x
    rw [norm_packet_sq]
    have h2 : lam - -(Asc T σ * (x - lam)) / Asc T σ = x := by
      field_simp
      ring
    have h3 : -(Asc T σ) * (x - lam) = -(Asc T σ * (x - lam)) := by ring
    show ag x * (T ^ 2 * ‖w.k (-(Asc T σ * (x - lam)))‖ ^ 2)
      = T ^ 2 * (ag (lam - -(Asc T σ) * (x - lam) / Asc T σ) * ‖w.k (-(Asc T σ) * (x - lam))‖ ^ 2)
    rw [h3, h2]
    ring
  simp_rw [h1]
  rw [integral_const_mul,
    integral_sub_right_eq_self (fun x : ℝ => (fun y : ℝ => ag (lam - y / Asc T σ) * ‖w.k y‖ ^ 2)
          (-(Asc T σ) * x)) lam,
    Measure.integral_comp_mul_left (fun y : ℝ => ag (lam - y / Asc T σ) * ‖w.k y‖ ^ 2) (-(Asc T σ))]
  rw [smul_eq_mul, abs_inv, abs_neg, abs_of_pos hA]
  field_simp

/-- `∫ ‖k‖² = κ₂ / 2π ≥ 0` -/
theorem kQ_eq (w : HeightWeight) : ∫ y, ‖w.k y‖ ^ 2 = w.kap2 / (2 * π) := by
  rw [w.inv2]
  unfold HeightWeight.kap2
  ring

theorem kap2_nonneg (w : HeightWeight) : 0 ≤ w.kap2 := by
  unfold HeightWeight.kap2
  exact integral_nonneg fun x => sq_nonneg (w.h x)

theorem Ipk_le (w : HeightWeight) {T σ : ℝ} (hA : 0 < Asc T σ) (lam : ℝ) :
    Ipk w T σ lam ≤ T ^ 2 / Asc T σ * (10 / 9 * (w.kap2 / (2 * π))) := by
  rw [Ipk_eq w hA, ← kQ_eq w]
  refine mul_le_mul_of_nonneg_left ?_ (div_nonneg (sq_nonneg T) hA.le)
  rw [← integral_const_mul]
  refine integral_mono (integrable_ag_mul_k_sq w lam _) ((integrable_k_sq w).const_mul _) fun y => ?_
  exact mul_le_mul_of_nonneg_right (ag_le _) (sq_nonneg _)

theorem Ipk_ge (w : HeightWeight) {T σ : ℝ} (hA : 0 < Asc T σ) (lam : ℝ) :
    T ^ 2 / Asc T σ * ((ag lam - 5 * w.kappa / Asc T σ) * (w.kap2 / (2 * π))) ≤ Ipk w T σ lam := by
  rw [Ipk_eq w hA, ← kQ_eq w]
  refine mul_le_mul_of_nonneg_left ?_ (div_nonneg (sq_nonneg T) hA.le)
  rw [← integral_const_mul]
  refine integral_mono ((integrable_k_sq w).const_mul _) (integrable_ag_mul_k_sq w lam _) fun y => ?_
  show (ag lam - 5 * w.kappa / Asc T σ) * ‖w.k y‖ ^ 2 ≤ ag (lam - y / Asc T σ) * ‖w.k y‖ ^ 2
  by_cases hy : w.k y = 0
  · rw [hy, norm_zero, zero_pow two_ne_zero, mul_zero, mul_zero]
  · refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
    have hyk : |y| ≤ w.kappa := w.k_supp y hy
    have hlip := ag_lipschitz lam (lam - y / Asc T σ)
    have h1 : lam - (lam - y / Asc T σ) = y / Asc T σ := by ring
    rw [h1, abs_div, abs_of_pos hA] at hlip
    have h2 : 5 * (|y| / Asc T σ) ≤ 5 * w.kappa / Asc T σ := by
      rw [mul_div_assoc]
      exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hyk hA.le) (by norm_num)
    have h3 := le_abs_self (ag lam - ag (lam - y / Asc T σ))
    linarith


/-! ### separation of the centres -/

/-- the facts about large `T` (from `separation`) used for the second trace -/
structure Sep (w : HeightWeight) (T σ : ℝ) : Prop where
  hT : 2 ≤ T
  hA : 0 < Asc T σ
  hκ : 3 * w.kappa / T < Real.log 2
  hlog : ∀ n n' : ℕ, 1 ≤ n → 1 ≤ n' → (n : ℝ) ≤ 4 * T ^ σ → (n' : ℝ) ≤ 4 * T ^ σ → n ≠ n' →
    3 * w.kappa / T < |Real.log n - Real.log n'|

theorem packet_ne_zero (w : HeightWeight) {T σ lam x : ℝ} (hA : 0 < Asc T σ)
    (h : packet w.k T σ lam x ≠ 0) : |x - lam| ≤ w.kappa / Asc T σ := by
  by_contra hcon
  exact h (packet_eq_zero w hA (not_le.mp hcon))

theorem three_kappa_div_Asc (w : HeightWeight) (T σ : ℝ) :
    3 * w.kappa / Asc T σ = 3 * w.kappa / T / (σ * Real.log T) := by
  unfold Asc
  rw [div_div]

theorem lamOf_nonneg (T σ : ℝ) (hσ : 0 < σ) (hT : 2 ≤ T) (n : ℕ) : 0 ≤ lamOf T σ n := by
  unfold lamOf
  exact div_nonneg (Real.log_natCast_nonneg n) (mul_pos hσ (Real.log_pos (by linarith))).le

theorem lamOf_gt (w : HeightWeight) {T σ : ℝ} (hσ : 0 < σ) (hs : Sep w T σ) {n : ℕ} (hn : 2 ≤ n) :
    3 * w.kappa / Asc T σ < lamOf T σ n := by
  have hσL : 0 < σ * Real.log T := mul_pos hσ (Real.log_pos (by linarith [hs.hT]))
  rw [three_kappa_div_Asc]
  unfold lamOf
  refine div_lt_div_of_pos_right (lt_of_lt_of_le hs.hκ ?_) hσL
  exact Real.log_le_log (by norm_num) (by exact_mod_cast hn)

theorem lamOf_sep (w : HeightWeight) {T σ : ℝ} (hσ : 0 < σ) (hs : Sep w T σ) {n n' : ℕ}
    (hn : 1 ≤ n) (hn' : 1 ≤ n') (hnT : (n : ℝ) ≤ 4 * T ^ σ) (hnT' : (n' : ℝ) ≤ 4 * T ^ σ)
    (hne : n ≠ n') : 3 * w.kappa / Asc T σ < |lamOf T σ n - lamOf T σ n'| := by
  have hσL : 0 < σ * Real.log T := mul_pos hσ (Real.log_pos (by linarith [hs.hT]))
  rw [three_kappa_div_Asc]
  unfold lamOf
  rw [← sub_div, abs_div, abs_of_pos hσL]
  exact div_lt_div_of_pos_right (hs.hlog n n' hn hn' hnT hnT' hne) hσL

theorem mem_Icc_Nmax {T σ : ℝ} (hT : 2 ≤ T) {n : ℕ} (hn : n ∈ Finset.Icc 2 (Nmax T σ)) :
    2 ≤ n ∧ (n : ℝ) ≤ 2 * T ^ σ := by
  rw [Finset.mem_Icc] at hn
  have h0 : 0 ≤ 2 * T ^ σ := by
    have := Real.rpow_nonneg (show (0 : ℝ) ≤ T by linarith) σ
    linarith
  refine ⟨hn.1, le_trans ?_ (Nat.floor_le h0)⟩
  exact_mod_cast hn.2

theorem norm_real_mul_sq (c : ℝ) (z : ℂ) : ‖(c : ℂ) * z‖ ^ 2 = c ^ 2 * ‖z‖ ^ 2 := by
  rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]

/-- **Disjoint supports.** For `T` large the packets of `K0` have pairwise disjoint supports, so the
squared modulus of `K0` is the sum of the squared moduli of its terms. -/
theorem K0_norm_sq (w : HeightWeight) {T σ : ℝ} (hσ : 0 < σ) (hs : Sep w T σ) (x : ℝ) :
    ‖K0 w.k T σ x‖ ^ 2 = Real.log (T / (2 * π)) ^ 2 * ‖packet w.k T σ 0 x‖ ^ 2
      + ∑ n ∈ Finset.Icc 2 (Nmax T σ), lamCoeff n ^ 2 *
          (‖packet w.k T σ (lamOf T σ n) x‖ ^ 2 + ‖packet w.k T σ (-(lamOf T σ n)) x‖ ^ 2) := by
  have hκA : 0 < w.kappa / Asc T σ := div_pos w.kappa_pos hs.hA
  have h3κ : 3 * w.kappa / Asc T σ = 3 * (w.kappa / Asc T σ) := by ring
  -- the two packets of the integer `n`
  set g : ℕ → ℂ := fun n =>
    (lamCoeff n : ℂ) * (packet w.k T σ (lamOf T σ n) x + packet w.k T σ (-(lamOf T σ n)) x) with hg
  -- if a packet of `n` is nonzero at `x`, then `|x|` is close to `lamOf n`
  have hi : ∀ n, g n ≠ 0 → |(|x|) - lamOf T σ n| ≤ w.kappa / Asc T σ := by
    intro n hgn
    have hlam0 : 0 ≤ lamOf T σ n := lamOf_nonneg T σ hσ hs.hT n
    by_cases hp : packet w.k T σ (lamOf T σ n) x = 0
    · have hm : packet w.k T σ (-(lamOf T σ n)) x ≠ 0 := by
        intro hm
        apply hgn
        simp only [hg, hp, hm, add_zero, mul_zero]
      have hpm := packet_ne_zero w hs.hA hm
      have habs := abs_abs_sub_abs_le_abs_sub x (-(lamOf T σ n))
      rw [abs_neg, abs_of_nonneg hlam0] at habs
      exact habs.trans hpm
    · have hpp := packet_ne_zero w hs.hA hp
      have habs := abs_abs_sub_abs_le_abs_sub x (lamOf T σ n)
      rw [abs_of_nonneg hlam0] at habs
      exact habs.trans hpp
  -- at most one integer has a nonzero packet at `x`
  have hii : ∀ n ∈ Finset.Icc 2 (Nmax T σ), ∀ n' ∈ Finset.Icc 2 (Nmax T σ),
      g n ≠ 0 → g n' ≠ 0 → n = n' := by
    intro n hn n' hn' hgn hgn'
    by_contra hne
    obtain ⟨hn2, hnT⟩ := mem_Icc_Nmax hs.hT hn
    obtain ⟨hn2', hnT'⟩ := mem_Icc_Nmax hs.hT hn'
    have hTσ : 0 ≤ T ^ σ := Real.rpow_nonneg (by linarith [hs.hT]) σ
    have h1 := lamOf_sep w hσ hs (n := n) (n' := n') (by omega) (by omega) (by linarith)
      (by linarith) hne
    obtain ⟨a1, a2⟩ := abs_le.mp (hi n hgn)
    obtain ⟨b1, b2⟩ := abs_le.mp (hi n' hgn')
    rw [h3κ] at h1
    rcases lt_abs.mp h1 with h | h <;> linarith
  -- the packet at `0` and the packets of the integers do not meet
  have hiii : ∀ n ∈ Finset.Icc 2 (Nmax T σ), packet w.k T σ 0 x ≠ 0 → g n = 0 := by
    intro n hn hp0
    by_contra hgn
    have h0 := packet_ne_zero w hs.hA hp0
    rw [sub_zero] at h0
    obtain ⟨a1, a2⟩ := abs_le.mp (hi n hgn)
    have h1 := lamOf_gt w hσ hs (mem_Icc_Nmax hs.hT hn).1
    rw [h3κ] at h1
    linarith
  -- the two packets of one integer do not meet
  have hiv : ∀ n ∈ Finset.Icc 2 (Nmax T σ), ‖g n‖ ^ 2 = lamCoeff n ^ 2 *
      (‖packet w.k T σ (lamOf T σ n) x‖ ^ 2 + ‖packet w.k T σ (-(lamOf T σ n)) x‖ ^ 2) := by
    intro n hn
    simp only [hg]
    rw [norm_real_mul_sq]
    congr 1
    by_cases hp : packet w.k T σ (lamOf T σ n) x = 0
    · rw [hp, zero_add, norm_zero, zero_pow two_ne_zero, zero_add]
    · have hm : packet w.k T σ (-(lamOf T σ n)) x = 0 := by
        by_contra hm
        obtain ⟨a1, a2⟩ := abs_le.mp (packet_ne_zero w hs.hA hp)
        obtain ⟨b1, b2⟩ := abs_le.mp (packet_ne_zero w hs.hA hm)
        have h1 := lamOf_gt w hσ hs (mem_Icc_Nmax hs.hT hn).1
        rw [h3κ] at h1
        linarith
      rw [hm, add_zero, norm_zero, zero_pow two_ne_zero, add_zero]
  -- assembly
  have hK : K0 w.k T σ x = (Real.log (T / (2 * π)) : ℂ) * packet w.k T σ 0 x
      - ∑ n ∈ Finset.Icc 2 (Nmax T σ), g n := rfl
  have hS : ‖∑ n ∈ Finset.Icc 2 (Nmax T σ), g n‖ ^ 2 = ∑ n ∈ Finset.Icc 2 (Nmax T σ), lamCoeff n ^ 2 *
      (‖packet w.k T σ (lamOf T σ n) x‖ ^ 2 + ‖packet w.k T σ (-(lamOf T σ n)) x‖ ^ 2) := by
    rw [sq_norm_sum_of_disjoint _ g hii]
    exact Finset.sum_congr rfl hiv
  rw [hK, ← hS, ← norm_real_mul_sq]
  by_cases hp0 : packet w.k T σ 0 x = 0
  · rw [hp0, mul_zero, zero_sub, norm_neg, norm_zero, zero_pow two_ne_zero, zero_add]
  · rw [Finset.sum_eq_zero fun n hn => hiii n hn hp0, sub_zero, norm_zero,
      zero_pow two_ne_zero, add_zero]

/-- the second trace of `K0` as a sum over the packets -/
theorem t2_K0_eq (w : HeightWeight) {T σ : ℝ} (hσ : 0 < σ) (hs : Sep w T σ) :
    t2 (K0 w.k T σ) = Real.log (T / (2 * π)) ^ 2 * Ipk w T σ 0
      + ∑ n ∈ Finset.Icc 2 (Nmax T σ), lamCoeff n ^ 2 *
          (Ipk w T σ (lamOf T σ n) + Ipk w T σ (-(lamOf T σ n))) := by
  have hc : ∀ lam : ℝ, IntervalIntegrable (fun x : ℝ => ag x * ‖packet w.k T σ lam x‖ ^ 2)
      volume (-1) 1 := fun lam => (continuous_ag_mul_packet w T σ lam).intervalIntegrable _ _
  have h1 : ∀ x : ℝ, ag x * ‖K0 w.k T σ x‖ ^ 2
      = Real.log (T / (2 * π)) ^ 2 * (ag x * ‖packet w.k T σ 0 x‖ ^ 2)
        + ∑ n ∈ Finset.Icc 2 (Nmax T σ), lamCoeff n ^ 2 *
          (ag x * ‖packet w.k T σ (lamOf T σ n) x‖ ^ 2
            + ag x * ‖packet w.k T σ (-(lamOf T σ n)) x‖ ^ 2) := by
    intro x
    rw [K0_norm_sq w hσ hs x, mul_add, Finset.mul_sum]
    congr 1
    · ring
    · exact Finset.sum_congr rfl fun n _ => by ring
  have hcn : ∀ n : ℕ, Continuous (fun x : ℝ => lamCoeff n ^ 2 *
      (ag x * ‖packet w.k T σ (lamOf T σ n) x‖ ^ 2
        + ag x * ‖packet w.k T σ (-(lamOf T σ n)) x‖ ^ 2)) := fun n =>
    continuous_const.mul
      ((continuous_ag_mul_packet w T σ _).add (continuous_ag_mul_packet w T σ _))
  have hc0 : IntervalIntegrable (fun x : ℝ => Real.log (T / (2 * π)) ^ 2 *
      (ag x * ‖packet w.k T σ 0 x‖ ^ 2)) volume (-1) 1 :=
    (continuous_const.mul (continuous_ag_mul_packet w T σ 0)).intervalIntegrable _ _
  unfold t2 Ipk
  simp_rw [h1]
  rw [intervalIntegral.integral_add hc0
      ((continuous_finsetSum _ fun n _ => hcn n).intervalIntegrable _ _),
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_finsetSum fun n _ => (hcn n).intervalIntegrable _ _]
  congr 1
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add (hc _) (hc _)]


/-! ### the second trace of `K0` -/

theorem lamCoeff_sq (n : ℕ) : lamCoeff n ^ 2 = Λ n ^ 2 / n := by
  unfold lamCoeff
  rw [div_pow, Real.sq_sqrt (Nat.cast_nonneg n)]

theorem primeSum_upper' : ∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℝ, 2 ≤ X →
    ∑ n ∈ Finset.Icc 2 ⌊X⌋₊, Λ n ^ 2 / n ≤ C * Real.log X ^ 2 := by
  obtain ⟨C, hC⟩ := primeSum_upper
  refine ⟨max C 0, le_max_right _ _, fun X hX => (hC X hX).trans ?_⟩
  exact mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _)

theorem sq_div_Asc {T σ : ℝ} (hT : 0 < T) : T ^ 2 / Asc T σ = T / (σ * Real.log T) := by
  unfold Asc
  rw [sq, mul_div_mul_left _ _ hT.ne']

/-- upper bound `t2 K0 ≤ C T log T` -/
theorem t2_K0_le (w : HeightWeight) {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ < 1) :
    ∃ C : ℝ, ∀ T : ℝ, Sep w T σ → 8 ≤ T → t2 (K0 w.k T σ) ≤ C * T * Real.log T := by
  obtain ⟨C₀, hC₀0, hC₀⟩ := primeSum_upper'
  refine ⟨10 / 9 * (w.kap2 / (2 * π)) * (1 + 8 * C₀) / σ, fun T hs hT8 => ?_⟩
  have hT0 : 0 < T := by linarith
  have hL : 0 < Real.log T := Real.log_pos (by linarith)
  have hσL : 0 < σ * Real.log T := mul_pos hσ hL
  have hQ : 0 ≤ w.kap2 / (2 * π) := div_nonneg (kap2_nonneg w) (by positivity)
  have hU0 : 0 ≤ T ^ 2 / Asc T σ * (10 / 9 * (w.kap2 / (2 * π))) :=
    mul_nonneg (div_nonneg (sq_nonneg T) hs.hA.le) (mul_nonneg (by norm_num) hQ)
  have h2π : 0 < 2 * π := by positivity
  have hell0 : 0 ≤ Real.log (T / (2 * π)) := by
    refine Real.log_nonneg ?_
    rw [le_div_iff₀ h2π]
    linarith [Real.pi_lt_four]
  have hell1 : Real.log (T / (2 * π)) ≤ Real.log T :=
    Real.log_le_log (div_pos hT0 h2π) (div_le_self hT0.le (by linarith [Real.pi_gt_three]))
  have hell2 : Real.log (T / (2 * π)) ^ 2 ≤ Real.log T ^ 2 := pow_le_pow_left₀ hell0 hell1 2
  have hTσ1 : 1 ≤ T ^ σ := Real.one_le_rpow (by linarith) hσ.le
  have hSN : ∑ n ∈ Finset.Icc 2 (Nmax T σ), Λ n ^ 2 / n ≤ C₀ * (2 * Real.log T) ^ 2 := by
    have h1 := hC₀ (2 * T ^ σ) (by linarith)
    have h2 : Real.log (2 * T ^ σ) = Real.log 2 + σ * Real.log T := by
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_rpow hT0]
    have h3 : Real.log 2 ≤ Real.log T := Real.log_le_log (by norm_num) (by linarith)
    have h3' : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have h3'' : σ * Real.log T ≤ 1 * Real.log T := mul_le_mul_of_nonneg_right hσ1.le hL.le
    have h4 : 0 ≤ Real.log (2 * T ^ σ) := by rw [h2]; linarith
    have h5 : Real.log (2 * T ^ σ) ≤ 2 * Real.log T := by rw [h2]; linarith
    exact h1.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h4 h5 2) hC₀0)
  rw [t2_K0_eq w hσ hs]
  have hsum : ∑ n ∈ Finset.Icc 2 (Nmax T σ), lamCoeff n ^ 2 *
        (Ipk w T σ (lamOf T σ n) + Ipk w T σ (-(lamOf T σ n)))
      ≤ ∑ n ∈ Finset.Icc 2 (Nmax T σ), Λ n ^ 2 / n *
        (2 * (T ^ 2 / Asc T σ * (10 / 9 * (w.kap2 / (2 * π))))) := by
    refine Finset.sum_le_sum fun n _ => ?_
    rw [lamCoeff_sq]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have h1 := Ipk_le w hs.hA (lamOf T σ n)
    have h2 := Ipk_le w hs.hA (-(lamOf T σ n))
    linarith
  rw [← Finset.sum_mul] at hsum
  have h1 : Real.log (T / (2 * π)) ^ 2 * Ipk w T σ 0
      ≤ Real.log T ^ 2 * (T ^ 2 / Asc T σ * (10 / 9 * (w.kap2 / (2 * π)))) :=
    mul_le_mul hell2 (Ipk_le w hs.hA 0) (Ipk_nonneg _ _ _ _) (sq_nonneg _)
  have h2 : (∑ n ∈ Finset.Icc 2 (Nmax T σ), Λ n ^ 2 / n) *
        (2 * (T ^ 2 / Asc T σ * (10 / 9 * (w.kap2 / (2 * π)))))
      ≤ C₀ * (2 * Real.log T) ^ 2 * (2 * (T ^ 2 / Asc T σ * (10 / 9 * (w.kap2 / (2 * π))))) :=
    mul_le_mul_of_nonneg_right hSN (by linarith)
  have h3 : Real.log T ^ 2 * (T ^ 2 / Asc T σ * (10 / 9 * (w.kap2 / (2 * π))))
      + C₀ * (2 * Real.log T) ^ 2 * (2 * (T ^ 2 / Asc T σ * (10 / 9 * (w.kap2 / (2 * π)))))
      = 10 / 9 * (w.kap2 / (2 * π)) * (1 + 8 * C₀) / σ * T * Real.log T := by
    rw [sq_div_Asc hT0]
    field_simp
    ring
  linarith

/-- lower bound for `t2 K0` in terms of prime sums up to `T^σ` -/
theorem t2_K0_ge_sum (w : HeightWeight) {T σ : ℝ} (hσ : 0 < σ) (hs : Sep w T σ) :
    T ^ 2 / Asc T σ * (w.kap2 / (2 * π)) *
      (Real.log (T / (2 * π)) ^ 2 * (I2 - 5 * w.kappa / Asc T σ)
        + 2 * ∑ n ∈ Finset.Icc 2 ⌊T ^ σ⌋₊, Λ n ^ 2 / n * ag (lamOf T σ n)
        - 2 * (5 * w.kappa / Asc T σ) * ∑ n ∈ Finset.Icc 2 ⌊T ^ σ⌋₊, Λ n ^ 2 / n)
      ≤ t2 (K0 w.k T σ) := by
  rw [t2_K0_eq w hσ hs]
  have hIge : ∀ lam : ℝ, T ^ 2 / Asc T σ * (w.kap2 / (2 * π)) * (ag lam - 5 * w.kappa / Asc T σ)
      ≤ Ipk w T σ lam := fun lam =>
    le_of_eq_of_le (by ring) (Ipk_ge w hs.hA lam)
  have hTσ : 0 ≤ T ^ σ := Real.rpow_nonneg (by linarith [hs.hT]) σ
  have hsub : Finset.Icc 2 ⌊T ^ σ⌋₊ ⊆ Finset.Icc 2 (Nmax T σ) :=
    Finset.Icc_subset_Icc_right (Nat.floor_le_floor (by linarith))
  have h0 : Real.log (T / (2 * π)) ^ 2 *
        (T ^ 2 / Asc T σ * (w.kap2 / (2 * π)) * (I2 - 5 * w.kappa / Asc T σ))
      ≤ Real.log (T / (2 * π)) ^ 2 * Ipk w T σ 0 :=
    mul_le_mul_of_nonneg_left (hIge 0) (sq_nonneg _)
  have h1 : ∑ n ∈ Finset.Icc 2 ⌊T ^ σ⌋₊, Λ n ^ 2 / n *
        (T ^ 2 / Asc T σ * (w.kap2 / (2 * π)) *
          (2 * ag (lamOf T σ n) - 2 * (5 * w.kappa / Asc T σ)))
      ≤ ∑ n ∈ Finset.Icc 2 ⌊T ^ σ⌋₊, lamCoeff n ^ 2 *
        (Ipk w T σ (lamOf T σ n) + Ipk w T σ (-(lamOf T σ n))) := by
    refine Finset.sum_le_sum fun n _ => ?_
    rw [lamCoeff_sq]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have h2 := hIge (lamOf T σ n)
    have h3 := hIge (-(lamOf T σ n))
    rw [ag_neg] at h3
    linarith
  have h2 : ∑ n ∈ Finset.Icc 2 ⌊T ^ σ⌋₊, lamCoeff n ^ 2 *
        (Ipk w T σ (lamOf T σ n) + Ipk w T σ (-(lamOf T σ n)))
      ≤ ∑ n ∈ Finset.Icc 2 (Nmax T σ), lamCoeff n ^ 2 *
        (Ipk w T σ (lamOf T σ n) + Ipk w T σ (-(lamOf T σ n))) :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub fun n _ _ =>
      mul_nonneg (sq_nonneg _) (add_nonneg (Ipk_nonneg _ _ _ _) (Ipk_nonneg _ _ _ _))
  have h3 : ∑ n ∈ Finset.Icc 2 ⌊T ^ σ⌋₊, Λ n ^ 2 / n *
        (T ^ 2 / Asc T σ * (w.kap2 / (2 * π)) *
          (2 * ag (lamOf T σ n) - 2 * (5 * w.kappa / Asc T σ)))
      = T ^ 2 / Asc T σ * (w.kap2 / (2 * π)) *
        (2 * ∑ n ∈ Finset.Icc 2 ⌊T ^ σ⌋₊, Λ n ^ 2 / n * ag (lamOf T σ n)
          - 2 * (5 * w.kappa / Asc T σ) * ∑ n ∈ Finset.Icc 2 ⌊T ^ σ⌋₊, Λ n ^ 2 / n) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.mul_sum]
    exact Finset.sum_congr rfl fun n _ => by ring
  rw [h3] at h1
  linarith

/-- the algebra behind the lower bound -/
theorem t2_alg {T L σ Q κ C₀ C₁ c I J SX SX' A : ℝ} (hT : 1 ≤ T) (hL : 0 < L) (hσ : 0 < σ)
    (hσ1 : σ ≤ 1) (hQ : 0 ≤ Q) (hκ : 0 ≤ κ) (hC₀ : 0 ≤ C₀) (hc : 0 ≤ c) (hcL : c ≤ L) (hI : 0 ≤ I)
    (hA : A = T * (σ * L)) (hSX : (σ * L) ^ 2 * (J / 2) - C₁ * (σ * L) ≤ SX)
    (hSX' : SX' ≤ C₀ * (σ * L) ^ 2) :
    T * L * Q * (I / σ + σ * J)
        - Q * (2 * c * I / σ + 2 * C₁ + 5 * κ * (1 + 2 * C₀) / σ ^ 2) * T
      ≤ T ^ 2 / A * Q * ((L - c) ^ 2 * (I - 5 * κ / A) + 2 * SX - 2 * (5 * κ / A) * SX') := by
  subst hA
  have hT0 : 0 < T := by linarith
  have hσL : 0 < σ * L := mul_pos hσ hL
  have hW0 : 0 ≤ T ^ 2 / (T * (σ * L)) * Q := by positivity
  have hε0 : 0 ≤ 5 * κ / (T * (σ * L)) := by positivity
  have p1 : (L ^ 2 - 2 * L * c) * I ≤ (L - c) ^ 2 * I := by
    refine mul_le_mul_of_nonneg_right ?_ hI
    have hsq : (L - c) ^ 2 = L ^ 2 - 2 * L * c + c ^ 2 := by ring
    rw [hsq]
    linarith [sq_nonneg c]
  have p2 : 5 * κ / (T * (σ * L)) * (L - c) ^ 2 ≤ 5 * κ / (T * (σ * L)) * L ^ 2 :=
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith) (by linarith) 2) hε0
  have hσL' : (σ * L) ^ 2 ≤ L ^ 2 := by
    refine pow_le_pow_left₀ hσL.le ?_ 2
    have := mul_le_mul_of_nonneg_right hσ1 hL.le
    linarith
  have p3 : 5 * κ / (T * (σ * L)) * SX' ≤ 5 * κ / (T * (σ * L)) * (C₀ * L ^ 2) := by
    refine mul_le_mul_of_nonneg_left (hSX'.trans ?_) hε0
    exact mul_le_mul_of_nonneg_left hσL' hC₀
  have hinner : L ^ 2 * I - 2 * L * c * I + (σ * L) ^ 2 * J - 2 * C₁ * (σ * L)
        - 5 * κ / (T * (σ * L)) * L ^ 2 * (1 + 2 * C₀)
      ≤ (L - c) ^ 2 * (I - 5 * κ / (T * (σ * L))) + 2 * SX
        - 2 * (5 * κ / (T * (σ * L))) * SX' := by
    linarith
  have hmul := mul_le_mul_of_nonneg_left hinner hW0
  have hid : T ^ 2 / (T * (σ * L)) * Q * (L ^ 2 * I - 2 * L * c * I + (σ * L) ^ 2 * J
        - 2 * C₁ * (σ * L) - 5 * κ / (T * (σ * L)) * L ^ 2 * (1 + 2 * C₀))
      = T * L * Q * (I / σ + σ * J) - Q * (2 * c * I / σ + 2 * C₁) * T
        - Q * (5 * κ * (1 + 2 * C₀) / σ ^ 2) := by
    field_simp
    ring
  have hlast : Q * (5 * κ * (1 + 2 * C₀) / σ ^ 2) ≤ Q * (5 * κ * (1 + 2 * C₀) / σ ^ 2) * T :=
    le_mul_of_one_le_right (by positivity) hT
  rw [hid] at hmul
  linarith

/-- lower bound `t2 K0 ≥ D · C₂(σ) κ₂ - C T` -/
theorem t2_K0_ge (w : HeightWeight) {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ < 1) :
    ∃ C : ℝ, ∀ T : ℝ, Sep w T σ → 8 ≤ T → 2 ≤ T ^ σ →
      Dsc T * (C2 σ * w.kap2) - C * T ≤ t2 (K0 w.k T σ) := by
  obtain ⟨F, hF, hFag⟩ := ag_smooth_on
  obtain ⟨C₁, hC₁⟩ := primeSum_asymp F hF
  obtain ⟨C₀, hC₀0, hC₀⟩ := primeSum_upper'
  refine ⟨w.kap2 / (2 * π) * (2 * Real.log (2 * π) * I2 / σ + 2 * C₁
    + 5 * w.kappa * (1 + 2 * C₀) / σ ^ 2), fun T hs hT8 hX2 => ?_⟩
  have hT0 : 0 < T := by linarith
  have hL : 0 < Real.log T := Real.log_pos (by linarith)
  have hσL : 0 < σ * Real.log T := mul_pos hσ hL
  have hQ : 0 ≤ w.kap2 / (2 * π) := div_nonneg (kap2_nonneg w) (by positivity)
  have hlogX : Real.log (T ^ σ) = σ * Real.log T := Real.log_rpow hT0 σ
  have h2π : 0 < 2 * π := by positivity
  have hc0 : 0 ≤ Real.log (2 * π) := Real.log_nonneg (by linarith [Real.pi_gt_three])
  have hcL : Real.log (2 * π) ≤ Real.log T :=
    Real.log_le_log h2π (by linarith [Real.pi_lt_four])
  have hell : Real.log (T / (2 * π)) = Real.log T - Real.log (2 * π) :=
    Real.log_div hT0.ne' h2π.ne'
  -- the prime sum with the weight `ag`
  have hSX : (σ * Real.log T) ^ 2 * (J2 / 2) - C₁ * (σ * Real.log T)
      ≤ ∑ n ∈ Finset.Icc 2 ⌊T ^ σ⌋₊, Λ n ^ 2 / n * ag (lamOf T σ n) := by
    have h1 := hC₁ (T ^ σ) hX2
    rw [hlogX] at h1
    have h2 : ∑ n ∈ Finset.Icc 2 ⌊T ^ σ⌋₊, Λ n ^ 2 / n * F (Real.log n / (σ * Real.log T))
        = ∑ n ∈ Finset.Icc 2 ⌊T ^ σ⌋₊, Λ n ^ 2 / n * ag (lamOf T σ n) := by
      refine Finset.sum_congr rfl fun n hn => ?_
      rw [Finset.mem_Icc] at hn
      have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
      have hnX : (n : ℝ) ≤ T ^ σ :=
        le_trans (by exact_mod_cast hn.2) (Nat.floor_le (by linarith))
      have hmem : Real.log n / (σ * Real.log T) ∈ Set.Icc (0 : ℝ) 1 := by
        refine ⟨div_nonneg (Real.log_nonneg hn1) hσL.le, ?_⟩
        rw [div_le_one hσL, ← hlogX]
        exact Real.log_le_log (by linarith) hnX
      rw [← hFag _ hmem]
      rfl
    have h3 : ∫ r in (0 : ℝ)..1, r * F r = J2 / 2 := by
      have h4 : ∫ r in (0 : ℝ)..1, r * F r = ∫ r in (0 : ℝ)..1, r * ag r := by
        refine intervalIntegral.integral_congr fun r hr => ?_
        rw [Set.uIcc_of_le (by norm_num)] at hr
        simp only [hFag r hr]
      rw [h4]
      unfold J2
      ring
    rw [h2, h3] at h1
    have h5 := (abs_le.mp h1).1
    linarith
  have hSX' : ∑ n ∈ Finset.Icc 2 ⌊T ^ σ⌋₊, Λ n ^ 2 / n ≤ C₀ * (σ * Real.log T) ^ 2 := by
    have h1 := hC₀ (T ^ σ) hX2
    rwa [hlogX] at h1
  have halg := t2_alg (T := T) (L := Real.log T) (σ := σ) (Q := w.kap2 / (2 * π))
    (κ := w.kappa) (C₀ := C₀) (C₁ := C₁) (c := Real.log (2 * π)) (I := I2) (J := J2)
    (A := Asc T σ) (by linarith) hL hσ hσ1.le hQ w.kappa_pos.le hC₀0 hc0 hcL (ag_nonneg 0) rfl
    hSX hSX'
  have hmain := t2_K0_ge_sum w hσ hs
  rw [hell] at hmain
  have hD : Dsc T * (C2 σ * w.kap2)
      = T * Real.log T * (w.kap2 / (2 * π)) * (I2 / σ + σ * J2) := by
    unfold Dsc C2
    ring
  rw [hD]
  linarith

/-- comparison of the second traces of two kernels -/
theorem t2_perturb {K K' : ℝ → ℂ} (hK : Continuous K) (hK' : Continuous K') {L : ℝ}
    (hL : 0 < L) :
    t2 K' - 1 / L * t2 K' - L * (10 / 9 * ∫ x in (-1 : ℝ)..1, ‖K x - K' x‖ ^ 2) ≤ t2 K := by
  unfold t2
  have hc1 : Continuous (fun x : ℝ => ag x * ‖K' x‖ ^ 2) := continuous_ag.mul (hK'.norm.pow 2)
  have hc2 : Continuous (fun x : ℝ => ‖K x - K' x‖ ^ 2) := (hK.sub hK').norm.pow 2
  have hc3 : Continuous (fun x : ℝ => ag x * ‖K x‖ ^ 2) := continuous_ag.mul (hK.norm.pow 2)
  have hc4 : Continuous (fun x : ℝ => 1 / L * (ag x * ‖K' x‖ ^ 2)) := continuous_const.mul hc1
  have hc5 : Continuous (fun x : ℝ => L * (10 / 9 * ‖K x - K' x‖ ^ 2)) :=
    continuous_const.mul (continuous_const.mul hc2)
  have hc6 : Continuous (fun x : ℝ => ag x * ‖K' x‖ ^ 2 - 1 / L * (ag x * ‖K' x‖ ^ 2)) :=
    hc1.sub hc4
  have hmono : ∫ x in (-1 : ℝ)..1, (ag x * ‖K' x‖ ^ 2 - 1 / L * (ag x * ‖K' x‖ ^ 2)
        - L * (10 / 9 * ‖K x - K' x‖ ^ 2))
      ≤ ∫ x in (-1 : ℝ)..1, ag x * ‖K x‖ ^ 2 := by
    refine intervalIntegral.integral_mono_on (by norm_num)
      ((hc6.sub hc5).intervalIntegrable _ _) (hc3.intervalIntegrable _ _) fun x _ => ?_
    have h1 := norm_add_sq_ge (K' x) (K x - K' x) hL
    rw [add_sub_cancel] at h1
    have h2 := mul_le_mul_of_nonneg_left h1 (ag_nonneg x)
    have h3 : ag x * ‖K x - K' x‖ ^ 2 ≤ 10 / 9 * ‖K x - K' x‖ ^ 2 :=
      mul_le_mul_of_nonneg_right (ag_le x) (sq_nonneg _)
    have h4 := mul_le_mul_of_nonneg_left h3 hL.le
    have h5 : ag x * (‖K' x‖ ^ 2 - 1 / L * ‖K' x‖ ^ 2 - L * ‖K x - K' x‖ ^ 2)
        = ag x * ‖K' x‖ ^ 2 - 1 / L * (ag x * ‖K' x‖ ^ 2) - L * (ag x * ‖K x - K' x‖ ^ 2) := by
      ring
    rw [h5] at h2
    linarith
  have heq : ∫ x in (-1 : ℝ)..1, (ag x * ‖K' x‖ ^ 2 - 1 / L * (ag x * ‖K' x‖ ^ 2)
        - L * (10 / 9 * ‖K x - K' x‖ ^ 2))
      = (∫ x in (-1 : ℝ)..1, ag x * ‖K' x‖ ^ 2) - 1 / L * (∫ x in (-1 : ℝ)..1, ag x * ‖K' x‖ ^ 2)
        - L * (10 / 9 * ∫ x in (-1 : ℝ)..1, ‖K x - K' x‖ ^ 2) := by
    rw [intervalIntegral.integral_sub (hc6.intervalIntegrable _ _) (hc5.intervalIntegrable _ _),
      intervalIntegral.integral_sub (hc1.intervalIntegrable _ _) (hc4.intervalIntegrable _ _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul]
  rw [heq] at hmono
  exact hmono


/-! ### the first trace -/

/-- `k(0) = κ₁ / 2π` -/
theorem k_zero (w : HeightWeight) : w.k 0 = ((w.kap1 / (2 * π) : ℝ) : ℂ) := by
  have h := w.inv 0
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, mul_one, neg_zero] at h
  rw [← h, integral_complex_ofReal]
  unfold HeightWeight.kap1
  push_cast
  ring

theorem kap1_nonneg (w : HeightWeight) : 0 ≤ w.kap1 := by
  unfold HeightWeight.kap1
  exact integral_nonneg fun x => w.h_nonneg x

/-- for `T` large the prime packets vanish at `x = 0` -/
theorem K0_zero (w : HeightWeight) {T σ : ℝ} (hσ : 0 < σ) (hs : Sep w T σ) :
    K0 w.k T σ 0 = ((Real.log (T / (2 * π)) * (T * (w.kap1 / (2 * π))) : ℝ) : ℂ) := by
  have hκA : 0 < w.kappa / Asc T σ := div_pos w.kappa_pos hs.hA
  have hsum : ∑ n ∈ Finset.Icc 2 (Nmax T σ), (lamCoeff n : ℂ) *
      (packet w.k T σ (lamOf T σ n) 0 + packet w.k T σ (-(lamOf T σ n)) 0) = 0 := by
    refine Finset.sum_eq_zero fun n hn => ?_
    have h1 := lamOf_gt w hσ hs (mem_Icc_Nmax hs.hT hn).1
    have h2 : w.kappa / Asc T σ < lamOf T σ n := by
      have h3 : 3 * w.kappa / Asc T σ = 3 * (w.kappa / Asc T σ) := by ring
      linarith
    have hlam0 : 0 ≤ lamOf T σ n := lamOf_nonneg T σ hσ hs.hT n
    have hp : packet w.k T σ (lamOf T σ n) 0 = 0 := by
      refine packet_eq_zero w hs.hA ?_
      rw [zero_sub, abs_neg, abs_of_nonneg hlam0]
      exact h2
    have hm : packet w.k T σ (-(lamOf T σ n)) 0 = 0 := by
      refine packet_eq_zero w hs.hA ?_
      rw [zero_sub, neg_neg, abs_of_nonneg hlam0]
      exact h2
    rw [hp, hm, add_zero, mul_zero]
  unfold K0
  rw [hsum, sub_zero]
  unfold packet
  rw [sub_zero, mul_zero, neg_zero, k_zero]
  push_cast
  ring

end T12

/-- first trace:  `K(0) = Σ m h(γ/T) ≤ (∫h + δ) D` -/
theorem t1_upper (hRH : RiemannHypothesis) (w : HeightWeight) {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ < 1) :
    ∀ δ > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (Kfull w.h T σ 0).re ≤ (w.kap1 + δ) * Dsc T := by
  intro δ hδ
  obtain ⟨C, T₁, hker⟩ := kernel_error hRH w hσ hσ1
  obtain ⟨T₂, hsep⟩ := separation w hσ hσ1
  obtain ⟨T₃, hT₃⟩ := Filter.eventually_atTop.mp
    (Real.tendsto_log_atTop.eventually_ge_atTop (2 * π * C / δ))
  refine ⟨max (max T₁ T₂) T₃, fun T hT => ?_⟩
  have hT1 : T₁ ≤ T := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hT
  have hT2 : T₂ ≤ T := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hT
  have hLδ : 2 * π * C / δ ≤ Real.log T := hT₃ T (le_trans (le_max_right _ _) hT)
  obtain ⟨hT2', hA, hκ, -, hlog⟩ := hsep T hT2
  have hs : T12.Sep w T σ := ⟨hT2', hA, hκ, hlog⟩
  have hT0 : 0 < T := by linarith
  have h2π : 0 < 2 * π := by positivity
  have hE := (hker T hT1).1 0 (by rw [abs_zero]; exact zero_le_one)
  rw [T12.K0_zero w hσ hs] at hE
  have hre : (Kfull w.h T σ 0).re
      ≤ Real.log (T / (2 * π)) * (T * (w.kap1 / (2 * π))) + C * T := by
    have h1 := Complex.re_le_norm
      (Kfull w.h T σ 0 - ((Real.log (T / (2 * π)) * (T * (w.kap1 / (2 * π))) : ℝ) : ℂ))
    rw [Complex.sub_re, Complex.ofReal_re] at h1
    linarith
  have hell : Real.log (T / (2 * π)) ≤ Real.log T :=
    Real.log_le_log (div_pos hT0 h2π) (div_le_self hT0.le (by linarith [Real.pi_gt_three]))
  have hk : 0 ≤ T * (w.kap1 / (2 * π)) :=
    mul_nonneg hT0.le (div_nonneg (T12.kap1_nonneg w) h2π.le)
  have h1 := mul_le_mul_of_nonneg_right hell hk
  have hC : C ≤ δ * Real.log T / (2 * π) := by
    rw [le_div_iff₀ h2π]
    rw [div_le_iff₀ hδ] at hLδ
    linarith
  have h2 := mul_le_mul_of_nonneg_right hC hT0.le
  have h3 : (w.kap1 + δ) * Dsc T
      = Real.log T * (T * (w.kap1 / (2 * π))) + δ * Real.log T / (2 * π) * T := by
    unfold Dsc
    ring
  rw [h3]
  linarith

/-- second trace:  `t2(K) ≥ (C₂(σ) ∫h² - δ) D` -/
theorem t2_lower (hRH : RiemannHypothesis) (w : HeightWeight) {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ < 1) :
    ∀ δ > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (C2 σ * w.kap2 - δ) * Dsc T ≤ t2 (Kfull w.h T σ) := by
  intro δ hδ
  obtain ⟨Ck, T₁, hker⟩ := kernel_error hRH w hσ hσ1
  obtain ⟨T₂, hsep⟩ := separation w hσ hσ1
  obtain ⟨Cu, hCu⟩ := T12.t2_K0_le w hσ hσ1
  obtain ⟨Cl, hCl⟩ := T12.t2_K0_ge w hσ hσ1
  obtain ⟨T₃, hT₃⟩ := Filter.eventually_atTop.mp
    (Real.tendsto_log_atTop.eventually_ge_atTop
      (max (Real.log 2 / σ) (2 * π * (Cl + Cu + 10 / 9 * Ck) / δ)))
  refine ⟨max (max T₁ T₂) (max T₃ 8), fun T hT => ?_⟩
  have hT1 : T₁ ≤ T := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hT
  have hT2 : T₂ ≤ T := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hT
  have hT3 : T₃ ≤ T := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hT
  have hT8 : 8 ≤ T := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hT
  have hLmax := hT₃ T hT3
  have hLσ : Real.log 2 / σ ≤ Real.log T := le_trans (le_max_left _ _) hLmax
  have hLδ : 2 * π * (Cl + Cu + 10 / 9 * Ck) / δ ≤ Real.log T :=
    le_trans (le_max_right _ _) hLmax
  obtain ⟨hT2', hA, hκ, -, hlog⟩ := hsep T hT2
  have hs : T12.Sep w T σ := ⟨hT2', hA, hκ, hlog⟩
  have hT0 : 0 < T := by linarith
  have hL : 0 < Real.log T := Real.log_pos (by linarith)
  have h2π : 0 < 2 * π := by positivity
  have hX2 : 2 ≤ T ^ σ := by
    rw [← Real.log_le_log_iff (by norm_num) (Real.rpow_pos_of_pos hT0 σ), Real.log_rpow hT0]
    rw [div_le_iff₀ hσ] at hLσ
    linarith
  have hu := hCu T hs hT8
  have hl := hCl T hs hT8 hX2
  have hE2 := (hker T hT1).2.2
  have hstep := T12.t2_perturb (continuous_Kfull hRH w hT0 σ) (continuous_K0 w T σ) hL
  -- the three error terms are `O(T)`
  have e1 : 1 / Real.log T * t2 (K0 w.k T σ) ≤ Cu * T := by
    have h1 := mul_le_mul_of_nonneg_left hu (one_div_pos.mpr hL).le
    have h2 : 1 / Real.log T * (Cu * T * Real.log T) = Cu * T := by
      field_simp
    linarith
  have e2 : Real.log T * (10 / 9 * ∫ x in (-1 : ℝ)..1, ‖Kfull w.h T σ x - K0 w.k T σ x‖ ^ 2)
      ≤ 10 / 9 * Ck * T := by
    have h1 := mul_le_mul_of_nonneg_left hE2 (show (0 : ℝ) ≤ Real.log T * (10 / 9) by positivity)
    have h2 : Real.log T * (10 / 9) * (Ck * T / Real.log T) = 10 / 9 * Ck * T := by
      field_simp
    linarith
  have hC : Cl + Cu + 10 / 9 * Ck ≤ δ * Real.log T / (2 * π) := by
    rw [le_div_iff₀ h2π]
    rw [div_le_iff₀ hδ] at hLδ
    linarith
  have h2 := mul_le_mul_of_nonneg_right hC hT0.le
  have h3 : (C2 σ * w.kap2 - δ) * Dsc T
      = Dsc T * (C2 σ * w.kap2) - δ * Real.log T / (2 * π) * T := by
    unfold Dsc
    ring
  rw [h3]
  linarith

end TMA

end
end Src_TMA_Traces

section Src_TMA_Trace3Aux1
/-
Written for Kristian Muri Knausgård, drafted with Claude (Anthropic), 22 November 2026.

TMA/Trace3Aux1.lean — the trilinear form `tri` behind the third trace `t3`:
* `t3 K = tri K K K`;
* representation as an integral over the plane (the kernel `Gg` vanishes outside the hexagon);
* trilinearity for continuous arguments;
* the three bounds `‖tri X Y Z‖ ≤ ‖·‖_{L¹[-1,1]} · (‖·‖²_{L²[-1,1]} + ‖·‖²_{L²[-1,1]})`, with the `L¹` norm on any
  of the three slots.
See BLUEPRINT.md, module "T3" (error term).
-/

open MeasureTheory Complex
open scoped BigOperators ArithmeticFunction Real

noncomputable section
namespace TMA.T3

/-- the trilinear form behind `t3` -/
def tri (X Y Z : ℝ → ℂ) : ℂ :=
  ∫ x in (-1 : ℝ)..1, ∫ y in (-1 : ℝ)..1, (Gg x y : ℂ) * (X x * Y y * Z (-x - y))

theorem t3_eq_tri (K : ℝ → ℂ) : t3 K = tri K K K := rfl

/-- the integrand of `tri` as a function on the plane -/
def triF (X Y Z : ℝ → ℂ) (p : ℝ × ℝ) : ℂ :=
  (Gg p.1 p.2 : ℂ) * (X p.1 * Y p.2 * Z (-p.1 - p.2))

theorem Gg_eq_zero_of_not {r s : ℝ} (h : ¬ (|r| ≤ 1 ∧ |s| ≤ 1 ∧ |r + s| ≤ 1)) : Gg r s = 0 := by
  apply Gg_eq_zero
  by_contra hc
  simp only [not_or, not_lt] at hc
  exact h hc

theorem abs_Gg_le (r s : ℝ) : |Gg r s| ≤ 2 := by
  rw [abs_of_nonneg (Gg_nonneg r s)]
  exact Gg_le r s

theorem triF_eq_zero {X Y Z : ℝ → ℂ} {p : ℝ × ℝ} (h : ¬ (|p.1| ≤ 1 ∧ |p.2| ≤ 1 ∧ |p.1 + p.2| ≤ 1)) :
    triF X Y Z p = 0 := by
  simp [triF, Gg_eq_zero_of_not h]

theorem continuous_triF {X Y Z : ℝ → ℂ} (hX : Continuous X) (hY : Continuous Y) (hZ : Continuous Z) :
    Continuous (triF X Y Z) := by
  unfold triF
  have h1 : Continuous (fun p : ℝ × ℝ => (Gg p.1 p.2 : ℂ)) := Complex.continuous_ofReal.comp continuous_Gg
  have h2 : Continuous (fun p : ℝ × ℝ => X p.1) := hX.comp continuous_fst
  have h3 : Continuous (fun p : ℝ × ℝ => Y p.2) := hY.comp continuous_snd
  have h4 : Continuous (fun p : ℝ × ℝ => Z (-p.1 - p.2)) :=
    hZ.comp (continuous_fst.neg.sub continuous_snd)
  exact h1.mul ((h2.mul h3).mul h4)

/-- a continuous function on the plane that vanishes outside a square is integrable -/
theorem integrable_of_continuous_of_square {f : ℝ × ℝ → ℂ} (hf : Continuous f) (R : ℝ)
    (h0 : ∀ p : ℝ × ℝ, ¬ (|p.1| ≤ R ∧ |p.2| ≤ R) → f p = 0) : Integrable f := by
  apply hf.integrable_of_hasCompactSupport
  apply HasCompactSupport.intro
    ((isCompact_Icc (a := -R) (b := R)).prod (isCompact_Icc (a := -R) (b := R)))
  intro p hp
  apply h0
  intro h
  apply hp
  exact ⟨abs_le.mp h.1, abs_le.mp h.2⟩

theorem integrable_triF {X Y Z : ℝ → ℂ} (hX : Continuous X) (hY : Continuous Y) (hZ : Continuous Z) :
    Integrable (triF X Y Z) :=
  integrable_of_continuous_of_square (continuous_triF hX hY hZ) 1
    (fun _ h => triF_eq_zero (fun h' => h ⟨h'.1, h'.2.1⟩))

theorem intervalIntegral_eq_integral_of_zero {f : ℝ → ℂ} (h : ∀ x, ¬ |x| ≤ 1 → f x = 0) :
    ∫ x in (-1 : ℝ)..1, f x = ∫ x, f x := by
  rw [intervalIntegral.integral_of_le (by norm_num), ← integral_Icc_eq_integral_Ioc]
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro x hx
  apply h
  intro hx'
  exact hx (abs_le.mp hx')

/-- `tri` as an iterated integral over the line -/
theorem tri_eq_integral_integral (X Y Z : ℝ → ℂ) :
    tri X Y Z = ∫ x, ∫ y, triF X Y Z (x, y) := by
  unfold tri
  have h1 : ∀ x : ℝ, ∫ y in (-1 : ℝ)..1, (Gg x y : ℂ) * (X x * Y y * Z (-x - y))
      = ∫ y, triF X Y Z (x, y) := by
    intro x
    apply intervalIntegral_eq_integral_of_zero (f := fun y => triF X Y Z (x, y))
    intro y hy
    exact triF_eq_zero (p := (x, y)) (fun h => hy h.2.1)
  simp_rw [h1]
  apply intervalIntegral_eq_integral_of_zero
  intro x hx
  have : ∀ y, triF X Y Z (x, y) = 0 := fun y => triF_eq_zero (p := (x, y)) (fun h => hx h.1)
  simp [this]

/-- `tri` as an integral over the plane -/
theorem tri_eq_integral_prod {X Y Z : ℝ → ℂ} (hX : Continuous X) (hY : Continuous Y) (hZ : Continuous Z) :
    tri X Y Z = ∫ p, triF X Y Z p := by
  rw [tri_eq_integral_integral]
  exact (integral_prod _ (integrable_triF hX hY hZ)).symm

/-! ### trilinearity -/

theorem tri_smul_left (c : ℂ) (X Y Z : ℝ → ℂ) : tri (fun x => c * X x) Y Z = c * tri X Y Z := by
  unfold tri
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr (fun x _ => ?_)
  beta_reduce
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr (fun y _ => ?_)
  ring

theorem tri_smul_mid (c : ℂ) (X Y Z : ℝ → ℂ) : tri X (fun x => c * Y x) Z = c * tri X Y Z := by
  unfold tri
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr (fun x _ => ?_)
  beta_reduce
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr (fun y _ => ?_)
  ring

theorem tri_smul_right (c : ℂ) (X Y Z : ℝ → ℂ) : tri X Y (fun x => c * Z x) = c * tri X Y Z := by
  unfold tri
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr (fun x _ => ?_)
  beta_reduce
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr (fun y _ => ?_)
  ring

theorem tri_add_left {X X' Y Z : ℝ → ℂ} (hX : Continuous X) (hX' : Continuous X') (hY : Continuous Y)
    (hZ : Continuous Z) : tri (fun x => X x + X' x) Y Z = tri X Y Z + tri X' Y Z := by
  rw [tri_eq_integral_prod (X := fun x => X x + X' x) (hX.add hX') hY hZ, tri_eq_integral_prod hX hY hZ,
    tri_eq_integral_prod hX' hY hZ, ← integral_add (integrable_triF hX hY hZ) (integrable_triF hX' hY hZ)]
  congr 1
  funext p
  simp only [triF]
  ring

theorem tri_add_mid {X Y Y' Z : ℝ → ℂ} (hX : Continuous X) (hY : Continuous Y) (hY' : Continuous Y')
    (hZ : Continuous Z) : tri X (fun x => Y x + Y' x) Z = tri X Y Z + tri X Y' Z := by
  rw [tri_eq_integral_prod (Y := fun x => Y x + Y' x) hX (hY.add hY') hZ, tri_eq_integral_prod hX hY hZ,
    tri_eq_integral_prod hX hY' hZ, ← integral_add (integrable_triF hX hY hZ) (integrable_triF hX hY' hZ)]
  congr 1
  funext p
  simp only [triF]
  ring

theorem tri_add_right {X Y Z Z' : ℝ → ℂ} (hX : Continuous X) (hY : Continuous Y) (hZ : Continuous Z)
    (hZ' : Continuous Z') : tri X Y (fun x => Z x + Z' x) = tri X Y Z + tri X Y Z' := by
  rw [tri_eq_integral_prod (Z := fun x => Z x + Z' x) hX hY (hZ.add hZ'), tri_eq_integral_prod hX hY hZ,
    tri_eq_integral_prod hX hY hZ', ← integral_add (integrable_triF hX hY hZ) (integrable_triF hX hY hZ')]
  congr 1
  funext p
  simp only [triF]
  ring

theorem tri_sub_left {X X' Y Z : ℝ → ℂ} (hX : Continuous X) (hX' : Continuous X') (hY : Continuous Y)
    (hZ : Continuous Z) : tri (fun x => X x - X' x) Y Z = tri X Y Z - tri X' Y Z := by
  rw [tri_eq_integral_prod (X := fun x => X x - X' x) (hX.sub hX') hY hZ, tri_eq_integral_prod hX hY hZ,
    tri_eq_integral_prod hX' hY hZ, ← integral_sub (integrable_triF hX hY hZ) (integrable_triF hX' hY hZ)]
  congr 1
  funext p
  simp only [triF]
  ring

theorem tri_sub_mid {X Y Y' Z : ℝ → ℂ} (hX : Continuous X) (hY : Continuous Y) (hY' : Continuous Y')
    (hZ : Continuous Z) : tri X (fun x => Y x - Y' x) Z = tri X Y Z - tri X Y' Z := by
  rw [tri_eq_integral_prod (Y := fun x => Y x - Y' x) hX (hY.sub hY') hZ, tri_eq_integral_prod hX hY hZ,
    tri_eq_integral_prod hX hY' hZ, ← integral_sub (integrable_triF hX hY hZ) (integrable_triF hX hY' hZ)]
  congr 1
  funext p
  simp only [triF]
  ring

theorem tri_sub_right {X Y Z Z' : ℝ → ℂ} (hX : Continuous X) (hY : Continuous Y) (hZ : Continuous Z)
    (hZ' : Continuous Z') : tri X Y (fun x => Z x - Z' x) = tri X Y Z - tri X Y Z' := by
  rw [tri_eq_integral_prod (Z := fun x => Z x - Z' x) hX hY (hZ.sub hZ'), tri_eq_integral_prod hX hY hZ,
    tri_eq_integral_prod hX hY hZ', ← integral_sub (integrable_triF hX hY hZ) (integrable_triF hX hY hZ')]
  congr 1
  funext p
  simp only [triF]
  ring

theorem tri_sum_left {ι : Type*} (s : Finset ι) {f : ι → ℝ → ℂ} (hf : ∀ i ∈ s, Continuous (f i))
    {Y Z : ℝ → ℂ} (hY : Continuous Y) (hZ : Continuous Z) :
    tri (fun x => ∑ i ∈ s, f i x) Y Z = ∑ i ∈ s, tri (f i) Y Z := by
  rw [tri_eq_integral_prod (continuous_finsetSum s hf) hY hZ]
  have h : (fun p => triF (fun x => ∑ i ∈ s, f i x) Y Z p) = fun p => ∑ i ∈ s, triF (f i) Y Z p := by
    funext p
    simp only [triF, Finset.sum_mul, Finset.mul_sum]
  rw [h, integral_finsetSum s (fun i hi => integrable_triF (hf i hi) hY hZ)]
  exact Finset.sum_congr rfl (fun i hi => (tri_eq_integral_prod (hf i hi) hY hZ).symm)

theorem tri_sum_mid {ι : Type*} (s : Finset ι) {f : ι → ℝ → ℂ} (hf : ∀ i ∈ s, Continuous (f i))
    {X Z : ℝ → ℂ} (hX : Continuous X) (hZ : Continuous Z) :
    tri X (fun x => ∑ i ∈ s, f i x) Z = ∑ i ∈ s, tri X (f i) Z := by
  rw [tri_eq_integral_prod hX (continuous_finsetSum s hf) hZ]
  have h : (fun p => triF X (fun x => ∑ i ∈ s, f i x) Z p) = fun p => ∑ i ∈ s, triF X (f i) Z p := by
    funext p
    simp only [triF, Finset.sum_mul, Finset.mul_sum]
  rw [h, integral_finsetSum s (fun i hi => integrable_triF hX (hf i hi) hZ)]
  exact Finset.sum_congr rfl (fun i hi => (tri_eq_integral_prod hX (hf i hi) hZ).symm)

theorem tri_sum_right {ι : Type*} (s : Finset ι) {f : ι → ℝ → ℂ} (hf : ∀ i ∈ s, Continuous (f i))
    {X Y : ℝ → ℂ} (hX : Continuous X) (hY : Continuous Y) :
    tri X Y (fun x => ∑ i ∈ s, f i x) = ∑ i ∈ s, tri X Y (f i) := by
  rw [tri_eq_integral_prod hX hY (continuous_finsetSum s hf)]
  have h : (fun p => triF X Y (fun x => ∑ i ∈ s, f i x) p) = fun p => ∑ i ∈ s, triF X Y (f i) p := by
    funext p
    simp only [triF, Finset.mul_sum]
  rw [h, integral_finsetSum s (fun i hi => integrable_triF hX hY (hf i hi))]
  exact Finset.sum_congr rfl (fun i hi => (tri_eq_integral_prod hX hY (hf i hi)).symm)

/-! ### bounds -/

/-- The common core of the three bounds: an iterated integral of a function dominated by
`2 ‖U p‖ ‖V q‖ ‖W (-p-q)‖` and supported in the hexagon. -/
theorem core_bound {Φ : ℝ → ℝ → ℂ} {U V W : ℝ → ℂ} (hU : Continuous U) (hV : Continuous V)
    (hW : Continuous W)
    (hΦ0 : ∀ p q, ¬ (|p| ≤ 1 ∧ |q| ≤ 1 ∧ |p + q| ≤ 1) → Φ p q = 0)
    (hΦ : ∀ p q, ‖Φ p q‖ ≤ 2 * (‖U p‖ * (‖V q‖ * ‖W (-p - q)‖))) :
    ‖∫ p, ∫ q, Φ p q‖ ≤ (∫ p in (-1 : ℝ)..1, ‖U p‖) *
      ((∫ q in (-1 : ℝ)..1, ‖V q‖ ^ 2) + ∫ q in (-1 : ℝ)..1, ‖W q‖ ^ 2) := by
  set Vt : ℝ → ℝ := (Set.Icc (-1 : ℝ) 1).indicator (fun q => ‖V q‖ ^ 2) with hVt
  set Wt : ℝ → ℝ := (Set.Icc (-1 : ℝ) 1).indicator (fun q => ‖W q‖ ^ 2) with hWt
  have hVi : Integrable Vt :=
    ((hV.norm.pow 2).integrableOn_Icc).integrable_indicator measurableSet_Icc
  have hWi : Integrable Wt :=
    ((hW.norm.pow 2).integrableOn_Icc).integrable_indicator measurableSet_Icc
  have hVint : ∫ q, Vt q = ∫ q in (-1 : ℝ)..1, ‖V q‖ ^ 2 := by
    rw [hVt, integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by norm_num)]
  have hWint : ∫ q, Wt q = ∫ q in (-1 : ℝ)..1, ‖W q‖ ^ 2 := by
    rw [hWt, integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by norm_num)]
  have hVnn : ∀ q, 0 ≤ Vt q := fun q => Set.indicator_nonneg (fun _ _ => by positivity) q
  have hWnn : ∀ q, 0 ≤ Wt q := fun q => Set.indicator_nonneg (fun _ _ => by positivity) q
  set c : ℝ := (∫ q in (-1 : ℝ)..1, ‖V q‖ ^ 2) + ∫ q in (-1 : ℝ)..1, ‖W q‖ ^ 2 with hc
  have hc0 : 0 ≤ c := by
    rw [hc, ← hVint, ← hWint]
    exact add_nonneg (integral_nonneg hVnn) (integral_nonneg hWnn)
  -- the inner integral
  have hin : ∀ p, ‖∫ q, Φ p q‖ ≤ ‖U p‖ * c := by
    intro p
    have hWs : Integrable (fun q => Wt (-p - q)) := hWi.comp_sub_left (-p)
    have hg : Integrable (fun q => ‖U p‖ * (Vt q + Wt (-p - q))) := (hVi.add hWs).const_mul _
    calc ‖∫ q, Φ p q‖ ≤ ∫ q, ‖Φ p q‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ q, ‖U p‖ * (Vt q + Wt (-p - q)) := by
          apply integral_mono_of_nonneg (Filter.Eventually.of_forall (fun q => norm_nonneg _)) hg
          apply Filter.Eventually.of_forall
          intro q
          show ‖Φ p q‖ ≤ ‖U p‖ * (Vt q + Wt (-p - q))
          by_cases h : |p| ≤ 1 ∧ |q| ≤ 1 ∧ |p + q| ≤ 1
          · have hq : q ∈ Set.Icc (-1 : ℝ) 1 := abs_le.mp h.2.1
            have hpq : -p - q ∈ Set.Icc (-1 : ℝ) 1 := by
              have := abs_le.mp h.2.2
              exact ⟨by linarith, by linarith⟩
            have h1 : Vt q = ‖V q‖ ^ 2 := Set.indicator_of_mem hq _
            have h2 : Wt (-p - q) = ‖W (-p - q)‖ ^ 2 := Set.indicator_of_mem hpq _
            rw [h1, h2]
            have h3 := hΦ p q
            have h4 := mul_nonneg (norm_nonneg (U p)) (sq_nonneg (‖V q‖ - ‖W (-p - q)‖))
            linarith [h3, h4]
          · rw [hΦ0 p q h, norm_zero]
            exact mul_nonneg (norm_nonneg _) (add_nonneg (hVnn _) (hWnn _))
      _ = ‖U p‖ * c := by
          rw [integral_const_mul, integral_add hVi hWs, integral_sub_left_eq_self Wt volume (-p),
            hVint, hWint]
  have hin0 : ∀ p, ¬ |p| ≤ 1 → ∫ q, Φ p q = 0 := by
    intro p hp
    have : ∀ q, Φ p q = 0 := fun q => hΦ0 p q (fun h => hp h.1)
    simp [this]
  calc ‖∫ p, ∫ q, Φ p q‖ ≤ ∫ p, ‖∫ q, Φ p q‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ p, (Set.Icc (-1 : ℝ) 1).indicator (fun p => ‖U p‖ * c) p := by
        apply integral_mono_of_nonneg (Filter.Eventually.of_forall (fun q => norm_nonneg _))
        · exact ((hU.norm.mul continuous_const).integrableOn_Icc).integrable_indicator measurableSet_Icc
        · apply Filter.Eventually.of_forall
          intro p
          show ‖∫ q, Φ p q‖ ≤ (Set.Icc (-1 : ℝ) 1).indicator (fun p => ‖U p‖ * c) p
          by_cases hp : |p| ≤ 1
          · have hp' : p ∈ Set.Icc (-1 : ℝ) 1 := abs_le.mp hp
            rw [Set.indicator_of_mem hp']
            exact hin p
          · rw [hin0 p hp, norm_zero]
            exact Set.indicator_nonneg (fun _ _ => mul_nonneg (norm_nonneg _) hc0) p
    _ = (∫ p in (-1 : ℝ)..1, ‖U p‖) * c := by
        rw [integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
          ← intervalIntegral.integral_of_le (by norm_num), intervalIntegral.integral_mul_const]

theorem norm_triF_le (X Y Z : ℝ → ℂ) (p : ℝ × ℝ) :
    ‖triF X Y Z p‖ ≤ 2 * (‖X p.1‖ * ‖Y p.2‖ * ‖Z (-p.1 - p.2)‖) := by
  unfold triF
  rw [norm_mul, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right (abs_Gg_le _ _) (by positivity)

/-- `L¹` norm on the first slot -/
theorem tri_bound_left {X Y Z : ℝ → ℂ} (hX : Continuous X) (hY : Continuous Y) (hZ : Continuous Z) :
    ‖tri X Y Z‖ ≤ (∫ x in (-1 : ℝ)..1, ‖X x‖) *
      ((∫ x in (-1 : ℝ)..1, ‖Y x‖ ^ 2) + ∫ x in (-1 : ℝ)..1, ‖Z x‖ ^ 2) := by
  rw [tri_eq_integral_integral]
  apply core_bound hX hY hZ (Φ := fun x y => triF X Y Z (x, y))
  · intro p q h
    exact triF_eq_zero h
  · intro p q
    have h := norm_triF_le X Y Z (p, q)
    simp only at h
    rw [mul_assoc] at h
    exact h

/-- `L¹` norm on the second slot -/
theorem tri_bound_mid {X Y Z : ℝ → ℂ} (hX : Continuous X) (hY : Continuous Y) (hZ : Continuous Z) :
    ‖tri X Y Z‖ ≤ (∫ x in (-1 : ℝ)..1, ‖Y x‖) *
      ((∫ x in (-1 : ℝ)..1, ‖X x‖ ^ 2) + ∫ x in (-1 : ℝ)..1, ‖Z x‖ ^ 2) := by
  rw [tri_eq_integral_integral,
    integral_integral_swap (f := fun x y => triF X Y Z (x, y)) (integrable_triF hX hY hZ)]
  apply core_bound hY hX hZ (Φ := fun y x => triF X Y Z (x, y))
  · intro p q h
    apply triF_eq_zero
    intro h'
    exact h ⟨h'.2.1, h'.1, by rw [add_comm]; exact h'.2.2⟩
  · intro p q
    have h := norm_triF_le X Y Z (q, p)
    simp only at h
    have e : -p - q = -q - p := by ring
    rw [e]
    calc ‖triF X Y Z (q, p)‖ ≤ 2 * (‖X q‖ * ‖Y p‖ * ‖Z (-q - p)‖) := h
      _ = 2 * (‖Y p‖ * (‖X q‖ * ‖Z (-q - p)‖)) := by ring

/-- `L¹` norm on the third slot -/
theorem tri_bound_right {X Y Z : ℝ → ℂ} (hX : Continuous X) (hY : Continuous Y) (hZ : Continuous Z) :
    ‖tri X Y Z‖ ≤ (∫ x in (-1 : ℝ)..1, ‖Z x‖) *
      ((∫ x in (-1 : ℝ)..1, ‖X x‖ ^ 2) + ∫ x in (-1 : ℝ)..1, ‖Y x‖ ^ 2) := by
  rw [tri_eq_integral_integral]
  have h1 : ∀ x : ℝ, ∫ y, triF X Y Z (x, y) = ∫ v, triF X Y Z (x, -x - v) := fun x =>
    (integral_sub_left_eq_self (fun y => triF X Y Z (x, y)) volume (-x)).symm
  simp_rw [h1]
  have hG : Integrable (fun p : ℝ × ℝ => triF X Y Z (p.1, -p.1 - p.2)) := by
    apply integrable_of_continuous_of_square _ 1
    · intro p h
      apply triF_eq_zero
      intro h'
      apply h
      refine ⟨h'.1, ?_⟩
      have h3 := h'.2.2
      have e : p.1 + (-p.1 - p.2) = -p.2 := by ring
      simp only at h3
      rw [e, abs_neg] at h3
      exact h3
    · exact (continuous_triF hX hY hZ).comp
        (continuous_fst.prodMk (continuous_fst.neg.sub continuous_snd))
  rw [integral_integral_swap (f := fun x v => triF X Y Z (x, -x - v)) hG]
  apply core_bound hZ hX hY (Φ := fun v x => triF X Y Z (x, -x - v))
  · intro v x h
    apply triF_eq_zero
    intro h'
    apply h
    have h2 := h'.2.1
    have h3 := h'.2.2
    simp only at h2 h3
    have e : x + (-x - v) = -v := by ring
    rw [e, abs_neg] at h3
    have e2 : -x - v = -(v + x) := by ring
    rw [e2, abs_neg] at h2
    exact ⟨h3, h'.1, h2⟩
  · intro v x
    have h := norm_triF_le X Y Z (x, -x - v)
    simp only at h
    have e1 : -x - (-x - v) = v := by ring
    have e2 : -v - x = -x - v := by ring
    rw [e1] at h
    rw [e2]
    calc ‖triF X Y Z (x, -x - v)‖ ≤ 2 * (‖X x‖ * ‖Y (-x - v)‖ * ‖Z v‖) := h
      _ = 2 * (‖Z v‖ * (‖X x‖ * ‖Y (-x - v)‖)) := by ring

end TMA.T3
end
end Src_TMA_Trace3Aux1

section Src_TMA_Trace3Aux2
/-
Written for Kristian Muri Knausgård, drafted with Claude (Anthropic), 22 November 2026.

TMA/Trace3Aux2.lean — packets and packet triples:
* norms of a packet (`sup`, `L¹`, `L²`);
* closure: `tri` of three packets vanishes unless the centres add up to at most `3κ/A` in absolute value;
* size: `‖tri‖ ≤ 2 T³ M (∫‖k‖)² / A²`;
* evaluation: if the centres add up to zero, `tri = (T³/A²) (Gg l1 l2 · (1/2π) ∫h³ + O(1/A))`.
See BLUEPRINT.md, module "T3" (main term).
-/

open MeasureTheory Complex
open scoped BigOperators ArithmeticFunction Real

noncomputable section
namespace TMA.T3

/-! ### changes of variables on the line -/

theorem integral_comp_packet_arg {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (g : ℝ → F)
    {A : ℝ} (hA : 0 < A) (lam : ℝ) : ∫ x, g (-(A * (x - lam))) = A⁻¹ • ∫ y, g y := by
  have h1 : ∫ x, g (-(A * (x - lam))) = ∫ x, g (-A * x) := by
    rw [← integral_sub_right_eq_self (fun x => g (-A * x)) lam]
    congr 1
    funext x
    congr 1
    ring
  rw [h1, Measure.integral_comp_mul_left g (-A), inv_neg, abs_neg, abs_of_pos (inv_pos.mpr hA)]

theorem integrable_comp_packet_arg {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {g : ℝ → F}
    (hg : Integrable g) {A : ℝ} (hA : 0 < A) (lam : ℝ) : Integrable (fun x => g (-(A * (x - lam)))) := by
  have h := (hg.comp_mul_left' (R := -A) (neg_ne_zero.mpr hA.ne')).comp_sub_right lam
  have e : (fun x => g (-(A * (x - lam)))) = fun t => g (-A * (t - lam)) := by
    funext x
    congr 1
    ring
  rw [e]
  exact h

/-- `∫ f = A⁻¹ ∫ f(l - u/A) du` -/
theorem integral_eq_smul_integral_comp (f : ℝ → ℂ) {A : ℝ} (hA : 0 < A) (l : ℝ) :
    ∫ y, f y = A⁻¹ • ∫ u, f (l - u / A) := by
  rw [← integral_comp_packet_arg (fun u => f (l - u / A)) hA l]
  congr 1
  funext x
  congr 1
  field_simp
  ring

/-! ### the weight `k` -/

theorem integrable_k_sq (w : HeightWeight) : Integrable (fun y => ‖w.k y‖ ^ 2) := by
  obtain ⟨M, _, hM⟩ := w.exists_k_bound
  refine Integrable.mono' (w.integrable_k.norm.const_mul M)
    ((w.continuous_k.norm.pow 2).aestronglyMeasurable) (Filter.Eventually.of_forall (fun y => ?_))
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), sq]
  exact mul_le_mul_of_nonneg_right (hM y) (norm_nonneg _)

theorem integral_norm_k_nonneg (w : HeightWeight) : 0 ≤ ∫ y, ‖w.k y‖ :=
  integral_nonneg (fun _ => norm_nonneg _)

/-! ### a single packet -/

theorem continuous_packet (w : HeightWeight) (T σ lam : ℝ) : Continuous (packet w.k T σ lam) := by
  unfold packet
  exact continuous_const.mul
    (w.continuous_k.comp ((continuous_const.mul (continuous_id.sub continuous_const)).neg))

theorem norm_packet (k : ℝ → ℂ) {T : ℝ} (hT : 0 ≤ T) (σ lam x : ℝ) :
    ‖packet k T σ lam x‖ = T * ‖k (-(Asc T σ * (x - lam)))‖ := by
  unfold packet
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hT]

theorem norm_packet_le (w : HeightWeight) {M : ℝ} (hM : ∀ y, ‖w.k y‖ ≤ M) {T : ℝ} (hT : 0 ≤ T)
    (σ lam x : ℝ) : ‖packet w.k T σ lam x‖ ≤ T * M := by
  rw [norm_packet _ hT]
  exact mul_le_mul_of_nonneg_left (hM _) hT

theorem packet_ne_zero_abs (w : HeightWeight) {T σ lam x : ℝ} (hA : 0 < Asc T σ)
    (h : packet w.k T σ lam x ≠ 0) : |x - lam| ≤ w.kappa / Asc T σ := by
  by_contra hc
  exact h (packet_eq_zero w hA (not_le.mp hc))

theorem integrable_norm_packet (w : HeightWeight) {T σ : ℝ} (hA : 0 < Asc T σ) (lam : ℝ) :
    Integrable (fun x => ‖packet w.k T σ lam x‖) := by
  have h : Integrable (packet w.k T σ lam) := by
    unfold packet
    exact (integrable_comp_packet_arg w.integrable_k hA lam).const_mul _
  exact h.norm

theorem integral_norm_packet (w : HeightWeight) {T σ : ℝ} (hT : 0 ≤ T) (hA : 0 < Asc T σ) (lam : ℝ) :
    ∫ x, ‖packet w.k T σ lam x‖ = T * (Asc T σ)⁻¹ * ∫ y, ‖w.k y‖ := by
  simp_rw [norm_packet _ hT]
  rw [integral_const_mul, integral_comp_packet_arg (fun y => ‖w.k y‖) hA lam, smul_eq_mul]
  ring

theorem integrable_norm_packet_sq (w : HeightWeight) {T σ : ℝ} (hT : 0 ≤ T) (hA : 0 < Asc T σ) (lam : ℝ) :
    Integrable (fun x => ‖packet w.k T σ lam x‖ ^ 2) := by
  have e : (fun x => ‖packet w.k T σ lam x‖ ^ 2)
      = fun x => T ^ 2 * (fun y => ‖w.k y‖ ^ 2) (-(Asc T σ * (x - lam))) := by
    funext x
    rw [norm_packet _ hT]
    ring
  rw [e]
  exact (integrable_comp_packet_arg (integrable_k_sq w) hA lam).const_mul _

theorem integral_norm_packet_sq (w : HeightWeight) {T σ : ℝ} (hT : 0 ≤ T) (hA : 0 < Asc T σ) (lam : ℝ) :
    ∫ x, ‖packet w.k T σ lam x‖ ^ 2 = T ^ 2 * (Asc T σ)⁻¹ * ∫ y, ‖w.k y‖ ^ 2 := by
  have e : ∀ x, ‖packet w.k T σ lam x‖ ^ 2
      = T ^ 2 * (fun y => ‖w.k y‖ ^ 2) (-(Asc T σ * (x - lam))) := by
    intro x
    rw [norm_packet _ hT]
    ring
  simp_rw [e]
  rw [integral_const_mul, integral_comp_packet_arg (fun y => ‖w.k y‖ ^ 2) hA lam, smul_eq_mul]
  ring

/-- the `L²` norm of a packet on `[-1,1]` -/
theorem intervalIntegral_norm_packet_sq_le (w : HeightWeight) {T σ : ℝ} (hT : 0 ≤ T) (hA : 0 < Asc T σ)
    (lam : ℝ) :
    ∫ x in (-1 : ℝ)..1, ‖packet w.k T σ lam x‖ ^ 2 ≤ T ^ 2 * (Asc T σ)⁻¹ * ∫ y, ‖w.k y‖ ^ 2 := by
  rw [← integral_norm_packet_sq w hT hA lam, intervalIntegral.integral_of_le (by norm_num)]
  exact setIntegral_le_integral (integrable_norm_packet_sq w hT hA lam)
    (Filter.Eventually.of_forall (fun x => by positivity))

/-! ### packet triples -/

/-- **Closure.** A packet triple vanishes unless the centres nearly add up to zero. -/
theorem tri_packet_eq_zero (w : HeightWeight) {T σ l1 l2 l3 : ℝ} (hA : 0 < Asc T σ)
    (h : 3 * w.kappa / Asc T σ < |l1 + l2 + l3|) :
    tri (packet w.k T σ l1) (packet w.k T σ l2) (packet w.k T σ l3) = 0 := by
  have h0 : ∀ x y : ℝ,
      packet w.k T σ l1 x * packet w.k T σ l2 y * packet w.k T σ l3 (-x - y) = 0 := by
    intro x y
    by_contra hne
    have h1 : packet w.k T σ l1 x ≠ 0 := fun h' => hne (by rw [h']; ring)
    have h2 : packet w.k T σ l2 y ≠ 0 := fun h' => hne (by rw [h']; ring)
    have h3 : packet w.k T σ l3 (-x - y) ≠ 0 := fun h' => hne (by rw [h']; ring)
    have a1 := packet_ne_zero_abs w hA h1
    have a2 := packet_ne_zero_abs w hA h2
    have a3 := packet_ne_zero_abs w hA h3
    have hle : |l1 + l2 + l3| ≤ 3 * w.kappa / Asc T σ := by
      have e : l1 + l2 + l3 = -((x - l1) + (y - l2) + (-x - y - l3)) := by ring
      have e' : 3 * w.kappa / Asc T σ
          = w.kappa / Asc T σ + w.kappa / Asc T σ + w.kappa / Asc T σ := by ring
      rw [e, abs_neg, e']
      exact (abs_add_three _ _ _).trans (by linarith)
    linarith
  unfold tri
  simp [h0]

/-- **Size.** -/
theorem norm_tri_packet_le (w : HeightWeight) {M : ℝ} (hM : ∀ y, ‖w.k y‖ ≤ M) {T σ : ℝ}
    (hT : 0 ≤ T) (hA : 0 < Asc T σ) (l1 l2 l3 : ℝ) :
    ‖tri (packet w.k T σ l1) (packet w.k T σ l2) (packet w.k T σ l3)‖
      ≤ 2 * T ^ 3 * M * (∫ y, ‖w.k y‖) ^ 2 / Asc T σ ^ 2 := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  set Ik : ℝ := ∫ y, ‖w.k y‖ with hIk
  set c : ℝ := 2 * (T * M) * (T * (Asc T σ)⁻¹ * Ik) with hc
  rw [tri_eq_integral_integral]
  have hin : ∀ x : ℝ,
      ‖∫ y, triF (packet w.k T σ l1) (packet w.k T σ l2) (packet w.k T σ l3) (x, y)‖
        ≤ ‖packet w.k T σ l1 x‖ * c := by
    intro x
    have hg : Integrable (fun y => 2 * (‖packet w.k T σ l1 x‖ * (T * M)) * ‖packet w.k T σ l2 y‖) :=
      (integrable_norm_packet w hA l2).const_mul _
    calc ‖∫ y, triF (packet w.k T σ l1) (packet w.k T σ l2) (packet w.k T σ l3) (x, y)‖
        ≤ ∫ y, ‖triF (packet w.k T σ l1) (packet w.k T σ l2) (packet w.k T σ l3) (x, y)‖ :=
          norm_integral_le_integral_norm _
      _ ≤ ∫ y, 2 * (‖packet w.k T σ l1 x‖ * (T * M)) * ‖packet w.k T σ l2 y‖ := by
          apply integral_mono_of_nonneg (Filter.Eventually.of_forall (fun y => norm_nonneg _)) hg
          apply Filter.Eventually.of_forall
          intro y
          have h1 := norm_triF_le (packet w.k T σ l1) (packet w.k T σ l2) (packet w.k T σ l3) (x, y)
          have h2 := norm_packet_le w hM hT σ l3 (-x - y)
          have h3 : 0 ≤ ‖packet w.k T σ l1 x‖ * ‖packet w.k T σ l2 y‖ := by positivity
          have h4 := mul_le_mul_of_nonneg_left h2 h3
          simp only at h1
          show ‖triF (packet w.k T σ l1) (packet w.k T σ l2) (packet w.k T σ l3) (x, y)‖
            ≤ 2 * (‖packet w.k T σ l1 x‖ * (T * M)) * ‖packet w.k T σ l2 y‖
          linarith [h1, h4]
      _ = ‖packet w.k T σ l1 x‖ * c := by
          rw [integral_const_mul, integral_norm_packet w hT hA l2, hc]
          ring
  calc ‖∫ x, ∫ y, triF (packet w.k T σ l1) (packet w.k T σ l2) (packet w.k T σ l3) (x, y)‖
      ≤ ∫ x, ‖∫ y, triF (packet w.k T σ l1) (packet w.k T σ l2) (packet w.k T σ l3) (x, y)‖ :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ x, ‖packet w.k T σ l1 x‖ * c := by
        apply integral_mono_of_nonneg (Filter.Eventually.of_forall (fun y => norm_nonneg _))
          ((integrable_norm_packet w hA l1).mul_const _)
        exact Filter.Eventually.of_forall hin
    _ = 2 * T ^ 3 * M * Ik ^ 2 / Asc T σ ^ 2 := by
        rw [integral_mul_const, integral_norm_packet w hT hA l1, hc, ← hIk]
        field_simp

/-- **Evaluation.** If the centres add up to zero, the packet triple is
`(T³/A²) · Gg l1 l2 · (1/2π) ∫ h³` up to `(T³/A²) · O(κ/A)`. -/
theorem tri_packet_eval (w : HeightWeight) {M : ℝ} (hM : ∀ y, ‖w.k y‖ ≤ M) {T σ : ℝ}
    (hA : 0 < Asc T σ) {l1 l2 l3 : ℝ} (h : l1 + l2 + l3 = 0) :
    ‖tri (packet w.k T σ l1) (packet w.k T σ l2) (packet w.k T σ l3)
        - ((T ^ 3 / Asc T σ ^ 2 * (Gg l1 l2 * ((1 / (2 * π)) * w.kap3)) : ℝ) : ℂ)‖
      ≤ |T| ^ 3 / Asc T σ ^ 2 * (10 * (2 * w.kappa / Asc T σ) * M * (∫ y, ‖w.k y‖) ^ 2) := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  have hκ := w.kappa_pos
  set A : ℝ := Asc T σ with hAdef
  have hA' : A ≠ 0 := hA.ne'
  set Ik : ℝ := ∫ y, ‖w.k y‖ with hIk
  set P1 := packet w.k T σ l1 with hP1
  set P2 := packet w.k T σ l2 with hP2
  set P3 := packet w.k T σ l3 with hP3
  -- the two integrands in the scaled variables
  set K3 : ℝ × ℝ → ℂ := fun p => w.k p.1 * w.k p.2 * w.k (-p.1 - p.2) with hK3
  set H : ℝ × ℝ → ℂ := fun p => (Gg (l1 - p.1 / A) (l2 - p.2 / A) : ℂ) * K3 p with hH
  have hK3c : Continuous K3 :=
    ((w.continuous_k.comp continuous_fst).mul (w.continuous_k.comp continuous_snd)).mul
      (w.continuous_k.comp (continuous_fst.neg.sub continuous_snd))
  have hK30 : ∀ p : ℝ × ℝ, ¬ (|p.1| ≤ w.kappa ∧ |p.2| ≤ w.kappa) → K3 p = 0 := by
    intro p hp
    by_contra hne
    apply hp
    constructor
    · apply w.k_supp
      intro h0
      exact hne (by simp [hK3, h0])
    · apply w.k_supp
      intro h0
      exact hne (by simp [hK3, h0])
  have hK3i : Integrable K3 := integrable_of_continuous_of_square hK3c w.kappa hK30
  have hHc : Continuous H := by
    have hG : Continuous (fun p : ℝ × ℝ => (Gg (l1 - p.1 / A) (l2 - p.2 / A) : ℂ)) :=
      Complex.continuous_ofReal.comp (continuous_Gg.comp
        ((continuous_const.sub (continuous_fst.div_const A)).prodMk
          (continuous_const.sub (continuous_snd.div_const A))))
    exact hG.mul hK3c
  have hHi : Integrable H :=
    integrable_of_continuous_of_square hHc w.kappa (fun p hp => by simp [hH, hK30 p hp])
  -- the packet triple in the scaled variables
  have hpt : ∀ y1 y2 : ℝ, triF P1 P2 P3 (l1 - y1 / A, l2 - y2 / A) = (T : ℂ) ^ 3 * H (y1, y2) := by
    intro y1 y2
    have e1 : -(A * (l1 - y1 / A - l1)) = y1 := by
      field_simp
      ring
    have e2 : -(A * (l2 - y2 / A - l2)) = y2 := by
      field_simp
      ring
    have e3 : -(A * (-(l1 - y1 / A) - (l2 - y2 / A) - l3)) = -y1 - y2 := by
      have hl3 : l3 = -l1 - l2 := by linarith
      rw [hl3]
      field_simp
      ring
    simp only [triF, hP1, hP2, hP3, packet, hH, hK3]
    rw [← hAdef, e1, e2, e3]
    ring
  have hstep : tri P1 P2 P3 = ((T : ℂ) ^ 3 * ((A⁻¹ : ℝ) : ℂ) ^ 2) * ∫ p, H p := by
    rw [tri_eq_integral_integral]
    have hinner : ∀ x : ℝ, ∫ y, triF P1 P2 P3 (x, y) = A⁻¹ • ∫ y2, triF P1 P2 P3 (x, l2 - y2 / A) :=
      fun x => integral_eq_smul_integral_comp (fun y => triF P1 P2 P3 (x, y)) hA l2
    simp_rw [hinner]
    rw [integral_eq_smul_integral_comp (fun x => A⁻¹ • ∫ y2, triF P1 P2 P3 (x, l2 - y2 / A)) hA l1]
    simp only [hpt]
    have hprod : ∫ p, H p = ∫ x, ∫ y, H (x, y) := integral_prod H hHi
    rw [hprod]
    simp only [integral_const_mul, Complex.real_smul]
    ring
  have hmain : ((T ^ 3 / A ^ 2 * (Gg l1 l2 * ((1 / (2 * π)) * w.kap3)) : ℝ) : ℂ)
      = ((T : ℂ) ^ 3 * ((A⁻¹ : ℝ) : ℂ) ^ 2) * ∫ p, (Gg l1 l2 : ℂ) * K3 p := by
    have hprod : ∫ p, K3 p = ∫ x, ∫ y, K3 (x, y) := integral_prod K3 hK3i
    rw [integral_const_mul, hprod]
    have hinv := w.inv3
    simp only [hK3]
    rw [hinv]
    unfold HeightWeight.kap3
    push_cast
    field_simp
  rw [hstep, hmain, ← mul_sub, ← integral_sub hHi (hK3i.const_mul _), norm_mul]
  have hnorm : ‖(T : ℂ) ^ 3 * ((A⁻¹ : ℝ) : ℂ) ^ 2‖ = |T| ^ 3 / A ^ 2 := by
    rw [norm_mul, norm_pow, norm_pow, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hA)]
    field_simp
  rw [hnorm]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  set c : ℝ := 10 * (2 * w.kappa / A) * M with hc
  have hgi : Integrable (fun p : ℝ × ℝ => c * (‖w.k p.1‖ * ‖w.k p.2‖)) :=
    (w.integrable_k.norm.mul_prod w.integrable_k.norm).const_mul c
  calc ‖∫ p, (H p - (Gg l1 l2 : ℂ) * K3 p)‖ ≤ ∫ p, ‖H p - (Gg l1 l2 : ℂ) * K3 p‖ :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ p : ℝ × ℝ, c * (‖w.k p.1‖ * ‖w.k p.2‖) := by
        apply integral_mono_of_nonneg (Filter.Eventually.of_forall (fun y => norm_nonneg _)) hgi
        apply Filter.Eventually.of_forall
        intro p
        show ‖H p - (Gg l1 l2 : ℂ) * K3 p‖ ≤ c * (‖w.k p.1‖ * ‖w.k p.2‖)
        by_cases hp : |p.1| ≤ w.kappa ∧ |p.2| ≤ w.kappa
        · have e : H p - (Gg l1 l2 : ℂ) * K3 p
              = ((Gg (l1 - p.1 / A) (l2 - p.2 / A) - Gg l1 l2 : ℝ) : ℂ) * K3 p := by
            simp only [hH]
            push_cast
            ring
          rw [e, norm_mul, Complex.norm_real, Real.norm_eq_abs]
          have hl := Gg_lipschitz (l1 - p.1 / A) (l2 - p.2 / A) l1 l2
          have e1 : l1 - p.1 / A - l1 = -(p.1 / A) := by ring
          have e2 : l2 - p.2 / A - l2 = -(p.2 / A) := by ring
          rw [e1, e2, abs_neg, abs_neg, abs_div, abs_div, abs_of_pos hA] at hl
          have hl1 : |p.1| / A ≤ w.kappa / A := div_le_div_of_nonneg_right hp.1 hA.le
          have hl2 : |p.2| / A ≤ w.kappa / A := div_le_div_of_nonneg_right hp.2 hA.le
          have hG : |Gg (l1 - p.1 / A) (l2 - p.2 / A) - Gg l1 l2| ≤ 10 * (2 * w.kappa / A) := by
            have e3 : 2 * w.kappa / A = w.kappa / A + w.kappa / A := by ring
            rw [e3]
            linarith
          have hK : ‖K3 p‖ ≤ M * (‖w.k p.1‖ * ‖w.k p.2‖) := by
            simp only [hK3]
            rw [norm_mul, norm_mul]
            have := hM (-p.1 - p.2)
            have h0 : 0 ≤ ‖w.k p.1‖ * ‖w.k p.2‖ := by positivity
            linarith [mul_le_mul_of_nonneg_left this h0]
          calc |Gg (l1 - p.1 / A) (l2 - p.2 / A) - Gg l1 l2| * ‖K3 p‖
              ≤ 10 * (2 * w.kappa / A) * (M * (‖w.k p.1‖ * ‖w.k p.2‖)) :=
                mul_le_mul hG hK (norm_nonneg _) (by positivity)
            _ = c * (‖w.k p.1‖ * ‖w.k p.2‖) := by
                rw [hc]
                ring
        · have h0 : H p - (Gg l1 l2 : ℂ) * K3 p = 0 := by simp [hH, hK30 p hp]
          rw [h0, norm_zero]
          positivity
    _ = 10 * (2 * w.kappa / A) * M * Ik ^ 2 := by
        have hprod : ∫ p : ℝ × ℝ, ‖w.k p.1‖ * ‖w.k p.2‖ = Ik * Ik :=
          integral_prod_mul (fun y : ℝ => ‖w.k y‖) (fun y : ℝ => ‖w.k y‖)
        rw [integral_const_mul, hprod, hc]
        ring

end TMA.T3
end
end Src_TMA_Trace3Aux2

section Src_TMA_Trace3Aux3
/-
Written for Kristian Muri Knausgård, drafted with Claude (Anthropic), 22 November 2026.

TMA/Trace3Aux3.lean — the structure of the prime-side kernel and the error term of the third trace:
* `K0 = ell · packet 0 - Qk`, with `Qk` a sum of packets over the signed index set `idx`;
* the "T large" bundle `Sep` and the separation of the centres in logarithmic form (one, two and three
  prime packets);
* `∫_{-1}^{1} ‖K0‖² ≤ C T log T` (disjoint supports);
* `‖t3 Kfull - t3 K0‖ ≤ C T`.
See BLUEPRINT.md, module "T3".
-/

open MeasureTheory Complex
open scoped BigOperators ArithmeticFunction Real

noncomputable section
namespace TMA.T3

/-! ### signed index set -/

/-- sign of a Boolean -/
def sgn : Bool → ℝ
  | true => 1
  | false => -1

@[simp] theorem sgn_true : sgn true = 1 := rfl
@[simp] theorem sgn_false : sgn false = -1 := rfl
theorem sgn_not (b : Bool) : sgn (!b) = -sgn b := by cases b <;> simp

/-- centre of the prime packet with index `p = (n, sign)` -/
def cen (T σ : ℝ) (p : ℕ × Bool) : ℝ := sgn p.2 * lamOf T σ p.1

/-- the index with the opposite sign -/
def bar (p : ℕ × Bool) : ℕ × Bool := (p.1, !p.2)

/-- index set of the prime packets of `K0` -/
def idx (T σ : ℝ) : Finset (ℕ × Bool) := Finset.Icc 2 (Nmax T σ) ×ˢ Finset.univ

/-- the prime part of `K0` -/
def Qk (k : ℝ → ℂ) (T σ : ℝ) (x : ℝ) : ℂ :=
  ∑ p ∈ idx T σ, (lamCoeff p.1 : ℂ) * packet k T σ (cen T σ p) x

theorem mem_idx {T σ : ℝ} {p : ℕ × Bool} : p ∈ idx T σ ↔ 2 ≤ p.1 ∧ p.1 ≤ Nmax T σ := by
  simp [idx]

theorem bar_mem {T σ : ℝ} {p : ℕ × Bool} (hp : p ∈ idx T σ) : bar p ∈ idx T σ := by
  rw [mem_idx] at hp ⊢
  exact hp

theorem cen_bar (T σ : ℝ) (p : ℕ × Bool) : cen T σ (bar p) = -cen T σ p := by
  simp only [cen, bar, sgn_not]
  ring

theorem cen_eq (T σ : ℝ) (p : ℕ × Bool) :
    cen T σ p = sgn p.2 * Real.log p.1 / (σ * Real.log T) := by
  simp only [cen, lamOf]
  ring

/-- a sum over the signed index set -/
theorem sum_idx {M : Type*} [AddCommMonoid M] (T σ : ℝ) (f : ℕ × Bool → M) :
    ∑ p ∈ idx T σ, f p = ∑ n ∈ Finset.Icc 2 (Nmax T σ), (f (n, true) + f (n, false)) := by
  unfold idx
  rw [Finset.sum_product]
  refine Finset.sum_congr rfl (fun n _ => ?_)
  rw [Fintype.sum_bool]

theorem K0_eq (k : ℝ → ℂ) (T σ : ℝ) :
    K0 k T σ = fun x => (Real.log (T / (2 * π)) : ℂ) * packet k T σ 0 x - Qk k T σ x := by
  funext x
  unfold K0 Qk
  rw [sum_idx]
  congr 1
  refine Finset.sum_congr rfl (fun n _ => ?_)
  simp only [cen, sgn_true, sgn_false, one_mul, neg_mul]
  ring

theorem continuous_Qk (w : HeightWeight) (T σ : ℝ) : Continuous (Qk w.k T σ) := by
  unfold Qk
  exact continuous_finsetSum _ (fun p _ => continuous_const.mul (continuous_packet w T σ _))

theorem lamCoeff_nonneg (n : ℕ) : 0 ≤ lamCoeff n := by
  unfold lamCoeff
  exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _)

theorem lamCoeff_sq (n : ℕ) : lamCoeff n ^ 2 = Λ n ^ 2 / n := by
  unfold lamCoeff
  rw [div_pow, Real.sq_sqrt (Nat.cast_nonneg n)]

/-! ### the "T large" bundle -/

/-- the properties of a large `T` used throughout (from `separation`, plus `T ≥ 2π`) -/
structure Sep (w : HeightWeight) (T σ : ℝ) : Prop where
  two_pi_le : 2 * π ≤ T
  A_pos : 0 < Asc T σ
  small : 3 * w.kappa / T < Real.log 2
  sep : ∀ n n' : ℕ, 1 ≤ n → 1 ≤ n' → (n : ℝ) ≤ 4 * T ^ σ → (n' : ℝ) ≤ 4 * T ^ σ → n ≠ n' →
    3 * w.kappa / T < |Real.log n - Real.log n'|

theorem sep_eventually (w : HeightWeight) {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ < 1) :
    ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T → Sep w T σ := by
  obtain ⟨T₀, h⟩ := separation w hσ hσ1
  refine ⟨max T₀ (2 * π), fun T hT => ?_⟩
  obtain ⟨_, h2, h3, _, h5⟩ := h T ((le_max_left _ _).trans hT)
  exact ⟨(le_max_right _ _).trans hT, h2, h3, h5⟩

namespace Sep

variable {w : HeightWeight} {T σ : ℝ}

theorem six_le (hS : Sep w T σ) : 6 ≤ T := by
  have := hS.two_pi_le
  have := Real.pi_gt_three
  linarith

theorem T_pos (hS : Sep w T σ) : 0 < T := by
  have := hS.six_le
  linarith

theorem one_le_log (hS : Sep w T σ) : 1 ≤ Real.log T := by
  rw [Real.le_log_iff_exp_le hS.T_pos]
  have := Real.exp_one_lt_d9
  have := hS.six_le
  linarith

theorem log_pos (hS : Sep w T σ) : 0 < Real.log T := by
  have := hS.one_le_log
  linarith

theorem ell_nonneg (hS : Sep w T σ) : 0 ≤ Real.log (T / (2 * π)) := by
  apply Real.log_nonneg
  rw [le_div_iff₀ (by positivity)]
  linarith [hS.two_pi_le]

theorem ell_le (hS : Sep w T σ) : Real.log (T / (2 * π)) ≤ Real.log T := by
  apply Real.log_le_log (div_pos hS.T_pos (by positivity))
  rw [div_le_iff₀ (by positivity)]
  have h1 : (1 : ℝ) ≤ 2 * π := by linarith [Real.pi_gt_three]
  exact le_mul_of_one_le_right hS.T_pos.le h1

theorem small_nonneg (hS : Sep w T σ) : 0 ≤ 3 * w.kappa / T :=
  div_nonneg (by linarith [w.kappa_pos]) hS.T_pos.le

theorem rpow_ge_one (hS : Sep w T σ) (hσ : 0 < σ) : 1 ≤ T ^ σ :=
  Real.one_le_rpow (by linarith [hS.six_le]) hσ.le

end Sep

theorem cast_le_of_le_Nmax {T σ : ℝ} (hT : 0 ≤ T) {n : ℕ} (h : n ≤ Nmax T σ) :
    (n : ℝ) ≤ 2 * T ^ σ := by
  have h0 : (0 : ℝ) ≤ 2 * T ^ σ := mul_nonneg (by norm_num) (Real.rpow_nonneg hT σ)
  exact (Nat.le_floor_iff h0).mp h

theorem log_two_le_log_cast {n : ℕ} (h : 2 ≤ n) : Real.log 2 ≤ Real.log n :=
  Real.log_le_log (by norm_num) (by exact_mod_cast h)

/-- scaling between the logarithmic variable and the centres -/
theorem scale_lt {T σ : ℝ} (hT : 0 < T) (hL : 0 < σ * Real.log T) (c a : ℝ) (h : c / T < |a|) :
    c / Asc T σ < |a / (σ * Real.log T)| := by
  have e : c / Asc T σ = c / T / (σ * Real.log T) := by
    unfold Asc
    field_simp
  rw [e, abs_div, abs_of_pos hL]
  exact (div_lt_div_iff_of_pos_right hL).mpr h

/-- **Closure in logarithmic form.** -/
theorem tri_packet_eq_zero_log (w : HeightWeight) {T σ : ℝ} (hσ : 0 < σ) (hS : Sep w T σ)
    {l1 l2 l3 a : ℝ} (hl : l1 + l2 + l3 = a / (σ * Real.log T)) (ha : 3 * w.kappa / T < |a|) :
    tri (packet w.k T σ l1) (packet w.k T σ l2) (packet w.k T σ l3) = 0 := by
  apply tri_packet_eq_zero w hS.A_pos
  rw [hl]
  exact scale_lt hS.T_pos (mul_pos hσ hS.log_pos) _ _ ha

/-! ### separation of one, two and three prime packets -/

section separation
variable {w : HeightWeight} {T σ : ℝ}

theorem single_sep (hS : Sep w T σ) {a : ℕ} (ha : 2 ≤ a) (sa : Bool) :
    3 * w.kappa / T < |sgn sa * Real.log a| := by
  have h1 := log_two_le_log_cast ha
  have h2 := hS.small
  cases sa
  · rw [sgn_false, neg_one_mul, abs_neg]
    exact lt_of_lt_of_le (by linarith) (le_abs_self _)
  · rw [sgn_true, one_mul]
    exact lt_of_lt_of_le (by linarith) (le_abs_self _)

theorem pair_core (hS : Sep w T σ) {a b : ℕ} (ha : 2 ≤ a) (ha' : a ≤ Nmax T σ)
    (hb : 2 ≤ b) (hb' : b ≤ Nmax T σ)
    (h : |Real.log a - Real.log b| ≤ 3 * w.kappa / T) : a = b := by
  by_contra hne
  have hT := hS.T_pos
  have h0 : (0 : ℝ) ≤ T ^ σ := Real.rpow_nonneg hT.le σ
  have h1 := hS.sep a b (by omega) (by omega)
    (by linarith [cast_le_of_le_Nmax hT.le ha']) (by linarith [cast_le_of_le_Nmax hT.le hb']) hne
  linarith

theorem pair_cases (hS : Sep w T σ) {a b : ℕ} (ha : 2 ≤ a) (ha' : a ≤ Nmax T σ)
    (hb : 2 ≤ b) (hb' : b ≤ Nmax T σ) (sa sb : Bool)
    (h : |sgn sa * Real.log a + sgn sb * Real.log b| ≤ 3 * w.kappa / T) : sb = (!sa) ∧ a = b := by
  have h1 := log_two_le_log_cast ha
  have h2 := log_two_le_log_cast hb
  have h3 := hS.small
  have h4 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  cases sa <;> cases sb
  · exfalso
    rw [sgn_false] at h
    have := (abs_le.mp h).1
    linarith
  · refine ⟨rfl, pair_core hS ha ha' hb hb' ?_⟩
    rw [sgn_false, sgn_true] at h
    have e : Real.log a - Real.log b = -(-1 * Real.log a + 1 * Real.log b) := by ring
    rw [e, abs_neg]
    exact h
  · refine ⟨rfl, pair_core hS ha ha' hb hb' ?_⟩
    rw [sgn_false, sgn_true] at h
    have e : Real.log a - Real.log b = 1 * Real.log a + -1 * Real.log b := by ring
    rw [e]
    exact h
  · exfalso
    rw [sgn_true] at h
    have := (abs_le.mp h).2
    linarith

theorem triple_core (hS : Sep w T σ) {a b c : ℕ} (ha : 2 ≤ a) (hb : 2 ≤ b)
    (hc : 2 ≤ c) (hc' : c ≤ Nmax T σ)
    (h : |Real.log a + Real.log b - Real.log c| ≤ 3 * w.kappa / T) : a * b = c := by
  by_contra hne
  have hT := hS.T_pos
  have h0 : (0 : ℝ) ≤ T ^ σ := Real.rpow_nonneg hT.le σ
  have hcc := cast_le_of_le_Nmax (σ := σ) hT.le hc'
  have ha0 : (a : ℝ) ≠ 0 := by
    have : (2 : ℝ) ≤ a := by exact_mod_cast ha
    linarith
  have hb0 : (b : ℝ) ≠ 0 := by
    have : (2 : ℝ) ≤ b := by exact_mod_cast hb
    linarith
  have hc0 : (0 : ℝ) < c := by
    have : (2 : ℝ) ≤ c := by exact_mod_cast hc
    linarith
  have hlog : Real.log ((a * b : ℕ) : ℝ) = Real.log a + Real.log b := by
    rw [Nat.cast_mul, Real.log_mul ha0 hb0]
  by_cases hab : ((a * b : ℕ) : ℝ) ≤ 4 * T ^ σ
  · have h1 := hS.sep (a * b) c (Nat.one_le_iff_ne_zero.mpr (by positivity)) (by omega) hab
      (by linarith) hne
    rw [hlog] at h1
    linarith
  · have hab' : 2 * (c : ℝ) < ((a * b : ℕ) : ℝ) := by
      have := not_le.mp hab
      linarith
    have h1 := Real.log_lt_log (by linarith) hab'
    rw [hlog, Real.log_mul (by norm_num) hc0.ne'] at h1
    have h2 := (abs_le.mp h).2
    linarith [hS.small]

theorem triple_cases (hS : Sep w T σ) {a b c : ℕ} (ha : 2 ≤ a) (ha' : a ≤ Nmax T σ)
    (hb : 2 ≤ b) (hb' : b ≤ Nmax T σ) (hc : 2 ≤ c) (hc' : c ≤ Nmax T σ) (sa sb sc : Bool)
    (h : |sgn sa * Real.log a + sgn sb * Real.log b + sgn sc * Real.log c| ≤ 3 * w.kappa / T) :
    a * b = c ∨ a * c = b ∨ b * c = a := by
  have h1 := log_two_le_log_cast ha
  have h2 := log_two_le_log_cast hb
  have h3 := log_two_le_log_cast hc
  have h4 := hS.small
  have h5 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  cases sa <;> cases sb <;> cases sc <;> simp only [sgn_true, sgn_false] at h
  · exfalso
    have := (abs_le.mp h).1
    linarith
  · -- (-,-,+)
    left
    apply triple_core hS ha hb hc hc'
    have e : Real.log a + Real.log b - Real.log c
        = -(-1 * Real.log a + -1 * Real.log b + 1 * Real.log c) := by ring
    rw [e, abs_neg]
    exact h
  · -- (-,+,-)
    right; left
    apply triple_core hS ha hc hb hb'
    have e : Real.log a + Real.log c - Real.log b
        = -(-1 * Real.log a + 1 * Real.log b + -1 * Real.log c) := by ring
    rw [e, abs_neg]
    exact h
  · -- (-,+,+)
    right; right
    apply triple_core hS hb hc ha ha'
    have e : Real.log b + Real.log c - Real.log a
        = -1 * Real.log a + 1 * Real.log b + 1 * Real.log c := by ring
    rw [e]
    exact h
  · -- (+,-,-)
    right; right
    apply triple_core hS hb hc ha ha'
    have e : Real.log b + Real.log c - Real.log a
        = -(1 * Real.log a + -1 * Real.log b + -1 * Real.log c) := by ring
    rw [e, abs_neg]
    exact h
  · -- (+,-,+)
    right; left
    apply triple_core hS ha hc hb hb'
    have e : Real.log a + Real.log c - Real.log b
        = 1 * Real.log a + -1 * Real.log b + 1 * Real.log c := by ring
    rw [e]
    exact h
  · -- (+,+,-)
    left
    apply triple_core hS ha hb hc hc'
    have e : Real.log a + Real.log b - Real.log c
        = 1 * Real.log a + 1 * Real.log b + -1 * Real.log c := by ring
    rw [e]
    exact h
  · exfalso
    have := (abs_le.mp h).2
    linarith

end separation

/-! ### disjointness of the packets of `K0` and its `L²` norm -/

theorem norm_sq_sum_le_of_disjoint {ι : Type*} (s : Finset ι) (f : ι → ℂ)
    (h : ∀ i ∈ s, ∀ j ∈ s, f i ≠ 0 → f j ≠ 0 → i = j) :
    ‖∑ i ∈ s, f i‖ ^ 2 ≤ ∑ i ∈ s, ‖f i‖ ^ 2 := by
  by_cases h0 : ∀ i ∈ s, f i = 0
  · rw [Finset.sum_eq_zero h0, norm_zero]
    have : (0 : ℝ) ^ 2 = 0 := by norm_num
    rw [this]
    exact Finset.sum_nonneg (fun i _ => by positivity)
  · simp only [not_forall] at h0
    obtain ⟨i, hi, hfi⟩ := h0
    rw [Finset.sum_eq_single_of_mem i hi (fun j hj hji => by
      by_contra hne
      exact hji (h j hj i hi hne hfi))]
    exact Finset.single_le_sum (f := fun i => ‖f i‖ ^ 2) (fun i _ => by positivity) hi

section disjoint
variable {w : HeightWeight} {T σ : ℝ}

/-- two prime packets that are both nonzero at a point coincide -/
theorem idx_eq_of_packets (hσ : 0 < σ) (hS : Sep w T σ) {p q : ℕ × Bool} (hp : p ∈ idx T σ)
    (hq : q ∈ idx T σ) {x : ℝ} (h1 : packet w.k T σ (cen T σ p) x ≠ 0)
    (h2 : packet w.k T σ (cen T σ q) x ≠ 0) : p = q := by
  have a1 := packet_ne_zero_abs w hS.A_pos h1
  have a2 := packet_ne_zero_abs w hS.A_pos h2
  have hL : 0 < σ * Real.log T := mul_pos hσ hS.log_pos
  have hκ := w.kappa_pos
  rw [mem_idx] at hp hq
  have key : |sgn p.2 * Real.log p.1 + sgn (!q.2) * Real.log q.1| ≤ 3 * w.kappa / T := by
    by_contra hc
    have h3 := scale_lt hS.T_pos hL _ _ (not_le.mp hc)
    have e : (sgn p.2 * Real.log p.1 + sgn (!q.2) * Real.log q.1) / (σ * Real.log T)
        = -((x - cen T σ p) - (x - cen T σ q)) := by
      rw [cen_eq, cen_eq, sgn_not]
      field_simp
      ring
    rw [e, abs_neg] at h3
    have h4 : |(x - cen T σ p) - (x - cen T σ q)| ≤ w.kappa / Asc T σ + w.kappa / Asc T σ :=
      (abs_sub _ _).trans (add_le_add a1 a2)
    have h5 : w.kappa / Asc T σ + w.kappa / Asc T σ ≤ 3 * w.kappa / Asc T σ := by
      rw [← add_div]
      exact div_le_div_of_nonneg_right (by linarith) hS.A_pos.le
    linarith
  obtain ⟨hs, hn⟩ := pair_cases hS hp.1 hp.2 hq.1 hq.2 p.2 (!q.2) key
  have hs' : q.2 = p.2 := by
    cases hq2 : q.2 <;> cases hp2 : p.2 <;> simp_all
  exact Prod.ext hn hs'.symm

/-- the central packet and a prime packet are not both nonzero at a point -/
theorem packet_cen_eq_zero_of_zero (hσ : 0 < σ) (hS : Sep w T σ) {p : ℕ × Bool} (hp : p ∈ idx T σ)
    {x : ℝ} (h0 : packet w.k T σ 0 x ≠ 0) : packet w.k T σ (cen T σ p) x = 0 := by
  by_contra h1
  have a0 := packet_ne_zero_abs w hS.A_pos h0
  have a1 := packet_ne_zero_abs w hS.A_pos h1
  have hL : 0 < σ * Real.log T := mul_pos hσ hS.log_pos
  have hκ := w.kappa_pos
  rw [mem_idx] at hp
  have h3 := scale_lt hS.T_pos hL _ _ (single_sep hS hp.1 p.2)
  have e : sgn p.2 * Real.log p.1 / (σ * Real.log T) = (x - 0) - (x - cen T σ p) := by
    rw [cen_eq]
    ring
  rw [e] at h3
  have h4 : |(x - 0) - (x - cen T σ p)| ≤ w.kappa / Asc T σ + w.kappa / Asc T σ :=
    (abs_sub _ _).trans (add_le_add a0 a1)
  have h5 : w.kappa / Asc T σ + w.kappa / Asc T σ ≤ 3 * w.kappa / Asc T σ := by
    rw [← add_div]
    exact div_le_div_of_nonneg_right (by linarith) hS.A_pos.le
  linarith

theorem norm_sq_Qk_le (hσ : 0 < σ) (hS : Sep w T σ) (x : ℝ) :
    ‖Qk w.k T σ x‖ ^ 2 ≤ ∑ p ∈ idx T σ, lamCoeff p.1 ^ 2 * ‖packet w.k T σ (cen T σ p) x‖ ^ 2 := by
  unfold Qk
  refine (norm_sq_sum_le_of_disjoint _ _ ?_).trans (le_of_eq ?_)
  · intro p hp q hq hfp hfq
    exact idx_eq_of_packets hσ hS hp hq (right_ne_zero_of_mul hfp) (right_ne_zero_of_mul hfq)
  · refine Finset.sum_congr rfl (fun p _ => ?_)
    rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]

theorem norm_sq_K0_le (hσ : 0 < σ) (hS : Sep w T σ) (x : ℝ) :
    ‖K0 w.k T σ x‖ ^ 2 ≤ Real.log (T / (2 * π)) ^ 2 * ‖packet w.k T σ 0 x‖ ^ 2
      + ∑ p ∈ idx T σ, lamCoeff p.1 ^ 2 * ‖packet w.k T σ (cen T σ p) x‖ ^ 2 := by
  rw [K0_eq]
  have hQ := norm_sq_Qk_le hσ hS x
  have hsum : 0 ≤ ∑ p ∈ idx T σ, lamCoeff p.1 ^ 2 * ‖packet w.k T σ (cen T σ p) x‖ ^ 2 :=
    Finset.sum_nonneg (fun p _ => by positivity)
  by_cases h0 : packet w.k T σ 0 x = 0
  · simp only [h0, mul_zero, zero_sub, norm_neg, norm_zero]
    have : (0 : ℝ) ^ 2 = 0 := by norm_num
    rw [this, mul_zero, zero_add]
    exact hQ
  · have hQ0 : Qk w.k T σ x = 0 := by
      unfold Qk
      refine Finset.sum_eq_zero (fun p hp => ?_)
      rw [packet_cen_eq_zero_of_zero hσ hS hp h0, mul_zero]
    simp only [hQ0, sub_zero]
    rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    linarith

end disjoint

/-- `Σ_{p ∈ idx} lamCoeff² = 2 Σ_{2 ≤ n ≤ Nmax} Λ(n)²/n` -/
theorem sum_idx_lamCoeff_sq (T σ : ℝ) :
    ∑ p ∈ idx T σ, lamCoeff p.1 ^ 2 = 2 * ∑ n ∈ Finset.Icc 2 (Nmax T σ), Λ n ^ 2 / n := by
  rw [sum_idx, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun n _ => ?_)
  rw [lamCoeff_sq]
  ring

/-- `Σ_{2 ≤ n ≤ Nmax} Λ(n)²/n ≤ C log² T` -/
theorem primeSum_Nmax_le {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (w : HeightWeight) (T : ℝ), Sep w T σ →
      ∑ n ∈ Finset.Icc 2 (Nmax T σ), Λ n ^ 2 / n ≤ C * Real.log T ^ 2 := by
  obtain ⟨C, hC⟩ := primeSum_upper
  refine ⟨4 * |C|, by positivity, fun w T hS => ?_⟩
  have hT := hS.T_pos
  have hX1 := hS.rpow_ge_one hσ
  have hX : (2 : ℝ) ≤ 2 * T ^ σ := by linarith
  have h1 := hC (2 * T ^ σ) hX
  have hlog : Real.log (2 * T ^ σ) = Real.log 2 + σ * Real.log T := by
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_rpow hT]
  have hL := hS.one_le_log
  have hl2 : Real.log 2 ≤ 1 := by
    have := Real.log_two_lt_d9
    linarith
  have hl2' : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hσL0 : 0 ≤ σ * Real.log T := mul_nonneg hσ.le (by linarith)
  have hσL1 : σ * Real.log T ≤ 1 * Real.log T := mul_le_mul_of_nonneg_right hσ1.le (by linarith)
  have hb1 : 0 ≤ Real.log (2 * T ^ σ) := by
    rw [hlog]
    linarith
  have hb2 : Real.log (2 * T ^ σ) ≤ 2 * Real.log T := by
    rw [hlog]
    linarith
  have hsq : Real.log (2 * T ^ σ) ^ 2 ≤ (2 * Real.log T) ^ 2 := pow_le_pow_left₀ hb1 hb2 2
  calc ∑ n ∈ Finset.Icc 2 (Nmax T σ), Λ n ^ 2 / n ≤ C * Real.log (2 * T ^ σ) ^ 2 := h1
    _ ≤ |C| * Real.log (2 * T ^ σ) ^ 2 := mul_le_mul_of_nonneg_right (le_abs_self C) (sq_nonneg _)
    _ ≤ |C| * (2 * Real.log T) ^ 2 := mul_le_mul_of_nonneg_left hsq (abs_nonneg C)
    _ = 4 * |C| * Real.log T ^ 2 := by ring

/-- `∫_{-1}^{1} ‖K0‖² ≤ C T log T` -/
theorem K0_L2_bound (w : HeightWeight) {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, Sep w T σ →
      ∫ x in (-1 : ℝ)..1, ‖K0 w.k T σ x‖ ^ 2 ≤ C * (T * Real.log T) := by
  obtain ⟨Cu, hCu0, hCu⟩ := primeSum_Nmax_le hσ hσ1
  set I2k : ℝ := ∫ y, ‖w.k y‖ ^ 2 with hI2k
  have hI2k0 : 0 ≤ I2k := integral_nonneg (fun y => by positivity)
  refine ⟨(1 + 2 * Cu) * I2k / σ, by positivity, fun T hS => ?_⟩
  have hT := hS.T_pos
  have hL := hS.log_pos
  have hA := hS.A_pos
  set ell : ℝ := Real.log (T / (2 * π)) with hell
  -- pointwise bound and integration
  have hcP : ∀ lam : ℝ, Continuous (fun x => ‖packet w.k T σ lam x‖ ^ 2) := fun lam =>
    (continuous_packet w T σ lam).norm.pow 2
  have hstep1 : ∫ x in (-1 : ℝ)..1, ‖K0 w.k T σ x‖ ^ 2
      ≤ ∫ x in (-1 : ℝ)..1, (ell ^ 2 * ‖packet w.k T σ 0 x‖ ^ 2
        + ∑ p ∈ idx T σ, lamCoeff p.1 ^ 2 * ‖packet w.k T σ (cen T σ p) x‖ ^ 2) := by
    apply intervalIntegral.integral_mono_on (by norm_num)
    · exact ((continuous_K0 w T σ).norm.pow 2).intervalIntegrable _ _
    · exact ((continuous_const.mul (hcP 0)).add
        (continuous_finsetSum _ (fun p _ => continuous_const.mul (hcP _)))).intervalIntegrable _ _
    · intro x _
      exact norm_sq_K0_le hσ hS x
  have hi1 : IntervalIntegrable (fun x => ell ^ 2 * ‖packet w.k T σ 0 x‖ ^ 2) volume (-1) 1 :=
    (continuous_const.mul (hcP 0)).intervalIntegrable _ _
  have hi2 : ∀ p ∈ idx T σ, IntervalIntegrable
      (fun x => lamCoeff p.1 ^ 2 * ‖packet w.k T σ (cen T σ p) x‖ ^ 2) volume (-1) 1 :=
    fun p _ => (continuous_const.mul (hcP _)).intervalIntegrable _ _
  have hi3 : IntervalIntegrable
      (fun x => ∑ p ∈ idx T σ, lamCoeff p.1 ^ 2 * ‖packet w.k T σ (cen T σ p) x‖ ^ 2) volume (-1) 1 :=
    (continuous_finsetSum _ (fun p _ => continuous_const.mul (hcP _))).intervalIntegrable _ _
  have hstep2 : ∫ x in (-1 : ℝ)..1, (ell ^ 2 * ‖packet w.k T σ 0 x‖ ^ 2
        + ∑ p ∈ idx T σ, lamCoeff p.1 ^ 2 * ‖packet w.k T σ (cen T σ p) x‖ ^ 2)
      = ell ^ 2 * (∫ x in (-1 : ℝ)..1, ‖packet w.k T σ 0 x‖ ^ 2)
        + ∑ p ∈ idx T σ,
            lamCoeff p.1 ^ 2 * ∫ x in (-1 : ℝ)..1, ‖packet w.k T σ (cen T σ p) x‖ ^ 2 := by
    rw [intervalIntegral.integral_add hi1 hi3, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_finsetSum hi2]
    congr 1
    refine Finset.sum_congr rfl (fun p _ => ?_)
    rw [intervalIntegral.integral_const_mul]
  set B : ℝ := T ^ 2 * (Asc T σ)⁻¹ * I2k with hB
  have hB0 : 0 ≤ B := by positivity
  have hPle : ∀ lam : ℝ, ∫ x in (-1 : ℝ)..1, ‖packet w.k T σ lam x‖ ^ 2 ≤ B := fun lam =>
    intervalIntegral_norm_packet_sq_le w hT.le hA lam
  have hstep3 : ell ^ 2 * (∫ x in (-1 : ℝ)..1, ‖packet w.k T σ 0 x‖ ^ 2)
        + ∑ p ∈ idx T σ,
            lamCoeff p.1 ^ 2 * ∫ x in (-1 : ℝ)..1, ‖packet w.k T σ (cen T σ p) x‖ ^ 2
      ≤ ell ^ 2 * B + ∑ p ∈ idx T σ, lamCoeff p.1 ^ 2 * B := by
    apply add_le_add
    · exact mul_le_mul_of_nonneg_left (hPle 0) (sq_nonneg _)
    · exact Finset.sum_le_sum (fun p _ => mul_le_mul_of_nonneg_left (hPle _) (sq_nonneg _))
  have hsum := hCu w T hS
  have hell2 : ell ^ 2 ≤ Real.log T ^ 2 := pow_le_pow_left₀ hS.ell_nonneg hS.ell_le 2
  have hBval : B = I2k / σ * (T / Real.log T) := by
    rw [hB]
    unfold Asc
    field_simp
  calc ∫ x in (-1 : ℝ)..1, ‖K0 w.k T σ x‖ ^ 2
      ≤ ell ^ 2 * B + ∑ p ∈ idx T σ, lamCoeff p.1 ^ 2 * B := hstep1.trans (hstep2.le.trans hstep3)
    _ = (ell ^ 2 + 2 * ∑ n ∈ Finset.Icc 2 (Nmax T σ), Λ n ^ 2 / n) * B := by
        rw [← Finset.sum_mul, sum_idx_lamCoeff_sq]
        ring
    _ ≤ (Real.log T ^ 2 + 2 * (Cu * Real.log T ^ 2)) * B :=
        mul_le_mul_of_nonneg_right (by linarith) hB0
    _ = (1 + 2 * Cu) * I2k / σ * (T * Real.log T) := by
        rw [hBval]
        field_simp

/-! ### the error term -/

/-- the difference of two third traces in terms of the `L¹` and `L²` norms of the difference -/
theorem t3_sub_t3_bound {Kf Kz : ℝ → ℂ} (hcKf : Continuous Kf) (hcKz : Continuous Kz) :
    ‖t3 Kf - t3 Kz‖ ≤ (∫ x in (-1 : ℝ)..1, ‖Kf x - Kz x‖) *
      (9 * (∫ x in (-1 : ℝ)..1, ‖Kz x‖ ^ 2) + 6 * ∫ x in (-1 : ℝ)..1, ‖Kf x - Kz x‖ ^ 2) := by
  set E : ℝ → ℂ := fun x => Kf x - Kz x with hEdef
  have hcE : Continuous E := hcKf.sub hcKz
  have hKfE : Kf = fun x => Kz x + E x := by
    funext x
    simp only [hEdef]
    ring
  set N1 : ℝ := ∫ x in (-1 : ℝ)..1, ‖E x‖ with hN1
  set SE : ℝ := ∫ x in (-1 : ℝ)..1, ‖E x‖ ^ 2 with hSE
  set SK : ℝ := ∫ x in (-1 : ℝ)..1, ‖Kz x‖ ^ 2 with hSK
  set SF : ℝ := ∫ x in (-1 : ℝ)..1, ‖Kf x‖ ^ 2 with hSFdef
  have hN10 : 0 ≤ N1 := intervalIntegral.integral_nonneg (by norm_num) (fun x _ => norm_nonneg _)
  -- `∫ ‖Kf‖² ≤ 2 ∫ ‖K0‖² + 2 ∫ ‖E‖²`
  have hi1 : IntervalIntegrable (fun x => 2 * ‖Kz x‖ ^ 2) volume (-1) 1 :=
    (continuous_const.mul (hcKz.norm.pow 2)).intervalIntegrable _ _
  have hi2 : IntervalIntegrable (fun x => 2 * ‖E x‖ ^ 2) volume (-1) 1 :=
    (continuous_const.mul (hcE.norm.pow 2)).intervalIntegrable _ _
  have hSF : SF ≤ 2 * SK + 2 * SE := by
    have h1 : SF ≤ ∫ x in (-1 : ℝ)..1, (2 * ‖Kz x‖ ^ 2 + 2 * ‖E x‖ ^ 2) := by
      apply intervalIntegral.integral_mono_on (by norm_num)
      · exact (hcKf.norm.pow 2).intervalIntegrable _ _
      · exact hi1.add hi2
      · intro x _
        have h2 : ‖Kf x‖ ≤ ‖Kz x‖ + ‖E x‖ := by
          have h3 : Kf x = Kz x + E x := congrFun hKfE x
          rw [h3]
          exact norm_add_le _ _
        have h3 : ‖Kf x‖ ^ 2 ≤ (‖Kz x‖ + ‖E x‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h2 2
        linarith [sq_nonneg (‖Kz x‖ - ‖E x‖)]
    rw [intervalIntegral.integral_add hi1 hi2, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul] at h1
    exact h1
  -- the telescoping identity
  have htel : t3 Kf - t3 Kz = tri E Kf Kf + tri Kz E Kf + tri Kz Kz E := by
    rw [t3_eq_tri, t3_eq_tri]
    have e1 : tri Kf Kf Kf = tri Kz Kf Kf + tri E Kf Kf :=
      (congrArg (fun K => tri K Kf Kf) hKfE).trans (tri_add_left hcKz hcE hcKf hcKf)
    have e2 : tri Kz Kf Kf = tri Kz Kz Kf + tri Kz E Kf :=
      (congrArg (fun K => tri Kz K Kf) hKfE).trans (tri_add_mid hcKz hcKz hcE hcKf)
    have e3 : tri Kz Kz Kf = tri Kz Kz Kz + tri Kz Kz E :=
      (congrArg (fun K => tri Kz Kz K) hKfE).trans (tri_add_right hcKz hcKz hcKz hcE)
    rw [e1, e2, e3]
    ring
  have b1 := tri_bound_left hcE hcKf hcKf
  have b2 := tri_bound_mid hcKz hcE hcKf
  have b3 := tri_bound_right hcKz hcKz hcE
  rw [htel]
  have h1 : ‖tri E Kf Kf + tri Kz E Kf + tri Kz Kz E‖
      ≤ ‖tri E Kf Kf‖ + ‖tri Kz E Kf‖ + ‖tri Kz Kz E‖ := norm_add₃_le
  have h2 : N1 * (SF + SF) + N1 * (SK + SF) + N1 * (SK + SK) ≤ N1 * (9 * SK + 6 * SE) := by
    have e : N1 * (SF + SF) + N1 * (SK + SF) + N1 * (SK + SK) = N1 * (3 * SF + 3 * SK) := by ring
    rw [e]
    exact mul_le_mul_of_nonneg_left (by linarith) hN10
  linarith

theorem t3_error (hRH : RiemannHypothesis) (w : HeightWeight) {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ < 1) :
    ∃ C T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T → ‖t3 (Kfull w.h T σ) - t3 (K0 w.k T σ)‖ ≤ C * T := by
  obtain ⟨CE, T1, hE⟩ := kernel_error hRH w hσ hσ1
  obtain ⟨T2, hSep⟩ := sep_eventually w hσ hσ1
  obtain ⟨CK, hCK0, hK⟩ := K0_L2_bound w hσ hσ1
  refine ⟨9 * CE * CK + 6 * CE ^ 2, max T1 T2, fun T hT => ?_⟩
  have hS := hSep T ((le_max_right _ _).trans hT)
  obtain ⟨_, hE1, hE2⟩ := hE T ((le_max_left _ _).trans hT)
  have hTpos := hS.T_pos
  have hL := hS.one_le_log
  have hLpos := hS.log_pos
  have hmain := t3_sub_t3_bound (continuous_Kfull hRH w hTpos σ) (continuous_K0 w T σ)
  have hSKle := hK T hS
  set N1 : ℝ := ∫ x in (-1 : ℝ)..1, ‖Kfull w.h T σ x - K0 w.k T σ x‖ with hN1
  set SE : ℝ := ∫ x in (-1 : ℝ)..1, ‖Kfull w.h T σ x - K0 w.k T σ x‖ ^ 2 with hSE
  set SK : ℝ := ∫ x in (-1 : ℝ)..1, ‖K0 w.k T σ x‖ ^ 2 with hSK
  have hN10 : 0 ≤ N1 := intervalIntegral.integral_nonneg (by norm_num) (fun x _ => norm_nonneg _)
  have hSE0 : 0 ≤ SE := intervalIntegral.integral_nonneg (by norm_num) (fun x _ => by positivity)
  have hSK0 : 0 ≤ SK := intervalIntegral.integral_nonneg (by norm_num) (fun x _ => by positivity)
  have hCE0 : 0 ≤ CE := by
    have h1 : 0 ≤ CE / Real.log T := hN10.trans hE1
    have h2 := mul_nonneg h1 hLpos.le
    rwa [div_mul_cancel₀ _ hLpos.ne'] at h2
  have hbound : 9 * SK + 6 * SE ≤ 9 * (CK * (T * Real.log T)) + 6 * (CE * T / Real.log T) := by
    linarith
  calc ‖t3 (Kfull w.h T σ) - t3 (K0 w.k T σ)‖ ≤ N1 * (9 * SK + 6 * SE) := hmain
    _ ≤ CE / Real.log T * (9 * (CK * (T * Real.log T)) + 6 * (CE * T / Real.log T)) :=
        mul_le_mul hE1 hbound (by positivity) (by positivity)
    _ = 9 * CE * CK * T + 6 * CE ^ 2 * T / Real.log T ^ 2 := by
        field_simp
    _ ≤ 9 * CE * CK * T + 6 * CE ^ 2 * T := by
        have h1 : 6 * CE ^ 2 * T / Real.log T ^ 2 ≤ 6 * CE ^ 2 * T := by
          apply div_le_self (by positivity)
          exact one_le_pow₀ hL
        linarith
    _ = (9 * CE * CK + 6 * CE ^ 2) * T := by ring

end TMA.T3
end
end Src_TMA_Trace3Aux3

section Src_TMA_Trace3Aux4
/-
Written for Kristian Muri Knausgård, drafted with Claude (Anthropic), 22 November 2026.

TMA/Trace3Aux4.lean — classification of the packet triples of `t3 K0`, with `K0 = ell · P0 - Q`:
* the expansion into eight terms;
* one prime packet: the term vanishes (closure);
* two prime packets: only the diagonal `(p, bar p)` survives, and it is evaluated;
* three prime packets: only `n_a n_b = n_c` survives; bounded with `triplePrime_bound`.
See BLUEPRINT.md, module "T3" (main term).
-/

open MeasureTheory Complex
open scoped BigOperators ArithmeticFunction Real

noncomputable section
namespace TMA.T3

/-! ### the expansion into eight terms -/

theorem tri_lin_left {X X' Y Z : ℝ → ℂ} (hX : Continuous X) (hX' : Continuous X') (hY : Continuous Y)
    (hZ : Continuous Z) (c : ℂ) :
    tri (fun x => c * X x - X' x) Y Z = c * tri X Y Z - tri X' Y Z := by
  rw [tri_sub_left (X := fun x => c * X x) (continuous_const.mul hX) hX' hY hZ, tri_smul_left]

theorem tri_lin_mid {X Y Y' Z : ℝ → ℂ} (hX : Continuous X) (hY : Continuous Y) (hY' : Continuous Y')
    (hZ : Continuous Z) (c : ℂ) :
    tri X (fun x => c * Y x - Y' x) Z = c * tri X Y Z - tri X Y' Z := by
  rw [tri_sub_mid (Y := fun x => c * Y x) hX (continuous_const.mul hY) hY' hZ, tri_smul_mid]

theorem tri_lin_right {X Y Z Z' : ℝ → ℂ} (hX : Continuous X) (hY : Continuous Y) (hZ : Continuous Z)
    (hZ' : Continuous Z') (c : ℂ) :
    tri X Y (fun x => c * Z x - Z' x) = c * tri X Y Z - tri X Y Z' := by
  rw [tri_sub_right (Z := fun x => c * Z x) hX hY (continuous_const.mul hZ) hZ', tri_smul_right]

theorem tri_expand {P Q : ℝ → ℂ} (hP : Continuous P) (hQ : Continuous Q) (c : ℂ) :
    tri (fun x => c * P x - Q x) (fun x => c * P x - Q x) (fun x => c * P x - Q x)
      = c ^ 3 * tri P P P - c ^ 2 * (tri Q P P + tri P Q P + tri P P Q)
        + c * (tri Q Q P + tri Q P Q + tri P Q Q) - tri Q Q Q := by
  have hR : Continuous (fun x => c * P x - Q x) := (continuous_const.mul hP).sub hQ
  rw [tri_lin_left hP hQ hR hR, tri_lin_mid hP hP hQ hR, tri_lin_mid hQ hP hQ hR,
    tri_lin_right hP hP hP hQ, tri_lin_right hP hQ hP hQ, tri_lin_right hQ hP hP hQ,
    tri_lin_right hQ hQ hP hQ]
  ring

/-! ### `tri` with the prime part `Qk` in one slot -/

section slots
variable (w : HeightWeight) {T σ : ℝ}

theorem tri_Qk_left {Y Z : ℝ → ℂ} (hY : Continuous Y) (hZ : Continuous Z) :
    tri (Qk w.k T σ) Y Z
      = ∑ p ∈ idx T σ, (lamCoeff p.1 : ℂ) * tri (packet w.k T σ (cen T σ p)) Y Z :=
  (tri_sum_left (idx T σ) (f := fun p x => (lamCoeff p.1 : ℂ) * packet w.k T σ (cen T σ p) x)
    (fun _ _ => continuous_const.mul (continuous_packet w T σ _)) hY hZ).trans
    (Finset.sum_congr rfl (fun _ _ => tri_smul_left _ _ _ _))

theorem tri_Qk_mid {X Z : ℝ → ℂ} (hX : Continuous X) (hZ : Continuous Z) :
    tri X (Qk w.k T σ) Z
      = ∑ p ∈ idx T σ, (lamCoeff p.1 : ℂ) * tri X (packet w.k T σ (cen T σ p)) Z :=
  (tri_sum_mid (idx T σ) (f := fun p x => (lamCoeff p.1 : ℂ) * packet w.k T σ (cen T σ p) x)
    (fun _ _ => continuous_const.mul (continuous_packet w T σ _)) hX hZ).trans
    (Finset.sum_congr rfl (fun _ _ => tri_smul_mid _ _ _ _))

theorem tri_Qk_right {X Y : ℝ → ℂ} (hX : Continuous X) (hY : Continuous Y) :
    tri X Y (Qk w.k T σ)
      = ∑ p ∈ idx T σ, (lamCoeff p.1 : ℂ) * tri X Y (packet w.k T σ (cen T σ p)) :=
  (tri_sum_right (idx T σ) (f := fun p x => (lamCoeff p.1 : ℂ) * packet w.k T σ (cen T σ p) x)
    (fun _ _ => continuous_const.mul (continuous_packet w T σ _)) hX hY).trans
    (Finset.sum_congr rfl (fun _ _ => tri_smul_right _ _ _ _))

/-! ### one prime packet: the term vanishes -/

theorem tri_Q_P_P (hσ : 0 < σ) (hS : Sep w T σ) :
    tri (Qk w.k T σ) (packet w.k T σ 0) (packet w.k T σ 0) = 0 := by
  rw [tri_Qk_left w (continuous_packet w T σ 0) (continuous_packet w T σ 0)]
  refine Finset.sum_eq_zero (fun p hp => ?_)
  rw [tri_packet_eq_zero_log w hσ hS (a := sgn p.2 * Real.log p.1) (by rw [cen_eq]; ring)
    (single_sep hS (mem_idx.mp hp).1 p.2), mul_zero]

theorem tri_P_Q_P (hσ : 0 < σ) (hS : Sep w T σ) :
    tri (packet w.k T σ 0) (Qk w.k T σ) (packet w.k T σ 0) = 0 := by
  rw [tri_Qk_mid w (continuous_packet w T σ 0) (continuous_packet w T σ 0)]
  refine Finset.sum_eq_zero (fun p hp => ?_)
  rw [tri_packet_eq_zero_log w hσ hS (a := sgn p.2 * Real.log p.1) (by rw [cen_eq]; ring)
    (single_sep hS (mem_idx.mp hp).1 p.2), mul_zero]

theorem tri_P_P_Q (hσ : 0 < σ) (hS : Sep w T σ) :
    tri (packet w.k T σ 0) (packet w.k T σ 0) (Qk w.k T σ) = 0 := by
  rw [tri_Qk_right w (continuous_packet w T σ 0) (continuous_packet w T σ 0)]
  refine Finset.sum_eq_zero (fun p hp => ?_)
  rw [tri_packet_eq_zero_log w hσ hS (a := sgn p.2 * Real.log p.1) (by rw [cen_eq]; ring)
    (single_sep hS (mem_idx.mp hp).1 p.2), mul_zero]

/-! ### two prime packets: reduction to the diagonal -/

variable {w}

theorem pair_log_lt (hS : Sep w T σ) {p q : ℕ × Bool} (hp : p ∈ idx T σ) (hq : q ∈ idx T σ)
    (hne : q ≠ bar p) :
    3 * w.kappa / T < |sgn p.2 * Real.log p.1 + sgn q.2 * Real.log q.1| := by
  by_contra hc
  rw [mem_idx] at hp hq
  obtain ⟨hs, hn⟩ := pair_cases hS hp.1 hp.2 hq.1 hq.2 p.2 q.2 (not_lt.mp hc)
  exact hne (Prod.ext hn.symm hs)

variable (w)

theorem tri_Q_Q_P (hσ : 0 < σ) (hS : Sep w T σ) :
    tri (Qk w.k T σ) (Qk w.k T σ) (packet w.k T σ 0)
      = ∑ p ∈ idx T σ, (lamCoeff p.1 : ℂ) ^ 2 *
          tri (packet w.k T σ (cen T σ p)) (packet w.k T σ (-(cen T σ p))) (packet w.k T σ 0) := by
  rw [tri_Qk_left w (continuous_Qk w T σ) (continuous_packet w T σ 0)]
  refine Finset.sum_congr rfl (fun p hp => ?_)
  rw [tri_Qk_mid w (continuous_packet w T σ _) (continuous_packet w T σ 0),
    Finset.sum_eq_single_of_mem (bar p) (bar_mem hp) (fun q hq hne => by
      rw [tri_packet_eq_zero_log w hσ hS
        (a := sgn p.2 * Real.log p.1 + sgn q.2 * Real.log q.1)
        (by rw [cen_eq, cen_eq]; ring) (pair_log_lt hS hp hq hne), mul_zero]),
    cen_bar]
  simp only [bar]
  ring

theorem tri_Q_P_Q (hσ : 0 < σ) (hS : Sep w T σ) :
    tri (Qk w.k T σ) (packet w.k T σ 0) (Qk w.k T σ)
      = ∑ p ∈ idx T σ, (lamCoeff p.1 : ℂ) ^ 2 *
          tri (packet w.k T σ (cen T σ p)) (packet w.k T σ 0) (packet w.k T σ (-(cen T σ p))) := by
  rw [tri_Qk_left w (continuous_packet w T σ 0) (continuous_Qk w T σ)]
  refine Finset.sum_congr rfl (fun p hp => ?_)
  rw [tri_Qk_right w (continuous_packet w T σ _) (continuous_packet w T σ 0),
    Finset.sum_eq_single_of_mem (bar p) (bar_mem hp) (fun q hq hne => by
      rw [tri_packet_eq_zero_log w hσ hS
        (a := sgn p.2 * Real.log p.1 + sgn q.2 * Real.log q.1)
        (by rw [cen_eq, cen_eq]; ring) (pair_log_lt hS hp hq hne), mul_zero]),
    cen_bar]
  simp only [bar]
  ring

theorem tri_P_Q_Q (hσ : 0 < σ) (hS : Sep w T σ) :
    tri (packet w.k T σ 0) (Qk w.k T σ) (Qk w.k T σ)
      = ∑ p ∈ idx T σ, (lamCoeff p.1 : ℂ) ^ 2 *
          tri (packet w.k T σ 0) (packet w.k T σ (cen T σ p)) (packet w.k T σ (-(cen T σ p))) := by
  rw [tri_Qk_mid w (continuous_packet w T σ 0) (continuous_Qk w T σ)]
  refine Finset.sum_congr rfl (fun p hp => ?_)
  rw [tri_Qk_right w (continuous_packet w T σ 0) (continuous_packet w T σ _),
    Finset.sum_eq_single_of_mem (bar p) (bar_mem hp) (fun q hq hne => by
      rw [tri_packet_eq_zero_log w hσ hS
        (a := sgn p.2 * Real.log p.1 + sgn q.2 * Real.log q.1)
        (by rw [cen_eq, cen_eq]; ring) (pair_log_lt hS hp hq hne), mul_zero]),
    cen_bar]
  simp only [bar]
  ring

end slots

/-! ### evaluation of the surviving terms -/

/-- the common factor `T³/A²` -/
def M3 (T σ : ℝ) : ℝ := T ^ 3 / Asc T σ ^ 2

/-- `(1/2π) ∫ h³` -/
def kt (w : HeightWeight) : ℝ := 1 / (2 * π) * w.kap3

/-- the error of one evaluation -/
def evErr (w : HeightWeight) (M T σ : ℝ) : ℝ :=
  |T| ^ 3 / Asc T σ ^ 2 * (10 * (2 * w.kappa / Asc T σ) * M * (∫ y, ‖w.k y‖) ^ 2)

/-- the size bound of one packet triple -/
def szB (w : HeightWeight) (M T σ : ℝ) : ℝ := 2 * T ^ 3 * M * (∫ y, ‖w.k y‖) ^ 2 / Asc T σ ^ 2

/-- `Σ_{2 ≤ n ≤ Nmax} Λ(n)²/n · (bg(λ_n) + bg(-λ_n))` -/
def Bsum (T σ : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 2 (Nmax T σ), Λ n ^ 2 / n * (bg (lamOf T σ n) + bg (-(lamOf T σ n)))

/-- `Σ_{2 ≤ n ≤ Nmax} Λ(n)²/n` -/
def SLam (T σ : ℝ) : ℝ := ∑ n ∈ Finset.Icc 2 (Nmax T σ), Λ n ^ 2 / n

theorem kap3_nonneg (w : HeightWeight) : 0 ≤ w.kap3 :=
  integral_nonneg (fun x => pow_nonneg (w.h_nonneg x) 3)

theorem kt_nonneg (w : HeightWeight) : 0 ≤ kt w := by
  unfold kt
  have := kap3_nonneg w
  positivity

theorem SLam_nonneg (T σ : ℝ) : 0 ≤ SLam T σ :=
  Finset.sum_nonneg (fun n _ =>
    div_nonneg (sq_nonneg _) (Nat.cast_nonneg n))

section eval
variable (w : HeightWeight) {M T σ : ℝ}

theorem evErr_nonneg (hM0 : 0 ≤ M) (hA : 0 < Asc T σ) : 0 ≤ evErr w M T σ := by
  unfold evErr
  have := w.kappa_pos
  positivity

theorem eval_000 (hM : ∀ y, ‖w.k y‖ ≤ M) (hA : 0 < Asc T σ) :
    ‖tri (packet w.k T σ 0) (packet w.k T σ 0) (packet w.k T σ 0)
        - ((M3 T σ * (I3 * kt w) : ℝ) : ℂ)‖ ≤ evErr w M T σ :=
  tri_packet_eval w hM hA (l1 := 0) (l2 := 0) (l3 := 0) (by ring)

theorem eval_12 (hM : ∀ y, ‖w.k y‖ ≤ M) (hA : 0 < Asc T σ) (l : ℝ) :
    ‖tri (packet w.k T σ l) (packet w.k T σ (-l)) (packet w.k T σ 0)
        - ((M3 T σ * (bg l * kt w) : ℝ) : ℂ)‖ ≤ evErr w M T σ := by
  have h := tri_packet_eval w hM hA (l1 := l) (l2 := -l) (l3 := 0) (by ring)
  rw [Gg_neg] at h
  exact h

theorem eval_13 (hM : ∀ y, ‖w.k y‖ ≤ M) (hA : 0 < Asc T σ) (l : ℝ) :
    ‖tri (packet w.k T σ l) (packet w.k T σ 0) (packet w.k T σ (-l))
        - ((M3 T σ * (bg (-l) * kt w) : ℝ) : ℂ)‖ ≤ evErr w M T σ := by
  have h := tri_packet_eval w hM hA (l1 := l) (l2 := 0) (l3 := -l) (by ring)
  rw [Gg_right_zero] at h
  exact h

theorem eval_23 (hM : ∀ y, ‖w.k y‖ ≤ M) (hA : 0 < Asc T σ) (l : ℝ) :
    ‖tri (packet w.k T σ 0) (packet w.k T σ l) (packet w.k T σ (-l))
        - ((M3 T σ * (bg l * kt w) : ℝ) : ℂ)‖ ≤ evErr w M T σ :=
  tri_packet_eval w hM hA (l1 := 0) (l2 := l) (l3 := -l) (by ring)

/-- the three terms with two prime packets -/
theorem two_Q_eval (hM : ∀ y, ‖w.k y‖ ≤ M) (hσ : 0 < σ) (hS : Sep w T σ) :
    ‖(tri (Qk w.k T σ) (Qk w.k T σ) (packet w.k T σ 0)
        + tri (Qk w.k T σ) (packet w.k T σ 0) (Qk w.k T σ)
        + tri (packet w.k T σ 0) (Qk w.k T σ) (Qk w.k T σ))
        - ((3 * (M3 T σ * kt w) * Bsum T σ : ℝ) : ℂ)‖ ≤ 6 * evErr w M T σ * SLam T σ := by
  have hA := hS.A_pos
  -- the main term as a sum over the signed index set
  have hid : 3 * (M3 T σ * kt w) * Bsum T σ
      = ∑ p ∈ idx T σ, lamCoeff p.1 ^ 2 *
          (M3 T σ * (bg (cen T σ p) * kt w) + M3 T σ * (bg (-(cen T σ p)) * kt w)
            + M3 T σ * (bg (cen T σ p) * kt w)) := by
    unfold Bsum
    rw [sum_idx, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun n _ => ?_)
    simp only [cen, sgn_true, sgn_false, one_mul, neg_mul, neg_neg]
    rw [lamCoeff_sq]
    ring
  rw [hid, tri_Q_Q_P w hσ hS, tri_Q_P_Q w hσ hS, tri_P_Q_Q w hσ hS, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]
  push_cast
  rw [← Finset.sum_sub_distrib]
  have hterm : ∀ p ∈ idx T σ,
      ‖(lamCoeff p.1 : ℂ) ^ 2 *
            tri (packet w.k T σ (cen T σ p)) (packet w.k T σ (-(cen T σ p))) (packet w.k T σ 0)
          + (lamCoeff p.1 : ℂ) ^ 2 *
            tri (packet w.k T σ (cen T σ p)) (packet w.k T σ 0) (packet w.k T σ (-(cen T σ p)))
          + (lamCoeff p.1 : ℂ) ^ 2 *
            tri (packet w.k T σ 0) (packet w.k T σ (cen T σ p)) (packet w.k T σ (-(cen T σ p)))
          - (lamCoeff p.1 : ℂ) ^ 2 *
            ((M3 T σ : ℂ) * ((bg (cen T σ p) : ℂ) * (kt w : ℂ))
              + (M3 T σ : ℂ) * ((bg (-(cen T σ p)) : ℂ) * (kt w : ℂ))
              + (M3 T σ : ℂ) * ((bg (cen T σ p) : ℂ) * (kt w : ℂ)))‖
        ≤ lamCoeff p.1 ^ 2 * (3 * evErr w M T σ) := by
    intro p _
    have h1 := eval_12 w hM hA (cen T σ p)
    have h2 := eval_13 w hM hA (cen T σ p)
    have h3 := eval_23 w hM hA (cen T σ p)
    push_cast at h1 h2 h3
    have e : (lamCoeff p.1 : ℂ) ^ 2 *
            tri (packet w.k T σ (cen T σ p)) (packet w.k T σ (-(cen T σ p))) (packet w.k T σ 0)
          + (lamCoeff p.1 : ℂ) ^ 2 *
            tri (packet w.k T σ (cen T σ p)) (packet w.k T σ 0) (packet w.k T σ (-(cen T σ p)))
          + (lamCoeff p.1 : ℂ) ^ 2 *
            tri (packet w.k T σ 0) (packet w.k T σ (cen T σ p)) (packet w.k T σ (-(cen T σ p)))
          - (lamCoeff p.1 : ℂ) ^ 2 *
            ((M3 T σ : ℂ) * ((bg (cen T σ p) : ℂ) * (kt w : ℂ))
              + (M3 T σ : ℂ) * ((bg (-(cen T σ p)) : ℂ) * (kt w : ℂ))
              + (M3 T σ : ℂ) * ((bg (cen T σ p) : ℂ) * (kt w : ℂ)))
        = (lamCoeff p.1 : ℂ) ^ 2 *
          ((tri (packet w.k T σ (cen T σ p)) (packet w.k T σ (-(cen T σ p))) (packet w.k T σ 0)
              - (M3 T σ : ℂ) * ((bg (cen T σ p) : ℂ) * (kt w : ℂ)))
            + (tri (packet w.k T σ (cen T σ p)) (packet w.k T σ 0) (packet w.k T σ (-(cen T σ p)))
              - (M3 T σ : ℂ) * ((bg (-(cen T σ p)) : ℂ) * (kt w : ℂ)))
            + (tri (packet w.k T σ 0) (packet w.k T σ (cen T σ p)) (packet w.k T σ (-(cen T σ p)))
              - (M3 T σ : ℂ) * ((bg (cen T σ p) : ℂ) * (kt w : ℂ)))) := by
      ring
    rw [e, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
    exact norm_add₃_le.trans (by linarith)
  calc _ ≤ ∑ p ∈ idx T σ, lamCoeff p.1 ^ 2 * (3 * evErr w M T σ) :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum hterm)
    _ = 6 * evErr w M T σ * SLam T σ := by
        rw [← Finset.sum_mul, sum_idx_lamCoeff_sq]
        unfold SLam
        ring

end eval

/-! ### three prime packets -/

theorem lamCoeff_triple (a b : ℕ) :
    lamCoeff a * lamCoeff b * lamCoeff (a * b) = Λ a * Λ b * Λ (a * b) / ((a : ℝ) * b) := by
  unfold lamCoeff
  have ha : Real.sqrt a * Real.sqrt a = a := Real.mul_self_sqrt (Nat.cast_nonneg a)
  have hb : Real.sqrt b * Real.sqrt b = b := Real.mul_self_sqrt (Nat.cast_nonneg b)
  rw [Nat.cast_mul, Real.sqrt_mul (Nat.cast_nonneg a), div_mul_div_comm, div_mul_div_comm]
  congr 1
  calc Real.sqrt a * Real.sqrt b * (Real.sqrt a * Real.sqrt b)
      = (Real.sqrt a * Real.sqrt a) * (Real.sqrt b * Real.sqrt b) := by ring
    _ = (a : ℝ) * b := by rw [ha, hb]

theorem sum_delta_le (s : Finset ℕ) (m : ℕ) :
    ∑ n ∈ s, lamCoeff n * (if m = n then 1 else 0) ≤ lamCoeff m := by
  simp only [mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq]
  split_ifs
  · exact le_rfl
  · exact lamCoeff_nonneg m

theorem sum_idx_fst (T σ : ℝ) (g : ℕ → ℝ) :
    ∑ p ∈ idx T σ, g p.1 = 2 * ∑ n ∈ Finset.Icc 2 (Nmax T σ), g n := by
  rw [sum_idx, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun n _ => (two_mul _).symm)

/-- the three-prime sum over a finite range, with the three possible product relations -/
theorem triple_delta_sum_le (s : Finset ℕ) :
    ∑ a ∈ s, ∑ b ∈ s, ∑ c ∈ s, lamCoeff a * lamCoeff b * lamCoeff c *
        ((if a * b = c then (1 : ℝ) else 0) + (if a * c = b then 1 else 0)
          + (if b * c = a then 1 else 0))
      ≤ 3 * ∑ a ∈ s, ∑ b ∈ s, lamCoeff a * lamCoeff b * lamCoeff (a * b) := by
  set V : ℝ := ∑ a ∈ s, ∑ b ∈ s, lamCoeff a * lamCoeff b * lamCoeff (a * b) with hV
  have hnn := lamCoeff_nonneg
  -- first relation
  have h1 : ∑ a ∈ s, ∑ b ∈ s, ∑ c ∈ s,
      lamCoeff a * lamCoeff b * lamCoeff c * (if a * b = c then (1 : ℝ) else 0) ≤ V := by
    refine Finset.sum_le_sum (fun a _ => Finset.sum_le_sum (fun b _ => ?_))
    calc ∑ c ∈ s, lamCoeff a * lamCoeff b * lamCoeff c * (if a * b = c then (1 : ℝ) else 0)
        = lamCoeff a * lamCoeff b * ∑ c ∈ s, lamCoeff c * (if a * b = c then (1 : ℝ) else 0) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl (fun c _ => by ring)
      _ ≤ lamCoeff a * lamCoeff b * lamCoeff (a * b) :=
          mul_le_mul_of_nonneg_left (sum_delta_le s (a * b)) (mul_nonneg (hnn a) (hnn b))
  -- second relation
  have h2 : ∑ a ∈ s, ∑ b ∈ s, ∑ c ∈ s,
      lamCoeff a * lamCoeff b * lamCoeff c * (if a * c = b then (1 : ℝ) else 0) ≤ V := by
    refine Finset.sum_le_sum (fun a _ => ?_)
    rw [Finset.sum_comm]
    refine Finset.sum_le_sum (fun c _ => ?_)
    calc ∑ b ∈ s, lamCoeff a * lamCoeff b * lamCoeff c * (if a * c = b then (1 : ℝ) else 0)
        = lamCoeff a * lamCoeff c * ∑ b ∈ s, lamCoeff b * (if a * c = b then (1 : ℝ) else 0) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl (fun b _ => by ring)
      _ ≤ lamCoeff a * lamCoeff c * lamCoeff (a * c) :=
          mul_le_mul_of_nonneg_left (sum_delta_le s (a * c)) (mul_nonneg (hnn a) (hnn c))
  -- third relation
  have h3 : ∑ a ∈ s, ∑ b ∈ s, ∑ c ∈ s,
      lamCoeff a * lamCoeff b * lamCoeff c * (if b * c = a then (1 : ℝ) else 0) ≤ V := by
    rw [Finset.sum_comm]
    refine Finset.sum_le_sum (fun b _ => ?_)
    rw [Finset.sum_comm]
    refine Finset.sum_le_sum (fun c _ => ?_)
    calc ∑ a ∈ s, lamCoeff a * lamCoeff b * lamCoeff c * (if b * c = a then (1 : ℝ) else 0)
        = lamCoeff b * lamCoeff c * ∑ a ∈ s, lamCoeff a * (if b * c = a then (1 : ℝ) else 0) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl (fun a _ => by ring)
      _ ≤ lamCoeff b * lamCoeff c * lamCoeff (b * c) :=
          mul_le_mul_of_nonneg_left (sum_delta_le s (b * c)) (mul_nonneg (hnn b) (hnn c))
  have hsplit : ∑ a ∈ s, ∑ b ∈ s, ∑ c ∈ s, lamCoeff a * lamCoeff b * lamCoeff c *
        ((if a * b = c then (1 : ℝ) else 0) + (if a * c = b then 1 else 0)
          + (if b * c = a then 1 else 0))
      = ∑ a ∈ s, ∑ b ∈ s, ∑ c ∈ s,
          lamCoeff a * lamCoeff b * lamCoeff c * (if a * b = c then (1 : ℝ) else 0)
        + ∑ a ∈ s, ∑ b ∈ s, ∑ c ∈ s,
          lamCoeff a * lamCoeff b * lamCoeff c * (if a * c = b then (1 : ℝ) else 0)
        + ∑ a ∈ s, ∑ b ∈ s, ∑ c ∈ s,
          lamCoeff a * lamCoeff b * lamCoeff c * (if b * c = a then (1 : ℝ) else 0) := by
    simp only [mul_add, Finset.sum_add_distrib]
  rw [hsplit]
  linarith

section three
variable (w : HeightWeight) {M T σ : ℝ}

theorem szB_nonneg (hM0 : 0 ≤ M) (hT : 0 ≤ T) : 0 ≤ szB w M T σ := by
  unfold szB
  positivity

/-- a triple of prime packets vanishes unless one of the three product relations holds -/
theorem norm_tri_cen_le (hM : ∀ y, ‖w.k y‖ ≤ M) (hσ : 0 < σ) (hS : Sep w T σ) {p q r : ℕ × Bool}
    (hp : p ∈ idx T σ) (hq : q ∈ idx T σ) (hr : r ∈ idx T σ) :
    ‖tri (packet w.k T σ (cen T σ p)) (packet w.k T σ (cen T σ q)) (packet w.k T σ (cen T σ r))‖
      ≤ szB w M T σ * ((if p.1 * q.1 = r.1 then (1 : ℝ) else 0) + (if p.1 * r.1 = q.1 then 1 else 0)
          + (if q.1 * r.1 = p.1 then 1 else 0)) := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  have hsz : 0 ≤ szB w M T σ := szB_nonneg w hM0 hS.T_pos.le
  have hsize := norm_tri_packet_le w hM hS.T_pos.le hS.A_pos (cen T σ p) (cen T σ q) (cen T σ r)
  have i1 : (0 : ℝ) ≤ (if p.1 * q.1 = r.1 then (1 : ℝ) else 0) := by split_ifs <;> norm_num
  have i2 : (0 : ℝ) ≤ (if p.1 * r.1 = q.1 then (1 : ℝ) else 0) := by split_ifs <;> norm_num
  have i3 : (0 : ℝ) ≤ (if q.1 * r.1 = p.1 then (1 : ℝ) else 0) := by split_ifs <;> norm_num
  by_cases h : p.1 * q.1 = r.1 ∨ p.1 * r.1 = q.1 ∨ q.1 * r.1 = p.1
  · have hone : (1 : ℝ) ≤ (if p.1 * q.1 = r.1 then (1 : ℝ) else 0)
        + (if p.1 * r.1 = q.1 then 1 else 0) + (if q.1 * r.1 = p.1 then 1 else 0) := by
      rcases h with h | h | h
      · rw [if_pos h]
        linarith
      · rw [if_pos h]
        linarith
      · rw [if_pos h]
        linarith
    calc _ ≤ szB w M T σ := hsize
      _ = szB w M T σ * 1 := (mul_one _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left hone hsz
  · have hlog : 3 * w.kappa / T
        < |sgn p.2 * Real.log p.1 + sgn q.2 * Real.log q.1 + sgn r.2 * Real.log r.1| := by
      by_contra hc
      rw [mem_idx] at hp hq hr
      exact h (triple_cases hS hp.1 hp.2 hq.1 hq.2 hr.1 hr.2 p.2 q.2 r.2 (not_lt.mp hc))
    rw [tri_packet_eq_zero_log w hσ hS
      (a := sgn p.2 * Real.log p.1 + sgn q.2 * Real.log q.1 + sgn r.2 * Real.log r.1)
      (by rw [cen_eq, cen_eq, cen_eq]; ring) hlog, norm_zero]
    exact mul_nonneg hsz (by linarith)

theorem tri_Q_Q_Q_expand :
    tri (Qk w.k T σ) (Qk w.k T σ) (Qk w.k T σ)
      = ∑ p ∈ idx T σ, ∑ q ∈ idx T σ, ∑ r ∈ idx T σ,
          ((lamCoeff p.1 : ℂ) * (lamCoeff q.1 : ℂ) * (lamCoeff r.1 : ℂ)) *
            tri (packet w.k T σ (cen T σ p)) (packet w.k T σ (cen T σ q))
              (packet w.k T σ (cen T σ r)) := by
  rw [tri_Qk_left w (continuous_Qk w T σ) (continuous_Qk w T σ)]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [tri_Qk_mid w (continuous_packet w T σ _) (continuous_Qk w T σ), Finset.mul_sum]
  refine Finset.sum_congr rfl (fun q _ => ?_)
  rw [tri_Qk_right w (continuous_packet w T σ _) (continuous_packet w T σ _), Finset.mul_sum,
    Finset.mul_sum]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  ring

end three

/-- **Three prime packets.** -/
theorem QQQ_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (w : HeightWeight) (M T σ : ℝ), (∀ y, ‖w.k y‖ ≤ M) → 0 < σ → Sep w T σ →
      ‖tri (Qk w.k T σ) (Qk w.k T σ) (Qk w.k T σ)‖ ≤ C * szB w M T σ := by
  obtain ⟨Ctp, hCtp⟩ := triplePrime_bound
  have hCtp0 : 0 ≤ Ctp := by
    have := hCtp 0
    simpa using this
  refine ⟨24 * Ctp, by positivity, fun w M T σ hM hσ hS => ?_⟩
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  have hsz : 0 ≤ szB w M T σ := szB_nonneg w hM0 hS.T_pos.le
  set s : Finset ℕ := Finset.Icc 2 (Nmax T σ) with hs
  -- the function of the three integers
  set g : ℕ → ℕ → ℕ → ℝ := fun a b c => lamCoeff a * lamCoeff b * lamCoeff c *
      ((if a * b = c then (1 : ℝ) else 0) + (if a * c = b then 1 else 0)
        + (if b * c = a then 1 else 0)) with hg
  have hstep1 : ‖tri (Qk w.k T σ) (Qk w.k T σ) (Qk w.k T σ)‖
      ≤ ∑ p ∈ idx T σ, ∑ q ∈ idx T σ, ∑ r ∈ idx T σ, szB w M T σ * g p.1 q.1 r.1 := by
    rw [tri_Q_Q_Q_expand]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun p hp => ?_))
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun q hq => ?_))
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun r hr => ?_))
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (lamCoeff_nonneg _),
      abs_of_nonneg (lamCoeff_nonneg _), abs_of_nonneg (lamCoeff_nonneg _)]
    have h1 := norm_tri_cen_le w hM hσ hS hp hq hr
    have h2 : 0 ≤ lamCoeff p.1 * lamCoeff q.1 * lamCoeff r.1 :=
      mul_nonneg (mul_nonneg (lamCoeff_nonneg _) (lamCoeff_nonneg _)) (lamCoeff_nonneg _)
    calc lamCoeff p.1 * lamCoeff q.1 * lamCoeff r.1 *
          ‖tri (packet w.k T σ (cen T σ p)) (packet w.k T σ (cen T σ q))
            (packet w.k T σ (cen T σ r))‖
        ≤ lamCoeff p.1 * lamCoeff q.1 * lamCoeff r.1 * (szB w M T σ *
            ((if p.1 * q.1 = r.1 then (1 : ℝ) else 0) + (if p.1 * r.1 = q.1 then 1 else 0)
              + (if q.1 * r.1 = p.1 then 1 else 0))) := mul_le_mul_of_nonneg_left h1 h2
      _ = szB w M T σ * g p.1 q.1 r.1 := by
          simp only [hg]
          ring
  have e1 : ∀ a b : ℕ, ∑ r ∈ idx T σ, szB w M T σ * g a b r.1
      = 2 * ∑ c ∈ s, szB w M T σ * g a b c := fun a b =>
    sum_idx_fst T σ (fun c => szB w M T σ * g a b c)
  have e2 : ∀ a : ℕ, ∑ q ∈ idx T σ, ∑ r ∈ idx T σ, szB w M T σ * g a q.1 r.1
      = 2 * ∑ b ∈ s, 2 * ∑ c ∈ s, szB w M T σ * g a b c := by
    intro a
    simp_rw [e1]
    exact sum_idx_fst T σ (fun b => 2 * ∑ c ∈ s, szB w M T σ * g a b c)
  have e3 : ∑ p ∈ idx T σ, ∑ q ∈ idx T σ, ∑ r ∈ idx T σ, szB w M T σ * g p.1 q.1 r.1
      = 2 * ∑ a ∈ s, 2 * ∑ b ∈ s, 2 * ∑ c ∈ s, szB w M T σ * g a b c := by
    simp_rw [e2]
    exact sum_idx_fst T σ (fun a => 2 * ∑ b ∈ s, 2 * ∑ c ∈ s, szB w M T σ * g a b c)
  have e4 : 2 * ∑ a ∈ s, 2 * ∑ b ∈ s, 2 * ∑ c ∈ s, szB w M T σ * g a b c
      = 8 * szB w M T σ * ∑ a ∈ s, ∑ b ∈ s, ∑ c ∈ s, g a b c := by
    simp only [← Finset.mul_sum]
    ring
  have h5 := triple_delta_sum_le s
  have h6 : ∑ a ∈ s, ∑ b ∈ s, lamCoeff a * lamCoeff b * lamCoeff (a * b) ≤ Ctp := by
    have := hCtp (Nmax T σ)
    simp only [lamCoeff_triple]
    exact this
  have h7 : ∑ a ∈ s, ∑ b ∈ s, ∑ c ∈ s, g a b c ≤ 3 * Ctp := h5.trans (by linarith)
  calc ‖tri (Qk w.k T σ) (Qk w.k T σ) (Qk w.k T σ)‖
      ≤ 8 * szB w M T σ * ∑ a ∈ s, ∑ b ∈ s, ∑ c ∈ s, g a b c := by
        rw [← e4, ← e3]
        exact hstep1
    _ ≤ 8 * szB w M T σ * (3 * Ctp) := mul_le_mul_of_nonneg_left h7 (by positivity)
    _ = 24 * Ctp * szB w M T σ := by ring

end TMA.T3
end
end Src_TMA_Trace3Aux4

section Src_TMA_Trace3Aux5
/-
Written for Kristian Muri Knausgård, drafted with Claude (Anthropic), 22 November 2026.

TMA/Trace3Aux5.lean — the main term of the third trace:
* the prime sum `Bsum` by `primeSum_asymp` (with the polynomial of `bgsum_smooth_on`);
* `Re t3 K0 ≤ C₃(σ) (∫h³) D + C T`.
See BLUEPRINT.md, module "T3" (main term, total).
-/

open MeasureTheory Complex
open scoped BigOperators ArithmeticFunction Real

noncomputable section
namespace TMA.T3

/-- `Σ_{2 ≤ n ≤ Nmax} Λ(n)²/n (bg(λ_n) + bg(-λ_n)) ≤ (σ log T)² J3 + C σ log T` -/
theorem Bsum_le {σ : ℝ} (hσ : 0 < σ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (w : HeightWeight) (T : ℝ), Sep w T σ → 2 ≤ T ^ σ →
      Bsum T σ ≤ (σ * Real.log T) ^ 2 * J3 + C * (σ * Real.log T) := by
  obtain ⟨F, hF, hFeq⟩ := bgsum_smooth_on
  obtain ⟨C, hC⟩ := primeSum_asymp F hF
  refine ⟨|C|, abs_nonneg C, fun w T hS hX => ?_⟩
  have hT := hS.T_pos
  have hL := hS.log_pos
  have hσL : 0 < σ * Real.log T := mul_pos hσ hL
  have hlogX : Real.log (T ^ σ) = σ * Real.log T := Real.log_rpow hT σ
  have hX0 : (0 : ℝ) ≤ T ^ σ := by linarith
  have h1 := hC (T ^ σ) hX
  rw [hlogX] at h1
  have hJ : ∫ r in (0 : ℝ)..1, r * F r = J3 := by
    unfold J3
    refine intervalIntegral.integral_congr (fun r hr => ?_)
    rw [Set.uIcc_of_le (by norm_num)] at hr
    rw [hFeq r hr]
  rw [hJ] at h1
  have hsum : ∑ n ∈ Finset.Icc 2 ⌊T ^ σ⌋₊, Λ n ^ 2 / n * F (Real.log n / (σ * Real.log T))
      = Bsum T σ := by
    unfold Bsum
    have hstep : ∑ n ∈ Finset.Icc 2 ⌊T ^ σ⌋₊, Λ n ^ 2 / n * F (Real.log n / (σ * Real.log T))
        = ∑ n ∈ Finset.Icc 2 ⌊T ^ σ⌋₊,
            Λ n ^ 2 / n * (bg (lamOf T σ n) + bg (-(lamOf T σ n))) := by
      refine Finset.sum_congr rfl (fun n hn => ?_)
      rw [Finset.mem_Icc] at hn
      have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn.1
      have hnX : (n : ℝ) ≤ T ^ σ := (Nat.le_floor_iff hX0).mp hn.2
      have hlog0 : 0 ≤ Real.log n := Real.log_nonneg (by linarith)
      have hlog1 : Real.log n ≤ σ * Real.log T := by
        rw [← hlogX]
        exact Real.log_le_log (by linarith) hnX
      have hmem : Real.log n / (σ * Real.log T) ∈ Set.Icc (0 : ℝ) 1 :=
        ⟨div_nonneg hlog0 hσL.le, (div_le_one hσL).mpr hlog1⟩
      rw [← hFeq _ hmem]
      rfl
    rw [hstep]
    apply Finset.sum_subset
    · apply Finset.Icc_subset_Icc_right
      unfold Nmax
      exact Nat.floor_le_floor (by linarith)
    · intro n hn hn'
      rw [Finset.mem_Icc] at hn hn'
      have hlt : ⌊T ^ σ⌋₊ < n := by
        by_contra hc
        exact hn' ⟨hn.1, not_lt.mp hc⟩
      have hXn : T ^ σ < n := Nat.lt_of_floor_lt hlt
      have hlam : 1 < lamOf T σ n := by
        unfold lamOf
        rw [one_lt_div hσL, ← hlogX]
        exact Real.log_lt_log (by linarith) hXn
      have hb1 : bg (lamOf T σ n) = 0 := by
        unfold bg
        apply Gg_eq_zero
        right; left
        exact lt_of_lt_of_le hlam (le_abs_self _)
      have hb2 : bg (-(lamOf T σ n)) = 0 := by
        unfold bg
        apply Gg_eq_zero
        right; left
        rw [abs_neg]
        exact lt_of_lt_of_le hlam (le_abs_self _)
      rw [hb1, hb2]
      ring
  rw [hsum] at h1
  have h2 := (abs_le.mp h1).2
  have h3 : C * (σ * Real.log T) ≤ |C| * (σ * Real.log T) :=
    mul_le_mul_of_nonneg_right (le_abs_self C) hσL.le
  linarith

theorem re_le_of_norm_sub_le {z : ℂ} {r e : ℝ} (h : ‖z - (r : ℂ)‖ ≤ e) : z.re ≤ r + e := by
  have h1 : (z - (r : ℂ)).re ≤ ‖z - (r : ℂ)‖ := Complex.re_le_norm _
  simp only [Complex.sub_re, Complex.ofReal_re] at h1
  linarith

/-- **Main term.** `Re t3 K0 ≤ C₃(σ) (∫h³) D + C T`. -/
theorem t3_K0_upper (w : HeightWeight) {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, Sep w T σ → 2 ≤ T ^ σ →
      (t3 (K0 w.k T σ)).re ≤ C3 σ * w.kap3 * Dsc T + C * T := by
  obtain ⟨M, hM0, hM⟩ := w.exists_k_bound
  obtain ⟨CB, hCB0, hCB⟩ := Bsum_le hσ
  obtain ⟨CQ, hCQ0, hCQ⟩ := QQQ_bound
  obtain ⟨Cu, hCu0, hCu⟩ := primeSum_Nmax_le hσ hσ1
  set Ik : ℝ := ∫ y, ‖w.k y‖ with hIk
  have hIk0 : 0 ≤ Ik := integral_norm_k_nonneg w
  have hκ := w.kappa_pos
  have hkt := kt_nonneg w
  have hI3 : 0 ≤ I3 := Gg_nonneg 0 0
  have hJ3 : 0 ≤ J3 := J3_nonneg
  set c1 : ℝ := 20 * w.kappa * M * Ik ^ 2 / σ ^ 3 with hc1
  have hc10 : 0 ≤ c1 := by positivity
  refine ⟨c1 + 6 * c1 * Cu + 3 * kt w * CB / σ + 2 * CQ * M * Ik ^ 2 / σ ^ 2, by positivity,
    fun T hS hX => ?_⟩
  have hT := hS.T_pos
  have hT1 : 1 ≤ T := by linarith [hS.six_le]
  have hL1 := hS.one_le_log
  have hL := hS.log_pos
  have hA := hS.A_pos
  have hell0 : 0 ≤ Real.log (T / (2 * π)) := hS.ell_nonneg
  have hellL : Real.log (T / (2 * π)) ≤ Real.log T := hS.ell_le
  set L : ℝ := Real.log T with hLdef
  set ell : ℝ := Real.log (T / (2 * π)) with hell
  -- values of the scale factors
  have hAval : Asc T σ = T * (σ * L) := rfl
  have hM3 : M3 T σ = T / (σ ^ 2 * L ^ 2) := by
    unfold M3
    rw [hAval]
    field_simp
  have hev : evErr w M T σ = c1 / L ^ 3 := by
    unfold evErr
    rw [hAval, abs_of_pos hT, hc1, ← hIk]
    field_simp
    ring
  have hsz : szB w M T σ = 2 * T * M * Ik ^ 2 / (σ ^ 2 * L ^ 2) := by
    unfold szB
    rw [hAval, ← hIk]
    field_simp
  have hM30 : 0 ≤ M3 T σ := by
    rw [hM3]
    positivity
  have hev0 : 0 ≤ evErr w M T σ := evErr_nonneg w hM0 hA
  -- the expansion
  set P0 : ℝ → ℂ := packet w.k T σ 0 with hP0
  set Q : ℝ → ℂ := Qk w.k T σ with hQ
  have hexp : t3 (K0 w.k T σ)
      = (ell : ℂ) ^ 3 * tri P0 P0 P0 + (ell : ℂ) * (tri Q Q P0 + tri Q P0 Q + tri P0 Q Q)
        - tri Q Q Q := by
    rw [t3_eq_tri, K0_eq, tri_expand (continuous_packet w T σ 0) (continuous_Qk w T σ),
      tri_Q_P_P w hσ hS, tri_P_Q_P w hσ hS, tri_P_P_Q w hσ hS]
    ring
  have hre : (t3 (K0 w.k T σ)).re
      = ell ^ 3 * (tri P0 P0 P0).re + ell * (tri Q Q P0 + tri Q P0 Q + tri P0 Q Q).re
        - (tri Q Q Q).re := by
    rw [hexp]
    simp only [Complex.sub_re, Complex.add_re, ← Complex.ofReal_pow, Complex.re_ofReal_mul]
  -- the three bounds
  have hb000 : (tri P0 P0 P0).re ≤ M3 T σ * (I3 * kt w) + evErr w M T σ :=
    re_le_of_norm_sub_le (eval_000 w hM hA)
  have hb2 : (tri Q Q P0 + tri Q P0 Q + tri P0 Q Q).re
      ≤ 3 * (M3 T σ * kt w) * Bsum T σ + 6 * evErr w M T σ * SLam T σ :=
    re_le_of_norm_sub_le (two_Q_eval w hM hσ hS)
  have hb3 : -(tri Q Q Q).re ≤ CQ * szB w M T σ := by
    have h1 := Complex.abs_re_le_norm (tri Q Q Q)
    have h2 := hCQ w M T σ hM hσ hS
    have h3 := neg_abs_le (tri Q Q Q).re
    linarith
  have hBs : Bsum T σ ≤ (σ * L) ^ 2 * J3 + CB * (σ * L) := hCB w T hS hX
  have hSL : SLam T σ ≤ Cu * L ^ 2 := hCu w T hS
  -- step 1: three central packets
  have hstep1 : ell ^ 3 * (tri P0 P0 P0).re ≤ T * L * I3 * kt w / σ ^ 2 + c1 := by
    have hnn : 0 ≤ M3 T σ * (I3 * kt w) + evErr w M T σ := by positivity
    have hpow : ell ^ 3 ≤ L ^ 3 := pow_le_pow_left₀ hell0 hellL 3
    calc ell ^ 3 * (tri P0 P0 P0).re ≤ ell ^ 3 * (M3 T σ * (I3 * kt w) + evErr w M T σ) :=
          mul_le_mul_of_nonneg_left hb000 (by positivity)
      _ ≤ L ^ 3 * (M3 T σ * (I3 * kt w) + evErr w M T σ) := mul_le_mul_of_nonneg_right hpow hnn
      _ = T * L * I3 * kt w / σ ^ 2 + c1 := by
          rw [hM3, hev]
          field_simp
  -- step 2: one central packet
  have hstep2 : ell * (tri Q Q P0 + tri Q P0 Q + tri P0 Q Q).re
      ≤ 3 * T * L * kt w * J3 + 3 * kt w * CB / σ * T + 6 * c1 * Cu := by
    set R2 : ℝ := 3 * (M3 T σ * kt w) * ((σ * L) ^ 2 * J3 + CB * (σ * L))
      + 6 * evErr w M T σ * (Cu * L ^ 2) with hR2
    have hR20 : 0 ≤ R2 := by positivity
    have h1 : (tri Q Q P0 + tri Q P0 Q + tri P0 Q Q).re ≤ R2 := by
      have h2 : 3 * (M3 T σ * kt w) * Bsum T σ
          ≤ 3 * (M3 T σ * kt w) * ((σ * L) ^ 2 * J3 + CB * (σ * L)) :=
        mul_le_mul_of_nonneg_left hBs (by positivity)
      have h3 : 6 * evErr w M T σ * SLam T σ ≤ 6 * evErr w M T σ * (Cu * L ^ 2) :=
        mul_le_mul_of_nonneg_left hSL (by positivity)
      linarith
    calc ell * (tri Q Q P0 + tri Q P0 Q + tri P0 Q Q).re ≤ ell * R2 :=
          mul_le_mul_of_nonneg_left h1 hell0
      _ ≤ L * R2 := mul_le_mul_of_nonneg_right hellL hR20
      _ = 3 * T * L * kt w * J3 + 3 * kt w * CB / σ * T + 6 * c1 * Cu := by
          rw [hR2, hM3, hev]
          field_simp
  -- step 3: no central packet
  have hstep3 : -(tri Q Q Q).re ≤ 2 * CQ * M * Ik ^ 2 / σ ^ 2 * T := by
    have h1 : CQ * szB w M T σ = 2 * CQ * M * Ik ^ 2 / σ ^ 2 * T / L ^ 2 := by
      rw [hsz]
      field_simp
    have h2 : 2 * CQ * M * Ik ^ 2 / σ ^ 2 * T / L ^ 2 ≤ 2 * CQ * M * Ik ^ 2 / σ ^ 2 * T := by
      apply div_le_self (by positivity)
      exact one_le_pow₀ hL1
    linarith
  -- total
  have hmain : T * L * I3 * kt w / σ ^ 2 + 3 * T * L * kt w * J3 = C3 σ * w.kap3 * Dsc T := by
    unfold C3 Dsc kt
    rw [← hLdef]
    field_simp
  have hconst : c1 + 6 * c1 * Cu ≤ (c1 + 6 * c1 * Cu) * T := by
    have h0 : 0 ≤ c1 + 6 * c1 * Cu := by positivity
    exact le_mul_of_one_le_right h0 hT1
  rw [hre]
  calc ell ^ 3 * (tri P0 P0 P0).re + ell * (tri Q Q P0 + tri Q P0 Q + tri P0 Q Q).re
        - (tri Q Q Q).re
      ≤ (T * L * I3 * kt w / σ ^ 2 + c1)
        + (3 * T * L * kt w * J3 + 3 * kt w * CB / σ * T + 6 * c1 * Cu)
        + 2 * CQ * M * Ik ^ 2 / σ ^ 2 * T := by linarith
    _ = C3 σ * w.kap3 * Dsc T + (c1 + 6 * c1 * Cu)
        + (3 * kt w * CB / σ + 2 * CQ * M * Ik ^ 2 / σ ^ 2) * T := by
        rw [← hmain]
        ring
    _ ≤ C3 σ * w.kap3 * Dsc T
        + (c1 + 6 * c1 * Cu + 3 * kt w * CB / σ + 2 * CQ * M * Ik ^ 2 / σ ^ 2) * T := by
        have e : (c1 + 6 * c1 * Cu + 3 * kt w * CB / σ + 2 * CQ * M * Ik ^ 2 / σ ^ 2) * T
            = (c1 + 6 * c1 * Cu) * T + (3 * kt w * CB / σ + 2 * CQ * M * Ik ^ 2 / σ ^ 2) * T := by
          ring
        rw [e]
        linarith

end TMA.T3
end
end Src_TMA_Trace3Aux5

section Src_TMG_Basic
/-
Written for Kristian Muri Knausgård, drafted with Claude (Anthropic), 22 November 2026.

TMG/Basic.lean — the third-moment bound for a GENERAL window (the class of Theorem 1.1 of the paper):
bounded measurable g >= 0 on [-1/2, 1/2] with integral 1.  Definitions only.
The window-independent objects (HeightWeight, packets, K0, Kfull, Kfin, cw, phase, Asc, Dsc, ...) are those of
TMA/Basic.lean; the modules TMA/Kernel, TMA/Packets, TMA/PrimeSum, TMA/Weight are reused unchanged.
-/

open MeasureTheory Complex
open scoped BigOperators ArithmeticFunction Real

noncomputable section

namespace TMG

/-- A window: bounded measurable, nonnegative, zero outside `[-1/2, 1/2]`, integral one. -/
structure Window where
  g : ℝ → ℝ
  meas : Measurable g
  nonneg : ∀ u, 0 ≤ g u
  bound : ℝ
  le_bound : ∀ u, g u ≤ bound
  supp : ∀ u, 1 / 2 < |u| → g u = 0
  integral_eq_one : ∫ u, g u = 1

/-- autocorrelation `a_g(r) = ∫ g(u) g(u+r) du` -/
def ag (W : Window) (r : ℝ) : ℝ := ∫ u, W.g u * W.g (u + r)

/-- triple correlation `G(r,s) = ∫ g(u) g(u+r) g(u+r+s) du` -/
def Gg (W : Window) (r s : ℝ) : ℝ := ∫ u, W.g u * W.g (u + r) * W.g (u + r + s)

/-- `b_g(s) = G(0,s)` -/
def bg (W : Window) (s : ℝ) : ℝ := Gg W 0 s

/-- `ĝ(x) = ∫ g(u) e^{ixu} du` -/
def ghat (W : Window) (x : ℝ) : ℂ := ∫ u, (W.g u : ℂ) * Complex.exp (Complex.I * x * u)

def I2 (W : Window) : ℝ := ag W 0
def I3 (W : Window) : ℝ := Gg W 0 0
def J2 (W : Window) : ℝ := 2 * ∫ r in (0 : ℝ)..1, r * ag W r
def J3 (W : Window) : ℝ := ∫ r in (0 : ℝ)..1, r * (bg W r + bg W (-r))

/-- `C₂ = (1/σ) ∫g² + σ ∬ |u-v| g g` -/
def C2 (W : Window) (σ : ℝ) : ℝ := I2 W / σ + σ * J2 W

/-- `C₃ = (1/σ²) ∫g³ + 3 ∬ |u-v| g² g` -/
def C3 (W : Window) (σ : ℝ) : ℝ := I3 W / σ ^ 2 + 3 * J3 W

/-- `K_t(g) = C₃ - 2 t C₂ + t²` at full bandwidth -/
def Kt (W : Window) (t : ℝ) : ℝ := C3 W 1 - 2 * t * C2 W 1 + t ^ 2

/-- second trace functional -/
def t2 (W : Window) (K : ℝ → ℂ) : ℝ := ∫ x in (-1 : ℝ)..1, ag W x * ‖K x‖ ^ 2

/-- third trace functional -/
def t3 (W : Window) (K : ℝ → ℂ) : ℂ :=
  ∫ x in (-1 : ℝ)..1, ∫ y in (-1 : ℝ)..1, (Gg W x y : ℂ) * (K x * K y * K (-x - y))

end TMG
end
end Src_TMG_Basic

section Src_TMG_Window
/-
Written for Kristian Muri Knausgård, drafted with Claude (Anthropic), 22 November 2026.
TMG/Window.lean — generic facts about a window and its correlations (no smoothness of g is used).
STATUS: all statements proved.  See BLUEPRINT.md, section "General windows".
Helper lemmas live in the namespace `TMG.Win`; the exported interface is in `TMG`.
The template is TMA/Window.lean; the new ingredient is the continuity of translation in `L¹`
(`Win.tendsto_transL1`), which replaces the Lipschitz bounds of the quadratic window.
-/

open MeasureTheory Complex
open scoped BigOperators Real ComplexConjugate ComplexOrder

noncomputable section
namespace TMG

variable (W : Window)

theorem Window.integrable : Integrable W.g := integrable_of_integral_eq_one W.integral_eq_one

theorem Window.one_le_bound : 1 ≤ W.bound := by
  have hle : ∀ u, W.g u ≤ Set.indicator (Set.Icc (-(1 / 2 : ℝ)) (1 / 2)) (fun _ => W.bound) u := by
    intro u
    by_cases hu : u ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2)
    · rw [Set.indicator_of_mem hu]
      exact W.le_bound u
    · have h : 1 / 2 < |u| := by
        rw [Set.mem_Icc, not_and_or, not_le, not_le] at hu
        rcases hu with hu | hu
        · exact lt_abs.mpr (Or.inr (by linarith))
        · exact lt_abs.mpr (Or.inl hu)
      rw [Set.indicator_of_notMem hu, W.supp u h]
  have i1 : Integrable (Set.indicator (Set.Icc (-(1 / 2 : ℝ)) (1 / 2)) (fun _ => W.bound)) :=
    (integrable_indicator_iff measurableSet_Icc).mpr (integrableOn_const (by simp))
  have h := integral_mono W.integrable i1 hle
  rw [W.integral_eq_one, integral_indicator_const _ measurableSet_Icc,
    Real.volume_real_Icc_of_le (by norm_num)] at h
  simp only [smul_eq_mul] at h
  linarith

/-! ### helpers: the window -/
namespace Win

theorem bound_pos : 0 < W.bound := lt_of_lt_of_le one_pos W.one_le_bound

theorem norm_g_le (u : ℝ) : ‖W.g u‖ ≤ W.bound := by
  rw [Real.norm_eq_abs, abs_of_nonneg (W.nonneg u)]
  exact W.le_bound u

/-- two points at distance more than 1 cannot both lie in the support -/
theorem g_mul_eq_zero {u v : ℝ} (h : 1 < |u - v|) : W.g u * W.g v = 0 := by
  by_cases hu : |u| ≤ 1 / 2
  · have hv : 1 / 2 < |v| := by
      by_contra hc
      have hv' := abs_le.mp (not_lt.mp hc)
      have hu' := abs_le.mp hu
      have : |u - v| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
      linarith
    rw [W.supp v hv, mul_zero]
  · rw [W.supp u (not_le.mp hu), zero_mul]

theorem integrable_gg (t : ℝ) : Integrable (fun u => W.g u * W.g (u + t)) :=
  (W.integrable.comp_add_right t).bdd_mul (c := W.bound) W.meas.aestronglyMeasurable
    (ae_of_all _ (norm_g_le W))

theorem integrable_ggg (r s : ℝ) : Integrable (fun u => W.g u * W.g (u + r) * W.g (u + r + s)) :=
  (integrable_gg W r).mul_bdd (c := W.bound)
    (show Measurable fun u : ℝ => W.g (u + r + s) from
      W.meas.comp ((measurable_id.add_const r).add_const s)).aestronglyMeasurable
    (ae_of_all _ fun _ => norm_g_le W _)

theorem integrable_sq : Integrable (fun u => W.g u ^ 2) :=
  (W.integrable.bdd_mul (c := W.bound) W.meas.aestronglyMeasurable
    (ae_of_all _ (norm_g_le W))).congr (ae_of_all _ fun u => (sq (W.g u)).symm)

end Win

open Win

/-! ### autocorrelation -/
theorem ag_nonneg (r : ℝ) : 0 ≤ ag W r :=
  integral_nonneg fun u => mul_nonneg (W.nonneg u) (W.nonneg _)

theorem ag_le (r : ℝ) : ag W r ≤ W.bound := by
  have h : ag W r ≤ ∫ u, W.g u * W.bound :=
    integral_mono (integrable_gg W r) (W.integrable.mul_const _)
      (fun u => mul_le_mul_of_nonneg_left (W.le_bound _) (W.nonneg u))
  rw [integral_mul_const, W.integral_eq_one] at h
  linarith

theorem ag_neg (r : ℝ) : ag W (-r) = ag W r := by
  unfold ag
  rw [← integral_add_right_eq_self (fun u => W.g u * W.g (u + -r)) r]
  refine integral_congr_ae (ae_of_all _ fun u => ?_)
  simp only [add_neg_cancel_right]
  ring

theorem ag_eq_zero {r : ℝ} (h : 1 < |r|) : ag W r = 0 := by
  unfold ag
  have h0 : ∀ u, W.g u * W.g (u + r) = 0 := fun u =>
    g_mul_eq_zero W (by rw [show u - (u + r) = -r by ring, abs_neg]; exact h)
  simp_rw [h0]
  exact integral_zero _ _

/-! ### helpers: continuity of translation in `L¹` -/
namespace Win

/-- the `L¹` distance of two integrable functions, through `Lp` -/
theorem norm_toLp_sub {a b : ℝ → ℝ} (ha : MemLp a 1 volume) (hb : MemLp b 1 volume) :
    ‖ha.toLp a - hb.toLp b‖ = ∫ u, |a u - b u| := by
  rw [← MemLp.toLp_sub ha hb, L1.norm_eq_integral_norm]
  refine integral_congr_ae ?_
  filter_upwards [MemLp.coeFn_toLp (ha.sub hb)] with u hu
  rw [hu]
  rfl

/-- translation is continuous in `L¹`: `∫ |f(u+d) - f(u)| du → 0` as `d → 0`, for integrable `f` -/
theorem tendsto_transL1 {f : ℝ → ℝ} (hf : Integrable f) :
    Filter.Tendsto (fun d : ℝ => ∫ u, |f (u + d) - f u|) (nhds 0) (nhds 0) := by
  have hfL : MemLp f 1 volume := memLp_one_iff_integrable.mpr hf
  let g : ℝ → C(ℝ, ℝ) := fun d => ⟨fun u => u + d, by fun_prop⟩
  have hg : Continuous g := ContinuousMap.continuous_of_continuous_uncurry g (by
    show Continuous fun p : ℝ × ℝ => p.2 + p.1
    fun_prop)
  have hgm : ∀ d, MeasurePreserving (g d) volume volume := fun d =>
    measurePreserving_add_right volume d
  have hc : Continuous fun d => Lp.compMeasurePreserving (g d) (hgm d) (hfL.toLp f) :=
    Continuous.compMeasurePreservingLp continuous_const hg hgm ENNReal.one_ne_top
  have hc2 : Continuous fun d =>
      ‖Lp.compMeasurePreserving (g d) (hgm d) (hfL.toLp f) - hfL.toLp f‖ :=
    (hc.sub continuous_const).norm
  have e : ∀ d, ‖Lp.compMeasurePreserving (g d) (hgm d) (hfL.toLp f) - hfL.toLp f‖
      = ∫ u, |f (u + d) - f u| := by
    intro d
    rw [Lp.toLp_compMeasurePreserving hfL (hgm d), norm_toLp_sub]
    rfl
  simp_rw [e] at hc2
  have h0 := hc2.tendsto 0
  simpa using h0

/-- `L¹` modulus of continuity of the window: `tr d = ∫ |g(u+d) - g(u)| du` -/
def tr (d : ℝ) : ℝ := ∫ u, |W.g (u + d) - W.g u|

theorem integrable_abs_shift (a b : ℝ) : Integrable (fun u => |W.g (u + a) - W.g (u + b)|) :=
  ((W.integrable.comp_add_right a).sub (W.integrable.comp_add_right b)).abs

theorem tr_nonneg (d : ℝ) : 0 ≤ tr W d := integral_nonneg fun _ => abs_nonneg _

theorem transL1 (a b : ℝ) : ∫ u, |W.g (u + a) - W.g (u + b)| = tr W (a - b) := by
  unfold tr
  rw [← integral_add_right_eq_self (fun v => |W.g (v + (a - b)) - W.g v|) b]
  refine integral_congr_ae (ae_of_all _ fun u => ?_)
  simp only [add_add_sub_cancel]

theorem tendsto_tr : Filter.Tendsto (tr W) (nhds 0) (nhds 0) := tendsto_transL1 W.integrable

theorem exists_tr_le {ε : ℝ} (hε : 0 < ε) : ∃ δ > 0, ∀ d : ℝ, |d| ≤ δ → tr W d ≤ ε := by
  obtain ⟨δ, hδ, h⟩ := (Metric.tendsto_nhds_nhds.mp (tendsto_tr W)) ε hε
  refine ⟨δ / 2, by positivity, fun d hd => ?_⟩
  have h1 := h (x := d) (by rw [Real.dist_eq, sub_zero]; linarith)
  rw [Real.dist_eq, sub_zero] at h1
  exact (le_abs_self _).trans h1.le

/-- `|a_g(r) - a_g(r')| ≤ bound · ‖τ_{r-r'} g - g‖₁` -/
theorem ag_diff_le (r r' : ℝ) : |ag W r - ag W r'| ≤ W.bound * tr W (r - r') := by
  have h1 : ag W r - ag W r' = ∫ u, W.g u * (W.g (u + r) - W.g (u + r')) := by
    unfold ag
    rw [← integral_sub (integrable_gg W r) (integrable_gg W r')]
    refine integral_congr_ae (ae_of_all _ fun u => ?_)
    simp only
    ring
  rw [h1, ← transL1]
  calc |∫ u, W.g u * (W.g (u + r) - W.g (u + r'))|
      ≤ ∫ u, |W.g u * (W.g (u + r) - W.g (u + r'))| := abs_integral_le_integral_abs
    _ ≤ ∫ u, W.bound * |W.g (u + r) - W.g (u + r')| :=
        integral_mono_of_nonneg (ae_of_all _ fun u => abs_nonneg _)
          ((integrable_abs_shift W r r').const_mul _)
          (ae_of_all _ fun u => by
            simp only
            rw [abs_mul, abs_of_nonneg (W.nonneg u)]
            exact mul_le_mul_of_nonneg_right (W.le_bound u) (abs_nonneg _))
    _ = W.bound * ∫ u, |W.g (u + r) - W.g (u + r')| := integral_const_mul _ _

end Win

/-- uniform continuity of the autocorrelation -/
theorem ag_unifCont : ∀ η > 0, ∃ δ > 0, ∀ r d : ℝ, |d| ≤ δ → |ag W (r + d) - ag W r| ≤ η := by
  intro η hη
  have hB : 0 < W.bound := bound_pos W
  obtain ⟨δ, hδ, h⟩ := exists_tr_le W (div_pos hη hB)
  refine ⟨δ, hδ, fun r d hd => ?_⟩
  have h1 := ag_diff_le W (r + d) r
  rw [add_sub_cancel_left] at h1
  have h2 := h d hd
  calc |ag W (r + d) - ag W r| ≤ W.bound * tr W d := h1
    _ ≤ W.bound * (η / W.bound) := mul_le_mul_of_nonneg_left h2 hB.le
    _ = η := by field_simp

theorem continuous_ag : Continuous (ag W) := by
  rw [Metric.continuous_iff]
  intro b ε hε
  obtain ⟨δ, hδ, h⟩ := ag_unifCont W (ε / 2) (by positivity)
  refine ⟨δ, hδ, fun a ha => ?_⟩
  have h1 := h b (a - b) (by rw [← Real.dist_eq]; exact ha.le)
  rw [add_sub_cancel] at h1
  rw [Real.dist_eq]
  linarith

/-! ### triple correlation -/
theorem Gg_nonneg (r s : ℝ) : 0 ≤ Gg W r s :=
  integral_nonneg fun u => mul_nonneg (mul_nonneg (W.nonneg u) (W.nonneg _)) (W.nonneg _)

theorem Gg_le (r s : ℝ) : Gg W r s ≤ W.bound ^ 2 := by
  have hB : 0 ≤ W.bound := (bound_pos W).le
  have h : Gg W r s ≤ ∫ u, W.g u * W.bound * W.bound :=
    integral_mono (integrable_ggg W r s) ((W.integrable.mul_const _).mul_const _)
      (fun u => mul_le_mul (mul_le_mul_of_nonneg_left (W.le_bound _) (W.nonneg u)) (W.le_bound _)
        (W.nonneg _) (mul_nonneg (W.nonneg u) hB))
  rw [integral_mul_const, integral_mul_const, W.integral_eq_one] at h
  linarith [sq (W.bound)]

theorem Gg_eq_zero {r s : ℝ} (h : 1 < |r| ∨ 1 < |s| ∨ 1 < |r + s|) : Gg W r s = 0 := by
  unfold Gg
  have h0 : ∀ u, W.g u * W.g (u + r) * W.g (u + r + s) = 0 := by
    intro u
    rcases h with h | h | h
    · rw [g_mul_eq_zero W (by rw [show u - (u + r) = -r by ring, abs_neg]; exact h), zero_mul]
    · rw [mul_assoc, g_mul_eq_zero W (u := u + r) (v := u + r + s)
        (by rw [show u + r - (u + r + s) = -s by ring, abs_neg]; exact h), mul_zero]
    · rw [mul_right_comm, g_mul_eq_zero W (u := u) (v := u + r + s)
        (by rw [show u - (u + r + s) = -(r + s) by ring, abs_neg]; exact h), zero_mul]
  simp_rw [h0]
  exact integral_zero _ _

namespace Win

/-- `|G(r,s) - G(r',s')| ≤ bound² (‖τ_{r-r'} g - g‖₁ + ‖τ_{(r+s)-(r'+s')} g - g‖₁)` -/
theorem Gg_diff_le (r s r' s' : ℝ) :
    |Gg W r s - Gg W r' s'| ≤ W.bound ^ 2 * (tr W (r - r') + tr W (r + s - (r' + s'))) := by
  have hB : 0 ≤ W.bound := (bound_pos W).le
  have h1 : Gg W r s - Gg W r' s' = ∫ u, (W.g u * (W.g (u + r) - W.g (u + r')) * W.g (u + r + s)
      + W.g u * W.g (u + r') * (W.g (u + (r + s)) - W.g (u + (r' + s')))) := by
    unfold Gg
    rw [← integral_sub (integrable_ggg W r s) (integrable_ggg W r' s')]
    refine integral_congr_ae (ae_of_all _ fun u => ?_)
    simp only [← add_assoc]
    ring
  have hb : ∀ u, |W.g u * (W.g (u + r) - W.g (u + r')) * W.g (u + r + s)
      + W.g u * W.g (u + r') * (W.g (u + (r + s)) - W.g (u + (r' + s')))|
      ≤ W.bound ^ 2 * |W.g (u + r) - W.g (u + r')|
        + W.bound ^ 2 * |W.g (u + (r + s)) - W.g (u + (r' + s'))| := by
    intro u
    have g0 := W.nonneg u
    have g1 := W.le_bound u
    have g2 := W.nonneg (u + r')
    have g3 := W.le_bound (u + r')
    have g4 := W.nonneg (u + r + s)
    have g5 := W.le_bound (u + r + s)
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [abs_mul, abs_mul, abs_of_nonneg g0, abs_of_nonneg g4]
      have hA := abs_nonneg (W.g (u + r) - W.g (u + r'))
      calc W.g u * |W.g (u + r) - W.g (u + r')| * W.g (u + r + s)
          ≤ W.bound * |W.g (u + r) - W.g (u + r')| * W.bound :=
            mul_le_mul (mul_le_mul_of_nonneg_right g1 hA) g5 g4 (mul_nonneg hB hA)
        _ = W.bound ^ 2 * |W.g (u + r) - W.g (u + r')| := by ring
    · rw [abs_mul, abs_mul, abs_of_nonneg g0, abs_of_nonneg g2]
      have hA := abs_nonneg (W.g (u + (r + s)) - W.g (u + (r' + s')))
      calc W.g u * W.g (u + r') * |W.g (u + (r + s)) - W.g (u + (r' + s'))|
          ≤ W.bound * W.bound * |W.g (u + (r + s)) - W.g (u + (r' + s'))| :=
            mul_le_mul_of_nonneg_right (mul_le_mul g1 g3 g2 hB) hA
        _ = W.bound ^ 2 * |W.g (u + (r + s)) - W.g (u + (r' + s'))| := by ring
  rw [h1, ← transL1 W r r', ← transL1 W (r + s) (r' + s')]
  calc |∫ u, (W.g u * (W.g (u + r) - W.g (u + r')) * W.g (u + r + s)
        + W.g u * W.g (u + r') * (W.g (u + (r + s)) - W.g (u + (r' + s'))))|
      ≤ ∫ u, |W.g u * (W.g (u + r) - W.g (u + r')) * W.g (u + r + s)
        + W.g u * W.g (u + r') * (W.g (u + (r + s)) - W.g (u + (r' + s')))| :=
        abs_integral_le_integral_abs
    _ ≤ ∫ u, (W.bound ^ 2 * |W.g (u + r) - W.g (u + r')|
        + W.bound ^ 2 * |W.g (u + (r + s)) - W.g (u + (r' + s'))|) :=
        integral_mono_of_nonneg (ae_of_all _ fun u => abs_nonneg _)
          (((integrable_abs_shift W r r').const_mul _).add
            ((integrable_abs_shift W (r + s) (r' + s')).const_mul _))
          (ae_of_all _ hb)
    _ = W.bound ^ 2 * ((∫ u, |W.g (u + r) - W.g (u + r')|)
        + ∫ u, |W.g (u + (r + s)) - W.g (u + (r' + s'))|) := by
        rw [integral_add ((integrable_abs_shift W r r').const_mul _)
          ((integrable_abs_shift W (r + s) (r' + s')).const_mul _), integral_const_mul,
          integral_const_mul, mul_add]

end Win

/-- uniform continuity of the triple correlation -/
theorem Gg_unifCont : ∀ η > 0, ∃ δ > 0, ∀ r s d e : ℝ, |d| ≤ δ → |e| ≤ δ →
    |Gg W (r + d) (s + e) - Gg W r s| ≤ η := by
  intro η hη
  have hB : 0 < W.bound := bound_pos W
  have hB2 : 0 < W.bound ^ 2 := by positivity
  obtain ⟨δ, hδ, h⟩ := exists_tr_le W (ε := η / (2 * W.bound ^ 2)) (by positivity)
  refine ⟨δ / 2, by positivity, fun r s d e hd he => ?_⟩
  have h1 := Gg_diff_le W (r + d) (s + e) r s
  rw [add_sub_cancel_left, show r + d + (s + e) - (r + s) = d + e by ring] at h1
  have h2 := h d (by linarith)
  have h3 := h (d + e) ((abs_add_le d e).trans (by linarith))
  calc |Gg W (r + d) (s + e) - Gg W r s| ≤ W.bound ^ 2 * (tr W d + tr W (d + e)) := h1
    _ ≤ W.bound ^ 2 * (η / (2 * W.bound ^ 2) + η / (2 * W.bound ^ 2)) :=
        mul_le_mul_of_nonneg_left (add_le_add h2 h3) hB2.le
    _ = η := by field_simp; ring

/-- `G(s,0) = ∫ g(u) g(u+s)² du = b_g(-s)` -/
theorem Gg_right_zero (s : ℝ) : Gg W s 0 = bg W (-s) := by
  unfold bg Gg
  rw [← integral_add_right_eq_self (fun u => W.g u * W.g (u + 0) * W.g (u + 0 + -s)) s]
  refine integral_congr_ae (ae_of_all _ fun u => ?_)
  simp only [add_zero, add_neg_cancel_right]
  ring

/-- `G(s,-s) = ∫ g(u)² g(u+s) du = b_g(s)` -/
theorem Gg_neg (s : ℝ) : Gg W s (-s) = bg W s := by
  unfold bg Gg
  refine integral_congr_ae (ae_of_all _ fun u => ?_)
  simp only [add_zero, add_neg_cancel_right]
  ring

theorem continuous_Gg : Continuous (fun p : ℝ × ℝ => Gg W p.1 p.2) := by
  rw [Metric.continuous_iff]
  intro b ε hε
  obtain ⟨δ, hδ, h⟩ := Gg_unifCont W (ε / 2) (by positivity)
  refine ⟨δ, hδ, fun a ha => ?_⟩
  rw [Prod.dist_eq] at ha
  have h1 : |a.1 - b.1| ≤ δ := by
    rw [← Real.dist_eq]
    exact (le_max_left _ _).trans ha.le
  have h2 : |a.2 - b.2| ≤ δ := by
    rw [← Real.dist_eq]
    exact (le_max_right _ _).trans ha.le
  have h3 := h b.1 b.2 (a.1 - b.1) (a.2 - b.2) h1 h2
  rw [add_sub_cancel, add_sub_cancel] at h3
  rw [Real.dist_eq]
  linarith

theorem continuous_bg : Continuous (bg W) :=
  (continuous_Gg W).comp (Continuous.prodMk continuous_const continuous_id)

/-! ### Fourier identities -/
namespace Win

/-- the modulated window `g(u) e^{itu}`; `ghat t = ∫ gk t` -/
def gk (t u : ℝ) : ℂ := (W.g u : ℂ) * Complex.exp (Complex.I * t * u)

theorem ghat_eq (t : ℝ) : ghat W t = ∫ u, gk W t u := rfl

theorem norm_gk (t u : ℝ) : ‖gk W t u‖ = W.g u := by
  unfold gk
  rw [norm_mul, show Complex.I * (t : ℂ) * (u : ℂ) = ((t * u : ℝ) : ℂ) * Complex.I by
    push_cast; ring, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (W.nonneg u)]

theorem measurable_gk (t : ℝ) : Measurable (gk W t) := by
  unfold gk
  exact (Complex.measurable_ofReal.comp W.meas).mul (Continuous.measurable (by fun_prop))

theorem integrable_gk (t : ℝ) : Integrable (gk W t) :=
  W.integrable.mono' (measurable_gk W t).aestronglyMeasurable
    (ae_of_all _ fun u => (norm_gk W t u).le)

theorem conj_gk (t u : ℝ) : conj (gk W t u) = gk W (-t) u := by
  unfold gk
  rw [map_mul, Complex.conj_ofReal, ← Complex.exp_conj]
  congr 2
  simp only [map_mul, Complex.conj_I, Complex.conj_ofReal, Complex.ofReal_neg]
  ring

/-- Fubini and translation invariance: `∫∫ F(u) G(u+x) du dx = (∫F)(∫G)` -/
theorem conv_eq (F G : ℝ → ℂ) (hF : Integrable F) (hG : Integrable G) :
    ∫ x, ∫ u, F u * G (u + x) = (∫ u, F u) * ∫ v, G v := by
  have hint : Integrable (fun z : ℝ × ℝ => F z.1 * G (z.1 + z.2)) (volume.prod volume) :=
    (measurePreserving_prod_add volume volume).integrable_comp_of_integrable (hF.mul_prod hG)
  calc ∫ x, ∫ u, F u * G (u + x)
      = ∫ z : ℝ × ℝ, F z.1 * G (z.1 + z.2) ∂(volume.prod volume) :=
        (integral_prod_symm (fun z : ℝ × ℝ => F z.1 * G (z.1 + z.2)) hint).symm
    _ = ∫ u, ∫ x, F u * G (u + x) :=
        integral_prod (fun z : ℝ × ℝ => F z.1 * G (z.1 + z.2)) hint
    _ = ∫ u, F u * ∫ v, G v := by
        refine integral_congr_ae (ae_of_all _ fun u => ?_)
        simp only
        rw [integral_const_mul, integral_add_left_eq_self]
    _ = (∫ u, F u) * ∫ v, G v := integral_mul_const _ _

/-- an integral over `[-1,1]` of a function vanishing outside is the integral over `ℝ` -/
theorem intervalIntegral_eq_integral {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} (h : ∀ x, 1 < |x| → f x = 0) : ∫ x in (-1 : ℝ)..1, f x = ∫ x, f x := by
  rw [intervalIntegral.integral_of_le (by norm_num), ← integral_Icc_eq_integral_Ioc]
  refine setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => h x ?_
  rw [Set.mem_Icc, not_and_or, not_le, not_le] at hx
  rcases hx with hx | hx
  · exact lt_abs.mpr (Or.inr (by linarith))
  · exact lt_abs.mpr (Or.inl hx)

/-- the trigonometric sum of the positivity argument -/
def Ssum {ι : Type*} [Fintype ι] (x : ι → ℝ) (z : ι → ℂ) (u : ℝ) : ℂ :=
  ∑ b, z b * Complex.exp (-(Complex.I * x b * u))

theorem sum_gk_eq {ι : Type*} [Fintype ι] (x : ι → ℝ) (z : ι → ℂ) (u : ℝ) :
    ∑ a, ∑ b, conj (z a) * gk W (x a - x b) u * z b = ((W.g u * ‖Ssum x z u‖ ^ 2 : ℝ) : ℂ) := by
  have hS : conj (Ssum x z u) = ∑ a, conj (z a) * Complex.exp (Complex.I * x a * u) := by
    unfold Ssum
    rw [map_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [map_mul, ← Complex.exp_conj]
    congr 2
    simp only [map_neg, map_mul, Complex.conj_I, Complex.conj_ofReal]
    ring
  have hn : ((‖Ssum x z u‖ ^ 2 : ℝ) : ℂ) = conj (Ssum x z u) * Ssum x z u := by
    rw [Complex.conj_mul']
    push_cast
    rfl
  rw [Complex.ofReal_mul, hn, hS]
  unfold Ssum
  rw [Finset.sum_mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  unfold gk
  rw [show Complex.I * ((x a - x b : ℝ) : ℂ) * (u : ℂ)
      = Complex.I * (x a : ℂ) * (u : ℂ) + -(Complex.I * (x b : ℂ) * (u : ℂ)) by push_cast; ring,
    Complex.exp_add]
  ring

end Win

theorem norm_ghat_le (x : ℝ) : ‖ghat W x‖ ≤ 1 := by
  calc ‖ghat W x‖ ≤ ∫ u, ‖gk W x u‖ := norm_integral_le_integral_norm _
    _ = ∫ u, W.g u := by simp_rw [norm_gk]
    _ = 1 := W.integral_eq_one

theorem ghat_zero : ghat W 0 = 1 := by
  unfold ghat
  simp only [Complex.ofReal_zero, mul_zero, zero_mul, Complex.exp_zero, mul_one]
  rw [integral_complex_ofReal, W.integral_eq_one, Complex.ofReal_one]

theorem ghat_neg (x : ℝ) : ghat W (-x) = conj (ghat W x) := by
  rw [ghat_eq, ghat_eq, ← integral_conj]
  simp_rw [conj_gk]

/-- positive definiteness: `(ĝ(x_a - x_b))_{a,b}` is a positive semidefinite matrix
(`Σ conj z_a z_b ĝ(x_a - x_b) = ∫ g(u) |Σ_b z_b e^{-i x_b u}|² du`). -/
theorem ghat_posSemidef {ι : Type*} [Fintype ι] [DecidableEq ι] (x : ι → ℝ) :
    (Matrix.of fun a b : ι => ghat W (x a - x b)).PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
  · refine Matrix.IsHermitian.ext fun i j => ?_
    simp only [Matrix.of_apply]
    rw [show x i - x j = -(x j - x i) by ring, ghat_neg]
    rfl
  · intro z
    have key : dotProduct (star z) (Matrix.mulVec (Matrix.of fun a b : ι => ghat W (x a - x b)) z)
        = ((∫ u, W.g u * ‖Ssum x z u‖ ^ 2 : ℝ) : ℂ) := by
      rw [← integral_complex_ofReal]
      simp_rw [← sum_gk_eq]
      rw [integral_finsetSum _ (fun a _ => integrable_finsetSum _
        (fun b _ => ((integrable_gk W _).const_mul _).mul_const _))]
      simp only [dotProduct, Matrix.mulVec, Matrix.of_apply, Pi.star_apply, Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [integral_finsetSum _ (fun b _ => ((integrable_gk W _).const_mul _).mul_const _)]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [integral_mul_const, integral_const_mul, ← ghat_eq, mul_assoc]
      rfl
    rw [key, Complex.zero_le_real]
    exact integral_nonneg fun u => mul_nonneg (W.nonneg u) (by positivity)

/-- `|ĝ(x)|² = ∫_{-1}^{1} a_g(w) e^{ixw} dw` -/
theorem ghat_normSq (x : ℝ) :
    ((‖ghat W x‖ ^ 2 : ℝ) : ℂ) = ∫ w in (-1 : ℝ)..1, (ag W w : ℂ) * Complex.exp (Complex.I * x * w) := by
  rw [intervalIntegral_eq_integral (fun w hw => by rw [ag_eq_zero W hw, Complex.ofReal_zero, zero_mul])]
  have h1 : ∀ w : ℝ, (ag W w : ℂ) * Complex.exp (Complex.I * x * w)
      = ∫ u, gk W (-x) u * gk W x (u + w) := by
    intro w
    unfold ag
    rw [← integral_complex_ofReal, ← integral_mul_const]
    refine integral_congr_ae (ae_of_all _ fun u => ?_)
    simp only [gk]
    push_cast
    rw [show Complex.I * (x : ℂ) * (w : ℂ)
        = Complex.I * -(x : ℂ) * (u : ℂ) + Complex.I * (x : ℂ) * ((u : ℂ) + (w : ℂ)) by ring,
      Complex.exp_add]
    ring
  simp_rw [h1]
  rw [conv_eq _ _ (integrable_gk W (-x)) (integrable_gk W x), ← ghat_eq, ← ghat_eq, ghat_neg,
    Complex.conj_mul']
  push_cast
  rfl

/-- `ĝ(a-b) ĝ(b-c) ĝ(c-a) = ∬ G(x,y) e^{i(bx + cy - a(x+y))} dy dx` -/
theorem ghat_triple (a b c : ℝ) :
    ghat W (a - b) * ghat W (b - c) * ghat W (c - a)
      = ∫ x in (-1 : ℝ)..1, ∫ y in (-1 : ℝ)..1,
          (Gg W x y : ℂ) * Complex.exp (Complex.I * (b * x + c * y - a * (x + y))) := by
  have hin : ∀ x : ℝ, ∫ y in (-1 : ℝ)..1,
      (Gg W x y : ℂ) * Complex.exp (Complex.I * (b * x + c * y - a * (x + y)))
      = ∫ y, (Gg W x y : ℂ) * Complex.exp (Complex.I * (b * x + c * y - a * (x + y))) := fun x =>
    intervalIntegral_eq_integral (fun y hy => by
      rw [Gg_eq_zero W (Or.inr (Or.inl hy)), Complex.ofReal_zero, zero_mul])
  simp_rw [hin]
  rw [intervalIntegral_eq_integral (fun x hx => by
    have h0 : ∀ y : ℝ, (Gg W x y : ℂ) * Complex.exp (Complex.I * (b * x + c * y - a * (x + y))) = 0 :=
      fun y => by rw [Gg_eq_zero W (Or.inl hx), Complex.ofReal_zero, zero_mul]
    simp_rw [h0]
    exact integral_zero _ _)]
  have h1 : ∀ x y : ℝ, (Gg W x y : ℂ) * Complex.exp (Complex.I * (b * x + c * y - a * (x + y)))
      = ∫ u, (gk W (a - b) u * gk W (b - c) (u + x)) * gk W (c - a) (u + (x + y)) := by
    intro x y
    unfold Gg
    rw [← integral_complex_ofReal, ← integral_mul_const]
    refine integral_congr_ae (ae_of_all _ fun u => ?_)
    simp only [gk]
    rw [add_assoc u x y]
    push_cast
    rw [show Complex.I * ((b : ℂ) * (x : ℂ) + (c : ℂ) * (y : ℂ) - (a : ℂ) * ((x : ℂ) + (y : ℂ)))
        = Complex.I * ((a : ℂ) - (b : ℂ)) * (u : ℂ)
          + Complex.I * ((b : ℂ) - (c : ℂ)) * ((u : ℂ) + (x : ℂ))
          + Complex.I * ((c : ℂ) - (a : ℂ)) * ((u : ℂ) + ((x : ℂ) + (y : ℂ))) by ring,
      Complex.exp_add, Complex.exp_add]
    ring
  simp_rw [h1]
  have h2 : ∀ x : ℝ, ∫ y, ∫ u, (gk W (a - b) u * gk W (b - c) (u + x)) * gk W (c - a) (u + (x + y))
      = (∫ u, gk W (a - b) u * gk W (b - c) (u + x)) * ghat W (c - a) := by
    intro x
    have hFx : Integrable (fun u => gk W (a - b) u * gk W (b - c) (u + x)) :=
      (integrable_gk W (a - b)).mul_bdd (c := W.bound)
        ((measurable_gk W (b - c)).comp (measurable_id.add_const x)).aestronglyMeasurable
        (ae_of_all _ fun u => by
          show ‖gk W (b - c) (u + x)‖ ≤ W.bound
          rw [norm_gk]
          exact W.le_bound _)
    exact (integral_add_left_eq_self
      (fun y => ∫ u, (gk W (a - b) u * gk W (b - c) (u + x)) * gk W (c - a) (u + y)) x).trans
      (conv_eq _ _ hFx (integrable_gk W (c - a)))
  simp_rw [h2]
  rw [integral_mul_const, conv_eq _ _ (integrable_gk W (a - b)) (integrable_gk W (b - c))]
  rfl

/-! ### constants -/
namespace Win

/-- Fubini and the substitution `v = u + r`:
`∬ |u-v| F(u) G(v) = ∫ |r| (∫ F(u) G(u+r) du) dr`, when `F(u) G(v) = 0` for `|u-v| > 1`. -/
theorem absdiff_eq (F G : ℝ → ℝ) (hFm : Measurable F) (hGm : Measurable G) (hF : Integrable F)
    (hG : Integrable G) (h0 : ∀ u v, 1 < |u - v| → F u * G v = 0) :
    ∫ u, ∫ v, |u - v| * (F u * G v) = ∫ r, |r| * ∫ u, F u * G (u + r) := by
  have hprod : Integrable (fun z : ℝ × ℝ => F z.1 * G (z.1 + z.2)) (volume.prod volume) :=
    (measurePreserving_prod_add volume volume).integrable_comp_of_integrable (hF.mul_prod hG)
  have hint : Integrable (fun z : ℝ × ℝ => |z.2| * (F z.1 * G (z.1 + z.2)))
      (volume.prod volume) := by
    refine hprod.norm.mono' ?_ (ae_of_all _ fun z => ?_)
    · exact (measurable_snd.abs.mul ((hFm.comp measurable_fst).mul
        (hGm.comp (measurable_fst.add measurable_snd)))).aestronglyMeasurable
    · by_cases h : 1 < |z.2|
      · rw [h0 z.1 (z.1 + z.2) (by rw [show z.1 - (z.1 + z.2) = -z.2 by ring, abs_neg]; exact h),
          mul_zero, norm_zero]
      · rw [norm_mul, Real.norm_eq_abs, abs_abs]
        exact mul_le_of_le_one_left (norm_nonneg _) (not_lt.mp h)
  calc ∫ u, ∫ v, |u - v| * (F u * G v)
      = ∫ u, ∫ r, |r| * (F u * G (u + r)) := by
        refine integral_congr_ae (ae_of_all _ fun u => ?_)
        simp only
        rw [← integral_add_left_eq_self (fun v => |u - v| * (F u * G v)) u]
        refine integral_congr_ae (ae_of_all _ fun r => ?_)
        simp only
        rw [show u - (u + r) = -r by ring, abs_neg]
    _ = ∫ z : ℝ × ℝ, |z.2| * (F z.1 * G (z.1 + z.2)) ∂(volume.prod volume) :=
        (integral_prod (fun z : ℝ × ℝ => |z.2| * (F z.1 * G (z.1 + z.2))) hint).symm
    _ = ∫ r, ∫ u, |r| * (F u * G (u + r)) :=
        integral_prod_symm (fun z : ℝ × ℝ => |z.2| * (F z.1 * G (z.1 + z.2))) hint
    _ = ∫ r, |r| * ∫ u, F u * G (u + r) := by
        refine integral_congr_ae (ae_of_all _ fun r => ?_)
        exact integral_const_mul _ _

/-- folding `ℝ` onto `[0,1]`: `∫ |r| f(r) dr = ∫_0^1 r (f(r) + f(-r)) dr` for continuous `f`
vanishing outside `[-1,1]` -/
theorem integral_abs_mul_eq (f : ℝ → ℝ) (hf : Continuous f) (h0 : ∀ r, 1 < |r| → f r = 0) :
    ∫ r, |r| * f r = ∫ r in (0 : ℝ)..1, r * (f r + f (-r)) := by
  have hc : Continuous fun r : ℝ => |r| * f r := continuous_abs.mul hf
  rw [← intervalIntegral_eq_integral (f := fun r => |r| * f r)
      (fun r hr => by rw [h0 r hr, mul_zero]),
    ← intervalIntegral.integral_add_adjacent_intervals (hc.intervalIntegrable (-1) 0)
      (hc.intervalIntegrable 0 1)]
  have e1 : ∫ r in (-1 : ℝ)..0, |r| * f r = ∫ r in (0 : ℝ)..1, r * f (-r) := by
    have h := intervalIntegral.integral_comp_neg (a := 0) (b := 1) (fun r : ℝ => |r| * f r)
    rw [neg_zero] at h
    rw [← h]
    refine intervalIntegral.integral_congr fun r hr => ?_
    rw [Set.uIcc_of_le zero_le_one] at hr
    rw [abs_neg, abs_of_nonneg hr.1]
  have e2 : ∫ r in (0 : ℝ)..1, |r| * f r = ∫ r in (0 : ℝ)..1, r * f r := by
    refine intervalIntegral.integral_congr fun r hr => ?_
    rw [Set.uIcc_of_le zero_le_one] at hr
    rw [abs_of_nonneg hr.1]
  have i1 : IntervalIntegrable (fun r : ℝ => r * f r) volume 0 1 :=
    (continuous_id.mul hf).intervalIntegrable _ _
  have i2 : IntervalIntegrable (fun r : ℝ => r * f (-r)) volume 0 1 :=
    (continuous_id.mul (hf.comp continuous_neg)).intervalIntegrable _ _
  rw [e1, e2, add_comm, ← intervalIntegral.integral_add i1 i2]
  refine intervalIntegral.integral_congr fun r _ => ?_
  ring

/-- `b_g(r) = ∫ g(u)² g(u+r) du` -/
theorem bg_eq (r : ℝ) : bg W r = ∫ u, W.g u ^ 2 * W.g (u + r) := by
  unfold bg Gg
  refine integral_congr_ae (ae_of_all _ fun u => ?_)
  simp only [add_zero]
  ring

theorem bg_eq_zero {r : ℝ} (h : 1 < |r|) : bg W r = 0 := Gg_eq_zero W (Or.inr (Or.inl h))

theorem bg_nonneg (r : ℝ) : 0 ≤ bg W r := Gg_nonneg W 0 r

/-- `∫ |r| a_g(r) dr = J2` -/
theorem J2_eq_integral : J2 W = ∫ r, |r| * ag W r := by
  rw [integral_abs_mul_eq (ag W) (continuous_ag W) (fun r hr => ag_eq_zero W hr)]
  unfold J2
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun r _ => ?_
  rw [ag_neg]
  ring

/-- `∫ |r| b_g(r) dr = J3` -/
theorem J3_eq_integral : J3 W = ∫ r, |r| * bg W r := by
  rw [integral_abs_mul_eq (bg W) (continuous_bg W) (fun r hr => bg_eq_zero W hr)]
  rfl

end Win

theorem I2_nonneg : 0 ≤ I2 W := ag_nonneg W 0

theorem I3_nonneg : 0 ≤ I3 W := Gg_nonneg W 0 0

theorem J2_nonneg : 0 ≤ J2 W := by
  unfold J2
  have h : 0 ≤ ∫ r in (0 : ℝ)..1, r * ag W r :=
    intervalIntegral.integral_nonneg zero_le_one fun r hr => mul_nonneg hr.1 (ag_nonneg W r)
  linarith

theorem J3_nonneg : 0 ≤ J3 W := by
  unfold J3
  exact intervalIntegral.integral_nonneg zero_le_one fun r hr =>
    mul_nonneg hr.1 (add_nonneg (bg_nonneg W r) (bg_nonneg W (-r)))

/-- `J2 = ∬ |u-v| g(u) g(v)` -/
theorem J2_eq : J2 W = ∫ u, ∫ v, |u - v| * (W.g u * W.g v) := by
  rw [absdiff_eq W.g W.g W.meas W.meas W.integrable W.integrable
    (fun u v h => g_mul_eq_zero W h)]
  exact J2_eq_integral W

/-- `J3 = ∬ |u-v| g(u)² g(v)` -/
theorem J3_eq : J3 W = ∫ u, ∫ v, |u - v| * (W.g u ^ 2 * W.g v) := by
  have h := absdiff_eq (fun u => W.g u ^ 2) W.g (W.meas.pow_const 2) W.meas (integrable_sq W)
    W.integrable (fun u v h => by
      show W.g u ^ 2 * W.g v = 0
      rw [sq, mul_assoc, g_mul_eq_zero W h, mul_zero])
  beta_reduce at h
  rw [h, J3_eq_integral]
  refine integral_congr_ae (ae_of_all _ fun r => ?_)
  simp only
  rw [bg_eq]

theorem I2_eq : I2 W = ∫ u, W.g u ^ 2 := by
  unfold I2 ag
  refine integral_congr_ae (ae_of_all _ fun u => ?_)
  simp only [add_zero]
  ring

theorem I3_eq : I3 W = ∫ u, W.g u ^ 3 := by
  unfold I3 Gg
  refine integral_congr_ae (ae_of_all _ fun u => ?_)
  simp only [add_zero]
  ring


end TMG
end
end Src_TMG_Window

section Src_TMG_PrimeSumC
/-
Written for Kristian Muri Knausgård, drafted with Claude (Anthropic), 22 November 2026.
TMG/PrimeSumC.lean — the prime sum of TMA/PrimeSum for merely continuous F (no rate).
Proof: Weierstrass approximation of `F` on `[0,1]` by a polynomial, `TMA.primeSum_asymp` for the
polynomial, `TMA.primeSum_upper` for the difference.
-/

open MeasureTheory
open scoped BigOperators ArithmeticFunction Real

noncomputable section
namespace TMG

namespace PrimeSumC

/-- for `2 ≤ n ≤ ⌊X⌋₊` and `X ≥ 2`: `log n / log X ∈ [0,1]` -/
theorem ratio_mem {X : ℝ} (hX : 2 ≤ X) {n : ℕ} (hn : n ∈ Finset.Icc 2 ⌊X⌋₊) :
    Real.log n / Real.log X ∈ Set.Icc (0 : ℝ) 1 := by
  rw [Finset.mem_Icc] at hn
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn.1
  have hnX : (n : ℝ) ≤ X := (Nat.le_floor_iff (by linarith)).mp hn.2
  have hL : 0 < Real.log X := Real.log_pos (by linarith)
  have h0 : 0 ≤ Real.log n := Real.log_nonneg (by linarith)
  have h1 : Real.log n ≤ Real.log X := Real.log_le_log (by linarith) hnX
  exact ⟨div_nonneg h0 hL.le, (div_le_one hL).mpr h1⟩

/-- the prime sums of two functions that are uniformly close on `[0,1]` are close -/
theorem sum_diff_le {F G : ℝ → ℝ} {δ Cu : ℝ} (hδ : 0 ≤ δ)
    (hFG : ∀ x ∈ Set.Icc (0 : ℝ) 1, |F x - G x| ≤ δ)
    (hCu : ∀ X : ℝ, 2 ≤ X → ∑ n ∈ Finset.Icc 2 ⌊X⌋₊, Λ n ^ 2 / n ≤ Cu * Real.log X ^ 2)
    {X : ℝ} (hX : 2 ≤ X) :
    |∑ n ∈ Finset.Icc 2 ⌊X⌋₊, Λ n ^ 2 / n * F (Real.log n / Real.log X)
      - ∑ n ∈ Finset.Icc 2 ⌊X⌋₊, Λ n ^ 2 / n * G (Real.log n / Real.log X)|
      ≤ δ * (Cu * Real.log X ^ 2) := by
  rw [← Finset.sum_sub_distrib]
  calc |∑ n ∈ Finset.Icc 2 ⌊X⌋₊, (Λ n ^ 2 / n * F (Real.log n / Real.log X)
          - Λ n ^ 2 / n * G (Real.log n / Real.log X))|
      ≤ ∑ n ∈ Finset.Icc 2 ⌊X⌋₊, |Λ n ^ 2 / n * F (Real.log n / Real.log X)
          - Λ n ^ 2 / n * G (Real.log n / Real.log X)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ n ∈ Finset.Icc 2 ⌊X⌋₊, Λ n ^ 2 / n * δ := by
        refine Finset.sum_le_sum fun n hn => ?_
        have hc : 0 ≤ Λ n ^ 2 / (n : ℝ) := div_nonneg (sq_nonneg _) (Nat.cast_nonneg _)
        rw [← mul_sub, abs_mul, abs_of_nonneg hc]
        exact mul_le_mul_of_nonneg_left (hFG _ (ratio_mem hX hn)) hc
    _ = δ * ∑ n ∈ Finset.Icc 2 ⌊X⌋₊, Λ n ^ 2 / n := by
        rw [← Finset.sum_mul, mul_comm]
    _ ≤ δ * (Cu * Real.log X ^ 2) := mul_le_mul_of_nonneg_left (hCu X hX) hδ

/-- `r ↦ r F(r)` is interval integrable on `[0,1]` for `F` continuous on `[0,1]` -/
theorem intervalIntegrable_id_mul {F : ℝ → ℝ} (hF : ContinuousOn F (Set.Icc 0 1)) :
    IntervalIntegrable (fun r : ℝ => r * F r) volume 0 1 := by
  apply ContinuousOn.intervalIntegrable
  rw [Set.uIcc_of_le zero_le_one]
  exact continuousOn_id.mul hF

/-- the integrals `∫₀¹ r F(r) dr` of two functions that are uniformly close on `[0,1]` are close -/
theorem integral_diff_le {F G : ℝ → ℝ} {δ : ℝ} (hF : ContinuousOn F (Set.Icc 0 1))
    (hG : ContinuousOn G (Set.Icc 0 1))
    (hFG : ∀ x ∈ Set.Icc (0 : ℝ) 1, |F x - G x| ≤ δ) :
    |(∫ r in (0 : ℝ)..1, r * F r) - ∫ r in (0 : ℝ)..1, r * G r| ≤ δ := by
  rw [← intervalIntegral.integral_sub (intervalIntegrable_id_mul hF) (intervalIntegrable_id_mul hG)]
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := 1) (C := δ)
    (f := fun r => r * F r - r * G r) (by
      intro x hx
      rw [Set.uIoc_of_le zero_le_one] at hx
      have hx' : x ∈ Set.Icc (0 : ℝ) 1 := ⟨hx.1.le, hx.2⟩
      rw [Real.norm_eq_abs, ← mul_sub, abs_mul, abs_of_nonneg hx'.1]
      calc x * |F x - G x| ≤ 1 * δ := mul_le_mul hx'.2 (hFG x hx') (abs_nonneg _) zero_le_one
        _ = δ := one_mul δ)
  rw [Real.norm_eq_abs, sub_zero, abs_one, mul_one] at h
  exact h

end PrimeSumC

open PrimeSumC

/-- For `F` continuous on `[0,1]`:  `Σ_{2 ≤ n ≤ X} Λ(n)²/n · F(log n/log X) = (∫₀¹ r F(r) dr + o(1)) log² X`. -/
theorem primeSum_tendsto (F : ℝ → ℝ) (hF : ContinuousOn F (Set.Icc 0 1)) :
    ∀ η > 0, ∃ X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X →
      |∑ n ∈ Finset.Icc 2 ⌊X⌋₊, Λ n ^ 2 / n * F (Real.log n / Real.log X)
          - Real.log X ^ 2 * ∫ r in (0 : ℝ)..1, r * F r| ≤ η * Real.log X ^ 2 := by
  intro η hη
  obtain ⟨Cu, hCu⟩ := TMA.primeSum_upper
  have hden : 0 < 2 * (|Cu| + 1) := by positivity
  obtain ⟨δ, hδdef⟩ : ∃ δ : ℝ, δ = η / (2 * (|Cu| + 1)) := ⟨_, rfl⟩
  have hδ : 0 < δ := by
    rw [hδdef]
    exact div_pos hη hden
  have hδC : δ * (|Cu| + 1) = η / 2 := by
    rw [hδdef]
    field_simp
  -- Weierstrass
  obtain ⟨p, hp⟩ := exists_polynomial_near_of_continuousOn 0 1 F hF δ hδ
  obtain ⟨G, hGdef⟩ : ∃ G : ℝ → ℝ, G = fun x => p.eval x := ⟨_, rfl⟩
  have hGc : ContDiff ℝ 1 G := by
    have h := Polynomial.contDiff_aeval (𝕜 := ℝ) p 1
    rw [hGdef]
    simpa using h
  have hFG : ∀ x ∈ Set.Icc (0 : ℝ) 1, |F x - G x| ≤ δ := by
    intro x hx
    rw [abs_sub_comm, hGdef]
    exact (hp x hx).le
  obtain ⟨Cp, hCp⟩ := TMA.primeSum_asymp G hGc
  refine ⟨max 2 (Real.exp (2 * |Cp| / η)), fun X hX => ?_⟩
  have hX2 : 2 ≤ X := le_trans (le_max_left _ _) hX
  have hXe : Real.exp (2 * |Cp| / η) ≤ X := le_trans (le_max_right _ _) hX
  have hL : 0 < Real.log X := Real.log_pos (by linarith)
  have hL2 : 0 ≤ Real.log X ^ 2 := sq_nonneg _
  have hLge : 2 * |Cp| / η ≤ Real.log X := by
    rw [← Real.log_exp (2 * |Cp| / η)]
    exact Real.log_le_log (Real.exp_pos _) hXe
  have hCpL : Cp * Real.log X ≤ η / 2 * Real.log X ^ 2 := by
    have h1 : |Cp| ≤ η / 2 * Real.log X := by
      rw [div_le_iff₀ hη] at hLge
      linarith
    calc Cp * Real.log X ≤ |Cp| * Real.log X := mul_le_mul_of_nonneg_right (le_abs_self _) hL.le
      _ ≤ η / 2 * Real.log X * Real.log X := mul_le_mul_of_nonneg_right h1 hL.le
      _ = η / 2 * Real.log X ^ 2 := by ring
  have h1 := sum_diff_le hδ.le hFG hCu hX2
  have h2 := hCp X hX2
  have h3 := integral_diff_le hF hGc.continuous.continuousOn hFG
  have h1' : δ * (Cu * Real.log X ^ 2) ≤ δ * (|Cu| * Real.log X ^ 2) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (le_abs_self _) hL2) hδ.le
  have h3' : |Real.log X ^ 2 * ((∫ r in (0 : ℝ)..1, r * G r) - ∫ r in (0 : ℝ)..1, r * F r)|
      ≤ Real.log X ^ 2 * δ := by
    rw [abs_mul, abs_of_nonneg hL2, abs_sub_comm]
    exact mul_le_mul_of_nonneg_left h3 hL2
  have e : ∑ n ∈ Finset.Icc 2 ⌊X⌋₊, Λ n ^ 2 / n * F (Real.log n / Real.log X)
        - Real.log X ^ 2 * ∫ r in (0 : ℝ)..1, r * F r
      = (∑ n ∈ Finset.Icc 2 ⌊X⌋₊, Λ n ^ 2 / n * F (Real.log n / Real.log X)
          - ∑ n ∈ Finset.Icc 2 ⌊X⌋₊, Λ n ^ 2 / n * G (Real.log n / Real.log X))
        + (∑ n ∈ Finset.Icc 2 ⌊X⌋₊, Λ n ^ 2 / n * G (Real.log n / Real.log X)
          - Real.log X ^ 2 * ∫ r in (0 : ℝ)..1, r * G r)
        + Real.log X ^ 2 * ((∫ r in (0 : ℝ)..1, r * G r) - ∫ r in (0 : ℝ)..1, r * F r) := by
    ring
  have hfin : δ * (|Cu| * Real.log X ^ 2) + η / 2 * Real.log X ^ 2 + Real.log X ^ 2 * δ
      = η * Real.log X ^ 2 := by
    have : δ * (|Cu| * Real.log X ^ 2) + Real.log X ^ 2 * δ
        = δ * (|Cu| + 1) * Real.log X ^ 2 := by ring
    rw [add_right_comm, this, hδC]
    ring
  rw [e]
  calc _ ≤ _ := abs_add_three _ _ _
    _ ≤ δ * (|Cu| * Real.log X ^ 2) + η / 2 * Real.log X ^ 2 + Real.log X ^ 2 * δ := by
        linarith
    _ = η * Real.log X ^ 2 := hfin

end TMG

end
end Src_TMG_PrimeSumC

section Src_TMG_Cumulative
/-
Written for Kristian Muri Knausgård, drafted with Claude (Anthropic), 22 November 2026.
TMG/Cumulative.lean — from dyadic windows (T, 2T] to (0, T]: the third-moment budget, and the counting
consequences on both kinds of windows (Theorem 1.2 lower bound, Corollaries 1.4 and 1.5).
The dyadic summation is `TMG.Cumulative.dyadic_upper` (the upper-bound analogue of `Zeta23.Assembly.dyadic`);
the corollaries on `(0, T]` repeat the proofs of `ThirdMoment.lean` with the window `(0, T]`.
-/

open MeasureTheory Complex
open scoped BigOperators Real

noncomputable section
namespace TMG

/-- the budget on `(0, T]` -/
def BudgetCum (t K : ℝ) : Prop :=
  ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
    ThirdMoment.phiSum t 0 T ≤ (K + ε) * (Zeta23.Ncount 0 T : ℝ)

namespace Cumulative

/-- **Dyadic summation, upper bounds.** For `f, g` additive over adjacent intervals and nonnegative, with
`g(0,T) → ∞`: the dyadic bounds `f(t,2t) ≤ (c + ε) g(t,2t)` give `f(0,T) ≤ (c + ε) g(0,T)`.
(No sign condition on `c`.) -/
theorem dyadic_upper {f g : ℝ → ℝ → ℝ} {c : ℝ}
    (hf_add : ∀ a b d : ℝ, a ≤ b → b ≤ d → f a d = f a b + f b d)
    (hg_add : ∀ a b d : ℝ, a ≤ b → b ≤ d → g a d = g a b + g b d)
    (hf_nn : ∀ a b, 0 ≤ f a b) (hg_nn : ∀ a b, 0 ≤ g a b)
    (hg_top : Filter.Tendsto (fun T => g 0 T) Filter.atTop Filter.atTop)
    (h : ∀ ε > 0, ∃ T₁, ∀ t ≥ T₁, f t (2 * t) ≤ (c + ε) * g t (2 * t)) :
    ∀ ε > 0, ∃ T₀, ∀ T ≥ T₀, f 0 T ≤ (c + ε) * g 0 T := by
  intro ε hε
  obtain ⟨T₁', hT₁'⟩ := h (ε / 2) (by linarith)
  -- WLOG T₁ ≥ 1
  obtain ⟨T₁, hT₁def⟩ : ∃ T₁ : ℝ, T₁ = max T₁' 1 := ⟨_, rfl⟩
  have hT₁ : ∀ t ≥ T₁, f t (2 * t) ≤ (c + ε / 2) * g t (2 * t) :=
    fun t ht => hT₁' t ((le_max_left _ _).trans (hT₁def ▸ ht))
  have hT₁pos : 0 < T₁ := hT₁def ▸ lt_of_lt_of_le one_pos (le_max_right _ _)
  -- f and g are monotone in the right endpoint
  have hf_mono : ∀ a b b', a ≤ b → b ≤ b' → f a b ≤ f a b' := by
    intro a b b' hab hbb'
    rw [hf_add a b b' hab hbb']
    linarith [hf_nn b b']
  have hg_mono : ∀ a b b', a ≤ b → b ≤ b' → g a b ≤ g a b' := by
    intro a b b' hab hbb'
    rw [hg_add a b b' hab hbb']
    linarith [hg_nn b b']
  -- induction: f(t, 2^n t) ≤ (c + ε/2) g(t, 2^n t) for t ≥ T₁
  have key : ∀ n : ℕ, ∀ t ≥ T₁, f t (2 ^ n * t) ≤ (c + ε / 2) * g t (2 ^ n * t) := by
    intro n
    induction n with
    | zero =>
      intro t _
      have hf0 : f t t = 0 := by
        have := hf_add t t t le_rfl le_rfl
        linarith
      have hg0 : g t t = 0 := by
        have := hg_add t t t le_rfl le_rfl
        linarith
      rw [pow_zero, one_mul, hf0, hg0, mul_zero]
    | succ n ih =>
      intro t ht
      have ht0 : 0 ≤ t := hT₁pos.le.trans ht
      have h2n : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
      have hmid : t ≤ 2 ^ n * t := le_mul_of_one_le_left ht0 h2n
      have e : 2 * (2 ^ n * t) = 2 ^ (n + 1) * t := by
        rw [pow_succ]
        ring
      have hmid' : 2 ^ n * t ≤ 2 ^ (n + 1) * t := by
        rw [← e]
        linarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 2 ^ n) ht0]
      rw [hf_add t (2 ^ n * t) (2 ^ (n + 1) * t) hmid hmid',
        hg_add t (2 ^ n * t) (2 ^ (n + 1) * t) hmid hmid']
      have hstep := hT₁ (2 ^ n * t) (ht.trans hmid)
      rw [e] at hstep
      have := ih t ht
      linarith
  -- the constant: what happens below 2 T₁
  obtain ⟨P₀, hP₀⟩ : ∃ P₀ : ℝ, P₀ = f 0 (2 * T₁) + |c + ε / 2| * g 0 (2 * T₁) := ⟨_, rfl⟩
  obtain ⟨T₂, hT₂⟩ := Filter.eventually_atTop.mp (hg_top.eventually_ge_atTop (P₀ * (2 / ε)))
  refine ⟨max T₁ T₂, fun T hT => ?_⟩
  have hTT₁ : T₁ ≤ T := (le_max_left _ _).trans hT
  -- find n with 2^n T₁ ≤ T < 2^(n+1) T₁
  obtain ⟨n, hn1, hn2⟩ := exists_nat_pow_near (x := T / T₁)
    ((one_le_div hT₁pos).2 hTT₁) one_lt_two
  obtain ⟨t, htdef⟩ : ∃ t : ℝ, t = T / 2 ^ n := ⟨_, rfl⟩
  have h2n : (0 : ℝ) < 2 ^ n := by positivity
  have h2n1 : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
  have htT₁ : T₁ ≤ t := by
    rw [htdef, le_div_iff₀ h2n]
    rw [le_div_iff₀ hT₁pos] at hn1
    linarith
  have ht2T₁ : t ≤ 2 * T₁ := by
    rw [htdef, div_le_iff₀ h2n]
    rw [div_lt_iff₀ hT₁pos, pow_succ] at hn2
    linarith
  have hTt : 2 ^ n * t = T := by
    rw [htdef]
    field_simp
  have ht0 : 0 ≤ t := hT₁pos.le.trans htT₁
  have htT : t ≤ T := by
    rw [← hTt]
    exact le_mul_of_one_le_left ht0 h2n1
  have hk := key n t htT₁
  rw [hTt] at hk
  have hfsplit : f 0 T = f 0 t + f t T := hf_add 0 t T ht0 htT
  have hgsplit : g 0 T = g 0 t + g t T := hg_add 0 t T ht0 htT
  have hf0t : f 0 t ≤ f 0 (2 * T₁) := hf_mono 0 t (2 * T₁) ht0 ht2T₁
  have hg0t : g 0 t ≤ g 0 (2 * T₁) := hg_mono 0 t (2 * T₁) ht0 ht2T₁
  have hbig : P₀ * (2 / ε) ≤ g 0 T := hT₂ T ((le_max_right _ _).trans hT)
  have hbig' : P₀ ≤ ε / 2 * g 0 T := by
    have := mul_le_mul_of_nonneg_left hbig (by linarith : 0 ≤ ε / 2)
    calc P₀ = ε / 2 * (P₀ * (2 / ε)) := by field_simp
      _ ≤ ε / 2 * g 0 T := this
  have habs : -(c + ε / 2) * g 0 t ≤ |c + ε / 2| * g 0 (2 * T₁) :=
    calc -(c + ε / 2) * g 0 t ≤ |c + ε / 2| * g 0 t :=
          mul_le_mul_of_nonneg_right (neg_le_abs _) (hg_nn 0 t)
      _ ≤ |c + ε / 2| * g 0 (2 * T₁) := mul_le_mul_of_nonneg_left hg0t (abs_nonneg _)
  have e1 : (c + ε / 2) * g t T = (c + ε / 2) * g 0 T + -(c + ε / 2) * g 0 t := by
    rw [hgsplit]
    ring
  have e2 : (c + ε) * g 0 T = ε / 2 * g 0 T + (c + ε / 2) * g 0 T := by ring
  rw [hfsplit, e2]
  rw [e1] at hk
  rw [hP₀] at hbig'
  linarith

/-- additivity of the third-moment sum over adjacent windows -/
theorem phiSum_add (t : ℝ) {a b d : ℝ} (hab : a ≤ b) (hbd : b ≤ d) :
    ThirdMoment.phiSum t a d = ThirdMoment.phiSum t a b + ThirdMoment.phiSum t b d := by
  unfold ThirdMoment.phiSum
  rw [Zeta23.zerosIn_union hab hbd]
  refine finsum_mem_union ?_ (Zeta23.zerosIn_finite a b) (Zeta23.zerosIn_finite b d)
  rw [Set.disjoint_left]
  rintro ρ ⟨_, _, hb⟩ ⟨_, ha, _⟩
  exact absurd hb (not_le.2 ha)

theorem phiSum_nonneg (t a b : ℝ) : 0 ≤ ThirdMoment.phiSum t a b := by
  rw [ThirdMoment.phiSum_eq]
  exact Finset.sum_nonneg fun ρ _ => ThirdMoment.phi_nonneg (Nat.cast_nonneg _)

end Cumulative

open Cumulative

/-- a dyadic budget gives a cumulative budget (paper, Step 3 of the proof of Theorem 1.1).
(The hypothesis `0 ≤ t` is not needed for the proof.) -/
theorem budgetCum_of_budget {t K : ℝ} (ht : 0 ≤ t) (hB : ThirdMoment.Budget t K) : BudgetCum t K := by
  have _ := ht
  exact dyadic_upper (f := fun a b => ThirdMoment.phiSum t a b)
    (g := fun a b => (Zeta23.Ncount a b : ℝ)) (c := K)
    (fun a b d hab hbd => phiSum_add t hab hbd)
    (fun a b d hab hbd => by exact_mod_cast Zeta23.Ncount_add hab hbd)
    (fun a b => phiSum_nonneg t a b) (fun _ _ => Nat.cast_nonneg _)
    (Zeta23.tendsto_Ncount_zero_atTop Zeta23.zetaSeam Zeta23.riemannVonMangoldt_zeta) hB

/-- Theorem 1.2, lower bound, on `(0, T]` -/
theorem lower_of_budgetCum {t K : ℝ} (ht1 : 1 ≤ t) (ht2 : t < 2) (hB : BudgetCum t K) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      ThirdMoment.Ac t * (Zeta23.Nsimple 0 T : ℝ)
          + (1 - ThirdMoment.Ac t - ThirdMoment.Bc t * K - ε) * (Zeta23.Ncount 0 T : ℝ)
        ≤ (Zeta23.Ndist 0 T : ℝ) := by
  intro ε hε
  obtain ⟨T₀, h₀⟩ := hB ε hε
  refine ⟨T₀, fun T hT => ?_⟩
  have h1 := ThirdMoment.window_ineq ht1 ht2 0 T
  have h2 := h₀ T hT
  have hB0 : 0 < ThirdMoment.Bc t := ThirdMoment.Bc_pos ht2
  have hB1 : ThirdMoment.Bc t ≤ 1 / 6 := ThirdMoment.Bc_le ht2
  have hN : (0 : ℝ) ≤ (Zeta23.Ncount 0 T : ℝ) := Nat.cast_nonneg _
  have h3 : ThirdMoment.Bc t * ThirdMoment.phiSum t 0 T
      ≤ ThirdMoment.Bc t * ((K + ε) * (Zeta23.Ncount 0 T : ℝ)) :=
    mul_le_mul_of_nonneg_left h2 hB0.le
  have h4 : ThirdMoment.Bc t * (ε * (Zeta23.Ncount 0 T : ℝ)) ≤ ε * (Zeta23.Ncount 0 T : ℝ) :=
    mul_le_of_le_one_left (mul_nonneg hε.le hN) (by linarith)
  nlinarith [h1, h3, h4]

/-- Corollary 1.4 (distinct zeros) on `(0, T]` -/
theorem distinct_of_budgetCum {t K : ℝ} (ht1 : 1 ≤ t) (ht2 : t < 2) (hB : BudgetCum t K) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (1 - K / (2 * (2 - t) ^ 2) - ε) * (Zeta23.Ncount 0 T : ℝ) ≤ (Zeta23.Ndist 0 T : ℝ) := by
  intro ε hε
  have hd : 0 < 2 * (2 - t) ^ 2 := by
    have : 0 < 2 - t := by linarith
    positivity
  obtain ⟨T₀, h₀⟩ := hB (ε * (2 * (2 - t) ^ 2)) (mul_pos hε hd)
  refine ⟨T₀, fun T hT => ?_⟩
  have hbud := h₀ T hT
  have hw := ThirdMoment.window_ineq ht1 ht2 0 T
  have h2 := ThirdMoment.two_Ndist_le 0 T
  have hA := ThirdMoment.one_sub_two_Ac t
  have hBpos := ThirdMoment.Bc_pos ht2
  have hA0 : 0 ≤ ThirdMoment.Ac t := by
    have := ThirdMoment.Ac_ge_third ht1 ht2
    linarith
  -- (1 - 2 A) N_d ≥ (1 - 2 A) N - B Φ
  have e1 : (1 - 2 * ThirdMoment.Ac t) * (Zeta23.Ncount 0 T : ℝ)
        - ThirdMoment.Bc t * ThirdMoment.phiSum t 0 T
      ≤ (1 - 2 * ThirdMoment.Ac t) * (Zeta23.Ndist 0 T : ℝ) := by
    have := mul_le_mul_of_nonneg_left h2 hA0
    nlinarith
  rw [hA] at e1
  -- divide by B_t
  have e2 : 2 * (2 - t) ^ 2 * (Zeta23.Ncount 0 T : ℝ) - ThirdMoment.phiSum t 0 T
      ≤ 2 * (2 - t) ^ 2 * (Zeta23.Ndist 0 T : ℝ) := by
    by_contra hcon
    have hcon' := not_le.mp hcon
    have := mul_lt_mul_of_pos_left hcon' hBpos
    nlinarith
  have e3 : (2 * (2 - t) ^ 2) * ((1 - K / (2 * (2 - t) ^ 2) - ε) * (Zeta23.Ncount 0 T : ℝ))
      = 2 * (2 - t) ^ 2 * (Zeta23.Ncount 0 T : ℝ)
        - (K + ε * (2 * (2 - t) ^ 2)) * (Zeta23.Ncount 0 T : ℝ) := by
    have hne : (2 : ℝ) - t ≠ 0 := ne_of_gt (by linarith)
    field_simp
    ring
  have e4 : (2 * (2 - t) ^ 2) * ((1 - K / (2 * (2 - t) ^ 2) - ε) * (Zeta23.Ncount 0 T : ℝ))
      ≤ (2 * (2 - t) ^ 2) * (Zeta23.Ndist 0 T : ℝ) := by
    rw [e3]
    linarith
  exact le_of_mul_le_mul_left e4 hd

/-- Corollary 1.4 (simple zeros) on `(0, T]` -/
theorem simple_of_budgetCum {t K : ℝ} (ht1 : 1 ≤ t) (ht2 : t < 2) (hB : BudgetCum t K) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (1 - K / (2 - t) ^ 2 - ε) * (Zeta23.Ncount 0 T : ℝ) ≤ (Zeta23.Nsimple 0 T : ℝ) := by
  intro ε hε
  have hd : 0 < (2 - t) ^ 2 := by
    have : 0 < 2 - t := by linarith
    positivity
  obtain ⟨T₀, h₀⟩ := hB (ε * (2 - t) ^ 2) (mul_pos hε hd)
  refine ⟨T₀, fun T hT => ?_⟩
  have hbud := h₀ T hT
  have hns := ThirdMoment.nonsimple_le_phiSum ht1 ht2 0 T
  have e3 : (2 - t) ^ 2 * ((1 - K / (2 - t) ^ 2 - ε) * (Zeta23.Ncount 0 T : ℝ))
      = (2 - t) ^ 2 * (Zeta23.Ncount 0 T : ℝ)
        - (K + ε * (2 - t) ^ 2) * (Zeta23.Ncount 0 T : ℝ) := by
    have hne : (2 : ℝ) - t ≠ 0 := ne_of_gt (by linarith)
    field_simp
    ring
  have e4 : (2 - t) ^ 2 * ((1 - K / (2 - t) ^ 2 - ε) * (Zeta23.Ncount 0 T : ℝ))
      ≤ (2 - t) ^ 2 * (Zeta23.Nsimple 0 T : ℝ) := by
    rw [e3]
    linarith
  exact le_of_mul_le_mul_left e4 hd

/-- Corollary 1.5 on `(0, T]` -/
theorem highMult_of_budgetCum {t K : ℝ} (j : ℕ) (htj : t < j) (hB : BudgetCum t K) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      ThirdMoment.highMult j 0 T ≤ (K / ((j : ℝ) - t) ^ 2 + ε) * (Zeta23.Ncount 0 T : ℝ) := by
  intro ε hε
  have hd : 0 < ((j : ℝ) - t) ^ 2 := by
    have : 0 < (j : ℝ) - t := by linarith
    positivity
  obtain ⟨T₀, h₀⟩ := hB (ε * ((j : ℝ) - t) ^ 2) (mul_pos hε hd)
  refine ⟨T₀, fun T hT => ?_⟩
  have hbud := h₀ T hT
  have hh := ThirdMoment.highMult_le_phiSum j htj 0 T
  have e : ((j : ℝ) - t) ^ 2 * ((K / ((j : ℝ) - t) ^ 2 + ε) * (Zeta23.Ncount 0 T : ℝ))
      = (K + ε * ((j : ℝ) - t) ^ 2) * (Zeta23.Ncount 0 T : ℝ) := by
    have hne : (j : ℝ) - t ≠ 0 := ne_of_gt (by linarith)
    field_simp
  have e2 : ((j : ℝ) - t) ^ 2 * ThirdMoment.highMult j 0 T
      ≤ ((j : ℝ) - t) ^ 2 * ((K / ((j : ℝ) - t) ^ 2 + ε) * (Zeta23.Ncount 0 T : ℝ)) := by
    rw [e]
    linarith
  exact le_of_mul_le_mul_left e2 hd

/-- Corollary 1.3 on `(0, T]`, from a cumulative lower bound for the simple zeros -/
theorem distinct_of_budgetCum_simple {t K s₀ : ℝ} (ht1 : 1 ≤ t) (ht2 : t < 2) (hB : BudgetCum t K)
    (hS : ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (s₀ - ε) * (Zeta23.Ncount 0 T : ℝ) ≤ (Zeta23.Nsimple 0 T : ℝ)) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (ThirdMoment.Ac t * s₀ + 1 - ThirdMoment.Ac t - ThirdMoment.Bc t * K - ε)
          * (Zeta23.Ncount 0 T : ℝ) ≤ (Zeta23.Ndist 0 T : ℝ) := by
  intro ε hε
  obtain ⟨Ta, ha⟩ := hB ε hε
  obtain ⟨Tb, hb⟩ := hS ε hε
  refine ⟨max Ta Tb, fun T hT => ?_⟩
  have hbud := ha T (le_trans (le_max_left _ _) hT)
  have hsim := hb T (le_trans (le_max_right _ _) hT)
  have hw := ThirdMoment.window_ineq ht1 ht2 0 T
  have hA0 : 0 ≤ ThirdMoment.Ac t := by
    have := ThirdMoment.Ac_ge_third ht1 ht2
    linarith
  have hB0 : 0 ≤ ThirdMoment.Bc t := (ThirdMoment.Bc_pos ht2).le
  have hAB : 0 ≤ 1 - ThirdMoment.Ac t - ThirdMoment.Bc t := by
    have h1 := ThirdMoment.Ac_le_half ht2
    have h2 := ThirdMoment.Bc_le ht2
    linarith
  have hN : (0 : ℝ) ≤ Zeta23.Ncount 0 T := Nat.cast_nonneg _
  have e1 := mul_le_mul_of_nonneg_left hsim hA0
  have e2 := mul_le_mul_of_nonneg_left hbud hB0
  have e3 : 0 ≤ ε * (1 - ThirdMoment.Ac t - ThirdMoment.Bc t) * (Zeta23.Ncount 0 T : ℝ) :=
    mul_nonneg (mul_nonneg hε.le hAB) hN
  nlinarith

end TMG

end
end Src_TMG_Cumulative

section Src_TMG_Gram
/-
Written for Kristian Muri Knausgård, drafted with Claude (Anthropic), 22 November 2026.
TMG/Gram.lean — the Gram step for a general window (generalisation of TMA/Gram.lean): under RH,
  Σ_{T < γ ≤ 2T, distinct} Φ_t(m_γ) ≤ Re t3(K) - 2 t · t2(K) + t² · Re K(0),   K = Kfull.
STATUS: proved from the interface statements of `TMG/Window.lean` (no `sorry` in this file).

Plan of the proof (helper statements live in the namespace `TMG.Gram`; the proof is that of
`TMA/Gram.lean` with the window as a parameter):
  Step 1a. For a finite index type, nonnegative weights `c_a` and real points `x_a`, the matrix
           `(√c_a √c_b ĝ(x_a - x_b))` is positive semidefinite, its diagonal is `c_a`, and its traces are
           `tr = K(0)`, `tr (·)² = t2 K`, `tr (·)³ = t3 K` for `K(u) = Σ_a c_a e^{i x_a u}`
           (`ghat_posSemidef`, `ghat_normSq`, `ghat_triple`).
  Step 1b. With the zeros of a finite set `S ⊇ zerosIn T (2T)`, `c_ρ = cw h T ρ ≥ m_ρ` on the window,
           and `ThirdMoment.sum_phi_diag_le`:  `phiSum ≤ Re t3(Kfin S) - 2t t2(Kfin S) + t² Re Kfin S 0`.
  Step 2.  `Kfin S → Kfull` uniformly on ℝ along the finite sets of zeros (`summable_cw`, `norm_phase`),
           all kernels are bounded by `Σ c`, and `t2`, `t3` are stable under such perturbations
           (`0 ≤ ag ≤ W.bound`, `0 ≤ Gg ≤ W.bound²`).  Pass to the limit.
The lemmas of Steps 1b and 2b that do not involve the window are copies of those of `TMA.Gram`
(this file does not import `TMA/Gram.lean`).
-/

open MeasureTheory Complex
open scoped BigOperators Real

noncomputable section
namespace TMG

namespace Gram

open scoped ComplexOrder
open TMA (HeightWeight Kfin Kfull cw phase)

/-! ### Step 1a: an abstract finite Gram matrix -/

/-- the trigonometric polynomial `Σ_a c_a e^{i x_a u}` -/
def trigK {ι : Type*} [Fintype ι] (c x : ι → ℝ) (u : ℝ) : ℂ :=
  ∑ a, (c a : ℂ) * Complex.exp (Complex.I * (x a : ℂ) * (u : ℂ))

/-- the weighted Gram matrix `(√(c_a) √(c_b) ĝ(x_a - x_b))` -/
def gramW {ι : Type*} (W : Window) (c x : ι → ℝ) : Matrix ι ι ℂ :=
  Matrix.of fun a b => (Real.sqrt (c a) : ℂ) * (Real.sqrt (c b) : ℂ) * ghat W (x a - x b)

theorem continuous_trigK {ι : Type*} [Fintype ι] (c x : ι → ℝ) : Continuous (trigK c x) := by
  unfold trigK
  fun_prop

theorem gramW_posSemidef {ι : Type*} [Fintype ι] [DecidableEq ι] (W : Window) (c x : ι → ℝ) :
    (gramW W c x).PosSemidef := by
  have h := (ghat_posSemidef W x).conjTranspose_mul_mul_same
    (Matrix.diagonal fun a => (Real.sqrt (c a) : ℂ))
  have e : gramW W c x = (Matrix.diagonal fun a => (Real.sqrt (c a) : ℂ)).conjTranspose
      * (Matrix.of fun a b : ι => ghat W (x a - x b))
      * (Matrix.diagonal fun a => (Real.sqrt (c a) : ℂ)) := by
    ext a b
    rw [Matrix.diagonal_conjTranspose, Matrix.mul_diagonal, Matrix.diagonal_mul]
    simp only [gramW, Matrix.of_apply, Pi.star_apply, RCLike.star_def, Complex.conj_ofReal]
    ring
  rw [e]
  exact h

theorem gramW_diag {ι : Type*} (W : Window) (c x : ι → ℝ) (hc : ∀ a, 0 ≤ c a) (a : ι) :
    gramW W c x a a = (c a : ℂ) := by
  simp only [gramW, Matrix.of_apply, sub_self, ghat_zero, mul_one]
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt (hc a)]

theorem gramW_mul_swap {ι : Type*} (W : Window) (c x : ι → ℝ) (hc : ∀ a, 0 ≤ c a) (a b : ι) :
    gramW W c x a b * gramW W c x b a
      = ((c a * c b : ℝ) : ℂ) * ((‖ghat W (x a - x b)‖ ^ 2 : ℝ) : ℂ) := by
  have h1 : ghat W (x b - x a) = (starRingEnd ℂ) (ghat W (x a - x b)) := by
    rw [← ghat_neg, neg_sub]
  have h2 : ((‖ghat W (x a - x b)‖ ^ 2 : ℝ) : ℂ)
      = ghat W (x a - x b) * (starRingEnd ℂ) (ghat W (x a - x b)) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have ha : ((Real.sqrt (c a) : ℝ) : ℂ) * ((Real.sqrt (c a) : ℝ) : ℂ) = (c a : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (hc a)]
  have hb : ((Real.sqrt (c b) : ℝ) : ℂ) * ((Real.sqrt (c b) : ℝ) : ℂ) = (c b : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (hc b)]
  simp only [gramW, Matrix.of_apply]
  rw [h1, h2, Complex.ofReal_mul, ← ha, ← hb]
  ring

theorem trace_gramW {ι : Type*} [Fintype ι] (W : Window) (c x : ι → ℝ) (hc : ∀ a, 0 ≤ c a) :
    Matrix.trace (gramW W c x) = trigK c x 0 := by
  unfold Matrix.trace trigK
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Matrix.diag_apply, gramW_diag W c x hc]
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, mul_one]

/-- interchange of a finite sum with an iterated interval integral of jointly continuous functions -/
theorem dblint_finsetSum {κ : Type*} (s : Finset κ) (F : κ → ℝ → ℝ → ℂ)
    (hF : ∀ i ∈ s, Continuous (Function.uncurry (F i))) (a b c d : ℝ) :
    (∫ x in a..b, ∫ y in c..d, ∑ i ∈ s, F i x y)
      = ∑ i ∈ s, ∫ x in a..b, ∫ y in c..d, F i x y := by
  have h1 : ∀ x, (∫ y in c..d, ∑ i ∈ s, F i x y) = ∑ i ∈ s, ∫ y in c..d, F i x y := fun x =>
    intervalIntegral.integral_finsetSum fun i hi =>
      ((hF i hi).uncurry_left x).intervalIntegrable _ _
  simp only [h1]
  exact intervalIntegral.integral_finsetSum fun i hi =>
    (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' (hF i hi)
      c d).intervalIntegrable _ _

theorem trace_gramW_sq {ι : Type*} [Fintype ι] [DecidableEq ι] (W : Window) (c x : ι → ℝ)
    (hc : ∀ a, 0 ≤ c a) :
    Matrix.trace (gramW W c x ^ 2) = ((t2 W (trigK c x) : ℝ) : ℂ) := by
  -- both sides are `Σ_{a,b} c_a c_b ‖ĝ(x_a - x_b)‖²`
  have hL : Matrix.trace (gramW W c x ^ 2)
      = ∑ p : ι × ι, ((c p.1 * c p.2 : ℝ) : ℂ) * ((‖ghat W (x p.1 - x p.2)‖ ^ 2 : ℝ) : ℂ) := by
    rw [pow_two, Fintype.sum_prod_type]
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
      gramW_mul_swap W c x hc a b
  have key : ∀ u : ℝ, ((ag W u * ‖trigK c x u‖ ^ 2 : ℝ) : ℂ)
      = ∑ p : ι × ι, ((c p.1 * c p.2 : ℝ) : ℂ)
          * ((ag W u : ℂ) * Complex.exp (Complex.I * ((x p.1 - x p.2 : ℝ) : ℂ) * (u : ℂ))) := by
    intro u
    have h2 : ((‖trigK c x u‖ ^ 2 : ℝ) : ℂ) = trigK c x u * (starRingEnd ℂ) (trigK c x u) := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    have h3 : (starRingEnd ℂ) (trigK c x u)
        = ∑ b, (c b : ℂ) * Complex.exp (-(Complex.I * (x b : ℂ) * (u : ℂ))) := by
      unfold trigK
      rw [map_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [map_mul, Complex.conj_ofReal, ← Complex.exp_conj]
      congr 2
      simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
      ring
    rw [Complex.ofReal_mul, h2, h3]
    unfold trigK
    rw [Finset.sum_mul_sum, Fintype.sum_prod_type, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    have hexp : Complex.exp (Complex.I * ((x a - x b : ℝ) : ℂ) * (u : ℂ))
        = Complex.exp (Complex.I * (x a : ℂ) * (u : ℂ))
          * Complex.exp (-(Complex.I * (x b : ℂ) * (u : ℂ))) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    rw [hexp]
    push_cast
    ring
  rw [hL]
  unfold t2
  rw [← intervalIntegral.integral_ofReal]
  simp only [key]
  rw [intervalIntegral.integral_finsetSum]
  · refine Finset.sum_congr rfl fun p _ => ?_
    rw [intervalIntegral.integral_const_mul, ghat_normSq]
  · intro p _
    refine Continuous.intervalIntegrable ?_ _ _
    have := continuous_ag W
    fun_prop

theorem gramW_mul_three {ι : Type*} (W : Window) (c x : ι → ℝ) (hc : ∀ a, 0 ≤ c a) (a b d : ι) :
    gramW W c x a b * gramW W c x b d * gramW W c x d a
      = ((c a * c b * c d : ℝ) : ℂ)
          * (ghat W (x a - x b) * ghat W (x b - x d) * ghat W (x d - x a)) := by
  have ha : ((Real.sqrt (c a) : ℝ) : ℂ) * ((Real.sqrt (c a) : ℝ) : ℂ) = (c a : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (hc a)]
  have hb : ((Real.sqrt (c b) : ℝ) : ℂ) * ((Real.sqrt (c b) : ℝ) : ℂ) = (c b : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (hc b)]
  have hd : ((Real.sqrt (c d) : ℝ) : ℂ) * ((Real.sqrt (c d) : ℝ) : ℂ) = (c d : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (hc d)]
  simp only [gramW, Matrix.of_apply]
  rw [Complex.ofReal_mul, Complex.ofReal_mul, ← ha, ← hb, ← hd]
  ring

theorem sum_mul_sum_mul_sum {ι : Type*} [Fintype ι] (B C A : ι → ℂ) :
    (∑ b, B b) * (∑ d, C d) * (∑ a, A a) = ∑ p : ι × ι × ι, B p.2.1 * C p.2.2 * A p.1 := by
  rw [Fintype.sum_prod_type, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Fintype.sum_prod_type, Finset.sum_mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_mul]

theorem trace_gramW_cube {ι : Type*} [Fintype ι] [DecidableEq ι] (W : Window) (c x : ι → ℝ)
    (hc : ∀ a, 0 ≤ c a) :
    Matrix.trace (gramW W c x ^ 3) = t3 W (trigK c x) := by
  -- both sides are `Σ_{a,b,d} c_a c_b c_d ĝ(x_a - x_b) ĝ(x_b - x_d) ĝ(x_d - x_a)`
  have hL : Matrix.trace (gramW W c x ^ 3)
      = ∑ p : ι × ι × ι, ((c p.1 * c p.2.1 * c p.2.2 : ℝ) : ℂ)
          * (ghat W (x p.1 - x p.2.1) * ghat W (x p.2.1 - x p.2.2)
              * ghat W (x p.2.2 - x p.1)) := by
    rw [pow_three', Fintype.sum_prod_type]
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun d _ =>
      gramW_mul_three W c x hc a b d
  have key : ∀ u v : ℝ,
      (Gg W u v : ℂ) * (trigK c x u * trigK c x v * trigK c x (-u - v))
        = ∑ p : ι × ι × ι, ((c p.1 * c p.2.1 * c p.2.2 : ℝ) : ℂ)
            * ((Gg W u v : ℂ) * Complex.exp (Complex.I
                * ((x p.2.1 : ℂ) * (u : ℂ) + (x p.2.2 : ℂ) * (v : ℂ)
                    - (x p.1 : ℂ) * ((u : ℂ) + (v : ℂ))))) := by
    intro u v
    unfold trigK
    rw [sum_mul_sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    have hexp : Complex.exp (Complex.I
          * ((x p.2.1 : ℂ) * (u : ℂ) + (x p.2.2 : ℂ) * (v : ℂ)
              - (x p.1 : ℂ) * ((u : ℂ) + (v : ℂ))))
        = Complex.exp (Complex.I * (x p.2.1 : ℂ) * (u : ℂ))
          * Complex.exp (Complex.I * (x p.2.2 : ℂ) * (v : ℂ))
          * Complex.exp (Complex.I * (x p.1 : ℂ) * ((-u - v : ℝ) : ℂ)) := by
      rw [← Complex.exp_add, ← Complex.exp_add]
      congr 1
      push_cast
      ring
    rw [hexp]
    push_cast
    ring
  rw [hL]
  unfold t3
  simp only [key]
  rw [dblint_finsetSum]
  · refine Finset.sum_congr rfl fun p _ => ?_
    simp only [intervalIntegral.integral_const_mul]
    rw [ghat_triple]
  · intro p _
    have h1 : Continuous fun q : ℝ × ℝ => ((Gg W q.1 q.2 : ℝ) : ℂ) :=
      Complex.continuous_ofReal.comp (continuous_Gg W)
    have h2 : Continuous fun q : ℝ × ℝ => Complex.exp (Complex.I
        * ((x p.2.1 : ℂ) * (q.1 : ℂ) + (x p.2.2 : ℂ) * (q.2 : ℂ)
            - (x p.1 : ℂ) * ((q.1 : ℂ) + (q.2 : ℂ)))) := by
      fun_prop
    exact continuous_const.mul (h1.mul h2)

/-! ### Step 1b: the finite kernel of the zeros -/

theorem Kfin_eq_trigK (h : ℝ → ℝ) (T σ : ℝ) (S : Finset ℂ) :
    Kfin h T σ S
      = trigK (fun a : S => cw h T a) (fun a : S => σ * Real.log T * (a : ℂ).im) := by
  funext u
  unfold TMA.Kfin trigK
  refine (Finset.sum_coe_sort S (fun ρ => (cw h T ρ : ℂ) * phase T σ ρ u)).symm.trans ?_
  refine Finset.sum_congr rfl fun a _ => ?_
  unfold TMA.phase
  congr 2
  push_cast
  ring

theorem continuous_Kfin (h : ℝ → ℝ) (T σ : ℝ) (S : Finset ℂ) : Continuous (Kfin h T σ S) := by
  rw [Kfin_eq_trigK]
  exact continuous_trigK _ _

/-- on the window `(T, 2T]` the weight of a zero is at least its multiplicity -/
theorem zeroMult_le_cw (w : HeightWeight) {T : ℝ} (hT : 0 < T) {ρ : ℂ}
    (hρ : ρ ∈ Zeta23.zerosIn T (2 * T)) : (Zeta23.zeroMult ρ : ℝ) ≤ cw w.h T ρ := by
  obtain ⟨-, h1, h2⟩ := hρ
  have hh : 1 ≤ w.h (ρ.im / T) :=
    w.h_ge_one _ ((one_le_div hT).mpr h1.le) ((div_le_iff₀ hT).mpr h2)
  unfold TMA.cw
  exact le_mul_of_one_le_right (Nat.cast_nonneg _) hh

/-- **Step 1.** The third-moment sum is bounded by the kernel functionals of every finite kernel
whose index set contains the window. -/
theorem phiSum_le_Kfin (W : Window) (w : HeightWeight) {T t : ℝ} (σ : ℝ) (hT : 0 < T)
    (ht : 0 ≤ t) (S : Finset ℂ) (hS : ThirdMoment.zerosFinset T (2 * T) ⊆ S) :
    ThirdMoment.phiSum t T (2 * T)
      ≤ (t3 W (Kfin w.h T σ S)).re - 2 * t * t2 W (Kfin w.h T σ S)
          + t ^ 2 * (Kfin w.h T σ S 0).re := by
  classical
  have hc : ∀ a : S, 0 ≤ cw w.h T a := fun a => TMA.cw_nonneg w T a
  have hW := gramW_posSemidef W (fun a : S => cw w.h T a)
    (fun a : S => σ * Real.log T * (a : ℂ).im)
  have h1 := ThirdMoment.sum_phi_diag_le hW ht
  rw [trace_gramW_cube W _ _ hc, trace_gramW_sq W _ _ hc, trace_gramW W _ _ hc,
    ← Kfin_eq_trigK] at h1
  have hre : (t3 W (Kfin w.h T σ S) - 2 * (t : ℂ) * ((t2 W (Kfin w.h T σ S) : ℝ) : ℂ)
        + (t : ℂ) ^ 2 * Kfin w.h T σ S 0).re
      = (t3 W (Kfin w.h T σ S)).re - 2 * t * t2 W (Kfin w.h T σ S)
          + t ^ 2 * (Kfin w.h T σ S 0).re := by
    have e1 : 2 * (t : ℂ) * ((t2 W (Kfin w.h T σ S) : ℝ) : ℂ)
        = ((2 * t * t2 W (Kfin w.h T σ S) : ℝ) : ℂ) := by
      push_cast
      ring
    have e2 : (t : ℂ) ^ 2 = ((t ^ 2 : ℝ) : ℂ) := by
      push_cast
      ring
    rw [e1, e2, Complex.add_re, Complex.sub_re, Complex.ofReal_re, Complex.re_ofReal_mul]
  rw [hre] at h1
  calc ThirdMoment.phiSum t T (2 * T)
      = ∑ ρ ∈ ThirdMoment.zerosFinset T (2 * T), ThirdMoment.phi t (Zeta23.zeroMult ρ) :=
        ThirdMoment.phiSum_eq t T (2 * T)
    _ ≤ ∑ ρ ∈ ThirdMoment.zerosFinset T (2 * T), ThirdMoment.phi t (cw w.h T ρ) :=
        Finset.sum_le_sum fun ρ hρ =>
          ThirdMoment.phi_mono ht (Nat.cast_nonneg _)
            (zeroMult_le_cw w hT (ThirdMoment.mem_zerosFinset.mp hρ))
    _ ≤ ∑ ρ ∈ S, ThirdMoment.phi t (cw w.h T ρ) :=
        Finset.sum_le_sum_of_subset_of_nonneg hS
          fun ρ _ _ => ThirdMoment.phi_nonneg (TMA.cw_nonneg w T ρ)
    _ = ∑ a : S, ThirdMoment.phi t (cw w.h T a) :=
        (Finset.sum_coe_sort S (fun ρ => ThirdMoment.phi t (cw w.h T ρ))).symm
    _ = ∑ a : S, ThirdMoment.phi t
          ((gramW W (fun a : S => cw w.h T a)
            (fun a : S => σ * Real.log T * (a : ℂ).im)) a a).re := by
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [gramW_diag W _ _ hc, Complex.ofReal_re]
    _ ≤ _ := h1

/-! ### Step 2a: stability of the functionals under uniform perturbation of the kernel -/

/-- directly from the fields of the structure: `0 ≤ g 0 ≤ bound` -/
theorem bound_nonneg (W : Window) : 0 ≤ W.bound := (W.nonneg 0).trans (W.le_bound 0)

theorem t2_sub_le (W : Window) {K₁ K₂ : ℝ → ℂ} {M η : ℝ} (hK₁ : Continuous K₁)
    (hK₂ : Continuous K₂) (h₁ : ∀ x, ‖K₁ x‖ ≤ M) (h₂ : ∀ x, ‖K₂ x‖ ≤ M)
    (hη : ∀ x, ‖K₁ x - K₂ x‖ ≤ η) :
    |t2 W K₁ - t2 W K₂| ≤ W.bound * (2 * M * η) * 2 := by
  have hi : ∀ K : ℝ → ℂ, Continuous K →
      IntervalIntegrable (fun x => ag W x * ‖K x‖ ^ 2) volume (-1) 1 := fun K hK =>
    ((continuous_ag W).mul (hK.norm.pow 2)).intervalIntegrable _ _
  unfold t2
  rw [← intervalIntegral.integral_sub (hi K₁ hK₁) (hi K₂ hK₂), ← Real.norm_eq_abs]
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const (a := (-1 : ℝ)) (b := 1)
    (C := W.bound * (2 * M * η))
    (f := fun x => ag W x * ‖K₁ x‖ ^ 2 - ag W x * ‖K₂ x‖ ^ 2) ?_
  · have e : |(1 : ℝ) - -1| = 2 := by norm_num
    rwa [e] at hb
  · intro x _
    have e : ag W x * ‖K₁ x‖ ^ 2 - ag W x * ‖K₂ x‖ ^ 2
        = ag W x * ((‖K₁ x‖ - ‖K₂ x‖) * (‖K₁ x‖ + ‖K₂ x‖)) := by ring
    rw [e, Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (ag_nonneg W x)]
    have h3 : |‖K₁ x‖ - ‖K₂ x‖| ≤ η := (abs_norm_sub_norm_le _ _).trans (hη x)
    have h4 : |‖K₁ x‖ + ‖K₂ x‖| ≤ 2 * M := by
      rw [abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
      linarith [h₁ x, h₂ x]
    have h5 : |‖K₁ x‖ - ‖K₂ x‖| * |‖K₁ x‖ + ‖K₂ x‖| ≤ η * (2 * M) :=
      mul_le_mul h3 h4 (abs_nonneg _) ((abs_nonneg _).trans h3)
    calc ag W x * (|‖K₁ x‖ - ‖K₂ x‖| * |‖K₁ x‖ + ‖K₂ x‖|)
        ≤ W.bound * (η * (2 * M)) :=
          mul_le_mul (ag_le W x) h5 (mul_nonneg (abs_nonneg _) (abs_nonneg _)) (bound_nonneg W)
      _ = W.bound * (2 * M * η) := by ring

theorem norm_mul3_sub_le {a₁ a₂ b₁ b₂ c₁ c₂ : ℂ} {M η : ℝ}
    (ha₂ : ‖a₂‖ ≤ M) (hb₁ : ‖b₁‖ ≤ M) (hb₂ : ‖b₂‖ ≤ M) (hc₁ : ‖c₁‖ ≤ M)
    (ha : ‖a₁ - a₂‖ ≤ η) (hb : ‖b₁ - b₂‖ ≤ η) (hc : ‖c₁ - c₂‖ ≤ η) :
    ‖a₁ * b₁ * c₁ - a₂ * b₂ * c₂‖ ≤ 3 * M ^ 2 * η := by
  have hM : 0 ≤ M := (norm_nonneg _).trans ha₂
  have hη0 : 0 ≤ η := (norm_nonneg _).trans ha
  have e : a₁ * b₁ * c₁ - a₂ * b₂ * c₂
      = (a₁ - a₂) * b₁ * c₁ + a₂ * (b₁ - b₂) * c₁ + a₂ * b₂ * (c₁ - c₂) := by ring
  have u1 : ‖(a₁ - a₂) * b₁ * c₁‖ ≤ η * M * M := by
    rw [norm_mul, norm_mul]
    exact mul_le_mul (mul_le_mul ha hb₁ (norm_nonneg _) hη0) hc₁ (norm_nonneg _)
      (mul_nonneg hη0 hM)
  have u2 : ‖a₂ * (b₁ - b₂) * c₁‖ ≤ M * η * M := by
    rw [norm_mul, norm_mul]
    exact mul_le_mul (mul_le_mul ha₂ hb (norm_nonneg _) hM) hc₁ (norm_nonneg _)
      (mul_nonneg hM hη0)
  have u3 : ‖a₂ * b₂ * (c₁ - c₂)‖ ≤ M * M * η := by
    rw [norm_mul, norm_mul]
    exact mul_le_mul (mul_le_mul ha₂ hb₂ (norm_nonneg _) hM) hc (norm_nonneg _)
      (mul_nonneg hM hM)
  rw [e]
  calc ‖(a₁ - a₂) * b₁ * c₁ + a₂ * (b₁ - b₂) * c₁ + a₂ * b₂ * (c₁ - c₂)‖
      ≤ ‖(a₁ - a₂) * b₁ * c₁‖ + ‖a₂ * (b₁ - b₂) * c₁‖ + ‖a₂ * b₂ * (c₁ - c₂)‖ :=
        norm_add₃_le
    _ ≤ η * M * M + M * η * M + M * M * η := add_le_add (add_le_add u1 u2) u3
    _ = 3 * M ^ 2 * η := by ring

theorem continuous_t3_integrand (W : Window) {K : ℝ → ℂ} (hK : Continuous K) :
    Continuous (Function.uncurry fun x y : ℝ => (Gg W x y : ℂ) * (K x * K y * K (-x - y))) := by
  have h1 : Continuous fun q : ℝ × ℝ => ((Gg W q.1 q.2 : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp (continuous_Gg W)
  have h2 : Continuous fun q : ℝ × ℝ => K q.1 * K q.2 * K (-q.1 - q.2) :=
    ((hK.comp continuous_fst).mul (hK.comp continuous_snd)).mul
      (hK.comp (continuous_fst.neg.sub continuous_snd))
  exact h1.mul h2

theorem t3_sub_le (W : Window) {K₁ K₂ : ℝ → ℂ} {M η : ℝ} (hK₁ : Continuous K₁)
    (hK₂ : Continuous K₂) (h₁ : ∀ x, ‖K₁ x‖ ≤ M) (h₂ : ∀ x, ‖K₂ x‖ ≤ M)
    (hη : ∀ x, ‖K₁ x - K₂ x‖ ≤ η) :
    ‖t3 W K₁ - t3 W K₂‖ ≤ W.bound ^ 2 * (3 * M ^ 2 * η) * 2 * 2 := by
  have hc₁ := continuous_t3_integrand W hK₁
  have hc₂ := continuous_t3_integrand W hK₂
  have e2 : |(1 : ℝ) - -1| = 2 := by norm_num
  unfold t3
  rw [← intervalIntegral.integral_sub
    ((intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hc₁
      (-1) 1).intervalIntegrable _ _)
    ((intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hc₂
      (-1) 1).intervalIntegrable _ _)]
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const (a := (-1 : ℝ)) (b := 1)
    (C := W.bound ^ 2 * (3 * M ^ 2 * η) * 2)
    (f := fun x => (∫ y in (-1 : ℝ)..1, (Gg W x y : ℂ) * (K₁ x * K₁ y * K₁ (-x - y)))
      - ∫ y in (-1 : ℝ)..1, (Gg W x y : ℂ) * (K₂ x * K₂ y * K₂ (-x - y))) ?_
  · rwa [e2] at hb
  · intro x _
    rw [← intervalIntegral.integral_sub ((hc₁.uncurry_left x).intervalIntegrable _ _)
      ((hc₂.uncurry_left x).intervalIntegrable _ _)]
    have hb' := intervalIntegral.norm_integral_le_of_norm_le_const (a := (-1 : ℝ)) (b := 1)
      (C := W.bound ^ 2 * (3 * M ^ 2 * η))
      (f := fun y => (Gg W x y : ℂ) * (K₁ x * K₁ y * K₁ (-x - y))
        - (Gg W x y : ℂ) * (K₂ x * K₂ y * K₂ (-x - y))) ?_
    · rwa [e2] at hb'
    · intro y _
      rw [← mul_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Gg_nonneg W x y)]
      exact mul_le_mul (Gg_le W x y)
        (norm_mul3_sub_le (h₂ x) (h₁ y) (h₂ y) (h₁ _) (hη x) (hη y) (hη _))
        (norm_nonneg _) (sq_nonneg _)

/-! ### Step 2b: the finite kernels converge uniformly to the full kernel -/

theorem norm_cw_mul_phase (w : HeightWeight) (T σ : ℝ) (ρ : ℂ) (x : ℝ) :
    ‖(cw w.h T ρ : ℂ) * phase T σ ρ x‖ = cw w.h T ρ := by
  rw [norm_mul, TMA.norm_phase, mul_one, Complex.norm_real,
    Real.norm_of_nonneg (TMA.cw_nonneg w T ρ)]

theorem summable_cw_mul_phase (hRH : RiemannHypothesis) (w : HeightWeight) {T : ℝ} (hT : 0 < T)
    (σ x : ℝ) :
    Summable fun ρ : Zeta23.zetaZeroConfig.carrier => (cw w.h T ρ : ℂ) * phase T σ ρ x := by
  refine Summable.of_norm ?_
  simp only [norm_cw_mul_phase]
  exact TMA.summable_cw hRH w hT

/-- a finite set of zeros, as a finite set of complex numbers -/
def zfin (s : Finset Zeta23.zetaZeroConfig.carrier) : Finset ℂ :=
  s.map (Function.Embedding.subtype _)

theorem Kfin_zfin (h : ℝ → ℝ) (T σ : ℝ) (s : Finset Zeta23.zetaZeroConfig.carrier) (x : ℝ) :
    Kfin h T σ (zfin s) x = ∑ ρ ∈ s, (cw h T ρ : ℂ) * phase T σ ρ x := by
  unfold TMA.Kfin zfin
  rw [Finset.sum_map]
  rfl

/-- the tail of the weights outside a finite set of zeros -/
def cwTail (h : ℝ → ℝ) (T : ℝ) (s : Finset Zeta23.zetaZeroConfig.carrier) : ℝ :=
  ∑' ρ : { ρ // ρ ∉ s }, cw h T ρ

theorem tendsto_cwTail (h : ℝ → ℝ) (T : ℝ) :
    Filter.Tendsto (cwTail h T) Filter.atTop (nhds 0) :=
  tendsto_tsum_compl_atTop_zero fun ρ : Zeta23.zetaZeroConfig.carrier => cw h T ρ

theorem norm_Kfull_sub_Kfin_le (hRH : RiemannHypothesis) (w : HeightWeight) {T : ℝ} (hT : 0 < T)
    (σ : ℝ) (s : Finset Zeta23.zetaZeroConfig.carrier) (x : ℝ) :
    ‖Kfull w.h T σ x - Kfin w.h T σ (zfin s) x‖ ≤ cwTail w.h T s := by
  have h := (summable_cw_mul_phase hRH w hT σ x).sum_add_tsum_subtype_compl s
  have e : Kfull w.h T σ x - Kfin w.h T σ (zfin s) x
      = ∑' ρ : { ρ // ρ ∉ s }, (cw w.h T ρ : ℂ) * phase T σ ρ x := by
    rw [Kfin_zfin, TMA.Kfull, ← h]
    ring
  have hs : Summable fun ρ : { ρ // ρ ∉ s } => ‖(cw w.h T ρ : ℂ) * phase T σ ρ x‖ := by
    simp only [norm_cw_mul_phase]
    exact (TMA.summable_cw hRH w hT).subtype _
  rw [e]
  refine (norm_tsum_le_tsum_norm hs).trans (le_of_eq ?_)
  simp only [norm_cw_mul_phase]
  rfl

theorem norm_Kfull_le (hRH : RiemannHypothesis) (w : HeightWeight) {T : ℝ} (hT : 0 < T)
    (σ x : ℝ) :
    ‖Kfull w.h T σ x‖ ≤ ∑' ρ : Zeta23.zetaZeroConfig.carrier, cw w.h T ρ := by
  have hs : Summable fun ρ : Zeta23.zetaZeroConfig.carrier =>
      ‖(cw w.h T ρ : ℂ) * phase T σ ρ x‖ := by
    simp only [norm_cw_mul_phase]
    exact TMA.summable_cw hRH w hT
  unfold TMA.Kfull
  refine (norm_tsum_le_tsum_norm hs).trans (le_of_eq ?_)
  simp only [norm_cw_mul_phase]

theorem norm_Kfin_le (hRH : RiemannHypothesis) (w : HeightWeight) {T : ℝ} (hT : 0 < T)
    (σ : ℝ) (s : Finset Zeta23.zetaZeroConfig.carrier) (x : ℝ) :
    ‖Kfin w.h T σ (zfin s) x‖ ≤ ∑' ρ : Zeta23.zetaZeroConfig.carrier, cw w.h T ρ := by
  rw [Kfin_zfin]
  calc ‖∑ ρ ∈ s, (cw w.h T ρ : ℂ) * phase T σ ρ x‖
      ≤ ∑ ρ ∈ s, ‖(cw w.h T ρ : ℂ) * phase T σ ρ x‖ := norm_sum_le _ _
    _ = ∑ ρ ∈ s, cw w.h T ρ := by simp only [norm_cw_mul_phase]
    _ ≤ ∑' ρ : Zeta23.zetaZeroConfig.carrier, cw w.h T ρ :=
        (TMA.summable_cw hRH w hT).sum_le_tsum s fun ρ _ => TMA.cw_nonneg w T ρ

/-- the window `(T, 2T]` as a finite set of zeros -/
theorem exists_zfin_window (T : ℝ) :
    ∃ s₀ : Finset Zeta23.zetaZeroConfig.carrier, ∀ s, s₀ ⊆ s →
      ThirdMoment.zerosFinset T (2 * T) ⊆ zfin s := by
  classical
  refine ⟨(ThirdMoment.zerosFinset T (2 * T)).subtype _, fun s hs ρ hρ => ?_⟩
  have hZ : ρ ∈ Zeta23.zetaZeroConfig.carrier := (ThirdMoment.mem_zerosFinset.mp hρ).1
  exact Finset.mem_map.mpr ⟨⟨ρ, hZ⟩, hs (Finset.mem_subtype.mpr hρ), rfl⟩

end Gram

/-! ### The theorem -/

open Gram in
set_option linter.unusedVariables false in
/-- **Gram step, general window.** Under RH the third-moment sum over the window `(T, 2T]` is bounded
by the functionals `t3 W`, `t2 W` and the value at 0 of the full zero-side kernel.
(The hypothesis `hσ` is not needed for the proof; it is part of the fixed interface.) -/
theorem phiSum_le_Xi (hRH : RiemannHypothesis) (W : Window) (w : TMA.HeightWeight) {T σ t : ℝ}
    (hT : 0 < T) (hσ : 0 < σ) (ht : 0 ≤ t) :
    ThirdMoment.phiSum t T (2 * T)
      ≤ (t3 W (TMA.Kfull w.h T σ)).re - 2 * t * t2 W (TMA.Kfull w.h T σ)
        + t ^ 2 * (TMA.Kfull w.h T σ 0).re := by
  set M : ℝ := ∑' ρ : Zeta23.zetaZeroConfig.carrier, TMA.cw w.h T ρ
  have hcF := TMA.continuous_Kfull hRH w hT σ
  have hcf : ∀ s, Continuous (TMA.Kfin w.h T σ (zfin s)) := fun s => continuous_Kfin _ _ _ _
  have hbF : ∀ x, ‖TMA.Kfull w.h T σ x‖ ≤ M := norm_Kfull_le hRH w hT σ
  have hbf : ∀ s x, ‖TMA.Kfin w.h T σ (zfin s) x‖ ≤ M := norm_Kfin_le hRH w hT σ
  have hd : ∀ s x, ‖TMA.Kfull w.h T σ x - TMA.Kfin w.h T σ (zfin s) x‖ ≤ cwTail w.h T s :=
    norm_Kfull_sub_Kfin_le hRH w hT σ
  have htail := tendsto_cwTail w.h T
  -- convergence of the three functionals
  have l3 : Filter.Tendsto (fun s => t3 W (TMA.Kfin w.h T σ (zfin s))) Filter.atTop
      (nhds (t3 W (TMA.Kfull w.h T σ))) := by
    refine tendsto_iff_norm_sub_tendsto_zero.mpr ?_
    have hz : Filter.Tendsto (fun s => W.bound ^ 2 * (3 * M ^ 2 * cwTail w.h T s) * 2 * 2)
        Filter.atTop (nhds 0) := by
      have := (((htail.const_mul (3 * M ^ 2)).const_mul (W.bound ^ 2)).mul_const 2).mul_const 2
      simpa only [mul_zero, zero_mul] using this
    refine squeeze_zero (fun s => norm_nonneg _) (fun s => ?_) hz
    rw [norm_sub_rev]
    exact t3_sub_le W hcF (hcf s) hbF (hbf s) (hd s)
  have l2 : Filter.Tendsto (fun s => t2 W (TMA.Kfin w.h T σ (zfin s))) Filter.atTop
      (nhds (t2 W (TMA.Kfull w.h T σ))) := by
    refine tendsto_iff_norm_sub_tendsto_zero.mpr ?_
    have hz : Filter.Tendsto (fun s => W.bound * (2 * M * cwTail w.h T s) * 2) Filter.atTop
        (nhds 0) := by
      have := ((htail.const_mul (2 * M)).const_mul W.bound).mul_const 2
      simpa only [mul_zero, zero_mul] using this
    refine squeeze_zero (fun s => norm_nonneg _) (fun s => ?_) hz
    rw [norm_sub_rev, Real.norm_eq_abs]
    exact t2_sub_le W hcF (hcf s) hbF (hbf s) (hd s)
  have l1 : Filter.Tendsto (fun s => TMA.Kfin w.h T σ (zfin s) 0) Filter.atTop
      (nhds (TMA.Kfull w.h T σ 0)) := by
    refine tendsto_iff_norm_sub_tendsto_zero.mpr ?_
    refine squeeze_zero (fun s => norm_nonneg _) (fun s => ?_) htail
    rw [norm_sub_rev]
    exact hd s 0
  have lim : Filter.Tendsto
      (fun s => (t3 W (TMA.Kfin w.h T σ (zfin s))).re - 2 * t * t2 W (TMA.Kfin w.h T σ (zfin s))
        + t ^ 2 * (TMA.Kfin w.h T σ (zfin s) 0).re) Filter.atTop
      (nhds ((t3 W (TMA.Kfull w.h T σ)).re - 2 * t * t2 W (TMA.Kfull w.h T σ)
        + t ^ 2 * (TMA.Kfull w.h T σ 0).re)) :=
    (((Complex.continuous_re.tendsto _).comp l3).sub (l2.const_mul (2 * t))).add
      (((Complex.continuous_re.tendsto _).comp l1).const_mul (t ^ 2))
  obtain ⟨s₀, hs₀⟩ := exists_zfin_window T
  refine ge_of_tendsto lim (Filter.eventually_atTop.mpr ⟨s₀, fun s hs => ?_⟩)
  exact phiSum_le_Kfin W w σ hT ht (zfin s) (hs₀ s hs)

end TMG

end
end Src_TMG_Gram

section Src_TMG_Traces
/-
Written for Kristian Muri Knausgård, drafted with Claude (Anthropic), 22 November 2026.
TMG/Traces.lean — the second trace for a general window (generalisation of TMA/Traces.lean, `t2_lower`).
STATUS: `t2_lower` is proved from the interface statements of `TMG/Window.lean`, `TMG/PrimeSumC.lean` and the
proved modules `TMA/Kernel.lean`, `TMA/Packets.lean`, `TMA/PrimeSum.lean`, `TMA/Traces.lean` (no `sorry` in this
file).  See BLUEPRINT.md, module "T1T2" and section "General windows (TMG)".  The window-dependent helper
lemmas live in the namespace `TMG.T12`; the window-independent ones are those of `TMA.T12`.

Outline of `t2_lower`.  Write `E = Kfull - K0`, `L = log T`, `B = W.bound`.
1. `t2 Kfull ≥ (1 - 1/L) t2 K0 - L B ∫_{-1}^{1} ‖E‖²`  (`T12.t2_perturb`).
2. For `T` large the packets of `K0` have disjoint supports (`TMA.T12.K0_norm_sq`), so `t2 K0` is a sum of
   masses of single packets (`T12.t2_K0_eq`).
3. The mass of the packet with centre `lam` is `(T²/A) ∫ ag(lam - y/A) ‖k y‖² dy` (`T12.Ipk_eq`), between
   `(T²/A)(ag lam - η) κ₂/2π` and `(T²/A) B κ₂/2π` once `κ/A` is below the modulus of uniform continuity of
   `ag` for `η`  (`T12.Ipk_ge`, `T12.Ipk_le`).
4. Sum over the integers with `primeSum_tendsto` and `primeSum_upper`:
   `D C₂(σ) κ₂ - C T - η c₁ T L ≤ t2 K0 ≤ C T L`  (`T12.t2_K0_ge`, `T12.t2_K0_le`), with `C`, `c₁`
   independent of `η` and `T`.  Given `δ`, take `η` with `η c₁ ≤ δ/4π`, then `T` large.
-/

open MeasureTheory Complex
open scoped BigOperators ArithmeticFunction Real

noncomputable section
namespace TMG

open TMA TMA.T12

namespace T12

/-! ### elementary lemmas -/

/-- since `ag` vanishes outside `[-1,1]`, integrals against `ag` over `[-1,1]` are integrals over `ℝ` -/
theorem integral_ag_mul (W : Window) (f : ℝ → ℝ) :
    ∫ x in (-1 : ℝ)..1, ag W x * f x = ∫ x, ag W x * f x := by
  rw [intervalIntegral.integral_of_le (by norm_num), ← integral_Icc_eq_integral_Ioc]
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro x hx
  have hx1 : 1 < |x| := lt_of_not_ge fun hcon =>
    hx ⟨by linarith [neg_abs_le x], by linarith [le_abs_self x]⟩
  rw [ag_eq_zero W hx1, zero_mul]

/-! ### a single packet -/

theorem continuous_ag_mul_packet (W : Window) (w : HeightWeight) (T σ lam : ℝ) :
    Continuous (fun x : ℝ => ag W x * ‖packet w.k T σ lam x‖ ^ 2) :=
  (continuous_ag W).mul ((TMA.T12.continuous_packet w T σ lam).norm.pow 2)

/-- the weighted `L²` mass of one packet -/
def Ipk (W : Window) (w : HeightWeight) (T σ lam : ℝ) : ℝ :=
  ∫ x in (-1 : ℝ)..1, ag W x * ‖packet w.k T σ lam x‖ ^ 2

theorem Ipk_nonneg (W : Window) (w : HeightWeight) (T σ lam : ℝ) : 0 ≤ Ipk W w T σ lam := by
  apply intervalIntegral.integral_nonneg (by norm_num)
  intro x _
  exact mul_nonneg (ag_nonneg W x) (sq_nonneg _)

theorem integrable_ag_mul_k_sq (W : Window) (w : HeightWeight) (lam A : ℝ) :
    Integrable (fun y : ℝ => ag W (lam - y / A) * ‖w.k y‖ ^ 2) := by
  refine Integrable.bdd_mul (c := W.bound) (TMA.T12.integrable_k_sq w)
    ((continuous_ag W).comp (by fun_prop)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun y => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (ag_nonneg W _)]
  exact ag_le W _

/-- substitution `y = -(A (x - lam))` in the mass of a packet -/
theorem Ipk_eq (W : Window) (w : HeightWeight) {T σ : ℝ} (hA : 0 < Asc T σ) (lam : ℝ) :
    Ipk W w T σ lam = T ^ 2 / Asc T σ * ∫ y, ag W (lam - y / Asc T σ) * ‖w.k y‖ ^ 2 := by
  unfold Ipk
  rw [integral_ag_mul W]
  have h1 : ∀ x : ℝ, ag W x * ‖packet w.k T σ lam x‖ ^ 2
      = T ^ 2 * (fun x : ℝ => (fun y : ℝ => ag W (lam - y / Asc T σ) * ‖w.k y‖ ^ 2)
          (-(Asc T σ) * x)) (x - lam) := by
    intro x
    rw [TMA.T12.norm_packet_sq]
    have h2 : lam - -(Asc T σ * (x - lam)) / Asc T σ = x := by
      field_simp
      ring
    have h3 : -(Asc T σ) * (x - lam) = -(Asc T σ * (x - lam)) := by ring
    show ag W x * (T ^ 2 * ‖w.k (-(Asc T σ * (x - lam)))‖ ^ 2)
      = T ^ 2 * (ag W (lam - -(Asc T σ) * (x - lam) / Asc T σ)
          * ‖w.k (-(Asc T σ) * (x - lam))‖ ^ 2)
    rw [h3, h2]
    ring
  simp_rw [h1]
  rw [integral_const_mul,
    integral_sub_right_eq_self (fun x : ℝ => (fun y : ℝ => ag W (lam - y / Asc T σ) * ‖w.k y‖ ^ 2)
          (-(Asc T σ) * x)) lam,
    Measure.integral_comp_mul_left (fun y : ℝ => ag W (lam - y / Asc T σ) * ‖w.k y‖ ^ 2)
      (-(Asc T σ))]
  rw [smul_eq_mul, abs_inv, abs_neg, abs_of_pos hA]
  field_simp

theorem Ipk_le (W : Window) (w : HeightWeight) {T σ : ℝ} (hA : 0 < Asc T σ) (lam : ℝ) :
    Ipk W w T σ lam ≤ T ^ 2 / Asc T σ * (W.bound * (w.kap2 / (2 * π))) := by
  rw [Ipk_eq W w hA, ← TMA.T12.kQ_eq w]
  refine mul_le_mul_of_nonneg_left ?_ (div_nonneg (sq_nonneg T) hA.le)
  rw [← integral_const_mul]
  refine integral_mono (integrable_ag_mul_k_sq W w lam _)
    ((TMA.T12.integrable_k_sq w).const_mul _) fun y => ?_
  exact mul_le_mul_of_nonneg_right (ag_le W _) (sq_nonneg _)

/-- lower bound for the mass of a packet: `eta` is a bound for the oscillation of `ag` over
distances `≤ κ/A` (uniform continuity replaces the Lipschitz bound of the quadratic window) -/
theorem Ipk_ge (W : Window) (w : HeightWeight) {T σ η : ℝ} (hA : 0 < Asc T σ)
    (hη : ∀ r d : ℝ, |d| ≤ w.kappa / Asc T σ → |ag W (r + d) - ag W r| ≤ η) (lam : ℝ) :
    T ^ 2 / Asc T σ * ((ag W lam - η) * (w.kap2 / (2 * π))) ≤ Ipk W w T σ lam := by
  rw [Ipk_eq W w hA, ← TMA.T12.kQ_eq w]
  refine mul_le_mul_of_nonneg_left ?_ (div_nonneg (sq_nonneg T) hA.le)
  rw [← integral_const_mul]
  refine integral_mono ((TMA.T12.integrable_k_sq w).const_mul _)
    (integrable_ag_mul_k_sq W w lam _) fun y => ?_
  show (ag W lam - η) * ‖w.k y‖ ^ 2 ≤ ag W (lam - y / Asc T σ) * ‖w.k y‖ ^ 2
  by_cases hy : w.k y = 0
  · rw [hy, norm_zero, zero_pow two_ne_zero, mul_zero, mul_zero]
  · refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
    have hyk : |y| ≤ w.kappa := w.k_supp y hy
    have hd : |-(y / Asc T σ)| ≤ w.kappa / Asc T σ := by
      rw [abs_neg, abs_div, abs_of_pos hA]
      exact div_le_div_of_nonneg_right hyk hA.le
    have h1 := hη lam (-(y / Asc T σ)) hd
    have h2 : lam + -(y / Asc T σ) = lam - y / Asc T σ := by ring
    rw [h2] at h1
    have h3 := neg_abs_le (ag W (lam - y / Asc T σ) - ag W lam)
    linarith

/-! ### the second trace of `K0` as a sum over the packets -/

theorem t2_K0_eq (W : Window) (w : HeightWeight) {T σ : ℝ} (hσ : 0 < σ) (hs : Sep w T σ) :
    t2 W (K0 w.k T σ) = Real.log (T / (2 * π)) ^ 2 * Ipk W w T σ 0
      + ∑ n ∈ Finset.Icc 2 (Nmax T σ), lamCoeff n ^ 2 *
          (Ipk W w T σ (lamOf T σ n) + Ipk W w T σ (-(lamOf T σ n))) := by
  have hc : ∀ lam : ℝ, IntervalIntegrable (fun x : ℝ => ag W x * ‖packet w.k T σ lam x‖ ^ 2)
      volume (-1) 1 := fun lam => (continuous_ag_mul_packet W w T σ lam).intervalIntegrable _ _
  have h1 : ∀ x : ℝ, ag W x * ‖K0 w.k T σ x‖ ^ 2
      = Real.log (T / (2 * π)) ^ 2 * (ag W x * ‖packet w.k T σ 0 x‖ ^ 2)
        + ∑ n ∈ Finset.Icc 2 (Nmax T σ), lamCoeff n ^ 2 *
          (ag W x * ‖packet w.k T σ (lamOf T σ n) x‖ ^ 2
            + ag W x * ‖packet w.k T σ (-(lamOf T σ n)) x‖ ^ 2) := by
    intro x
    rw [TMA.T12.K0_norm_sq w hσ hs x, mul_add, Finset.mul_sum]
    congr 1
    · ring
    · exact Finset.sum_congr rfl fun n _ => by ring
  have hcn : ∀ n : ℕ, Continuous (fun x : ℝ => lamCoeff n ^ 2 *
      (ag W x * ‖packet w.k T σ (lamOf T σ n) x‖ ^ 2
        + ag W x * ‖packet w.k T σ (-(lamOf T σ n)) x‖ ^ 2)) := fun n =>
    continuous_const.mul
      ((continuous_ag_mul_packet W w T σ _).add (continuous_ag_mul_packet W w T σ _))
  have hc0 : IntervalIntegrable (fun x : ℝ => Real.log (T / (2 * π)) ^ 2 *
      (ag W x * ‖packet w.k T σ 0 x‖ ^ 2)) volume (-1) 1 :=
    (continuous_const.mul (continuous_ag_mul_packet W w T σ 0)).intervalIntegrable _ _
  unfold t2 Ipk
  simp_rw [h1]
  rw [intervalIntegral.integral_add hc0
      ((continuous_finsetSum _ fun n _ => hcn n).intervalIntegrable _ _),
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_finsetSum fun n _ => (hcn n).intervalIntegrable _ _]
  congr 1
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add (hc _) (hc _)]

/-- upper bound `t2 K0 ≤ C T log T` -/
theorem t2_K0_le (W : Window) (w : HeightWeight) {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ < 1) :
    ∃ C : ℝ, ∀ T : ℝ, Sep w T σ → 8 ≤ T → t2 W (K0 w.k T σ) ≤ C * T * Real.log T := by
  obtain ⟨C₀, hC₀0, hC₀⟩ := TMA.T12.primeSum_upper'
  refine ⟨W.bound * (w.kap2 / (2 * π)) * (1 + 8 * C₀) / σ, fun T hs hT8 => ?_⟩
  have hB0 : 0 ≤ W.bound := le_trans zero_le_one W.one_le_bound
  have hT0 : 0 < T := by linarith
  have hL : 0 < Real.log T := Real.log_pos (by linarith)
  have hσL : 0 < σ * Real.log T := mul_pos hσ hL
  have hQ : 0 ≤ w.kap2 / (2 * π) := div_nonneg (TMA.T12.kap2_nonneg w) (by positivity)
  have hU0 : 0 ≤ T ^ 2 / Asc T σ * (W.bound * (w.kap2 / (2 * π))) :=
    mul_nonneg (div_nonneg (sq_nonneg T) hs.hA.le) (mul_nonneg hB0 hQ)
  have h2π : 0 < 2 * π := by positivity
  have hell0 : 0 ≤ Real.log (T / (2 * π)) := by
    refine Real.log_nonneg ?_
    rw [le_div_iff₀ h2π]
    linarith [Real.pi_lt_four]
  have hell1 : Real.log (T / (2 * π)) ≤ Real.log T :=
    Real.log_le_log (div_pos hT0 h2π) (div_le_self hT0.le (by linarith [Real.pi_gt_three]))
  have hell2 : Real.log (T / (2 * π)) ^ 2 ≤ Real.log T ^ 2 := pow_le_pow_left₀ hell0 hell1 2
  have hTσ1 : 1 ≤ T ^ σ := Real.one_le_rpow (by linarith) hσ.le
  have hSN : ∑ n ∈ Finset.Icc 2 (Nmax T σ), Λ n ^ 2 / n ≤ C₀ * (2 * Real.log T) ^ 2 := by
    have h1 := hC₀ (2 * T ^ σ) (by linarith)
    have h2 : Real.log (2 * T ^ σ) = Real.log 2 + σ * Real.log T := by
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_rpow hT0]
    have h3 : Real.log 2 ≤ Real.log T := Real.log_le_log (by norm_num) (by linarith)
    have h3' : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have h3'' : σ * Real.log T ≤ 1 * Real.log T := mul_le_mul_of_nonneg_right hσ1.le hL.le
    have h4 : 0 ≤ Real.log (2 * T ^ σ) := by rw [h2]; linarith
    have h5 : Real.log (2 * T ^ σ) ≤ 2 * Real.log T := by rw [h2]; linarith
    exact h1.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h4 h5 2) hC₀0)
  rw [t2_K0_eq W w hσ hs]
  have hsum : ∑ n ∈ Finset.Icc 2 (Nmax T σ), lamCoeff n ^ 2 *
        (Ipk W w T σ (lamOf T σ n) + Ipk W w T σ (-(lamOf T σ n)))
      ≤ ∑ n ∈ Finset.Icc 2 (Nmax T σ), Λ n ^ 2 / n *
        (2 * (T ^ 2 / Asc T σ * (W.bound * (w.kap2 / (2 * π))))) := by
    refine Finset.sum_le_sum fun n _ => ?_
    rw [TMA.T12.lamCoeff_sq]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have h1 := Ipk_le W w hs.hA (lamOf T σ n)
    have h2 := Ipk_le W w hs.hA (-(lamOf T σ n))
    linarith
  rw [← Finset.sum_mul] at hsum
  have h1 : Real.log (T / (2 * π)) ^ 2 * Ipk W w T σ 0
      ≤ Real.log T ^ 2 * (T ^ 2 / Asc T σ * (W.bound * (w.kap2 / (2 * π)))) :=
    mul_le_mul hell2 (Ipk_le W w hs.hA 0) (Ipk_nonneg _ _ _ _ _) (sq_nonneg _)
  have h2 : (∑ n ∈ Finset.Icc 2 (Nmax T σ), Λ n ^ 2 / n) *
        (2 * (T ^ 2 / Asc T σ * (W.bound * (w.kap2 / (2 * π)))))
      ≤ C₀ * (2 * Real.log T) ^ 2 * (2 * (T ^ 2 / Asc T σ * (W.bound * (w.kap2 / (2 * π))))) :=
    mul_le_mul_of_nonneg_right hSN (by linarith)
  have h3 : Real.log T ^ 2 * (T ^ 2 / Asc T σ * (W.bound * (w.kap2 / (2 * π))))
      + C₀ * (2 * Real.log T) ^ 2 * (2 * (T ^ 2 / Asc T σ * (W.bound * (w.kap2 / (2 * π)))))
      = W.bound * (w.kap2 / (2 * π)) * (1 + 8 * C₀) / σ * T * Real.log T := by
    rw [TMA.T12.sq_div_Asc hT0]
    field_simp
    ring
  linarith

/-- lower bound for `t2 K0` in terms of prime sums up to `T^σ`; `η` bounds the oscillation of `ag`
over distances `≤ κ/A` -/
theorem t2_K0_ge_sum (W : Window) (w : HeightWeight) {T σ η : ℝ} (hσ : 0 < σ) (hs : Sep w T σ)
    (hη : ∀ r d : ℝ, |d| ≤ w.kappa / Asc T σ → |ag W (r + d) - ag W r| ≤ η) :
    T ^ 2 / Asc T σ * (w.kap2 / (2 * π)) *
      (Real.log (T / (2 * π)) ^ 2 * (I2 W - η)
        + 2 * ∑ n ∈ Finset.Icc 2 ⌊T ^ σ⌋₊, Λ n ^ 2 / n * ag W (lamOf T σ n)
        - 2 * η * ∑ n ∈ Finset.Icc 2 ⌊T ^ σ⌋₊, Λ n ^ 2 / n)
      ≤ t2 W (K0 w.k T σ) := by
  rw [t2_K0_eq W w hσ hs]
  have hIge : ∀ lam : ℝ, T ^ 2 / Asc T σ * (w.kap2 / (2 * π)) * (ag W lam - η)
      ≤ Ipk W w T σ lam := fun lam =>
    le_of_eq_of_le (by ring) (Ipk_ge W w hs.hA hη lam)
  have hTσ : 0 ≤ T ^ σ := Real.rpow_nonneg (by linarith [hs.hT]) σ
  have hsub : Finset.Icc 2 ⌊T ^ σ⌋₊ ⊆ Finset.Icc 2 (Nmax T σ) :=
    Finset.Icc_subset_Icc_right (Nat.floor_le_floor (by linarith))
  have h0 : Real.log (T / (2 * π)) ^ 2 *
        (T ^ 2 / Asc T σ * (w.kap2 / (2 * π)) * (I2 W - η))
      ≤ Real.log (T / (2 * π)) ^ 2 * Ipk W w T σ 0 :=
    mul_le_mul_of_nonneg_left (hIge 0) (sq_nonneg _)
  have h1 : ∑ n ∈ Finset.Icc 2 ⌊T ^ σ⌋₊, Λ n ^ 2 / n *
        (T ^ 2 / Asc T σ * (w.kap2 / (2 * π)) * (2 * ag W (lamOf T σ n) - 2 * η))
      ≤ ∑ n ∈ Finset.Icc 2 ⌊T ^ σ⌋₊, lamCoeff n ^ 2 *
        (Ipk W w T σ (lamOf T σ n) + Ipk W w T σ (-(lamOf T σ n))) := by
    refine Finset.sum_le_sum fun n _ => ?_
    rw [TMA.T12.lamCoeff_sq]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have h2 := hIge (lamOf T σ n)
    have h3 := hIge (-(lamOf T σ n))
    rw [ag_neg W] at h3
    linarith
  have h2 : ∑ n ∈ Finset.Icc 2 ⌊T ^ σ⌋₊, lamCoeff n ^ 2 *
        (Ipk W w T σ (lamOf T σ n) + Ipk W w T σ (-(lamOf T σ n)))
      ≤ ∑ n ∈ Finset.Icc 2 (Nmax T σ), lamCoeff n ^ 2 *
        (Ipk W w T σ (lamOf T σ n) + Ipk W w T σ (-(lamOf T σ n))) :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub fun n _ _ =>
      mul_nonneg (sq_nonneg _) (add_nonneg (Ipk_nonneg _ _ _ _ _) (Ipk_nonneg _ _ _ _ _))
  have h3 : ∑ n ∈ Finset.Icc 2 ⌊T ^ σ⌋₊, Λ n ^ 2 / n *
        (T ^ 2 / Asc T σ * (w.kap2 / (2 * π)) * (2 * ag W (lamOf T σ n) - 2 * η))
      = T ^ 2 / Asc T σ * (w.kap2 / (2 * π)) *
        (2 * ∑ n ∈ Finset.Icc 2 ⌊T ^ σ⌋₊, Λ n ^ 2 / n * ag W (lamOf T σ n)
          - 2 * η * ∑ n ∈ Finset.Icc 2 ⌊T ^ σ⌋₊, Λ n ^ 2 / n) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.mul_sum]
    exact Finset.sum_congr rfl fun n _ => by ring
  rw [h3] at h1
  have h4 : T ^ 2 / Asc T σ * (w.kap2 / (2 * π)) *
      (Real.log (T / (2 * π)) ^ 2 * (I2 W - η)
        + 2 * ∑ n ∈ Finset.Icc 2 ⌊T ^ σ⌋₊, Λ n ^ 2 / n * ag W (lamOf T σ n)
        - 2 * η * ∑ n ∈ Finset.Icc 2 ⌊T ^ σ⌋₊, Λ n ^ 2 / n)
      = Real.log (T / (2 * π)) ^ 2 * (T ^ 2 / Asc T σ * (w.kap2 / (2 * π)) * (I2 W - η))
        + T ^ 2 / Asc T σ * (w.kap2 / (2 * π)) *
          (2 * ∑ n ∈ Finset.Icc 2 ⌊T ^ σ⌋₊, Λ n ^ 2 / n * ag W (lamOf T σ n)
            - 2 * η * ∑ n ∈ Finset.Icc 2 ⌊T ^ σ⌋₊, Λ n ^ 2 / n) := by
    ring
  rw [h4]
  linarith

/-- the algebra behind the lower bound: the error is `C T + η c₁ T L` with `C`, `c₁` free of `η` -/
theorem t2_alg {T L σ Q C₀ c I J SX SX' A η : ℝ} (hT : 0 < T) (hL : 0 < L) (hσ : 0 < σ)
    (hσ1 : σ ≤ 1) (hQ : 0 ≤ Q) (hη : 0 ≤ η) (hC₀ : 0 ≤ C₀) (hc : 0 ≤ c) (hcL : c ≤ L) (hI : 0 ≤ I)
    (hA : A = T * (σ * L)) (hSX : (σ * L) ^ 2 * (J / 2) - η * (σ * L) ^ 2 ≤ SX)
    (hSX' : SX' ≤ C₀ * (σ * L) ^ 2) :
    T * L * Q * (I / σ + σ * J) - Q * (2 * c * I / σ) * T - η * (Q * (3 + 2 * C₀) / σ) * (T * L)
      ≤ T ^ 2 / A * Q * ((L - c) ^ 2 * (I - η) + 2 * SX - 2 * η * SX') := by
  subst hA
  have hσL : 0 < σ * L := mul_pos hσ hL
  have hW0 : 0 ≤ T ^ 2 / (T * (σ * L)) * Q := by positivity
  have p1 : (L ^ 2 - 2 * L * c) * I ≤ (L - c) ^ 2 * I := by
    refine mul_le_mul_of_nonneg_right ?_ hI
    have hsq : (L - c) ^ 2 = L ^ 2 - 2 * L * c + c ^ 2 := by ring
    rw [hsq]
    linarith [sq_nonneg c]
  have p2 : η * (L - c) ^ 2 ≤ η * L ^ 2 :=
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith) (by linarith) 2) hη
  have hσL' : (σ * L) ^ 2 ≤ L ^ 2 := by
    refine pow_le_pow_left₀ hσL.le ?_ 2
    have := mul_le_mul_of_nonneg_right hσ1 hL.le
    linarith
  have p3 : η * SX' ≤ η * (C₀ * L ^ 2) := by
    refine mul_le_mul_of_nonneg_left (hSX'.trans ?_) hη
    exact mul_le_mul_of_nonneg_left hσL' hC₀
  have p4 : η * (σ * L) ^ 2 ≤ η * L ^ 2 := mul_le_mul_of_nonneg_left hσL' hη
  have hinner : L ^ 2 * I - 2 * L * c * I + (σ * L) ^ 2 * J - η * L ^ 2 * (3 + 2 * C₀)
      ≤ (L - c) ^ 2 * (I - η) + 2 * SX - 2 * η * SX' := by
    have e1 : (L - c) ^ 2 * (I - η) = (L - c) ^ 2 * I - η * (L - c) ^ 2 := by ring
    have e2 : η * L ^ 2 * (3 + 2 * C₀) = 3 * (η * L ^ 2) + 2 * (η * (C₀ * L ^ 2)) := by ring
    have e3 : (L ^ 2 - 2 * L * c) * I = L ^ 2 * I - 2 * L * c * I := by ring
    rw [e1, e2]
    rw [e3] at p1
    linarith
  have hmul := mul_le_mul_of_nonneg_left hinner hW0
  have hid : T ^ 2 / (T * (σ * L)) * Q * (L ^ 2 * I - 2 * L * c * I + (σ * L) ^ 2 * J
        - η * L ^ 2 * (3 + 2 * C₀))
      = T * L * Q * (I / σ + σ * J) - Q * (2 * c * I / σ) * T
        - η * (Q * (3 + 2 * C₀) / σ) * (T * L) := by
    field_simp
    ring
  rw [hid] at hmul
  exact hmul

/-- lower bound `t2 K0 ≥ D · C₂(σ) κ₂ - C T - η c₁ T log T` for `T ≥ T₀(η)`; the constants `C`, `c₁`
do not depend on `η` -/
theorem t2_K0_ge (W : Window) (w : HeightWeight) {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ < 1) :
    ∃ C c₁ : ℝ, 0 ≤ c₁ ∧ ∀ η > 0, ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T → Sep w T σ →
      Dsc T * (C2 W σ * w.kap2) - C * T - η * c₁ * (T * Real.log T) ≤ t2 W (K0 w.k T σ) := by
  obtain ⟨C₀, hC₀0, hC₀⟩ := TMA.T12.primeSum_upper'
  have hQ : 0 ≤ w.kap2 / (2 * π) := div_nonneg (TMA.T12.kap2_nonneg w) (by positivity)
  refine ⟨w.kap2 / (2 * π) * (2 * Real.log (2 * π) * I2 W / σ),
    w.kap2 / (2 * π) * (3 + 2 * C₀) / σ, by positivity, fun η hη => ?_⟩
  obtain ⟨δ', hδ', hunif⟩ := ag_unifCont W η hη
  obtain ⟨X₀, hX₀⟩ := primeSum_tendsto (ag W) (continuous_ag W).continuousOn η hη
  obtain ⟨T₁, hT₁⟩ := Filter.eventually_atTop.mp
    ((tendsto_rpow_atTop hσ).eventually_ge_atTop (max X₀ 2))
  refine ⟨max (max T₁ 8) (w.kappa / (σ * δ')), fun T hT hs => ?_⟩
  have hTT1 : T₁ ≤ T := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hT
  have hT8 : 8 ≤ T := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hT
  have hTκ : w.kappa / (σ * δ') ≤ T := le_trans (le_max_right _ _) hT
  have hXmax := hT₁ T hTT1
  have hXX₀ : X₀ ≤ T ^ σ := le_trans (le_max_left _ _) hXmax
  have hX2 : 2 ≤ T ^ σ := le_trans (le_max_right _ _) hXmax
  have hT0 : 0 < T := by linarith
  have hL : 0 < Real.log T := Real.log_pos (by linarith)
  have hL1 : 1 ≤ Real.log T := by
    rw [Real.le_log_iff_exp_le hT0]
    linarith [Real.exp_one_lt_three]
  have hσL : 0 < σ * Real.log T := mul_pos hσ hL
  have hlogX : Real.log (T ^ σ) = σ * Real.log T := Real.log_rpow hT0 σ
  have h2π : 0 < 2 * π := by positivity
  have hc0 : 0 ≤ Real.log (2 * π) := Real.log_nonneg (by linarith [Real.pi_gt_three])
  have hcL : Real.log (2 * π) ≤ Real.log T :=
    Real.log_le_log h2π (by linarith [Real.pi_lt_four])
  have hell : Real.log (T / (2 * π)) = Real.log T - Real.log (2 * π) :=
    Real.log_div hT0.ne' h2π.ne'
  -- `κ/A` is below the modulus of uniform continuity
  have hκA : w.kappa / Asc T σ ≤ δ' := by
    rw [div_le_iff₀ hs.hA]
    rw [div_le_iff₀ (mul_pos hσ hδ')] at hTκ
    have h1 : T * (σ * δ') * 1 ≤ T * (σ * δ') * Real.log T :=
      mul_le_mul_of_nonneg_left hL1 (by positivity)
    have h2 : δ' * Asc T σ = T * (σ * δ') * Real.log T := by
      unfold Asc
      ring
    rw [h2]
    linarith
  have hη' : ∀ r d : ℝ, |d| ≤ w.kappa / Asc T σ → |ag W (r + d) - ag W r| ≤ η :=
    fun r d hd => hunif r d (hd.trans hκA)
  -- the prime sum with the weight `ag`
  have hSX : (σ * Real.log T) ^ 2 * (J2 W / 2) - η * (σ * Real.log T) ^ 2
      ≤ ∑ n ∈ Finset.Icc 2 ⌊T ^ σ⌋₊, Λ n ^ 2 / n * ag W (lamOf T σ n) := by
    have h1 := hX₀ (T ^ σ) hXX₀
    rw [hlogX] at h1
    have h3 : ∫ r in (0 : ℝ)..1, r * ag W r = J2 W / 2 := by
      unfold J2
      ring
    rw [h3] at h1
    have h5 : -(η * (σ * Real.log T) ^ 2)
        ≤ ∑ n ∈ Finset.Icc 2 ⌊T ^ σ⌋₊, Λ n ^ 2 / n * ag W (lamOf T σ n)
          - (σ * Real.log T) ^ 2 * (J2 W / 2) := (abs_le.mp h1).1
    linarith
  have hSX' : ∑ n ∈ Finset.Icc 2 ⌊T ^ σ⌋₊, Λ n ^ 2 / n ≤ C₀ * (σ * Real.log T) ^ 2 := by
    have h1 := hC₀ (T ^ σ) hX2
    rwa [hlogX] at h1
  have halg := t2_alg (T := T) (L := Real.log T) (σ := σ) (Q := w.kap2 / (2 * π))
    (C₀ := C₀) (c := Real.log (2 * π)) (I := I2 W) (J := J2 W) (A := Asc T σ) (η := η)
    hT0 hL hσ hσ1.le hQ hη.le hC₀0 hc0 hcL (I2_nonneg W) rfl hSX hSX'
  have hmain := t2_K0_ge_sum W w hσ hs hη'
  rw [hell] at hmain
  have hD : Dsc T * (C2 W σ * w.kap2)
      = T * Real.log T * (w.kap2 / (2 * π)) * (I2 W / σ + σ * J2 W) := by
    unfold Dsc C2
    ring
  rw [hD]
  linarith

/-- comparison of the second traces of two kernels -/
theorem t2_perturb (W : Window) {K K' : ℝ → ℂ} (hK : Continuous K) (hK' : Continuous K') {L : ℝ}
    (hL : 0 < L) :
    t2 W K' - 1 / L * t2 W K' - L * (W.bound * ∫ x in (-1 : ℝ)..1, ‖K x - K' x‖ ^ 2)
      ≤ t2 W K := by
  unfold t2
  have hc1 : Continuous (fun x : ℝ => ag W x * ‖K' x‖ ^ 2) :=
    (continuous_ag W).mul (hK'.norm.pow 2)
  have hc2 : Continuous (fun x : ℝ => ‖K x - K' x‖ ^ 2) := (hK.sub hK').norm.pow 2
  have hc3 : Continuous (fun x : ℝ => ag W x * ‖K x‖ ^ 2) :=
    (continuous_ag W).mul (hK.norm.pow 2)
  have hc4 : Continuous (fun x : ℝ => 1 / L * (ag W x * ‖K' x‖ ^ 2)) := continuous_const.mul hc1
  have hc5 : Continuous (fun x : ℝ => L * (W.bound * ‖K x - K' x‖ ^ 2)) :=
    continuous_const.mul (continuous_const.mul hc2)
  have hc6 : Continuous (fun x : ℝ => ag W x * ‖K' x‖ ^ 2 - 1 / L * (ag W x * ‖K' x‖ ^ 2)) :=
    hc1.sub hc4
  have hmono : ∫ x in (-1 : ℝ)..1, (ag W x * ‖K' x‖ ^ 2 - 1 / L * (ag W x * ‖K' x‖ ^ 2)
        - L * (W.bound * ‖K x - K' x‖ ^ 2))
      ≤ ∫ x in (-1 : ℝ)..1, ag W x * ‖K x‖ ^ 2 := by
    refine intervalIntegral.integral_mono_on (by norm_num)
      ((hc6.sub hc5).intervalIntegrable _ _) (hc3.intervalIntegrable _ _) fun x _ => ?_
    have h1 := TMA.T12.norm_add_sq_ge (K' x) (K x - K' x) hL
    rw [add_sub_cancel] at h1
    have h2 := mul_le_mul_of_nonneg_left h1 (ag_nonneg W x)
    have h3 : ag W x * ‖K x - K' x‖ ^ 2 ≤ W.bound * ‖K x - K' x‖ ^ 2 :=
      mul_le_mul_of_nonneg_right (ag_le W x) (sq_nonneg _)
    have h4 := mul_le_mul_of_nonneg_left h3 hL.le
    have h5 : ag W x * (‖K' x‖ ^ 2 - 1 / L * ‖K' x‖ ^ 2 - L * ‖K x - K' x‖ ^ 2)
        = ag W x * ‖K' x‖ ^ 2 - 1 / L * (ag W x * ‖K' x‖ ^ 2)
          - L * (ag W x * ‖K x - K' x‖ ^ 2) := by
      ring
    rw [h5] at h2
    linarith
  have heq : ∫ x in (-1 : ℝ)..1, (ag W x * ‖K' x‖ ^ 2 - 1 / L * (ag W x * ‖K' x‖ ^ 2)
        - L * (W.bound * ‖K x - K' x‖ ^ 2))
      = (∫ x in (-1 : ℝ)..1, ag W x * ‖K' x‖ ^ 2)
        - 1 / L * (∫ x in (-1 : ℝ)..1, ag W x * ‖K' x‖ ^ 2)
        - L * (W.bound * ∫ x in (-1 : ℝ)..1, ‖K x - K' x‖ ^ 2) := by
    rw [intervalIntegral.integral_sub (hc6.intervalIntegrable _ _) (hc5.intervalIntegrable _ _),
      intervalIntegral.integral_sub (hc1.intervalIntegrable _ _) (hc4.intervalIntegrable _ _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul]
  rw [heq] at hmono
  exact hmono

end T12

/-- second trace for a general window:  `t2(K) ≥ (C₂(σ) ∫h² - δ) D` -/
theorem t2_lower (hRH : RiemannHypothesis) (W : Window) (w : TMA.HeightWeight) {σ : ℝ} (hσ : 0 < σ)
    (hσ1 : σ < 1) :
    ∀ δ > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (C2 W σ * w.kap2 - δ) * TMA.Dsc T ≤ t2 W (TMA.Kfull w.h T σ) := by
  intro δ hδ
  obtain ⟨Ck, T₁, hker⟩ := kernel_error hRH w hσ hσ1
  obtain ⟨T₂, hsep⟩ := separation w hσ hσ1
  obtain ⟨Cu, hCu⟩ := T12.t2_K0_le W w hσ hσ1
  obtain ⟨Cl, c₁, hc₁, hCl⟩ := T12.t2_K0_ge W w hσ hσ1
  have hπ := Real.pi_pos
  have h4π : 0 < 4 * π := by positivity
  have hB0 : 0 ≤ W.bound := le_trans zero_le_one W.one_le_bound
  -- the oscillation parameter: `η c₁ ≤ δ / 4π`; it is chosen before any threshold for `T`
  obtain ⟨η, hηdef⟩ : ∃ η : ℝ, η = δ / (4 * π * (c₁ + 1)) := ⟨_, rfl⟩
  have hη : 0 < η := by
    rw [hηdef]
    positivity
  have hηc : η * c₁ ≤ δ / (4 * π) := by
    have h1 : η * (c₁ + 1) = δ / (4 * π) := by
      rw [hηdef]
      field_simp
    have h2 : η * c₁ ≤ η * (c₁ + 1) := mul_le_mul_of_nonneg_left (by linarith) hη.le
    linarith
  obtain ⟨T₄, hT₄⟩ := hCl η hη
  obtain ⟨T₃, hT₃⟩ := Filter.eventually_atTop.mp
    (Real.tendsto_log_atTop.eventually_ge_atTop (4 * π * (Cl + Cu + W.bound * Ck) / δ))
  refine ⟨max (max T₁ T₂) (max (max T₃ T₄) 8), fun T hT => ?_⟩
  have hT1 : T₁ ≤ T := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hT
  have hT2 : T₂ ≤ T := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hT
  have hT34 : max T₃ T₄ ≤ T := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hT
  have hT3 : T₃ ≤ T := le_trans (le_max_left _ _) hT34
  have hT4 : T₄ ≤ T := le_trans (le_max_right _ _) hT34
  have hT8 : 8 ≤ T := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hT
  have hLδ : 4 * π * (Cl + Cu + W.bound * Ck) / δ ≤ Real.log T := hT₃ T hT3
  obtain ⟨hT2', hA, hκ, -, hlog⟩ := hsep T hT2
  have hs : TMA.T12.Sep w T σ := ⟨hT2', hA, hκ, hlog⟩
  have hT0 : 0 < T := by linarith
  have hL : 0 < Real.log T := Real.log_pos (by linarith)
  have hu := hCu T hs hT8
  have hl := hT₄ T hT4 hs
  have hE2 := (hker T hT1).2.2
  have hstep := T12.t2_perturb W (continuous_Kfull hRH w hT0 σ) (continuous_K0 w T σ) hL
  -- the error terms `1/L · t2 K0` and `L B ∫ ‖E‖²` are `O(T)`
  have e1 : 1 / Real.log T * t2 W (K0 w.k T σ) ≤ Cu * T := by
    have h1 := mul_le_mul_of_nonneg_left hu (one_div_pos.mpr hL).le
    have h2 : 1 / Real.log T * (Cu * T * Real.log T) = Cu * T := by
      field_simp
    linarith
  have e2 : Real.log T * (W.bound * ∫ x in (-1 : ℝ)..1, ‖Kfull w.h T σ x - K0 w.k T σ x‖ ^ 2)
      ≤ W.bound * Ck * T := by
    have h1 := mul_le_mul_of_nonneg_left hE2
      (show (0 : ℝ) ≤ Real.log T * W.bound from mul_nonneg hL.le hB0)
    have h2 : Real.log T * W.bound * (Ck * T / Real.log T) = W.bound * Ck * T := by
      field_simp
    have h3 : Real.log T * (W.bound * ∫ x in (-1 : ℝ)..1, ‖Kfull w.h T σ x - K0 w.k T σ x‖ ^ 2)
        = Real.log T * W.bound * ∫ x in (-1 : ℝ)..1, ‖Kfull w.h T σ x - K0 w.k T σ x‖ ^ 2 := by
      ring
    rw [h3]
    linarith
  -- the `O(T)` terms against `δ/2 · D`
  have hC : Cl + Cu + W.bound * Ck ≤ δ * Real.log T / (4 * π) := by
    rw [le_div_iff₀ h4π]
    rw [div_le_iff₀ hδ] at hLδ
    linarith
  have h2 := mul_le_mul_of_nonneg_right hC hT0.le
  -- the oscillation term against `δ/2 · D`
  have h4 : η * c₁ * (T * Real.log T) ≤ δ / (4 * π) * (T * Real.log T) :=
    mul_le_mul_of_nonneg_right hηc (mul_nonneg hT0.le hL.le)
  have h3 : (C2 W σ * w.kap2 - δ) * Dsc T
      = Dsc T * (C2 W σ * w.kap2) - δ * Real.log T / (4 * π) * T
        - δ / (4 * π) * (T * Real.log T) := by
    unfold Dsc
    ring
  rw [h3]
  linarith

end TMG

end
end Src_TMG_Traces

section Src_TMG_Trace3Aux1
/-
Written for Kristian Muri Knausgård, drafted with Claude (Anthropic), 22 November 2026.

TMG/Trace3Aux1.lean — the trilinear form `tri W` behind the third trace `t3 W` of a general window
(generalisation of TMA/Trace3Aux1.lean):
* `t3 W K = tri W K K K`;
* representation as an integral over the plane (the kernel `Gg W` vanishes outside the hexagon);
* trilinearity for continuous arguments;
* the three bounds `‖tri W X Y Z‖ ≤ (W.bound²/2) ‖·‖_{L¹[-1,1]} (‖·‖²_{L²[-1,1]} + ‖·‖²_{L²[-1,1]})`, with the
  `L¹` norm on any of the three slots (the bound `Gg ≤ 2` of the quadratic window becomes `Gg W ≤ W.bound²`).
The window-independent lemmas are those of `TMA.T3` (imported, not copied).
See BLUEPRINT.md, module "T3" (error term) and section "General windows (TMG)".
-/

open MeasureTheory Complex
open scoped BigOperators ArithmeticFunction Real

noncomputable section
namespace TMG.T3
open TMA TMA.T3

variable (W : Window)

/-- the trilinear form behind `t3 W` -/
def tri (X Y Z : ℝ → ℂ) : ℂ :=
  ∫ x in (-1 : ℝ)..1, ∫ y in (-1 : ℝ)..1, (Gg W x y : ℂ) * (X x * Y y * Z (-x - y))

theorem t3_eq_tri (K : ℝ → ℂ) : t3 W K = tri W K K K := rfl

/-- the integrand of `tri W` as a function on the plane -/
def triF (X Y Z : ℝ → ℂ) (p : ℝ × ℝ) : ℂ :=
  (Gg W p.1 p.2 : ℂ) * (X p.1 * Y p.2 * Z (-p.1 - p.2))

theorem bound_sq_pos : 0 < W.bound ^ 2 := by
  have := W.one_le_bound
  positivity

theorem Gg_eq_zero_of_not {r s : ℝ} (h : ¬ (|r| ≤ 1 ∧ |s| ≤ 1 ∧ |r + s| ≤ 1)) : Gg W r s = 0 := by
  apply Gg_eq_zero
  by_contra hc
  simp only [not_or, not_lt] at hc
  exact h hc

theorem abs_Gg_le (r s : ℝ) : |Gg W r s| ≤ W.bound ^ 2 := by
  rw [abs_of_nonneg (Gg_nonneg W r s)]
  exact Gg_le W r s

theorem triF_eq_zero {X Y Z : ℝ → ℂ} {p : ℝ × ℝ} (h : ¬ (|p.1| ≤ 1 ∧ |p.2| ≤ 1 ∧ |p.1 + p.2| ≤ 1)) :
    triF W X Y Z p = 0 := by
  simp [triF, Gg_eq_zero_of_not W h]

theorem continuous_triF {X Y Z : ℝ → ℂ} (hX : Continuous X) (hY : Continuous Y) (hZ : Continuous Z) :
    Continuous (triF W X Y Z) := by
  unfold triF
  have h1 : Continuous (fun p : ℝ × ℝ => (Gg W p.1 p.2 : ℂ)) :=
    Complex.continuous_ofReal.comp (continuous_Gg W)
  have h2 : Continuous (fun p : ℝ × ℝ => X p.1) := hX.comp continuous_fst
  have h3 : Continuous (fun p : ℝ × ℝ => Y p.2) := hY.comp continuous_snd
  have h4 : Continuous (fun p : ℝ × ℝ => Z (-p.1 - p.2)) :=
    hZ.comp (continuous_fst.neg.sub continuous_snd)
  exact h1.mul ((h2.mul h3).mul h4)

theorem integrable_triF {X Y Z : ℝ → ℂ} (hX : Continuous X) (hY : Continuous Y) (hZ : Continuous Z) :
    Integrable (triF W X Y Z) :=
  integrable_of_continuous_of_square (continuous_triF W hX hY hZ) 1
    (fun _ h => triF_eq_zero W (fun h' => h ⟨h'.1, h'.2.1⟩))

/-- `tri W` as an iterated integral over the line -/
theorem tri_eq_integral_integral (X Y Z : ℝ → ℂ) :
    tri W X Y Z = ∫ x, ∫ y, triF W X Y Z (x, y) := by
  unfold tri
  have h1 : ∀ x : ℝ, ∫ y in (-1 : ℝ)..1, (Gg W x y : ℂ) * (X x * Y y * Z (-x - y))
      = ∫ y, triF W X Y Z (x, y) := by
    intro x
    apply intervalIntegral_eq_integral_of_zero (f := fun y => triF W X Y Z (x, y))
    intro y hy
    exact triF_eq_zero W (p := (x, y)) (fun h => hy h.2.1)
  simp_rw [h1]
  apply intervalIntegral_eq_integral_of_zero
  intro x hx
  have : ∀ y, triF W X Y Z (x, y) = 0 := fun y => triF_eq_zero W (p := (x, y)) (fun h => hx h.1)
  simp [this]

/-- `tri W` as an integral over the plane -/
theorem tri_eq_integral_prod {X Y Z : ℝ → ℂ} (hX : Continuous X) (hY : Continuous Y) (hZ : Continuous Z) :
    tri W X Y Z = ∫ p, triF W X Y Z p := by
  rw [tri_eq_integral_integral]
  exact (integral_prod _ (integrable_triF W hX hY hZ)).symm

/-! ### trilinearity -/

theorem tri_smul_left (c : ℂ) (X Y Z : ℝ → ℂ) : tri W (fun x => c * X x) Y Z = c * tri W X Y Z := by
  unfold tri
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr (fun x _ => ?_)
  beta_reduce
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr (fun y _ => ?_)
  ring

theorem tri_smul_mid (c : ℂ) (X Y Z : ℝ → ℂ) : tri W X (fun x => c * Y x) Z = c * tri W X Y Z := by
  unfold tri
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr (fun x _ => ?_)
  beta_reduce
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr (fun y _ => ?_)
  ring

theorem tri_smul_right (c : ℂ) (X Y Z : ℝ → ℂ) : tri W X Y (fun x => c * Z x) = c * tri W X Y Z := by
  unfold tri
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr (fun x _ => ?_)
  beta_reduce
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr (fun y _ => ?_)
  ring

theorem tri_add_left {X X' Y Z : ℝ → ℂ} (hX : Continuous X) (hX' : Continuous X') (hY : Continuous Y)
    (hZ : Continuous Z) : tri W (fun x => X x + X' x) Y Z = tri W X Y Z + tri W X' Y Z := by
  rw [tri_eq_integral_prod W (X := fun x => X x + X' x) (hX.add hX') hY hZ,
    tri_eq_integral_prod W hX hY hZ, tri_eq_integral_prod W hX' hY hZ,
    ← integral_add (integrable_triF W hX hY hZ) (integrable_triF W hX' hY hZ)]
  congr 1
  funext p
  simp only [triF]
  ring

theorem tri_add_mid {X Y Y' Z : ℝ → ℂ} (hX : Continuous X) (hY : Continuous Y) (hY' : Continuous Y')
    (hZ : Continuous Z) : tri W X (fun x => Y x + Y' x) Z = tri W X Y Z + tri W X Y' Z := by
  rw [tri_eq_integral_prod W (Y := fun x => Y x + Y' x) hX (hY.add hY') hZ,
    tri_eq_integral_prod W hX hY hZ, tri_eq_integral_prod W hX hY' hZ,
    ← integral_add (integrable_triF W hX hY hZ) (integrable_triF W hX hY' hZ)]
  congr 1
  funext p
  simp only [triF]
  ring

theorem tri_add_right {X Y Z Z' : ℝ → ℂ} (hX : Continuous X) (hY : Continuous Y) (hZ : Continuous Z)
    (hZ' : Continuous Z') : tri W X Y (fun x => Z x + Z' x) = tri W X Y Z + tri W X Y Z' := by
  rw [tri_eq_integral_prod W (Z := fun x => Z x + Z' x) hX hY (hZ.add hZ'),
    tri_eq_integral_prod W hX hY hZ, tri_eq_integral_prod W hX hY hZ',
    ← integral_add (integrable_triF W hX hY hZ) (integrable_triF W hX hY hZ')]
  congr 1
  funext p
  simp only [triF]
  ring

theorem tri_sub_left {X X' Y Z : ℝ → ℂ} (hX : Continuous X) (hX' : Continuous X') (hY : Continuous Y)
    (hZ : Continuous Z) : tri W (fun x => X x - X' x) Y Z = tri W X Y Z - tri W X' Y Z := by
  rw [tri_eq_integral_prod W (X := fun x => X x - X' x) (hX.sub hX') hY hZ,
    tri_eq_integral_prod W hX hY hZ, tri_eq_integral_prod W hX' hY hZ,
    ← integral_sub (integrable_triF W hX hY hZ) (integrable_triF W hX' hY hZ)]
  congr 1
  funext p
  simp only [triF]
  ring

theorem tri_sub_mid {X Y Y' Z : ℝ → ℂ} (hX : Continuous X) (hY : Continuous Y) (hY' : Continuous Y')
    (hZ : Continuous Z) : tri W X (fun x => Y x - Y' x) Z = tri W X Y Z - tri W X Y' Z := by
  rw [tri_eq_integral_prod W (Y := fun x => Y x - Y' x) hX (hY.sub hY') hZ,
    tri_eq_integral_prod W hX hY hZ, tri_eq_integral_prod W hX hY' hZ,
    ← integral_sub (integrable_triF W hX hY hZ) (integrable_triF W hX hY' hZ)]
  congr 1
  funext p
  simp only [triF]
  ring

theorem tri_sub_right {X Y Z Z' : ℝ → ℂ} (hX : Continuous X) (hY : Continuous Y) (hZ : Continuous Z)
    (hZ' : Continuous Z') : tri W X Y (fun x => Z x - Z' x) = tri W X Y Z - tri W X Y Z' := by
  rw [tri_eq_integral_prod W (Z := fun x => Z x - Z' x) hX hY (hZ.sub hZ'),
    tri_eq_integral_prod W hX hY hZ, tri_eq_integral_prod W hX hY hZ',
    ← integral_sub (integrable_triF W hX hY hZ) (integrable_triF W hX hY hZ')]
  congr 1
  funext p
  simp only [triF]
  ring

theorem tri_sum_left {ι : Type*} (s : Finset ι) {f : ι → ℝ → ℂ} (hf : ∀ i ∈ s, Continuous (f i))
    {Y Z : ℝ → ℂ} (hY : Continuous Y) (hZ : Continuous Z) :
    tri W (fun x => ∑ i ∈ s, f i x) Y Z = ∑ i ∈ s, tri W (f i) Y Z := by
  rw [tri_eq_integral_prod W (continuous_finsetSum s hf) hY hZ]
  have h : (fun p => triF W (fun x => ∑ i ∈ s, f i x) Y Z p) = fun p => ∑ i ∈ s, triF W (f i) Y Z p := by
    funext p
    simp only [triF, Finset.sum_mul, Finset.mul_sum]
  rw [h, integral_finsetSum s (fun i hi => integrable_triF W (hf i hi) hY hZ)]
  exact Finset.sum_congr rfl (fun i hi => (tri_eq_integral_prod W (hf i hi) hY hZ).symm)

theorem tri_sum_mid {ι : Type*} (s : Finset ι) {f : ι → ℝ → ℂ} (hf : ∀ i ∈ s, Continuous (f i))
    {X Z : ℝ → ℂ} (hX : Continuous X) (hZ : Continuous Z) :
    tri W X (fun x => ∑ i ∈ s, f i x) Z = ∑ i ∈ s, tri W X (f i) Z := by
  rw [tri_eq_integral_prod W hX (continuous_finsetSum s hf) hZ]
  have h : (fun p => triF W X (fun x => ∑ i ∈ s, f i x) Z p) = fun p => ∑ i ∈ s, triF W X (f i) Z p := by
    funext p
    simp only [triF, Finset.sum_mul, Finset.mul_sum]
  rw [h, integral_finsetSum s (fun i hi => integrable_triF W hX (hf i hi) hZ)]
  exact Finset.sum_congr rfl (fun i hi => (tri_eq_integral_prod W hX (hf i hi) hZ).symm)

theorem tri_sum_right {ι : Type*} (s : Finset ι) {f : ι → ℝ → ℂ} (hf : ∀ i ∈ s, Continuous (f i))
    {X Y : ℝ → ℂ} (hX : Continuous X) (hY : Continuous Y) :
    tri W X Y (fun x => ∑ i ∈ s, f i x) = ∑ i ∈ s, tri W X Y (f i) := by
  rw [tri_eq_integral_prod W hX hY (continuous_finsetSum s hf)]
  have h : (fun p => triF W X Y (fun x => ∑ i ∈ s, f i x) p) = fun p => ∑ i ∈ s, triF W X Y (f i) p := by
    funext p
    simp only [triF, Finset.mul_sum]
  rw [h, integral_finsetSum s (fun i hi => integrable_triF W hX hY (hf i hi))]
  exact Finset.sum_congr rfl (fun i hi => (tri_eq_integral_prod W hX hY (hf i hi)).symm)

/-! ### bounds -/

/-- `TMA.T3.core_bound` with a general constant `c` in place of `2`. -/
theorem core_bound_c {Φ : ℝ → ℝ → ℂ} {U V Z : ℝ → ℂ} {c : ℝ} (hc : 0 < c) (hU : Continuous U)
    (hV : Continuous V) (hZ : Continuous Z)
    (hΦ0 : ∀ p q, ¬ (|p| ≤ 1 ∧ |q| ≤ 1 ∧ |p + q| ≤ 1) → Φ p q = 0)
    (hΦ : ∀ p q, ‖Φ p q‖ ≤ c * (‖U p‖ * (‖V q‖ * ‖Z (-p - q)‖))) :
    ‖∫ p, ∫ q, Φ p q‖ ≤ c / 2 * ((∫ p in (-1 : ℝ)..1, ‖U p‖) *
      ((∫ q in (-1 : ℝ)..1, ‖V q‖ ^ 2) + ∫ q in (-1 : ℝ)..1, ‖Z q‖ ^ 2)) := by
  have hc2 : (0 : ℝ) < 2 / c := by positivity
  have h := core_bound hU hV hZ (Φ := fun p q => ((2 / c : ℝ) : ℂ) * Φ p q)
    (fun p q hpq => by rw [hΦ0 p q hpq, mul_zero])
    (fun p q => by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc2]
      calc 2 / c * ‖Φ p q‖ ≤ 2 / c * (c * (‖U p‖ * (‖V q‖ * ‖Z (-p - q)‖))) :=
            mul_le_mul_of_nonneg_left (hΦ p q) hc2.le
        _ = 2 * (‖U p‖ * (‖V q‖ * ‖Z (-p - q)‖)) := by
            field_simp)
  have e : ∫ p, ∫ q, ((2 / c : ℝ) : ℂ) * Φ p q = ((2 / c : ℝ) : ℂ) * ∫ p, ∫ q, Φ p q := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun p => ?_))
    exact integral_const_mul _ _
  rw [e, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc2] at h
  have h2 : ‖∫ p, ∫ q, Φ p q‖ = c / 2 * (2 / c * ‖∫ p, ∫ q, Φ p q‖) := by
    field_simp
  rw [h2]
  exact mul_le_mul_of_nonneg_left h (by positivity)

theorem norm_triF_le (X Y Z : ℝ → ℂ) (p : ℝ × ℝ) :
    ‖triF W X Y Z p‖ ≤ W.bound ^ 2 * (‖X p.1‖ * ‖Y p.2‖ * ‖Z (-p.1 - p.2)‖) := by
  unfold triF
  rw [norm_mul, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right (abs_Gg_le W _ _) (by positivity)

/-- `L¹` norm on the first slot -/
theorem tri_bound_left {X Y Z : ℝ → ℂ} (hX : Continuous X) (hY : Continuous Y) (hZ : Continuous Z) :
    ‖tri W X Y Z‖ ≤ W.bound ^ 2 / 2 * ((∫ x in (-1 : ℝ)..1, ‖X x‖) *
      ((∫ x in (-1 : ℝ)..1, ‖Y x‖ ^ 2) + ∫ x in (-1 : ℝ)..1, ‖Z x‖ ^ 2)) := by
  rw [tri_eq_integral_integral]
  apply core_bound_c (bound_sq_pos W) hX hY hZ (Φ := fun x y => triF W X Y Z (x, y))
  · intro p q h
    exact triF_eq_zero W h
  · intro p q
    have h := norm_triF_le W X Y Z (p, q)
    simp only at h
    rw [mul_assoc] at h
    exact h

/-- `L¹` norm on the second slot -/
theorem tri_bound_mid {X Y Z : ℝ → ℂ} (hX : Continuous X) (hY : Continuous Y) (hZ : Continuous Z) :
    ‖tri W X Y Z‖ ≤ W.bound ^ 2 / 2 * ((∫ x in (-1 : ℝ)..1, ‖Y x‖) *
      ((∫ x in (-1 : ℝ)..1, ‖X x‖ ^ 2) + ∫ x in (-1 : ℝ)..1, ‖Z x‖ ^ 2)) := by
  rw [tri_eq_integral_integral,
    integral_integral_swap (f := fun x y => triF W X Y Z (x, y)) (integrable_triF W hX hY hZ)]
  apply core_bound_c (bound_sq_pos W) hY hX hZ (Φ := fun y x => triF W X Y Z (x, y))
  · intro p q h
    apply triF_eq_zero
    intro h'
    exact h ⟨h'.2.1, h'.1, by rw [add_comm]; exact h'.2.2⟩
  · intro p q
    have h := norm_triF_le W X Y Z (q, p)
    simp only at h
    have e : -p - q = -q - p := by ring
    rw [e]
    calc ‖triF W X Y Z (q, p)‖ ≤ W.bound ^ 2 * (‖X q‖ * ‖Y p‖ * ‖Z (-q - p)‖) := h
      _ = W.bound ^ 2 * (‖Y p‖ * (‖X q‖ * ‖Z (-q - p)‖)) := by ring

/-- `L¹` norm on the third slot -/
theorem tri_bound_right {X Y Z : ℝ → ℂ} (hX : Continuous X) (hY : Continuous Y) (hZ : Continuous Z) :
    ‖tri W X Y Z‖ ≤ W.bound ^ 2 / 2 * ((∫ x in (-1 : ℝ)..1, ‖Z x‖) *
      ((∫ x in (-1 : ℝ)..1, ‖X x‖ ^ 2) + ∫ x in (-1 : ℝ)..1, ‖Y x‖ ^ 2)) := by
  rw [tri_eq_integral_integral]
  have h1 : ∀ x : ℝ, ∫ y, triF W X Y Z (x, y) = ∫ v, triF W X Y Z (x, -x - v) := fun x =>
    (integral_sub_left_eq_self (fun y => triF W X Y Z (x, y)) volume (-x)).symm
  simp_rw [h1]
  have hG : Integrable (fun p : ℝ × ℝ => triF W X Y Z (p.1, -p.1 - p.2)) := by
    apply integrable_of_continuous_of_square _ 1
    · intro p h
      apply triF_eq_zero
      intro h'
      apply h
      refine ⟨h'.1, ?_⟩
      have h3 := h'.2.2
      have e : p.1 + (-p.1 - p.2) = -p.2 := by ring
      simp only at h3
      rw [e, abs_neg] at h3
      exact h3
    · exact (continuous_triF W hX hY hZ).comp
        (continuous_fst.prodMk (continuous_fst.neg.sub continuous_snd))
  rw [integral_integral_swap (f := fun x v => triF W X Y Z (x, -x - v)) hG]
  apply core_bound_c (bound_sq_pos W) hZ hX hY (Φ := fun v x => triF W X Y Z (x, -x - v))
  · intro v x h
    apply triF_eq_zero
    intro h'
    apply h
    have h2 := h'.2.1
    have h3 := h'.2.2
    simp only at h2 h3
    have e : x + (-x - v) = -v := by ring
    rw [e, abs_neg] at h3
    have e2 : -x - v = -(v + x) := by ring
    rw [e2, abs_neg] at h2
    exact ⟨h3, h'.1, h2⟩
  · intro v x
    have h := norm_triF_le W X Y Z (x, -x - v)
    simp only at h
    have e1 : -x - (-x - v) = v := by ring
    have e2 : -v - x = -x - v := by ring
    rw [e1] at h
    rw [e2]
    calc ‖triF W X Y Z (x, -x - v)‖ ≤ W.bound ^ 2 * (‖X x‖ * ‖Y (-x - v)‖ * ‖Z v‖) := h
      _ = W.bound ^ 2 * (‖Z v‖ * (‖X x‖ * ‖Y (-x - v)‖)) := by ring

end TMG.T3
end
end Src_TMG_Trace3Aux1

section Src_TMG_Trace3Aux2
/-
Written for Kristian Muri Knausgård, drafted with Claude (Anthropic), 22 November 2026.

TMG/Trace3Aux2.lean — packet triples for a general window and the error term of the third trace
(generalisation of the `Gg`-dependent parts of TMA/Trace3Aux2.lean and TMA/Trace3Aux3.lean):
* closure: `tri W` of three packets vanishes unless the centres add up to at most `3κ/A` in absolute value;
* size: `‖tri W‖ ≤ W.bound² T³ M (∫‖k‖)² / A²`;
* evaluation: if the centres add up to zero and `κ/A` is below a modulus of uniform continuity of `Gg W` for the
  tolerance `η`, then `tri W = (T³/A²) (Gg W l1 l2 · (1/2π) ∫ h³ + O(η))` (no Lipschitz bound is available);
* `‖t3 W Kfull - t3 W K0‖ ≤ C T`.
See BLUEPRINT.md, module "T3" and section "General windows (TMG)".
-/

open MeasureTheory Complex
open scoped BigOperators ArithmeticFunction Real

noncomputable section
namespace TMG.T3
open TMA TMA.T3

variable (W : Window)

/-! ### packet triples -/

/-- **Closure.** A packet triple vanishes unless the centres nearly add up to zero. -/
theorem tri_packet_eq_zero (w : HeightWeight) {T σ l1 l2 l3 : ℝ} (hA : 0 < Asc T σ)
    (h : 3 * w.kappa / Asc T σ < |l1 + l2 + l3|) :
    tri W (packet w.k T σ l1) (packet w.k T σ l2) (packet w.k T σ l3) = 0 := by
  have h0 : ∀ x y : ℝ,
      packet w.k T σ l1 x * packet w.k T σ l2 y * packet w.k T σ l3 (-x - y) = 0 := by
    intro x y
    by_contra hne
    have h1 : packet w.k T σ l1 x ≠ 0 := fun h' => hne (by rw [h']; ring)
    have h2 : packet w.k T σ l2 y ≠ 0 := fun h' => hne (by rw [h']; ring)
    have h3 : packet w.k T σ l3 (-x - y) ≠ 0 := fun h' => hne (by rw [h']; ring)
    have a1 := packet_ne_zero_abs w hA h1
    have a2 := packet_ne_zero_abs w hA h2
    have a3 := packet_ne_zero_abs w hA h3
    have hle : |l1 + l2 + l3| ≤ 3 * w.kappa / Asc T σ := by
      have e : l1 + l2 + l3 = -((x - l1) + (y - l2) + (-x - y - l3)) := by ring
      have e' : 3 * w.kappa / Asc T σ
          = w.kappa / Asc T σ + w.kappa / Asc T σ + w.kappa / Asc T σ := by ring
      rw [e, abs_neg, e']
      exact (abs_add_three _ _ _).trans (by linarith)
    linarith
  unfold tri
  simp [h0]

/-- **Size.** -/
theorem norm_tri_packet_le (w : HeightWeight) {M : ℝ} (hM : ∀ y, ‖w.k y‖ ≤ M) {T σ : ℝ}
    (hT : 0 ≤ T) (hA : 0 < Asc T σ) (l1 l2 l3 : ℝ) :
    ‖tri W (packet w.k T σ l1) (packet w.k T σ l2) (packet w.k T σ l3)‖
      ≤ W.bound ^ 2 * T ^ 3 * M * (∫ y, ‖w.k y‖) ^ 2 / Asc T σ ^ 2 := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  set Ik : ℝ := ∫ y, ‖w.k y‖ with hIk
  set c : ℝ := W.bound ^ 2 * (T * M) * (T * (Asc T σ)⁻¹ * Ik) with hc
  rw [tri_eq_integral_integral]
  have hin : ∀ x : ℝ,
      ‖∫ y, triF W (packet w.k T σ l1) (packet w.k T σ l2) (packet w.k T σ l3) (x, y)‖
        ≤ ‖packet w.k T σ l1 x‖ * c := by
    intro x
    have hg : Integrable
        (fun y => W.bound ^ 2 * (‖packet w.k T σ l1 x‖ * (T * M)) * ‖packet w.k T σ l2 y‖) :=
      (integrable_norm_packet w hA l2).const_mul _
    calc ‖∫ y, triF W (packet w.k T σ l1) (packet w.k T σ l2) (packet w.k T σ l3) (x, y)‖
        ≤ ∫ y, ‖triF W (packet w.k T σ l1) (packet w.k T σ l2) (packet w.k T σ l3) (x, y)‖ :=
          norm_integral_le_integral_norm _
      _ ≤ ∫ y, W.bound ^ 2 * (‖packet w.k T σ l1 x‖ * (T * M)) * ‖packet w.k T σ l2 y‖ := by
          apply integral_mono_of_nonneg (Filter.Eventually.of_forall (fun y => norm_nonneg _)) hg
          apply Filter.Eventually.of_forall
          intro y
          have h1 := norm_triF_le W (packet w.k T σ l1) (packet w.k T σ l2) (packet w.k T σ l3) (x, y)
          have h2 := norm_packet_le w hM hT σ l3 (-x - y)
          have h3 : 0 ≤ ‖packet w.k T σ l1 x‖ * ‖packet w.k T σ l2 y‖ := by positivity
          have h4 := mul_le_mul_of_nonneg_left h2 h3
          have h5 := mul_le_mul_of_nonneg_left h4 (sq_nonneg W.bound)
          simp only at h1
          show ‖triF W (packet w.k T σ l1) (packet w.k T σ l2) (packet w.k T σ l3) (x, y)‖
            ≤ W.bound ^ 2 * (‖packet w.k T σ l1 x‖ * (T * M)) * ‖packet w.k T σ l2 y‖
          calc ‖triF W (packet w.k T σ l1) (packet w.k T σ l2) (packet w.k T σ l3) (x, y)‖
              ≤ W.bound ^ 2 * (‖packet w.k T σ l1 x‖ * ‖packet w.k T σ l2 y‖
                  * ‖packet w.k T σ l3 (-x - y)‖) := h1
            _ ≤ W.bound ^ 2 * (‖packet w.k T σ l1 x‖ * ‖packet w.k T σ l2 y‖ * (T * M)) := h5
            _ = W.bound ^ 2 * (‖packet w.k T σ l1 x‖ * (T * M)) * ‖packet w.k T σ l2 y‖ := by ring
      _ = ‖packet w.k T σ l1 x‖ * c := by
          rw [integral_const_mul, integral_norm_packet w hT hA l2, hc]
          ring
  calc ‖∫ x, ∫ y, triF W (packet w.k T σ l1) (packet w.k T σ l2) (packet w.k T σ l3) (x, y)‖
      ≤ ∫ x, ‖∫ y, triF W (packet w.k T σ l1) (packet w.k T σ l2) (packet w.k T σ l3) (x, y)‖ :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ x, ‖packet w.k T σ l1 x‖ * c := by
        apply integral_mono_of_nonneg (Filter.Eventually.of_forall (fun y => norm_nonneg _))
          ((integrable_norm_packet w hA l1).mul_const _)
        exact Filter.Eventually.of_forall hin
    _ = W.bound ^ 2 * T ^ 3 * M * Ik ^ 2 / Asc T σ ^ 2 := by
        rw [integral_mul_const, integral_norm_packet w hT hA l1, hc, ← hIk]
        field_simp

/-- **Evaluation.** If the centres add up to zero and `κ/A ≤ δ'`, where `δ'` is a modulus of uniform
continuity of `Gg W` for the tolerance `η`, the packet triple is `(T³/A²) · Gg W l1 l2 · (1/2π) ∫ h³` up to
`(T³/A²) · η M (∫‖k‖)²`. -/
theorem tri_packet_eval (w : HeightWeight) {M : ℝ} (hM : ∀ y, ‖w.k y‖ ≤ M) {T σ : ℝ}
    (hA : 0 < Asc T σ) {η δ' : ℝ}
    (hG : ∀ r s d e : ℝ, |d| ≤ δ' → |e| ≤ δ' → |Gg W (r + d) (s + e) - Gg W r s| ≤ η)
    (hκδ : w.kappa / Asc T σ ≤ δ') {l1 l2 l3 : ℝ} (h : l1 + l2 + l3 = 0) :
    ‖tri W (packet w.k T σ l1) (packet w.k T σ l2) (packet w.k T σ l3)
        - ((T ^ 3 / Asc T σ ^ 2 * (Gg W l1 l2 * ((1 / (2 * π)) * w.kap3)) : ℝ) : ℂ)‖
      ≤ |T| ^ 3 / Asc T σ ^ 2 * (η * M * (∫ y, ‖w.k y‖) ^ 2) := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  have hκ := w.kappa_pos
  have hδ0 : 0 ≤ δ' := (div_pos hκ hA).le.trans hκδ
  have hη0 : 0 ≤ η :=
    (abs_nonneg _).trans (hG 0 0 0 0 (by rw [abs_zero]; exact hδ0) (by rw [abs_zero]; exact hδ0))
  set A : ℝ := Asc T σ with hAdef
  have hA' : A ≠ 0 := hA.ne'
  set Ik : ℝ := ∫ y, ‖w.k y‖ with hIk
  set P1 := packet w.k T σ l1 with hP1
  set P2 := packet w.k T σ l2 with hP2
  set P3 := packet w.k T σ l3 with hP3
  -- the two integrands in the scaled variables
  set K3 : ℝ × ℝ → ℂ := fun p => w.k p.1 * w.k p.2 * w.k (-p.1 - p.2) with hK3
  set H : ℝ × ℝ → ℂ := fun p => (Gg W (l1 - p.1 / A) (l2 - p.2 / A) : ℂ) * K3 p with hH
  have hK3c : Continuous K3 :=
    ((w.continuous_k.comp continuous_fst).mul (w.continuous_k.comp continuous_snd)).mul
      (w.continuous_k.comp (continuous_fst.neg.sub continuous_snd))
  have hK30 : ∀ p : ℝ × ℝ, ¬ (|p.1| ≤ w.kappa ∧ |p.2| ≤ w.kappa) → K3 p = 0 := by
    intro p hp
    by_contra hne
    apply hp
    constructor
    · apply w.k_supp
      intro h0
      exact hne (by simp [hK3, h0])
    · apply w.k_supp
      intro h0
      exact hne (by simp [hK3, h0])
  have hK3i : Integrable K3 := integrable_of_continuous_of_square hK3c w.kappa hK30
  have hHc : Continuous H := by
    have hGc : Continuous (fun p : ℝ × ℝ => (Gg W (l1 - p.1 / A) (l2 - p.2 / A) : ℂ)) :=
      Complex.continuous_ofReal.comp ((continuous_Gg W).comp
        ((continuous_const.sub (continuous_fst.div_const A)).prodMk
          (continuous_const.sub (continuous_snd.div_const A))))
    exact hGc.mul hK3c
  have hHi : Integrable H :=
    integrable_of_continuous_of_square hHc w.kappa (fun p hp => by simp [hH, hK30 p hp])
  -- the packet triple in the scaled variables
  have hpt : ∀ y1 y2 : ℝ, triF W P1 P2 P3 (l1 - y1 / A, l2 - y2 / A) = (T : ℂ) ^ 3 * H (y1, y2) := by
    intro y1 y2
    have e1 : -(A * (l1 - y1 / A - l1)) = y1 := by
      field_simp
      ring
    have e2 : -(A * (l2 - y2 / A - l2)) = y2 := by
      field_simp
      ring
    have e3 : -(A * (-(l1 - y1 / A) - (l2 - y2 / A) - l3)) = -y1 - y2 := by
      have hl3 : l3 = -l1 - l2 := by linarith
      rw [hl3]
      field_simp
      ring
    simp only [triF, hP1, hP2, hP3, packet, hH, hK3]
    rw [← hAdef, e1, e2, e3]
    ring
  have hstep : tri W P1 P2 P3 = ((T : ℂ) ^ 3 * ((A⁻¹ : ℝ) : ℂ) ^ 2) * ∫ p, H p := by
    rw [tri_eq_integral_integral]
    have hinner : ∀ x : ℝ,
        ∫ y, triF W P1 P2 P3 (x, y) = A⁻¹ • ∫ y2, triF W P1 P2 P3 (x, l2 - y2 / A) :=
      fun x => integral_eq_smul_integral_comp (fun y => triF W P1 P2 P3 (x, y)) hA l2
    simp_rw [hinner]
    rw [integral_eq_smul_integral_comp (fun x => A⁻¹ • ∫ y2, triF W P1 P2 P3 (x, l2 - y2 / A)) hA l1]
    simp only [hpt]
    have hprod : ∫ p, H p = ∫ x, ∫ y, H (x, y) := integral_prod H hHi
    rw [hprod]
    simp only [integral_const_mul, Complex.real_smul]
    ring
  have hmain : ((T ^ 3 / A ^ 2 * (Gg W l1 l2 * ((1 / (2 * π)) * w.kap3)) : ℝ) : ℂ)
      = ((T : ℂ) ^ 3 * ((A⁻¹ : ℝ) : ℂ) ^ 2) * ∫ p, (Gg W l1 l2 : ℂ) * K3 p := by
    have hprod : ∫ p, K3 p = ∫ x, ∫ y, K3 (x, y) := integral_prod K3 hK3i
    rw [integral_const_mul, hprod]
    have hinv := w.inv3
    simp only [hK3]
    rw [hinv]
    unfold HeightWeight.kap3
    push_cast
    field_simp
  rw [hstep, hmain, ← mul_sub, ← integral_sub hHi (hK3i.const_mul _), norm_mul]
  have hnorm : ‖(T : ℂ) ^ 3 * ((A⁻¹ : ℝ) : ℂ) ^ 2‖ = |T| ^ 3 / A ^ 2 := by
    rw [norm_mul, norm_pow, norm_pow, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hA)]
    field_simp
  rw [hnorm]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  set c : ℝ := η * M with hc
  have hgi : Integrable (fun p : ℝ × ℝ => c * (‖w.k p.1‖ * ‖w.k p.2‖)) :=
    (w.integrable_k.norm.mul_prod w.integrable_k.norm).const_mul c
  calc ‖∫ p, (H p - (Gg W l1 l2 : ℂ) * K3 p)‖ ≤ ∫ p, ‖H p - (Gg W l1 l2 : ℂ) * K3 p‖ :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ p : ℝ × ℝ, c * (‖w.k p.1‖ * ‖w.k p.2‖) := by
        apply integral_mono_of_nonneg (Filter.Eventually.of_forall (fun y => norm_nonneg _)) hgi
        apply Filter.Eventually.of_forall
        intro p
        show ‖H p - (Gg W l1 l2 : ℂ) * K3 p‖ ≤ c * (‖w.k p.1‖ * ‖w.k p.2‖)
        by_cases hp : |p.1| ≤ w.kappa ∧ |p.2| ≤ w.kappa
        · have e : H p - (Gg W l1 l2 : ℂ) * K3 p
              = ((Gg W (l1 - p.1 / A) (l2 - p.2 / A) - Gg W l1 l2 : ℝ) : ℂ) * K3 p := by
            simp only [hH]
            push_cast
            ring
          rw [e, norm_mul, Complex.norm_real, Real.norm_eq_abs]
          have hl1 : |-(p.1 / A)| ≤ δ' := by
            rw [abs_neg, abs_div, abs_of_pos hA]
            exact (div_le_div_of_nonneg_right hp.1 hA.le).trans hκδ
          have hl2 : |-(p.2 / A)| ≤ δ' := by
            rw [abs_neg, abs_div, abs_of_pos hA]
            exact (div_le_div_of_nonneg_right hp.2 hA.le).trans hκδ
          have hGG : |Gg W (l1 - p.1 / A) (l2 - p.2 / A) - Gg W l1 l2| ≤ η := by
            have h1 := hG l1 l2 (-(p.1 / A)) (-(p.2 / A)) hl1 hl2
            rw [← sub_eq_add_neg, ← sub_eq_add_neg] at h1
            exact h1
          have hK : ‖K3 p‖ ≤ M * (‖w.k p.1‖ * ‖w.k p.2‖) := by
            simp only [hK3]
            rw [norm_mul, norm_mul]
            have := hM (-p.1 - p.2)
            have h0 : 0 ≤ ‖w.k p.1‖ * ‖w.k p.2‖ := by positivity
            linarith [mul_le_mul_of_nonneg_left this h0]
          calc |Gg W (l1 - p.1 / A) (l2 - p.2 / A) - Gg W l1 l2| * ‖K3 p‖
              ≤ η * (M * (‖w.k p.1‖ * ‖w.k p.2‖)) :=
                mul_le_mul hGG hK (norm_nonneg _) hη0
            _ = c * (‖w.k p.1‖ * ‖w.k p.2‖) := by
                rw [hc]
                ring
        · have h0 : H p - (Gg W l1 l2 : ℂ) * K3 p = 0 := by simp [hH, hK30 p hp]
          rw [h0, norm_zero]
          positivity
    _ = η * M * Ik ^ 2 := by
        have hprod : ∫ p : ℝ × ℝ, ‖w.k p.1‖ * ‖w.k p.2‖ = Ik * Ik :=
          integral_prod_mul (fun y : ℝ => ‖w.k y‖) (fun y : ℝ => ‖w.k y‖)
        rw [integral_const_mul, hprod, hc]
        ring

/-- **Closure in logarithmic form.** -/
theorem tri_packet_eq_zero_log (w : HeightWeight) {T σ : ℝ} (hσ : 0 < σ) (hS : Sep w T σ)
    {l1 l2 l3 a : ℝ} (hl : l1 + l2 + l3 = a / (σ * Real.log T)) (ha : 3 * w.kappa / T < |a|) :
    tri W (packet w.k T σ l1) (packet w.k T σ l2) (packet w.k T σ l3) = 0 := by
  apply tri_packet_eq_zero W w hS.A_pos
  rw [hl]
  exact scale_lt hS.T_pos (mul_pos hσ hS.log_pos) _ _ ha

/-! ### the error term -/

/-- the difference of two third traces in terms of the `L¹` and `L²` norms of the difference -/
theorem t3_sub_t3_bound {Kf Kz : ℝ → ℂ} (hcKf : Continuous Kf) (hcKz : Continuous Kz) :
    ‖t3 W Kf - t3 W Kz‖ ≤ W.bound ^ 2 / 2 * ((∫ x in (-1 : ℝ)..1, ‖Kf x - Kz x‖) *
      (9 * (∫ x in (-1 : ℝ)..1, ‖Kz x‖ ^ 2) + 6 * ∫ x in (-1 : ℝ)..1, ‖Kf x - Kz x‖ ^ 2)) := by
  set E : ℝ → ℂ := fun x => Kf x - Kz x with hEdef
  have hcE : Continuous E := hcKf.sub hcKz
  have hKfE : Kf = fun x => Kz x + E x := by
    funext x
    simp only [hEdef]
    ring
  set N1 : ℝ := ∫ x in (-1 : ℝ)..1, ‖E x‖ with hN1
  set SE : ℝ := ∫ x in (-1 : ℝ)..1, ‖E x‖ ^ 2 with hSE
  set SK : ℝ := ∫ x in (-1 : ℝ)..1, ‖Kz x‖ ^ 2 with hSK
  set SF : ℝ := ∫ x in (-1 : ℝ)..1, ‖Kf x‖ ^ 2 with hSFdef
  set b : ℝ := W.bound ^ 2 / 2 with hb
  have hb0 : 0 ≤ b := by positivity
  have hN10 : 0 ≤ N1 := intervalIntegral.integral_nonneg (by norm_num) (fun x _ => norm_nonneg _)
  -- `∫ ‖Kf‖² ≤ 2 ∫ ‖K0‖² + 2 ∫ ‖E‖²`
  have hi1 : IntervalIntegrable (fun x => 2 * ‖Kz x‖ ^ 2) volume (-1) 1 :=
    (continuous_const.mul (hcKz.norm.pow 2)).intervalIntegrable _ _
  have hi2 : IntervalIntegrable (fun x => 2 * ‖E x‖ ^ 2) volume (-1) 1 :=
    (continuous_const.mul (hcE.norm.pow 2)).intervalIntegrable _ _
  have hSF : SF ≤ 2 * SK + 2 * SE := by
    have h1 : SF ≤ ∫ x in (-1 : ℝ)..1, (2 * ‖Kz x‖ ^ 2 + 2 * ‖E x‖ ^ 2) := by
      apply intervalIntegral.integral_mono_on (by norm_num)
      · exact (hcKf.norm.pow 2).intervalIntegrable _ _
      · exact hi1.add hi2
      · intro x _
        have h2 : ‖Kf x‖ ≤ ‖Kz x‖ + ‖E x‖ := by
          have h3 : Kf x = Kz x + E x := congrFun hKfE x
          rw [h3]
          exact norm_add_le _ _
        have h3 : ‖Kf x‖ ^ 2 ≤ (‖Kz x‖ + ‖E x‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h2 2
        linarith [sq_nonneg (‖Kz x‖ - ‖E x‖)]
    rw [intervalIntegral.integral_add hi1 hi2, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul] at h1
    exact h1
  -- the telescoping identity
  have htel : t3 W Kf - t3 W Kz = tri W E Kf Kf + tri W Kz E Kf + tri W Kz Kz E := by
    rw [t3_eq_tri, t3_eq_tri]
    have e1 : tri W Kf Kf Kf = tri W Kz Kf Kf + tri W E Kf Kf :=
      (congrArg (fun K => tri W K Kf Kf) hKfE).trans (tri_add_left W hcKz hcE hcKf hcKf)
    have e2 : tri W Kz Kf Kf = tri W Kz Kz Kf + tri W Kz E Kf :=
      (congrArg (fun K => tri W Kz K Kf) hKfE).trans (tri_add_mid W hcKz hcKz hcE hcKf)
    have e3 : tri W Kz Kz Kf = tri W Kz Kz Kz + tri W Kz Kz E :=
      (congrArg (fun K => tri W Kz Kz K) hKfE).trans (tri_add_right W hcKz hcKz hcKz hcE)
    rw [e1, e2, e3]
    ring
  have b1 : ‖tri W E Kf Kf‖ ≤ b * (N1 * (SF + SF)) := tri_bound_left W hcE hcKf hcKf
  have b2 : ‖tri W Kz E Kf‖ ≤ b * (N1 * (SK + SF)) := tri_bound_mid W hcKz hcE hcKf
  have b3 : ‖tri W Kz Kz E‖ ≤ b * (N1 * (SK + SK)) := tri_bound_right W hcKz hcKz hcE
  rw [htel]
  have h1 : ‖tri W E Kf Kf + tri W Kz E Kf + tri W Kz Kz E‖
      ≤ ‖tri W E Kf Kf‖ + ‖tri W Kz E Kf‖ + ‖tri W Kz Kz E‖ := norm_add₃_le
  have h2 : b * (N1 * (SF + SF)) + b * (N1 * (SK + SF)) + b * (N1 * (SK + SK))
      ≤ b * (N1 * (9 * SK + 6 * SE)) := by
    have e : b * (N1 * (SF + SF)) + b * (N1 * (SK + SF)) + b * (N1 * (SK + SK))
        = b * (N1 * (3 * SF + 3 * SK)) := by ring
    rw [e]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (by linarith) hN10) hb0
  linarith

theorem t3_error (hRH : RiemannHypothesis) (w : HeightWeight) {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ < 1) :
    ∃ C T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T → ‖t3 W (Kfull w.h T σ) - t3 W (K0 w.k T σ)‖ ≤ C * T := by
  obtain ⟨CE, T1, hE⟩ := kernel_error hRH w hσ hσ1
  obtain ⟨T2, hSep⟩ := sep_eventually w hσ hσ1
  obtain ⟨CK, hCK0, hK⟩ := K0_L2_bound w hσ hσ1
  set b : ℝ := W.bound ^ 2 / 2 with hb
  have hb0 : 0 ≤ b := by positivity
  refine ⟨b * (9 * CE * CK + 6 * CE ^ 2), max T1 T2, fun T hT => ?_⟩
  have hS := hSep T ((le_max_right _ _).trans hT)
  obtain ⟨_, hE1, hE2⟩ := hE T ((le_max_left _ _).trans hT)
  have hTpos := hS.T_pos
  have hL := hS.one_le_log
  have hLpos := hS.log_pos
  have hmain := t3_sub_t3_bound W (continuous_Kfull hRH w hTpos σ) (continuous_K0 w T σ)
  have hSKle := hK T hS
  set N1 : ℝ := ∫ x in (-1 : ℝ)..1, ‖Kfull w.h T σ x - K0 w.k T σ x‖ with hN1
  set SE : ℝ := ∫ x in (-1 : ℝ)..1, ‖Kfull w.h T σ x - K0 w.k T σ x‖ ^ 2 with hSE
  set SK : ℝ := ∫ x in (-1 : ℝ)..1, ‖K0 w.k T σ x‖ ^ 2 with hSK
  have hN10 : 0 ≤ N1 := intervalIntegral.integral_nonneg (by norm_num) (fun x _ => norm_nonneg _)
  have hSE0 : 0 ≤ SE := intervalIntegral.integral_nonneg (by norm_num) (fun x _ => by positivity)
  have hSK0 : 0 ≤ SK := intervalIntegral.integral_nonneg (by norm_num) (fun x _ => by positivity)
  have hCE0 : 0 ≤ CE := by
    have h1 : 0 ≤ CE / Real.log T := hN10.trans hE1
    have h2 := mul_nonneg h1 hLpos.le
    rwa [div_mul_cancel₀ _ hLpos.ne'] at h2
  have hbound : 9 * SK + 6 * SE ≤ 9 * (CK * (T * Real.log T)) + 6 * (CE * T / Real.log T) := by
    linarith
  have hprod : N1 * (9 * SK + 6 * SE) ≤ (9 * CE * CK + 6 * CE ^ 2) * T := by
    calc N1 * (9 * SK + 6 * SE)
        ≤ CE / Real.log T * (9 * (CK * (T * Real.log T)) + 6 * (CE * T / Real.log T)) :=
          mul_le_mul hE1 hbound (by positivity) (by positivity)
      _ = 9 * CE * CK * T + 6 * CE ^ 2 * T / Real.log T ^ 2 := by
          field_simp
      _ ≤ 9 * CE * CK * T + 6 * CE ^ 2 * T := by
          have h1 : 6 * CE ^ 2 * T / Real.log T ^ 2 ≤ 6 * CE ^ 2 * T := by
            apply div_le_self (by positivity)
            exact one_le_pow₀ hL
          linarith
      _ = (9 * CE * CK + 6 * CE ^ 2) * T := by ring
  calc ‖t3 W (Kfull w.h T σ) - t3 W (K0 w.k T σ)‖ ≤ b * (N1 * (9 * SK + 6 * SE)) := hmain
    _ ≤ b * ((9 * CE * CK + 6 * CE ^ 2) * T) := mul_le_mul_of_nonneg_left hprod hb0
    _ = b * (9 * CE * CK + 6 * CE ^ 2) * T := by ring

end TMG.T3
end
end Src_TMG_Trace3Aux2

section Src_TMG_Trace3Aux3
/-
Written for Kristian Muri Knausgård, drafted with Claude (Anthropic), 22 November 2026.

TMG/Trace3Aux3.lean — classification of the packet triples of `t3 W K0`, with `K0 = ell · P0 - Q`
(generalisation of TMA/Trace3Aux4.lean):
* the expansion into eight terms;
* one prime packet: the term vanishes (closure);
* two prime packets: only the diagonal `(p, bar p)` survives, and it is evaluated up to the tolerance `η` of a
  modulus of uniform continuity of `Gg W`;
* three prime packets: only `n_a n_b = n_c` survives; bounded with `triplePrime_bound`.
The combinatorial lemmas (`idx`, `cen`, `bar`, `Qk`, `Sep`, separation, `triple_delta_sum_le`, ...) are those of
`TMA.T3`.  See BLUEPRINT.md, module "T3" (main term) and section "General windows (TMG)".
-/

open MeasureTheory Complex
open scoped BigOperators ArithmeticFunction Real

noncomputable section
namespace TMG.T3
open TMA TMA.T3

variable (W : Window)

/-! ### the expansion into eight terms -/

theorem tri_lin_left {X X' Y Z : ℝ → ℂ} (hX : Continuous X) (hX' : Continuous X') (hY : Continuous Y)
    (hZ : Continuous Z) (c : ℂ) :
    tri W (fun x => c * X x - X' x) Y Z = c * tri W X Y Z - tri W X' Y Z := by
  rw [tri_sub_left W (X := fun x => c * X x) (continuous_const.mul hX) hX' hY hZ, tri_smul_left]

theorem tri_lin_mid {X Y Y' Z : ℝ → ℂ} (hX : Continuous X) (hY : Continuous Y) (hY' : Continuous Y')
    (hZ : Continuous Z) (c : ℂ) :
    tri W X (fun x => c * Y x - Y' x) Z = c * tri W X Y Z - tri W X Y' Z := by
  rw [tri_sub_mid W (Y := fun x => c * Y x) hX (continuous_const.mul hY) hY' hZ, tri_smul_mid]

theorem tri_lin_right {X Y Z Z' : ℝ → ℂ} (hX : Continuous X) (hY : Continuous Y) (hZ : Continuous Z)
    (hZ' : Continuous Z') (c : ℂ) :
    tri W X Y (fun x => c * Z x - Z' x) = c * tri W X Y Z - tri W X Y Z' := by
  rw [tri_sub_right W (Z := fun x => c * Z x) hX hY (continuous_const.mul hZ) hZ', tri_smul_right]

theorem tri_expand {P Q : ℝ → ℂ} (hP : Continuous P) (hQ : Continuous Q) (c : ℂ) :
    tri W (fun x => c * P x - Q x) (fun x => c * P x - Q x) (fun x => c * P x - Q x)
      = c ^ 3 * tri W P P P - c ^ 2 * (tri W Q P P + tri W P Q P + tri W P P Q)
        + c * (tri W Q Q P + tri W Q P Q + tri W P Q Q) - tri W Q Q Q := by
  have hR : Continuous (fun x => c * P x - Q x) := (continuous_const.mul hP).sub hQ
  rw [tri_lin_left W hP hQ hR hR, tri_lin_mid W hP hP hQ hR, tri_lin_mid W hQ hP hQ hR,
    tri_lin_right W hP hP hP hQ, tri_lin_right W hP hQ hP hQ, tri_lin_right W hQ hP hP hQ,
    tri_lin_right W hQ hQ hP hQ]
  ring

/-! ### `tri W` with the prime part `Qk` in one slot -/

section slots
variable (w : HeightWeight) {T σ : ℝ}

theorem tri_Qk_left {Y Z : ℝ → ℂ} (hY : Continuous Y) (hZ : Continuous Z) :
    tri W (Qk w.k T σ) Y Z
      = ∑ p ∈ idx T σ, (lamCoeff p.1 : ℂ) * tri W (packet w.k T σ (cen T σ p)) Y Z :=
  (tri_sum_left W (idx T σ) (f := fun p x => (lamCoeff p.1 : ℂ) * packet w.k T σ (cen T σ p) x)
    (fun _ _ => continuous_const.mul (continuous_packet w T σ _)) hY hZ).trans
    (Finset.sum_congr rfl (fun _ _ => tri_smul_left W _ _ _ _))

theorem tri_Qk_mid {X Z : ℝ → ℂ} (hX : Continuous X) (hZ : Continuous Z) :
    tri W X (Qk w.k T σ) Z
      = ∑ p ∈ idx T σ, (lamCoeff p.1 : ℂ) * tri W X (packet w.k T σ (cen T σ p)) Z :=
  (tri_sum_mid W (idx T σ) (f := fun p x => (lamCoeff p.1 : ℂ) * packet w.k T σ (cen T σ p) x)
    (fun _ _ => continuous_const.mul (continuous_packet w T σ _)) hX hZ).trans
    (Finset.sum_congr rfl (fun _ _ => tri_smul_mid W _ _ _ _))

theorem tri_Qk_right {X Y : ℝ → ℂ} (hX : Continuous X) (hY : Continuous Y) :
    tri W X Y (Qk w.k T σ)
      = ∑ p ∈ idx T σ, (lamCoeff p.1 : ℂ) * tri W X Y (packet w.k T σ (cen T σ p)) :=
  (tri_sum_right W (idx T σ) (f := fun p x => (lamCoeff p.1 : ℂ) * packet w.k T σ (cen T σ p) x)
    (fun _ _ => continuous_const.mul (continuous_packet w T σ _)) hX hY).trans
    (Finset.sum_congr rfl (fun _ _ => tri_smul_right W _ _ _ _))

/-! ### one prime packet: the term vanishes -/

theorem tri_Q_P_P (hσ : 0 < σ) (hS : Sep w T σ) :
    tri W (Qk w.k T σ) (packet w.k T σ 0) (packet w.k T σ 0) = 0 := by
  rw [tri_Qk_left W w (continuous_packet w T σ 0) (continuous_packet w T σ 0)]
  refine Finset.sum_eq_zero (fun p hp => ?_)
  rw [tri_packet_eq_zero_log W w hσ hS (a := sgn p.2 * Real.log p.1) (by rw [cen_eq]; ring)
    (single_sep hS (mem_idx.mp hp).1 p.2), mul_zero]

theorem tri_P_Q_P (hσ : 0 < σ) (hS : Sep w T σ) :
    tri W (packet w.k T σ 0) (Qk w.k T σ) (packet w.k T σ 0) = 0 := by
  rw [tri_Qk_mid W w (continuous_packet w T σ 0) (continuous_packet w T σ 0)]
  refine Finset.sum_eq_zero (fun p hp => ?_)
  rw [tri_packet_eq_zero_log W w hσ hS (a := sgn p.2 * Real.log p.1) (by rw [cen_eq]; ring)
    (single_sep hS (mem_idx.mp hp).1 p.2), mul_zero]

theorem tri_P_P_Q (hσ : 0 < σ) (hS : Sep w T σ) :
    tri W (packet w.k T σ 0) (packet w.k T σ 0) (Qk w.k T σ) = 0 := by
  rw [tri_Qk_right W w (continuous_packet w T σ 0) (continuous_packet w T σ 0)]
  refine Finset.sum_eq_zero (fun p hp => ?_)
  rw [tri_packet_eq_zero_log W w hσ hS (a := sgn p.2 * Real.log p.1) (by rw [cen_eq]; ring)
    (single_sep hS (mem_idx.mp hp).1 p.2), mul_zero]

/-! ### two prime packets: reduction to the diagonal -/

theorem tri_Q_Q_P (hσ : 0 < σ) (hS : Sep w T σ) :
    tri W (Qk w.k T σ) (Qk w.k T σ) (packet w.k T σ 0)
      = ∑ p ∈ idx T σ, (lamCoeff p.1 : ℂ) ^ 2 *
          tri W (packet w.k T σ (cen T σ p)) (packet w.k T σ (-(cen T σ p))) (packet w.k T σ 0) := by
  rw [tri_Qk_left W w (continuous_Qk w T σ) (continuous_packet w T σ 0)]
  refine Finset.sum_congr rfl (fun p hp => ?_)
  rw [tri_Qk_mid W w (continuous_packet w T σ _) (continuous_packet w T σ 0),
    Finset.sum_eq_single_of_mem (bar p) (bar_mem hp) (fun q hq hne => by
      rw [tri_packet_eq_zero_log W w hσ hS
        (a := sgn p.2 * Real.log p.1 + sgn q.2 * Real.log q.1)
        (by rw [cen_eq, cen_eq]; ring) (pair_log_lt hS hp hq hne), mul_zero]),
    cen_bar]
  simp only [bar]
  ring

theorem tri_Q_P_Q (hσ : 0 < σ) (hS : Sep w T σ) :
    tri W (Qk w.k T σ) (packet w.k T σ 0) (Qk w.k T σ)
      = ∑ p ∈ idx T σ, (lamCoeff p.1 : ℂ) ^ 2 *
          tri W (packet w.k T σ (cen T σ p)) (packet w.k T σ 0) (packet w.k T σ (-(cen T σ p))) := by
  rw [tri_Qk_left W w (continuous_packet w T σ 0) (continuous_Qk w T σ)]
  refine Finset.sum_congr rfl (fun p hp => ?_)
  rw [tri_Qk_right W w (continuous_packet w T σ _) (continuous_packet w T σ 0),
    Finset.sum_eq_single_of_mem (bar p) (bar_mem hp) (fun q hq hne => by
      rw [tri_packet_eq_zero_log W w hσ hS
        (a := sgn p.2 * Real.log p.1 + sgn q.2 * Real.log q.1)
        (by rw [cen_eq, cen_eq]; ring) (pair_log_lt hS hp hq hne), mul_zero]),
    cen_bar]
  simp only [bar]
  ring

theorem tri_P_Q_Q (hσ : 0 < σ) (hS : Sep w T σ) :
    tri W (packet w.k T σ 0) (Qk w.k T σ) (Qk w.k T σ)
      = ∑ p ∈ idx T σ, (lamCoeff p.1 : ℂ) ^ 2 *
          tri W (packet w.k T σ 0) (packet w.k T σ (cen T σ p)) (packet w.k T σ (-(cen T σ p))) := by
  rw [tri_Qk_mid W w (continuous_packet w T σ 0) (continuous_Qk w T σ)]
  refine Finset.sum_congr rfl (fun p hp => ?_)
  rw [tri_Qk_right W w (continuous_packet w T σ 0) (continuous_packet w T σ _),
    Finset.sum_eq_single_of_mem (bar p) (bar_mem hp) (fun q hq hne => by
      rw [tri_packet_eq_zero_log W w hσ hS
        (a := sgn p.2 * Real.log p.1 + sgn q.2 * Real.log q.1)
        (by rw [cen_eq, cen_eq]; ring) (pair_log_lt hS hp hq hne), mul_zero]),
    cen_bar]
  simp only [bar]
  ring

end slots

/-! ### evaluation of the surviving terms -/

/-- the error of one evaluation, for the tolerance `η` -/
def evErr (w : HeightWeight) (η M T σ : ℝ) : ℝ :=
  |T| ^ 3 / Asc T σ ^ 2 * (η * M * (∫ y, ‖w.k y‖) ^ 2)

/-- the size bound of one packet triple -/
def szB (w : HeightWeight) (M T σ : ℝ) : ℝ :=
  W.bound ^ 2 * T ^ 3 * M * (∫ y, ‖w.k y‖) ^ 2 / Asc T σ ^ 2

/-- `Σ_{2 ≤ n ≤ Nmax} Λ(n)²/n · (bg(λ_n) + bg(-λ_n))` -/
def Bsum (T σ : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 2 (Nmax T σ), Λ n ^ 2 / n * (bg W (lamOf T σ n) + bg W (-(lamOf T σ n)))

section eval
variable (w : HeightWeight) {M T σ η δ' : ℝ}

theorem evErr_nonneg (hη0 : 0 ≤ η) (hM0 : 0 ≤ M) (hA : 0 < Asc T σ) : 0 ≤ evErr w η M T σ := by
  unfold evErr
  positivity

theorem eval_000 (hM : ∀ y, ‖w.k y‖ ≤ M) (hA : 0 < Asc T σ)
    (hG : ∀ r s d e : ℝ, |d| ≤ δ' → |e| ≤ δ' → |Gg W (r + d) (s + e) - Gg W r s| ≤ η)
    (hκδ : w.kappa / Asc T σ ≤ δ') :
    ‖tri W (packet w.k T σ 0) (packet w.k T σ 0) (packet w.k T σ 0)
        - ((M3 T σ * (I3 W * kt w) : ℝ) : ℂ)‖ ≤ evErr w η M T σ :=
  tri_packet_eval W w hM hA hG hκδ (l1 := 0) (l2 := 0) (l3 := 0) (by ring)

theorem eval_12 (hM : ∀ y, ‖w.k y‖ ≤ M) (hA : 0 < Asc T σ)
    (hG : ∀ r s d e : ℝ, |d| ≤ δ' → |e| ≤ δ' → |Gg W (r + d) (s + e) - Gg W r s| ≤ η)
    (hκδ : w.kappa / Asc T σ ≤ δ') (l : ℝ) :
    ‖tri W (packet w.k T σ l) (packet w.k T σ (-l)) (packet w.k T σ 0)
        - ((M3 T σ * (bg W l * kt w) : ℝ) : ℂ)‖ ≤ evErr w η M T σ := by
  have h := tri_packet_eval W w hM hA hG hκδ (l1 := l) (l2 := -l) (l3 := 0) (by ring)
  rw [Gg_neg] at h
  exact h

theorem eval_13 (hM : ∀ y, ‖w.k y‖ ≤ M) (hA : 0 < Asc T σ)
    (hG : ∀ r s d e : ℝ, |d| ≤ δ' → |e| ≤ δ' → |Gg W (r + d) (s + e) - Gg W r s| ≤ η)
    (hκδ : w.kappa / Asc T σ ≤ δ') (l : ℝ) :
    ‖tri W (packet w.k T σ l) (packet w.k T σ 0) (packet w.k T σ (-l))
        - ((M3 T σ * (bg W (-l) * kt w) : ℝ) : ℂ)‖ ≤ evErr w η M T σ := by
  have h := tri_packet_eval W w hM hA hG hκδ (l1 := l) (l2 := 0) (l3 := -l) (by ring)
  rw [Gg_right_zero] at h
  exact h

theorem eval_23 (hM : ∀ y, ‖w.k y‖ ≤ M) (hA : 0 < Asc T σ)
    (hG : ∀ r s d e : ℝ, |d| ≤ δ' → |e| ≤ δ' → |Gg W (r + d) (s + e) - Gg W r s| ≤ η)
    (hκδ : w.kappa / Asc T σ ≤ δ') (l : ℝ) :
    ‖tri W (packet w.k T σ 0) (packet w.k T σ l) (packet w.k T σ (-l))
        - ((M3 T σ * (bg W l * kt w) : ℝ) : ℂ)‖ ≤ evErr w η M T σ :=
  tri_packet_eval W w hM hA hG hκδ (l1 := 0) (l2 := l) (l3 := -l) (by ring)

/-- the three terms with two prime packets -/
theorem two_Q_eval (hM : ∀ y, ‖w.k y‖ ≤ M) (hσ : 0 < σ) (hS : Sep w T σ)
    (hG : ∀ r s d e : ℝ, |d| ≤ δ' → |e| ≤ δ' → |Gg W (r + d) (s + e) - Gg W r s| ≤ η)
    (hκδ : w.kappa / Asc T σ ≤ δ') :
    ‖(tri W (Qk w.k T σ) (Qk w.k T σ) (packet w.k T σ 0)
        + tri W (Qk w.k T σ) (packet w.k T σ 0) (Qk w.k T σ)
        + tri W (packet w.k T σ 0) (Qk w.k T σ) (Qk w.k T σ))
        - ((3 * (M3 T σ * kt w) * Bsum W T σ : ℝ) : ℂ)‖ ≤ 6 * evErr w η M T σ * SLam T σ := by
  have hA := hS.A_pos
  -- the main term as a sum over the signed index set
  have hid : 3 * (M3 T σ * kt w) * Bsum W T σ
      = ∑ p ∈ idx T σ, lamCoeff p.1 ^ 2 *
          (M3 T σ * (bg W (cen T σ p) * kt w) + M3 T σ * (bg W (-(cen T σ p)) * kt w)
            + M3 T σ * (bg W (cen T σ p) * kt w)) := by
    unfold Bsum
    rw [sum_idx, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun n _ => ?_)
    simp only [cen, sgn_true, sgn_false, one_mul, neg_mul, neg_neg]
    rw [lamCoeff_sq]
    ring
  rw [hid, tri_Q_Q_P W w hσ hS, tri_Q_P_Q W w hσ hS, tri_P_Q_Q W w hσ hS, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]
  push_cast
  rw [← Finset.sum_sub_distrib]
  have hterm : ∀ p ∈ idx T σ,
      ‖(lamCoeff p.1 : ℂ) ^ 2 *
            tri W (packet w.k T σ (cen T σ p)) (packet w.k T σ (-(cen T σ p))) (packet w.k T σ 0)
          + (lamCoeff p.1 : ℂ) ^ 2 *
            tri W (packet w.k T σ (cen T σ p)) (packet w.k T σ 0) (packet w.k T σ (-(cen T σ p)))
          + (lamCoeff p.1 : ℂ) ^ 2 *
            tri W (packet w.k T σ 0) (packet w.k T σ (cen T σ p)) (packet w.k T σ (-(cen T σ p)))
          - (lamCoeff p.1 : ℂ) ^ 2 *
            ((M3 T σ : ℂ) * ((bg W (cen T σ p) : ℂ) * (kt w : ℂ))
              + (M3 T σ : ℂ) * ((bg W (-(cen T σ p)) : ℂ) * (kt w : ℂ))
              + (M3 T σ : ℂ) * ((bg W (cen T σ p) : ℂ) * (kt w : ℂ)))‖
        ≤ lamCoeff p.1 ^ 2 * (3 * evErr w η M T σ) := by
    intro p _
    have h1 := eval_12 W w hM hA hG hκδ (cen T σ p)
    have h2 := eval_13 W w hM hA hG hκδ (cen T σ p)
    have h3 := eval_23 W w hM hA hG hκδ (cen T σ p)
    push_cast at h1 h2 h3
    have e : (lamCoeff p.1 : ℂ) ^ 2 *
            tri W (packet w.k T σ (cen T σ p)) (packet w.k T σ (-(cen T σ p))) (packet w.k T σ 0)
          + (lamCoeff p.1 : ℂ) ^ 2 *
            tri W (packet w.k T σ (cen T σ p)) (packet w.k T σ 0) (packet w.k T σ (-(cen T σ p)))
          + (lamCoeff p.1 : ℂ) ^ 2 *
            tri W (packet w.k T σ 0) (packet w.k T σ (cen T σ p)) (packet w.k T σ (-(cen T σ p)))
          - (lamCoeff p.1 : ℂ) ^ 2 *
            ((M3 T σ : ℂ) * ((bg W (cen T σ p) : ℂ) * (kt w : ℂ))
              + (M3 T σ : ℂ) * ((bg W (-(cen T σ p)) : ℂ) * (kt w : ℂ))
              + (M3 T σ : ℂ) * ((bg W (cen T σ p) : ℂ) * (kt w : ℂ)))
        = (lamCoeff p.1 : ℂ) ^ 2 *
          ((tri W (packet w.k T σ (cen T σ p)) (packet w.k T σ (-(cen T σ p))) (packet w.k T σ 0)
              - (M3 T σ : ℂ) * ((bg W (cen T σ p) : ℂ) * (kt w : ℂ)))
            + (tri W (packet w.k T σ (cen T σ p)) (packet w.k T σ 0) (packet w.k T σ (-(cen T σ p)))
              - (M3 T σ : ℂ) * ((bg W (-(cen T σ p)) : ℂ) * (kt w : ℂ)))
            + (tri W (packet w.k T σ 0) (packet w.k T σ (cen T σ p)) (packet w.k T σ (-(cen T σ p)))
              - (M3 T σ : ℂ) * ((bg W (cen T σ p) : ℂ) * (kt w : ℂ)))) := by
      ring
    rw [e, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
    exact norm_add₃_le.trans (by linarith)
  calc _ ≤ ∑ p ∈ idx T σ, lamCoeff p.1 ^ 2 * (3 * evErr w η M T σ) :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum hterm)
    _ = 6 * evErr w η M T σ * SLam T σ := by
        rw [← Finset.sum_mul, sum_idx_lamCoeff_sq]
        unfold SLam
        ring

end eval

/-! ### three prime packets -/

section three
variable (w : HeightWeight) {M T σ : ℝ}

theorem szB_nonneg (hM0 : 0 ≤ M) (hT : 0 ≤ T) : 0 ≤ szB W w M T σ := by
  unfold szB
  positivity

/-- a triple of prime packets vanishes unless one of the three product relations holds -/
theorem norm_tri_cen_le (hM : ∀ y, ‖w.k y‖ ≤ M) (hσ : 0 < σ) (hS : Sep w T σ) {p q r : ℕ × Bool}
    (hp : p ∈ idx T σ) (hq : q ∈ idx T σ) (hr : r ∈ idx T σ) :
    ‖tri W (packet w.k T σ (cen T σ p)) (packet w.k T σ (cen T σ q)) (packet w.k T σ (cen T σ r))‖
      ≤ szB W w M T σ * ((if p.1 * q.1 = r.1 then (1 : ℝ) else 0) + (if p.1 * r.1 = q.1 then 1 else 0)
          + (if q.1 * r.1 = p.1 then 1 else 0)) := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  have hsz : 0 ≤ szB W w M T σ := szB_nonneg W w hM0 hS.T_pos.le
  have hsize := norm_tri_packet_le W w hM hS.T_pos.le hS.A_pos (cen T σ p) (cen T σ q) (cen T σ r)
  have i1 : (0 : ℝ) ≤ (if p.1 * q.1 = r.1 then (1 : ℝ) else 0) := by split_ifs <;> norm_num
  have i2 : (0 : ℝ) ≤ (if p.1 * r.1 = q.1 then (1 : ℝ) else 0) := by split_ifs <;> norm_num
  have i3 : (0 : ℝ) ≤ (if q.1 * r.1 = p.1 then (1 : ℝ) else 0) := by split_ifs <;> norm_num
  by_cases h : p.1 * q.1 = r.1 ∨ p.1 * r.1 = q.1 ∨ q.1 * r.1 = p.1
  · have hone : (1 : ℝ) ≤ (if p.1 * q.1 = r.1 then (1 : ℝ) else 0)
        + (if p.1 * r.1 = q.1 then 1 else 0) + (if q.1 * r.1 = p.1 then 1 else 0) := by
      rcases h with h | h | h
      · rw [if_pos h]
        linarith
      · rw [if_pos h]
        linarith
      · rw [if_pos h]
        linarith
    calc _ ≤ szB W w M T σ := hsize
      _ = szB W w M T σ * 1 := (mul_one _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left hone hsz
  · have hlog : 3 * w.kappa / T
        < |sgn p.2 * Real.log p.1 + sgn q.2 * Real.log q.1 + sgn r.2 * Real.log r.1| := by
      by_contra hc
      rw [mem_idx] at hp hq hr
      exact h (triple_cases hS hp.1 hp.2 hq.1 hq.2 hr.1 hr.2 p.2 q.2 r.2 (not_lt.mp hc))
    rw [tri_packet_eq_zero_log W w hσ hS
      (a := sgn p.2 * Real.log p.1 + sgn q.2 * Real.log q.1 + sgn r.2 * Real.log r.1)
      (by rw [cen_eq, cen_eq, cen_eq]; ring) hlog, norm_zero]
    exact mul_nonneg hsz (by linarith)

theorem tri_Q_Q_Q_expand :
    tri W (Qk w.k T σ) (Qk w.k T σ) (Qk w.k T σ)
      = ∑ p ∈ idx T σ, ∑ q ∈ idx T σ, ∑ r ∈ idx T σ,
          ((lamCoeff p.1 : ℂ) * (lamCoeff q.1 : ℂ) * (lamCoeff r.1 : ℂ)) *
            tri W (packet w.k T σ (cen T σ p)) (packet w.k T σ (cen T σ q))
              (packet w.k T σ (cen T σ r)) := by
  rw [tri_Qk_left W w (continuous_Qk w T σ) (continuous_Qk w T σ)]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [tri_Qk_mid W w (continuous_packet w T σ _) (continuous_Qk w T σ), Finset.mul_sum]
  refine Finset.sum_congr rfl (fun q _ => ?_)
  rw [tri_Qk_right W w (continuous_packet w T σ _) (continuous_packet w T σ _), Finset.mul_sum,
    Finset.mul_sum]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  ring

end three

/-- **Three prime packets.** -/
theorem QQQ_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (w : HeightWeight) (M T σ : ℝ), (∀ y, ‖w.k y‖ ≤ M) → 0 < σ → Sep w T σ →
      ‖tri W (Qk w.k T σ) (Qk w.k T σ) (Qk w.k T σ)‖ ≤ C * szB W w M T σ := by
  obtain ⟨Ctp, hCtp⟩ := triplePrime_bound
  have hCtp0 : 0 ≤ Ctp := by
    have := hCtp 0
    simpa using this
  refine ⟨24 * Ctp, by positivity, fun w M T σ hM hσ hS => ?_⟩
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  have hsz : 0 ≤ szB W w M T σ := szB_nonneg W w hM0 hS.T_pos.le
  set s : Finset ℕ := Finset.Icc 2 (Nmax T σ) with hs
  -- the function of the three integers
  set g : ℕ → ℕ → ℕ → ℝ := fun a b c => lamCoeff a * lamCoeff b * lamCoeff c *
      ((if a * b = c then (1 : ℝ) else 0) + (if a * c = b then 1 else 0)
        + (if b * c = a then 1 else 0)) with hg
  have hstep1 : ‖tri W (Qk w.k T σ) (Qk w.k T σ) (Qk w.k T σ)‖
      ≤ ∑ p ∈ idx T σ, ∑ q ∈ idx T σ, ∑ r ∈ idx T σ, szB W w M T σ * g p.1 q.1 r.1 := by
    rw [tri_Q_Q_Q_expand]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun p hp => ?_))
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun q hq => ?_))
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun r hr => ?_))
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (lamCoeff_nonneg _),
      abs_of_nonneg (lamCoeff_nonneg _), abs_of_nonneg (lamCoeff_nonneg _)]
    have h1 := norm_tri_cen_le W w hM hσ hS hp hq hr
    have h2 : 0 ≤ lamCoeff p.1 * lamCoeff q.1 * lamCoeff r.1 :=
      mul_nonneg (mul_nonneg (lamCoeff_nonneg _) (lamCoeff_nonneg _)) (lamCoeff_nonneg _)
    calc lamCoeff p.1 * lamCoeff q.1 * lamCoeff r.1 *
          ‖tri W (packet w.k T σ (cen T σ p)) (packet w.k T σ (cen T σ q))
            (packet w.k T σ (cen T σ r))‖
        ≤ lamCoeff p.1 * lamCoeff q.1 * lamCoeff r.1 * (szB W w M T σ *
            ((if p.1 * q.1 = r.1 then (1 : ℝ) else 0) + (if p.1 * r.1 = q.1 then 1 else 0)
              + (if q.1 * r.1 = p.1 then 1 else 0))) := mul_le_mul_of_nonneg_left h1 h2
      _ = szB W w M T σ * g p.1 q.1 r.1 := by
          simp only [hg]
          ring
  have e1 : ∀ a b : ℕ, ∑ r ∈ idx T σ, szB W w M T σ * g a b r.1
      = 2 * ∑ c ∈ s, szB W w M T σ * g a b c := fun a b =>
    sum_idx_fst T σ (fun c => szB W w M T σ * g a b c)
  have e2 : ∀ a : ℕ, ∑ q ∈ idx T σ, ∑ r ∈ idx T σ, szB W w M T σ * g a q.1 r.1
      = 2 * ∑ b ∈ s, 2 * ∑ c ∈ s, szB W w M T σ * g a b c := by
    intro a
    simp_rw [e1]
    exact sum_idx_fst T σ (fun b => 2 * ∑ c ∈ s, szB W w M T σ * g a b c)
  have e3 : ∑ p ∈ idx T σ, ∑ q ∈ idx T σ, ∑ r ∈ idx T σ, szB W w M T σ * g p.1 q.1 r.1
      = 2 * ∑ a ∈ s, 2 * ∑ b ∈ s, 2 * ∑ c ∈ s, szB W w M T σ * g a b c := by
    simp_rw [e2]
    exact sum_idx_fst T σ (fun a => 2 * ∑ b ∈ s, 2 * ∑ c ∈ s, szB W w M T σ * g a b c)
  have e4 : 2 * ∑ a ∈ s, 2 * ∑ b ∈ s, 2 * ∑ c ∈ s, szB W w M T σ * g a b c
      = 8 * szB W w M T σ * ∑ a ∈ s, ∑ b ∈ s, ∑ c ∈ s, g a b c := by
    simp only [← Finset.mul_sum]
    ring
  have h5 := triple_delta_sum_le s
  have h6 : ∑ a ∈ s, ∑ b ∈ s, lamCoeff a * lamCoeff b * lamCoeff (a * b) ≤ Ctp := by
    have := hCtp (Nmax T σ)
    simp only [lamCoeff_triple]
    exact this
  have h7 : ∑ a ∈ s, ∑ b ∈ s, ∑ c ∈ s, g a b c ≤ 3 * Ctp := h5.trans (by linarith)
  calc ‖tri W (Qk w.k T σ) (Qk w.k T σ) (Qk w.k T σ)‖
      ≤ 8 * szB W w M T σ * ∑ a ∈ s, ∑ b ∈ s, ∑ c ∈ s, g a b c := by
        rw [← e4, ← e3]
        exact hstep1
    _ ≤ 8 * szB W w M T σ * (3 * Ctp) := mul_le_mul_of_nonneg_left h7 (by positivity)
    _ = 24 * Ctp * szB W w M T σ := by ring

end TMG.T3
end
end Src_TMG_Trace3Aux3

section Src_TMG_Trace3Aux4
/-
Written for Kristian Muri Knausgård, drafted with Claude (Anthropic), 22 November 2026.

TMG/Trace3Aux4.lean — the main term of the third trace for a general window
(generalisation of TMA/Trace3Aux5.lean):
* the prime sum `Bsum W` by `TMG.primeSum_tendsto` (the function `r ↦ bg W r + bg W (-r)` is only continuous, so
  there is no rate: the error is `η (σ log T)²` for `T^σ` large);
* `Re t3 W K0 ≤ C₃(σ) (∫h³) D + c η T log T + C T` for every tolerance `η > 0` and `T ≥ T₀(η)`, with `c`, `C`
  independent of `η` (the evaluation of the packet triples uses `TMG.Gg_unifCont` instead of a Lipschitz bound).
See BLUEPRINT.md, module "T3" (main term, total) and section "General windows (TMG)".
-/

open MeasureTheory Complex
open scoped BigOperators ArithmeticFunction Real

noncomputable section
namespace TMG.T3
open TMA TMA.T3

variable (W : Window)

/-- `Σ_{2 ≤ n ≤ Nmax} Λ(n)²/n (bg(λ_n) + bg(-λ_n)) ≤ (σ log T)² (J3 + η)` once `T^σ ≥ X₀(η)` -/
theorem Bsum_le {σ : ℝ} (hσ : 0 < σ) :
    ∀ η > 0, ∃ X₀ : ℝ, ∀ (w : HeightWeight) (T : ℝ), Sep w T σ → X₀ ≤ T ^ σ →
      Bsum W T σ ≤ (σ * Real.log T) ^ 2 * J3 W + η * (σ * Real.log T) ^ 2 := by
  intro η hη
  have hFc : ContinuousOn (fun r : ℝ => bg W r + bg W (-r)) (Set.Icc 0 1) :=
    ((continuous_bg W).add ((continuous_bg W).comp continuous_neg)).continuousOn
  obtain ⟨X₀, hX₀⟩ := primeSum_tendsto (fun r : ℝ => bg W r + bg W (-r)) hFc η hη
  refine ⟨X₀, fun w T hS hX => ?_⟩
  have hT := hS.T_pos
  have hL := hS.log_pos
  have hσL : 0 < σ * Real.log T := mul_pos hσ hL
  have hlogX : Real.log (T ^ σ) = σ * Real.log T := Real.log_rpow hT σ
  have hXpos : (0 : ℝ) < T ^ σ := Real.rpow_pos_of_pos hT σ
  have h1 : |∑ n ∈ Finset.Icc 2 ⌊T ^ σ⌋₊,
          Λ n ^ 2 / n * (bg W (lamOf T σ n) + bg W (-(lamOf T σ n)))
        - (σ * Real.log T) ^ 2 * J3 W| ≤ η * (σ * Real.log T) ^ 2 := by
    have h := hX₀ (T ^ σ) hX
    rw [hlogX] at h
    exact h
  have hsum : ∑ n ∈ Finset.Icc 2 ⌊T ^ σ⌋₊,
        Λ n ^ 2 / n * (bg W (lamOf T σ n) + bg W (-(lamOf T σ n))) = Bsum W T σ := by
    unfold Bsum
    apply Finset.sum_subset
    · apply Finset.Icc_subset_Icc_right
      unfold Nmax
      exact Nat.floor_le_floor (by linarith)
    · intro n hn hn'
      rw [Finset.mem_Icc] at hn hn'
      have hlt : ⌊T ^ σ⌋₊ < n := by
        by_contra hc
        exact hn' ⟨hn.1, not_lt.mp hc⟩
      have hXn : T ^ σ < n := Nat.lt_of_floor_lt hlt
      have hlam : 1 < lamOf T σ n := by
        unfold lamOf
        rw [one_lt_div hσL, ← hlogX]
        exact Real.log_lt_log hXpos hXn
      have hb1 : bg W (lamOf T σ n) = 0 := by
        unfold bg
        apply Gg_eq_zero
        right; left
        exact lt_of_lt_of_le hlam (le_abs_self _)
      have hb2 : bg W (-(lamOf T σ n)) = 0 := by
        unfold bg
        apply Gg_eq_zero
        right; left
        rw [abs_neg]
        exact lt_of_lt_of_le hlam (le_abs_self _)
      rw [hb1, hb2]
      ring
  rw [hsum] at h1
  have h2 := (abs_le.mp h1).2
  linarith

/-- **Main term.** `Re t3 W K0 ≤ C₃(σ) (∫h³) D + c η T log T + C T` for `T ≥ T₀(η)`; the constants `c`, `C`
do not depend on the tolerance `η`. -/
theorem t3_K0_upper (w : HeightWeight) {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ < 1) :
    ∃ c C : ℝ, 0 ≤ c ∧ 0 ≤ C ∧ ∀ η > 0, ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T → Sep w T σ →
      (t3 W (K0 w.k T σ)).re
        ≤ C3 W σ * w.kap3 * Dsc T + c * η * (T * Real.log T) + C * T := by
  obtain ⟨M, hM0, hM⟩ := w.exists_k_bound
  obtain ⟨CQ, hCQ0, hCQ⟩ := QQQ_bound W
  obtain ⟨Cu, hCu0, hCu⟩ := primeSum_Nmax_le hσ hσ1
  set Ik : ℝ := ∫ y, ‖w.k y‖ with hIk
  have hIk0 : 0 ≤ Ik := integral_norm_k_nonneg w
  have hκ := w.kappa_pos
  have hkt := kt_nonneg w
  have hI3 : 0 ≤ I3 W := I3_nonneg W
  have hJ3 : 0 ≤ J3 W := J3_nonneg W
  have hb2 : 0 < W.bound ^ 2 := bound_sq_pos W
  set c1 : ℝ := M * Ik ^ 2 / σ ^ 2 with hc1
  have hc10 : 0 ≤ c1 := by positivity
  refine ⟨c1 + 6 * c1 * Cu + 3 * kt w, W.bound ^ 2 * CQ * M * Ik ^ 2 / σ ^ 2, by positivity,
    by positivity, fun η hη' => ?_⟩
  have hη : 0 < η := hη'
  obtain ⟨δ', hδ', hG⟩ := Gg_unifCont W η hη
  obtain ⟨X₀, hBs⟩ := Bsum_le W hσ η hη
  refine ⟨max ((max X₀ 1) ^ (1 / σ)) (w.kappa / (σ * δ')), fun T hTge hS => ?_⟩
  have hTa : (max X₀ 1) ^ (1 / σ) ≤ T := (le_max_left _ _).trans hTge
  have hTb : w.kappa / (σ * δ') ≤ T := (le_max_right _ _).trans hTge
  have hm0 : (0 : ℝ) ≤ max X₀ 1 := zero_le_one.trans (le_max_right _ _)
  -- `T^σ ≥ X₀`
  have hX : X₀ ≤ T ^ σ := by
    have h := Real.rpow_le_rpow (Real.rpow_nonneg hm0 _) hTa hσ.le
    rw [← Real.rpow_mul hm0, one_div, inv_mul_cancel₀ hσ.ne', Real.rpow_one] at h
    exact (le_max_left _ _).trans h
  have hT := hS.T_pos
  have hT1 : 1 ≤ T := by linarith [hS.six_le]
  have hL1 := hS.one_le_log
  have hL := hS.log_pos
  have hA := hS.A_pos
  -- `κ/A ≤ δ'`
  have hκδ : w.kappa / Asc T σ ≤ δ' := by
    have hA1 : T * σ ≤ Asc T σ := by
      unfold Asc
      have h1 : T * σ * 1 ≤ T * σ * Real.log T :=
        mul_le_mul_of_nonneg_left hL1 (mul_nonneg hT.le hσ.le)
      linarith
    rw [div_le_iff₀ hA]
    rw [div_le_iff₀ (mul_pos hσ hδ')] at hTb
    calc w.kappa ≤ T * (σ * δ') := hTb
      _ = δ' * (T * σ) := by ring
      _ ≤ δ' * Asc T σ := mul_le_mul_of_nonneg_left hA1 hδ'.le
  have hell0 : 0 ≤ Real.log (T / (2 * π)) := hS.ell_nonneg
  have hellL : Real.log (T / (2 * π)) ≤ Real.log T := hS.ell_le
  set L : ℝ := Real.log T with hLdef
  set ell : ℝ := Real.log (T / (2 * π)) with hell
  -- values of the scale factors
  have hAval : Asc T σ = T * (σ * L) := rfl
  have hM3 : M3 T σ = T / (σ ^ 2 * L ^ 2) := by
    unfold M3
    rw [hAval]
    field_simp
  have hev : evErr w η M T σ = η * c1 * T / L ^ 2 := by
    unfold evErr
    rw [hAval, abs_of_pos hT, hc1, ← hIk]
    field_simp
  have hsz : szB W w M T σ = W.bound ^ 2 * T * M * Ik ^ 2 / (σ ^ 2 * L ^ 2) := by
    unfold szB
    rw [hAval, ← hIk]
    field_simp
  have hM30 : 0 ≤ M3 T σ := by
    rw [hM3]
    positivity
  have hev0 : 0 ≤ evErr w η M T σ := evErr_nonneg w hη.le hM0 hA
  -- the expansion
  set P0 : ℝ → ℂ := packet w.k T σ 0 with hP0
  set Q : ℝ → ℂ := Qk w.k T σ with hQ
  have hexp : t3 W (K0 w.k T σ)
      = (ell : ℂ) ^ 3 * tri W P0 P0 P0
        + (ell : ℂ) * (tri W Q Q P0 + tri W Q P0 Q + tri W P0 Q Q) - tri W Q Q Q := by
    rw [t3_eq_tri, K0_eq, tri_expand W (continuous_packet w T σ 0) (continuous_Qk w T σ),
      tri_Q_P_P W w hσ hS, tri_P_Q_P W w hσ hS, tri_P_P_Q W w hσ hS]
    ring
  have hre : (t3 W (K0 w.k T σ)).re
      = ell ^ 3 * (tri W P0 P0 P0).re + ell * (tri W Q Q P0 + tri W Q P0 Q + tri W P0 Q Q).re
        - (tri W Q Q Q).re := by
    rw [hexp]
    simp only [Complex.sub_re, Complex.add_re, ← Complex.ofReal_pow, Complex.re_ofReal_mul]
  -- the three bounds
  have hb000 : (tri W P0 P0 P0).re ≤ M3 T σ * (I3 W * kt w) + evErr w η M T σ :=
    re_le_of_norm_sub_le (eval_000 W w hM hA hG hκδ)
  have hb2Q : (tri W Q Q P0 + tri W Q P0 Q + tri W P0 Q Q).re
      ≤ 3 * (M3 T σ * kt w) * Bsum W T σ + 6 * evErr w η M T σ * SLam T σ :=
    re_le_of_norm_sub_le (two_Q_eval W w hM hσ hS hG hκδ)
  have hb3 : -(tri W Q Q Q).re ≤ CQ * szB W w M T σ := by
    have h1 := Complex.abs_re_le_norm (tri W Q Q Q)
    have h2 := hCQ w M T σ hM hσ hS
    have h3 := neg_abs_le (tri W Q Q Q).re
    linarith
  have hBsum : Bsum W T σ ≤ (σ * L) ^ 2 * J3 W + η * (σ * L) ^ 2 := hBs w T hS hX
  have hSL : SLam T σ ≤ Cu * L ^ 2 := hCu w T hS
  -- step 1: three central packets
  have hstep1 : ell ^ 3 * (tri W P0 P0 P0).re
      ≤ T * L * I3 W * kt w / σ ^ 2 + c1 * η * (T * L) := by
    have hnn : 0 ≤ M3 T σ * (I3 W * kt w) + evErr w η M T σ := by positivity
    have hpow : ell ^ 3 ≤ L ^ 3 := pow_le_pow_left₀ hell0 hellL 3
    calc ell ^ 3 * (tri W P0 P0 P0).re
        ≤ ell ^ 3 * (M3 T σ * (I3 W * kt w) + evErr w η M T σ) :=
          mul_le_mul_of_nonneg_left hb000 (by positivity)
      _ ≤ L ^ 3 * (M3 T σ * (I3 W * kt w) + evErr w η M T σ) :=
          mul_le_mul_of_nonneg_right hpow hnn
      _ = T * L * I3 W * kt w / σ ^ 2 + c1 * η * (T * L) := by
          rw [hM3, hev]
          field_simp
  -- step 2: one central packet
  have hstep2 : ell * (tri W Q Q P0 + tri W Q P0 Q + tri W P0 Q Q).re
      ≤ 3 * T * L * kt w * J3 W + 3 * kt w * η * (T * L) + 6 * c1 * Cu * η * (T * L) := by
    set R2 : ℝ := 3 * (M3 T σ * kt w) * ((σ * L) ^ 2 * J3 W + η * (σ * L) ^ 2)
      + 6 * evErr w η M T σ * (Cu * L ^ 2) with hR2
    have hR20 : 0 ≤ R2 := by positivity
    have h1 : (tri W Q Q P0 + tri W Q P0 Q + tri W P0 Q Q).re ≤ R2 := by
      have h2 : 3 * (M3 T σ * kt w) * Bsum W T σ
          ≤ 3 * (M3 T σ * kt w) * ((σ * L) ^ 2 * J3 W + η * (σ * L) ^ 2) :=
        mul_le_mul_of_nonneg_left hBsum (by positivity)
      have h3 : 6 * evErr w η M T σ * SLam T σ ≤ 6 * evErr w η M T σ * (Cu * L ^ 2) :=
        mul_le_mul_of_nonneg_left hSL (by positivity)
      linarith
    calc ell * (tri W Q Q P0 + tri W Q P0 Q + tri W P0 Q Q).re ≤ ell * R2 :=
          mul_le_mul_of_nonneg_left h1 hell0
      _ ≤ L * R2 := mul_le_mul_of_nonneg_right hellL hR20
      _ = 3 * T * L * kt w * J3 W + 3 * kt w * η * (T * L) + 6 * c1 * Cu * η * (T * L) := by
          rw [hR2, hM3, hev]
          field_simp
  -- step 3: no central packet
  have hstep3 : -(tri W Q Q Q).re ≤ W.bound ^ 2 * CQ * M * Ik ^ 2 / σ ^ 2 * T := by
    have h1 : CQ * szB W w M T σ = W.bound ^ 2 * CQ * M * Ik ^ 2 / σ ^ 2 * T / L ^ 2 := by
      rw [hsz]
      field_simp
    have h2 : W.bound ^ 2 * CQ * M * Ik ^ 2 / σ ^ 2 * T / L ^ 2
        ≤ W.bound ^ 2 * CQ * M * Ik ^ 2 / σ ^ 2 * T := by
      apply div_le_self (by positivity)
      exact one_le_pow₀ hL1
    linarith
  -- total
  have hmain : T * L * I3 W * kt w / σ ^ 2 + 3 * T * L * kt w * J3 W = C3 W σ * w.kap3 * Dsc T := by
    unfold C3 Dsc kt
    rw [← hLdef]
    field_simp
  rw [hre]
  calc ell ^ 3 * (tri W P0 P0 P0).re + ell * (tri W Q Q P0 + tri W Q P0 Q + tri W P0 Q Q).re
        - (tri W Q Q Q).re
      ≤ (T * L * I3 W * kt w / σ ^ 2 + c1 * η * (T * L))
        + (3 * T * L * kt w * J3 W + 3 * kt w * η * (T * L) + 6 * c1 * Cu * η * (T * L))
        + W.bound ^ 2 * CQ * M * Ik ^ 2 / σ ^ 2 * T := by linarith
    _ = C3 W σ * w.kap3 * Dsc T + (c1 + 6 * c1 * Cu + 3 * kt w) * η * (T * L)
        + W.bound ^ 2 * CQ * M * Ik ^ 2 / σ ^ 2 * T := by
        rw [← hmain]
        ring

end TMG.T3
end
end Src_TMG_Trace3Aux4

section Src_TMG_Trace3
/-
Written for Kristian Muri Knausgård, drafted with Claude (Anthropic), 22 November 2026.
TMG/Trace3.lean — the third trace for a general window (generalisation of TMA/Trace3*.lean):
`Re t3 W (K) ≤ (C₃(σ) ∫h³ + δ) D`.
See BLUEPRINT.md, module "T3" and section "General windows (TMG)".  The proof is split over the auxiliary files
* `TMG/Trace3Aux1.lean`: the trilinear form `tri W` (`t3 W K = tri W K K K`), trilinearity, the three bounds;
* `TMG/Trace3Aux2.lean`: packet triples (closure, size, evaluation by uniform continuity of `Gg W`), the error
  term `t3_error`;
* `TMG/Trace3Aux3.lean`: classification of the packet triples of `t3 W K0`;
* `TMG/Trace3Aux4.lean`: the prime sum by `TMG.primeSum_tendsto` and the main term `t3_K0_upper`.
The window-independent lemmas (structure of `K0`, separation, `∫‖K0‖² ≤ C T log T`, ...) are those of `TMA.T3`
(`TMA/Trace3Aux1.lean` ... `TMA/Trace3Aux5.lean`).

Differences from the quadratic window: `Gg W ≤ W.bound²` instead of `≤ 2`; no Lipschitz bound for `Gg W` and no
smoothness of `bg W`, so the main term is `Re t3 W K0 ≤ C₃(σ) (∫h³) D + c η T log T + C T` for every tolerance
`η > 0` and `T ≥ T₀(η)`, with `c`, `C` independent of `η`; given `δ`, take `η = δ / (4π (c + 1))`, then `T` large.
-/

open MeasureTheory Complex
open scoped BigOperators ArithmeticFunction Real

noncomputable section
namespace TMG

theorem t3_upper (hRH : RiemannHypothesis) (W : Window) (w : TMA.HeightWeight) {σ : ℝ} (hσ : 0 < σ)
    (hσ1 : σ < 1) :
    ∀ δ > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (t3 W (TMA.Kfull w.h T σ)).re ≤ (C3 W σ * w.kap3 + δ) * TMA.Dsc T := by
  intro δ hδ
  have hπ := Real.pi_pos
  obtain ⟨T1, hSep⟩ := TMA.T3.sep_eventually w hσ hσ1
  obtain ⟨CE, T2, hErr⟩ := TMG.T3.t3_error W hRH w hσ hσ1
  obtain ⟨c, C0, hc0, hC00, hK0⟩ := TMG.T3.t3_K0_upper W w hσ hσ1
  -- the tolerance: `c η T log T ≤ (δ/2) D`
  set η : ℝ := δ / (4 * π * (c + 1)) with hηdef
  have hη : 0 < η := by positivity
  obtain ⟨T3, hK0η⟩ := hK0 η hη
  set Ct : ℝ := C0 + |CE| with hCt
  refine ⟨max (max T1 T2) (max T3 (Real.exp (4 * π * Ct / δ))), fun T hT => ?_⟩
  have hT1 : T1 ≤ T := (le_max_left _ _).trans ((le_max_left _ _).trans hT)
  have hT2 : T2 ≤ T := (le_max_right _ _).trans ((le_max_left _ _).trans hT)
  have hT3 : T3 ≤ T := (le_max_left _ _).trans ((le_max_right _ _).trans hT)
  have hT4 : Real.exp (4 * π * Ct / δ) ≤ T := (le_max_right _ _).trans ((le_max_right _ _).trans hT)
  have hS := hSep T hT1
  have hTpos := hS.T_pos
  have hLpos := hS.log_pos
  have h1 := hK0η T hT3 hS
  have h2 := hErr T hT2
  -- main term plus error term
  have h3 : (t3 W (TMA.Kfull w.h T σ)).re
      ≤ (t3 W (TMA.K0 w.k T σ)).re + ‖t3 W (TMA.Kfull w.h T σ) - t3 W (TMA.K0 w.k T σ)‖ := by
    have e : (t3 W (TMA.Kfull w.h T σ)).re
        = (t3 W (TMA.K0 w.k T σ)).re + (t3 W (TMA.Kfull w.h T σ) - t3 W (TMA.K0 w.k T σ)).re := by
      rw [Complex.sub_re]
      ring
    rw [e]
    linarith [Complex.re_le_norm (t3 W (TMA.Kfull w.h T σ) - t3 W (TMA.K0 w.k T σ))]
  -- `c η T log T ≤ (δ/2) D`
  have h4 : c * η * (T * Real.log T) ≤ δ / 2 * TMA.Dsc T := by
    unfold TMA.Dsc
    have hcη : c * η ≤ δ / (4 * π) := by
      have e : δ / (4 * π) = (c + 1) * η := by
        rw [hηdef]
        field_simp
      rw [e]
      exact mul_le_mul_of_nonneg_right (by linarith) hη.le
    calc c * η * (T * Real.log T) ≤ δ / (4 * π) * (T * Real.log T) :=
          mul_le_mul_of_nonneg_right hcη (mul_nonneg hTpos.le hLpos.le)
      _ = δ / 2 * (T * Real.log T / (2 * π)) := by
          field_simp
          ring
  -- `C T ≤ (δ/2) D` for `log T ≥ 4π C / δ`
  have hL : 4 * π * Ct / δ ≤ Real.log T := (Real.le_log_iff_exp_le hTpos).mpr hT4
  have h5 : Ct * T ≤ δ / 2 * TMA.Dsc T := by
    unfold TMA.Dsc
    have h6 : Ct ≤ δ / 2 * Real.log T / (2 * π) := by
      rw [le_div_iff₀ (by positivity)]
      rw [div_le_iff₀ hδ] at hL
      linarith
    calc Ct * T ≤ δ / 2 * Real.log T / (2 * π) * T := mul_le_mul_of_nonneg_right h6 hTpos.le
      _ = δ / 2 * (T * Real.log T / (2 * π)) := by ring
  have h7 : CE * T ≤ |CE| * T := mul_le_mul_of_nonneg_right (le_abs_self CE) hTpos.le
  have h8 : Ct * T = C0 * T + |CE| * T := by
    rw [hCt]
    ring
  have h9 : (C3 W σ * w.kap3 + δ) * TMA.Dsc T
      = C3 W σ * w.kap3 * TMA.Dsc T + δ / 2 * TMA.Dsc T + δ / 2 * TMA.Dsc T := by ring
  rw [h9]
  linarith

end TMG

end
end Src_TMG_Trace3

section Src_TMG_Main
/-
Written for Kristian Muri Knausgård, drafted with Claude (Anthropic), 22 November 2026.
TMG/Main.lean — Theorem 1.1 of the paper on dyadic windows, for every window.
STATUS: proved from the interface statements of `TMA/Weight.lean`, `TMA/Traces.lean` (`t1_upper`),
`TMG/Gram.lean`, `TMG/Traces.lean`, `TMG/Trace3.lean`, `TMG/Window.lean` (no `sorry` in this file).
The proof is that of `TMA/Main.lean` with the window as a parameter; the only facts about the constants
that are used are `I2, I3, J2, J3 ≥ 0`.  Helper statements live in the namespace `TMG.MainAux`; those that
do not involve the window are copies of the helpers of `TMA/Main.lean` (which this file does not import).
-/

open MeasureTheory Complex
open scoped BigOperators Real

noncomputable section
namespace TMG

namespace MainAux

/-! ### real-number bookkeeping -/

/-- a positive number `x` with `x c ≤ ε/4`, for `c ≥ 0`. -/
theorem exists_small_mul {ε c : ℝ} (hε : 0 < ε) (hc : 0 ≤ c) : ∃ x : ℝ, 0 < x ∧ x * c ≤ ε / 4 := by
  refine ⟨ε / (4 * (c + 1)), by positivity, ?_⟩
  rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
  have h : 0 ≤ ε * c := mul_nonneg hε.le hc
  linarith

/-- the three trace bounds combined: with `X₃ ≤ (c₃ k₃ + δ) D`, `X₂ ≥ (c₂ k₂ - δ) D`, `X₁ ≤ (k₁ + δ) D`,
`k₁, k₃ ≤ 1 + ε₁`, `k₂ ≥ 1`:
`X₃ - 2 t X₂ + t² X₁ ≤ (c₃ - 2 t c₂ + t² + ε₁ (c₃ + t²) + δ (1+t)²) D`. -/
theorem assemble_real {P X3 X2 X1 D c3 c2 k1 k2 k3 t δ ε1 : ℝ}
    (hP : P ≤ X3 - 2 * t * X2 + t ^ 2 * X1)
    (h3 : X3 ≤ (c3 * k3 + δ) * D) (h2 : (c2 * k2 - δ) * D ≤ X2) (h1 : X1 ≤ (k1 + δ) * D)
    (hD : 0 ≤ D) (ht : 0 ≤ t) (hc3 : 0 ≤ c3) (hc2 : 0 ≤ c2)
    (hk1 : k1 ≤ 1 + ε1) (hk3 : k3 ≤ 1 + ε1) (hk2 : 1 ≤ k2) :
    P ≤ (c3 - 2 * t * c2 + t ^ 2 + (ε1 * (c3 + t ^ 2) + δ * (1 + t) ^ 2)) * D := by
  have h2t : 0 ≤ 2 * t := by linarith
  have ht2 : 0 ≤ t ^ 2 := sq_nonneg t
  have e2 : 2 * t * ((c2 * k2 - δ) * D) ≤ 2 * t * X2 := mul_le_mul_of_nonneg_left h2 h2t
  have e1 : t ^ 2 * X1 ≤ t ^ 2 * ((k1 + δ) * D) := mul_le_mul_of_nonneg_left h1 ht2
  have e3 : c3 * k3 ≤ c3 * (1 + ε1) := mul_le_mul_of_nonneg_left hk3 hc3
  have e4 : 2 * t * (c2 * 1) ≤ 2 * t * (c2 * k2) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hk2 hc2) h2t
  have e5 : t ^ 2 * k1 ≤ t ^ 2 * (1 + ε1) := mul_le_mul_of_nonneg_left hk1 ht2
  have e6 : (c3 * k3 + δ) - 2 * t * (c2 * k2 - δ) + t ^ 2 * (k1 + δ)
      ≤ c3 - 2 * t * c2 + t ^ 2 + (ε1 * (c3 + t ^ 2) + δ * (1 + t) ^ 2) := by
    linarith
  have e7 := mul_le_mul_of_nonneg_right e6 hD
  linarith

/-- passage from the scale `D` to the counting function `N`: if `0 ≤ P ≤ (K + η) D`, `0 < D ≤ (1+θ) N`,
`η ≤ ε/2` and `θ (|K| + ε) ≤ ε/2`, then `P ≤ (K + ε) N`. -/
theorem final_real {P K η ε θ D N : ℝ} (hP0 : 0 ≤ P) (hP : P ≤ (K + η) * D) (hD : 0 < D)
    (hDN : D ≤ (1 + θ) * N) (hθ : 0 ≤ θ) (hη : η ≤ ε / 2) (hθK : θ * (|K| + ε) ≤ ε / 2)
    (hε : 0 < ε) (hN : 0 ≤ N) :
    P ≤ (K + ε) * N := by
  have hKη : 0 ≤ K + η := by
    by_contra hcon
    have hneg : (K + η) * D < 0 := mul_neg_of_neg_of_pos (not_le.mp hcon) hD
    linarith
  have e1 : (K + η) * D ≤ (K + η) * ((1 + θ) * N) := mul_le_mul_of_nonneg_left hDN hKη
  have e2 : K + η ≤ |K| + ε := by
    have := le_abs_self K
    linarith
  have e3 : θ * (K + η) ≤ θ * (|K| + ε) := mul_le_mul_of_nonneg_left e2 hθ
  have e4 : (K + η) * (1 + θ) ≤ K + ε := by linarith
  have e5 : (K + η) * (1 + θ) * N ≤ (K + ε) * N := mul_le_mul_of_nonneg_right e4 hN
  linarith

/-! ### the constants -/

theorem C2_nonneg (W : Window) {σ : ℝ} (hσ : 0 < σ) : 0 ≤ C2 W σ := by
  unfold C2
  exact add_nonneg (div_nonneg (I2_nonneg W) hσ.le) (mul_nonneg hσ.le (J2_nonneg W))

theorem C3_nonneg (W : Window) (σ : ℝ) : 0 ≤ C3 W σ := by
  unfold C3
  exact add_nonneg (div_nonneg (I3_nonneg W) (sq_nonneg σ))
    (mul_nonneg (by norm_num) (J3_nonneg W))

theorem phiSum_nonneg (t T₁ T₂ : ℝ) : 0 ≤ ThirdMoment.phiSum t T₁ T₂ := by
  rw [ThirdMoment.phiSum_eq]
  exact Finset.sum_nonneg fun ρ _ => ThirdMoment.phi_nonneg (Nat.cast_nonneg _)

/-! ### Riemann–von Mangoldt: `D ≤ (1 + θ) N(T, 2T)` for large `T` -/

theorem rvm_Dsc_le {θ : ℝ} (hθ : 0 < θ) :
    ∃ T₁ : ℝ, ∀ T ≥ T₁,
      0 < T ∧ 0 < TMA.Dsc T ∧ TMA.Dsc T ≤ (1 + θ) * (Zeta23.Ncount T (2 * T) : ℝ) := by
  obtain ⟨C, T₀, hmain⟩ := Zeta23.riemannVonMangoldt_zeta.main
  obtain ⟨c₀, hc₀⟩ : ∃ c₀ : ℝ, c₀ = Real.log (2 * π) - 2 * Real.log 2 + 1 := ⟨_, rfl⟩
  refine ⟨max (max T₀ 3)
    (max (Real.exp (2 * (1 + θ) * |c₀| / θ)) (2 * π * (2 * (1 + θ) * |C| / θ))), fun T hT => ?_⟩
  have hT0 : T₀ ≤ T := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hT
  have hT3 : 3 ≤ T := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hT
  have hTe : Real.exp (2 * (1 + θ) * |c₀| / θ) ≤ T :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hT
  have hTC : 2 * π * (2 * (1 + θ) * |C| / θ) ≤ T :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hT
  have hTpos : 0 < T := by linarith
  have hπ : 0 < 2 * π := by positivity
  have hLpos : 0 < Real.log T := Real.log_pos (by linarith)
  have hL1 : 2 * (1 + θ) * |c₀| / θ ≤ Real.log T := (Real.le_log_iff_exp_le hTpos).mpr hTe
  have ha : 2 * (1 + θ) * |C| / θ ≤ T / (2 * π) := by
    rw [le_div_iff₀ hπ]
    linarith
  have hD : TMA.Dsc T = T / (2 * π) * Real.log T := by
    unfold TMA.Dsc
    ring
  have hell : Zeta23.ell1 T = Real.log T - c₀ := by
    unfold Zeta23.ell1 Zeta23.l
    rw [Real.log_div hTpos.ne' hπ.ne', hc₀]
    ring
  have hN := hmain T hT0
  rw [Zeta23.zetaZeroConfig_N, hell] at hN
  have hN1 := (abs_le.mp hN).1
  have hapos : 0 < T / (2 * π) := div_pos hTpos hπ
  have h1 : 2 * (1 + θ) * |c₀| ≤ Real.log T * θ := (div_le_iff₀ hθ).mp hL1
  have h2 : 2 * (1 + θ) * |C| ≤ T / (2 * π) * θ := (div_le_iff₀ hθ).mp ha
  rw [hD]
  generalize T / (2 * π) = a at *
  generalize Real.log T = L at *
  generalize (Zeta23.Ncount T (2 * T) : ℝ) = N at *
  have h3 : a * (2 * (1 + θ) * |c₀|) ≤ a * (L * θ) := mul_le_mul_of_nonneg_left h1 hapos.le
  have h4 : 2 * (1 + θ) * |C| * L ≤ a * θ * L := mul_le_mul_of_nonneg_right h2 hLpos.le
  have h1θ : 0 ≤ 1 + θ := by linarith
  have h5 : (1 + θ) * (a * c₀) ≤ (1 + θ) * (a * |c₀|) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (le_abs_self _) hapos.le) h1θ
  have h6 : (1 + θ) * (C * L) ≤ (1 + θ) * (|C| * L) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (le_abs_self _) hLpos.le) h1θ
  have h7 : (1 + θ) * (a * (L - c₀) - C * L) ≤ (1 + θ) * N :=
    mul_le_mul_of_nonneg_left (by linarith) h1θ
  refine ⟨hTpos, mul_pos hapos hLpos, ?_⟩
  linarith

/-! ### one-sided continuity of the constant at `σ = 1` -/

/-- for `1/2 ≤ σ < 1`:  `K(σ) ≤ K(1) + (8 I₃ + 2 t J₂)(1 - σ)`.
(`C₃(σ) - C₃(1) = I₃ (1/σ² - 1) ≤ 8 I₃ (1 - σ)` and
`C₂(1) - C₂(σ) = I₂ (1 - 1/σ) + J₂ (1 - σ) ≤ J₂ (1 - σ)`; only `I₂, I₃ ≥ 0` is used.) -/
theorem const_le_one (W : Window) {σ t : ℝ} (hσ : 1 / 2 ≤ σ) (hσ1 : σ < 1) (ht : 0 ≤ t) :
    C3 W σ - 2 * t * C2 W σ + t ^ 2
      ≤ C3 W 1 - 2 * t * C2 W 1 + t ^ 2 + (8 * I3 W + 2 * t * J2 W) * (1 - σ) := by
  have hσpos : 0 < σ := by linarith
  have hI2 : 0 ≤ I2 W := I2_nonneg W
  have hI3 : 0 ≤ I3 W := I3_nonneg W
  -- `1/σ² ≤ 1 + 8 (1 - σ)` and `1 ≤ 1/σ`
  have h1 : 1 / σ ^ 2 ≤ 1 + 8 * (1 - σ) := by
    rw [div_le_iff₀ (by positivity)]
    have hq : 0 ≤ (1 - σ) * (8 * (σ - 1 / 2) ^ 2 + 7 * (σ - 1 / 2) + 1 / 2) :=
      mul_nonneg (by linarith) (by nlinarith [sq_nonneg (σ - 1 / 2)])
    nlinarith
  have h2 : 1 ≤ 1 / σ := (one_le_div hσpos).mpr hσ1.le
  have e3 : I3 W * (1 / σ ^ 2) ≤ I3 W * (1 + 8 * (1 - σ)) := mul_le_mul_of_nonneg_left h1 hI3
  have e2 : 2 * t * (I2 W * 1) ≤ 2 * t * (I2 W * (1 / σ)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 hI2) (by linarith)
  have hC3 : C3 W σ = I3 W * (1 / σ ^ 2) + 3 * J3 W := by
    unfold C3
    ring
  have hC2 : C2 W σ = I2 W * (1 / σ) + σ * J2 W := by
    unfold C2
    ring
  have hC31 : C3 W 1 = I3 W + 3 * J3 W := by
    unfold C3
    ring
  have hC21 : C2 W 1 = I2 W + J2 W := by
    unfold C2
    ring
  rw [hC3, hC2, hC31, hC21]
  linarith

end MainAux

/-! ### the budget -/

open MainAux in
/-- the budget at bandwidth `σ < 1`, for every window -/
theorem budget_sigma (hRH : RiemannHypothesis) (W : Window) {σ t : ℝ} (hσ : 0 < σ) (hσ1 : σ < 1)
    (ht : 0 ≤ t) : ThirdMoment.Budget t (C3 W σ - 2 * t * C2 W σ + t ^ 2) := by
  intro ε hε
  have hC3 : 0 ≤ C3 W σ := C3_nonneg W σ
  have hC2 : 0 ≤ C2 W σ := C2_nonneg W hσ
  obtain ⟨ε1, hε1pos, hε1le⟩ := exists_small_mul hε (add_nonneg hC3 (sq_nonneg t))
  obtain ⟨δ, hδpos, hδle⟩ := exists_small_mul hε (sq_nonneg (1 + t))
  obtain ⟨θ, hθpos, hθK⟩ : ∃ θ : ℝ, 0 < θ ∧
      θ * (|C3 W σ - 2 * t * C2 W σ + t ^ 2| + ε) ≤ ε / 2 := by
    have hden : 0 < |C3 W σ - 2 * t * C2 W σ + t ^ 2| + ε := by positivity
    refine ⟨ε / (2 * (|C3 W σ - 2 * t * C2 W σ + t ^ 2| + ε)), by positivity, le_of_eq ?_⟩
    field_simp
  obtain ⟨w, hw1, hw3⟩ := TMA.exists_heightWeight hε1pos
  obtain ⟨Ta, ha⟩ := TMA.t1_upper hRH w hσ hσ1 δ hδpos
  obtain ⟨Tb, hb⟩ := t2_lower hRH W w hσ hσ1 δ hδpos
  obtain ⟨Tc, hc⟩ := t3_upper hRH W w hσ hσ1 δ hδpos
  obtain ⟨Td, hd⟩ := rvm_Dsc_le hθpos
  refine ⟨max (max Ta Tb) (max Tc Td), fun T hT => ?_⟩
  have hTa : Ta ≤ T := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hT
  have hTb : Tb ≤ T := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hT
  have hTc : Tc ≤ T := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hT
  have hTd : Td ≤ T := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hT
  obtain ⟨hTpos, hDpos, hDN⟩ := hd T hTd
  have hP := assemble_real (phiSum_le_Xi hRH W w hTpos hσ ht) (hc T hTc) (hb T hTb) (ha T hTa)
    hDpos.le ht hC3 hC2 hw1 hw3 w.one_le_kap2
  exact final_real (phiSum_nonneg t T (2 * T)) hP hDpos hDN hθpos.le (by linarith) hθK hε
    (Nat.cast_nonneg _)

open MainAux in
/-- **Theorem 1.1, dyadic form:** for every window `W` and every `t ≥ 0`,
`Σ Φ_t(m) ≤ (K_t(W) + ε) N(T, 2T)` for large `T`. -/
theorem budget_dyadic (hRH : RiemannHypothesis) (W : Window) {t : ℝ} (ht : 0 ≤ t) :
    ThirdMoment.Budget t (Kt W t) := by
  unfold Kt
  intro ε hε
  have hM : 0 ≤ 8 * I3 W + 2 * t * J2 W := by
    have h1 := mul_nonneg ht (J2_nonneg W)
    have h2 := I3_nonneg W
    linarith
  -- `s = 1 - σ` with `0 < s ≤ 1/2` and `M s ≤ ε/2`
  obtain ⟨s, hs0, hs1, hsM⟩ :
      ∃ s : ℝ, 0 < s ∧ s ≤ 1 / 2 ∧ (8 * I3 W + 2 * t * J2 W) * s ≤ ε / 2 := by
    obtain ⟨x, hx0, hxM⟩ := exists_small_mul hε hM
    refine ⟨min x (1 / 2), lt_min hx0 (by norm_num), min_le_right _ _, ?_⟩
    have h1 : (8 * I3 W + 2 * t * J2 W) * min x (1 / 2) ≤ (8 * I3 W + 2 * t * J2 W) * x :=
      mul_le_mul_of_nonneg_left (min_le_left _ _) hM
    linarith
  have hσ : (1 : ℝ) / 2 ≤ 1 - s := by linarith
  have hσ1 : 1 - s < 1 := by linarith
  have hK := const_le_one W hσ hσ1 ht
  rw [sub_sub_cancel] at hK
  obtain ⟨T₀, h₀⟩ :=
    budget_sigma hRH W (by linarith : (0 : ℝ) < 1 - s) hσ1 ht (ε / 2) (by linarith)
  refine ⟨T₀, fun T hT => ?_⟩
  have hN : (0 : ℝ) ≤ (Zeta23.Ncount T (2 * T) : ℝ) := Nat.cast_nonneg _
  have h1 := h₀ T hT
  have h2 : (C3 W (1 - s) - 2 * t * C2 W (1 - s) + t ^ 2 + ε / 2)
        * (Zeta23.Ncount T (2 * T) : ℝ)
      ≤ (C3 W 1 - 2 * t * C2 W 1 + t ^ 2 + ε) * (Zeta23.Ncount T (2 * T) : ℝ) :=
    mul_le_mul_of_nonneg_right (by linarith) hN
  exact le_trans h1 h2

end TMG

end
end Src_TMG_Main

section Src_TMG_Poly
/-
Written for Kristian Muri Knausgård, drafted with Claude (Anthropic), 22 November 2026.
TMG/Poly.lean — the two quartic windows of the paper and their exact constants.
  W1:  v₁(u) = 1 - (743/500) u² + (1197/1000) u⁴   (Corollary 1.3; San Martin's window)
  W2:  v₂(u) = 1 - (37/25) u² + (59/50) u⁴          (Corollary 1.4)
each normalised to integral 1 on [-1/2, 1/2].
STATUS: all statements proved (the constants use `I2_eq`, `I3_eq`, `J2_eq`, `J3_eq` of TMG/Window).
Helper lemmas live in the namespace `TMG.PolyAux`; the exported interface is in `TMG`.

Method.  For `v(u) = 1 + c2 u² + c4 u⁴`, `Z = ∫ v = 1 + c2/12 + c4/80` and `g = v/Z` on `[-1/2, 1/2]`:
  `∫ |u - w| v(w) dw = 1/4 + c2/32 + c4/192 + u² + (c2/6) u⁴ + (c4/15) u⁶ =: P(u)`   (`|u| ≤ 1/2`),
  `I2 = ∫ v² / Z²`, `J2 = ∫ v P / Z²`, `I3 = ∫ v³ / Z³`, `J3 = ∫ v² P / Z³`,
all four numerators being explicit polynomials in `c2, c4` (`PolyAux.nI2`, `nJ2`, `nI3`, `nJ3`).
-/

open MeasureTheory Complex
open scoped BigOperators Real

noncomputable section
namespace TMG

namespace PolyAux

/-! ### integrals of explicit polynomials -/

theorem hasDerivAt_poly5 (a0 a1 a2 a3 a4 a5 u : ℝ) :
    HasDerivAt (fun u : ℝ => a0 * u + a1 / 2 * u ^ 2 + a2 / 3 * u ^ 3 + a3 / 4 * u ^ 4 + a4 / 5 * u ^ 5
        + a5 / 6 * u ^ 6)
      (a0 + a1 * u + a2 * u ^ 2 + a3 * u ^ 3 + a4 * u ^ 4 + a5 * u ^ 5) u := by
  have h := (((((((hasDerivAt_id' u).const_mul a0).add
    ((hasDerivAt_pow 2 u).const_mul (a1 / 2))).add
    ((hasDerivAt_pow 3 u).const_mul (a2 / 3))).add
    ((hasDerivAt_pow 4 u).const_mul (a3 / 4))).add
    ((hasDerivAt_pow 5 u).const_mul (a4 / 5))).add
    ((hasDerivAt_pow 6 u).const_mul (a5 / 6)))
  refine h.congr_deriv ?_
  norm_num
  ring

/-- the integral of a polynomial of degree at most 5 with explicit coefficients -/
theorem integral_poly5 (a0 a1 a2 a3 a4 a5 a b : ℝ) :
    ∫ u in a..b, (a0 + a1 * u + a2 * u ^ 2 + a3 * u ^ 3 + a4 * u ^ 4 + a5 * u ^ 5)
      = a0 * (b - a) + a1 / 2 * (b ^ 2 - a ^ 2) + a2 / 3 * (b ^ 3 - a ^ 3) + a3 / 4 * (b ^ 4 - a ^ 4)
        + a4 / 5 * (b ^ 5 - a ^ 5) + a5 / 6 * (b ^ 6 - a ^ 6) := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ => hasDerivAt_poly5 a0 a1 a2 a3 a4 a5 x)
    (Continuous.intervalIntegrable (by fun_prop) _ _)]
  ring

theorem hasDerivAt_even14 (e0 e1 e2 e3 e4 e5 e6 e7 u : ℝ) :
    HasDerivAt (fun u : ℝ => e0 * u + e1 / 3 * u ^ 3 + e2 / 5 * u ^ 5 + e3 / 7 * u ^ 7 + e4 / 9 * u ^ 9
        + e5 / 11 * u ^ 11 + e6 / 13 * u ^ 13 + e7 / 15 * u ^ 15)
      (e0 + e1 * u ^ 2 + e2 * u ^ 4 + e3 * u ^ 6 + e4 * u ^ 8 + e5 * u ^ 10 + e6 * u ^ 12
        + e7 * u ^ 14) u := by
  have h := (((((((((hasDerivAt_id' u).const_mul e0).add
    ((hasDerivAt_pow 3 u).const_mul (e1 / 3))).add
    ((hasDerivAt_pow 5 u).const_mul (e2 / 5))).add
    ((hasDerivAt_pow 7 u).const_mul (e3 / 7))).add
    ((hasDerivAt_pow 9 u).const_mul (e4 / 9))).add
    ((hasDerivAt_pow 11 u).const_mul (e5 / 11))).add
    ((hasDerivAt_pow 13 u).const_mul (e6 / 13))).add
    ((hasDerivAt_pow 15 u).const_mul (e7 / 15)))
  refine h.congr_deriv ?_
  norm_num
  ring

/-- the integral over `[-1/2, 1/2]` of an even polynomial of degree at most 14
(`∫ u^(2k) = 1/((2k+1) 4^k)`) -/
theorem integral_even14 (e0 e1 e2 e3 e4 e5 e6 e7 : ℝ) :
    ∫ u in (-(1 / 2 : ℝ))..(1 / 2), (e0 + e1 * u ^ 2 + e2 * u ^ 4 + e3 * u ^ 6 + e4 * u ^ 8
        + e5 * u ^ 10 + e6 * u ^ 12 + e7 * u ^ 14)
      = e0 + e1 / 12 + e2 / 80 + e3 / 448 + e4 / 2304 + e5 / 11264 + e6 / 53248 + e7 / 245760 := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ => hasDerivAt_even14 e0 e1 e2 e3 e4 e5 e6 e7 x)
    (Continuous.intervalIntegrable (by fun_prop) _ _)]
  ring

/-! ### functions cut off outside `[-1/2, 1/2]` -/

/-- `q` on `[-1/2, 1/2]`, zero outside -/
def cut (q : ℝ → ℝ) (u : ℝ) : ℝ := if |u| ≤ 1 / 2 then q u else 0

theorem cut_pos (q : ℝ → ℝ) {u : ℝ} (h : |u| ≤ 1 / 2) : cut q u = q u := if_pos h

theorem cut_neg (q : ℝ → ℝ) {u : ℝ} (h : ¬ |u| ≤ 1 / 2) : cut q u = 0 := if_neg h

theorem cut_eq_indicator (q : ℝ → ℝ) : cut q = Set.indicator (Set.Icc (-(1 / 2)) (1 / 2)) q := by
  funext u
  by_cases h : |u| ≤ 1 / 2
  · rw [cut_pos q h, Set.indicator_of_mem (Set.mem_Icc.mpr (abs_le.mp h))]
  · rw [cut_neg q h, Set.indicator_of_notMem (fun h' => h (abs_le.mpr (Set.mem_Icc.mp h')))]

theorem measurable_cut {q : ℝ → ℝ} (hq : Continuous q) : Measurable (cut q) := by
  rw [cut_eq_indicator]
  exact hq.measurable.indicator measurableSet_Icc

/-- the integral over `ℝ` of a cut-off function is an interval integral -/
theorem integral_cut (q : ℝ → ℝ) : ∫ u, cut q u = ∫ u in (-(1 / 2 : ℝ))..(1 / 2), q u := by
  rw [cut_eq_indicator, integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num)]

theorem cut_pow (q : ℝ → ℝ) {n : ℕ} (hn : n ≠ 0) (u : ℝ) :
    cut q u ^ n = cut (fun u => q u ^ n) u := by
  by_cases h : |u| ≤ 1 / 2
  · rw [cut_pos _ h, cut_pos _ h]
  · rw [cut_neg _ h, cut_neg _ h, zero_pow hn]

/-- the first absolute moment about `u` of a cut-off function, split at `w = u` -/
theorem integral_abs_cut {q : ℝ → ℝ} (hq : Continuous q) {u : ℝ} (hu : |u| ≤ 1 / 2) :
    ∫ w, |u - w| * cut q w
      = (∫ w in (-(1 / 2 : ℝ))..u, (u - w) * q w) + ∫ w in u..(1 / 2 : ℝ), (w - u) * q w := by
  have hu' := abs_le.mp hu
  have h1 : ∀ w, |u - w| * cut q w = cut (fun w => |u - w| * q w) w := by
    intro w
    by_cases h : |w| ≤ 1 / 2
    · rw [cut_pos _ h, cut_pos _ h]
    · rw [cut_neg _ h, cut_neg _ h, mul_zero]
  simp_rw [h1]
  rw [integral_cut]
  have hc : Continuous fun w => |u - w| * q w := by fun_prop
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := u)
    (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _)]
  congr 1
  · refine intervalIntegral.integral_congr fun w hw => ?_
    rw [Set.uIcc_of_le hu'.1] at hw
    rw [abs_of_nonneg (by linarith [hw.2])]
  · refine intervalIntegral.integral_congr fun w hw => ?_
    rw [Set.uIcc_of_le hu'.2] at hw
    rw [abs_of_nonpos (by linarith [hw.1])]
    ring

/-- `∬ |u - w| p(u) q(w)` for cut-off functions: the inner integral is split at `w = u` -/
theorem integral_integral_abs_cut (p : ℝ → ℝ) {q : ℝ → ℝ} (hq : Continuous q) :
    ∫ u, ∫ w, |u - w| * (cut p u * cut q w)
      = ∫ u in (-(1 / 2 : ℝ))..(1 / 2), p u *
          ((∫ w in (-(1 / 2 : ℝ))..u, (u - w) * q w) + ∫ w in u..(1 / 2 : ℝ), (w - u) * q w) := by
  have h : ∀ u, ∫ w, |u - w| * (cut p u * cut q w)
      = cut (fun u => p u *
          ((∫ w in (-(1 / 2 : ℝ))..u, (u - w) * q w) + ∫ w in u..(1 / 2 : ℝ), (w - u) * q w)) u := by
    intro u
    have h1 : ∀ w, |u - w| * (cut p u * cut q w) = cut p u * (|u - w| * cut q w) := fun w => by ring
    simp_rw [h1]
    rw [integral_const_mul]
    by_cases hu : |u| ≤ 1 / 2
    · rw [integral_abs_cut hq hu, cut_pos _ hu, cut_pos _ hu]
    · rw [cut_neg _ hu, cut_neg _ hu, zero_mul]
  simp_rw [h]
  rw [integral_cut]

theorem sq_le_of_abs {u : ℝ} (h : |u| ≤ 1 / 2) : u ^ 2 ≤ 1 / 4 := by
  have h0 := abs_nonneg u
  nlinarith [sq_abs u]

theorem pow4_le_of_abs {u : ℝ} (h : |u| ≤ 1 / 2) : u ^ 4 ≤ 1 / 16 := by
  calc u ^ 4 = (u ^ 2) ^ 2 := by ring
    _ ≤ (1 / 4) ^ 2 := pow_le_pow_left₀ (sq_nonneg u) (sq_le_of_abs h) 2
    _ = 1 / 16 := by norm_num

/-! ### the quartic `v(u) = 1 + c2 u² + c4 u⁴`, divided by a constant `Z` -/

/-- `v(u) / Z` with `v(u) = 1 + c2 u² + c4 u⁴` -/
def qp (c2 c4 Z u : ℝ) : ℝ := (1 + c2 * u ^ 2 + c4 * u ^ 4) / Z

theorem continuous_qp (c2 c4 Z : ℝ) : Continuous (qp c2 c4 Z) := by
  unfold qp
  fun_prop

/-- `∫ v = 1 + c2/12 + c4/80` is positive when `v` is positive on `[-1/2, 1/2]`
(Boole's rule is exact in degree 4: `∫ v = (2/15) v(0) + (32/45) v(1/4) + (7/45) v(1/2)`) -/
theorem qZ_pos {c2 c4 : ℝ} (hpos : ∀ u : ℝ, |u| ≤ 1 / 2 → 0 < 1 + c2 * u ^ 2 + c4 * u ^ 4) :
    0 < 1 + c2 / 12 + c4 / 80 := by
  have h1 := hpos (1 / 4) (by rw [abs_of_pos (by norm_num)]; norm_num)
  have h2 := hpos (1 / 2) (by rw [abs_of_pos (by norm_num)])
  norm_num at h1 h2
  linarith

theorem qp_nonneg {c2 c4 : ℝ} (hpos : ∀ u : ℝ, |u| ≤ 1 / 2 → 0 < 1 + c2 * u ^ 2 + c4 * u ^ 4)
    (u : ℝ) : 0 ≤ cut (qp c2 c4 (1 + c2 / 12 + c4 / 80)) u := by
  by_cases h : |u| ≤ 1 / 2
  · rw [cut_pos _ h]
    exact div_nonneg (hpos u h).le (qZ_pos hpos).le
  · rw [cut_neg _ h]

theorem qp_le {c2 c4 : ℝ} (hpos : ∀ u : ℝ, |u| ≤ 1 / 2 → 0 < 1 + c2 * u ^ 2 + c4 * u ^ 4)
    (u : ℝ) : cut (qp c2 c4 (1 + c2 / 12 + c4 / 80)) u
      ≤ (1 + |c2| / 4 + |c4| / 16) / (1 + c2 / 12 + c4 / 80) := by
  have hZ := qZ_pos hpos
  by_cases h : |u| ≤ 1 / 2
  · rw [cut_pos _ h]
    unfold qp
    refine div_le_div_of_nonneg_right ?_ hZ.le
    have e2 : c2 * u ^ 2 ≤ |c2| * (1 / 4) :=
      mul_le_mul (le_abs_self c2) (sq_le_of_abs h) (sq_nonneg u) (abs_nonneg c2)
    have e4 : c4 * u ^ 4 ≤ |c4| * (1 / 16) :=
      mul_le_mul (le_abs_self c4) (pow4_le_of_abs h) (by positivity) (abs_nonneg c4)
    linarith
  · rw [cut_neg _ h]
    exact div_nonneg (by positivity) hZ.le

theorem integral_cut_qp (c2 c4 Z : ℝ) :
    ∫ u, cut (qp c2 c4 Z) u = (1 + c2 / 12 + c4 / 80) / Z := by
  rw [integral_cut]
  have h : ∀ u : ℝ, qp c2 c4 Z u = 1 / Z + c2 / Z * u ^ 2 + c4 / Z * u ^ 4 + 0 * u ^ 6 + 0 * u ^ 8
      + 0 * u ^ 10 + 0 * u ^ 12 + 0 * u ^ 14 := by
    intro u
    unfold qp
    ring
  simp_rw [h]
  rw [integral_even14]
  ring

/-- `P(u) / Z` with `P(u) = ∫ |u - w| v(w) dw` (for `|u| ≤ 1/2`) -/
def qM (c2 c4 Z u : ℝ) : ℝ :=
  (1 / 4 + c2 / 32 + c4 / 192 + u ^ 2 + c2 / 6 * u ^ 4 + c4 / 15 * u ^ 6) / Z

/-- the inner integral `∫_{-1/2}^{u} (u - w) v(w)/Z dw + ∫_{u}^{1/2} (w - u) v(w)/Z dw` -/
theorem inner_qp (c2 c4 Z u : ℝ) :
    (∫ w in (-(1 / 2 : ℝ))..u, (u - w) * qp c2 c4 Z w) + ∫ w in u..(1 / 2 : ℝ), (w - u) * qp c2 c4 Z w
      = qM c2 c4 Z u := by
  have h1 : ∀ w : ℝ, (u - w) * qp c2 c4 Z w
      = u / Z + (-(1 / Z)) * w + (c2 * u / Z) * w ^ 2 + (-(c2 / Z)) * w ^ 3 + (c4 * u / Z) * w ^ 4
        + (-(c4 / Z)) * w ^ 5 := by
    intro w
    unfold qp
    ring
  have h2 : ∀ w : ℝ, (w - u) * qp c2 c4 Z w
      = -(u / Z) + (1 / Z) * w + (-(c2 * u / Z)) * w ^ 2 + (c2 / Z) * w ^ 3 + (-(c4 * u / Z)) * w ^ 4
        + (c4 / Z) * w ^ 5 := by
    intro w
    unfold qp
    ring
  simp_rw [h1, h2]
  rw [integral_poly5, integral_poly5]
  unfold qM
  ring

/-- `∫ v²` -/
def nI2 (c2 c4 : ℝ) : ℝ :=
  1 + (1 / 6) * c2 + (1 / 40) * c4 + (1 / 80) * c2 ^ 2 + (1 / 224) * c2 * c4 + (1 / 2304) * c4 ^ 2

/-- `∬ |u - w| v(u) v(w)` -/
def nJ2 (c2 c4 : ℝ) : ℝ :=
  1 / 3 + (1 / 15) * c2 + (3 / 280) * c4 + (1 / 336) * c2 ^ 2 + (1 / 1080) * c2 * c4
    + (1 / 14080) * c4 ^ 2

/-- `∫ v³` -/
def nI3 (c2 c4 : ℝ) : ℝ :=
  1 + (1 / 4) * c2 + (3 / 80) * c4 + (3 / 80) * c2 ^ 2 + (3 / 224) * c2 * c4 + (1 / 768) * c4 ^ 2
    + (1 / 448) * c2 ^ 3 + (1 / 768) * c2 ^ 2 * c4 + (3 / 11264) * c2 * c4 ^ 2 + (1 / 53248) * c4 ^ 3

/-- `∬ |u - w| v(u)² v(w)` -/
def nJ3 (c2 c4 : ℝ) : ℝ :=
  1 / 3 + (1 / 10) * c2 + (9 / 560) * c4 + (19 / 1680) * c2 ^ 2 + (29 / 7560) * c2 * c4
    + (43 / 126720) * c4 ^ 2 + (1 / 2160) * c2 ^ 3 + (71 / 295680) * c2 ^ 2 * c4
    + (89 / 2096640) * c2 * c4 ^ 2 + (7 / 2764800) * c4 ^ 3

theorem integral_sq_qp (c2 c4 Z : ℝ) : ∫ u, cut (qp c2 c4 Z) u ^ 2 = nI2 c2 c4 / Z ^ 2 := by
  simp_rw [cut_pow _ two_ne_zero]
  rw [integral_cut]
  have h : ∀ u : ℝ, qp c2 c4 Z u ^ 2
      = 1 / Z ^ 2 + (2 * c2) / Z ^ 2 * u ^ 2 + (2 * c4 + c2 ^ 2) / Z ^ 2 * u ^ 4
        + (2 * c2 * c4) / Z ^ 2 * u ^ 6 + c4 ^ 2 / Z ^ 2 * u ^ 8 + 0 * u ^ 10 + 0 * u ^ 12
        + 0 * u ^ 14 := by
    intro u
    unfold qp
    ring
  simp_rw [h]
  rw [integral_even14]
  unfold nI2
  ring

theorem integral_cube_qp (c2 c4 Z : ℝ) : ∫ u, cut (qp c2 c4 Z) u ^ 3 = nI3 c2 c4 / Z ^ 3 := by
  simp_rw [cut_pow _ three_ne_zero]
  rw [integral_cut]
  have h : ∀ u : ℝ, qp c2 c4 Z u ^ 3
      = 1 / Z ^ 3 + (3 * c2) / Z ^ 3 * u ^ 2 + (3 * c4 + 3 * c2 ^ 2) / Z ^ 3 * u ^ 4
        + (6 * c2 * c4 + c2 ^ 3) / Z ^ 3 * u ^ 6 + (3 * c4 ^ 2 + 3 * c2 ^ 2 * c4) / Z ^ 3 * u ^ 8
        + (3 * c2 * c4 ^ 2) / Z ^ 3 * u ^ 10 + c4 ^ 3 / Z ^ 3 * u ^ 12 + 0 * u ^ 14 := by
    intro u
    unfold qp
    ring
  simp_rw [h]
  rw [integral_even14]
  unfold nI3
  ring

theorem integral_abs_qp (c2 c4 Z : ℝ) :
    ∫ u, ∫ w, |u - w| * (cut (qp c2 c4 Z) u * cut (qp c2 c4 Z) w) = nJ2 c2 c4 / Z ^ 2 := by
  rw [integral_integral_abs_cut _ (continuous_qp c2 c4 Z)]
  simp_rw [inner_qp]
  have h : ∀ u : ℝ, qp c2 c4 Z u * qM c2 c4 Z u
      = (1 / 4 + (1 / 32) * c2 + (1 / 192) * c4) / Z ^ 2
        + (1 + (1 / 4) * c2 + (1 / 32) * c2 ^ 2 + (1 / 192) * c2 * c4) / Z ^ 2 * u ^ 2
        + ((7 / 6) * c2 + (1 / 4) * c4 + (1 / 32) * c2 * c4 + (1 / 192) * c4 ^ 2) / Z ^ 2 * u ^ 4
        + ((16 / 15) * c4 + (1 / 6) * c2 ^ 2) / Z ^ 2 * u ^ 6
        + ((7 / 30) * c2 * c4) / Z ^ 2 * u ^ 8
        + ((1 / 15) * c4 ^ 2) / Z ^ 2 * u ^ 10 + 0 * u ^ 12 + 0 * u ^ 14 := by
    intro u
    unfold qp qM
    ring
  simp_rw [h]
  rw [integral_even14]
  unfold nJ2
  ring

theorem integral_abs_sq_qp (c2 c4 Z : ℝ) :
    ∫ u, ∫ w, |u - w| * (cut (qp c2 c4 Z) u ^ 2 * cut (qp c2 c4 Z) w) = nJ3 c2 c4 / Z ^ 3 := by
  simp_rw [cut_pow _ two_ne_zero]
  rw [integral_integral_abs_cut _ (continuous_qp c2 c4 Z)]
  simp_rw [inner_qp]
  have h : ∀ u : ℝ, qp c2 c4 Z u ^ 2 * qM c2 c4 Z u
      = (1 / 4 + (1 / 32) * c2 + (1 / 192) * c4) / Z ^ 3
        + (1 + (1 / 2) * c2 + (1 / 16) * c2 ^ 2 + (1 / 96) * c2 * c4) / Z ^ 3 * u ^ 2
        + ((13 / 6) * c2 + (1 / 2) * c4 + (1 / 4) * c2 ^ 2 + (1 / 16) * c2 * c4 + (1 / 96) * c4 ^ 2
            + (1 / 32) * c2 ^ 3 + (1 / 192) * c2 ^ 2 * c4) / Z ^ 3 * u ^ 4
        + ((31 / 15) * c4 + (4 / 3) * c2 ^ 2 + (1 / 2) * c2 * c4 + (1 / 16) * c2 ^ 2 * c4
            + (1 / 96) * c2 * c4 ^ 2) / Z ^ 3 * u ^ 6
        + ((37 / 15) * c2 * c4 + (1 / 4) * c4 ^ 2 + (1 / 6) * c2 ^ 3 + (1 / 32) * c2 * c4 ^ 2
            + (1 / 192) * c4 ^ 3) / Z ^ 3 * u ^ 8
        + ((17 / 15) * c4 ^ 2 + (2 / 5) * c2 ^ 2 * c4) / Z ^ 3 * u ^ 10
        + ((3 / 10) * c2 * c4 ^ 2) / Z ^ 3 * u ^ 12
        + ((1 / 15) * c4 ^ 3) / Z ^ 3 * u ^ 14 := by
    intro u
    unfold qp qM
    ring
  simp_rw [h]
  rw [integral_even14]
  unfold nJ3
  ring

end PolyAux

open PolyAux

/-- the window `v / ∫v` for `v(u) = 1 + c2 u² + c4 u⁴` on `[-1/2, 1/2]` (requires positivity of `v`) -/
def quarticWindow (c2 c4 : ℝ) (hpos : ∀ u : ℝ, |u| ≤ 1 / 2 → 0 < 1 + c2 * u ^ 2 + c4 * u ^ 4) : Window where
  g := cut (qp c2 c4 (1 + c2 / 12 + c4 / 80))
  meas := measurable_cut (continuous_qp _ _ _)
  nonneg := qp_nonneg hpos
  bound := (1 + |c2| / 4 + |c4| / 16) / (1 + c2 / 12 + c4 / 80)
  le_bound := qp_le hpos
  supp := fun _ hu => cut_neg _ (not_le.mpr hu)
  integral_eq_one := by
    rw [integral_cut_qp]
    exact div_self (qZ_pos hpos).ne'

namespace PolyAux

theorem quarticWindow_g_eq_cut (c2 c4 : ℝ)
    (hpos : ∀ u : ℝ, |u| ≤ 1 / 2 → 0 < 1 + c2 * u ^ 2 + c4 * u ^ 4) :
    (quarticWindow c2 c4 hpos).g = cut (qp c2 c4 (1 + c2 / 12 + c4 / 80)) := rfl

/-- the explicit formula for a quartic window -/
theorem quarticWindow_g (c2 c4 : ℝ)
    (hpos : ∀ u : ℝ, |u| ≤ 1 / 2 → 0 < 1 + c2 * u ^ 2 + c4 * u ^ 4) (u : ℝ) :
    (quarticWindow c2 c4 hpos).g u
      = if |u| ≤ 1 / 2 then (1 + c2 * u ^ 2 + c4 * u ^ 4) / (1 + c2 / 12 + c4 / 80) else 0 := rfl

theorem I2_quartic (c2 c4 : ℝ) (hpos : ∀ u : ℝ, |u| ≤ 1 / 2 → 0 < 1 + c2 * u ^ 2 + c4 * u ^ 4) :
    I2 (quarticWindow c2 c4 hpos) = nI2 c2 c4 / (1 + c2 / 12 + c4 / 80) ^ 2 := by
  rw [I2_eq, quarticWindow_g_eq_cut]
  exact integral_sq_qp c2 c4 _

theorem I3_quartic (c2 c4 : ℝ) (hpos : ∀ u : ℝ, |u| ≤ 1 / 2 → 0 < 1 + c2 * u ^ 2 + c4 * u ^ 4) :
    I3 (quarticWindow c2 c4 hpos) = nI3 c2 c4 / (1 + c2 / 12 + c4 / 80) ^ 3 := by
  rw [I3_eq, quarticWindow_g_eq_cut]
  exact integral_cube_qp c2 c4 _

theorem J2_quartic (c2 c4 : ℝ) (hpos : ∀ u : ℝ, |u| ≤ 1 / 2 → 0 < 1 + c2 * u ^ 2 + c4 * u ^ 4) :
    J2 (quarticWindow c2 c4 hpos) = nJ2 c2 c4 / (1 + c2 / 12 + c4 / 80) ^ 2 := by
  rw [J2_eq, quarticWindow_g_eq_cut]
  exact integral_abs_qp c2 c4 _

theorem J3_quartic (c2 c4 : ℝ) (hpos : ∀ u : ℝ, |u| ≤ 1 / 2 → 0 < 1 + c2 * u ^ 2 + c4 * u ^ 4) :
    J3 (quarticWindow c2 c4 hpos) = nJ3 c2 c4 / (1 + c2 / 12 + c4 / 80) ^ 3 := by
  rw [J3_eq, quarticWindow_g_eq_cut]
  exact integral_abs_sq_qp c2 c4 _

/-- `C₂` at full bandwidth for a quartic window, as a rational function of the coefficients -/
theorem C2_quartic (c2 c4 : ℝ) (hpos : ∀ u : ℝ, |u| ≤ 1 / 2 → 0 < 1 + c2 * u ^ 2 + c4 * u ^ 4) :
    C2 (quarticWindow c2 c4 hpos) 1 = (nI2 c2 c4 + nJ2 c2 c4) / (1 + c2 / 12 + c4 / 80) ^ 2 := by
  unfold C2
  rw [I2_quartic, J2_quartic]
  ring

/-- `C₃` at full bandwidth for a quartic window, as a rational function of the coefficients -/
theorem C3_quartic (c2 c4 : ℝ) (hpos : ∀ u : ℝ, |u| ≤ 1 / 2 → 0 < 1 + c2 * u ^ 2 + c4 * u ^ 4) :
    C3 (quarticWindow c2 c4 hpos) 1 = (nI3 c2 c4 + 3 * nJ3 c2 c4) / (1 + c2 / 12 + c4 / 80) ^ 3 := by
  unfold C3
  rw [I3_quartic, J3_quartic]
  ring

/-- positivity of a quartic with `c2 > -4` and `c4 ≥ 0`:
for `s = u² ≤ 1/4`, `1 + c2 s + c4 s² ≥ 1 + c2/4 > 0` when `c2 ≤ 0` -/
theorem quartic_pos {c2 c4 : ℝ} (h2 : -4 < c2) (h2' : c2 ≤ 0) (h4 : 0 ≤ c4) (u : ℝ)
    (hu : |u| ≤ 1 / 2) : 0 < 1 + c2 * u ^ 2 + c4 * u ^ 4 := by
  have e1 : c2 * (1 / 4) ≤ c2 * u ^ 2 := mul_le_mul_of_nonpos_left (sq_le_of_abs hu) h2'
  have e2 : 0 ≤ c4 * u ^ 4 := mul_nonneg h4 (by positivity)
  linarith

end PolyAux

def W1 : Window := quarticWindow (-(743 / 500)) (1197 / 1000)
  (quartic_pos (by norm_num) (by norm_num) (by norm_num))
def W2 : Window := quarticWindow (-(37 / 25)) (59 / 50)
  (quartic_pos (by norm_num) (by norm_num) (by norm_num))

theorem W1_g (u : ℝ) : W1.g u
    = if |u| ≤ 1 / 2 then (1 - 743 / 500 * u ^ 2 + 1197 / 1000 * u ^ 4) / (213871 / 240000) else 0 := by
  unfold W1
  rw [quarticWindow_g]
  by_cases h : |u| ≤ 1 / 2
  · rw [if_pos h, if_pos h,
      show (1 + -(743 / 500 : ℝ) / 12 + 1197 / 1000 / 80) = 213871 / 240000 by norm_num]
    ring
  · rw [if_neg h, if_neg h]
theorem C2_W1 : C2 W1 1 = 4677629393520 / 3522041957357 := by
  unfold W1
  rw [C2_quartic]
  unfold nI2 nJ2
  norm_num
theorem C3_W1 : C3 W1 1 = 1484618890495233180 / 753262635461898947 := by
  unfold W1
  rw [C3_quartic]
  unfold nI3 nJ3
  norm_num
theorem C2_W2 : C2 W2 1 = 35104552720 / 26432361879 := by
  unfold W2
  rw [C2_quartic]
  unfold nI2 nJ2
  norm_num
theorem C3_W2 : C3 W2 1 = 344973131634060 / 175033841678839 := by
  unfold W2
  rw [C3_quartic]
  unfold nI3 nJ3
  norm_num


end TMG
end
end Src_TMG_Poly

section Src_TMG_Results
/-
Written for Kristian Muri Knausgård, drafted with Claude (Anthropic), 22 November 2026.

TMG/Results.lean — the statements of the paper "Distinct zeros of the Riemann zeta function and the third
moment of multiplicities", in the order of its introduction, for the zeros of Mathlib's `riemannZeta`
(counting functions of Zeta23).  `RiemannHypothesis` is a hypothesis; no other assumption is made, except
where a lower bound for the simple zeros is stated explicitly as a hypothesis (Corollary 1.3).

  W1:  v(u) = 1 - (743/500) u² + (1197/1000) u⁴  (normalised),  W2:  v(u) = 1 - (37/25) u² + (59/50) u⁴.
-/

open MeasureTheory Complex
open scoped BigOperators Real

noncomputable section
namespace TMG

open ThirdMoment (Ac Bc phiSum highMult Budget SimpleLower)

/-! ## Theorem 1.1: the third moment of the multiplicities, for every window and every `t ≥ 0` -/

/-- **Theorem 1.1 on `(T, 2T]`.** -/
theorem theorem_1_1_dyadic (hRH : RiemannHypothesis) (W : Window) {t : ℝ} (ht : 0 ≤ t) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, phiSum t T (2 * T) ≤ (Kt W t + ε) * (Zeta23.Ncount T (2 * T) : ℝ) :=
  budget_dyadic hRH W ht

/-- **Theorem 1.1 on `(0, T]`.** -/
theorem theorem_1_1_cumulative (hRH : RiemannHypothesis) (W : Window) {t : ℝ} (ht : 0 ≤ t) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, phiSum t 0 T ≤ (Kt W t + ε) * (Zeta23.Ncount 0 T : ℝ) :=
  budgetCum_of_budget ht (budget_dyadic hRH W ht)

/-! ## Theorem 1.2: distinct zeros against simple zeros -/

/-- **Theorem 1.2, lower bound, on `(T, 2T]`.** -/
theorem theorem_1_2_dyadic (hRH : RiemannHypothesis) (W : Window) {t : ℝ} (ht1 : 1 ≤ t) (ht2 : t < 2) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      Ac t * (Zeta23.Nsimple T (2 * T) : ℝ) + (1 - Ac t - Bc t * Kt W t - ε) * (Zeta23.Ncount T (2 * T) : ℝ)
        ≤ (Zeta23.Ndist T (2 * T) : ℝ) :=
  ThirdMoment.lower_of_budget ht1 ht2 (budget_dyadic hRH W (by linarith))

/-- **Theorem 1.2, lower bound, on `(0, T]`.** -/
theorem theorem_1_2_cumulative (hRH : RiemannHypothesis) (W : Window) {t : ℝ} (ht1 : 1 ≤ t)
    (ht2 : t < 2) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      Ac t * (Zeta23.Nsimple 0 T : ℝ) + (1 - Ac t - Bc t * Kt W t - ε) * (Zeta23.Ncount 0 T : ℝ)
        ≤ (Zeta23.Ndist 0 T : ℝ) :=
  lower_of_budgetCum ht1 ht2 (theorem_1_1_cumulative hRH W (by linarith))

/-- **Theorem 1.2, upper bound** (every window, no hypothesis): `2 N_d ≤ N + N_s`. -/
theorem theorem_1_2_upper (T₁ T₂ : ℝ) :
    2 * (Zeta23.Ndist T₁ T₂ : ℝ) ≤ (Zeta23.Ncount T₁ T₂ : ℝ) + (Zeta23.Nsimple T₁ T₂ : ℝ) :=
  ThirdMoment.two_Ndist_le T₁ T₂

/-! ## Corollary 1.4: no input on simple zeros (window W2, `t = 51/50`) -/

theorem Kt_W2 : Kt W2 (51 / 50) = 925024809189607673 / 3063092229379682500 := by
  unfold Kt
  rw [C2_W2, C3_W2]
  norm_num

/-- **Corollary 1.4, distinct zeros, `(T, 2T]`:** `0.842778...` -/
theorem corollary_1_4_distinct_dyadic (hRH : RiemannHypothesis) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      ((4958562745002886473 : ℝ) / 5883587554192494146 - ε) * (Zeta23.Ncount T (2 * T) : ℝ)
        ≤ (Zeta23.Ndist T (2 * T) : ℝ) := by
  have h := ThirdMoment.distinct_of_budget (t := 51 / 50) (by norm_num) (by norm_num)
    (budget_dyadic hRH W2 (by norm_num))
  have e : (1 : ℝ) - Kt W2 (51 / 50) / (2 * (2 - 51 / 50) ^ 2)
      = 4958562745002886473 / 5883587554192494146 := by
    rw [Kt_W2]; norm_num
  rw [e] at h
  exact h

/-- **Corollary 1.4, distinct zeros, `(0, T]`.** -/
theorem corollary_1_4_distinct_cumulative (hRH : RiemannHypothesis) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      ((4958562745002886473 : ℝ) / 5883587554192494146 - ε) * (Zeta23.Ncount 0 T : ℝ)
        ≤ (Zeta23.Ndist 0 T : ℝ) := by
  have h := distinct_of_budgetCum (t := 51 / 50) (by norm_num) (by norm_num)
    (theorem_1_1_cumulative hRH W2 (by norm_num))
  have e : (1 : ℝ) - Kt W2 (51 / 50) / (2 * (2 - 51 / 50) ^ 2)
      = 4958562745002886473 / 5883587554192494146 := by
    rw [Kt_W2]; norm_num
  rw [e] at h
  exact h

/-- **Corollary 1.4, simple zeros, `(T, 2T]`:** `0.685557...` -/
theorem corollary_1_4_simple_dyadic (hRH : RiemannHypothesis) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      ((2016768967906639400 : ℝ) / 2941793777096247073 - ε) * (Zeta23.Ncount T (2 * T) : ℝ)
        ≤ (Zeta23.Nsimple T (2 * T) : ℝ) := by
  have h := ThirdMoment.simple_of_budget (t := 51 / 50) (by norm_num) (by norm_num)
    (budget_dyadic hRH W2 (by norm_num))
  have e : (1 : ℝ) - Kt W2 (51 / 50) / (2 - 51 / 50) ^ 2
      = 2016768967906639400 / 2941793777096247073 := by
    rw [Kt_W2]; norm_num
  rw [e] at h
  exact h

/-- **Corollary 1.4, simple zeros, `(0, T]`.** -/
theorem corollary_1_4_simple_cumulative (hRH : RiemannHypothesis) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      ((2016768967906639400 : ℝ) / 2941793777096247073 - ε) * (Zeta23.Ncount 0 T : ℝ)
        ≤ (Zeta23.Nsimple 0 T : ℝ) := by
  have h := simple_of_budgetCum (t := 51 / 50) (by norm_num) (by norm_num)
    (theorem_1_1_cumulative hRH W2 (by norm_num))
  have e : (1 : ℝ) - Kt W2 (51 / 50) / (2 - 51 / 50) ^ 2
      = 2016768967906639400 / 2941793777096247073 := by
    rw [Kt_W2]; norm_num
  rw [e] at h
  exact h

/-! ## Corollary 1.5: zeros of high multiplicity -/

/-- **Corollary 1.5, general form, `(T, 2T]`:** zeros of multiplicity `≥ j` carry at most
`(K_t(W)/(j-t)² + ε) N`, for `0 ≤ t < j`. -/
theorem corollary_1_5_dyadic (hRH : RiemannHypothesis) (W : Window) {t : ℝ} (ht : 0 ≤ t) (j : ℕ)
    (htj : t < j) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      highMult j T (2 * T) ≤ (Kt W t / ((j : ℝ) - t) ^ 2 + ε) * (Zeta23.Ncount T (2 * T) : ℝ) :=
  ThirdMoment.highMult_of_budget j htj (budget_dyadic hRH W ht)

/-- **Corollary 1.5, general form, `(0, T]`.** -/
theorem corollary_1_5_cumulative (hRH : RiemannHypothesis) (W : Window) {t : ℝ} (ht : 0 ≤ t) (j : ℕ)
    (htj : t < j) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      highMult j 0 T ≤ (Kt W t / ((j : ℝ) - t) ^ 2 + ε) * (Zeta23.Ncount 0 T : ℝ) :=
  highMult_of_budgetCum j htj (theorem_1_1_cumulative hRH W ht)

theorem Kt_W1_six_fifths : Kt W1 (6 / 5) / ((3 : ℝ) - 6 / 5) ^ 2
    = 1402790192572745464 / 20338091157471271569 := by
  unfold Kt
  rw [C2_W1, C3_W1]
  norm_num

/-- **Corollary 1.5, `j = 3`, `(0, T]`:** zeros of multiplicity at least three carry at most `6.8974%`. -/
theorem corollary_1_5_three_cumulative (hRH : RiemannHypothesis) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      highMult 3 0 T ≤ ((1402790192572745464 : ℝ) / 20338091157471271569 + ε) * (Zeta23.Ncount 0 T : ℝ) := by
  have h := corollary_1_5_cumulative hRH W1 (t := 6 / 5) (by norm_num) 3 (by norm_num)
  have e : Kt W1 (6 / 5) / (((3 : ℕ) : ℝ) - 6 / 5) ^ 2
      = 1402790192572745464 / 20338091157471271569 := by
    have := Kt_W1_six_fifths
    push_cast
    exact this
  rw [e] at h
  exact h

/-! ## Corollary 1.3: with a lower bound for the simple zeros (window W1, `t = 1037/1000`)

The proportion `19/27` of simple zeros (Bui and Heath-Brown, under RH) is NOT proved here; it enters as
the hypothesis `hS`. -/

theorem kappa_W1 (s₀ : ℝ) :
    Ac (1037 / 1000) * s₀ + 1 - Ac (1037 / 1000) - Bc (1037 / 1000) * Kt W1 (1037 / 1000)
      = 2616877 / 5852000 * s₀
        + 322313022364071761395 / 601103583098595359706 := by
  unfold Kt Ac Bc
  rw [C2_W1, C3_W1]
  norm_num
  ring

/-- **Corollary 1.3 on `(0, T]`, conditional on the simple-zero bound:** if a proportion `19/27` of the
zeros up to `T` are simple, then the proportion of distinct zeros is at least
`9206426916034466876368351/10819864495774716474708000 = 0.85088190...`. -/
theorem corollary_1_3_cumulative (hRH : RiemannHypothesis)
    (hS : ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      ((19 : ℝ) / 27 - ε) * (Zeta23.Ncount 0 T : ℝ) ≤ (Zeta23.Nsimple 0 T : ℝ)) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      ((9206426916034466876368351 : ℝ) / 10819864495774716474708000 - ε) * (Zeta23.Ncount 0 T : ℝ)
        ≤ (Zeta23.Ndist 0 T : ℝ) := by
  have h := distinct_of_budgetCum_simple (t := 1037 / 1000) (s₀ := 19 / 27) (by norm_num)
    (by norm_num) (theorem_1_1_cumulative hRH W1 (by norm_num)) hS
  have e : Ac (1037 / 1000) * (19 / 27) + 1 - Ac (1037 / 1000)
      - Bc (1037 / 1000) * Kt W1 (1037 / 1000)
      = 9206426916034466876368351 / 10819864495774716474708000 := by
    rw [kappa_W1]; norm_num
  rw [e] at h
  exact h

/-- **Corollary 1.3 on `(T, 2T]`, conditional on the dyadic simple-zero bound.** -/
theorem corollary_1_3_dyadic (hRH : RiemannHypothesis) (hS : SimpleLower (19 / 27)) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      ((9206426916034466876368351 : ℝ) / 10819864495774716474708000 - ε)
          * (Zeta23.Ncount T (2 * T) : ℝ) ≤ (Zeta23.Ndist T (2 * T) : ℝ) := by
  have h := ThirdMoment.distinct_of_budget_simple (t := 1037 / 1000) (s₀ := 19 / 27) (by norm_num)
    (by norm_num) (budget_dyadic hRH W1 (by norm_num)) hS
  have e : Ac (1037 / 1000) * (19 / 27) + 1 - Ac (1037 / 1000)
      - Bc (1037 / 1000) * Kt W1 (1037 / 1000)
      = 9206426916034466876368351 / 10819864495774716474708000 := by
    rw [kappa_W1]; norm_num
  rw [e] at h
  exact h

end TMG

end
end Src_TMG_Results

section Src_TMG_Record
/-
Written for Kristian Muri Knausgård, drafted with Claude (Anthropic), 22 November 2026.

TMG/Record.lean — the quartic window and the shift that are optimal, within the family of even quartic windows, for
the bound without input on simple zeros:  N_d ≥ (1 - K_t(g)/(2 (2 - t)²) - ε) N  (Corollary 1.4 of the paper).

  window  v(u) = 1 + c2 u² + c4 u⁴,  c2 = -14768021/10000000,  c4 = 5894147/5000000  (normalised),
  shift   t = (4 C2 - 2 C3)/(4 - 2 C2), the exact maximiser of t ↦ 1 - K_t/(2 (2 - t)²),
  bound   504678117694414992253315078804551328482467/598826272881181027171250673799386945725202 = 0.842778850143325...
-/

open MeasureTheory Complex
open scoped BigOperators Real

noncomputable section
namespace TMG

/-- the re-tuned quartic window -/
def W3 : Window := quarticWindow (-(14768021 / 10000000)) (5894147 / 5000000)
  (PolyAux.quartic_pos (by norm_num) (by norm_num) (by norm_num))

theorem C2_W3 : C2 W3 1 = 351240553143347815340 / 264473002873689770391 := by
  unfold W3
  rw [PolyAux.C2_quartic]
  unfold PolyAux.nI2 PolyAux.nJ2
  norm_num

theorem C3_W3 : C3 W3 1 = 2416827303744667025195108877690 / 1226275713494509017254406883391 := by
  unfold W3
  rw [PolyAux.C3_quartic]
  unfold PolyAux.nI3 PolyAux.nJ3
  norm_num

/-- the optimal shift for `W3` -/
def tStar : ℝ := 1260525325636730390103424989485 / 1235943999856661587815176497163

theorem record_value : (1 : ℝ) - Kt W3 tStar / (2 * (2 - tStar) ^ 2)
    = 504678117694414992253315078804551328482467 / 598826272881181027171250673799386945725202 := by
  unfold Kt tStar
  rw [C2_W3, C3_W3]
  norm_num

/-- **Distinct zeros on `(T, 2T]`:** `0.8427788501433...` -/
theorem record_distinct_dyadic (hRH : RiemannHypothesis) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      ((504678117694414992253315078804551328482467 : ℝ) / 598826272881181027171250673799386945725202 - ε) * (Zeta23.Ncount T (2 * T) : ℝ)
        ≤ (Zeta23.Ndist T (2 * T) : ℝ) := by
  have h := ThirdMoment.distinct_of_budget (t := tStar) (by unfold tStar; norm_num)
    (by unfold tStar; norm_num) (budget_dyadic hRH W3 (by unfold tStar; norm_num))
  rw [record_value] at h
  exact h

/-- **Distinct zeros on `(0, T]`.** -/
theorem record_distinct_cumulative (hRH : RiemannHypothesis) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      ((504678117694414992253315078804551328482467 : ℝ) / 598826272881181027171250673799386945725202 - ε) * (Zeta23.Ncount 0 T : ℝ)
        ≤ (Zeta23.Ndist 0 T : ℝ) := by
  have h := distinct_of_budgetCum (t := tStar) (by unfold tStar; norm_num)
    (by unfold tStar; norm_num) (theorem_1_1_cumulative hRH W3 (by unfold tStar; norm_num))
  rw [record_value] at h
  exact h

end TMG

end
end Src_TMG_Record
end Src_Devine_KnausgardTraceBase

section Src_Devine_ConditionalShiftedCubicSpacing
/-
Copyright (c) 2026 Michael Devine.
Released under the Apache 2.0 license.
SPDX-License-Identifier: Apache-2.0
-/




/-! Scalar parts of the spacing correction to Knausgård's W3 bound.
The full zeta-zero argument and the exact Fourier certificate are in T041-0074. -/
namespace Range5Zeros.ShiftedCubicSpacing

def cubic (t x : ℝ) : ℝ := x * (x - t)^2

/-- A repeated diagonal retains its off-diagonal variance. Apply this pointwise
to the spectral measure of a row with mean c. The linear term averages to zero. -/
theorem tangent_retains_variance {x t c : ℝ} (hx : 0 ≤ x) :
    cubic t c + ((c-t)*(3*c-t))*(x-c) + 2*(c-t)*(x-c)^2 ≤ cubic t x := by
  unfold cubic
  nlinarith [mul_nonneg hx (sq_nonneg (x-c))]

def exceptional (x : ℝ) : Prop :=
  (2099/2000 < x ∧ x < 1109/1000) ∨ (987/500 < x ∧ x < 1679/800) ∨ 293/100 < x

theorem gaps_not_all_exceptional {x y : ℝ} (hz : x + y ≤ 3)
    (hx : exceptional x) (hy : exceptional y) : ¬ exceptional (x + y) := by
  rcases hx with ⟨h1,h2⟩ | ⟨h1,h2⟩ | h1 <;>
    rcases hy with ⟨k1,k2⟩ | ⟨k1,k2⟩ | k1 <;>
    rintro (⟨j1,j2⟩ | ⟨j1,j2⟩ | j1) <;> linarith

def eta : ℚ := 49 / 2000
def shift : ℚ := 1260525325636730390103424989485 / 1235943999856661587815176497163
def leader : ℚ := 504678117694414992253315078804551328482467 / 598826272881181027171250673799386945725202
def pairGain : ℚ := (1 + eta) * (1 + eta - shift)^2
def b : ℚ := pairGain / (6 * (2-shift)^2)
def bound : ℚ := (leader - 2*b/3)/(1-b)

theorem pair_constants : 1 < shift ∧ shift < 1 + eta ∧ 1 + eta < 2 ∧
    pairGain < 4*(2-shift)*eta^2 ∧ 0 < b ∧ b < 1 := by
  norm_num [shift, eta, pairGain, b]

theorem score : leader < 842779515794 / (10^12 : ℚ) ∧
    842779515794 / (10^12 : ℚ) < bound := by
  norm_num [bound, leader, b, pairGain, eta, shift]

/-! The coefficient vector represents (1+z)^n times the signed Taylor
polynomial at (lo+hi*z)/(1+z), with the required floor and the uniform
error already subtracted. Endpoint z=infinity uses the leading coefficient. -/
namespace FourierCertificate

def c2 : ℚ := -(14768021 / 10000000)
def c4 : ℚ := 5894147 / 5000000
def piApprox : ℚ := 3141593 / 1000000

def coeff (k : ℕ) : ℚ :=
  if k % 2 = 0 then
    (-1 : ℚ)^(k/2) * piApprox^k *
      (1/(k+1 : ℚ) + c2/(4*(k+3 : ℚ)) + c4/(16*(k+5 : ℚ))) /
      ((1+c2/12+c4/80) * (k.factorial : ℚ))
  else 0

def linearMul (lo hi : ℚ) (xs : List ℚ) : List ℚ :=
  List.zipWith (· + ·) (xs.map (lo * ·) ++ [0]) (0 :: xs.map (hi * ·))

def coefficients (n : ℕ) (lo hi sign : ℚ) : List ℚ :=
  let cutoff := eta + hi/1000000 + (piApprox*hi)^(n+2) / ((n+2).factorial : ℚ)
  let a := fun k => sign * coeff k - (if k = 0 then cutoff else 0)
  let start : List ℚ × List ℚ := ([a n], [1])
  let (xs, _) := (List.range n).reverse.foldl (fun state k =>
    let base := linearMul 1 1 state.2
    (List.zipWith (fun x y => x + a k * y) (linearMul lo hi state.1) base, base)) start
  xs

def positive (n : ℕ) (lo hi sign : ℚ) : Bool :=
  (coefficients n lo hi sign).all (fun c => decide (0 < c))

theorem first_coefficients : positive 14 0 (2099/2000) 1 = true := by decide +kernel
theorem second_coefficients : positive 22 (1109/1000) (987/500) (-1) = true := by decide +kernel
theorem third_coefficients : positive 30 (1679/800) (293/100) 1 = true := by decide +kernel

end FourierCertificate

end Range5Zeros.ShiftedCubicSpacing
end Src_Devine_ConditionalShiftedCubicSpacing

section Src_Devine_ConditionalShiftedCubicIntervals
/-
Copyright (c) 2026 Michael Devine.
Released under the Apache 2.0 license.
SPDX-License-Identifier: Apache-2.0
-/





open scoped BigOperators
namespace Range5Zeros.ShiftedCubicSpacing.FourierCertificate

def heval (u v : ℝ) : List ℚ → ℝ
  | [] => 0
  | a::as => (a:ℝ)*u^as.length + v*heval u v as

private theorem map_eval (u v : ℝ) (k : ℚ) (xs : List ℚ) :
    heval u v (xs.map (k * ·)) = (k:ℝ)*heval u v xs := by
  induction xs with
  | nil => simp [heval]
  | cons a xs ih => simp [heval, ih]; ring

private theorem pad_eval (u v : ℝ) (xs : List ℚ) :
    heval u v (xs ++ [0]) = u * heval u v xs := by
  induction xs with
  | nil => simp [heval]
  | cons a xs ih => simp [heval, ih, pow_succ]; ring

private theorem zip_eval (u v : ℝ) (k : ℚ) (xs ys : List ℚ)
    (h : xs.length = ys.length) :
    heval u v (List.zipWith (fun a b => a+k*b) xs ys) =
    heval u v xs + (k:ℝ)*heval u v ys := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp_all [heval]
  | cons a xs ih =>
    cases ys with
    | nil => simp at h
    | cons b ys =>
      have h' : xs.length = ys.length := by simpa using h
      simp [heval, ih ys h', h']; ring

private theorem linear_len (l h : ℚ) (xs : List ℚ) :
    (linearMul l h xs).length = xs.length + 1 := by simp [linearMul]

private theorem linear_eval (u v : ℝ) (l h : ℚ) (xs : List ℚ) :
    heval u v (linearMul l h xs) = ((l:ℝ)*u+(h:ℝ)*v)*heval u v xs := by
  have eqn := zip_eval u v 1 ((xs.map (l * ·)) ++ [0]) (0 :: xs.map (h * ·)) (by simp)
  simp only [one_mul, Rat.cast_one] at eqn
  unfold linearMul
  rw [eqn, pad_eval, map_eval]
  simp [heval, map_eval]; ring

private theorem eval_nonneg (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (xs : List ℚ) (hp : ∀ x ∈ xs, 0 ≤ x) : 0 ≤ heval u v xs := by
  induction xs with
  | nil => simp [heval]
  | cons x xs ih =>
    have hx : (0:ℝ) ≤ x := by exact_mod_cast hp x (by simp)
    exact add_nonneg (mul_nonneg hx (pow_nonneg hu _))
      (mul_nonneg hv (ih fun y hy => hp y (by simp [hy])))


private def advance (l h : ℚ) (a : ℕ → ℚ) (state : List ℚ × List ℚ) (k : ℕ) :=
  let base := linearMul 1 1 state.2
  (List.zipWith (fun x y => x + a k * y) (linearMul l h state.1) base, base)

private theorem fold_eval (u v : ℝ) (uv : u+v=1) (l h : ℚ) (a : ℕ → ℚ)
    (ks : List ℕ) (state : List ℚ × List ℚ)
    (hlen : state.1.length = state.2.length) (hbase : heval u v state.2 = 1) :
    heval u v (ks.foldl (advance l h a) state).1 =
      ks.foldl (fun val k => ((l:ℝ)*u+(h:ℝ)*v)*val + (a k:ℝ)) (heval u v state.1) := by
  induction ks generalizing state with
  | nil => rfl
  | cons k ks ih =>
    have h1 : heval u v (linearMul 1 1 state.2) = 1 := by
      simp [linear_eval, hbase, uv]
    have hlen' : (linearMul l h state.1).length = (linearMul 1 1 state.2).length := by
      simp [linear_len, hlen]
    have h2 : (advance l h a state k).1.length = (advance l h a state k).2.length := by
      simp [advance, hlen']
    simp only [List.foldl_cons]
    rw [ih _ h2 h1]
    congr 1
    simp [advance, zip_eval _ _ _ _ _ hlen', linear_eval, hbase, uv]

private theorem horner_sum (x : ℝ) (a : ℕ → ℚ) (n : ℕ) (y : ℝ) :
    (List.range n).reverse.foldl (fun val k => x*val+(a k:ℝ)) y =
      x^n*y + ∑ k ∈ Finset.range n, x^k*(a k:ℝ) := by
  induction n generalizing y with
  | zero => simp
  | succ n ih =>
    simp [List.range_succ, ih, Finset.sum_range_succ, pow_succ]
    ring

def taylorValue (n : ℕ) (x : ℝ) := ∑ k ∈ Finset.range (n+1), x^k*(coeff k:ℝ)
def errorBound (n : ℕ) (hi : ℚ) := hi/1000000 + (piApprox*hi)^(n+2) / ((n+2).factorial : ℚ)

theorem checked_interval {n : ℕ} {l h sign : ℚ} (ok : positive n l h sign = true)
    {x : ℝ} (lh : l < h) (xl : (l:ℝ) ≤ x) (xh : x ≤ (h:ℝ)) :
    (eta:ℝ) + (errorBound n h:ℝ) ≤ (sign:ℝ) * taylorValue n x := by
  let u := ((h:ℝ)-x)/((h:ℝ)-l)
  let v := (x-(l:ℝ))/((h:ℝ)-l)
  have den : (0:ℝ) < (h:ℝ)-l := sub_pos.mpr (by exact_mod_cast lh)
  have hu : 0 ≤ u := div_nonneg (sub_nonneg.mpr xh) den.le
  have hv : 0 ≤ v := div_nonneg (sub_nonneg.mpr xl) den.le
  have uv : u+v=1 := by dsimp [u,v]; field_simp; ring
  have loc : (l:ℝ)*u+(h:ℝ)*v=x := by dsimp [u,v]; field_simp; ring
  let cut : ℚ := eta + h/1000000 + (piApprox*h)^(n+2) / ((n+2).factorial : ℚ)
  let a := fun k => sign*coeff k - (if k=0 then cut else 0)
  let arr := coefficients n l h sign
  have nonneg : 0 ≤ heval u v arr := eval_nonneg _ _ hu hv _ (by
    intro y hy
    exact le_of_lt (of_decide_eq_true (List.all_eq_true.mp ok y hy)))
  have ev := fold_eval u v uv l h a (List.range n).reverse ([a n],[1]) rfl (by simp [heval])
  change heval u v arr = _ at ev
  rw [ev, loc] at nonneg
  simp only [heval, List.length_nil, pow_zero, mul_one, mul_zero, add_zero] at nonneg
  rw [horner_sum] at nonneg
  have combined : 0 ≤ ∑ k ∈ Finset.range (n+1), x^k*(a k:ℝ) := by
    rw [Finset.sum_range_succ]; linarith
  simp only [a, Rat.cast_sub, Rat.cast_mul, apply_ite (fun q : ℚ => (q:ℝ)),
    Rat.cast_zero, mul_sub, Finset.sum_sub_distrib, mul_ite, mul_zero] at combined
  simp only [Finset.sum_ite_eq', Finset.mem_range, Nat.zero_lt_succ, if_true,
    pow_zero, one_mul] at combined
  dsimp [taylorValue]
  rw [Finset.mul_sum]
  simp only [mul_left_comm (sign:ℝ)]
  simpa [cut, errorBound, add_assoc] using (sub_nonneg.mp combined)

theorem first_interval {x : ℝ} (hx : 0 ≤ x) (hu : x ≤ 2099/2000) :
    (eta:ℝ) + errorBound 14 (2099/2000) ≤ taylorValue 14 x := by
  simpa using checked_interval first_coefficients (x := x) (by norm_num) (by simpa using hx) (by simpa using hu)

theorem second_interval {x : ℝ} (hl : 1109/1000 ≤ x) (hu : x ≤ 987/500) :
    (eta:ℝ) + errorBound 22 (987/500) ≤ -taylorValue 22 x := by
  simpa using checked_interval second_coefficients (x := x) (by norm_num) (by simpa using hl) (by simpa using hu)

theorem third_interval {x : ℝ} (hl : 1679/800 ≤ x) (hu : x ≤ 293/100) :
    (eta:ℝ) + errorBound 30 (293/100) ≤ taylorValue 30 x := by
  simpa using checked_interval third_coefficients (x := x) (by norm_num) (by simpa using hl) (by simpa using hu)

/-- Convert the analytic remainder on each of the three intervals into
the pair overlap needed in the finite Gram inequality. -/
theorem triple_overlap (F : ℝ → ℝ)
    (h₁ : ∀ x : ℝ, 0 ≤ x → x ≤ 2099/2000 →
      |F x - taylorValue 14 x| ≤ errorBound 14 (2099/2000))
    (h₂ : ∀ x : ℝ, 1109/1000 ≤ x → x ≤ 987/500 →
      |F x - taylorValue 22 x| ≤ errorBound 22 (987/500))
    (h₃ : ∀ x : ℝ, 1679/800 ≤ x → x ≤ 293/100 →
      |F x - taylorValue 30 x| ≤ errorBound 30 (293/100))
    {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : x+y ≤ 3) :
    (eta:ℝ) ≤ |F x| ∨ (eta:ℝ) ≤ |F y| ∨ (eta:ℝ) ≤ |F (x+y)| := by
  have bad (s : ℝ) (hs : 0 ≤ s) (h : |F s| < (eta:ℝ)) : exceptional s := by
    have low := (abs_lt.mp h).1
    have high := (abs_lt.mp h).2
    by_cases h0 : s ≤ 2099/2000
    · have ⟨hl,_⟩ := abs_le.mp (h₁ s hs h0)
      linarith [first_interval hs h0]
    by_cases h1 : s < 1109/1000
    · exact Or.inl ⟨lt_of_not_ge h0,h1⟩
    by_cases h2 : s ≤ 987/500
    · have ⟨_,hu⟩ := abs_le.mp (h₂ s (le_of_not_gt h1) h2)
      linarith [second_interval (le_of_not_gt h1) h2]
    by_cases h3 : s < 1679/800
    · exact Or.inr (Or.inl ⟨lt_of_not_ge h2,h3⟩)
    by_cases h4 : s ≤ 293/100
    · have ⟨hl,_⟩ := abs_le.mp (h₃ s (le_of_not_gt h3) h4)
      linarith [third_interval (le_of_not_gt h3) h4]
    exact Or.inr (Or.inr (lt_of_not_ge h4))
  by_contra! h
  exact gaps_not_all_exceptional hz (bad x hx h.1) (bad y hy h.2.1)
    (bad (x+y) (add_nonneg hx hy) h.2.2)

end Range5Zeros.ShiftedCubicSpacing.FourierCertificate
end Src_Devine_ConditionalShiftedCubicIntervals

section Src_Devine_ConditionalShiftedCubicFourier







/-! Remainder bounds for the quartic-window Fourier certificate of T041-0074. -/

noncomputable section
open Set
namespace Range5Zeros.ShiftedCubicSpacing.FourierCertificate

def cosCoeff (k : ℕ) : ℝ :=
  if k % 2 = 0 then (-1 : ℝ)^(k/2) / k.factorial else 0

def cosPoly (n : ℕ) (y : ℝ) := ∑ k ∈ Finset.range (n+1), y^k * cosCoeff k

private theorem cos_coeff_deriv (k : ℕ) :
    iteratedDeriv k Real.cos 0 / k.factorial = cosCoeff k := by
  by_cases even : k % 2 = 0
  · rw [cosCoeff, if_pos even]
    conv_lhs => arg 1; rw [show k = 2*(k/2) by omega, Real.iteratedDeriv_even_cos]
    simp
  · rw [cosCoeff, if_neg even]
    conv_lhs => arg 1; rw [show k = 2*(k/2)+1 by omega, Real.iteratedDeriv_odd_cos]
    simp

theorem cosPoly_remainder (n : ℕ) (hn : n % 2 = 0) (y : ℝ) :
    |Real.cos y - cosPoly n y| ≤ |y|^(n+2) / (n+2).factorial := by
  by_cases hy : 0 = y
  · subst y
    have h0 : cosPoly n 0 = 1 := by
      unfold cosPoly
      rw [Finset.sum_eq_single 0]
      · norm_num [cosCoeff]
      · intro k _ hk; simp [zero_pow hk]
      · simp
    simp [h0]
  have hp : taylorWithinEval Real.cos (n+1) (uIcc 0 y) 0 y = cosPoly n y := by
    rw [taylor_within_apply]
    simp only [sub_zero, smul_eq_mul]
    have term (k : ℕ) :
        ((k.factorial : ℝ)⁻¹ * y^k) * iteratedDerivWithin k Real.cos (uIcc 0 y) 0 =
          y^k * cosCoeff k := by
      rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_uIcc hy)
        Real.contDiff_cos.contDiffAt left_mem_uIcc, ← cos_coeff_deriv]
      ring
    simp_rw [term]
    rw [Finset.sum_range_succ, cosPoly]
    simp [cosCoeff, show (n+1)%2 ≠ 0 by omega]
  obtain ⟨z, _, hz⟩ := taylor_mean_remainder_lagrange_iteratedDeriv
    (n := n+1) hy Real.contDiff_cos.contDiffOn
  rw [hp, sub_zero] at hz
  rw [hz, abs_div, abs_mul, abs_pow, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) (n+2).factorial)]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  simpa using (mul_le_mul_of_nonneg_right (Real.abs_iteratedDeriv_cos_le_one (n+2) z)
    (pow_nonneg (abs_nonneg y) (n+2)))

theorem pointwise_fourier_remainder (n : ℕ) (hn : n % 2 = 0)
    {s h u : ℝ} (hs : 0 ≤ s) (sh : s ≤ h) (hu : |u| ≤ 1/2) :
    |Real.cos (2*Real.pi*s*u) - cosPoly n (2*(piApprox:ℝ)*s*u)| ≤
      h/1000000 + ((piApprox:ℝ)*h)^(n+2)/(n+2).factorial := by
  have hp : (0:ℝ) ≤ piApprox := by norm_num [piApprox]
  have delta : |Real.pi - (piApprox:ℝ)| ≤ 1/1000000 := by
    rw [abs_le]; norm_num [piApprox]; constructor <;> linarith [Real.pi_gt_d6, Real.pi_lt_d6]
  have hs' : |s| = s := abs_of_nonneg hs
  have hu' : |2*u| ≤ 1 := by rw [abs_mul]; norm_num; linarith
  have arg (a : ℝ) : |2*a*s*u| ≤ |a| *h := by
    rw [show 2*a*s*u = (a*s)*(2*u) by ring, abs_mul, abs_mul, hs']
    calc
      _ ≤ (|a| *s)*1 := mul_le_mul_of_nonneg_left hu' (mul_nonneg (abs_nonneg _) hs)
      _ ≤ _ := by simpa using mul_le_mul_of_nonneg_left sh (abs_nonneg a)
  have d := (Real.abs_cos_sub_cos_le (2*Real.pi*s*u) (2*(piApprox:ℝ)*s*u)).trans
    (c := 1/1000000*h) (by
      rw [show 2*Real.pi*s*u - 2*(piApprox:ℝ)*s*u = 2*(Real.pi-(piApprox:ℝ))*s*u by ring]
      exact (arg _).trans (mul_le_mul_of_nonneg_right delta (hs.trans sh)))
  have a := arg (piApprox:ℝ)
  rw [abs_of_nonneg hp] at a
  refine (abs_sub_le _ (Real.cos (2*(piApprox:ℝ)*s*u)) _).trans ?_
  exact add_le_add (by linarith only [d]) ((cosPoly_remainder n hn _).trans
    (div_le_div_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg _) a _) (Nat.cast_nonneg _)))

def weight (u : ℝ) := (1 + (c2:ℝ)*u^2 + (c4:ℝ)*u^4) / (1 + (c2:ℝ)/12 + (c4:ℝ)/80)

theorem weight_continuous : Continuous weight := by unfold weight; fun_prop

private theorem scaled_even_moment (k : ℕ) (hk : k%2=0) :
    (∫ u in (-(1/2:ℝ))..(1/2), (2*u)^k) = 1/(k+1:ℝ) := by
  have h := intervalIntegral.mul_integral_comp_mul_left (a := -(1/2:ℝ)) (b := 1/2)
    (f := fun v => v^k) 2
  norm_num only [show (2:ℝ)* -(1/2) = -1 by norm_num, show (2:ℝ)*(1/2)=1 by norm_num,
    integral_pow, one_pow] at h
  have powneg : (-1:ℝ)^(k+1) = -1 := by
    rw [pow_succ, show k=2*(k/2) by omega, pow_mul]; norm_num
  rw [powneg] at h
  simp only [div_eq_mul_inv] at h ⊢
  linarith

private theorem weight_moment (k : ℕ) (hk : k%2=0) :
    (∫ u in (-(1/2:ℝ))..(1/2), weight u*(2*u)^k) =
      (1/(k+1:ℝ) + (c2:ℝ)/(4*(k+3:ℝ)) + (c4:ℝ)/(16*(k+5:ℝ))) /
        (1+(c2:ℝ)/12+(c4:ℝ)/80) := by
  let z : ℝ := 1+(c2:ℝ)/12+(c4:ℝ)/80
  have expand (u : ℝ) : weight u*(2*u)^k =
      (1/z)*(2*u)^k + ((c2:ℝ)/(4*z))*(2*u)^(k+2) + ((c4:ℝ)/(16*z))*(2*u)^(k+4) := by
    dsimp only [weight, z]
    rw [pow_add, pow_add]; simp only [div_eq_mul_inv, mul_inv_rev]; ring
  have cont (a : ℝ) (j : ℕ) : Continuous (fun u : ℝ => a*(2*u)^j) := by fun_prop
  simp_rw [expand]
  have hsum : Continuous (fun u : ℝ =>
      1/z * (2*u)^k + ((c2:ℝ)/(4*z))*(2*u)^(k+2)) := by fun_prop
  rw [intervalIntegral.integral_add (hsum.intervalIntegrable _ _) ((cont _ _).intervalIntegrable _ _),
      intervalIntegral.integral_add ((cont _ _).intervalIntegrable _ _) ((cont _ _).intervalIntegrable _ _)]
  simp only [intervalIntegral.integral_const_mul, scaled_even_moment k hk,
    scaled_even_moment (k+2) (by omega), scaled_even_moment (k+4) (by omega),
    Nat.cast_add, Nat.cast_ofNat]
  dsimp only [z]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

theorem integrated_cosPoly (n : ℕ) (s : ℝ) :
    (∫ u in (-(1/2:ℝ))..(1/2), weight u * cosPoly n (2*(piApprox:ℝ)*s*u)) = taylorValue n s := by
  let a (k : ℕ) := ((piApprox:ℝ)*s)^k*cosCoeff k
  have expand (u : ℝ) : weight u * cosPoly n (2*(piApprox:ℝ)*s*u) =
      ∑ k ∈ Finset.range (n+1), a k * (weight u * (2*u)^k) := by
    unfold cosPoly
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    dsimp [a]
    rw [show 2*(piApprox:ℝ)*s*u = ((piApprox:ℝ)*s)*(2*u) by ring, mul_pow]
    ring
  simp_rw [expand]
  rw [intervalIntegral.integral_finsetSum (fun k _ => Continuous.intervalIntegrable
    (by unfold weight; fun_prop) _ _)]
  apply Finset.sum_congr rfl
  intro k _
  rw [intervalIntegral.integral_const_mul]
  by_cases hk : k%2=0
  · rw [weight_moment k hk]
    simp [a, cosCoeff, coeff, hk, mul_pow, div_eq_mul_inv, mul_inv_rev]
    ring
  · simp [a, cosCoeff, coeff, hk]

theorem weight_nonneg {u : ℝ} (hu : |u| ≤ 1/2) : 0 ≤ weight u := by
  have hu2 : u^2 ≤ 1/4 := by nlinarith [sq_abs u, mul_self_le_mul_self (abs_nonneg u) hu]
  unfold weight
  apply div_nonneg
  · norm_num [c2, c4]
    nlinarith [sq_nonneg (u^2)]
  · norm_num [c2, c4]

theorem weight_mass : (∫ u in (-(1/2:ℝ))..(1/2), weight u) = 1 := by
  have h := weight_moment 0 (by decide)
  norm_num [c2, c4] at h
  exact h

def fourierReal (s : ℝ) := ∫ u in (-(1/2:ℝ))..(1/2), weight u * Real.cos (2*Real.pi*s*u)

theorem fourier_error (n : ℕ) (hn : n%2=0) {s : ℝ} {hi : ℚ}
    (hs : 0 ≤ s) (sh : s ≤ (hi:ℝ)) :
    |fourierReal s - taylorValue n s| ≤ (errorBound n hi:ℝ) := by
  let C : ℝ := (hi:ℝ)/1000000 + ((piApprox:ℝ)*hi)^(n+2)/(n+2).factorial
  let f (u : ℝ) := weight u * Real.cos (2*Real.pi*s*u)
  let g (u : ℝ) := weight u * cosPoly n (2*(piApprox:ℝ)*s*u)
  have cf : Continuous f := by unfold f weight; fun_prop
  have cg : Continuous g := by unfold g weight cosPoly; fun_prop
  have hab : -(1/2:ℝ) ≤ 1/2 := by norm_num
  have mono : (∫ u in (-(1/2:ℝ))..(1/2), |f u-g u|) ≤
      ∫ u in (-(1/2:ℝ))..(1/2), weight u*C := by
    apply intervalIntegral.integral_mono_on hab ((cf.sub cg).abs.intervalIntegrable _ _)
      ((weight_continuous.mul continuous_const).intervalIntegrable _ _)
    intro u hu
    have hu' := abs_le.mpr hu
    change |weight u * _ - weight u * _| ≤ _
    rw [← mul_sub, abs_mul, abs_of_nonneg (weight_nonneg hu')]
    exact mul_le_mul_of_nonneg_left (pointwise_fourier_remainder n hn hs sh hu') (weight_nonneg hu')
  change |(∫ u in (-(1/2:ℝ))..(1/2), f u) - taylorValue n s| ≤ _
  rw [← integrated_cosPoly]
  change |(∫ u in (-(1/2:ℝ))..(1/2), f u) - (∫ u in (-(1/2:ℝ))..(1/2), g u)| ≤ _
  rw [← intervalIntegral.integral_sub (cf.intervalIntegrable _ _) (cg.intervalIntegrable _ _)]
  refine (intervalIntegral.abs_integral_le_integral_abs hab).trans (mono.trans_eq ?_)
  rw [intervalIntegral.integral_mul_const, weight_mass, one_mul]
  simp [C, errorBound]

/-- The real part of the normalized quartic transform has a large absolute
value on at least one of the three pair separations. -/
theorem fourier_triple {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : x+y ≤ 3) :
    (eta:ℝ) ≤ |fourierReal x| ∨ (eta:ℝ) ≤ |fourierReal y| ∨ (eta:ℝ) ≤ |fourierReal (x+y)| := by
  apply triple_overlap _ _ _ _ hx hy hz
  · intro s hs hu; exact fourier_error 14 (by decide) hs (by simpa using hu)
  · intro s hs hu; exact fourier_error 22 (by decide) (by linarith) (by simpa using hu)
  · intro s hs hu; exact fourier_error 30 (by decide) (by linarith) (by simpa using hu)

open MeasureTheory

/-- Same sign and angular-frequency convention as Knausgaard's `TMG.ghat`. -/
def quarticTransform (a : ℝ) : ℂ :=
  ∫ u : ℝ, ((if |u| ≤ 1/2 then weight u else 0 : ℝ) : ℂ) *
    Complex.exp (Complex.I * (a:ℂ) * (u:ℂ))

theorem quarticTransform_re (s : ℝ) : (quarticTransform (2*Real.pi*s)).re = fourierReal s := by
  let S := Icc (-(1/2:ℝ)) (1/2)
  let f (u : ℝ) : ℂ := (weight u:ℂ) * Complex.exp (Complex.I * ((2*Real.pi*s:ℝ):ℂ) * (u:ℂ))
  have cf : Continuous f := by unfold f weight; fun_prop
  have cut (u : ℝ) : ((if |u| ≤ 1/2 then weight u else 0 : ℝ) : ℂ) *
      Complex.exp (Complex.I * ((2*Real.pi*s:ℝ):ℂ) * (u:ℂ)) = S.indicator f u := by
    by_cases h : |u| ≤ 1/2
    · rw [if_pos h, indicator_of_mem (show u ∈ S from abs_le.mp h)]
    · rw [if_neg h, indicator_of_notMem (show u ∉ S from fun hm => h (abs_le.mpr hm))]; simp
  unfold quarticTransform
  simp_rw [cut]
  rw [integral_indicator (show MeasurableSet S from measurableSet_Icc)]
  change RCLike.re (∫ u in S, f u) = _
  rw [← integral_re (cf.continuousOn.integrableOn_compact isCompact_Icc)]
  have hre (u : ℝ) : RCLike.re (f u) = weight u * Real.cos (2*Real.pi*s*u) := by
    change ((weight u:ℂ) * Complex.exp _).re = _
    rw [show Complex.I * ((2*Real.pi*s:ℝ):ℂ) * (u:ℂ) = ((2*Real.pi*s*u:ℝ):ℂ)*Complex.I by push_cast; ring]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, Complex.exp_ofReal_mul_I_re]
  simp_rw [hre]
  exact (integral_Icc_eq_integral_Ioc.trans (intervalIntegral.integral_of_le (by norm_num)).symm)

theorem complex_triple {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : x+y ≤ 3) :
    (eta:ℝ) ≤ ‖quarticTransform (2*Real.pi*x)‖ ∨
    (eta:ℝ) ≤ ‖quarticTransform (2*Real.pi*y)‖ ∨
    (eta:ℝ) ≤ ‖quarticTransform (2*Real.pi*(x+y))‖ := by
  have h (s : ℝ) : |fourierReal s| ≤ ‖quarticTransform (2*Real.pi*s)‖ := by
    rw [← quarticTransform_re]; exact Complex.abs_re_le_norm _
  rcases fourier_triple hx hy hz with a | a | a
  · exact Or.inl (a.trans (h x))
  · exact Or.inr (Or.inl (a.trans (h y)))
  · exact Or.inr (Or.inr (a.trans (h (x+y))))

end Range5Zeros.ShiftedCubicSpacing.FourierCertificate
end
end Src_Devine_ConditionalShiftedCubicFourier

section Src_Devine_ConditionalShiftedCubicPacking




/-! Selecting disjoint pairs from an ordered list of distinct ordinates. -/
noncomputable section
namespace Range5Zeros.ShiftedCubicSpacing
open FourierCertificate

private theorem sum_spans (v : ℕ → ℝ) (m : ℕ) :
    ∑ i ∈ Finset.range m, (v (i+2) - v i) = v m + v (m+1) - v 0 - v 1 := by
  induction m with
  | zero => simp
  | succ m ih => rw [Finset.sum_range_succ, ih]; ring

/-- There are `m+2` ordinates, numbered `0,...,m+1`, in an interval of
length `L`. One residue class of short triples already gives the required
number of pairwise disjoint triples. -/
theorem pack_short_triples (v : ℕ → ℝ) (m : ℕ) (hv : Monotone v) {L : ℝ}
    (hL : v (m+1) - v 0 ≤ L) :
    ∃ starts : Finset ℕ, (m:ℝ) - 2*L/3 ≤ 3*starts.card ∧
      (∀ i ∈ starts, i < m ∧ v (i+2) - v i ≤ 3) ∧
      ∀ i ∈ starts, ∀ j ∈ starts, i < j → i+2 < j := by
  classical
  let all := Finset.range m
  let good := all.filter (fun i => v (i+2)-v i ≤ 3)
  let bad := all \ good
  have hbad : (3:ℝ)*bad.card ≤ ∑ i ∈ all, (v (i+2)-v i) := by
    calc
      _ = ∑ _ ∈ bad, (3:ℝ) := by simp; ring
      _ ≤ ∑ i ∈ bad, (v (i+2)-v i) := by
        apply Finset.sum_le_sum
        intro i hi
        obtain ⟨hi, hn⟩ := Finset.mem_sdiff.mp hi
        exact le_of_not_ge (fun h => hn (Finset.mem_filter.mpr ⟨hi,h⟩))
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset
        (fun i _ _ => sub_nonneg.mpr (hv (by omega)))
  rw [show all = Finset.range m from rfl, sum_spans] at hbad
  have hcard : bad.card + good.card = m := by
    simpa [good,bad,all] using Finset.card_sdiff_add_card_eq_card (Finset.filter_subset _ all :
      good ⊆ all)
  let fiber (r : ℕ) := good.filter (fun i => i%3 = r)
  obtain ⟨r, hr, hmax⟩ := (Finset.range 3).exists_max_image (fun r => (fiber r).card) (by decide)
  have partition : good.card = ∑ j ∈ Finset.range 3, (fiber j).card :=
    Finset.card_eq_sum_card_fiberwise (fun i _ => Finset.mem_range.mpr (Nat.mod_lt i (by decide)))
  have largest : good.card ≤ 3*(fiber r).card := by
    rw [partition]
    simpa using Finset.sum_le_sum (s := Finset.range 3) (f := fun j => (fiber j).card)
      (g := fun _ => (fiber r).card) hmax
  refine ⟨fiber r, ?_, ?_, ?_⟩
  · have cm : (bad.card:ℝ) + good.card = m := by exact_mod_cast hcard
    have cr : (good.card:ℝ) ≤ 3*(fiber r).card := by exact_mod_cast largest
    linarith [hbad, hv (show m ≤ m+1 by omega), hv (show 0 ≤ 1 by decide)]
  · intro i hi
    obtain ⟨hgood,_⟩ := Finset.mem_filter.mp hi
    obtain ⟨hm,hspan⟩ := Finset.mem_filter.mp hgood
    exact ⟨Finset.mem_range.mp hm,hspan⟩
  · intro i hi j hj hij
    have h1 := (Finset.mem_filter.mp hi).2
    have h2 := (Finset.mem_filter.mp hj).2
    omega

/-- Each selected short triple supplies two distinct endpoints whose
absolute real Fourier overlap reaches the threshold used in the trace proof. -/
theorem select_pairs (v : ℕ → ℝ) (m : ℕ) (hv : Monotone v) {L : ℝ}
    (hL : v (m+1) - v 0 ≤ L) :
    ∃ (starts : Finset ℕ) (p q : ℕ → ℕ),
      (m:ℝ) - 2*L/3 ≤ 3*starts.card ∧
      (∀ i ∈ starts, i ≤ p i ∧ p i < q i ∧ q i ≤ i+2 ∧ q i < m+2 ∧
        (eta:ℝ) ≤ |fourierReal (v (q i)-v (p i))|) ∧
      ∀ i ∈ starts, ∀ j ∈ starts, i < j → q i < p j := by
  classical
  obtain ⟨s, hcard, hshort, hdis⟩ := pack_short_triples v m hv hL
  let P (i a b : ℕ) := i ≤ a ∧ a < b ∧ b ≤ i+2 ∧ b < m+2 ∧
        (eta:ℝ) ≤ |fourierReal (v b-v a)|
  have pair : ∀ i, ∃ a b, i ∈ s → P i a b := by
    intro i
    by_cases hi : i ∈ s
    · obtain ⟨him, hspan⟩ := hshort i hi
      have x := sub_nonneg.mpr (hv (show i ≤ i+1 by omega))
      have y := sub_nonneg.mpr (hv (show i+1 ≤ i+2 by omega))
      have h := fourier_triple x y (by linarith)
      rw [show v (i+1)-v i + (v (i+2)-v (i+1)) = v (i+2)-v i by ring] at h
      rcases h with he | he | he
      · exact ⟨i,i+1,fun _ => ⟨by omega,by omega,by omega,by omega,he⟩⟩
      · exact ⟨i+1,i+2,fun _ => ⟨by omega,by omega,by omega,by omega,he⟩⟩
      · exact ⟨i,i+2,fun _ => ⟨by omega,by omega,by omega,by omega,he⟩⟩
    · exact ⟨0,0,fun h => (hi h).elim⟩
  choose p q hpq using pair
  refine ⟨s,p,q,hcard,hpq,?_⟩
  intro i hi j hj hij
  exact lt_of_le_of_lt (hpq i hi).2.2.1 ((hdis i hi j hj hij).trans_le (hpq j hj).1)

/-- Finite-window version, including empty and singleton windows. The
endpoints are ordinates in the supplied set, and different pairs are ordered. -/
theorem pack_window (S : Finset ℝ) {a b : ℝ} (hab : a ≤ b)
    (hS : ∀ x ∈ S, a ≤ x ∧ x ≤ b) :
    ∃ (starts : Finset ℕ) (p q : ℕ → ℝ),
      (S.card:ℝ) - 2 - 2*(b-a)/3 ≤ 3*starts.card ∧
      (∀ i ∈ starts, p i ∈ S ∧ q i ∈ S ∧ p i < q i ∧
        (eta:ℝ) ≤ |fourierReal (q i-p i)|) ∧
      ∀ i ∈ starts, ∀ j ∈ starts, i < j → q i < p j := by
  classical
  by_cases hsmall : S.card < 2
  · refine ⟨∅,fun _ => 0,fun _ => 0,?_,by simp,by simp⟩
    have h : (S.card:ℝ) ≤ 1 := by exact_mod_cast (show S.card ≤ 1 by omega)
    simp only [Finset.card_empty, Nat.cast_zero, mul_zero]
    linarith
  let m := S.card - 2
  have hm : S.card = m+2 := by dsimp [m]; omega
  let index (i : ℕ) : Fin (m+2) := ⟨min i (m+1),by omega⟩
  let v (i : ℕ) := S.orderEmbOfFin hm (index i)
  have mem (i : ℕ) : v i ∈ S := S.orderEmbOfFin_mem hm _
  have mono : Monotone v := fun i j hij =>
    (S.orderEmbOfFin hm).monotone (show min i (m+1) ≤ min j (m+1) from min_le_min_right _ hij)
  have strict {i j : ℕ} (hij : i < j) (hj : j < m+2) : v i < v j := by
    apply (S.orderEmbOfFin hm).strictMono
    change min i (m+1) < min j (m+1)
    omega
  obtain ⟨s,p,q,hc,hpq,hd⟩ := select_pairs v m mono
    (L := b-a) (by linarith [(hS _ (mem 0)).1, (hS _ (mem (m+1))).2])
  refine ⟨s,v ∘ p,v ∘ q,?_,?_,?_⟩
  · rw [hm, Nat.cast_add, Nat.cast_ofNat]; linarith
  · intro i hi
    obtain ⟨_,hp,_,hq,he⟩ := hpq i hi
    exact ⟨mem _,mem _,strict hp hq,he⟩
  · intro i hi j hj hij
    obtain ⟨_,hp,_,hq,_⟩ := hpq j hj
    exact strict (hd i hi j hj hij) (hp.trans hq)

end Range5Zeros.ShiftedCubicSpacing
end
end Src_Devine_ConditionalShiftedCubicPacking

section Src_Devine_ConditionalShiftedCubicZeroPairs



/-! The disjoint pairs in T041-0074 come from actual nontrivial zeros. -/
noncomputable section
namespace Range5Zeros.ShiftedCubicSpacing
open FourierCertificate

/-- With normalization `k = σ log T / (2π)`, the width is `k*T`. RH makes
the scaled ordinate map injective on the distinct complex zeros. -/
theorem dyadic_zero_pairs (hRH : RiemannHypothesis) {T k : ℝ} (hT : 0 ≤ T) (hk : 0 < k) :
    ∃ (s : Finset ℕ) (p q : ℕ → ℂ),
      (Zeta23.Ndist T (2*T):ℝ) - 2 - 2*(k*T)/3 ≤ 3*s.card ∧
      (∀ i ∈ s, p i ∈ Zeta23.zerosIn T (2*T) ∧ q i ∈ Zeta23.zerosIn T (2*T) ∧
        (p i).im < (q i).im ∧ (eta:ℝ) ≤ |fourierReal (k*((q i).im-(p i).im))|) ∧
      ∀ i ∈ s, ∀ j ∈ s, i < j → (q i).im < (p j).im := by
  classical
  let Z := (Zeta23.zerosIn_finite T (2*T)).toFinset
  let S := Z.image (fun ρ : ℂ => k*ρ.im)
  have zm {ρ : ℂ} : ρ ∈ Z ↔ ρ ∈ Zeta23.zerosIn T (2*T) := Set.Finite.mem_toFinset _
  have inj : Set.InjOn (fun ρ : ℂ => k*ρ.im) Z := by
    intro ρ hr τ ht he
    exact Complex.ext ((Zeta23.RH_implies_on_line hRH (zm.mp hr).1).trans
      (Zeta23.RH_implies_on_line hRH (zm.mp ht).1).symm) (mul_left_cancel₀ hk.ne' he)
  have card : S.card = Zeta23.Ndist T (2*T) := by
    rw [show S.card = Z.card from Finset.card_image_of_injOn inj]
    exact (Set.ncard_eq_toFinset_card _ (Zeta23.zerosIn_finite T (2*T))).symm
  have bounds : ∀ u ∈ S, k*T ≤ u ∧ u ≤ k*(2*T) := by
    intro u hu
    obtain ⟨ρ,hm,rfl⟩ := Finset.mem_image.mp hu
    exact ⟨mul_le_mul_of_nonneg_left (zm.mp hm).2.1.le hk.le,
      mul_le_mul_of_nonneg_left (zm.mp hm).2.2 hk.le⟩
  obtain ⟨s,P,Q,hc,hpq,hd⟩ := pack_window S (by nlinarith : k*T ≤ k*(2*T)) bounds
  let z (u : ℝ) : ℂ := ⟨1/2,u/k⟩
  have lift {u : ℝ} (hu : u ∈ S) : z u ∈ Zeta23.zerosIn T (2*T) := by
    obtain ⟨ρ,hm,rfl⟩ := Finset.mem_image.mp hu
    have he : z (k*ρ.im) = ρ := by
      apply Complex.ext
      · exact (Zeta23.RH_implies_on_line hRH (zm.mp hm).1).symm
      · change k*ρ.im/k = ρ.im; field_simp
    rw [he]; exact zm.mp hm
  refine ⟨s,z ∘ P,z ∘ Q,?_,?_,?_⟩
  · rw [card, show k*(2*T)-k*T = k*T by ring] at hc
    exact hc
  · intro i hi
    obtain ⟨hp,hq,hlt,he⟩ := hpq i hi
    refine ⟨lift hp,lift hq,div_lt_div_of_pos_right hlt hk,?_⟩
    change (eta:ℝ) ≤ |fourierReal (k*(Q i/k-P i/k))|
    rwa [show k*(Q i/k-P i/k) = Q i-P i by field_simp]
  · intro i hi j hj hij
    exact div_lt_div_of_pos_right (hd i hi j hj hij) hk

end Range5Zeros.ShiftedCubicSpacing
end
end Src_Devine_ConditionalShiftedCubicZeroPairs

section Src_Devine_QuarticWindowLink



open Range5Zeros.ShiftedCubicSpacing.FourierCertificate

namespace DevineQuarticSpacing

theorem kernel_eq (a : ℝ) : TMG.ghat TMG.W3 a = quarticTransform a := by
  unfold TMG.ghat quarticTransform
  congr 1
  funext u
  rw [TMG.W3, TMG.PolyAux.quarticWindow_g]
  norm_num only [weight, c2, c4, Rat.cast_neg, Rat.cast_div, Rat.cast_ofNat]

theorem kernel_re (s : ℝ) : (TMG.ghat TMG.W3 (2*Real.pi*s)).re = fourierReal s := by
  rw [kernel_eq, quarticTransform_re]

end DevineQuarticSpacing
end Src_Devine_QuarticWindowLink

section Src_Devine_ConditionalShiftedCubicGram


/-!
# Retained pair energy in the shifted cubic trace (T041-0074, Section 1)

Matrix-generic part. Let `A` be a positive semidefinite complex matrix and
write `P(A) = A (A - t)(A - t)`, exactly the form of `ThirdMoment.phi_diag_le`.

* `simple_pair`: the plus/minus test vectors on two coordinates, with the
  tangent of the cubic at the Rayleigh value. When that value is below `t`,
  `P(A)` itself is positive semidefinite.
* `repeated_gain`: the tangent at a repeated diagonal value `c` keeps the
  term `2 (c - t) (Re A_qp)^2`.
* `pair_gain`: the two cases with the multiplicity baseline.
* `pairs_trace_le`: the sum over disjoint pairs, in the form of
  `ThirdMoment.sum_phi_diag_le`.

Only the positive semidefinite calculus already used by the leader's
`phi_diag_le` is needed: `add`, `diagonal` and `conjTranspose_mul_mul_same`.
-/

open Matrix
open scoped ComplexOrder BigOperators

noncomputable section

namespace TMG.PairGain

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The leader's shifted cubic `A (A - t)(A - t)`. -/
abbrev cubeP (A : Matrix ι ι ℂ) (t : ℝ) : Matrix ι ι ℂ :=
  A * (A - (t : ℂ) • (1 : Matrix ι ι ℂ)) * (A - (t : ℂ) • (1 : Matrix ι ι ℂ))

theorem cubeP_psd {A : Matrix ι ι ℂ} (hA : A.PosSemidef) (t : ℝ) : (cubeP A t).PosSemidef := by
  have hSH := ThirdMoment.conjTranspose_sub_real hA.isHermitian t
  have hcomm : A * (A - (t : ℂ) • (1 : Matrix ι ι ℂ)) = (A - (t : ℂ) • (1 : Matrix ι ι ℂ)) * A := by
    simp [mul_sub, sub_mul]
  have hpsd := hA.conjTranspose_mul_mul_same (A - (t : ℂ) • (1 : Matrix ι ι ℂ))
  rw [hSH, ← hcomm] at hpsd
  exact hpsd

/-- The tangent line of `x (x - t)^2` at `c`, evaluated at `A`. -/
def tangentC (A : Matrix ι ι ℂ) (t c : ℝ) : Matrix ι ι ℂ :=
  (((c - t) * (3 * c - t) : ℝ) : ℂ) • (A - (c : ℂ) • (1 : Matrix ι ι ℂ)) +
    ((c * (c - t) ^ 2 : ℝ) : ℂ) • (1 : Matrix ι ι ℂ)

/-- `x (x-t)^2 = (x-c)(x+2c-2t)(x-c) + (c-t)(3c-t)(x-c) + c(c-t)^2`, with the
left factor written as a conjugate transpose. -/
theorem cube_tangent_identity {A : Matrix ι ι ℂ} (hA : A.PosSemidef) (t c : ℝ) :
    cubeP A t =
      (A - (c : ℂ) • (1 : Matrix ι ι ℂ))ᴴ * (A + (2 * (c : ℂ) - 2 * (t : ℂ)) • (1 : Matrix ι ι ℂ))
          * (A - (c : ℂ) • (1 : Matrix ι ι ℂ)) + tangentC A t c := by
  rw [ThirdMoment.conjTranspose_sub_real hA.isHermitian c]
  unfold cubeP tangentC
  push_cast
  simp only [mul_sub, sub_mul, mul_add, add_mul, smul_mul_assoc, mul_smul_comm, mul_one, one_mul,
    smul_sub, smul_add, smul_smul, mul_assoc]
  module

theorem above_tangent {A : Matrix ι ι ℂ} (hA : A.PosSemidef) {t c : ℝ} (htc : t ≤ c) :
    (cubeP A t - tangentC A t c).PosSemidef := by
  have hQpsd : (A + (2 * (c : ℂ) - 2 * (t : ℂ)) • (1 : Matrix ι ι ℂ)).PosSemidef := by
    refine hA.add ?_
    rw [Matrix.smul_one_eq_diagonal]
    refine Matrix.PosSemidef.diagonal fun i => ?_
    have h : (2 * (c : ℂ) - 2 * (t : ℂ)) = ((2 * c - 2 * t : ℝ) : ℂ) := by
      push_cast
      ring
    show (0 : ℂ) ≤ 2 * (c : ℂ) - 2 * (t : ℂ)
    rw [h]
    exact Complex.zero_le_real.mpr (by linarith)
  rw [cube_tangent_identity hA t c, add_sub_cancel_right]
  exact hQpsd.conjTranspose_mul_mul_same (A - (c : ℂ) • (1 : Matrix ι ι ℂ))

theorem tangentC_diag (A : Matrix ι ι ℂ) (t c : ℝ) (i : ι) :
    ((tangentC A t c) i i).re = (c - t) * (3 * c - t) * ((A i i).re - c) + c * (c - t) ^ 2 := by
  simp only [tangentC, Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, Matrix.one_apply_eq,
    smul_eq_mul, mul_one, Complex.add_re, Complex.re_ofReal_mul, Complex.sub_re, Complex.ofReal_re]

theorem tangentC_off (A : Matrix ι ι ℂ) (t c : ℝ) {i j : ι} (hij : i ≠ j) :
    ((tangentC A t c) i j).re = (c - t) * (3 * c - t) * (A i j).re := by
  simp only [tangentC, Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply,
    Matrix.one_apply_ne hij, smul_zero, mul_zero, sub_zero, add_zero, smul_eq_mul,
    Complex.re_ofReal_mul]

/-! ### The two-coordinate test -/

/-- Real part of the quadratic form at `e_p + s e_q` when `s^2 = 1`. -/
def testVal (M : Matrix ι ι ℂ) (p q : ι) (s : ℝ) : ℝ :=
  (M p p).re + (M q q).re + s * ((M p q).re + (M q p).re)

private theorem quad_unit {M : Matrix ι ι ℂ} (hM : M.PosSemidef) (p q : ι) (u : ℂ)
    (hu : star u = u) :
    0 ≤ (M p p + u * (M p q + M q p) + u ^ 2 * M q q).re := by
  have h := hM.dotProduct_mulVec_nonneg (Pi.single p (1 : ℂ) + Pi.single q u)
  have e : star (Pi.single p (1 : ℂ) + Pi.single q u) ⬝ᵥ
      (M *ᵥ (Pi.single p (1 : ℂ) + Pi.single q u)) = M p p + u * (M p q + M q p) + u ^ 2 * M q q := by
    rw [star_add, Pi.star_single, Pi.star_single, star_one, hu, add_dotProduct,
      single_dotProduct, single_dotProduct]
    first
      | (simp only [Matrix.mulVec, dotProduct_add, dotProduct_single]; ring1)
      | (simp only [Matrix.mulVec_apply, Matrix.row_apply, dotProduct_add, dotProduct_single]; ring1)
      | (simp [Matrix.mulVec, dotProduct_add]; ring1)
  rw [e] at h
  exact (Complex.nonneg_iff.mp h).1

theorem quad_test {M : Matrix ι ι ℂ} (hM : M.PosSemidef) (p q : ι) {s : ℝ}
    (hs : s = 1 ∨ s = -1) : 0 ≤ testVal M p q s := by
  unfold testVal
  rcases hs with rfl | rfl
  · have h := quad_unit hM p q 1 (star_one ℂ)
    simp only [Complex.add_re, one_mul, one_pow] at h
    linarith
  · have h := quad_unit hM p q (-1) (by rw [star_neg, star_one])
    simp only [Complex.add_re, Complex.neg_re, neg_one_mul, neg_one_sq, one_mul] at h
    linarith

theorem testVal_sub (M N : Matrix ι ι ℂ) (p q : ι) (s : ℝ) :
    testVal (M - N) p q s = testVal M p q s - testVal N p q s := by
  unfold testVal
  simp only [Matrix.sub_apply, Complex.sub_re]
  ring

theorem testVal_tangentC (A : Matrix ι ι ℂ) (t c : ℝ) {p q : ι} (hpq : p ≠ q) (s : ℝ) :
    testVal (tangentC A t c) p q s
      = (c - t) * (3 * c - t) * (testVal A p q s - 2 * c) + 2 * (c * (c - t) ^ 2) := by
  unfold testVal
  rw [tangentC_diag, tangentC_diag, tangentC_off A t c hpq, tangentC_off A t c hpq.symm]
  ring

/-- Scalar Jensen along `e_p + s e_q`, by the tangent at the Rayleigh value. -/
theorem pair_test {A : Matrix ι ι ℂ} (hA : A.PosSemidef) (t : ℝ) {p q : ι} (hpq : p ≠ q)
    {s : ℝ} (hs : s = 1 ∨ s = -1) :
    2 * ThirdMoment.phi t (testVal A p q s / 2) ≤ testVal (cubeP A t) p q s := by
  by_cases hrt : testVal A p q s / 2 ≤ t
  · rw [ThirdMoment.phi_of_ge hrt, mul_zero]
    exact quad_test (cubeP_psd hA t) p q hs
  · have htr : t ≤ testVal A p q s / 2 := le_of_lt (not_le.mp hrt)
    have h := quad_test (above_tangent hA htr) p q hs
    rw [testVal_sub, testVal_tangentC A t _ hpq] at h
    rw [ThirdMoment.phi_of_le htr]
    have z : (testVal A p q s / 2 - t) * (3 * (testVal A p q s / 2) - t) *
        (testVal A p q s - 2 * (testVal A p q s / 2)) = 0 := by ring
    linarith [h, z]

/-- Both zeros simple: one of the two test vectors has Rayleigh value at least `x`. -/
theorem simple_pair {A : Matrix ι ι ℂ} (hA : A.PosSemidef) {t x : ℝ} (ht : 0 ≤ t) (hx : 0 ≤ x)
    {p q : ι} (hpq : p ≠ q)
    (hr : x ≤ testVal A p q 1 / 2 ∨ x ≤ testVal A p q (-1) / 2) :
    ThirdMoment.phi t x ≤ ((cubeP A t) p p).re + ((cubeP A t) q q).re := by
  have h1 := pair_test hA t hpq (s := 1) (Or.inl rfl)
  have h2 := pair_test hA t hpq (s := -1) (Or.inr rfl)
  have hsum : testVal (cubeP A t) p q 1 + testVal (cubeP A t) p q (-1)
      = 2 * (((cubeP A t) p p).re + ((cubeP A t) q q).re) := by
    unfold testVal
    ring
  have hq1 := quad_test hA p q (s := 1) (Or.inl rfl)
  have hq2 := quad_test hA p q (s := -1) (Or.inr rfl)
  have n1 : 0 ≤ ThirdMoment.phi t (testVal A p q 1 / 2) :=
    ThirdMoment.phi_nonneg (div_nonneg hq1 (by norm_num))
  have n2 : 0 ≤ ThirdMoment.phi t (testVal A p q (-1) / 2) :=
    ThirdMoment.phi_nonneg (div_nonneg hq2 (by norm_num))
  rcases hr with h | h
  · have hm := ThirdMoment.phi_mono ht hx h
    linarith
  · have hm := ThirdMoment.phi_mono ht hx h
    linarith

/-! ### The retained variance at a repeated diagonal value -/

theorem gram_split (A : Matrix ι ι ℂ) (t c : ℝ) :
    (A - (c : ℂ) • (1 : Matrix ι ι ℂ))ᴴ * (A + (2 * (c : ℂ) - 2 * (t : ℂ)) • (1 : Matrix ι ι ℂ))
        * (A - (c : ℂ) • (1 : Matrix ι ι ℂ))
      = (A - (c : ℂ) • (1 : Matrix ι ι ℂ))ᴴ * A * (A - (c : ℂ) • (1 : Matrix ι ι ℂ))
        + ((2 * c - 2 * t : ℝ) : ℂ) •
          ((A - (c : ℂ) • (1 : Matrix ι ι ℂ))ᴴ * (A - (c : ℂ) • (1 : Matrix ι ι ℂ))) := by
  push_cast
  simp only [mul_add, add_mul, Matrix.mul_add, Matrix.add_mul, mul_smul_comm, smul_mul_assoc,
    Matrix.mul_smul, Matrix.smul_mul, mul_one, Matrix.mul_one]

theorem re_sq_le_gram_diag (B : Matrix ι ι ℂ) (p q : ι) :
    ((B q p).re) ^ 2 ≤ ((Bᴴ * B) p p).re := by
  have hterm : ∀ j, (Bᴴ p j * B j p).re = (B j p).re ^ 2 + (B j p).im ^ 2 := by
    intro j
    have h1 : (star (B j p)).re = (B j p).re := Complex.conj_re (B j p)
    have h2 : (star (B j p)).im = -(B j p).im := Complex.conj_im (B j p)
    rw [Matrix.conjTranspose_apply, Complex.mul_re, h1, h2]
    ring
  rw [Matrix.mul_apply, Complex.re_sum]
  simp only [hterm]
  calc ((B q p).re) ^ 2 ≤ (B q p).re ^ 2 + (B q p).im ^ 2 := le_add_of_nonneg_right (sq_nonneg _)
    _ ≤ ∑ j, ((B j p).re ^ 2 + (B j p).im ^ 2) :=
        Finset.single_le_sum (f := fun j => (B j p).re ^ 2 + (B j p).im ^ 2)
          (fun j _ => by positivity) (Finset.mem_univ q)

/-- A repeated diagonal value `c = Re A_pp ≥ t` keeps its off-diagonal variance. -/
theorem repeated_gain {A : Matrix ι ι ℂ} (hA : A.PosSemidef) {t c : ℝ} {p q : ι} (hpq : p ≠ q)
    (hc : (A p p).re = c) (htc : t ≤ c) :
    ThirdMoment.phi t c + 2 * (c - t) * ((A q p).re) ^ 2 ≤ ((cubeP A t) p p).re := by
  have hid := cube_tangent_identity hA t c
  have hsplit := gram_split A t c
  have hP : ((cubeP A t) p p).re
      = (((A - (c : ℂ) • (1 : Matrix ι ι ℂ))ᴴ * A * (A - (c : ℂ) • (1 : Matrix ι ι ℂ))) p p).re
        + (2 * c - 2 * t) *
          (((A - (c : ℂ) • (1 : Matrix ι ι ℂ))ᴴ * (A - (c : ℂ) • (1 : Matrix ι ι ℂ))) p p).re
        + ((c - t) * (3 * c - t) * ((A p p).re - c) + c * (c - t) ^ 2) := by
    rw [hid, hsplit, Matrix.add_apply, Matrix.add_apply, Complex.add_re, Complex.add_re,
      Matrix.smul_apply, smul_eq_mul, Complex.re_ofReal_mul, tangentC_diag]
  have h0 := ThirdMoment.re_diag_nonneg
    (hA.conjTranspose_mul_mul_same (A - (c : ℂ) • (1 : Matrix ι ι ℂ))) p
  have hvar := re_sq_le_gram_diag (A - (c : ℂ) • (1 : Matrix ι ι ℂ)) p q
  have hD : (A - (c : ℂ) • (1 : Matrix ι ι ℂ)) q p = A q p := by
    rw [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply_ne hpq.symm, smul_zero, sub_zero]
  rw [hD] at hvar
  have hk : 0 ≤ 2 * c - 2 * t := by linarith
  have hmul := mul_le_mul_of_nonneg_left hvar hk
  have hz : (c - t) * (3 * c - t) * ((A p p).re - c) = 0 := by rw [hc, sub_self, mul_zero]
  rw [ThirdMoment.phi_of_le htc, hP]
  linarith [h0, hmul, hz]

/-! ### One selected pair with the multiplicity baseline -/

/-- T041, Section 1. The diagonal of `A` dominates the multiplicities, and the
off-diagonal real part satisfies `eta^2 A_pp A_qq ≤ (Re A_qp)^2`. -/
theorem pair_gain {A : Matrix ι ι ℂ} (hA : A.PosSemidef) {t η : ℝ} (ht1 : 1 ≤ t) (ht2 : t < 2)
    (hη : 0 ≤ η) (htη : t ≤ 1 + η) (hg : (1 + η) * (1 + η - t) ^ 2 ≤ 4 * (2 - t) * η ^ 2)
    {p q : ι} (hpq : p ≠ q) {mp mq : ℕ} (hmp : 1 ≤ mp) (hmq : 1 ≤ mq)
    (hcp : (mp : ℝ) ≤ (A p p).re) (hcq : (mq : ℝ) ≤ (A q q).re)
    (hoff : η ^ 2 * ((A p p).re * (A q q).re) ≤ ((A q p).re) ^ 2) :
    ThirdMoment.phi t mp + ThirdMoment.phi t mq + (1 + η) * (1 + η - t) ^ 2
      ≤ ((cubeP A t) p p).re + ((cubeP A t) q q).re := by
  have ht0 : 0 ≤ t := by linarith
  have hsym : (A p q).re = (A q p).re := by
    rw [← hA.isHermitian.apply q p]
    exact (Complex.conj_re (A p q)).symm
  have hmp1 : (1 : ℝ) ≤ mp := by exact_mod_cast hmp
  have hmq1 : (1 : ℝ) ≤ mq := by exact_mod_cast hmq
  have hcp1 : 1 ≤ (A p p).re := le_trans hmp1 hcp
  have hcq1 : 1 ≤ (A q q).re := le_trans hmq1 hcq
  have hdp : ThirdMoment.phi t (A p p).re ≤ ((cubeP A t) p p).re := ThirdMoment.phi_diag_le hA ht0 p
  have hdq : ThirdMoment.phi t (A q q).re ≤ ((cubeP A t) q q).re := ThirdMoment.phi_diag_le hA ht0 q
  have hmono_p := ThirdMoment.phi_mono ht0 (Nat.cast_nonneg mp) hcp
  have hmono_q := ThirdMoment.phi_mono ht0 (Nat.cast_nonneg mq) hcq
  by_cases hp2 : 2 ≤ mp
  · -- a repeated endpoint at `p`
    have hmp2 : (2 : ℝ) ≤ mp := by exact_mod_cast hp2
    have hcp2 : 2 ≤ (A p p).re := le_trans hmp2 hcp
    have hrep := repeated_gain hA hpq rfl (by linarith : t ≤ (A p p).re)
    have hcc : 2 ≤ (A p p).re * (A q q).re := by nlinarith
    have hsq : 2 * η ^ 2 ≤ ((A q p).re) ^ 2 := by
      have := mul_le_mul_of_nonneg_left hcc (sq_nonneg η)
      linarith
    have h1 : 2 * (2 - t) * (2 * η ^ 2) ≤ 2 * ((A p p).re - t) * (2 * η ^ 2) :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    have h2 : 2 * ((A p p).re - t) * (2 * η ^ 2) ≤ 2 * ((A p p).re - t) * ((A q p).re) ^ 2 :=
      mul_le_mul_of_nonneg_left hsq (by linarith)
    linarith
  · by_cases hq2 : 2 ≤ mq
    · -- a repeated endpoint at `q`
      have hmq2 : (2 : ℝ) ≤ mq := by exact_mod_cast hq2
      have hcq2 : 2 ≤ (A q q).re := le_trans hmq2 hcq
      have hrep := repeated_gain hA hpq.symm rfl (by linarith : t ≤ (A q q).re)
      rw [hsym] at hrep
      have hcc : 2 ≤ (A p p).re * (A q q).re := by nlinarith
      have hsq : 2 * η ^ 2 ≤ ((A q p).re) ^ 2 := by
        have := mul_le_mul_of_nonneg_left hcc (sq_nonneg η)
        linarith
      have h1 : 2 * (2 - t) * (2 * η ^ 2) ≤ 2 * ((A q q).re - t) * (2 * η ^ 2) :=
        mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      have h2 : 2 * ((A q q).re - t) * (2 * η ^ 2) ≤ 2 * ((A q q).re - t) * ((A q p).re) ^ 2 :=
        mul_le_mul_of_nonneg_left hsq (by linarith)
      linarith
    · -- both endpoints simple
      have e1 : mp = 1 := by omega
      have e2 : mq = 1 := by omega
      subst e1 e2
      rw [Nat.cast_one, ThirdMoment.phi_one ht1]
      have hcc : 1 ≤ (A p p).re * (A q q).re := by nlinarith
      have hsq : η ^ 2 ≤ ((A q p).re) ^ 2 := by
        have := mul_le_mul_of_nonneg_left hcc (sq_nonneg η)
        linarith
      have ho : η ≤ |(A q p).re| := by
        have h := sq_le_sq.mp hsq
        rwa [abs_of_nonneg hη] at h
      have hr : 1 + η ≤ testVal A p q 1 / 2 ∨ 1 + η ≤ testVal A p q (-1) / 2 := by
        unfold testVal
        rw [hsym]
        rcases le_total 0 (A q p).re with h | h
        · left
          rw [abs_of_nonneg h] at ho
          linarith
        · right
          rw [abs_of_nonpos h] at ho
          linarith
      have hx := simple_pair hA ht0 (by linarith : (0 : ℝ) ≤ 1 + η) hpq hr
      rw [ThirdMoment.phi_of_le htη] at hx
      linarith

/-! ### Disjoint pairs -/

theorem sum_pairs_le {κ : Type*} (f b : ι → ℝ) (Z : Finset ι) (hf0 : ∀ a, 0 ≤ f a)
    (hfb : ∀ a ∈ Z, b a ≤ f a) (s : Finset κ) (p q : κ → ι)
    (hpZ : ∀ k ∈ s, p k ∈ Z) (hqZ : ∀ k ∈ s, q k ∈ Z)
    (hp : Set.InjOn p s) (hq : Set.InjOn q s) (hpq : ∀ k ∈ s, ∀ l ∈ s, p k ≠ q l) {g : ℝ}
    (hgain : ∀ k ∈ s, b (p k) + b (q k) + g ≤ f (p k) + f (q k)) :
    ∑ a ∈ Z, b a + (s.card : ℝ) * g ≤ ∑ a, f a := by
  have hdisj : Disjoint (s.image p) (s.image q) := by
    rw [Finset.disjoint_left]
    intro a ha hb
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨l, hl, hl'⟩ := Finset.mem_image.mp hb
    exact hpq k hk l hl hl'.symm
  have hU : s.image p ∪ s.image q ⊆ Z := by
    intro a ha
    rcases Finset.mem_union.mp ha with h | h
    · obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp h
      exact hpZ k hk
    · obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp h
      exact hqZ k hk
  have h1 : ∑ a ∈ s.image p ∪ s.image q, (f a - b a) ≤ ∑ a ∈ Z, (f a - b a) :=
    Finset.sum_le_sum_of_subset_of_nonneg hU (fun a ha _ => sub_nonneg.mpr (hfb a ha))
  rw [Finset.sum_union hdisj, Finset.sum_image hp, Finset.sum_image hq] at h1
  have h2 : ∑ k ∈ s, g ≤ ∑ k ∈ s, ((f (p k) - b (p k)) + (f (q k) - b (q k))) :=
    Finset.sum_le_sum fun k hk => by linarith [hgain k hk]
  rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul] at h2
  have h3 : ∑ a ∈ Z, (f a - b a) = ∑ a ∈ Z, f a - ∑ a ∈ Z, b a := by
    rw [Finset.sum_sub_distrib]
  have h4 : ∑ a ∈ Z, f a ≤ ∑ a, f a :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ Z) (fun a _ _ => hf0 a)
  linarith

theorem sum_re_cubeP (A : Matrix ι ι ℂ) (t : ℝ) :
    ∑ a, ((cubeP A t) a a).re
      = (Matrix.trace (A ^ 3) - 2 * t * Matrix.trace (A ^ 2) + t ^ 2 * Matrix.trace A).re := by
  have e : ∑ a, ((cubeP A t) a a).re = (Matrix.trace (cubeP A t)).re := by
    rw [Matrix.trace, Complex.re_sum]
    rfl
  rw [e]
  show (Matrix.trace (A * (A - (t : ℂ) • (1 : Matrix ι ι ℂ)) * (A - (t : ℂ) • (1 : Matrix ι ι ℂ)))).re = _
  rw [ThirdMoment.cubic_expand A (t : ℂ), Matrix.trace_add, Matrix.trace_sub, Matrix.trace_smul,
    Matrix.trace_smul, smul_eq_mul, smul_eq_mul]

/-- The strengthened `ThirdMoment.sum_phi_diag_le`: the baseline on `Z`
plus `g` for each of the disjoint pairs. -/
theorem pairs_trace_le {A : Matrix ι ι ℂ} (hA : A.PosSemidef) {t : ℝ} (ht : 0 ≤ t)
    (b : ι → ℝ) (Z : Finset ι) (hb : ∀ a ∈ Z, b a ≤ ThirdMoment.phi t (A a a).re)
    {κ : Type*} (s : Finset κ) (p q : κ → ι) (hpZ : ∀ k ∈ s, p k ∈ Z) (hqZ : ∀ k ∈ s, q k ∈ Z)
    (hp : Set.InjOn p s) (hq : Set.InjOn q s) (hpq : ∀ k ∈ s, ∀ l ∈ s, p k ≠ q l) {g : ℝ}
    (hgain : ∀ k ∈ s, b (p k) + b (q k) + g ≤
      ((cubeP A t) (p k) (p k)).re + ((cubeP A t) (q k) (q k)).re) :
    ∑ a ∈ Z, b a + (s.card : ℝ) * g
      ≤ (Matrix.trace (A ^ 3) - 2 * t * Matrix.trace (A ^ 2) + t ^ 2 * Matrix.trace A).re := by
  rw [← sum_re_cubeP A t]
  have hd : ∀ a, ThirdMoment.phi t (A a a).re ≤ ((cubeP A t) a a).re :=
    fun a => ThirdMoment.phi_diag_le hA ht a
  exact sum_pairs_le (fun a => ((cubeP A t) a a).re) b Z
    (fun a => le_trans (ThirdMoment.phi_nonneg (ThirdMoment.re_diag_nonneg hA a)) (hd a))
    (fun a ha => le_trans (hb a ha) (hd a)) s p q hpZ hqZ hp hq hpq hgain

end TMG.PairGain

end
end Src_Devine_ConditionalShiftedCubicGram

section Src_Devine_ConditionalShiftedCubicGramZeros



/-!
# Retained pair energy for the Gram matrix of the zeros (T041-0074, Sections 1 and 3)

The input is the leader's Gram matrix for a finite set `S` of zeros that
contains the window `(T, 2T]`. The disjoint pairs are those selected by
`Range5Zeros.ShiftedCubicSpacing.dyadic_zero_pairs` at the scale
`sigma log T / (2 pi)`. For each `S`, the finite trace combination is at least
`phiSum + m g`. The selection and its size `m` do not depend on `S`, so the
leader's uniform limit (`TMG.phiSum_le_Xi`) carries the same bound to the full
kernel.
-/

open Matrix
open scoped ComplexOrder BigOperators

noncomputable section

namespace TMG.PairGain

/-- Order facts for the ordinates of the selected pairs. -/
theorem pairs_ordered {s : Finset ℕ} {p q : ℕ → ℂ}
    (hlt : ∀ i ∈ s, (p i).im < (q i).im)
    (hdis : ∀ i ∈ s, ∀ j ∈ s, i < j → (q i).im < (p j).im) :
    (∀ i ∈ s, ∀ j ∈ s, p i = p j → i = j) ∧ (∀ i ∈ s, ∀ j ∈ s, q i = q j → i = j) ∧
      (∀ i ∈ s, ∀ j ∈ s, p i ≠ q j) := by
  refine ⟨fun i hi j hj h => ?_, fun i hi j hj h => ?_, fun i hi j hj h => ?_⟩
  · have e := congrArg Complex.im h
    rcases lt_trichotomy i j with hij | hij | hij
    · exfalso
      linarith [hlt i hi, hdis i hi j hj hij]
    · exact hij
    · exfalso
      linarith [hlt j hj, hdis j hj i hi hij]
  · have e := congrArg Complex.im h
    rcases lt_trichotomy i j with hij | hij | hij
    · exfalso
      linarith [hlt j hj, hdis i hi j hj hij]
    · exact hij
    · exfalso
      linarith [hlt i hi, hdis j hj i hi hij]
  · have e := congrArg Complex.im h
    rcases lt_trichotomy i j with hij | hij | hij
    · linarith [hlt i hi, hlt j hj, hdis i hi j hj hij]
    · rw [← hij] at e
      linarith [hlt i hi]
    · linarith [hlt i hi, hdis j hj i hi hij]

/-- The finite Gram inequality with retained pairs. The number `m` of selected
pairs comes before the finite set `S`. -/
theorem phiSum_pairs_le_Kfin (hRH : RiemannHypothesis) (w : TMA.HeightWeight) {T t σ : ℝ}
    (hT : 1 < T) (hσ : 0 < σ) (ht1 : 1 ≤ t) (ht2 : t < 2)
    (htη : t ≤ 1 + (Range5Zeros.ShiftedCubicSpacing.eta : ℝ))
    (hg : (1 + (Range5Zeros.ShiftedCubicSpacing.eta : ℝ)) *
        (1 + (Range5Zeros.ShiftedCubicSpacing.eta : ℝ) - t) ^ 2
      ≤ 4 * (2 - t) * (Range5Zeros.ShiftedCubicSpacing.eta : ℝ) ^ 2) :
    ∃ m : ℕ,
      (Zeta23.Ndist T (2 * T) : ℝ) - 2 - 2 * (σ * Real.log T / (2 * Real.pi) * T) / 3
          ≤ 3 * (m : ℝ) ∧
      ∀ S : Finset ℂ, ThirdMoment.zerosFinset T (2 * T) ⊆ S →
        ThirdMoment.phiSum t T (2 * T) + (m : ℝ) *
            ((1 + (Range5Zeros.ShiftedCubicSpacing.eta : ℝ)) *
              (1 + (Range5Zeros.ShiftedCubicSpacing.eta : ℝ) - t) ^ 2)
          ≤ (t3 W3 (TMA.Kfin w.h T σ S)).re - 2 * t * t2 W3 (TMA.Kfin w.h T σ S)
              + t ^ 2 * (TMA.Kfin w.h T σ S 0).re := by
  classical
  have hT0 : (0 : ℝ) ≤ T := by linarith
  have hTpos : (0 : ℝ) < T := by linarith
  have ht0 : (0 : ℝ) ≤ t := by linarith
  have heta0 : (0 : ℝ) ≤ (Range5Zeros.ShiftedCubicSpacing.eta : ℝ) := by
    norm_num [Range5Zeros.ShiftedCubicSpacing.eta]
  have hk : 0 < σ * Real.log T / (2 * Real.pi) :=
    div_pos (mul_pos hσ (Real.log_pos hT)) (by positivity)
  obtain ⟨s, p, q, hcard, hpq, hdis⟩ :=
    Range5Zeros.ShiftedCubicSpacing.dyadic_zero_pairs hRH hT0 hk
  refine ⟨s.card, hcard, fun S hS => ?_⟩
  obtain ⟨hinjp, hinjq, hne⟩ := pairs_ordered (s := s) (p := p) (q := q)
    (fun i hi => (hpq i hi).2.2.1) hdis
  -- the leader's Gram matrix of the finite kernel
  have hc : ∀ a : S, 0 ≤ TMA.cw w.h T a := fun a => TMA.cw_nonneg w T a
  obtain ⟨A, hAdef⟩ : ∃ A : Matrix S S ℂ, A = Gram.gramW W3 (fun a : S => TMA.cw w.h T a)
      (fun a : S => σ * Real.log T * (a : ℂ).im) := ⟨_, rfl⟩
  have hA : A.PosSemidef := by
    rw [hAdef]
    exact Gram.gramW_posSemidef _ _ _
  have hdiag : ∀ a : S, (A a a).re = TMA.cw w.h T a := by
    intro a
    rw [hAdef, Gram.gramW_diag W3 _ _ hc a, Complex.ofReal_re]
  have hoffd : ∀ a b : S, (A a b).re = Real.sqrt (TMA.cw w.h T a) * Real.sqrt (TMA.cw w.h T b) *
      (ghat W3 (σ * Real.log T * (a : ℂ).im - σ * Real.log T * (b : ℂ).im)).re := by
    intro a b
    rw [hAdef]
    simp only [Gram.gramW, Matrix.of_apply]
    rw [← Complex.ofReal_mul, Complex.re_ofReal_mul]
  have hker : ∀ u v : ℝ, (ghat W3 (σ * Real.log T * u - σ * Real.log T * v)).re
      = Range5Zeros.ShiftedCubicSpacing.FourierCertificate.fourierReal
          (σ * Real.log T / (2 * Real.pi) * (u - v)) := by
    intro u v
    have hπ : (2 * Real.pi) ≠ 0 := by positivity
    have e : 2 * Real.pi * (σ * Real.log T / (2 * Real.pi) * (u - v))
        = σ * Real.log T * u - σ * Real.log T * v := by
      first
        | (rw [div_mul_eq_mul_div, mul_div_assoc', mul_div_cancel_left₀ _ hπ]; ring)
        | (field_simp; done)
        | (field_simp; ring)
    rw [← e, DevineQuarticSpacing.kernel_re]
  -- the window as a finset of indices
  obtain ⟨Zs, hsumZ, hZ1, hZ2⟩ : ∃ Zs : Finset S,
      ∑ a ∈ Zs, ThirdMoment.phi t (Zeta23.zeroMult (a : ℂ)) = ThirdMoment.phiSum t T (2 * T) ∧
      (∀ a ∈ Zs, (a : ℂ) ∈ ThirdMoment.zerosFinset T (2 * T)) ∧
      (∀ a : S, (a : ℂ) ∈ ThirdMoment.zerosFinset T (2 * T) → a ∈ Zs) := by
    let embed : ↥(ThirdMoment.zerosFinset T (2*T)) ↪ ↥S :=
      ⟨fun ρ => ⟨ρ.1,hS ρ.2⟩,fun _ _ h => Subtype.ext (congrArg (fun z : S => (z : ℂ)) h)⟩
    refine ⟨(ThirdMoment.zerosFinset T (2*T)).attach.map embed, ?_, ?_, ?_⟩
    · rw [Finset.sum_map, ThirdMoment.phiSum_eq]
      exact Finset.sum_attach (ThirdMoment.zerosFinset T (2 * T))
        (fun ρ => ThirdMoment.phi t (Zeta23.zeroMult ρ))
    · intro a ha
      obtain ⟨ρ, -, rfl⟩ := Finset.mem_map.mp ha
      exact ρ.2
    · intro a ha
      exact Finset.mem_map.mpr ⟨⟨a.1, ha⟩, Finset.mem_attach _ _, rfl⟩
  -- the selected pairs as indices
  obtain ⟨P, hP⟩ : ∃ P : s → S, ∀ k, (P k : ℂ) = p k.1 :=
    ⟨fun k => ⟨p k.1, hS (ThirdMoment.mem_zerosFinset.mpr (hpq k.1 k.2).1)⟩, fun k => rfl⟩
  obtain ⟨Q, hQ⟩ : ∃ Q : s → S, ∀ k, (Q k : ℂ) = q k.1 :=
    ⟨fun k => ⟨q k.1, hS (ThirdMoment.mem_zerosFinset.mpr (hpq k.1 k.2).2.1)⟩, fun k => rfl⟩
  have hPm : ∀ k : s, (P k : ℂ) ∈ ThirdMoment.zerosFinset T (2 * T) := fun k => by
    rw [hP]
    exact ThirdMoment.mem_zerosFinset.mpr (hpq k.1 k.2).1
  have hQm : ∀ k : s, (Q k : ℂ) ∈ ThirdMoment.zerosFinset T (2 * T) := fun k => by
    rw [hQ]
    exact ThirdMoment.mem_zerosFinset.mpr (hpq k.1 k.2).2.1
  have hPinj : Set.InjOn P (Finset.univ : Finset s) := by
    intro i _ j _ h
    apply Subtype.ext
    have h' := congrArg Subtype.val h
    rw [hP, hP] at h'
    exact hinjp i.1 i.2 j.1 j.2 h'
  have hQinj : Set.InjOn Q (Finset.univ : Finset s) := by
    intro i _ j _ h
    apply Subtype.ext
    have h' := congrArg Subtype.val h
    rw [hQ, hQ] at h'
    exact hinjq i.1 i.2 j.1 j.2 h'
  have hPQ : ∀ k ∈ (Finset.univ : Finset s), ∀ l ∈ (Finset.univ : Finset s), P k ≠ Q l := by
    intro k _ l _ h
    have h' := congrArg Subtype.val h
    rw [hP, hQ] at h'
    exact hne k.1 k.2 l.1 l.2 h'
  -- the gain on each selected pair
  have hgain : ∀ k ∈ (Finset.univ : Finset s),
      ThirdMoment.phi t (Zeta23.zeroMult (P k : ℂ)) + ThirdMoment.phi t (Zeta23.zeroMult (Q k : ℂ))
        + (1 + (Range5Zeros.ShiftedCubicSpacing.eta : ℝ)) *
            (1 + (Range5Zeros.ShiftedCubicSpacing.eta : ℝ) - t) ^ 2
      ≤ ((cubeP A t) (P k) (P k)).re + ((cubeP A t) (Q k) (Q k)).re := by
    intro k _
    refine pair_gain hA ht1 ht2 heta0 htη hg ?_ (ThirdMoment.one_le_mult_of_mem (hPm k))
      (ThirdMoment.one_le_mult_of_mem (hQm k)) ?_ ?_ ?_
    · intro h
      have h' := congrArg Subtype.val h
      rw [hP, hQ] at h'
      exact hne k.1 k.2 k.1 k.2 h'
    · rw [hdiag]
      exact Gram.zeroMult_le_cw w hTpos (ThirdMoment.mem_zerosFinset.mp (hPm k))
    · rw [hdiag]
      exact Gram.zeroMult_le_cw w hTpos (ThirdMoment.mem_zerosFinset.mp (hQm k))
    · rw [hdiag, hdiag, hoffd, hker, hQ, hP]
      have hF := (hpq k.1 k.2).2.2.2
      have hcp := TMA.cw_nonneg w T (p k.1)
      have hcq := TMA.cw_nonneg w T (q k.1)
      rw [mul_pow, mul_pow, Real.sq_sqrt hcq, Real.sq_sqrt hcp]
      have hF2 : (Range5Zeros.ShiftedCubicSpacing.eta : ℝ) ^ 2 ≤
          (Range5Zeros.ShiftedCubicSpacing.FourierCertificate.fourierReal
            (σ * Real.log T / (2 * Real.pi) * ((q k.1).im - (p k.1).im))) ^ 2 := by
        rw [sq_le_sq, abs_of_nonneg heta0]
        exact hF
      have hmul := mul_le_mul_of_nonneg_right hF2 (mul_nonneg hcp hcq)
      linarith
  -- assemble with the leader's trace identities
  have key := pairs_trace_le hA ht0 (fun a : S => ThirdMoment.phi t (Zeta23.zeroMult (a : ℂ))) Zs
    (fun a ha => by
      rw [hdiag]
      exact ThirdMoment.phi_mono ht0 (Nat.cast_nonneg _)
        (Gram.zeroMult_le_cw w hTpos (ThirdMoment.mem_zerosFinset.mp (hZ1 a ha))))
    (Finset.univ : Finset s) P Q (fun k _ => hZ2 _ (hPm k)) (fun k _ => hZ2 _ (hQm k))
    hPinj hQinj hPQ hgain
  rw [hsumZ, Finset.card_univ, Fintype.card_coe, hAdef] at key
  rw [Gram.trace_gramW_cube W3 _ _ hc, Gram.trace_gramW_sq W3 _ _ hc, Gram.trace_gramW W3 _ _ hc,
    ← Gram.Kfin_eq_trigK] at key
  have hre : (t3 W3 (TMA.Kfin w.h T σ S) - 2 * (t : ℂ) * ((t2 W3 (TMA.Kfin w.h T σ S) : ℝ) : ℂ)
        + (t : ℂ) ^ 2 * TMA.Kfin w.h T σ S 0).re
      = (t3 W3 (TMA.Kfin w.h T σ S)).re - 2 * t * t2 W3 (TMA.Kfin w.h T σ S)
          + t ^ 2 * (TMA.Kfin w.h T σ S 0).re := by
    have e1 : 2 * (t : ℂ) * ((t2 W3 (TMA.Kfin w.h T σ S) : ℝ) : ℂ)
        = ((2 * t * t2 W3 (TMA.Kfin w.h T σ S) : ℝ) : ℂ) := by
      push_cast
      ring
    have e2 : (t : ℂ) ^ 2 = ((t ^ 2 : ℝ) : ℂ) := by
      push_cast
      ring
    rw [e1, e2, Complex.add_re, Complex.sub_re, Complex.ofReal_re, Complex.re_ofReal_mul]
  rw [hre] at key
  exact key

open Gram in
/-- The leader's passage from finite kernels to the full kernel (the proof of
`TMG.phiSum_le_Xi`), for any left side bounded at every finite set containing
the window. -/
theorem le_Xi_of_le_Kfin (hRH : RiemannHypothesis) (W : Window) (w : TMA.HeightWeight)
    {T σ t : ℝ} (hT : 0 < T) {L : ℝ}
    (hL : ∀ S : Finset ℂ, ThirdMoment.zerosFinset T (2 * T) ⊆ S →
      L ≤ (t3 W (TMA.Kfin w.h T σ S)).re - 2 * t * t2 W (TMA.Kfin w.h T σ S)
        + t ^ 2 * (TMA.Kfin w.h T σ S 0).re) :
    L ≤ (t3 W (TMA.Kfull w.h T σ)).re - 2 * t * t2 W (TMA.Kfull w.h T σ)
        + t ^ 2 * (TMA.Kfull w.h T σ 0).re := by
  set M : ℝ := ∑' ρ : Zeta23.zetaZeroConfig.carrier, TMA.cw w.h T ρ
  have hcF := TMA.continuous_Kfull hRH w hT σ
  have hcf : ∀ s, Continuous (TMA.Kfin w.h T σ (zfin s)) := fun s => continuous_Kfin _ _ _ _
  have hbF : ∀ x, ‖TMA.Kfull w.h T σ x‖ ≤ M := norm_Kfull_le hRH w hT σ
  have hbf : ∀ s x, ‖TMA.Kfin w.h T σ (zfin s) x‖ ≤ M := norm_Kfin_le hRH w hT σ
  have hd : ∀ s x, ‖TMA.Kfull w.h T σ x - TMA.Kfin w.h T σ (zfin s) x‖ ≤ cwTail w.h T s :=
    norm_Kfull_sub_Kfin_le hRH w hT σ
  have htail := tendsto_cwTail w.h T
  have l3 : Filter.Tendsto (fun s => t3 W (TMA.Kfin w.h T σ (zfin s))) Filter.atTop
      (nhds (t3 W (TMA.Kfull w.h T σ))) := by
    refine tendsto_iff_norm_sub_tendsto_zero.mpr ?_
    have hz : Filter.Tendsto (fun s => W.bound ^ 2 * (3 * M ^ 2 * cwTail w.h T s) * 2 * 2)
        Filter.atTop (nhds 0) := by
      have := (((htail.const_mul (3 * M ^ 2)).const_mul (W.bound ^ 2)).mul_const 2).mul_const 2
      simpa only [mul_zero, zero_mul] using this
    refine squeeze_zero (fun s => norm_nonneg _) (fun s => ?_) hz
    rw [norm_sub_rev]
    exact t3_sub_le W hcF (hcf s) hbF (hbf s) (hd s)
  have l2 : Filter.Tendsto (fun s => t2 W (TMA.Kfin w.h T σ (zfin s))) Filter.atTop
      (nhds (t2 W (TMA.Kfull w.h T σ))) := by
    refine tendsto_iff_norm_sub_tendsto_zero.mpr ?_
    have hz : Filter.Tendsto (fun s => W.bound * (2 * M * cwTail w.h T s) * 2) Filter.atTop
        (nhds 0) := by
      have := ((htail.const_mul (2 * M)).const_mul W.bound).mul_const 2
      simpa only [mul_zero, zero_mul] using this
    refine squeeze_zero (fun s => norm_nonneg _) (fun s => ?_) hz
    rw [norm_sub_rev, Real.norm_eq_abs]
    exact t2_sub_le W hcF (hcf s) hbF (hbf s) (hd s)
  have l1 : Filter.Tendsto (fun s => TMA.Kfin w.h T σ (zfin s) 0) Filter.atTop
      (nhds (TMA.Kfull w.h T σ 0)) := by
    refine tendsto_iff_norm_sub_tendsto_zero.mpr ?_
    refine squeeze_zero (fun s => norm_nonneg _) (fun s => ?_) htail
    rw [norm_sub_rev]
    exact hd s 0
  have lim : Filter.Tendsto
      (fun s => (t3 W (TMA.Kfin w.h T σ (zfin s))).re - 2 * t * t2 W (TMA.Kfin w.h T σ (zfin s))
        + t ^ 2 * (TMA.Kfin w.h T σ (zfin s) 0).re) Filter.atTop
      (nhds ((t3 W (TMA.Kfull w.h T σ)).re - 2 * t * t2 W (TMA.Kfull w.h T σ)
        + t ^ 2 * (TMA.Kfull w.h T σ 0).re)) :=
    (((Complex.continuous_re.tendsto _).comp l3).sub (l2.const_mul (2 * t))).add
      (((Complex.continuous_re.tendsto _).comp l1).const_mul (t ^ 2))
  obtain ⟨s₀, hs₀⟩ := exists_zfin_window T
  refine ge_of_tendsto lim (Filter.eventually_atTop.mpr ⟨s₀, fun s hs => ?_⟩)
  exact hL (zfin s) (hs₀ s hs)

/-- The Gram step with retained pairs, for the full kernel of the zeros. -/
theorem phiSum_pairs_le_Xi (hRH : RiemannHypothesis) (w : TMA.HeightWeight) {T t σ : ℝ}
    (hT : 1 < T) (hσ : 0 < σ) (ht1 : 1 ≤ t) (ht2 : t < 2)
    (htη : t ≤ 1 + (Range5Zeros.ShiftedCubicSpacing.eta : ℝ))
    (hg : (1 + (Range5Zeros.ShiftedCubicSpacing.eta : ℝ)) *
        (1 + (Range5Zeros.ShiftedCubicSpacing.eta : ℝ) - t) ^ 2
      ≤ 4 * (2 - t) * (Range5Zeros.ShiftedCubicSpacing.eta : ℝ) ^ 2) :
    ∃ m : ℕ,
      (Zeta23.Ndist T (2 * T) : ℝ) - 2 - 2 * (σ * Real.log T / (2 * Real.pi) * T) / 3
          ≤ 3 * (m : ℝ) ∧
      ThirdMoment.phiSum t T (2 * T) + (m : ℝ) *
          ((1 + (Range5Zeros.ShiftedCubicSpacing.eta : ℝ)) *
            (1 + (Range5Zeros.ShiftedCubicSpacing.eta : ℝ) - t) ^ 2)
        ≤ (t3 W3 (TMA.Kfull w.h T σ)).re - 2 * t * t2 W3 (TMA.Kfull w.h T σ)
            + t ^ 2 * (TMA.Kfull w.h T σ 0).re := by
  obtain ⟨m, hm, h⟩ := phiSum_pairs_le_Kfin hRH w hT hσ ht1 ht2 htη hg
  exact ⟨m, hm, le_Xi_of_le_Kfin hRH W3 w (by linarith) h⟩

end TMG.PairGain

end
end Src_Devine_ConditionalShiftedCubicGramZeros

section Src_Devine_ConditionalShiftedCubicTransfer


/-!
# Transfer of the retained pairs to both distinct-zero counts (T041-0074, Sections 3 and 4)

With `g = (1 + eta)(1 + eta - t)^2`, the Gram step with retained pairs and
`3 m ≥ D - 2 - (2/3) sigma Dsc` give the additive budget

    phiSum t T (2T) + (g/3) Ndist T (2T) ≤ (C3 - 2 t C2 + t^2 + 2g/9 + eps) N(T, 2T)

at every bandwidth `sigma < 1` (`budget_sigma_pairs`). The limit `sigma → 1`
is taken exactly as in the leader's `budget_dyadic` (`budget_dyadic_pairs`).
The left side is additive over adjacent windows, so the leader's
`Cumulative.dyadic_upper` gives the same budget on `(0, T]`.

With `H = 2(2-t)^2`, the inequality `phi(m) ≥ H (m - 1)` gives
`H (N - D) + (g/3) D ≤ (K + eps) N`. Hence
`D ≥ ((H - K)/(H - g/3) - eps) N`. At the leader's window `W3` and shift
`tStar`, this ratio exceeds `421389757897 / 500000000000`.
-/

open scoped BigOperators Real

noncomputable section

namespace TMG.PairGain

section Transfer

local notation "η₀" => ((Range5Zeros.ShiftedCubicSpacing.eta : ℚ) : ℝ)

/-- The third-moment budget with retained pairs on dyadic windows. -/
def PairBudget (t K c : ℝ) : Prop :=
  ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
    ThirdMoment.phiSum t T (2 * T) + c * (Zeta23.Ndist T (2 * T) : ℝ)
      ≤ (K + ε) * (Zeta23.Ncount T (2 * T) : ℝ)

theorem Dsc_large {a b : ℝ} (hb : 0 < b) : ∃ T₁ : ℝ, ∀ T ≥ T₁, a ≤ b * TMA.Dsc T := by
  refine ⟨max 3 (2 * Real.pi * |a| / b), fun T hT => ?_⟩
  have hT3 : 3 ≤ T := le_trans (le_max_left _ _) hT
  have hTa : 2 * Real.pi * |a| / b ≤ T := le_trans (le_max_right _ _) hT
  have hTpos : 0 < T := by linarith
  have hπ : 0 < 2 * Real.pi := by positivity
  have hlog : 1 ≤ Real.log T := by
    rw [Real.le_log_iff_exp_le hTpos]
    have h3 : Real.exp 1 ≤ 3 := by linarith [Real.exp_one_lt_d9]
    linarith
  have h1 : 2 * Real.pi * |a| ≤ T * b := (div_le_iff₀ hb).mp hTa
  have h2 : T ≤ T * Real.log T := by
    have := mul_le_mul_of_nonneg_left hlog hTpos.le
    linarith
  have h3 : |a| * (2 * Real.pi) ≤ b * (T * Real.log T) := by
    have := mul_le_mul_of_nonneg_left h2 hb.le
    linarith
  have h4 : |a| ≤ b * (T * Real.log T / (2 * Real.pi)) := by
    rw [mul_div_assoc', le_div_iff₀ hπ]
    exact h3
  unfold TMA.Dsc
  linarith [le_abs_self a]

/-- Bookkeeping for the retained pairs: `3 m ≥ D - 2 - (2/3) sigma Dsc`. -/
theorem pair_assemble {P Dc m D K0 η g σ ε : ℝ}
    (hP : P + m * g ≤ (K0 + η) * D)
    (hm : Dc - 2 - 2 * (σ * D) / 3 ≤ 3 * m) (hg : 0 ≤ g) (hσ1 : σ ≤ 1) (hD : 0 ≤ D)
    (hc0 : 2 * g / 3 ≤ ε / 4 * D) :
    P + g / 3 * Dc ≤ (K0 + 2 * g / 9 + (η + ε / 4)) * D := by
  have h1 : g / 3 * Dc ≤ g / 3 * (3 * m + 2 + 2 * (σ * D) / 3) :=
    mul_le_mul_of_nonneg_left (by linarith) (div_nonneg hg (by norm_num))
  have h2 : g * (σ * D) ≤ g * D := mul_le_mul_of_nonneg_left (mul_le_of_le_one_left hD hσ1) hg
  linarith

open MainAux in
/-- The budget with retained pairs at bandwidth `sigma < 1`. This is the
leader's `budget_sigma` with the Gram step `phiSum_pairs_le_Xi`. -/
theorem budget_sigma_pairs (hRH : RiemannHypothesis) {σ t : ℝ} (hσ : 0 < σ) (hσ1 : σ < 1)
    (ht1 : 1 ≤ t) (ht2 : t < 2) (htη : t ≤ 1 + η₀)
    (hg : (1 + η₀) * (1 + η₀ - t) ^ 2 ≤ 4 * (2 - t) * η₀ ^ 2) :
    PairBudget t (C3 W3 σ - 2 * t * C2 W3 σ + t ^ 2 + 2 * ((1 + η₀) * (1 + η₀ - t) ^ 2) / 9)
      ((1 + η₀) * (1 + η₀ - t) ^ 2 / 3) := by
  intro ε hε
  have ht : 0 ≤ t := by linarith
  have heta : 0 ≤ η₀ := by norm_num [Range5Zeros.ShiftedCubicSpacing.eta]
  have hg0 : 0 ≤ (1 + η₀) * (1 + η₀ - t) ^ 2 := mul_nonneg (by linarith) (sq_nonneg _)
  have hC3 : 0 ≤ C3 W3 σ := C3_nonneg W3 σ
  have hC2 : 0 ≤ C2 W3 σ := C2_nonneg W3 hσ
  have hε2 : 0 < ε / 2 := by linarith
  obtain ⟨ε1, hε1pos, hε1le⟩ := exists_small_mul hε2 (add_nonneg hC3 (sq_nonneg t))
  obtain ⟨δ, hδpos, hδle⟩ := exists_small_mul hε2 (sq_nonneg (1 + t))
  obtain ⟨θ, hθpos, hθK⟩ : ∃ θ : ℝ, 0 < θ ∧
      θ * (|C3 W3 σ - 2 * t * C2 W3 σ + t ^ 2 + 2 * ((1 + η₀) * (1 + η₀ - t) ^ 2) / 9| + ε)
        ≤ ε / 2 := by
    have hden : 0 < |C3 W3 σ - 2 * t * C2 W3 σ + t ^ 2 + 2 * ((1 + η₀) * (1 + η₀ - t) ^ 2) / 9|
        + ε := by positivity
    refine ⟨ε / (2 * (|C3 W3 σ - 2 * t * C2 W3 σ + t ^ 2
      + 2 * ((1 + η₀) * (1 + η₀ - t) ^ 2) / 9| + ε)), by positivity, le_of_eq ?_⟩
    field_simp
  obtain ⟨w, hw1, hw3⟩ := TMA.exists_heightWeight hε1pos
  obtain ⟨Ta, ha⟩ := TMA.t1_upper hRH w hσ hσ1 δ hδpos
  obtain ⟨Tb, hb⟩ := t2_lower hRH W3 w hσ hσ1 δ hδpos
  obtain ⟨Tc, hc⟩ := t3_upper hRH W3 w hσ hσ1 δ hδpos
  obtain ⟨Td, hd⟩ := rvm_Dsc_le hθpos
  obtain ⟨Te, he⟩ := Dsc_large (a := 2 * ((1 + η₀) * (1 + η₀ - t) ^ 2) / 3) (b := ε / 4)
    (by linarith)
  refine ⟨max Ta (max Tb (max Tc (max Td (max Te 2)))), fun T hT => ?_⟩
  simp only [ge_iff_le, max_le_iff] at hT
  obtain ⟨hTa, hTb, hTc, hTd, hTe, hT2⟩ := hT
  obtain ⟨hTpos, hDpos, hDN⟩ := hd T hTd
  obtain ⟨m, hm, hXi⟩ := phiSum_pairs_le_Xi hRH w (by linarith : (1 : ℝ) < T) hσ ht1 ht2 htη hg
  have hP := assemble_real hXi (hc T hTc) (hb T hTb) (ha T hTa) hDpos.le ht hC3 hC2 hw1 hw3
    w.one_le_kap2
  have hσD : σ * Real.log T / (2 * Real.pi) * T = σ * TMA.Dsc T := by
    unfold TMA.Dsc
    ring
  rw [hσD] at hm
  have hA := pair_assemble hP hm hg0 hσ1.le hDpos.le (he T hTe)
  have hP0 : 0 ≤ ThirdMoment.phiSum t T (2 * T)
      + (1 + η₀) * (1 + η₀ - t) ^ 2 / 3 * (Zeta23.Ndist T (2 * T) : ℝ) :=
    add_nonneg (phiSum_nonneg t T (2 * T))
      (mul_nonneg (div_nonneg hg0 (by norm_num)) (Nat.cast_nonneg _))
  exact final_real hP0 hA hDpos hDN hθpos.le (by linarith) hθK hε (Nat.cast_nonneg _)

open MainAux in
/-- The budget with retained pairs at full bandwidth, as in the leader's `budget_dyadic`. -/
theorem budget_dyadic_pairs (hRH : RiemannHypothesis) {t : ℝ} (ht1 : 1 ≤ t) (ht2 : t < 2)
    (htη : t ≤ 1 + η₀) (hg : (1 + η₀) * (1 + η₀ - t) ^ 2 ≤ 4 * (2 - t) * η₀ ^ 2) :
    PairBudget t (Kt W3 t + 2 * ((1 + η₀) * (1 + η₀ - t) ^ 2) / 9)
      ((1 + η₀) * (1 + η₀ - t) ^ 2 / 3) := by
  unfold Kt
  intro ε hε
  have ht : 0 ≤ t := by linarith
  have hM : 0 ≤ 8 * I3 W3 + 2 * t * J2 W3 := by
    have h1 := mul_nonneg ht (J2_nonneg W3)
    have h2 := I3_nonneg W3
    linarith
  obtain ⟨s, hs0, hs1, hsM⟩ :
      ∃ s : ℝ, 0 < s ∧ s ≤ 1 / 2 ∧ (8 * I3 W3 + 2 * t * J2 W3) * s ≤ ε / 2 := by
    obtain ⟨x, hx0, hxM⟩ := exists_small_mul hε hM
    refine ⟨min x (1 / 2), lt_min hx0 (by norm_num), min_le_right _ _, ?_⟩
    have h1 : (8 * I3 W3 + 2 * t * J2 W3) * min x (1 / 2) ≤ (8 * I3 W3 + 2 * t * J2 W3) * x :=
      mul_le_mul_of_nonneg_left (min_le_left _ _) hM
    linarith
  have hσ : (1 : ℝ) / 2 ≤ 1 - s := by linarith
  have hσ1 : 1 - s < 1 := by linarith
  have hK := const_le_one W3 hσ hσ1 ht
  rw [sub_sub_cancel] at hK
  obtain ⟨T₀, h₀⟩ :=
    budget_sigma_pairs hRH (by linarith : (0 : ℝ) < 1 - s) hσ1 ht1 ht2 htη hg (ε / 2)
      (by linarith)
  refine ⟨T₀, fun T hT => ?_⟩
  have hN : (0 : ℝ) ≤ (Zeta23.Ncount T (2 * T) : ℝ) := Nat.cast_nonneg _
  have h1 := h₀ T hT
  have h2 : (C3 W3 (1 - s) - 2 * t * C2 W3 (1 - s) + t ^ 2
        + 2 * ((1 + η₀) * (1 + η₀ - t) ^ 2) / 9 + ε / 2) * (Zeta23.Ncount T (2 * T) : ℝ)
      ≤ (C3 W3 1 - 2 * t * C2 W3 1 + t ^ 2 + 2 * ((1 + η₀) * (1 + η₀ - t) ^ 2) / 9 + ε)
        * (Zeta23.Ncount T (2 * T) : ℝ) :=
    mul_le_mul_of_nonneg_right (by linarith) hN
  exact le_trans h1 h2

/-! ### The multiplicity deficit and the counts -/

theorem phi_ge_deficit {t : ℝ} (ht1 : 1 ≤ t) (ht2 : t < 2) (m : ℕ) (hm : 1 ≤ m) :
    2 * (2 - t) ^ 2 * ((m : ℝ) - 1) ≤ ThirdMoment.phi t m := by
  rcases Nat.lt_or_ge m 2 with h | h
  · have e : m = 1 := by omega
    subst e
    rw [Nat.cast_one, ThirdMoment.phi_one ht1]
    norm_num
  · rcases Nat.lt_or_ge m 3 with h3 | h3
    · have e : m = 2 := by omega
      subst e
      have h2 : t ≤ ((2 : ℕ) : ℝ) := by push_cast; linarith
      rw [ThirdMoment.phi_of_le h2]
      push_cast
      nlinarith [sq_nonneg (2 - t)]
    · have hm3 : (3 : ℝ) ≤ m := by exact_mod_cast h3
      rw [ThirdMoment.phi_of_le (by linarith)]
      have hsq : (2 * (2 - t)) ^ 2 ≤ ((m : ℝ) - t) ^ 2 :=
        pow_le_pow_left₀ (by linarith) (by linarith) 2
      have hmul := mul_le_mul_of_nonneg_left hsq (Nat.cast_nonneg m)
      have hpos : 0 ≤ (2 - t) ^ 2 * (2 * (m : ℝ) + 2) := mul_nonneg (sq_nonneg _) (by positivity)
      nlinarith [hmul, hpos]

/-- `2 (2 - t)^2 (N - D) ≤ phiSum` on every window. -/
theorem deficit_le_phiSum {t : ℝ} (ht1 : 1 ≤ t) (ht2 : t < 2) (a b : ℝ) :
    2 * (2 - t) ^ 2 * ((Zeta23.Ncount a b : ℝ) - (Zeta23.Ndist a b : ℝ))
      ≤ ThirdMoment.phiSum t a b := by
  rw [ThirdMoment.Ncount_eq, ThirdMoment.Ndist_eq, ThirdMoment.phiSum_eq]
  have h : ∀ ρ ∈ ThirdMoment.zerosFinset a b,
      2 * (2 - t) ^ 2 * ((Zeta23.zeroMult ρ : ℝ) - 1) ≤ ThirdMoment.phi t (Zeta23.zeroMult ρ) :=
    fun ρ hρ => phi_ge_deficit ht1 ht2 _ (ThirdMoment.one_le_mult_of_mem hρ)
  have hsum := Finset.sum_le_sum h
  rw [← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_one] at hsum
  exact hsum

/-- Division by `H - c > 0`. -/
theorem count_alg {H K c ε N D Φ : ℝ} (hHc : 0 < H - c) (hdef : H * (N - D) ≤ Φ)
    (hbud : Φ + c * D ≤ (K + ε * (H - c)) * N) :
    ((H - K) / (H - c) - ε) * N ≤ D := by
  have key : (H - K - ε * (H - c)) * N ≤ (H - c) * D := by linarith
  have hX : (H - K) / (H - c) * (H - c) = H - K := div_mul_cancel₀ _ hHc.ne'
  have hXN : (H - K) / (H - c) * (H - c) * N = (H - K) * N := by rw [hX]
  have key2 : (H - c) * (((H - K) / (H - c) - ε) * N) ≤ (H - c) * D := by linarith
  exact le_of_mul_le_mul_left key2 hHc

theorem distinct_of_pairBudget {t K c : ℝ} (ht1 : 1 ≤ t) (ht2 : t < 2)
    (hcH : c < 2 * (2 - t) ^ 2) (hB : PairBudget t K c) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      ((2 * (2 - t) ^ 2 - K) / (2 * (2 - t) ^ 2 - c) - ε) * (Zeta23.Ncount T (2 * T) : ℝ)
        ≤ (Zeta23.Ndist T (2 * T) : ℝ) := by
  intro ε hε
  have hHc : 0 < 2 * (2 - t) ^ 2 - c := by linarith
  obtain ⟨T₀, h₀⟩ := hB (ε * (2 * (2 - t) ^ 2 - c)) (mul_pos hε hHc)
  exact ⟨T₀, fun T hT => count_alg hHc (deficit_le_phiSum ht1 ht2 T (2 * T)) (h₀ T hT)⟩

theorem Ndist_add_real {a b d : ℝ} (hab : a ≤ b) (hbd : b ≤ d) :
    (Zeta23.Ndist a d : ℝ) = (Zeta23.Ndist a b : ℝ) + (Zeta23.Ndist b d : ℝ) := by
  have h : Zeta23.Ndist a d = Zeta23.Ndist a b + Zeta23.Ndist b d := by
    unfold Zeta23.Ndist
    rw [Zeta23.zerosIn_union hab hbd]
    refine Set.ncard_union_eq ?_ (Zeta23.zerosIn_finite a b) (Zeta23.zerosIn_finite b d)
    rw [Set.disjoint_left]
    rintro ρ ⟨_, _, hb⟩ ⟨_, ha, _⟩
    exact absurd hb (not_le.2 ha)
  exact_mod_cast h

/-- The dyadic budget with retained pairs gives the same budget on `(0, T]`. -/
theorem pairBudget_cumulative {t K c : ℝ} (hc : 0 ≤ c) (hB : PairBudget t K c) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      ThirdMoment.phiSum t 0 T + c * (Zeta23.Ndist 0 T : ℝ) ≤ (K + ε) * (Zeta23.Ncount 0 T : ℝ) :=
  Cumulative.dyadic_upper (f := fun a b => ThirdMoment.phiSum t a b + c * (Zeta23.Ndist a b : ℝ))
    (g := fun a b => (Zeta23.Ncount a b : ℝ)) (c := K)
    (fun a b d hab hbd => by
      show ThirdMoment.phiSum t a d + c * (Zeta23.Ndist a d : ℝ)
        = (ThirdMoment.phiSum t a b + c * (Zeta23.Ndist a b : ℝ))
          + (ThirdMoment.phiSum t b d + c * (Zeta23.Ndist b d : ℝ))
      rw [Cumulative.phiSum_add t hab hbd, Ndist_add_real hab hbd]
      ring)
    (fun a b d hab hbd => by exact_mod_cast Zeta23.Ncount_add hab hbd)
    (fun a b => add_nonneg (Cumulative.phiSum_nonneg t a b) (mul_nonneg hc (Nat.cast_nonneg _)))
    (fun _ _ => Nat.cast_nonneg _)
    (Zeta23.tendsto_Ncount_zero_atTop Zeta23.zetaSeam Zeta23.riemannVonMangoldt_zeta) hB

theorem distinct_cumulative_of_pairBudget {t K c : ℝ} (ht1 : 1 ≤ t) (ht2 : t < 2) (hc : 0 ≤ c)
    (hcH : c < 2 * (2 - t) ^ 2) (hB : PairBudget t K c) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      ((2 * (2 - t) ^ 2 - K) / (2 * (2 - t) ^ 2 - c) - ε) * (Zeta23.Ncount 0 T : ℝ)
        ≤ (Zeta23.Ndist 0 T : ℝ) := by
  intro ε hε
  have hHc : 0 < 2 * (2 - t) ^ 2 - c := by linarith
  obtain ⟨T₀, h₀⟩ := pairBudget_cumulative hc hB (ε * (2 * (2 - t) ^ 2 - c)) (mul_pos hε hHc)
  exact ⟨T₀, fun T hT => count_alg hHc (deficit_le_phiSum ht1 ht2 0 T) (h₀ T hT)⟩

/-! ### The constants at the leader's window and shift -/

theorem tStar_pair_facts : 1 ≤ tStar ∧ tStar < 2 ∧ tStar ≤ 1 + η₀ ∧
    (1 + η₀) * (1 + η₀ - tStar) ^ 2 ≤ 4 * (2 - tStar) * η₀ ^ 2 ∧
    0 ≤ (1 + η₀) * (1 + η₀ - tStar) ^ 2 / 3 ∧
    (1 + η₀) * (1 + η₀ - tStar) ^ 2 / 3 < 2 * (2 - tStar) ^ 2 := by
  unfold tStar
  norm_num [Range5Zeros.ShiftedCubicSpacing.eta, Rat.cast_div, Rat.cast_ofNat]

/-- The new constant exceeds `421389757897 / 500000000000 = 0.842779515794`. -/
theorem pair_record_value :
    (421389757897 / 500000000000 : ℝ) <
      (2 * (2 - tStar) ^ 2 - (Kt W3 tStar + 2 * ((1 + η₀) * (1 + η₀ - tStar) ^ 2) / 9)) /
        (2 * (2 - tStar) ^ 2 - (1 + η₀) * (1 + η₀ - tStar) ^ 2 / 3) := by
  unfold Kt
  rw [C2_W3, C3_W3]
  unfold tStar
  norm_num [Range5Zeros.ShiftedCubicSpacing.eta, Rat.cast_div, Rat.cast_ofNat]

/-- **Distinct zeros on `(T, 2T]` under RH:** at least `0.842779515794 - eps` of the
zeros counted with multiplicity, for all sufficiently large `T`. -/
theorem pair_distinct_dyadic (hRH : RiemannHypothesis) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      ((421389757897 / 500000000000 : ℝ) - ε) * (Zeta23.Ncount T (2 * T) : ℝ)
        ≤ (Zeta23.Ndist T (2 * T) : ℝ) := by
  obtain ⟨h1, h2, h3, h4, _, h6⟩ := tStar_pair_facts
  intro ε hε
  obtain ⟨T₀, h⟩ := distinct_of_pairBudget h1 h2 h6 (budget_dyadic_pairs hRH h1 h2 h3 h4) ε hε
  refine ⟨T₀, fun T hT => le_trans ?_ (h T hT)⟩
  exact mul_le_mul_of_nonneg_right (by linarith [pair_record_value]) (Nat.cast_nonneg _)

/-- **Distinct zeros on `(0, T]` under RH.** -/
theorem pair_distinct_cumulative (hRH : RiemannHypothesis) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      ((421389757897 / 500000000000 : ℝ) - ε) * (Zeta23.Ncount 0 T : ℝ)
        ≤ (Zeta23.Ndist 0 T : ℝ) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := tStar_pair_facts
  intro ε hε
  obtain ⟨T₀, h⟩ :=
    distinct_cumulative_of_pairBudget h1 h2 h5 h6 (budget_dyadic_pairs hRH h1 h2 h3 h4) ε hε
  refine ⟨T₀, fun T hT => le_trans ?_ (h T hT)⟩
  exact mul_le_mul_of_nonneg_right (by linarith [pair_record_value]) (Nat.cast_nonneg _)

/-- The dyadic statement for critical-line zeros (`N0star = Ndist` under RH). -/
theorem pair_critical_line_dyadic (hRH : RiemannHypothesis) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      ((421389757897 / 500000000000 : ℝ) - ε) * (Zeta23.Ncount T (2 * T) : ℝ)
        ≤ Zeta23.N0star T (2 * T) := by
  intro ε hε
  obtain ⟨T₀, h⟩ := pair_distinct_dyadic hRH ε hε
  refine ⟨T₀, fun T hT => ?_⟩
  rw [(Zeta23.RH_implies_all_on_line hRH T (2 * T)).2]
  exact h T hT

/-- The cumulative statement for critical-line zeros. -/
theorem pair_critical_line_cumulative (hRH : RiemannHypothesis) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      ((421389757897 / 500000000000 : ℝ) - ε) * (Zeta23.Ncount 0 T : ℝ)
        ≤ Zeta23.N0star 0 T := by
  intro ε hε
  obtain ⟨T₀, h⟩ := pair_distinct_cumulative hRH ε hε
  refine ⟨T₀, fun T hT => ?_⟩
  rw [(Zeta23.RH_implies_all_on_line hRH 0 T).2]
  exact h T hT

end Transfer

end TMG.PairGain

end
end Src_Devine_ConditionalShiftedCubicTransfer


section Src_BeiYiFrozenOctic

/- Original general third-moment framework and cutoff identities by Kristian Muri Knausgård.
   Apache-2.0 §4(b) modification by 贝奕 (Bei Yi), 2026-11-22.
   Add the frozen, unit-mass octic window and its exact integrals.
   All original upstream and sextic-candidate notices are retained.
   SPDX-License-Identifier: Apache-2.0 -/
open MeasureTheory
namespace DevineDegree32
noncomputable section
open TMG.PolyAux (cut cut_pos cut_neg cut_pow integral_cut integral_integral_abs_cut measurable_cut)

set_option maxHeartbeats 0
set_option maxRecDepth 16000


def q (u : ℝ) : ℝ := (120442038807691126445521663 / 107374182400000000000000000) * u ^ 0 + (-21880815954788081037201 / 13107200000000000000000) * u ^ 2 + (245568575373413537892311 / 167772160000000000000000) * u ^ 4 + (-26442595365396232982421 / 52428800000000000000000) * u ^ 6 + (4163967043535719776213 / 4194304000000000000000) * u ^ 8 + (-4070655085035826724723 / 1638400000000000000000) * u ^ 10 + (4529476148191948428657 / 3276800000000000000000) * u ^ 12 + (1621744705501989813 / 1638400000000000000) * u ^ 14 + (-4930650918923353299 / 32768000000000000000) * u ^ 16 + (65875087890281439 / 128000000000000000) * u ^ 18 + (-2068703240142357819 / 512000000000000000) * u ^ 20 + (-735791782466109447 / 160000000000000000) * u ^ 22 + (1950841680607749501 / 64000000000000000) * u ^ 24 + (-1900049869174041963 / 25000000000000000) * u ^ 26 + (1805282199044482851 / 10000000000000000) * u ^ 28 + (-879592825388656841 / 3125000000000000) * u ^ 30 + (916312070471295267 / 5000000000000000) * u ^ 32

def P (u : ℝ) : ℝ := (151716888786467940982014947 / 644245094400000000000000000) * u ^ 0 + (120442038807691126445521663 / 107374182400000000000000000) * u ^ 2 + (-7293605318262693679067 / 26214400000000000000000) * u ^ 4 + (245568575373413537892311 / 2516582400000000000000000) * u ^ 6 + (-3777513623628033283203 / 209715200000000000000000) * u ^ 8 + (462663004837302197357 / 20971520000000000000000) * u ^ 10 + (-370059553185075156793 / 9830400000000000000000) * u ^ 12 + (49774463166944488227 / 3276800000000000000000) * u ^ 14 + (540581568500663271 / 65536000000000000000) * u ^ 16 + (-32226476594270283 / 32768000000000000000) * u ^ 18 + (3467109888962181 / 1280000000000000000) * u ^ 20 + (-8955425282001549 / 512000000000000000) * u ^ 22 + (-10663649021247963 / 640000000000000000) * u ^ 24 + (150064744662134577 / 1600000000000000000) * u ^ 26 + (-10053173910973767 / 50000000000000000) * u ^ 28 + (20750370103959573 / 50000000000000000) * u ^ 30 + (-28373962109311511 / 50000000000000000) * u ^ 32 + (1633354849324947 / 5000000000000000) * u ^ 34

theorem q_cont : Continuous q := by unfold q; fun_prop

theorem q_positive_lower (u : ℝ) (hu : |u| ≤ 1/2) : 1/2 ≤ q u := by
  have hz : 0 ≤ 1-4*u^2 := by linarith [TMG.PolyAux.sq_le_of_abs hu]
  apply sub_nonneg.mp
  rw [show q u - 1/2 = (66754947607691126445521663 / 107374182400000000000000000) * (4*u^2)^0 * (1-4*u^2)^16 + (12790840633095650414551987 / 1342177280000000000000000) * (4*u^2)^1 * (1-4*u^2)^15 + (45926486186292386659471733 / 671088640000000000000000) * (4*u^2)^2 * (1-4*u^2)^14 + (256360876848022037226692851 / 838860800000000000000000) * (4*u^2)^3 * (1-4*u^2)^13 + (398390121086248823102066379 / 419430400000000000000000) * (4*u^2)^4 * (1-4*u^2)^12 + (114224397710154949559536857 / 52428800000000000000000) * (4*u^2)^5 * (1-4*u^2)^11 + (50002278721341599183390041 / 13107200000000000000000) * (4*u^2)^6 * (1-4*u^2)^10 + (426125151098366801573659 / 81920000000000000000) * (4*u^2)^7 * (1-4*u^2)^9 + (9145279424525763682135041 / 1638400000000000000000) * (4*u^2)^8 * (1-4*u^2)^8 + (60536859645085138825891 / 12800000000000000000) * (4*u^2)^9 * (1-4*u^2)^7 + (322921967504026187493203 / 102400000000000000000) * (4*u^2)^10 * (1-4*u^2)^6 + (20958295312366236166423 / 12800000000000000000) * (4*u^2)^11 * (1-4*u^2)^5 + (166134499878053980259 / 256000000000000000) * (4*u^2)^12 * (1-4*u^2)^4 + (303690524176868191869 / 1600000000000000000) * (4*u^2)^13 * (1-4*u^2)^3 + (15453325897441142583 / 400000000000000000) * (4*u^2)^14 * (1-4*u^2)^2 + (244457042948201249 / 50000000000000000) * (4*u^2)^15 * (1-4*u^2)^1 + (28980680731781047 / 100000000000000000) * (4*u^2)^16 * (1-4*u^2)^0 by unfold q; ring]
  positivity

theorem q_bound (u : ℝ) (hu : |u| ≤ 1/2) : q u ≤ 2 := by
  have hz : 0 ≤ 1-4*u^2 := by linarith [TMG.PolyAux.sq_le_of_abs hu]
  apply sub_nonneg.mp
  rw [show 2 - q u = (94306325992308873554478337 / 107374182400000000000000000) * (4*u^2)^0 * (1-4*u^2)^16 + (19421414086904349585448013 / 1342177280000000000000000) * (4*u^2)^1 * (1-4*u^2)^15 + (74869469013707613340528267 / 671088640000000000000000) * (4*u^2)^2 * (1-4*u^2)^14 + (448282195151977962773307149 / 838860800000000000000000) * (4*u^2)^3 * (1-4*u^2)^13 + (746654870913751176897933621 / 419430400000000000000000) * (4*u^2)^4 * (1-4*u^2)^12 + (229289099889845050440463143 / 52428800000000000000000) * (4*u^2)^5 * (1-4*u^2)^11 + (107441407678658400816609959 / 13107200000000000000000) * (4*u^2)^6 * (1-4*u^2)^10 + (979622048901633198426341 / 81920000000000000000) * (4*u^2)^7 * (1-4*u^2)^9 + (22484032575474236317864959 / 1638400000000000000000) * (4*u^2)^8 * (1-4*u^2)^8 + (159111140354914861174109 / 12800000000000000000) * (4*u^2)^9 * (1-4*u^2)^7 + (907106832495973812506797 / 102400000000000000000) * (4*u^2)^10 * (1-4*u^2)^6 + (62907304687633763833577 / 12800000000000000000) * (4*u^2)^11 * (1-4*u^2)^5 + (532745500121946019741 / 256000000000000000) * (4*u^2)^12 * (1-4*u^2)^4 + (1040309475823131808131 / 1600000000000000000) * (4*u^2)^13 * (1-4*u^2)^3 + (56546674102558857417 / 400000000000000000) * (4*u^2)^14 * (1-4*u^2)^2 + (955542957051798751 / 50000000000000000) * (4*u^2)^15 * (1-4*u^2)^1 + (121019319268218953 / 100000000000000000) * (4*u^2)^16 * (1-4*u^2)^0 by unfold q; ring]
  positivity

theorem inner_q (u : ℝ) : (∫ w in (-(1/2:ℝ))..u, (u-w)*q w) + (∫ w in u..(1/2:ℝ), (w-u)*q w) = P u := by

  have L (w : ℝ) : (u-w)*q w = ((120442038807691126445521663 / 107374182400000000000000000) * u) * w ^ 0 + (-120442038807691126445521663 / 107374182400000000000000000) * w ^ 1 + ((-21880815954788081037201 / 13107200000000000000000) * u) * w ^ 2 + (21880815954788081037201 / 13107200000000000000000) * w ^ 3 + ((245568575373413537892311 / 167772160000000000000000) * u) * w ^ 4 + (-245568575373413537892311 / 167772160000000000000000) * w ^ 5 + ((-26442595365396232982421 / 52428800000000000000000) * u) * w ^ 6 + (26442595365396232982421 / 52428800000000000000000) * w ^ 7 + ((4163967043535719776213 / 4194304000000000000000) * u) * w ^ 8 + (-4163967043535719776213 / 4194304000000000000000) * w ^ 9 + ((-4070655085035826724723 / 1638400000000000000000) * u) * w ^ 10 + (4070655085035826724723 / 1638400000000000000000) * w ^ 11 + ((4529476148191948428657 / 3276800000000000000000) * u) * w ^ 12 + (-4529476148191948428657 / 3276800000000000000000) * w ^ 13 + ((1621744705501989813 / 1638400000000000000) * u) * w ^ 14 + (-1621744705501989813 / 1638400000000000000) * w ^ 15 + ((-4930650918923353299 / 32768000000000000000) * u) * w ^ 16 + (4930650918923353299 / 32768000000000000000) * w ^ 17 + ((65875087890281439 / 128000000000000000) * u) * w ^ 18 + (-65875087890281439 / 128000000000000000) * w ^ 19 + ((-2068703240142357819 / 512000000000000000) * u) * w ^ 20 + (2068703240142357819 / 512000000000000000) * w ^ 21 + ((-735791782466109447 / 160000000000000000) * u) * w ^ 22 + (735791782466109447 / 160000000000000000) * w ^ 23 + ((1950841680607749501 / 64000000000000000) * u) * w ^ 24 + (-1950841680607749501 / 64000000000000000) * w ^ 25 + ((-1900049869174041963 / 25000000000000000) * u) * w ^ 26 + (1900049869174041963 / 25000000000000000) * w ^ 27 + ((1805282199044482851 / 10000000000000000) * u) * w ^ 28 + (-1805282199044482851 / 10000000000000000) * w ^ 29 + ((-879592825388656841 / 3125000000000000) * u) * w ^ 30 + (879592825388656841 / 3125000000000000) * w ^ 31 + ((916312070471295267 / 5000000000000000) * u) * w ^ 32 + (-916312070471295267 / 5000000000000000) * w ^ 33 := by unfold q; ring

  have R (w : ℝ) : (w-u)*q w = ((-120442038807691126445521663 / 107374182400000000000000000) * u) * w ^ 0 + (120442038807691126445521663 / 107374182400000000000000000) * w ^ 1 + ((21880815954788081037201 / 13107200000000000000000) * u) * w ^ 2 + (-21880815954788081037201 / 13107200000000000000000) * w ^ 3 + ((-245568575373413537892311 / 167772160000000000000000) * u) * w ^ 4 + (245568575373413537892311 / 167772160000000000000000) * w ^ 5 + ((26442595365396232982421 / 52428800000000000000000) * u) * w ^ 6 + (-26442595365396232982421 / 52428800000000000000000) * w ^ 7 + ((-4163967043535719776213 / 4194304000000000000000) * u) * w ^ 8 + (4163967043535719776213 / 4194304000000000000000) * w ^ 9 + ((4070655085035826724723 / 1638400000000000000000) * u) * w ^ 10 + (-4070655085035826724723 / 1638400000000000000000) * w ^ 11 + ((-4529476148191948428657 / 3276800000000000000000) * u) * w ^ 12 + (4529476148191948428657 / 3276800000000000000000) * w ^ 13 + ((-1621744705501989813 / 1638400000000000000) * u) * w ^ 14 + (1621744705501989813 / 1638400000000000000) * w ^ 15 + ((4930650918923353299 / 32768000000000000000) * u) * w ^ 16 + (-4930650918923353299 / 32768000000000000000) * w ^ 17 + ((-65875087890281439 / 128000000000000000) * u) * w ^ 18 + (65875087890281439 / 128000000000000000) * w ^ 19 + ((2068703240142357819 / 512000000000000000) * u) * w ^ 20 + (-2068703240142357819 / 512000000000000000) * w ^ 21 + ((735791782466109447 / 160000000000000000) * u) * w ^ 22 + (-735791782466109447 / 160000000000000000) * w ^ 23 + ((-1950841680607749501 / 64000000000000000) * u) * w ^ 24 + (1950841680607749501 / 64000000000000000) * w ^ 25 + ((1900049869174041963 / 25000000000000000) * u) * w ^ 26 + (-1900049869174041963 / 25000000000000000) * w ^ 27 + ((-1805282199044482851 / 10000000000000000) * u) * w ^ 28 + (1805282199044482851 / 10000000000000000) * w ^ 29 + ((879592825388656841 / 3125000000000000) * u) * w ^ 30 + (-879592825388656841 / 3125000000000000) * w ^ 31 + ((-916312070471295267 / 5000000000000000) * u) * w ^ 32 + (916312070471295267 / 5000000000000000) * w ^ 33 := by unfold q; ring

  simp_rw [L,R]
  simp (disch := exact Continuous.intervalIntegrable (by fun_prop) _ _) only [intervalIntegral.integral_add, intervalIntegral.integral_const_mul, integral_pow]
  unfold P
  ring

theorem normalization : (∫ u in (-(1/2:ℝ))..(1/2), q u) = (1) := by
  have he (u : ℝ) : q u = (120442038807691126445521663 / 107374182400000000000000000) * u ^ 0 + (-21880815954788081037201 / 13107200000000000000000) * u ^ 2 + (245568575373413537892311 / 167772160000000000000000) * u ^ 4 + (-26442595365396232982421 / 52428800000000000000000) * u ^ 6 + (4163967043535719776213 / 4194304000000000000000) * u ^ 8 + (-4070655085035826724723 / 1638400000000000000000) * u ^ 10 + (4529476148191948428657 / 3276800000000000000000) * u ^ 12 + (1621744705501989813 / 1638400000000000000) * u ^ 14 + (-4930650918923353299 / 32768000000000000000) * u ^ 16 + (65875087890281439 / 128000000000000000) * u ^ 18 + (-2068703240142357819 / 512000000000000000) * u ^ 20 + (-735791782466109447 / 160000000000000000) * u ^ 22 + (1950841680607749501 / 64000000000000000) * u ^ 24 + (-1900049869174041963 / 25000000000000000) * u ^ 26 + (1805282199044482851 / 10000000000000000) * u ^ 28 + (-879592825388656841 / 3125000000000000) * u ^ 30 + (916312070471295267 / 5000000000000000) * u ^ 32 := by unfold q; ring
  simp_rw [he]
  simp (disch := exact Continuous.intervalIntegrable (by fun_prop) _ _) only [intervalIntegral.integral_add, intervalIntegral.integral_const_mul, integral_pow]
  norm_num

def W : TMG.Window where
  g := cut q
  meas := measurable_cut q_cont
  nonneg := fun u => by
    by_cases hu : |u| ≤ 1 / 2
    · rw [cut_pos _ hu]
      exact le_trans (by norm_num : (0 : ℝ) ≤ (1 / 2)) (q_positive_lower u hu)
    · rw [cut_neg _ hu]
  bound := 2
  le_bound := fun u => by
    by_cases hu : |u| ≤ 1 / 2
    · rw [cut_pos _ hu]
      exact q_bound u hu
    · rw [cut_neg _ hu]
      norm_num
  supp := fun _ hu => cut_neg _ (not_le.mpr hu)
  integral_eq_one := by
    rw [integral_cut]
    exact normalization



theorem I2_polynomial : (∫ u in (-(1/2:ℝ))..(1/2), q u ^ 2) = (731896853529297298550210480358593843964234104741921 / 724279913802695250000000000000000000000000000000000) := by
  have he (u : ℝ) : q u ^ 2 = (14506284712153375339593605868574051490214628202285569 / 11529215046068469760000000000000000000000000000000000) * u ^ 0 + (-2635370084370533224299570031928242254598554385263 / 703687441776640000000000000000000000000000000000) * u ^ 2 + (273390610314751360665710378012395936585007342901709 / 45035996273704960000000000000000000000000000000000) * u ^ 4 + (-16940296550359552560186676527807887171216179154283 / 2814749767106560000000000000000000000000000000000) * u ^ 6 + (34078247905409106793390913219485564809802908886139 / 5629499534213120000000000000000000000000000000000) * u ^ 8 + (-911702596054235897957732357373501586386794874569 / 87960930222080000000000000000000000000000000000) * u ^ 10 + (2560869233302815804179879497612562226571586549547 / 175921860444160000000000000000000000000000000000) * u ^ 12 + (-117308447918416913523978994013003337255689335349 / 10995116277760000000000000000000000000000000000) * u ^ 14 + (171342688072542280593485778863411041853452029087 / 43980465111040000000000000000000000000000000000) * u ^ 16 + (-304571390266397086017859685073669260649467769 / 171798691840000000000000000000000000000000000) * u ^ 18 + (-2270561242697788646858918094603458891730042251 / 687194767360000000000000000000000000000000000) * u ^ 20 + (-3079853557796155681869734764072887352448331 / 42949672960000000000000000000000000000000000) * u ^ 22 + (5848328649947996699916171654869129999318340357 / 85899345920000000000000000000000000000000000) * u ^ 24 + (-371991766235120446390944157335966994037545119 / 1342177280000000000000000000000000000000000) * u ^ 26 + (1993416572556902481688504194251758998978202587 / 2684354560000000000000000000000000000000000) * u ^ 28 + (-247523358117450980032129022256386025451894733 / 167772160000000000000000000000000000000000) * u ^ 30 + (21789195706882504076905322078432259247728207 / 10737418240000000000000000000000000000000) * u ^ 32 + (-508868863176917285770115763305415496464547 / 262144000000000000000000000000000000000) * u ^ 34 + (17124852170710869462466783938511183010032671 / 10485760000000000000000000000000000000000) * u ^ 36 + (-1175273529749579458852244751400457969075481 / 655360000000000000000000000000000000000) * u ^ 38 + (2770281482131180372984825141083750473670701 / 1310720000000000000000000000000000000000) * u ^ 40 + (-25395012826248382373866170460710098704503 / 20480000000000000000000000000000000000) * u ^ 42 + (-3344828446057547642394226744524041108091 / 8192000000000000000000000000000000000) * u ^ 44 + (19806839983007907129584958208195729629 / 20480000000000000000000000000000000) * u ^ 46 + (-359478112026942898334306321318593420221 / 2048000000000000000000000000000000000) * u ^ 48 + (-6128972827553517992219390226552182097 / 1600000000000000000000000000000000) * u ^ 50 + (2862377364916827025555300175052310777119 / 160000000000000000000000000000000000) * u ^ 52 + (-92572020670638092273561146044261187773 / 2000000000000000000000000000000000) * u ^ 54 + (1730946595274045695385038665687483279171 / 20000000000000000000000000000000000) * u ^ 56 + (-1618538341989423416893262515962924777 / 12500000000000000000000000000000) * u ^ 58 + (90870793202198386889413697067064509409 / 625000000000000000000000000000000) * u ^ 60 + (-805981523003576639989202274650471547 / 7812500000000000000000000000000) * u ^ 62 + (839627810491391983594064608696601289 / 25000000000000000000000000000000) * u ^ 64 := by unfold q; ring
  simp_rw [he]
  simp (disch := exact Continuous.intervalIntegrable (by fun_prop) _ _) only [intervalIntegral.integral_add, intervalIntegral.integral_const_mul, integral_pow]
  norm_num

theorem I2_exact : TMG.I2 W = (731896853529297298550210480358593843964234104741921 / 724279913802695250000000000000000000000000000000000) := by
  rw [TMG.I2_eq]
  change (∫ u, (cut q u) ^ 2) = _
  simp_rw [cut_pow q (by decide : (2 : ℕ) ≠ 0)]
  rw [integral_cut]
  exact I2_polynomial


theorem I3_polynomial : (∫ u in (-(1/2:ℝ))..(1/2), q u ^ 3) = (324995203720220715071316961801168757086693102879344601839327579227150864704437694040039 / 315214370070676347134213184205513525195312500000000000000000000000000000000000000000000) := by
  have he (u : ℝ) : q u ^ 3 = (1747166506256593334178205684226858914146103571342652081293058382769661101781247 / 1237940039285380274899124224000000000000000000000000000000000000000000000000000) * u ^ 0 + (-952228037923152002182250342799909352776717451926094624004782869768943357107 / 151115727451828646838272000000000000000000000000000000000000000000000000000) * u ^ 2 + (144132019922256382185271063514828130057734964973476311770201482214329964933017 / 9671406556917033397649408000000000000000000000000000000000000000000000000000) * u ^ 4 + (-13903289460367905103902178962987686547074575754570064664608805969391431893183 / 604462909807314587353088000000000000000000000000000000000000000000000000000) * u ^ 6 + (34890287093007874147476625691198101548903469189182817288874184006934739714487 / 1208925819614629174706176000000000000000000000000000000000000000000000000000) * u ^ 8 + (-764018088019012889355321952759114783797624139381558607735009885395084077297 / 18889465931478580854784000000000000000000000000000000000000000000000000000) * u ^ 10 + (2364879162977871885261369405486939176980370071239416487076980977929866295147 / 37778931862957161709568000000000000000000000000000000000000000000000000000) * u ^ 12 + (-187669614586931301495751816605376079329564014679159906585589762838840448677 / 2361183241434822606848000000000000000000000000000000000000000000000000000) * u ^ 14 + (700541465344926849317616676882009256208519680174762209178069660284946406807 / 9444732965739290427392000000000000000000000000000000000000000000000000000) * u ^ 16 + (-2135389728171166674807761177865311553892008478837149690499493555473991727 / 36893488147419103232000000000000000000000000000000000000000000000000000) * u ^ 18 + (6644661032966649627912063302712732234424715788881993956651914934897981019 / 147573952589676412928000000000000000000000000000000000000000000000000000) * u ^ 20 + (-376712390718802943854142498656228599565909104509346128621646578601344133 / 9223372036854775808000000000000000000000000000000000000000000000000000) * u ^ 22 + (2579310278331230767466416633551503193307068966149290797120289008947259123 / 18446744073709551616000000000000000000000000000000000000000000000000000) * u ^ 24 + (-185467306881766419417909274620408187840256033757752960327412617195884773 / 288230376151711744000000000000000000000000000000000000000000000000000) * u ^ 26 + (1201234905406059927140774112681867649324652393559905553440651653915255569 / 576460752303423488000000000000000000000000000000000000000000000000000) * u ^ 28 + (-179315080358549508050404329952967348922962151760502852699722732303535191 / 36028797018963968000000000000000000000000000000000000000000000000000) * u ^ 30 + (2603487854166527347442078560375079744745046225427882458676305935727351137 / 288230376151711744000000000000000000000000000000000000000000000000000) * u ^ 32 + (-1805072207958728451580675958944381729683575384536975752156696889847901 / 140737488355328000000000000000000000000000000000000000000000000000) * u ^ 34 + (3483624814672893085436588763950024278442672758074084204173852708010273 / 225179981368524800000000000000000000000000000000000000000000000000) * u ^ 36 + (-1291274668051111628754385606339070534491568954303660555718789496555011 / 70368744177664000000000000000000000000000000000000000000000000000) * u ^ 38 + (3203448748831089059603150214684506775035250175781729106214256427573831 / 140737488355328000000000000000000000000000000000000000000000000000) * u ^ 40 + (-436670370083351341152180638509106988162137695159180613046311380701 / 17592186044416000000000000000000000000000000000000000000000000) * u ^ 42 + (3391424699360900541589543726513264716766194822696495261861899657223 / 175921860444160000000000000000000000000000000000000000000000000) * u ^ 44 + (-2567120076109329288014665850676579342439075227185612455471449726033 / 274877906944000000000000000000000000000000000000000000000000000) * u ^ 46 + (5511808209346920690653168213981134664289527714678077589704238666097 / 1099511627776000000000000000000000000000000000000000000000000000) * u ^ 48 + (-648535073397833065909015874185648537099855470100026016650037521 / 34359738368000000000000000000000000000000000000000000000000) * u ^ 50 + (56546419678064785993377246977061251060313904071788538558548736219 / 687194767360000000000000000000000000000000000000000000000000) * u ^ 52 + (-274824560526945843910916757911143446243128862953371189955130552333 / 1073741824000000000000000000000000000000000000000000000000000) * u ^ 54 + (1283594530958263073799820295009895005722547935557738983341438683519 / 2147483648000000000000000000000000000000000000000000000000000) * u ^ 56 + (-37160653807403115328025055903277042606657003528798729013247469137 / 33554432000000000000000000000000000000000000000000000000000) * u ^ 58 + (112166223519056464717433194937922688655765829393406906995274551561 / 67108864000000000000000000000000000000000000000000000000000) * u ^ 60 + (-8654220001361470638586122583655424472853128580062507381968444207 / 4194304000000000000000000000000000000000000000000000000000) * u ^ 62 + (143047342388532460703726459119507604201813976511899920059841464497 / 67108864000000000000000000000000000000000000000000000000000) * u ^ 64 + (-65843955273623825029467489063534168035422761159015272700146481 / 32768000000000000000000000000000000000000000000000000000) * u ^ 66 + (996182677767495582482631628634450453970840102106534444656626733 / 524288000000000000000000000000000000000000000000000000000) * u ^ 68 + (-53357573380754240042347440496038858014442214482698240291597547 / 32768000000000000000000000000000000000000000000000000000) * u ^ 70 + (56016796313978032930982161828088442285391192725755617208645883 / 65536000000000000000000000000000000000000000000000000000) * u ^ 72 + (9316412137954200344506175335339081625277948843858552633447 / 204800000000000000000000000000000000000000000000000000) * u ^ 74 + (2894665136297376060443164854137996520969048040411570383027 / 16384000000000000000000000000000000000000000000000000) * u ^ 76 + (-382295373000920089032796775033952339776006656429225286738889 / 128000000000000000000000000000000000000000000000000000) * u ^ 78 + (1063062220571964559213770887627515188269699744355222105514443 / 102400000000000000000000000000000000000000000000000000) * u ^ 80 + (-49705103247206990442807683371953561138039138584828164840143 / 2000000000000000000000000000000000000000000000000000) * u ^ 82 + (74467916039115993135331903734270251526859195498610754174147 / 1600000000000000000000000000000000000000000000000000) * u ^ 84 + (-35283797969975695914636752908727484539585127118472967348657 / 500000000000000000000000000000000000000000000000000) * u ^ 86 + (17483710686661180138361472641149200011136339981841474580931 / 200000000000000000000000000000000000000000000000000) * u ^ 88 + (-1341094123760016804806283266744302489385737962280351707577 / 15625000000000000000000000000000000000000000000000) * u ^ 90 + (385913642479141510903447669501990714688758904212957382793 / 6250000000000000000000000000000000000000000000000) * u ^ 92 + (-2215591794315045616419564025297068218568220828257804147 / 78125000000000000000000000000000000000000000000) * u ^ 94 + (769361097456647718794649367418147028459173456491799163 / 125000000000000000000000000000000000000000000000) * u ^ 96 := by unfold q; ring
  simp_rw [he]
  simp (disch := exact Continuous.intervalIntegrable (by fun_prop) _ _) only [intervalIntegral.integral_add, intervalIntegral.integral_const_mul, integral_pow]
  norm_num

theorem I3_exact : TMG.I3 W = (324995203720220715071316961801168757086693102879344601839327579227150864704437694040039 / 315214370070676347134213184205513525195312500000000000000000000000000000000000000000000) := by
  rw [TMG.I3_eq]
  change (∫ u, (cut q u) ^ 3) = _
  simp_rw [cut_pow q (by decide : (3 : ℕ) ≠ 0)]
  rw [integral_cut]
  exact I3_polynomial


theorem J2_polynomial : (∫ u in (-(1/2:ℝ))..(1/2), q u * P u) = (1310140525245234850225043093440538398996137211954353429914491 / 4125618814317140204336522250000000000000000000000000000000000) := by
  have he (u : ℝ) : q u * P u = (18273091407001930438289826975140433253753474278296861 / 69175290276410818560000000000000000000000000000000000) * u ^ 0 + (1994760445239146858736123643971039160153674300620493 / 2305843009213693952000000000000000000000000000000000) * u ^ 2 + (-994361296601101125736673416840682656901450972735239 / 540431955284459520000000000000000000000000000000000) * u ^ 4 + (70830110331043410274286659862048542240091736111667 / 33776997205278720000000000000000000000000000000000) * u ^ 6 + (-5192025203417751488751592008921503927185620060943 / 5629499534213120000000000000000000000000000000000) * u ^ 8 + (4877762788517035014345654703494716185788618464529 / 5629499534213120000000000000000000000000000000000) * u ^ 10 + (-6105691671802195985876716629824351617842193313363 / 2111062325329920000000000000000000000000000000000) * u ^ 12 + (236880359159134248284682627825969318597334393633 / 87960930222080000000000000000000000000000000000) * u ^ 14 + (30576815965813297172045723156167757037903572139 / 87960930222080000000000000000000000000000000000) * u ^ 16 + (-4182653711806890140526545463487686075150596533 / 43980465111040000000000000000000000000000000000) * u ^ 18 + (-944914292976560735724202431915442702747691801 / 2748779069440000000000000000000000000000000000) * u ^ 20 + (-1464107846814415429998672140808934992616011781 / 257698037760000000000000000000000000000000000) * u ^ 22 + (135389947220567021980587652132642118298121759 / 42949672960000000000000000000000000000000000) * u ^ 24 + (1480430871847992971237156458198482758923257843 / 85899345920000000000000000000000000000000000) * u ^ 26 + (-557745797518545613382575551327913723528703517 / 10737418240000000000000000000000000000000000) * u ^ 28 + (649223149787227437561443322797042893010495341 / 4026531840000000000000000000000000000000000) * u ^ 30 + (-892133789632537770519875339583887104989309263 / 2684354560000000000000000000000000000000000) * u ^ 32 + (410422240504046047962581824849290536099707339 / 1342177280000000000000000000000000000000000) * u ^ 34 + (-10908515229734535873112309116621545692090693 / 125829120000000000000000000000000000000000) * u ^ 36 + (83935103252513189364028652657407430247153 / 2621440000000000000000000000000000000000) * u ^ 38 + (-25122334315031973800582345734897712219867 / 1310720000000000000000000000000000000000) * u ^ 40 + (74194051190920469649156958886904438460237 / 3932160000000000000000000000000000000000) * u ^ 42 + (-1718168923113093517150119544086296333379 / 163840000000000000000000000000000000000) * u ^ 44 + (-4231050204322760939247700782323675757 / 4096000000000000000000000000000000000) * u ^ 46 + (16803160129657169637929725257509765571 / 4096000000000000000000000000000000000) * u ^ 48 + (-2188104741073794547099527808475169801 / 2048000000000000000000000000000000000) * u ^ 50 + (-6587467160266350729493307979711257571 / 640000000000000000000000000000000000) * u ^ 52 + (476374184923630347351154729896409743 / 10000000000000000000000000000000000) * u ^ 54 + (-580459069033076034705396871594189323 / 5000000000000000000000000000000000) * u ^ 56 + (4035783980454151264956958611162016509 / 20000000000000000000000000000000000) * u ^ 58 + (-702332629610364338916251678521838703 / 2500000000000000000000000000000000) * u ^ 60 + (92111500453464278092379648418094097 / 312500000000000000000000000000000) * u ^ 62 + (-48986399276337215138208659899117269 / 250000000000000000000000000000000) * u ^ 64 + (1496662763799272698028635666125849 / 25000000000000000000000000000000) * u ^ 66 := by unfold q P; ring
  simp_rw [he]
  simp (disch := exact Continuous.intervalIntegrable (by fun_prop) _ _) only [intervalIntegral.integral_add, intervalIntegral.integral_const_mul, integral_pow]
  norm_num

theorem J2_exact : TMG.J2 W = (1310140525245234850225043093440538398996137211954353429914491 / 4125618814317140204336522250000000000000000000000000000000000) := by
  rw [TMG.J2_eq]
  change (∫ u, ∫ w, |u - w| * (cut q u * cut q w)) = _
  rw [integral_integral_abs_cut _ q_cont]
  simp_rw [inner_q]
  exact J2_polynomial


theorem J3_polynomial : (∫ u in (-(1/2:ℝ))..(1/2), (q u)^2 * P u) = (610522233880601489305961259676821391878348141276611527877957295517187623127651198417047 / 1948802974891337130046226770329614925000000000000000000000000000000000000000000000000000) := by
  have he (u : ℝ) : (q u)^2 * P u = (2200848384378613754085231547227782874258592724457465955845095875850028320399843 / 7427640235712281649394745344000000000000000000000000000000000000000000000000000) * u ^ 0 + (655363643318812226338331239386802620916421835109044527306449615409558630617343 / 1237940039285380274899124224000000000000000000000000000000000000000000000000000) * u ^ 2 + (-90564315104956016990579274073413279601503036853314620968415844730934222341081 / 29014219670751100192948224000000000000000000000000000000000000000000000000000) * u ^ 4 + (190239125537128480946769275826615248249211901040600915086697652741410790448889 / 29014219670751100192948224000000000000000000000000000000000000000000000000000) * u ^ 6 + (-53693613856641920220929876466944773481830122338457043908058645574837721026911 / 7253554917687775048237056000000000000000000000000000000000000000000000000000) * u ^ 8 + (8113633965529963339583693856271850503782948493520404942725157434499826212363 / 1208925819614629174706176000000000000000000000000000000000000000000000000000) * u ^ 10 + (-75858430217541823083268250113100801328778018575706584422801080607488097173 / 7083549724304467820544000000000000000000000000000000000000000000000000000) * u ^ 12 + (2005254117545995280567300808717403247891922342144001502902283387822765030359 / 113336795588871485128704000000000000000000000000000000000000000000000000000) * u ^ 14 + (-314104269465535934649509174945414825002268833812191739693888139786665087859 / 18889465931478580854784000000000000000000000000000000000000000000000000000) * u ^ 16 + (84514706668092539658117477528336051845393323049408570679465812299632956319 / 9444732965739290427392000000000000000000000000000000000000000000000000000) * u ^ 18 + (-833018374741707704016747578757891755468518404076804759261597747792536487 / 147573952589676412928000000000000000000000000000000000000000000000000000) * u ^ 20 + (-34390699898356938941058117977132281464312336490214905108864268932753301 / 17708874310761169551360000000000000000000000000000000000000000000000000) * u ^ 22 + (583104969867286283049111052981396438427502784197767959640433751452094699 / 36893488147419103232000000000000000000000000000000000000000000000000000) * u ^ 24 + (25468216310219010440079242537871821886943516561543200055828590698356997 / 2213609288845146193920000000000000000000000000000000000000000000000000) * u ^ 26 + (-8975354927139119419135983091949020152356440337710130886625661923786577 / 57646075230342348800000000000000000000000000000000000000000000000000) * u ^ 28 + (987586597893772753039072893895475935048081446681941793942319230992032829 / 1729382256910270464000000000000000000000000000000000000000000000000000) * u ^ 30 + (-2448295545039907815101453247264730878571260071728749187137651770557600603 / 1729382256910270464000000000000000000000000000000000000000000000000000) * u ^ 32 + (2001940864379789185768179277522611211555247404615508353758947081177706227 / 864691128455135232000000000000000000000000000000000000000000000000000) * u ^ 34 + (-8555305934827753568189555459475873102573445115801524971710283739164401 / 3377699720527872000000000000000000000000000000000000000000000000000) * u ^ 36 + (498457701092954905623455398287139552984618124497079596292857861253531 / 225179981368524800000000000000000000000000000000000000000000000000) * u ^ 38 + (-25580840735484204764414943161485862237673335049765204913929212684197 / 11258999068426240000000000000000000000000000000000000000000000000) * u ^ 40 + (1223482987295998763495452953189869617683653070034543143975149514230081 / 422212465065984000000000000000000000000000000000000000000000000000) * u ^ 42 + (-2673497240476875415941204410223052330120767200278975024612328324623 / 1099511627776000000000000000000000000000000000000000000000000000) * u ^ 44 + (2158849502191162371380001758714466664479106075151090415665544188873 / 4398046511104000000000000000000000000000000000000000000000000000) * u ^ 46 + (1947549449063159011780813818500815430026646242053670552397780720899 / 2199023255552000000000000000000000000000000000000000000000000000) * u ^ 48 + (-1396043288419666650353987801059940647116550867734813268034368393703 / 1099511627776000000000000000000000000000000000000000000000000000) * u ^ 50 + (-3686594193446019874944400153758030062158214344366048185441554369 / 51539607552000000000000000000000000000000000000000000000000000) * u ^ 52 + (178464626717938987762371857100143240013410538439490356546961454649 / 17179869184000000000000000000000000000000000000000000000000000) * u ^ 54 + (-160140091599997925185039574650583362031333846704771601828719668321 / 4294967296000000000000000000000000000000000000000000000000000) * u ^ 56 + (176513264206109801012003719821338408847202234294021785044528194251 / 2147483648000000000000000000000000000000000000000000000000000) * u ^ 58 + (-2852612389355491692581384793491430518456205273737325076936341569 / 20132659200000000000000000000000000000000000000000000000000) * u ^ 60 + (12555915567141614050442404093660272583673484270472486610894164407 / 67108864000000000000000000000000000000000000000000000000000) * u ^ 62 + (-22436398703543867301038083565482771961657356562050001496028716769 / 134217728000000000000000000000000000000000000000000000000000) * u ^ 64 + (18083078466449632326045210196699225257049001740014586759626129331 / 201326592000000000000000000000000000000000000000000000000000) * u ^ 66 + (-16543142791192295300697086334352107260114042296492114895793687 / 524288000000000000000000000000000000000000000000000000000) * u ^ 68 + (8781095036788275734073871308970012306837505131495857205968143 / 524288000000000000000000000000000000000000000000000000000) * u ^ 70 + (-909922026323178830603328714524354647320466594147398298209719 / 78643200000000000000000000000000000000000000000000000000) * u ^ 72 + (414133110281343750656448206267009351739948811037232878173983 / 65536000000000000000000000000000000000000000000000000000) * u ^ 74 + (-43764566476539982044508112276043049901983201393113575757 / 51200000000000000000000000000000000000000000000000000) * u ^ 76 + (237393886693164093399665455660904467574696591858297123169 / 2048000000000000000000000000000000000000000000000000000) * u ^ 78 + (-7697723874418170290050266476683885674305392524890389778499 / 1024000000000000000000000000000000000000000000000000000) * u ^ 80 + (2689689617773204509388595557568236982250430006905491561427 / 102400000000000000000000000000000000000000000000000000) * u ^ 82 + (-19419321753659006979789574050721087988091502899133123323 / 320000000000000000000000000000000000000000000000000) * u ^ 84 + (870644397537577247284698098588763652793211573392645368653 / 8000000000000000000000000000000000000000000000000000) * u ^ 86 + (-314878726452472099794721076832035590146160868563876042569 / 2000000000000000000000000000000000000000000000000000) * u ^ 88 + (185983540712275400921206359844147393819543547197567649259 / 1000000000000000000000000000000000000000000000000000) * u ^ 90 + (-2724582234970915547717819369438487344907162073321806277 / 15625000000000000000000000000000000000000000000000) * u ^ 92 + (749863667676137080345953729078530973771811894179540903 / 6250000000000000000000000000000000000000000000000) * u ^ 94 + (-65950090210861285383236212816712608886520747250193967 / 1250000000000000000000000000000000000000000000000) * u ^ 96 + (1371410155894202707298840227126821797609934860056683 / 125000000000000000000000000000000000000000000000) * u ^ 98 := by unfold q P; ring
  simp_rw [he]
  simp (disch := exact Continuous.intervalIntegrable (by fun_prop) _ _) only [intervalIntegral.integral_add, intervalIntegral.integral_const_mul, integral_pow]
  norm_num

theorem J3_exact : TMG.J3 W = (610522233880601489305961259676821391878348141276611527877957295517187623127651198417047 / 1948802974891337130046226770329614925000000000000000000000000000000000000000000000000000) := by
  rw [TMG.J3_eq]
  change (∫ u, ∫ w, |u - w| * ((cut q u) ^ 2 * cut q w)) = _
  simp_rw [cut_pow q (by decide : (2 : ℕ) ≠ 0)]
  rw [integral_integral_abs_cut _ q_cont]
  simp_rw [inner_q]
  exact J3_polynomial


theorem C2_exact : TMG.C2 W 1 = (12452606124331935739771760532976017448309674458647038137221 / 9376406396175318646219368750000000000000000000000000000000) := by unfold TMG.C2; rw [I2_exact,J2_exact]; norm_num

theorem C3_exact : TMG.C3 W 1 = (715676403424950496284189484154289566223867065490630825402683499463785677467869243449254201 / 363126954321419151898613588204751581025000000000000000000000000000000000000000000000000000) := by unfold TMG.C3; rw [I3_exact,J3_exact]; norm_num

end
end DevineDegree32

end Src_BeiYiFrozenOctic

/-
Retained-pair method, original proofs, and source for adapted sections by Michael Devine.
Base third-moment framework and quartic specialization by Kristian Muri Knausgård.
Alpöge and Furman cubic certificate, Josu San Martin shift, and rStation paper 155 packet method.
Apache-2.0 §4(b) changes by 贝奕 (Bei Yi), 2026-11-23 UTC+08:00.
Bind the frozen octic window to the retained pair argument.
SPDX-License-Identifier: Apache-2.0
-/
section Src_Devine_ConditionalShiftedCubicSpacing
/-
Copyright (c) 2026 Michael Devine.
Released under the Apache 2.0 license.
SPDX-License-Identifier: Apache-2.0
-/




/-! Scalar spacing checks and exact octic coefficients.
The full zeta-zero argument and the exact Fourier certificate are in T041-0074. -/
namespace Devine32Retained

def cubic (t x : ℝ) : ℝ := x * (x - t)^2

/-- A repeated diagonal retains its off-diagonal variance. Apply this pointwise
to the spectral measure of a row with mean c. The linear term averages to zero. -/
theorem tangent_retains_variance {x t c : ℝ} (hx : 0 ≤ x) :
    cubic t c + ((c-t)*(3*c-t))*(x-c) + 2*(c-t)*(x-c)^2 ≤ cubic t x := by
  unfold cubic
  nlinarith [mul_nonneg hx (sq_nonneg (x-c))]

def exceptional (x : ℝ) : Prop :=
  (5247238848358489/5000000000000000 < x ∧ x < 23/20) ∨ (9868029242552487/5000000000000000 < x ∧ x < 5247238848358489/2500000000000000) ∨ 11/4 < x

theorem gaps_not_all_exceptional {x y : ℝ} (hz : x + y ≤ (59044015980121 / 19531250000000))
    (hx : exceptional x) (hy : exceptional y) : ¬ exceptional (x + y) := by
  rcases hx with ⟨h1,h2⟩ | ⟨h1,h2⟩ | h1 <;>
    rcases hy with ⟨k1,k2⟩ | ⟨k1,k2⟩ | k1 <;>
    rintro (⟨j1,j2⟩ | ⟨j1,j2⟩ | j1) <;> linarith

def eta : ℚ := 308508742413987 / 12500000000000000


/-! The coefficient vector represents (1+z)^n times the signed Taylor
polynomial at (lo+hi*z)/(1+z), with the required floor and the uniform
error already subtracted. Endpoint z=infinity uses the leading coefficient. -/
namespace FourierCertificate

def piApprox : ℚ := 314159265358979323846 / 100000000000000000000

def moment (k : ℕ) : ℚ := (120442038807691126445521663 / 107374182400000000000000000) / ((k : ℚ) + 1) + (-21880815954788081037201 / 52428800000000000000000) / ((k : ℚ) + 3) + (245568575373413537892311 / 2684354560000000000000000) / ((k : ℚ) + 5) + (-26442595365396232982421 / 3355443200000000000000000) / ((k : ℚ) + 7) + (4163967043535719776213 / 1073741824000000000000000) / ((k : ℚ) + 9) + (-4070655085035826724723 / 1677721600000000000000000) / ((k : ℚ) + 11) + (4529476148191948428657 / 13421772800000000000000000) / ((k : ℚ) + 13) + (1621744705501989813 / 26843545600000000000000) / ((k : ℚ) + 15) + (-4930650918923353299 / 2147483648000000000000000) / ((k : ℚ) + 17) + (65875087890281439 / 33554432000000000000000) / ((k : ℚ) + 19) + (-2068703240142357819 / 536870912000000000000000) / ((k : ℚ) + 21) + (-735791782466109447 / 671088640000000000000000) / ((k : ℚ) + 23) + (1950841680607749501 / 1073741824000000000000000) / ((k : ℚ) + 25) + (-1900049869174041963 / 1677721600000000000000000) / ((k : ℚ) + 27) + (1805282199044482851 / 2684354560000000000000000) / ((k : ℚ) + 29) + (-879592825388656841 / 3355443200000000000000000) / ((k : ℚ) + 31) + (916312070471295267 / 21474836480000000000000000) / ((k : ℚ) + 33)

def coeff (k : ℕ) : ℚ :=
  if k % 2 = 0 then
    (-1 : ℚ) ^ (k / 2) * piApprox ^ k * moment k / (k.factorial : ℚ)
  else 0

def linearMul (lo hi : ℚ) (xs : List ℚ) : List ℚ :=
  List.zipWith (· + ·) (xs.map (lo * ·) ++ [0]) (0 :: xs.map (hi * ·))

def coefficients (n : ℕ) (lo hi sign : ℚ) : List ℚ :=
  let cutoff := eta + hi/100000000000000000000 + (piApprox*hi)^(n+2) / ((n+2).factorial : ℚ)
  let a := fun k => sign * coeff k - (if k = 0 then cutoff else 0)
  let start : List ℚ × List ℚ := ([a n], [1])
  let (xs, _) := (List.range n).reverse.foldl (fun state k =>
    let base := linearMul 1 1 state.2
    (List.zipWith (fun x y => x + a k * y) (linearMul lo hi state.1) base, base)) start
  xs

def positive (n : ℕ) (lo hi sign : ℚ) : Bool :=
  (coefficients n lo hi sign).all (fun c => decide (0 < c))

theorem first_coefficients : positive 28 0 (5247238848358489/5000000000000000) 1 = true := by decide +kernel
theorem second_coefficients : positive 38 (23/20) (9868029242552487/5000000000000000) (-1) = true := by decide +kernel
theorem third_coefficients : positive 44 (5247238848358489/2500000000000000) (11/4) 1 = true := by decide +kernel

end FourierCertificate

end Devine32Retained
end Src_Devine_ConditionalShiftedCubicSpacing
section Src_Devine_ConditionalShiftedCubicIntervals
/-
Copyright (c) 2026 Michael Devine.
Released under the Apache 2.0 license.
SPDX-License-Identifier: Apache-2.0
-/





open scoped BigOperators
namespace Devine32Retained.FourierCertificate

def heval (u v : ℝ) : List ℚ → ℝ
  | [] => 0
  | a::as => (a:ℝ)*u^as.length + v*heval u v as

private theorem map_eval (u v : ℝ) (k : ℚ) (xs : List ℚ) :
    heval u v (xs.map (k * ·)) = (k:ℝ)*heval u v xs := by
  induction xs with
  | nil => simp [heval]
  | cons a xs ih => simp [heval, ih]; ring

private theorem pad_eval (u v : ℝ) (xs : List ℚ) :
    heval u v (xs ++ [0]) = u * heval u v xs := by
  induction xs with
  | nil => simp [heval]
  | cons a xs ih => simp [heval, ih, pow_succ]; ring

private theorem zip_eval (u v : ℝ) (k : ℚ) (xs ys : List ℚ)
    (h : xs.length = ys.length) :
    heval u v (List.zipWith (fun a b => a+k*b) xs ys) =
    heval u v xs + (k:ℝ)*heval u v ys := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp_all [heval]
  | cons a xs ih =>
    cases ys with
    | nil => simp at h
    | cons b ys =>
      have h' : xs.length = ys.length := by simpa using h
      simp [heval, ih ys h', h']; ring

private theorem linear_len (l h : ℚ) (xs : List ℚ) :
    (linearMul l h xs).length = xs.length + 1 := by simp [linearMul]

private theorem linear_eval (u v : ℝ) (l h : ℚ) (xs : List ℚ) :
    heval u v (linearMul l h xs) = ((l:ℝ)*u+(h:ℝ)*v)*heval u v xs := by
  have eqn := zip_eval u v 1 ((xs.map (l * ·)) ++ [0]) (0 :: xs.map (h * ·)) (by simp)
  simp only [one_mul, Rat.cast_one] at eqn
  unfold linearMul
  rw [eqn, pad_eval, map_eval]
  simp [heval, map_eval]; ring

private theorem eval_nonneg (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (xs : List ℚ) (hp : ∀ x ∈ xs, 0 ≤ x) : 0 ≤ heval u v xs := by
  induction xs with
  | nil => simp [heval]
  | cons x xs ih =>
    have hx : (0:ℝ) ≤ x := by exact_mod_cast hp x (by simp)
    exact add_nonneg (mul_nonneg hx (pow_nonneg hu _))
      (mul_nonneg hv (ih fun y hy => hp y (by simp [hy])))


private def advance (l h : ℚ) (a : ℕ → ℚ) (state : List ℚ × List ℚ) (k : ℕ) :=
  let base := linearMul 1 1 state.2
  (List.zipWith (fun x y => x + a k * y) (linearMul l h state.1) base, base)

private theorem fold_eval (u v : ℝ) (uv : u+v=1) (l h : ℚ) (a : ℕ → ℚ)
    (ks : List ℕ) (state : List ℚ × List ℚ)
    (hlen : state.1.length = state.2.length) (hbase : heval u v state.2 = 1) :
    heval u v (ks.foldl (advance l h a) state).1 =
      ks.foldl (fun val k => ((l:ℝ)*u+(h:ℝ)*v)*val + (a k:ℝ)) (heval u v state.1) := by
  induction ks generalizing state with
  | nil => rfl
  | cons k ks ih =>
    have h1 : heval u v (linearMul 1 1 state.2) = 1 := by
      simp [linear_eval, hbase, uv]
    have hlen' : (linearMul l h state.1).length = (linearMul 1 1 state.2).length := by
      simp [linear_len, hlen]
    have h2 : (advance l h a state k).1.length = (advance l h a state k).2.length := by
      simp [advance, hlen']
    simp only [List.foldl_cons]
    rw [ih _ h2 h1]
    congr 1
    simp [advance, zip_eval _ _ _ _ _ hlen', linear_eval, hbase, uv]

private theorem horner_sum (x : ℝ) (a : ℕ → ℚ) (n : ℕ) (y : ℝ) :
    (List.range n).reverse.foldl (fun val k => x*val+(a k:ℝ)) y =
      x^n*y + ∑ k ∈ Finset.range n, x^k*(a k:ℝ) := by
  induction n generalizing y with
  | zero => simp
  | succ n ih =>
    simp [List.range_succ, ih, Finset.sum_range_succ, pow_succ]
    ring

def taylorValue (n : ℕ) (x : ℝ) := ∑ k ∈ Finset.range (n+1), x^k*(coeff k:ℝ)
def errorBound (n : ℕ) (hi : ℚ) := hi/100000000000000000000 + (piApprox*hi)^(n+2) / ((n+2).factorial : ℚ)

theorem checked_interval {n : ℕ} {l h sign : ℚ} (ok : positive n l h sign = true)
    {x : ℝ} (lh : l < h) (xl : (l:ℝ) ≤ x) (xh : x ≤ (h:ℝ)) :
    (eta:ℝ) + (errorBound n h:ℝ) ≤ (sign:ℝ) * taylorValue n x := by
  let u := ((h:ℝ)-x)/((h:ℝ)-l)
  let v := (x-(l:ℝ))/((h:ℝ)-l)
  have den : (0:ℝ) < (h:ℝ)-l := sub_pos.mpr (by exact_mod_cast lh)
  have hu : 0 ≤ u := div_nonneg (sub_nonneg.mpr xh) den.le
  have hv : 0 ≤ v := div_nonneg (sub_nonneg.mpr xl) den.le
  have uv : u+v=1 := by dsimp [u,v]; field_simp; ring
  have loc : (l:ℝ)*u+(h:ℝ)*v=x := by dsimp [u,v]; field_simp; ring
  let cut : ℚ := eta + h/100000000000000000000 + (piApprox*h)^(n+2) / ((n+2).factorial : ℚ)
  let a := fun k => sign*coeff k - (if k=0 then cut else 0)
  let arr := coefficients n l h sign
  have nonneg : 0 ≤ heval u v arr := eval_nonneg _ _ hu hv _ (by
    intro y hy
    exact le_of_lt (of_decide_eq_true (List.all_eq_true.mp ok y hy)))
  have ev := fold_eval u v uv l h a (List.range n).reverse ([a n],[1]) rfl (by simp [heval])
  change heval u v arr = _ at ev
  rw [ev, loc] at nonneg
  simp only [heval, List.length_nil, pow_zero, mul_one, mul_zero, add_zero] at nonneg
  rw [horner_sum] at nonneg
  have combined : 0 ≤ ∑ k ∈ Finset.range (n+1), x^k*(a k:ℝ) := by
    rw [Finset.sum_range_succ]; linarith
  simp only [a, Rat.cast_sub, Rat.cast_mul, apply_ite (fun q : ℚ => (q:ℝ)),
    Rat.cast_zero, mul_sub, Finset.sum_sub_distrib, mul_ite, mul_zero] at combined
  simp only [Finset.sum_ite_eq', Finset.mem_range, Nat.zero_lt_succ, if_true,
    pow_zero, one_mul] at combined
  dsimp [taylorValue]
  rw [Finset.mul_sum]
  simp only [mul_left_comm (sign:ℝ)]
  simpa [cut, errorBound, add_assoc] using (sub_nonneg.mp combined)

theorem first_interval {x : ℝ} (hx : 0 ≤ x) (hu : x ≤ 5247238848358489/5000000000000000) :
    (eta:ℝ) + errorBound 28 (5247238848358489/5000000000000000) ≤ taylorValue 28 x := by
  simpa using checked_interval first_coefficients (x := x) (by norm_num) (by simpa using hx) (by simpa using hu)

theorem second_interval {x : ℝ} (hl : 23/20 ≤ x) (hu : x ≤ 9868029242552487/5000000000000000) :
    (eta:ℝ) + errorBound 38 (9868029242552487/5000000000000000) ≤ -taylorValue 38 x := by
  simpa using checked_interval second_coefficients (x := x) (by norm_num) (by simpa using hl) (by simpa using hu)

theorem third_interval {x : ℝ} (hl : 5247238848358489/2500000000000000 ≤ x) (hu : x ≤ 11/4) :
    (eta:ℝ) + errorBound 44 (11/4) ≤ taylorValue 44 x := by
  simpa using checked_interval third_coefficients (x := x) (by norm_num) (by simpa using hl) (by simpa using hu)

/-- Convert the analytic remainder on each of the three intervals into
the pair overlap needed in the finite Gram inequality. -/
theorem triple_overlap (F : ℝ → ℝ)
    (h₁ : ∀ x : ℝ, 0 ≤ x → x ≤ 5247238848358489/5000000000000000 →
      |F x - taylorValue 28 x| ≤ errorBound 28 (5247238848358489/5000000000000000))
    (h₂ : ∀ x : ℝ, 23/20 ≤ x → x ≤ 9868029242552487/5000000000000000 →
      |F x - taylorValue 38 x| ≤ errorBound 38 (9868029242552487/5000000000000000))
    (h₃ : ∀ x : ℝ, 5247238848358489/2500000000000000 ≤ x → x ≤ 11/4 →
      |F x - taylorValue 44 x| ≤ errorBound 44 (11/4))
    {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : x+y ≤ (59044015980121 / 19531250000000)) :
    (eta:ℝ) ≤ |F x| ∨ (eta:ℝ) ≤ |F y| ∨ (eta:ℝ) ≤ |F (x+y)| := by
  have bad (s : ℝ) (hs : 0 ≤ s) (h : |F s| < (eta:ℝ)) : exceptional s := by
    have low := (abs_lt.mp h).1
    have high := (abs_lt.mp h).2
    by_cases h0 : s ≤ 5247238848358489/5000000000000000
    · have ⟨hl,_⟩ := abs_le.mp (h₁ s hs h0)
      linarith [first_interval hs h0]
    by_cases h1 : s < 23/20
    · exact Or.inl ⟨lt_of_not_ge h0,h1⟩
    by_cases h2 : s ≤ 9868029242552487/5000000000000000
    · have ⟨_,hu⟩ := abs_le.mp (h₂ s (le_of_not_gt h1) h2)
      linarith [second_interval (le_of_not_gt h1) h2]
    by_cases h3 : s < 5247238848358489/2500000000000000
    · exact Or.inr (Or.inl ⟨lt_of_not_ge h2,h3⟩)
    by_cases h4 : s ≤ 11/4
    · have ⟨hl,_⟩ := abs_le.mp (h₃ s (le_of_not_gt h3) h4)
      linarith [third_interval (le_of_not_gt h3) h4]
    exact Or.inr (Or.inr (lt_of_not_ge h4))
  by_contra! h
  exact gaps_not_all_exceptional hz (bad x hx h.1) (bad y hy h.2.1)
    (bad (x+y) (add_nonneg hx hy) h.2.2)

end Devine32Retained.FourierCertificate
end Src_Devine_ConditionalShiftedCubicIntervals
section Src_Devine_ConditionalShiftedCubicFourier







/-! Remainder bounds for the octic-window Fourier certificate of T041-0074. -/

noncomputable section
open Set
namespace Devine32Retained.FourierCertificate

def cosCoeff (k : ℕ) : ℝ :=
  if k % 2 = 0 then (-1 : ℝ)^(k/2) / k.factorial else 0

def cosPoly (n : ℕ) (y : ℝ) := ∑ k ∈ Finset.range (n+1), y^k * cosCoeff k

private theorem cos_coeff_deriv (k : ℕ) :
    iteratedDeriv k Real.cos 0 / k.factorial = cosCoeff k := by
  by_cases even : k % 2 = 0
  · rw [cosCoeff, if_pos even]
    conv_lhs => arg 1; rw [show k = 2*(k/2) by omega, Real.iteratedDeriv_even_cos]
    simp
  · rw [cosCoeff, if_neg even]
    conv_lhs => arg 1; rw [show k = 2*(k/2)+1 by omega, Real.iteratedDeriv_odd_cos]
    simp

theorem cosPoly_remainder (n : ℕ) (hn : n % 2 = 0) (y : ℝ) :
    |Real.cos y - cosPoly n y| ≤ |y|^(n+2) / (n+2).factorial := by
  by_cases hy : 0 = y
  · subst y
    have h0 : cosPoly n 0 = 1 := by
      unfold cosPoly
      rw [Finset.sum_eq_single 0]
      · norm_num [cosCoeff]
      · intro k _ hk; simp [zero_pow hk]
      · simp
    simp [h0]
  have hp : taylorWithinEval Real.cos (n+1) (uIcc 0 y) 0 y = cosPoly n y := by
    rw [taylor_within_apply]
    simp only [sub_zero, smul_eq_mul]
    have term (k : ℕ) :
        ((k.factorial : ℝ)⁻¹ * y^k) * iteratedDerivWithin k Real.cos (uIcc 0 y) 0 =
          y^k * cosCoeff k := by
      rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_uIcc hy)
        Real.contDiff_cos.contDiffAt left_mem_uIcc, ← cos_coeff_deriv]
      ring
    simp_rw [term]
    rw [Finset.sum_range_succ, cosPoly]
    simp [cosCoeff, show (n+1)%2 ≠ 0 by omega]
  obtain ⟨z, _, hz⟩ := taylor_mean_remainder_lagrange_iteratedDeriv
    (n := n+1) hy Real.contDiff_cos.contDiffOn
  rw [hp, sub_zero] at hz
  rw [hz, abs_div, abs_mul, abs_pow, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) (n+2).factorial)]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  simpa using (mul_le_mul_of_nonneg_right (Real.abs_iteratedDeriv_cos_le_one (n+2) z)
    (pow_nonneg (abs_nonneg y) (n+2)))

theorem pointwise_fourier_remainder (n : ℕ) (hn : n % 2 = 0)
    {s h u : ℝ} (hs : 0 ≤ s) (sh : s ≤ h) (hu : |u| ≤ 1/2) :
    |Real.cos (2*Real.pi*s*u) - cosPoly n (2*(piApprox:ℝ)*s*u)| ≤
      h/100000000000000000000 + ((piApprox:ℝ)*h)^(n+2)/(n+2).factorial := by
  have hp : (0:ℝ) ≤ piApprox := by norm_num [piApprox]
  have delta : |Real.pi - (piApprox:ℝ)| ≤ 1/100000000000000000000 := by
    rw [abs_le]; norm_num [piApprox]; constructor <;> linarith [Real.pi_gt_d20, Real.pi_lt_d20]
  have hs' : |s| = s := abs_of_nonneg hs
  have hu' : |2*u| ≤ 1 := by rw [abs_mul]; norm_num; linarith
  have arg (a : ℝ) : |2*a*s*u| ≤ |a| *h := by
    rw [show 2*a*s*u = (a*s)*(2*u) by ring, abs_mul, abs_mul, hs']
    calc
      _ ≤ (|a| *s)*1 := mul_le_mul_of_nonneg_left hu' (mul_nonneg (abs_nonneg _) hs)
      _ ≤ _ := by simpa using mul_le_mul_of_nonneg_left sh (abs_nonneg a)
  have d := (Real.abs_cos_sub_cos_le (2*Real.pi*s*u) (2*(piApprox:ℝ)*s*u)).trans
    (c := 1/100000000000000000000*h) (by
      rw [show 2*Real.pi*s*u - 2*(piApprox:ℝ)*s*u = 2*(Real.pi-(piApprox:ℝ))*s*u by ring]
      exact (arg _).trans (mul_le_mul_of_nonneg_right delta (hs.trans sh)))
  have a := arg (piApprox:ℝ)
  rw [abs_of_nonneg hp] at a
  refine (abs_sub_le _ (Real.cos (2*(piApprox:ℝ)*s*u)) _).trans ?_
  exact add_le_add (by linarith only [d]) ((cosPoly_remainder n hn _).trans
    (div_le_div_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg _) a _) (Nat.cast_nonneg _)))

def weight (u : ℝ) := DevineDegree32.q u

theorem weight_continuous : Continuous weight := DevineDegree32.q_cont

private theorem scaled_even_moment (k : ℕ) (hk : k%2=0) :
    (∫ u in (-(1/2:ℝ))..(1/2), (2*u)^k) = 1/(k+1:ℝ) := by
  have h := intervalIntegral.mul_integral_comp_mul_left (a := -(1/2:ℝ)) (b := 1/2)
    (f := fun v => v^k) 2
  norm_num only [show (2:ℝ)* -(1/2) = -1 by norm_num, show (2:ℝ)*(1/2)=1 by norm_num,
    integral_pow, one_pow] at h
  have powneg : (-1:ℝ)^(k+1) = -1 := by
    rw [pow_succ, show k=2*(k/2) by omega, pow_mul]; norm_num
  rw [powneg] at h
  simp only [div_eq_mul_inv] at h ⊢
  linarith

private theorem weight_moment (k : ℕ) (hk : k % 2 = 0) :
    (∫ u in (-(1/2:ℝ))..(1/2), weight u * (2*u)^k) = (moment k : ℝ) := by
  have he (u : ℝ) : weight u * (2*u)^k = (120442038807691126445521663 / 107374182400000000000000000) * (2*u)^(k+0) + (-21880815954788081037201 / 52428800000000000000000) * (2*u)^(k+2) + (245568575373413537892311 / 2684354560000000000000000) * (2*u)^(k+4) + (-26442595365396232982421 / 3355443200000000000000000) * (2*u)^(k+6) + (4163967043535719776213 / 1073741824000000000000000) * (2*u)^(k+8) + (-4070655085035826724723 / 1677721600000000000000000) * (2*u)^(k+10) + (4529476148191948428657 / 13421772800000000000000000) * (2*u)^(k+12) + (1621744705501989813 / 26843545600000000000000) * (2*u)^(k+14) + (-4930650918923353299 / 2147483648000000000000000) * (2*u)^(k+16) + (65875087890281439 / 33554432000000000000000) * (2*u)^(k+18) + (-2068703240142357819 / 536870912000000000000000) * (2*u)^(k+20) + (-735791782466109447 / 671088640000000000000000) * (2*u)^(k+22) + (1950841680607749501 / 1073741824000000000000000) * (2*u)^(k+24) + (-1900049869174041963 / 1677721600000000000000000) * (2*u)^(k+26) + (1805282199044482851 / 2684354560000000000000000) * (2*u)^(k+28) + (-879592825388656841 / 3355443200000000000000000) * (2*u)^(k+30) + (916312070471295267 / 21474836480000000000000000) * (2*u)^(k+32) := by
    unfold weight DevineDegree32.q
    simp only [pow_add]
    ring
  simp_rw [he]
  simp (disch := exact Continuous.intervalIntegrable (by fun_prop) _ _) only [intervalIntegral.integral_add, intervalIntegral.integral_const_mul]
  simp only [scaled_even_moment (k+0) (by omega), scaled_even_moment (k+2) (by omega), scaled_even_moment (k+4) (by omega), scaled_even_moment (k+6) (by omega), scaled_even_moment (k+8) (by omega), scaled_even_moment (k+10) (by omega), scaled_even_moment (k+12) (by omega), scaled_even_moment (k+14) (by omega), scaled_even_moment (k+16) (by omega), scaled_even_moment (k+18) (by omega), scaled_even_moment (k+20) (by omega), scaled_even_moment (k+22) (by omega), scaled_even_moment (k+24) (by omega), scaled_even_moment (k+26) (by omega), scaled_even_moment (k+28) (by omega), scaled_even_moment (k+30) (by omega), scaled_even_moment (k+32) (by omega)]
  unfold moment
  push_cast
  ring

theorem integrated_cosPoly (n : ℕ) (s : ℝ) :
    (∫ u in (-(1/2:ℝ))..(1/2), weight u * cosPoly n (2*(piApprox:ℝ)*s*u)) = taylorValue n s := by
  let a (k : ℕ) := ((piApprox:ℝ)*s)^k*cosCoeff k
  have expand (u : ℝ) : weight u * cosPoly n (2*(piApprox:ℝ)*s*u) =
      ∑ k ∈ Finset.range (n+1), a k * (weight u * (2*u)^k) := by
    unfold cosPoly
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    dsimp [a]
    rw [show 2*(piApprox:ℝ)*s*u = ((piApprox:ℝ)*s)*(2*u) by ring, mul_pow]
    ring
  simp_rw [expand]
  have ht (k : ℕ) : Continuous (fun u : ℝ => a k * (weight u * (2*u)^k)) :=
    continuous_const.mul (weight_continuous.mul (by fun_prop))
  rw [intervalIntegral.integral_finsetSum (fun k _ => (ht k).intervalIntegrable _ _)]
  apply Finset.sum_congr rfl
  intro k _
  rw [intervalIntegral.integral_const_mul]
  by_cases hk : k%2=0
  · rw [weight_moment k hk]
    simp [a, cosCoeff, coeff, hk, mul_pow, div_eq_mul_inv, mul_inv_rev]
    ring
  · simp [a, cosCoeff, coeff, hk]

theorem weight_nonneg {u : ℝ} (hu : |u| ≤ 1/2) : 0 ≤ weight u :=
  le_trans (by norm_num) (DevineDegree32.q_positive_lower u hu)

theorem weight_mass : (∫ u in (-(1/2:ℝ))..(1/2), weight u) = 1 :=
  DevineDegree32.normalization

def fourierReal (s : ℝ) := ∫ u in (-(1/2:ℝ))..(1/2), weight u * Real.cos (2*Real.pi*s*u)

theorem fourier_error (n : ℕ) (hn : n%2=0) {s : ℝ} {hi : ℚ}
    (hs : 0 ≤ s) (sh : s ≤ (hi:ℝ)) :
    |fourierReal s - taylorValue n s| ≤ (errorBound n hi:ℝ) := by
  let C : ℝ := (hi:ℝ)/100000000000000000000 + ((piApprox:ℝ)*hi)^(n+2)/(n+2).factorial
  let f (u : ℝ) := weight u * Real.cos (2*Real.pi*s*u)
  let g (u : ℝ) := weight u * cosPoly n (2*(piApprox:ℝ)*s*u)
  have cf : Continuous f := by
    dsimp [f]
    exact weight_continuous.mul (by fun_prop)
  have cg : Continuous g := by
    dsimp [g]
    exact weight_continuous.mul (by unfold cosPoly; fun_prop)
  have hab : -(1/2:ℝ) ≤ 1/2 := by norm_num
  have mono : (∫ u in (-(1/2:ℝ))..(1/2), |f u-g u|) ≤
      ∫ u in (-(1/2:ℝ))..(1/2), weight u*C := by
    apply intervalIntegral.integral_mono_on hab ((cf.sub cg).abs.intervalIntegrable _ _)
      ((weight_continuous.mul continuous_const).intervalIntegrable _ _)
    intro u hu
    have hu' := abs_le.mpr hu
    change |weight u * _ - weight u * _| ≤ _
    rw [← mul_sub, abs_mul, abs_of_nonneg (weight_nonneg hu')]
    exact mul_le_mul_of_nonneg_left (pointwise_fourier_remainder n hn hs sh hu') (weight_nonneg hu')
  change |(∫ u in (-(1/2:ℝ))..(1/2), f u) - taylorValue n s| ≤ _
  rw [← integrated_cosPoly]
  change |(∫ u in (-(1/2:ℝ))..(1/2), f u) - (∫ u in (-(1/2:ℝ))..(1/2), g u)| ≤ _
  rw [← intervalIntegral.integral_sub (cf.intervalIntegrable _ _) (cg.intervalIntegrable _ _)]
  refine (intervalIntegral.abs_integral_le_integral_abs hab).trans (mono.trans_eq ?_)
  rw [intervalIntegral.integral_mul_const, weight_mass, one_mul]
  simp [C, errorBound]

/-- The real part of the normalized octic transform has a large absolute
value on at least one of the three pair separations. -/
theorem fourier_triple {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : x+y ≤ (59044015980121 / 19531250000000)) :
    (eta:ℝ) ≤ |fourierReal x| ∨ (eta:ℝ) ≤ |fourierReal y| ∨ (eta:ℝ) ≤ |fourierReal (x+y)| := by
  apply triple_overlap _ _ _ _ hx hy hz
  · intro s hs hu; exact fourier_error 28 (by decide) hs (by simpa using hu)
  · intro s hs hu; exact fourier_error 38 (by decide) (by linarith) (by simpa using hu)
  · intro s hs hu; exact fourier_error 44 (by decide) (by linarith) (by simpa using hu)

open MeasureTheory

/-- Same sign and angular-frequency convention as Knausgaard's `TMG.ghat`. -/
def octicTransform (a : ℝ) : ℂ :=
  ∫ u : ℝ, ((if |u| ≤ 1/2 then weight u else 0 : ℝ) : ℂ) *
    Complex.exp (Complex.I * (a:ℂ) * (u:ℂ))

theorem octicTransform_re (s : ℝ) : (octicTransform (2*Real.pi*s)).re = fourierReal s := by
  let S := Icc (-(1/2:ℝ)) (1/2)
  let f (u : ℝ) : ℂ := (weight u:ℂ) * Complex.exp (Complex.I * ((2*Real.pi*s:ℝ):ℂ) * (u:ℂ))
  have cf : Continuous f := by
    dsimp [f]
    exact (Complex.continuous_ofReal.comp weight_continuous).mul (by fun_prop)
  have cut (u : ℝ) : ((if |u| ≤ 1/2 then weight u else 0 : ℝ) : ℂ) *
      Complex.exp (Complex.I * ((2*Real.pi*s:ℝ):ℂ) * (u:ℂ)) = S.indicator f u := by
    by_cases h : |u| ≤ 1/2
    · rw [if_pos h, indicator_of_mem (show u ∈ S from abs_le.mp h)]
    · rw [if_neg h, indicator_of_notMem (show u ∉ S from fun hm => h (abs_le.mpr hm))]; simp
  unfold octicTransform
  simp_rw [cut]
  rw [integral_indicator (show MeasurableSet S from measurableSet_Icc)]
  change RCLike.re (∫ u in S, f u) = _
  rw [← integral_re (cf.continuousOn.integrableOn_compact isCompact_Icc)]
  have hre (u : ℝ) : RCLike.re (f u) = weight u * Real.cos (2*Real.pi*s*u) := by
    change ((weight u:ℂ) * Complex.exp _).re = _
    rw [show Complex.I * ((2*Real.pi*s:ℝ):ℂ) * (u:ℂ) = ((2*Real.pi*s*u:ℝ):ℂ)*Complex.I by push_cast; ring]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, Complex.exp_ofReal_mul_I_re]
  simp_rw [hre]
  exact (integral_Icc_eq_integral_Ioc.trans (intervalIntegral.integral_of_le (by norm_num)).symm)

theorem complex_triple {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : x+y ≤ (59044015980121 / 19531250000000)) :
    (eta:ℝ) ≤ ‖octicTransform (2*Real.pi*x)‖ ∨
    (eta:ℝ) ≤ ‖octicTransform (2*Real.pi*y)‖ ∨
    (eta:ℝ) ≤ ‖octicTransform (2*Real.pi*(x+y))‖ := by
  have h (s : ℝ) : |fourierReal s| ≤ ‖octicTransform (2*Real.pi*s)‖ := by
    rw [← octicTransform_re]; exact Complex.abs_re_le_norm _
  rcases fourier_triple hx hy hz with a | a | a
  · exact Or.inl (a.trans (h x))
  · exact Or.inr (Or.inl (a.trans (h y)))
  · exact Or.inr (Or.inr (a.trans (h (x+y))))

end Devine32Retained.FourierCertificate
end
end Src_Devine_ConditionalShiftedCubicFourier
section Src_Devine32Link



open Devine32Retained.FourierCertificate

noncomputable section
namespace Devine32Link

theorem kernel_eq (a : ℝ) : TMG.ghat DevineDegree32.W a = octicTransform a := by
  rfl

theorem kernel_re (s : ℝ) : (TMG.ghat DevineDegree32.W (2*Real.pi*s)).re = fourierReal s := by
  rw [kernel_eq, octicTransform_re]

theorem triple_actual {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hxy : x+y ≤ (59044015980121 / 19531250000000)) :
    (Devine32Retained.eta : ℝ) ≤ |(TMG.ghat DevineDegree32.W (2*Real.pi*x)).re| ∨
    (Devine32Retained.eta : ℝ) ≤ |(TMG.ghat DevineDegree32.W (2*Real.pi*y)).re| ∨
    (Devine32Retained.eta : ℝ) ≤ |(TMG.ghat DevineDegree32.W (2*Real.pi*(x+y))).re| := by
  simpa only [kernel_re] using fourier_triple hx hy hxy

end Devine32Link
end
end Src_Devine32Link

/-
Retained-pair method, original proofs, and source for adapted sections by Michael Devine.
Base third-moment framework and quartic specialization by Kristian Muri Knausgård.
Alpöge and Furman cubic certificate, Josu San Martin shift, and rStation paper 155 packet method.
Apache-2.0 §4(b) changes by 贝奕 (Bei Yi), 2026-11-23 UTC+08:00.
Bind the frozen octic window to the retained pair argument.
SPDX-License-Identifier: Apache-2.0
-/
section Src_Devine_ConditionalShiftedCubicPacking




/-! Selecting disjoint pairs from an ordered list of distinct ordinates. -/
noncomputable section
namespace Devine32Retained
open FourierCertificate

private theorem sum_spans (v : ℕ → ℝ) (m : ℕ) :
    ∑ i ∈ Finset.range m, (v (i+2) - v i) = v m + v (m+1) - v 0 - v 1 := by
  induction m with
  | zero => simp
  | succ m ih => rw [Finset.sum_range_succ, ih]; ring

/-- There are `m+2` ordinates, numbered `0,...,m+1`, in an interval of
length `L`. One residue class of short triples already gives the required
number of pairwise disjoint triples. -/
theorem pack_short_triples (v : ℕ → ℝ) (m : ℕ) (hv : Monotone v) {L : ℝ}
    (hL : v (m+1) - v 0 ≤ L) :
    ∃ starts : Finset ℕ, (m:ℝ) - 2*L/(59044015980121 / 19531250000000) ≤ 3*starts.card ∧
      (∀ i ∈ starts, i < m ∧ v (i+2) - v i ≤ (59044015980121 / 19531250000000)) ∧
      ∀ i ∈ starts, ∀ j ∈ starts, i < j → i+2 < j := by
  classical
  let all := Finset.range m
  let good := all.filter (fun i => v (i+2)-v i ≤ (59044015980121 / 19531250000000))
  let bad := all \ good
  have hbad : (59044015980121 / 19531250000000)*bad.card ≤ ∑ i ∈ all, (v (i+2)-v i) := by
    calc
      _ = ∑ _ ∈ bad, ((59044015980121 / 19531250000000):ℝ) := by simp <;> ring
      _ ≤ ∑ i ∈ bad, (v (i+2)-v i) := by
        apply Finset.sum_le_sum
        intro i hi
        obtain ⟨hi, hn⟩ := Finset.mem_sdiff.mp hi
        exact le_of_not_ge (fun h => hn (Finset.mem_filter.mpr ⟨hi,h⟩))
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset
        (fun i _ _ => sub_nonneg.mpr (hv (by omega)))
  rw [show all = Finset.range m from rfl, sum_spans] at hbad
  have hcard : bad.card + good.card = m := by
    simpa [good,bad,all] using Finset.card_sdiff_add_card_eq_card (Finset.filter_subset _ all :
      good ⊆ all)
  let fiber (r : ℕ) := good.filter (fun i => i%3 = r)
  obtain ⟨r, hr, hmax⟩ := (Finset.range 3).exists_max_image (fun r => (fiber r).card) (by decide)
  have partition : good.card = ∑ j ∈ Finset.range 3, (fiber j).card :=
    Finset.card_eq_sum_card_fiberwise (fun i _ => Finset.mem_range.mpr (Nat.mod_lt i (by decide)))
  have largest : good.card ≤ 3*(fiber r).card := by
    rw [partition]
    simpa using Finset.sum_le_sum (s := Finset.range 3) (f := fun j => (fiber j).card)
      (g := fun _ => (fiber r).card) hmax
  refine ⟨fiber r, ?_, ?_, ?_⟩
  · have cm : (bad.card:ℝ) + good.card = m := by exact_mod_cast hcard
    have cr : (good.card:ℝ) ≤ 3*(fiber r).card := by exact_mod_cast largest
    linarith [hbad, hv (show m ≤ m+1 by omega), hv (show 0 ≤ 1 by decide)]
  · intro i hi
    obtain ⟨hgood,_⟩ := Finset.mem_filter.mp hi
    obtain ⟨hm,hspan⟩ := Finset.mem_filter.mp hgood
    exact ⟨Finset.mem_range.mp hm,hspan⟩
  · intro i hi j hj hij
    have h1 := (Finset.mem_filter.mp hi).2
    have h2 := (Finset.mem_filter.mp hj).2
    omega

/-- Each selected short triple supplies two distinct endpoints whose
absolute real Fourier overlap reaches the threshold used in the trace proof. -/
theorem select_pairs (v : ℕ → ℝ) (m : ℕ) (hv : Monotone v) {L : ℝ}
    (hL : v (m+1) - v 0 ≤ L) :
    ∃ (starts : Finset ℕ) (p q : ℕ → ℕ),
      (m:ℝ) - 2*L/(59044015980121 / 19531250000000) ≤ 3*starts.card ∧
      (∀ i ∈ starts, i ≤ p i ∧ p i < q i ∧ q i ≤ i+2 ∧ q i < m+2 ∧
        (eta:ℝ) ≤ |fourierReal (v (q i)-v (p i))|) ∧
      ∀ i ∈ starts, ∀ j ∈ starts, i < j → q i < p j := by
  classical
  obtain ⟨s, hcard, hshort, hdis⟩ := pack_short_triples v m hv hL
  let P (i a b : ℕ) := i ≤ a ∧ a < b ∧ b ≤ i+2 ∧ b < m+2 ∧
        (eta:ℝ) ≤ |fourierReal (v b-v a)|
  have pair : ∀ i, ∃ a b, i ∈ s → P i a b := by
    intro i
    by_cases hi : i ∈ s
    · obtain ⟨him, hspan⟩ := hshort i hi
      have x := sub_nonneg.mpr (hv (show i ≤ i+1 by omega))
      have y := sub_nonneg.mpr (hv (show i+1 ≤ i+2 by omega))
      have h := fourier_triple x y (by linarith)
      rw [show v (i+1)-v i + (v (i+2)-v (i+1)) = v (i+2)-v i by ring] at h
      rcases h with he | he | he
      · exact ⟨i,i+1,fun _ => ⟨by omega,by omega,by omega,by omega,he⟩⟩
      · exact ⟨i+1,i+2,fun _ => ⟨by omega,by omega,by omega,by omega,he⟩⟩
      · exact ⟨i,i+2,fun _ => ⟨by omega,by omega,by omega,by omega,he⟩⟩
    · exact ⟨0,0,fun h => (hi h).elim⟩
  choose p q hpq using pair
  refine ⟨s,p,q,hcard,hpq,?_⟩
  intro i hi j hj hij
  exact lt_of_le_of_lt (hpq i hi).2.2.1 ((hdis i hi j hj hij).trans_le (hpq j hj).1)

/-- Finite-window version, including empty and singleton windows. The
endpoints are ordinates in the supplied set, and different pairs are ordered. -/
theorem pack_window (S : Finset ℝ) {a b : ℝ} (hab : a ≤ b)
    (hS : ∀ x ∈ S, a ≤ x ∧ x ≤ b) :
    ∃ (starts : Finset ℕ) (p q : ℕ → ℝ),
      (S.card:ℝ) - 2 - 2*(b-a)/(59044015980121 / 19531250000000) ≤ 3*starts.card ∧
      (∀ i ∈ starts, p i ∈ S ∧ q i ∈ S ∧ p i < q i ∧
        (eta:ℝ) ≤ |fourierReal (q i-p i)|) ∧
      ∀ i ∈ starts, ∀ j ∈ starts, i < j → q i < p j := by
  classical
  by_cases hsmall : S.card < 2
  · refine ⟨∅,fun _ => 0,fun _ => 0,?_,by simp,by simp⟩
    have h : (S.card:ℝ) ≤ 1 := by exact_mod_cast (show S.card ≤ 1 by omega)
    simp only [Finset.card_empty, Nat.cast_zero, mul_zero]
    linarith
  let m := S.card - 2
  have hm : S.card = m+2 := by dsimp [m]; omega
  let index (i : ℕ) : Fin (m+2) := ⟨min i (m+1),by omega⟩
  let v (i : ℕ) := S.orderEmbOfFin hm (index i)
  have mem (i : ℕ) : v i ∈ S := S.orderEmbOfFin_mem hm _
  have mono : Monotone v := fun i j hij =>
    (S.orderEmbOfFin hm).monotone (show min i (m+1) ≤ min j (m+1) from min_le_min_right _ hij)
  have strict {i j : ℕ} (hij : i < j) (hj : j < m+2) : v i < v j := by
    apply (S.orderEmbOfFin hm).strictMono
    change min i (m+1) < min j (m+1)
    omega
  obtain ⟨s,p,q,hc,hpq,hd⟩ := select_pairs v m mono
    (L := b-a) (by linarith [(hS _ (mem 0)).1, (hS _ (mem (m+1))).2])
  refine ⟨s,v ∘ p,v ∘ q,?_,?_,?_⟩
  · rw [hm, Nat.cast_add, Nat.cast_ofNat]; linarith
  · intro i hi
    obtain ⟨_,hp,_,hq,he⟩ := hpq i hi
    exact ⟨mem _,mem _,strict hp hq,he⟩
  · intro i hi j hj hij
    obtain ⟨_,hp,_,hq,_⟩ := hpq j hj
    exact strict (hd i hi j hj hij) (hp.trans hq)

end Devine32Retained
end
end Src_Devine_ConditionalShiftedCubicPacking
section Src_Devine_ConditionalShiftedCubicZeroPairs



/-! The disjoint pairs in T041-0074 come from actual nontrivial zeros. -/
noncomputable section
namespace Devine32Retained
open FourierCertificate

/-- With normalization `k = σ log T / (2π)`, the width is `k*T`. RH makes
the scaled ordinate map injective on the distinct complex zeros. -/
theorem dyadic_zero_pairs (hRH : RiemannHypothesis) {T k : ℝ} (hT : 0 ≤ T) (hk : 0 < k) :
    ∃ (s : Finset ℕ) (p q : ℕ → ℂ),
      (Zeta23.Ndist T (2*T):ℝ) - 2 - 2*(k*T)/(59044015980121 / 19531250000000) ≤ 3*s.card ∧
      (∀ i ∈ s, p i ∈ Zeta23.zerosIn T (2*T) ∧ q i ∈ Zeta23.zerosIn T (2*T) ∧
        (p i).im < (q i).im ∧ (eta:ℝ) ≤ |fourierReal (k*((q i).im-(p i).im))|) ∧
      ∀ i ∈ s, ∀ j ∈ s, i < j → (q i).im < (p j).im := by
  classical
  let Z := (Zeta23.zerosIn_finite T (2*T)).toFinset
  let S := Z.image (fun ρ : ℂ => k*ρ.im)
  have zm {ρ : ℂ} : ρ ∈ Z ↔ ρ ∈ Zeta23.zerosIn T (2*T) := Set.Finite.mem_toFinset _
  have inj : Set.InjOn (fun ρ : ℂ => k*ρ.im) Z := by
    intro ρ hr τ ht he
    exact Complex.ext ((Zeta23.RH_implies_on_line hRH (zm.mp hr).1).trans
      (Zeta23.RH_implies_on_line hRH (zm.mp ht).1).symm) (mul_left_cancel₀ hk.ne' he)
  have card : S.card = Zeta23.Ndist T (2*T) := by
    rw [show S.card = Z.card from Finset.card_image_of_injOn inj]
    exact (Set.ncard_eq_toFinset_card _ (Zeta23.zerosIn_finite T (2*T))).symm
  have bounds : ∀ u ∈ S, k*T ≤ u ∧ u ≤ k*(2*T) := by
    intro u hu
    obtain ⟨ρ,hm,rfl⟩ := Finset.mem_image.mp hu
    exact ⟨mul_le_mul_of_nonneg_left (zm.mp hm).2.1.le hk.le,
      mul_le_mul_of_nonneg_left (zm.mp hm).2.2 hk.le⟩
  obtain ⟨s,P,Q,hc,hpq,hd⟩ := pack_window S (by nlinarith : k*T ≤ k*(2*T)) bounds
  let z (u : ℝ) : ℂ := ⟨1/2,u/k⟩
  have lift {u : ℝ} (hu : u ∈ S) : z u ∈ Zeta23.zerosIn T (2*T) := by
    obtain ⟨ρ,hm,rfl⟩ := Finset.mem_image.mp hu
    have he : z (k*ρ.im) = ρ := by
      apply Complex.ext
      · exact (Zeta23.RH_implies_on_line hRH (zm.mp hm).1).symm
      · change k*ρ.im/k = ρ.im; field_simp
    rw [he]; exact zm.mp hm
  refine ⟨s,z ∘ P,z ∘ Q,?_,?_,?_⟩
  · rw [card, show k*(2*T)-k*T = k*T by ring] at hc
    exact hc
  · intro i hi
    obtain ⟨hp,hq,hlt,he⟩ := hpq i hi
    refine ⟨lift hp,lift hq,div_lt_div_of_pos_right hlt hk,?_⟩
    change (eta:ℝ) ≤ |fourierReal (k*(Q i/k-P i/k))|
    rwa [show k*(Q i/k-P i/k) = Q i-P i by field_simp]
  · intro i hi j hj hij
    exact div_lt_div_of_pos_right (hd i hi j hj hij) hk

end Devine32Retained
end
end Src_Devine_ConditionalShiftedCubicZeroPairs

section Src_Devine32RetainedGram



/-!
# Retained pair energy for the Gram matrix of the zeros (T041-0074, Sections 1 and 3)

The input is the leader's Gram matrix for a finite set `S` of zeros that
contains the window `(T, 2T]`. The disjoint pairs are those selected by
`Devine32Retained.dyadic_zero_pairs` at the scale
`sigma log T / (2 pi)`. For each `S`, the finite trace combination is at least
`phiSum + m g`. The selection and its size `m` do not depend on `S`, so the
leader's uniform limit (`TMG.phiSum_le_Xi`) carries the same bound to the full
kernel.
-/

open Matrix
open scoped ComplexOrder BigOperators

noncomputable section

namespace TMG.Devine32Gain
open TMG.PairGain

/-- Order facts for the ordinates of the selected pairs. -/
theorem pairs_ordered {s : Finset ℕ} {p q : ℕ → ℂ}
    (hlt : ∀ i ∈ s, (p i).im < (q i).im)
    (hdis : ∀ i ∈ s, ∀ j ∈ s, i < j → (q i).im < (p j).im) :
    (∀ i ∈ s, ∀ j ∈ s, p i = p j → i = j) ∧ (∀ i ∈ s, ∀ j ∈ s, q i = q j → i = j) ∧
      (∀ i ∈ s, ∀ j ∈ s, p i ≠ q j) := by
  refine ⟨fun i hi j hj h => ?_, fun i hi j hj h => ?_, fun i hi j hj h => ?_⟩
  · have e := congrArg Complex.im h
    rcases lt_trichotomy i j with hij | hij | hij
    · exfalso
      linarith [hlt i hi, hdis i hi j hj hij]
    · exact hij
    · exfalso
      linarith [hlt j hj, hdis j hj i hi hij]
  · have e := congrArg Complex.im h
    rcases lt_trichotomy i j with hij | hij | hij
    · exfalso
      linarith [hlt j hj, hdis i hi j hj hij]
    · exact hij
    · exfalso
      linarith [hlt i hi, hdis j hj i hi hij]
  · have e := congrArg Complex.im h
    rcases lt_trichotomy i j with hij | hij | hij
    · linarith [hlt i hi, hlt j hj, hdis i hi j hj hij]
    · rw [← hij] at e
      linarith [hlt i hi]
    · linarith [hlt i hi, hdis j hj i hi hij]

/-- The finite Gram inequality with retained pairs. The number `m` of selected
pairs comes before the finite set `S`. -/
theorem phiSum_pairs_le_Kfin (hRH : RiemannHypothesis) (w : TMA.HeightWeight) {T t σ : ℝ}
    (hT : 1 < T) (hσ : 0 < σ) (ht1 : 1 ≤ t) (ht2 : t < 2)
    (htη : t ≤ 1 + (Devine32Retained.eta : ℝ))
    (hg : (1 + (Devine32Retained.eta : ℝ)) *
        (1 + (Devine32Retained.eta : ℝ) - t) ^ 2
      ≤ 4 * (2 - t) * (Devine32Retained.eta : ℝ) ^ 2) :
    ∃ m : ℕ,
      (Zeta23.Ndist T (2 * T) : ℝ) - 2 - 2 * (σ * Real.log T / (2 * Real.pi) * T) / (59044015980121 / 19531250000000)
          ≤ 3 * (m : ℝ) ∧
      ∀ S : Finset ℂ, ThirdMoment.zerosFinset T (2 * T) ⊆ S →
        ThirdMoment.phiSum t T (2 * T) + (m : ℝ) *
            ((1 + (Devine32Retained.eta : ℝ)) *
              (1 + (Devine32Retained.eta : ℝ) - t) ^ 2)
          ≤ (t3 DevineDegree32.W (TMA.Kfin w.h T σ S)).re - 2 * t * t2 DevineDegree32.W (TMA.Kfin w.h T σ S)
              + t ^ 2 * (TMA.Kfin w.h T σ S 0).re := by
  classical
  have hT0 : (0 : ℝ) ≤ T := by linarith
  have hTpos : (0 : ℝ) < T := by linarith
  have ht0 : (0 : ℝ) ≤ t := by linarith
  have heta0 : (0 : ℝ) ≤ (Devine32Retained.eta : ℝ) := by
    norm_num [Devine32Retained.eta]
  have hk : 0 < σ * Real.log T / (2 * Real.pi) :=
    div_pos (mul_pos hσ (Real.log_pos hT)) (by positivity)
  obtain ⟨s, p, q, hcard, hpq, hdis⟩ :=
    Devine32Retained.dyadic_zero_pairs hRH hT0 hk
  refine ⟨s.card, hcard, fun S hS => ?_⟩
  obtain ⟨hinjp, hinjq, hne⟩ := pairs_ordered (s := s) (p := p) (q := q)
    (fun i hi => (hpq i hi).2.2.1) hdis
  -- the leader's Gram matrix of the finite kernel
  have hc : ∀ a : S, 0 ≤ TMA.cw w.h T a := fun a => TMA.cw_nonneg w T a
  obtain ⟨A, hAdef⟩ : ∃ A : Matrix S S ℂ, A = Gram.gramW DevineDegree32.W (fun a : S => TMA.cw w.h T a)
      (fun a : S => σ * Real.log T * (a : ℂ).im) := ⟨_, rfl⟩
  have hA : A.PosSemidef := by
    rw [hAdef]
    exact Gram.gramW_posSemidef _ _ _
  have hdiag : ∀ a : S, (A a a).re = TMA.cw w.h T a := by
    intro a
    rw [hAdef, Gram.gramW_diag DevineDegree32.W _ _ hc a, Complex.ofReal_re]
  have hoffd : ∀ a b : S, (A a b).re = Real.sqrt (TMA.cw w.h T a) * Real.sqrt (TMA.cw w.h T b) *
      (ghat DevineDegree32.W (σ * Real.log T * (a : ℂ).im - σ * Real.log T * (b : ℂ).im)).re := by
    intro a b
    rw [hAdef]
    simp only [Gram.gramW, Matrix.of_apply]
    rw [← Complex.ofReal_mul, Complex.re_ofReal_mul]
  have hker : ∀ u v : ℝ, (ghat DevineDegree32.W (σ * Real.log T * u - σ * Real.log T * v)).re
      = Devine32Retained.FourierCertificate.fourierReal
          (σ * Real.log T / (2 * Real.pi) * (u - v)) := by
    intro u v
    have hπ : (2 * Real.pi) ≠ 0 := by positivity
    have e : 2 * Real.pi * (σ * Real.log T / (2 * Real.pi) * (u - v))
        = σ * Real.log T * u - σ * Real.log T * v := by
      first
        | (rw [div_mul_eq_mul_div, mul_div_assoc', mul_div_cancel_left₀ _ hπ]; ring)
        | (field_simp; done)
        | (field_simp; ring)
    rw [← e, Devine32Link.kernel_re]
  -- the window as a finset of indices
  obtain ⟨Zs, hsumZ, hZ1, hZ2⟩ : ∃ Zs : Finset S,
      ∑ a ∈ Zs, ThirdMoment.phi t (Zeta23.zeroMult (a : ℂ)) = ThirdMoment.phiSum t T (2 * T) ∧
      (∀ a ∈ Zs, (a : ℂ) ∈ ThirdMoment.zerosFinset T (2 * T)) ∧
      (∀ a : S, (a : ℂ) ∈ ThirdMoment.zerosFinset T (2 * T) → a ∈ Zs) := by
    let embed : ↥(ThirdMoment.zerosFinset T (2*T)) ↪ ↥S :=
      ⟨fun ρ => ⟨ρ.1,hS ρ.2⟩,fun _ _ h => Subtype.ext (congrArg (fun z : S => (z : ℂ)) h)⟩
    refine ⟨(ThirdMoment.zerosFinset T (2*T)).attach.map embed, ?_, ?_, ?_⟩
    · rw [Finset.sum_map, ThirdMoment.phiSum_eq]
      exact Finset.sum_attach (ThirdMoment.zerosFinset T (2 * T))
        (fun ρ => ThirdMoment.phi t (Zeta23.zeroMult ρ))
    · intro a ha
      obtain ⟨ρ, -, rfl⟩ := Finset.mem_map.mp ha
      exact ρ.2
    · intro a ha
      exact Finset.mem_map.mpr ⟨⟨a.1, ha⟩, Finset.mem_attach _ _, rfl⟩
  -- the selected pairs as indices
  obtain ⟨P, hP⟩ : ∃ P : s → S, ∀ k, (P k : ℂ) = p k.1 :=
    ⟨fun k => ⟨p k.1, hS (ThirdMoment.mem_zerosFinset.mpr (hpq k.1 k.2).1)⟩, fun k => rfl⟩
  obtain ⟨Q, hQ⟩ : ∃ Q : s → S, ∀ k, (Q k : ℂ) = q k.1 :=
    ⟨fun k => ⟨q k.1, hS (ThirdMoment.mem_zerosFinset.mpr (hpq k.1 k.2).2.1)⟩, fun k => rfl⟩
  have hPm : ∀ k : s, (P k : ℂ) ∈ ThirdMoment.zerosFinset T (2 * T) := fun k => by
    rw [hP]
    exact ThirdMoment.mem_zerosFinset.mpr (hpq k.1 k.2).1
  have hQm : ∀ k : s, (Q k : ℂ) ∈ ThirdMoment.zerosFinset T (2 * T) := fun k => by
    rw [hQ]
    exact ThirdMoment.mem_zerosFinset.mpr (hpq k.1 k.2).2.1
  have hPinj : Set.InjOn P (Finset.univ : Finset s) := by
    intro i _ j _ h
    apply Subtype.ext
    have h' := congrArg Subtype.val h
    rw [hP, hP] at h'
    exact hinjp i.1 i.2 j.1 j.2 h'
  have hQinj : Set.InjOn Q (Finset.univ : Finset s) := by
    intro i _ j _ h
    apply Subtype.ext
    have h' := congrArg Subtype.val h
    rw [hQ, hQ] at h'
    exact hinjq i.1 i.2 j.1 j.2 h'
  have hPQ : ∀ k ∈ (Finset.univ : Finset s), ∀ l ∈ (Finset.univ : Finset s), P k ≠ Q l := by
    intro k _ l _ h
    have h' := congrArg Subtype.val h
    rw [hP, hQ] at h'
    exact hne k.1 k.2 l.1 l.2 h'
  -- the gain on each selected pair
  have hgain : ∀ k ∈ (Finset.univ : Finset s),
      ThirdMoment.phi t (Zeta23.zeroMult (P k : ℂ)) + ThirdMoment.phi t (Zeta23.zeroMult (Q k : ℂ))
        + (1 + (Devine32Retained.eta : ℝ)) *
            (1 + (Devine32Retained.eta : ℝ) - t) ^ 2
      ≤ ((cubeP A t) (P k) (P k)).re + ((cubeP A t) (Q k) (Q k)).re := by
    intro k _
    refine pair_gain hA ht1 ht2 heta0 htη hg ?_ (ThirdMoment.one_le_mult_of_mem (hPm k))
      (ThirdMoment.one_le_mult_of_mem (hQm k)) ?_ ?_ ?_
    · intro h
      have h' := congrArg Subtype.val h
      rw [hP, hQ] at h'
      exact hne k.1 k.2 k.1 k.2 h'
    · rw [hdiag]
      exact Gram.zeroMult_le_cw w hTpos (ThirdMoment.mem_zerosFinset.mp (hPm k))
    · rw [hdiag]
      exact Gram.zeroMult_le_cw w hTpos (ThirdMoment.mem_zerosFinset.mp (hQm k))
    · rw [hdiag, hdiag, hoffd, hker, hQ, hP]
      have hF := (hpq k.1 k.2).2.2.2
      have hcp := TMA.cw_nonneg w T (p k.1)
      have hcq := TMA.cw_nonneg w T (q k.1)
      rw [mul_pow, mul_pow, Real.sq_sqrt hcq, Real.sq_sqrt hcp]
      have hF2 : (Devine32Retained.eta : ℝ) ^ 2 ≤
          (Devine32Retained.FourierCertificate.fourierReal
            (σ * Real.log T / (2 * Real.pi) * ((q k.1).im - (p k.1).im))) ^ 2 := by
        rw [sq_le_sq, abs_of_nonneg heta0]
        exact hF
      have hmul := mul_le_mul_of_nonneg_right hF2 (mul_nonneg hcp hcq)
      linarith
  -- assemble with the leader's trace identities
  have key := pairs_trace_le hA ht0 (fun a : S => ThirdMoment.phi t (Zeta23.zeroMult (a : ℂ))) Zs
    (fun a ha => by
      rw [hdiag]
      exact ThirdMoment.phi_mono ht0 (Nat.cast_nonneg _)
        (Gram.zeroMult_le_cw w hTpos (ThirdMoment.mem_zerosFinset.mp (hZ1 a ha))))
    (Finset.univ : Finset s) P Q (fun k _ => hZ2 _ (hPm k)) (fun k _ => hZ2 _ (hQm k))
    hPinj hQinj hPQ hgain
  rw [hsumZ, Finset.card_univ, Fintype.card_coe, hAdef] at key
  rw [Gram.trace_gramW_cube DevineDegree32.W _ _ hc, Gram.trace_gramW_sq DevineDegree32.W _ _ hc, Gram.trace_gramW DevineDegree32.W _ _ hc,
    ← Gram.Kfin_eq_trigK] at key
  have hre : (t3 DevineDegree32.W (TMA.Kfin w.h T σ S) - 2 * (t : ℂ) * ((t2 DevineDegree32.W (TMA.Kfin w.h T σ S) : ℝ) : ℂ)
        + (t : ℂ) ^ 2 * TMA.Kfin w.h T σ S 0).re
      = (t3 DevineDegree32.W (TMA.Kfin w.h T σ S)).re - 2 * t * t2 DevineDegree32.W (TMA.Kfin w.h T σ S)
          + t ^ 2 * (TMA.Kfin w.h T σ S 0).re := by
    have e1 : 2 * (t : ℂ) * ((t2 DevineDegree32.W (TMA.Kfin w.h T σ S) : ℝ) : ℂ)
        = ((2 * t * t2 DevineDegree32.W (TMA.Kfin w.h T σ S) : ℝ) : ℂ) := by
      push_cast
      ring
    have e2 : (t : ℂ) ^ 2 = ((t ^ 2 : ℝ) : ℂ) := by
      push_cast
      ring
    rw [e1, e2, Complex.add_re, Complex.sub_re, Complex.ofReal_re, Complex.re_ofReal_mul]
  rw [hre] at key
  exact key

/-- The Gram step with retained pairs, for the full kernel of the zeros. -/
theorem phiSum_pairs_le_Xi (hRH : RiemannHypothesis) (w : TMA.HeightWeight) {T t σ : ℝ}
    (hT : 1 < T) (hσ : 0 < σ) (ht1 : 1 ≤ t) (ht2 : t < 2)
    (htη : t ≤ 1 + (Devine32Retained.eta : ℝ))
    (hg : (1 + (Devine32Retained.eta : ℝ)) *
        (1 + (Devine32Retained.eta : ℝ) - t) ^ 2
      ≤ 4 * (2 - t) * (Devine32Retained.eta : ℝ) ^ 2) :
    ∃ m : ℕ,
      (Zeta23.Ndist T (2 * T) : ℝ) - 2 - 2 * (σ * Real.log T / (2 * Real.pi) * T) / (59044015980121 / 19531250000000)
          ≤ 3 * (m : ℝ) ∧
      ThirdMoment.phiSum t T (2 * T) + (m : ℝ) *
          ((1 + (Devine32Retained.eta : ℝ)) *
            (1 + (Devine32Retained.eta : ℝ) - t) ^ 2)
        ≤ (t3 DevineDegree32.W (TMA.Kfull w.h T σ)).re - 2 * t * t2 DevineDegree32.W (TMA.Kfull w.h T σ)
            + t ^ 2 * (TMA.Kfull w.h T σ 0).re := by
  obtain ⟨m, hm, h⟩ := phiSum_pairs_le_Kfin hRH w hT hσ ht1 ht2 htη hg
  exact ⟨m, hm, le_Xi_of_le_Kfin hRH DevineDegree32.W w (by linarith) h⟩

end TMG.Devine32Gain

end
end Src_Devine32RetainedGram

section Src_Devine32RetainedTransfer
/-
Apache-2.0 §4(b), 贝奕 (Bei Yi), 2026-11-23 UTC+08:00.
Optimize the shift for the frozen octic window in the retained-pair quotient.
The shift-only quartic improvement is due to ajp88.
Original retained-pair extension by Michael Devine, based on Kristian Muri Knausgård.
SPDX-License-Identifier: Apache-2.0
-/


/-!
# Transfer of the retained pairs to both distinct-zero counts (T041-0074, Sections 3 and 4)

With `g = (1 + eta)(1 + eta - t)^2`, the Gram step with retained pairs and
`3 m ≥ D - 2 - (2/3) sigma Dsc` give the additive budget

    phiSum t T (2T) + (g/3) Ndist T (2T) ≤ (C3 - 2 t C2 + t^2 + 2g/9 + eps) N(T, 2T)

at every bandwidth `sigma < 1` (`budget_sigma_pairs`). The limit `sigma → 1`
is taken exactly as in the leader's `budget_dyadic` (`budget_dyadic_pairs`).
The left side is additive over adjacent windows, so the leader's
`Cumulative.dyadic_upper` gives the same budget on `(0, T]`.

With `H = 2(2-t)^2`, the inequality `phi(m) ≥ H (m - 1)` gives
`H (N - D) + (g/3) D ≤ (K + eps) N`. Hence
`D ≥ ((H - K)/(H - g/3) - eps) N`. At the leader's window `DevineDegree32.W` and shift
`pairShift`, this ratio exceeds `7467259030701813869739730211166225298027652489304375443581010163149153437228159306762267726029670194888697704273164057355823112360018062855667878677027709276696065953004943987720266315230953455410883 / 8860274382827684373426110524043993283228053047698953524152136784089094997182778051879727134858536985101946476314074081005564061157704101990052816823160393668320260609150049071187435095675724245271026`.
-/

open scoped BigOperators Real

noncomputable section

namespace TMG.Devine32Gain

section Transfer

local notation "η₀" => ((Devine32Retained.eta : ℚ) : ℝ)

/-- The third-moment budget with retained pairs on dyadic windows. -/
def PairBudget (t K c : ℝ) : Prop :=
  ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
    ThirdMoment.phiSum t T (2 * T) + c * (Zeta23.Ndist T (2 * T) : ℝ)
      ≤ (K + ε) * (Zeta23.Ncount T (2 * T) : ℝ)

theorem Dsc_large {a b : ℝ} (hb : 0 < b) : ∃ T₁ : ℝ, ∀ T ≥ T₁, a ≤ b * TMA.Dsc T := by
  refine ⟨max 3 (2 * Real.pi * |a| / b), fun T hT => ?_⟩
  have hT3 : 3 ≤ T := le_trans (le_max_left _ _) hT
  have hTa : 2 * Real.pi * |a| / b ≤ T := le_trans (le_max_right _ _) hT
  have hTpos : 0 < T := by linarith
  have hπ : 0 < 2 * Real.pi := by positivity
  have hlog : 1 ≤ Real.log T := by
    rw [Real.le_log_iff_exp_le hTpos]
    have h3 : Real.exp 1 ≤ 3 := by linarith [Real.exp_one_lt_d9]
    linarith
  have h1 : 2 * Real.pi * |a| ≤ T * b := (div_le_iff₀ hb).mp hTa
  have h2 : T ≤ T * Real.log T := by
    have := mul_le_mul_of_nonneg_left hlog hTpos.le
    linarith
  have h3 : |a| * (2 * Real.pi) ≤ b * (T * Real.log T) := by
    have := mul_le_mul_of_nonneg_left h2 hb.le
    linarith
  have h4 : |a| ≤ b * (T * Real.log T / (2 * Real.pi)) := by
    rw [mul_div_assoc', le_div_iff₀ hπ]
    exact h3
  unfold TMA.Dsc
  linarith [le_abs_self a]

/-- Bookkeeping for the retained pairs: `3 m ≥ D - 2 - (2/3) sigma Dsc`. -/
theorem pair_assemble {P Dc m D K0 η g σ ε : ℝ}
    (hP : P + m * g ≤ (K0 + η) * D)
    (hm : Dc - 2 - 2 * (σ * D) / (59044015980121 / 19531250000000) ≤ 3 * m) (hg : 0 ≤ g) (hσ1 : σ ≤ 1) (hD : 0 ≤ D)
    (hc0 : 2 * g / 3 ≤ ε / 4 * D) :
    P + g / 3 * Dc ≤ (K0 + 2 * g / (3 * (59044015980121 / 19531250000000)) + (η + ε / 4)) * D := by
  have h1 : g / 3 * Dc ≤ g / 3 * (3 * m + 2 + 2 * (σ * D) / (59044015980121 / 19531250000000)) :=
    mul_le_mul_of_nonneg_left (by linarith) (div_nonneg hg (by norm_num))
  have h2 : g * (σ * D) ≤ g * D := mul_le_mul_of_nonneg_left (mul_le_of_le_one_left hD hσ1) hg
  linear_combination hP + h1 + (39062500000000/177132047940363) * h2 + hc0

open MainAux in
/-- The budget with retained pairs at bandwidth `sigma < 1`. This is the
leader's `budget_sigma` with the Gram step `phiSum_pairs_le_Xi`. -/
theorem budget_sigma_pairs (hRH : RiemannHypothesis) {σ t : ℝ} (hσ : 0 < σ) (hσ1 : σ < 1)
    (ht1 : 1 ≤ t) (ht2 : t < 2) (htη : t ≤ 1 + η₀)
    (hg : (1 + η₀) * (1 + η₀ - t) ^ 2 ≤ 4 * (2 - t) * η₀ ^ 2) :
    PairBudget t (C3 DevineDegree32.W σ - 2 * t * C2 DevineDegree32.W σ + t ^ 2 + 2 * ((1 + η₀) * (1 + η₀ - t) ^ 2) / (3 * (59044015980121 / 19531250000000)))
      ((1 + η₀) * (1 + η₀ - t) ^ 2 / 3) := by
  intro ε hε
  have ht : 0 ≤ t := by linarith
  have heta : 0 ≤ η₀ := by norm_num [Devine32Retained.eta]
  have hg0 : 0 ≤ (1 + η₀) * (1 + η₀ - t) ^ 2 := mul_nonneg (by linarith) (sq_nonneg _)
  have hC3 : 0 ≤ C3 DevineDegree32.W σ := C3_nonneg DevineDegree32.W σ
  have hC2 : 0 ≤ C2 DevineDegree32.W σ := C2_nonneg DevineDegree32.W hσ
  have hε2 : 0 < ε / 2 := by linarith
  obtain ⟨ε1, hε1pos, hε1le⟩ := exists_small_mul hε2 (add_nonneg hC3 (sq_nonneg t))
  obtain ⟨δ, hδpos, hδle⟩ := exists_small_mul hε2 (sq_nonneg (1 + t))
  obtain ⟨θ, hθpos, hθK⟩ : ∃ θ : ℝ, 0 < θ ∧
      θ * (|C3 DevineDegree32.W σ - 2 * t * C2 DevineDegree32.W σ + t ^ 2 + 2 * ((1 + η₀) * (1 + η₀ - t) ^ 2) / (3 * (59044015980121 / 19531250000000))| + ε)
        ≤ ε / 2 := by
    have hden : 0 < |C3 DevineDegree32.W σ - 2 * t * C2 DevineDegree32.W σ + t ^ 2 + 2 * ((1 + η₀) * (1 + η₀ - t) ^ 2) / (3 * (59044015980121 / 19531250000000))|
        + ε := by positivity
    refine ⟨ε / (2 * (|C3 DevineDegree32.W σ - 2 * t * C2 DevineDegree32.W σ + t ^ 2
      + 2 * ((1 + η₀) * (1 + η₀ - t) ^ 2) / (3 * (59044015980121 / 19531250000000))| + ε)), by positivity, le_of_eq ?_⟩
    field_simp
  obtain ⟨w, hw1, hw3⟩ := TMA.exists_heightWeight hε1pos
  obtain ⟨Ta, ha⟩ := TMA.t1_upper hRH w hσ hσ1 δ hδpos
  obtain ⟨Tb, hb⟩ := t2_lower hRH DevineDegree32.W w hσ hσ1 δ hδpos
  obtain ⟨Tc, hc⟩ := t3_upper hRH DevineDegree32.W w hσ hσ1 δ hδpos
  obtain ⟨Td, hd⟩ := rvm_Dsc_le hθpos
  obtain ⟨Te, he⟩ := Dsc_large (a := 2 * ((1 + η₀) * (1 + η₀ - t) ^ 2) / 3) (b := ε / 4)
    (by linarith)
  refine ⟨max Ta (max Tb (max Tc (max Td (max Te 2)))), fun T hT => ?_⟩
  simp only [ge_iff_le, max_le_iff] at hT
  obtain ⟨hTa, hTb, hTc, hTd, hTe, hT2⟩ := hT
  obtain ⟨hTpos, hDpos, hDN⟩ := hd T hTd
  obtain ⟨m, hm, hXi⟩ := phiSum_pairs_le_Xi hRH w (by linarith : (1 : ℝ) < T) hσ ht1 ht2 htη hg
  have hP := assemble_real hXi (hc T hTc) (hb T hTb) (ha T hTa) hDpos.le ht hC3 hC2 hw1 hw3
    w.one_le_kap2
  have hσD : σ * Real.log T / (2 * Real.pi) * T = σ * TMA.Dsc T := by
    unfold TMA.Dsc
    ring
  rw [hσD] at hm
  have hA := pair_assemble hP hm hg0 hσ1.le hDpos.le (he T hTe)
  have hP0 : 0 ≤ ThirdMoment.phiSum t T (2 * T)
      + (1 + η₀) * (1 + η₀ - t) ^ 2 / 3 * (Zeta23.Ndist T (2 * T) : ℝ) :=
    add_nonneg (phiSum_nonneg t T (2 * T))
      (mul_nonneg (div_nonneg hg0 (by norm_num)) (Nat.cast_nonneg _))
  exact final_real hP0 hA hDpos hDN hθpos.le (by linarith) hθK hε (Nat.cast_nonneg _)

open MainAux in
/-- The budget with retained pairs at full bandwidth, as in the leader's `budget_dyadic`. -/
theorem budget_dyadic_pairs (hRH : RiemannHypothesis) {t : ℝ} (ht1 : 1 ≤ t) (ht2 : t < 2)
    (htη : t ≤ 1 + η₀) (hg : (1 + η₀) * (1 + η₀ - t) ^ 2 ≤ 4 * (2 - t) * η₀ ^ 2) :
    PairBudget t (Kt DevineDegree32.W t + 2 * ((1 + η₀) * (1 + η₀ - t) ^ 2) / (3 * (59044015980121 / 19531250000000)))
      ((1 + η₀) * (1 + η₀ - t) ^ 2 / 3) := by
  unfold Kt
  intro ε hε
  have ht : 0 ≤ t := by linarith
  have hM : 0 ≤ 8 * I3 DevineDegree32.W + 2 * t * J2 DevineDegree32.W := by
    have h1 := mul_nonneg ht (J2_nonneg DevineDegree32.W)
    have h2 := I3_nonneg DevineDegree32.W
    linarith
  obtain ⟨s, hs0, hs1, hsM⟩ :
      ∃ s : ℝ, 0 < s ∧ s ≤ 1 / 2 ∧ (8 * I3 DevineDegree32.W + 2 * t * J2 DevineDegree32.W) * s ≤ ε / 2 := by
    obtain ⟨x, hx0, hxM⟩ := exists_small_mul hε hM
    refine ⟨min x (1 / 2), lt_min hx0 (by norm_num), min_le_right _ _, ?_⟩
    have h1 : (8 * I3 DevineDegree32.W + 2 * t * J2 DevineDegree32.W) * min x (1 / 2) ≤ (8 * I3 DevineDegree32.W + 2 * t * J2 DevineDegree32.W) * x :=
      mul_le_mul_of_nonneg_left (min_le_left _ _) hM
    linarith
  have hσ : (1 : ℝ) / 2 ≤ 1 - s := by linarith
  have hσ1 : 1 - s < 1 := by linarith
  have hK := const_le_one DevineDegree32.W hσ hσ1 ht
  rw [sub_sub_cancel] at hK
  obtain ⟨T₀, h₀⟩ :=
    budget_sigma_pairs hRH (by linarith : (0 : ℝ) < 1 - s) hσ1 ht1 ht2 htη hg (ε / 2)
      (by linarith)
  refine ⟨T₀, fun T hT => ?_⟩
  have hN : (0 : ℝ) ≤ (Zeta23.Ncount T (2 * T) : ℝ) := Nat.cast_nonneg _
  have h1 := h₀ T hT
  have h2 : (C3 DevineDegree32.W (1 - s) - 2 * t * C2 DevineDegree32.W (1 - s) + t ^ 2
        + 2 * ((1 + η₀) * (1 + η₀ - t) ^ 2) / (3 * (59044015980121 / 19531250000000)) + ε / 2) * (Zeta23.Ncount T (2 * T) : ℝ)
      ≤ (C3 DevineDegree32.W 1 - 2 * t * C2 DevineDegree32.W 1 + t ^ 2 + 2 * ((1 + η₀) * (1 + η₀ - t) ^ 2) / (3 * (59044015980121 / 19531250000000)) + ε)
        * (Zeta23.Ncount T (2 * T) : ℝ) :=
    mul_le_mul_of_nonneg_right (by linarith) hN
  exact le_trans h1 h2

/-! ### The multiplicity deficit and the counts -/

theorem phi_ge_deficit {t : ℝ} (ht1 : 1 ≤ t) (ht2 : t < 2) (m : ℕ) (hm : 1 ≤ m) :
    2 * (2 - t) ^ 2 * ((m : ℝ) - 1) ≤ ThirdMoment.phi t m := by
  rcases Nat.lt_or_ge m 2 with h | h
  · have e : m = 1 := by omega
    subst e
    rw [Nat.cast_one, ThirdMoment.phi_one ht1]
    norm_num
  · rcases Nat.lt_or_ge m 3 with h3 | h3
    · have e : m = 2 := by omega
      subst e
      have h2 : t ≤ ((2 : ℕ) : ℝ) := by push_cast; linarith
      rw [ThirdMoment.phi_of_le h2]
      push_cast
      nlinarith [sq_nonneg (2 - t)]
    · have hm3 : (3 : ℝ) ≤ m := by exact_mod_cast h3
      rw [ThirdMoment.phi_of_le (by linarith)]
      have hsq : (2 * (2 - t)) ^ 2 ≤ ((m : ℝ) - t) ^ 2 :=
        pow_le_pow_left₀ (by linarith) (by linarith) 2
      have hmul := mul_le_mul_of_nonneg_left hsq (Nat.cast_nonneg m)
      have hpos : 0 ≤ (2 - t) ^ 2 * (2 * (m : ℝ) + 2) := mul_nonneg (sq_nonneg _) (by positivity)
      nlinarith [hmul, hpos]

/-- `2 (2 - t)^2 (N - D) ≤ phiSum` on every window. -/
theorem deficit_le_phiSum {t : ℝ} (ht1 : 1 ≤ t) (ht2 : t < 2) (a b : ℝ) :
    2 * (2 - t) ^ 2 * ((Zeta23.Ncount a b : ℝ) - (Zeta23.Ndist a b : ℝ))
      ≤ ThirdMoment.phiSum t a b := by
  rw [ThirdMoment.Ncount_eq, ThirdMoment.Ndist_eq, ThirdMoment.phiSum_eq]
  have h : ∀ ρ ∈ ThirdMoment.zerosFinset a b,
      2 * (2 - t) ^ 2 * ((Zeta23.zeroMult ρ : ℝ) - 1) ≤ ThirdMoment.phi t (Zeta23.zeroMult ρ) :=
    fun ρ hρ => phi_ge_deficit ht1 ht2 _ (ThirdMoment.one_le_mult_of_mem hρ)
  have hsum := Finset.sum_le_sum h
  rw [← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_one] at hsum
  exact hsum

/-- Division by `H - c > 0`. -/
theorem count_alg {H K c ε N D Φ : ℝ} (hHc : 0 < H - c) (hdef : H * (N - D) ≤ Φ)
    (hbud : Φ + c * D ≤ (K + ε * (H - c)) * N) :
    ((H - K) / (H - c) - ε) * N ≤ D := by
  have key : (H - K - ε * (H - c)) * N ≤ (H - c) * D := by linarith
  have hX : (H - K) / (H - c) * (H - c) = H - K := div_mul_cancel₀ _ hHc.ne'
  have hXN : (H - K) / (H - c) * (H - c) * N = (H - K) * N := by rw [hX]
  have key2 : (H - c) * (((H - K) / (H - c) - ε) * N) ≤ (H - c) * D := by linarith
  exact le_of_mul_le_mul_left key2 hHc

theorem distinct_of_pairBudget {t K c : ℝ} (ht1 : 1 ≤ t) (ht2 : t < 2)
    (hcH : c < 2 * (2 - t) ^ 2) (hB : PairBudget t K c) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      ((2 * (2 - t) ^ 2 - K) / (2 * (2 - t) ^ 2 - c) - ε) * (Zeta23.Ncount T (2 * T) : ℝ)
        ≤ (Zeta23.Ndist T (2 * T) : ℝ) := by
  intro ε hε
  have hHc : 0 < 2 * (2 - t) ^ 2 - c := by linarith
  obtain ⟨T₀, h₀⟩ := hB (ε * (2 * (2 - t) ^ 2 - c)) (mul_pos hε hHc)
  exact ⟨T₀, fun T hT => count_alg hHc (deficit_le_phiSum ht1 ht2 T (2 * T)) (h₀ T hT)⟩

theorem Ndist_add_real {a b d : ℝ} (hab : a ≤ b) (hbd : b ≤ d) :
    (Zeta23.Ndist a d : ℝ) = (Zeta23.Ndist a b : ℝ) + (Zeta23.Ndist b d : ℝ) := by
  have h : Zeta23.Ndist a d = Zeta23.Ndist a b + Zeta23.Ndist b d := by
    unfold Zeta23.Ndist
    rw [Zeta23.zerosIn_union hab hbd]
    refine Set.ncard_union_eq ?_ (Zeta23.zerosIn_finite a b) (Zeta23.zerosIn_finite b d)
    rw [Set.disjoint_left]
    rintro ρ ⟨_, _, hb⟩ ⟨_, ha, _⟩
    exact absurd hb (not_le.2 ha)
  exact_mod_cast h

/-- The dyadic budget with retained pairs gives the same budget on `(0, T]`. -/
theorem pairBudget_cumulative {t K c : ℝ} (hc : 0 ≤ c) (hB : PairBudget t K c) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      ThirdMoment.phiSum t 0 T + c * (Zeta23.Ndist 0 T : ℝ) ≤ (K + ε) * (Zeta23.Ncount 0 T : ℝ) :=
  Cumulative.dyadic_upper (f := fun a b => ThirdMoment.phiSum t a b + c * (Zeta23.Ndist a b : ℝ))
    (g := fun a b => (Zeta23.Ncount a b : ℝ)) (c := K)
    (fun a b d hab hbd => by
      show ThirdMoment.phiSum t a d + c * (Zeta23.Ndist a d : ℝ)
        = (ThirdMoment.phiSum t a b + c * (Zeta23.Ndist a b : ℝ))
          + (ThirdMoment.phiSum t b d + c * (Zeta23.Ndist b d : ℝ))
      rw [Cumulative.phiSum_add t hab hbd, Ndist_add_real hab hbd]
      ring)
    (fun a b d hab hbd => by exact_mod_cast Zeta23.Ncount_add hab hbd)
    (fun a b => add_nonneg (Cumulative.phiSum_nonneg t a b) (mul_nonneg hc (Nat.cast_nonneg _)))
    (fun _ _ => Nat.cast_nonneg _)
    (Zeta23.tendsto_Ncount_zero_atTop Zeta23.zetaSeam Zeta23.riemannVonMangoldt_zeta) hB

theorem distinct_cumulative_of_pairBudget {t K c : ℝ} (ht1 : 1 ≤ t) (ht2 : t < 2) (hc : 0 ≤ c)
    (hcH : c < 2 * (2 - t) ^ 2) (hB : PairBudget t K c) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      ((2 * (2 - t) ^ 2 - K) / (2 * (2 - t) ^ 2 - c) - ε) * (Zeta23.Ncount 0 T : ℝ)
        ≤ (Zeta23.Ndist 0 T : ℝ) := by
  intro ε hε
  have hHc : 0 < 2 * (2 - t) ^ 2 - c := by linarith
  obtain ⟨T₀, h₀⟩ := pairBudget_cumulative hc hB (ε * (2 * (2 - t) ^ 2 - c)) (mul_pos hε hHc)
  exact ⟨T₀, fun T hT => count_alg hHc (deficit_le_phiSum ht1 ht2 0 T) (h₀ T hT)⟩

/-! ### The constants at the leader's window and shift -/

def pairShift : ℝ := 318568213286260499659270516838072866311528290643861596159856943303569043463205981629841925918622079349921108093514259800707133127769361034665205538116532183015120777600071322106580534949274204507071453100423314666249323 / 312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000

theorem pairShift_pair_facts : 1 ≤ pairShift ∧ pairShift < 2 ∧ pairShift ≤ 1 + η₀ ∧
    (1 + η₀) * (1 + η₀ - pairShift) ^ 2 ≤ 4 * (2 - pairShift) * η₀ ^ 2 ∧
    0 ≤ (1 + η₀) * (1 + η₀ - pairShift) ^ 2 / 3 ∧
    (1 + η₀) * (1 + η₀ - pairShift) ^ 2 / 3 < 2 * (2 - pairShift) ^ 2 := by
  unfold pairShift
  norm_num [Devine32Retained.eta, Rat.cast_div, Rat.cast_ofNat]

theorem pair_ratio_exact :
    (2 * (2 - pairShift) ^ 2 -
      (Kt DevineDegree32.W pairShift + 2 * ((1 + η₀) * (1 + η₀ - pairShift) ^ 2) / (3 * (59044015980121 / 19531250000000)))) /
      (2 * (2 - pairShift) ^ 2 - (1 + η₀) * (1 + η₀ - pairShift) ^ 2 / 3) =
        (19064433548596738985535096155146818004249635757248796307499931864193862877977546736254394675568981714541916528372913799433519606903970303407305560453141582574947022682162732057617261358557061900323522774143304677716135990875075037897273213212921046800695813860149285227769043638790666142470109033966340341343426391152596399574379401930689822735891996962331772850180455234753730151744156203829806666719518896004316614785645318301472349607228452715326189144795260707153400719405100785415124648437500000000 : ℝ) / 22620898980368799603335462310380730867592651216783148424891553123197068815577034587405990395672964145284952437168282867376226795173200185315276812638197997243228816614856905744781529353482742332664999535335420298525783752098464495430672135721633736087423376665228900616763921563524416786148797831729581301056536301174853618501482908104487806368445298650840230247565173219704689180347072140155721778320623594663402538056195770874170514057441479603434739605137728701342051378304637421515232935671675048991 := by
  unfold Kt
  rw [DevineDegree32.C2_exact, DevineDegree32.C3_exact]
  norm_num [pairShift, Devine32Retained.eta, Rat.cast_div, Rat.cast_ofNat]

/-- The new constant exceeds `7467259030701813869739730211166225298027652489304375443581010163149153437228159306762267726029670194888697704273164057355823112360018062855667878677027709276696065953004943987720266315230953455410883 / 8860274382827684373426110524043993283228053047698953524152136784089094997182778051879727134858536985101946476314074081005564061157704101990052816823160393668320260609150049071187435095675724245271026 = 84.277965986858061559127160 percent`. -/
theorem pair_record_value :
    (7467259030701813869739730211166225298027652489304375443581010163149153437228159306762267726029670194888697704273164057355823112360018062855667878677027709276696065953004943987720266315230953455410883 / 8860274382827684373426110524043993283228053047698953524152136784089094997182778051879727134858536985101946476314074081005564061157704101990052816823160393668320260609150049071187435095675724245271026 : ℝ) <
      (2 * (2 - pairShift) ^ 2 - (Kt DevineDegree32.W pairShift + 2 * ((1 + η₀) * (1 + η₀ - pairShift) ^ 2) / (3 * (59044015980121 / 19531250000000)))) /
        (2 * (2 - pairShift) ^ 2 - (1 + η₀) * (1 + η₀ - pairShift) ^ 2 / 3) := by
  rw [pair_ratio_exact]
  norm_num

/-- **Distinct zeros on `(T, 2T]` under RH:** at least `84.277965986858061559127160 percent - eps` of the
zeros counted with multiplicity, for all sufficiently large `T`. -/
theorem pair_distinct_dyadic (hRH : RiemannHypothesis) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      ((7467259030701813869739730211166225298027652489304375443581010163149153437228159306762267726029670194888697704273164057355823112360018062855667878677027709276696065953004943987720266315230953455410883 / 8860274382827684373426110524043993283228053047698953524152136784089094997182778051879727134858536985101946476314074081005564061157704101990052816823160393668320260609150049071187435095675724245271026 : ℝ) - ε) * (Zeta23.Ncount T (2 * T) : ℝ)
        ≤ (Zeta23.Ndist T (2 * T) : ℝ) := by
  obtain ⟨h1, h2, h3, h4, _, h6⟩ := pairShift_pair_facts
  intro ε hε
  obtain ⟨T₀, h⟩ := distinct_of_pairBudget h1 h2 h6 (budget_dyadic_pairs hRH h1 h2 h3 h4) ε hε
  refine ⟨T₀, fun T hT => le_trans ?_ (h T hT)⟩
  exact mul_le_mul_of_nonneg_right (by linarith [pair_record_value]) (Nat.cast_nonneg _)

/-- **Distinct zeros on `(0, T]` under RH.** -/
theorem pair_distinct_cumulative (hRH : RiemannHypothesis) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      ((7467259030701813869739730211166225298027652489304375443581010163149153437228159306762267726029670194888697704273164057355823112360018062855667878677027709276696065953004943987720266315230953455410883 / 8860274382827684373426110524043993283228053047698953524152136784089094997182778051879727134858536985101946476314074081005564061157704101990052816823160393668320260609150049071187435095675724245271026 : ℝ) - ε) * (Zeta23.Ncount 0 T : ℝ)
        ≤ (Zeta23.Ndist 0 T : ℝ) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := pairShift_pair_facts
  intro ε hε
  obtain ⟨T₀, h⟩ :=
    distinct_cumulative_of_pairBudget h1 h2 h5 h6 (budget_dyadic_pairs hRH h1 h2 h3 h4) ε hε
  refine ⟨T₀, fun T hT => le_trans ?_ (h T hT)⟩
  exact mul_le_mul_of_nonneg_right (by linarith [pair_record_value]) (Nat.cast_nonneg _)

/-- The dyadic statement for critical-line zeros (`N0star = Ndist` under RH). -/
theorem pair_critical_line_dyadic (hRH : RiemannHypothesis) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      ((7467259030701813869739730211166225298027652489304375443581010163149153437228159306762267726029670194888697704273164057355823112360018062855667878677027709276696065953004943987720266315230953455410883 / 8860274382827684373426110524043993283228053047698953524152136784089094997182778051879727134858536985101946476314074081005564061157704101990052816823160393668320260609150049071187435095675724245271026 : ℝ) - ε) * (Zeta23.Ncount T (2 * T) : ℝ)
        ≤ Zeta23.N0star T (2 * T) := by
  intro ε hε
  obtain ⟨T₀, h⟩ := pair_distinct_dyadic hRH ε hε
  refine ⟨T₀, fun T hT => ?_⟩
  rw [(Zeta23.RH_implies_all_on_line hRH T (2 * T)).2]
  exact h T hT

/-- The cumulative statement for critical-line zeros. -/
theorem pair_critical_line_cumulative (hRH : RiemannHypothesis) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      ((7467259030701813869739730211166225298027652489304375443581010163149153437228159306762267726029670194888697704273164057355823112360018062855667878677027709276696065953004943987720266315230953455410883 / 8860274382827684373426110524043993283228053047698953524152136784089094997182778051879727134858536985101946476314074081005564061157704101990052816823160393668320260609150049071187435095675724245271026 : ℝ) - ε) * (Zeta23.Ncount 0 T : ℝ)
        ≤ Zeta23.N0star 0 T := by
  intro ε hε
  obtain ⟨T₀, h⟩ := pair_distinct_cumulative hRH ε hε
  refine ⟨T₀, fun T hT => ?_⟩
  rw [(Zeta23.RH_implies_all_on_line hRH 0 T).2]
  exact h T hT

end Transfer

end TMG.Devine32Gain

end
end Src_Devine32RetainedTransfer

section T052CapacitySource
/- Apache-2.0. 贝奕, 2026-11-23. Finite row accounting for Devine's retained-pair proof. -/

open scoped BigOperators
namespace T052

theorem weighted_pay {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (p q : E → V) (w g : E → ℝ) (residual : V → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hr : ∀ v, 0 ≤ residual v)
    (he : ∀ i, g i ≤ residual (p i) + residual (q i))
    (hcap : ∀ v, (∑ i, ((if p i = v then w i else 0) +
      (if q i = v then w i else 0))) ≤ 1) :
    ∑ i, w i * g i ≤ ∑ v, residual v := by
  classical
  let a (i : E) (v : V) : ℝ :=
    (if p i = v then w i else 0) + (if q i = v then w i else 0)
  have edge (i : E) : (∑ v, a i v * residual v) =
      w i * (residual (p i) + residual (q i)) := by
    simp [a, add_mul, ite_mul, Finset.sum_add_distrib, mul_add]
  calc
    ∑ i, w i * g i ≤ ∑ i, w i * (residual (p i) + residual (q i)) :=
      Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (he i) (hw i)
    _ = ∑ i, ∑ v, a i v * residual v := by simp_rw [edge]
    _ = ∑ v, (∑ i, a i v) * residual v := by
      rw [Finset.sum_comm]
      simp_rw [Finset.sum_mul]
    _ ≤ ∑ v, residual v := Finset.sum_le_sum fun v _ => by
      simpa using mul_le_mul_of_nonneg_right (hcap v) (hr v)

theorem slack_weight (d : ℕ) (x : ℝ) (hd : d ≤ 3)
    (hx0 : 0 ≤ x) (hx : x ≤ (d : ℝ) / 6) (h : d ≤ 2 ∨ x = 0) :
    (d : ℝ) / 3 + x ≤ 1 := by
  rcases h with h | rfl
  · have hh : (d : ℝ) ≤ 2 := by exact_mod_cast h
    linarith
  · have hh : (d : ℝ) ≤ 3 := by exact_mod_cast hd
    linarith

theorem four_outer (r₀ r₁ r₂ r₃ left right : ℝ)
    (hl : left ≤ r₀ + r₁) (hr : right ≤ r₂ + r₃) :
    left + right ≤ r₀ + r₁ + r₂ + r₃ := by linarith

theorem four_skip (r₀ r₁ r₂ r₃ left right : ℝ)
    (hl : left ≤ r₀ + r₂) (hr : right ≤ r₁ + r₃) :
    left + right ≤ r₀ + r₁ + r₂ + r₃ := by linarith

theorem four_nested (r₀ r₁ r₂ r₃ left right : ℝ)
    (hl : left ≤ r₀ + r₃) (hr : right ≤ r₁ + r₂) :
    left + right ≤ r₀ + r₁ + r₂ + r₃ := by linarith

theorem four_shared_middle (r₀ r₁ r₂ r₃ left right : ℝ)
    (hr₁ : 0 ≤ r₁) (hr₃ : 0 ≤ r₃)
    (hl : left ≤ r₀ + r₁) (hr : right ≤ r₁ + r₂) (hr₀ : 0 ≤ r₀) (hr₂ : 0 ≤ r₂) :
    (left + right) / 2 ≤ r₀ + r₁ + r₂ + r₃ := by linarith

theorem charge_to_window {r Dc w A B z : ℝ}
    (hB : 0 ≤ B) (hz : z ≤ 2*w)
    (hr : A*(Dc-2)-B*z ≤ 3*r) :
    A/3*Dc - (2*B/3)*w - 2*A/3 ≤ r := by
  have := mul_le_mul_of_nonneg_left hz hB
  linarith

theorem charge_assemble {P R Dc A B σ D K err : ℝ}
    (hP : P + R ≤ K*D) (hR : A/3*Dc - (2*B/3)*(σ*D) - 2*A/3 ≤ R)
    (hB : 0 ≤ B) (hσ : σ ≤ 1) (hD : 0 ≤ D) (hedge : 2*A/3 ≤ err*D) :
    P + A/3*Dc ≤ (K+2*B/3+err)*D := by
  have h := mul_le_mul_of_nonneg_left (mul_le_of_le_one_left hD hσ)
    (show 0 ≤ 2*B/3 by positivity)
  linarith only [hP,hR,hedge,h]

end T052
end T052CapacitySource

section T052PaymentSource
/-
Apache-2.0 §4(b), 贝奕, 2026-11-23.
Variable payment on Devine's degree-32 Fourier intervals, based on Michael Devine's
verified Bernstein/Taylor checker and retained-pair argument. Upstream framework
by Kristian Muri Knausgård. The original public source and all notices are preserved.
-/
open scoped BigOperators
namespace T052
open Devine32Retained.FourierCertificate (coeff linearMul piApprox taylorValue errorBound fourierReal fourier_error)
namespace VariableFloor
def coefficients (n : ℕ) (lo hi sign e : ℚ) : List ℚ :=
  let cutoff := e + hi/100000000000000000000 + (piApprox*hi)^(n+2) / ((n+2).factorial : ℚ)
  let a := fun k => sign * coeff k - (if k = 0 then cutoff else 0)
  let start : List ℚ × List ℚ := ([a n], [1])
  let (xs, _) := (List.range n).reverse.foldl (fun state k =>
    let base := linearMul 1 1 state.2
    (List.zipWith (fun x y => x + a k * y) (linearMul lo hi state.1) base, base)) start
  xs

def positive (n : ℕ) (lo hi sign e : ℚ) : Bool :=
  (coefficients n lo hi sign e).all (fun c => decide (0 < c))

def heval (u v : ℝ) : List ℚ → ℝ
  | [] => 0
  | a::as => (a:ℝ)*u^as.length + v*heval u v as

private theorem map_eval (u v : ℝ) (k : ℚ) (xs : List ℚ) :
    heval u v (xs.map (k * ·)) = (k:ℝ)*heval u v xs := by
  induction xs with
  | nil => simp [heval]
  | cons a xs ih => simp [heval, ih]; ring

private theorem pad_eval (u v : ℝ) (xs : List ℚ) :
    heval u v (xs ++ [0]) = u * heval u v xs := by
  induction xs with
  | nil => simp [heval]
  | cons a xs ih => simp [heval, ih, pow_succ]; ring

private theorem zip_eval (u v : ℝ) (k : ℚ) (xs ys : List ℚ)
    (h : xs.length = ys.length) :
    heval u v (List.zipWith (fun a b => a+k*b) xs ys) =
    heval u v xs + (k:ℝ)*heval u v ys := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp_all [heval]
  | cons a xs ih =>
    cases ys with
    | nil => simp at h
    | cons b ys =>
      have h' : xs.length = ys.length := by simpa using h
      simp [heval, ih ys h', h']; ring

private theorem linear_len (l h : ℚ) (xs : List ℚ) :
    (linearMul l h xs).length = xs.length + 1 := by simp [linearMul]

private theorem linear_eval (u v : ℝ) (l h : ℚ) (xs : List ℚ) :
    heval u v (linearMul l h xs) = ((l:ℝ)*u+(h:ℝ)*v)*heval u v xs := by
  have eqn := zip_eval u v 1 ((xs.map (l * ·)) ++ [0]) (0 :: xs.map (h * ·)) (by simp)
  simp only [one_mul, Rat.cast_one] at eqn
  unfold linearMul
  rw [eqn, pad_eval, map_eval]
  simp [heval, map_eval]; ring

private theorem eval_nonneg (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (xs : List ℚ) (hp : ∀ x ∈ xs, 0 ≤ x) : 0 ≤ heval u v xs := by
  induction xs with
  | nil => simp [heval]
  | cons x xs ih =>
    have hx : (0:ℝ) ≤ x := by exact_mod_cast hp x (by simp)
    exact add_nonneg (mul_nonneg hx (pow_nonneg hu _))
      (mul_nonneg hv (ih fun y hy => hp y (by simp [hy])))


private def advance (l h : ℚ) (a : ℕ → ℚ) (state : List ℚ × List ℚ) (k : ℕ) :=
  let base := linearMul 1 1 state.2
  (List.zipWith (fun x y => x + a k * y) (linearMul l h state.1) base, base)

private theorem fold_eval (u v : ℝ) (uv : u+v=1) (l h : ℚ) (a : ℕ → ℚ)
    (ks : List ℕ) (state : List ℚ × List ℚ)
    (hlen : state.1.length = state.2.length) (hbase : heval u v state.2 = 1) :
    heval u v (ks.foldl (advance l h a) state).1 =
      ks.foldl (fun val k => ((l:ℝ)*u+(h:ℝ)*v)*val + (a k:ℝ)) (heval u v state.1) := by
  induction ks generalizing state with
  | nil => rfl
  | cons k ks ih =>
    have h1 : heval u v (linearMul 1 1 state.2) = 1 := by
      simp [linear_eval, hbase, uv]
    have hlen' : (linearMul l h state.1).length = (linearMul 1 1 state.2).length := by
      simp [linear_len, hlen]
    have h2 : (advance l h a state k).1.length = (advance l h a state k).2.length := by
      simp [advance, hlen']
    simp only [List.foldl_cons]
    rw [ih _ h2 h1]
    congr 1
    simp [advance, zip_eval _ _ _ _ _ hlen', linear_eval, hbase, uv]

private theorem horner_sum (x : ℝ) (a : ℕ → ℚ) (n : ℕ) (y : ℝ) :
    (List.range n).reverse.foldl (fun val k => x*val+(a k:ℝ)) y =
      x^n*y + ∑ k ∈ Finset.range n, x^k*(a k:ℝ) := by
  induction n generalizing y with
  | zero => simp
  | succ n ih =>
    simp [List.range_succ, ih, Finset.sum_range_succ, pow_succ]
    ring

theorem checked_interval {n : ℕ} {l h sign e : ℚ} (ok : positive n l h sign e = true)
    {x : ℝ} (lh : l < h) (xl : (l:ℝ) ≤ x) (xh : x ≤ (h:ℝ)) :
    (e:ℝ) + (errorBound n h:ℝ) ≤ (sign:ℝ) * taylorValue n x := by
  let u := ((h:ℝ)-x)/((h:ℝ)-l)
  let v := (x-(l:ℝ))/((h:ℝ)-l)
  have den : (0:ℝ) < (h:ℝ)-l := sub_pos.mpr (by exact_mod_cast lh)
  have hu : 0 ≤ u := div_nonneg (sub_nonneg.mpr xh) den.le
  have hv : 0 ≤ v := div_nonneg (sub_nonneg.mpr xl) den.le
  have uv : u+v=1 := by dsimp [u,v]; field_simp; ring
  have loc : (l:ℝ)*u+(h:ℝ)*v=x := by dsimp [u,v]; field_simp; ring
  let cut : ℚ := e + h/100000000000000000000 + (piApprox*h)^(n+2) / ((n+2).factorial : ℚ)
  let a := fun k => sign*coeff k - (if k=0 then cut else 0)
  let arr := coefficients n l h sign e
  have nonneg : 0 ≤ heval u v arr := eval_nonneg _ _ hu hv _ (by
    intro y hy
    exact le_of_lt (of_decide_eq_true (List.all_eq_true.mp ok y hy)))
  have ev := fold_eval u v uv l h a (List.range n).reverse ([a n],[1]) rfl (by simp [heval])
  change heval u v arr = _ at ev
  rw [ev, loc] at nonneg
  simp only [heval, List.length_nil, pow_zero, mul_one, mul_zero, add_zero] at nonneg
  rw [horner_sum] at nonneg
  have combined : 0 ≤ ∑ k ∈ Finset.range (n+1), x^k*(a k:ℝ) := by
    rw [Finset.sum_range_succ]; linarith
  simp only [a, Rat.cast_sub, Rat.cast_mul, apply_ite (fun q : ℚ => (q:ℝ)),
    Rat.cast_zero, mul_sub, Finset.sum_sub_distrib, mul_ite, mul_zero] at combined
  simp only [Finset.sum_ite_eq', Finset.mem_range, Nat.zero_lt_succ, if_true,
    pow_zero, one_mul] at combined
  dsimp [taylorValue]
  rw [Finset.mul_sum]
  simp only [mul_left_comm (sign:ℝ)]
  simpa [cut, errorBound, add_assoc] using (sub_nonneg.mp combined)


end VariableFloor

noncomputable section

def shift : ℝ := 318568213286260499659270516838072866311528290643861596159856943303569043463205981629841925918622079349921108093514259800707133127769361034665205538116532183015120777600071322106580534949274204507071453100423314666249323 / 312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
def cutoff : ℚ := 26087380561 / 25000000000
def span : ℝ := 59044015980121 / 19531250000000
def oldEta : ℝ := 308508742413987 / 12500000000000000
def head : ℝ := 9 / 100000
def slope : ℝ := 3 / 100000
def pay (e : ℝ) : ℝ := (1+e)*(1+e-shift)^2

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem close_cutoff : VariableFloor.positive 32 0 cutoff 1 (3/100) = true := by decide +kernel

theorem small_overlap {x : ℝ} (hx : 0 ≤ x) (ha : x ≤ (cutoff:ℝ)) :
    (3/100:ℝ) ≤ |fourierReal x| := by
  have hp := VariableFloor.checked_interval close_cutoff (x := x)
    (by norm_num [cutoff]) (by simpa using hx) ha
  simp only [Rat.cast_zero, Rat.cast_one, one_mul] at hp
  have he := fourier_error 32 (by decide) hx ha
  have he' := (abs_le.mp he).1
  apply le_trans _ (le_abs_self (fourierReal x))
  push_cast at hp
  linarith

theorem imbalance_select {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hd : x+y-|x-y| ≤ 2*(cutoff:ℝ)) :
    (3/100:ℝ) ≤ |fourierReal x| ∨ (3/100:ℝ) ≤ |fourierReal y| := by
  rcases le_total x y with h | h
  · rw [abs_of_nonpos (sub_nonpos.mpr h)] at hd
    exact Or.inl (small_overlap hx (by linarith))
  · rw [abs_of_nonneg (sub_nonneg.mpr h)] at hd
    exact Or.inr (small_overlap hy (by linarith))

def OldExceptional (x : ℝ) : Prop :=
  (5247238848358489/5000000000000000 < x ∧ x < 23/20) ∨ (9868029242552487/5000000000000000 < x ∧ x < 5247238848358489/2500000000000000) ∨ 11/4 < x

theorem old_gaps {x y : ℝ} (hz : x + y ≤ (59044015980121 / 19531250000000))
    (hx : OldExceptional x) (hy : OldExceptional y) : ¬ OldExceptional (x + y) := by
  rcases hx with ⟨h1,h2⟩ | ⟨h1,h2⟩ | h1 <;>
    rcases hy with ⟨k1,k2⟩ | ⟨k1,k2⟩ | k1 <;>
    rintro (⟨j1,j2⟩ | ⟨j1,j2⟩ | j1) <;> linarith

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem old_first_coefficients : VariableFloor.positive 28 (0 / 1) (5247238848358489 / 5000000000000000) (1) (308508742413987 / 12500000000000000) = true := by decide +kernel

theorem old_first_interval {x : ℝ} (hl : (0 / 1:ℝ) ≤ x) (hu : x ≤ (5247238848358489 / 5000000000000000:ℝ)) :
    oldEta + (errorBound 28 (5247238848358489 / 5000000000000000):ℝ) ≤ taylorValue 28 x := by
  have h := VariableFloor.checked_interval old_first_coefficients (x := x)
    (by norm_num) (by norm_num [Rat.cast_div, Rat.cast_ofNat, Rat.cast_zero] at hl ⊢; exact hl) (by norm_num [Rat.cast_div, Rat.cast_ofNat, Rat.cast_zero]; exact hu)
  norm_num [oldEta] at h ⊢
  exact h

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem old_second_coefficients : VariableFloor.positive 38 (23 / 20) (9868029242552487 / 5000000000000000) (-1) (308508742413987 / 12500000000000000) = true := by decide +kernel

theorem old_second_interval {x : ℝ} (hl : (23 / 20:ℝ) ≤ x) (hu : x ≤ (9868029242552487 / 5000000000000000:ℝ)) :
    oldEta + (errorBound 38 (9868029242552487 / 5000000000000000):ℝ) ≤ -taylorValue 38 x := by
  have h := VariableFloor.checked_interval old_second_coefficients (x := x)
    (by norm_num) (by norm_num [Rat.cast_div, Rat.cast_ofNat, Rat.cast_zero] at hl ⊢; exact hl) (by norm_num [Rat.cast_div, Rat.cast_ofNat, Rat.cast_zero]; exact hu)
  norm_num [oldEta] at h ⊢
  exact h

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem old_third_coefficients : VariableFloor.positive 44 (5247238848358489 / 2500000000000000) (11 / 4) (1) (308508742413987 / 12500000000000000) = true := by decide +kernel

theorem old_third_interval {x : ℝ} (hl : (5247238848358489 / 2500000000000000:ℝ) ≤ x) (hu : x ≤ (11 / 4:ℝ)) :
    oldEta + (errorBound 44 (11 / 4):ℝ) ≤ taylorValue 44 x := by
  have h := VariableFloor.checked_interval old_third_coefficients (x := x)
    (by norm_num) (by norm_num [Rat.cast_div, Rat.cast_ofNat, Rat.cast_zero] at hl ⊢; exact hl) (by norm_num [Rat.cast_div, Rat.cast_ofNat, Rat.cast_zero]; exact hu)
  norm_num [oldEta] at h ⊢
  exact h
theorem old_triple (F : ℝ → ℝ)
    (h₁ : ∀ x : ℝ, 0 ≤ x → x ≤ 5247238848358489/5000000000000000 →
      |F x - taylorValue 28 x| ≤ errorBound 28 (5247238848358489/5000000000000000))
    (h₂ : ∀ x : ℝ, 23/20 ≤ x → x ≤ 9868029242552487/5000000000000000 →
      |F x - taylorValue 38 x| ≤ errorBound 38 (9868029242552487/5000000000000000))
    (h₃ : ∀ x : ℝ, 5247238848358489/2500000000000000 ≤ x → x ≤ 11/4 →
      |F x - taylorValue 44 x| ≤ errorBound 44 (11/4))
    {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : x+y ≤ (59044015980121 / 19531250000000)) :
    oldEta ≤ |F x| ∨ oldEta ≤ |F y| ∨ oldEta ≤ |F (x+y)| := by
  have bad (s : ℝ) (hs : 0 ≤ s) (h : |F s| < oldEta) : OldExceptional s := by
    have low := (abs_lt.mp h).1
    have high := (abs_lt.mp h).2
    by_cases h0 : s ≤ 5247238848358489/5000000000000000
    · have ⟨hl,_⟩ := abs_le.mp (h₁ s hs h0)
      linarith [old_first_interval (by simpa using hs) h0]
    by_cases h1 : s < 23/20
    · exact Or.inl ⟨lt_of_not_ge h0,h1⟩
    by_cases h2 : s ≤ 9868029242552487/5000000000000000
    · have ⟨_,hu⟩ := abs_le.mp (h₂ s (le_of_not_gt h1) h2)
      linarith [old_second_interval (le_of_not_gt h1) h2]
    by_cases h3 : s < 5247238848358489/2500000000000000
    · exact Or.inr (Or.inl ⟨lt_of_not_ge h2,h3⟩)
    by_cases h4 : s ≤ 11/4
    · have ⟨hl,_⟩ := abs_le.mp (h₃ s (le_of_not_gt h3) h4)
      linarith [old_third_interval (le_of_not_gt h3) h4]
    exact Or.inr (Or.inr (lt_of_not_ge h4))
  by_contra! h
  exact old_gaps hz (bad x hx h.1) (bad y hy h.2.1)
    (bad (x+y) (add_nonneg hx hy) h.2.2)


theorem old_whole_band {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hs : x+y ≤ span) :
    oldEta ≤ |fourierReal x| ∨ oldEta ≤ |fourierReal y| ∨ oldEta ≤ |fourierReal (x+y)| := by
  apply old_triple _ _ _ _ hx hy (by simpa [span] using hs)
  · intro s hlo hhi
    exact fourier_error 28 (by decide) hlo (by norm_num [Rat.cast_div, Rat.cast_ofNat, Rat.cast_zero]; exact hhi)
  · intro s hlo hhi
    exact fourier_error 38 (by decide) (by linarith) (by norm_num [Rat.cast_div, Rat.cast_ofNat, Rat.cast_zero]; exact hhi)
  · intro s hlo hhi
    exact fourier_error 44 (by decide) (by linarith) (by norm_num [Rat.cast_div, Rat.cast_ofNat, Rat.cast_zero]; exact hhi)

theorem wide_gram : 0 ≤ oldEta ∧ shift ≤ 1+oldEta ∧ pay oldEta ≤ 4*(2-shift)*oldEta^2 := by
  norm_num [shift, oldEta, pay]

theorem short_gram : 0 ≤ (3/100:ℝ) ∧ shift ≤ 1+3/100 ∧
    pay (3/100) ≤ 4*(2-shift)*(3/100)^2 := by norm_num [shift, pay]

theorem ht1 : 1 ≤ shift := by norm_num [shift]
theorem ht2 : shift < 2 := by norm_num [shift]

theorem local_charge {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    head - slope*(x+y) ≤ 0 ∨
      ∃ e : ℝ, 0 ≤ e ∧ shift ≤ 1+e ∧ pay e ≤ 4*(2-shift)*e^2 ∧
        head - slope*(x+y) ≤ pay e ∧
          (e ≤ |fourierReal x| ∨ e ≤ |fourierReal y| ∨ e ≤ |fourierReal (x+y)|) := by
  have hB : 0 ≤ slope := by norm_num [slope]
  have short : head ≤ pay (3/100) := by norm_num [head, pay, shift]
  have middle : head - slope*(2*(cutoff:ℝ)) ≤ pay oldEta := by
    norm_num [head, slope, cutoff, pay, oldEta, shift]
  have hp : head ≤ slope*span := by norm_num [head, slope, span]
  by_cases hw : x+y ≤ span
  · right
    by_cases h : x+y-|x-y| ≤ 2*(cutoff:ℝ)
    · refine ⟨3/100,short_gram.1,short_gram.2.1,short_gram.2.2,?_,?_⟩
      · have z : 0 ≤ slope*(x+y) := mul_nonneg hB (add_nonneg hx hy)
        linarith
      · rcases imbalance_select hx hy h with h'|h'
        · exact Or.inl h'
        · exact Or.inr (Or.inl h')
    · refine ⟨oldEta,wide_gram.1,wide_gram.2.1,wide_gram.2.2,?_,old_whole_band hx hy hw⟩
      have hs : (2*(cutoff:ℝ)) ≤ x+y := by
        linarith [abs_nonneg (x-y)]
      have hmul := mul_le_mul_of_nonneg_left hs hB
      linarith
  · left
    have hs := mul_le_mul_of_nonneg_left (le_of_lt (not_le.mp hw)) hB
    linarith

end
end T052
end T052PaymentSource

section T052PackingSource
/- Apache-2.0 §4(b), 贝奕. Weighted version of Devine's residue-class packing. -/

open scoped BigOperators
namespace T052
open Devine32Retained.FourierCertificate (fourierReal)
noncomputable section

def CanPay (distance credit e : ℝ) : Prop :=
  credit ≤ 0 ∨ (0 ≤ e ∧ shift ≤ 1+e ∧ pay e ≤ 4*(2-shift)*e^2 ∧
    credit ≤ pay e ∧ e ≤ |fourierReal distance|)

theorem biggest_fiber (m : ℕ) (f : ℕ → ℝ) :
    ∃ r ∈ Finset.range 3,
      ∑ i ∈ Finset.range m, f i ≤
        3 * ∑ i ∈ (Finset.range m).filter (fun i => i%3=r), f i := by
  classical
  let fiber (r : ℕ) := (Finset.range m).filter (fun i => i%3=r)
  obtain ⟨r,hr,hm⟩ := (Finset.range 3).exists_max_image
    (fun r => ∑ i ∈ fiber r, f i) (by decide)
  have hs : ∑ i ∈ Finset.range m, f i = ∑ j ∈ Finset.range 3, ∑ i ∈ fiber j, f i := by
    symm
    exact Finset.sum_fiberwise_of_maps_to (fun i _ => Finset.mem_range.mpr (Nat.mod_lt i (by decide))) f
  refine ⟨r,hr,?_⟩
  rw [hs]
  simpa using Finset.sum_le_sum (s := Finset.range 3) (f := fun j => ∑ i ∈ fiber j, f i)
    (g := fun _ => ∑ i ∈ fiber r, f i) hm

theorem sum_spans (v : ℕ → ℝ) (m : ℕ) :
    ∑ i ∈ Finset.range m, (v (i+2) - v i) = v m + v (m+1) - v 0 - v 1 := by
  induction m with
  | zero => simp
  | succ m ih => rw [Finset.sum_range_succ, ih]; ring

theorem select_weighted (v : ℕ → ℝ) (m : ℕ) (hv : Monotone v) {L : ℝ}
    (hL : v (m+1) - v 0 ≤ L) :
    ∃ (s : Finset ℕ) (p q : ℕ → ℕ) (e r : ℕ → ℝ),
      head*(m:ℝ) - 2*slope*L ≤ 3*(∑ i ∈ s, r i) ∧
      (∀ i ∈ s, i ≤ p i ∧ p i < q i ∧ q i ≤ i+2 ∧ q i < m+2 ∧
        CanPay (v (q i)-v (p i)) (r i) (e i)) ∧
      ∀ i ∈ s, ∀ j ∈ s, i < j → q i < p j := by
  classical
  let r (i : ℕ) := head - slope * (v (i+2)-v i)
  have nc (i : ℕ) : ∃ a b e, i ≤ a ∧ a < b ∧ b ≤ i+2 ∧ CanPay (v b-v a) (r i) e := by
    have hx := sub_nonneg.mpr (hv (show i ≤ i+1 by omega))
    have hy := sub_nonneg.mpr (hv (show i+1 ≤ i+2 by omega))
    rcases local_charge hx hy with h | ⟨e,h₁,h₂,h₃,h₄,h₅⟩
    · have eq : v (i+1)-v i + (v (i+2)-v (i+1)) = v (i+2)-v i := by ring
      rw [eq] at h
      exact ⟨i,i+1,0,by omega,by omega,by omega,Or.inl h⟩
    · have eq : v (i+1)-v i + (v (i+2)-v (i+1)) = v (i+2)-v i := by ring
      rw [eq] at h₄ h₅
      rcases h₅ with h|h|h
      · exact ⟨i,i+1,e,by omega,by omega,by omega,Or.inr ⟨h₁,h₂,h₃,h₄,h⟩⟩
      · exact ⟨i+1,i+2,e,by omega,by omega,by omega,Or.inr ⟨h₁,h₂,h₃,h₄,h⟩⟩
      · exact ⟨i,i+2,e,by omega,by omega,by omega,Or.inr ⟨h₁,h₂,h₃,h₄,h⟩⟩
  choose p q e hp using nc
  obtain ⟨c,_,hc⟩ := biggest_fiber m r
  let s := (Finset.range m).filter (fun i => i % 3 = c)
  refine ⟨s,p,q,e,r,?_,?_,?_⟩
  · have hs : ∑ i ∈ Finset.range m, r i =
        head*(m:ℝ) - slope * ∑ i ∈ Finset.range m, (v (i+2)-v i) := by
      simp_rw [r]
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
      simp [nsmul_eq_mul,mul_comm]
    have hsum : ∑ i ∈ Finset.range m, (v (i+2)-v i) ≤ 2*L := by
      rw [sum_spans]
      linarith [hv (show m ≤ m+1 by omega), hv (show 0 ≤ 1 by decide)]
    have hm := mul_le_mul_of_nonneg_left hsum (show 0 ≤ slope by norm_num [slope])
    change ∑ i ∈ Finset.range m, r i ≤ 3*(∑ i ∈ s, r i) at hc
    linarith
  · intro i hi
    obtain ⟨ha,hb,hc,hd⟩ := hp i
    have him := Finset.mem_range.mp (Finset.mem_filter.mp hi).1
    exact ⟨ha,hb,hc,by omega,hd⟩
  · intro i hi j hj hij
    have heq := (Finset.mem_filter.mp hi).2.trans (Finset.mem_filter.mp hj).2.symm
    have hqi := (hp i).2.2.1
    have hpj := (hp j).1
    omega

theorem pack_window (S : Finset ℝ) {a b : ℝ} (hab : a ≤ b)
    (hS : ∀ x ∈ S, a ≤ x ∧ x ≤ b) :
    ∃ (s : Finset ℕ) (p q e r : ℕ → ℝ),
      head*((S.card:ℝ)-2) - 2*slope*(b-a) ≤ 3*(∑ i ∈ s, r i) ∧
      (∀ i ∈ s, p i ∈ S ∧ q i ∈ S ∧ p i < q i ∧ CanPay (q i-p i) (r i) (e i)) ∧
      ∀ i ∈ s, ∀ j ∈ s, i < j → q i < p j := by
  classical
  by_cases hsmall : S.card < 2
  · refine ⟨∅,fun _ => 0,fun _ => 0,fun _ => 0,fun _ => 0,?_,by simp,by simp⟩
    have h : (S.card:ℝ) ≤ 1 := by exact_mod_cast (show S.card ≤ 1 by omega)
    have hA : 0 ≤ head := by norm_num [head]
    have hB : 0 ≤ slope := by norm_num [slope]
    have ha := mul_nonpos_of_nonneg_of_nonpos hA (show (S.card:ℝ)-2 ≤ 0 by linarith)
    have hb := mul_nonneg hB (sub_nonneg.mpr hab)
    simp only [Finset.sum_empty,mul_zero]
    linarith
  let m := S.card - 2
  have hm : S.card = m+2 := by dsimp [m]; omega
  let index (i : ℕ) : Fin (m+2) := ⟨min i (m+1),by omega⟩
  let v (i : ℕ) := S.orderEmbOfFin hm (index i)
  have mem (i : ℕ) : v i ∈ S := S.orderEmbOfFin_mem hm _
  have mono : Monotone v := fun i j hij =>
    (S.orderEmbOfFin hm).monotone (show min i (m+1) ≤ min j (m+1) from min_le_min_right _ hij)
  have strict {i j : ℕ} (hij : i < j) (hj : j < m+2) : v i < v j := by
    apply (S.orderEmbOfFin hm).strictMono
    change min i (m+1) < min j (m+1)
    omega
  obtain ⟨s,p,q,e,r,hc,hpq,hd⟩ := select_weighted v m mono
    (L := b-a) (by linarith [(hS _ (mem 0)).1, (hS _ (mem (m+1))).2])
  refine ⟨s,v ∘ p,v ∘ q,e,r,?_,?_,?_⟩
  · rw [hm, Nat.cast_add, Nat.cast_ofNat, add_sub_cancel_right]
    exact hc
  · intro i hi
    obtain ⟨_,hp,_,hq,he⟩ := hpq i hi
    exact ⟨mem _,mem _,strict hp hq,he⟩
  · intro i hi j hj hij
    obtain ⟨_,hp,_,hq,_⟩ := hpq j hj
    exact strict (hd i hi j hj hij) (hp.trans hq)

end
end T052
end T052PackingSource

section T052GramSource
/-
Apache-2.0 §4(b), 贝奕, 2026-11-23.
Variable retained-pair weights for Michael Devine's fixed degree-32 proof.
Pair, Fourier, and moment framework by Michael Devine and Kristian Muri Knausgård.
-/
open Matrix TMG TMG.PairGain
open scoped ComplexOrder BigOperators
namespace T052
noncomputable section

theorem zero_payments (hRH : RiemannHypothesis) {T k : ℝ} (hT : 0 ≤ T) (hk : 0 < k) :
    ∃ (s : Finset ℕ) (p q : ℕ → ℂ) (e r : ℕ → ℝ),
      head*((Zeta23.Ndist T (2*T):ℝ)-2) - 2*slope*(k*T) ≤ 3*(∑ i ∈ s,r i) ∧
      (∀ i ∈ s, p i ∈ Zeta23.zerosIn T (2*T) ∧ q i ∈ Zeta23.zerosIn T (2*T) ∧
        (p i).im < (q i).im ∧ CanPay (k*((q i).im-(p i).im)) (r i) (e i)) ∧
      ∀ i ∈ s, ∀ j ∈ s, i < j → (q i).im < (p j).im := by
  classical
  let Z := (Zeta23.zerosIn_finite T (2*T)).toFinset
  let S := Z.image (fun ρ : ℂ => k*ρ.im)
  have zm {ρ : ℂ} : ρ ∈ Z ↔ ρ ∈ Zeta23.zerosIn T (2*T) := Set.Finite.mem_toFinset _
  have inj : Set.InjOn (fun ρ : ℂ => k*ρ.im) Z := by
    intro ρ hr τ ht he
    exact Complex.ext ((Zeta23.RH_implies_on_line hRH (zm.mp hr).1).trans
      (Zeta23.RH_implies_on_line hRH (zm.mp ht).1).symm) (mul_left_cancel₀ hk.ne' he)
  have card : S.card = Zeta23.Ndist T (2*T) := by
    rw [show S.card = Z.card from Finset.card_image_of_injOn inj]
    exact (Set.ncard_eq_toFinset_card _ (Zeta23.zerosIn_finite T (2*T))).symm
  have bounds : ∀ u ∈ S, k*T ≤ u ∧ u ≤ k*(2*T) := by
    intro u hu
    obtain ⟨ρ,hm,rfl⟩ := Finset.mem_image.mp hu
    exact ⟨mul_le_mul_of_nonneg_left (zm.mp hm).2.1.le hk.le,
      mul_le_mul_of_nonneg_left (zm.mp hm).2.2 hk.le⟩
  obtain ⟨s,P,Q,e,r,hc,hpq,hd⟩ := pack_window S (by nlinarith : k*T ≤ k*(2*T)) bounds
  let z (u : ℝ) : ℂ := ⟨1/2,u/k⟩
  have lift {u : ℝ} (hu : u ∈ S) : z u ∈ Zeta23.zerosIn T (2*T) := by
    obtain ⟨ρ,hm,rfl⟩ := Finset.mem_image.mp hu
    have he : z (k*ρ.im) = ρ := by
      apply Complex.ext
      · exact (Zeta23.RH_implies_on_line hRH (zm.mp hm).1).symm
      · change k*ρ.im/k = ρ.im; field_simp
    rw [he]; exact zm.mp hm
  refine ⟨s,z ∘ P,z ∘ Q,e,r,?_,?_,?_⟩
  · rw [card, show k*(2*T)-k*T = k*T by ring] at hc
    exact hc
  · intro i hi
    obtain ⟨hp,hq,hlt,he⟩ := hpq i hi
    refine ⟨lift hp,lift hq,div_lt_div_of_pos_right hlt hk,?_⟩
    change CanPay (k*(Q i/k-P i/k)) (r i) (e i)
    rwa [show k*(Q i/k-P i/k) = Q i-P i by field_simp]
  · intro i hi j hj hij
    exact div_lt_div_of_pos_right (hd i hi j hj hij) hk

section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
theorem sum_variable_pay {κ : Type*} (f b : ι → ℝ) (Z : Finset ι) (hf0 : ∀ a, 0 ≤ f a)
    (hfb : ∀ a ∈ Z, b a ≤ f a) (s : Finset κ) (p q : κ → ι)
    (hpZ : ∀ k ∈ s, p k ∈ Z) (hqZ : ∀ k ∈ s, q k ∈ Z)
    (hp : Set.InjOn p s) (hq : Set.InjOn q s) (hpq : ∀ k ∈ s, ∀ l ∈ s, p k ≠ q l) (g : κ → ℝ)
    (hgain : ∀ k ∈ s, b (p k) + b (q k) + g k ≤ f (p k) + f (q k)) :
    ∑ a ∈ Z, b a + (∑ k ∈ s, g k) ≤ ∑ a, f a := by
  have hdisj : Disjoint (s.image p) (s.image q) := by
    rw [Finset.disjoint_left]
    intro a ha hb
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨l, hl, hl'⟩ := Finset.mem_image.mp hb
    exact hpq k hk l hl hl'.symm
  have hU : s.image p ∪ s.image q ⊆ Z := by
    intro a ha
    rcases Finset.mem_union.mp ha with h | h
    · obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp h
      exact hpZ k hk
    · obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp h
      exact hqZ k hk
  have h1 : ∑ a ∈ s.image p ∪ s.image q, (f a - b a) ≤ ∑ a ∈ Z, (f a - b a) :=
    Finset.sum_le_sum_of_subset_of_nonneg hU (fun a ha _ => sub_nonneg.mpr (hfb a ha))
  rw [Finset.sum_union hdisj, Finset.sum_image hp, Finset.sum_image hq] at h1
  have h2 : ∑ k ∈ s, g k ≤ ∑ k ∈ s, ((f (p k) - b (p k)) + (f (q k) - b (q k))) :=
    Finset.sum_le_sum fun k hk => by linarith [hgain k hk]
  rw [Finset.sum_add_distrib] at h2
  have h3 : ∑ a ∈ Z, (f a - b a) = ∑ a ∈ Z, f a - ∑ a ∈ Z, b a := by
    rw [Finset.sum_sub_distrib]
  have h4 : ∑ a ∈ Z, f a ≤ ∑ a, f a :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ Z) (fun a _ _ => hf0 a)
  linarith

end
section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
theorem trace_variable_pay {A : Matrix ι ι ℂ} (hA : A.PosSemidef) {t : ℝ} (ht : 0 ≤ t)
    (b : ι → ℝ) (Z : Finset ι) (hb : ∀ a ∈ Z, b a ≤ ThirdMoment.phi t (A a a).re)
    {κ : Type*} (s : Finset κ) (p q : κ → ι) (hpZ : ∀ k ∈ s, p k ∈ Z) (hqZ : ∀ k ∈ s, q k ∈ Z)
    (hp : Set.InjOn p s) (hq : Set.InjOn q s) (hpq : ∀ k ∈ s, ∀ l ∈ s, p k ≠ q l) (g : κ → ℝ)
    (hgain : ∀ k ∈ s, b (p k) + b (q k) + g k ≤
      ((cubeP A t) (p k) (p k)).re + ((cubeP A t) (q k) (q k)).re) :
    ∑ a ∈ Z, b a + (∑ k ∈ s, g k)
      ≤ (Matrix.trace (A ^ 3) - 2 * t * Matrix.trace (A ^ 2) + t ^ 2 * Matrix.trace A).re := by
  rw [← sum_re_cubeP A t]
  have hd : ∀ a, ThirdMoment.phi t (A a a).re ≤ ((cubeP A t) a a).re :=
    fun a => ThirdMoment.phi_diag_le hA ht a
  exact sum_variable_pay (fun a => ((cubeP A t) a a).re) b Z
    (fun a => le_trans (ThirdMoment.phi_nonneg (ThirdMoment.re_diag_nonneg hA a)) (hd a))
    (fun a ha => le_trans (hb a ha) (hd a)) s p q hpZ hqZ hp hq hpq g hgain

end
theorem phi_weighted_fin (hRH : RiemannHypothesis) (w : TMA.HeightWeight) {T σ : ℝ}
    (hT : 1 < T) (hσ : 0 < σ) :
    ∃ R : ℝ,
      head*((Zeta23.Ndist T (2 * T) : ℝ)-2) - 2*slope*(σ * Real.log T / (2 * Real.pi) * T) ≤ 3*R ∧
      ∀ S : Finset ℂ, ThirdMoment.zerosFinset T (2 * T) ⊆ S →
        ThirdMoment.phiSum shift T (2 * T) + R
          ≤ (t3 DevineDegree32.W (TMA.Kfin w.h T σ S)).re -
            2 * shift * t2 DevineDegree32.W (TMA.Kfin w.h T σ S) +
            shift ^ 2 * (TMA.Kfin w.h T σ S 0).re := by
  classical
  have hT0 : (0 : ℝ) ≤ T := by linarith
  have hTpos : (0 : ℝ) < T := by linarith
  have ht0 : (0 : ℝ) ≤ shift := by linarith [ht1]
  have hk : 0 < σ * Real.log T / (2 * Real.pi) :=
    div_pos (mul_pos hσ (Real.log_pos hT)) (by positivity)
  obtain ⟨s, p, q, e, r, hcard, hpq, hdis⟩ := zero_payments hRH hT0 hk
  let R := ∑ i ∈ s, r i
  refine ⟨R, hcard, fun S hS => ?_⟩
  obtain ⟨hinjp, hinjq, hne⟩ := TMG.Devine32Gain.pairs_ordered (s := s) (p := p) (q := q)
    (fun i hi => (hpq i hi).2.2.1) hdis
  have hc : ∀ a : S, 0 ≤ TMA.cw w.h T a := fun a => TMA.cw_nonneg w T a
  obtain ⟨A, hAdef⟩ : ∃ A : Matrix S S ℂ, A = Gram.gramW DevineDegree32.W (fun a : S => TMA.cw w.h T a)
      (fun a : S => σ * Real.log T * (a : ℂ).im) := ⟨_, rfl⟩
  have hA : A.PosSemidef := by
    rw [hAdef]
    exact Gram.gramW_posSemidef _ _ _
  have hdiag : ∀ a : S, (A a a).re = TMA.cw w.h T a := by
    intro a
    rw [hAdef, Gram.gramW_diag DevineDegree32.W _ _ hc a, Complex.ofReal_re]
  have hoffd : ∀ a b : S, (A a b).re = Real.sqrt (TMA.cw w.h T a) * Real.sqrt (TMA.cw w.h T b) *
      (ghat DevineDegree32.W (σ * Real.log T * (a : ℂ).im - σ * Real.log T * (b : ℂ).im)).re := by
    intro a b
    rw [hAdef]
    simp only [Gram.gramW, Matrix.of_apply]
    rw [← Complex.ofReal_mul, Complex.re_ofReal_mul]
  have hker : ∀ u v : ℝ, (ghat DevineDegree32.W (σ * Real.log T * u - σ * Real.log T * v)).re
      = Devine32Retained.FourierCertificate.fourierReal
          (σ * Real.log T / (2 * Real.pi) * (u - v)) := by
    intro u v
    have hπ : (2 * Real.pi) ≠ 0 := by positivity
    have e : 2 * Real.pi * (σ * Real.log T / (2 * Real.pi) * (u - v))
        = σ * Real.log T * u - σ * Real.log T * v := by
      first
        | (rw [div_mul_eq_mul_div, mul_div_assoc', mul_div_cancel_left₀ _ hπ]; ring)
        | (field_simp; done)
        | (field_simp; ring)
    rw [← e, Devine32Link.kernel_re]
  -- the window as a finset of indices
  obtain ⟨Zs, hsumZ, hZ1, hZ2⟩ : ∃ Zs : Finset S,
      ∑ a ∈ Zs, ThirdMoment.phi shift (Zeta23.zeroMult (a : ℂ)) = ThirdMoment.phiSum shift T (2 * T) ∧
      (∀ a ∈ Zs, (a : ℂ) ∈ ThirdMoment.zerosFinset T (2 * T)) ∧
      (∀ a : S, (a : ℂ) ∈ ThirdMoment.zerosFinset T (2 * T) → a ∈ Zs) := by
    let embed : ↥(ThirdMoment.zerosFinset T (2*T)) ↪ ↥S :=
      ⟨fun ρ => ⟨ρ.1,hS ρ.2⟩,fun _ _ h => Subtype.ext (congrArg (fun z : S => (z : ℂ)) h)⟩
    refine ⟨(ThirdMoment.zerosFinset T (2*T)).attach.map embed, ?_, ?_, ?_⟩
    · rw [Finset.sum_map, ThirdMoment.phiSum_eq]
      exact Finset.sum_attach (ThirdMoment.zerosFinset T (2 * T))
        (fun ρ => ThirdMoment.phi shift (Zeta23.zeroMult ρ))
    · intro a ha
      obtain ⟨ρ, -, rfl⟩ := Finset.mem_map.mp ha
      exact ρ.2
    · intro a ha
      exact Finset.mem_map.mpr ⟨⟨a.1, ha⟩, Finset.mem_attach _ _, rfl⟩
  -- the selected pairs as indices
  obtain ⟨P, hP⟩ : ∃ P : s → S, ∀ k, (P k : ℂ) = p k.1 :=
    ⟨fun k => ⟨p k.1, hS (ThirdMoment.mem_zerosFinset.mpr (hpq k.1 k.2).1)⟩, fun k => rfl⟩
  obtain ⟨Q, hQ⟩ : ∃ Q : s → S, ∀ k, (Q k : ℂ) = q k.1 :=
    ⟨fun k => ⟨q k.1, hS (ThirdMoment.mem_zerosFinset.mpr (hpq k.1 k.2).2.1)⟩, fun k => rfl⟩
  have hPm : ∀ k : s, (P k : ℂ) ∈ ThirdMoment.zerosFinset T (2 * T) := fun k => by
    rw [hP]
    exact ThirdMoment.mem_zerosFinset.mpr (hpq k.1 k.2).1
  have hQm : ∀ k : s, (Q k : ℂ) ∈ ThirdMoment.zerosFinset T (2 * T) := fun k => by
    rw [hQ]
    exact ThirdMoment.mem_zerosFinset.mpr (hpq k.1 k.2).2.1
  have hPinj : Set.InjOn P (Finset.univ : Finset s) := by
    intro i _ j _ h
    apply Subtype.ext
    have h' := congrArg Subtype.val h
    rw [hP, hP] at h'
    exact hinjp i.1 i.2 j.1 j.2 h'
  have hQinj : Set.InjOn Q (Finset.univ : Finset s) := by
    intro i _ j _ h
    apply Subtype.ext
    have h' := congrArg Subtype.val h
    rw [hQ, hQ] at h'
    exact hinjq i.1 i.2 j.1 j.2 h'
  have hPQ : ∀ k ∈ (Finset.univ : Finset s), ∀ l ∈ (Finset.univ : Finset s), P k ≠ Q l := by
    intro k _ l _ h
    have h' := congrArg Subtype.val h
    rw [hP, hQ] at h'
    exact hne k.1 k.2 l.1 l.2 h'
  have hgain : ∀ k ∈ (Finset.univ : Finset s),
      ThirdMoment.phi shift (Zeta23.zeroMult (P k : ℂ)) +
        ThirdMoment.phi shift (Zeta23.zeroMult (Q k : ℂ)) + r k.val
      ≤ ((cubeP A shift) (P k) (P k)).re + ((cubeP A shift) (Q k) (Q k)).re := by
    intro k _
    have hMp : (Zeta23.zeroMult (P k : ℂ) : ℝ) ≤ (A (P k) (P k)).re := by
      rw [hdiag]
      exact Gram.zeroMult_le_cw w hTpos (ThirdMoment.mem_zerosFinset.mp (hPm k))
    have hMq : (Zeta23.zeroMult (Q k : ℂ) : ℝ) ≤ (A (Q k) (Q k)).re := by
      rw [hdiag]
      exact Gram.zeroMult_le_cw w hTpos (ThirdMoment.mem_zerosFinset.mp (hQm k))
    rcases (hpq k.1 k.2).2.2.2 with h | ⟨he0,he1,he2,hcredit,hF⟩
    · have h1 := le_trans (ThirdMoment.phi_mono ht0 (Nat.cast_nonneg _) hMp)
          (ThirdMoment.phi_diag_le hA ht0 (P k))
      have h2 := le_trans (ThirdMoment.phi_mono ht0 (Nat.cast_nonneg _) hMq)
          (ThirdMoment.phi_diag_le hA ht0 (Q k))
      linarith
    · have hdiff : P k ≠ Q k := by
        intro eq
        have h' := congrArg Subtype.val eq
        rw [hP, hQ] at h'
        exact hne k.1 k.2 k.1 k.2 h'
      refine le_trans (by unfold pay at hcredit; linarith) (pair_gain hA ht1 ht2 he0 he1 (by simpa [pay] using he2) hdiff
        (ThirdMoment.one_le_mult_of_mem (hPm k)) (ThirdMoment.one_le_mult_of_mem (hQm k)) hMp hMq ?_)
      rw [hdiag, hdiag, hoffd, hker, hQ, hP]
      have hcp := TMA.cw_nonneg w T (p k.1)
      have hcq := TMA.cw_nonneg w T (q k.1)
      rw [mul_pow, mul_pow, Real.sq_sqrt hcq, Real.sq_sqrt hcp]
      have hF2 : (e k.1) ^ 2 ≤
          (Devine32Retained.FourierCertificate.fourierReal
            (σ * Real.log T / (2 * Real.pi) * ((q k.1).im - (p k.1).im))) ^ 2 := by
        rw [sq_le_sq, abs_of_nonneg he0]
        exact hF
      have hmul := mul_le_mul_of_nonneg_right hF2 (mul_nonneg hcp hcq)
      linarith
  -- assemble with the leader's trace identities
  have key := trace_variable_pay hA ht0 (fun a : S => ThirdMoment.phi shift (Zeta23.zeroMult (a : ℂ))) Zs
    (fun a ha => by
      rw [hdiag]
      exact ThirdMoment.phi_mono ht0 (Nat.cast_nonneg _)
        (Gram.zeroMult_le_cw w hTpos (ThirdMoment.mem_zerosFinset.mp (hZ1 a ha))))
    (Finset.univ : Finset s) P Q (fun k _ => hZ2 _ (hPm k)) (fun k _ => hZ2 _ (hQm k))
    hPinj hQinj hPQ (fun j : s => r j.1) hgain
  have hsr : (∑ j : s, r j.val) = R := Finset.sum_attach s r
  rw [hsumZ, hsr, hAdef] at key
  rw [Gram.trace_gramW_cube DevineDegree32.W _ _ hc, Gram.trace_gramW_sq DevineDegree32.W _ _ hc, Gram.trace_gramW DevineDegree32.W _ _ hc,
    ← Gram.Kfin_eq_trigK] at key
  have hre : (t3 DevineDegree32.W (TMA.Kfin w.h T σ S) - 2 * (shift : ℂ) * ((t2 DevineDegree32.W (TMA.Kfin w.h T σ S) : ℝ) : ℂ)
        + (shift : ℂ) ^ 2 * TMA.Kfin w.h T σ S 0).re
      = (t3 DevineDegree32.W (TMA.Kfin w.h T σ S)).re - 2 * shift * t2 DevineDegree32.W (TMA.Kfin w.h T σ S)
          + shift ^ 2 * (TMA.Kfin w.h T σ S 0).re := by
    have e1 : 2 * (shift : ℂ) * ((t2 DevineDegree32.W (TMA.Kfin w.h T σ S) : ℝ) : ℂ)
        = ((2 * shift * t2 DevineDegree32.W (TMA.Kfin w.h T σ S) : ℝ) : ℂ) := by
      push_cast
      ring
    have e2 : (shift : ℂ) ^ 2 = ((shift ^ 2 : ℝ) : ℂ) := by
      push_cast
      ring
    rw [e1, e2, Complex.add_re, Complex.sub_re, Complex.ofReal_re, Complex.re_ofReal_mul]
  rw [hre] at key
  exact key


theorem phi_weighted_full (hRH : RiemannHypothesis) (w : TMA.HeightWeight) {T σ : ℝ}
    (hT : 1 < T) (hσ : 0 < σ) :
    ∃ R : ℝ,
      head*((Zeta23.Ndist T (2 * T) : ℝ)-2) - 2*slope*(σ * Real.log T / (2 * Real.pi) * T) ≤ 3*R ∧
      ThirdMoment.phiSum shift T (2 * T) + R
        ≤ (t3 DevineDegree32.W (TMA.Kfull w.h T σ)).re -
          2 * shift * t2 DevineDegree32.W (TMA.Kfull w.h T σ) +
          shift ^ 2 * (TMA.Kfull w.h T σ 0).re := by
  obtain ⟨R, hR, hp⟩ := phi_weighted_fin hRH w hT hσ
  exact ⟨R, hR, le_Xi_of_le_Kfin hRH DevineDegree32.W w (by linarith) hp⟩

end
end T052
end T052GramSource

section T052CountSource
/-
Apache-2.0 §4(b), 贝奕. Lift the variable credit into Devine's RH count proof.
The exact window and analytic trace theorems are reused with their original credits.
-/
open TMG TMG.Devine32Gain TMG.MainAux
open scoped BigOperators
namespace T052
noncomputable section

theorem budget_sigma (hRH : RiemannHypothesis) {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ < 1) :
    PairBudget shift (C3 DevineDegree32.W σ - 2*shift*C2 DevineDegree32.W σ + shift^2 + 2*slope/3) (head/3) := by
  intro ε hε
  have ht : 0 ≤ shift := by linarith [ht1]
  have ha0 : 0 ≤ head := by norm_num [head]
  have hb0 : 0 ≤ slope := by norm_num [slope]
  have hC3 : 0 ≤ C3 DevineDegree32.W σ := C3_nonneg DevineDegree32.W σ
  have hC2 : 0 ≤ C2 DevineDegree32.W σ := C2_nonneg DevineDegree32.W hσ
  have hε2 : 0 < ε / 2 := by linarith
  obtain ⟨ε1, hε1pos, hε1le⟩ := exists_small_mul hε2 (add_nonneg hC3 (sq_nonneg shift))
  obtain ⟨δ, hδpos, hδle⟩ := exists_small_mul hε2 (sq_nonneg (1 + shift))
  obtain ⟨θ, hθpos, hθK⟩ : ∃ θ : ℝ, 0 < θ ∧
      θ * (|C3 DevineDegree32.W σ - 2 * shift * C2 DevineDegree32.W σ + shift ^ 2 + 2*slope/3| + ε)
        ≤ ε / 2 := by
    have hden : 0 < |C3 DevineDegree32.W σ - 2 * shift * C2 DevineDegree32.W σ + shift ^ 2 + 2*slope/3|
        + ε := by positivity
    refine ⟨ε / (2 * (|C3 DevineDegree32.W σ - 2 * shift * C2 DevineDegree32.W σ + shift ^ 2
      + 2*slope/3| + ε)), by positivity, le_of_eq ?_⟩
    field_simp
  obtain ⟨w, hw1, hw3⟩ := TMA.exists_heightWeight hε1pos
  obtain ⟨Ta, ha⟩ := TMA.t1_upper hRH w hσ hσ1 δ hδpos
  obtain ⟨Tb, hb⟩ := t2_lower hRH DevineDegree32.W w hσ hσ1 δ hδpos
  obtain ⟨Tc, hc⟩ := t3_upper hRH DevineDegree32.W w hσ hσ1 δ hδpos
  obtain ⟨Td, hd⟩ := rvm_Dsc_le hθpos
  obtain ⟨Te, he⟩ := Dsc_large (a := 2*head/3) (b := ε / 4)
    (by linarith)
  refine ⟨max Ta (max Tb (max Tc (max Td (max Te 2)))), fun T hT => ?_⟩
  simp only [ge_iff_le, max_le_iff] at hT
  obtain ⟨hTa, hTb, hTc, hTd, hTe, hT2⟩ := hT
  obtain ⟨hTpos, hDpos, hDN⟩ := hd T hTd

  obtain ⟨R, hR, hXi⟩ := phi_weighted_full hRH w (by linarith : (1 : ℝ) < T) hσ
  have hP := assemble_real hXi (hc T hTc) (hb T hTb) (ha T hTa) hDpos.le ht hC3 hC2 hw1 hw3
    w.one_le_kap2
  have hσD : σ * Real.log T / (2 * Real.pi) * T = σ * TMA.Dsc T := by
    unfold TMA.Dsc
    ring
  rw [hσD] at hR
  have hrr : head/3 * (Zeta23.Ndist T (2*T):ℝ) - (2*slope/3)*(σ*TMA.Dsc T) - 2*head/3 ≤ R := by
    linarith
  have hA := charge_assemble hP hrr hb0 hσ1.le hDpos.le (he T hTe)
  have hP0 : 0 ≤ ThirdMoment.phiSum shift T (2 * T) + head/3*(Zeta23.Ndist T (2 * T) : ℝ) :=
    add_nonneg (phiSum_nonneg shift T (2 * T))
      (mul_nonneg (div_nonneg ha0 (by norm_num)) (Nat.cast_nonneg _))
  have hA' : ThirdMoment.phiSum shift T (2*T) + head/3*(Zeta23.Ndist T (2*T):ℝ) ≤
      (C3 DevineDegree32.W σ - 2*shift*C2 DevineDegree32.W σ + shift^2 + 2*slope/3 + ε/2) * TMA.Dsc T := by
    have h1 := mul_le_mul_of_nonneg_right hε1le hDpos.le
    have h2 := mul_le_mul_of_nonneg_right hδle hDpos.le
    linarith only [hA,h1,h2]
  exact final_real hP0 hA' hDpos hDN hθpos.le (by linarith) hθK hε (Nat.cast_nonneg _)

theorem budget_dyadic (hRH : RiemannHypothesis) :
    PairBudget shift (Kt DevineDegree32.W shift + 2*slope/3) (head/3) := by
  unfold Kt
  intro ε hε
  have ht : 0 ≤ shift := by linarith [ht1]
  have hM : 0 ≤ 8 * I3 DevineDegree32.W + 2 * shift * J2 DevineDegree32.W := by
    have h1 := mul_nonneg ht (J2_nonneg DevineDegree32.W)
    have h2 := I3_nonneg DevineDegree32.W
    linarith
  obtain ⟨s, hs0, hs1, hsM⟩ :
      ∃ s : ℝ, 0 < s ∧ s ≤ 1 / 2 ∧ (8 * I3 DevineDegree32.W + 2 * shift * J2 DevineDegree32.W) * s ≤ ε / 2 := by
    obtain ⟨x, hx0, hxM⟩ := exists_small_mul hε hM
    refine ⟨min x (1 / 2), lt_min hx0 (by norm_num), min_le_right _ _, ?_⟩
    have h1 : (8 * I3 DevineDegree32.W + 2 * shift * J2 DevineDegree32.W) * min x (1 / 2) ≤ (8 * I3 DevineDegree32.W + 2 * shift * J2 DevineDegree32.W) * x :=
      mul_le_mul_of_nonneg_left (min_le_left _ _) hM
    linarith
  have hσ : (1 : ℝ) / 2 ≤ 1 - s := by linarith
  have hσ1 : 1 - s < 1 := by linarith
  have hK := const_le_one DevineDegree32.W hσ hσ1 ht
  rw [sub_sub_cancel] at hK
  obtain ⟨T₀, h₀⟩ :=
    budget_sigma hRH (by linarith : (0 : ℝ) < 1 - s) hσ1 (ε / 2)
      (by linarith)
  refine ⟨T₀, fun T hT => ?_⟩
  have hN : (0 : ℝ) ≤ (Zeta23.Ncount T (2 * T) : ℝ) := Nat.cast_nonneg _
  have h1 := h₀ T hT
  have h2 : (C3 DevineDegree32.W (1 - s) - 2 * shift * C2 DevineDegree32.W (1 - s) + shift ^ 2
        + 2*slope/3 + ε / 2) * (Zeta23.Ncount T (2 * T) : ℝ)
      ≤ (C3 DevineDegree32.W 1 - 2 * shift * C2 DevineDegree32.W 1 + shift ^ 2 + 2*slope/3 + ε)
        * (Zeta23.Ncount T (2 * T) : ℝ) :=
    mul_le_mul_of_nonneg_right (by linarith) hN
  exact le_trans h1 h2


def record : ℝ := 8427815160217 / 10000000000000
def published : ℝ := 7467259030701813869739730211166225298027652489304375443581010163149153437228159306762267726029670194888697704273164057355823112360018062855667878677027709276696065953004943987720266315230953455410883 / 8860274382827684373426110524043993283228053047698953524152136784089094997182778051879727134858536985101946476314074081005564061157704101990052816823160393668320260609150049071187435095675724245271026

theorem exact_envelope_ratio :
    (2*(2-shift)^2 - (Kt DevineDegree32.W shift+2*slope/3)) /
      (2*(2-shift)^2-head/3) = 2298922484834904153295876896242149475393634087020928016663119904189717739558980556480194141810696186412360069933169364334592806571763025197312097199232926350394446600891979768743477357789529884597337893888391519492792410520600282727463126756991354766193592711366357980325886564052764235152267564299175313336065284446312719670427355981548388477316492859188452903526436250778705727479329812879273835802223912412049226756468647170861513988443328177324287891026878295925792684289 / 2727779906335415033376271004328846014426440650000301529737373925616033488109125612466423387993685680416898042997782093496727825646286092873114671553507997365682183710414169137899521413568221019581160517043361631013100599316751049656613366009032157786124017692621855362174360646893352821825135128598350626672130568892625439340854711963096776954632985718376905807052872501557411454958659625758547671604447824824098453512937294341723027976886656354648575782053756591851585368578 := by
  unfold Kt
  rw [DevineDegree32.C2_exact, DevineDegree32.C3_exact]
  norm_num [head, slope, shift]

theorem live_advantage : published < record := by norm_num [published, record]

theorem ratio_gt_record : record <
    (2*(2-shift)^2 - (Kt DevineDegree32.W shift+2*slope/3)) /
      (2*(2-shift)^2-head/3) := by
  rw [exact_envelope_ratio]
  norm_num [record]

theorem critical_dyadic (hRH : RiemannHypothesis) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (record-ε) * (Zeta23.Ncount T (2*T):ℝ) ≤ Zeta23.N0star T (2*T) := by
  intro ε hε
  have hd : head/3 < 2*(2-shift)^2 := by norm_num [head, shift]
  obtain ⟨T₀, h⟩ := distinct_of_pairBudget ht1 ht2 hd (budget_dyadic hRH) ε hε
  refine ⟨T₀, fun T hT => ?_⟩
  rw [(Zeta23.RH_implies_all_on_line hRH T (2*T)).2]
  exact le_trans (mul_le_mul_of_nonneg_right (by linarith [ratio_gt_record]) (Nat.cast_nonneg _)) (h T hT)

theorem critical_cumulative (hRH : RiemannHypothesis) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (record-ε) * (Zeta23.Ncount 0 T:ℝ) ≤ Zeta23.N0star 0 T := by
  intro ε hε
  have hc : 0 ≤ head/3 := by norm_num [head]
  have hd : head/3 < 2*(2-shift)^2 := by norm_num [head, shift]
  obtain ⟨T₀, h⟩ := distinct_cumulative_of_pairBudget ht1 ht2 hc hd (budget_dyadic hRH) ε hε
  refine ⟨T₀, fun T hT => ?_⟩
  rw [(Zeta23.RH_implies_all_on_line hRH 0 T).2]
  exact le_trans (mul_le_mul_of_nonneg_right (by linarith [ratio_gt_record]) (Nat.cast_nonneg _)) (h T hT)

end
end T052
end T052CountSource

section T052Candidate

theorem candidate_strict_improvement : currentRecordKappa < candidateKappa := by
  norm_num [currentRecordKappa, candidateKappa]

theorem candidate_critical_line_bound :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (candidateKappa - ε) * (Ncount T (2 * T) : ℝ) ≤ N0star T (2 * T) := by
  rw [show candidateKappa = T052.record by norm_num [candidateKappa, T052.record]]
  exact T052.critical_dyadic _root_.riemannHypothesis

theorem candidate_critical_line_bound_cumulative :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (candidateKappa - ε) * (Ncount 0 T : ℝ) ≤ N0star 0 T := by
  rw [show candidateKappa = T052.record by norm_num [candidateKappa, T052.record]]
  exact T052.critical_cumulative _root_.riemannHypothesis

end T052Candidate
