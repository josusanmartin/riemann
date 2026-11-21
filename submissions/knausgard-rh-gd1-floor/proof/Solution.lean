import ChallengeDeps.CandidateSpec
import Zeta23.ThmD.Mult
import Mathlib.Tactic
import Main

/-
Candidate 8362503491/10^10 (Kristian Muri Knausgård, 2026-11-21): Josu San Martin's record
critical-line-669-800 (Apache-2.0) with the rational floor taken at the full strength of its own
enclosure `gam_upper`; nothing else is changed. Source:
https://github.com/josusanmartin/riemann/blob/b13a32d590666d36453b0ac684181d4f642beb7a/submissions/critical-line-669-800/proof/Solution.lean
The Main import is from the published
RH source at 2f097b744a6460c73f3e4cc550baa83698409876; the numerical
enclosure and corollaries are inlined below. SPDX-License-Identifier: Apache-2.0
-/

noncomputable section

/-
Exact rational certificate for the Montgomery--Taylor distinct-zero constant.

The Taylor and square-root enclosure lemmas below are extracted and narrowed
from the Apache-2.0 submission `five-point-pyramid` by typh (typhdotcom), which
attributes the analytic enclosure development to Samuel Lavery's
`attempt-002` submission. Source:
https://github.com/josusanmartin/riemann/blob/main/submissions/five-point-pyramid/proof/Solution.lean

Modifications: retained only the upper bound needed for x*cot(x), changed the
namespace, removed all Zeta23/certificate-table dependencies, and added the
669/800 corollary. The original authors' Apache-2.0 licensing remains applicable.

This file proves only a real-number inequality. It does not prove RH.
-/


namespace RiemannRHBridge.Numeric

private def taylorCos (t : ℝ) : ℝ :=
  1 - t^2/2 + t^4/24 - t^6/720 + t^8/40320 - t^10/3628800

private def taylorSin (t : ℝ) : ℝ :=
  t - t^3/6 + t^5/120 - t^7/5040 + t^9/362880 - t^11/39916800

private def taylorErr : ℝ := 13/5748019200

private theorem cos_sin_taylor12 (θ : ℝ) (hθ : |θ| ≤ 1) :
    |Real.cos θ - (1 - θ^2/2 + θ^4/24 - θ^6/720 + θ^8/40320 - θ^10/3628800)|
        ≤ |θ|^12 * (13/5748019200) ∧
    |Real.sin θ - (θ - θ^3/6 + θ^5/120 - θ^7/5040 + θ^9/362880 - θ^11/39916800)|
        ≤ |θ|^12 * (13/5748019200) := by
  have hx : ‖(θ : ℂ) * Complex.I‖ ≤ 1 := by
    simpa using hθ
  have hb := Complex.exp_bound hx (n := 12) (by norm_num)
  have hnx : ‖(θ : ℂ) * Complex.I‖ = |θ| := by simp
  have hsum : ∑ m ∈ Finset.range 12, ((θ : ℂ) * Complex.I) ^ m / (m.factorial : ℂ)
      = ((1 - θ^2/2 + θ^4/24 - θ^6/720 + θ^8/40320 - θ^10/3628800 : ℝ) : ℂ)
        + ((θ - θ^3/6 + θ^5/120 - θ^7/5040 + θ^9/362880 - θ^11/39916800 : ℝ) : ℂ)
          * Complex.I := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
    apply Complex.ext <;> · simp [pow_succ]; ring
  rw [hsum, hnx] at hb
  have hE : ‖Complex.exp ((θ : ℂ) * Complex.I)
      - (((1 - θ^2/2 + θ^4/24 - θ^6/720 + θ^8/40320 - θ^10/3628800 : ℝ) : ℂ)
        + ((θ - θ^3/6 + θ^5/120 - θ^7/5040 + θ^9/362880 - θ^11/39916800 : ℝ) : ℂ)
          * Complex.I)‖ ≤ |θ|^12 * (13/5748019200) := by
    refine hb.trans (le_of_eq ?_)
    norm_num
  constructor
  · have := Complex.abs_re_le_norm (Complex.exp ((θ : ℂ) * Complex.I)
      - (((1 - θ^2/2 + θ^4/24 - θ^6/720 + θ^8/40320 - θ^10/3628800 : ℝ) : ℂ)
        + ((θ - θ^3/6 + θ^5/120 - θ^7/5040 + θ^9/362880 - θ^11/39916800 : ℝ) : ℂ)
          * Complex.I))
    refine le_trans (le_of_eq ?_) (this.trans hE)
    simp [Complex.exp_ofReal_mul_I_re, - Complex.ofReal_pow]
  · have := Complex.abs_im_le_norm (Complex.exp ((θ : ℂ) * Complex.I)
      - (((1 - θ^2/2 + θ^4/24 - θ^6/720 + θ^8/40320 - θ^10/3628800 : ℝ) : ℂ)
        + ((θ - θ^3/6 + θ^5/120 - θ^7/5040 + θ^9/362880 - θ^11/39916800 : ℝ) : ℂ)
          * Complex.I))
    refine le_trans (le_of_eq ?_) (this.trans hE)
    simp [Complex.exp_ofReal_mul_I_im, - Complex.ofReal_pow]

private lemma one_le_pi : (1 : ℝ) ≤ Real.pi := by
  linarith [Real.pi_gt_three]

private lemma err_scale {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    |t| ^ 12 * (13 / 5748019200) ≤ taylorErr := by
  rw [abs_of_nonneg h0]
  have : t ^ 12 ≤ 1 := pow_le_one₀ h0 h1
  unfold taylorErr
  nlinarith

private theorem cos_upper {θ l : ℝ} (h0 : 0 ≤ l) (hl : l ≤ θ) (hθ1 : θ ≤ 1) :
    Real.cos θ ≤ taylorCos l + taylorErr := by
  have hl1 : l ≤ 1 := hl.trans hθ1
  have hmono : Real.cos θ ≤ Real.cos l :=
    Real.cos_le_cos_of_nonneg_of_le_pi h0 (hθ1.trans one_le_pi) hl
  have ht := (cos_sin_taylor12 l (by rw [abs_of_nonneg h0]; exact hl1)).1
  have he := err_scale h0 hl1
  have := abs_le.mp ht
  unfold taylorCos
  linarith [this.1, this.2]

private theorem sin_lower {θ l : ℝ} (h0 : 0 ≤ l) (hl : l ≤ θ) (hθ1 : θ ≤ 1) :
    taylorSin l - taylorErr ≤ Real.sin θ := by
  have hl1 : l ≤ 1 := hl.trans hθ1
  have hpi2 : (1 : ℝ) ≤ Real.pi / 2 := by linarith [Real.pi_gt_three]
  have hmono : Real.sin l ≤ Real.sin θ :=
    Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith) (hθ1.trans hpi2) hl
  have ht := (cos_sin_taylor12 l (by rw [abs_of_nonneg h0]; exact hl1)).2
  have he := err_scale h0 hl1
  have := abs_le.mp ht
  unfold taylorSin
  linarith [this.1, this.2]

private lemma sqrt2_half_bounds :
    (7071067811865475244/10^19 : ℝ) ≤ Real.sqrt 2 / 2 ∧
      Real.sqrt 2 / 2 ≤ 7071067811865475245/10^19 := by
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hnn : (0:ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  constructor <;> nlinarith [h2, hnn]

private theorem cos_sqrt2_half_upper :
    Real.cos (Real.sqrt 2 / 2) ≤ (7602445994/10^10 : ℝ) := by
  have hb := sqrt2_half_bounds
  have := cos_upper (by norm_num) hb.1 (by linarith [hb.2])
  have h : taylorCos (7071067811865475244/10^19 : ℝ) + taylorErr
      ≤ 7602445994/10^10 := by
    unfold taylorCos taylorErr
    norm_num
  linarith

private theorem sin_sqrt2_half_lower :
    (6496369368/10^10 : ℝ) ≤ Real.sin (Real.sqrt 2 / 2) := by
  have hb := sqrt2_half_bounds
  have := sin_lower (by norm_num) hb.1 (by linarith [hb.2])
  have h : (6496369368/10^10 : ℝ)
      ≤ taylorSin (7071067811865475244/10^19) - taylorErr := by
    unfold taylorSin taylorErr
    norm_num
  linarith

/-- A certified upper bound for x*cot(x) at x = sqrt(2)/2. -/
theorem gam_upper :
    (Real.sqrt 2 / 2) * Real.cos (Real.sqrt 2 / 2) / Real.sin (Real.sqrt 2 / 2)
      ≤ (8274993018/10^10 : ℝ) := by
  have hb := sqrt2_half_bounds
  have hc := cos_sqrt2_half_upper
  have hs := sin_sqrt2_half_lower
  have h0 : (0:ℝ) ≤ Real.sqrt 2 / 2 := by linarith [hb.1]
  have hspos : (0:ℝ) < Real.sin (Real.sqrt 2 / 2) := by linarith
  have hprodu : (Real.sqrt 2 / 2) * Real.cos (Real.sqrt 2 / 2)
      ≤ (7071067811865475245/10^19 : ℝ) * (7602445994/10^10) := by
    calc
      _ ≤ (Real.sqrt 2 / 2) * (7602445994/10^10) :=
        mul_le_mul_of_nonneg_left hc h0
      _ ≤ _ := mul_le_mul_of_nonneg_right hb.2 (by norm_num)
  rw [div_le_iff₀ hspos]
  nlinarith [hprodu, hs]

theorem inv_sqrt_two : (Real.sqrt 2)⁻¹ = Real.sqrt 2 / 2 := by
  have hne : Real.sqrt 2 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  rw [inv_eq_one_div, div_eq_div_iff hne two_ne_zero, one_mul,
    Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 2)]

/-- Exact, conservative rational floor for GD(1), independent of Zeta23. -/
theorem montgomery_taylor_rational_floor :
    (8362503491 / 10000000000 : ℝ) ≤
      5 / 4 - (Real.sqrt 2)⁻¹ *
        (Real.cos ((Real.sqrt 2)⁻¹) / Real.sin ((Real.sqrt 2)⁻¹)) / 2 := by
  rw [inv_sqrt_two]
  have hg := gam_upper
  have hid : (Real.sqrt 2 / 2) *
      (Real.cos (Real.sqrt 2 / 2) / Real.sin (Real.sqrt 2 / 2)) =
      (Real.sqrt 2 / 2) * Real.cos (Real.sqrt 2 / 2) / Real.sin (Real.sqrt 2 / 2) := by
    ring
  rw [hid]
  linarith


end RiemannRHBridge.Numeric

namespace RiemannRHBridge
theorem rational_le_GD_one : (8362503491 / 10000000000 : ℝ) ≤ Zeta23.ThmD.GD 1 := by
  calc
    (8362503491 / 10000000000 : ℝ) ≤
        5 / 4 - (Real.sqrt 2)⁻¹ *
          (Real.cos ((Real.sqrt 2)⁻¹) / Real.sin ((Real.sqrt 2)⁻¹)) / 2 :=
      Numeric.montgomery_taylor_rational_floor
    _ = Zeta23.ThmD.GD 1 := by
      rw [Zeta23.ThmD.GD_eq, Zeta23.ThmD.HD_one]
      ring

end RiemannRHBridge
end

/-!
Exact asymptotic critical-line bounds obtained by applying Alpöge's published
RH theorem to the distinct-zero results of Alpöge and Furman. We use the
counting functions defined in Zeta23. The denominator counts multiplicities.
-/
noncomputable section
namespace CriticalLine669

theorem onLineCount (a b : ℝ) :
    Zeta23.N0star a b = Zeta23.Ndist a b :=
  (Zeta23.RH_implies_all_on_line _root_.riemannHypothesis a b).2

/-- In every window the exact loss from discarding distinct off-line zeros is zero. -/
theorem offLineLoss (a b : ℝ) : Zeta23.Ndist a b - Zeta23.N0star a b = 0 := by
  rw [onLineCount, Nat.sub_self]

/-- A bound for distinct zeros anywhere transfers to the critical line. -/
private theorem transfer {a b k : ℝ} {ε : ℝ}
    (h : (k - ε) * (Zeta23.Ncount a b : ℝ) ≤ Zeta23.Ndist a b) :
    (k - ε) * (Zeta23.Ncount a b : ℝ) ≤ Zeta23.N0star a b := by
  rw [onLineCount]
  exact h

theorem dyadic {k : ℝ} (hk : k ≤ Zeta23.ThmD.GD 1) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (k - ε) * (Zeta23.Ncount T (2 * T) : ℝ) ≤ Zeta23.N0star T (2 * T) := by
  intro ε hε
  obtain ⟨T₀, h⟩ := Zeta23.ThmD.thmD₀_dist_mult ε hε
  refine ⟨T₀, fun T hT => transfer ?_⟩
  exact (mul_le_mul_of_nonneg_right (sub_le_sub_right hk ε) (Nat.cast_nonneg _)).trans (h T hT)

theorem cumulative {k : ℝ} (hk : k ≤ Zeta23.ThmD.GD 1) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (k - ε) * (Zeta23.Ncount 0 T : ℝ) ≤ Zeta23.N0star 0 T := by
  intro ε hε
  obtain ⟨T₀, h⟩ := Zeta23.ThmD.thmD₀_dist_mult_cumulative ε hε
  refine ⟨T₀, fun T hT => transfer ?_⟩
  exact (mul_le_mul_of_nonneg_right (sub_le_sub_right hk ε) (Nat.cast_nonneg _)).trans (h T hT)

theorem dyadic_669 :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      ((8362503491 / 10000000000 : ℝ) - ε) * (Zeta23.Ncount T (2 * T) : ℝ) ≤ Zeta23.N0star T (2 * T) :=
  dyadic RiemannRHBridge.rational_le_GD_one

theorem cumulative_669 :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      ((8362503491 / 10000000000 : ℝ) - ε) * (Zeta23.Ncount 0 T : ℝ) ≤ Zeta23.N0star 0 T :=
  cumulative RiemannRHBridge.rational_le_GD_one

end CriticalLine669
end

#print axioms CriticalLine669.offLineLoss
#print axioms CriticalLine669.dyadic_669
#print axioms CriticalLine669.cumulative_669

noncomputable section

theorem candidate_strict_improvement :
    currentRecordKappa < candidateKappa := by
  norm_num [currentRecordKappa, candidateKappa]

theorem candidate_critical_line_bound :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (candidateKappa - ε) * (Ncount T (2 * T) : ℝ) ≤ N0star T (2 * T) := by
  have e : candidateKappa = (8362503491 / 10000000000 : ℝ) := by norm_num [candidateKappa]
  rw [e]
  exact CriticalLine669.dyadic_669

theorem candidate_critical_line_bound_cumulative :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (candidateKappa - ε) * (Ncount 0 T : ℝ) ≤ N0star 0 T := by
  have e : candidateKappa = (8362503491 / 10000000000 : ℝ) := by norm_num [candidateKappa]
  rw [e]
  exact CriticalLine669.cumulative_669

end
