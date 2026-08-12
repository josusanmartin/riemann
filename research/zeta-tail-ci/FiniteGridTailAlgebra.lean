/-
Copyright (c) 2026.
SPDX-License-Identifier: Apache-2.0

Infinite-tail algebra needed by the D-window finite-grid comparison.

The upstream tail proof supplies the sharp finite partial-sum estimate for
`(D+n h)^-4`.  This file takes its monotone limit and records a product-tail
lemma: if both omitted square tails are at most `q`, then the omitted overlap
tail has norm at most `q`.  The latter uses the pointwise inequality
`|xy| <= (x^2+y^2)/2`, avoiding an additional Hilbert-space layer.
-/
import Zeta23.Tail.Grid
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Analysis.Normed.Group.InfiniteSum

open Finset Real

noncomputable section

namespace Zeta23.GapMatching.FiniteGridTailAlgebra

open Zeta23
open Zeta23.Tail

/-- Infinite version of the upstream inverse-fourth-power grid estimate. -/
theorem tsum_inv_pow_four_le
    {D h : ℝ} (hD : 0 < D) (hh : 0 < h) :
    ∑' n : ℕ, ((D + n * h) ^ 4)⁻¹
      ≤ (D ^ 4)⁻¹ + (D ^ 3)⁻¹ / (3 * h) := by
  apply Real.tsum_le_of_sum_range_le
  · intro n
    positivity
  · intro n
    exact sum_inv_pow_four_le hD hh n

/-- The inverse-fourth-power tail is summable. -/
theorem summable_inv_pow_four
    {D h : ℝ} (hD : 0 < D) (hh : 0 < h) :
    Summable (fun n : ℕ => ((D + n * h) ^ 4)⁻¹) := by
  apply summable_of_sum_range_le
  · intro n
    positivity
  · intro n
    exact sum_inv_pow_four_le hD hh n

/-- Scalar Young inequality in the exact form used for overlap tails. -/
theorem abs_mul_le_sq_average (x y : ℝ) :
    |x * y| ≤ (x ^ 2 + y ^ 2) / 2 := by
  rw [abs_mul]
  nlinarith [sq_nonneg (|x| - |y|), sq_abs x, sq_abs y]

/-- Products of two square-summable real sequences are summable. -/
theorem summable_mul_of_sq_summable
    (x y : ℕ → ℝ)
    (hx : Summable (fun n => x n ^ 2))
    (hy : Summable (fun n => y n ^ 2)) :
    Summable (fun n => x n * y n) := by
  have hfin : ∀ u : Finset ℕ,
      ∑ n ∈ u, |x n * y n|
        ≤ ((∑' n, x n ^ 2) + (∑' n, y n ^ 2)) / 2 := by
    intro u
    calc
      ∑ n ∈ u, |x n * y n|
          ≤ ∑ n ∈ u, (x n ^ 2 + y n ^ 2) / 2 := by
            exact Finset.sum_le_sum fun n _ =>
              abs_mul_le_sq_average (x n) (y n)
      _ = ((∑ n ∈ u, x n ^ 2) + (∑ n ∈ u, y n ^ 2)) / 2 := by
            rw [show
              ∑ n ∈ u, (x n ^ 2 + y n ^ 2) / 2
                = (1 / 2 : ℝ) *
                    ∑ n ∈ u, (x n ^ 2 + y n ^ 2) by
                  rw [Finset.mul_sum]
                  apply Finset.sum_congr rfl
                  intro n _
                  ring,
              Finset.sum_add_distrib]
            ring
      _ ≤ ((∑' n, x n ^ 2) + (∑' n, y n ^ 2)) / 2 := by
            gcongr
            · exact Summable.sum_le_tsum u
                (fun n _ => sq_nonneg (x n)) hx
            · exact Summable.sum_le_tsum u
                (fun n _ => sq_nonneg (y n)) hy
  have habs : Summable (fun n => |x n * y n|) :=
    summable_of_sum_le (fun n => abs_nonneg (x n * y n)) hfin
  apply Summable.of_norm
  simpa only [Real.norm_eq_abs] using habs

/-- Square-tail control implies product-tail control.

The hypotheses are deliberately phrased using `tsum` bounds, the natural
output of the inverse-fourth-power estimate. -/
theorem norm_tsum_mul_le_of_sq_tsum_le
    (x y : ℕ → ℝ) {qx qy : ℝ}
    (hx : Summable (fun n => x n ^ 2))
    (hy : Summable (fun n => y n ^ 2))
    (hxq : ∑' n, x n ^ 2 ≤ qx)
    (hyq : ∑' n, y n ^ 2 ≤ qy) :
    ‖∑' n, x n * y n‖ ≤ (qx + qy) / 2 := by
  have hfin : ∀ u : Finset ℕ,
      ∑ n ∈ u, |x n * y n| ≤ (qx + qy) / 2 := by
    intro u
    calc
      ∑ n ∈ u, |x n * y n|
          ≤ ∑ n ∈ u, (x n ^ 2 + y n ^ 2) / 2 := by
            exact Finset.sum_le_sum fun n _ =>
              abs_mul_le_sq_average (x n) (y n)
      _ = (1 / 2 : ℝ) *
            ∑ n ∈ u, (x n ^ 2 + y n ^ 2) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro n _
            ring
      _ = ((∑ n ∈ u, x n ^ 2) + (∑ n ∈ u, y n ^ 2)) / 2 := by
            rw [Finset.sum_add_distrib]
            ring
      _ ≤ ((∑' n, x n ^ 2) + (∑' n, y n ^ 2)) / 2 := by
            gcongr
            · exact Summable.sum_le_tsum u
                (fun n _ => sq_nonneg (x n)) hx
            · exact Summable.sum_le_tsum u
                (fun n _ => sq_nonneg (y n)) hy
      _ ≤ (qx + qy) / 2 := by
            linarith

  have habs : Summable (fun n => |x n * y n|) :=
    summable_of_sum_le (fun n => abs_nonneg (x n * y n)) hfin
  have hnorm :
      ‖∑' n, x n * y n‖ ≤ ∑' n, |x n * y n| := by
    simpa only [Real.norm_eq_abs] using
      (norm_tsum_le_tsum_norm
        (f := fun n => x n * y n)
        (by simpa only [Real.norm_eq_abs] using habs))
  exact hnorm.trans
    (Real.tsum_le_of_sum_le
      (fun n => abs_nonneg (x n * y n)) hfin)

/-- Symmetric specialization: two square tails bounded by the same `q` give
an overlap-tail bound `q`. -/
theorem norm_tsum_mul_le_of_sq_tsum_le_same
    (x y : ℕ → ℝ) {q : ℝ}
    (hx : Summable (fun n => x n ^ 2))
    (hy : Summable (fun n => y n ^ 2))
    (hxq : ∑' n, x n ^ 2 ≤ q)
    (hyq : ∑' n, y n ^ 2 ≤ q) :
    ‖∑' n, x n * y n‖ ≤ q := by
  have h := norm_tsum_mul_le_of_sq_tsum_le
    x y hx hy hxq hyq
  simpa using h

/-- Scaling a product tail by a nonnegative constant scales its norm bound. -/
theorem norm_tsum_const_mul_mul_le_same
    (a : ℝ) (ha : 0 ≤ a)
    (x y : ℕ → ℝ) {q : ℝ}
    (hx : Summable (fun n => x n ^ 2))
    (hy : Summable (fun n => y n ^ 2))
    (hxq : ∑' n, x n ^ 2 ≤ q)
    (hyq : ∑' n, y n ^ 2 ≤ q) :
    ‖∑' n, a * (x n * y n)‖ ≤ a * q := by
  have hprod := summable_mul_of_sq_summable x y hx hy
  have hscaled :
      HasSum (fun n => a • (x n * y n))
        (a • ∑' n, x n * y n) :=
    HasSum.const_smul a hprod.hasSum
  have heq :
      (∑' n, a * (x n * y n)) =
        a * (∑' n, x n * y n) := by
    simpa only [smul_eq_mul] using hscaled.tsum_eq
  rw [heq, norm_mul, Real.norm_eq_abs, abs_of_nonneg ha]
  exact mul_le_mul_of_nonneg_left
    (norm_tsum_mul_le_of_sq_tsum_le_same x y hx hy hxq hyq) ha

end Zeta23.GapMatching.FiniteGridTailAlgebra
