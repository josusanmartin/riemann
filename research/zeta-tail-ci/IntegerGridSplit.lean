/-
Copyright (c) 2026.
SPDX-License-Identifier: Apache-2.0

Exact decomposition of a summable integer-indexed series into a finite
nonnegative block and its two omitted tails.
-/
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Algebra.InfiniteSum.Real

open Finset

noncomputable section

namespace Zeta23.GapMatching.IntegerGridSplit

/-- Split an absolutely summable integer grid into

* the negative tail `-(n+1)`,
* the finite block `0, ..., d-1`, and
* the right tail `d+n`.
-/
theorem tsum_int_eq_left_add_finite_add_right
    {f : ℤ → ℝ} (hf : Summable f) (d : ℕ) :
    ∑' k : ℤ, f k =
      (∑' n : ℕ, f (-(n + 1)))
        + (∑ n ∈ Finset.range d, f n)
        + ∑' n : ℕ, f (n + d) := by
  have hparts :=
    (summable_int_iff_summable_nat_and_neg_add_one.mp hf)
  have hnat : Summable (fun n : ℕ => f n) := hparts.1
  have hneg : Summable (fun n : ℕ => f (-(n + 1))) := hparts.2
  rw [tsum_of_nat_of_neg_add_one hnat hneg]
  have hsplit := hnat.sum_add_tsum_nat_add d
  rw [← hsplit]
  ring

/-- The finite block differs from the full integer sum by at most the sum of
the norms of its two omitted tails. -/
theorem norm_finite_sub_tsum_le
    {f : ℤ → ℝ} (hf : Summable f) (d : ℕ) :
    ‖(∑ n ∈ Finset.range d, f n) - ∑' k : ℤ, f k‖
      ≤ ‖∑' n : ℕ, f (-(n + 1))‖
        + ‖∑' n : ℕ, f (n + d)‖ := by
  rw [tsum_int_eq_left_add_finite_add_right hf d]
  have hid :
      (∑ n ∈ Finset.range d, f n)
          - ((∑' n : ℕ, f (-(n + 1)))
            + (∑ n ∈ Finset.range d, f n)
            + ∑' n : ℕ, f (n + d))
        = -((∑' n : ℕ, f (-(n + 1)))
            + ∑' n : ℕ, f (n + d)) := by
    ring
  rw [hid, norm_neg]
  exact norm_add_le _ _

/-- Quantitative wrapper for two separately controlled tails. -/
theorem norm_finite_sub_tsum_le_of_tail_bounds
    {f : ℤ → ℝ} (hf : Summable f) (d : ℕ)
    {qLeft qRight : ℝ}
    (hleft : ‖∑' n : ℕ, f (-(n + 1))‖ ≤ qLeft)
    (hright : ‖∑' n : ℕ, f (n + d)‖ ≤ qRight) :
    ‖(∑ n ∈ Finset.range d, f n) - ∑' k : ℤ, f k‖
      ≤ qLeft + qRight :=
  (norm_finite_sub_tsum_le hf d).trans (add_le_add hleft hright)

end Zeta23.GapMatching.IntegerGridSplit
