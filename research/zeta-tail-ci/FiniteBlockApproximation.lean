/-
Copyright (c) 2026.
SPDX-License-Identifier: Apache-2.0

Abstract bridge from a full integer Poisson sum to a finite nonnegative block.
-/
import Zeta23.GapMatching.IntegerGridSplit

open Finset

noncomputable section

namespace Zeta23.GapMatching.FiniteBlockApproximation

open Zeta23.GapMatching.IntegerGridSplit

/-- The nonnegative finite block `0, ..., d-1` of an integer-indexed series. -/
def finiteBlock (f : ℤ → ℝ) (d : ℕ) : ℝ :=
  ∑ n ∈ Finset.range d, f (n : ℤ)

/-- A full `HasSum` identity and separate left/right tail bounds give an
absolute error estimate for the finite block. -/
theorem abs_finiteBlock_sub_le
    {f : ℤ → ℝ} {full qLeft qRight : ℝ}
    (hfull : HasSum f full) (d : ℕ)
    (hleft : norm (∑' n : ℕ, f (-((n : ℤ) + 1))) ≤ qLeft)
    (hright : norm (∑' n : ℕ, f ((n + d : ℕ) : ℤ)) ≤ qRight) :
    |finiteBlock f d - full| ≤ qLeft + qRight := by
  have h := norm_finite_sub_tsum_le_of_tail_bounds
    hfull.summable d hleft hright
  rw [hfull.tsum_eq] at h
  simpa only [finiteBlock, Real.norm_eq_abs] using h

/-- Symmetric specialization. -/
theorem abs_finiteBlock_sub_le_same
    {f : ℤ → ℝ} {full q : ℝ}
    (hfull : HasSum f full) (d : ℕ)
    (hleft : norm (∑' n : ℕ, f (-((n : ℤ) + 1))) ≤ q)
    (hright : norm (∑' n : ℕ, f ((n + d : ℕ) : ℤ)) ≤ q) :
    |finiteBlock f d - full| ≤ 2 * q := by
  have h := abs_finiteBlock_sub_le hfull d hleft hright
  linarith

end Zeta23.GapMatching.FiniteBlockApproximation
