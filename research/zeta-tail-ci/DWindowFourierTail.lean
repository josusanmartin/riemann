/-
Copyright (c) 2026.
SPDX-License-Identifier: Apache-2.0

Fourier-decay input for the omitted D-window grid tails.

This file converts the admissible-window estimate

  |vHatR(r)| * r^2 <= c / w

into a summable inverse-fourth-power bound along any sequence whose absolute
arguments grow at least arithmetically.  It is the analytic half of the
finite-grid tail estimate; the remaining bookkeeping is the reindexing of the
omitted integer grid into its left and right natural-number tails.
-/
import Zeta23.GapMatching.FiniteGridTailAlgebra
import Zeta23.ThmD.WindowCore

open Finset Real

noncomputable section

namespace Zeta23.GapMatching.DWindowFourierTail

open Zeta23
open Zeta23.AdmWindow
open Zeta23.GapMatching.FiniteGridTailAlgebra

/-- Pointwise inverse-fourth-power decay after squaring the real Fourier
bound. -/
theorem vHatR_sq_le_inv_four
    {v : ℝ → ℝ} {L w c r D : ℝ}
    (hW : AdmWindow v L w c)
    (hD : 0 < D)
    (habs : D ≤ |r|) :
    vHatR v r ^ 2
      ≤ (c / w) ^ 2 * (D ^ 4)⁻¹ := by
  have hrabs : 0 < |r| := hD.trans_le habs
  have hrne : r ≠ 0 := by
    intro hr
    subst r
    simp at hrabs
  have hr2 : 0 < r ^ 2 := sq_pos_of_ne_zero hrne
  have hdecay := hW.abs_vHatR_mul_sq_le r
  have hquot :
      |vHatR v r| ≤ (c / w) / (r ^ 2) := by
    rw [le_div_iff₀ hr2]
    exact hdecay
  have hsquare :
      |vHatR v r| ^ 2 ≤ ((c / w) / (r ^ 2)) ^ 2 :=
    pow_le_pow_left₀ (abs_nonneg _) hquot 2
  have hpow : D ^ 4 ≤ |r| ^ 4 :=
    pow_le_pow_left₀ hD.le habs 4
  have hinv : (|r| ^ 4)⁻¹ ≤ (D ^ 4)⁻¹ :=
    inv_anti₀ (by positivity) hpow
  calc
    vHatR v r ^ 2 = |vHatR v r| ^ 2 := by rw [sq_abs]
    _ ≤ ((c / w) / (r ^ 2)) ^ 2 := hsquare
    _ = (c / w) ^ 2 * (|r| ^ 4)⁻¹ := by
          rw [show r ^ 2 = |r| ^ 2 by rw [sq_abs]]
          field_simp [hrabs.ne']
    _ ≤ (c / w) ^ 2 * (D ^ 4)⁻¹ := by
          exact mul_le_mul_of_nonneg_left hinv (sq_nonneg (c / w))

/-- Finite partial sums along an arithmetically escaping argument sequence. -/
theorem sum_vHatR_sq_range_le
    {v : ℝ → ℝ} {L w c D h : ℝ}
    (hW : AdmWindow v L w c)
    (hD : 0 < D) (hh : 0 < h)
    (r : ℕ → ℝ)
    (harg : ∀ n, D + n * h ≤ |r n|)
    (m : ℕ) :
    ∑ n ∈ Finset.range m, vHatR v (r n) ^ 2
      ≤ (c / w) ^ 2
          * ((D ^ 4)⁻¹ + (D ^ 3)⁻¹ / (3 * h)) := by
  calc
    ∑ n ∈ Finset.range m, vHatR v (r n) ^ 2
        ≤ ∑ n ∈ Finset.range m,
            (c / w) ^ 2 * ((D + n * h) ^ 4)⁻¹ := by
          exact Finset.sum_le_sum fun n _ =>
            vHatR_sq_le_inv_four hW (by positivity) (harg n)
    _ = (c / w) ^ 2
          * ∑ n ∈ Finset.range m, ((D + n * h) ^ 4)⁻¹ := by
          rw [Finset.mul_sum]
    _ ≤ (c / w) ^ 2
          * ((D ^ 4)⁻¹ + (D ^ 3)⁻¹ / (3 * h)) := by
          exact mul_le_mul_of_nonneg_left
            (Zeta23.Tail.sum_inv_pow_four_le hD hh m)
            (sq_nonneg (c / w))

/-- Summability of the squared Fourier tail. -/
theorem summable_vHatR_sq
    {v : ℝ → ℝ} {L w c D h : ℝ}
    (hW : AdmWindow v L w c)
    (hD : 0 < D) (hh : 0 < h)
    (r : ℕ → ℝ)
    (harg : ∀ n, D + n * h ≤ |r n|) :
    Summable (fun n => vHatR v (r n) ^ 2) := by
  apply summable_of_sum_range_le
  · intro n
    exact sq_nonneg _
  · intro m
    exact sum_vHatR_sq_range_le hW hD hh r harg m

/-- Quantitative `tsum` bound for the squared Fourier tail. -/
theorem tsum_vHatR_sq_le
    {v : ℝ → ℝ} {L w c D h : ℝ}
    (hW : AdmWindow v L w c)
    (hD : 0 < D) (hh : 0 < h)
    (r : ℕ → ℝ)
    (harg : ∀ n, D + n * h ≤ |r n|) :
    ∑' n, vHatR v (r n) ^ 2
      ≤ (c / w) ^ 2
          * ((D ^ 4)⁻¹ + (D ^ 3)⁻¹ / (3 * h)) := by
  apply Real.tsum_le_of_sum_range_le
  · intro n
    exact sq_nonneg _
  · intro m
    exact sum_vHatR_sq_range_le hW hD hh r harg m

/-- Left omitted grid arguments escape arithmetically from every point at
least `D` to the right of the grid origin. -/
theorem left_argument_lower
    {T tau D h : ℝ}
    (hD : 0 ≤ D) (hh : 0 ≤ h)
    (htau : T + D ≤ tau) (n : ℕ) :
    D + n * h
      ≤ |tau - (T - (n + 1) * h)| := by
  have hpos : 0 ≤ tau - (T - (n + 1) * h) := by
    push_cast
    nlinarith
  rw [abs_of_nonneg hpos]
  push_cast
  nlinarith

/-- Right omitted grid arguments escape arithmetically from every point at
least `D` to the left of the first omitted grid point. -/
theorem right_argument_lower
    {T tau D h : ℝ} {d : ℕ}
    (hD : 0 ≤ D) (hh : 0 ≤ h)
    (htau : tau + D ≤ T + d * h) (n : ℕ) :
    D + n * h
      ≤ |tau - (T + (d + n) * h)| := by
  have hneg : tau - (T + (d + n) * h) ≤ 0 := by
    push_cast
    nlinarith
  rw [abs_of_nonpos hneg]
  push_cast
  nlinarith

end Zeta23.GapMatching.DWindowFourierTail
