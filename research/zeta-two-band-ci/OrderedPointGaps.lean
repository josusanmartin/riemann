/-
Copyright (c) 2026.
SPDX-License-Identifier: Apache-2.0

Exact telescoping facts for a finite ordered list of ordinates.

The first point is carried separately and the tail contains every later
point.  `successiveDiffs x xs` therefore has exactly `xs.length` gaps and
its sum is the last point minus the first.  This is the finite identity used
by the gap-matching length estimate before the analytic normalization by
`L/(2*pi)`.
-/
import Mathlib

noncomputable section

namespace Zeta23.GapMatching.OrderedPointGaps

/-- Last point reached after starting at `x` and traversing `xs`. -/
def lastFrom (x : ℝ) : List ℝ → ℝ
  | [] => x
  | y :: ys => lastFrom y ys

/-- Consecutive differences from the ordered points `x :: xs`. -/
def successiveDiffs (x : ℝ) : List ℝ → List ℝ
  | [] => []
  | y :: ys => (y - x) :: successiveDiffs y ys

/-- Recursive monotonicity predicate for `x :: xs`. -/
def OrderedFrom (x : ℝ) : List ℝ → Prop
  | [] => True
  | y :: ys => x ≤ y ∧ OrderedFrom y ys

/-- There is one consecutive gap for every point after the first. -/
theorem successiveDiffs_length : ∀ x xs,
    (successiveDiffs x xs).length = xs.length
  | _, [] => by simp [successiveDiffs]
  | x, y :: ys => by
      simp [successiveDiffs, successiveDiffs_length y ys]

/-- Exact telescoping identity. -/
theorem successiveDiffs_sum : ∀ x xs,
    (successiveDiffs x xs).sum = lastFrom x xs - x
  | x, [] => by simp [successiveDiffs, lastFrom]
  | x, y :: ys => by
      simp [successiveDiffs, lastFrom, successiveDiffs_sum y ys]
      ring

/-- Ordered points have nonnegative consecutive gaps. -/
theorem successiveDiffs_nonneg : ∀ x xs,
    OrderedFrom x xs →
      ∀ gap ∈ successiveDiffs x xs, 0 ≤ gap
  | _, [], _ => by simp [successiveDiffs]
  | x, y :: ys, hordered => by
      change x ≤ y ∧ OrderedFrom y ys at hordered
      intro gap hgap
      simp only [successiveDiffs, List.mem_cons] at hgap
      rcases hgap with rfl | htail
      · linarith [hordered.1]
      · exact successiveDiffs_nonneg y ys hordered.2 gap htail

/-- Consecutive gaps after multiplication by a nonnegative scale. -/
def normalizedGaps (scale x : ℝ) (xs : List ℝ) : List ℝ :=
  (successiveDiffs x xs).map (fun gap => scale * gap)

/-- Normalization preserves the number of gaps. -/
theorem normalizedGaps_length (scale x : ℝ) (xs : List ℝ) :
    (normalizedGaps scale x xs).length = xs.length := by
  simp [normalizedGaps, successiveDiffs_length]

/-- Normalized gaps telescope to scale times the endpoint displacement. -/
theorem normalizedGaps_sum : ∀ scale x xs,
    (normalizedGaps scale x xs).sum
      = scale * (lastFrom x xs - x)
  | scale, x, [] => by
      simp [normalizedGaps, successiveDiffs, lastFrom]
  | scale, x, y :: ys => by
      simp [normalizedGaps, successiveDiffs, lastFrom,
        normalizedGaps_sum scale y ys]
      ring

/-- Nonnegative scale and ordered points give nonnegative normalized gaps. -/
theorem normalizedGaps_nonneg
    {scale x : ℝ} {xs : List ℝ}
    (hscale : 0 ≤ scale) (hordered : OrderedFrom x xs) :
    ∀ gap ∈ normalizedGaps scale x xs, 0 ≤ gap := by
  intro gap hgap
  simp only [normalizedGaps, List.mem_map] at hgap
  obtain ⟨raw, hraw, rfl⟩ := hgap
  exact mul_nonneg hscale
    (successiveDiffs_nonneg x xs hordered raw hraw)

/-- Endpoint form of the normalized total-length estimate. -/
theorem normalizedGaps_sum_le
    {scale x endpoint total error : ℝ} {xs : List ℝ}
    (hendpoint : lastFrom x xs ≤ endpoint)
    (hscale : 0 ≤ scale)
    (hlength : scale * (endpoint - x) ≤ total + error) :
    (normalizedGaps scale x xs).sum ≤ total + error := by
  rw [normalizedGaps_sum]
  have hdiff : lastFrom x xs - x ≤ endpoint - x := by
    linarith
  exact (mul_le_mul_of_nonneg_left hdiff hscale).trans hlength

end Zeta23.GapMatching.OrderedPointGaps
