/-
Copyright (c) 2026.
SPDX-License-Identifier: Apache-2.0

Normalized gap list attached to the canonical central ordered vertices.
-/
import Mathlib.Data.List.OfFn
import Zeta23.GapMatching.CentralPathConstructionD
import Zeta23.GapMatching.DWindowLength
import Zeta23.GapMatching.OrderedPointGaps

open Filter Real

noncomputable section

namespace Zeta23.GapMatching.CentralGapGeometryD

open Zeta23
open Zeta23.Assembly
open Zeta23.GapMatching.CentralPathConstructionD
open Zeta23.GapMatching.DWindowLength
open Zeta23.GapMatching.OrderedPointGaps

variable {Z : ZeroConfig} {P : Params} {T : ℝ}

/-- Ordinate of one canonical central vertex. -/
def ordinate (V : OrderedCentralVerticesD Z P T)
    (i : Fin (V.n + 2)) : ℝ :=
  (((V.vertices i).1.1 : ℂ)).im

/-- First retained ordinate. -/
def firstOrdinate (V : OrderedCentralVerticesD Z P T) : ℝ :=
  ordinate V 0

/-- All retained ordinates after the first. -/
def remainingOrdinates
    (V : OrderedCentralVerticesD Z P T) : List ℝ :=
  List.ofFn fun i : Fin (V.n + 1) => ordinate V i.succ

/-- The normalized Gram-grid scale. -/
def gapScale (P : Params) (T : ℝ) : ℝ :=
  P.L T / (2 * Real.pi)

/-- Consecutive central gaps in Gram-grid units. -/
def normalizedGapList
    (V : OrderedCentralVerticesD Z P T) : List ℝ :=
  normalizedGaps (gapScale P T)
    (firstOrdinate V) (remainingOrdinates V)

/-- The full `ofFn` list splits into first and tail. -/
theorem allOrdinates_eq_cons
    (V : OrderedCentralVerticesD Z P T) :
    List.ofFn (ordinate V)
      = firstOrdinate V :: remainingOrdinates V := by
  rw [List.ofFn_succ]
  rfl

/-- A pairwise nondecreasing list satisfies `OrderedFrom`. -/
theorem orderedFrom_of_pairwise :
    ∀ (x : ℝ) (xs : List ℝ),
      (x :: xs).Pairwise (· ≤ ·) → OrderedFrom x xs
  | _, [], _ => by simp [OrderedFrom]
  | x, y :: ys, h => by
      rw [List.pairwise_cons] at h
      refine ⟨h.1 y (by simp), ?_⟩
      exact orderedFrom_of_pairwise y ys h.2

/-- The canonical ordinate list is ordered. -/
theorem orderedFrom_remaining
    (V : OrderedCentralVerticesD Z P T) :
    OrderedFrom (firstOrdinate V) (remainingOrdinates V) := by
  have hpwlt :
      (List.ofFn (ordinate V)).Pairwise (· < ·) := by
    rw [List.pairwise_ofFn]
    intro i j hij
    exact V.strictMono_im hij
  have hpwle :
      (List.ofFn (ordinate V)).Pairwise (· ≤ ·) :=
    hpwlt.imp fun _ _ h => h.le
  rw [allOrdinates_eq_cons] at hpwle
  exact orderedFrom_of_pairwise _ _ hpwle

/-- Every normalized central gap is nonnegative once `L ≥ 0`. -/
theorem normalizedGapList_nonneg
    (V : OrderedCentralVerticesD Z P T)
    (hL : 0 ≤ P.L T) :
    ∀ gap ∈ normalizedGapList V, 0 ≤ gap := by
  apply normalizedGaps_nonneg
  · unfold gapScale
    positivity
  · exact orderedFrom_remaining V

@[simp] theorem normalizedGapList_length
    (V : OrderedCentralVerticesD Z P T) :
    (normalizedGapList V).length = V.n + 1 := by
  unfold normalizedGapList remainingOrdinates
  rw [normalizedGaps_length, List.length_ofFn]

/-- If every tail point is below an endpoint, so is `lastFrom`. -/
theorem lastFrom_le_of_forall_mem :
    ∀ {x endpoint : ℝ} {xs : List ℝ},
      x ≤ endpoint →
      (∀ y ∈ xs, y ≤ endpoint) →
      lastFrom x xs ≤ endpoint
  | _, _, [], hx, _ => by simpa [lastFrom] using hx
  | x, endpoint, y :: ys, _, hall => by
      simp only [lastFrom]
      apply lastFrom_le_of_forall_mem (x := y) (endpoint := endpoint)
      · exact hall y (by simp)
      · intro z hz
        exact hall z (by simp [hz])

/-- The first retained central ordinate lies above `T`. -/
theorem firstOrdinate_ge
    (V : OrderedCentralVerticesD Z P T) :
    T ≤ firstOrdinate V := by
  have hmem := V.central_mem 0
  exact le_of_lt (hmem.1.2.1.trans' (lt_add_of_pos_right _
    (Real.sqrt_pos.2 (by
      have h := hmem.1.2.1
      have hs := Real.sqrt_nonneg T
      linarith))))

/-- Cleaner proof of the same endpoint fact, requiring only `T ≥ 0`. -/
theorem firstOrdinate_ge_of_nonneg
    (V : OrderedCentralVerticesD Z P T) (hT : 0 ≤ T) :
    T ≤ firstOrdinate V := by
  have hmem := V.central_mem 0
  have hs := Real.sqrt_nonneg T
  linarith [hmem.1.2.1]

/-- Every retained central ordinate is at most `2T`. -/
theorem ordinate_le_two_mul
    (V : OrderedCentralVerticesD Z P T)
    (i : Fin (V.n + 2)) :
    ordinate V i ≤ 2 * T := by
  have hmem := V.central_mem i
  have hs := Real.sqrt_nonneg T
  linarith [hmem.1.2.2]

/-- The last retained ordinate is at most `2T`. -/
theorem lastFrom_le_two_mul
    (V : OrderedCentralVerticesD Z P T) :
    lastFrom (firstOrdinate V) (remainingOrdinates V) ≤ 2 * T := by
  apply lastFrom_le_of_forall_mem
  · exact ordinate_le_two_mul V 0
  · intro y hy
    simp only [remainingOrdinates, List.mem_ofFn] at hy
    obtain ⟨i, rfl⟩ := hy
    exact ordinate_le_two_mul V i.succ

/-- At a height where the normalized full span is below the zero count, the
central gap list has total length at most that count. -/
theorem normalizedGapList_sum_le_count
    (V : OrderedCentralVerticesD Z P T)
    (hT : 0 ≤ T)
    (hL : 0 ≤ P.L T)
    (hspan : P.L T * T / (2 * Real.pi)
      ≤ (Z.N T (2 * T) : ℝ)) :
    (normalizedGapList V).sum ≤ (Z.N T (2 * T) : ℝ) := by
  apply normalizedGaps_sum_le
    (endpoint := 2 * T) (total := (Z.N T (2 * T) : ℝ))
    (error := 0)
  · exact lastFrom_le_two_mul V
  · unfold gapScale
    positivity
  · have hfirst := firstOrdinate_ge_of_nonneg V hT
    have hscale : 0 ≤ gapScale P T := by
      unfold gapScale
      positivity
    have hdiff : 2 * T - firstOrdinate V ≤ T := by
      linarith
    have hmul := mul_le_mul_of_nonneg_left hdiff hscale
    unfold gapScale at hmul ⊢
    have heq :
        P.L T / (2 * Real.pi) * T
          = P.L T * T / (2 * Real.pi) := by ring
    rw [heq] at hmul
    nlinarith

/-- Eventual uniform form for every canonical central enumeration. -/
theorem eventually_normalizedGapList_sum_le_count
    (Z : ZeroConfig) (H : PaperInputs Z)
    (P : Params) (hP : P.Valid) (hlam : P.lam < 1) :
    ∀ᶠ T in atTop,
      ∀ V : OrderedCentralVerticesD Z P T,
        (normalizedGapList V).sum
          ≤ (Z.N T (2 * T) : ℝ) := by
  filter_upwards [
      eventually_normalized_span_le_count Z H P hP hlam,
      eventually_ge_atTop (0 : ℝ), eventually_l_pos]
    with T hspan hT hlT
  intro V
  have hL : 0 ≤ P.L T := by
    unfold Params.L
    positivity
  exact normalizedGapList_sum_le_count V hT hL hspan

end Zeta23.GapMatching.CentralGapGeometryD
