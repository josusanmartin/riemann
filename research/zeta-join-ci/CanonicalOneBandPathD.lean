/-
Copyright (c) 2026.
SPDX-License-Identifier: Apache-2.0

Canonical Boolean one-band path attached to the ordered central simple zeros.
This module contains no analytic overlap estimate: it fixes the exact gap
indexing and constructs the path object consumed by the matching theorem.
-/
import Zeta23.GapMatching.CentralGapGeometryD
import Zeta23.GapMatching.OneBandPotentialSafeNumerics
import Zeta23.GapMatching.TwoBandGapMatchingDPath

noncomputable section

namespace Zeta23.GapMatching.CanonicalOneBandPathD

open Zeta23
open Zeta23.GapMatching.CentralGapGeometryD
open Zeta23.GapMatching.CentralPathConstructionD
open Zeta23.GapMatching.OneBandPotentialSafeNumerics
open Zeta23.GapMatching.TwoBandGapMatchingDPath

variable {Z : ZeroConfig} {P : Params} {T : ℝ}

/-- The `i`th consecutive central gap, in Gram-grid units. -/
def gapAt (V : OrderedCentralVerticesD Z P T)
    (i : Fin (V.n + 1)) : ℝ :=
  gapScale P T *
    (ordinate V i.succ - ordinate V i.castSucc)

/-- Total natural-number extension of `gapAt`; indices after the final gap are
set to zero. -/
def gapAtNat (V : OrderedCentralVerticesD Z P T) (i : ℕ) : ℝ :=
  if hi : i < V.n + 1 then gapAt V ⟨i, hi⟩ else 0

/-- A gap is bad precisely when it lies in the certified one-band interval. -/
def badFlag (V : OrderedCentralVerticesD Z P T) (i : ℕ) : Bool :=
  if hi : i < V.n + 1 then
    decide (badLeft ≤ gapAt V ⟨i, hi⟩ ∧
      gapAt V ⟨i, hi⟩ ≤ badRight)
  else false

/-- Every non-bad gap carries a short candidate edge. -/
def shortFlag (V : OrderedCentralVerticesD Z P T) (i : ℕ) : Bool :=
  !(badFlag V i)

@[simp] theorem shortFlag_eq_true_iff
    (V : OrderedCentralVerticesD Z P T) (i : ℕ) :
    shortFlag V i = true ↔ badFlag V i = false := by
  cases h : badFlag V i <;> simp [shortFlag, h]

@[simp] theorem shortFlag_eq_false_iff
    (V : OrderedCentralVerticesD Z P T) (i : ℕ) :
    shortFlag V i = false ↔ badFlag V i = true := by
  cases h : badFlag V i <;> simp [shortFlag, h]

/-- The bad flag is false beyond the final gap. -/
theorem badFlag_eq_false_of_le
    (V : OrderedCentralVerticesD Z P T) {i : ℕ}
    (hi : V.n + 1 ≤ i) :
    badFlag V i = false := by
  simp [badFlag, not_lt.mpr hi]

/-- Characterization of a genuine bad gap. -/
theorem badFlag_eq_true_iff
    (V : OrderedCentralVerticesD Z P T) {i : ℕ} :
    badFlag V i = true ↔
      ∃ hi : i < V.n + 1,
        badLeft ≤ gapAt V ⟨i, hi⟩ ∧
          gapAt V ⟨i, hi⟩ ≤ badRight := by
  by_cases hi : i < V.n + 1
  · simp [badFlag, hi]
  · simp [badFlag, hi]

/-- Characterization of a genuine good gap. -/
theorem badFlag_eq_false_iff
    (V : OrderedCentralVerticesD Z P T) {i : ℕ} :
    badFlag V i = false ↔
      V.n + 1 ≤ i ∨
        ∃ hi : i < V.n + 1,
          ¬ (badLeft ≤ gapAt V ⟨i, hi⟩ ∧
            gapAt V ⟨i, hi⟩ ≤ badRight) := by
  by_cases hi : i < V.n + 1
  · simp [badFlag, hi, not_le]
  · have hle : V.n + 1 ≤ i := not_lt.mp hi
    simp [badFlag, hi, hle]

/-- Consecutive gaps are nonnegative when the Gram scale is nonnegative. -/
theorem gapAt_nonneg
    (V : OrderedCentralVerticesD Z P T)
    (hL : 0 ≤ P.L T) (i : Fin (V.n + 1)) :
    0 ≤ gapAt V i := by
  have him : ordinate V i.castSucc < ordinate V i.succ :=
    V.strictMono_im (Fin.castSucc_lt_succ i)
  have hscale : 0 ≤ gapScale P T := by
    unfold gapScale
    positivity
  unfold gapAt
  exact mul_nonneg hscale (sub_nonneg.mpr him.le)

/-- The canonical path fed to the path-forest matching theorem. -/
def canonicalPathData
    (V : OrderedCentralVerticesD Z P T) :
    PathDataD Z P T where
  n := V.n
  U := badFlag V
  short := shortFlag V
  disjoint := by
    intro i hi
    exact (shortFlag_eq_true_iff V i).mp hi
  vertices := V.vertices

@[simp] theorem canonicalPathData_n
    (V : OrderedCentralVerticesD Z P T) :
    (canonicalPathData V).n = V.n := rfl

@[simp] theorem canonicalPathData_U
    (V : OrderedCentralVerticesD Z P T) (i : ℕ) :
    (canonicalPathData V).U i = badFlag V i := rfl

@[simp] theorem canonicalPathData_short
    (V : OrderedCentralVerticesD Z P T) (i : ℕ) :
    (canonicalPathData V).short i = shortFlag V i := rfl

@[simp] theorem canonicalPathData_vertices
    (V : OrderedCentralVerticesD Z P T) :
    (canonicalPathData V).vertices = V.vertices := rfl

end Zeta23.GapMatching.CanonicalOneBandPathD
