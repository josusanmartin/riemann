/-
Copyright (c) 2026.
SPDX-License-Identifier: Apache-2.0

The actual-overlap one-band word on the canonical ordered D-window path.
This module is intentionally quantitative but height-local: the later
asymptotic module supplies a single uniform overlap error tending to zero.
-/
import Zeta23.GapMatching.CanonicalOneBandPathD
import Zeta23.GapMatching.OneBandGapWord
import Zeta23.GapMatching.OneBandSharpProfileBridge
import Zeta23.GapMatching.OneBandPotentialOverlap
import Zeta23.GapMatching.DWindowGramIdentity

noncomputable section

namespace Zeta23.GapMatching.OneBandActualWordD

open Zeta23
open Zeta23.GapMatching.FiniteStateGapPotential
open Zeta23.GapMatching.OneBandGapWord
open Zeta23.GapMatching.OneBandPotentialSafeNumerics
open Zeta23.GapMatching.OneBandPotentialOverlap
open Zeta23.GapMatching.OneBandSharpProfileAPI
open Zeta23.GapMatching.OneBandSharpProfileBridge
open Zeta23.GapMatching.CentralGapGeometryD
open Zeta23.GapMatching.CanonicalOneBandPathD
open Zeta23.GapMatching.DWindowGramIdentity

variable {Z : ZeroConfig} {P : Params} {T : ℝ}

/-- Real normalized overlap on one consecutive edge. -/
def shortOverlap
    (V : OrderedCentralVerticesD Z P T)
    (i : Fin (V.n + 1)) : ℝ :=
  gramOverlap (V.vertices i.castSucc) (V.vertices i.succ)

/-- Real normalized overlap across two consecutive gaps. -/
def longOverlap
    (V : OrderedCentralVerticesD Z P T)
    (i : Fin V.n) : ℝ :=
  gramOverlap (V.vertices (Fin.castSucc (Fin.castSucc i)))
    (V.vertices (Fin.succ (Fin.succ i)))

/-- Total natural-number extension of the short overlap. -/
def shortOverlapNat
    (V : OrderedCentralVerticesD Z P T) (i : ℕ) : ℝ :=
  if hi : i < V.n + 1 then shortOverlap V ⟨i, hi⟩ else 0

/-- Total natural-number extension of the two-gap overlap. -/
def longOverlapNat
    (V : OrderedCentralVerticesD Z P T) (i : ℕ) : ℝ :=
  if hi : i < V.n then longOverlap V ⟨i, hi⟩ else 0

/-- State compatibility between the Boolean path and the profile bridge. -/
theorem stateOf_badFlag
    (V : OrderedCentralVerticesD Z P T)
    {i : ℕ} (hi : i < V.n + 1) :
    stateOf (badFlag V) i = stateFor (gapAtNat V i) := by
  simp [stateOf, badFlag, gapAtNat, hi, stateFor]

/-- Previous-state compatibility for a genuine word index. -/
theorem previousState_badFlag
    (V : OrderedCentralVerticesD Z P T)
    {i : ℕ} (hi : i < V.n + 1) :
    previousState (badFlag V) i =
      stateFor (if i = 0 then 0 else gapAtNat V (i - 1)) := by
  rcases i with _ | i
  · simp [previousState, stateFor, badLeft]
  · have hprev : i < V.n + 1 := by omega
    simp [previousState, stateOf_badFlag V hprev]

/-- The actual-overlap gap datum used by the finite-state potential. -/
def actualDatumAt
    (V : OrderedCentralVerticesD Z P T)
    (i : ℕ) : GapDatum State :=
  datumAt (badFlag V) (gapAtNat V)
    (fun j => shortOverlapNat V j ^ 2)
    (fun j => longOverlapNat V j ^ 2) i

/-- Uniform hypotheses needed to turn the sharp profile into actual finite
Gram overlaps on the first `V.n` gaps. -/
structure UniformOverlapApprox
    (V : OrderedCentralVerticesD Z P T) (eps : ℝ) : Prop where
  eps_le : eps ≤ overlapTolerance
  short_actual_bound : ∀ i : Fin V.n,
    |shortOverlapNat V i| ≤ 1
  short_profile_bound : ∀ i : Fin V.n,
    |sharpProfile (gapAtNat V i)| ≤ 1
  short_close : ∀ i : Fin V.n,
    |shortOverlapNat V i - sharpProfile (gapAtNat V i)| ≤ eps
  long_actual_bound : ∀ i : Fin V.n,
    |longOverlapNat V i| ≤ 1
  long_profile_bound : ∀ i : Fin V.n,
    |sharpProfile (gapAtNat V i + gapAtNat V (i + 1))| ≤ 1
  long_close : ∀ i : Fin V.n,
    |longOverlapNat V i
      - sharpProfile (gapAtNat V i + gapAtNat V (i + 1))| ≤ eps

/-- Every actual datum in the retained word satisfies the local potential
certificate. -/
theorem localCertificate_actualDatum
    (V : OrderedCentralVerticesD Z P T)
    {eps : ℝ} (H : UniformOverlapApprox V eps)
    (hL : 0 ≤ P.L T)
    {i : ℕ} (hi : i < V.n) :
    LocalCertificate A B State.good phi
      (previousState (badFlag V) i)
      (actualDatumAt V i) := by
  have higap : i < V.n + 1 := by omega
  have hgap0 : 0 ≤ gapAtNat V i := by
    simp [gapAtNat, higap, gapAt_nonneg V hL]
  let previousGap : ℝ := if i = 0 then 0 else gapAtNat V (i - 1)
  have hprofile := sharpProfileStep previousGap (gapAtNat V i) hgap0
  have hstateCurrent := stateOf_badFlag V higap
  have hstatePrevious := previousState_badFlag V higap
  rw [hstateCurrent, hstatePrevious]
  unfold actualDatumAt datumAt
  by_cases hi0 : i = 0
  · subst i
    simp [previousGap, shortOverlapNat, longOverlapNat,
      hprofile, H.eps_le]
    exact localCertificate_of_profile_close hprofile
      (H.short_actual_bound ⟨0, hi⟩)
      (H.short_profile_bound ⟨0, hi⟩)
      (H.short_close ⟨0, hi⟩)
      (by simp) (by simp) (by simp) H.eps_le
  · have him1 : i - 1 < V.n := by omega
    have hsum :
        previousGap + gapAtNat V i =
          gapAtNat V (i - 1) + gapAtNat V i := by
      simp [previousGap, hi0]
    simp only [hi0, if_false]
    rw [hsum]
    exact localCertificate_of_profile_close hprofile
      (H.short_actual_bound ⟨i, hi⟩)
      (H.short_profile_bound ⟨i, hi⟩)
      (H.short_close ⟨i, hi⟩)
      (H.long_actual_bound ⟨i - 1, him1⟩)
      (by
        simpa [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 hi0)] using
          H.long_profile_bound ⟨i - 1, him1⟩)
      (by
        simpa [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 hi0)] using
          H.long_close ⟨i - 1, him1⟩)
      H.eps_le

/-- The first `V.n` actual gaps form a valid finite-state word.  This retains
all short candidates except the final gap and all long candidates except the
last start; omitting nonnegative candidate energy is harmless downstream. -/
theorem valid_actual_word
    (V : OrderedCentralVerticesD Z P T)
    {eps : ℝ} (H : UniformOverlapApprox V eps)
    (hL : 0 ≤ P.L T) :
    ValidPath A B State.good phi State.good
      (word (badFlag V) (gapAtNat V)
        (fun i => shortOverlapNat V i ^ 2)
        (fun i => longOverlapNat V i ^ 2) V.n) := by
  apply valid_word
  intro i
  by_cases hi : i < V.n
  · exact localCertificate_actualDatum V H hL hi
  · -- This branch is not reached by the finite word recursion.  A harmless
    -- total extension keeps the local function convenient.
    simp [actualDatumAt, datumAt, previousState, stateOf, badFlag,
      gapAtNat, shortOverlapNat, longOverlapNat, hi, LocalCertificate,
      A, B, p, j, phi, physicalFloor, transitionFloor, stepCost, stepWeight]

end Zeta23.GapMatching.OneBandActualWordD
