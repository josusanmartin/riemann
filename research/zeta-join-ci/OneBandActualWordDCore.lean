/-
Copyright (c) 2026.
SPDX-License-Identifier: Apache-2.0

Bounded actual-overlap one-band word on the canonical ordered D-window path.
-/
import Zeta23.GapMatching.CanonicalOneBandPathD
import Zeta23.GapMatching.OneBandGapWordBounded
import Zeta23.GapMatching.OneBandSharpProfileBridge
import Zeta23.GapMatching.OneBandPotentialOverlap
import Zeta23.GapMatching.DWindowGramIdentity

noncomputable section

namespace Zeta23.GapMatching.OneBandActualWordDCore

open Zeta23
open Zeta23.GapMatching.FiniteStateGapPotential
open Zeta23.GapMatching.OneBandGapWord
open Zeta23.GapMatching.OneBandGapWordBounded
open Zeta23.GapMatching.OneBandPotentialSafeNumerics
open Zeta23.GapMatching.OneBandPotentialOverlap
open Zeta23.GapMatching.OneBandSharpProfileAPI
open Zeta23.GapMatching.OneBandSharpProfileBridge
open Zeta23.GapMatching.CentralGapGeometryD
open Zeta23.GapMatching.CanonicalOneBandPathD
open Zeta23.GapMatching.DWindowGramIdentity

variable {Z : ZeroConfig} {P : Params} {T : ℝ}

def shortOverlap
    (V : OrderedCentralVerticesD Z P T)
    (i : Fin (V.n + 1)) : ℝ :=
  gramOverlap (V.vertices i.castSucc) (V.vertices i.succ)

def longOverlap
    (V : OrderedCentralVerticesD Z P T)
    (i : Fin V.n) : ℝ :=
  gramOverlap (V.vertices (Fin.castSucc (Fin.castSucc i)))
    (V.vertices (Fin.succ (Fin.succ i)))

def shortOverlapNat
    (V : OrderedCentralVerticesD Z P T) (i : ℕ) : ℝ :=
  if hi : i < V.n + 1 then shortOverlap V ⟨i, hi⟩ else 0

def longOverlapNat
    (V : OrderedCentralVerticesD Z P T) (i : ℕ) : ℝ :=
  if hi : i < V.n then longOverlap V ⟨i, hi⟩ else 0

/-- Boolean-state compatibility on a genuine gap. -/
theorem stateOf_badFlag
    (V : OrderedCentralVerticesD Z P T)
    {i : ℕ} (hi : i < V.n + 1) :
    stateOf (badFlag V) i = stateFor (gapAtNat V i) := by
  simp [stateOf, badFlag, gapAtNat, hi, stateFor]

/-- Previous-state compatibility on a genuine retained gap. -/
theorem previousState_badFlag
    (V : OrderedCentralVerticesD Z P T)
    {i : ℕ} (hi : i < V.n + 1) :
    previousState (badFlag V) i =
      stateFor (if i = 0 then 0 else gapAtNat V (i - 1)) := by
  rcases i with _ | i
  · simp [previousState, stateFor, badLeft]
  · have hprev : i < V.n + 1 := by omega
    simpa using stateOf_badFlag V hprev

/-- Uniform finite/full/sharp overlap comparison on all retained starts. -/
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

/-- The actual datum used at one retained index. -/
def actualDatumAt
    (V : OrderedCentralVerticesD Z P T) (i : ℕ) : GapDatum State :=
  datumAt (badFlag V) (gapAtNat V)
    (fun j => shortOverlapNat V j ^ 2)
    (fun j => longOverlapNat V j ^ 2) i

/-- One retained actual datum satisfies the local potential certificate. -/
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
  have hcur := stateOf_badFlag V higap
  have hprev := previousState_badFlag V higap
  change LocalCertificate A B State.good phi
    (previousState (badFlag V) i)
    (datumAt (badFlag V) (gapAtNat V)
      (fun j => shortOverlapNat V j ^ 2)
      (fun j => longOverlapNat V j ^ 2) i)
  rw [hcur, hprev]
  by_cases hi0 : i = 0
  · subst i
    simpa [previousGap] using
      (localCertificate_of_profile_close hprofile
        (H.short_actual_bound ⟨0, hi⟩)
        (H.short_profile_bound ⟨0, hi⟩)
        (H.short_close ⟨0, hi⟩)
        (by norm_num) (by norm_num) (by norm_num) H.eps_le)
  · have him1 : i - 1 < V.n := by omega
    have hone : i - 1 + 1 = i := Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 hi0)
    simpa [previousGap, hi0, hone] using
      (localCertificate_of_profile_close hprofile
        (H.short_actual_bound ⟨i, hi⟩)
        (H.short_profile_bound ⟨i, hi⟩)
        (H.short_close ⟨i, hi⟩)
        (H.long_actual_bound ⟨i - 1, him1⟩)
        (H.long_profile_bound ⟨i - 1, him1⟩)
        (H.long_close ⟨i - 1, him1⟩)
        H.eps_le)

/-- Validity of the actual-overlap word on the first `V.n` gaps. -/
theorem valid_actual_word
    (V : OrderedCentralVerticesD Z P T)
    {eps : ℝ} (H : UniformOverlapApprox V eps)
    (hL : 0 ≤ P.L T) :
    ValidPath A B State.good phi State.good
      (word (badFlag V) (gapAtNat V)
        (fun i => shortOverlapNat V i ^ 2)
        (fun i => longOverlapNat V i ^ 2) V.n) := by
  apply valid_word_bounded
  intro i hi
  exact localCertificate_actualDatum V H hL hi

end Zeta23.GapMatching.OneBandActualWordDCore
