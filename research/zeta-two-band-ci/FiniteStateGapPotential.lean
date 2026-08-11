/-
Copyright (c) 2026.
SPDX-License-Identifier: Apache-2.0

Finite-state telescoping potential for gap-matching certificates.

The state type may distinguish several bad overlap intervals. The underlying
candidate graph still uses only "good versus bad": good gaps carry short
edges, and two consecutive bad gaps carry a long edge. State-dependent
potentials and transition floors recover more information than a single bad
state.
-/
import Mathlib

noncomputable section

namespace Zeta23.GapMatching.FiniteStateGapPotential

variable {State : Type*} [DecidableEq State]

/-- One normalized gap and the actual finite Gram weights attached to it. -/
structure GapDatum (State : Type*) where
  state : State
  length : ℝ
  shortWeight : ℝ
  longFromPrev : ℝ

/-- Candidate weight: short on a good current gap, long when both states are
bad. -/
def stepWeight
    (good : State) (previous : State) (g : GapDatum State) : ℝ :=
  (if g.state = good then g.shortWeight else 0)
    + (if previous = good then 0
       else if g.state = good then 0
       else g.longFromPrev)

/-- Length charge plus candidate weight. -/
def stepCost
    (B : ℝ) (good : State) (previous : State)
    (g : GapDatum State) : ℝ :=
  B * g.length + stepWeight good previous g

/-- Local potential certificate. -/
def LocalCertificate
    (A B : ℝ) (good : State) (phi : State → ℝ)
    (previous : State) (g : GapDatum State) : Prop :=
  A ≤ stepCost B good previous g + phi previous - phi g.state

/-- Validity along a finite word. -/
def ValidPath
    (A B : ℝ) (good : State) (phi : State → ℝ) :
    State → List (GapDatum State) → Prop
  | _, [] => True
  | previous, g :: rest =>
      LocalCertificate A B good phi previous g ∧
        ValidPath A B good phi g.state rest

def candidateWeight
    (good : State) : State → List (GapDatum State) → ℝ
  | _, [] => 0
  | previous, g :: rest =>
      stepWeight good previous g
        + candidateWeight good g.state rest

def totalLength : List (GapDatum State) → ℝ
  | [] => 0
  | g :: rest => g.length + totalLength rest

def totalCost
    (B : ℝ) (good : State) :
    State → List (GapDatum State) → ℝ
  | _, [] => 0
  | previous, g :: rest =>
      stepCost B good previous g
        + totalCost B good g.state rest

def finalState : State → List (GapDatum State) → State
  | previous, [] => previous
  | _, g :: rest => finalState g.state rest

/-- The arbitrary state potential telescopes. -/
theorem telescope
    {A B : ℝ} (good : State) (phi : State → ℝ)
    (previous : State) (gaps : List (GapDatum State))
    (hvalid : ValidPath A B good phi previous gaps) :
    A * (gaps.length : ℝ) ≤
      totalCost B good previous gaps
        + phi previous - phi (finalState previous gaps) := by
  induction gaps generalizing previous with
  | nil => simp [totalCost, finalState]
  | cons g rest ih =>
      rcases hvalid with ⟨hstep, hrest⟩
      have htail := ih g.state hrest
      simp only [List.length_cons, Nat.cast_add, Nat.cast_one,
        totalCost, finalState]
      nlinarith [hstep]

theorem totalCost_eq
    (B : ℝ) (good previous : State)
    (gaps : List (GapDatum State)) :
    totalCost B good previous gaps =
      B * totalLength gaps + candidateWeight good previous gaps := by
  induction gaps generalizing previous with
  | nil => simp [totalCost, totalLength, candidateWeight]
  | cons g rest ih =>
      simp [totalCost, totalLength, candidateWeight, stepCost, ih]
      ring

/-- If every state potential is at least `-boundary`, a word beginning in the
good state loses at most that boundary constant. -/
theorem candidateWeight_lower
    {A B boundary : ℝ}
    (good : State) (phi : State → ℝ)
    (hgood : phi good = 0)
    (hboundary : ∀ state, -boundary ≤ phi state)
    (gaps : List (GapDatum State))
    (hvalid : ValidPath A B good phi good gaps) :
    A * (gaps.length : ℝ) - boundary - B * totalLength gaps
      ≤ candidateWeight good good gaps := by
  have hmain := telescope good phi good gaps hvalid
  have hfinal := hboundary (finalState good gaps)
  rw [hgood] at hmain
  rw [totalCost_eq] at hmain
  nlinarith

/-- Error-explicit version used by the zeta seam. -/
theorem candidateWeight_lower_with_errors
    {A B boundary fullSimple centralSimple gapCount totalN
      guardError countError lengthError W : ℝ}
    (good : State) (phi : State → ℝ)
    (hA0 : 0 ≤ A) (hB0 : 0 ≤ B)
    (hgood : phi good = 0)
    (hboundary : ∀ state, -boundary ≤ phi state)
    (gaps : List (GapDatum State))
    (hvalid : ValidPath A B good phi good gaps)
    (hgapCount : gapCount = (gaps.length : ℝ))
    (hguard : fullSimple - guardError ≤ centralSimple)
    (hcount : centralSimple - countError ≤ gapCount)
    (hlength : totalLength gaps ≤ totalN + lengthError)
    (hweight : candidateWeight good good gaps ≤ W) :
    A * fullSimple - B * totalN
      - (A * guardError + A * countError
          + B * lengthError + boundary)
      ≤ W := by
  have hword := candidateWeight_lower
    good phi hgood hboundary gaps hvalid
  rw [← hgapCount] at hword
  have hcount' : fullSimple - guardError - countError ≤ gapCount := by
    linarith
  have hcountA := mul_le_mul_of_nonneg_left hcount' hA0
  have hlengthB := mul_le_mul_of_nonneg_left hlength hB0
  nlinarith

end Zeta23.GapMatching.FiniteStateGapPotential
