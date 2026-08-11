/-
Copyright (c) 2026.
SPDX-License-Identifier: Apache-2.0

Conversion from uniform finite-Gram overlap approximation to the exact
three-state transition floors.
-/
import Mathlib
import Zeta23.GapMatching.FiniteStateGapPotential
import Zeta23.GapMatching.TwoBandPotentialSafeNumerics

noncomputable section

namespace Zeta23.GapMatching.TwoBandPotentialOverlap

open Zeta23.GapMatching.FiniteStateGapPotential
open Zeta23.GapMatching.TwoBandPotentialSafeNumerics

def ofOverlaps
    (state : State) (length shortOverlap longOverlap : ℝ) :
    GapDatum State where
  state := state
  length := length
  shortWeight := shortOverlap ^ 2
  longFromPrev := longOverlap ^ 2

theorem sq_lower_of_close
    {actual profile eps : ℝ}
    (hactual : |actual| ≤ 1)
    (hprofile : |profile| ≤ 1)
    (hclose : |actual - profile| ≤ eps) :
    profile ^ 2 - 2 * eps ≤ actual ^ 2 := by
  have hsum : |actual + profile| ≤ 2 := by
    calc
      |actual + profile| ≤ |actual| + |profile| := abs_add _ _
      _ ≤ 2 := by linarith
  have hprod :
      |actual ^ 2 - profile ^ 2| ≤ 2 * eps := by
    calc
      |actual ^ 2 - profile ^ 2|
          = |actual - profile| * |actual + profile| := by
              rw [show actual ^ 2 - profile ^ 2 =
                (actual - profile) * (actual + profile) by ring,
                abs_mul]
      _ ≤ eps * 2 := mul_le_mul hclose hsum (abs_nonneg _) (by positivity)
      _ = 2 * eps := by ring
  nlinarith [le_abs_self (actual ^ 2 - profile ^ 2), hprod]

/-- Profile conditions sufficient for one transition. -/
structure ProfileStep
    (previous current : State)
    (length profileShort profileLong : ℝ) : Prop where
  length_floor : lengthFloor current ≤ length
  short_floor :
    current = .good →
      p + shortMargin ≤ profileShort ^ 2 + B * length
  long_floor :
    previous ≠ .good → current ≠ .good →
      (previous = .second ∧ current = .second) ∨
        longFloor previous current + crossMargin ≤ profileLong ^ 2

/-- A uniform overlap error below `4e-9` preserves every transition floor. -/
theorem stepDominates_of_profile_close
    {previous current : State}
    {length actualShort profileShort actualLong profileLong eps : ℝ}
    (hprofile : ProfileStep previous current
      length profileShort profileLong)
    (hactualShort : |actualShort| ≤ 1)
    (hprofileShort : |profileShort| ≤ 1)
    (hcloseShort : |actualShort - profileShort| ≤ eps)
    (hactualLong : |actualLong| ≤ 1)
    (hprofileLong : |profileLong| ≤ 1)
    (hcloseLong : |actualLong - profileLong| ≤ eps)
    (heps : eps ≤ overlapTolerance) :
    transitionFloor previous current ≤
      stepCost B State.good previous
        (ofOverlaps current length actualShort actualLong) := by
  have hshortError : 2 * eps ≤ shortMargin := by
    nlinarith [overlap_margin_arithmetic.1]
  have hlongError : 2 * eps ≤ crossMargin := by
    nlinarith [overlap_margin_arithmetic.2]
  have hsquareShort := sq_lower_of_close
    hactualShort hprofileShort hcloseShort
  have hsquareLong := sq_lower_of_close
    hactualLong hprofileLong hcloseLong
  rcases hprofile with ⟨hlength, hshort, hlong⟩
  cases previous <;> cases current
  all_goals
    simp [transitionFloor, lengthFloor, shortFloor, longFloor,
      phi, stepCost, stepWeight, ofOverlaps] at *
  all_goals try nlinarith
  · rcases hlong (by decide) (by decide) with hzero | hbound
    · simp at hzero
    · nlinarith
  · rcases hlong (by decide) (by decide) with hzero | hbound
    · simp at hzero
    · nlinarith
  · rcases hlong (by decide) (by decide) with hzero | hbound
    · simp at hzero
    · nlinarith
  · have hnonneg : 0 ≤ actualLong ^ 2 := sq_nonneg _
    nlinarith

/-- Direct local-certificate wrapper. -/
theorem localCertificate_of_profile_close
    {previous current : State}
    {length actualShort profileShort actualLong profileLong eps : ℝ}
    (hprofile : ProfileStep previous current
      length profileShort profileLong)
    (hactualShort : |actualShort| ≤ 1)
    (hprofileShort : |profileShort| ≤ 1)
    (hcloseShort : |actualShort - profileShort| ≤ eps)
    (hactualLong : |actualLong| ≤ 1)
    (hprofileLong : |profileLong| ≤ 1)
    (hcloseLong : |actualLong - profileLong| ≤ eps)
    (heps : eps ≤ overlapTolerance) :
    LocalCertificate A B State.good phi previous
      (ofOverlaps current length actualShort actualLong) :=
  localCertificate_of_dominates previous _
    (stepDominates_of_profile_close hprofile
      hactualShort hprofileShort hcloseShort
      hactualLong hprofileLong hcloseLong heps)

end Zeta23.GapMatching.TwoBandPotentialOverlap
