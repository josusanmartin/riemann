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
  have heps0 : 0 ≤ eps := (abs_nonneg (actual - profile)).trans hclose
  have hsum : |actual + profile| ≤ 2 := by
    rw [← Real.norm_eq_abs, ← Real.norm_eq_abs, ← Real.norm_eq_abs]
    calc
      ‖actual + profile‖ ≤ ‖actual‖ + ‖profile‖ := norm_add_le _ _
      _ ≤ 2 := by
        simpa [Real.norm_eq_abs] using add_le_add hactual hprofile
  have hprod :
      |actual ^ 2 - profile ^ 2| ≤ 2 * eps := by
    calc
      |actual ^ 2 - profile ^ 2|
          = |actual - profile| * |actual + profile| := by
              rw [show actual ^ 2 - profile ^ 2 =
                (actual - profile) * (actual + profile) by ring,
                abs_mul]
      _ ≤ eps * 2 :=
            mul_le_mul hclose hsum (abs_nonneg _) heps0
      _ = 2 * eps := by ring
  have hneg := (abs_le.mp hprod).1
  nlinarith

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

/-- A uniform overlap error below `4e-9` preserves the physical length-and-
overlap floor. The state potential is added only afterwards by
`localCertificate_of_dominates`. -/
theorem physicalFloorDominates_of_profile_close
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
    physicalFloor previous current ≤
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
  have hB0 : 0 ≤ B := parameter_ranges.2.2.1
  have hlengthB :=
    mul_le_mul_of_nonneg_left hprofile.length_floor hB0
  rcases hprofile with ⟨hlength, hshort, hlong⟩
  cases previous <;> cases current
  all_goals
    simp [physicalFloor, lengthFloor, shortFloor, longFloor,
      stepCost, stepWeight, ofOverlaps] at hlength hlengthB hshort hlong ⊢
  all_goals
    nlinarith [sq_nonneg actualShort, sq_nonneg actualLong]

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
    (physicalFloorDominates_of_profile_close hprofile
      hactualShort hprofileShort hcloseShort
      hactualLong hprofileLong hcloseLong heps)

end Zeta23.GapMatching.TwoBandPotentialOverlap
