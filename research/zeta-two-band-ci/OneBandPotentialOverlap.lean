/-
Copyright (c) 2026.
SPDX-License-Identifier: Apache-2.0

Conversion of coarse sharp-profile bounds into the conservative one-band
finite-state certificate.
-/
import Zeta23.GapMatching.DWindowOverlap
import Zeta23.GapMatching.FiniteStateGapPotential
import Zeta23.GapMatching.OneBandPotentialSafeNumerics

noncomputable section

namespace Zeta23.GapMatching.OneBandPotentialOverlap

open Zeta23.GapMatching.DWindowOverlap
open Zeta23.GapMatching.FiniteStateGapPotential
open Zeta23.GapMatching.OneBandPotentialSafeNumerics

def ofOverlaps
    (state : State) (length shortOverlap longOverlap : ℝ) :
    GapDatum State where
  state := state
  length := length
  shortWeight := shortOverlap ^ 2
  longFromPrev := longOverlap ^ 2

/-- The profile facts required from one classified gap. -/
structure ProfileStep
    (previous current : State)
    (length sharpShort sharpLong : ℝ) : Prop where
  length_nonneg : 0 ≤ length
  bad_range : current = .bad →
    badLeft ≤ length ∧ length ≤ badRight
  good_short : current = .good →
    lengthThreshold ≤ length ∨ sharpAbsFloor ≤ |sharpShort|
  bad_bad_long : previous = .bad → current = .bad →
    sharpAbsFloor ≤ |sharpLong|

private theorem sharpSqFloor_le_sq
    {x : ℝ} (h : sharpAbsFloor ≤ |x|) :
    sharpSqFloor ≤ x ^ 2 := by
  rw [← floor_arithmetic.2.1]
  nlinarith [sq_nonneg (|x| - sharpAbsFloor), sq_abs x]

/-- A `1e-6` uniform overlap approximation leaves far more than the physical
short- and long-edge floors required by the potential. -/
theorem stepDominates_of_profile_close
    {previous current : State}
    {length actualShort sharpShort actualLong sharpLong eps : ℝ}
    (hprofile : ProfileStep previous current length sharpShort sharpLong)
    (hsharpShort : |sharpShort| ≤ 1)
    (hsharpLong : |sharpLong| ≤ 1)
    (hshort : |actualShort - sharpShort| ≤ eps)
    (hlong : |actualLong - sharpLong| ≤ eps)
    (heps0 : 0 ≤ eps)
    (heps : eps ≤ overlapTolerance) :
    transitionFloor previous current ≤
      stepCost B State.good previous
        (ofOverlaps current length actualShort actualLong) := by
  have hshortFloor_of_overlap
      (hmag : sharpAbsFloor ≤ |sharpShort|) :
      finiteSqFloor ≤ actualShort ^ 2 := by
    have hraw := sq_ge_of_abs_sub_le heps0 hshort hsharpShort
      (sharpSqFloor_le_sq hmag)
    have hloss : 2 * eps ≤ 2 * overlapTolerance := by linarith
    unfold finiteSqFloor
    linarith

  have hlongFloor_of_overlap
      (hmag : sharpAbsFloor ≤ |sharpLong|) :
      finiteSqFloor ≤ actualLong ^ 2 := by
    have hraw := sq_ge_of_abs_sub_le heps0 hlong hsharpLong
      (sharpSqFloor_le_sq hmag)
    have hloss : 2 * eps ≤ 2 * overlapTolerance := by linarith
    unfold finiteSqFloor
    linarith

  rcases hprofile with ⟨hlength0, hbadRange, hgoodShort, hbadLong⟩
  cases previous <;> cases current
  · have hphysical :
        p ≤ B * length + actualShort ^ 2 := by
      rcases hgoodShort rfl with hlength | hoverlap
      · have hB : 0 ≤ B := parameter_ranges.2.2.1
        have hcharge := mul_le_mul_of_nonneg_left hlength hB
        have hBthreshold : B * lengthThreshold = p := by
          norm_num [B, lengthThreshold, p]
        rw [hBthreshold] at hcharge
        nlinarith [sq_nonneg actualShort]
      · have hsquare := hshortFloor_of_overlap hoverlap
        have hp := floor_arithmetic.2.2.1
        nlinarith
    simp [transitionFloor, lengthFloor, shortFloor, longFloor,
      phi, stepCost, stepWeight, ofOverlaps]
    nlinarith
  · rcases hbadRange rfl with ⟨hlow, _⟩
    simp [transitionFloor, lengthFloor, shortFloor, longFloor,
      phi, stepCost, stepWeight, ofOverlaps]
    nlinarith
  · have hphysical :
        p ≤ B * length + actualShort ^ 2 := by
      rcases hgoodShort rfl with hlength | hoverlap
      · have hB : 0 ≤ B := parameter_ranges.2.2.1
        have hcharge := mul_le_mul_of_nonneg_left hlength hB
        have hBthreshold : B * lengthThreshold = p := by
          norm_num [B, lengthThreshold, p]
        rw [hBthreshold] at hcharge
        nlinarith [sq_nonneg actualShort]
      · have hsquare := hshortFloor_of_overlap hoverlap
        have hp := floor_arithmetic.2.2.1
        nlinarith
    simp [transitionFloor, lengthFloor, shortFloor, longFloor,
      phi, stepCost, stepWeight, ofOverlaps]
    nlinarith
  · rcases hbadRange rfl with ⟨hlow, _⟩
    have hlongMag := hbadLong rfl rfl
    have hlongSquare := hlongFloor_of_overlap hlongMag
    have hj := floor_arithmetic.2.2.2
    simp [transitionFloor, lengthFloor, shortFloor, longFloor,
      phi, stepCost, stepWeight, ofOverlaps]
    nlinarith

/-- Direct local-certificate wrapper. -/
theorem localCertificate_of_profile_close
    {previous current : State}
    {length actualShort sharpShort actualLong sharpLong eps : ℝ}
    (hprofile : ProfileStep previous current length sharpShort sharpLong)
    (hsharpShort : |sharpShort| ≤ 1)
    (hsharpLong : |sharpLong| ≤ 1)
    (hshort : |actualShort - sharpShort| ≤ eps)
    (hlong : |actualLong - sharpLong| ≤ eps)
    (heps0 : 0 ≤ eps)
    (heps : eps ≤ overlapTolerance) :
    LocalCertificate A B State.good phi previous
      (ofOverlaps current length actualShort actualLong) :=
  localCertificate_of_dominates previous _
    (stepDominates_of_profile_close hprofile hsharpShort hsharpLong
      hshort hlong heps0 heps)

end Zeta23.GapMatching.OneBandPotentialOverlap
