/-
Copyright (c) 2026.
SPDX-License-Identifier: Apache-2.0

Exact three-state potential for two bad Montgomery--Taylor gap intervals.
All transcendental inequalities are delegated to the interval certificate;
every state-potential and fixed-point calculation here is exact rational
arithmetic.
-/
import Mathlib
import Zeta23.GapMatching.FiniteStateGapPotential

noncomputable section

namespace Zeta23.GapMatching.TwoBandPotentialSafeNumerics

open Zeta23.GapMatching.FiniteStateGapPotential

inductive State
  | good
  | first
  | second
  deriving DecidableEq

def lam : ℝ := 0.999999999
def B : ℝ := 0.000110345
def p : ℝ := 0.0003278

def left1 : ℝ := 1.04093
def right1 : ℝ := 1.07410
def left2 : ℝ := 2.00581
def right2 : ℝ := 2.05431

def j11 : ℝ := 0.0001064
def j12 : ℝ := 0.00005313
def j22 : ℝ := 0

/-- Profile slack reserved for the finite-grid approximation. -/
def shortMargin : ℝ := 0.000000030
def crossMargin : ℝ := 0.000000012
def overlapTolerance : ℝ := 0.000000004

/-- Exact per-gap reward. -/
def A : ℝ := B * (left1 + left2) / 2 + j12

/-- State potentials solving the active transition equations. -/
def phi : State → ℝ
  | .good => 0
  | .first => B * left1 - A
  | .second => -j12

def boundary : ℝ := -(phi .first)

def lengthFloor : State → ℝ
  | .good => 0
  | .first => left1
  | .second => left2

def shortFloor : State → ℝ
  | .good => p
  | .first => 0
  | .second => 0

def longFloor : State → State → ℝ
  | .first, .first => j11
  | .first, .second => j12
  | .second, .first => j12
  | .second, .second => j22
  | _, _ => 0

/-- The part of one transition supplied by length and actual candidate
edges, before adding the telescoping state potential. -/
def physicalFloor (previous current : State) : ℝ :=
  B * lengthFloor current
    + shortFloor current
    + longFloor previous current

/-- The full local dual floor, including the state-potential difference. -/
def transitionFloor (previous current : State) : ℝ :=
  physicalFloor previous current + phi previous - phi current

/-- All nine transition inequalities. -/
theorem transition_certificate (previous current : State) :
    A ≤ transitionFloor previous current := by
  cases previous <;> cases current <;>
    norm_num [A, B, p, left1, left2, j11, j12, j22,
      transitionFloor, physicalFloor, lengthFloor, shortFloor,
      longFloor, phi]

theorem parameter_ranges :
    0 < A ∧ A < 1 ∧ 0 ≤ B ∧ 0 ≤ boundary := by
  norm_num [A, B, left1, left2, j12, boundary, phi]

theorem potential_boundary (state : State) :
    -boundary ≤ phi state := by
  cases state <;>
    norm_num [boundary, phi, A, B, left1, left2, j12]

theorem overlap_margin_arithmetic :
    2 * overlapTolerance ≤ shortMargin ∧
    2 * overlapTolerance ≤ crossMargin := by
  norm_num [overlapTolerance, shortMargin, crossMargin]

/-- A step whose actual physical cost dominates the physical transition floor
supplies the generic local certificate after adding the potential difference
once. -/
theorem localCertificate_of_dominates
    (previous : State) (g : GapDatum State)
    (h : physicalFloor previous g.state
      ≤ stepCost B State.good previous g) :
    LocalCertificate A B State.good phi previous g := by
  unfold LocalCertificate
  calc
    A ≤ transitionFloor previous g.state :=
      transition_certificate previous g.state
    _ = physicalFloor previous g.state
          + phi previous - phi g.state := rfl
    _ ≤ stepCost B State.good previous g
          + phi previous - phi g.state := by
      exact sub_le_sub_right (add_le_add_right h (phi previous))
        (phi g.state)

def deltaLower : ℝ := 0.67250069
def advertised : ℝ := 0.6725391

theorem advertised_lt_exact :
    advertised < (deltaLower - B) / (1 - A) := by
  have hden : 0 < 1 - A := by
    nlinarith [parameter_ranges.1, parameter_ranges.2.1]
  rw [lt_div_iff₀ hden]
  norm_num [advertised, deltaLower, A, B, left1, left2, j12]

theorem fixed_point_improves
    {sigma : ℝ}
    (h : deltaLower + A * sigma - B ≤ sigma) :
    advertised < sigma := by
  have hden : 0 < 1 - A := by
    nlinarith [parameter_ranges.1, parameter_ranges.2.1]
  have hrearranged :
      (deltaLower - B) / (1 - A) ≤ sigma := by
    rw [div_le_iff₀ hden]
    nlinarith
  exact advertised_lt_exact.trans_le hrearranged

end Zeta23.GapMatching.TwoBandPotentialSafeNumerics
