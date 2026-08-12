/-
Copyright (c) 2026.
SPDX-License-Identifier: Apache-2.0

A deliberately conservative two-state gap potential.  The constants are
chosen with large analytic margins so that the final Fourier-overlap estimates
can be proved with coarse rational trigonometric bounds.
-/
import Mathlib
import Zeta23.GapMatching.FiniteStateGapPotential

noncomputable section

namespace Zeta23.GapMatching.OneBandPotentialSafeNumerics

open Zeta23.GapMatching.FiniteStateGapPotential

inductive State
  | good
  | bad
  deriving DecidableEq

/-- Fixed bandwidth, just below one. -/
def lam : ℝ := 0.999999999

/-- Length charge. -/
def B : ℝ := 1 / 1000000

/-- Short-edge floor on a good gap. -/
def p : ℝ := 1 / 500000

/-- The sole bad interval surrounds the first zero of the sharp profile. -/
def badLeft : ℝ := 33 / 32
def badRight : ℝ := 35 / 32

/-- Gaps at least this long pay the short-edge floor from length alone. -/
def lengthThreshold : ℝ := 2

/-- Exact per-gap reward and bad-bad long-edge floor. -/
def A : ℝ := 97 / 64000000
def j : ℝ := 31 / 64000000

/-- The bad-state potential. -/
def phi : State → ℝ
  | .good => 0
  | .bad => -j

def boundary : ℝ := j

def lengthFloor : State → ℝ
  | .good => 0
  | .bad => badLeft

def shortFloor : State → ℝ
  | .good => p
  | .bad => 0

def longFloor : State → State → ℝ
  | .bad, .bad => j
  | _, _ => 0

def transitionFloor (previous current : State) : ℝ :=
  B * lengthFloor current
    + shortFloor current
    + longFloor previous current
    + phi previous - phi current

/-- All four state transitions satisfy the exact local certificate. -/
theorem transition_certificate (previous current : State) :
    A ≤ transitionFloor previous current := by
  cases previous <;> cases current <;>
    norm_num [A, B, p, j, badLeft, transitionFloor,
      lengthFloor, shortFloor, longFloor, phi]

theorem parameter_ranges :
    0 < A ∧ A < 1 ∧ 0 ≤ B ∧ 0 ≤ boundary := by
  norm_num [A, B, boundary, j]

theorem potential_boundary (state : State) :
    -boundary ≤ phi state := by
  cases state <;> norm_num [boundary, phi, j]

/-- A convenient sharp-profile magnitude floor. -/
def sharpAbsFloor : ℝ := 1 / 300

def sharpSqFloor : ℝ := 1 / 90000

/-- Total full-grid plus ramp approximation budget. -/
def overlapTolerance : ℝ := 1 / 1000000

/-- The squared-overlap floor after the approximation loss. -/
def finiteSqFloor : ℝ := sharpSqFloor - 2 * overlapTolerance

theorem floor_arithmetic :
    0 ≤ overlapTolerance ∧
    sharpAbsFloor ^ 2 = sharpSqFloor ∧
    p ≤ finiteSqFloor ∧
    j ≤ finiteSqFloor := by
  norm_num [overlapTolerance, sharpAbsFloor, sharpSqFloor,
    finiteSqFloor, p, j]

/-- A step whose physical cost dominates the exact transition floor gives the
abstract local certificate. -/
theorem localCertificate_of_dominates
    (previous : State) (g : GapDatum State)
    (h : transitionFloor previous g.state
      ≤ stepCost B State.good previous g) :
    LocalCertificate A B State.good phi previous g :=
  (transition_certificate previous g.state).trans h

/-- A safe lower bound for the fixed-window baseline. -/
def deltaLower : ℝ := 0.67250069

/-- Rational score intended for the first fully formal submission. -/
def advertised : ℝ := 0.672500708

theorem advertised_lt_exact :
    advertised < (deltaLower - B) / (1 - A) := by
  have hden : 0 < 1 - A := by
    nlinarith [parameter_ranges.1, parameter_ranges.2.1]
  rw [lt_div_iff₀ hden]
  norm_num [advertised, deltaLower, A, B]

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

end Zeta23.GapMatching.OneBandPotentialSafeNumerics
