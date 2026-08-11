/-
Copyright (c) 2026.
SPDX-License-Identifier: Apache-2.0

Exact endpoint identity between the full finite-state word weight and the
candidate starts representable by a path with one fewer start than gaps.
-/
import Zeta23.GapMatching.FiniteStateGapPotential

noncomputable section

namespace Zeta23.GapMatching.FiniteStatePathWeight

open Zeta23.GapMatching.FiniteStateGapPotential

variable {State : Type*} [DecidableEq State]

/-- Physical candidate weight represented at path starts.  The short edge of
the final gap is omitted, while the final adjacent bad-bad long edge remains
represented by the preceding start. -/
def pathWeight (good : State) : List (GapDatum State) → ℝ
  | [] => 0
  | [_] => 0
  | g :: h :: rest =>
      (if g.state = good then g.shortWeight else 0)
        + (if g.state = good then 0
           else if h.state = good then 0
           else h.longFromPrev)
        + pathWeight good (h :: rest)
termination_by gaps => gaps.length

/-- The omitted final short edge. -/
def finalShort (good : State) : List (GapDatum State) → ℝ
  | [] => 0
  | [g] => if g.state = good then g.shortWeight else 0
  | _ :: h :: rest => finalShort good (h :: rest)
termination_by gaps => gaps.length

/-- Recursive expansion of `candidateWeight` after the first gap. -/
theorem candidateWeight_cons_cons
    (good previous : State) (g h : GapDatum State)
    (rest : List (GapDatum State)) :
    candidateWeight good previous (g :: h :: rest)
      = stepWeight good previous g
          + candidateWeight good g.state (h :: rest) := by
  rfl

/-- Starting in the good state suppresses the nonexistent long edge before
the first gap. -/
theorem stepWeight_initial (good : State) (g : GapDatum State) :
    stepWeight good good g
      = (if g.state = good then g.shortWeight else 0) := by
  simp [stepWeight]

/-- Full word weight equals path-start weight plus one endpoint short edge. -/
theorem candidateWeight_eq_path_add_final
    (good : State) : ∀ gaps : List (GapDatum State),
    candidateWeight good good gaps
      = pathWeight good gaps + finalShort good gaps
  | [] => by
      simp [candidateWeight, pathWeight, finalShort]
  | [g] => by
      simp [candidateWeight, pathWeight, finalShort, stepWeight]
  | g :: h :: rest => by
      rw [candidateWeight_cons_cons]
      simp only [stepWeight_initial, pathWeight, finalShort]
      have ih := candidateWeight_eq_path_add_final good (h :: rest)
      change candidateWeight good good (h :: rest)
        = pathWeight good (h :: rest) + finalShort good (h :: rest)
        at ih
      rw [show candidateWeight good g.state (h :: rest)
          = (if h.state = good then h.shortWeight else 0)
              + (if g.state = good then 0
                 else if h.state = good then 0
                 else h.longFromPrev)
              + candidateWeight good h.state rest by
            rfl]
      rw [show candidateWeight good good (h :: rest)
          = (if h.state = good then h.shortWeight else 0)
              + candidateWeight good h.state rest by
            simp [candidateWeight, stepWeight]] at ih
      nlinarith
termination_by gaps => gaps.length

/-- A pointwise unit bound controls the sole omitted endpoint. -/
theorem finalShort_le_one
    (good : State) : ∀ gaps : List (GapDatum State),
    (∀ g ∈ gaps, g.shortWeight ≤ 1) → finalShort good gaps ≤ 1
  | [], _ => by simp [finalShort]
  | [g], h => by
      have hg := h g (by simp)
      simp [finalShort]
      split <;> linarith
  | g :: h :: rest, hall => by
      apply finalShort_le_one good (h :: rest)
      intro x hx
      exact hall x (by simp [hx])
termination_by gaps => gaps.length

/-- Endpoint-safe path comparison. -/
theorem candidateWeight_le_path_add_one
    (good : State) (gaps : List (GapDatum State))
    (hshort : ∀ g ∈ gaps, g.shortWeight ≤ 1) :
    candidateWeight good good gaps ≤ pathWeight good gaps + 1 := by
  rw [candidateWeight_eq_path_add_final]
  exact add_le_add_left (finalShort_le_one good gaps hshort)
    (pathWeight good gaps)

end Zeta23.GapMatching.FiniteStatePathWeight
