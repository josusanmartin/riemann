/-
Copyright (c) 2026.
SPDX-License-Identifier: Apache-2.0

Stable bridge from a real normalized gap to the generated one-band profile
certificate.  The proof deliberately uses only the stable API aliases; the
large interval/Taylor implementation can change without affecting downstream
modules.
-/
import Zeta23.GapMatching.OneBandSharpProfileAPI
import Zeta23.GapMatching.OneBandPotentialOverlap

noncomputable section

namespace Zeta23.GapMatching.OneBandSharpProfileBridge

open Zeta23.GapMatching.OneBandPotentialSafeNumerics
open Zeta23.GapMatching.OneBandPotentialOverlap
open Zeta23.GapMatching.OneBandSharpProfileAPI

/-- The canonical state associated with one normalized gap. -/
def stateFor (x : ℝ) : State :=
  if badLeft ≤ x ∧ x ≤ badRight then .bad else .good

@[simp] theorem stateFor_eq_bad_iff {x : ℝ} :
    stateFor x = .bad ↔ badLeft ≤ x ∧ x ≤ badRight := by
  simp [stateFor]

@[simp] theorem stateFor_eq_good_iff {x : ℝ} :
    stateFor x = .good ↔ ¬ (badLeft ≤ x ∧ x ≤ badRight) := by
  simp [stateFor]

/-- The generated sharp-profile certificate in the canonical state notation.
`aesop` only instantiates the already-proved exported theorem; no numerical
claim is reproved here. -/
theorem sharpProfileStep
    (previousGap currentGap : ℝ)
    (hcurrent : 0 ≤ currentGap) :
    ProfileStep (stateFor previousGap) (stateFor currentGap)
      currentGap
      (sharpProfile currentGap)
      (sharpProfile (previousGap + currentGap)) := by
  have hcert := profileStepCertificate
  aesop

end Zeta23.GapMatching.OneBandSharpProfileBridge
