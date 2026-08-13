/-
Copyright (c) 2026.
SPDX-License-Identifier: Apache-2.0

Elementary floor geometry for the finite D-window grid.
-/
import Zeta23.GapMatching.CentralGapGeometryD
import Zeta23.ThmD.ZeroSideD

open Filter Real

noncomputable section

namespace Zeta23.GapMatching.DWindowGridGeometry

open Zeta23
open Zeta23.ThmD
open Zeta23.GapMatching.CentralPathConstructionD
open Zeta23.GapMatching.CentralGapGeometryD

variable {Z : ZeroConfig} {P : Params} {T : ℝ}

/-- The last retained grid point lies less than one mesh below `2T`. -/
theorem grid_floor_lower
    (hL : 0 < P.L T) :
    T - 2 * Real.pi / P.L T
      < (P.d T : ℝ) * (2 * Real.pi / P.L T) := by
  have hx :
      P.L T * T / (2 * Real.pi) < (P.d T : ℝ) + 1 := by
    simpa [Params.d] using
      (Nat.lt_floor_add_one
        (P.L T * T / (2 * Real.pi) : ℝ))
  have hh : 0 < 2 * Real.pi / P.L T := by positivity
  have hmul := mul_lt_mul_of_pos_right hx hh
  have hleft :
      P.L T * T / (2 * Real.pi)
          * (2 * Real.pi / P.L T) = T := by
    field_simp [hL.ne', Real.pi_ne_zero]
    ring
  have hright :
      ((P.d T : ℝ) + 1) * (2 * Real.pi / P.L T)
        = (P.d T : ℝ) * (2 * Real.pi / P.L T)
            + 2 * Real.pi / P.L T := by ring
  rw [hleft, hright] at hmul
  linarith

/-- A retained central vertex has a unit left guard once `sqrt T >= 1`. -/
theorem central_left_guard_one
    (V : OrderedCentralVerticesD Z P T)
    (hD : 1 ≤ D0 T)
    (i : Fin (V.n + 2)) :
    T + 1 ≤ ordinate V i := by
  have hmem := V.central_mem i
  linarith [hmem.1.2.1]

/-- A retained central vertex has a unit right grid guard once the central
`sqrt T` guard absorbs one unit plus the mesh floor loss. -/
theorem central_right_guard_one
    (V : OrderedCentralVerticesD Z P T)
    (hL : 0 < P.L T)
    (hD : 1 + 2 * Real.pi / P.L T ≤ D0 T)
    (i : Fin (V.n + 2)) :
    ordinate V i + 1
      ≤ T + (P.d T : ℝ) * (2 * Real.pi / P.L T) := by
  have hmem := V.central_mem i
  have hfloor := grid_floor_lower (P := P) (T := T) hL
  linarith [hmem.1.2.2]

/-- Eventually every retained central vertex is one unit from both omitted
sides of the finite grid. -/
theorem eventually_central_unit_guards
    (P : Params) (hP : P.Valid) :
    ∀ᶠ T in atTop,
      ∀ (V : OrderedCentralVerticesD Z P T)
        (i : Fin (V.n + 2)),
        T + 1 ≤ ordinate V i ∧
          ordinate V i + 1
            ≤ T + (P.d T : ℝ)
                * (2 * Real.pi / P.L T) := by
  filter_upwards [
      (tendsto_L hP).eventually_ge_atTop (2 * Real.pi),
      eventually_ge_atTop (4 : ℝ)]
    with T hLbig hTbig
  have hL : 0 < P.L T :=
    (show 0 < 2 * Real.pi by positivity).trans_le hLbig
  have hmesh : 2 * Real.pi / P.L T ≤ 1 := by
    rw [div_le_iff₀ hL]
    nlinarith
  have hT0 : 0 ≤ T := by linarith
  have hsqrtSq : Real.sqrt T ^ 2 = T := Real.sq_sqrt hT0
  have hsqrt : 2 ≤ Real.sqrt T := by
    nlinarith [Real.sqrt_nonneg T]
  have hD : 1 + 2 * Real.pi / P.L T ≤ D0 T := by
    unfold D0
    linarith
  have hDone : 1 ≤ D0 T := by
    have hmesh0 : 0 ≤ 2 * Real.pi / P.L T := by positivity
    linarith
  intro V i
  exact ⟨central_left_guard_one V hDone i,
    central_right_guard_one V hL hD i⟩

end Zeta23.GapMatching.DWindowGridGeometry
