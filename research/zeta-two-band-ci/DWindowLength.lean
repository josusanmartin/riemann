/-
Copyright (c) 2026.
SPDX-License-Identifier: Apache-2.0

The fixed-lambda Montgomery--Taylor grid is asymptotically shorter than the
number of zeros in the dyadic window.
-/
import Zeta23.Assembly
import Zeta23.PrimeSideB.Traces

open Filter Real

noncomputable section

namespace Zeta23.GapMatching.DWindowLength

open Zeta23
open Zeta23.Assembly
open Zeta23.PrimeSide

/-- For every fixed `lambda < 1`, the normalized width of `[T,2T]` is at most
`N(T,2T)` for all sufficiently large `T`. -/
theorem eventually_normalized_span_le_count
    (Z : ZeroConfig) (H : PaperInputs Z)
    (P : Params) (hP : P.Valid) (hlam : P.lam < 1) :
    ∀ᶠ T in atTop,
      P.L T * T / (2 * Real.pi)
        ≤ (Z.N T (2 * T) : ℝ) := by
  obtain ⟨C, hC, T0, hRvM⟩ := rvm_evBound H.RvM
  have hlamGap : 0 < 1 - P.lam := sub_pos.mpr hlam
  have hpi : 0 < 2 * Real.pi := by positivity
  have hlog2 : 0 ≤ 2 * Real.log 2 - 1 := by
    nlinarith [Real.log_two_gt_d9]

  filter_upwards
    [eventually_ge_atTop T0,
      eventually_l_pos,
      eventually_ge_atTop (2 * Real.pi * C / (1 - P.lam))]
    with T hT0 hl hTlarge

  have hl0 : 0 ≤ l T := hl.le
  have hTpos : 0 < T := by
    have hthreshold :
        0 < 2 * Real.pi * C / (1 - P.lam) := by positivity
    exact hthreshold.trans_le hTlarge

  have hcoef :
      C ≤ T * (1 - P.lam) / (2 * Real.pi) := by
    have hmul := mul_le_mul_of_nonneg_right hTlarge hlamGap.le
    have hcancel :
        (2 * Real.pi * C / (1 - P.lam)) * (1 - P.lam)
          = 2 * Real.pi * C := by
      field_simp
    rw [hcancel] at hmul
    rw [le_div_iff₀ hpi]
    nlinarith

  have hmainGap :
      C * l T
        ≤ T * ell1 T / (2 * Real.pi)
            - P.L T * T / (2 * Real.pi) := by
    have hlead :
        C * l T
          ≤ (T * (1 - P.lam) / (2 * Real.pi)) * l T :=
      mul_le_mul_of_nonneg_right hcoef hl0
    have hconstant :
        0 ≤ T * (2 * Real.log 2 - 1) / (2 * Real.pi) := by
      exact div_nonneg (mul_nonneg hTpos.le hlog2) hpi.le
    have heq :
        T * ell1 T / (2 * Real.pi)
            - P.L T * T / (2 * Real.pi)
          = (T * (1 - P.lam) / (2 * Real.pi)) * l T
              + T * (2 * Real.log 2 - 1) / (2 * Real.pi) := by
      unfold ell1 Params.L
      ring
    rw [heq]
    linarith

  have hNlower :
      T * ell1 T / (2 * Real.pi) - C * l T
        ≤ (Z.N T (2 * T) : ℝ) := by
    have h := (abs_le.mp (hRvM T hT0)).1
    linarith

  linarith

end Zeta23.GapMatching.DWindowLength
