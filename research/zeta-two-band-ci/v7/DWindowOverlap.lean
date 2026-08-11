/-
Copyright (c) 2026.
SPDX-License-Identifier: Apache-2.0

Exact full-grid overlap identity for an admissible window, together with the
scalar perturbation lemma needed to pass from the full Poisson overlap to the
finite D-window Gram overlap.

The remaining analytic task after this module is quantitative: bound the
omitted grid tails uniformly for guarded zeros.  The identity itself is an
immediate normalized form of the upstream Poisson theorem.
-/
import Zeta23.ThmD.WindowCore
import Zeta23.ThmD.ZeroSideD

open Filter Real

noncomputable section

namespace Zeta23.GapMatching.DWindowOverlap

open Zeta23
open Zeta23.AdmWindow
open Zeta23.ThmD

/-- Scale-free full-grid overlap attached to an admissible window. -/
def fullGridOverlap
    (v : ℝ → ℝ) (L : ℝ) (tau tau' : ℝ) : ℝ :=
  VPhiR v (tau - tau') / (av v L * L)

/-- Normalized Poisson identity.

The normalization is exactly the one used by the zero-side vectors:
`c = a L^2`.  Thus the infinite-grid dot product of the normalized evaluation
vectors equals `VPhiR(tau-tau')/(aL)`. -/
theorem hasSum_normalized_fullGridOverlap
    {v : ℝ → ℝ} {L w c : ℝ}
    (hW : AdmWindow v L w c)
    (ha : 0 < av v L)
    (T tau tau' : ℝ) :
    HasSum
      (fun k : ℤ =>
        (av v L * L ^ 2)⁻¹
          * (vHatR v (tau - (T + k * (2 * Real.pi / L)))
            * vHatR v (tau' - (T + k * (2 * Real.pi / L)))))
      (fullGridOverlap v L tau tau') := by
  have hraw := hW.hasSum_vHatR_mul T tau tau'
  have hscaled := hraw.const_mul (av v L * L ^ 2)⁻¹
  convert hscaled using 1
  · funext k
    ring
  · unfold fullGridOverlap
    field_simp [ha.ne', hW.L_pos.ne']
    ring

/-- D-window specialization of the exact normalized full-grid identity. -/
theorem hasSum_normalized_fullGridOverlapD
    {P : Params} (hP : P.Valid) {T : ℝ}
    (h8 : 8 * P.w ≤ P.L T)
    (ha : 0 < AdmWindow.av (P.phiD T) (P.L T))
    (tau tau' : ℝ) :
    HasSum
      (fun k : ℤ =>
        (AdmWindow.av (P.phiD T) (P.L T) * P.L T ^ 2)⁻¹
          * (AdmWindow.vHatR (P.phiD T)
              (tau - (T + k * (2 * Real.pi / P.L T)))
            * AdmWindow.vHatR (P.phiD T)
              (tau' - (T + k * (2 * Real.pi / P.L T)))))
      (fullGridOverlap (P.phiD T) (P.L T) tau tau') := by
  exact hasSum_normalized_fullGridOverlap
    (admWindow_params hP h8) ha T tau tau'

/-- Absolute error controls the loss in squared overlap.  This form is
particularly convenient because the safe sharp profile satisfies `|y| ≤ 1`:
if `|x-y| ≤ eps`, `g ≤ y^2`, and `|y| ≤ 1`, then `x^2 ≥ g-2eps`. -/
theorem sq_ge_of_abs_sub_le
    {x y eps g : ℝ}
    (heps : 0 ≤ eps)
    (hxy : |x - y| ≤ eps)
    (hy : |y| ≤ 1)
    (hg : g ≤ y ^ 2) :
    g - 2 * eps ≤ x ^ 2 := by
  have habsMul : |2 * y * (x - y)| ≤ 2 * eps := by
    rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    calc
      2 * |y| * |x - y|
          ≤ 2 * 1 * eps := by
            gcongr
      _ = 2 * eps := by ring
  have hcross : -2 * eps ≤ 2 * y * (x - y) := by
    exact (neg_le_of_abs_le habsMul)
  have hid : x ^ 2 = y ^ 2 + 2 * y * (x - y) + (x - y) ^ 2 := by
    ring
  rw [hid]
  nlinarith [sq_nonneg (x - y)]

/-- Sum of two independent approximation errors. -/
theorem sq_ge_of_two_errors
    {finite full sharp epsGrid epsProfile g : ℝ}
    (hGrid0 : 0 ≤ epsGrid) (hProfile0 : 0 ≤ epsProfile)
    (hGrid : |finite - full| ≤ epsGrid)
    (hProfile : |full - sharp| ≤ epsProfile)
    (hsharp : |sharp| ≤ 1)
    (hg : g ≤ sharp ^ 2) :
    g - 2 * (epsGrid + epsProfile) ≤ finite ^ 2 := by
  have htotal : |finite - sharp| ≤ epsGrid + epsProfile := by
    calc
      |finite - sharp|
          = |(finite - full) + (full - sharp)| := by ring_nf
      _ ≤ |finite - full| + |full - sharp| := abs_add_le _ _
      _ ≤ epsGrid + epsProfile := add_le_add hGrid hProfile
  exact sq_ge_of_abs_sub_le
    (add_nonneg hGrid0 hProfile0) htotal hsharp hg

end Zeta23.GapMatching.DWindowOverlap
