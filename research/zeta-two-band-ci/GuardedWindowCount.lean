/-
Copyright (c) 2026.
SPDX-License-Identifier: Apache-2.0

Zero-count control for the two INNER guard strips

  (T, T + sqrt T]  and  (2T - sqrt T, 2T].

The upstream tail theorem controls the corresponding outer strips.  For the
gap-matching path we need the inner strips, because the retained simple zeros
must stay a distance sqrt T from the finite Gabor grid endpoints.  The same
unit-window local count gives O(sqrt T log T), hence o(N(T,2T)).
-/
import Zeta23.Tail
import Zeta23.ThmD.Endgame

open Filter Asymptotics Real Finset

noncomputable section

namespace Zeta23.GapMatching.GuardedWindowCount

open Zeta23
open Zeta23.Tail

/-- A local unit-window bound controls every finite interval of length `R`.
The harmless `+4` in the logarithm absorbs the final partial unit window. -/
theorem finite_interval_count_le
    {ι : Type*} {gamma : ι → ℝ} {mult : ι → ℕ}
    {A0 left R : ℝ}
    (hlocal : LocalCount gamma mult A0)
    (hR : 0 < R)
    (s : Finset ι)
    (hs : ∀ rho ∈ s,
      left < gamma rho ∧ gamma rho ≤ left + R) :
    (∑ rho ∈ s, (mult rho : ℝ))
      ≤ (⌈R⌉₊ : ℝ) *
          (A0 * Real.log (|left| + R + 4)) := by
  classical
  set K : ℕ := ⌈R⌉₊ with hK
  set C : ℝ := A0 * Real.log (|left| + R + 4) with hC
  set key : ι → ℕ := fun rho => ⌈gamma rho - left⌉₊ - 1 with hkey

  have hKpos : 1 ≤ K := by
    rw [hK]
    exact Nat.one_le_ceil_iff.mpr hR
  have hKlt : (K : ℝ) < R + 1 := by
    rw [hK]
    exact Nat.ceil_lt_add_one hR.le
  have hA0 : 0 ≤ A0 := hlocal.A₀_pos.le

  apply (sum_mult_le_of_windows s mult key K) <;> clear hC
  · intro rho hrho
    have hx := hs rho hrho
    have hceil1 : 1 ≤ ⌈gamma rho - left⌉₊ :=
      Nat.one_le_ceil_iff.mpr (by linarith [hx.1])
    have hceilK : ⌈gamma rho - left⌉₊ ≤ K := by
      rw [hK]
      exact Nat.ceil_mono (by linarith [hx.2])
    simp only [hkey]
    omega
  · intro j hj
    refine (hlocal.window (left + j) _ ?_).trans ?_
    · intro rho hrho
      rw [mem_filter] at hrho
      obtain ⟨hrhos, hrhoj⟩ := hrho
      have hx := hs rho hrhos
      have hceil1 : 1 ≤ ⌈gamma rho - left⌉₊ :=
        Nat.one_le_ceil_iff.mpr (by linarith [hx.1])
      have hceil : ⌈gamma rho - left⌉₊ = j + 1 := by
        simp only [hkey] at hrhoj
        omega
      have hb := (Nat.ceil_eq_iff (Nat.succ_ne_zero j)).mp hceil
      push_cast at hb
      constructor <;> linarith [hb.1, hb.2]
    · have hjK : ((j : ℕ) : ℝ) < K := by exact_mod_cast hj
      have hjR : (j : ℝ) < R + 1 := hjK.trans hKlt
      have habs : |left + (j : ℝ)| ≤ |left| + j := by
        calc
          |left + (j : ℝ)| ≤ |left| + |(j : ℝ)| := abs_add _ _
          _ = |left| + j := by rw [abs_of_nonneg (Nat.cast_nonneg j)]
      have harg : |left + (j : ℝ)| + 3 ≤ |left| + R + 4 := by
        linarith
      have hlog :
          Real.log (|left + (j : ℝ)| + 3)
            ≤ Real.log (|left| + R + 4) :=
        Real.log_le_log (by positivity) harg
      simpa [C] using mul_le_mul_of_nonneg_left hlog hA0

/-- ZeroConfig version of `finite_interval_count_le`. -/
theorem zero_interval_count_le
    (Z : ZeroConfig) {A0 left R : ℝ}
    (hA0 : 1 ≤ A0)
    (hlocal : ∀ t : ℝ,
      (Z.N t (t + 1) : ℝ) ≤ A0 * Real.log (|t| + 3))
    (hR : 0 < R) :
    (Z.N left (left + R) : ℝ)
      ≤ (⌈R⌉₊ : ℝ) *
          (A0 * Real.log (|left| + R + 4)) := by
  classical
  have hfinite : (Z.window left (left + R)).Finite :=
    Z.finite_window _ _
  set s : Finset Z.carrier :=
    hfinite.toFinset.subtype (· ∈ Z.carrier) with hsdef

  have hcount :
      (Z.N left (left + R) : ℝ)
        = ∑ rho ∈ s, (Z.mult (rho : ℂ) : ℝ) := by
    unfold ZeroConfig.N
    rw [finsum_mem_eq_finite_toFinset_sum _ hfinite,
      hsdef,
      Finset.sum_subtype_of_mem
        (f := fun rho : ℂ => (Z.mult rho : ℝ))]
    · push_cast
      rfl
    · intro rho hrho
      exact ((Set.Finite.mem_toFinset _).mp hrho).1

  have hmem : ∀ rho ∈ s,
      left < (rho : ℂ).im ∧
        (rho : ℂ).im ≤ left + R := by
    intro rho hrho
    rw [hsdef, Finset.mem_subtype,
      Set.Finite.mem_toFinset] at hrho
    exact hrho.2

  rw [hcount]
  exact finite_interval_count_le
    (LocalCount.ofWindowCount Z hA0 hlocal)
    hR s hmem

/-- Total multiplicity in the two inner guard strips. -/
def innerGuard (Z : ZeroConfig) (T : ℝ) : ℝ :=
  (Z.N T (T + Real.sqrt T) : ℝ)
    + (Z.N (2 * T - Real.sqrt T) (2 * T) : ℝ)

/-- Explicit inner-guard estimate, parallel to upstream `Tail.NII_le`. -/
theorem innerGuard_le
    (Z : ZeroConfig) {A0 T : ℝ}
    (hA0 : 1 ≤ A0)
    (hlocal : ∀ t : ℝ,
      (Z.N t (t + 1) : ℝ) ≤ A0 * Real.log (|t| + 3))
    (hT : Tail.T₀ ≤ T) :
    innerGuard Z T
      ≤ 4 * A0 * Real.sqrt T * Real.log (4 * T) := by
  have hT300 : (300 : ℝ) ≤ T := hT
  have hT0 : 0 < T := by linarith
  have hsqrt0 : 0 < Real.sqrt T := Real.sqrt_pos.2 hT0
  have hsqrt1 : 1 ≤ Real.sqrt T := by
    rw [Real.le_sqrt (by norm_num) hT0.le]
    linarith
  have hsqrtT : Real.sqrt T ≤ T := by
    nlinarith [Real.sq_sqrt hT0.le]
  have hK : (⌈Real.sqrt T⌉₊ : ℝ) ≤ 2 * Real.sqrt T := by
    have hceil : (⌈Real.sqrt T⌉₊ : ℝ) < Real.sqrt T + 1 :=
      Nat.ceil_lt_add_one hsqrt0.le
    linarith
  have hlog0 : 0 ≤ Real.log (4 * T) := by
    exact Real.log_nonneg (by nlinarith)
  have hA0nonneg : 0 ≤ A0 := by linarith

  have hlo := zero_interval_count_le Z hA0 hlocal hsqrt0
    (left := T)
  have hhi0 := zero_interval_count_le Z hA0 hlocal hsqrt0
    (left := 2 * T - Real.sqrt T)
  have hhi :
      (Z.N (2 * T - Real.sqrt T) (2 * T) : ℝ)
        ≤ (⌈Real.sqrt T⌉₊ : ℝ) *
            (A0 * Real.log
              (|2 * T - Real.sqrt T| + Real.sqrt T + 4)) := by
    simpa [sub_add_cancel] using hhi0

  have hargLo : |T| + Real.sqrt T + 4 ≤ 4 * T := by
    rw [abs_of_pos hT0]
    nlinarith
  have hbase : 0 ≤ 2 * T - Real.sqrt T := by
    nlinarith
  have hargHi :
      |2 * T - Real.sqrt T| + Real.sqrt T + 4 ≤ 4 * T := by
    rw [abs_of_nonneg hbase]
    nlinarith
  have hlogLo :
      Real.log (|T| + Real.sqrt T + 4)
        ≤ Real.log (4 * T) :=
    Real.log_le_log (by positivity) hargLo
  have hlogHi :
      Real.log (|2 * T - Real.sqrt T| + Real.sqrt T + 4)
        ≤ Real.log (4 * T) :=
    Real.log_le_log (by positivity) hargHi

  have hKnonneg : (0 : ℝ) ≤ ⌈Real.sqrt T⌉₊ := Nat.cast_nonneg _
  have hlo' :
      (Z.N T (T + Real.sqrt T) : ℝ)
        ≤ 2 * A0 * Real.sqrt T * Real.log (4 * T) := by
    calc
      (Z.N T (T + Real.sqrt T) : ℝ)
          ≤ (⌈Real.sqrt T⌉₊ : ℝ) *
              (A0 * Real.log (|T| + Real.sqrt T + 4)) := hlo
      _ ≤ (2 * Real.sqrt T) *
              (A0 * Real.log (4 * T)) := by
            gcongr
      _ = 2 * A0 * Real.sqrt T * Real.log (4 * T) := by ring
  have hhi' :
      (Z.N (2 * T - Real.sqrt T) (2 * T) : ℝ)
        ≤ 2 * A0 * Real.sqrt T * Real.log (4 * T) := by
    calc
      (Z.N (2 * T - Real.sqrt T) (2 * T) : ℝ)
          ≤ (⌈Real.sqrt T⌉₊ : ℝ) *
              (A0 * Real.log
                (|2 * T - Real.sqrt T| + Real.sqrt T + 4)) := hhi
      _ ≤ (2 * Real.sqrt T) *
              (A0 * Real.log (4 * T)) := by
            gcongr
      _ = 2 * A0 * Real.sqrt T * Real.log (4 * T) := by ring

  unfold innerGuard
  linarith

/-- Eventual `O(sqrt T * l T)` form of the inner guard estimate. -/
theorem innerGuard_isBigO
    (Z : ZeroConfig) {A0 : ℝ}
    (hA0 : 1 ≤ A0)
    (hlocal : ∀ t : ℝ,
      (Z.N t (t + 1) : ℝ) ≤ A0 * Real.log (|t| + 3)) :
    innerGuard Z =O[atTop] (fun T => Real.sqrt T * l T) := by
  refine IsBigO.of_bound (8 * A0) ?_
  filter_upwards [eventually_ge_atTop Tail.T₀] with T hT
  have h1 := innerGuard_le Z hA0 hlocal hT
  have h2 := Tail.log_four_mul_le_two_mul_l hT
  have hguard0 : 0 ≤ innerGuard Z T := by
    unfold innerGuard
    positivity
  have hmajor0 : 0 ≤ Real.sqrt T * l T := by
    have hl : 0 ≤ l T := by
      have := Tail.one_le_log_four_mul hT
      have hlog := Tail.log_four_mul_le_two_mul_l hT
      linarith
    positivity
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg hguard0, abs_of_nonneg hmajor0]
  have hA : 0 ≤ 4 * A0 * Real.sqrt T := by
    have := Real.sqrt_nonneg T
    positivity
  calc
    innerGuard Z T
        ≤ 4 * A0 * Real.sqrt T * Real.log (4 * T) := h1
    _ ≤ 4 * A0 * Real.sqrt T * (2 * l T) := by
          exact mul_le_mul_of_nonneg_left h2 hA
    _ = (8 * A0) * (Real.sqrt T * l T) := by ring

/-- The inner guard is negligible relative to the dyadic zero count. -/
theorem innerGuard_isLittleO_count
    (Z : ZeroConfig) (H : PaperInputs Z) :
    innerGuard Z =o[atTop]
      (fun T => (Z.N T (2 * T) : ℝ)) := by
  obtain ⟨A0, hA0, hlocal⟩ := H.RvM.local_count
  exact (innerGuard_isBigO Z hA0 hlocal).trans_isLittleO
    (isLittleO_N_of_isLittleO_Tl Z H.RvM
      isLittleO_sqrt_mul_l_Tl)

end Zeta23.GapMatching.GuardedWindowCount
