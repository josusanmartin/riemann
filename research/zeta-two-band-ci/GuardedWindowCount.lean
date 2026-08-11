/-
Copyright (c) 2026.
SPDX-License-Identifier: Apache-2.0

Counting loss from replacing the full dyadic interval `[T,2T]` by the central
subinterval `[T+sqrt T, 2T-sqrt T]`.

The upstream tail development proves a unit-window count for the two outer
boundary strips of `I'`.  The same theorem, after translating the height,
controls the two inner guard strips.  This module also records the exact set
inclusion converting that strip count into a lower bound for the number of
central simple critical-line zeros.
-/
import Zeta23.Tail.Count
import Zeta23.ThmD.Endgame

open Filter Asymptotics Real

noncomputable section

namespace Zeta23.GapMatching.GuardedWindowCount

open Zeta23
open Zeta23.Tail
open Zeta23.Assembly

/-- The two inner guard strips removed from `(T,2T]`. -/
def innerGuardSet (Z : ZeroConfig) (T : ℝ) : Set ℂ :=
  Z.window T (T + D0 T) ∪ Z.window (2 * T - D0 T) (2 * T)

/-- Number of distinct simple critical-line zeros in the two removed strips. -/
def innerGuardCount (Z : ZeroConfig) (T : ℝ) : ℕ :=
  (innerGuardSet Z T ∩ ZeroConfig.onLine ∩ Z.simple).ncard

/-- The central simple critical-line set. -/
def centralSimpleSet (Z : ZeroConfig) (T : ℝ) : Set ℂ :=
  Z.window (T + D0 T) (2 * T - D0 T)
    ∩ ZeroConfig.onLine ∩ Z.simple

lemma innerGuardSet_subset_window (Z : ZeroConfig) {T : ℝ} (hT : 0 ≤ T) :
    innerGuardSet Z T ⊆ Z.window T (2 * T) := by
  intro rho hrho
  rcases hrho with hrho | hrho
  · rcases hrho with ⟨hcarrier, him⟩
    exact ⟨hcarrier, ⟨him.1, by
      have hsqrt : Real.sqrt T ≤ T := by
        rw [Real.sqrt_le_iff]
        constructor
        · exact hT
        · nlinarith
      linarith⟩⟩
  · rcases hrho with ⟨hcarrier, him⟩
    exact ⟨hcarrier, ⟨by
      have hsqrt : Real.sqrt T ≤ T := by
        rw [Real.sqrt_le_iff]
        constructor
        · exact hT
        · nlinarith
      linarith, him.2⟩⟩

/-- Every simple critical-line zero in `(T,2T]` lies either in the central
interval or one of the two guard strips. -/
lemma full_simple_subset_central_union_guard
    (Z : ZeroConfig) (T : ℝ) :
    Z.window T (2 * T) ∩ ZeroConfig.onLine ∩ Z.simple
      ⊆ centralSimpleSet Z T
        ∪ (innerGuardSet Z T ∩ ZeroConfig.onLine ∩ Z.simple) := by
  intro rho hrho
  rcases hrho with ⟨⟨hcarrier, him⟩, hon, hsimple⟩
  by_cases hlo : rho.im ≤ T + D0 T
  · right
    refine ⟨?_, hon, hsimple⟩
    left
    exact ⟨hcarrier, ⟨him.1, hlo⟩⟩
  · by_cases hhi : 2 * T - D0 T < rho.im
    · right
      refine ⟨?_, hon, hsimple⟩
      right
      exact ⟨hcarrier, ⟨hhi, him.2⟩⟩
    · left
      exact ⟨⟨hcarrier, ⟨lt_of_not_ge hlo, le_of_not_gt hhi⟩⟩,
        hon, hsimple⟩

/-- The full simple count is at most central plus guard. -/
theorem N0s_le_central_add_guard
    (Z : ZeroConfig) {T : ℝ} (hT : 0 ≤ T) :
    Z.N0s T (2 * T)
      ≤ (centralSimpleSet Z T).ncard + innerGuardCount Z T := by
  have hcentral : (centralSimpleSet Z T).Finite :=
    (Z.finite_window (T + D0 T) (2 * T - D0 T)).subset
      (fun _ h => h.1.1)
  have hguard :
      (innerGuardSet Z T ∩ ZeroConfig.onLine ∩ Z.simple).Finite := by
    have hfull : (Z.window T (2 * T)).Finite := Z.finite_window T (2 * T)
    exact hfull.subset fun rho hrho =>
      innerGuardSet_subset_window Z hT hrho.1.1
  calc
    Z.N0s T (2 * T)
        ≤ (centralSimpleSet Z T ∪
            (innerGuardSet Z T ∩ ZeroConfig.onLine ∩ Z.simple)).ncard :=
          Set.ncard_le_ncard
            (full_simple_subset_central_union_guard Z T)
            (hcentral.union hguard)
    _ ≤ (centralSimpleSet Z T).ncard
          + (innerGuardSet Z T ∩ ZeroConfig.onLine ∩ Z.simple).ncard :=
          Set.ncard_union_le _ _
    _ = (centralSimpleSet Z T).ncard + innerGuardCount Z T := rfl

/-- Real subtraction form consumed by the gap-family bridge. -/
theorem central_count_lower
    (Z : ZeroConfig) {T : ℝ} (hT : 0 ≤ T) :
    (Z.N0s T (2 * T) : ℝ) - innerGuardCount Z T
      ≤ ((centralSimpleSet Z T).ncard : ℝ) := by
  have h := N0s_le_central_add_guard Z hT
  exact_mod_cast (Nat.le_add_left
    (Z.N0s T (2 * T) - innerGuardCount Z T)
    ((centralSimpleSet Z T).ncard)).trans (by omega :
      Z.N0s T (2 * T) - innerGuardCount Z T
        ≤ (centralSimpleSet Z T).ncard)

/-- Local unit-window count for the two inner guard strips. -/
theorem inner_guard_count_le
    (Z : ZeroConfig) {A0 T : ℝ}
    (hA0 : 1 ≤ A0)
    (hloc : ∀ t : ℝ,
      (Z.N t (t + 1) : ℝ) ≤ A0 * Real.log (|t| + 3))
    (hT : T0 ≤ T) :
    (innerGuardCount Z T : ℝ)
      ≤ 3 * A0 * Real.sqrt T * Real.log (4 * T) := by
  let s : Finset ℂ :=
    ((Z.finite_window T (2 * T)).subset
      (fun rho hrho =>
        innerGuardSet_subset_window Z (by
          have : 0 < T := lt_of_lt_of_le T0_pos hT
          linarith) hrho.1.1)).toFinset
  have hlocal : LocalCount (fun rho : ℂ => rho.im) Z.mult A0 :=
    LocalCount.ofWindowCount Z hA0 hloc
  have hs : ∀ rho ∈ s,
      (T < rho.im ∧ rho.im ≤ T + Real.sqrt T) ∨
      (2 * T - Real.sqrt T < rho.im ∧ rho.im ≤ 2 * T) := by
    intro rho hrho
    have hmem : rho ∈ innerGuardSet Z T ∩ ZeroConfig.onLine ∩ Z.simple :=
      Set.Finite.mem_toFinset.mp hrho
    rcases hmem.1.1 with hlo | hhi
    · exact Or.inl hlo.2
    · exact Or.inr hhi.2
  have hshift := boundary_count_le
    hlocal hT s (fun rho hrho => by
      rcases hs rho hrho with hlo | hhi
      · left
        constructor <;> linarith
      · right
        constructor <;> linarith)
  have hmult :
      (innerGuardCount Z T : ℝ)
        ≤ ∑ rho ∈ s, (Z.mult rho : ℝ) := by
    unfold innerGuardCount
    rw [Set.ncard_eq_toFinset_card _
      (((Z.finite_window T (2 * T)).subset
        (fun rho hrho =>
          innerGuardSet_subset_window Z (by
            have : 0 < T := lt_of_lt_of_le T0_pos hT
            linarith) hrho.1.1)))]
    exact_mod_cast Finset.card_le_sum_of_subadditive_on_pred
      (p := fun _ : ℂ => True)
      (f := fun rho => Z.mult rho)
      (fun _ _ _ => Nat.zero_le _)
      (fun rho _ => Z.one_le_mult rho
        ((innerGuardSet_subset_window Z (by
          have : 0 < T := lt_of_lt_of_le T0_pos hT
          linarith)
          (Set.Finite.mem_toFinset.mp (by assumption))).1))
  exact hmult.trans hshift

/-- The inner guard count is `o(N(T,2T))`. -/
theorem innerGuardCount_isLittleO
    (Z : ZeroConfig) (H : PaperInputs Z) :
    (fun T => (innerGuardCount Z T : ℝ))
      =o[atTop] (fun T => (Z.N T (2 * T) : ℝ)) := by
  obtain ⟨A0, hA0, hloc⟩ := H.RvM.local_count
  have hO :
      (fun T => (innerGuardCount Z T : ℝ))
        =O[atTop] (fun T => Real.sqrt T * l T) := by
    refine IsBigO.of_bound (6 * A0) ?_
    filter_upwards [eventually_ge_atTop T0,
      eventually_l_pos] with T hT hlT
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (Nat.cast_nonneg _),
      abs_of_nonneg (by positivity)]
    have hguard := inner_guard_count_le Z hA0 hloc hT
    have hlog := log_four_mul_le_two_mul_l hT
    have hcoef : 0 ≤ 3 * A0 * Real.sqrt T := by
      have hA0nonneg : 0 ≤ A0 := by linarith
      positivity
    have hmul := mul_le_mul_of_nonneg_left hlog hcoef
    calc
      (innerGuardCount Z T : ℝ)
          ≤ 3 * A0 * Real.sqrt T * Real.log (4 * T) := hguard
      _ ≤ 6 * A0 * Real.sqrt T * l T := by
            nlinarith
  exact hO.trans_isLittleO
    (isLittleO_N_of_isLittleO_Tl Z H.RvM
      isLittleO_sqrt_mul_l_Tl)

end Zeta23.GapMatching.GuardedWindowCount
