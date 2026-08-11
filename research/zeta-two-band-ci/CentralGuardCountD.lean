/-
Copyright (c) 2026.
SPDX-License-Identifier: Apache-2.0

Set-theoretic guard decomposition and eventual existence of a nontrivial
central ordered path.
-/
import Zeta23.Unconditional
import Zeta23.GapMatching.CentralPathConstructionD
import Zeta23.GapMatching.GuardedWindowCount

open Set Filter Asymptotics Real

noncomputable section

namespace Zeta23.GapMatching.CentralGuardCountD

open Zeta23
open Zeta23.Assembly
open Zeta23.GapMatching.CentralPathConstructionD
open Zeta23.GapMatching.GuardedWindowCount

/-- Simple critical-line zeros in the full dyadic window. -/
def fullSimpleSet (Z : ZeroConfig) (T : ℝ) : Set ℂ :=
  Z.window T (2 * T) ∩ ZeroConfig.onLine ∩ Z.simple

/-- Lower inner guard strip. -/
def lowerInnerSet (Z : ZeroConfig) (T : ℝ) : Set ℂ :=
  Z.window T (T + D0 T)

/-- Upper inner guard strip. -/
def upperInnerSet (Z : ZeroConfig) (T : ℝ) : Set ℂ :=
  Z.window (2 * T - D0 T) (2 * T)

@[simp] theorem ncard_fullSimpleSet
    (Z : ZeroConfig) (T : ℝ) :
    (fullSimpleSet Z T).ncard = Z.N0s T (2 * T) := by
  rfl

/-- Every full-window simple zero is central or belongs to one of the two
inner guard strips. -/
theorem fullSimpleSet_subset
    (Z : ZeroConfig) (T : ℝ) :
    fullSimpleSet Z T ⊆
      centralSimpleSet Z T ∪
        (lowerInnerSet Z T ∪ upperInnerSet Z T) := by
  intro rho hrho
  rcases hrho with ⟨⟨hwindow, honline⟩, hsimple⟩
  rcases hwindow with ⟨hcarrier, hheight⟩
  by_cases hlo : rho.im ≤ T + D0 T
  · right
    left
    exact ⟨hcarrier, hheight.1, hlo⟩
  · by_cases hhi : rho.im ≤ 2 * T - D0 T
    · left
      exact ⟨⟨⟨hcarrier, lt_of_not_ge hlo, hhi⟩, honline⟩,
        hsimple⟩
    · right
      right
      exact ⟨hcarrier, lt_of_not_ge hhi, hheight.2⟩

lemma lowerInnerSet_finite
    (Z : ZeroConfig) (T : ℝ) :
    (lowerInnerSet Z T).Finite :=
  Z.finite_window _ _

lemma upperInnerSet_finite
    (Z : ZeroConfig) (T : ℝ) :
    (upperInnerSet Z T).Finite :=
  Z.finite_window _ _

/-- Cardinality form of the central/guard decomposition. -/
theorem fullSimple_ncard_le
    (Z : ZeroConfig) (T : ℝ) :
    (fullSimpleSet Z T).ncard ≤
      (centralSimpleSet Z T).ncard
        + (lowerInnerSet Z T).ncard
        + (upperInnerSet Z T).ncard := by
  have hfinite :
      (centralSimpleSet Z T ∪
        (lowerInnerSet Z T ∪ upperInnerSet Z T)).Finite :=
    (centralSimpleSet_finite Z T).union
      ((lowerInnerSet_finite Z T).union
        (upperInnerSet_finite Z T))
  calc
    (fullSimpleSet Z T).ncard
        ≤ (centralSimpleSet Z T ∪
            (lowerInnerSet Z T ∪ upperInnerSet Z T)).ncard :=
          Set.ncard_le_ncard (fullSimpleSet_subset Z T) hfinite
    _ ≤ (centralSimpleSet Z T).ncard
          + (lowerInnerSet Z T ∪ upperInnerSet Z T).ncard :=
          Set.ncard_union_le _ _
    _ ≤ (centralSimpleSet Z T).ncard
          + ((lowerInnerSet Z T).ncard
            + (upperInnerSet Z T).ncard) := by
          exact Nat.add_le_add_left
            (Set.ncard_union_le _ _) _
    _ = _ := by omega

/-- Distinct points in a guard strip are bounded by the multiplicity count of
that strip. -/
theorem lowerInner_ncard_le_N
    (Z : ZeroConfig) (T : ℝ) :
    (lowerInnerSet Z T).ncard ≤ Z.N T (T + D0 T) := by
  simpa [lowerInnerSet, ZeroConfig.N] using
    (Z.ncard_le_finsum_mult T (T + D0 T)
      (s := lowerInnerSet Z T) (by rfl))

/-- Upper-strip counterpart. -/
theorem upperInner_ncard_le_N
    (Z : ZeroConfig) (T : ℝ) :
    (upperInnerSet Z T).ncard ≤
      Z.N (2 * T - D0 T) (2 * T) := by
  simpa [upperInnerSet, ZeroConfig.N] using
    (Z.ncard_le_finsum_mult (2 * T - D0 T) (2 * T)
      (s := upperInnerSet Z T) (by rfl))

/-- Exact guard-cover inequality at the level of the central-set cardinality. -/
theorem N0s_sub_innerGuard_le_central
    (Z : ZeroConfig) (T : ℝ) :
    (Z.N0s T (2 * T) : ℝ) - innerGuard Z T
      ≤ ((centralSimpleSet Z T).ncard : ℝ) := by
  have hfullNat := fullSimple_ncard_le Z T
  have hloNat := lowerInner_ncard_le_N Z T
  have hhiNat := upperInner_ncard_le_N Z T
  rw [ncard_fullSimpleSet] at hfullNat
  have hfull :
      (Z.N0s T (2 * T) : ℝ) ≤
        ((centralSimpleSet Z T).ncard : ℝ)
          + ((lowerInnerSet Z T).ncard : ℝ)
          + ((upperInnerSet Z T).ncard : ℝ) := by
    exact_mod_cast hfullNat
  have hlo :
      ((lowerInnerSet Z T).ncard : ℝ) ≤
        (Z.N T (T + D0 T) : ℝ) := by
    exact_mod_cast hloNat
  have hhi :
      ((upperInnerSet Z T).ncard : ℝ) ≤
        (Z.N (2 * T - D0 T) (2 * T) : ℝ) := by
    exact_mod_cast hhiNat
  unfold innerGuard
  linarith

/-- The central guarded set contains at least two simple critical-line zeros
for all sufficiently large heights.  This uses only the already-formalized
half-simple theorem, the inner-guard `o(N)` estimate, and `N(T,2T) → ∞`. -/
theorem eventually_two_le_central_ncard :
    ∀ᶠ T in atTop,
      2 ≤ (centralSimpleSet zetaZeroConfig T).ncard := by
  obtain ⟨Tbase, hbase⟩ :=
    Zeta23.thmB₀ (1 / 4 : ℝ) (by norm_num)
  have hbase_ev : ∀ᶠ T in atTop,
      (1 / 4 : ℝ) * (zetaZeroConfig.N T (2 * T) : ℝ)
        ≤ (zetaZeroConfig.N0s T (2 * T) : ℝ) := by
    filter_upwards [eventually_ge_atTop Tbase] with T hT
    have h := hbase T hT
    norm_num at h ⊢
    simpa using h

  have hguard_o :=
    innerGuard_isLittleO_count zetaZeroConfig paperInputs_zeta
  have hguard_ev := hguard_o.def (show 0 < (1 / 8 : ℝ) by norm_num)
  have hNtop := tendsto_N_atTop zetaZeroConfig paperInputs_zeta.RvM
  have hNlarge : ∀ᶠ T in atTop,
      (16 : ℝ) ≤ (zetaZeroConfig.N T (2 * T) : ℝ) :=
    hNtop.eventually_ge_atTop 16

  filter_upwards [hbase_ev, hguard_ev, hNlarge]
    with T hbaseT hguardT hNT
  have hguard0 : 0 ≤ innerGuard zetaZeroConfig T := by
    unfold innerGuard
    positivity
  have hN0 : 0 ≤ (zetaZeroConfig.N T (2 * T) : ℝ) :=
    Nat.cast_nonneg _
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg hguard0, abs_of_nonneg hN0] at hguardT
  have hcentral :=
    N0s_sub_innerGuard_le_central zetaZeroConfig T
  have hcentral_real :
      (2 : ℝ) ≤
        ((centralSimpleSet zetaZeroConfig T).ncard : ℝ) := by
    nlinarith
  exact_mod_cast hcentral_real

/-- Canonical eventual ordered central vertices. -/
theorem eventually_nonempty_orderedCentralVertices
    (P : Params) :
    ∀ᶠ T in atTop,
      Nonempty (OrderedCentralVerticesD zetaZeroConfig P T) := by
  filter_upwards [eventually_two_le_central_ncard]
    with T hcard
  exact ⟨orderedCentralVertices zetaZeroConfig P T hcard⟩

end Zeta23.GapMatching.CentralGuardCountD
