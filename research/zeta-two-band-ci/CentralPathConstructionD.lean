/-
Copyright (c) 2026.
SPDX-License-Identifier: Apache-2.0

Canonical ordered enumeration of the central guarded simple critical-line
zeros.  The only numerical hypothesis is that the central set has at least
two points; a later asymptotic lemma discharges this from the existing
multiplicity-aware Montgomery--Taylor theorem and the guard-strip estimate.
-/
import Mathlib.Data.Finset.Sort
import Zeta23.Defs.Counting
import Zeta23.GapMatching.TwoBandGapMatchingDPath

open Set Real

noncomputable section

namespace Zeta23.GapMatching.CentralPathConstructionD

open Zeta23
open Zeta23.ZeroSide
open Zeta23.GapMatching.GapMatchingBlockSpecialization
open Zeta23.GapMatching.TwoBandGapMatchingDPath

/-- The simple critical-line zeros retained after deleting a `sqrt T` guard
from both endpoints of the dyadic interval. -/
def centralSimpleSet (Z : ZeroConfig) (T : ℝ) : Set ℂ :=
  Z.window (T + D0 T) (2 * T - D0 T)
    ∩ ZeroConfig.onLine ∩ Z.simple

lemma centralSimpleSet_finite (Z : ZeroConfig) (T : ℝ) :
    (centralSimpleSet Z T).Finite :=
  (Z.finite_window (T + D0 T) (2 * T - D0 T)).subset
    (fun _ h => h.1.1)

/-- Two central simple critical-line points with the same ordinate coincide. -/
theorem central_im_injective (Z : ZeroConfig) (T : ℝ) :
    Function.Injective
      (fun z : centralSimpleSet Z T => (z.1 : ℂ).im) := by
  intro x y him
  apply Subtype.ext
  apply Complex.ext
  · have hx : (x.1 : ℂ).re = 1 / 2 := x.2.1.2
    have hy : (y.1 : ℂ).re = 1 / 2 := y.2.1.2
    linarith
  · exact him

/-- Pull back the real order along the injective ordinate map. -/
noncomputable def centralLinearOrder (Z : ZeroConfig) (T : ℝ) :
    LinearOrder (centralSimpleSet Z T) :=
  LinearOrder.lift' (fun z => (z.1 : ℂ).im)
    (central_im_injective Z T)

/-- A central point belongs to the enlarged D-window block. -/
def centralZI
    {Z : ZeroConfig} {P : Params} {T : ℝ}
    (z : centralSimpleSet Z T) : ZeroSide.ZI Z T := by
  refine ⟨z.1, ?_⟩
  rw [mem_ZI, mem_ZIprime_iff]
  rcases z.2.1.1 with ⟨hcarrier, hlow, hhigh⟩
  refine ⟨hcarrier, ?_, ?_⟩
  · have hsqrt := Real.sqrt_nonneg T
    linarith
  · have hsqrt := Real.sqrt_nonneg T
    linarith

/-- Embed a central simple zero into the simple on-line atom subtype of the
actual D-window block. -/
def centralToSimple
    {Z : ZeroConfig} {P : Params} {T : ℝ}
    (z : centralSimpleSet Z T) : dSimpleOnLine Z P T := by
  let zi : ZeroSide.ZI Z T := centralZI (P := P) z
  let on : (dBlock Z P T).onLine := by
    refine ⟨zi, ?_⟩
    rw [ZeroBlockData.mem_onLine]
    change (blockData Z T (P.atD T) (dConj P T)).σ zi = zi
    rw [mkData_σ_eq_iff]
    exact z.2.1.2
  refine ⟨on, ?_⟩
  change Z.mult z.1 = 1
  exact z.2.2

/-- The central-to-block map is injective. -/
theorem centralToSimple_injective
    {Z : ZeroConfig} {P : Params} {T : ℝ} :
    Function.Injective
      (centralToSimple (Z := Z) (P := P) (T := T)) := by
  intro x y hxy
  apply Subtype.ext
  have hxy0 := congrArg
    (fun z : dSimpleOnLine Z P T => (((z.1.1 : ZeroSide.ZI Z T) : ℂ)))
    hxy
  exact hxy0

/-- Central points as an embedding into the D-window simple atoms. -/
def centralEmbedding
    {Z : ZeroConfig} {P : Params} {T : ℝ} :
    centralSimpleSet Z T ↪ dSimpleOnLine Z P T where
  toFun := centralToSimple
  inj' := centralToSimple_injective

/-- A canonical increasing enumeration, available whenever the central set
contains at least two points. -/
structure OrderedCentralVerticesD
    (Z : ZeroConfig) (P : Params) (T : ℝ) where
  n : ℕ
  vertices : Fin (n + 2) ↪ dSimpleOnLine Z P T
  central_mem : ∀ i,
    ((vertices i).1.1 : ℂ) ∈ centralSimpleSet Z T
  central_surj : ∀ rho ∈ centralSimpleSet Z T,
    ∃ i, ((vertices i).1.1 : ℂ) = rho
  strictMono_im : StrictMono
    (fun i => (((vertices i).1.1 : ℂ)).im)

/-- Construct the canonical increasing enumeration by lifting the order from
ordinates and applying `Finset.orderEmbOfFin`. -/
noncomputable def orderedCentralVertices
    (Z : ZeroConfig) (P : Params) (T : ℝ)
    (hcard : 2 ≤ (centralSimpleSet Z T).ncard) :
    OrderedCentralVerticesD Z P T := by
  letI : Fintype (centralSimpleSet Z T) :=
    (centralSimpleSet_finite Z T).fintype
  letI : LinearOrder (centralSimpleSet Z T) :=
    centralLinearOrder Z T
  let k : ℕ := Fintype.card (centralSimpleSet Z T)
  have hkset : k = (centralSimpleSet Z T).ncard := by
    simp [k]
  have hk2 : 2 ≤ k := by simpa [hkset] using hcard
  let n : ℕ := k - 2
  have hkn : k = n + 2 := by
    dsimp [n]
    omega
  let ordered : Fin (n + 2) ↪o centralSimpleSet Z T :=
    (Finset.univ.orderEmbOfFin (by simpa [k] using hkn))
  let vertices : Fin (n + 2) ↪ dSimpleOnLine Z P T :=
    ordered.toEmbedding.trans centralEmbedding
  refine
    { n := n
      vertices := vertices
      central_mem := ?_
      central_surj := ?_
      strictMono_im := ?_ }
  · intro i
    exact (ordered i).2
  · intro rho hrho
    let z : centralSimpleSet Z T := ⟨rho, hrho⟩
    have hz : z ∈ (Finset.univ : Finset (centralSimpleSet Z T)) := by simp
    rw [← Finset.range_orderEmbOfFin
      (Finset.univ : Finset (centralSimpleSet Z T))
      (by simpa [k] using hkn)] at hz
    rcases hz with ⟨i, hi⟩
    refine ⟨i, ?_⟩
    change ((centralEmbedding (ordered i)).1.1 : ℂ) = rho
    simpa [z] using congrArg Subtype.val hi
  · intro i j hij
    change (((centralEmbedding (ordered i)).1.1 : ℂ)).im
      < (((centralEmbedding (ordered j)).1.1 : ℂ)).im
    change ((ordered i).1 : ℂ).im < ((ordered j).1 : ℂ).im
    exact ordered.strictMono hij

end Zeta23.GapMatching.CentralPathConstructionD
