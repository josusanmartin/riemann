/-
Concrete short/long finite-full-sharp component bounds on the canonical
ordered D-window path.
-/
import Zeta23.GapMatching.DWindowConcreteIdentification
import Zeta23.GapMatching.GramFiniteFullBound
import Zeta23.GapMatching.DWindowRampProfileBridge
import Zeta23.GapMatching.OneBandUniformCloseFromBounds

noncomputable section

namespace Zeta23.GapMatching.DWindowActualComponentsD

open Zeta23
open Zeta23.GapMatching.DWindowConcreteIdentification
open Zeta23.GapMatching.GramFiniteFullBound
open Zeta23.GapMatching.DWindowRampProfileBridge
open Zeta23.GapMatching.OneBandUniformCloseFromBounds
open Zeta23.GapMatching.OneBandActualWordDCore
open Zeta23.GapMatching.CentralPathConstructionD
open Zeta23.GapMatching.CentralGapGeometryD
open Zeta23.GapMatching.CanonicalOneBandPathD
open Zeta23.GapMatching.DWindowGramIdentity
open Zeta23.GapMatching.DWindowFiniteGridApprox

variable {Z : ZeroConfig} {P : Params} {T : ℝ}

/-- Common tail budget at guard distance `sqrt T`. -/
def tailBudget (Q : Package Z P T) : ℝ :=
  2 * ((AdmWindow.av Q.v Q.L * Q.L ^ 2)⁻¹ *
    rawTailMajorant Q.c Q.w (Real.sqrt T)
      (2 * Real.pi / Q.L))

/-- Common ramp budget. -/
def rampBudget (Q : Package Z P T) : ℝ := 12 * Q.w / Q.L

/-- One canonical vertex is guarded from both omitted sides of the finite
D-grid. -/
theorem vertex_guard_bounds
    (Q : Package Z P T)
    (V : OrderedCentralVerticesD Z P T)
    (hspan : 2 * T ≤
      T + ((P.atD T).d T) * (2 * Real.pi / Q.L))
    (i : Fin (V.n + 2)) :
    T + Real.sqrt T ≤ atomOrdinate (V.vertices i) ∧
    atomOrdinate (V.vertices i) + Real.sqrt T ≤
      T + ((P.atD T).d T) * (2 * Real.pi / Q.L) := by
  have hmem := V.central_mem i
  have him : atomOrdinate (V.vertices i) = ordinate V i := by
    rfl
  rw [him]
  constructor
  · exact hmem.1.1.2.1.le
  · exact hmem.1.1.2.2.le.trans hspan

/-- Consecutive normalized separation is exactly one stored gap. -/
theorem normalized_short_separation
    (Q : Package Z P T)
    (V : OrderedCentralVerticesD Z P T)
    (i : Fin (V.n + 1)) :
    Q.L * (atomOrdinate (V.vertices i.succ)
      - atomOrdinate (V.vertices i.castSucc)) /
        (2 * Real.pi)
      = gapAt V i := by
  rw [Q.L_eq]
  rfl

/-- Two-step normalized separation is the sum of the two stored gaps. -/
theorem normalized_long_separation
    (Q : Package Z P T)
    (V : OrderedCentralVerticesD Z P T)
    (i : Fin V.n) :
    Q.L * (atomOrdinate (V.vertices (Fin.succ (Fin.succ i)))
      - atomOrdinate (V.vertices (Fin.castSucc (Fin.castSucc i)))) /
        (2 * Real.pi)
      = gapAtNat V i + gapAtNat V (i + 1) := by
  rw [Q.L_eq]
  unfold gapAtNat gapAt
  simp only [dif_pos (by omega)]
  ring

/-- Concrete component bounds for all retained short and long starts. -/
theorem components
    (hreal : PhiHatReal T (P.atD T))
    (Q : Package Z P T)
    (V : OrderedCentralVerticesD Z P T)
    (hT : 0 < T)
    (hspan : 2 * T ≤
      T + ((P.atD T).d T) * (2 * Real.pi / Q.L)) :
    Components V (tailBudget Q) (rampBudget Q) where
  short_finite_full := by
    intro i
    let z := V.vertices (Fin.castSucc (Fin.castSucc i))
    let z' := V.vertices (Fin.succ (Fin.castSucc i))
    let full := normalizedFullOverlap Q.v Q.L
      (atomOrdinate z) (atomOrdinate z')
    refine ⟨full, ?_, ?_⟩
    · have hz := vertex_guard_bounds Q V hspan
        (Fin.castSucc (Fin.castSucc i))
      have hz' := vertex_guard_bounds Q V hspan
        (Fin.succ (Fin.castSucc i))
      simpa [shortOverlapNat, shortOverlap, z, z', tailBudget, full,
        dif_pos i.isLt] using
        (abs_gramOverlap_sub_full_le hreal Q.scale_pos
          Q.identification Q.admissible Q.average_pos
          (Real.sqrt_pos.2 hT) z z' hz.1 hz'.1 hz.2 hz'.2)
    · have hramp := abs_normalizedFullOverlap_sub_sharpProfile_le
        Q.admissible Q.L_pos
        (tau := atomOrdinate z) (tau' := atomOrdinate z')
      rw [normalized_short_separation Q V (Fin.castSucc i)] at hramp
      simpa [full, rampBudget, z, z'] using hramp
  long_finite_full := by
    intro i
    let z := V.vertices (Fin.castSucc (Fin.castSucc i))
    let z' := V.vertices (Fin.succ (Fin.succ i))
    let full := normalizedFullOverlap Q.v Q.L
      (atomOrdinate z) (atomOrdinate z')
    refine ⟨full, ?_, ?_⟩
    · have hz := vertex_guard_bounds Q V hspan
        (Fin.castSucc (Fin.castSucc i))
      have hz' := vertex_guard_bounds Q V hspan
        (Fin.succ (Fin.succ i))
      simpa [longOverlapNat, longOverlap, z, z', tailBudget, full,
        dif_pos i.isLt] using
        (abs_gramOverlap_sub_full_le hreal Q.scale_pos
          Q.identification Q.admissible Q.average_pos
          (Real.sqrt_pos.2 hT) z z' hz.1 hz'.1 hz.2 hz'.2)
    · have hramp := abs_normalizedFullOverlap_sub_sharpProfile_le
        Q.admissible Q.L_pos
        (tau := atomOrdinate z) (tau' := atomOrdinate z')
      rw [normalized_long_separation Q V i] at hramp
      simpa [full, rampBudget, z, z'] using hramp

end Zeta23.GapMatching.DWindowActualComponentsD
