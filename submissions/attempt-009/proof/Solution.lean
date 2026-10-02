/-
Riemann.fail submission — an unconditional critical-line proportion of 6730423/10000000 = 0.6730423,
strictly above the board's current record `currentRecordKappa` (the exact rational of the last accepted
candidate; the original closed form 2 − 1/cMT = 0.67250070… is covered as a fallback).

The mathematics: Ainta's n-point simple-zero refinement of Theorem D of the pinned Zeta23
development (the Montgomery–Taylor window at λ = 1), at n = 6 with pair weights a_ij and
per-gap pressures b_r (the weighted bookkeeping of `n_point_bound_w'`), made unconditional by a
kernel-checked finite certificate `SixW25P`: a bisection over the gaps with 167720 leaves over the
half-space g₀ ≤ g₄ (the pair weights are symmetric under gap reversal, so the other half follows by
the reflection `G_rev`), each leaf decided by a dyadic pyramid of lower bounds for `wfun`
(495 blocks, 7374 finest cells certified by the integer pipeline `cellN_soundZ'` — Taylor
enclosures of cos and sin at scale 10¹⁵ —, 14253 stored entries, every coarser entry at most its
children), read by the oracle `Pyr.lb` whose soundness is `Pyr.lb_sound`.
Pyramid lower-bound table adapted from five-point-pyramid-2 by typh (Apache-2.0).
The resulting constant is `(14550000000·H − 25739571)/14500045810 = 0.67304239…` with
`H = HD 1 = 3/2 − (1/√2)cot(1/√2)`, and `H` is enclosed to `1.1·10⁻⁸` by a twelve-term Taylor argument,
which is what places the exact rational `6730423/10000000` strictly between the record and the
proved constant.

Every declaration below is proved from the pinned `anthropics/zeta-23-lean` and Mathlib; no
placeholders, no `native_decide`, no additional axioms: every certificate check is a
`decide +kernel` evaluation of the data.  Sources: the Zeta Lab bridge (`Zeta23Ext.Bridge`,
`Zeta23Ext.BridgeW`, `ThreePoint.Base`), MIT-licensed, ported here into one file; the counting
functions and `cMT` are those of `ChallengeDeps`.
-/
import ChallengeDeps.CandidateSpec
import Zeta23.ZeroSide.RankTraceMult
import Zeta23.ThmD.Mult
import Zeta23.ThmD.ZeroSideD
import Zeta23.PrimeSideA.EndsE1
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Analysis.Real.Pi.Bounds

set_option linter.all false

set_option Elab.async false

/-! ###### source module: Zeta23Ext/StableRankTrace.lean ###### -/



noncomputable section
set_option linter.unusedSectionVars false

open Matrix Finset RHLinalg
open Zeta23.ZeroSide.RankTraceMult
open scoped ComplexOrder

namespace Zeta23Ext.StableRankTrace

def Psi (t : ℝ) : ℝ := if t ≤ 2 then (t - 1) ^ 2 else 2 * t - 3

lemma Psi_eq_gc_two_add_one (t : ℝ) : Psi t = gc 2 t + 1 := by
  unfold Psi
  split_ifs with h
  · rw [gc_of_le h]; ring
  · rw [gc_of_ge (le_of_lt (not_le.mp h))]; ring

@[simp] lemma Psi_zero : Psi 0 = 1 := by norm_num [Psi]

lemma Psi_nonneg (t : ℝ) : 0 ≤ Psi t := by
  unfold Psi
  split_ifs with h
  · positivity
  · have : (2 : ℝ) < t := not_le.mp h
    linarith

lemma two_mul_sub_one_add_Psi_le {p nu : ℝ} (hp : 0 ≤ p) (hnu : 0 ≤ nu) :
    2 * p - 1 + Psi p ≤ (p - nu) ^ 2 + 4 * nu := by
  have h := sq_sub_ge_gc (c := 2) hp hnu (by norm_num)
  rw [Psi_eq_gc_two_add_one]
  linarith

lemma Psi_attained (p : ℝ) :
    (p - max (p - 2) 0) ^ 2 + 4 * max (p - 2) 0 = 2 * p - 1 + Psi p := by
  unfold Psi
  rcases le_or_gt p 2 with h | h
  · rw [max_eq_right (by linarith), if_pos h]; ring
  · rw [max_eq_left (by linarith), if_neg (not_le.mpr h)]; ring

section Eigen

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

def eigCols {P : Matrix n n 𝕜} (hP : P.PosSemidef) : n → n → 𝕜 :=
  fun j a => (hP.1.eigenvectorUnitary : Matrix n n 𝕜) a j

lemma wmat_eigCols {P : Matrix n n 𝕜} (hP : P.PosSemidef) :
    Wmat hP.1.eigenvalues (eigCols hP)
      = (hP.1.eigenvectorUnitary : Matrix n n 𝕜)
        * diagonal (fun j => ((Real.sqrt (hP.1.eigenvalues j) : ℝ) : 𝕜)) := by
  ext a j
  simp only [Wmat, eigCols, Matrix.mul_diagonal]
  ring

lemma pmat_eigCols {P : Matrix n n 𝕜} (hP : P.PosSemidef) :
    Pmat hP.1.eigenvalues (eigCols hP) = P := by
  have hdd : (fun j => ((Real.sqrt (hP.1.eigenvalues j) : ℝ) : 𝕜)
        * ((Real.sqrt (hP.1.eigenvalues j) : ℝ) : 𝕜))
      = RCLike.ofReal ∘ hP.1.eigenvalues := by
    funext j
    simp only [Function.comp_apply, ← RCLike.ofReal_mul]
    rw [Real.mul_self_sqrt (hP.eigenvalues_nonneg j)]
  have hstar : (diagonal (fun j => ((Real.sqrt (hP.1.eigenvalues j) : ℝ) : 𝕜)))ᴴ
      = diagonal (fun j => ((Real.sqrt (hP.1.eigenvalues j) : ℝ) : 𝕜)) := by
    rw [diagonal_conjTranspose]
    simp [RCLike.star_def]
  unfold Pmat
  rw [wmat_eigCols hP, conjTranspose_mul, hstar, ← Matrix.mul_assoc,
    Matrix.mul_assoc _ (diagonal _) (diagonal _), diagonal_mul_diagonal, hdd]
  conv_rhs => rw [hP.1.spectral_theorem, Unitary.conjStarAlgAut_apply]
  rfl

lemma xsq_eigCols {P : Matrix n n 𝕜} (hP : P.PosSemidef) (j : n) :
    xsq (eigCols hP) j = 1 := by
  have hDS := normSqMatrix_mem_doublyStochastic_of_unitary (hP.1.eigenvectorUnitary).2
  rw [mem_doublyStochastic_iff_sum] at hDS
  simpa [xsq, eigCols, normSqMatrix] using hDS.2.2 j

end Eigen

section Main

variable {𝕜 : Type*} [RCLike 𝕜] {n r : Type*} [Fintype n] [DecidableEq n]
  [Fintype r] [DecidableEq r]

lemma rtrace_self_mul_conjTranspose (V : Matrix n r 𝕜) :
    rtrace (V * Vᴴ) = ∑ j, ∑ i, ‖V i j‖ ^ 2 := by
  unfold rtrace
  rw [trace_mul_comm, Matrix.trace, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.diag_apply, Matrix.mul_apply, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.conjTranspose_apply, RCLike.star_def, RCLike.conj_mul]
  simp

lemma rtrace_specMap_Psi (V : Matrix n r 𝕜) :
    rtrace (specMap (isHermitian_conjTranspose_mul_self V) Psi)
      = (∑ i, gc 2 ((Matrix.posSemidef_self_mul_conjTranspose V).1.eigenvalues i))
        + (Fintype.card r : ℝ) := by
  rw [rtrace_specMap]
  have hshift : ∀ x : ℝ, Psi x = gc 2 x + 1 := Psi_eq_gc_two_add_one
  simp only [hshift]
  rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, mul_one, Finset.card_univ]
  congr 1
  exact (sum_eigenvalues_comm V (gc 2) (gc_zero (by norm_num))).symm

theorem stable_rank_trace_sharp (V : Matrix n r 𝕜)
    {Q : Matrix n n 𝕜} (hQ : Q.IsHermitian) {b : ℕ} (hb : posIndex hQ ≤ b) :
    2 * rtrace (V * Vᴴ) + 4 * rtrace Q - (Fintype.card r : ℝ) - 4 * b
        + rtrace (specMap (isHermitian_conjTranspose_mul_self V) Psi)
      ≤ frobSq (V * Vᴴ + Q) := by
  classical
  have hP : (V * Vᴴ).PosSemidef := Matrix.posSemidef_self_mul_conjTranspose V
  have hm : ∀ j, 0 ≤ hP.1.eigenvalues j := fun j => hP.eigenvalues_nonneg j
  have hR := rank_trace_mult hm (eigCols hP) hQ hb (c := 2) (by norm_num)
  rw [pmat_eigCols hP] at hR
  have hx : ∀ j, hP.1.eigenvalues j * xsq (eigCols hP) j = hP.1.eigenvalues j := by
    intro j; rw [xsq_eigCols hP j, mul_one]
  simp only [hx] at hR
  rw [rtrace_specMap_Psi V]
  have hcast : ((2 : ℝ) ^ 2) * (b : ℝ) = 4 * b := by norm_num
  linarith [hR]

theorem stable_rank_trace (V : Matrix n r 𝕜) (hV : ∀ j, ∑ i, ‖V i j‖ ^ 2 ≤ 1)
    {Q : Matrix n n 𝕜} (hQ : Q.IsHermitian) {b : ℕ} (hb : posIndex hQ ≤ b) :
    4 * rtrace (V * Vᴴ + Q) - 3 * (Fintype.card r : ℝ) - 4 * b
        + rtrace (specMap (isHermitian_conjTranspose_mul_self V) Psi)
      ≤ frobSq (V * Vᴴ + Q) := by
  have hsharp := stable_rank_trace_sharp V hQ hb
  have hle : rtrace (V * Vᴴ) ≤ (Fintype.card r : ℝ) := by
    rw [rtrace_self_mul_conjTranspose V]
    calc ∑ j, ∑ i, ‖V i j‖ ^ 2 ≤ ∑ _j : r, (1 : ℝ) := Finset.sum_le_sum fun j _ => hV j
      _ = (Fintype.card r : ℝ) := by simp
  rw [rtrace_add]
  linarith

theorem stable_rank_trace_no_defect (V : Matrix n r 𝕜) (hV : ∀ j, ∑ i, ‖V i j‖ ^ 2 ≤ 1)
    {Q : Matrix n n 𝕜} (hQ : Q.IsHermitian) {b : ℕ} (hb : posIndex hQ ≤ b) :
    4 * rtrace (V * Vᴴ + Q) - 3 * (Fintype.card r : ℝ) - 4 * b
      ≤ frobSq (V * Vᴴ + Q) := by
  have hP : (V * Vᴴ).PosSemidef := Matrix.posSemidef_self_mul_conjTranspose V
  have hr : (V * Vᴴ).rank ≤ Fintype.card r := by
    rw [Matrix.rank_self_mul_conjTranspose]
    exact Matrix.rank_le_card_width V
  have h := rank_trace_ineq_two hP hQ hr hb
  have hle : rtrace (V * Vᴴ) ≤ (Fintype.card r : ℝ) := by
    rw [rtrace_self_mul_conjTranspose V]
    calc ∑ j, ∑ i, ‖V i j‖ ^ 2 ≤ ∑ _j : r, (1 : ℝ) := Finset.sum_le_sum fun j _ => hV j
      _ = (Fintype.card r : ℝ) := by simp
  rw [rtrace_add]
  linarith

theorem stable_rank_trace_collapse (V : Matrix n r 𝕜) (hV : ∀ j, ∑ i, ‖V i j‖ ^ 2 ≤ 1)
    {Q : Matrix n n 𝕜} (hQ : Q.IsHermitian) {b : ℕ} (hb : posIndex hQ ≤ b) :
    4 * rtrace (V * Vᴴ + Q) - 3 * (Fintype.card r : ℝ) - 4 * b
      ≤ frobSq (V * Vᴴ + Q) := by
  have h := stable_rank_trace V hV hQ hb
  have hpos : 0 ≤ rtrace (specMap (isHermitian_conjTranspose_mul_self V) Psi) := by
    rw [rtrace_specMap]
    exact Finset.sum_nonneg fun j _ => Psi_nonneg _
  linarith

theorem sharp_le_stable (V : Matrix n r 𝕜) (hV : ∀ j, ∑ i, ‖V i j‖ ^ 2 ≤ 1)
    {Q : Matrix n n 𝕜} :
    4 * rtrace (V * Vᴴ + Q) - 3 * (Fintype.card r : ℝ)
      ≤ 2 * rtrace (V * Vᴴ) + 4 * rtrace Q - (Fintype.card r : ℝ) := by
  have hle : rtrace (V * Vᴴ) ≤ (Fintype.card r : ℝ) := by
    rw [rtrace_self_mul_conjTranspose V]
    calc ∑ j, ∑ i, ‖V i j‖ ^ 2 ≤ ∑ _j : r, (1 : ℝ) := Finset.sum_le_sum fun j _ => hV j
      _ = (Fintype.card r : ℝ) := by simp
  rw [rtrace_add]
  linarith

end Main


end Zeta23Ext.StableRankTrace

end

/-! ###### source module: Zeta23Ext/Bridge/Defs.lean ###### -/



noncomputable section
set_option linter.unusedSectionVars false

open Matrix Finset RHLinalg Filter
open scoped ComplexOrder BigOperators
open Zeta23 Zeta23.ZeroSide Zeta23.ThmD Zeta23Ext.StableRankTrace

namespace Zeta23Ext.Bridge

def Kfun (x : ℝ) : ℝ :=
  ∫ t in (-(1 : ℝ) / 2)..(1 / 2), Real.cos (Real.sqrt 2 * t) * Real.cos (2 * Real.pi * x * t)

def kfun (x : ℝ) : ℝ := Kfun x / Kfun 0

def wfun (x : ℝ) : ℝ := kfun x ^ 2

def ptsN (n : ℕ) (g : Fin (n - 1) → ℝ) (i : Fin n) : ℝ :=
  ∑ j : Fin (n - 1), if (j : ℕ) < (i : ℕ) then g j else 0

def F (n p : ℕ) (g : Fin (n - 1) → ℝ) : ℝ :=
  (1 / (p : ℝ)) * ∑ i, g i
    + ∑ i : Fin n, ∑ j : Fin n,
        if (i : ℕ) < (j : ℕ) then
          (2 / ((n : ℝ) - (((j : ℕ) - (i : ℕ) : ℕ) : ℝ))) * wfun (ptsN n g j - ptsN n g i)
        else 0

def pts (g : Fin 6 → ℝ) (i : Fin 7) : ℝ := ∑ j : Fin 6, if (j : ℕ) < (i : ℕ) then g j else 0

def F6 (p : ℕ) (g : Fin 6 → ℝ) : ℝ :=
  (1 / (p : ℝ)) * ∑ i, g i
    + ∑ i : Fin 7, ∑ j : Fin 7,
        if (i : ℕ) < (j : ℕ) then
          (2 / ((7 : ℝ) - (((j : ℕ) - (i : ℕ) : ℕ) : ℝ))) * wfun (pts g j - pts g i)
        else 0

theorem pts_eq_ptsN (g : Fin 6 → ℝ) (i : Fin 7) : pts g i = ptsN 7 g i := rfl

theorem F6_eq (p : ℕ) (g : Fin 6 → ℝ) : F6 p g = F 7 p g := rfl

section Blocks

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def energyOn (x : ι → ℝ) (B : Finset ι) : ℝ :=
  ∑ i ∈ B, ∑ j ∈ B, if i = j then 0 else wfun (x i - x j)

def offDiagSqOn (G : Matrix ι ι ℂ) (B : Finset ι) : ℝ :=
  ∑ i ∈ B, ∑ j ∈ B, if i = j then 0 else ‖G i j‖ ^ 2

def spanOf (x : ι → ℝ) (B : Finset ι) : ℝ :=
  if h : B.Nonempty then B.sup' h x - B.inf' h x else 0

def IsInterval (x : ι → ℝ) (B : Finset ι) : Prop :=
  ∀ i ∈ B, ∀ j ∈ B, ∀ k, x i ≤ x k → x k ≤ x j → k ∈ B

lemma abs_sub_le_spanOf (x : ι → ℝ) {B : Finset ι} {i j : ι} (hi : i ∈ B) (hj : j ∈ B) :
    |x i - x j| ≤ spanOf x B := by
  have hne : B.Nonempty := ⟨i, hi⟩
  unfold spanOf
  rw [dif_pos hne, abs_le]
  constructor
  · linarith [Finset.le_sup' x hj, Finset.inf'_le x hi]
  · linarith [Finset.le_sup' x hi, Finset.inf'_le x hj]

lemma spanOf_nonneg (x : ι → ℝ) (B : Finset ι) : 0 ≤ spanOf x B := by
  unfold spanOf
  split_ifs with h
  · obtain ⟨i, hi⟩ := h
    linarith [Finset.le_sup' x hi, Finset.inf'_le x hi]
  · exact le_rfl

def defect {M : Matrix ι ι ℂ} (hM : M.IsHermitian) : ℝ := rtrace (specMap hM Psi)

lemma defect_nonneg {M : Matrix ι ι ℂ} (hM : M.IsHermitian) : 0 ≤ defect hM := by
  unfold defect
  rw [rtrace_specMap]
  exact Finset.sum_nonneg fun _ _ => Psi_nonneg _

def blockDefect {M : Matrix ι ι ℂ} (hM : M.IsHermitian) (B : Finset ι) : ℝ :=
  defect (hM.submatrix (Subtype.val : B → ι))

lemma blockDefect_nonneg {M : Matrix ι ι ℂ} (hM : M.IsHermitian) (B : Finset ι) :
    0 ≤ blockDefect hM B :=
  defect_nonneg _

end Blocks

def Phi_n (n : ℕ) (c : ℝ) (m p : ℕ) : ℝ :=
  (HD 1 - ((n : ℝ) - 1) * ((m : ℝ) - 1) / ((p : ℝ) * m))
    / (1 - c * ((m : ℝ) - ((n : ℝ) - 1)) / m)

def Phi (c : ℝ) (m p : ℕ) : ℝ :=
  (HD 1 - 6 * ((m : ℝ) - 1) / ((p : ℝ) * m)) / (1 - c * ((m : ℝ) - 6) / m)

theorem Phi_eq_Phi_n (c : ℝ) (m p : ℕ) : Phi c m p = Phi_n 7 c m p := by
  unfold Phi Phi_n
  norm_num

section BlockLevel

variable {ι d : Type*} [Fintype ι] [DecidableEq ι] [Fintype d] [DecidableEq d]
variable (D : ZeroBlockData ι d)

def Vsimple (c : ℝ) : Matrix d D.S₁ ℂ := fun k z => D.v z k / (Real.sqrt c : ℂ)

def P₁ (c : ℝ) : Matrix d d ℂ := Vsimple D c * (Vsimple D c)ᴴ

def Q' (c : ℝ) : Matrix d d ℂ := D.blockP c + D.blockQ c - P₁ D c

def gramS₁ (c : ℝ) : Matrix D.S₁ D.S₁ ℂ := (Vsimple D c)ᴴ * Vsimple D c

lemma P₁_posSemidef (c : ℝ) : (P₁ D c).PosSemidef := posSemidef_self_mul_conjTranspose _

lemma gramS₁_isHermitian (c : ℝ) : (gramS₁ D c).IsHermitian :=
  isHermitian_conjTranspose_mul_self _

lemma gramS₁_posSemidef (c : ℝ) : (gramS₁ D c).PosSemidef :=
  posSemidef_conjTranspose_mul_self _

lemma blockP_isHermitian (c : ℝ) : (D.blockP c).IsHermitian :=
  ZeroBlockData.isHermitian_real_smul D.onPart_posSemidef.isHermitian _

lemma Q'_isHermitian (c : ℝ) : (Q' D c).IsHermitian :=
  ((blockP_isHermitian D c).add (D.blockQ_isHermitian c)).sub (P₁_posSemidef D c).1

lemma P₁_add_Q' (c : ℝ) : P₁ D c + Q' D c = D.blockP c + D.blockQ c := by
  unfold Q'; abel

end BlockLevel

section Concrete

open Classical

def mtParams (T : ℝ) : Params := (paramsOf stdProfile 1).atD T

variable (Z : ZeroConfig) (P : Params) (T : ℝ)

def xnorm (ρ : ℂ) : ℝ := P.L T * (ρ.im - T) / (2 * Real.pi)

def aL2 : ℝ := P.a T * P.L T ^ 2

def bdata : ZeroBlockData (ZI Z T) (Fin (P.d T)) := blockData Z T P phiHatConj

def retained : Finset (ZI Z T) :=
  (bdata Z P T).S₁.filter fun z =>
    P.L T ^ 2 ≤ xnorm P T z ∧ xnorm P T z ≤ (P.d T : ℝ) - P.L T ^ 2

lemma mem_S₁_of_mem_retained {z : ZI Z T} (hz : z ∈ retained Z P T) : z ∈ (bdata Z P T).S₁ :=
  (Finset.mem_filter.mp hz).1

def toS₁ : retained Z P T → (bdata Z P T).S₁ :=
  fun z => ⟨z.1, mem_S₁_of_mem_retained Z P T z.2⟩

lemma toS₁_injective : Function.Injective (toS₁ Z P T) :=
  fun _ _ h => Subtype.ext (congrArg (Subtype.val : (bdata Z P T).S₁ → ZI Z T) h)

def gram : Matrix (retained Z P T) (retained Z P T) ℂ :=
  (gramS₁ (bdata Z P T) (aL2 P T)).submatrix (toS₁ Z P T) (toS₁ Z P T)

lemma gram_isHermitian : (gram Z P T).IsHermitian :=
  (gramS₁_isHermitian _ _).submatrix _

lemma gram_posSemidef : (gram Z P T).PosSemidef :=
  (gramS₁_posSemidef _ _).submatrix _

def Dcirc : ℝ := defect (gram_isHermitian Z P T)

def xret : retained Z P T → ℝ := fun z => xnorm P T (z.1 : ℂ)

lemma re_eq_half_of_mem_S₁ {z : ZI Z T} (hz : z ∈ (bdata Z P T).S₁) : (z : ℂ).re = 1 / 2 := by
  have h : (bdata Z P T).σ z = z := by
    simp only [ZeroBlockData.S₁, Finset.mem_filter, Finset.mem_univ, true_and] at hz
    exact hz.1
  exact (mkData_σ_eq_iff Z T _ _ z).mp h

lemma xret_injective (hL : 0 < P.L T) : Function.Injective (xret Z P T) := by
  intro z z' h
  have hz := re_eq_half_of_mem_S₁ Z P T (mem_S₁_of_mem_retained Z P T z.2)
  have hz' := re_eq_half_of_mem_S₁ Z P T (mem_S₁_of_mem_retained Z P T z'.2)
  unfold xret xnorm at h
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  have him : (z.1 : ℂ).im = (z'.1 : ℂ).im := by
    have h1 := (div_left_inj' hpi.ne').mp h
    have h2 := mul_left_cancel₀ hL.ne' h1
    linarith
  apply Subtype.ext; apply Subtype.ext
  exact Complex.ext (by rw [hz, hz']) him

end Concrete


end Zeta23Ext.Bridge

end

/-! ###### source module: Zeta23Ext/Bridge/Helpers_finite.lean ###### -/



noncomputable section
set_option linter.unusedSectionVars false

open Finset
open scoped BigOperators

namespace Zeta23Ext.Bridge

lemma Kfun_neg (x : ℝ) : Kfun (-x) = Kfun x := by
  unfold Kfun
  simp only [mul_neg, neg_mul, Real.cos_neg]

lemma kfun_neg (x : ℝ) : kfun (-x) = kfun x := by
  unfold kfun; rw [Kfun_neg]

lemma wfun_neg (x : ℝ) : wfun (-x) = wfun x := by
  unfold wfun; rw [kfun_neg]

lemma wfun_sub_comm (a b : ℝ) : wfun (a - b) = wfun (b - a) := by
  rw [← wfun_neg, neg_sub]

lemma wfun_nonneg (x : ℝ) : 0 ≤ wfun x := sq_nonneg _

lemma cos_sqrt_two_mul_nonneg {t : ℝ} (ht : t ∈ Set.Icc (-(1 : ℝ) / 2) (1 / 2)) :
    0 ≤ Real.cos (Real.sqrt 2 * t) := by
  obtain ⟨h1, h2⟩ := ht
  have hs : Real.sqrt 2 < 2 := by
    rw [show (2 : ℝ) = Real.sqrt 4 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have hs0 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  apply Real.cos_nonneg_of_mem_Icc
  constructor
  · nlinarith [Real.pi_gt_three]
  · nlinarith [Real.pi_gt_three]

lemma abs_Kfun_le_Kfun_zero (x : ℝ) : |Kfun x| ≤ Kfun 0 := by
  unfold Kfun
  have hle : (-(1 : ℝ) / 2) ≤ 1 / 2 := by norm_num
  simp only [mul_zero, zero_mul, Real.cos_zero, mul_one]
  refine (intervalIntegral.abs_integral_le_integral_abs hle).trans ?_
  refine intervalIntegral.integral_mono_on hle ?_ ?_ ?_
  · exact Continuous.intervalIntegrable (by fun_prop) _ _
  · exact Continuous.intervalIntegrable (by fun_prop) _ _
  · intro t ht
    rw [abs_mul, abs_of_nonneg (cos_sqrt_two_mul_nonneg ht)]
    calc Real.cos (Real.sqrt 2 * t) * |Real.cos (2 * Real.pi * x * t)|
        ≤ Real.cos (Real.sqrt 2 * t) * 1 :=
          mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (cos_sqrt_two_mul_nonneg ht)
      _ = Real.cos (Real.sqrt 2 * t) := mul_one _

lemma abs_kfun_le_one (x : ℝ) : |kfun x| ≤ 1 := by
  unfold kfun
  rw [abs_div]
  rcases eq_or_ne (Kfun 0) 0 with h | h
  · rw [h, abs_zero, div_zero]; exact zero_le_one
  · rw [div_le_one (abs_pos.mpr h)]
    exact (abs_Kfun_le_Kfun_zero x).trans (le_abs_self _)

lemma wfun_le_one (x : ℝ) : wfun x ≤ 1 := by
  unfold wfun
  rw [← sq_abs]
  exact pow_le_one₀ (abs_nonneg _) (abs_kfun_le_one x)

section Sorted

variable {m : ℕ}

def sortedExt (y : Fin m → ℝ) (n : ℕ) : ℝ := if h : n < m then y ⟨n, h⟩ else 0

lemma sortedExt_of_lt (y : Fin m → ℝ) {n : ℕ} (h : n < m) : sortedExt y n = y ⟨n, h⟩ := by
  unfold sortedExt; rw [dif_pos h]

lemma sortedExt_mono {y : Fin m → ℝ} (hy : StrictMono y) {a b : ℕ} (hab : a ≤ b) (hb : b < m) :
    sortedExt y a ≤ sortedExt y b := by
  rw [sortedExt_of_lt y (lt_of_le_of_lt hab hb), sortedExt_of_lt y hb]
  exact hy.monotone (Fin.mk_le_mk.mpr hab)

def windowGaps (n : ℕ) (Y : ℕ → ℝ) (i : ℕ) : Fin (n - 1) → ℝ :=
  fun j => Y (i + ((j : ℕ) + 1)) - Y (i + j)

lemma range_filter_lt {N k : ℕ} (hk : k ≤ N) : ((range N).filter fun j => j < k) = range k := by
  ext j
  simp only [mem_filter, mem_range]
  omega

lemma ptsN_windowGaps (n : ℕ) (Y : ℕ → ℝ) (i : ℕ) (k : Fin n) :
    ptsN n (windowGaps n Y i) k = Y (i + k) - Y i := by
  have hk : (k : ℕ) ≤ n - 1 := by have := k.2; omega
  unfold ptsN windowGaps
  rw [Fin.sum_univ_eq_sum_range
    (fun j => if j < (k : ℕ) then Y (i + (j + 1)) - Y (i + j) else 0) (n - 1),
    ← sum_filter, range_filter_lt hk]
  have := Finset.sum_range_sub (fun j => Y (i + j)) (k : ℕ)
  simpa using this

lemma sum_windowGaps (n : ℕ) (Y : ℕ → ℝ) (i : ℕ) :
    ∑ j, windowGaps n Y i j = Y (i + (n - 1)) - Y i := by
  unfold windowGaps
  rw [Fin.sum_univ_eq_sum_range (fun j => Y (i + (j + 1)) - Y (i + j)) (n - 1)]
  have := Finset.sum_range_sub (fun j => Y (i + j)) (n - 1)
  simpa using this

lemma F_windowGaps (n p : ℕ) (Y : ℕ → ℝ) (i : ℕ) :
    F n p (windowGaps n Y i) = (1 / (p : ℝ)) * (Y (i + (n - 1)) - Y i)
      + ∑ a : Fin n, ∑ b : Fin n,
          if (a : ℕ) < (b : ℕ) then
            (2 / ((n : ℝ) - (((b : ℕ) - (a : ℕ) : ℕ) : ℝ))) * wfun (Y (i + b) - Y (i + a))
          else 0 := by
  unfold F
  rw [sum_windowGaps]
  congr 1
  refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => ?_
  rw [ptsN_windowGaps, ptsN_windowGaps,
    show Y (i + ↑b) - Y i - (Y (i + ↑a) - Y i) = Y (i + ↑b) - Y (i + ↑a) by ring]

lemma sum_shift_sub (f : ℕ → ℝ) (d N : ℕ) :
    ∑ i ∈ range N, (f (i + d) - f i) = ∑ i ∈ range d, (f (N + i) - f i) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_range_succ, ih]
    have h1 : ∑ i ∈ range d, (f (N + 1 + i) - f i) = ∑ i ∈ range d, (f (N + (i + 1)) - f i) :=
      sum_congr rfl fun i _ => by rw [Nat.add_right_comm, Nat.add_assoc]
    have h2 : ∑ i ∈ range d, f (N + (i + 1)) = ∑ i ∈ range d, f (N + i) + f (N + d) - f (N + 0) := by
      have := sum_range_succ' (fun i => f (N + i)) d
      rw [sum_range_succ] at this
      linarith
    rw [h1, sum_sub_distrib, sum_sub_distrib, h2]
    simp only [add_zero]
    ring

end Sorted


end Zeta23Ext.Bridge

end

/-! ###### source module: Zeta23Ext/Bridge/Helpers_pinching.lean ###### -/



noncomputable section
set_option linter.unusedSectionVars false

open Matrix Finset RHLinalg
open scoped ComplexOrder BigOperators

namespace Zeta23Ext.Bridge

section PsiConvex
open Zeta23Ext.StableRankTrace

lemma affine_le_Psi {s x : ℝ} (hs : s ≤ 2) : 2 * (s - 1) * x - (s ^ 2 - 1) ≤ Psi x := by
  unfold Psi
  split_ifs with h
  · nlinarith [sq_nonneg (x - s)]
  · have hx : 2 < x := not_le.mp h
    nlinarith [mul_nonneg (sub_nonneg.mpr hs) (by linarith : (0 : ℝ) ≤ 2 * x - 2 - s)]

lemma affine_eq_Psi (x : ℝ) : 2 * (min x 2 - 1) * x - ((min x 2) ^ 2 - 1) = Psi x := by
  unfold Psi
  rcases le_or_gt x 2 with h | h
  · rw [min_eq_left h, if_pos h]; ring
  · rw [min_eq_right h.le, if_neg (not_le.mpr h)]; ring

theorem Psi_convexOn : ConvexOn ℝ Set.univ Psi := by
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
  simp only [smul_eq_mul]
  set z := a * x + b * y with hz
  set t := min z 2 with ht
  have ht2 : t ≤ 2 := min_le_right _ _
  have hx := affine_le_Psi (x := x) ht2
  have hy := affine_le_Psi (x := y) ht2
  have hsplit : 2 * (t - 1) * z - (t ^ 2 - 1)
      = a * (2 * (t - 1) * x - (t ^ 2 - 1)) + b * (2 * (t - 1) * y - (t ^ 2 - 1)) := by
    rw [hz]; linear_combination (t ^ 2 - 1) * hab
  calc Psi z = 2 * (t - 1) * z - (t ^ 2 - 1) := (affine_eq_Psi z).symm
    _ = a * (2 * (t - 1) * x - (t ^ 2 - 1)) + b * (2 * (t - 1) * y - (t ^ 2 - 1)) := hsplit
    _ ≤ a * Psi x + b * Psi y :=
        add_le_add (mul_le_mul_of_nonneg_left hx ha) (mul_le_mul_of_nonneg_left hy hb)

end PsiConvex

section Entries

variable {𝕜 : Type*} [RCLike 𝕜] {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

lemma re_mul_conjTranspose_apply_self (Y : Matrix κ ι 𝕜) (j : κ) :
    RCLike.re ((Y * Yᴴ) j j) = ∑ i, ‖Y j i‖ ^ 2 := by
  rw [Matrix.mul_apply, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [conjTranspose_apply, RCLike.star_def, RCLike.mul_conj]
  simp

lemma re_conjTranspose_mul_apply_self (Y : Matrix κ ι 𝕜) (i : ι) :
    RCLike.re ((Yᴴ * Y) i i) = ∑ j, ‖Y j i‖ ^ 2 := by
  rw [Matrix.mul_apply, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [conjTranspose_apply, RCLike.star_def, RCLike.conj_mul]
  simp

lemma re_mul_diagonal_mul_conjTranspose_apply (Y : Matrix κ ι 𝕜) (d : ι → ℝ) (j : κ) :
    RCLike.re ((Y * (diagonal (RCLike.ofReal ∘ d) : Matrix ι ι 𝕜) * Yᴴ : Matrix κ κ 𝕜) j j)
      = ∑ i, ‖Y j i‖ ^ 2 * d i := by
  rw [Matrix.mul_apply, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_diagonal, conjTranspose_apply, Function.comp_apply, RCLike.star_def,
    show Y j i * (d i : 𝕜) * starRingEnd 𝕜 (Y j i) = (d i : 𝕜) * (Y j i * starRingEnd 𝕜 (Y j i))
      by ring,
    RCLike.mul_conj,
    show ((d i : 𝕜) * ((‖Y j i‖ : 𝕜) ^ 2) : 𝕜) = ((‖Y j i‖ ^ 2 * d i : ℝ) : 𝕜) by push_cast; ring,
    RCLike.ofReal_re]

lemma sum_normSq_col_eigenvectorUnitary {M : Matrix ι ι 𝕜} (hM : M.IsHermitian) (i : ι) :
    ∑ k, ‖(hM.eigenvectorUnitary : Matrix ι ι 𝕜) k i‖ ^ 2 = 1 := by
  have h := re_conjTranspose_mul_apply_self (hM.eigenvectorUnitary : Matrix ι ι 𝕜) i
  rw [← star_eq_conjTranspose, Unitary.star_mul_self_of_mem hM.eigenvectorUnitary.2] at h
  simpa using h.symm

end Entries

section Mix

variable {𝕜 : Type*} [RCLike 𝕜] {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

def compressWeight {M : Matrix ι ι 𝕜} (hM : M.IsHermitian) (g : κ → ι) (i : ι) : ℝ :=
  ∑ j, ‖(hM.eigenvectorUnitary : Matrix ι ι 𝕜) (g j) i‖ ^ 2

lemma compressWeight_nonneg {M : Matrix ι ι 𝕜} (hM : M.IsHermitian) (g : κ → ι) (i : ι) :
    0 ≤ compressWeight hM g i :=
  Finset.sum_nonneg fun _ _ => by positivity

lemma compressWeight_le_one {M : Matrix ι ι 𝕜} (hM : M.IsHermitian) {g : κ → ι}
    (hg : Function.Injective g) (i : ι) : compressWeight hM g i ≤ 1 := by
  unfold compressWeight
  calc ∑ j, ‖(hM.eigenvectorUnitary : Matrix ι ι 𝕜) (g j) i‖ ^ 2
      = ∑ k ∈ univ.image g, ‖(hM.eigenvectorUnitary : Matrix ι ι 𝕜) k i‖ ^ 2 :=
        (Finset.sum_image (f := fun k => ‖(hM.eigenvectorUnitary : Matrix ι ι 𝕜) k i‖ ^ 2)
          (s := univ) (g := g) hg.injOn).symm
    _ ≤ ∑ k, ‖(hM.eigenvectorUnitary : Matrix ι ι 𝕜) k i‖ ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun _ _ _ => by positivity
    _ = 1 := sum_normSq_col_eigenvectorUnitary hM i

lemma sum_compressWeight_fiberwise {M : Matrix ι ι 𝕜} (hM : M.IsHermitian) (β : ι → κ) (i : ι) :
    ∑ b, compressWeight hM (Subtype.val : (univ.filter fun i => β i = b) → ι) i = 1 := by
  unfold compressWeight
  have h : ∀ b : κ, ∑ j : (univ.filter fun i => β i = b),
      ‖(hM.eigenvectorUnitary : Matrix ι ι 𝕜) (j : ι) i‖ ^ 2
        = ∑ j ∈ univ.filter (fun i => β i = b), ‖(hM.eigenvectorUnitary : Matrix ι ι 𝕜) j i‖ ^ 2 :=
    fun b => Finset.sum_coe_sort (univ.filter fun i => β i = b)
      (fun j => ‖(hM.eigenvectorUnitary : Matrix ι ι 𝕜) j i‖ ^ 2)
  simp only [h]
  rw [Finset.sum_fiberwise univ β (fun j => ‖(hM.eigenvectorUnitary : Matrix ι ι 𝕜) j i‖ ^ 2)]
  exact sum_normSq_col_eigenvectorUnitary hM i

theorem eigenvalues_submatrix_eq_mix {M : Matrix ι ι 𝕜} (hM : M.IsHermitian) {g : κ → ι}
    (hg : Function.Injective g) :
    ∃ S : κ → ι → ℝ, (∀ j i, 0 ≤ S j i) ∧ (∀ j, ∑ i, S j i = 1)
      ∧ (∀ i, ∑ j, S j i = compressWeight hM g i)
      ∧ ∀ j, (hM.submatrix g).eigenvalues j = ∑ i, S j i * hM.eigenvalues i := by
  set U : Matrix ι ι 𝕜 := (hM.eigenvectorUnitary : Matrix ι ι 𝕜) with hUdef
  have hP : (M.submatrix g g).IsHermitian := hM.submatrix g
  set V : Matrix κ κ 𝕜 := (hP.eigenvectorUnitary : Matrix κ κ 𝕜) with hVdef
  set Ug : Matrix κ ι 𝕜 := U.submatrix g id with hUgdef
  set Y : Matrix κ ι 𝕜 := star V * Ug with hYdef
  have hUU : U * star U = 1 := Unitary.mul_star_self_of_mem hM.eigenvectorUnitary.2
  have hVsV : star V * V = 1 := Unitary.star_mul_self_of_mem hP.eigenvectorUnitary.2
  have hVVs : V * star V = 1 := Unitary.mul_star_self_of_mem hP.eigenvectorUnitary.2

  have hM' : M = U * (diagonal (RCLike.ofReal ∘ hM.eigenvalues) : Matrix ι ι 𝕜) * star U := by
    conv_lhs => rw [hM.spectral_theorem, Unitary.conjStarAlgAut_apply]

  have hUgUg : Ug * Ugᴴ = 1 := by
    rw [hUgdef, conjTranspose_submatrix, ← star_eq_conjTranspose,
      ← Matrix.submatrix_mul _ _ g id g Function.bijective_id, hUU, submatrix_one _ hg]
  have hPsub : M.submatrix g g = Ug * (diagonal (RCLike.ofReal ∘ hM.eigenvalues) : Matrix ι ι 𝕜) * Ugᴴ := by
    conv_lhs => rw [hM']
    rw [Matrix.submatrix_mul _ _ g id g Function.bijective_id,
      Matrix.submatrix_mul _ _ g id id Function.bijective_id, submatrix_id_id, hUgdef,
      conjTranspose_submatrix, star_eq_conjTranspose]

  have hdiag0 : diagonal (RCLike.ofReal ∘ hP.eigenvalues) = star V * M.submatrix g g * V := by
    rw [← hP.conjStarAlgAut_star_eigenvectorUnitary, Unitary.conjStarAlgAut_star_apply]
  have hdiag : diagonal (RCLike.ofReal ∘ hP.eigenvalues)
      = Y * (diagonal (RCLike.ofReal ∘ hM.eigenvalues) : Matrix ι ι 𝕜) * Yᴴ := by
    rw [hdiag0, hPsub, hYdef, conjTranspose_mul, star_eq_conjTranspose V,
      conjTranspose_conjTranspose]
    simp only [Matrix.mul_assoc]
  have hYY : Y * Yᴴ = 1 := by
    rw [hYdef, conjTranspose_mul, star_eq_conjTranspose V, conjTranspose_conjTranspose,
      Matrix.mul_assoc, ← Matrix.mul_assoc Ug, hUgUg, Matrix.one_mul, ← star_eq_conjTranspose,
      hVsV]
  have hYtY : Yᴴ * Y = Ugᴴ * Ug := by
    rw [hYdef, conjTranspose_mul, star_eq_conjTranspose V, conjTranspose_conjTranspose,
      Matrix.mul_assoc, ← Matrix.mul_assoc V, ← star_eq_conjTranspose V, hVVs, Matrix.one_mul]
  refine ⟨fun j i => ‖Y j i‖ ^ 2, fun j i => by positivity, ?_, ?_, ?_⟩
  · intro j
    show ∑ i, ‖Y j i‖ ^ 2 = 1
    have h := re_mul_conjTranspose_apply_self Y j
    rw [hYY] at h
    simpa using h.symm
  · intro i
    show ∑ j, ‖Y j i‖ ^ 2 = compressWeight hM g i
    have h1 := re_conjTranspose_mul_apply_self Y i
    have h2 := re_conjTranspose_mul_apply_self Ug i
    rw [hYtY] at h1
    rw [← h1, h2]
    rfl
  · intro j
    show hP.eigenvalues j = ∑ i, ‖Y j i‖ ^ 2 * hM.eigenvalues i
    have h := re_mul_diagonal_mul_conjTranspose_apply Y hM.eigenvalues j
    rw [← hdiag, diagonal_apply_eq, Function.comp_apply, RCLike.ofReal_re] at h
    exact h

end Mix

section Pinching

variable {𝕜 : Type*} [RCLike 𝕜] {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

theorem sum_eigenvalues_submatrix_le {M : Matrix ι ι 𝕜} (hM : M.IsHermitian) {g : κ → ι}
    (hg : Function.Injective g) {f : ℝ → ℝ} (hf : ConvexOn ℝ Set.univ f) :
    ∑ j, f ((hM.submatrix g).eigenvalues j)
      ≤ ∑ i, compressWeight hM g i * f (hM.eigenvalues i) := by
  obtain ⟨S, hS0, hSrow, hScol, hSeig⟩ := eigenvalues_submatrix_eq_mix hM hg
  calc ∑ j, f ((hM.submatrix g).eigenvalues j)
      = ∑ j, f (∑ i, S j i * hM.eigenvalues i) := by simp only [hSeig]
    _ ≤ ∑ j, ∑ i, S j i * f (hM.eigenvalues i) := by
        refine Finset.sum_le_sum fun j _ => ?_
        have h := hf.map_sum_le (t := Finset.univ) (w := S j) (p := hM.eigenvalues)
          (fun i _ => hS0 j i) (hSrow j) (fun i _ => Set.mem_univ _)
        simpa only [smul_eq_mul] using h
    _ = ∑ i, (∑ j, S j i) * f (hM.eigenvalues i) := by
        rw [Finset.sum_comm]; simp only [Finset.sum_mul]
    _ = ∑ i, compressWeight hM g i * f (hM.eigenvalues i) := by simp only [hScol]

theorem sum_eigenvalues_pinching_le {M : Matrix ι ι 𝕜} (hM : M.IsHermitian) {f : ℝ → ℝ}
    (hf : ConvexOn ℝ Set.univ f) (β : ι → κ) :
    ∑ b, ∑ j, f ((hM.submatrix (Subtype.val : (univ.filter fun i => β i = b) → ι)).eigenvalues j)
      ≤ ∑ i, f (hM.eigenvalues i) := by
  calc ∑ b, ∑ j, f ((hM.submatrix (Subtype.val : (univ.filter fun i => β i = b) → ι)).eigenvalues j)
      ≤ ∑ b, ∑ i, compressWeight hM (Subtype.val : (univ.filter fun i => β i = b) → ι) i
            * f (hM.eigenvalues i) :=
        Finset.sum_le_sum fun b _ => sum_eigenvalues_submatrix_le hM Subtype.val_injective hf
    _ = ∑ i, (∑ b, compressWeight hM (Subtype.val : (univ.filter fun i => β i = b) → ι) i)
            * f (hM.eigenvalues i) := by
        rw [Finset.sum_comm]; simp only [Finset.sum_mul]
    _ = ∑ i, f (hM.eigenvalues i) := by simp only [sum_compressWeight_fiberwise, one_mul]

theorem sum_eigenvalues_submatrix_le_of_nonneg {M : Matrix ι ι 𝕜} (hM : M.IsHermitian)
    {g : κ → ι} (hg : Function.Injective g) {f : ℝ → ℝ} (hf : ConvexOn ℝ Set.univ f)
    (hf0 : ∀ t, 0 ≤ f t) :
    ∑ j, f ((hM.submatrix g).eigenvalues j) ≤ ∑ i, f (hM.eigenvalues i) :=
  (sum_eigenvalues_submatrix_le hM hg hf).trans <| Finset.sum_le_sum fun i _ => by
    calc compressWeight hM g i * f (hM.eigenvalues i) ≤ 1 * f (hM.eigenvalues i) :=
          mul_le_mul_of_nonneg_right (compressWeight_le_one hM hg i) (hf0 _)
      _ = f (hM.eigenvalues i) := one_mul _

theorem rtrace_specMap_pinching_le {M : Matrix ι ι 𝕜} (hM : M.IsHermitian) {f : ℝ → ℝ}
    (hf : ConvexOn ℝ Set.univ f) (β : ι → κ) :
    ∑ b, rtrace (specMap (hM.submatrix (Subtype.val : (univ.filter fun i => β i = b) → ι)) f)
      ≤ rtrace (specMap hM f) := by
  simp only [rtrace_specMap]
  exact sum_eigenvalues_pinching_le hM hf β

theorem rtrace_specMap_submatrix_le {M : Matrix ι ι 𝕜} (hM : M.IsHermitian) {g : κ → ι}
    (hg : Function.Injective g) {f : ℝ → ℝ} (hf : ConvexOn ℝ Set.univ f) (hf0 : ∀ t, 0 ≤ f t) :
    rtrace (specMap (hM.submatrix g) f) ≤ rtrace (specMap hM f) := by
  rw [rtrace_specMap, rtrace_specMap]
  exact sum_eigenvalues_submatrix_le_of_nonneg hM hg hf hf0

end Pinching


end Zeta23Ext.Bridge

end

/-! ###### source module: Zeta23Ext/Bridge/Helpers_S8.lean ###### -/



noncomputable section
set_option linter.unusedSectionVars false

open Filter Asymptotics Topology Real RHLinalg
open Zeta23 Zeta23.ThmD Zeta23.Assembly

namespace Zeta23Ext.Bridge

theorem seamA_mult2_defect {Z : ZeroConfig} {P : Params} {T : ℝ} (hT : 0 ≤ T)
    {θ₀ : ℝ} (hTl : TailInputs Z P T θ₀) (ha : 0 < P.a T) (hL : 0 < P.L T)
    {D : ℝ}
    (hcore : 4 * rtrace (P.hat T (Z.Az P T)) - frobSq (P.hat T (Z.Az P T))
      - 2 * (Z.NIprime T : ℝ) + D ≤ (Z.s1 T : ℝ)) :
    4 * rtrace (P.hat T (Z.Gz P T)) - frobSq (P.hat T (Z.Gz P T)) - 2 * (Z.N T (2 * T) : ℝ)
      - 3 * (NII Z T : ℝ)
      - θ₀ / (P.a T * P.L T)
          * (4 + 2 * Real.sqrt (frobSq (P.hat T (Z.Gz P T))) + θ₀ / (P.a T * P.L T))
      + D ≤ Z.N0s T (2 * T) := by
  obtain ⟨Bc, hB0, htrE, hfrE, hBle⟩ := hTl.hat
  have hGAE : P.hat T (Z.Gz P T) = P.hat T (Z.Az P T) + P.hat T (Z.Ez P T) := by
    rw [← hat_add]; congr 1; simp [ZeroConfig.Ez]
  have hB₀ : 0 ≤ θ₀ / (P.a T * P.L T) := div_nonneg hTl.theta_nonneg (mul_pos ha hL).le

  have hpert := ctr_sub_frobSq_perturb 4 (by norm_num) hGAE hB₀ (htrE.trans hBle)
    (hfrE.trans (pow_le_pow_left₀ hB0 hBle 2))
  have hs1 : (Z.s1 T : ℝ) ≤ (Z.N0s T (2 * T) : ℝ) + (NII Z T : ℝ) := by
    exact_mod_cast s1_le Z hT
  have hNI : (Z.NIprime T : ℝ) = (Z.N T (2 * T) : ℝ) + (NII Z T : ℝ) := by
    exact_mod_cast NIprime_eq Z hT
  rw [hNI] at hcore
  linarith [hcore, hpert, hs1]

theorem endgame_defect (Z : ZeroConfig) (H : PaperInputs Z) (P : Params) (hP : P.Valid)
    (aT bT JT trG trG2 : ℝ → ℝ)
    (hTr : TracesBoundsD P aT bT JT trG trG2 (fun T => (Z.N T (2 * T) : ℝ)))
    {c : ℝ} (hc0 : 0 < c)
    (hc : Tendsto (fun T => cRatio (P.lam1 T) (aT T) (bT T) (JT T)) atTop (𝓝 c))
    (ha : ∀ᶠ T in atTop, 1 / 2 ≤ aT T ∧ aT T ≤ 1)
    (θ₀ : ℝ → ℝ) (hTail : ∀ᶠ T in atTop, TailInputs Z (P.atD T) T (θ₀ T))
    (hθ₀ : ∃ C : ℝ, ∀ᶠ T in atTop, θ₀ T ≤ C * l T * T ^ (P.lam / 2 - 1))
    (hNII : ∃ C : ℝ, ∀ᶠ T in atTop, (NII Z T : ℝ) ≤ C * Real.sqrt T * l T)
    (hGzGp : ∀ᶠ T in atTop, Z.Gz (P.atD T) T = (P.atD T).Gp T)
    (hId : ∀ᶠ T in atTop, (P.atD T).trGtilde T = trG T ∧ (P.atD T).trGtildeSq T = trG2 T ∧
      (P.atD T).a T = aT T)
    (hcalE : Tendsto P.calE atTop (𝓝 0))
    (D : ℝ → ℝ)
    (hcore : ∀ᶠ T in atTop,
      4 * rtrace ((P.atD T).hat T (Z.Az (P.atD T) T))
        - frobSq ((P.atD T).hat T (Z.Az (P.atD T) T))
        - 2 * (Z.NIprime T : ℝ) + D T ≤ (Z.s1 T : ℝ)) :
    ∀ ε > 0, ∀ᶠ T in atTop,
      (2 - c⁻¹ - ε) * (Z.N T (2 * T) : ℝ) + D T ≤ (Z.N0s T (2 * T) : ℝ) := by
  have hlam0 := hP.lam_pos
  have hlam1 : P.lam ≤ 1 := hP.lam_le_one
  obtain ⟨C₁, hC₁, T₁, htr1⟩ := hTr.tr1
  obtain ⟨C₂, hC₂, T₂, hfr2⟩ := hTr.frhat
  obtain ⟨Cθ, hθ⟩ := hθ₀
  obtain ⟨CII, hII⟩ := hNII

  set N : ℝ → ℝ := fun T => (Z.N T (2 * T) : ℝ) with hNdef
  set cinv : ℝ → ℝ := fun T => (cRatio (P.lam1 T) (aT T) (bT T) (JT T))⁻¹ with hcinv
  set R₁ : ℝ → ℝ := fun T => C₁ * Real.sqrt (P.X T) / aT T with hR₁
  set R₂ : ℝ → ℝ := fun T => C₂ * P.calE T * (cinv T * N T) with hR₂
  set B : ℝ → ℝ := fun T => θ₀ T / (aT T * P.L T) with hBdef
  set err : ℝ → ℝ := fun T => (4 * R₁ T + R₂ T + 3 * (NII Z T : ℝ)
      + B T * (4 + 2 * Real.sqrt (cinv T * N T + R₂ T) + B T)) + |cinv T - c⁻¹| * N T with herr

  have hcinv_to : Tendsto cinv atTop (𝓝 c⁻¹) := hc.inv₀ hc0.ne'

  have hmain : ∀ᶠ T in atTop,
      (2 - c⁻¹) * N T - err T ≤ (Z.N0s T (2 * T) : ℝ) - D T := by
    filter_upwards [hcore, hTail, hGzGp, hId, ha, eventually_ge_atTop T₁,
      eventually_ge_atTop T₂, eventually_ge_atTop (0:ℝ), eventually_l_pos,
      eventually_calE_nonneg P hlam0 (zero_le_one.trans hP.one_le_w), eventually_w8 hP]
      with T hcoreT hTl hGG hid ha2 hT₁ hT₂ hT0 hl hE0 h8
    obtain ⟨hidtr, hidfr, hida⟩ := hid
    have hapos' : 0 < aT T := by linarith [ha2.1]
    have haposD : 0 < (P.atD T).a T := by rw [hida]; exact hapos'
    have hLpos : 0 < P.L T := by simp only [Params.L]; positivity

    have hA := seamA_mult2_defect hT0 hTl haposD hLpos hcoreT

    have hrt : rtrace ((P.atD T).hat T (Z.Gz (P.atD T) T)) = (aT T * P.L T)⁻¹ * trG T := by
      rw [rtrace_hat, hGG, rtrace_tilde_Gp, hidtr, hida]; rfl
    have hfr : frobSq ((P.atD T).hat T (Z.Gz (P.atD T) T))
        = ((aT T * P.L T)⁻¹) ^ 2 * trG2 T := by
      rw [frobSq_hat, hGG, frobSq_tilde_Gp, hidfr, hida]; rfl
    have haL : (P.atD T).a T * (P.atD T).L T = aT T * P.L T := by rw [hida]; rfl
    rw [hrt, hfr, haL] at hA

    have hA' : 4 * ((aT T * P.L T)⁻¹ * trG T) - ((aT T * P.L T)⁻¹) ^ 2 * trG2 T
        - 2 * (Z.N T (2 * T) : ℝ) - 3 * (NII Z T : ℝ)
        - θ₀ T / (aT T * P.L T)
            * (4 + 2 * Real.sqrt (((aT T * P.L T)⁻¹) ^ 2 * trG2 T) + θ₀ T / (aT T * P.L T))
        ≤ (Z.N0s T (2 * T) : ℝ) - D T := by linarith [hA]

    have htr : |(aT T * P.L T)⁻¹ * trG T - N T| ≤ R₁ T :=
      trGhat_sub_N_le hapos' hLpos (by simpa only using htr1 T hT₁)

    have hfrb : ((aT T * P.L T)⁻¹) ^ 2 * trG2 T ≤ cinv T * N T + R₂ T := by
      have h := hfr2 T hT₂
      simp only at h
      have h1 : trG2 T / (aT T * P.L T) ^ 2 - cinv T * N T ≤ C₂ * P.calE T * (cinv T * N T) := by
        rw [← mul_assoc] at h
        exact le_trans (le_trans (le_max_left _ 0) (le_abs_self _)) h
      have e : ((aT T * P.L T)⁻¹) ^ 2 * trG2 T = trG2 T / (aT T * P.L T) ^ 2 := by
        rw [inv_pow, div_eq_inv_mul]
      rw [e]; simp only [hR₂]; linarith
    have hB₀ : 0 ≤ B T := div_nonneg hTl.theta_nonneg (mul_pos hapos' hLpos).le
    have h := N0star_lower_c hB₀ hA' htr hfrb
    have hN0 : 0 ≤ N T := Nat.cast_nonneg _
    have hcd : (2 - c⁻¹) * N T - |cinv T - c⁻¹| * N T ≤ (2 - cinv T) * N T := by
      have h1 := mul_le_mul_of_nonneg_right (le_abs_self (cinv T - c⁻¹)) hN0
      linarith [h1]
    simp only [herr, hR₁, hR₂, hBdef, hNdef] at h hcd ⊢
    linarith

  have hNtop : Tendsto N atTop atTop := tendsto_N_atTop Z H.RvM

  have o1 : R₁ =o[atTop] N := by
    have hbd : (fun T => C₁ / aT T) =O[atTop] (fun _ => (1:ℝ)) := by
      refine isBigO_one_of_abs_le (C := 2 * C₁) ?_
      filter_upwards [ha] with T ha2
      rw [abs_of_nonneg (div_nonneg hC₁.le (by linarith [ha2.1]))]
      rw [div_le_iff₀ (by linarith [ha2.1])]; nlinarith [ha2.1]
    have := isLittleO_of_bdd_mul hbd
      (isLittleO_N_of_isLittleO_Tl Z H.RvM (isLittleO_sqrtX_Tl P hlam0 hlam1))
    exact this.congr_left fun T => by simp only [hR₁]; ring

  have hcinv_bd : ∀ᶠ T in atTop, 0 ≤ cinv T ∧ cinv T ≤ 2 * c⁻¹ := by
    have hcpos : (0:ℝ) < c⁻¹ := inv_pos.mpr hc0
    filter_upwards [hcinv_to.eventually (eventually_ge_nhds hcpos),
      hcinv_to.eventually (eventually_le_nhds (show c⁻¹ < 2 * c⁻¹ by linarith))] with T h1 h2
    exact ⟨h1, h2⟩
  have hcinvO : cinv =O[atTop] (fun _ => (1:ℝ)) := by
    refine isBigO_one_of_abs_le (C := 2 * c⁻¹) ?_
    filter_upwards [hcinv_bd] with T h
    rw [abs_of_nonneg h.1]; exact h.2

  have o2 : R₂ =o[atTop] N := by
    have hcE0 : Tendsto (fun T => C₂ * P.calE T) atTop (𝓝 0) := by
      simpa using hcalE.const_mul C₂
    have i1 : (fun T => cinv T * N T) =O[atTop] N := by
      have := hcinvO.mul (isBigO_refl N atTop)
      simpa using this
    have := ((isLittleO_one_iff ℝ).2 hcE0).mul_isBigO i1
    refine (this.congr_left fun T => ?_).congr_right fun T => by simp
    simp only [hR₂]

  have o3 : (fun T => (NII Z T : ℝ)) =o[atTop] N := by
    have hO : (fun T => (NII Z T : ℝ)) =O[atTop] (fun T => Real.sqrt T * l T) := by
      refine IsBigO.of_bound CII ?_
      filter_upwards [hII, eventually_l_pos] with T h hl
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _),
        abs_of_nonneg (by positivity)]
      simpa [mul_assoc] using h
    exact hO.trans_isLittleO (isLittleO_N_of_isLittleO_Tl Z H.RvM isLittleO_sqrt_mul_l_Tl)

  have o4 : Tendsto B atTop (𝓝 0) := by
    have hup : Tendsto (fun T => 2 * |Cθ| * (l T * T ^ (P.lam / 2 - 1) / P.L T)) atTop (𝓝 0) := by
      simpa using (tendsto_theta_over_L P hlam0 hlam1).const_mul (2 * |Cθ|)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
    · filter_upwards [hTail, ha, eventually_l_pos] with T hTl ha2 hl
      have hLpos : 0 < P.L T := by simp only [Params.L]; positivity
      exact div_nonneg hTl.theta_nonneg (by nlinarith [ha2.1])
    · filter_upwards [hTail, ha, eventually_l_pos, hθ, eventually_gt_atTop (0:ℝ)]
        with T hTl ha2 hl hθT hT0
      have hLpos : 0 < P.L T := by simp only [Params.L]; positivity
      have hapos' : 0 < aT T := by linarith [ha2.1]
      have hq : 0 ≤ l T * T ^ (P.lam / 2 - 1) / P.L T := by positivity
      simp only [hBdef]
      rw [div_le_iff₀ (mul_pos hapos' hLpos)]
      calc θ₀ T ≤ Cθ * l T * T ^ (P.lam / 2 - 1) := hθT
        _ ≤ |Cθ| * l T * T ^ (P.lam / 2 - 1) := by gcongr; exact le_abs_self _
        _ = |Cθ| * (l T * T ^ (P.lam / 2 - 1) / P.L T) * P.L T := by field_simp
        _ ≤ (2 * |Cθ| * (l T * T ^ (P.lam / 2 - 1) / P.L T)) * (aT T * P.L T) := by
          have : |Cθ| * (l T * T ^ (P.lam / 2 - 1) / P.L T) * P.L T
              = (2 * |Cθ| * (l T * T ^ (P.lam / 2 - 1) / P.L T)) * (1 / 2 * P.L T) := by ring
          rw [this]; gcongr; exact ha2.1

  have o5 := err_isLittleO (R₁ := R₁) (R₂ := R₂) (NII := fun T => (NII Z T : ℝ)) (B := B)
    (cl := cinv) hNtop o1 o2 o3 o4 hcinv_bd
  have o6 : (fun T => |cinv T - c⁻¹| * N T) =o[atTop] N := by
    refine isLittleO_of_tendsto_zero_mul ?_
    have : Tendsto (fun T => cinv T - c⁻¹) atTop (𝓝 0) := by
      simpa using hcinv_to.sub_const c⁻¹
    simpa using this.abs
  have herr_o : err =o[atTop] N := o5.add o6

  have hfin := eps_form_of_isLittleO (lower := fun T => (Z.N0s T (2 * T) : ℝ) - D T) hmain
    (Eventually.of_forall fun T => Nat.cast_nonneg _) herr_o
  intro ε hε
  obtain ⟨T₀, hT₀⟩ := hfin ε hε
  filter_upwards [eventually_ge_atTop T₀] with T hT
  have := hT₀ T hT
  simp only [hNdef] at this
  linarith


end Zeta23Ext.Bridge

end

/-! ###### source module: Zeta23Ext/Bridge/Helpers_S9.lean ###### -/



noncomputable section
set_option linter.unusedSectionVars false

open Matrix Finset Filter MeasureTheory Real Set
open scoped BigOperators
open Zeta23 Zeta23.ZeroSide Zeta23.ThmD

namespace Zeta23Ext.Bridge

open Classical

section GramEntry

variable (Z : ZeroConfig) (P : Params) (T : ℝ)

lemma bdata_v_eq (hreal : PhiHatReal T P) {y : ZI Z T} (hy : (y : ℂ).re = 1 / 2) (k : Fin (P.d T)) :
    (bdata Z P T).v y k = (P.phiHatR T ((y : ℂ).im - P.tau T k) : ℂ) := by
  simp only [bdata, blockData, mkData_v, evalVec]
  rw [gammaOf_of_re_eq_half hy, ← Complex.ofReal_sub, hreal]

lemma gram_apply (hreal : PhiHatReal T P) (hc : 0 ≤ aL2 P T) (z z' : retained Z P T) :
    gram Z P T z z' =
      (((aL2 P T)⁻¹ * ∑ k : Fin (P.d T),
        P.phiHatR T ((z.1 : ℂ).im - P.tau T k) * P.phiHatR T ((z'.1 : ℂ).im - P.tau T k) : ℝ) : ℂ) := by
  have hz := re_eq_half_of_mem_S₁ Z P T (mem_S₁_of_mem_retained Z P T z.2)
  have hz' := re_eq_half_of_mem_S₁ Z P T (mem_S₁_of_mem_retained Z P T z'.2)
  have hsq : (Real.sqrt (aL2 P T) : ℂ) * (Real.sqrt (aL2 P T) : ℂ) = (aL2 P T : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt hc]
  have hentry : ∀ a b : (bdata Z P T).S₁, gramS₁ (bdata Z P T) (aL2 P T) a b
      = ∑ k, star (Vsimple (bdata Z P T) (aL2 P T) k a) * Vsimple (bdata Z P T) (aL2 P T) k b := by
    intro a b
    simp only [gramS₁, Matrix.mul_apply, Matrix.conjTranspose_apply]
  unfold gram
  rw [Matrix.submatrix_apply, hentry]
  have e : ∀ k : Fin (P.d T),
      star (Vsimple (bdata Z P T) (aL2 P T) k (toS₁ Z P T z))
        * Vsimple (bdata Z P T) (aL2 P T) k (toS₁ Z P T z')
      = (((aL2 P T)⁻¹ * (P.phiHatR T ((z.1 : ℂ).im - P.tau T k)
          * P.phiHatR T ((z'.1 : ℂ).im - P.tau T k)) : ℝ) : ℂ) := by
    intro k
    have h1 : (bdata Z P T).v (toS₁ Z P T z) k = (P.phiHatR T ((z.1 : ℂ).im - P.tau T k) : ℂ) :=
      bdata_v_eq Z P T hreal hz k
    have h2 : (bdata Z P T).v (toS₁ Z P T z') k = (P.phiHatR T ((z'.1 : ℂ).im - P.tau T k) : ℂ) :=
      bdata_v_eq Z P T hreal hz' k
    simp only [Vsimple]
    rw [h1, h2]
    simp only [star_div₀, Complex.star_def, Complex.conj_ofReal]
    rw [div_mul_div_comm, hsq]
    push_cast
    ring
  simp_rw [e]
  rw [← Complex.ofReal_sum, Finset.mul_sum]

end GramEntry

section Window

variable {P : Params} (hP : P.Valid) (T : ℝ)
include hP

lemma atD_phiHatR_eq : (P.atD T).phiHatR T = AdmWindow.vHatR (P.phiD T) := atD_phiHatR hP T

lemma phiHatReal_atD : PhiHatReal T (P.atD T) := fun r => GzGp.phiHat_ofReal _ T r

lemma abs_phiHatR_atD_mul_sq_le (h8 : 8 * P.w ≤ P.L T) (r : ℝ) :
    |(P.atD T).phiHatR T r| * r ^ 2 ≤ cDT P.ϱ P.lam / P.w := by
  rw [atD_phiHatR_eq hP T]
  exact (admWindow_params hP h8).abs_vHatR_mul_sq_le r

lemma hasSum_phiHatR_atD_mul (h8 : 8 * P.w ≤ P.L T) (τ τ' : ℝ) :
    HasSum (fun k : ℤ => (P.atD T).phiHatR T (τ - (P.atD T).tau T k)
        * (P.atD T).phiHatR T (τ' - (P.atD T).tau T k))
      (P.L T * AdmWindow.VPhiR (P.phiD T) (τ - τ')) := by
  have h := (admWindow_params hP h8).hasSum_vHatR_mul T τ τ'
  simp only [atD_phiHatR_eq hP T, atD_tau_eq]
  exact h

end Window

section Tail

lemma Wfun_le_of_L_le {c : ℝ} {p : PrimeSide.Setting} {F : PrimeSide.LocalFun}
    (hF : PrimeSide.LocalHypsCoreW c p F) {Δ : ℝ} (hΔ : p.L ≤ Δ) :
    PrimeSide.Wfun c p Δ ≤ 2 * (c / p.w) ^ 2 / p.L ^ 2 := by
  have h8 := hF.eight_le_L
  have hL : 0 < p.L := hF.L_pos
  have hΔ0 : 0 < Δ := lt_of_lt_of_le hL hΔ
  have hw : 0 < p.w := by linarith [hF.one_le_w]
  have hc : 0 ≤ c := by linarith [hF.four_le_cϱ]
  set K : ℝ := (c / p.w) ^ 2 with hK
  have hK0 : 0 ≤ K := sq_nonneg _
  have hπ := Real.pi_pos

  have hψ : PrimeSide.psiA c p Δ ^ 2 ≤ K / Δ ^ 4 := by
    have h1 : PrimeSide.psiA c p Δ ≤ c / (p.w * Δ ^ 2) := PrimeSide.psiA_le_div_sq hΔ0.ne'
    calc PrimeSide.psiA c p Δ ^ 2 ≤ (c / (p.w * Δ ^ 2)) ^ 2 :=
          pow_le_pow_left₀ (PrimeSide.psiA_nonneg_of hF Δ) h1 2
      _ = K / Δ ^ 4 := by rw [hK]; field_simp

  have hint : ∫ r in Set.Ioi Δ, PrimeSide.psiA c p r ^ 2 ≤ K / (3 * Δ ^ 3) :=
    PrimeSide.setIntegral_psiA_sq_Ioi_le_div hF hΔ0
  have hh : (p.h)⁻¹ = p.L / (2 * Real.pi) := by
    unfold PrimeSide.Setting.h; rw [inv_div]
  have hhpos : 0 ≤ (p.h)⁻¹ := by rw [hh]; positivity

  have hΔ4 : p.L ^ 2 ≤ Δ ^ 4 := by
    have : p.L ^ 2 ≤ Δ ^ 2 := pow_le_pow_left₀ hL.le hΔ 2
    have h2 : (1 : ℝ) ≤ Δ ^ 2 := by nlinarith
    calc p.L ^ 2 ≤ Δ ^ 2 := this
      _ = Δ ^ 2 * 1 := (mul_one _).symm
      _ ≤ Δ ^ 2 * Δ ^ 2 := by gcongr
      _ = Δ ^ 4 := by ring
  have hA : K / Δ ^ 4 ≤ K / p.L ^ 2 :=
    div_le_div_of_nonneg_left hK0 (by positivity) hΔ4
  have hB : (p.h)⁻¹ * (K / (3 * Δ ^ 3)) ≤ K / p.L ^ 2 := by
    rw [hh]
    have e : p.L / (2 * Real.pi) * (K / (3 * Δ ^ 3)) = K * (p.L / (6 * Real.pi * Δ ^ 3)) := by
      field_simp; ring
    rw [e]
    have hΔ3 : p.L ^ 3 ≤ Δ ^ 3 := pow_le_pow_left₀ hL.le hΔ 3
    have h3 : p.L / (6 * Real.pi * Δ ^ 3) ≤ 1 / p.L ^ 2 := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have : p.L * p.L ^ 2 = p.L ^ 3 := by ring
      rw [this]
      nlinarith [Real.pi_gt_three, pow_pos hΔ0 3]
    calc K * (p.L / (6 * Real.pi * Δ ^ 3)) ≤ K * (1 / p.L ^ 2) :=
          mul_le_mul_of_nonneg_left h3 hK0
      _ = K / p.L ^ 2 := by ring
  unfold PrimeSide.Wfun
  calc PrimeSide.psiA c p Δ ^ 2 + (p.h)⁻¹ * ∫ r in Set.Ioi Δ, PrimeSide.psiA c p r ^ 2
      ≤ K / Δ ^ 4 + (p.h)⁻¹ * (K / (3 * Δ ^ 3)) := by
        gcongr
    _ ≤ K / p.L ^ 2 + K / p.L ^ 2 := add_le_add hA hB
    _ = 2 * K / p.L ^ 2 := by ring

lemma rho_le_of_far {c : ℝ} {p : PrimeSide.Setting} {F : PrimeSide.LocalFun}
    (hF : PrimeSide.LocalHypsCoreW c p F) (hT : 0 < p.T) {τ : ℝ}
    (h1 : p.L ≤ τ - p.T) (h2 : p.L ≤ 2 * p.T - τ) (h3 : p.L ≤ p.tau p.d - τ) :
    PrimeSide.rho p F τ ≤ 5 * (c / p.w) ^ 2 / p.L ^ 2 := by
  have hL : 0 < p.L := hF.L_pos
  have hτ : τ ∈ Set.Icc p.T (2 * p.T) := ⟨by linarith, by linarith⟩
  have hmaj := PrimeSide.rho_le_majorant hF hT hτ
  have hW1 := Wfun_le_of_L_le hF h1
  have hW2 := Wfun_le_of_L_le hF h2
  have hψ : PrimeSide.psiA c p (p.tau p.d - τ) ^ 2 ≤ (c / p.w) ^ 2 / p.L ^ 2 := by
    have hΔ0 : 0 < p.tau p.d - τ := lt_of_lt_of_le hL h3
    have hw : 0 < p.w := by linarith [hF.one_le_w]
    have hc : 0 ≤ c := by linarith [hF.four_le_cϱ]
    have hb : PrimeSide.psiA c p (p.tau p.d - τ) ≤ c / (p.w * (p.tau p.d - τ) ^ 2) :=
      PrimeSide.psiA_le_div_sq hΔ0.ne'
    have hΔ4 : p.L ^ 2 ≤ (p.tau p.d - τ) ^ 4 := by
      have h8 := hF.eight_le_L
      have : p.L ^ 2 ≤ (p.tau p.d - τ) ^ 2 := pow_le_pow_left₀ hL.le h3 2
      have h2' : (1 : ℝ) ≤ (p.tau p.d - τ) ^ 2 := by nlinarith
      calc p.L ^ 2 ≤ (p.tau p.d - τ) ^ 2 := this
        _ = (p.tau p.d - τ) ^ 2 * 1 := (mul_one _).symm
        _ ≤ (p.tau p.d - τ) ^ 2 * (p.tau p.d - τ) ^ 2 := by gcongr
        _ = (p.tau p.d - τ) ^ 4 := by ring
    calc PrimeSide.psiA c p (p.tau p.d - τ) ^ 2 ≤ (c / (p.w * (p.tau p.d - τ) ^ 2)) ^ 2 :=
          pow_le_pow_left₀ (PrimeSide.psiA_nonneg_of hF _) hb 2
      _ = (c / p.w) ^ 2 / (p.tau p.d - τ) ^ 4 := by field_simp
      _ ≤ (c / p.w) ^ 2 / p.L ^ 2 :=
          div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) hΔ4
  calc PrimeSide.rho p F τ
      ≤ PrimeSide.Wfun c p (τ - p.T) + PrimeSide.Wfun c p (2 * p.T - τ)
          + PrimeSide.psiA c p (p.tau p.d - τ) ^ 2 := hmaj
    _ ≤ 2 * (c / p.w) ^ 2 / p.L ^ 2 + 2 * (c / p.w) ^ 2 / p.L ^ 2 + (c / p.w) ^ 2 / p.L ^ 2 :=
        add_le_add (add_le_add hW1 hW2) hψ
    _ = 5 * (c / p.w) ^ 2 / p.L ^ 2 := by ring

lemma abs_Kinf_sub_Kfun_le_of_far {c : ℝ} {p : PrimeSide.Setting} {F : PrimeSide.LocalFun}
    (hF : PrimeSide.LocalHypsCoreW c p F) (hT : 0 < p.T) {τ τ' : ℝ}
    (h1 : p.L ≤ τ - p.T) (h2 : p.L ≤ 2 * p.T - τ) (h3 : p.L ≤ p.tau p.d - τ)
    (h1' : p.L ≤ τ' - p.T) (h2' : p.L ≤ 2 * p.T - τ') (h3' : p.L ≤ p.tau p.d - τ') :
    |PrimeSide.Kinf p F τ τ' - PrimeSide.Kfun p F τ τ'| ≤ 5 * (c / p.w) ^ 2 / p.L ^ 2 := by
  have h := PrimeSide.abs_Kinf_sub_Kfun_le hF τ τ' one_pos
  have hρ := rho_le_of_far hF hT h1 h2 h3
  have hρ' := rho_le_of_far hF hT h1' h2' h3'
  calc |PrimeSide.Kinf p F τ τ' - PrimeSide.Kfun p F τ τ'|
      ≤ (1 * PrimeSide.rho p F τ + PrimeSide.rho p F τ' / 1) / 2 := h
    _ ≤ (1 * (5 * (c / p.w) ^ 2 / p.L ^ 2) + 5 * (c / p.w) ^ 2 / p.L ^ 2 / 1) / 2 := by
        gcongr
    _ = 5 * (c / p.w) ^ 2 / p.L ^ 2 := by ring

end Tail

section Limit

lemma Kfun_zero_eq_aStar : Kfun 0 = aStar 1 := by
  simp [Kfun, aStar, vStar]

lemma cos_sqrt_two_mul_pos {t : ℝ} (ht : t ∈ Set.Ioo (-(1 : ℝ) / 2) (1 / 2)) :
    0 < Real.cos (Real.sqrt 2 * t) := by
  apply Real.cos_pos_of_mem_Ioo
  have hs : Real.sqrt 2 < 3 / 2 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have h0 := Real.sqrt_nonneg 2
  have hπ := Real.pi_gt_three
  constructor <;> nlinarith [mul_nonneg h0 (by linarith [ht.1] : (0:ℝ) ≤ t + 1 / 2),
    mul_nonneg h0 (by linarith [ht.2] : (0:ℝ) ≤ 1 / 2 - t)]

lemma Kfun_zero_pos : 0 < Kfun 0 := by
  unfold Kfun
  apply intervalIntegral.intervalIntegral_pos_of_pos_on
  · exact (by fun_prop : Continuous fun t : ℝ =>
      Real.cos (Real.sqrt 2 * t) * Real.cos (2 * Real.pi * 0 * t)).intervalIntegrable _ _
  · intro t ht
    simp only [mul_zero, zero_mul, Real.cos_zero, mul_one]
    exact cos_sqrt_two_mul_pos ht
  · norm_num

lemma abs_Kfun_le (x : ℝ) : |Kfun x| ≤ Kfun 0 := by
  unfold Kfun
  have hab : (-(1 : ℝ) / 2) ≤ 1 / 2 := by norm_num
  calc |∫ t in (-(1 : ℝ) / 2)..(1 / 2), Real.cos (Real.sqrt 2 * t) * Real.cos (2 * Real.pi * x * t)|
      ≤ ∫ t in (-(1 : ℝ) / 2)..(1 / 2), |Real.cos (Real.sqrt 2 * t) * Real.cos (2 * Real.pi * x * t)| :=
        intervalIntegral.abs_integral_le_integral_abs hab
    _ ≤ ∫ t in (-(1 : ℝ) / 2)..(1 / 2), Real.cos (Real.sqrt 2 * t) * Real.cos (2 * Real.pi * 0 * t) := by
        apply intervalIntegral.integral_mono_on hab
        · exact ((by fun_prop : Continuous fun t : ℝ =>
            Real.cos (Real.sqrt 2 * t) * Real.cos (2 * Real.pi * x * t)).abs).intervalIntegrable _ _
        · exact (by fun_prop : Continuous fun t : ℝ =>
            Real.cos (Real.sqrt 2 * t) * Real.cos (2 * Real.pi * 0 * t)).intervalIntegrable _ _
        · intro t ht
          simp only [mul_zero, zero_mul, Real.cos_zero, mul_one]
          rw [abs_mul, abs_of_nonneg (cos_sqrt_two_mul_nonneg ht)]
          exact mul_le_of_le_one_right (cos_sqrt_two_mul_nonneg ht) (Real.abs_cos_le_one _)

lemma re_paperFT_ofReal {g : ℝ → ℝ} (hg : Integrable g) (r : ℝ) :
    (paperFT (fun u => (g u : ℂ)) r).re = ∫ u, g u * Real.cos (r * u) := by
  unfold paperFT
  have hexp : Continuous fun u : ℝ => Complex.exp (Complex.I * (r : ℂ) * (u : ℂ)) := by fun_prop
  have hint : Integrable (fun u : ℝ => (g u : ℂ) * Complex.exp (Complex.I * (r : ℂ) * (u : ℂ))) := by
    refine hg.ofReal.mul_bdd (c := 1) hexp.aestronglyMeasurable (Filter.Eventually.of_forall fun u => ?_)
    rw [Complex.norm_exp]
    simp
  rw [← integral_re_C hint]
  congr 1 with u
  have e : Complex.I * (r : ℂ) * (u : ℂ) = ((r * u : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [e, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]

lemma sharpW_integrable {L : ℝ} : Integrable (sharpW 1 L) := by
  unfold sharpW
  rw [integrable_indicator_iff measurableSet_Icc]
  have hc : Continuous fun u : ℝ => vStar 1 (u / L) := by unfold vStar; fun_prop
  exact hc.integrableOn_Icc

lemma integral_sharpW_mul_cos {L : ℝ} (hL : 0 < L) (x : ℝ) :
    ∫ u, sharpW 1 L u * Real.cos (2 * Real.pi * x / L * u) = L * Kfun x := by
  set f : ℝ → ℝ := fun t => Real.cos (Real.sqrt 2 * t) * Real.cos (2 * Real.pi * x * t) with hf
  have hind : ∀ u, sharpW 1 L u * Real.cos (2 * Real.pi * x / L * u)
      = (Set.Icc (-(L / 2)) (L / 2)).indicator (fun u => f (u / L)) u := by
    intro u
    unfold sharpW vStar
    by_cases hu : u ∈ Set.Icc (-(L / 2)) (L / 2)
    · rw [Set.indicator_of_mem hu, Set.indicator_of_mem hu, hf]
      simp only [mul_one]
      congr 2
      field_simp
    · rw [Set.indicator_of_notMem hu, Set.indicator_of_notMem hu, zero_mul]
  simp_rw [hind]
  rw [integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith), intervalIntegral.integral_comp_div (f := f) hL.ne',
    smul_eq_mul, show -(L / 2) / L = -(1 : ℝ) / 2 by field_simp; try ring,
    show L / 2 / L = (1 : ℝ) / 2 by field_simp; try ring]
  rfl

lemma abs_integral_mul_cos_sub_le {f g : ℝ → ℝ} (hf : Integrable f) (hg : Integrable g) (r : ℝ) :
    |(∫ u, f u * Real.cos (r * u)) - ∫ u, g u * Real.cos (r * u)| ≤ ∫ u, |f u - g u| := by
  have hcos : Continuous fun u : ℝ => Real.cos (r * u) := by fun_prop
  have hbd : ∀ u : ℝ, ‖Real.cos (r * u)‖ ≤ 1 := fun u => by
    rw [Real.norm_eq_abs]; exact Real.abs_cos_le_one _
  have hfi : Integrable fun u => f u * Real.cos (r * u) :=
    hf.mul_bdd (c := 1) hcos.aestronglyMeasurable (Filter.Eventually.of_forall hbd)
  have hgi : Integrable fun u => g u * Real.cos (r * u) :=
    hg.mul_bdd (c := 1) hcos.aestronglyMeasurable (Filter.Eventually.of_forall hbd)
  rw [← integral_sub hfi hgi]
  calc |∫ u, (f u * Real.cos (r * u) - g u * Real.cos (r * u))|
      ≤ ∫ u, |f u * Real.cos (r * u) - g u * Real.cos (r * u)| := abs_integral_le_integral_abs
    _ ≤ ∫ u, |f u - g u| := by
        refine integral_mono (hfi.sub hgi).abs (hf.sub hg).abs fun u => ?_
        rw [← sub_mul, abs_mul]
        exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _)

variable {P : Params} (hP : P.Valid) (hlam : P.lam = 1) {T : ℝ} (h8 : 8 * P.w ≤ P.L T)
include hP hlam h8

lemma abs_VPhiR_sub_L_mul_Kfun_le (x : ℝ) :
    |AdmWindow.VPhiR (P.phiD T) (2 * Real.pi * x / P.L T) - P.L T * Kfun x| ≤ 2 * P.w := by
  have hW := admWindow_params hP h8
  have hL := hW.L_pos
  have hw : 0 < P.w := hW.w_pos
  set r := 2 * Real.pi * x / P.L T with hr
  have hV : AdmWindow.VPhiR (P.phiD T) r = ∫ u, P.phiD T u ^ 2 * Real.cos (r * u) :=
    re_paperFT_ofReal (hW.integrable_pow two_pos) r
  have hS : ∫ u, sharpW 1 (P.L T) u * Real.cos (r * u) = P.L T * Kfun x :=
    integral_sharpW_mul_cos hL x
  have hL1 : ∫ u, |P.phiD T u ^ 2 - sharpW P.lam (P.L T) u| ≤ 2 * P.w :=
    integral_abs_phiDsq_sub_sharp hP.taper hP.lam_pos hP.lam_le_one hw (by linarith)
  rw [hlam] at hL1
  rw [hV, ← hS]
  exact (abs_integral_mul_cos_sub_le (hW.integrable_pow two_pos) sharpW_integrable r).trans hL1

lemma abs_aL_sub_L_mul_Kfun_zero_le :
    |(P.atD T).a T * P.L T - P.L T * Kfun 0| ≤ 4 * P.w := by
  have hW := admWindow_params hP h8
  have hL := hW.L_pos
  have h : |(P.L T)⁻¹ * (∫ u, P.phiD T u ^ 2) - aStar P.lam| ≤ 4 * P.w / P.L T :=
    aD_close hP.taper hP.lam_pos hP.lam_le_one hP.one_le_w h8
  rw [hlam, ← Kfun_zero_eq_aStar] at h
  have ha : (P.atD T).a T = (P.L T)⁻¹ * ∫ u, P.phiD T u ^ 2 := by rw [atD_a_eq_av hP]; rfl
  rw [ha]
  have e : (P.L T)⁻¹ * (∫ u, P.phiD T u ^ 2) * P.L T - P.L T * Kfun 0
      = ((P.L T)⁻¹ * (∫ u, P.phiD T u ^ 2) - Kfun 0) * P.L T := by ring
  rw [e, abs_mul, abs_of_pos hL]
  calc |(P.L T)⁻¹ * (∫ u, P.phiD T u ^ 2) - Kfun 0| * P.L T ≤ 4 * P.w / P.L T * P.L T :=
        mul_le_mul_of_nonneg_right h hL.le
    _ = 4 * P.w := by field_simp

lemma abs_VPhiR_div_sub_kfun_le (h4π : 4 * Real.pi * P.w ≤ P.L T) (x : ℝ) :
    |AdmWindow.VPhiR (P.phiD T) (2 * Real.pi * x / P.L T) / ((P.atD T).a T * P.L T) - kfun x|
      ≤ 12 * P.w / P.L T := by
  have hW := admWindow_params hP h8
  have hL := hW.L_pos
  have hw : 0 < P.w := hW.w_pos
  have ha : 1 / 2 ≤ (P.atD T).a T := (aD_range_of hP h8 h4π).1
  have h1 := abs_VPhiR_sub_L_mul_Kfun_le hP hlam h8 x
  have h2 := abs_aL_sub_L_mul_Kfun_zero_le hP hlam h8
  have hK0 : 0 < Kfun 0 := Kfun_zero_pos
  have hK : |Kfun x| ≤ Kfun 0 := abs_Kfun_le x
  set V := AdmWindow.VPhiR (P.phiD T) (2 * Real.pi * x / P.L T) with hV
  set A := (P.atD T).a T * P.L T with hA
  set K := Kfun x with hK'
  set K0 := Kfun 0 with hK0'
  have hA2 : P.L T / 2 ≤ A := by rw [hA]; nlinarith
  have hApos : 0 < A := by linarith
  have e : V / A - K / K0 = (V - P.L T * K) / A + K * (P.L T * K0 - A) / (A * K0) := by
    field_simp
    ring
  unfold kfun
  rw [e]
  have h2' : |P.L T * K0 - A| ≤ 4 * P.w := by rw [abs_sub_comm]; exact h2
  calc |(V - P.L T * K) / A + K * (P.L T * K0 - A) / (A * K0)|
      ≤ |(V - P.L T * K) / A| + |K * (P.L T * K0 - A) / (A * K0)| := abs_add_le _ _
    _ = |V - P.L T * K| / A + |K| * |P.L T * K0 - A| / (A * K0) := by
        rw [abs_div, abs_of_pos hApos, abs_div, abs_mul, abs_of_pos (mul_pos hApos hK0)]
    _ ≤ 2 * P.w / A + K0 * (4 * P.w) / (A * K0) := by gcongr
    _ = 6 * P.w / A := by field_simp; ring
    _ ≤ 12 * P.w / P.L T := by
        rw [div_le_div_iff₀ hApos hL]
        nlinarith

end Limit

section Assembly

lemma retained_far {Z : ZeroConfig} {P : Params} {T : ℝ} (hL : 0 < P.L T) (hT : 0 ≤ T)
    {z : ZI Z T} (hz : z ∈ retained Z P T) :
    P.L T ≤ (z : ℂ).im - T ∧ P.L T ≤ 2 * T - (z : ℂ).im ∧ P.L T ≤ P.tau T (P.d T) - (z : ℂ).im := by
  obtain ⟨-, h1, h2⟩ := Finset.mem_filter.mp hz
  unfold xnorm at h1 h2
  have hπ : (0 : ℝ) < 2 * Real.pi := by positivity
  have hπ1 : (1 : ℝ) ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
  have hd : ((P.d T : ℕ) : ℝ) ≤ P.L T * T / (2 * Real.pi) := Nat.floor_le (by positivity)
  have h1' : 2 * Real.pi * P.L T ^ 2 ≤ P.L T * ((z : ℂ).im - T) := by
    have := (le_div_iff₀ hπ).mp h1; linarith
  have h2' : P.L T * ((z : ℂ).im - T) ≤ 2 * Real.pi * ((P.d T : ℝ) - P.L T ^ 2) := by
    have := (div_le_iff₀ hπ).mp h2; linarith
  have hd' : 2 * Real.pi * (P.d T : ℝ) ≤ P.L T * T := by
    have := (le_div_iff₀ hπ).mp hd; linarith
  have g1 : 2 * Real.pi * P.L T ≤ (z : ℂ).im - T := by
    have : P.L T * (2 * Real.pi * P.L T) ≤ P.L T * ((z : ℂ).im - T) := by nlinarith
    exact le_of_mul_le_mul_left this hL
  have g2 : 2 * Real.pi * P.L T ≤ 2 * T - (z : ℂ).im := by
    have : P.L T * ((z : ℂ).im - T) ≤ P.L T * (T - 2 * Real.pi * P.L T) := by nlinarith
    have := le_of_mul_le_mul_left this hL
    linarith
  have hL2 : P.L T ≤ 2 * Real.pi * P.L T := by nlinarith
  refine ⟨by linarith, by linarith, ?_⟩

  have htau : P.tau T (P.d T) = T + (P.d T : ℝ) * (2 * Real.pi / P.L T) := by
    simp only [Params.tau, Params.hgrid, Int.cast_natCast]
  rw [htau]
  have e : T + (P.d T : ℝ) * (2 * Real.pi / P.L T) - (z : ℂ).im
      = (2 * Real.pi * (P.d T : ℝ) - P.L T * ((z : ℂ).im - T)) / P.L T := by
    field_simp
    ring
  rw [e, le_div_iff₀ hL]
  nlinarith

lemma Kfun_eq_sum {P : Params} (hP : P.Valid) (T γ γ' : ℝ) :
    PrimeSide.Kfun (P.toSetting T) (P.localFunD T) γ γ'
      = ∑ k : Fin ((P.atD T).d T), (P.atD T).phiHatR T (γ - (P.atD T).tau T k)
          * (P.atD T).phiHatR T (γ' - (P.atD T).tau T k) := by
  rw [atD_phiHatR_eq hP T]; rfl

lemma Kinf_eq {P : Params} (T γ γ' : ℝ) :
    PrimeSide.Kinf (P.toSetting T) (P.localFunD T) γ γ'
      = P.L T * AdmWindow.VPhiR (P.phiD T) (γ - γ') := rfl

theorem gram_close_of {P : Params} (hP : P.Valid) (hlam : P.lam = 1) {T : ℝ} (hT : 0 < T)
    (h8 : 8 * P.w ≤ P.L T) (h4π : 4 * Real.pi * P.w ≤ P.L T)
    (hF : PrimeSide.LocalHypsCoreW (cDT P.ϱ P.lam) (P.toSetting T) (P.localFunD T))
    (Z : ZeroConfig) (z z' : retained Z (P.atD T) T) :
    ‖gram Z (P.atD T) T z z'
        - (kfun (xret Z (P.atD T) T z - xret Z (P.atD T) T z') : ℂ)‖
      ≤ 10 * (cDT P.ϱ P.lam / P.w) ^ 2 / P.L T ^ 4 + 12 * P.w / P.L T := by
  have hW := admWindow_params hP h8
  have hL := hW.L_pos
  have ha : 1 / 2 ≤ (P.atD T).a T := (aD_range_of hP h8 h4π).1
  have hc : 0 < aL2 (P.atD T) T := by
    unfold aL2; rw [Params.atD_L]; positivity
  set K : ℝ := (cDT P.ϱ P.lam / P.w) ^ 2 with hK
  have hK0 : 0 ≤ K := sq_nonneg _
  rw [gram_apply Z (P.atD T) T (phiHatReal_atD hP T) hc.le z z', ← Complex.ofReal_sub,
    Complex.norm_real, Real.norm_eq_abs, ← Kfun_eq_sum hP T (z.1 : ℂ).im (z'.1 : ℂ).im]
  set γ : ℝ := (z.1 : ℂ).im with hγ
  set γ' : ℝ := (z'.1 : ℂ).im with hγ'

  obtain ⟨g1, g2, g3⟩ := retained_far (Z := Z) (P := P.atD T) hL hT.le z.2
  obtain ⟨g1', g2', g3'⟩ := retained_far (Z := Z) (P := P.atD T) hL hT.le z'.2
  have htail : |PrimeSide.Kinf (P.toSetting T) (P.localFunD T) γ γ'
      - PrimeSide.Kfun (P.toSetting T) (P.localFunD T) γ γ'| ≤ 5 * K / P.L T ^ 2 :=
    abs_Kinf_sub_Kfun_le_of_far hF hT g1 g2 g3 g1' g2' g3'

  have hx : 2 * Real.pi * (xret Z (P.atD T) T z - xret Z (P.atD T) T z') / P.L T = γ - γ' := by
    unfold xret xnorm
    rw [Params.atD_L]
    field_simp
    ring
  have hlim := abs_VPhiR_div_sub_kfun_le hP hlam h8 h4π (xret Z (P.atD T) T z - xret Z (P.atD T) T z')
  rw [hx] at hlim

  set A : ℝ := (P.atD T).a T with hA
  set V : ℝ := AdmWindow.VPhiR (P.phiD T) (γ - γ') with hV
  set Kf : ℝ := PrimeSide.Kfun (P.toSetting T) (P.localFunD T) γ γ' with hKf
  have hKinf : PrimeSide.Kinf (P.toSetting T) (P.localFunD T) γ γ' = P.L T * V := Kinf_eq T γ γ'
  rw [hKinf] at htail
  have haL2 : aL2 (P.atD T) T = A * P.L T ^ 2 := by unfold aL2; rw [Params.atD_L]
  rw [haL2]
  have hApos : 0 < A := by linarith
  have hsplit : (A * P.L T ^ 2)⁻¹ * Kf - kfun (xret Z (P.atD T) T z - xret Z (P.atD T) T z')
      = (A * P.L T ^ 2)⁻¹ * (Kf - P.L T * V)
        + (V / (A * P.L T) - kfun (xret Z (P.atD T) T z - xret Z (P.atD T) T z')) := by
    field_simp
    ring
  rw [hsplit]
  have hinv : (A * P.L T ^ 2)⁻¹ ≤ 2 / P.L T ^ 2 := by
    rw [inv_eq_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [pow_pos hL 2]
  calc |(A * P.L T ^ 2)⁻¹ * (Kf - P.L T * V)
        + (V / (A * P.L T) - kfun (xret Z (P.atD T) T z - xret Z (P.atD T) T z'))|
      ≤ |(A * P.L T ^ 2)⁻¹ * (Kf - P.L T * V)|
        + |V / (A * P.L T) - kfun (xret Z (P.atD T) T z - xret Z (P.atD T) T z')| := abs_add_le _ _
    _ = (A * P.L T ^ 2)⁻¹ * |P.L T * V - Kf|
        + |V / (A * P.L T) - kfun (xret Z (P.atD T) T z - xret Z (P.atD T) T z')| := by
        rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < (A * P.L T ^ 2)⁻¹), abs_sub_comm]
    _ ≤ 2 / P.L T ^ 2 * (5 * K / P.L T ^ 2) + 12 * P.w / P.L T := by
        gcongr
    _ = 10 * K / P.L T ^ 4 + 12 * P.w / P.L T := by
        field_simp
        ring

end Assembly

section Strips

variable (Z : ZeroConfig)

lemma window_union {a b c : ℝ} (h1 : a ≤ b) (h2 : b ≤ c) :
    Z.window a c = Z.window a b ∪ Z.window b c := by
  ext ρ
  simp only [ZeroConfig.window, Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_union]
  constructor
  · rintro ⟨hρ, ha, hc⟩
    rcases le_or_gt ρ.im b with hle | hgt
    · exact Or.inl ⟨hρ, ha, hle⟩
    · exact Or.inr ⟨hρ, hgt, hc⟩
  · rintro (⟨hρ, ha, hb⟩ | ⟨hρ, hb, hc⟩)
    · exact ⟨hρ, ha, le_trans hb h2⟩
    · exact ⟨hρ, lt_of_le_of_lt h1 hb, hc⟩

lemma N_add {a b c : ℝ} (h1 : a ≤ b) (h2 : b ≤ c) : Z.N a c = Z.N a b + Z.N b c := by
  unfold ZeroConfig.N
  rw [window_union Z h1 h2]
  refine finsum_mem_union ?_ (Z.finite_window a b) (Z.finite_window b c)
  rw [Set.disjoint_left]
  rintro ρ ⟨_, _, hb⟩ ⟨_, hb', _⟩
  exact absurd hb (not_le.2 hb')

lemma N_mono {a b c d : ℝ} (hca : c ≤ a) (hbd : b ≤ d) : Z.N a b ≤ Z.N c d := by
  unfold ZeroConfig.N
  have hsub : Z.window a b ⊆ Z.window c d := by
    rintro ρ ⟨hρ, h1, h2⟩
    exact ⟨hρ, lt_of_le_of_lt hca h1, le_trans h2 hbd⟩
  have hfab : (Z.window a b).Finite := Z.finite_window a b
  have hfcd : (Z.window c d).Finite := Z.finite_window c d
  rw [finsum_mem_eq_finite_toFinset_sum _ hfab, finsum_mem_eq_finite_toFinset_sum _ hfcd]
  apply Finset.sum_le_sum_of_subset
  intro ρ hρ
  rw [Set.Finite.mem_toFinset] at hρ ⊢
  exact hsub hρ

lemma ncard_window_le_N (a b : ℝ) : (Z.window a b).ncard ≤ Z.N a b := by
  unfold ZeroConfig.N
  have hfin : (Z.window a b).Finite := Z.finite_window a b
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin, Set.ncard_eq_toFinset_card _ hfin,
    Finset.card_eq_sum_ones]
  apply Finset.sum_le_sum
  intro ρ hρ
  rw [Set.Finite.mem_toFinset] at hρ
  exact Z.one_le_mult ρ hρ.1

lemma N_le_of_local_count {A₀ : ℝ} (hA₀ : 1 ≤ A₀)
    (hloc : ∀ t : ℝ, (Z.N t (t + 1) : ℝ) ≤ A₀ * Real.log (|t| + 3)) (a : ℝ) (n : ℕ) :
    (Z.N a (a + n) : ℝ) ≤ n * A₀ * Real.log (|a| + n + 3) := by
  induction n with
  | zero =>
    simp only [Nat.cast_zero, add_zero, zero_mul]
    have : Z.N a a = 0 := by
      unfold ZeroConfig.N
      have : Z.window a a = ∅ := by
        ext ρ
        simp only [ZeroConfig.window, Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_empty_iff_false,
          iff_false]
        rintro ⟨_, h1, h2⟩; linarith
      rw [this, finsum_mem_empty]
    rw [this]; simp
  | succ n ih =>
    have hsplit : Z.N a (a + (n + 1 : ℕ)) = Z.N a (a + n) + Z.N (a + n) (a + n + 1) := by
      push_cast
      rw [← add_assoc]
      exact N_add Z (by linarith [(n.cast_nonneg : (0:ℝ) ≤ n)]) (by linarith)
    rw [hsplit]
    push_cast
    have h1 := hloc (a + n)
    have hlogmono : Real.log (|a| + n + 3) ≤ Real.log (|a| + (n + 1) + 3) :=
      Real.log_le_log (by positivity) (by linarith)
    have hlogmono' : Real.log (|a + n| + 3) ≤ Real.log (|a| + (n + 1) + 3) :=
      Real.log_le_log (by positivity) (by linarith [abs_add_le a (n : ℝ), abs_of_nonneg (n.cast_nonneg : (0:ℝ) ≤ n)])
    have hA : 0 ≤ A₀ := by linarith
    have hn : (0 : ℝ) ≤ n := n.cast_nonneg
    calc ((Z.N a (a + n) : ℕ) : ℝ) + ((Z.N (a + n) (a + n + 1) : ℕ) : ℝ)
        ≤ n * A₀ * Real.log (|a| + n + 3) + A₀ * Real.log (|a + n| + 3) := add_le_add ih h1
      _ ≤ n * A₀ * Real.log (|a| + (n + 1) + 3) + A₀ * Real.log (|a| + (n + 1) + 3) := by
          gcongr
      _ = (n + 1) * A₀ * Real.log (|a| + (n + 1) + 3) := by ring

lemma N_le_of_local_count_real {A₀ : ℝ} (hA₀ : 1 ≤ A₀)
    (hloc : ∀ t : ℝ, (Z.N t (t + 1) : ℝ) ≤ A₀ * Real.log (|t| + 3)) (a : ℝ) {ℓ : ℝ} (hℓ : 0 ≤ ℓ) :
    (Z.N a (a + ℓ) : ℝ) ≤ (ℓ + 1) * A₀ * Real.log (|a| + ℓ + 4) := by
  set n : ℕ := ⌈ℓ⌉₊ with hn
  have hn1 : ℓ ≤ n := Nat.le_ceil ℓ
  have hn2 : (n : ℝ) < ℓ + 1 := Nat.ceil_lt_add_one hℓ
  have hA : 0 ≤ A₀ := by linarith
  have hmono : (Z.N a (a + ℓ) : ℝ) ≤ Z.N a (a + n) := by
    exact_mod_cast N_mono Z le_rfl (by linarith)
  have hlog : Real.log (|a| + n + 3) ≤ Real.log (|a| + ℓ + 4) :=
    Real.log_le_log (by positivity) (by linarith)
  have hlog0 : 0 ≤ Real.log (|a| + n + 3) := Real.log_nonneg (by linarith [abs_nonneg a, (n.cast_nonneg : (0:ℝ) ≤ n)])
  calc (Z.N a (a + ℓ) : ℝ) ≤ Z.N a (a + n) := hmono
    _ ≤ n * A₀ * Real.log (|a| + n + 3) := N_le_of_local_count Z hA₀ hloc a n
    _ ≤ (ℓ + 1) * A₀ * Real.log (|a| + ℓ + 4) := by gcongr

end Strips

section StripInclusion

lemma N0s_le_card_retained_add (Z : ZeroConfig) (P : Params) (T : ℝ) (hL : 0 < P.L T) :
    (Z.N0s T (2 * T) : ℝ) ≤ (retained Z P T).card
      + Z.N T (T + 2 * Real.pi * P.L T)
      + Z.N (2 * T - (2 * Real.pi * P.L T + 2 * Real.pi / P.L T)) (2 * T) := by
  classical
  set ℓ : ℝ := 2 * Real.pi * P.L T with hℓ
  set ℓ' : ℝ := 2 * Real.pi * P.L T + 2 * Real.pi / P.L T with hℓ'
  set A : Set ℂ := Z.window T (2 * T) ∩ ZeroConfig.onLine ∩ Z.simple with hA
  set R : Finset ℂ := (retained Z P T).map (Function.Embedding.subtype _) with hR
  have hπ : (0 : ℝ) < 2 * Real.pi := by positivity
  have hD0 : 0 ≤ D0 T := Real.sqrt_nonneg T
  have hsub : A ⊆ (↑R : Set ℂ) ∪ Z.window T (T + ℓ) ∪ Z.window (2 * T - ℓ') (2 * T) := by
    rintro ρ ⟨⟨⟨hρc, hT1, hT2⟩, hre⟩, hm⟩
    have hre' : ρ.re = 1 / 2 := hre
    have hm' : Z.mult ρ = 1 := hm
    have hρZ : ρ ∈ ZI Z T := by
      rw [mem_ZI, mem_ZIprime_iff]
      exact ⟨hρc, by linarith, by linarith⟩
    set z : ZI Z T := ⟨ρ, hρZ⟩ with hz
    have hzS : z ∈ (bdata Z P T).S₁ := by
      simp only [ZeroBlockData.S₁, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨(mkData_σ_eq_iff Z T _ _ z).mpr hre', hm'⟩
    by_cases hx : P.L T ^ 2 ≤ xnorm P T z ∧ xnorm P T z ≤ (P.d T : ℝ) - P.L T ^ 2
    · left; left
      rw [Finset.mem_coe, hR, Finset.mem_map]
      exact ⟨z, Finset.mem_filter.mpr ⟨hzS, hx⟩, rfl⟩
    · rw [not_and_or] at hx
      rcases hx with hx | hx
      · left; right
        refine ⟨hρc, hT1, ?_⟩
        push Not at hx
        unfold xnorm at hx
        have h1 := (div_lt_iff₀ hπ).mp hx
        have : P.L T * (ρ.im - T) < P.L T * ℓ := by rw [hℓ]; nlinarith
        have := lt_of_mul_lt_mul_left this hL.le
        show ρ.im ≤ T + ℓ
        linarith
      · right
        refine ⟨hρc, ?_, hT2⟩
        push Not at hx
        unfold xnorm at hx
        have h1 := (lt_div_iff₀ hπ).mp hx
        have hd : P.L T * T / (2 * Real.pi) < (P.d T : ℝ) + 1 := Nat.lt_floor_add_one _
        have hd' := (div_lt_iff₀ hπ).mp hd
        have hLℓ' : P.L T * ℓ' = 2 * Real.pi * P.L T ^ 2 + 2 * Real.pi := by
          rw [hℓ']; field_simp
        have : P.L T * (2 * T - ℓ') < P.L T * ρ.im := by nlinarith
        exact lt_of_mul_lt_mul_left this hL.le
  have hfin : ((↑R : Set ℂ) ∪ Z.window T (T + ℓ) ∪ Z.window (2 * T - ℓ') (2 * T)).Finite :=
    ((R.finite_toSet).union (Z.finite_window _ _)).union (Z.finite_window _ _)
  have hN0s : Z.N0s T (2 * T) = A.ncard := rfl
  have hcard : ((↑R : Set ℂ).ncard : ℝ) = (retained Z P T).card := by
    rw [Set.ncard_coe_finset, hR, Finset.card_map]
  have hlo := ncard_window_le_N Z T (T + ℓ)
  have hhi := ncard_window_le_N Z (2 * T - ℓ') (2 * T)
  have hu : ((↑R : Set ℂ) ∪ Z.window T (T + ℓ) ∪ Z.window (2 * T - ℓ') (2 * T)).ncard
      ≤ (↑R : Set ℂ).ncard + (Z.window T (T + ℓ)).ncard + (Z.window (2 * T - ℓ') (2 * T)).ncard :=
    (Set.ncard_union_le _ _).trans (by gcongr; exact Set.ncard_union_le _ _)
  have hle : A.ncard ≤ (↑R : Set ℂ).ncard + (Z.window T (T + ℓ)).ncard
      + (Z.window (2 * T - ℓ') (2 * T)).ncard :=
    (Set.ncard_le_ncard hsub hfin).trans hu
  rw [hN0s]
  calc (A.ncard : ℝ) ≤ ((↑R : Set ℂ).ncard : ℝ) + (Z.window T (T + ℓ)).ncard
        + (Z.window (2 * T - ℓ') (2 * T)).ncard := by exact_mod_cast hle
    _ ≤ (retained Z P T).card + Z.N T (T + ℓ) + Z.N (2 * T - ℓ') (2 * T) := by
        rw [hcard]
        have hlo' : ((Z.window T (T + ℓ)).ncard : ℝ) ≤ Z.N T (T + ℓ) := by exact_mod_cast hlo
        have hhi' : ((Z.window (2 * T - ℓ') (2 * T)).ncard : ℝ) ≤ Z.N (2 * T - ℓ') (2 * T) := by
          exact_mod_cast hhi
        linarith

end StripInclusion

section StripCount

lemma strips_le (Z : ZeroConfig) {A₀ : ℝ} (hA₀ : 1 ≤ A₀)
    (hloc : ∀ t : ℝ, (Z.N t (t + 1) : ℝ) ≤ A₀ * Real.log (|t| + 3)) {T L : ℝ} (hT : 1 ≤ T)
    (hL1 : 1 ≤ L) (hLT : L ≤ T) (hlogT : Real.log T ≤ L + 2 * Real.pi) :
    (Z.N T (T + 2 * Real.pi * L) : ℝ) + Z.N (2 * T - (2 * Real.pi * L + 2 * Real.pi / L)) (2 * T)
      ≤ 1600 * A₀ * L ^ 2 := by
  have hπ := Real.pi_pos
  have hπ4 := Real.pi_lt_four
  have hπ3 := Real.pi_gt_three
  have hA : 0 ≤ A₀ := by linarith
  set ℓ : ℝ := 2 * Real.pi * L with hℓ
  set ℓ' : ℝ := 2 * Real.pi * L + 2 * Real.pi / L with hℓ'
  have hLpos : 0 < L := by linarith
  have hℓ0 : 0 ≤ ℓ := by positivity
  have h2πL : 2 * Real.pi / L ≤ 2 * Real.pi * L := by
    rw [div_le_iff₀ hLpos]; nlinarith
  have hℓ'0 : 0 ≤ ℓ' := by positivity
  have hℓ'le : ℓ' ≤ 4 * Real.pi * L := by rw [hℓ']; linarith
  have hℓle : ℓ ≤ ℓ' := by
    have : 0 ≤ 2 * Real.pi / L := by positivity
    rw [hℓ, hℓ']; linarith
  have h1 := N_le_of_local_count_real Z hA₀ hloc T hℓ0
  have h2 := N_le_of_local_count_real Z hA₀ hloc (2 * T - ℓ') hℓ'0
  rw [sub_add_cancel] at h2

  set M : ℝ := (6 + 8 * Real.pi) * T with hM
  have hM1 : |T| + ℓ + 4 ≤ M := by
    rw [abs_of_pos (by linarith), hM]; nlinarith
  have hM2 : |2 * T - ℓ'| + ℓ' + 4 ≤ M := by
    have : |2 * T - ℓ'| ≤ 2 * T + ℓ' := by
      rw [abs_le]; constructor <;> linarith
    rw [hM]; nlinarith
  have hlogM : Real.log M ≤ (6 + 10 * Real.pi) * L := by
    have hT0 : 0 < T := by linarith
    rw [hM, Real.log_mul (by positivity) hT0.ne']
    have := Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < 6 + 8 * Real.pi)
    nlinarith
  have hlog1 : Real.log (|T| + ℓ + 4) ≤ (6 + 10 * Real.pi) * L :=
    (Real.log_le_log (by positivity) hM1).trans hlogM
  have hlog2 : Real.log (|2 * T - ℓ'| + ℓ' + 4) ≤ (6 + 10 * Real.pi) * L :=
    (Real.log_le_log (by positivity) hM2).trans hlogM
  have hcoef : ℓ' + 1 ≤ (4 * Real.pi + 1) * L := by nlinarith
  have hcoef' : ℓ + 1 ≤ (4 * Real.pi + 1) * L := by linarith
  have hb1 : (Z.N T (T + ℓ) : ℝ) ≤ (4 * Real.pi + 1) * L * A₀ * ((6 + 10 * Real.pi) * L) := by
    refine h1.trans ?_
    have h0 : 0 ≤ Real.log (|T| + ℓ + 4) := Real.log_nonneg (by linarith [abs_nonneg T])
    gcongr
  have hb2 : (Z.N (2 * T - ℓ') (2 * T) : ℝ)
      ≤ (4 * Real.pi + 1) * L * A₀ * ((6 + 10 * Real.pi) * L) := by
    refine h2.trans ?_
    have h0 : 0 ≤ Real.log (|2 * T - ℓ'| + ℓ' + 4) :=
      Real.log_nonneg (by linarith [abs_nonneg (2 * T - ℓ')])
    gcongr
  have hL2 : 0 ≤ A₀ * L ^ 2 := by positivity
  have hconst : 2 * ((4 * Real.pi + 1) * (6 + 10 * Real.pi)) ≤ 1600 := by nlinarith
  calc (Z.N T (T + ℓ) : ℝ) + Z.N (2 * T - ℓ') (2 * T)
      ≤ 2 * ((4 * Real.pi + 1) * L * A₀ * ((6 + 10 * Real.pi) * L)) := by linarith
    _ = 2 * ((4 * Real.pi + 1) * (6 + 10 * Real.pi)) * (A₀ * L ^ 2) := by ring
    _ ≤ 1600 * (A₀ * L ^ 2) := by
        gcongr
    _ = 1600 * A₀ * L ^ 2 := by ring

end StripCount

end Zeta23Ext.Bridge

end

/-! ###### source module: Zeta23Ext/Bridge/S6.lean ###### -/



noncomputable section
set_option linter.unusedSectionVars false

open Matrix Finset RHLinalg
open scoped ComplexOrder BigOperators
open Zeta23 Zeta23.ZeroSide

namespace Zeta23Ext.Bridge

variable {ι d : Type*} [Fintype ι] [DecidableEq ι] [Fintype d] [DecidableEq d]
variable (D : ZeroBlockData ι d)

def multPart (c : ℝ) : Matrix d d ℂ :=
  ((c⁻¹ : ℝ) : ℂ) • ∑ z ∈ D.S₂, (D.m z : ℂ) • vecMulVec (D.v z) (D.v z)

lemma mem_S₂_σ {z : ι} (hz : z ∈ D.S₂) : D.σ z = z := by
  simp only [ZeroBlockData.S₂, mem_filter, mem_univ, true_and] at hz
  exact hz.1

lemma mem_S₁_σ {z : ι} (hz : z ∈ D.S₁) : D.σ z = z := by
  simp only [ZeroBlockData.S₁, mem_filter, mem_univ, true_and] at hz
  exact hz.1

lemma mem_S₁_m {z : ι} (hz : z ∈ D.S₁) : D.m z = 1 := by
  simp only [ZeroBlockData.S₁, mem_filter, mem_univ, true_and] at hz
  exact hz.2

lemma multPart_posSemidef {c : ℝ} (hc : 0 < c) : (multPart D c).PosSemidef := by
  unfold multPart
  refine (posSemidef_sum _ fun z hz => ?_).smul (Complex.zero_le_real.mpr (inv_nonneg.mpr hc.le))
  have := ZeroBlockData.posSemidef_smul_vecMulVec (D.star_v_of_onLine (mem_S₂_σ D hz)) (Nat.cast_nonneg (D.m z))
  simpa using this

lemma rank_multPart_le {c : ℝ} (hc : 0 < c) : (multPart D c).rank ≤ D.s₂ := by
  unfold multPart
  rw [rank_smul_of_ne_zero _ (by exact_mod_cast (inv_ne_zero hc.ne'))]
  refine (rank_sum_le _ _ (fun _ => 1) fun z _ => rank_smul_vecMulVec_le _ _ _).trans ?_
  simp [ZeroBlockData.s₂]

lemma P₁_eq_simplePart {c : ℝ} (hc : 0 < c) :
    P₁ D c = ((c⁻¹ : ℝ) : ℂ) • ∑ z ∈ D.S₁, (D.m z : ℂ) • vecMulVec (D.v z) (D.v z) := by
  ext k l
  simp only [P₁, Vsimple, mul_apply, conjTranspose_apply, Matrix.smul_apply, Matrix.sum_apply,
    vecMulVec_apply, smul_eq_mul]
  rw [← Finset.sum_coe_sort D.S₁, mul_sum]
  refine sum_congr rfl fun z _ => ?_
  have hσ := mem_S₁_σ D z.2
  have hm := mem_S₁_m D z.2
  have hstar : star (D.v z l) = D.v z l := congrFun (D.star_v_of_onLine hσ) l
  rw [hm, star_div₀, hstar, Nat.cast_one, one_mul, Complex.star_def, Complex.conj_ofReal]
  have hsq : ((Real.sqrt c : ℂ)) * (Real.sqrt c : ℂ) = (c : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt hc.le]
  rw [div_mul_div_comm, hsq, Complex.ofReal_inv, inv_mul_eq_div]

lemma Q'_eq_multPart_add_blockQ {c : ℝ} (hc : 0 < c) :
    Q' D c = multPart D c + D.blockQ c := by
  unfold Q' ZeroBlockData.blockP ZeroBlockData.onPart multPart
  rw [P₁_eq_simplePart D hc, D.onLine_eq_S₁_union_S₂, sum_union D.disjoint_S₁_S₂, smul_add]
  abel

theorem regroup_posIndex (Pr : D.PairReps) {c : ℝ} (hc : 0 < c) :
    posIndex (Q'_isHermitian D c) ≤ D.s₂ + Pr.p := by
  have hR := multPart_posSemidef D hc
  have hH : (multPart D c + D.blockQ c).IsHermitian := hR.isHermitian.add (D.blockQ_isHermitian c)
  rw [ZeroBlockData.posIndex_congr (Q'_isHermitian D c) hH (Q'_eq_multPart_add_blockQ D hc)]
  calc posIndex hH
      ≤ posIndex hR.isHermitian + posIndex (D.blockQ_isHermitian c) := posIndex_add_le _ _
    _ ≤ D.s₂ + Pr.p := by
        rw [posIndex_eq_rank_of_posSemidef hR]
        exact Nat.add_le_add (rank_multPart_le D hc) (D.posIndex_blockQ_le Pr hc)


end Zeta23Ext.Bridge

end

/-! ###### source module: Zeta23Ext/Bridge/S7.lean ###### -/



noncomputable section
set_option linter.unusedSectionVars false

open Matrix Finset RHLinalg
open scoped ComplexOrder BigOperators
open Zeta23 Zeta23.ZeroSide Zeta23Ext.StableRankTrace

namespace Zeta23Ext.Bridge

variable {ι d : Type*} [Fintype ι] [DecidableEq ι] [Fintype d] [DecidableEq d]
variable (D : ZeroBlockData ι d)

lemma Vsimple_col_le_one {c : ℝ} (hc : 0 < c)
    (hPois : ∀ z ∈ D.onLine, ∑ k, ‖D.v z k‖ ^ 2 ≤ c) (z : D.S₁) :
    ∑ k, ‖Vsimple D c k z‖ ^ 2 ≤ 1 := by
  have hz : (z : ι) ∈ D.onLine := by
    have := z.2
    simp only [ZeroBlockData.S₁, mem_filter, mem_univ, true_and] at this
    exact (D.mem_onLine).mpr this.1
  have hs : ∀ k, ‖Vsimple D c k z‖ ^ 2 = ‖D.v z k‖ ^ 2 / c := by
    intro k
    simp only [Vsimple]
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.sqrt_pos.mpr hc), div_pow,
      Real.sq_sqrt hc.le]
  simp_rw [hs]
  rw [← Finset.sum_div, div_le_one hc]
  exact hPois z hz

theorem count_defect (Pr : D.PairReps) {c : ℝ} (hc : 0 < c)
    (hPois : ∀ z ∈ D.onLine, ∑ k, ‖D.v z k‖ ^ 2 ≤ c) :
    4 * rtrace (D.blockP c + D.blockQ c) - frobSq (D.blockP c + D.blockQ c) - 2 * (D.Ncount : ℝ)
      + defect (gramS₁_isHermitian D c) ≤ (D.s₁ : ℝ) := by
  classical
  have hb := regroup_posIndex D Pr hc
  have h := stable_rank_trace (Vsimple D c) (Vsimple_col_le_one D hc hPois) (Q'_isHermitian D c) hb
  have e : Vsimple D c * (Vsimple D c)ᴴ + Q' D c = D.blockP c + D.blockQ c := P₁_add_Q' D c
  rw [e] at h
  have hN : (D.s₁ : ℝ) + 2 * D.s₂ + 2 * Pr.p ≤ D.Ncount := by
    exact_mod_cast D.s₁_add_two_s₂_add_two_p_le_Ncount Pr
  have hcard : (Fintype.card D.S₁ : ℝ) = D.s₁ := by rw [Fintype.card_coe]; rfl
  have hdef : defect (gramS₁_isHermitian D c)
      = rtrace (specMap (isHermitian_conjTranspose_mul_self (Vsimple D c)) Psi) := rfl
  rw [hcard] at h
  push_cast at h
  linarith


end Zeta23Ext.Bridge

end

/-! ###### source module: Zeta23Ext/Bridge/S8.lean ###### -/



noncomputable section

open Matrix RHLinalg Filter Topology
open Zeta23 Zeta23.ZeroSide Zeta23.ThmD

namespace Zeta23Ext.Bridge

theorem tail_passage (Z : ZeroConfig) (H : PaperInputs Z)
    (h7 : ∀ᶠ T in atTop,
      4 * rtrace ((mtParams T).hat T (Z.Az (mtParams T) T))
        - frobSq ((mtParams T).hat T (Z.Az (mtParams T) T))
        - 2 * (Z.NIprime T : ℝ) + Dcirc Z (mtParams T) T ≤ (Z.s1 T : ℝ)) :
    ∀ ε > 0, ∀ᶠ T in atTop,
      (HD 1 - ε) * (Z.N T (2 * T) : ℝ) + Dcirc Z (mtParams T) T ≤ (Z.N0s T (2 * T) : ℝ) := by

  set P : Params := paramsOf stdProfile 1 with hPdef
  have hP : P.Valid := paramsOf_valid taperProfile_stdProfile one_pos le_rfl
  have hlam : P.lam = 1 := rfl

  have hLoc : LocalHypsCoreDEventually P := localHypsCoreD_eventually hP
  have hTr := tracesBoundsD_concrete (Z := Z) hP H hLoc
  have hc := tendsto_cRatio_concrete hP Z
  have hc0 := cStar_pos hP.lam_pos hP.lam_le_one
  have ha : ∀ᶠ T in atTop, 1 / 2 ≤ (concreteDataD P Z).aT T ∧ (concreteDataD P Z).aT T ≤ 1 :=
    (concreteFactsD hP H hLoc).ab_range.mono fun T h => ⟨h.1.trans h.2.1, h.2.2.1⟩
  obtain ⟨θ₀, hTail, hθ₀⟩ := eventually_tailPackageD Z H hP
  obtain ⟨A₀, hA₀, hloc⟩ := H.RvM.local_count
  have hNII := Tail.eventually_NII_le Z hA₀ hloc
  have hGzGp := eventually_GzGpD Z H hP
  have hId : ∀ᶠ T in atTop,
      (P.atD T).trGtilde T = (concreteDataD P Z).trG T ∧
      (P.atD T).trGtildeSq T = (concreteDataD P Z).trG2 T ∧
      (P.atD T).a T = (concreteDataD P Z).aT T :=
    Eventually.of_forall fun T =>
      ⟨Params.atD_trGtilde T hP, Params.atD_trGtildeSq T hP, Params.atD_a T hP⟩
  have hcalE := Assembly.calE_tendsto_zero P hP.lam_pos hP.lam_le_one
    (zero_le_one.trans hP.one_le_w)

  have h := endgame_defect Z H P hP _ _ _ _ _ hTr hc0 hc ha θ₀ hTail hθ₀ hNII hGzGp hId hcalE
    (fun T => Dcirc Z (mtParams T) T) h7
  intro ε hε
  have h' := h ε hε

  have hHD : HD 1 = 2 - (cStar P.lam)⁻¹ := by rw [hlam, HD, one_div]
  rw [hHD]
  exact h'


end Zeta23Ext.Bridge

end

/-! ###### source module: Zeta23Ext/Bridge/S9.lean ###### -/



noncomputable section

open Matrix RHLinalg Filter
open Zeta23 Zeta23.ZeroSide Zeta23.ThmD

namespace Zeta23Ext.Bridge

open Classical

set_option linter.unusedVariables false in

theorem kernel_limit (Z : ZeroConfig) (H : PaperInputs Z) (R₀ : ℝ) :
    ∀ δ > 0, ∀ᶠ T in atTop, ∀ z z' : retained Z (mtParams T) T,
      |xret Z (mtParams T) T z - xret Z (mtParams T) T z'| ≤ R₀ →
      ‖gram Z (mtParams T) T z z'
          - (kfun (xret Z (mtParams T) T z - xret Z (mtParams T) T z') : ℂ)‖ ≤ δ := by
  intro δ hδ
  have hP : (paramsOf stdProfile 1).Valid := paramsOf_valid taperProfile_stdProfile one_pos le_rfl
  have hlam : (paramsOf stdProfile 1).lam = 1 := rfl
  obtain ⟨T₀, hT₀⟩ := localHypsCoreD_eventually hP
  set K : ℝ := (cDT (paramsOf stdProfile 1).ϱ (paramsOf stdProfile 1).lam
    / (paramsOf stdProfile 1).w) ^ 2 with hK
  have hK0 : 0 ≤ K := sq_nonneg _
  have hw : 0 < (paramsOf stdProfile 1).w := by linarith [hP.one_le_w]
  filter_upwards [eventually_gt_atTop 0, eventually_w8 hP, eventually_w4pi hP,
    eventually_ge_atTop T₀, (tendsto_L hP).eventually_ge_atTop 1,
    (tendsto_L hP).eventually_ge_atTop ((10 * K + 12 * (paramsOf stdProfile 1).w) / δ)]
    with T hT h8 h4π hTT₀ hL1 hLδ
  intro z z' _
  have hF := (hT₀ T hTT₀).toCoreW
  have h := gram_close_of hP hlam hT h8 h4π hF Z z z'
  refine h.trans ?_
  set L := (paramsOf stdProfile 1).L T with hLdef
  have hL : 0 < L := by linarith
  have hL4 : L ≤ L ^ 4 := by nlinarith [pow_pos hL 2, pow_pos hL 3]
  have h1 : 10 * K / L ^ 4 ≤ 10 * K / L :=
    div_le_div_of_nonneg_left (by positivity) hL hL4
  have h2 : (10 * K + 12 * (paramsOf stdProfile 1).w) / L ≤ δ := by
    rw [div_le_iff₀ hL]
    have := (div_le_iff₀ hδ).mp hLδ
    linarith
  calc 10 * K / L ^ 4 + 12 * (paramsOf stdProfile 1).w / L
      ≤ 10 * K / L + 12 * (paramsOf stdProfile 1).w / L := by gcongr
    _ = (10 * K + 12 * (paramsOf stdProfile 1).w) / L := by ring
    _ ≤ δ := h2

theorem deleted_strips (Z : ZeroConfig) (H : PaperInputs Z) :
    ∀ ε > 0, ∀ᶠ T in atTop,
      (Z.N0s T (2 * T) : ℝ) - ε * (Z.N T (2 * T) : ℝ)
        ≤ ((retained Z (mtParams T) T).card : ℝ) := by
  intro ε hε
  have hP : (paramsOf stdProfile 1).Valid := paramsOf_valid taperProfile_stdProfile one_pos le_rfl
  obtain ⟨A₀, hA₀, hloc⟩ := H.RvM.local_count
  obtain ⟨C, T₀, hRvM⟩ := H.RvM.main
  have hA0 : 0 < A₀ := by linarith
  have hπ := Real.pi_pos
  set c : ℝ := ε / (4 * Real.pi * (1600 * A₀)) with hc
  have hcpos : 0 < c := by positivity
  have hlittle : ∀ᶠ x in atTop, ‖Real.log x‖ ≤ c * ‖id x‖ :=
    Real.isLittleO_log_id_atTop.def hcpos
  filter_upwards [eventually_ge_atTop 1, eventually_ge_atTop T₀,
    (tendsto_L hP).eventually_ge_atTop 1, hlittle,
    eventually_ge_atTop (4 * Real.pi * |C| * (1 + 2 * Real.pi))] with T hT1 hTT₀ hL1 hlog hTC
  have hT0 : 0 < T := by linarith
  set L : ℝ := (paramsOf stdProfile 1).L T with hLdef

  have hLeq : L = Real.log T - Real.log (2 * Real.pi) := by
    rw [hLdef]
    show 1 * Real.log (T / (2 * Real.pi)) = _
    rw [one_mul, Real.log_div hT0.ne' (by positivity)]
  have hlog2π0 : 0 < Real.log (2 * Real.pi) := Real.log_pos (by linarith [Real.pi_gt_three])
  have hlog2π : Real.log (2 * Real.pi) ≤ 2 * Real.pi - 1 := Real.log_le_sub_one_of_pos (by positivity)
  have hlogT : Real.log T ≤ L + 2 * Real.pi := by linarith
  have hLlogT : L ≤ Real.log T := by linarith
  have hlogT_le : Real.log T ≤ T - 1 := Real.log_le_sub_one_of_pos hT0
  have hLT : L ≤ T := by linarith
  have hlogT0 : 0 ≤ Real.log T := Real.log_nonneg hT1
  have hlogc : Real.log T ≤ c * T := by
    have h := hlog
    simp only [id, Real.norm_eq_abs, abs_of_pos hT0, abs_of_nonneg hlogT0] at h
    exact h

  have hLpos : 0 < (mtParams T).L T := by show 0 < L; linarith
  have hincl := N0s_le_card_retained_add Z (mtParams T) T hLpos
  have hstrips := strips_le Z hA₀ hloc hT1 hL1 hLT hlogT
  have hincl' : (Z.N0s T (2 * T) : ℝ) ≤ (retained Z (mtParams T) T).card + 1600 * A₀ * L ^ 2 := by
    have e1 : (mtParams T).L T = L := rfl
    rw [e1] at hincl
    linarith

  have hN : T * L / (2 * Real.pi) - |C| * Real.log T ≤ (Z.N T (2 * T) : ℝ) := by
    have h := hRvM T hTT₀
    have hℓ₁ : L ≤ ell1 T := by
      show 1 * l T ≤ l T + 2 * Real.log 2 - 1
      have := Real.log_two_gt_d9
      linarith
    have h1 := (abs_le.mp h).1
    have h2 : C * Real.log T ≤ |C| * Real.log T :=
      mul_le_mul_of_nonneg_right (le_abs_self C) hlogT0
    have h3 : T * L / (2 * Real.pi) ≤ T / (2 * Real.pi) * ell1 T := by
      rw [mul_div_right_comm]
      exact mul_le_mul_of_nonneg_left hℓ₁ (by positivity)
    linarith

  have hkey : 1600 * A₀ * L ^ 2 + ε * |C| * Real.log T ≤ ε * (T * L / (2 * Real.pi)) := by
    have hA : 1600 * A₀ * L ^ 2 ≤ ε * T * L / (4 * Real.pi) := by
      have h1 : 1600 * A₀ * L ^ 2 ≤ 1600 * A₀ * L * (c * T) := by
        have : L * L ≤ L * (c * T) := by
          have : L ≤ c * T := hLlogT.trans hlogc
          exact mul_le_mul_of_nonneg_left this (by linarith)
        nlinarith
      have h2 : 1600 * A₀ * L * (c * T) = ε * T * L / (4 * Real.pi) := by
        rw [hc]; field_simp
      linarith
    have hB : ε * |C| * Real.log T ≤ ε * T * L / (4 * Real.pi) := by
      have h1 : |C| * Real.log T ≤ |C| * ((1 + 2 * Real.pi) * L) := by
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg C)
        nlinarith
      have h2 : |C| * (1 + 2 * Real.pi) * (4 * Real.pi) ≤ T := by linarith
      have h3 : |C| * ((1 + 2 * Real.pi) * L) ≤ T * L / (4 * Real.pi) := by
        rw [le_div_iff₀ (by positivity)]
        have hL0 : 0 ≤ L := by linarith
        nlinarith
      calc ε * |C| * Real.log T = ε * (|C| * Real.log T) := by ring
        _ ≤ ε * (|C| * ((1 + 2 * Real.pi) * L)) := mul_le_mul_of_nonneg_left h1 hε.le
        _ ≤ ε * (T * L / (4 * Real.pi)) := mul_le_mul_of_nonneg_left h3 hε.le
        _ = ε * T * L / (4 * Real.pi) := by ring
    have : ε * T * L / (4 * Real.pi) + ε * T * L / (4 * Real.pi) = ε * (T * L / (2 * Real.pi)) := by
      field_simp
      ring
    linarith
  have hεN : 1600 * A₀ * L ^ 2 ≤ ε * (Z.N T (2 * T) : ℝ) := by
    have := mul_le_mul_of_nonneg_left hN hε.le
    nlinarith [hkey]
  linarith


end Zeta23Ext.Bridge

end

/-! ###### source module: Zeta23Ext/Bridge/S11.lean ###### -/



noncomputable section
set_option linter.unusedSectionVars false

open Finset
open scoped BigOperators

namespace Zeta23Ext.Bridge

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def pairCoef (n r : ℕ) : ℝ := 2 / ((n : ℝ) - (r : ℝ))

lemma energyOn_eq_sorted {m : ℕ} (x : ι → ℝ) (hx : Function.Injective x)
    (hS : (univ.image x).card = m) :
    energyOn x univ = ∑ r : Fin m × Fin m,
      if r.1 = r.2 then 0 else wfun ((univ.image x).orderEmbOfFin hS r.1
        - (univ.image x).orderEmbOfFin hS r.2) := by
  classical
  set S := univ.image x with hSdef
  set y := S.orderEmbOfFin hS with hydef
  have hy : Function.Injective y := y.injective
  have hSy : univ.image y = S := by
    apply Finset.coe_injective
    rw [coe_image, coe_univ, Set.image_univ]
    exact Finset.range_orderEmbOfFin S hS
  unfold energyOn
  have h1 : ∀ i j : ι, (if i = j then (0 : ℝ) else wfun (x i - x j))
      = (if x i = x j then 0 else wfun (x i - x j)) := by
    intro i j; simp [hx.eq_iff]
  simp_rw [h1]
  have e1 : ∀ i : ι, ∑ j, (if x i = x j then (0 : ℝ) else wfun (x i - x j))
      = ∑ t ∈ S, (if x i = t then 0 else wfun (x i - t)) := fun i =>
    (sum_image (f := fun t => if x i = t then (0 : ℝ) else wfun (x i - t))
      (fun a _ b _ h => hx h)).symm
  simp_rw [e1]
  rw [← sum_image (f := fun s => ∑ t ∈ S, (if s = t then (0 : ℝ) else wfun (s - t)))
    (fun a _ b _ h => hx h)]
  rw [← hSdef, ← hSy, sum_image (fun a _ b _ h => hy h)]
  simp_rw [sum_image (fun a _ b _ h => hy h)]
  simp only [hy.eq_iff]
  exact (Fintype.sum_prod_type' (f := fun k l => if k = l then (0 : ℝ) else wfun (y k - y l))).symm

lemma window_pairs_le_energy {n m : ℕ} (hn : 2 ≤ n) (hm : n ≤ m) (x : ι → ℝ)
    (hx : Function.Injective x) (hS : (univ.image x).card = m) :
    ∑ i ∈ range (m - (n - 1)), ∑ a : Fin n, ∑ b : Fin n,
        (if (a : ℕ) < (b : ℕ) then
          pairCoef n ((b : ℕ) - (a : ℕ))
            * wfun (sortedExt ((univ.image x).orderEmbOfFin hS) (i + b)
                - sortedExt ((univ.image x).orderEmbOfFin hS) (i + a))
        else 0)
      ≤ energyOn x univ := by
  classical
  set y : Fin m → ℝ := ⇑((univ.image x).orderEmbOfFin hS) with hydef
  set Y := sortedExt y with hYdef
  have hm0 : 0 < m := by omega

  set T : Finset (ℕ × (Fin n × Fin n)) :=
    (range (m - (n - 1)) ×ˢ (univ : Finset (Fin n × Fin n))).filter fun t => (t.2.1 : ℕ) < t.2.2
    with hTdef
  set f : ℕ × (Fin n × Fin n) → ℝ := fun t =>
    pairCoef n ((t.2.2 : ℕ) - (t.2.1 : ℕ)) * wfun (Y (t.1 + t.2.2) - Y (t.1 + t.2.1)) with hfdef
  have hLHS : ∑ i ∈ range (m - (n - 1)), ∑ a : Fin n, ∑ b : Fin n,
      (if (a : ℕ) < (b : ℕ) then
        pairCoef n ((b : ℕ) - (a : ℕ)) * wfun (Y (i + b) - Y (i + a)) else 0)
      = ∑ t ∈ T, f t := by
    rw [hTdef, sum_filter, sum_product]
    refine sum_congr rfl fun i _ => ?_
    exact (Fintype.sum_prod_type' (f := fun (a b : Fin n) => if (a : ℕ) < (b : ℕ) then
      pairCoef n ((b : ℕ) - (a : ℕ)) * wfun (Y (i + b) - Y (i + a)) else 0)).symm
  rw [hLHS]

  set φ : ℕ × (Fin n × Fin n) → ℕ × ℕ := fun t => (t.1 + t.2.1, t.1 + t.2.2) with hφdef
  set I := T.image φ with hIdef
  have hmem : ∀ t ∈ T, t.1 < m - (n - 1) ∧ (t.2.1 : ℕ) < t.2.2 := by
    intro t ht
    simp only [hTdef, mem_filter, mem_product, mem_range, mem_univ, and_true] at ht
    exact ht
  have hI : ∀ q ∈ I, q.1 < q.2 ∧ q.2 < m ∧ q.2 - q.1 < n := by
    intro q hq
    obtain ⟨t, ht, rfl⟩ := mem_image.mp hq
    obtain ⟨h1, h2⟩ := hmem t ht
    have hb := t.2.2.2
    simp only [hφdef]
    omega

  rw [← sum_fiberwise_of_maps_to (g := φ) (t := I) (fun t ht => mem_image_of_mem φ ht)]

  have hfib : ∀ q ∈ I, ∑ t ∈ T with φ t = q, f t ≤ 2 * wfun (Y q.2 - Y q.1) := by
    intro q hq
    obtain ⟨hq1, hq2, hq3⟩ := hI q hq
    set r := q.2 - q.1 with hrdef
    have hconst : ∀ t ∈ T.filter (fun t => φ t = q), f t = pairCoef n r * wfun (Y q.2 - Y q.1) := by
      intro t ht
      rw [mem_filter] at ht
      obtain ⟨ht, hφt⟩ := ht
      have e1 : t.1 + (t.2.1 : ℕ) = q.1 := congrArg Prod.fst hφt
      have e2 : t.1 + (t.2.2 : ℕ) = q.2 := congrArg Prod.snd hφt
      simp only [hfdef]
      rw [e1, e2, hrdef, ← e1, ← e2, Nat.add_sub_add_left]
    rw [sum_congr rfl hconst, sum_const, nsmul_eq_mul]

    have hcard : (T.filter (fun t => φ t = q)).card ≤ n - r := by
      rw [← card_range (n - r)]
      refine card_le_card_of_injOn (fun t => (t.2.1 : ℕ)) ?_ ?_
      · intro t ht
        rw [mem_coe, mem_filter] at ht
        obtain ⟨ht, hφt⟩ := ht
        have e1 : t.1 + (t.2.1 : ℕ) = q.1 := congrArg Prod.fst hφt
        have e2 : t.1 + (t.2.2 : ℕ) = q.2 := congrArg Prod.snd hφt
        have hb := t.2.2.2
        simp only [coe_range, Set.mem_Iio]
        omega
      · intro t ht t' ht' hee
        rw [mem_coe, mem_filter] at ht ht'
        have e1 : t.1 + (t.2.1 : ℕ) = q.1 := congrArg Prod.fst ht.2
        have e2 : t.1 + (t.2.2 : ℕ) = q.2 := congrArg Prod.snd ht.2
        have e1' : t'.1 + (t'.2.1 : ℕ) = q.1 := congrArg Prod.fst ht'.2
        have e2' : t'.1 + (t'.2.2 : ℕ) = q.2 := congrArg Prod.snd ht'.2
        simp only at hee
        have ha : t.2.1 = t'.2.1 := Fin.ext hee
        have hi : t.1 = t'.1 := by omega
        have hb : t.2.2 = t'.2.2 := Fin.ext (by omega)
        exact Prod.ext hi (Prod.ext ha hb)
    have hr7 : (r : ℝ) < (n : ℝ) := by exact_mod_cast hq3
    have hcoef : 0 ≤ pairCoef n r := by
      unfold pairCoef; apply div_nonneg (by norm_num); linarith
    have hcardR : ((T.filter (fun t => φ t = q)).card : ℝ) ≤ (n : ℝ) - (r : ℝ) := by
      have := (Nat.cast_le (α := ℝ)).mpr hcard
      rwa [Nat.cast_sub hq3.le] at this
    calc ((T.filter (fun t => φ t = q)).card : ℝ) * (pairCoef n r * wfun (Y q.2 - Y q.1))
        ≤ ((n : ℝ) - (r : ℝ)) * (pairCoef n r * wfun (Y q.2 - Y q.1)) :=
          mul_le_mul_of_nonneg_right hcardR (mul_nonneg hcoef (wfun_nonneg _))
      _ = 2 * wfun (Y q.2 - Y q.1) := by
          have h7 : (n : ℝ) - (r : ℝ) ≠ 0 := by linarith
          unfold pairCoef
          field_simp
  refine (sum_le_sum hfib).trans ?_

  rw [energyOn_eq_sorted x hx hS, ← hydef]
  set G : Fin m × Fin m → ℝ := fun r => if r.1 = r.2 then 0 else wfun (y r.1 - y r.2) with hGdef
  set toFin : ℕ → Fin m := fun n => if h : n < m then ⟨n, h⟩ else ⟨0, hm0⟩ with htoFin
  have htoFin_lt : ∀ n (h : n < m), toFin n = ⟨n, h⟩ := by
    intro n h; simp only [htoFin, dif_pos h]
  set ψ₁ : ℕ × ℕ → Fin m × Fin m := fun q => (toFin q.1, toFin q.2) with hψ₁
  set ψ₂ : ℕ × ℕ → Fin m × Fin m := fun q => (toFin q.2, toFin q.1) with hψ₂
  have hG1 : ∀ q ∈ I, G (ψ₁ q) = wfun (Y q.2 - Y q.1) := by
    intro q hq
    obtain ⟨hq1, hq2, -⟩ := hI q hq
    have hq1m : q.1 < m := by omega
    simp only [hGdef, hψ₁, htoFin_lt _ hq1m, htoFin_lt _ hq2, hYdef,
      sortedExt_of_lt y hq1m, sortedExt_of_lt y hq2]
    rw [if_neg (by intro h; exact absurd (Fin.mk.inj_iff.mp h) hq1.ne), wfun_sub_comm]
  have hG2 : ∀ q ∈ I, G (ψ₂ q) = wfun (Y q.2 - Y q.1) := by
    intro q hq
    obtain ⟨hq1, hq2, -⟩ := hI q hq
    have hq1m : q.1 < m := by omega
    simp only [hGdef, hψ₂, htoFin_lt _ hq1m, htoFin_lt _ hq2, hYdef,
      sortedExt_of_lt y hq1m, sortedExt_of_lt y hq2]
    rw [if_neg (by intro h; exact absurd (Fin.mk.inj_iff.mp h) hq1.ne')]
  have hsplit : ∑ q ∈ I, 2 * wfun (Y q.2 - Y q.1) = ∑ q ∈ I, G (ψ₁ q) + ∑ q ∈ I, G (ψ₂ q) := by
    rw [← sum_add_distrib]
    refine sum_congr rfl fun q hq => ?_
    rw [hG1 q hq, hG2 q hq]; ring
  have hinj₁ : Set.InjOn ψ₁ I := by
    intro q hq q' hq' h
    obtain ⟨hq1, hq2, -⟩ := hI q hq
    obtain ⟨hq1', hq2', -⟩ := hI q' hq'
    simp only [hψ₁, htoFin_lt _ (by omega : q.1 < m), htoFin_lt _ hq2,
      htoFin_lt _ (by omega : q'.1 < m), htoFin_lt _ hq2', Prod.mk.injEq, Fin.mk.injEq] at h
    exact Prod.ext h.1 h.2
  have hinj₂ : Set.InjOn ψ₂ I := by
    intro q hq q' hq' h
    obtain ⟨hq1, hq2, -⟩ := hI q hq
    obtain ⟨hq1', hq2', -⟩ := hI q' hq'
    simp only [hψ₂, htoFin_lt _ (by omega : q.1 < m), htoFin_lt _ hq2,
      htoFin_lt _ (by omega : q'.1 < m), htoFin_lt _ hq2', Prod.mk.injEq, Fin.mk.injEq] at h
    exact Prod.ext h.2 h.1
  have hdisj : Disjoint (I.image ψ₁) (I.image ψ₂) := by
    rw [disjoint_left]
    intro r hr1 hr2
    obtain ⟨q, hq, rfl⟩ := mem_image.mp hr1
    obtain ⟨q', hq', hqq'⟩ := mem_image.mp hr2
    obtain ⟨hq1, hq2, -⟩ := hI q hq
    obtain ⟨hq1', hq2', -⟩ := hI q' hq'
    simp only [hψ₁, hψ₂, htoFin_lt _ (by omega : q.1 < m), htoFin_lt _ hq2,
      htoFin_lt _ (by omega : q'.1 < m), htoFin_lt _ hq2', Prod.mk.injEq, Fin.mk.injEq] at hqq'
    omega
  have hGnn : ∀ r, 0 ≤ G r := by
    intro r; simp only [hGdef]; split_ifs
    · exact le_rfl
    · exact wfun_nonneg _
  rw [hsplit, ← sum_image hinj₁, ← sum_image hinj₂, ← sum_union hdisj]
  exact sum_le_sum_of_subset_of_nonneg (subset_univ _) fun r _ _ => hGnn r

theorem block_energy {c : ℝ} {n p : ℕ} (hn : 2 ≤ n) (hp : 0 < p)
    (hCert : ∀ g : Fin (n - 1) → ℝ, (∀ i, 0 ≤ g i) → c ≤ F n p g)
    {m : ℕ} (hm : n ≤ m) (hcard : Fintype.card ι = m) (x : ι → ℝ) (hx : Function.Injective x) :
    c * ((m : ℝ) - ((n : ℝ) - 1))
      ≤ energyOn x univ + (((n : ℝ) - 1) / (p : ℝ)) * spanOf x univ := by
  classical

  have hS : (univ.image x).card = m := by
    rw [card_image_of_injective _ hx, card_univ, hcard]
  set y : Fin m → ℝ := ⇑((univ.image x).orderEmbOfFin hS) with hydef
  have hymem : ∀ k, y k ∈ univ.image x := fun k => Finset.orderEmbOfFin_mem _ hS k
  have hymono : StrictMono y := ((univ.image x).orderEmbOfFin hS).strictMono
  set Y := sortedExt y with hYdef
  have hm0 : 0 < m := by omega
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
  have hcastn : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ n)]; norm_num

  have hwin : ∀ i ∈ range (m - (n - 1)), c ≤ F n p (windowGaps n Y i) := by
    intro i hi
    rw [mem_range] at hi
    apply hCert
    intro j
    have hj := j.2
    have hlt : i + ((j : ℕ) + 1) < m := by omega
    exact sub_nonneg.mpr (sortedExt_mono hymono (by omega) hlt)
  have hsum : c * ((m : ℝ) - ((n : ℝ) - 1))
      ≤ ∑ i ∈ range (m - (n - 1)), F n p (windowGaps n Y i) := by
    have h := sum_le_sum hwin
    rw [sum_const, card_range, nsmul_eq_mul] at h
    have hcast : ((m - (n - 1) : ℕ) : ℝ) = (m : ℝ) - ((n : ℝ) - 1) := by
      rw [Nat.cast_sub (by omega : n - 1 ≤ m), hcastn]
    rw [hcast] at h
    linarith
  simp_rw [F_windowGaps] at hsum
  rw [sum_add_distrib, ← mul_sum] at hsum

  have hlin : ∑ i ∈ range (m - (n - 1)), (Y (i + (n - 1)) - Y i)
      ≤ ((n : ℝ) - 1) * spanOf x univ := by
    rw [sum_shift_sub]
    have hterm : ∀ i ∈ range (n - 1), Y (m - (n - 1) + i) - Y i ≤ Y (m - 1) - Y 0 := by
      intro i hi
      rw [mem_range] at hi
      have h1 := sortedExt_mono hymono (a := m - (n - 1) + i) (b := m - 1) (by omega) (by omega)
      have h2 := sortedExt_mono hymono (a := 0) (b := i) (by omega) (by omega)
      linarith
    have hspan : Y (m - 1) - Y 0 ≤ spanOf x univ := by
      obtain ⟨i₀, -, hi₀⟩ := mem_image.mp (hymem ⟨m - 1, by omega⟩)
      obtain ⟨j₀, -, hj₀⟩ := mem_image.mp (hymem ⟨0, hm0⟩)
      rw [hYdef, sortedExt_of_lt y (by omega : m - 1 < m), sortedExt_of_lt y hm0, ← hi₀, ← hj₀]
      exact (le_abs_self _).trans (abs_sub_le_spanOf x (mem_univ i₀) (mem_univ j₀))
    calc ∑ i ∈ range (n - 1), (Y (m - (n - 1) + i) - Y i)
        ≤ ∑ i ∈ range (n - 1), (Y (m - 1) - Y 0) := sum_le_sum hterm
      _ = ((n : ℝ) - 1) * (Y (m - 1) - Y 0) := by
          rw [sum_const, card_range, nsmul_eq_mul, hcastn]
      _ ≤ ((n : ℝ) - 1) * spanOf x univ := by nlinarith

  have hquad := window_pairs_le_energy hn hm x hx hS
  simp only [pairCoef] at hquad
  rw [← hydef, ← hYdef] at hquad
  have hp' : 0 ≤ 1 / (p : ℝ) := by positivity
  calc c * ((m : ℝ) - ((n : ℝ) - 1))
      ≤ _ := hsum
    _ ≤ (1 / (p : ℝ)) * (((n : ℝ) - 1) * spanOf x univ) + energyOn x univ := by
        gcongr
    _ = energyOn x univ + (((n : ℝ) - 1) / (p : ℝ)) * spanOf x univ := by ring


end Zeta23Ext.Bridge

end

/-! ###### source module: Zeta23Ext/Bridge/S12.lean ###### -/



noncomputable section
set_option linter.unusedSectionVars false

open Matrix Finset RHLinalg
open scoped ComplexOrder BigOperators
open Zeta23Ext.StableRankTrace

namespace Zeta23Ext.Bridge

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma specMap_const_one {A : Matrix ι ι ℂ} (hA : A.IsHermitian) :
    specMap hA (fun _ => 1) = 1 := by
  unfold specMap
  simp

lemma specMap_sub_one {A : Matrix ι ι ℂ} (hA : A.IsHermitian) :
    specMap hA (fun t => t - 1) = A - 1 := by
  have h : (fun t : ℝ => t - 1) = id - fun _ => 1 := rfl
  rw [h, specMap_sub, specMap_id, specMap_const_one]

lemma offDiagSqOn_le_frobSq_sub_one (A : Matrix ι ι ℂ) :
    offDiagSqOn A univ ≤ frobSq (A - 1) := by
  rw [Zeta23.Assembly.frobSq_eq_sum_norm_sq]
  unfold offDiagSqOn
  refine sum_le_sum fun i _ => sum_le_sum fun j _ => ?_
  split_ifs with h
  · positivity
  · rw [Matrix.sub_apply, Matrix.one_apply_ne h, sub_zero]

theorem block_defect_of_isHermitian {A : Matrix ι ι ℂ} (hA : A.IsHermitian) :
    min 1 (offDiagSqOn A univ) ≤ defect hA := by
  unfold defect
  rw [rtrace_specMap]
  by_cases hall : ∀ i, hA.eigenvalues i ≤ 2
  ·
    have hsum : ∑ i, Psi (hA.eigenvalues i) = ∑ i, (hA.eigenvalues i - 1) ^ 2 :=
      sum_congr rfl fun i _ => by simp [Psi, hall i]
    have hfrob := frobSq_specMap hA (fun t => t - 1)
    rw [specMap_sub_one] at hfrob
    rw [hsum, ← hfrob]
    exact (min_le_right _ _).trans (offDiagSqOn_le_frobSq_sub_one A)
  ·
    push Not at hall
    obtain ⟨i, hi⟩ := hall
    refine (min_le_left _ _).trans ?_
    calc (1 : ℝ) ≤ Psi (hA.eigenvalues i) := by
          unfold Psi; rw [if_neg (not_le.mpr hi)]; linarith
      _ ≤ ∑ j, Psi (hA.eigenvalues j) :=
          single_le_sum (fun j _ => Psi_nonneg (hA.eigenvalues j)) (mem_univ i)

theorem block_defect {G : Matrix ι ι ℂ} (hG : G.PosSemidef) :
    min 1 (offDiagSqOn G univ) ≤ defect hG.1 :=
  block_defect_of_isHermitian hG.1


end Zeta23Ext.Bridge

end

/-! ###### source module: Zeta23Ext/Bridge/S13.lean ###### -/



noncomputable section
set_option linter.unusedSectionVars false

open Matrix Finset RHLinalg
open scoped ComplexOrder BigOperators

namespace Zeta23Ext.Bridge

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma sq_sub_two_mul_le_sq {a b δ : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b)
    (h : |b - a| ≤ δ) : a ^ 2 - 2 * δ ≤ b ^ 2 := by
  rw [abs_le] at h
  obtain ⟨h1, h2⟩ := h
  rcases le_or_gt a b with hab | hab
  · nlinarith
  · rcases le_or_gt δ a with hδa | hδa
    · nlinarith
    · nlinarith

lemma wfun_sub_le_norm_sq {g : ℂ} {t δ : ℝ} (h : ‖g - (kfun t : ℂ)‖ ≤ δ) :
    wfun t - 2 * δ ≤ ‖g‖ ^ 2 := by
  have hk : ‖(kfun t : ℂ)‖ = |kfun t| := Complex.norm_real _
  have htri : abs (‖g‖ - |kfun t|) ≤ δ := by
    rw [← hk]; exact (abs_norm_sub_norm_le g _).trans h
  have := sq_sub_two_mul_le_sq (abs_nonneg _) (abs_kfun_le_one t) (norm_nonneg g) htri
  rw [sq_abs] at this
  exact this

lemma offDiagSqOn_submatrix (G : Matrix ι ι ℂ) (B : Finset ι) :
    offDiagSqOn (G.submatrix (Subtype.val : B → ι) Subtype.val) univ = offDiagSqOn G B := by
  unfold offDiagSqOn
  rw [← Finset.sum_coe_sort B]
  refine sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_coe_sort B]
  refine sum_congr rfl fun j _ => ?_
  simp only [submatrix_apply, Subtype.ext_iff]

lemma energyOn_subtype (x : ι → ℝ) (B : Finset ι) :
    energyOn (fun i : B => x i) univ = energyOn x B := by
  unfold energyOn
  rw [← Finset.sum_coe_sort B]
  refine sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_coe_sort B]
  refine sum_congr rfl fun j _ => ?_
  simp only [Subtype.ext_iff]

lemma spanOf_subtype_le (x : ι → ℝ) (B : Finset ι) :
    spanOf (fun i : B => x i) univ ≤ spanOf x B := by
  by_cases h1 : (univ : Finset B).Nonempty
  · have h2 : B.Nonempty := by
      obtain ⟨i, -⟩ := h1
      exact ⟨i.1, i.2⟩
    unfold spanOf
    rw [dif_pos h1, dif_pos h2]
    have hs : (univ : Finset B).sup' h1 (fun i : B => x i) ≤ B.sup' h2 x :=
      sup'_le _ _ fun i _ => le_sup' x i.2
    have hi : B.inf' h2 x ≤ (univ : Finset B).inf' h1 (fun i : B => x i) :=
      le_inf' _ _ fun i _ => inf'_le x i.2
    linarith
  · have h0 : spanOf (fun i : B => x i) univ = 0 := by
      unfold spanOf; rw [dif_neg h1]
    rw [h0]
    exact spanOf_nonneg x B

theorem block_bound {c : ℝ} {n m p : ℕ} (hn : 2 ≤ n) (hm : n ≤ m) (hp : 0 < p)
    (hCert : ∀ g : Fin (n - 1) → ℝ, (∀ i, 0 ≤ g i) → c ≤ F n p g)
    (hA0 : c * ((m : ℝ) - ((n : ℝ) - 1)) ≤ 1)
    (x : ι → ℝ) {G : Matrix ι ι ℂ} (hG : G.PosSemidef) (B : Finset ι) (hB : B.card = m)
    (hx : Set.InjOn x B) {δ : ℝ} (hδ : 0 ≤ δ)
    (hclose : ∀ i ∈ B, ∀ j ∈ B, i ≠ j → ‖G i j - (kfun (x i - x j) : ℂ)‖ ≤ δ) :
    c * ((m : ℝ) - ((n : ℝ) - 1)) - 2 * (m : ℝ) ^ 2 * δ
      ≤ blockDefect hG.1 B + (((n : ℝ) - 1) / (p : ℝ)) * spanOf x B := by
  classical
  have hn1 : (0 : ℝ) ≤ (n : ℝ) - 1 := by
    have : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
    linarith

  have hS12 : min 1 (offDiagSqOn G B) ≤ blockDefect hG.1 B := by
    have h := block_defect (hG.submatrix (Subtype.val : B → ι))
    rw [offDiagSqOn_submatrix] at h
    exact h

  have hoff : energyOn x B - 2 * (m : ℝ) ^ 2 * δ ≤ offDiagSqOn G B := by
    have hterm : ∀ i ∈ B, ∀ j ∈ B,
        (if i = j then (0 : ℝ) else wfun (x i - x j)) - 2 * δ
          ≤ (if i = j then 0 else ‖G i j‖ ^ 2) := by
      intro i hi j hj
      split_ifs with hij
      · linarith
      · exact wfun_sub_le_norm_sq (hclose i hi j hj hij)
    have hsum : ∑ i ∈ B, ∑ j ∈ B, ((if i = j then (0 : ℝ) else wfun (x i - x j)) - 2 * δ)
        ≤ offDiagSqOn G B :=
      sum_le_sum fun i hi => sum_le_sum fun j hj => hterm i hi j hj
    have hsplit : ∑ i ∈ B, ∑ j ∈ B, ((if i = j then (0 : ℝ) else wfun (x i - x j)) - 2 * δ)
        = energyOn x B - 2 * (m : ℝ) ^ 2 * δ := by
      unfold energyOn
      simp only [sum_sub_distrib, sum_const, nsmul_eq_mul, hB]
      ring
    linarith

  have hS11 : c * ((m : ℝ) - ((n : ℝ) - 1))
      ≤ energyOn x B + (((n : ℝ) - 1) / (p : ℝ)) * spanOf x B := by
    have hcard : Fintype.card B = m := by simp [hB]
    have hinj : Function.Injective (fun i : B => x i) := by
      intro i j h
      exact Subtype.ext (hx i.2 j.2 h)
    have h := block_energy hn hp hCert hm hcard (fun i : B => x i) hinj
    rw [energyOn_subtype] at h
    have hp' : (0 : ℝ) ≤ ((n : ℝ) - 1) / (p : ℝ) := div_nonneg hn1 (by positivity)
    have := mul_le_mul_of_nonneg_left (spanOf_subtype_le x B) hp'
    linarith

  have hspan := spanOf_nonneg x B
  have hp' : (0 : ℝ) ≤ ((n : ℝ) - 1) / (p : ℝ) := div_nonneg hn1 (by positivity)
  have hm2 : (0 : ℝ) ≤ 2 * (m : ℝ) ^ 2 * δ := by positivity
  rcases le_or_gt 1 (offDiagSqOn G B) with h1 | h1
  · rw [min_eq_left h1] at hS12
    nlinarith [mul_nonneg hp' hspan]
  · rw [min_eq_right h1.le] at hS12
    nlinarith [mul_nonneg hp' hspan]


end Zeta23Ext.Bridge

end

/-! ###### source module: Zeta23Ext/Bridge/S14.lean ###### -/



noncomputable section
set_option linter.unusedSectionVars false

open Matrix Finset RHLinalg
open scoped ComplexOrder BigOperators

namespace Zeta23Ext.Bridge

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem pinching_partition {M : Matrix ι ι ℂ} (hM : M.IsHermitian)
    (κ : Type) [Fintype κ] [DecidableEq κ] (β : ι → κ) :
    ∑ b, blockDefect hM (univ.filter fun i => β i = b) ≤ defect hM := by
  unfold blockDefect defect
  exact rtrace_specMap_pinching_le hM Psi_convexOn β

theorem pinching_submatrix {κ : Type*} [Fintype κ] [DecidableEq κ]
    {M : Matrix ι ι ℂ} (hM : M.IsHermitian) (f : κ → ι) (hf : Function.Injective f) :
    defect (hM.submatrix f) ≤ defect hM := by
  unfold defect
  exact rtrace_specMap_submatrix_le hM hf Psi_convexOn Zeta23Ext.StableRankTrace.Psi_nonneg


end Zeta23Ext.Bridge

end

/-! ###### source module: Zeta23Ext/Bridge/S15.lean ###### -/



noncomputable section
set_option linter.unusedSectionVars false

open Matrix Finset RHLinalg Filter
open scoped ComplexOrder BigOperators
open Zeta23 Zeta23.ZeroSide Zeta23.ThmD

namespace Zeta23Ext.Bridge

section Abstract

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma eq_of_mod_eq_of_overlap {m s s' k : ℕ} (_hm : 0 < m) (h : s % m = s' % m)
    (hs : s ≤ k ∧ k < s + m) (hs' : s' ≤ k ∧ k < s' + m) : s = s' := by
  rcases le_total s s' with h1 | h1
  · have hd : m ∣ s' - s := (Nat.modEq_iff_dvd' h1).mp h
    rcases Nat.eq_zero_or_pos (s' - s) with h0 | hpos
    · omega
    · have := Nat.le_of_dvd hpos hd; omega
  · have hd : m ∣ s - s' := (Nat.modEq_iff_dvd' h1).mp h.symm
    rcases Nat.eq_zero_or_pos (s - s') with h0 | hpos
    · omega
    · have := Nat.le_of_dvd hpos hd; omega

open Classical in

def blockStart (n m j k : ℕ) : ℕ :=
  if h : ∃ s, s + m ≤ n ∧ s % m = j ∧ s ≤ k ∧ k < s + m then h.choose else n

lemma blockStart_le (n m j k : ℕ) : blockStart n m j k ≤ n := by
  unfold blockStart
  split_ifs with h
  · have := h.choose_spec.1; omega
  · exact le_rfl

lemma blockStart_eq_iff {n m j k s : ℕ} (hm : 0 < m) (hs : s + m ≤ n) (hj : s % m = j) :
    blockStart n m j k = s ↔ (s ≤ k ∧ k < s + m) := by
  unfold blockStart
  constructor
  · intro h
    split_ifs at h with hex
    · obtain ⟨h1, h2, h3⟩ := hex.choose_spec
      rw [h] at h3; exact h3
    · omega
  · intro hk
    have hex : ∃ s, s + m ≤ n ∧ s % m = j ∧ s ≤ k ∧ k < s + m := ⟨s, hs, hj, hk⟩
    rw [dif_pos hex]
    obtain ⟨h1, h2, h3⟩ := hex.choose_spec
    exact eq_of_mod_eq_of_overlap hm (h2.trans hj.symm) h3 hk

theorem offset_average (x : ι → ℝ) (hx : Function.Injective x) {m : ℕ} (hm : 1 ≤ m)
    (Dblk : Finset ι → ℝ) (Dtot A q : ℝ) (hA : 0 ≤ A) (hq : 0 ≤ q)
    (hD0 : ∀ B, 0 ≤ Dblk B)
    (hblock : ∀ B : Finset ι, B.card = m → IsInterval x B → A ≤ Dblk B + q * spanOf x B)
    (hpinch : ∀ (κ : Type) [Fintype κ] [DecidableEq κ] (β : ι → κ),
      ∑ b, Dblk (univ.filter fun i => β i = b) ≤ Dtot) :
    A * ((Fintype.card ι : ℝ) - m) - q * ((m : ℝ) - 1) * spanOf x univ ≤ m * Dtot := by
  classical
  set n := Fintype.card ι with hndef
  have hDtot : 0 ≤ Dtot := by
    have h := hpinch Unit (fun _ => ())
    rw [Fintype.sum_unique] at h
    exact (hD0 _).trans h
  have hspan0 := spanOf_nonneg x (univ : Finset ι)
  have hm0 : 0 < m := hm
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm

  rcases lt_or_ge n m with hnm | hnm
  · have : (n : ℝ) - m ≤ 0 := by
      have : (n : ℝ) < m := by exact_mod_cast hnm
      linarith
    nlinarith [mul_nonneg hq (mul_nonneg (by linarith : (0:ℝ) ≤ (m : ℝ) - 1) hspan0),
      mul_nonneg hA (by linarith : (0:ℝ) ≤ (m : ℝ) - n), mul_nonneg (by positivity : (0:ℝ) ≤ m) hDtot]

  have hS : (univ.image x).card = n := by rw [card_image_of_injective _ hx, card_univ]
  set y : Fin n → ℝ := ⇑((univ.image x).orderEmbOfFin hS) with hydef
  have hymem : ∀ k, y k ∈ univ.image x := fun k => Finset.orderEmbOfFin_mem _ hS k
  have hymono : StrictMono y := ((univ.image x).orderEmbOfFin hS).strictMono
  choose ι' hι' using fun k => mem_image.mp (hymem k)
  have hι'inj : Function.Injective ι' := by
    intro k k' h
    apply hymono.injective
    rw [← (hι' k).2, ← (hι' k').2, h]
  have hbij : Function.Bijective ι' :=
    (Fintype.bijective_iff_injective_and_card ι').mpr ⟨hι'inj, by simp [hndef]⟩
  set e : Fin n ≃ ι := Equiv.ofBijective ι' hbij with hedef
  set pos : ι → ℕ := fun i => (e.symm i : ℕ) with hposdef
  set Y := sortedExt y with hYdef
  have hpos_lt : ∀ i, pos i < n := fun i => (e.symm i).2
  have hxY : ∀ i, x i = Y (pos i) := by
    intro i
    rw [hYdef, hposdef]; simp only
    rw [sortedExt_of_lt y (e.symm i).2, Fin.eta, ← (hι' (e.symm i)).2]
    congr 1
    exact (Equiv.ofBijective_apply_symm_apply ι' hbij i).symm
  have hpos_inj : Function.Injective pos := by
    intro i i' h
    have : e.symm i = e.symm i' := Fin.ext h
    exact e.symm.injective this
  have hle_iff : ∀ i i', x i ≤ x i' ↔ pos i ≤ pos i' := by
    intro i i'
    rw [hxY, hxY, hYdef, hposdef]; simp only
    rw [sortedExt_of_lt y (e.symm i).2, sortedExt_of_lt y (e.symm i').2, Fin.eta, Fin.eta,
      hymono.le_iff_le, Fin.le_def]

  set B : ℕ → Finset ι := fun s => univ.filter fun i => s ≤ pos i ∧ pos i < s + m with hBdef
  have hmemB : ∀ s i, i ∈ B s ↔ s ≤ pos i ∧ pos i < s + m := by
    intro s i; simp [hBdef]
  set toFin : ℕ → Fin n := fun t => if h : t < n then ⟨t, h⟩ else ⟨0, by omega⟩ with htoFin
  have hcardB : ∀ s, s + m ≤ n → (B s).card = m := by
    intro s hs
    have : (B s).card = (Ico s (s + m)).card := by
      refine card_nbij' pos (fun t => e (toFin t)) ?_ ?_ ?_ ?_
      · intro i hi
        rw [mem_coe, hmemB] at hi
        rw [mem_coe, mem_Ico]; exact hi
      · intro t ht
        rw [mem_coe, mem_Ico] at ht
        rw [mem_coe, hmemB]
        have htn : t < n := by omega
        simp only [hposdef, htoFin, dif_pos htn, Equiv.symm_apply_apply]
        exact ht
      · intro i hi
        have h := hpos_lt i
        simp only [htoFin, dif_pos h]
        simp only [hposdef, Fin.eta, Equiv.apply_symm_apply]
      · intro t ht
        rw [mem_coe, mem_Ico] at ht
        have htn : t < n := by omega
        simp only [hposdef, htoFin, dif_pos htn, Equiv.symm_apply_apply]
    rw [this, Nat.card_Ico]; omega
  have hintB : ∀ s, IsInterval x (B s) := by
    intro s i hi j hj k hik hkj
    rw [hmemB] at hi hj ⊢
    rw [hle_iff] at hik hkj
    omega
  have hspanB : ∀ s, s + m ≤ n → spanOf x (B s) ≤ Y (s + (m - 1)) - Y s := by
    intro s hs
    have hne : (B s).Nonempty := by
      rw [← card_pos, hcardB s hs]; exact hm0
    unfold spanOf
    rw [dif_pos hne]
    have h1 : (B s).sup' hne x ≤ Y (s + (m - 1)) := by
      apply sup'_le
      intro i hi
      rw [hmemB] at hi
      rw [hxY]
      exact sortedExt_mono hymono (by omega) (by omega)
    have h2 : Y s ≤ (B s).inf' hne x := by
      apply le_inf'
      intro i hi
      rw [hmemB] at hi
      rw [hxY]
      exact sortedExt_mono hymono (by omega) (hpos_lt i)
    linarith

  set St := range (n - m + 1) with hStdef
  have hmemSt : ∀ s, s ∈ St ↔ s + m ≤ n := by
    intro s; rw [hStdef, mem_range]; omega
  have hsumblock : A * ((n : ℝ) - m + 1) ≤ ∑ s ∈ St, Dblk (B s) + q * ∑ s ∈ St, spanOf x (B s) := by
    have h := sum_le_sum fun s (hs : s ∈ St) =>
      hblock (B s) (hcardB s ((hmemSt s).mp hs)) (hintB s)
    rw [sum_const, card_range, nsmul_eq_mul, sum_add_distrib, ← mul_sum] at h
    have hcast : ((n - m + 1 : ℕ) : ℝ) = (n : ℝ) - m + 1 := by
      rw [Nat.cast_add, Nat.cast_sub hnm]; norm_num
    rw [hcast] at h
    linarith

  have hspans : ∑ s ∈ St, spanOf x (B s) ≤ ((m : ℝ) - 1) * spanOf x univ := by
    have hY0 : ∀ i ∈ range (m - 1), Y (n - m + 1 + i) - Y i ≤ spanOf x univ := by
      intro i hi
      rw [mem_range] at hi
      have hi' : n - m + 1 + i < n := by omega
      obtain ⟨a, -, ha⟩ := mem_image.mp (hymem ⟨n - m + 1 + i, hi'⟩)
      obtain ⟨b, -, hb⟩ := mem_image.mp (hymem ⟨i, by omega⟩)
      rw [hYdef, sortedExt_of_lt y hi', sortedExt_of_lt y (by omega : i < n), ← ha, ← hb]
      exact (le_abs_self _).trans (abs_sub_le_spanOf x (mem_univ a) (mem_univ b))
    calc ∑ s ∈ St, spanOf x (B s)
        ≤ ∑ s ∈ St, (Y (s + (m - 1)) - Y s) :=
          sum_le_sum fun s hs => hspanB s ((hmemSt s).mp hs)
      _ = ∑ i ∈ range (m - 1), (Y (n - m + 1 + i) - Y i) := sum_shift_sub Y (m - 1) (n - m + 1)
      _ ≤ ∑ i ∈ range (m - 1), spanOf x univ := sum_le_sum hY0
      _ = ((m : ℝ) - 1) * spanOf x univ := by
          rw [sum_const, card_range, nsmul_eq_mul, Nat.cast_sub hm]; norm_num

  have hdefects : ∑ s ∈ St, Dblk (B s) ≤ m * Dtot := by
    rw [← sum_fiberwise_of_maps_to (g := fun s => s % m) (t := range m)
      (fun s _ => mem_range.mpr (Nat.mod_lt s hm0))]
    calc ∑ j ∈ range m, ∑ s ∈ St with s % m = j, Dblk (B s)
        ≤ ∑ j ∈ range m, Dtot := by
          refine sum_le_sum fun j hj => ?_

          set β : ι → Fin (n + 1) := fun i =>
            ⟨blockStart n m j (pos i), Nat.lt_succ_of_le (blockStart_le n m j (pos i))⟩ with hβ
          have hclass : ∀ s (hs : s + m ≤ n) (hj : s % m = j),
              (univ.filter fun i => β i = ⟨s, by omega⟩) = B s := by
            intro s hs hj
            ext i
            rw [mem_filter, hmemB, hβ]
            simp only [mem_univ, true_and, Fin.mk.injEq]
            exact blockStart_eq_iff hm0 hs hj
          set toFin' : ℕ → Fin (n + 1) := fun s => if h : s < n + 1 then ⟨s, h⟩ else 0 with htoFin'
          have hinj : Set.InjOn toFin' (St.filter (fun s => s % m = j)) := by
            intro s hs s' hs' h
            rw [mem_coe, mem_filter, hmemSt] at hs hs'
            simp only [htoFin', dif_pos (by omega : s < n + 1), dif_pos (by omega : s' < n + 1),
              Fin.mk.injEq] at h
            exact h
          calc ∑ s ∈ St with s % m = j, Dblk (B s)
              = ∑ s ∈ St with s % m = j, Dblk (univ.filter fun i => β i = toFin' s) := by
                refine sum_congr rfl fun s hs => ?_
                rw [mem_filter, hmemSt] at hs
                have hsn : s < n + 1 := by omega
                rw [← hclass s hs.1 hs.2]
                congr 2
                simp only [htoFin', dif_pos hsn]
            _ = ∑ b ∈ (St.filter (fun s => s % m = j)).image toFin',
                  Dblk (univ.filter fun i => β i = b) :=
                (sum_image (f := fun b => Dblk (univ.filter fun i => β i = b)) hinj).symm
            _ ≤ ∑ b, Dblk (univ.filter fun i => β i = b) :=
                sum_le_sum_of_subset_of_nonneg (subset_univ _) fun b _ _ => hD0 _
            _ ≤ Dtot := hpinch (Fin (n + 1)) β
      _ = m * Dtot := by rw [sum_const, card_range, nsmul_eq_mul]

  have hmn : (m : ℝ) ≤ n := by exact_mod_cast hnm
  calc A * ((n : ℝ) - m) - q * ((m : ℝ) - 1) * spanOf x univ
      ≤ A * ((n : ℝ) - m + 1) - q * ((m : ℝ) - 1) * spanOf x univ := by linarith
    _ ≤ ∑ s ∈ St, Dblk (B s) + q * ∑ s ∈ St, spanOf x (B s)
          - q * ((m : ℝ) - 1) * spanOf x univ := by linarith
    _ ≤ m * Dtot := by nlinarith [mul_le_mul_of_nonneg_left hspans hq]

end Abstract

section Analytic

open Classical

lemma spanOf_xret_le_d (Z : ZeroConfig) (P : Params) (T : ℝ) :
    spanOf (xret Z P T) univ ≤ (P.d T : ℝ) := by
  have hb : ∀ z : retained Z P T,
      P.L T ^ 2 ≤ xret Z P T z ∧ xret Z P T z ≤ (P.d T : ℝ) - P.L T ^ 2 :=
    fun z => (Finset.mem_filter.mp z.2).2
  unfold spanOf
  split_ifs with h
  · have h1 : (univ : Finset (retained Z P T)).sup' h (xret Z P T) ≤ (P.d T : ℝ) - P.L T ^ 2 :=
      sup'_le _ _ fun z _ => (hb z).2
    have h2 : P.L T ^ 2 ≤ (univ : Finset (retained Z P T)).inf' h (xret Z P T) :=
      le_inf' _ _ fun z _ => (hb z).1
    have : 0 ≤ P.L T ^ 2 := sq_nonneg _
    linarith
  · exact Nat.cast_nonneg _

theorem span_retained_le (Z : ZeroConfig) (H : PaperInputs Z) :
    ∀ ε > 0, ∀ᶠ T in atTop,
      spanOf (xret Z (mtParams T) T) univ ≤ (1 + ε) * (Z.N T (2 * T) : ℝ) := by
  intro ε hε
  obtain ⟨C, T₀, hRvM⟩ := H.RvM.main
  have hV : (paramsOf stdProfile 1).Valid := paramsOf_valid taperProfile_stdProfile one_pos le_rfl
  have hLpos : ∀ᶠ T in atTop, 0 < (mtParams T).L T := (tendsto_L hV).eventually_gt_atTop 0
  set K : ℝ := max ((1 + ε) * C / ε) 0 with hK
  have hK0 : 0 ≤ K := le_max_right _ _
  have hc : (0 : ℝ) < 1 / (2 * Real.pi * (K + 1)) := by positivity
  have hlogT : ∀ᶠ T in atTop, ‖Real.log T‖ ≤ (1 / (2 * Real.pi * (K + 1))) * ‖id T‖ :=
    Real.isLittleO_log_id_atTop.def hc
  have hell : ∀ᶠ T in atTop, 1 ≤ ell1 T := by
    have h : Tendsto (fun T : ℝ => Real.log (T / (2 * Real.pi))) atTop atTop :=
      Real.tendsto_log_atTop.comp (tendsto_id.atTop_div_const (by positivity))
    have h' : Tendsto (fun T : ℝ => Real.log (T / (2 * Real.pi)) + (2 * Real.log 2 - 1))
        atTop atTop := h.atTop_add tendsto_const_nhds
    exact (h'.eventually_ge_atTop 1).mono fun T hT => by unfold ell1 l; linarith
  filter_upwards [eventually_ge_atTop T₀, eventually_ge_atTop (2 * Real.pi), hLpos, hlogT, hell]
    with T hT₀ h2π hL hlog hel
  have hpi : 0 < 2 * Real.pi := by positivity
  have hT0 : 0 < T := lt_of_lt_of_le hpi h2π
  have hT1 : 1 ≤ T := by linarith [Real.pi_gt_three]
  have hLg0 : 0 ≤ Real.log T := Real.log_nonneg hT1
  have hl0 : 0 ≤ l T := Real.log_nonneg (by rw [le_div_iff₀ hpi]; linarith)
  have hN := abs_le.mp (hRvM T hT₀)

  have hLle : (mtParams T).L T ≤ l T := by
    show (paramsOf stdProfile 1).lam * l T ≤ l T
    exact mul_le_of_le_one_left hl0 hV.lam_le_one
  have hl_ell : l T ≤ ell1 T := by
    unfold ell1; linarith [Real.log_two_gt_d9]
  have hd : ((mtParams T).d T : ℝ) ≤ T / (2 * Real.pi) * ell1 T := by
    have h0 : 0 ≤ (mtParams T).L T * T / (2 * Real.pi) := by positivity
    calc ((mtParams T).d T : ℝ) ≤ (mtParams T).L T * T / (2 * Real.pi) := Nat.floor_le h0
      _ = T / (2 * Real.pi) * (mtParams T).L T := by ring
      _ ≤ T / (2 * Real.pi) * ell1 T := by gcongr; exact hLle.trans hl_ell

  have hKA : K * Real.log T ≤ T / (2 * Real.pi) * ell1 T := by
    simp only [Real.norm_eq_abs, id, abs_of_nonneg hLg0, abs_of_pos hT0] at hlog
    have h1 : K * Real.log T ≤ K * (1 / (2 * Real.pi * (K + 1)) * T) :=
      mul_le_mul_of_nonneg_left hlog hK0
    have h2 : K * (1 / (2 * Real.pi * (K + 1)) * T) ≤ T / (2 * Real.pi) := by
      rw [show K * (1 / (2 * Real.pi * (K + 1)) * T) = T / (2 * Real.pi) * (K / (K + 1)) by
        field_simp]
      have : K / (K + 1) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
      exact mul_le_of_le_one_right (by positivity) this
    have h3 : T / (2 * Real.pi) ≤ T / (2 * Real.pi) * ell1 T :=
      le_mul_of_one_le_right (by positivity) hel
    linarith
  have h1 : (1 + ε) * C / ε * Real.log T ≤ T / (2 * Real.pi) * ell1 T :=
    (mul_le_mul_of_nonneg_right (le_max_left _ _) hLg0).trans hKA
  have h2 : (1 + ε) * C * Real.log T ≤ ε * (T / (2 * Real.pi) * ell1 T) := by
    have e : (1 + ε) * C * Real.log T = ε * ((1 + ε) * C / ε * Real.log T) := by
      field_simp
    rw [e]
    exact mul_le_mul_of_nonneg_left h1 hε.le
  calc spanOf (xret Z (mtParams T) T) univ ≤ ((mtParams T).d T : ℝ) := spanOf_xret_le_d Z _ T
    _ ≤ (1 + ε) * (Z.N T (2 * T) : ℝ) := by nlinarith [hN.1, hN.2, hd, h2]

end Analytic


end Zeta23Ext.Bridge

end

/-! ###### source module: Zeta23Ext/Bridge/S16.lean ###### -/



noncomputable section

open Filter
open Zeta23.ThmD

namespace Zeta23Ext.Bridge

lemma one_sub_div_pos {c : ℝ} {n m : ℕ} (hn : 2 ≤ n) (hm : n ≤ m)
    (hA0 : c * ((m : ℝ) - ((n : ℝ) - 1)) ≤ 1) :
    0 < 1 - c * ((m : ℝ) - ((n : ℝ) - 1)) / m := by
  have hm' : (2 : ℝ) ≤ m := by exact_mod_cast (by omega : 2 ≤ m)
  have hmpos : (0 : ℝ) < m := by linarith
  rw [sub_pos, div_lt_one hmpos]
  linarith

theorem solve_linear {N N0 : ℝ → ℝ} {c : ℝ} {n m p : ℕ} (hn : 2 ≤ n) (hm : n ≤ m)
    (hA0 : c * ((m : ℝ) - ((n : ℝ) - 1)) ≤ 1)
    (h : ∀ ε > 0, ∀ᶠ T in atTop,
      (HD 1 - ((n : ℝ) - 1) * ((m : ℝ) - 1) / ((p : ℝ) * m) - ε) * N T
        ≤ (1 - c * ((m : ℝ) - ((n : ℝ) - 1)) / m) * N0 T) :
    ∀ ε > 0, ∀ᶠ T in atTop, (Phi_n n c m p - ε) * N T ≤ N0 T := by
  intro ε hε
  have hD := one_sub_div_pos hn hm hA0
  set Dn : ℝ := 1 - c * ((m : ℝ) - ((n : ℝ) - 1)) / m with hDn
  filter_upwards [h (ε * Dn) (mul_pos hε hD)] with T hT
  have hPhi : Phi_n n c m p
      = (HD 1 - ((n : ℝ) - 1) * ((m : ℝ) - 1) / ((p : ℝ) * m)) / Dn := rfl
  rw [hPhi]
  have : (HD 1 - ((n : ℝ) - 1) * ((m : ℝ) - 1) / ((p : ℝ) * m)) / Dn - ε
      = (HD 1 - ((n : ℝ) - 1) * ((m : ℝ) - 1) / ((p : ℝ) * m) - ε * Dn) / Dn := by
    field_simp
  rw [this, div_mul_eq_mul_div, div_le_iff₀ hD]
  linarith

theorem Phi_paper : Phi (19 / 5000) 269 3000 = (1345000 * HD 1 - 2680) / 1340003 := by
  unfold Phi
  norm_num
  field_simp
  ring

theorem Phi_paper' :
    Phi (19 / 5000) 269 3000
      = (1345000 * (3 / 2 - (Real.sqrt 2)⁻¹ * (Real.cos (Real.sqrt 2)⁻¹ / Real.sin (Real.sqrt 2)⁻¹))
          - 2680) / 1340003 := by
  rw [Phi_paper, HD_one]

theorem Phi_lab : Phi (34697 / 10000000) 294 3400
    = (520625000 * HD 1 - 915625) / 518855453 := by
  unfold Phi
  norm_num
  field_simp
  ring

theorem Phi_lab8 : Phi_n 8 (41763 / 10000000) 246 3200
    = (2460000000 * HD 1 - 5359375) / 2450018643 := by
  unfold Phi_n
  norm_num
  field_simp
  ring


end Zeta23Ext.Bridge

end

/-! ###### source module: Zeta23Ext/Bridge/Main.lean ###### -/



noncomputable section
set_option linter.unusedSectionVars false

open Matrix Finset RHLinalg Filter
open scoped ComplexOrder BigOperators
open Zeta23 Zeta23.ZeroSide Zeta23.ThmD

namespace Zeta23Ext.Bridge

open Classical

def P₀ : Params := paramsOf stdProfile 1

lemma P₀_valid : P₀.Valid := paramsOf_valid taperProfile_stdProfile one_pos le_rfl

lemma eventually_L_pos : ∀ᶠ T in atTop, 0 < (mtParams T).L T :=
  (tendsto_L P₀_valid).eventually_gt_atTop 0

theorem eventually_h7 (Z : ZeroConfig) :
    ∀ᶠ T in atTop,
      4 * rtrace ((mtParams T).hat T (Z.Az (mtParams T) T))
        - frobSq ((mtParams T).hat T (Z.Az (mtParams T) T))
        - 2 * (Z.NIprime T : ℝ) + Dcirc Z (mtParams T) T ≤ (Z.s1 T : ℝ) := by
  filter_upwards [eventually_w8 P₀_valid, eventually_w4pi P₀_valid] with T h8 h4π
  set P := mtParams T with hP
  have hconj : PhiHatConj T P := phiHatConj
  have hL : 0 < P.L T := by
    change 0 < P₀.L T; linarith [P₀_valid.one_le_w]
  have ha : 1 / 2 ≤ P.a T := (aD_range_of P₀_valid h8 h4π).1
  have hc : 0 < aL2 P T := mul_pos (by linarith) (pow_pos hL 2)
  have hPois : PoissonSq T P := poissonSqD P₀_valid h8
  have h7 := count_defect (bdata Z P T) (mkPairReps Z T _ (evalVec_reflect hconj)) hc
    (sum_normSq_v_le Z T P hconj phiHatReal hPois)
  have hD : Dcirc Z P T ≤ defect (gramS₁_isHermitian (bdata Z P T) (aL2 P T)) :=
    pinching_submatrix (gramS₁_isHermitian (bdata Z P T) (aL2 P T)) (toS₁ Z P T)
      (toS₁_injective Z P T)
  have hA : P.hat T (Z.Az P T) = (bdata Z P T).blockP (aL2 P T) + (bdata Z P T).blockQ (aL2 P T) :=
    hat_Az_eq_hatP_add_hatQ Z T P hconj
  have hN : (Z.NIprime T : ℝ) = ((bdata Z P T).Ncount : ℝ) := by
    rw [NIprime_eq_mk Z T _ (evalVec_reflect hconj)]; rfl
  have hs : (Z.s1 T : ℝ) = ((bdata Z P T).s₁ : ℝ) := by
    rw [s1_eq_mk Z T _ (evalVec_reflect hconj)]; rfl
  rw [hA, hN, hs]
  linarith [h7, hD]

theorem block_bound_eventually (Z : ZeroConfig) (H : PaperInputs Z) {c : ℝ} {n m p : ℕ}
    (hn : 2 ≤ n) (hm : n ≤ m) (hp : 0 < p)
    (hCert : ∀ g : Fin (n - 1) → ℝ, (∀ i, 0 ≤ g i) → c ≤ F n p g)
    (hA0 : c * ((m : ℝ) - ((n : ℝ) - 1)) ≤ 1)
    {η : ℝ} (hη : 0 < η) :
    ∀ᶠ T in atTop, ∀ B : Finset (retained Z (mtParams T) T), B.card = m →
      c * ((m : ℝ) - ((n : ℝ) - 1)) - η ≤ blockDefect (gram_isHermitian Z (mtParams T) T) B
        + (((n : ℝ) - 1) / (p : ℝ)) * spanOf (xret Z (mtParams T) T) B := by
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hgap : (1 : ℝ) ≤ (n : ℝ) - 1 := by linarith
  have hm' : (2 : ℝ) ≤ m := by exact_mod_cast (by omega : 2 ≤ m)
  have hmsq : 0 < 2 * (m : ℝ) ^ 2 := by positivity
  set δ : ℝ := η / (2 * (m : ℝ) ^ 2) with hδ
  have hδpos : 0 < δ := div_pos hη hmsq
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
  filter_upwards [kernel_limit Z H ((p : ℝ) / ((n : ℝ) - 1)) δ hδpos, eventually_L_pos]
    with T hclose hL
  intro B hB
  set x := xret Z (mtParams T) T with hx
  set q : ℝ := ((n : ℝ) - 1) / (p : ℝ) with hq
  have hq0 : 0 < q := by rw [hq]; exact div_pos (by linarith) hp'
  by_cases hsp : c * ((m : ℝ) - ((n : ℝ) - 1)) ≤ q * spanOf x B
  · linarith [blockDefect_nonneg (gram_isHermitian Z (mtParams T) T) B]
  · rw [not_le] at hsp
    have hR : spanOf x B ≤ (p : ℝ) / ((n : ℝ) - 1) := by
      have h1 : spanOf x B < 1 / q := by
        rw [lt_div_iff₀ hq0]; linarith
      have h1q : 1 / q = (p : ℝ) / ((n : ℝ) - 1) := by
        rw [hq]; exact one_div_div ((n : ℝ) - 1) (p : ℝ)
      linarith
    have hcl : ∀ i ∈ B, ∀ j ∈ B, i ≠ j →
        ‖gram Z (mtParams T) T i j - (kfun (x i - x j) : ℂ)‖ ≤ δ := by
      intro i hi j hj _
      exact hclose i j ((abs_sub_le_spanOf x hi hj).trans hR)
    have h13 := block_bound hn hm hp hCert hA0 x (gram_posSemidef Z (mtParams T) T) B hB
      (xret_injective Z (mtParams T) T hL).injOn hδpos.le hcl
    have hη' : 2 * (m : ℝ) ^ 2 * δ = η := by rw [hδ]; field_simp
    rw [hη'] at h13
    exact h13

theorem pre_solve (Z : ZeroConfig) (H : PaperInputs Z) {c : ℝ} {n m p : ℕ}
    (hn : 2 ≤ n) (hm : n ≤ m) (hp : 0 < p) (hc : 0 < c)
    (hCert : ∀ g : Fin (n - 1) → ℝ, (∀ i, 0 ≤ g i) → c ≤ F n p g)
    (hA0 : c * ((m : ℝ) - ((n : ℝ) - 1)) ≤ 1) :
    ∀ ε > 0, ∀ᶠ T in atTop,
      (HD 1 - ((n : ℝ) - 1) * ((m : ℝ) - 1) / ((p : ℝ) * m) - ε) * (Z.N T (2 * T) : ℝ)
        ≤ (1 - c * ((m : ℝ) - ((n : ℝ) - 1)) / m) * (Z.N0s T (2 * T) : ℝ) := by
  intro ε hε
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hmn : (n : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hm' : (2 : ℝ) ≤ m := le_trans hn' hmn
  have hmpos : (0 : ℝ) < m := by linarith
  have hgap : (1 : ℝ) ≤ (n : ℝ) - 1 := by linarith
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hA₀pos : 0 < c * ((m : ℝ) - ((n : ℝ) - 1)) := mul_pos hc (by linarith)
  have hq0 : (0 : ℝ) ≤ ((n : ℝ) - 1) / (p : ℝ) := div_nonneg (by linarith) hp'.le
  have hqn : ((n : ℝ) - 1) / (p : ℝ) ≤ (n : ℝ) - 1 := by
    rw [div_le_iff₀ hp']; nlinarith

  set Cn : ℝ := (m : ℝ) + 3 + ((n : ℝ) - 1) * ((m : ℝ) - 1) with hCn
  have hCnpos : 0 < Cn := by
    have h := mul_nonneg (by linarith : (0 : ℝ) ≤ (n : ℝ) - 1) (by linarith : (0 : ℝ) ≤ (m : ℝ) - 1)
    rw [hCn]; linarith
  have hCne : Cn ≠ 0 := hCnpos.ne'
  set ε₀ : ℝ := ε * (m : ℝ) / Cn with hε₀
  have hε₀pos : 0 < ε₀ := by rw [hε₀]; positivity
  have hηpos : 0 < min ε₀ (c * ((m : ℝ) - ((n : ℝ) - 1))) := lt_min hε₀pos hA₀pos
  have hηε : min ε₀ (c * ((m : ℝ) - ((n : ℝ) - 1))) ≤ ε₀ := min_le_left _ _
  have hηA : min ε₀ (c * ((m : ℝ) - ((n : ℝ) - 1))) ≤ c * ((m : ℝ) - ((n : ℝ) - 1)) :=
    min_le_right _ _
  have hA' : 0 ≤ c * ((m : ℝ) - ((n : ℝ) - 1)) - min ε₀ (c * ((m : ℝ) - ((n : ℝ) - 1))) := by
    linarith
  filter_upwards [block_bound_eventually Z H hn hm hp hCert hA0 hηpos,
    deleted_strips Z H _ hηpos, span_retained_le Z H _ hηpos,
    tail_passage Z H (eventually_h7 Z) _ hηpos,
    (Assembly.tendsto_N_atTop Z H.RvM).eventually_ge_atTop
      ((m : ℝ) / min ε₀ (c * ((m : ℝ) - ((n : ℝ) - 1)))),
    eventually_L_pos] with T hblk hstrip hspan h8 hNbig hL

  have h15 := offset_average (xret Z (mtParams T) T) (xret_injective Z (mtParams T) T hL)
    (show 1 ≤ m by omega) (blockDefect (gram_isHermitian Z (mtParams T) T))
    (Dcirc Z (mtParams T) T)
    (c * ((m : ℝ) - ((n : ℝ) - 1)) - min ε₀ (c * ((m : ℝ) - ((n : ℝ) - 1))))
    (((n : ℝ) - 1) / (p : ℝ))
    hA' hq0 (blockDefect_nonneg _) (fun B hB _ => hblk B hB)
    (fun κ _ _ β => pinching_partition (gram_isHermitian Z (mtParams T) T) κ β)
  rw [Fintype.card_coe] at h15
  have hN0 : (0 : ℝ) ≤ (Z.N T (2 * T) : ℝ) := Nat.cast_nonneg _
  have hn0N : (Z.N0s T (2 * T) : ℝ) ≤ (Z.N T (2 * T) : ℝ) := by
    have h := (Z.trivial_chain T (2 * T)).1.trans
      ((Z.trivial_chain T (2 * T)).2.1.trans (Z.trivial_chain T (2 * T)).2.2.1)
    exact_mod_cast h
  have hmN : (m : ℝ) ≤ min ε₀ (c * ((m : ℝ) - ((n : ℝ) - 1))) * (Z.N T (2 * T) : ℝ) := by
    have := (div_le_iff₀ hηpos).mp hNbig; linarith

  set A₀ : ℝ := c * ((m : ℝ) - ((n : ℝ) - 1)) with hA₀
  set q : ℝ := ((n : ℝ) - 1) / (p : ℝ) with hq
  set η : ℝ := min ε₀ A₀ with hη
  set N : ℝ := (Z.N T (2 * T) : ℝ) with hNdef
  set n0 : ℝ := (Z.N0s T (2 * T) : ℝ) with hn0def
  set S : ℝ := ((retained Z (mtParams T) T).card : ℝ) with hSdef
  set D : ℝ := Dcirc Z (mtParams T) T with hDdef
  set sp : ℝ := spanOf (xret Z (mtParams T) T) univ with hspdef
  clear_value A₀ q η N n0 S D sp

  have step1 : (A₀ - η) * (n0 - 2 * η * N) ≤ (A₀ - η) * (S - m) :=
    mul_le_mul_of_nonneg_left (by linarith) hA'
  have step2 : q * ((m : ℝ) - 1) * sp ≤ q * ((m : ℝ) - 1) * ((1 + η) * N) :=
    mul_le_mul_of_nonneg_left hspan (mul_nonneg hq0 (by linarith))
  have hηN : 0 ≤ η * N := mul_nonneg hηpos.le hN0
  have e1 : A₀ * (η * N) ≤ 1 * (η * N) := mul_le_mul_of_nonneg_right hA0 hηN
  have e2 : η * n0 ≤ η * N := mul_le_mul_of_nonneg_left hn0N hηpos.le
  have e3 : 0 ≤ η * η * N := mul_nonneg (mul_nonneg hηpos.le hηpos.le) hN0
  have step3 : A₀ * n0 - 3 * η * N ≤ (A₀ - η) * (n0 - 2 * η * N) := by linarith [e1, e2, e3]
  have hmD : (m : ℝ) * D ≤ m * (n0 - (HD 1 - η) * N) :=
    mul_le_mul_of_nonneg_left (by linarith) hmpos.le
  have hq' : q * ((m : ℝ) - 1) ≤ ((n : ℝ) - 1) * ((m : ℝ) - 1) :=
    mul_le_mul_of_nonneg_right hqn (by linarith)
  have hcoef1 : η * ((m : ℝ) + 3 + q * ((m : ℝ) - 1)) ≤ η * Cn :=
    mul_le_mul_of_nonneg_left (by rw [hCn]; linarith) hηpos.le
  have hcoef2 : η * Cn ≤ ε₀ * Cn := mul_le_mul_of_nonneg_right hηε hCnpos.le
  have hεCn : ε₀ * Cn = ε * (m : ℝ) := by
    rw [hε₀, div_mul_eq_mul_div, mul_div_assoc, div_self hCne, mul_one]
  have hcoef : η * ((m : ℝ) + 3 + q * ((m : ℝ) - 1)) ≤ m * ε := by
    linarith [hcoef1, hcoef2, hεCn]
  have hηN' : η * ((m : ℝ) + 3 + q * ((m : ℝ) - 1)) * N ≤ m * ε * N :=
    mul_le_mul_of_nonneg_right hcoef hN0
  have key : ((m : ℝ) * HD 1 - q * ((m : ℝ) - 1) - m * ε) * N ≤ ((m : ℝ) - A₀) * n0 := by
    linarith [h15, step1, step2, step3, hmD, hηN']
  have hL1 : (HD 1 - ((n : ℝ) - 1) * ((m : ℝ) - 1) / ((p : ℝ) * m) - ε) * N
      = ((m : ℝ) * HD 1 - q * ((m : ℝ) - 1) - m * ε) * N / m := by
    rw [hq]; field_simp
  have hR1 : (1 - A₀ / m) * n0 = ((m : ℝ) - A₀) * n0 / m := by
    field_simp
  rw [hL1, hR1]
  exact div_le_div_of_nonneg_right key hmpos.le

theorem n_point_bound (n : ℕ) (c : ℝ) (m p : ℕ) (hn : 2 ≤ n) (hm : n ≤ m) (hp : 0 < p)
    (hc : 0 < c)
    (hCert : ∀ g : Fin (n - 1) → ℝ, (∀ i, 0 ≤ g i) → c ≤ F n p g)
    (hA0 : c * ((m : ℝ) - ((n : ℝ) - 1)) ≤ 1) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (Phi_n n c m p - ε) * (Zeta23.Ncount T (2 * T) : ℝ) ≤ Zeta23.N0simple T (2 * T) := by
  have h := solve_linear (N := fun T => (Zeta23.Ncount T (2 * T) : ℝ))
    (N0 := fun T => (Zeta23.N0simple T (2 * T) : ℝ)) hn hm hA0 (by
      have := pre_solve zetaZeroConfig paperInputs_zeta hn hm hp hc hCert hA0
      simpa only [zetaZeroConfig_N, zetaZeroConfig_N0s] using this)
  intro ε hε
  exact eventually_atTop.mp (h ε hε)

theorem seven_point_bound (c : ℝ) (m p : ℕ) (hm : 7 ≤ m) (hp : 0 < p) (hc : 0 < c)
    (hCert : ∀ g : Fin 6 → ℝ, (∀ i, 0 ≤ g i) → c ≤ F6 p g)
    (hA0 : c * ((m : ℝ) - 6) ≤ 1) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (Phi c m p - ε) * (Zeta23.Ncount T (2 * T) : ℝ) ≤ Zeta23.N0simple T (2 * T) := by
  have h7 : ((7 : ℕ) : ℝ) - 1 = 6 := by norm_num
  rw [Phi_eq_Phi_n]
  refine n_point_bound 7 c m p (by norm_num) hm hp hc (fun g hg => ?_) ?_
  · exact le_of_le_of_eq (hCert g hg) (F6_eq p g)
  · rw [h7]; exact hA0

theorem seven_point_bound_paper
    (hCert : ∀ g : Fin 6 → ℝ, (∀ i, 0 ≤ g i) → 19 / 5000 ≤ F6 3000 g) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      ((1345000 * HD 1 - 2680) / 1340003 - ε) * (Zeta23.Ncount T (2 * T) : ℝ) ≤ Zeta23.N0simple T (2 * T) := by
  rw [← Phi_paper]
  exact seven_point_bound (19 / 5000) 269 3000 (by norm_num) (by norm_num) (by norm_num) hCert
    (by norm_num)

lemma eventually_Ncount_pos : ∀ᶠ T in atTop, 0 < (Zeta23.Ncount T (2 * T) : ℝ) := by
  have h := Zeta23.Assembly.tendsto_N_atTop zetaZeroConfig paperInputs_zeta.RvM
  simpa only [zetaZeroConfig_N] using h.eventually_gt_atTop 0

theorem seven_point_bound_lab
    (hCert : ∀ g : Fin 6 → ℝ, (∀ i, 0 ≤ g i) → 34697 / 10000000 ≤ F6 3400 g) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      ((520625000 * HD 1 - 915625) / 518855453 - ε) * (Zeta23.Ncount T (2 * T) : ℝ)
        ≤ Zeta23.N0simple T (2 * T) := by
  rw [← Phi_lab]
  exact seven_point_bound (34697 / 10000000) 294 3400 (by norm_num) (by norm_num) (by norm_num)
    hCert (by norm_num)

theorem seven_point_bound_lab_ratio
    (hCert : ∀ g : Fin 6 → ℝ, (∀ i, 0 ≤ g i) → 34697 / 10000000 ≤ F6 3400 g) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (520625000 * HD 1 - 915625) / 518855453 - ε
        ≤ (Zeta23.N0simple T (2 * T) : ℝ) / (Zeta23.Ncount T (2 * T) : ℝ) := by
  intro ε hε
  obtain ⟨T₁, hT₁⟩ := seven_point_bound_lab hCert ε hε
  obtain ⟨T₂, hT₂⟩ := eventually_atTop.mp eventually_Ncount_pos
  refine ⟨max T₁ T₂, fun T hT => ?_⟩
  have h1 := hT₁ T (le_trans (le_max_left _ _) hT)
  have h2 := hT₂ T (le_trans (le_max_right _ _) hT)
  rw [le_div_iff₀ h2]
  exact h1

theorem eight_point_bound
    (hCert : ∀ g : Fin 7 → ℝ, (∀ i, 0 ≤ g i) → 41763 / 10000000 ≤ F 8 3200 g) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      ((2460000000 * HD 1 - 5359375) / 2450018643 - ε) * (Zeta23.Ncount T (2 * T) : ℝ)
        ≤ Zeta23.N0simple T (2 * T) := by
  rw [← Phi_lab8]
  exact n_point_bound 8 (41763 / 10000000) 246 3200 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) hCert (by norm_num)

theorem eight_point_bound_ratio
    (hCert : ∀ g : Fin 7 → ℝ, (∀ i, 0 ≤ g i) → 41763 / 10000000 ≤ F 8 3200 g) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (2460000000 * HD 1 - 5359375) / 2450018643 - ε
        ≤ (Zeta23.N0simple T (2 * T) : ℝ) / (Zeta23.Ncount T (2 * T) : ℝ) := by
  intro ε hε
  obtain ⟨T₁, hT₁⟩ := eight_point_bound hCert ε hε
  obtain ⟨T₂, hT₂⟩ := eventually_atTop.mp eventually_Ncount_pos
  refine ⟨max T₁ T₂, fun T hT => ?_⟩
  have h1 := hT₁ T (le_trans (le_max_left _ _) hT)
  have h2 := hT₂ T (le_trans (le_max_right _ _) hT)
  rw [le_div_iff₀ h2]
  exact h1


end Zeta23Ext.Bridge

end

/-! ###### source module: Zeta23Ext/BridgeW/DefsW.lean ###### -/



noncomputable section
set_option linter.unusedSectionVars false

open Finset
open scoped BigOperators

namespace Zeta23Ext.BridgeW

open Zeta23Ext.Bridge

structure WCert (n : ℕ) where
  a : Fin n → Fin n → ℝ
  b : Fin (n - 1) → ℝ

variable {n : ℕ}

def Fw (W : WCert n) (g : Fin (n - 1) → ℝ) : ℝ :=
  ∑ r, W.b r * g r
    + ∑ i : Fin n, ∑ j : Fin n,
        if (i : ℕ) < (j : ℕ) then W.a i j * wfun (ptsN n g j - ptsN n g i) else 0

def WCert.B (W : WCert n) : ℝ := ∑ r, W.b r

def WCert.spanMass (W : WCert n) (s : ℕ) : ℝ :=
  ∑ i : Fin n, ∑ j : Fin n,
    if (i : ℕ) < (j : ℕ) ∧ (j : ℕ) - (i : ℕ) = s then W.a i j else 0

structure WCert.Adm (W : WCert n) : Prop where
  a_nonneg : ∀ i j, 0 ≤ W.a i j
  b_nonneg : ∀ r, 0 ≤ W.b r
  capacity : ∀ s : ℕ, W.spanMass s ≤ 2

lemma WCert.B_nonneg {W : WCert n} (hW : W.Adm) : 0 ≤ W.B :=
  sum_nonneg fun r _ => hW.b_nonneg r

def ofFixed (n p : ℕ) : WCert n :=
  ⟨fun i j => 2 / ((n : ℝ) - (((j : ℕ) - (i : ℕ) : ℕ) : ℝ)), fun _ => 1 / (p : ℝ)⟩

theorem Fw_ofFixed (n p : ℕ) (g : Fin (n - 1) → ℝ) : Fw (ofFixed n p) g = F n p g := by
  unfold Fw F ofFixed
  simp only
  rw [← mul_sum]

lemma Fw_windowGaps (W : WCert n) (Y : ℕ → ℝ) (i : ℕ) :
    Fw W (windowGaps n Y i)
      = ∑ r : Fin (n - 1), W.b r * (Y (i + ((r : ℕ) + 1)) - Y (i + r))
        + ∑ a : Fin n, ∑ b : Fin n,
            if (a : ℕ) < (b : ℕ) then W.a a b * wfun (Y (i + b) - Y (i + a)) else 0 := by
  unfold Fw
  have hq : (∑ a : Fin n, ∑ b : Fin n,
        if (a : ℕ) < (b : ℕ) then
          W.a a b * wfun (ptsN n (windowGaps n Y i) b - ptsN n (windowGaps n Y i) a) else 0)
      = ∑ a : Fin n, ∑ b : Fin n,
          if (a : ℕ) < (b : ℕ) then W.a a b * wfun (Y (i + b) - Y (i + a)) else 0 := by
    refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => ?_
    rw [ptsN_windowGaps, ptsN_windowGaps,
      show Y (i + ↑b) - Y i - (Y (i + ↑a) - Y i) = Y (i + ↑b) - Y (i + ↑a) by ring]
  rw [hq]
  rfl

section BlockPressure

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def sortedOn (x : ι → ℝ) (B : Finset ι) : ℕ → ℝ :=
  sortedExt (⇑((B.image x).orderEmbOfFin (rfl : (B.image x).card = (B.image x).card)))

def blkPress (b : Fin (n - 1) → ℝ) (x : ι → ℝ) (B : Finset ι) : ℝ :=
  ∑ r : Fin (n - 1), b r * (sortedOn x B ((B.image x).card - (n - 1) + r) - sortedOn x B r)

end BlockPressure


end Zeta23Ext.BridgeW

end

/-! ###### source module: Zeta23Ext/BridgeW/S11W.lean ###### -/



noncomputable section
set_option linter.unusedSectionVars false

open Finset
open scoped BigOperators

namespace Zeta23Ext.BridgeW

open Zeta23Ext.Bridge

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma window_pairs_le_energy_w {n m : ℕ} (hn : 2 ≤ n) (hm : n ≤ m) (W : WCert n) (hW : W.Adm)
    (x : ι → ℝ) (hx : Function.Injective x) (hS : (univ.image x).card = m) :
    ∑ i ∈ range (m - (n - 1)), ∑ a : Fin n, ∑ b : Fin n,
        (if (a : ℕ) < (b : ℕ) then
          W.a a b * wfun (sortedExt ((univ.image x).orderEmbOfFin hS) (i + b)
                - sortedExt ((univ.image x).orderEmbOfFin hS) (i + a))
        else 0)
      ≤ energyOn x univ := by
  classical
  set y : Fin m → ℝ := ⇑((univ.image x).orderEmbOfFin hS) with hydef
  set Y := sortedExt y with hYdef
  have hm0 : 0 < m := by omega

  set T : Finset (ℕ × (Fin n × Fin n)) :=
    (range (m - (n - 1)) ×ˢ (univ : Finset (Fin n × Fin n))).filter fun t => (t.2.1 : ℕ) < t.2.2
    with hTdef
  set f : ℕ × (Fin n × Fin n) → ℝ := fun t =>
    W.a t.2.1 t.2.2 * wfun (Y (t.1 + t.2.2) - Y (t.1 + t.2.1)) with hfdef
  have hLHS : ∑ i ∈ range (m - (n - 1)), ∑ a : Fin n, ∑ b : Fin n,
      (if (a : ℕ) < (b : ℕ) then
        W.a a b * wfun (Y (i + b) - Y (i + a)) else 0)
      = ∑ t ∈ T, f t := by
    rw [hTdef, sum_filter, sum_product]
    refine sum_congr rfl fun i _ => ?_
    exact (Fintype.sum_prod_type' (f := fun (a b : Fin n) => if (a : ℕ) < (b : ℕ) then
      W.a a b * wfun (Y (i + b) - Y (i + a)) else 0)).symm
  rw [hLHS]

  set φ : ℕ × (Fin n × Fin n) → ℕ × ℕ := fun t => (t.1 + t.2.1, t.1 + t.2.2) with hφdef
  set I := T.image φ with hIdef
  have hmem : ∀ t ∈ T, t.1 < m - (n - 1) ∧ (t.2.1 : ℕ) < t.2.2 := by
    intro t ht
    simp only [hTdef, mem_filter, mem_product, mem_range, mem_univ, and_true] at ht
    exact ht
  have hI : ∀ q ∈ I, q.1 < q.2 ∧ q.2 < m ∧ q.2 - q.1 < n := by
    intro q hq
    obtain ⟨t, ht, rfl⟩ := mem_image.mp hq
    obtain ⟨h1, h2⟩ := hmem t ht
    have hb := t.2.2.2
    simp only [hφdef]
    omega

  rw [← sum_fiberwise_of_maps_to (g := φ) (t := I) (fun t ht => mem_image_of_mem φ ht)]

  have hfib : ∀ q ∈ I, ∑ t ∈ T with φ t = q, f t ≤ 2 * wfun (Y q.2 - Y q.1) := by
    intro q hq
    obtain ⟨hq1, hq2, hq3⟩ := hI q hq
    set r := q.2 - q.1 with hrdef
    have hconst : ∀ t ∈ T.filter (fun t => φ t = q),
        f t = W.a t.2.1 t.2.2 * wfun (Y q.2 - Y q.1) := by
      intro t ht
      rw [mem_filter] at ht
      obtain ⟨ht, hφt⟩ := ht
      have e1 : t.1 + (t.2.1 : ℕ) = q.1 := congrArg Prod.fst hφt
      have e2 : t.1 + (t.2.2 : ℕ) = q.2 := congrArg Prod.snd hφt
      simp only [hfdef]
      rw [e1, e2]
    rw [sum_congr rfl hconst, ← sum_mul]

    set ψ : ℕ × (Fin n × Fin n) → Fin n × Fin n := fun t => t.2 with hψdef
    have hψinj : Set.InjOn ψ (T.filter (fun t => φ t = q)) := by
      intro t ht t' ht' hee
      rw [mem_coe, mem_filter] at ht ht'
      have e1 : t.1 + (t.2.1 : ℕ) = q.1 := congrArg Prod.fst ht.2
      have e1' : t'.1 + (t'.2.1 : ℕ) = q.1 := congrArg Prod.fst ht'.2
      simp only [hψdef] at hee
      have ha : (t.2.1 : ℕ) = t'.2.1 := by rw [hee]
      have hi : t.1 = t'.1 := by omega
      exact Prod.ext hi hee
    have hsub : (T.filter (fun t => φ t = q)).image ψ
        ⊆ (univ ×ˢ univ).filter fun p : Fin n × Fin n =>
            (p.1 : ℕ) < (p.2 : ℕ) ∧ (p.2 : ℕ) - (p.1 : ℕ) = r := by
      intro p hp
      obtain ⟨t, ht, rfl⟩ := mem_image.mp hp
      rw [mem_filter] at ht
      have e1 : t.1 + (t.2.1 : ℕ) = q.1 := congrArg Prod.fst ht.2
      have e2 : t.1 + (t.2.2 : ℕ) = q.2 := congrArg Prod.snd ht.2
      obtain ⟨-, hlt⟩ := hmem t ht.1
      rw [mem_filter, mem_product]
      refine ⟨⟨mem_univ _, mem_univ _⟩, hlt, ?_⟩
      simp only [hψdef]
      omega
    have hmass : ∑ t ∈ T.filter (fun t => φ t = q), W.a t.2.1 t.2.2 ≤ 2 := by
      have h1 : ∑ t ∈ T.filter (fun t => φ t = q), W.a t.2.1 t.2.2
          = ∑ p ∈ (T.filter (fun t => φ t = q)).image ψ, W.a p.1 p.2 := by
        rw [sum_image hψinj]
      have h2 : ∑ p ∈ (T.filter (fun t => φ t = q)).image ψ, W.a p.1 p.2
          ≤ ∑ p ∈ (univ ×ˢ univ).filter (fun p : Fin n × Fin n =>
              (p.1 : ℕ) < (p.2 : ℕ) ∧ (p.2 : ℕ) - (p.1 : ℕ) = r), W.a p.1 p.2 :=
        sum_le_sum_of_subset_of_nonneg hsub fun p _ _ => hW.a_nonneg p.1 p.2
      have h3 : ∑ p ∈ (univ ×ˢ univ).filter (fun p : Fin n × Fin n =>
              (p.1 : ℕ) < (p.2 : ℕ) ∧ (p.2 : ℕ) - (p.1 : ℕ) = r), W.a p.1 p.2
          = W.spanMass r := by
        unfold WCert.spanMass
        rw [sum_filter, sum_product]
      rw [h1]
      exact h2.trans (h3 ▸ hW.capacity r)
    exact mul_le_mul_of_nonneg_right hmass (wfun_nonneg _)
  refine (sum_le_sum hfib).trans ?_

  rw [energyOn_eq_sorted x hx hS, ← hydef]
  set G : Fin m × Fin m → ℝ := fun r => if r.1 = r.2 then 0 else wfun (y r.1 - y r.2) with hGdef
  set toFin : ℕ → Fin m := fun n => if h : n < m then ⟨n, h⟩ else ⟨0, hm0⟩ with htoFin
  have htoFin_lt : ∀ n (h : n < m), toFin n = ⟨n, h⟩ := by
    intro n h; simp only [htoFin, dif_pos h]
  set ψ₁ : ℕ × ℕ → Fin m × Fin m := fun q => (toFin q.1, toFin q.2) with hψ₁
  set ψ₂ : ℕ × ℕ → Fin m × Fin m := fun q => (toFin q.2, toFin q.1) with hψ₂
  have hG1 : ∀ q ∈ I, G (ψ₁ q) = wfun (Y q.2 - Y q.1) := by
    intro q hq
    obtain ⟨hq1, hq2, -⟩ := hI q hq
    have hq1m : q.1 < m := by omega
    simp only [hGdef, hψ₁, htoFin_lt _ hq1m, htoFin_lt _ hq2, hYdef,
      sortedExt_of_lt y hq1m, sortedExt_of_lt y hq2]
    rw [if_neg (by intro h; exact absurd (Fin.mk.inj_iff.mp h) hq1.ne), wfun_sub_comm]
  have hG2 : ∀ q ∈ I, G (ψ₂ q) = wfun (Y q.2 - Y q.1) := by
    intro q hq
    obtain ⟨hq1, hq2, -⟩ := hI q hq
    have hq1m : q.1 < m := by omega
    simp only [hGdef, hψ₂, htoFin_lt _ hq1m, htoFin_lt _ hq2, hYdef,
      sortedExt_of_lt y hq1m, sortedExt_of_lt y hq2]
    rw [if_neg (by intro h; exact absurd (Fin.mk.inj_iff.mp h) hq1.ne')]
  have hsplit : ∑ q ∈ I, 2 * wfun (Y q.2 - Y q.1) = ∑ q ∈ I, G (ψ₁ q) + ∑ q ∈ I, G (ψ₂ q) := by
    rw [← sum_add_distrib]
    refine sum_congr rfl fun q hq => ?_
    rw [hG1 q hq, hG2 q hq]; ring
  have hinj₁ : Set.InjOn ψ₁ I := by
    intro q hq q' hq' h
    obtain ⟨hq1, hq2, -⟩ := hI q hq
    obtain ⟨hq1', hq2', -⟩ := hI q' hq'
    simp only [hψ₁, htoFin_lt _ (by omega : q.1 < m), htoFin_lt _ hq2,
      htoFin_lt _ (by omega : q'.1 < m), htoFin_lt _ hq2', Prod.mk.injEq, Fin.mk.injEq] at h
    exact Prod.ext h.1 h.2
  have hinj₂ : Set.InjOn ψ₂ I := by
    intro q hq q' hq' h
    obtain ⟨hq1, hq2, -⟩ := hI q hq
    obtain ⟨hq1', hq2', -⟩ := hI q' hq'
    simp only [hψ₂, htoFin_lt _ (by omega : q.1 < m), htoFin_lt _ hq2,
      htoFin_lt _ (by omega : q'.1 < m), htoFin_lt _ hq2', Prod.mk.injEq, Fin.mk.injEq] at h
    exact Prod.ext h.2 h.1
  have hdisj : Disjoint (I.image ψ₁) (I.image ψ₂) := by
    rw [disjoint_left]
    intro r hr1 hr2
    obtain ⟨q, hq, rfl⟩ := mem_image.mp hr1
    obtain ⟨q', hq', hqq'⟩ := mem_image.mp hr2
    obtain ⟨hq1, hq2, -⟩ := hI q hq
    obtain ⟨hq1', hq2', -⟩ := hI q' hq'
    simp only [hψ₁, hψ₂, htoFin_lt _ (by omega : q.1 < m), htoFin_lt _ hq2,
      htoFin_lt _ (by omega : q'.1 < m), htoFin_lt _ hq2', Prod.mk.injEq, Fin.mk.injEq] at hqq'
    omega
  have hGnn : ∀ r, 0 ≤ G r := by
    intro r; simp only [hGdef]; split_ifs
    · exact le_rfl
    · exact wfun_nonneg _
  rw [hsplit, ← sum_image hinj₁, ← sum_image hinj₂, ← sum_union hdisj]
  exact sum_le_sum_of_subset_of_nonneg (subset_univ _) fun r _ _ => hGnn r

lemma sum_gap_shift (Y : ℕ → ℝ) (r N : ℕ) :
    ∑ i ∈ range N, (Y (i + (r + 1)) - Y (i + r)) = Y (N + r) - Y r := by
  have h : ∀ i, i + (r + 1) = i + 1 + r := fun i => by omega
  simp_rw [h]
  have := Finset.sum_range_sub (fun i => Y (i + r)) N
  simpa using this

theorem block_energy_w {c : ℝ} {n : ℕ} (hn : 2 ≤ n) (W : WCert n) (hW : W.Adm)
    (hCert : ∀ g : Fin (n - 1) → ℝ, (∀ i, 0 ≤ g i) → c ≤ Fw W g)
    {m : ℕ} (hm : n ≤ m) (hcard : Fintype.card ι = m) (x : ι → ℝ) (hx : Function.Injective x) :
    c * ((m : ℝ) - ((n : ℝ) - 1)) ≤ energyOn x univ + W.B * spanOf x univ := by
  classical

  have hS : (univ.image x).card = m := by
    rw [card_image_of_injective _ hx, card_univ, hcard]
  set y : Fin m → ℝ := ⇑((univ.image x).orderEmbOfFin hS) with hydef
  have hymem : ∀ k, y k ∈ univ.image x := fun k => Finset.orderEmbOfFin_mem _ hS k
  have hymono : StrictMono y := ((univ.image x).orderEmbOfFin hS).strictMono
  set Y := sortedExt y with hYdef
  have hm0 : 0 < m := by omega
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
  have hcastn : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ n)]; norm_num

  have hwin : ∀ i ∈ range (m - (n - 1)), c ≤ Fw W (windowGaps n Y i) := by
    intro i hi
    rw [mem_range] at hi
    apply hCert
    intro j
    have hj := j.2
    have hlt : i + ((j : ℕ) + 1) < m := by omega
    exact sub_nonneg.mpr (sortedExt_mono hymono (by omega) hlt)
  have hsum : c * ((m : ℝ) - ((n : ℝ) - 1))
      ≤ ∑ i ∈ range (m - (n - 1)), Fw W (windowGaps n Y i) := by
    have h := sum_le_sum hwin
    rw [sum_const, card_range, nsmul_eq_mul] at h
    have hcast : ((m - (n - 1) : ℕ) : ℝ) = (m : ℝ) - ((n : ℝ) - 1) := by
      rw [Nat.cast_sub (by omega : n - 1 ≤ m), hcastn]
    rw [hcast] at h
    linarith
  simp_rw [Fw_windowGaps] at hsum
  rw [sum_add_distrib] at hsum

  have hspan : ∀ r : Fin (n - 1), Y (m - (n - 1) + r) - Y r ≤ spanOf x univ := by
    intro r
    have hr := r.2
    have h1 := sortedExt_mono hymono (a := m - (n - 1) + r) (b := m - 1) (by omega) (by omega)
    have h2 := sortedExt_mono hymono (a := 0) (b := r) (by omega) (by omega)
    have hsp : Y (m - 1) - Y 0 ≤ spanOf x univ := by
      obtain ⟨i₀, -, hi₀⟩ := mem_image.mp (hymem ⟨m - 1, by omega⟩)
      obtain ⟨j₀, -, hj₀⟩ := mem_image.mp (hymem ⟨0, hm0⟩)
      rw [hYdef, sortedExt_of_lt y (by omega : m - 1 < m), sortedExt_of_lt y hm0, ← hi₀, ← hj₀]
      exact (le_abs_self _).trans (abs_sub_le_spanOf x (mem_univ i₀) (mem_univ j₀))
    linarith
  have hlin : ∑ i ∈ range (m - (n - 1)), ∑ r : Fin (n - 1), W.b r * (Y (i + ((r : ℕ) + 1)) - Y (i + r))
      ≤ W.B * spanOf x univ := by
    rw [sum_comm]
    unfold WCert.B
    rw [sum_mul]
    refine sum_le_sum fun r _ => ?_
    rw [← mul_sum, sum_gap_shift]
    exact mul_le_mul_of_nonneg_left (hspan r) (hW.b_nonneg r)

  have hquad := window_pairs_le_energy_w hn hm W hW x hx hS
  rw [← hydef, ← hYdef] at hquad
  linarith

lemma sortedOn_eq {x : ι → ℝ} {B : Finset ι} {m : ℕ} (hS : (B.image x).card = m) (k : ℕ) :
    sortedOn x B k = sortedExt (⇑((B.image x).orderEmbOfFin hS)) k := by
  unfold sortedOn sortedExt
  by_cases hk : k < (B.image x).card
  · have hk' : k < m := hS ▸ hk
    rw [dif_pos hk, dif_pos hk']
    set f : Fin (B.image x).card → ℝ := fun j => (B.image x).orderEmbOfFin hS ⟨j, hS ▸ j.2⟩
      with hf
    have hfs : ∀ j, f j ∈ B.image x := fun j => Finset.orderEmbOfFin_mem _ hS _
    have hmono : StrictMono f := by
      intro j j' hj
      exact ((B.image x).orderEmbOfFin hS).strictMono (Fin.mk_lt_mk.mpr (Fin.lt_def.mp hj))
    have := Finset.orderEmbOfFin_unique rfl hfs hmono
    have h2 := congrFun this ⟨k, hk⟩
    simp only [hf] at h2
    rw [← h2]
  · have hk' : ¬ k < m := hS ▸ hk
    rw [dif_neg hk, dif_neg hk']

lemma sortedOn_congr {S S' : Finset ℝ} (h : S = S') :
    sortedExt (⇑(S.orderEmbOfFin (rfl : S.card = S.card)))
      = sortedExt (⇑(S'.orderEmbOfFin (rfl : S'.card = S'.card))) := by
  subst h; rfl

theorem block_energy_w' {c : ℝ} {n : ℕ} (hn : 2 ≤ n) (W : WCert n) (hW : W.Adm)
    (hCert : ∀ g : Fin (n - 1) → ℝ, (∀ i, 0 ≤ g i) → c ≤ Fw W g)
    {m : ℕ} (hm : n ≤ m) (hcard : Fintype.card ι = m) (x : ι → ℝ) (hx : Function.Injective x) :
    c * ((m : ℝ) - ((n : ℝ) - 1)) ≤ energyOn x univ + blkPress W.b x univ := by
  classical
  have hS : (univ.image x).card = m := by
    rw [card_image_of_injective _ hx, card_univ, hcard]
  set y : Fin m → ℝ := ⇑((univ.image x).orderEmbOfFin hS) with hydef
  have hymono : StrictMono y := ((univ.image x).orderEmbOfFin hS).strictMono
  set Y := sortedExt y with hYdef
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
  have hcastn : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ n)]; norm_num
  have hwin : ∀ i ∈ range (m - (n - 1)), c ≤ Fw W (windowGaps n Y i) := by
    intro i hi
    rw [mem_range] at hi
    apply hCert
    intro j
    have hj := j.2
    have hlt : i + ((j : ℕ) + 1) < m := by omega
    exact sub_nonneg.mpr (sortedExt_mono hymono (by omega) hlt)
  have hsum : c * ((m : ℝ) - ((n : ℝ) - 1))
      ≤ ∑ i ∈ range (m - (n - 1)), Fw W (windowGaps n Y i) := by
    have h := sum_le_sum hwin
    rw [sum_const, card_range, nsmul_eq_mul] at h
    have hcast : ((m - (n - 1) : ℕ) : ℝ) = (m : ℝ) - ((n : ℝ) - 1) := by
      rw [Nat.cast_sub (by omega : n - 1 ≤ m), hcastn]
    rw [hcast] at h
    linarith
  simp_rw [Fw_windowGaps] at hsum
  rw [sum_add_distrib] at hsum
  have hlin : ∑ i ∈ range (m - (n - 1)), ∑ r : Fin (n - 1), W.b r * (Y (i + ((r : ℕ) + 1)) - Y (i + r))
      = blkPress W.b x univ := by
    rw [sum_comm]
    unfold blkPress
    rw [hS]
    refine sum_congr rfl fun r _ => ?_
    rw [← mul_sum, sum_gap_shift, sortedOn_eq hS, sortedOn_eq hS]
  have hquad := window_pairs_le_energy_w hn hm W hW x hx hS
  rw [← hydef, ← hYdef] at hquad
  linarith

theorem block_energy_blk {c : ℝ} {n : ℕ} (hn : 2 ≤ n) (W : WCert n) (hW : W.Adm)
    (hCert : ∀ g : Fin (n - 1) → ℝ, (∀ i, 0 ≤ g i) → c ≤ Fw W g)
    {m : ℕ} (hm : n ≤ m) (x : ι → ℝ) (B : Finset ι) (hB : B.card = m) (hx : Set.InjOn x B) :
    c * ((m : ℝ) - ((n : ℝ) - 1)) ≤ energyOn x B + blkPress W.b x B := by
  classical
  have hcard : Fintype.card B = m := by simp [hB]
  have hinj : Function.Injective (fun i : B => x i) := by
    intro i j h
    exact Subtype.ext (hx i.2 j.2 h)
  have h := block_energy_w' hn W hW hCert hm hcard (fun i : B => x i) hinj
  rw [energyOn_subtype] at h
  have himg : (univ : Finset B).image (fun i : B => x i) = B.image x := by
    ext t
    simp only [mem_image, mem_univ, true_and]
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨i.1, i.2, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨⟨i, hi⟩, rfl⟩
  have hP : blkPress W.b (fun i : B => x i) univ = blkPress W.b x B := by
    unfold blkPress sortedOn
    rw [sortedOn_congr himg, himg]
  rw [hP] at h
  exact h


end Zeta23Ext.BridgeW

end

/-! ###### source module: Zeta23Ext/BridgeW/S13W.lean ###### -/



noncomputable section
set_option linter.unusedSectionVars false

open Matrix Finset RHLinalg
open scoped ComplexOrder BigOperators

namespace Zeta23Ext.BridgeW

open Zeta23Ext.Bridge

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem block_bound_w {c : ℝ} {n m : ℕ} (hn : 2 ≤ n) (hm : n ≤ m) (W : WCert n) (hW : W.Adm)
    (hCert : ∀ g : Fin (n - 1) → ℝ, (∀ i, 0 ≤ g i) → c ≤ Fw W g)
    (hA0 : c * ((m : ℝ) - ((n : ℝ) - 1)) ≤ 1)
    (x : ι → ℝ) {G : Matrix ι ι ℂ} (hG : G.PosSemidef) (B : Finset ι) (hB : B.card = m)
    (hx : Set.InjOn x B) {δ : ℝ} (hδ : 0 ≤ δ)
    (hclose : ∀ i ∈ B, ∀ j ∈ B, i ≠ j → ‖G i j - (kfun (x i - x j) : ℂ)‖ ≤ δ) :
    c * ((m : ℝ) - ((n : ℝ) - 1)) - 2 * (m : ℝ) ^ 2 * δ
      ≤ blockDefect hG.1 B + W.B * spanOf x B := by
  classical
  have hBnn : 0 ≤ W.B := WCert.B_nonneg hW

  have hS12 : min 1 (offDiagSqOn G B) ≤ blockDefect hG.1 B := by
    have h := block_defect (hG.submatrix (Subtype.val : B → ι))
    rw [offDiagSqOn_submatrix] at h
    exact h

  have hoff : energyOn x B - 2 * (m : ℝ) ^ 2 * δ ≤ offDiagSqOn G B := by
    have hterm : ∀ i ∈ B, ∀ j ∈ B,
        (if i = j then (0 : ℝ) else wfun (x i - x j)) - 2 * δ
          ≤ (if i = j then 0 else ‖G i j‖ ^ 2) := by
      intro i hi j hj
      split_ifs with hij
      · linarith
      · exact wfun_sub_le_norm_sq (hclose i hi j hj hij)
    have hsum : ∑ i ∈ B, ∑ j ∈ B, ((if i = j then (0 : ℝ) else wfun (x i - x j)) - 2 * δ)
        ≤ offDiagSqOn G B :=
      sum_le_sum fun i hi => sum_le_sum fun j hj => hterm i hi j hj
    have hsplit : ∑ i ∈ B, ∑ j ∈ B, ((if i = j then (0 : ℝ) else wfun (x i - x j)) - 2 * δ)
        = energyOn x B - 2 * (m : ℝ) ^ 2 * δ := by
      unfold energyOn
      simp only [sum_sub_distrib, sum_const, nsmul_eq_mul, hB]
      ring
    linarith

  have hS11 : c * ((m : ℝ) - ((n : ℝ) - 1)) ≤ energyOn x B + W.B * spanOf x B := by
    have hcard : Fintype.card B = m := by simp [hB]
    have hinj : Function.Injective (fun i : B => x i) := by
      intro i j h
      exact Subtype.ext (hx i.2 j.2 h)
    have h := block_energy_w hn W hW hCert hm hcard (fun i : B => x i) hinj
    rw [energyOn_subtype] at h
    have := mul_le_mul_of_nonneg_left (spanOf_subtype_le x B) hBnn
    linarith

  have hspan := spanOf_nonneg x B
  have hm2 : (0 : ℝ) ≤ 2 * (m : ℝ) ^ 2 * δ := by positivity
  rcases le_or_gt 1 (offDiagSqOn G B) with h1 | h1
  · rw [min_eq_left h1] at hS12
    nlinarith [mul_nonneg hBnn hspan]
  · rw [min_eq_right h1.le] at hS12
    nlinarith [mul_nonneg hBnn hspan]

theorem block_bound_w' {c : ℝ} {n m : ℕ} (hn : 2 ≤ n) (hm : n ≤ m) (W : WCert n) (hW : W.Adm)
    (hCert : ∀ g : Fin (n - 1) → ℝ, (∀ i, 0 ≤ g i) → c ≤ Fw W g)
    (hA0 : c * ((m : ℝ) - ((n : ℝ) - 1)) ≤ 1)
    (x : ι → ℝ) {G : Matrix ι ι ℂ} (hG : G.PosSemidef) (B : Finset ι) (hB : B.card = m)
    (hx : Set.InjOn x B) {δ : ℝ} (hδ : 0 ≤ δ)
    (hclose : ∀ i ∈ B, ∀ j ∈ B, i ≠ j → ‖G i j - (kfun (x i - x j) : ℂ)‖ ≤ δ) :
    c * ((m : ℝ) - ((n : ℝ) - 1)) - 2 * (m : ℝ) ^ 2 * δ
      ≤ blockDefect hG.1 B + blkPress W.b x B := by
  classical
  have hS12 : min 1 (offDiagSqOn G B) ≤ blockDefect hG.1 B := by
    have h := block_defect (hG.submatrix (Subtype.val : B → ι))
    rw [offDiagSqOn_submatrix] at h
    exact h
  have hoff : energyOn x B - 2 * (m : ℝ) ^ 2 * δ ≤ offDiagSqOn G B := by
    have hterm : ∀ i ∈ B, ∀ j ∈ B,
        (if i = j then (0 : ℝ) else wfun (x i - x j)) - 2 * δ
          ≤ (if i = j then 0 else ‖G i j‖ ^ 2) := by
      intro i hi j hj
      split_ifs with hij
      · linarith
      · exact wfun_sub_le_norm_sq (hclose i hi j hj hij)
    have hsum : ∑ i ∈ B, ∑ j ∈ B, ((if i = j then (0 : ℝ) else wfun (x i - x j)) - 2 * δ)
        ≤ offDiagSqOn G B :=
      sum_le_sum fun i hi => sum_le_sum fun j hj => hterm i hi j hj
    have hsplit : ∑ i ∈ B, ∑ j ∈ B, ((if i = j then (0 : ℝ) else wfun (x i - x j)) - 2 * δ)
        = energyOn x B - 2 * (m : ℝ) ^ 2 * δ := by
      unfold energyOn
      simp only [sum_sub_distrib, sum_const, nsmul_eq_mul, hB]
      ring
    linarith
  have hS11 := block_energy_blk hn W hW hCert hm x B hB hx
  have hP0 : 0 ≤ blkPress W.b x B := by
    unfold blkPress
    refine sum_nonneg fun r _ => mul_nonneg (hW.b_nonneg r) ?_

    unfold sortedOn
    have hic : (B.image x).card = m := by rw [card_image_of_injOn hx, hB]
    have hr2 := r.2
    have hr : (r : ℕ) < (B.image x).card := by rw [hic]; omega
    have hk : (B.image x).card - (n - 1) + r < (B.image x).card := by rw [hic]; omega
    have hmono := ((B.image x).orderEmbOfFin rfl).strictMono
    rw [sub_nonneg, sortedExt_of_lt _ hk, sortedExt_of_lt _ hr]
    exact hmono.monotone (Fin.mk_le_mk.mpr (by omega))
  have hm2 : (0 : ℝ) ≤ 2 * (m : ℝ) ^ 2 * δ := by positivity
  rcases le_or_gt 1 (offDiagSqOn G B) with h1 | h1
  · rw [min_eq_left h1] at hS12
    nlinarith
  · rw [min_eq_right h1.le] at hS12
    nlinarith


end Zeta23Ext.BridgeW

end

/-! ###### source module: Zeta23Ext/BridgeW/S15W.lean ###### -/



noncomputable section
set_option linter.unusedSectionVars false

open Matrix Finset RHLinalg Filter
open scoped ComplexOrder BigOperators

namespace Zeta23Ext.BridgeW

open Zeta23Ext.Bridge

section Abstract

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem offset_average_w {n : ℕ} (hn : 2 ≤ n) (b : Fin (n - 1) → ℝ) (hb : ∀ r, 0 ≤ b r)
    (x : ι → ℝ) (hx : Function.Injective x) {m : ℕ} (hm : n ≤ m)
    (Dblk : Finset ι → ℝ) (Dtot A : ℝ) (hA : 0 ≤ A)
    (hD0 : ∀ B, 0 ≤ Dblk B)
    (hblock : ∀ B : Finset ι, B.card = m → IsInterval x B → A ≤ Dblk B + blkPress b x B)
    (hpinch : ∀ (κ : Type) [Fintype κ] [DecidableEq κ] (β : ι → κ),
      ∑ b, Dblk (univ.filter fun i => β i = b) ≤ Dtot) :
    A * ((Fintype.card ι : ℝ) - m)
      - (∑ r, b r) * ((m : ℝ) - ((n : ℝ) - 1)) * spanOf x univ ≤ m * Dtot := by
  classical
  set N := Fintype.card ι with hNdef
  set Bt : ℝ := ∑ r, b r with hBt
  have hBt0 : 0 ≤ Bt := sum_nonneg fun r _ => hb r
  have hDtot : 0 ≤ Dtot := by
    have h := hpinch Unit (fun _ => ())
    rw [Fintype.sum_unique] at h
    exact (hD0 _).trans h
  have hspan0 := spanOf_nonneg x (univ : Finset ι)
  have hm0 : 0 < m := by omega
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm0
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
  have hmn' : (n : ℝ) ≤ m := by exact_mod_cast hm
  have hmq0 : (0 : ℝ) ≤ (m : ℝ) - ((n : ℝ) - 1) := by linarith

  rcases lt_or_ge N m with hnm | hnm
  · have : (N : ℝ) - m ≤ 0 := by
      have : (N : ℝ) < m := by exact_mod_cast hnm
      linarith
    nlinarith [mul_nonneg hBt0 (mul_nonneg hmq0 hspan0),
      mul_nonneg hA (by linarith : (0:ℝ) ≤ (m : ℝ) - N), mul_nonneg (by positivity : (0:ℝ) ≤ m) hDtot]

  have hS : (univ.image x).card = N := by rw [card_image_of_injective _ hx, card_univ]
  set y : Fin N → ℝ := ⇑((univ.image x).orderEmbOfFin hS) with hydef
  have hymem : ∀ k, y k ∈ univ.image x := fun k => Finset.orderEmbOfFin_mem _ hS k
  have hymono : StrictMono y := ((univ.image x).orderEmbOfFin hS).strictMono
  choose ι' hι' using fun k => mem_image.mp (hymem k)
  have hι'inj : Function.Injective ι' := by
    intro k k' h
    apply hymono.injective
    rw [← (hι' k).2, ← (hι' k').2, h]
  have hbij : Function.Bijective ι' :=
    (Fintype.bijective_iff_injective_and_card ι').mpr ⟨hι'inj, by simp [hNdef]⟩
  set e : Fin N ≃ ι := Equiv.ofBijective ι' hbij with hedef
  set pos : ι → ℕ := fun i => (e.symm i : ℕ) with hposdef
  set Y := sortedExt y with hYdef
  have hpos_lt : ∀ i, pos i < N := fun i => (e.symm i).2
  have hxY : ∀ i, x i = Y (pos i) := by
    intro i
    rw [hYdef, hposdef]; simp only
    rw [sortedExt_of_lt y (e.symm i).2, Fin.eta, ← (hι' (e.symm i)).2]
    congr 1
    exact (Equiv.ofBijective_apply_symm_apply ι' hbij i).symm
  have hpos_inj : Function.Injective pos := by
    intro i i' h
    have : e.symm i = e.symm i' := Fin.ext h
    exact e.symm.injective this
  have hle_iff : ∀ i i', x i ≤ x i' ↔ pos i ≤ pos i' := by
    intro i i'
    rw [hxY, hxY, hYdef, hposdef]; simp only
    rw [sortedExt_of_lt y (e.symm i).2, sortedExt_of_lt y (e.symm i').2, Fin.eta, Fin.eta,
      hymono.le_iff_le, Fin.le_def]
  have hYlt : ∀ a b, a < b → b < N → Y a < Y b := by
    intro a b hab hb
    rw [hYdef, sortedExt_of_lt y (lt_trans hab hb), sortedExt_of_lt y hb]
    exact hymono (Fin.mk_lt_mk.mpr hab)

  set B : ℕ → Finset ι := fun s => univ.filter fun i => s ≤ pos i ∧ pos i < s + m with hBdef
  have hmemB : ∀ s i, i ∈ B s ↔ s ≤ pos i ∧ pos i < s + m := by
    intro s i; simp [hBdef]
  set toFin : ℕ → Fin N := fun t => if h : t < N then ⟨t, h⟩ else ⟨0, by omega⟩ with htoFin
  have hcardB : ∀ s, s + m ≤ N → (B s).card = m := by
    intro s hs
    have : (B s).card = (Ico s (s + m)).card := by
      refine card_nbij' pos (fun t => e (toFin t)) ?_ ?_ ?_ ?_
      · intro i hi
        rw [mem_coe, hmemB] at hi
        rw [mem_coe, mem_Ico]; exact hi
      · intro t ht
        rw [mem_coe, mem_Ico] at ht
        rw [mem_coe, hmemB]
        have htn : t < N := by omega
        simp only [hposdef, htoFin, dif_pos htn, Equiv.symm_apply_apply]
        exact ht
      · intro i hi
        have h := hpos_lt i
        simp only [htoFin, dif_pos h]
        simp only [hposdef, Fin.eta, Equiv.apply_symm_apply]
      · intro t ht
        rw [mem_coe, mem_Ico] at ht
        have htn : t < N := by omega
        simp only [hposdef, htoFin, dif_pos htn, Equiv.symm_apply_apply]
    rw [this, Nat.card_Ico]; omega
  have hintB : ∀ s, IsInterval x (B s) := by
    intro s i hi j hj k hik hkj
    rw [hmemB] at hi hj ⊢
    rw [hle_iff] at hik hkj
    omega

  have hsortB : ∀ s, s + m ≤ N → ∀ k, k < m → sortedOn x (B s) k = Y (s + k) := by
    intro s hs k hk
    have hxinj : Set.InjOn x (B s) := hx.injOn
    have hic : ((B s).image x).card = m := by rw [card_image_of_injOn hxinj, hcardB s hs]
    rw [sortedOn_eq hic, sortedExt_of_lt _ hk]
    set f : Fin m → ℝ := fun j => Y (s + j) with hf
    have hfs : ∀ j, f j ∈ (B s).image x := by
      intro j
      have hj : s + (j : ℕ) < N := by have := j.2; omega
      refine mem_image.mpr ⟨e ⟨s + j, hj⟩, ?_, ?_⟩
      · rw [hmemB, hposdef]
        simp only [Equiv.symm_apply_apply]
        have := j.2
        constructor <;> omega
      · rw [hxY, hposdef]
        simp only [hf, Equiv.symm_apply_apply]
    have hmono : StrictMono f := by
      intro j j' hj
      simp only [hf]
      have := j'.2
      exact hYlt _ _ (by have := Fin.lt_def.mp hj; omega) (by omega)
    have := Finset.orderEmbOfFin_unique hic hfs hmono
    have h2 := congrFun this ⟨k, hk⟩
    simp only [hf] at h2
    rw [← h2]

  set St := range (N - m + 1) with hStdef
  have hmemSt : ∀ s, s ∈ St ↔ s + m ≤ N := by
    intro s; rw [hStdef, mem_range]; omega
  have hsumblock : A * ((N : ℝ) - m + 1) ≤ ∑ s ∈ St, Dblk (B s) + ∑ s ∈ St, blkPress b x (B s) := by
    have h := sum_le_sum fun s (hs : s ∈ St) =>
      hblock (B s) (hcardB s ((hmemSt s).mp hs)) (hintB s)
    rw [sum_const, card_range, nsmul_eq_mul, sum_add_distrib] at h
    have hcast : ((N - m + 1 : ℕ) : ℝ) = (N : ℝ) - m + 1 := by
      rw [Nat.cast_add, Nat.cast_sub hnm]; norm_num
    rw [hcast] at h
    linarith

  have hpress : ∑ s ∈ St, blkPress b x (B s) ≤ Bt * ((m : ℝ) - ((n : ℝ) - 1)) * spanOf x univ := by
    have hY0 : ∀ r : Fin (n - 1), ∀ i ∈ range (m - (n - 1)),
        Y (N - m + 1 + i + r) - Y (i + r) ≤ spanOf x univ := by
      intro r i hi
      rw [mem_range] at hi
      have hr := r.2
      have hi' : N - m + 1 + i + r < N := by omega
      obtain ⟨a, -, ha⟩ := mem_image.mp (hymem ⟨N - m + 1 + i + r, hi'⟩)
      obtain ⟨c, -, hc⟩ := mem_image.mp (hymem ⟨i + r, by omega⟩)
      rw [hYdef, sortedExt_of_lt y hi', sortedExt_of_lt y (by omega : i + r < N), ← ha, ← hc]
      exact (le_abs_self _).trans (abs_sub_le_spanOf x (mem_univ a) (mem_univ c))
    have hblk : ∀ s ∈ St, blkPress b x (B s)
        = ∑ r : Fin (n - 1), b r * (Y (s + (m - (n - 1) + r)) - Y (s + r)) := by
      intro s hs
      have hs' := (hmemSt s).mp hs
      unfold blkPress
      have hic : ((B s).image x).card = m := by
        rw [card_image_of_injOn hx.injOn, hcardB s hs']
      rw [hic]
      refine sum_congr rfl fun r _ => ?_
      have hr := r.2
      rw [hsortB s hs' _ (by omega), hsortB s hs' _ (by omega)]
    calc ∑ s ∈ St, blkPress b x (B s)
        = ∑ s ∈ St, ∑ r : Fin (n - 1), b r * (Y (s + (m - (n - 1) + r)) - Y (s + r)) :=
          sum_congr rfl hblk
      _ = ∑ r : Fin (n - 1), b r * ∑ s ∈ St, (Y (s + (m - (n - 1)) + r) - Y (s + r)) := by
          rw [sum_comm]
          refine sum_congr rfl fun r _ => ?_
          rw [mul_sum]
          refine sum_congr rfl fun s _ => ?_
          congr 3
          omega
      _ = ∑ r : Fin (n - 1), b r * ∑ i ∈ range (m - (n - 1)), (Y (N - m + 1 + i + r) - Y (i + r)) := by
          refine sum_congr rfl fun r _ => ?_
          congr 1
          have := sum_shift_sub (fun t => Y (t + r)) (m - (n - 1)) (N - m + 1)
          simpa only [hStdef] using this
      _ ≤ ∑ r : Fin (n - 1), b r * ∑ i ∈ range (m - (n - 1)), spanOf x univ := by
          refine sum_le_sum fun r _ => mul_le_mul_of_nonneg_left (sum_le_sum (hY0 r)) (hb r)
      _ = Bt * ((m : ℝ) - ((n : ℝ) - 1)) * spanOf x univ := by
          rw [sum_const, card_range, nsmul_eq_mul, ← sum_mul, ← hBt]
          have hcast : ((m - (n - 1) : ℕ) : ℝ) = (m : ℝ) - ((n : ℝ) - 1) := by
            rw [Nat.cast_sub (by omega : n - 1 ≤ m), Nat.cast_sub (by omega : 1 ≤ n)]; norm_num
          rw [hcast]; ring

  have hdefects : ∑ s ∈ St, Dblk (B s) ≤ m * Dtot := by
    rw [← sum_fiberwise_of_maps_to (g := fun s => s % m) (t := range m)
      (fun s _ => mem_range.mpr (Nat.mod_lt s hm0))]
    calc ∑ j ∈ range m, ∑ s ∈ St with s % m = j, Dblk (B s)
        ≤ ∑ j ∈ range m, Dtot := by
          refine sum_le_sum fun j hj => ?_
          set β : ι → Fin (N + 1) := fun i =>
            ⟨blockStart N m j (pos i), Nat.lt_succ_of_le (blockStart_le N m j (pos i))⟩ with hβ
          have hclass : ∀ s (hs : s + m ≤ N) (hj : s % m = j),
              (univ.filter fun i => β i = ⟨s, by omega⟩) = B s := by
            intro s hs hj
            ext i
            rw [mem_filter, hmemB, hβ]
            simp only [mem_univ, true_and, Fin.mk.injEq]
            exact blockStart_eq_iff hm0 hs hj
          set toFin' : ℕ → Fin (N + 1) := fun s => if h : s < N + 1 then ⟨s, h⟩ else 0 with htoFin'
          have hinj : Set.InjOn toFin' (St.filter (fun s => s % m = j)) := by
            intro s hs s' hs' h
            rw [mem_coe, mem_filter, hmemSt] at hs hs'
            simp only [htoFin', dif_pos (by omega : s < N + 1), dif_pos (by omega : s' < N + 1),
              Fin.mk.injEq] at h
            exact h
          calc ∑ s ∈ St with s % m = j, Dblk (B s)
              = ∑ s ∈ St with s % m = j, Dblk (univ.filter fun i => β i = toFin' s) := by
                refine sum_congr rfl fun s hs => ?_
                rw [mem_filter, hmemSt] at hs
                have hsn : s < N + 1 := by omega
                rw [← hclass s hs.1 hs.2]
                congr 2
                simp only [htoFin', dif_pos hsn]
            _ = ∑ b ∈ (St.filter (fun s => s % m = j)).image toFin',
                  Dblk (univ.filter fun i => β i = b) :=
                (sum_image (f := fun b => Dblk (univ.filter fun i => β i = b)) hinj).symm
            _ ≤ ∑ b, Dblk (univ.filter fun i => β i = b) :=
                sum_le_sum_of_subset_of_nonneg (subset_univ _) fun b _ _ => hD0 _
            _ ≤ Dtot := hpinch (Fin (N + 1)) β
      _ = m * Dtot := by rw [sum_const, card_range, nsmul_eq_mul]

  have hmn : (m : ℝ) ≤ N := by exact_mod_cast hnm
  calc A * ((N : ℝ) - m) - Bt * ((m : ℝ) - ((n : ℝ) - 1)) * spanOf x univ
      ≤ A * ((N : ℝ) - m + 1) - Bt * ((m : ℝ) - ((n : ℝ) - 1)) * spanOf x univ := by linarith
    _ ≤ ∑ s ∈ St, Dblk (B s) + ∑ s ∈ St, blkPress b x (B s)
          - Bt * ((m : ℝ) - ((n : ℝ) - 1)) * spanOf x univ := by linarith
    _ ≤ m * Dtot := by linarith

end Abstract


end Zeta23Ext.BridgeW

end

/-! ###### source module: Zeta23Ext/BridgeW/MainW.lean ###### -/



noncomputable section
set_option linter.unusedSectionVars false

open Matrix Finset RHLinalg Filter
open scoped ComplexOrder BigOperators
open Zeta23 Zeta23.ZeroSide Zeta23.ThmD

namespace Zeta23Ext.BridgeW

open Zeta23Ext.Bridge
open Classical

def Phi_w (n : ℕ) (c : ℝ) (m : ℕ) (B : ℝ) : ℝ :=
  (HD 1 - B * ((m : ℝ) - 1) / m) / (1 - c * ((m : ℝ) - ((n : ℝ) - 1)) / m)

theorem Phi_w_ofFixed (n : ℕ) (c : ℝ) (m p : ℕ) (hn : 1 ≤ n) (hp : 0 < p) :
    Phi_w n c m (ofFixed n p).B = Phi_n n c m p := by
  unfold Phi_w Phi_n WCert.B ofFixed
  simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub hn]; norm_num
  rw [hcast]
  have hp' : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  congr 1
  field_simp

theorem block_bound_eventually_w (Z : ZeroConfig) (H : PaperInputs Z) {c : ℝ} {n m : ℕ}
    (hn : 2 ≤ n) (hm : n ≤ m) (W : WCert n) (hW : W.Adm) (hBpos : 0 < W.B)
    (hCert : ∀ g : Fin (n - 1) → ℝ, (∀ i, 0 ≤ g i) → c ≤ Fw W g)
    (hA0 : c * ((m : ℝ) - ((n : ℝ) - 1)) ≤ 1)
    {η : ℝ} (hη : 0 < η) :
    ∀ᶠ T in atTop, ∀ B : Finset (retained Z (mtParams T) T), B.card = m →
      c * ((m : ℝ) - ((n : ℝ) - 1)) - η ≤ blockDefect (gram_isHermitian Z (mtParams T) T) B
        + W.B * spanOf (xret Z (mtParams T) T) B := by
  have hm' : (2 : ℝ) ≤ m := by exact_mod_cast (by omega : 2 ≤ m)
  have hmsq : 0 < 2 * (m : ℝ) ^ 2 := by positivity
  set δ : ℝ := η / (2 * (m : ℝ) ^ 2) with hδ
  have hδpos : 0 < δ := div_pos hη hmsq
  filter_upwards [kernel_limit Z H (1 / W.B) δ hδpos, eventually_L_pos]
    with T hclose hL
  intro B hB
  set x := xret Z (mtParams T) T with hx
  by_cases hsp : c * ((m : ℝ) - ((n : ℝ) - 1)) ≤ W.B * spanOf x B
  · linarith [blockDefect_nonneg (gram_isHermitian Z (mtParams T) T) B]
  · rw [not_le] at hsp
    have hR : spanOf x B ≤ 1 / W.B := by
      rw [le_div_iff₀ hBpos]; linarith
    have hcl : ∀ i ∈ B, ∀ j ∈ B, i ≠ j →
        ‖gram Z (mtParams T) T i j - (Bridge.kfun (x i - x j) : ℂ)‖ ≤ δ := by
      intro i hi j hj _
      exact hclose i j ((abs_sub_le_spanOf x hi hj).trans hR)
    have h13 := block_bound_w hn hm W hW hCert hA0 x (gram_posSemidef Z (mtParams T) T) B hB
      (xret_injective Z (mtParams T) T hL).injOn hδpos.le hcl
    have hη' : 2 * (m : ℝ) ^ 2 * δ = η := by rw [hδ]; field_simp
    rw [hη'] at h13
    exact h13

theorem pre_solve_w (Z : ZeroConfig) (H : PaperInputs Z) {c : ℝ} {n m : ℕ}
    (hn : 2 ≤ n) (hm : n ≤ m) (W : WCert n) (hW : W.Adm) (hBpos : 0 < W.B) (hc : 0 < c)
    (hCert : ∀ g : Fin (n - 1) → ℝ, (∀ i, 0 ≤ g i) → c ≤ Fw W g)
    (hA0 : c * ((m : ℝ) - ((n : ℝ) - 1)) ≤ 1) :
    ∀ ε > 0, ∀ᶠ T in atTop,
      (HD 1 - W.B * ((m : ℝ) - 1) / m - ε) * (Z.N T (2 * T) : ℝ)
        ≤ (1 - c * ((m : ℝ) - ((n : ℝ) - 1)) / m) * (Z.N0s T (2 * T) : ℝ) := by
  intro ε hε
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hmn : (n : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hm' : (2 : ℝ) ≤ m := le_trans hn' hmn
  have hmpos : (0 : ℝ) < m := by linarith
  have hA₀pos : 0 < c * ((m : ℝ) - ((n : ℝ) - 1)) := mul_pos hc (by linarith)
  have hq0 : (0 : ℝ) ≤ W.B := hBpos.le

  set Cn : ℝ := (m : ℝ) + 3 + W.B * ((m : ℝ) - 1) with hCn
  have hCnpos : 0 < Cn := by
    have h := mul_nonneg hq0 (by linarith : (0 : ℝ) ≤ (m : ℝ) - 1)
    rw [hCn]; linarith
  have hCne : Cn ≠ 0 := hCnpos.ne'
  set ε₀ : ℝ := ε * (m : ℝ) / Cn with hε₀
  have hε₀pos : 0 < ε₀ := by rw [hε₀]; positivity
  have hηpos : 0 < min ε₀ (c * ((m : ℝ) - ((n : ℝ) - 1))) := lt_min hε₀pos hA₀pos
  have hηε : min ε₀ (c * ((m : ℝ) - ((n : ℝ) - 1))) ≤ ε₀ := min_le_left _ _
  have hηA : min ε₀ (c * ((m : ℝ) - ((n : ℝ) - 1))) ≤ c * ((m : ℝ) - ((n : ℝ) - 1)) :=
    min_le_right _ _
  have hA' : 0 ≤ c * ((m : ℝ) - ((n : ℝ) - 1)) - min ε₀ (c * ((m : ℝ) - ((n : ℝ) - 1))) := by
    linarith
  filter_upwards [block_bound_eventually_w Z H hn hm W hW hBpos hCert hA0 hηpos,
    deleted_strips Z H _ hηpos, span_retained_le Z H _ hηpos,
    tail_passage Z H (eventually_h7 Z) _ hηpos,
    (Assembly.tendsto_N_atTop Z H.RvM).eventually_ge_atTop
      ((m : ℝ) / min ε₀ (c * ((m : ℝ) - ((n : ℝ) - 1)))),
    eventually_L_pos] with T hblk hstrip hspan h8 hNbig hL

  have h15 := offset_average (xret Z (mtParams T) T) (xret_injective Z (mtParams T) T hL)
    (show 1 ≤ m by omega) (blockDefect (gram_isHermitian Z (mtParams T) T))
    (Dcirc Z (mtParams T) T)
    (c * ((m : ℝ) - ((n : ℝ) - 1)) - min ε₀ (c * ((m : ℝ) - ((n : ℝ) - 1))))
    W.B
    hA' hq0 (blockDefect_nonneg _) (fun B hB _ => hblk B hB)
    (fun κ _ _ β => pinching_partition (gram_isHermitian Z (mtParams T) T) κ β)
  rw [Fintype.card_coe] at h15
  have hN0 : (0 : ℝ) ≤ (Z.N T (2 * T) : ℝ) := Nat.cast_nonneg _
  have hn0N : (Z.N0s T (2 * T) : ℝ) ≤ (Z.N T (2 * T) : ℝ) := by
    have h := (Z.trivial_chain T (2 * T)).1.trans
      ((Z.trivial_chain T (2 * T)).2.1.trans (Z.trivial_chain T (2 * T)).2.2.1)
    exact_mod_cast h
  have hmN : (m : ℝ) ≤ min ε₀ (c * ((m : ℝ) - ((n : ℝ) - 1))) * (Z.N T (2 * T) : ℝ) := by
    have := (div_le_iff₀ hηpos).mp hNbig; linarith

  set A₀ : ℝ := c * ((m : ℝ) - ((n : ℝ) - 1)) with hA₀
  set q : ℝ := W.B with hq
  set η : ℝ := min ε₀ A₀ with hη
  set N : ℝ := (Z.N T (2 * T) : ℝ) with hNdef
  set n0 : ℝ := (Z.N0s T (2 * T) : ℝ) with hn0def
  set S : ℝ := ((retained Z (mtParams T) T).card : ℝ) with hSdef
  set D : ℝ := Dcirc Z (mtParams T) T with hDdef
  set sp : ℝ := spanOf (xret Z (mtParams T) T) univ with hspdef
  clear_value A₀ q η N n0 S D sp

  have step1 : (A₀ - η) * (n0 - 2 * η * N) ≤ (A₀ - η) * (S - m) :=
    mul_le_mul_of_nonneg_left (by linarith) hA'
  have step2 : q * ((m : ℝ) - 1) * sp ≤ q * ((m : ℝ) - 1) * ((1 + η) * N) :=
    mul_le_mul_of_nonneg_left hspan (mul_nonneg hq0 (by linarith))
  have hηN : 0 ≤ η * N := mul_nonneg hηpos.le hN0
  have e1 : A₀ * (η * N) ≤ 1 * (η * N) := mul_le_mul_of_nonneg_right hA0 hηN
  have e2 : η * n0 ≤ η * N := mul_le_mul_of_nonneg_left hn0N hηpos.le
  have e3 : 0 ≤ η * η * N := mul_nonneg (mul_nonneg hηpos.le hηpos.le) hN0
  have step3 : A₀ * n0 - 3 * η * N ≤ (A₀ - η) * (n0 - 2 * η * N) := by linarith [e1, e2, e3]
  have hmD : (m : ℝ) * D ≤ m * (n0 - (HD 1 - η) * N) :=
    mul_le_mul_of_nonneg_left (by linarith) hmpos.le
  have hcoef1 : η * ((m : ℝ) + 3 + q * ((m : ℝ) - 1)) ≤ η * Cn :=
    mul_le_mul_of_nonneg_left (by rw [hCn]) hηpos.le
  have hcoef2 : η * Cn ≤ ε₀ * Cn := mul_le_mul_of_nonneg_right hηε hCnpos.le
  have hεCn : ε₀ * Cn = ε * (m : ℝ) := by
    rw [hε₀]; field_simp
  have hcoef : η * ((m : ℝ) + 3 + q * ((m : ℝ) - 1)) ≤ m * ε := by
    linarith [hcoef1, hcoef2, hεCn]
  have hηN' : η * ((m : ℝ) + 3 + q * ((m : ℝ) - 1)) * N ≤ m * ε * N :=
    mul_le_mul_of_nonneg_right hcoef hN0
  have key : ((m : ℝ) * HD 1 - q * ((m : ℝ) - 1) - m * ε) * N ≤ ((m : ℝ) - A₀) * n0 := by
    linarith [h15, step1, step2, step3, hmD, hηN']
  have hL1 : (HD 1 - q * ((m : ℝ) - 1) / m - ε) * N
      = ((m : ℝ) * HD 1 - q * ((m : ℝ) - 1) - m * ε) * N / m := by
    field_simp
  have hR1 : (1 - A₀ / m) * n0 = ((m : ℝ) - A₀) * n0 / m := by
    field_simp
  rw [hL1, hR1]
  exact div_le_div_of_nonneg_right key hmpos.le

theorem solve_linear_w {N N0 : ℝ → ℝ} {c : ℝ} {n m : ℕ} (K : ℝ) (hn : 2 ≤ n) (hm : n ≤ m)
    (hA0 : c * ((m : ℝ) - ((n : ℝ) - 1)) ≤ 1)
    (h : ∀ ε > 0, ∀ᶠ T in atTop,
      (K - ε) * N T ≤ (1 - c * ((m : ℝ) - ((n : ℝ) - 1)) / m) * N0 T) :
    ∀ ε > 0, ∀ᶠ T in atTop,
      (K / (1 - c * ((m : ℝ) - ((n : ℝ) - 1)) / m) - ε) * N T ≤ N0 T := by
  intro ε hε
  have hD := one_sub_div_pos hn hm hA0
  set Dn : ℝ := 1 - c * ((m : ℝ) - ((n : ℝ) - 1)) / m with hDn
  filter_upwards [h (ε * Dn) (mul_pos hε hD)] with T hT
  have : K / Dn - ε = (K - ε * Dn) / Dn := by
    field_simp
  rw [this, div_mul_eq_mul_div, div_le_iff₀ hD]
  linarith

theorem n_point_bound_w (n : ℕ) (c : ℝ) (m : ℕ) (W : WCert n) (hn : 2 ≤ n) (hm : n ≤ m)
    (hW : W.Adm) (hBpos : 0 < W.B) (hc : 0 < c)
    (hCert : ∀ g : Fin (n - 1) → ℝ, (∀ i, 0 ≤ g i) → c ≤ Fw W g)
    (hA0 : c * ((m : ℝ) - ((n : ℝ) - 1)) ≤ 1) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (Phi_w n c m W.B - ε) * (Zeta23.Ncount T (2 * T) : ℝ) ≤ Zeta23.N0simple T (2 * T) := by
  have h := solve_linear_w (N := fun T => (Zeta23.Ncount T (2 * T) : ℝ))
    (N0 := fun T => (Zeta23.N0simple T (2 * T) : ℝ)) (HD 1 - W.B * ((m : ℝ) - 1) / m) hn hm hA0 (by
      have := pre_solve_w zetaZeroConfig paperInputs_zeta hn hm W hW hBpos hc hCert hA0
      simpa only [zetaZeroConfig_N, zetaZeroConfig_N0s] using this)
  intro ε hε
  exact eventually_atTop.mp (h ε hε)

def Phi_w' (n : ℕ) (c : ℝ) (m : ℕ) (B : ℝ) : ℝ :=
  (HD 1 - B * ((m : ℝ) - ((n : ℝ) - 1)) / m) / (1 - c * ((m : ℝ) - ((n : ℝ) - 1)) / m)

section SpanPressure

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma spanOf_le_blkPress_div {n m : ℕ} (hn3 : 3 ≤ n) (h2n : 2 * n ≤ m) (b : Fin (n - 1) → ℝ)
    {bmin : ℝ} (hbmin : 0 < bmin) (hb : ∀ r, bmin ≤ b r)
    (x : ι → ℝ) (B : Finset ι) (hB : B.card = m) (hx : Set.InjOn x B) :
    spanOf x B ≤ blkPress b x B / bmin := by
  classical
  have hn : 2 ≤ n := by omega
  have hm0 : 0 < m := by omega
  have hne : B.Nonempty := by rw [← card_pos, hB]; exact hm0
  have hic : (B.image x).card = m := by rw [card_image_of_injOn hx, hB]
  have hine : (B.image x).Nonempty := by rw [← card_pos, hic]; exact hm0
  set S := B.image x with hSdef
  set y : ℕ → ℝ := sortedOn x B with hydef
  have hyk : ∀ k (hk : k < m), y k = S.orderEmbOfFin hic ⟨k, hk⟩ := by
    intro k hk
    rw [hydef, sortedOn_eq hic, sortedExt_of_lt _ hk]
  have hmono : ∀ a c, a ≤ c → c < m → y a ≤ y c := by
    intro a c hac hc
    rw [hyk a (lt_of_le_of_lt hac hc), hyk c hc]
    exact (S.orderEmbOfFin hic).monotone (Fin.mk_le_mk.mpr hac)

  have hspan : spanOf x B ≤ y (m - 1) - y 0 := by
    unfold spanOf
    rw [dif_pos hne]
    have h1 : B.sup' hne x ≤ S.max' hine := by
      apply sup'_le
      intro i hi
      exact le_max' _ _ (mem_image_of_mem x hi)
    have h2 : S.min' hine ≤ B.inf' hne x := by
      apply le_inf'
      intro i hi
      exact min'_le _ _ (mem_image_of_mem x hi)
    have hlast : y (m - 1) = S.max' hine := by
      rw [hyk (m - 1) (by omega)]
      exact Finset.orderEmbOfFin_last hic hm0
    have hzero : y 0 = S.min' hine := by
      rw [hyk 0 hm0]
      exact Finset.orderEmbOfFin_zero hic hm0
    rw [hlast, hzero]
    linarith

  have hq1 : n - 1 - 1 < n - 1 := by omega
  have h0 : 0 < n - 1 := by omega
  set r0 : Fin (n - 1) := ⟨0, h0⟩ with hr0
  set r1 : Fin (n - 1) := ⟨n - 1 - 1, hq1⟩ with hr1
  have hterm : ∀ r : Fin (n - 1), 0 ≤ b r * (y (m - (n - 1) + r) - y r) := by
    intro r
    have hr := r.2
    exact mul_nonneg (hbmin.le.trans (hb r)) (sub_nonneg.mpr (hmono _ _ (by omega) (by omega)))
  have hsum : b r0 * (y (m - (n - 1) + r0) - y r0) + b r1 * (y (m - (n - 1) + r1) - y r1)
      ≤ blkPress b x B := by
    unfold blkPress
    rw [← hydef, hic]
    have hr01 : r0 ≠ r1 := by
      intro h; rw [hr0, hr1] at h
      have := Fin.mk.inj_iff.mp h; omega
    have := Finset.add_le_sum (s := univ) (f := fun r : Fin (n - 1) => b r * (y (m - (n - 1) + r) - y r))
      (fun r _ => hterm r) (mem_univ r0) (mem_univ r1) hr01
    simpa using this
  have hmid : y (m - 1) - y 0 ≤ (y (m - (n - 1) + r0) - y r0) + (y (m - (n - 1) + r1) - y r1) := by
    simp only [hr0, hr1]
    have e1 : m - (n - 1) + 0 = m - (n - 1) := by omega
    have e2 : m - (n - 1) + (n - 1 - 1) = m - 1 := by omega
    rw [e1, e2]
    have := hmono (n - 1 - 1) (m - (n - 1)) (by omega) (by omega)
    linarith
  have hb0 := hb r0
  have hb1 := hb r1
  have hnn0 : 0 ≤ y (m - (n - 1) + r0) - y r0 := by
    have := r0.2; exact sub_nonneg.mpr (hmono _ _ (by omega) (by omega))
  have hnn1 : 0 ≤ y (m - (n - 1) + r1) - y r1 := by
    have := r1.2; exact sub_nonneg.mpr (hmono _ _ (by omega) (by omega))
  rw [le_div_iff₀ hbmin]
  nlinarith [mul_le_mul_of_nonneg_right hb0 hnn0, mul_le_mul_of_nonneg_right hb1 hnn1]

end SpanPressure

theorem block_bound_eventually_w' (Z : ZeroConfig) (H : PaperInputs Z) {c : ℝ} {n m : ℕ}
    (hn3 : 3 ≤ n) (h2n : 2 * n ≤ m) (W : WCert n) (hW : W.Adm)
    {bmin : ℝ} (hbmin : 0 < bmin) (hb : ∀ r, bmin ≤ W.b r)
    (hCert : ∀ g : Fin (n - 1) → ℝ, (∀ i, 0 ≤ g i) → c ≤ Fw W g)
    (hA0 : c * ((m : ℝ) - ((n : ℝ) - 1)) ≤ 1)
    {η : ℝ} (hη : 0 < η) :
    ∀ᶠ T in atTop, ∀ B : Finset (retained Z (mtParams T) T), B.card = m →
      c * ((m : ℝ) - ((n : ℝ) - 1)) - η ≤ blockDefect (gram_isHermitian Z (mtParams T) T) B
        + blkPress W.b (xret Z (mtParams T) T) B := by
  have hn : 2 ≤ n := by omega
  have hm : n ≤ m := by omega
  have hm' : (2 : ℝ) ≤ m := by exact_mod_cast (by omega : 2 ≤ m)
  have hmsq : 0 < 2 * (m : ℝ) ^ 2 := by positivity
  set δ : ℝ := η / (2 * (m : ℝ) ^ 2) with hδ
  have hδpos : 0 < δ := div_pos hη hmsq
  filter_upwards [kernel_limit Z H (1 / bmin) δ hδpos, eventually_L_pos]
    with T hclose hL
  intro B hB
  set x := xret Z (mtParams T) T with hx
  have hinj : Set.InjOn x B := (xret_injective Z (mtParams T) T hL).injOn
  by_cases hsp : spanOf x B ≤ 1 / bmin
  · have hcl : ∀ i ∈ B, ∀ j ∈ B, i ≠ j →
        ‖gram Z (mtParams T) T i j - (Bridge.kfun (x i - x j) : ℂ)‖ ≤ δ := by
      intro i hi j hj _
      exact hclose i j ((abs_sub_le_spanOf x hi hj).trans hsp)
    have h13 := block_bound_w' hn hm W hW hCert hA0 x (gram_posSemidef Z (mtParams T) T) B hB
      hinj hδpos.le hcl
    have hη' : 2 * (m : ℝ) ^ 2 * δ = η := by rw [hδ]; field_simp
    rw [hη'] at h13
    exact h13
  · rw [not_le] at hsp
    have hP := spanOf_le_blkPress_div hn3 h2n W.b hbmin hb x B hB hinj
    have hP1 : 1 < blkPress W.b x B := by
      have := (lt_of_lt_of_le hsp hP)
      rw [lt_div_iff₀ hbmin] at this
      rw [div_mul_cancel₀ _ hbmin.ne'] at this
      exact this
    linarith [blockDefect_nonneg (gram_isHermitian Z (mtParams T) T) B]

theorem pre_solve_w' (Z : ZeroConfig) (H : PaperInputs Z) {c : ℝ} {n m : ℕ}
    (hn3 : 3 ≤ n) (h2n : 2 * n ≤ m) (W : WCert n) (hW : W.Adm)
    {bmin : ℝ} (hbmin : 0 < bmin) (hb : ∀ r, bmin ≤ W.b r) (hc : 0 < c)
    (hCert : ∀ g : Fin (n - 1) → ℝ, (∀ i, 0 ≤ g i) → c ≤ Fw W g)
    (hA0 : c * ((m : ℝ) - ((n : ℝ) - 1)) ≤ 1) :
    ∀ ε > 0, ∀ᶠ T in atTop,
      (HD 1 - W.B * ((m : ℝ) - ((n : ℝ) - 1)) / m - ε) * (Z.N T (2 * T) : ℝ)
        ≤ (1 - c * ((m : ℝ) - ((n : ℝ) - 1)) / m) * (Z.N0s T (2 * T) : ℝ) := by
  intro ε hε
  have hn : 2 ≤ n := by omega
  have hm : n ≤ m := by omega
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hmn : (n : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hm' : (2 : ℝ) ≤ m := le_trans hn' hmn
  have hmpos : (0 : ℝ) < m := by linarith
  have hmq : (1 : ℝ) ≤ (m : ℝ) - ((n : ℝ) - 1) := by linarith
  have hA₀pos : 0 < c * ((m : ℝ) - ((n : ℝ) - 1)) := mul_pos hc (by linarith)
  have hq0 : (0 : ℝ) ≤ W.B := WCert.B_nonneg hW

  set Cn : ℝ := (m : ℝ) + 3 + W.B * ((m : ℝ) - ((n : ℝ) - 1)) with hCn
  have hCnpos : 0 < Cn := by
    have h := mul_nonneg hq0 (by linarith : (0 : ℝ) ≤ (m : ℝ) - ((n : ℝ) - 1))
    rw [hCn]; linarith
  have hCne : Cn ≠ 0 := hCnpos.ne'
  set ε₀ : ℝ := ε * (m : ℝ) / Cn with hε₀
  have hε₀pos : 0 < ε₀ := by rw [hε₀]; positivity
  have hηpos : 0 < min ε₀ (c * ((m : ℝ) - ((n : ℝ) - 1))) := lt_min hε₀pos hA₀pos
  have hηε : min ε₀ (c * ((m : ℝ) - ((n : ℝ) - 1))) ≤ ε₀ := min_le_left _ _
  have hηA : min ε₀ (c * ((m : ℝ) - ((n : ℝ) - 1))) ≤ c * ((m : ℝ) - ((n : ℝ) - 1)) :=
    min_le_right _ _
  have hA' : 0 ≤ c * ((m : ℝ) - ((n : ℝ) - 1)) - min ε₀ (c * ((m : ℝ) - ((n : ℝ) - 1))) := by
    linarith
  filter_upwards [block_bound_eventually_w' Z H hn3 h2n W hW hbmin hb hCert hA0 hηpos,
    deleted_strips Z H _ hηpos, span_retained_le Z H _ hηpos,
    tail_passage Z H (eventually_h7 Z) _ hηpos,
    (Assembly.tendsto_N_atTop Z H.RvM).eventually_ge_atTop
      ((m : ℝ) / min ε₀ (c * ((m : ℝ) - ((n : ℝ) - 1)))),
    eventually_L_pos] with T hblk hstrip hspan h8 hNbig hL

  have h15 := offset_average_w hn W.b hW.b_nonneg (xret Z (mtParams T) T)
    (xret_injective Z (mtParams T) T hL) hm
    (blockDefect (gram_isHermitian Z (mtParams T) T))
    (Dcirc Z (mtParams T) T)
    (c * ((m : ℝ) - ((n : ℝ) - 1)) - min ε₀ (c * ((m : ℝ) - ((n : ℝ) - 1))))
    hA' (blockDefect_nonneg _) (fun B hB _ => hblk B hB)
    (fun κ _ _ β => pinching_partition (gram_isHermitian Z (mtParams T) T) κ β)
  rw [Fintype.card_coe] at h15
  have hBeq : (∑ r, W.b r) = W.B := rfl
  rw [hBeq] at h15
  have hN0 : (0 : ℝ) ≤ (Z.N T (2 * T) : ℝ) := Nat.cast_nonneg _
  have hn0N : (Z.N0s T (2 * T) : ℝ) ≤ (Z.N T (2 * T) : ℝ) := by
    have h := (Z.trivial_chain T (2 * T)).1.trans
      ((Z.trivial_chain T (2 * T)).2.1.trans (Z.trivial_chain T (2 * T)).2.2.1)
    exact_mod_cast h
  have hmN : (m : ℝ) ≤ min ε₀ (c * ((m : ℝ) - ((n : ℝ) - 1))) * (Z.N T (2 * T) : ℝ) := by
    have := (div_le_iff₀ hηpos).mp hNbig; linarith

  set A₀ : ℝ := c * ((m : ℝ) - ((n : ℝ) - 1)) with hA₀
  set q : ℝ := W.B with hq
  set mq : ℝ := (m : ℝ) - ((n : ℝ) - 1) with hmqdef
  set η : ℝ := min ε₀ A₀ with hη
  set N : ℝ := (Z.N T (2 * T) : ℝ) with hNdef
  set n0 : ℝ := (Z.N0s T (2 * T) : ℝ) with hn0def
  set S : ℝ := ((retained Z (mtParams T) T).card : ℝ) with hSdef
  set D : ℝ := Dcirc Z (mtParams T) T with hDdef
  set sp : ℝ := spanOf (xret Z (mtParams T) T) univ with hspdef
  clear_value A₀ q mq η N n0 S D sp

  have step1 : (A₀ - η) * (n0 - 2 * η * N) ≤ (A₀ - η) * (S - m) :=
    mul_le_mul_of_nonneg_left (by linarith) hA'
  have hmq0 : (0 : ℝ) ≤ mq := by linarith
  have step2 : q * mq * sp ≤ q * mq * ((1 + η) * N) :=
    mul_le_mul_of_nonneg_left hspan (mul_nonneg hq0 hmq0)
  have hηN : 0 ≤ η * N := mul_nonneg hηpos.le hN0
  have e1 : A₀ * (η * N) ≤ 1 * (η * N) := mul_le_mul_of_nonneg_right hA0 hηN
  have e2 : η * n0 ≤ η * N := mul_le_mul_of_nonneg_left hn0N hηpos.le
  have e3 : 0 ≤ η * η * N := mul_nonneg (mul_nonneg hηpos.le hηpos.le) hN0
  have step3 : A₀ * n0 - 3 * η * N ≤ (A₀ - η) * (n0 - 2 * η * N) := by linarith [e1, e2, e3]
  have hmD : (m : ℝ) * D ≤ m * (n0 - (HD 1 - η) * N) :=
    mul_le_mul_of_nonneg_left (by linarith) hmpos.le
  have hcoef1 : η * ((m : ℝ) + 3 + q * mq) ≤ η * Cn :=
    mul_le_mul_of_nonneg_left (by rw [hCn]) hηpos.le
  have hcoef2 : η * Cn ≤ ε₀ * Cn := mul_le_mul_of_nonneg_right hηε hCnpos.le
  have hεCn : ε₀ * Cn = ε * (m : ℝ) := by
    rw [hε₀]; field_simp
  have hcoef : η * ((m : ℝ) + 3 + q * mq) ≤ m * ε := by
    linarith [hcoef1, hcoef2, hεCn]
  have hηN' : η * ((m : ℝ) + 3 + q * mq) * N ≤ m * ε * N :=
    mul_le_mul_of_nonneg_right hcoef hN0
  have key : ((m : ℝ) * HD 1 - q * mq - m * ε) * N ≤ ((m : ℝ) - A₀) * n0 := by
    linarith [h15, step1, step2, step3, hmD, hηN']
  have hL1 : (HD 1 - q * mq / m - ε) * N
      = ((m : ℝ) * HD 1 - q * mq - m * ε) * N / m := by
    field_simp
  have hR1 : (1 - A₀ / m) * n0 = ((m : ℝ) - A₀) * n0 / m := by
    field_simp
  rw [hL1, hR1]
  exact div_le_div_of_nonneg_right key hmpos.le

theorem n_point_bound_w' (n : ℕ) (c : ℝ) (m : ℕ) (W : WCert n) (hn3 : 3 ≤ n) (h2n : 2 * n ≤ m)
    (hW : W.Adm) {bmin : ℝ} (hbmin : 0 < bmin) (hb : ∀ r, bmin ≤ W.b r) (hc : 0 < c)
    (hCert : ∀ g : Fin (n - 1) → ℝ, (∀ i, 0 ≤ g i) → c ≤ Fw W g)
    (hA0 : c * ((m : ℝ) - ((n : ℝ) - 1)) ≤ 1) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (Phi_w' n c m W.B - ε) * (Zeta23.Ncount T (2 * T) : ℝ) ≤ Zeta23.N0simple T (2 * T) := by
  have hn : 2 ≤ n := by omega
  have hm : n ≤ m := by omega
  have h := solve_linear_w (N := fun T => (Zeta23.Ncount T (2 * T) : ℝ))
    (N0 := fun T => (Zeta23.N0simple T (2 * T) : ℝ)) (HD 1 - W.B * ((m : ℝ) - ((n : ℝ) - 1)) / m) hn hm hA0
    (by
      have := pre_solve_w' zetaZeroConfig paperInputs_zeta hn3 h2n W hW hbmin hb hc hCert hA0
      simpa only [zetaZeroConfig_N, zetaZeroConfig_N0s] using this)
  intro ε hε
  exact eventually_atTop.mp (h ε hε)


end Zeta23Ext.BridgeW

end

/-! ###### source module: Zeta23Ext/BridgeW/Fixed.lean ###### -/



noncomputable section
set_option linter.unusedSectionVars false

open Finset Filter
open scoped BigOperators
open Zeta23 Zeta23.ThmD

namespace Zeta23Ext.BridgeW

open Zeta23Ext.Bridge

theorem ofFixed_spanMass_le (n p : ℕ) (s : ℕ) : (ofFixed n p).spanMass s ≤ 2 := by
  classical
  set P : Finset (Fin n × Fin n) :=
    (univ ×ˢ univ).filter fun q : Fin n × Fin n => (q.1 : ℕ) < (q.2 : ℕ) ∧ (q.2 : ℕ) - (q.1 : ℕ) = s
    with hP
  have e : (ofFixed n p).spanMass s = ∑ q ∈ P, (2 / ((n : ℝ) - (((q.2 : ℕ) - (q.1 : ℕ) : ℕ) : ℝ))) := by
    unfold WCert.spanMass ofFixed
    rw [hP, sum_filter, sum_product]
  rw [e]
  by_cases hs : 0 < s ∧ s < n
  · obtain ⟨hs0, hsn⟩ := hs
    have hconst : ∀ q ∈ P, (2 / ((n : ℝ) - (((q.2 : ℕ) - (q.1 : ℕ) : ℕ) : ℝ))) = 2 / ((n : ℝ) - (s : ℝ)) := by
      intro q hq
      rw [hP, mem_filter] at hq
      rw [hq.2.2]
    rw [sum_congr rfl hconst, sum_const, nsmul_eq_mul]
    have hcard : P.card ≤ n - s := by
      rw [← card_range (n - s)]
      refine card_le_card_of_injOn (fun q => (q.1 : ℕ)) ?_ ?_
      · intro q hq
        rw [mem_coe, hP, mem_filter] at hq
        have h2 := q.2.2
        simp only [coe_range, Set.mem_Iio]
        omega
      · intro q hq q' hq' h
        rw [mem_coe, hP, mem_filter] at hq hq'
        simp only at h
        have h1 : q.1 = q'.1 := Fin.ext h
        have h2 : q.2 = q'.2 := Fin.ext (by omega)
        exact Prod.ext h1 h2
    have hns : (s : ℝ) < (n : ℝ) := by exact_mod_cast hsn
    have hcardR : (P.card : ℝ) ≤ (n : ℝ) - (s : ℝ) := by
      have := (Nat.cast_le (α := ℝ)).mpr hcard
      rwa [Nat.cast_sub hsn.le] at this
    have hpos : 0 < (n : ℝ) - (s : ℝ) := by linarith
    calc (P.card : ℝ) * (2 / ((n : ℝ) - (s : ℝ)))
        ≤ ((n : ℝ) - (s : ℝ)) * (2 / ((n : ℝ) - (s : ℝ))) :=
          mul_le_mul_of_nonneg_right hcardR (by positivity)
      _ = 2 := by field_simp
  · have hempty : P = ∅ := by
      rw [hP, filter_eq_empty_iff]
      intro q _
      have h2 := q.2.2
      intro hq
      apply hs
      omega
    rw [hempty, sum_empty]
    norm_num

theorem ofFixed_adm (n p : ℕ) : (ofFixed n p).Adm := by
  refine ⟨fun i j => ?_, fun _ => ?_, ofFixed_spanMass_le n p⟩
  · unfold ofFixed
    simp only
    have hj := j.2
    have h1 : (((j : ℕ) - (i : ℕ) : ℕ) : ℝ) ≤ (n : ℝ) - 1 := by
      have h2 : (j : ℕ) - (i : ℕ) ≤ n - 1 := by omega
      have h3 : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega : 1 ≤ n)]; norm_num
      rw [← h3]; exact_mod_cast h2
    apply div_nonneg (by norm_num); linarith
  · unfold ofFixed; simp only; positivity

theorem ofFixed_B (n p : ℕ) (hn : 1 ≤ n) : (ofFixed n p).B = ((n : ℝ) - 1) / (p : ℝ) := by
  unfold WCert.B ofFixed
  simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [Nat.cast_sub hn]
  simp only [Nat.cast_one]
  ring

theorem n_point_bound_fixed' (n : ℕ) (c : ℝ) (m p : ℕ) (hn3 : 3 ≤ n) (h2n : 2 * n ≤ m)
    (hp : 0 < p) (hc : 0 < c)
    (hCert : ∀ g : Fin (n - 1) → ℝ, (∀ i, 0 ≤ g i) → c ≤ F n p g)
    (hA0 : c * ((m : ℝ) - ((n : ℝ) - 1)) ≤ 1) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (Phi_w' n c m (((n : ℝ) - 1) / (p : ℝ)) - ε) * (Zeta23.Ncount T (2 * T) : ℝ)
        ≤ Zeta23.N0simple T (2 * T) := by
  have hn1 : 1 ≤ n := by omega
  rw [← ofFixed_B n p hn1]
  have hp' : (0 : ℝ) < 1 / (p : ℝ) := by positivity
  refine n_point_bound_w' n c m (ofFixed n p) hn3 h2n (ofFixed_adm n p) hp'
    (fun r => le_of_eq rfl) hc (fun g hg => ?_) hA0
  rw [Fw_ofFixed]; exact hCert g hg

theorem eight_point_bound_w'
    (hCert : ∀ g : Fin 7 → ℝ, (∀ i, 0 ≤ g i) → 41763 / 10000000 ≤ F 8 3200 g) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      ((2460000000 * HD 1 - 5228125) / 2450018643 - ε) * (Zeta23.Ncount T (2 * T) : ℝ)
        ≤ Zeta23.N0simple T (2 * T) := by
  have h := n_point_bound_fixed' 8 (41763 / 10000000) 246 3200 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hCert (by norm_num)
  have hPhi : Phi_w' 8 (41763 / 10000000) 246 (((8 : ℕ) - 1 : ℝ) / ((3200 : ℕ) : ℝ))
      = (2460000000 * HD 1 - 5228125) / 2450018643 := by
    unfold Phi_w'
    norm_num
    field_simp
    ring
  rw [hPhi] at h
  exact h

theorem eight_point_bound_w'_ratio
    (hCert : ∀ g : Fin 7 → ℝ, (∀ i, 0 ≤ g i) → 41763 / 10000000 ≤ F 8 3200 g) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (2460000000 * HD 1 - 5228125) / 2450018643 - ε
        ≤ (Zeta23.N0simple T (2 * T) : ℝ) / (Zeta23.Ncount T (2 * T) : ℝ) := by
  intro ε hε
  obtain ⟨T₁, hT₁⟩ := eight_point_bound_w' hCert ε hε
  obtain ⟨T₂, hT₂⟩ := Filter.eventually_atTop.mp eventually_Ncount_pos
  refine ⟨max T₁ T₂, fun T hT => ?_⟩
  have h1 := hT₁ T (le_trans (le_max_left _ _) hT)
  have h2 := hT₂ T (le_trans (le_max_right _ _) hT)
  rw [le_div_iff₀ h2]
  exact h1


end Zeta23Ext.BridgeW

end

/-! ###### source module: ThreePoint/Base.lean ###### -/



noncomputable section
open Real intervalIntegral

namespace Zeta23Ext.Bridge.ThreePoint

def taylorCos (t : ℝ) : ℝ := 1 - t^2/2 + t^4/24 - t^6/720 + t^8/40320 - t^10/3628800

def taylorSin (t : ℝ) : ℝ := t - t^3/6 + t^5/120 - t^7/5040 + t^9/362880 - t^11/39916800

def taylorErr : ℝ := 13/5748019200

theorem cos_sin_taylor12 (θ : ℝ) (hθ : |θ| ≤ 1) :
    |Real.cos θ - (1 - θ^2/2 + θ^4/24 - θ^6/720 + θ^8/40320 - θ^10/3628800)|
        ≤ |θ|^12 * (13/5748019200) ∧
    |Real.sin θ - (θ - θ^3/6 + θ^5/120 - θ^7/5040 + θ^9/362880 - θ^11/39916800)|
        ≤ |θ|^12 * (13/5748019200) := by
  have hx : ‖(θ : ℂ) * Complex.I‖ ≤ 1 := by
    simpa using hθ
  have hb := Complex.exp_bound hx (n := 12) (by norm_num)
  have hnx : ‖(θ : ℂ) * Complex.I‖ = |θ| := by simp
  have hsum : ∑ m ∈ Finset.range 12, ((θ : ℂ) * Complex.I) ^ m / (m.factorial : ℂ)
      = ((1 - θ^2/2 + θ^4/24 - θ^6/720 + θ^8/40320 - θ^10/3628800 : ℝ) : ℂ)
        + ((θ - θ^3/6 + θ^5/120 - θ^7/5040 + θ^9/362880 - θ^11/39916800 : ℝ) : ℂ)
          * Complex.I := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
    apply Complex.ext <;> · simp [pow_succ]; ring
  rw [hsum, hnx] at hb
  have hE : ‖Complex.exp ((θ : ℂ) * Complex.I)
      - (((1 - θ^2/2 + θ^4/24 - θ^6/720 + θ^8/40320 - θ^10/3628800 : ℝ) : ℂ)
        + ((θ - θ^3/6 + θ^5/120 - θ^7/5040 + θ^9/362880 - θ^11/39916800 : ℝ) : ℂ)
          * Complex.I)‖ ≤ |θ|^12 * (13/5748019200) := by
    refine hb.trans (le_of_eq ?_)
    norm_num
  constructor
  · have := Complex.abs_re_le_norm (Complex.exp ((θ : ℂ) * Complex.I)
      - (((1 - θ^2/2 + θ^4/24 - θ^6/720 + θ^8/40320 - θ^10/3628800 : ℝ) : ℂ)
        + ((θ - θ^3/6 + θ^5/120 - θ^7/5040 + θ^9/362880 - θ^11/39916800 : ℝ) : ℂ)
          * Complex.I))
    refine le_trans (le_of_eq ?_) (this.trans hE)
    simp [Complex.exp_ofReal_mul_I_re, - Complex.ofReal_pow]
  · have := Complex.abs_im_le_norm (Complex.exp ((θ : ℂ) * Complex.I)
      - (((1 - θ^2/2 + θ^4/24 - θ^6/720 + θ^8/40320 - θ^10/3628800 : ℝ) : ℂ)
        + ((θ - θ^3/6 + θ^5/120 - θ^7/5040 + θ^9/362880 - θ^11/39916800 : ℝ) : ℂ)
          * Complex.I))
    refine le_trans (le_of_eq ?_) (this.trans hE)
    simp [Complex.exp_ofReal_mul_I_im, - Complex.ofReal_pow]

private lemma one_le_pi : (1 : ℝ) ≤ Real.pi := by linarith [Real.pi_gt_three]

private lemma err_scale {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    |t| ^ 12 * (13 / 5748019200) ≤ taylorErr := by
  rw [abs_of_nonneg h0]
  have : t ^ 12 ≤ 1 := pow_le_one₀ h0 h1
  unfold taylorErr; nlinarith

theorem cos_lower {θ u : ℝ} (h0 : 0 ≤ θ) (hu : θ ≤ u) (hu1 : u ≤ 1) :
    taylorCos u - taylorErr ≤ Real.cos θ := by
  have h0u : 0 ≤ u := h0.trans hu
  have hmono : Real.cos u ≤ Real.cos θ :=
    Real.cos_le_cos_of_nonneg_of_le_pi h0 (hu1.trans one_le_pi) hu
  have ht := (cos_sin_taylor12 u (by rw [abs_of_nonneg h0u]; exact hu1)).1
  have he := err_scale h0u hu1
  have := abs_le.mp ht
  unfold taylorCos
  linarith [this.1, this.2]

theorem cos_upper {θ l : ℝ} (h0 : 0 ≤ l) (hl : l ≤ θ) (hθ1 : θ ≤ 1) :
    Real.cos θ ≤ taylorCos l + taylorErr := by
  have hl1 : l ≤ 1 := hl.trans hθ1
  have hmono : Real.cos θ ≤ Real.cos l :=
    Real.cos_le_cos_of_nonneg_of_le_pi h0 (hθ1.trans one_le_pi) hl
  have ht := (cos_sin_taylor12 l (by rw [abs_of_nonneg h0]; exact hl1)).1
  have he := err_scale h0 hl1
  have := abs_le.mp ht
  unfold taylorCos
  linarith [this.1, this.2]

theorem sin_lower {θ l : ℝ} (h0 : 0 ≤ l) (hl : l ≤ θ) (hθ1 : θ ≤ 1) :
    taylorSin l - taylorErr ≤ Real.sin θ := by
  have hl1 : l ≤ 1 := hl.trans hθ1
  have hpi2 : (1 : ℝ) ≤ Real.pi / 2 := by linarith [Real.pi_gt_three]
  have hmono : Real.sin l ≤ Real.sin θ :=
    Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith) (hθ1.trans hpi2) hl
  have ht := (cos_sin_taylor12 l (by rw [abs_of_nonneg h0]; exact hl1)).2
  have he := err_scale h0 hl1
  have := abs_le.mp ht
  unfold taylorSin
  linarith [this.1, this.2]

theorem sin_upper {θ u : ℝ} (h0 : 0 ≤ θ) (hu : θ ≤ u) (hu1 : u ≤ 1) :
    Real.sin θ ≤ taylorSin u + taylorErr := by
  have h0u : 0 ≤ u := h0.trans hu
  have hpi2 : (1 : ℝ) ≤ Real.pi / 2 := by linarith [Real.pi_gt_three]
  have hmono : Real.sin θ ≤ Real.sin u :=
    Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith) (hu1.trans hpi2) hu
  have ht := (cos_sin_taylor12 u (by rw [abs_of_nonneg h0u]; exact hu1)).2
  have he := err_scale h0u hu1
  have := abs_le.mp ht
  unfold taylorSin
  linarith [this.1, this.2]

theorem integral_cos_mul_eq_sinc (c : ℝ) :
    (∫ t in (-(1 : ℝ) / 2)..(1 / 2), Real.cos (c * t)) = Real.sinc (c / 2) := by
  rcases eq_or_ne c 0 with hc | hc
  · subst hc; norm_num
  · have hc2 : c / 2 ≠ 0 := by simpa using hc
    rw [integral_comp_mul_left _ hc, integral_cos, Real.sinc_of_ne_zero hc2,
      show c * ((1:ℝ)/2) = c/2 by ring, show c * (-(1:ℝ)/2) = -(c/2) by ring,
      Real.sin_neg, smul_eq_mul]
    field_simp
    ring

private lemma cos_mul_intervalIntegrable (c a b : ℝ) :
    IntervalIntegrable (fun t => Real.cos (c * t)) MeasureTheory.volume a b :=
  (Real.continuous_cos.comp (continuous_const.mul continuous_id)).intervalIntegrable _ _

theorem Kfun_eq_sinc (x : ℝ) :
    Kfun x =
      (Real.sinc ((Real.sqrt 2 - 2 * Real.pi * x) / 2)
        + Real.sinc ((Real.sqrt 2 + 2 * Real.pi * x) / 2)) / 2 := by
  have key : ∀ t : ℝ, Real.cos (Real.sqrt 2 * t) * Real.cos (2 * Real.pi * x * t)
      = (Real.cos ((Real.sqrt 2 - 2 * Real.pi * x) * t)
          + Real.cos ((Real.sqrt 2 + 2 * Real.pi * x) * t)) / 2 := by
    intro t
    rw [sub_mul, add_mul, Real.cos_sub, Real.cos_add]; ring
  unfold Kfun
  simp_rw [key]
  rw [intervalIntegral.integral_div,
    intervalIntegral.integral_add (cos_mul_intervalIntegrable _ _ _)
      (cos_mul_intervalIntegrable _ _ _),
    integral_cos_mul_eq_sinc, integral_cos_mul_eq_sinc]

def gam : ℝ := (Real.sqrt 2 / 2) * Real.cos (Real.sqrt 2 / 2) / Real.sin (Real.sqrt 2 / 2)

private lemma sqrt2_half_bounds :
    (7071067811865475244/10^19 : ℝ) ≤ Real.sqrt 2 / 2 ∧
      Real.sqrt 2 / 2 ≤ 7071067811865475245/10^19 := by
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hnn : (0:ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  constructor <;> nlinarith [h2, hnn]

private lemma sin_sqrt2_half_pos : 0 < Real.sin (Real.sqrt 2 / 2) := by
  have hb := sqrt2_half_bounds
  refine Real.sin_pos_of_pos_of_lt_pi (by linarith [hb.1]) ?_
  linarith [hb.2, Real.pi_gt_three]

theorem cos_sqrt2_half_bounds :
    (7602445947/10^10 : ℝ) ≤ Real.cos (Real.sqrt 2 / 2) ∧
      Real.cos (Real.sqrt 2 / 2) ≤ 7602445994/10^10 := by
  have hb := sqrt2_half_bounds
  have h0 : (0:ℝ) ≤ Real.sqrt 2 / 2 := by linarith [hb.1]
  constructor
  · have := cos_lower h0 hb.2 (by norm_num)
    have h : (7602445947/10^10 : ℝ)
        ≤ taylorCos (7071067811865475245/10^19) - taylorErr := by
      unfold taylorCos taylorErr; norm_num
    linarith
  · have := cos_upper (by norm_num) hb.1 (by linarith [hb.2])
    have h : taylorCos (7071067811865475244/10^19 : ℝ) + taylorErr
        ≤ 7602445994/10^10 := by
      unfold taylorCos taylorErr; norm_num
    linarith

theorem sin_sqrt2_half_bounds :
    (6496369368/10^10 : ℝ) ≤ Real.sin (Real.sqrt 2 / 2) ∧
      Real.sin (Real.sqrt 2 / 2) ≤ 6496369414/10^10 := by
  have hb := sqrt2_half_bounds
  have h0 : (0:ℝ) ≤ Real.sqrt 2 / 2 := by linarith [hb.1]
  constructor
  · have := sin_lower (by norm_num) hb.1 (by linarith [hb.2])
    have h : (6496369368/10^10 : ℝ)
        ≤ taylorSin (7071067811865475244/10^19) - taylorErr := by
      unfold taylorSin taylorErr; norm_num
    linarith
  · have := sin_upper h0 hb.2 (by norm_num)
    have h : taylorSin (7071067811865475245/10^19 : ℝ) + taylorErr
        ≤ 6496369414/10^10 := by
      unfold taylorSin taylorErr; norm_num
    linarith

theorem gam_bounds : (8274992907/10^10 : ℝ) ≤ gam ∧ gam ≤ 8274993018/10^10 := by
  have hb := sqrt2_half_bounds
  have hc := cos_sqrt2_half_bounds
  have hs := sin_sqrt2_half_bounds
  have h0 : (0:ℝ) ≤ Real.sqrt 2 / 2 := by linarith [hb.1]
  have hspos : (0:ℝ) < Real.sin (Real.sqrt 2 / 2) := by linarith [hs.1]
  have hprodl : (7071067811865475244/10^19 : ℝ) * (7602445947/10^10)
      ≤ (Real.sqrt 2 / 2) * Real.cos (Real.sqrt 2 / 2) :=
    mul_le_mul hb.1 hc.1 (by norm_num) h0
  have hprodu : (Real.sqrt 2 / 2) * Real.cos (Real.sqrt 2 / 2)
      ≤ (7071067811865475245/10^19 : ℝ) * (7602445994/10^10) :=
    mul_le_mul hb.2 hc.2 (by linarith [hc.1]) (by norm_num)
  constructor
  · rw [gam, le_div_iff₀ hspos]; nlinarith [hprodl, hs.2]
  · rw [gam, div_le_iff₀ hspos]; nlinarith [hprodu, hs.1]

private lemma kfun_aux (a b : ℝ) (ha : a ≠ 0) (hsa : Real.sin a ≠ 0)
    (h1 : a - b ≠ 0) (h2 : a + b ≠ 0) :
    ((Real.sin (a - b) / (a - b) + Real.sin (a + b) / (a + b)) / 2) / (Real.sin a / a)
      = (a^2 * Real.cos b - a * b * (Real.cos a / Real.sin a) * Real.sin b) / (a^2 - b^2) := by
  have hab : a^2 - b^2 ≠ 0 := by
    have hfac : a^2 - b^2 = (a - b) * (a + b) := by ring
    rw [hfac]; exact mul_ne_zero h1 h2
  rw [Real.sin_sub, Real.sin_add]
  field_simp
  ring

theorem kfun_closed (x : ℝ) (h : 1 - 2*(Real.pi*x)^2 ≠ 0) :
    kfun x = (Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x))
      / (1 - 2*(Real.pi*x)^2) := by
  have hb := sqrt2_half_bounds
  set a : ℝ := Real.sqrt 2 / 2 with ha_def
  set b : ℝ := Real.pi * x with hb_def
  have ha2 : a^2 = 1/2 := by
    rw [ha_def, div_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]; norm_num
  have ha : a ≠ 0 := by positivity
  have hsa : Real.sin a ≠ 0 := ne_of_gt sin_sqrt2_half_pos
  have h1 : a - b ≠ 0 := by
    intro hz
    apply h
    have : b = a := by linarith [sub_eq_zero.mp hz]
    rw [this]; nlinarith [ha2]
  have h2 : a + b ≠ 0 := by
    intro hz
    apply h
    have : b = -a := by linarith
    rw [this]; nlinarith [ha2]
  have hK : Kfun x = (Real.sin (a - b)/(a - b) + Real.sin (a + b)/(a + b))/2 := by
    rw [Kfun_eq_sinc, show (Real.sqrt 2 - 2*Real.pi*x)/2 = a - b by rw [ha_def, hb_def]; ring,
      show (Real.sqrt 2 + 2*Real.pi*x)/2 = a + b by rw [ha_def, hb_def]; ring,
      Real.sinc_of_ne_zero h1, Real.sinc_of_ne_zero h2]
  have hK0 : Kfun 0 = Real.sin a / a := by
    rw [Kfun_eq_sinc, show (Real.sqrt 2 - 2*Real.pi*0)/2 = a by rw [ha_def]; ring,
      show (Real.sqrt 2 + 2*Real.pi*0)/2 = a by rw [ha_def]; ring,
      Real.sinc_of_ne_zero ha]
    ring
  have hgam : gam = a * (Real.cos a / Real.sin a) := by
    rw [gam, ← ha_def]; field_simp
  have hne1 : (1/2 : ℝ) - b^2 ≠ 0 := by
    intro hz; apply h; linarith
  rw [kfun, hK, hK0, kfun_aux a b ha hsa h1 h2, hgam, ha2,
    div_eq_div_iff hne1 h]
  ring

theorem pi_lo : (3.14159265358979323846 : ℝ) ≤ Real.pi := le_of_lt Real.pi_gt_d20

theorem pi_hi : Real.pi ≤ 3.14159265358979323847 := le_of_lt Real.pi_lt_d20

lemma wfun_nonneg (x : ℝ) : 0 ≤ wfun x := sq_nonneg _

theorem wfun_ge (x nlo dhi : ℝ) (hnlo : 0 ≤ nlo) (hdhi : 0 < dhi)
    (hD0 : 1 < 2*(Real.pi*x)^2) (hD : 2*(Real.pi*x)^2 - 1 ≤ dhi)
    (hN : nlo ≤ |Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x)|) :
    (nlo/dhi)^2 ≤ wfun x := by
  have hne : 1 - 2*(Real.pi*x)^2 ≠ 0 := by intro hz; nlinarith
  have hk : kfun x = (Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x))
      / (1 - 2*(Real.pi*x)^2) := kfun_closed x hne
  have hw : wfun x = kfun x ^ 2 := rfl
  set N : ℝ := Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x) with hN_def
  set Dd : ℝ := 1 - 2*(Real.pi*x)^2 with hD_def
  have hNsq : nlo^2 ≤ N^2 := by
    have := abs_nonneg N
    nlinarith [sq_abs N]
  have h1 : Dd < 0 := by rw [hD_def]; linarith
  have hDsq : Dd^2 ≤ dhi^2 := by nlinarith
  have hDpos : 0 < Dd^2 := by positivity
  rw [hw, hk, div_pow, div_pow, div_le_div_iff₀ (by positivity) hDpos]
  nlinarith [sq_nonneg nlo, sq_nonneg N, hNsq, hDsq, hDpos]

lemma abs_ge_of_le {N nlo : ℝ} (h : nlo ≤ N) : nlo ≤ |N| := h.trans (le_abs_self N)

lemma abs_ge_of_ge {N nlo : ℝ} (h : N ≤ -nlo) : nlo ≤ |N| :=
  le_trans (by linarith) (neg_le_abs N)

lemma cs_h1 : Real.cos (Real.pi*(1/2:ℝ)) = 0 ∧ Real.sin (Real.pi*(1/2:ℝ)) = 1 := by
  constructor <;> · rw [show Real.pi*(1/2:ℝ) = Real.pi/2 by ring]; simp

lemma cs_1 : Real.cos (Real.pi*(1:ℝ)) = -1 ∧ Real.sin (Real.pi*(1:ℝ)) = 0 := by
  constructor <;> · rw [show Real.pi*(1:ℝ) = Real.pi by ring]; simp

lemma cs_h3 : Real.cos (Real.pi*(3/2:ℝ)) = 0 ∧ Real.sin (Real.pi*(3/2:ℝ)) = -1 := by
  constructor <;> · rw [show Real.pi*(3/2:ℝ) = Real.pi/2 + Real.pi by ring]
                    simp [Real.cos_add, Real.sin_add]

lemma cs_2 : Real.cos (Real.pi*(2:ℝ)) = 1 ∧ Real.sin (Real.pi*(2:ℝ)) = 0 := by
  constructor <;> · rw [show Real.pi*(2:ℝ) = 2*Real.pi by ring]; simp

lemma cs_h5 : Real.cos (Real.pi*(5/2:ℝ)) = 0 ∧ Real.sin (Real.pi*(5/2:ℝ)) = 1 := by
  constructor <;> · rw [show Real.pi*(5/2:ℝ) = Real.pi/2 + 2*Real.pi by ring]
                    simp [Real.cos_add, Real.sin_add]

lemma cs_3 : Real.cos (Real.pi*(3:ℝ)) = -1 ∧ Real.sin (Real.pi*(3:ℝ)) = 0 := by
  constructor <;> · rw [show Real.pi*(3:ℝ) = Real.pi + 2*Real.pi by ring]
                    simp [Real.cos_add, Real.sin_add]

lemma cs_h7 : Real.cos (Real.pi*(7/2:ℝ)) = 0 ∧ Real.sin (Real.pi*(7/2:ℝ)) = -1 := by
  constructor <;> · rw [show Real.pi*(7/2:ℝ) = Real.pi/2 + Real.pi + 2*Real.pi by ring]
                    simp [Real.cos_add, Real.sin_add]

lemma cs_4 : Real.cos (Real.pi*(4:ℝ)) = 1 ∧ Real.sin (Real.pi*(4:ℝ)) = 0 := by
  constructor <;> · rw [show Real.pi*(4:ℝ) = 2*Real.pi + 2*Real.pi by ring]
                    simp [Real.cos_add, Real.sin_add]

lemma cs_h9 : Real.cos (Real.pi*(9/2:ℝ)) = 0 ∧ Real.sin (Real.pi*(9/2:ℝ)) = 1 := by
  constructor <;> · rw [show Real.pi*(9/2:ℝ) = Real.pi/2 + 2*Real.pi + 2*Real.pi by ring]
                    simp [Real.cos_add, Real.sin_add]

lemma cos_flip (a x : ℝ) : Real.cos (Real.pi*(x-a)) = Real.cos (Real.pi*(a-x)) := by
  rw [show Real.pi*(x-a) = -(Real.pi*(a-x)) by ring, Real.cos_neg]

lemma sin_flip (a x : ℝ) : Real.sin (Real.pi*(x-a)) = -Real.sin (Real.pi*(a-x)) := by
  rw [show Real.pi*(x-a) = -(Real.pi*(a-x)) by ring, Real.sin_neg]

def taylorSinc (z : ℝ) : ℝ :=
  1 - z^2/6 + z^4/120 - z^6/5040 + z^8/362880 - z^10/39916800

theorem sinc_taylor (z : ℝ) (hz : |z| ≤ 1) : taylorSinc z - taylorErr ≤ Real.sinc z := by
  rcases eq_or_ne z 0 with rfl | hz0
  · norm_num [Real.sinc_zero, taylorSinc, taylorErr]
  · have ht := (cos_sin_taylor12 z hz).2
    have hzpos : 0 < |z| := abs_pos.mpr hz0
    have hpow : |z|^12 * (13/5748019200) ≤ |z| * taylorErr := by
      have h11 : |z|^11 ≤ 1 := pow_le_one₀ (abs_nonneg z) hz
      have hsplit : |z|^12 = |z| * |z|^11 := by ring
      rw [hsplit]
      unfold taylorErr
      nlinarith [abs_nonneg z]
    have key : |Real.sin z - z * taylorSinc z| ≤ |z| * taylorErr := by
      have hpoly : z * taylorSinc z
          = z - z^3/6 + z^5/120 - z^7/5040 + z^9/362880 - z^11/39916800 := by
        unfold taylorSinc; ring
      rw [hpoly]
      exact le_trans ht hpow
    have habs : |(Real.sin z - z * taylorSinc z)/z| ≤ taylorErr := by
      rw [abs_div, div_le_iff₀ hzpos]
      exact le_of_le_of_eq key (mul_comm _ _)
    have hsplit : Real.sin z / z = (Real.sin z - z * taylorSinc z)/z + taylorSinc z := by
      field_simp; ring
    rw [Real.sinc_of_ne_zero hz0, hsplit]
    linarith [(abs_le.mp habs).1]

private lemma sqrt2_bounds : (14142135623/10^10 : ℝ) ≤ Real.sqrt 2 ∧
    Real.sqrt 2 ≤ 14142135624/10^10 := by
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hnn : (0:ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  constructor <;> nlinarith [h2, hnn]

theorem wfun_window (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1/2) : (19/100 : ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  have h2 := sqrt2_bounds
  set A : ℝ := (Real.sqrt 2 - 2*Real.pi*x)/2 with hA
  set B : ℝ := (Real.sqrt 2 + 2*Real.pi*x)/2 with hB
  have hAlo : (-8637/10000 : ℝ) ≤ A := by rw [hA]; nlinarith
  have hAhi : A ≤ 7072/10000 := by rw [hA]; nlinarith
  have hAabs : |A| ≤ 1 := by rw [abs_le]; constructor <;> linarith
  have hA2 : A^2 ≤ 7460/10000 := by nlinarith
  have hsincA : (87557/100000 : ℝ) ≤ Real.sinc A := by
    have h := sinc_taylor A hAabs
    have hq : (87557/100000 : ℝ) ≤ taylorSinc A - taylorErr := by
      unfold taylorSinc taylorErr
      nlinarith [sq_nonneg A, sq_nonneg (A^2), sq_nonneg (A^3), sq_nonneg (A^4),
        sq_nonneg (A^5), hA2, sq_nonneg (A^2 - 7460/10000)]
    linarith
  have hBlo : (7071/10000 : ℝ) < B := by rw [hB]; nlinarith
  have hBhi : B ≤ 22780/10000 := by rw [hB]; nlinarith
  have hsincB : (0:ℝ) ≤ Real.sinc B := by
    rw [Real.sinc_of_ne_zero (by positivity)]
    exact div_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith))
      (by linarith)
  have hK : (43778/100000 : ℝ) ≤ Kfun x := by
    rw [Kfun_eq_sinc, ← hA, ← hB]; linarith
  have hK0 : Kfun 0 = Real.sinc (Real.sqrt 2/2) := by
    rw [Kfun_eq_sinc, show (Real.sqrt 2 - 2*Real.pi*0)/2 = Real.sqrt 2/2 by ring,
      show (Real.sqrt 2 + 2*Real.pi*0)/2 = Real.sqrt 2/2 by ring]
    ring
  have hK0le : Kfun 0 ≤ 1 := by rw [hK0]; exact Real.sinc_le_one _
  have hK0pos : 0 < Kfun 0 := by
    rw [hK0, Real.sinc_of_ne_zero (by positivity)]
    exact div_pos sin_sqrt2_half_pos (by linarith [sqrt2_bounds.1])
  have hk : (43778/100000 : ℝ) ≤ kfun x := by
    rw [kfun, le_div_iff₀ hK0pos]
    nlinarith
  have hw : wfun x = kfun x ^ 2 := rfl
  rw [hw]; nlinarith

lemma trig_shift (a y : ℝ) :
    Real.cos (Real.pi * (a + y)) =
        Real.cos (Real.pi*a) * Real.cos (Real.pi*y) - Real.sin (Real.pi*a) * Real.sin (Real.pi*y)
      ∧ Real.sin (Real.pi * (a + y)) =
        Real.sin (Real.pi*a) * Real.cos (Real.pi*y) + Real.cos (Real.pi*a) * Real.sin (Real.pi*y) := by
  constructor
  · rw [mul_add, Real.cos_add]
  · rw [mul_add, Real.sin_add]

end Zeta23Ext.Bridge.ThreePoint

end

/-! ###### helper lemmas for the cell certificates ###### -/

noncomputable section

namespace Zeta23Ext.Bridge.ThreePoint

/-- Interval product, lower end, for a nonnegative first factor: `P s ≥ P c ≥ min (a c) (b c)`. -/
theorem prod_lo {P s a b c m : ℝ} (ha : 0 ≤ a) (h1 : a ≤ P) (h2 : P ≤ b) (h3 : c ≤ s)
    (k1 : m ≤ a * c) (k3 : m ≤ b * c) : m ≤ P * s := by
  rcases le_total 0 c with hc | hc
  · nlinarith [mul_nonneg (sub_nonneg.2 h1) hc, mul_nonneg (ha.trans h1) (sub_nonneg.2 h3)]
  · nlinarith [mul_nonneg (sub_nonneg.2 h2) (neg_nonneg.2 hc), mul_nonneg (ha.trans h1) (sub_nonneg.2 h3)]

/-- Interval product, upper end, for a nonnegative first factor: `P s ≤ P d ≤ max (a d) (b d)`. -/
theorem prod_hi {P s a b d m : ℝ} (ha : 0 ≤ a) (h1 : a ≤ P) (h2 : P ≤ b) (h4 : s ≤ d)
    (k2 : a * d ≤ m) (k4 : b * d ≤ m) : P * s ≤ m := by
  rcases le_total 0 d with hd | hd
  · nlinarith [mul_nonneg (sub_nonneg.2 h2) hd, mul_nonneg (ha.trans h1) (sub_nonneg.2 h4)]
  · nlinarith [mul_nonneg (sub_nonneg.2 h1) (neg_nonneg.2 hd), mul_nonneg (ha.trans h1) (sub_nonneg.2 h4)]

/-- Product of nonnegative lower bounds. -/
theorem mul_ge_of {P s a c m : ℝ} (h1 : a ≤ P) (h2 : c ≤ s) (ha : 0 ≤ a) (hc : 0 ≤ c)
    (hm : m ≤ a * c) : m ≤ P * s :=
  hm.trans (mul_le_mul h1 h2 hc (ha.trans h1))

/-- Product of upper bounds of nonnegative factors. -/
theorem mul_le_of {P s b d m : ℝ} (h1 : P ≤ b) (h2 : s ≤ d) (hP : 0 ≤ P) (hs : 0 ≤ s)
    (hm : b * d ≤ m) : P * s ≤ m :=
  (mul_le_mul h1 h2 hs (hP.trans h1)).trans hm

end Zeta23Ext.Bridge.ThreePoint

end

/-! ###### verified rational certificate checker (cells, chains, boxes, cover): the four-point instance, kept
for the constants, the anchor table and the trig lemmas that the integer checker below reuses ###### -/

section CheckerDefs

namespace Zeta23Ext.Bridge.ThreePoint

/-! ### Rational mirrors of the enclosure constants -/

/-- Horner forms of the twelve-term Taylor polynomials (fewer rational operations for the kernel). -/
def taylorCosQ (t : ℚ) : ℚ :=
  let s := t * t
  1 + s * (-1/2 + s * (1/24 + s * (-1/720 + s * (1/40320 + s * (-1/3628800)))))
def taylorSinQ (t : ℚ) : ℚ :=
  let s := t * t
  t * (1 + s * (-1/6 + s * (1/120 + s * (-1/5040 + s * (1/362880 + s * (-1/39916800))))))
def errQ : ℚ := 13/5748019200
def piLoQ : ℚ := 314159265358979323846 / 10^20
def piHiQ : ℚ := 314159265358979323847 / 10^20
def gamLoQ : ℚ := 8274992907 / 10^10
def gamHiQ : ℚ := 8274993018 / 10^10

/-- rounding to `10⁻¹²`, downwards and upwards -/
def floorD (x : ℚ) : ℚ := ((⌊x * 1000000000000⌋ : ℤ) : ℚ) / 1000000000000
def ceilD (x : ℚ) : ℚ := ((⌈x * 1000000000000⌉ : ℤ) : ℚ) / 1000000000000

/-- `(cos (π k/2), sin (π k/2))` as integers. -/
def csA : ℕ → ℤ × ℤ
  | 0 => (1, 0)
  | k+1 => (-(csA k).2, (csA k).1)

def imulZ (e : ℤ) (I : ℚ × ℚ) : ℚ × ℚ :=
  if 0 ≤ e then ((e:ℚ) * I.1, (e:ℚ) * I.2) else ((e:ℚ) * I.2, (e:ℚ) * I.1)
def iadd (I J : ℚ × ℚ) : ℚ × ℚ := (I.1 + J.1, I.2 + J.2)
def isub (I J : ℚ × ℚ) : ℚ × ℚ := (I.1 - J.2, I.2 - J.1)

/-- A table cell: the interval `[L, U]`, its anchor `A = k/2`, the side (`true`: `x − A`,
`false`: `A − x`), and the claimed lower bound `W ≤ wfun` on the cell. -/
structure Cell where
  (L U : ℚ) (k : ℕ) (side : Bool) (W : ℚ)

instance : Inhabited Cell := ⟨⟨0, 0, 0, true, 0⟩⟩

namespace Cell
def A (c : Cell) : ℚ := (c.k : ℚ) / 2
def rlo (c : Cell) : ℚ := if c.side then c.L - c.A else c.A - c.U
def rhi (c : Cell) : ℚ := if c.side then c.U - c.A else c.A - c.L
def TL (c : Cell) : ℚ := floorD (piLoQ * c.rlo)
def TU (c : Cell) : ℚ := ceilD (piHiQ * c.rhi)
def CI (c : Cell) : ℚ × ℚ := (floorD (taylorCosQ c.TU - errQ), ceilD (taylorCosQ c.TL + errQ))
def SI (c : Cell) : ℚ × ℚ := (floorD (taylorSinQ c.TL - errQ), ceilD (taylorSinQ c.TU + errQ))
def cA (c : Cell) : ℤ := (csA c.k).1
def sA (c : Cell) : ℤ := (csA c.k).2
def CX (c : Cell) : ℚ × ℚ :=
  if c.side then isub (imulZ c.cA c.CI) (imulZ c.sA c.SI) else iadd (imulZ c.cA c.CI) (imulZ c.sA c.SI)
def SX (c : Cell) : ℚ × ℚ :=
  if c.side then iadd (imulZ c.sA c.CI) (imulZ c.cA c.SI) else isub (imulZ c.sA c.CI) (imulZ c.cA c.SI)
def BL (c : Cell) : ℚ := floorD (piLoQ * c.L)
def BU (c : Cell) : ℚ := ceilD (piHiQ * c.U)
def P2L (c : Cell) : ℚ := floorD (2 * gamLoQ * c.BL)
def P2U (c : Cell) : ℚ := ceilD (2 * gamHiQ * c.BU)
def TLO (c : Cell) : ℚ := floorD (min (c.P2L * c.SX.1) (c.P2U * c.SX.1))
def THI (c : Cell) : ℚ := ceilD (max (c.P2L * c.SX.2) (c.P2U * c.SX.2))
def NLO (c : Cell) : ℚ := max 0 (max (c.CX.1 - c.THI) (c.TLO - c.CX.2))
def DHI (c : Cell) : ℚ := ceilD (2 * c.BU * c.BU - 1)
def Wc (c : Cell) : ℚ := (c.NLO / c.DHI)^2
def ok (c : Cell) : Bool :=
  decide (0 ≤ c.L) && decide (c.L ≤ c.U) && decide (0 ≤ c.rlo) && decide (c.TU ≤ 1)
    && decide (0 ≤ c.TL) && decide (0 ≤ c.BL) && decide (0 ≤ c.P2L)
    && decide (1 < 2 * c.BL * c.BL) && decide (0 < c.DHI) && decide (c.W ≤ c.Wc)
end Cell

/-! ### Chains of cells covering an interval -/

def chainW (cs : List Cell) : List ℕ → ℚ
  | [] => 0
  | i :: rest => if rest.isEmpty then (cs.getD i default).W else min (cs.getD i default).W (chainW cs rest)

def chainCheck (cs : List Cell) : ℚ → ℚ → List ℕ → Bool
  | lo, hi, [] => decide (hi ≤ lo)
  | lo, hi, i :: rest =>
      decide (i < cs.length) && decide ((cs.getD i default).L ≤ lo)
        && chainCheck cs (cs.getD i default).U hi rest

def termW (cs : List Cell) (idxs : List ℕ) : ℚ := if idxs.isEmpty then 0 else chainW cs idxs
def termCheck (cs : List Cell) (lo hi : ℚ) (idxs : List ℕ) : Bool :=
  idxs.isEmpty || chainCheck cs lo hi idxs

/-! ### Boxes and bisection trees for the four-point functional (rational instance; not used by the weighted path) -/

structure Box where
  (xl xu yl yu zl zu : ℚ)
  deriving DecidableEq

inductive Tree
  | leaf (t0 t1 t2 t3 t4 t5 : List ℕ)
  | split (ax : ℕ) (q : ℚ) (lo hi : Tree)

def leafCheck (cs : List Cell) (c p : ℚ) (b : Box) (t0 t1 t2 t3 t4 t5 : List ℕ) : Bool :=
  termCheck cs b.xl b.xu t0 && termCheck cs b.yl b.yu t1 && termCheck cs b.zl b.zu t2
    && termCheck cs (b.xl + b.yl) (b.xu + b.yu) t3 && termCheck cs (b.yl + b.zl) (b.yu + b.zu) t4
    && termCheck cs (b.xl + b.yl + b.zl) (b.xu + b.yu + b.zu) t5
    && decide (c ≤ (b.xl + b.yl + b.zl) / p
        + 2/3 * termW cs t0 + 2/3 * termW cs t1 + 2/3 * termW cs t2
        + termW cs t3 + termW cs t4 + 2 * termW cs t5)

def treeCheck (cs : List Cell) (c p : ℚ) : Box → Tree → Bool
  | b, .leaf t0 t1 t2 t3 t4 t5 => leafCheck cs c p b t0 t1 t2 t3 t4 t5
  | b, .split ax q lo hi =>
      if ax = 0 then treeCheck cs c p {b with xu := q} lo && treeCheck cs c p {b with xl := q} hi
      else if ax = 1 then treeCheck cs c p {b with yu := q} lo && treeCheck cs c p {b with yl := q} hi
      else if ax = 2 then treeCheck cs c p {b with zu := q} lo && treeCheck cs c p {b with zl := q} hi
      else false

/-! ### The one-dimensional cover and the trees over the bad triples -/

/-- segments `(a, b, chain)`, contiguous from `pos`; an empty chain marks a bad segment. -/
def coverCheck (cs : List Cell) (lvl : ℚ) : ℚ → ℚ → List (ℚ × ℚ × List ℕ) → Bool
  | pos, S, [] => decide (S ≤ pos)
  | pos, S, (a, b, ch) :: rest =>
      decide (a = pos) && decide (a ≤ b)
        && (ch.isEmpty || (chainCheck cs a b ch && decide (lvl ≤ chainW cs ch)))
        && coverCheck cs lvl b S rest

def badOf (cover : List (ℚ × ℚ × List ℕ)) : List (ℚ × ℚ) :=
  cover.filterMap fun s => if s.2.2.isEmpty then some (s.1, s.2.1) else none

def boxOf (bad : List (ℚ × ℚ)) (i j k : ℕ) : Box :=
  ⟨(bad.getD i (0, 0)).1, (bad.getD i (0, 0)).2, (bad.getD j (0, 0)).1, (bad.getD j (0, 0)).2,
    (bad.getD k (0, 0)).1, (bad.getD k (0, 0)).2⟩

def treesCheck (cs : List Cell) (c p : ℚ) (bad : List (ℚ × ℚ)) (trees : List Tree) : Bool :=
  let nb := bad.length
  (List.range nb).all fun i => (List.range nb).all fun j => (List.range nb).all fun k =>
    treeCheck cs c p (boxOf bad i j k) (trees.getD (i * nb * nb + j * nb + k) (.leaf [] [] [] [] [] []))

end Zeta23Ext.Bridge.ThreePoint

end CheckerDefs

noncomputable section

open Real

namespace Zeta23Ext.Bridge.ThreePoint

/-! ### Soundness: the constants -/

theorem taylorCosQ_cast (q : ℚ) : taylorCos (q:ℝ) = ((taylorCosQ q : ℚ) : ℝ) := by
  simp only [taylorCos, taylorCosQ]; push_cast; ring

theorem taylorSinQ_cast (q : ℚ) : taylorSin (q:ℝ) = ((taylorSinQ q : ℚ) : ℝ) := by
  simp only [taylorSin, taylorSinQ]; push_cast; ring

theorem errQ_cast : taylorErr = ((errQ : ℚ) : ℝ) := by
  simp only [taylorErr, errQ]; push_cast; ring

theorem floorD_le (x : ℚ) : floorD x ≤ x := by
  unfold floorD
  rw [div_le_iff₀ (by norm_num)]
  exact Int.floor_le _

theorem le_ceilD (x : ℚ) : x ≤ ceilD x := by
  unfold ceilD
  rw [le_div_iff₀ (by norm_num)]
  exact Int.le_ceil _

theorem floorD_le' (x : ℚ) : ((floorD x : ℚ) : ℝ) ≤ (x : ℝ) := Rat.cast_le.mpr (floorD_le x)
theorem le_ceilD' (x : ℚ) : (x : ℝ) ≤ ((ceilD x : ℚ) : ℝ) := Rat.cast_le.mpr (le_ceilD x)

theorem piLoQ_le : ((piLoQ : ℚ) : ℝ) ≤ Real.pi := by
  have h := pi_lo
  simp only [piLoQ]; push_cast
  norm_num at h ⊢
  linarith

theorem piHiQ_ge : Real.pi ≤ ((piHiQ : ℚ) : ℝ) := by
  have h := pi_hi
  simp only [piHiQ]; push_cast
  norm_num at h ⊢
  linarith

theorem piLoQ_nonneg : (0:ℝ) ≤ ((piLoQ : ℚ) : ℝ) := by simp only [piLoQ]; push_cast; norm_num
theorem gamLoQ_le : ((gamLoQ : ℚ) : ℝ) ≤ gam := by
  have h := gam_bounds.1; simp only [gamLoQ]; push_cast; norm_num at h ⊢; linarith
theorem gamHiQ_ge : gam ≤ ((gamHiQ : ℚ) : ℝ) := by
  have h := gam_bounds.2; simp only [gamHiQ]; push_cast; norm_num at h ⊢; linarith
theorem gamLoQ_nonneg : (0:ℝ) ≤ ((gamLoQ : ℚ) : ℝ) := by simp only [gamLoQ]; push_cast; norm_num

theorem cos_sin_half (k : ℕ) :
    Real.cos (Real.pi * ((k:ℝ) / 2)) = ((csA k).1 : ℝ) ∧
      Real.sin (Real.pi * ((k:ℝ) / 2)) = ((csA k).2 : ℝ) := by
  induction k with
  | zero => simp [csA]
  | succ k ih =>
    have e : Real.pi * (((k + 1 : ℕ) : ℝ) / 2) = Real.pi * ((k:ℝ) / 2) + Real.pi / 2 := by
      push_cast; ring
    rw [e, Real.cos_add_pi_div_two, Real.sin_add_pi_div_two, ih.1, ih.2]
    simp [csA]

theorem imulZ_sound (e : ℤ) (I : ℚ × ℚ) {f : ℝ} (h1 : (I.1 : ℝ) ≤ f) (h2 : f ≤ I.2) :
    ((imulZ e I).1 : ℝ) ≤ (e:ℝ) * f ∧ (e:ℝ) * f ≤ ((imulZ e I).2 : ℝ) := by
  unfold imulZ
  split_ifs with he
  · have he' : (0:ℝ) ≤ e := by exact_mod_cast he
    simp only; push_cast
    exact ⟨mul_le_mul_of_nonneg_left h1 he', mul_le_mul_of_nonneg_left h2 he'⟩
  · have he' : (e:ℝ) ≤ 0 := by push_neg at he; exact_mod_cast he.le
    simp only; push_cast
    exact ⟨mul_le_mul_of_nonpos_left h2 he', mul_le_mul_of_nonpos_left h1 he'⟩

theorem iadd_sound (I J : ℚ × ℚ) {f g : ℝ} (hI : (I.1:ℝ) ≤ f ∧ f ≤ I.2) (hJ : (J.1:ℝ) ≤ g ∧ g ≤ J.2) :
    ((iadd I J).1 : ℝ) ≤ f + g ∧ f + g ≤ ((iadd I J).2 : ℝ) := by
  unfold iadd; simp only; push_cast; constructor <;> linarith [hI.1, hI.2, hJ.1, hJ.2]

theorem isub_sound (I J : ℚ × ℚ) {f g : ℝ} (hI : (I.1:ℝ) ≤ f ∧ f ≤ I.2) (hJ : (J.1:ℝ) ≤ g ∧ g ≤ J.2) :
    ((isub I J).1 : ℝ) ≤ f - g ∧ f - g ≤ ((isub I J).2 : ℝ) := by
  unfold isub; simp only; push_cast; constructor <;> linarith [hI.1, hI.2, hJ.1, hJ.2]

/-! ### Soundness: one cell -/

set_option maxHeartbeats 4000000 in
theorem cell_sound (c : Cell) (h : c.ok = true) (x : ℝ) (hx1 : (c.L : ℝ) ≤ x) (hx2 : x ≤ c.U) :
    (c.W : ℝ) ≤ wfun x := by
  simp only [Cell.ok, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨h0, hLU⟩, hr0⟩, hTU⟩, hTL0q⟩, hBL0q⟩, hP2L0q⟩, hB⟩, hD⟩, hW⟩ := h
  have h0' : (0:ℝ) ≤ c.L := Rat.cast_nonneg.mpr h0
  have hr0' : (0:ℝ) ≤ c.rlo := Rat.cast_nonneg.mpr hr0
  have hTL0 : (0:ℝ) ≤ c.TL := Rat.cast_nonneg.mpr hTL0q
  have hBL0 : (0:ℝ) ≤ c.BL := Rat.cast_nonneg.mpr hBL0q
  have hP2L0 : (0:ℝ) ≤ c.P2L := Rat.cast_nonneg.mpr hP2L0q
  have hTU' : (c.TU : ℝ) ≤ 1 := by
    have := (Rat.cast_le (K := ℝ)).mpr hTU; simpa using this
  have hB' : (1:ℝ) < 2 * c.BL * c.BL := by
    have := (Rat.cast_lt (K := ℝ)).mpr hB; push_cast at this; exact this
  have hD' : (0:ℝ) < c.DHI := Rat.cast_pos.mpr hD
  have hW' : (c.W : ℝ) ≤ c.Wc := (Rat.cast_le (K := ℝ)).mpr hW
  -- the reduced offset
  set r : ℝ := if c.side then x - c.A else c.A - x with hr
  have hrlo : (c.rlo : ℝ) ≤ r := by
    simp only [Cell.rlo, hr]; split_ifs <;> push_cast <;> linarith
  have hrhi : r ≤ c.rhi := by
    simp only [Cell.rhi, hr]; split_ifs <;> push_cast <;> linarith
  have hr0r : 0 ≤ r := hr0'.trans hrlo
  have hTL : (c.TL : ℝ) ≤ Real.pi * r := by
    have h1 : (c.TL : ℝ) ≤ ((piLoQ * c.rlo : ℚ) : ℝ) := floorD_le' _
    rw [Rat.cast_mul] at h1
    exact h1.trans (mul_ge_of piLoQ_le hrlo piLoQ_nonneg hr0' le_rfl)
  have hTUr : Real.pi * r ≤ c.TU := by
    have h1 : ((piHiQ * c.rhi : ℚ) : ℝ) ≤ (c.TU : ℝ) := le_ceilD' _
    rw [Rat.cast_mul] at h1
    exact (mul_le_of piHiQ_ge hrhi Real.pi_pos.le hr0r le_rfl).trans h1
  have hθ0 : (0:ℝ) ≤ Real.pi * r := mul_nonneg Real.pi_pos.le hr0r
  have hθ1 : Real.pi * r ≤ 1 := hTUr.trans hTU'
  -- Taylor enclosures of cos (π r), sin (π r)
  have hc1 : ((c.CI).1 : ℝ) ≤ Real.cos (Real.pi * r) := by
    have h := cos_lower hθ0 hTUr hTU'
    rw [taylorCosQ_cast, errQ_cast] at h
    have h1 : ((c.CI).1 : ℝ) ≤ ((taylorCosQ c.TU - errQ : ℚ) : ℝ) := floorD_le' _
    push_cast at h1; exact h1.trans h
  have hc2 : Real.cos (Real.pi * r) ≤ ((c.CI).2 : ℝ) := by
    have h := cos_upper hTL0 hTL hθ1
    rw [taylorCosQ_cast, errQ_cast] at h
    have h1 : ((taylorCosQ c.TL + errQ : ℚ) : ℝ) ≤ ((c.CI).2 : ℝ) := le_ceilD' _
    push_cast at h1; exact h.trans h1
  have hs1 : ((c.SI).1 : ℝ) ≤ Real.sin (Real.pi * r) := by
    have h := sin_lower hTL0 hTL hθ1
    rw [taylorSinQ_cast, errQ_cast] at h
    have h1 : ((c.SI).1 : ℝ) ≤ ((taylorSinQ c.TL - errQ : ℚ) : ℝ) := floorD_le' _
    push_cast at h1; exact h1.trans h
  have hs2 : Real.sin (Real.pi * r) ≤ ((c.SI).2 : ℝ) := by
    have h := sin_upper hθ0 hTUr hTU'
    rw [taylorSinQ_cast, errQ_cast] at h
    have h1 : ((taylorSinQ c.TU + errQ : ℚ) : ℝ) ≤ ((c.SI).2 : ℝ) := le_ceilD' _
    push_cast at h1; exact h.trans h1
  -- the shift to the anchor
  have hcs := cos_sin_half c.k
  have eA : (c.A : ℝ) = (c.k : ℝ) / 2 := by simp [Cell.A]
  have hCX : ((c.CX).1 : ℝ) ≤ Real.cos (Real.pi * x) ∧ Real.cos (Real.pi * x) ≤ ((c.CX).2 : ℝ) := by
    cases hsd : c.side
    · have ex : Real.pi * x = Real.pi * ((c.k:ℝ) / 2) - Real.pi * r := by
        simp only [hr, hsd, Bool.false_eq_true, if_false]; rw [← eA]; ring
      rw [ex, Real.cos_sub, hcs.1, hcs.2]
      simp only [Cell.CX, hsd, Bool.false_eq_true, if_false]
      exact iadd_sound _ _ (imulZ_sound _ _ hc1 hc2) (imulZ_sound _ _ hs1 hs2)
    · have ex : Real.pi * x = Real.pi * ((c.k:ℝ) / 2) + Real.pi * r := by
        simp only [hr, hsd, if_true]; rw [← eA]; ring
      rw [ex, Real.cos_add, hcs.1, hcs.2]
      simp only [Cell.CX, hsd, if_true]
      exact isub_sound _ _ (imulZ_sound _ _ hc1 hc2) (imulZ_sound _ _ hs1 hs2)
  have hSX : ((c.SX).1 : ℝ) ≤ Real.sin (Real.pi * x) ∧ Real.sin (Real.pi * x) ≤ ((c.SX).2 : ℝ) := by
    cases hsd : c.side
    · have ex : Real.pi * x = Real.pi * ((c.k:ℝ) / 2) - Real.pi * r := by
        simp only [hr, hsd, Bool.false_eq_true, if_false]; rw [← eA]; ring
      rw [ex, Real.sin_sub, hcs.1, hcs.2]
      simp only [Cell.SX, hsd, Bool.false_eq_true, if_false]
      exact isub_sound _ _ (imulZ_sound _ _ hc1 hc2) (imulZ_sound _ _ hs1 hs2)
    · have ex : Real.pi * x = Real.pi * ((c.k:ℝ) / 2) + Real.pi * r := by
        simp only [hr, hsd, if_true]; rw [← eA]; ring
      rw [ex, Real.sin_add, hcs.1, hcs.2]
      simp only [Cell.SX, hsd, if_true]
      exact iadd_sound _ _ (imulZ_sound _ _ hc1 hc2) (imulZ_sound _ _ hs1 hs2)
  -- π x and 2 γ π x
  have hb1 : (c.BL : ℝ) ≤ Real.pi * x := by
    have h1 : (c.BL : ℝ) ≤ ((piLoQ * c.L : ℚ) : ℝ) := floorD_le' _
    rw [Rat.cast_mul] at h1
    exact h1.trans (mul_ge_of piLoQ_le hx1 piLoQ_nonneg h0' le_rfl)
  have hb2 : Real.pi * x ≤ c.BU := by
    have h1 : ((piHiQ * c.U : ℚ) : ℝ) ≤ (c.BU : ℝ) := le_ceilD' _
    rw [Rat.cast_mul] at h1
    exact (mul_le_of piHiQ_ge hx2 Real.pi_pos.le (h0'.trans hx1) le_rfl).trans h1
  have hπx0 : (0:ℝ) ≤ Real.pi * x := hBL0.trans hb1
  have hgam0 : (0:ℝ) ≤ gam := gamLoQ_nonneg.trans gamLoQ_le
  have hp1 : (c.P2L : ℝ) ≤ 2 * gam * (Real.pi * x) := by
    have h1 : (c.P2L : ℝ) ≤ ((2 * gamLoQ * c.BL : ℚ) : ℝ) := floorD_le' _
    push_cast at h1
    have := mul_le_mul gamLoQ_le hb1 hBL0 hgam0
    linarith
  have hp2 : 2 * gam * (Real.pi * x) ≤ c.P2U := by
    have h1 : ((2 * gamHiQ * c.BU : ℚ) : ℝ) ≤ (c.P2U : ℝ) := le_ceilD' _
    push_cast at h1
    have := mul_le_mul gamHiQ_ge hb2 hπx0 (gamLoQ_nonneg.trans (gamLoQ_le.trans gamHiQ_ge))
    linarith
  -- the product 2 γ π x · sin (π x)
  have hT1 : (c.TLO : ℝ) ≤ 2 * gam * (Real.pi * x) * Real.sin (Real.pi * x) := by
    have h1 : (c.TLO : ℝ) ≤ ((min (c.P2L * c.SX.1) (c.P2U * c.SX.1) : ℚ) : ℝ) := floorD_le' _
    rw [Rat.cast_min, Rat.cast_mul, Rat.cast_mul] at h1
    exact h1.trans (prod_lo hP2L0 hp1 hp2 hSX.1 (min_le_left _ _) (min_le_right _ _))
  have hT2 : 2 * gam * (Real.pi * x) * Real.sin (Real.pi * x) ≤ c.THI := by
    have h1 : ((max (c.P2L * c.SX.2) (c.P2U * c.SX.2) : ℚ) : ℝ) ≤ (c.THI : ℝ) := le_ceilD' _
    rw [Rat.cast_max, Rat.cast_mul, Rat.cast_mul] at h1
    exact (prod_hi hP2L0 hp1 hp2 hSX.2 (le_max_left _ _) (le_max_right _ _)).trans h1
  -- the numerator
  have eNLO : (c.NLO : ℝ) = max 0 (max (((c.CX).1 : ℝ) - c.THI) ((c.TLO : ℝ) - (c.CX).2)) := by
    rw [Cell.NLO, Rat.cast_max, Rat.cast_max]; push_cast; rfl
  have hN : (c.NLO : ℝ) ≤ |Real.cos (Real.pi * x) - 2 * gam * (Real.pi * x) * Real.sin (Real.pi * x)| := by
    rw [eNLO]
    refine max_le (abs_nonneg _) (max_le ?_ ?_)
    · exact le_trans (by linarith [hCX.1, hT2]) (le_abs_self _)
    · exact le_trans (by linarith [hCX.2, hT1]) (neg_le_abs _)
  have hNLO0 : (0:ℝ) ≤ c.NLO := by rw [eNLO]; exact le_max_left _ _
  -- the denominator
  have hD0 : (1:ℝ) < 2 * (Real.pi * x)^2 := by
    have := mul_le_mul hb1 hb1 hBL0 hπx0
    rw [pow_two]; linarith [this, hB']
  have hDD : 2 * (Real.pi * x)^2 - 1 ≤ c.DHI := by
    have h1 : ((2 * c.BU * c.BU - 1 : ℚ) : ℝ) ≤ (c.DHI : ℝ) := le_ceilD' _
    push_cast at h1
    have := mul_le_mul hb2 hb2 hπx0 (hπx0.trans hb2)
    rw [pow_two]; linarith [this, h1]
  have hfin := wfun_ge x (c.NLO : ℝ) (c.DHI : ℝ) hNLO0 hD' hD0 hDD hN
  have eWc : (c.Wc : ℝ) = ((c.NLO : ℝ) / c.DHI)^2 := by rw [Cell.Wc]; push_cast; rfl
  rw [eWc] at hW'
  exact hW'.trans hfin

/-! ### Soundness: chains -/

theorem getD_mem_of_lt {cs : List Cell} {i : ℕ} (h : i < cs.length) : cs.getD i default ∈ cs := by
  rw [List.getD_eq_getElem cs default h]; exact List.getElem_mem h

theorem chain_sound (cs : List Cell) (hcs : cs.all Cell.ok = true) :
    ∀ (idxs : List ℕ) (lo hi : ℚ), chainCheck cs lo hi idxs = true →
      ∀ e : ℝ, (lo : ℝ) ≤ e → e ≤ hi → (chainW cs idxs : ℝ) ≤ wfun e := by
  intro idxs
  induction idxs with
  | nil =>
    intro lo hi h e _ _
    simp only [chainW, Rat.cast_zero]; exact wfun_nonneg e
  | cons i rest ih =>
    intro lo hi h e he1 he2
    simp only [chainCheck, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨hi_lt, hL⟩, hrest⟩ := h
    have hok : (cs.getD i default).ok = true :=
      List.all_eq_true.mp hcs _ (getD_mem_of_lt hi_lt)
    have hL' : ((cs.getD i default).L : ℝ) ≤ e := le_trans (by exact_mod_cast hL) he1
    simp only [chainW]
    split_ifs with hempty
    · -- the last cell: `chainCheck cs U hi [] = decide (hi ≤ U)`
      have hU : hi ≤ (cs.getD i default).U := by
        rw [List.isEmpty_iff.mp hempty] at hrest
        simpa [chainCheck] using hrest
      exact cell_sound _ hok e hL' (he2.trans (by exact_mod_cast hU))
    · rw [Rat.cast_min]
      rcases le_total e ((cs.getD i default).U : ℝ) with hU | hU
      · exact (min_le_left _ _).trans (cell_sound _ hok e hL' hU)
      · exact (min_le_right _ _).trans (ih _ _ hrest e hU he2)

theorem term_sound (cs : List Cell) (hcs : cs.all Cell.ok = true) (idxs : List ℕ) (lo hi : ℚ)
    (h : termCheck cs lo hi idxs = true) (e : ℝ) (he1 : (lo : ℝ) ≤ e) (he2 : e ≤ hi) :
    (termW cs idxs : ℝ) ≤ wfun e := by
  simp only [termCheck, Bool.or_eq_true] at h
  simp only [termW]
  split_ifs with hempty
  · simp only [Rat.cast_zero]; exact wfun_nonneg e
  · rcases h with h | h
    · exact absurd h (by simpa using hempty)
    · exact chain_sound cs hcs idxs lo hi h e he1 he2

/-! ### Soundness: boxes and trees -/

/-- The four-point functional written out on the three gaps (rational instance). -/
def G4 (p : ℚ) (x y z : ℝ) : ℝ :=
  (1 / (p : ℝ)) * (x + y + z) + 2/3 * wfun x + 2/3 * wfun y + 2/3 * wfun z
    + wfun (x + y) + wfun (y + z) + 2 * wfun (x + y + z)

theorem leaf_sound (cs : List Cell) (hcs : cs.all Cell.ok = true) (c p : ℚ) (hp : 0 < p) (b : Box)
    (t0 t1 t2 t3 t4 t5 : List ℕ) (h : leafCheck cs c p b t0 t1 t2 t3 t4 t5 = true)
    (x y z : ℝ) (hx1 : (b.xl : ℝ) ≤ x) (hx2 : x ≤ b.xu) (hy1 : (b.yl : ℝ) ≤ y) (hy2 : y ≤ b.yu)
    (hz1 : (b.zl : ℝ) ≤ z) (hz2 : z ≤ b.zu) : (c : ℝ) ≤ G4 p x y z := by
  simp only [leafCheck, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, hineq⟩ := h
  have w0 := term_sound cs hcs t0 _ _ h0 x hx1 hx2
  have w1 := term_sound cs hcs t1 _ _ h1 y hy1 hy2
  have w2 := term_sound cs hcs t2 _ _ h2 z hz1 hz2
  have w3 := term_sound cs hcs t3 _ _ h3 (x + y) (by push_cast; linarith) (by push_cast; linarith)
  have w4 := term_sound cs hcs t4 _ _ h4 (y + z) (by push_cast; linarith) (by push_cast; linarith)
  have w5 := term_sound cs hcs t5 _ _ h5 (x + y + z) (by push_cast; linarith) (by push_cast; linarith)
  have hineq' := (Rat.cast_le (K := ℝ)).mpr hineq
  push_cast at hineq'
  have hp' : (0:ℝ) < p := by exact_mod_cast hp
  have hlin : ((b.xl : ℝ) + b.yl + b.zl) / (p : ℝ) ≤ (1 / (p : ℝ)) * (x + y + z) := by
    rw [div_eq_mul_one_div, mul_comm]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    linarith
  unfold G4
  linarith

theorem tree_sound (cs : List Cell) (hcs : cs.all Cell.ok = true) (c p : ℚ) (hp : 0 < p) :
    ∀ (t : Tree) (b : Box), treeCheck cs c p b t = true →
      ∀ x y z : ℝ, (b.xl : ℝ) ≤ x → x ≤ b.xu → (b.yl : ℝ) ≤ y → y ≤ b.yu →
        (b.zl : ℝ) ≤ z → z ≤ b.zu → (c : ℝ) ≤ G4 p x y z := by
  intro t
  induction t with
  | leaf t0 t1 t2 t3 t4 t5 =>
    intro b h x y z hx1 hx2 hy1 hy2 hz1 hz2
    exact leaf_sound cs hcs c p hp b t0 t1 t2 t3 t4 t5 h x y z hx1 hx2 hy1 hy2 hz1 hz2
  | split ax q lo hi ihlo ihhi =>
    intro b h x y z hx1 hx2 hy1 hy2 hz1 hz2
    simp only [treeCheck] at h
    split_ifs at h with h0 h1 h2
    · rw [Bool.and_eq_true] at h
      rcases le_total x (q : ℝ) with hq | hq
      · exact ihlo _ h.1 x y z hx1 hq hy1 hy2 hz1 hz2
      · exact ihhi _ h.2 x y z hq hx2 hy1 hy2 hz1 hz2
    · rw [Bool.and_eq_true] at h
      rcases le_total y (q : ℝ) with hq | hq
      · exact ihlo _ h.1 x y z hx1 hx2 hy1 hq hz1 hz2
      · exact ihhi _ h.2 x y z hx1 hx2 hq hy2 hz1 hz2
    · rw [Bool.and_eq_true] at h
      rcases le_total z (q : ℝ) with hq | hq
      · exact ihlo _ h.1 x y z hx1 hx2 hy1 hy2 hz1 hq
      · exact ihhi _ h.2 x y z hx1 hx2 hy1 hy2 hq hz2

/-! ### Soundness: the cover -/

theorem cover_sound (cs : List Cell) (hcs : cs.all Cell.ok = true) (lvl : ℚ) :
    ∀ (cover : List (ℚ × ℚ × List ℕ)) (pos S : ℚ), coverCheck cs lvl pos S cover = true →
      ∀ v : ℝ, (pos : ℝ) ≤ v → v < S →
        (lvl : ℝ) ≤ wfun v ∨ ∃ s ∈ cover, s.2.2.isEmpty = true ∧ (s.1 : ℝ) ≤ v ∧ v ≤ s.2.1 := by
  intro cover
  induction cover with
  | nil =>
    intro pos S h v hv1 hv2
    simp only [coverCheck, decide_eq_true_eq] at h
    have : (S : ℝ) ≤ pos := by exact_mod_cast h
    exact absurd (lt_of_le_of_lt (this.trans hv1) hv2) (lt_irrefl _)
  | cons s rest ih =>
    intro pos S h v hv1 hv2
    obtain ⟨a, b, ch⟩ := s
    simp only [coverCheck, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true] at h
    obtain ⟨⟨⟨hpos, hab⟩, hch⟩, hrest⟩ := h
    rcases le_total v (b : ℝ) with hvb | hvb
    · rcases hch with hch | ⟨hchain, hlvl⟩
      · right
        refine ⟨(a, b, ch), List.mem_cons_self .., hch, ?_, hvb⟩
        rw [hpos]; exact hv1
      · left
        have hW := chain_sound cs hcs ch a b hchain v (by rw [hpos]; exact hv1) hvb
        exact le_trans (by exact_mod_cast hlvl) hW
    · rcases ih b S hrest v hvb hv2 with h | ⟨s', hs', he, h1, h2⟩
      · left; exact h
      · right; exact ⟨s', List.mem_cons_of_mem _ hs', he, h1, h2⟩

theorem badOf_mem {cover : List (ℚ × ℚ × List ℕ)} {s : ℚ × ℚ × List ℕ} (hs : s ∈ cover)
    (he : s.2.2.isEmpty = true) : (s.1, s.2.1) ∈ badOf cover := by
  simp only [badOf, List.mem_filterMap]
  exact ⟨s, hs, by simp [he]⟩

theorem trees_sound (cs : List Cell) (hcs : cs.all Cell.ok = true) (c p : ℚ) (hp : 0 < p)
    (bad : List (ℚ × ℚ)) (trees : List Tree) (h : treesCheck cs c p bad trees = true)
    (i j k : ℕ) (hi : i < bad.length) (hj : j < bad.length) (hk : k < bad.length)
    (x y z : ℝ)
    (hx1 : ((bad.getD i (0, 0)).1 : ℝ) ≤ x) (hx2 : x ≤ (bad.getD i (0, 0)).2)
    (hy1 : ((bad.getD j (0, 0)).1 : ℝ) ≤ y) (hy2 : y ≤ (bad.getD j (0, 0)).2)
    (hz1 : ((bad.getD k (0, 0)).1 : ℝ) ≤ z) (hz2 : z ≤ (bad.getD k (0, 0)).2) :
    (c : ℝ) ≤ G4 p x y z := by
  simp only [treesCheck, List.all_eq_true, List.mem_range] at h
  have ht := h i hi j hj k hk
  exact tree_sound cs hcs c p hp _ (boxOf bad i j k) ht x y z hx1 hx2 hy1 hy2 hz1 hz2

/-! ### The four-point certificate from a checked rational table (not used by the weighted path) -/

theorem four_point_of_check (cs : List Cell) (cover : List (ℚ × ℚ × List ℕ)) (trees : List Tree)
    (c p S : ℚ) (hS : S = c * p) (hp : 0 < p)
    (hwin : 3/2 * c ≤ 19/100) (hcs : cs.all Cell.ok = true)
    (hcov : coverCheck cs (3/2 * c) (1/2) S cover = true)
    (htr : treesCheck cs c p (badOf cover) trees = true) :
    ∀ x y z : ℝ, 0 ≤ x → 0 ≤ y → 0 ≤ z → (c : ℝ) ≤ G4 p x y z := by
  intro x y z hx hy hz
  have hw := fun t : ℝ => wfun_nonneg t
  have hp' : (0:ℝ) < p := by exact_mod_cast hp
  have hlin : (0:ℝ) ≤ (1 / (p : ℝ)) * (x + y + z) := by positivity
  by_cases hsum : (S : ℝ) ≤ x + y + z
  · have hS' : (S : ℝ) = c * p := by exact_mod_cast hS
    have : (c : ℝ) ≤ (1 / (p : ℝ)) * (x + y + z) := by
      rw [one_div, inv_mul_eq_div, le_div_iff₀ hp']; linarith
    unfold G4; linarith [hw x, hw y, hw z, hw (x + y), hw (y + z), hw (x + y + z)]
  push_neg at hsum
  have key : ∀ v : ℝ, 0 ≤ v → v < S →
      (c : ℝ) ≤ 2/3 * wfun v ∨ ∃ i, i < (badOf cover).length ∧
        (((badOf cover).getD i (0, 0)).1 : ℝ) ≤ v ∧ v ≤ ((badOf cover).getD i (0, 0)).2 := by
    intro v hv0 hvS
    rcases le_total v (1/2 : ℝ) with hv | hv
    · left
      have := wfun_window v hv0 hv
      have hwin' := (Rat.cast_le (K := ℝ)).mpr hwin
      push_cast at hwin'
      linarith
    · rcases cover_sound cs hcs _ cover (1/2) S hcov v (by push_cast; exact hv) hvS with
        h | ⟨s, hs, he, h1, h2⟩
      · left; push_cast at h; linarith
      · right
        have hmem := badOf_mem hs he
        obtain ⟨i, hi, hsi⟩ := List.mem_iff_getElem.mp hmem
        refine ⟨i, hi, ?_, ?_⟩
        · rw [List.getD_eq_getElem _ _ hi, hsi]; exact h1
        · rw [List.getD_eq_getElem _ _ hi, hsi]; exact h2
  rcases key x hx (by linarith) with hxc | ⟨i, hi, hxi1, hxi2⟩
  · unfold G4; linarith [hw y, hw z, hw (x + y), hw (y + z), hw (x + y + z)]
  rcases key y hy (by linarith) with hyc | ⟨j, hj, hyj1, hyj2⟩
  · unfold G4; linarith [hw x, hw z, hw (x + y), hw (y + z), hw (x + y + z)]
  rcases key z hz (by linarith) with hzc | ⟨k, hk, hzk1, hzk2⟩
  · unfold G4; linarith [hw x, hw y, hw (x + y), hw (y + z), hw (x + y + z)]
  exact trees_sound cs hcs c p hp _ trees htr i j k hi hj hk x y z hxi1 hxi2 hyj1 hyj2 hzk1 hzk2

private lemma sum3 (f : Fin (4 - 1) → ℝ) : ∑ i, f i = f 0 + f 1 + f 2 := by
  show ∑ i : Fin 3, f i = f 0 + f 1 + f 2
  exact Fin.sum_univ_three f

/-- The four-point functional, written out (rational instance). -/
lemma F4_eq (p : ℕ) (g : Fin 3 → ℝ) :
    F 4 p g = (1 / (p : ℝ)) * (g 0 + g 1 + g 2)
      + 2/3 * wfun (g 0) + 2/3 * wfun (g 1) + 2/3 * wfun (g 2)
      + wfun (g 0 + g 1) + wfun (g 1 + g 2) + 2 * wfun (g 0 + g 1 + g 2) := by
  simp only [F, ptsN, sum3, Fin.sum_univ_four, Fin.isValue]
  norm_num
  try ring

end Zeta23Ext.Bridge.ThreePoint

end

/-! ###### integer cell pipeline for the pyramid certificate `SixW25P` ###### -/

section SixW25PCells

namespace Zeta23Ext.Bridge.ThreePoint

structure CellN where
  (key : ℕ) (WN : ℕ)

instance : Inhabited CellN := ⟨⟨0, 0⟩⟩

def SC : ℕ := 32768
def SW : ℕ := 10000000000000

/-- a cell's endpoints are packed into one key `LN * KB + UN` (every coordinate is below `KB`) -/
def KB : ℕ := 1048576
def CellN.LN (c : CellN) : ℕ := c.key / KB
def CellN.UN (c : CellN) : ℕ := c.key % KB

/-- the anchor index `k` (anchor at `k/2`) nearest the cell's midpoint, and the side of that anchor the cell lies on -/
def CellN.k (c : CellN) : ℕ := (2 * (c.LN + c.UN) + SC) / (2 * SC)
def CellN.side (c : CellN) : Bool := Nat.ble (c.k * SC) (2 * c.LN)

-- ZDEFS-BEGIN
/-- the scale of the integer bounds -/
def DZ : ℕ := 1000000000000000
def DZ2 : ℕ := 500000000000000
/-- π·10²⁰, below and above -/
def PLN : ℕ := 314159265358979323846
def PUN : ℕ := 314159265358979323847
/-- γ·10¹⁰, below and above -/
def GLN : ℕ := 8274992907
def GUN : ℕ := 8274993018
/-- the Taylor remainder, rounded up at scale `10¹⁵` -/
def ERRD : ℕ := 2262000

/-- floor and ceiling of `a / b` for naturals -/
def ndiv (a b : ℕ) : ℕ := a / b
def ndivc (a b : ℕ) : ℕ := (a + b - 1) / b

/-- `cos (T / DZ)` by the twelve-term Taylor polynomial: positive and negative parts of the
numerator over `3628800 · DZ¹⁰`. -/
def cosP (T : ℕ) : ℕ := 3628800 * DZ^10 + 151200 * T^4 * DZ^6 + 90 * T^8 * DZ^2
def cosN (T : ℕ) : ℕ := 1814400 * T^2 * DZ^8 + 5040 * T^6 * DZ^4 + T^10
def sinP (T : ℕ) : ℕ := 39916800 * T * DZ^10 + 332640 * T^5 * DZ^6 + 110 * T^9 * DZ^2
def sinN (T : ℕ) : ℕ := 6652800 * T^3 * DZ^8 + 7920 * T^7 * DZ^4 + T^11
/-- lower / upper bounds of the polynomial values at scale `DZ` -/
def cosLo (T : ℕ) : ℕ := ndiv (cosP T - cosN T) (3628800 * DZ^9)
def cosHi (T : ℕ) : ℕ := ndivc (cosP T - cosN T) (3628800 * DZ^9)
def sinLo (T : ℕ) : ℕ := ndiv (sinP T - sinN T) (39916800 * DZ^10)
def sinHi (T : ℕ) : ℕ := ndivc (sinP T - sinN T) (39916800 * DZ^10)

/-- floor / ceiling division of an integer by `DZ` -/
def zfdiv (z : ℤ) : ℤ := if 0 ≤ z then ((ndiv z.toNat DZ : ℕ) : ℤ) else -((ndivc (-z).toNat DZ : ℕ) : ℤ)
def zcdiv (z : ℤ) : ℤ := if 0 ≤ z then ((ndivc z.toNat DZ : ℕ) : ℤ) else -((ndiv (-z).toNat DZ : ℕ) : ℤ)

def imulZZ (e : ℤ) (I : ℤ × ℤ) : ℤ × ℤ := if 0 ≤ e then (e * I.1, e * I.2) else (e * I.2, e * I.1)
def iaddZ (I J : ℤ × ℤ) : ℤ × ℤ := (I.1 + J.1, I.2 + J.2)
def isubZ (I J : ℤ × ℤ) : ℤ × ℤ := (I.1 - J.2, I.2 - J.1)

namespace CellN
/-- lower/upper integer bounds (scale `DZ`) of the cell's endpoints -/
def LLO (c : CellN) : ℕ := ndiv (c.LN * DZ) SC
def UHI (c : CellN) : ℕ := ndivc (c.UN * DZ) SC
def AD (c : CellN) : ℕ := c.k * DZ2
def RLO (c : CellN) : ℕ := if c.side then c.LLO - c.AD else c.AD - c.UHI
def RHI (c : CellN) : ℕ := if c.side then c.UHI - c.AD else c.AD - c.LLO
def TLZ (c : CellN) : ℕ := ndiv (PLN * c.RLO) 100000000000000000000
def TUZ (c : CellN) : ℕ := ndivc (PUN * c.RHI) 100000000000000000000
def CLZ (c : CellN) : ℤ := (cosLo c.TUZ : ℤ) - ERRD
def CUZ (c : CellN) : ℤ := (cosHi c.TLZ : ℤ) + ERRD
def SLZ (c : CellN) : ℤ := (sinLo c.TLZ : ℤ) - ERRD
def SUZ (c : CellN) : ℤ := (sinHi c.TUZ : ℤ) + ERRD
def cAZ (c : CellN) : ℤ := (csA c.k).1
def sAZ (c : CellN) : ℤ := (csA c.k).2
def CXZ (c : CellN) : ℤ × ℤ :=
  if c.side then isubZ (imulZZ c.cAZ (c.CLZ, c.CUZ)) (imulZZ c.sAZ (c.SLZ, c.SUZ))
  else iaddZ (imulZZ c.cAZ (c.CLZ, c.CUZ)) (imulZZ c.sAZ (c.SLZ, c.SUZ))
def SXZ (c : CellN) : ℤ × ℤ :=
  if c.side then iaddZ (imulZZ c.sAZ (c.CLZ, c.CUZ)) (imulZZ c.cAZ (c.SLZ, c.SUZ))
  else isubZ (imulZZ c.sAZ (c.CLZ, c.CUZ)) (imulZZ c.cAZ (c.SLZ, c.SUZ))
def BLZ (c : CellN) : ℕ := ndiv (PLN * c.LLO) 100000000000000000000
def BUZ (c : CellN) : ℕ := ndivc (PUN * c.UHI) 100000000000000000000
def P2LZ (c : CellN) : ℕ := ndiv (2 * GLN * c.BLZ) 10000000000
def P2UZ (c : CellN) : ℕ := ndivc (2 * GUN * c.BUZ) 10000000000
def TLOZ (c : CellN) : ℤ := zfdiv (min ((c.P2LZ : ℤ) * c.SXZ.1) ((c.P2UZ : ℤ) * c.SXZ.1))
def THIZ (c : CellN) : ℤ := zcdiv (max ((c.P2LZ : ℤ) * c.SXZ.2) ((c.P2UZ : ℤ) * c.SXZ.2))
def NLOZ (c : CellN) : ℤ := max 0 (max (c.CXZ.1 - c.THIZ) (c.TLOZ - c.CXZ.2))
def DHIZ (c : CellN) : ℤ := ((ndivc (2 * c.BUZ * c.BUZ) DZ : ℕ) : ℤ) - DZ
/-- the conditions of the integer check that do not involve the claimed bound -/
def okC (c : CellN) : Bool :=
  decide (c.LN ≤ c.UN) && decide (c.TUZ ≤ DZ)
    && (if c.side then decide (c.k * SC ≤ 2 * c.LN) else decide (2 * c.UN ≤ c.k * SC))
    && decide (cosN c.TUZ ≤ cosP c.TUZ) && decide (cosN c.TLZ ≤ cosP c.TLZ)
    && decide (sinN c.TLZ ≤ sinP c.TLZ) && decide (sinN c.TUZ ≤ sinP c.TUZ)
    && decide (DZ * DZ < 2 * c.BLZ * c.BLZ) && decide (0 < c.DHIZ)
/-- the integer check of a claimed bound `WN` -/
def okZ (c : CellN) : Bool :=
  c.okC && decide ((c.WN : ℤ) * c.DHIZ * c.DHIZ ≤ c.NLOZ * c.NLOZ * SW)
/-- the bound the pipeline certifies for the cell (0 outside its scope) -/
def WZ (c : CellN) : ℕ :=
  bif c.okC then ((c.NLOZ * c.NLOZ * SW) / (c.DHIZ * c.DHIZ)).toNat else 0
end CellN
-- ZDEFS-END

end Zeta23Ext.Bridge.ThreePoint

end SixW25PCells

noncomputable section

open Real

namespace Zeta23Ext.Bridge.ThreePoint

-- ZLEMMAS-BEGIN
/-! ### rounding lemmas -/

theorem DZ_pos : (0:ℝ) < DZ := by norm_num [DZ]
theorem DZ_ne : (DZ:ℝ) ≠ 0 := by norm_num [DZ]

theorem ndiv_le (a b : ℕ) (hb : 0 < b) : ((ndiv a b : ℕ) : ℝ) ≤ (a : ℝ) / b := by
  unfold ndiv
  rw [le_div_iff₀ (by exact_mod_cast hb)]
  exact_mod_cast Nat.div_mul_le_self a b

theorem le_ndivc (a b : ℕ) (hb : 0 < b) : (a : ℝ) / b ≤ ((ndivc a b : ℕ) : ℝ) := by
  unfold ndivc
  rw [div_le_iff₀ (by exact_mod_cast hb)]
  have h : a ≤ ((a + b - 1) / b) * b := by
    have := Nat.lt_div_mul_add (a := a + b - 1) hb
    omega
  exact_mod_cast h

theorem zfdiv_le (z : ℤ) : ((zfdiv z : ℤ) : ℝ) ≤ (z : ℝ) / DZ := by
  unfold zfdiv
  split_ifs with h
  · have hz : (((z.toNat : ℕ) : ℤ) : ℝ) = (z : ℝ) := by rw [Int.toNat_of_nonneg h]
    rw [Int.cast_natCast, ← hz, Int.cast_natCast]
    exact ndiv_le _ _ (by norm_num [DZ])
  · push_neg at h
    have hz : ((((-z).toNat : ℕ) : ℤ) : ℝ) = ((-z : ℤ) : ℝ) := by rw [Int.toNat_of_nonneg (by linarith)]
    rw [Int.cast_neg, Int.cast_natCast]
    rw [Int.cast_natCast, Int.cast_neg] at hz
    rw [show (z : ℝ) = -(((-z).toNat : ℕ) : ℝ) by linarith, neg_div]
    exact neg_le_neg (le_ndivc _ _ (by norm_num [DZ]))

theorem le_zcdiv (z : ℤ) : (z : ℝ) / DZ ≤ ((zcdiv z : ℤ) : ℝ) := by
  unfold zcdiv
  split_ifs with h
  · have hz : (((z.toNat : ℕ) : ℤ) : ℝ) = (z : ℝ) := by rw [Int.toNat_of_nonneg h]
    rw [Int.cast_natCast, ← hz, Int.cast_natCast]
    exact le_ndivc _ _ (by norm_num [DZ])
  · push_neg at h
    have hz : ((((-z).toNat : ℕ) : ℤ) : ℝ) = ((-z : ℤ) : ℝ) := by rw [Int.toNat_of_nonneg (by linarith)]
    rw [Int.cast_neg, Int.cast_natCast]
    rw [Int.cast_natCast, Int.cast_neg] at hz
    rw [show (z : ℝ) = -(((-z).toNat : ℕ) : ℝ) by linarith, neg_div]
    exact neg_le_neg (ndiv_le _ _ (by norm_num [DZ]))

/-! ### the Taylor polynomials at scale `DZ` -/

theorem taylorCos_eq (T : ℕ) (h : cosN T ≤ cosP T) :
    taylorCos ((T : ℝ) / DZ) = ((cosP T - cosN T : ℕ) : ℝ) / (3628800 * (DZ : ℝ)^10) := by
  rw [Nat.cast_sub h]
  unfold taylorCos cosP cosN
  push_cast
  have hD := DZ_ne
  field_simp
  ring

theorem taylorSin_eq (T : ℕ) (h : sinN T ≤ sinP T) :
    taylorSin ((T : ℝ) / DZ) = ((sinP T - sinN T : ℕ) : ℝ) / (39916800 * (DZ : ℝ)^11) := by
  rw [Nat.cast_sub h]
  unfold taylorSin sinP sinN
  push_cast
  have hD := DZ_ne
  field_simp
  ring

theorem cosLo_le (T : ℕ) (h : cosN T ≤ cosP T) :
    ((cosLo T : ℕ) : ℝ) / DZ ≤ taylorCos ((T : ℝ) / DZ) := by
  rw [taylorCos_eq T h]
  unfold cosLo
  have := ndiv_le (cosP T - cosN T) (3628800 * DZ^9) (by norm_num [DZ])
  rw [div_le_div_iff₀ DZ_pos (by norm_num [DZ])]
  push_cast at this ⊢
  have hD : (0:ℝ) < DZ := DZ_pos
  calc ((ndiv (cosP T - cosN T) (3628800 * DZ ^ 9) : ℕ) : ℝ) * (3628800 * (DZ:ℝ) ^ 10)
      = (((ndiv (cosP T - cosN T) (3628800 * DZ ^ 9) : ℕ) : ℝ)) * (3628800 * (DZ:ℝ)^9) * DZ := by ring
    _ ≤ ((cosP T - cosN T : ℕ) : ℝ) * DZ := by
        apply mul_le_mul_of_nonneg_right _ hD.le
        rw [le_div_iff₀ (by norm_num [DZ])] at this
        exact this

theorem le_cosHi (T : ℕ) (h : cosN T ≤ cosP T) :
    taylorCos ((T : ℝ) / DZ) ≤ ((cosHi T : ℕ) : ℝ) / DZ := by
  rw [taylorCos_eq T h]
  unfold cosHi
  have := le_ndivc (cosP T - cosN T) (3628800 * DZ^9) (by norm_num [DZ])
  rw [div_le_div_iff₀ (by norm_num [DZ]) DZ_pos]
  push_cast at this ⊢
  have hD : (0:ℝ) < DZ := DZ_pos
  calc ((cosP T - cosN T : ℕ) : ℝ) * DZ
      ≤ ((ndivc (cosP T - cosN T) (3628800 * DZ ^ 9) : ℕ) : ℝ) * (3628800 * (DZ:ℝ)^9) * DZ := by
        apply mul_le_mul_of_nonneg_right _ hD.le
        rw [div_le_iff₀ (by norm_num [DZ])] at this
        exact this
    _ = _ := by ring

theorem sinLo_le (T : ℕ) (h : sinN T ≤ sinP T) :
    ((sinLo T : ℕ) : ℝ) / DZ ≤ taylorSin ((T : ℝ) / DZ) := by
  rw [taylorSin_eq T h]
  unfold sinLo
  have := ndiv_le (sinP T - sinN T) (39916800 * DZ^10) (by norm_num [DZ])
  rw [div_le_div_iff₀ DZ_pos (by norm_num [DZ])]
  push_cast at this ⊢
  have hD : (0:ℝ) < DZ := DZ_pos
  calc ((ndiv (sinP T - sinN T) (39916800 * DZ ^ 10) : ℕ) : ℝ) * (39916800 * (DZ:ℝ) ^ 11)
      = (((ndiv (sinP T - sinN T) (39916800 * DZ ^ 10) : ℕ) : ℝ)) * (39916800 * (DZ:ℝ)^10) * DZ := by ring
    _ ≤ ((sinP T - sinN T : ℕ) : ℝ) * DZ := by
        apply mul_le_mul_of_nonneg_right _ hD.le
        rw [le_div_iff₀ (by norm_num [DZ])] at this
        exact this

theorem le_sinHi (T : ℕ) (h : sinN T ≤ sinP T) :
    taylorSin ((T : ℝ) / DZ) ≤ ((sinHi T : ℕ) : ℝ) / DZ := by
  rw [taylorSin_eq T h]
  unfold sinHi
  have := le_ndivc (sinP T - sinN T) (39916800 * DZ^10) (by norm_num [DZ])
  rw [div_le_div_iff₀ (by norm_num [DZ]) DZ_pos]
  push_cast at this ⊢
  have hD : (0:ℝ) < DZ := DZ_pos
  calc ((sinP T - sinN T : ℕ) : ℝ) * DZ
      ≤ ((ndivc (sinP T - sinN T) (39916800 * DZ ^ 10) : ℕ) : ℝ) * (39916800 * (DZ:ℝ)^10) * DZ := by
        apply mul_le_mul_of_nonneg_right _ hD.le
        rw [div_le_iff₀ (by norm_num [DZ])] at this
        exact this
    _ = _ := by ring

theorem ERRD_ge : taylorErr ≤ (ERRD : ℝ) / DZ := by norm_num [taylorErr, ERRD, DZ]

/-! ### interval operations at scale `DZ` -/

theorem imulZZ_sound (e : ℤ) (I : ℤ × ℤ) {f : ℝ} (h1 : (I.1 : ℝ) / DZ ≤ f) (h2 : f ≤ (I.2 : ℝ) / DZ) :
    ((imulZZ e I).1 : ℝ) / DZ ≤ (e : ℝ) * f ∧ (e : ℝ) * f ≤ ((imulZZ e I).2 : ℝ) / DZ := by
  unfold imulZZ
  have hD := DZ_pos
  split_ifs with he
  · have he' : (0:ℝ) ≤ e := by exact_mod_cast he
    simp only; push_cast
    constructor
    · rw [mul_div_assoc]; exact mul_le_mul_of_nonneg_left h1 he'
    · rw [mul_div_assoc]; exact mul_le_mul_of_nonneg_left h2 he'
  · have he' : (e:ℝ) ≤ 0 := by push_neg at he; exact_mod_cast he.le
    simp only; push_cast
    constructor
    · rw [mul_div_assoc]; exact mul_le_mul_of_nonpos_left h2 he'
    · rw [mul_div_assoc]; exact mul_le_mul_of_nonpos_left h1 he'

theorem iaddZ_sound (I J : ℤ × ℤ) {f g : ℝ} (hI : (I.1:ℝ) / DZ ≤ f ∧ f ≤ (I.2:ℝ) / DZ)
    (hJ : (J.1:ℝ) / DZ ≤ g ∧ g ≤ (J.2:ℝ) / DZ) :
    ((iaddZ I J).1 : ℝ) / DZ ≤ f + g ∧ f + g ≤ ((iaddZ I J).2 : ℝ) / DZ := by
  unfold iaddZ; simp only; push_cast; rw [add_div, add_div]
  constructor <;> linarith [hI.1, hI.2, hJ.1, hJ.2]

theorem isubZ_sound (I J : ℤ × ℤ) {f g : ℝ} (hI : (I.1:ℝ) / DZ ≤ f ∧ f ≤ (I.2:ℝ) / DZ)
    (hJ : (J.1:ℝ) / DZ ≤ g ∧ g ≤ (J.2:ℝ) / DZ) :
    ((isubZ I J).1 : ℝ) / DZ ≤ f - g ∧ f - g ≤ ((isubZ I J).2 : ℝ) / DZ := by
  unfold isubZ; simp only; push_cast; rw [sub_div, sub_div]
  constructor <;> linarith [hI.1, hI.2, hJ.1, hJ.2]

/-! ### the integer cell check is sound -/

theorem PLN_le : ((PLN : ℕ) : ℝ) / 100000000000000000000 ≤ Real.pi := by
  have h := pi_lo; norm_num [PLN] at h ⊢; linarith
theorem PUN_ge : Real.pi ≤ ((PUN : ℕ) : ℝ) / 100000000000000000000 := by
  have h := pi_hi; norm_num [PUN] at h ⊢; linarith
theorem GLN_le : ((GLN : ℕ) : ℝ) / 10000000000 ≤ gam := by
  have h := gam_bounds.1; norm_num [GLN] at h ⊢; linarith
theorem GUN_ge : gam ≤ ((GUN : ℕ) : ℝ) / 10000000000 := by
  have h := gam_bounds.2; norm_num [GUN] at h ⊢; linarith

/-- `ndiv a b / DZ ≤ (a / b) / DZ` packaged with a product bound: if `a = p * q` with
`p / P ≤ A` and `q / DZ ≤ B` (all nonnegative) then `ndiv (p*q) P / DZ ≤ A * B`. -/
theorem ndiv_prod_le (p q P : ℕ) (hP : 0 < P) {A B : ℝ} (hA : ((p : ℕ) : ℝ) / P ≤ A)
    (hB : ((q : ℕ) : ℝ) / DZ ≤ B) (hA0 : 0 ≤ ((p : ℕ) : ℝ) / P) (hB0 : 0 ≤ ((q : ℕ) : ℝ) / DZ) :
    ((ndiv (p * q) P : ℕ) : ℝ) / DZ ≤ A * B := by
  have h := ndiv_le (p * q) P hP
  have hD := DZ_pos
  calc ((ndiv (p * q) P : ℕ) : ℝ) / DZ ≤ (((p * q : ℕ) : ℝ) / P) / DZ :=
        div_le_div_of_nonneg_right h hD.le
    _ = (((p : ℕ) : ℝ) / P) * (((q : ℕ) : ℝ) / DZ) := by push_cast; field_simp
    _ ≤ A * B := mul_le_mul hA hB hB0 (hA0.trans hA)

theorem le_ndivc_prod (p q P : ℕ) (hP : 0 < P) {A B : ℝ} (hA : A ≤ ((p : ℕ) : ℝ) / P)
    (hB : B ≤ ((q : ℕ) : ℝ) / DZ) (hA0 : 0 ≤ A) (hB0 : 0 ≤ B) :
    A * B ≤ ((ndivc (p * q) P : ℕ) : ℝ) / DZ := by
  have h := le_ndivc (p * q) P hP
  have hD := DZ_pos
  calc A * B ≤ (((p : ℕ) : ℝ) / P) * (((q : ℕ) : ℝ) / DZ) := mul_le_mul hA hB hB0 (hA0.trans hA)
    _ = (((p * q : ℕ) : ℝ) / P) / DZ := by push_cast; field_simp
    _ ≤ ((ndivc (p * q) P : ℕ) : ℝ) / DZ := div_le_div_of_nonneg_right h hD.le

set_option maxHeartbeats 4000000 in
theorem cellN_soundZ' (c : CellN) (w : ℕ) (hc : c.okC = true)
    (hW : (w : ℤ) * c.DHIZ * c.DHIZ ≤ c.NLOZ * c.NLOZ * SW) (x : ℝ)
    (hx1 : (c.LN : ℝ) / SC ≤ x) (hx2 : x ≤ (c.UN : ℝ) / SC) : (w : ℝ) / SW ≤ wfun x := by
  simp only [CellN.okC, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hLU, hTU⟩, hside⟩, hcP1⟩, hcP2⟩, hsP1⟩, hsP2⟩, hB⟩, hD⟩ := hc
  have hsideT : c.side = true → c.k * SC ≤ 2 * c.LN := fun hs => by simpa [hs] using hside
  have hsideF : c.side = false → 2 * c.UN ≤ c.k * SC := fun hs => by simpa [hs] using hside
  have hD0 := DZ_pos
  have hSC : (0:ℝ) < SC := by norm_num [SC]
  have hSW : (0:ℝ) < SW := by norm_num [SW]
  have nd0 : ∀ a : ℕ, (0:ℝ) ≤ (a : ℝ) / DZ := fun a => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have nP0 : ∀ a : ℕ, (0:ℝ) ≤ (a : ℝ) / 100000000000000000000 :=
    fun a => div_nonneg (Nat.cast_nonneg _) (by norm_num)
  have nG0 : ∀ a : ℕ, (0:ℝ) ≤ (a : ℝ) / 10000000000 :=
    fun a => div_nonneg (Nat.cast_nonneg _) (by norm_num)
  -- endpoints at scale DZ
  have hLLO : ((c.LLO : ℕ) : ℝ) / DZ ≤ (c.LN : ℝ) / SC := by
    have := ndiv_le (c.LN * DZ) SC (by norm_num [SC])
    unfold CellN.LLO
    push_cast at this ⊢
    rw [div_le_iff₀ hD0]
    calc ((ndiv (c.LN * DZ) SC : ℕ) : ℝ) ≤ (c.LN : ℝ) * DZ / SC := this
      _ = (c.LN : ℝ) / SC * DZ := by ring
  have hUHI : (c.UN : ℝ) / SC ≤ ((c.UHI : ℕ) : ℝ) / DZ := by
    have := le_ndivc (c.UN * DZ) SC (by norm_num [SC])
    unfold CellN.UHI
    push_cast at this ⊢
    rw [le_div_iff₀ hD0]
    calc (c.UN : ℝ) / SC * DZ = (c.UN : ℝ) * DZ / SC := by ring
      _ ≤ _ := this
  have hAD : ((c.AD : ℕ) : ℝ) / DZ = (c.k : ℝ) / 2 := by
    unfold CellN.AD; simp only [DZ, DZ2]; push_cast; ring
  have hL0 : (0:ℝ) ≤ (c.LN : ℝ) / SC := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hx0 : 0 ≤ x := hL0.trans hx1
  have hLNUN : (c.LN : ℝ) / SC ≤ (c.UN : ℝ) / SC :=
    div_le_div_of_nonneg_right (by exact_mod_cast hLU) hSC.le
  have hkF : c.side = false → (c.UN : ℝ) / SC ≤ (c.k : ℝ) / 2 := fun hs => by
    have : (2 * c.UN : ℝ) ≤ (c.k * SC : ℝ) := by exact_mod_cast hsideF hs
    rw [div_le_div_iff₀ hSC (by norm_num)]; linarith
  have hkT : c.side = true → (c.k : ℝ) / 2 ≤ (c.LN : ℝ) / SC := fun hs => by
    have : (c.k * SC : ℝ) ≤ (2 * c.LN : ℝ) := by exact_mod_cast hsideT hs
    rw [div_le_div_iff₀ (by norm_num) hSC]; linarith
  -- the reduced offset r and the integer bounds RLO ≤ r ≤ RHI
  set r : ℝ := if c.side then x - (c.k : ℝ) / 2 else (c.k : ℝ) / 2 - x with hr
  have hr0 : 0 ≤ r := by
    simp only [hr]
    cases hsd : c.side
    · simp only [Bool.false_eq_true, if_false]; linarith [hkF hsd]
    · simp only [if_true]; linarith [hkT hsd]
  have hRLO : ((c.RLO : ℕ) : ℝ) / DZ ≤ r := by
    unfold CellN.RLO
    cases hsd : c.side
    · simp only [Bool.false_eq_true, if_false]
      simp only [hr, hsd, Bool.false_eq_true, if_false]
      rcases le_or_gt c.UHI c.AD with hle | hlt
      · rw [Nat.cast_sub hle, sub_div, hAD]; linarith
      · rw [Nat.sub_eq_zero_of_le hlt.le]; simp only [Nat.cast_zero, zero_div]
        linarith [hkF hsd]
    · simp only [if_true]
      simp only [hr, hsd, if_true]
      rcases le_or_gt c.AD c.LLO with hle | hlt
      · rw [Nat.cast_sub hle, sub_div, hAD]; linarith
      · rw [Nat.sub_eq_zero_of_le hlt.le]; simp only [Nat.cast_zero, zero_div]
        linarith [hkT hsd]
  have hRHI : r ≤ ((c.RHI : ℕ) : ℝ) / DZ := by
    unfold CellN.RHI
    cases hsd : c.side
    · simp only [Bool.false_eq_true, if_false]
      simp only [hr, hsd, Bool.false_eq_true, if_false]
      have hle : c.LLO ≤ c.AD := by
        have h1 : ((c.LLO : ℕ) : ℝ) / DZ ≤ (c.k : ℝ) / 2 := by linarith [hkF hsd]
        rw [← hAD] at h1
        have := (div_le_div_iff_of_pos_right hD0).mp h1
        exact_mod_cast this
      rw [Nat.cast_sub hle, sub_div, hAD]; linarith
    · simp only [if_true]
      simp only [hr, hsd, if_true]
      have hle : c.AD ≤ c.UHI := by
        have h1 : (c.k : ℝ) / 2 ≤ ((c.UHI : ℕ) : ℝ) / DZ := by linarith [hkT hsd]
        rw [← hAD] at h1
        have := (div_le_div_iff_of_pos_right hD0).mp h1
        exact_mod_cast this
      rw [Nat.cast_sub hle, sub_div, hAD]; linarith
  -- θ = π r at scale DZ
  have hTL : ((c.TLZ : ℕ) : ℝ) / DZ ≤ Real.pi * r := by
    unfold CellN.TLZ
    exact ndiv_prod_le PLN c.RLO _ (by norm_num) PLN_le hRLO (nP0 _) (nd0 _)
  have hTUr : Real.pi * r ≤ ((c.TUZ : ℕ) : ℝ) / DZ := by
    unfold CellN.TUZ
    exact le_ndivc_prod PUN c.RHI _ (by norm_num) PUN_ge hRHI Real.pi_pos.le hr0
  have hTU1 : ((c.TUZ : ℕ) : ℝ) / DZ ≤ 1 := by
    rw [div_le_one hD0]; exact_mod_cast hTU
  have hTL0 : (0:ℝ) ≤ ((c.TLZ : ℕ) : ℝ) / DZ := nd0 _
  have hθ0 : (0:ℝ) ≤ Real.pi * r := mul_nonneg Real.pi_pos.le hr0
  have hθ1 : Real.pi * r ≤ 1 := hTUr.trans hTU1
  -- Taylor enclosures at the integer endpoints
  have hc1 : ((c.CLZ : ℤ) : ℝ) / DZ ≤ Real.cos (Real.pi * r) := by
    have h := cos_lower hθ0 hTUr hTU1
    have h1 := cosLo_le c.TUZ hcP1
    have h2 := ERRD_ge
    unfold CellN.CLZ; push_cast; rw [sub_div]
    linarith
  have hc2 : Real.cos (Real.pi * r) ≤ ((c.CUZ : ℤ) : ℝ) / DZ := by
    have h := cos_upper hTL0 hTL hθ1
    have h1 := le_cosHi c.TLZ hcP2
    have h2 := ERRD_ge
    unfold CellN.CUZ; push_cast; rw [add_div]
    linarith
  have hs1 : ((c.SLZ : ℤ) : ℝ) / DZ ≤ Real.sin (Real.pi * r) := by
    have h := sin_lower hTL0 hTL hθ1
    have h1 := sinLo_le c.TLZ hsP1
    have h2 := ERRD_ge
    unfold CellN.SLZ; push_cast; rw [sub_div]
    linarith
  have hs2 : Real.sin (Real.pi * r) ≤ ((c.SUZ : ℤ) : ℝ) / DZ := by
    have h := sin_upper hθ0 hTUr hTU1
    have h1 := le_sinHi c.TUZ hsP2
    have h2 := ERRD_ge
    unfold CellN.SUZ; push_cast; rw [add_div]
    linarith
  -- the shift to the anchor
  have hcs := cos_sin_half c.k
  have hCX : ((c.CXZ).1 : ℝ) / DZ ≤ Real.cos (Real.pi * x) ∧ Real.cos (Real.pi * x) ≤ ((c.CXZ).2 : ℝ) / DZ := by
    cases hsd : c.side
    · have ex : Real.pi * x = Real.pi * ((c.k:ℝ) / 2) - Real.pi * r := by
        simp only [hr, hsd, Bool.false_eq_true, if_false]; ring
      rw [ex, Real.cos_sub, hcs.1, hcs.2]
      simp only [CellN.CXZ, hsd, Bool.false_eq_true, if_false]
      exact iaddZ_sound _ _ (imulZZ_sound _ _ hc1 hc2) (imulZZ_sound _ _ hs1 hs2)
    · have ex : Real.pi * x = Real.pi * ((c.k:ℝ) / 2) + Real.pi * r := by
        simp only [hr, hsd, if_true]; ring
      rw [ex, Real.cos_add, hcs.1, hcs.2]
      simp only [CellN.CXZ, hsd, if_true]
      exact isubZ_sound _ _ (imulZZ_sound _ _ hc1 hc2) (imulZZ_sound _ _ hs1 hs2)
  have hSX : ((c.SXZ).1 : ℝ) / DZ ≤ Real.sin (Real.pi * x) ∧ Real.sin (Real.pi * x) ≤ ((c.SXZ).2 : ℝ) / DZ := by
    cases hsd : c.side
    · have ex : Real.pi * x = Real.pi * ((c.k:ℝ) / 2) - Real.pi * r := by
        simp only [hr, hsd, Bool.false_eq_true, if_false]; ring
      rw [ex, Real.sin_sub, hcs.1, hcs.2]
      simp only [CellN.SXZ, hsd, Bool.false_eq_true, if_false]
      exact isubZ_sound _ _ (imulZZ_sound _ _ hc1 hc2) (imulZZ_sound _ _ hs1 hs2)
    · have ex : Real.pi * x = Real.pi * ((c.k:ℝ) / 2) + Real.pi * r := by
        simp only [hr, hsd, if_true]; ring
      rw [ex, Real.sin_add, hcs.1, hcs.2]
      simp only [CellN.SXZ, hsd, if_true]
      exact iaddZ_sound _ _ (imulZZ_sound _ _ hc1 hc2) (imulZZ_sound _ _ hs1 hs2)
  -- π x and 2 γ π x
  have hb1 : ((c.BLZ : ℕ) : ℝ) / DZ ≤ Real.pi * x := by
    unfold CellN.BLZ
    exact ndiv_prod_le PLN c.LLO _ (by norm_num) PLN_le (hLLO.trans hx1) (nP0 _) (nd0 _)
  have hb2 : Real.pi * x ≤ ((c.BUZ : ℕ) : ℝ) / DZ := by
    unfold CellN.BUZ
    exact le_ndivc_prod PUN c.UHI _ (by norm_num) PUN_ge (hx2.trans hUHI) Real.pi_pos.le hx0
  have hBL0 : (0:ℝ) ≤ ((c.BLZ : ℕ) : ℝ) / DZ := nd0 _
  have hπx0 : (0:ℝ) ≤ Real.pi * x := hBL0.trans hb1
  have hgam0 : (0:ℝ) ≤ gam := (nG0 GLN).trans GLN_le
  have hp1 : ((c.P2LZ : ℕ) : ℝ) / DZ ≤ 2 * gam * (Real.pi * x) := by
    unfold CellN.P2LZ
    exact ndiv_prod_le (2 * GLN) c.BLZ 10000000000 (by norm_num) (A := 2 * gam) (B := Real.pi * x)
      (by push_cast; have := GLN_le; linarith) hb1 (nG0 _) hBL0
  have hp2 : 2 * gam * (Real.pi * x) ≤ ((c.P2UZ : ℕ) : ℝ) / DZ := by
    unfold CellN.P2UZ
    exact le_ndivc_prod (2 * GUN) c.BUZ 10000000000 (by norm_num) (A := 2 * gam) (B := Real.pi * x)
      (by push_cast; have := GUN_ge; linarith) hb2 (by linarith) hπx0
  have hP2L0 : (0:ℝ) ≤ ((c.P2LZ : ℕ) : ℝ) / DZ := nd0 _
  -- the product 2 γ π x · sin (π x)
  have hT1 : ((c.TLOZ : ℤ) : ℝ) / DZ ≤ 2 * gam * (Real.pi * x) * Real.sin (Real.pi * x) := by
    have hz := zfdiv_le (min ((c.P2LZ : ℤ) * c.SXZ.1) ((c.P2UZ : ℤ) * c.SXZ.1))
    have hmA : ((min ((c.P2LZ : ℤ) * c.SXZ.1) ((c.P2UZ : ℤ) * c.SXZ.1) : ℤ) : ℝ)
        ≤ (((c.P2LZ : ℤ) * c.SXZ.1 : ℤ) : ℝ) := by exact_mod_cast min_le_left _ _
    have hmB : ((min ((c.P2LZ : ℤ) * c.SXZ.1) ((c.P2UZ : ℤ) * c.SXZ.1) : ℤ) : ℝ)
        ≤ (((c.P2UZ : ℤ) * c.SXZ.1 : ℤ) : ℝ) := by exact_mod_cast min_le_right _ _
    have eA : (((c.P2LZ : ℤ) * c.SXZ.1 : ℤ) : ℝ) / DZ / DZ
        = ((c.P2LZ : ℕ) : ℝ) / DZ * ((((c.SXZ).1 : ℤ) : ℝ) / DZ) := by push_cast; ring
    have eB : (((c.P2UZ : ℤ) * c.SXZ.1 : ℤ) : ℝ) / DZ / DZ
        = ((c.P2UZ : ℕ) : ℝ) / DZ * ((((c.SXZ).1 : ℤ) : ℝ) / DZ) := by push_cast; ring
    unfold CellN.TLOZ
    refine (div_le_div_of_nonneg_right hz hD0.le).trans (prod_lo hP2L0 hp1 hp2 hSX.1 ?_ ?_)
    · rw [← eA]; exact div_le_div_of_nonneg_right (div_le_div_of_nonneg_right hmA hD0.le) hD0.le
    · rw [← eB]; exact div_le_div_of_nonneg_right (div_le_div_of_nonneg_right hmB hD0.le) hD0.le
  have hT2 : 2 * gam * (Real.pi * x) * Real.sin (Real.pi * x) ≤ ((c.THIZ : ℤ) : ℝ) / DZ := by
    have hz := le_zcdiv (max ((c.P2LZ : ℤ) * c.SXZ.2) ((c.P2UZ : ℤ) * c.SXZ.2))
    have hmA : (((c.P2LZ : ℤ) * c.SXZ.2 : ℤ) : ℝ)
        ≤ ((max ((c.P2LZ : ℤ) * c.SXZ.2) ((c.P2UZ : ℤ) * c.SXZ.2) : ℤ) : ℝ) := by exact_mod_cast le_max_left _ _
    have hmB : (((c.P2UZ : ℤ) * c.SXZ.2 : ℤ) : ℝ)
        ≤ ((max ((c.P2LZ : ℤ) * c.SXZ.2) ((c.P2UZ : ℤ) * c.SXZ.2) : ℤ) : ℝ) := by exact_mod_cast le_max_right _ _
    have eA : (((c.P2LZ : ℤ) * c.SXZ.2 : ℤ) : ℝ) / DZ / DZ
        = ((c.P2LZ : ℕ) : ℝ) / DZ * ((((c.SXZ).2 : ℤ) : ℝ) / DZ) := by push_cast; ring
    have eB : (((c.P2UZ : ℤ) * c.SXZ.2 : ℤ) : ℝ) / DZ / DZ
        = ((c.P2UZ : ℕ) : ℝ) / DZ * ((((c.SXZ).2 : ℤ) : ℝ) / DZ) := by push_cast; ring
    unfold CellN.THIZ
    refine (prod_hi hP2L0 hp1 hp2 hSX.2 ?_ ?_).trans (div_le_div_of_nonneg_right hz hD0.le)
    · rw [← eA]; exact div_le_div_of_nonneg_right (div_le_div_of_nonneg_right hmA hD0.le) hD0.le
    · rw [← eB]; exact div_le_div_of_nonneg_right (div_le_div_of_nonneg_right hmB hD0.le) hD0.le
  -- the numerator and the denominator
  set N : ℝ := Real.cos (Real.pi * x) - 2 * gam * (Real.pi * x) * Real.sin (Real.pi * x) with hNdef
  have hN : ((c.NLOZ : ℤ) : ℝ) / DZ ≤ |N| := by
    have hCX1 := (div_le_iff₀ hD0).mp hCX.1
    have hCX2 := (le_div_iff₀ hD0).mp hCX.2
    have hT1' := (div_le_iff₀ hD0).mp hT1
    have hT2' := (le_div_iff₀ hD0).mp hT2
    have ha1 := mul_le_mul_of_nonneg_right (le_abs_self N) hD0.le
    have ha2 := mul_le_mul_of_nonneg_right (neg_le_abs N) hD0.le
    rw [div_le_iff₀ hD0]
    unfold CellN.NLOZ
    rw [Int.cast_max, Int.cast_max, Int.cast_zero]
    refine max_le (mul_nonneg (abs_nonneg _) hD0.le) (max_le ?_ ?_)
    · push_cast; rw [hNdef] at ha1; linarith
    · push_cast; rw [hNdef] at ha2; linarith
  have hNLO0 : (0:ℝ) ≤ ((c.NLOZ : ℤ) : ℝ) / DZ := by
    unfold CellN.NLOZ; rw [Int.cast_max, Int.cast_zero]
    exact div_nonneg (le_max_left _ _) hD0.le
  have hD' : (0:ℝ) < ((c.DHIZ : ℤ) : ℝ) / DZ := by
    have : (0:ℝ) < ((c.DHIZ : ℤ) : ℝ) := by exact_mod_cast hD
    exact div_pos this hD0
  have hD0' : (1:ℝ) < 2 * (Real.pi * x)^2 := by
    have h1 : ((DZ * DZ : ℕ) : ℝ) < ((2 * c.BLZ * c.BLZ : ℕ) : ℝ) := by exact_mod_cast hB
    push_cast at h1
    have h2 : ((c.BLZ : ℕ) : ℝ) / DZ * (((c.BLZ : ℕ) : ℝ) / DZ) ≤ (Real.pi * x) * (Real.pi * x) :=
      mul_le_mul hb1 hb1 hBL0 hπx0
    have h3 : (1:ℝ) < 2 * (((c.BLZ : ℕ) : ℝ) / DZ * (((c.BLZ : ℕ) : ℝ) / DZ)) := by
      rw [div_mul_div_comm, ← mul_div_assoc, lt_div_iff₀ (mul_pos hD0 hD0)]
      linarith
    rw [pow_two]; linarith
  have hDD : 2 * (Real.pi * x)^2 - 1 ≤ ((c.DHIZ : ℤ) : ℝ) / DZ := by
    have h1 := le_ndivc (2 * c.BUZ * c.BUZ) DZ (by norm_num [DZ])
    push_cast at h1
    have h2 : (Real.pi * x) * (Real.pi * x) ≤ ((c.BUZ : ℕ) : ℝ) / DZ * (((c.BUZ : ℕ) : ℝ) / DZ) :=
      mul_le_mul hb2 hb2 hπx0 (hπx0.trans hb2)
    have h3 : 2 * (((c.BUZ : ℕ) : ℝ) / DZ * (((c.BUZ : ℕ) : ℝ) / DZ))
        = 2 * (c.BUZ : ℝ) * (c.BUZ : ℝ) / DZ / DZ := by ring
    have h4 := div_le_div_of_nonneg_right h1 hD0.le
    unfold CellN.DHIZ
    push_cast
    rw [sub_div, div_self DZ_ne, pow_two]
    linarith
  have hfin := wfun_ge x (((c.NLOZ : ℤ) : ℝ) / DZ) (((c.DHIZ : ℤ) : ℝ) / DZ) hNLO0 hD' hD0' hDD hN
  have hWr : ((w : ℕ) : ℝ) * ((c.DHIZ : ℤ) : ℝ) * ((c.DHIZ : ℤ) : ℝ)
      ≤ ((c.NLOZ : ℤ) : ℝ) * ((c.NLOZ : ℤ) : ℝ) * ((SW : ℕ) : ℝ) := by exact_mod_cast hW
  have hDHpos : (0:ℝ) < ((c.DHIZ : ℤ) : ℝ) := by exact_mod_cast hD
  have e : (((c.NLOZ : ℤ) : ℝ) / DZ / (((c.DHIZ : ℤ) : ℝ) / DZ))^2
      = (((c.NLOZ : ℤ) : ℝ) * ((c.NLOZ : ℤ) : ℝ)) / (((c.DHIZ : ℤ) : ℝ) * ((c.DHIZ : ℤ) : ℝ)) := by
    rw [div_div_div_cancel_right₀ DZ_ne]; ring
  have hle : ((w : ℕ) : ℝ) / SW
      ≤ (((c.NLOZ : ℤ) : ℝ) * ((c.NLOZ : ℤ) : ℝ)) / (((c.DHIZ : ℤ) : ℝ) * ((c.DHIZ : ℤ) : ℝ)) := by
    rw [div_le_div_iff₀ hSW (mul_pos hDHpos hDHpos)]
    calc ((w : ℕ) : ℝ) * (((c.DHIZ : ℤ) : ℝ) * ((c.DHIZ : ℤ) : ℝ))
        = ((w : ℕ) : ℝ) * ((c.DHIZ : ℤ) : ℝ) * ((c.DHIZ : ℤ) : ℝ) := by ring
      _ ≤ _ := hWr
  rw [← e] at hle
  exact hle.trans hfin

/-- a claimed bound that passes the integer check is sound -/
theorem cellN_soundZ (c : CellN) (h : c.okZ = true) (x : ℝ)
    (hx1 : (c.LN : ℝ) / SC ≤ x) (hx2 : x ≤ (c.UN : ℝ) / SC) : (c.WN : ℝ) / SW ≤ wfun x := by
  simp only [CellN.okZ, Bool.and_eq_true, decide_eq_true_eq] at h
  exact cellN_soundZ' c c.WN h.1 h.2 x hx1 hx2

/-- the computed bound is sound: no claimed value, the pipeline's own quotient -/
theorem cellN_soundWZ (c : CellN) (x : ℝ)
    (hx1 : (c.LN : ℝ) / SC ≤ x) (hx2 : x ≤ (c.UN : ℝ) / SC) : (c.WZ : ℝ) / SW ≤ wfun x := by
  have key : ∀ b : Bool, c.okC = b →
      ((bif b then ((c.NLOZ * c.NLOZ * SW) / (c.DHIZ * c.DHIZ)).toNat else 0 : ℕ) : ℝ) / SW ≤ wfun x := by
    intro b hb
    cases b
    · simp only [cond_false, Nat.cast_zero, zero_div]; exact wfun_nonneg x
    · simp only [cond_true]
      have hD : 0 < c.DHIZ := by
        simp only [CellN.okC, Bool.and_eq_true, decide_eq_true_eq] at hb; exact hb.2
      have hN : 0 ≤ c.NLOZ := by unfold CellN.NLOZ; exact le_max_left _ _
      have hSWz : (0:ℤ) ≤ (SW : ℤ) := by positivity
      set q : ℤ := (c.NLOZ * c.NLOZ * SW) / (c.DHIZ * c.DHIZ) with hq
      have hq0 : 0 ≤ q := by
        rw [hq]; exact Int.ediv_nonneg (mul_nonneg (mul_nonneg hN hN) hSWz) (mul_pos hD hD).le
      have hqe : ((q.toNat : ℕ) : ℤ) = q := Int.toNat_of_nonneg hq0
      have h1 : q * (c.DHIZ * c.DHIZ) ≤ c.NLOZ * c.NLOZ * SW := by
        rw [hq]; exact Int.ediv_mul_le _ (mul_pos hD hD).ne'
      rw [← hqe] at h1
      exact cellN_soundZ' c q.toNat hb (by linarith) x hx1 hx2
  exact key c.okC rfl
-- ZLEMMAS-END

end Zeta23Ext.Bridge.ThreePoint

end

/-! ###### pyramid lower-bound oracle for `wfun`, kernel-evaluated, and its soundness ######

Pyramid lower-bound table adapted from five-point-pyramid-2 by typh (Apache-2.0).

Cells are absolute and dyadic: the level-`l` cell `i` is `[i 2^l, (i+1) 2^l] / 2^15`.  A table is a natural
`top` (levels 11..19 in heap order: cell `(l, i)` at field `2^(19-l) + i`) and a block map `bk : ℕ → ℕ`: block
`j` (the level-10 cell `j`) is `r + 2^5 Y`, `r ≤ 10` its finest stored level and `Y` its sub-pyramid, depth
`d = 10 - l`, local index `t`, at field `2^d - 1 + t`.  Fields are 32 bits; entries are lower bounds in units of
`10⁻¹⁰`.  `lb top bk lo hi` covers `[lo, hi]` by blocks of level-`k` cells (`k` from the width, the block size
from the alignment of the running start) and returns the least entry read.  The verification `topOk`/`blockOk`
checks the finest cells of every block by the integer cell bound and every coarser entry against its two children.
Only kernel primitives are used, so the kernel evaluates all of it on numerals. -/

noncomputable section

namespace Zeta23Ext.Bridge.ThreePoint.Pyr

open Zeta23Ext.Bridge.ThreePoint

/-- evaluate a natural number to a numeral before continuing (the kernel is call-by-name) -/
def forceR (a : ℕ) (k : ℕ → ℕ) : ℕ := Nat.rec (motive := fun _ => ℕ) (k 0) (fun n _ => k (Nat.succ n)) a

/-- field `i` (32 bits) of a packed natural -/
def fld (X i : ℕ) : ℕ := Nat.land (Nat.shiftRight X (Nat.mul 32 i)) 4294967295

/-- the entry for the level-`l` cell `i` (`l ≤ 10`) from the constant `X` of its block `j`: the entry of its
ancestor at level `max l r`, `r` the block's finest stored level -/
def entB (X l i j : ℕ) : ℕ :=
  let r := Nat.land X 31
  let kk := Bool.rec (motive := fun _ => ℕ) l r (Nat.ble l r)
  let d := Nat.sub 10 kk
  fld (Nat.shiftRight X 5) (Nat.add (Nat.sub (Nat.shiftLeft 1 d) 1) (Nat.sub (Nat.shiftRight i (Nat.sub kk l)) (Nat.shiftLeft j d)))

/-- the entry for the level-`l` cell `i` -/
def entry (top : ℕ) (bk : ℕ → ℕ) (l i : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => ℕ)
    (forceR (Nat.shiftRight i (Nat.sub 10 l)) fun j => entB (bk j) l i j)
    (Bool.rec (motive := fun _ => ℕ) (fld top (Nat.add (Nat.shiftLeft 1 (Nat.sub 19 l)) i)) 0 (Nat.ble 20 l))
    (Nat.ble 11 l)

/-- the size `t` of the next block of cells (`2^t` cells, `t ≤ 4`); any value is sound -/
def alignK1 (g ib : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => ℕ) 0 (Bool.rec (motive := fun _ => ℕ) 0 1 (Nat.ble (Nat.add g 2) (Nat.add ib 1))) (Nat.beq (Nat.land g 1) 0)
def alignK2 (g ib : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => ℕ) (alignK1 g ib) (Bool.rec (motive := fun _ => ℕ) (alignK1 g ib) 2 (Nat.ble (Nat.add g 4) (Nat.add ib 1))) (Nat.beq (Nat.land g 3) 0)
def alignK3 (g ib : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => ℕ) (alignK2 g ib) (Bool.rec (motive := fun _ => ℕ) (alignK2 g ib) 3 (Nat.ble (Nat.add g 8) (Nat.add ib 1))) (Nat.beq (Nat.land g 7) 0)
def alignK4 (g ib : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => ℕ) (alignK3 g ib) (Bool.rec (motive := fun _ => ℕ) (alignK3 g ib) 4 (Nat.ble (Nat.add g 16) (Nat.add ib 1))) (Nat.beq (Nat.land g 15) 0)

def nmin (a b : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) b a (Nat.ble a b)

/-- min of the entries over a cover of the level-`k` cells from `g` on, by blocks read through their own entries;
the next block starts where the one just read ends; stops after the block reaching past `ib` -/
def dcov (top : ℕ) (bk : ℕ → ℕ) (k ib : ℕ) (fuel : ℕ) : ℕ → ℕ :=
  Nat.rec (motive := fun _ => ℕ → ℕ) (fun _ => 0)
    (fun _ ih g =>
      let t := alignK4 g ib
      let h := Nat.shiftRight g t
      let v := forceR (Nat.add k t) fun l => forceR h fun h => entry top bk l h
      let g' := Nat.shiftLeft (Nat.add h 1) t
      Bool.rec (motive := fun _ => ℕ) v (nmin v (ih g')) (Nat.ble g' ib))
    fuel

/-- 4-bit bit lengths of `0 .. 255` -/
def BL8 : ℕ := 0x8888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888877777777777777777777777777777777777777777777777777777777777777776666666666666666666666666666666655555555555555554444444433332210

/-- the cover level: the bit length of `x < 2^16` (any value is sound) -/
def blen (x : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => ℕ) (Nat.land (Nat.shiftRight BL8 (Nat.mul 4 x)) 15)
    (Nat.add 8 (Nat.land (Nat.shiftRight BL8 (Nat.mul 4 (Nat.shiftRight x 8))) 15)) (Nat.ble 256 x)

/-- the lower-bound oracle: `lb top bk lo hi / 10¹⁰ ≤ wfun x` on `[lo, hi] / 2^15` (0 when `hi ≤ lo` or `2^19 < hi`) -/
def lb (top : ℕ) (bk : ℕ → ℕ) (lo hi : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => ℕ)
    (Bool.rec (motive := fun _ => ℕ)
      (let k := blen (Nat.shiftRight (Nat.sub hi lo) 5)
       dcov top bk k (Nat.shiftRight (Nat.sub hi 1) k) 14 (Nat.shiftRight lo k))
      0 (Nat.ble 524289 hi))
    0 (Nat.ble hi lo)

/-! ### verification of a table -/

/-- `f i` for every `i < n` -/
def allBelow (n : ℕ) (f : ℕ → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun k ih => Bool.rec (motive := fun _ => Bool) false (f k) ih) n

/-- `f (a + i)` for every `i < n` -/
def allFrom (a n : ℕ) (f : ℕ → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun k ih => Bool.rec (motive := fun _ => Bool) false (f (Nat.add a k)) ih) n

/-- the integer cell of the level-`l` cell `i` (endpoints packed as `LN * KB + UN`) -/
def cellAt (l i : ℕ) : CellN := ⟨Nat.add (Nat.mul (Nat.shiftLeft i l) KB) (Nat.shiftLeft (Nat.add i 1) l), 0⟩

/-- the integer cell bound `CellN.okC`, and the claim `v / 10¹⁰` below the bound it certifies -/
def cellOkCore (c : CellN) (v : ℕ) : Bool :=
  c.okC && decide (((Nat.mul v 1000 : ℕ) : ℤ) * c.DHIZ * c.DHIZ ≤ c.NLOZ * c.NLOZ * SW)

/-- the claim `v` on the level-`l` cell `i` passes the integer cell bound (or is `0`) -/
def cellOk (l i v : ℕ) : Bool :=
  Bool.rec (motive := fun _ => Bool)
    (Bool.rec (motive := fun _ => Bool) false (cellOkCore (cellAt l i) v) (Nat.ble (Nat.add (Nat.shiftLeft (Nat.add i 1) l) 1) KB))
    true (Nat.beq v 0)

/-- a block constant: its finest cells pass the cell bound, every coarser entry is at most its children -/
def blockOkX (X j : ℕ) : Bool :=
  let r := Nat.land X 31
  let D := Nat.sub 10 r
  let Y := Nat.shiftRight X 5
  Nat.ble r 10
    && allBelow (Nat.shiftLeft 1 D) (fun t => cellOk r (Nat.add (Nat.shiftLeft j D) t) (fld Y (Nat.add (Nat.sub (Nat.shiftLeft 1 D) 1) t)))
    && allBelow D (fun d => allBelow (Nat.shiftLeft 1 d) (fun t =>
         Nat.ble (fld Y (Nat.add (Nat.sub (Nat.shiftLeft 1 d) 1) t))
           (nmin (fld Y (Nat.add (Nat.sub (Nat.shiftLeft 1 (Nat.add d 1)) 1) (Nat.mul 2 t)))
                 (fld Y (Nat.add (Nat.sub (Nat.shiftLeft 1 (Nat.add d 1)) 1) (Nat.add (Nat.mul 2 t) 1))))))

def blockOk (X j : ℕ) : Bool := Bool.rec (motive := fun _ => Bool) (blockOkX X j) true (Nat.beq X 0)

/-- the entry of the level-`l` cell `i` for `10 ≤ l ≤ 19` as the top levels read it (level 10: the block's own) -/
def topv (top : ℕ) (bk : ℕ → ℕ) (l i : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => ℕ) (fld top (Nat.add (Nat.shiftLeft 1 (Nat.sub 19 l)) i)) (fld (Nat.shiftRight (bk i) 5) 0) (Nat.beq l 10)

/-- every top entry (levels 11..19) is at most its two children -/
def topOk (top : ℕ) (bk : ℕ → ℕ) : Bool :=
  allFrom 11 9 fun l => allBelow (Nat.shiftLeft 1 (Nat.sub 19 l)) fun i =>
    Nat.ble (fld top (Nat.add (Nat.shiftLeft 1 (Nat.sub 19 l)) i))
      (nmin (topv top bk (Nat.sub l 1) (Nat.mul 2 i)) (topv top bk (Nat.sub l 1) (Nat.add (Nat.mul 2 i) 1)))

/-! ### soundness -/

theorem forceR_eq (a : ℕ) (k : ℕ → ℕ) : forceR a k = k a := by cases a <;> rfl

theorem nmin_eq (a b : ℕ) : nmin a b = min a b := by
  unfold nmin
  cases h : Nat.ble a b
  · have : ¬ a ≤ b := by rw [← Nat.ble_eq, h]; decide
    show b = min a b; omega
  · have : a ≤ b := by rw [← Nat.ble_eq, h]
    show a = min a b; omega

theorem allBelow_spec {n : ℕ} {f : ℕ → Bool} (h : allBelow n f = true) : ∀ i < n, f i = true := by
  induction n with
  | zero => intro i hi; omega
  | succ n ih =>
    have h' : Bool.rec (motive := fun _ => Bool) false (f n) (allBelow n f) = true := h
    cases hb : allBelow n f
    · rw [hb] at h'; exact absurd (show (false : Bool) = true from h') (by decide)
    · rw [hb] at h'
      intro i hi
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | hi
      · exact ih hb i hi
      · subst hi; exact h'

theorem allFrom_spec {a n : ℕ} {f : ℕ → Bool} (h : allFrom a n f = true) : ∀ i < n, f (a + i) = true := by
  induction n with
  | zero => intro i hi; omega
  | succ n ih =>
    have h' : Bool.rec (motive := fun _ => Bool) false (f (Nat.add a n)) (allFrom a n f) = true := h
    cases hb : allFrom a n f
    · rw [hb] at h'; exact absurd (show (false : Bool) = true from h') (by decide)
    · rw [hb] at h'
      intro i hi
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | hi
      · exact ih hb i hi
      · subst hi; exact h'


theorem allFrom_add {a n m : ℕ} {f : ℕ → Bool} (h1 : allFrom a n f = true) (h2 : allFrom (a + n) m f = true) :
    allFrom a (n + m) f = true := by
  induction m with
  | zero => exact h1
  | succ m ih =>
    have h2' : Bool.rec (motive := fun _ => Bool) false (f (Nat.add (a + n) m)) (allFrom (a + n) m f) = true := h2
    cases hb : allFrom (a + n) m f
    · rw [hb] at h2'; exact absurd (show (false : Bool) = true from h2') (by decide)
    · rw [hb] at h2'
      have h3 := ih hb
      show Bool.rec (motive := fun _ => Bool) false (f (Nat.add a (n + m))) (allFrom a (n + m) f) = true
      rw [h3]
      have e : Nat.add a (n + m) = Nat.add (a + n) m := by simp only [Nat.add_eq]; omega
      rw [e]; exact h2'

/-- all `512` blocks verified, from a verified run `allFrom 0 512` -/
theorem blocks_of {bk : ℕ → ℕ} (h : allFrom 0 512 (fun j => blockOk (bk j) j) = true) :
    ∀ j < 512, blockOk (bk j) j = true := by
  intro j hj
  have := allFrom_spec h j hj
  simpa using this

/-- `v / 10¹⁰` bounds `wfun` below on the level-`l` cell `i`, i.e. on `[i 2^l, (i+1) 2^l] / 2^15` -/
def CS (l i v : ℕ) : Prop :=
  ∀ x : ℝ, ((i * 2 ^ l : ℕ) : ℝ) / SC ≤ x → x ≤ (((i + 1) * 2 ^ l : ℕ) : ℝ) / SC → (v : ℝ) / 10000000000 ≤ wfun x

theorem CS_zero (l i : ℕ) : CS l i 0 := by
  intro x _ _; simp only [Nat.cast_zero, zero_div]; exact wfun_nonneg x

theorem CS_mono {l i v v' : ℕ} (hv : v' ≤ v) (h : CS l i v) : CS l i v' := by
  intro x h1 h2
  exact le_trans (div_le_div_of_nonneg_right (by exact_mod_cast hv) (by norm_num)) (h x h1 h2)

theorem SC_posR : (0:ℝ) < SC := by norm_num [SC]

theorem castdiv_le {a b : ℕ} (h : a ≤ b) : (a : ℝ) / SC ≤ (b : ℝ) / SC :=
  div_le_div_of_nonneg_right (by exact_mod_cast h) SC_posR.le

theorem CS_min {l i a b : ℕ} (ha : CS l (2 * i) a) (hb : CS l (2 * i + 1) b) : CS (l + 1) i (min a b) := by
  intro x h1 h2
  have e1 : (2 * i) * 2 ^ l = i * 2 ^ (l + 1) := by rw [pow_succ]; ring
  have e2 : (2 * i + 1 + 1) * 2 ^ l = (i + 1) * 2 ^ (l + 1) := by rw [pow_succ]; ring
  rcases le_total x ((((2 * i + 1) * 2 ^ l : ℕ) : ℝ) / SC) with hx | hx
  · have := ha x (by rw [e1]; exact h1) hx
    exact le_trans (div_le_div_of_nonneg_right (by exact_mod_cast min_le_left a b) (by norm_num)) this
  · have := hb x hx (by rw [e2]; exact h2)
    exact le_trans (div_le_div_of_nonneg_right (by exact_mod_cast min_le_right a b) (by norm_num)) this

theorem CS_anc {l m i v : ℕ} (h : CS (l + m) (i / 2 ^ m) v) : CS l i v := by
  intro x h1 h2
  have hp : 0 < 2 ^ m := by positivity
  apply h x
  · refine le_trans (castdiv_le ?_) h1
    calc (i / 2 ^ m) * 2 ^ (l + m) = ((i / 2 ^ m) * 2 ^ m) * 2 ^ l := by rw [pow_add]; ring
      _ ≤ i * 2 ^ l := Nat.mul_le_mul_right _ (Nat.div_mul_le_self i (2 ^ m))
  · refine le_trans h2 (castdiv_le ?_)
    have hq : i + 1 ≤ (i / 2 ^ m + 1) * 2 ^ m := by
      have h3 := Nat.div_add_mod i (2 ^ m); have h4 := Nat.mod_lt i hp; nlinarith
    calc (i + 1) * 2 ^ l ≤ ((i / 2 ^ m + 1) * 2 ^ m) * 2 ^ l := Nat.mul_le_mul_right _ hq
      _ = (i / 2 ^ m + 1) * 2 ^ (l + m) := by rw [pow_add]; ring

/-- a cell claim that passes `cellOk` is sound -/
theorem cellOk_sound {l i v : ℕ} (h : cellOk l i v = true) : CS l i v := by
  unfold cellOk at h
  cases hv : Nat.beq v 0
  · rw [hv] at h
    cases hK : Nat.ble (Nat.add (Nat.shiftLeft (Nat.add i 1) l) 1) KB
    · rw [hK] at h; exact absurd (show (false : Bool) = true from h) (by decide)
    · rw [hK] at h
      have h' : cellOkCore (cellAt l i) v = true := h
      simp only [cellOkCore, Bool.and_eq_true, decide_eq_true_eq] at h'
      obtain ⟨hc, hW⟩ := h'
      have hK' : (i + 1) * 2 ^ l < KB := by
        rw [Nat.ble_eq] at hK
        simp only [Nat.add_eq, Nat.shiftLeft_eq', Nat.shiftLeft_eq] at hK; omega
      have hLN : (cellAt l i).LN = i * 2 ^ l := by
        simp only [cellAt, CellN.LN, Nat.add_eq, Nat.mul_eq, Nat.shiftLeft_eq', Nat.shiftLeft_eq]
        rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by norm_num [KB]), Nat.div_eq_of_lt hK', Nat.zero_add]
      have hUN : (cellAt l i).UN = (i + 1) * 2 ^ l := by
        simp only [cellAt, CellN.UN, Nat.add_eq, Nat.mul_eq, Nat.shiftLeft_eq', Nat.shiftLeft_eq]
        rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hK']
      intro x h1 h2
      have := cellN_soundZ' (cellAt l i) (Nat.mul v 1000) hc hW x (by rw [hLN]; exact h1) (by rw [hUN]; exact h2)
      have e : ((Nat.mul v 1000 : ℕ) : ℝ) / SW = (v : ℝ) / 10000000000 := by
        simp only [Nat.mul_eq]; push_cast; norm_num [SW]; ring
      rw [e] at this; exact this
  · have : v = 0 := by rw [← Nat.beq_eq, hv]
    subst this; exact CS_zero l i

theorem fld_zero (i : ℕ) : fld 0 i = 0 := by
  simp [fld]

/-- what a verified block constant guarantees: every stored entry bounds its cell -/
def BlockSound (X j : ℕ) : Prop :=
  X % 32 ≤ 10 ∧ ∀ d, d ≤ 10 - X % 32 → ∀ t < 2 ^ d, CS (10 - d) (j * 2 ^ d + t) (fld (X / 32) (2 ^ d - 1 + t))

theorem blockOkX_sound {X j : ℕ} (h : blockOkX X j = true) : BlockSound X j := by
  have hr : Nat.land X 31 = X % 32 := by
    rw [Nat.land_eq, show (31:ℕ) = 2 ^ 5 - 1 by norm_num, Nat.and_two_pow_sub_one_eq_mod]
  have hY : Nat.shiftRight X 5 = X / 32 := by rw [Nat.shiftRight_eq', Nat.shiftRight_eq_div_pow]
  unfold blockOkX at h
  simp only [hr, hY, Bool.and_eq_true, Nat.ble_eq] at h
  obtain ⟨⟨h10, hfin⟩, hint⟩ := h
  refine ⟨h10, ?_⟩
  set D := Nat.sub 10 (X % 32) with hD
  have hD' : D = 10 - X % 32 := rfl
  have hfin' := allBelow_spec hfin
  have hint' := allBelow_spec hint
  -- downward induction on the depth
  suffices key : ∀ e, e ≤ D → ∀ t < 2 ^ (D - e), CS (10 - (D - e)) (j * 2 ^ (D - e) + t) (fld (X / 32) (2 ^ (D - e) - 1 + t)) by
    intro d hd t ht
    have := key (D - d) (Nat.sub_le _ _) t (by rw [Nat.sub_sub_self (by omega)]; exact ht)
    rwa [Nat.sub_sub_self (by omega)] at this
  intro e
  induction e with
  | zero =>
    intro _ t ht
    have := hfin' t (by simp only [Nat.shiftLeft_eq', Nat.shiftLeft_eq, one_mul]; simpa using ht)
    simp only [Nat.sub_zero]
    have hc := cellOk_sound this
    simp only [Nat.add_eq, Nat.shiftLeft_eq', Nat.shiftLeft_eq, one_mul, Nat.sub_eq] at hc
    have e10 : 10 - D = X % 32 := by omega
    rw [e10]; exact hc
  | succ e ih =>
    intro he t ht
    set d := D - (e + 1) with hd
    have hdD : d < D := by omega
    have hde : D - e = d + 1 := by omega
    have hc := hint' d hdD
    have hct := allBelow_spec hc t (by simp only [Nat.shiftLeft_eq', Nat.shiftLeft_eq, one_mul]; exact ht)
    simp only [Nat.ble_eq, nmin_eq, Nat.add_eq, Nat.sub_eq, Nat.mul_eq, Nat.shiftLeft_eq', Nat.shiftLeft_eq, one_mul] at hct
    have h0 := ih (by omega) (2 * t) (by rw [hde, pow_succ]; omega)
    have h1 := ih (by omega) (2 * t + 1) (by rw [hde, pow_succ]; omega)
    rw [hde] at h0 h1
    have e0 : j * 2 ^ (d + 1) + 2 * t = 2 * (j * 2 ^ d + t) := by rw [pow_succ]; ring
    have e1 : j * 2 ^ (d + 1) + (2 * t + 1) = 2 * (j * 2 ^ d + t) + 1 := by rw [pow_succ]; ring
    rw [e0] at h0; rw [e1] at h1
    have hlev : 10 - (d + 1) + 1 = 10 - d := by omega
    have hm := CS_min h0 h1
    rw [hlev] at hm
    refine CS_mono ?_ hm
    have a0 : 2 ^ (d + 1) - 1 + 2 * t = 2 ^ (d + 1) - 1 + 2 * t := rfl
    exact hct

theorem blockOk_sound {X j : ℕ} (h : blockOk X j = true) : BlockSound X j := by
  unfold blockOk at h
  cases hX : Nat.beq X 0
  · rw [hX] at h
    exact blockOkX_sound h
  · have : X = 0 := by rw [← Nat.beq_eq, hX]
    subst this
    refine ⟨by norm_num, fun d _ t _ => ?_⟩
    simp only [Nat.zero_div, fld_zero]; exact CS_zero _ _

theorem topv_ten (top : ℕ) (bk : ℕ → ℕ) (i : ℕ) : topv top bk 10 i = fld (bk i / 32) 0 := by
  unfold topv
  rw [show Nat.beq 10 10 = true from rfl, Nat.shiftRight_eq', Nat.shiftRight_eq_div_pow]

theorem topv_top (top : ℕ) (bk : ℕ → ℕ) {l : ℕ} (hl : l ≠ 10) (i : ℕ) :
    topv top bk l i = fld top (2 ^ (19 - l) + i) := by
  unfold topv
  have : Nat.beq l 10 = false := by
    cases h : Nat.beq l 10
    · rfl
    · exact absurd (by rw [← Nat.beq_eq, h]) hl
  rw [this]
  simp only [Nat.add_eq, Nat.sub_eq, Nat.shiftLeft_eq', Nat.shiftLeft_eq, one_mul]

/-- the top levels and the blocks' own entries bound their cells -/
theorem top_sound {top : ℕ} {bk : ℕ → ℕ} (hb : ∀ j < 512, blockOk (bk j) j = true) (ht : topOk top bk = true) :
    ∀ e, e ≤ 9 → ∀ i < 2 ^ (9 - e), CS (10 + e) i (topv top bk (10 + e) i) := by
  have ht' := allFrom_spec ht
  intro e
  induction e with
  | zero =>
    intro _ i hi
    rw [Nat.add_zero, topv_ten]
    have hB := blockOk_sound (hb i (by simpa using hi))
    have := hB.2 0 (Nat.zero_le _) 0 (by norm_num)
    simpa using this
  | succ e ih =>
    intro he i hi
    have hl := ht' e (by omega) |> allBelow_spec
    have hle := hl i (by simp only [Nat.shiftLeft_eq', Nat.shiftLeft_eq, one_mul, Nat.sub_eq, Nat.add_eq]; convert hi using 2; omega)
    simp only [Nat.ble_eq, nmin_eq, Nat.add_eq, Nat.sub_eq, Nat.mul_eq, Nat.shiftLeft_eq', Nat.shiftLeft_eq, one_mul] at hle
    have e1 : 11 + e - 1 = 10 + e := by omega
    rw [e1] at hle
    have h0 := ih (by omega) (2 * i) (by rw [show 9 - e = 9 - (e + 1) + 1 by omega, pow_succ]; omega)
    have h1 := ih (by omega) (2 * i + 1) (by rw [show 9 - e = 9 - (e + 1) + 1 by omega, pow_succ]; omega)
    have hm := CS_min h0 h1
    rw [show 10 + e + 1 = 10 + (e + 1) by omega] at hm
    rw [topv_top top bk (by omega)]
    refine CS_mono ?_ hm
    rw [show 19 - (10 + (e + 1)) = 19 - (11 + e) by omega]
    exact hle

/-- every entry the oracle reads bounds its cell -/
theorem entry_sound {top : ℕ} {bk : ℕ → ℕ} (hb : ∀ j < 512, blockOk (bk j) j = true) (ht : topOk top bk = true)
    (l i : ℕ) (hi : l ≤ 19 → i < 2 ^ (19 - l)) : CS l i (entry top bk l i) := by
  unfold entry
  cases h11 : Nat.ble 11 l
  · -- a block level
    have hl : l ≤ 10 := by
      have : ¬ 11 ≤ l := by rw [← Nat.ble_eq, h11]; decide
      omega
    show CS l i (forceR (Nat.shiftRight i (Nat.sub 10 l)) fun j => entB (bk j) l i j)
    rw [forceR_eq]
    set j := Nat.shiftRight i (Nat.sub 10 l) with hj
    have hj' : j = i / 2 ^ (10 - l) := by rw [hj, Nat.shiftRight_eq', Nat.shiftRight_eq_div_pow]; rfl
    have hj512 : j < 512 := by
      rw [hj']
      have hi' := hi (by omega)
      rw [Nat.div_lt_iff_lt_mul (by positivity), show (512:ℕ) = 2 ^ 9 by norm_num, ← pow_add]
      rwa [show 9 + (10 - l) = 19 - l by omega]
    have hB := blockOk_sound (hb j hj512)
    set X := bk j
    unfold entB
    have hr : Nat.land X 31 = X % 32 := by
      rw [Nat.land_eq, show (31:ℕ) = 2 ^ 5 - 1 by norm_num, Nat.and_two_pow_sub_one_eq_mod]
    simp only [hr]
    set r := X % 32
    have hr10 : r ≤ 10 := hB.1
    -- kk = max l r
    have hkk : Bool.rec (motive := fun _ => ℕ) l r (Nat.ble l r) = max l r := by
      cases hc : Nat.ble l r
      · have : ¬ l ≤ r := by rw [← Nat.ble_eq, hc]; decide
        show l = max l r; omega
      · have : l ≤ r := by rw [← Nat.ble_eq, hc]
        show r = max l r; omega
    simp only [hkk]
    set kk := max l r with hkkdef
    have hkk10 : kk ≤ 10 := by omega
    have hlkk : l ≤ kk := le_max_left _ _
    set d := Nat.sub 10 kk with hd
    have hd' : d = 10 - kk := rfl
    set q := i / 2 ^ (kk - l) with hq
    have hqj : q / 2 ^ d = j := by
      rw [hq, hj', Nat.div_div_eq_div_mul, ← pow_add]
      congr 2; omega
    have ht' : q % 2 ^ d < 2 ^ d := Nat.mod_lt _ (by positivity)
    have hidx : Nat.add (Nat.sub (Nat.shiftLeft 1 d) 1) (Nat.sub (Nat.shiftRight i (Nat.sub kk l)) (Nat.shiftLeft j d))
        = 2 ^ d - 1 + q % 2 ^ d := by
      simp only [Nat.add_eq, Nat.sub_eq, Nat.shiftLeft_eq', Nat.shiftLeft_eq, one_mul, Nat.shiftRight_eq',
        Nat.shiftRight_eq_div_pow]
      rw [← hq]
      have := Nat.div_add_mod' q (2 ^ d)
      rw [hqj] at this
      congr 1; omega
    have hY : Nat.shiftRight X 5 = X / 32 := by rw [Nat.shiftRight_eq', Nat.shiftRight_eq_div_pow]
    rw [hidx, hY]
    have hcs := hB.2 d (by omega) (q % 2 ^ d) ht'
    have e1 : j * 2 ^ d + q % 2 ^ d = q := by
      have := Nat.div_add_mod' q (2 ^ d); rw [hqj] at this; omega
    rw [e1, show 10 - d = l + (kk - l) by omega] at hcs
    exact CS_anc hcs
  · cases h20 : Nat.ble 20 l
    · have hl : 11 ≤ l := by rw [← Nat.ble_eq, h11]
      have hl' : l ≤ 19 := by
        have : ¬ 20 ≤ l := by rw [← Nat.ble_eq, h20]; decide
        omega
      show CS l i (fld top (Nat.add (Nat.shiftLeft 1 (Nat.sub 19 l)) i))
      have := top_sound hb ht (l - 10) (by omega) i (by rw [show 9 - (l - 10) = 19 - l by omega]; exact hi hl')
      rw [show 10 + (l - 10) = l by omega, topv_top top bk (by omega)] at this
      simpa only [Nat.add_eq, Nat.sub_eq, Nat.shiftLeft_eq', Nat.shiftLeft_eq, one_mul] using this
    · exact CS_zero l i

/-- the cover of the level-`k` cells `g .. ib` reads only cells that hold sound entries -/
theorem dcov_sound {top : ℕ} {bk : ℕ → ℕ} (hb : ∀ j < 512, blockOk (bk j) j = true) (ht : topOk top bk = true)
    (k ib : ℕ) (hk : k ≤ 19 → (ib + 1) * 2 ^ k ≤ 2 ^ 19) :
    ∀ fuel g, g ≤ ib → ∀ x : ℝ, ((g * 2 ^ k : ℕ) : ℝ) / SC ≤ x → x ≤ (((ib + 1) * 2 ^ k : ℕ) : ℝ) / SC →
      (dcov top bk k ib fuel g : ℝ) / 10000000000 ≤ wfun x := by
  intro fuel
  induction fuel with
  | zero =>
    intro g _ x _ _
    show ((0 : ℕ) : ℝ) / 10000000000 ≤ wfun x
    simp only [Nat.cast_zero, zero_div]; exact wfun_nonneg x
  | succ fuel ih =>
    intro g hg x h1 h2
    show ((let t := alignK4 g ib
      let h := Nat.shiftRight g t
      let v := forceR (Nat.add k t) fun l => forceR h fun h => entry top bk l h
      let g' := Nat.shiftLeft (Nat.add h 1) t
      Bool.rec (motive := fun _ => ℕ) v (nmin v (dcov top bk k ib fuel g')) (Nat.ble g' ib) : ℕ) : ℝ) / 10000000000 ≤ wfun x
    simp only [forceR_eq]
    set t := alignK4 g ib
    set h := Nat.shiftRight g t with hh
    have hh' : h = g / 2 ^ t := by rw [hh, Nat.shiftRight_eq', Nat.shiftRight_eq_div_pow]
    set g' := Nat.shiftLeft (Nat.add h 1) t with hg'
    have hg'' : g' = (h + 1) * 2 ^ t := by rw [hg', Nat.shiftLeft_eq', Nat.shiftLeft_eq]
    -- the block read covers [g, g') at level k
    have hcell : CS (Nat.add k t) h (entry top bk (Nat.add k t) h) := by
      apply entry_sound hb ht
      intro hkt
      have hk' : k ≤ 19 := by simp only [Nat.add_eq] at hkt; omega
      have hgib : g * 2 ^ k < 2 ^ 19 := by
        have := hk hk'
        calc g * 2 ^ k < (ib + 1) * 2 ^ k := Nat.mul_lt_mul_of_pos_right (by omega) (by positivity)
          _ ≤ 2 ^ 19 := this
      rw [hh', Nat.div_lt_iff_lt_mul (by positivity)]
      have e : 2 ^ (19 - Nat.add k t) * 2 ^ t * 2 ^ k = 2 ^ 19 := by
        rw [← pow_add, ← pow_add]; congr 1; simp only [Nat.add_eq] at hkt ⊢; omega
      by_contra hcon
      push_neg at hcon
      have := Nat.mul_le_mul_right (2 ^ k) hcon
      rw [e] at this; omega
    have hcellx : ∀ y : ℝ, ((g * 2 ^ k : ℕ) : ℝ) / SC ≤ y → y ≤ ((g' * 2 ^ k : ℕ) : ℝ) / SC →
        (entry top bk (Nat.add k t) h : ℝ) / 10000000000 ≤ wfun y := by
      intro y hy1 hy2
      apply hcell y
      · refine le_trans (castdiv_le ?_) hy1
        rw [hh', Nat.add_eq, pow_add]
        calc g / 2 ^ t * (2 ^ k * 2 ^ t) = (g / 2 ^ t * 2 ^ t) * 2 ^ k := by ring
          _ ≤ g * 2 ^ k := Nat.mul_le_mul_right _ (Nat.div_mul_le_self g _)
      · refine le_trans hy2 (castdiv_le (le_of_eq ?_))
        rw [hg'', Nat.add_eq, pow_add]; ring
    cases hc : Nat.ble g' ib
    · -- the block reaches past ib
      have hgt : ib + 1 ≤ g' := by
        have : ¬ g' ≤ ib := by rw [← Nat.ble_eq, hc]; decide
        omega
      exact hcellx x h1 (le_trans h2 (castdiv_le (Nat.mul_le_mul_right _ hgt)))
    · have hle : g' ≤ ib := by rw [← Nat.ble_eq, hc]
      show ((nmin _ _ : ℕ) : ℝ) / 10000000000 ≤ wfun x
      rw [nmin_eq]
      rcases le_total x ((((g' * 2 ^ k : ℕ) : ℝ)) / SC) with hx | hx
      · exact le_trans (div_le_div_of_nonneg_right (by exact_mod_cast min_le_left _ _) (by norm_num)) (hcellx x h1 hx)
      · exact le_trans (div_le_div_of_nonneg_right (by exact_mod_cast min_le_right _ _) (by norm_num)) (ih g' hle x hx h2)

/-- the oracle's soundness: what a verified table certifies -/
def LBSound (top : ℕ) (bk : ℕ → ℕ) : Prop :=
  ∀ lo hi : ℕ, ∀ x : ℝ, (lo : ℝ) / SC ≤ x → x ≤ (hi : ℝ) / SC → (lb top bk lo hi : ℝ) / 10000000000 ≤ wfun x

theorem lb_sound {top : ℕ} {bk : ℕ → ℕ} (hb : ∀ j < 512, blockOk (bk j) j = true) (ht : topOk top bk = true) :
    LBSound top bk := by
  intro lo hi x h1 h2
  unfold lb
  cases hlo : Nat.ble hi lo
  · cases hhi : Nat.ble 524289 hi
    · have hlh : lo < hi := by
        have : ¬ hi ≤ lo := by rw [← Nat.ble_eq, hlo]; decide
        omega
      have hhi' : hi ≤ 524288 := by
        have : ¬ 524289 ≤ hi := by rw [← Nat.ble_eq, hhi]; decide
        omega
      show ((dcov top bk (blen (Nat.shiftRight (Nat.sub hi lo) 5)) (Nat.shiftRight (Nat.sub hi 1) (blen (Nat.shiftRight (Nat.sub hi lo) 5))) 14
        (Nat.shiftRight lo (blen (Nat.shiftRight (Nat.sub hi lo) 5))) : ℕ) : ℝ) / 10000000000 ≤ wfun x
      set k := blen (Nat.shiftRight (Nat.sub hi lo) 5)
      simp only [Nat.shiftRight_eq', Nat.shiftRight_eq_div_pow, Nat.sub_eq]
      have hp : 0 < 2 ^ k := by positivity
      apply dcov_sound hb ht k ((hi - 1) / 2 ^ k)
      · intro hk
        have : (hi - 1) / 2 ^ k < 2 ^ (19 - k) := by
          rw [Nat.div_lt_iff_lt_mul hp, ← pow_add, show 19 - k + k = 19 by omega]; norm_num; omega
        calc ((hi - 1) / 2 ^ k + 1) * 2 ^ k ≤ 2 ^ (19 - k) * 2 ^ k := Nat.mul_le_mul_right _ this
          _ = 2 ^ 19 := by rw [← pow_add]; congr 1; omega
      · exact Nat.div_le_div_right (by omega)
      · exact le_trans (castdiv_le (Nat.div_mul_le_self lo _)) h1
      · refine le_trans h2 (castdiv_le ?_)
        have h5 := Nat.lt_div_mul_add (a := hi - 1) hp
        have e : ((hi - 1) / 2 ^ k + 1) * 2 ^ k = (hi - 1) / 2 ^ k * 2 ^ k + 2 ^ k := by ring
        rw [e]
        generalize (hi - 1) / 2 ^ k * 2 ^ k = A at h5 ⊢
        generalize 2 ^ k = P at h5 ⊢
        omega
    · simp only [Nat.cast_zero, zero_div]; exact wfun_nonneg x
  · simp only [Nat.cast_zero, zero_div]; exact wfun_nonneg x

end Zeta23Ext.Bridge.ThreePoint.Pyr

end


/-! ###### the 6-point weighted certificate `SixW25P` on the pyramid oracle: leaf test, walk, cover ###### -/

noncomputable section

namespace Zeta23Ext.Bridge.ThreePoint.SixW25P

open Zeta23Ext.Bridge.ThreePoint Zeta23Ext.Bridge.ThreePoint.Pyr

def SA : ℕ := 100000000
def cN : ℕ := 349330

/-- the weighted functional on the gaps, in real form -/
def G (g0 g1 g2 g3 g4 : ℝ) : ℝ :=
  (24896 / (SA:ℝ)) * g0 + (42034 / (SA:ℝ)) * g1 + (46137 / (SA:ℝ)) * g2 + (42034 / (SA:ℝ)) * g3 + (24896 / (SA:ℝ)) * g4
    + (25326800 / (SA:ℝ)) * wfun (g0) + (62369200 / (SA:ℝ)) * wfun (g0 + g1) + (40126500 / (SA:ℝ)) * wfun (g0 + g1 + g2) + (99999900 / (SA:ℝ)) * wfun (g0 + g1 + g2 + g3) + (200000000 / (SA:ℝ)) * wfun (g0 + g1 + g2 + g3 + g4) + (48244400 / (SA:ℝ)) * wfun (g1) + (37630700 / (SA:ℝ)) * wfun (g1 + g2) + (119746800 / (SA:ℝ)) * wfun (g1 + g2 + g3) + (99999900 / (SA:ℝ)) * wfun (g1 + g2 + g3 + g4) + (52857300 / (SA:ℝ)) * wfun (g2) + (37630700 / (SA:ℝ)) * wfun (g2 + g3) + (40126500 / (SA:ℝ)) * wfun (g2 + g3 + g4) + (48244400 / (SA:ℝ)) * wfun (g3) + (62369200 / (SA:ℝ)) * wfun (g3 + g4) + (25326800 / (SA:ℝ)) * wfun (g4)

/-- early exit: `true` once the running sum `s` reaches `C`, else the rest of the test -/
def ee (C s : ℕ) (rest : Bool) : Bool := Bool.rec (motive := fun _ => Bool) rest true (Nat.ble C s)

/-- the leaf test `cN·SC·U ≤ U·Σ b_r l_r + SC·Σ a_t lb_t` (U = 10¹⁰), the terms added in a fixed order and the
running sum tested after each -/
def leafOK (top : ℕ) (bk : ℕ → ℕ) (l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 : ℕ) : Bool :=
  let s0 := Nat.mul (Nat.add (Nat.add (Nat.add (Nat.add (Nat.mul 24896 l0) (Nat.mul 42034 l1)) (Nat.mul 46137 l2)) (Nat.mul 42034 l3)) (Nat.mul 24896 l4)) 10000000000
  ee 114468454400000000000 s0 (
  let s1 := Nat.add s0 (Nat.mul 1580872499200 (lb top bk l1 u1))
  ee 114468454400000000000 s1 (
  let s2 := Nat.add s1 (Nat.mul 1580872499200 (lb top bk l3 u3))
  ee 114468454400000000000 s2 (
  let s3 := Nat.add s2 (Nat.mul 1732028006400 (lb top bk l2 u2))
  ee 114468454400000000000 s3 (
  let s4 := Nat.add s3 (Nat.mul 829908582400 (lb top bk l0 u0))
  ee 114468454400000000000 s4 (
  let s5 := Nat.add s4 (Nat.mul 6553600000000 (lb top bk (Nat.add (Nat.add (Nat.add (Nat.add l0 l1) l2) l3) l4) (Nat.add (Nat.add (Nat.add (Nat.add u0 u1) u2) u3) u4)))
  ee 114468454400000000000 s5 (
  let s6 := Nat.add s5 (Nat.mul 829908582400 (lb top bk l4 u4))
  ee 114468454400000000000 s6 (
  let s7 := Nat.add s6 (Nat.mul 3276796723200 (lb top bk (Nat.add (Nat.add (Nat.add l0 l1) l2) l3) (Nat.add (Nat.add (Nat.add u0 u1) u2) u3)))
  ee 114468454400000000000 s7 (
  let s8 := Nat.add s7 (Nat.mul 3923863142400 (lb top bk (Nat.add (Nat.add l1 l2) l3) (Nat.add (Nat.add u1 u2) u3)))
  ee 114468454400000000000 s8 (
  let s9 := Nat.add s8 (Nat.mul 1314865152000 (lb top bk (Nat.add (Nat.add l0 l1) l2) (Nat.add (Nat.add u0 u1) u2)))
  ee 114468454400000000000 s9 (
  let s10 := Nat.add s9 (Nat.mul 3276796723200 (lb top bk (Nat.add (Nat.add (Nat.add l1 l2) l3) l4) (Nat.add (Nat.add (Nat.add u1 u2) u3) u4)))
  ee 114468454400000000000 s10 (
  let s11 := Nat.add s10 (Nat.mul 2043713945600 (lb top bk (Nat.add l0 l1) (Nat.add u0 u1)))
  ee 114468454400000000000 s11 (
  let s12 := Nat.add s11 (Nat.mul 1314865152000 (lb top bk (Nat.add (Nat.add l2 l3) l4) (Nat.add (Nat.add u2 u3) u4)))
  ee 114468454400000000000 s12 (
  let s13 := Nat.add s12 (Nat.mul 1233082777600 (lb top bk (Nat.add l2 l3) (Nat.add u2 u3)))
  ee 114468454400000000000 s13 (
  let s14 := Nat.add s13 (Nat.mul 2043713945600 (lb top bk (Nat.add l3 l4) (Nat.add u3 u4)))
  ee 114468454400000000000 s14 (
  let s15 := Nat.add s14 (Nat.mul 1233082777600 (lb top bk (Nat.add l1 l2) (Nat.add u1 u2)))
  Nat.ble 114468454400000000000 s15)))))))))))))))

/-- the type of a walk continuation: position and the ten coordinates to the end position (`0` = failure) -/
abbrev WF : Type := ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ

/-- a split on gap 0: the lower half (`u0 := q`) from `pos + 4`, then the upper half from where it ends -/
def split0 (ih : WF) (pos l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 : ℕ) : ℕ :=
  forceR (Nat.shiftRight (Nat.add l0 u0) 1) fun q =>
  let p := ih (Nat.add pos 4) l0 q l1 u1 l2 u2 l3 u3 l4 u4
  Bool.rec (motive := fun _ => ℕ) (ih p q u0 l1 u1 l2 u2 l3 u3 l4 u4) (0) (Nat.beq p 0)

/-- a split on gap 1: the lower half (`u1 := q`) from `pos + 4`, then the upper half from where it ends -/
def split1 (ih : WF) (pos l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 : ℕ) : ℕ :=
  forceR (Nat.shiftRight (Nat.add l1 u1) 1) fun q =>
  let p := ih (Nat.add pos 4) l0 u0 l1 q l2 u2 l3 u3 l4 u4
  Bool.rec (motive := fun _ => ℕ) (ih p l0 u0 q u1 l2 u2 l3 u3 l4 u4) (0) (Nat.beq p 0)

/-- a split on gap 2: the lower half (`u2 := q`) from `pos + 4`, then the upper half from where it ends -/
def split2 (ih : WF) (pos l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 : ℕ) : ℕ :=
  forceR (Nat.shiftRight (Nat.add l2 u2) 1) fun q =>
  let p := ih (Nat.add pos 4) l0 u0 l1 u1 l2 q l3 u3 l4 u4
  Bool.rec (motive := fun _ => ℕ) (ih p l0 u0 l1 u1 q u2 l3 u3 l4 u4) (0) (Nat.beq p 0)

/-- a split on gap 3: the lower half (`u3 := q`) from `pos + 4`, then the upper half from where it ends -/
def split3 (ih : WF) (pos l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 : ℕ) : ℕ :=
  forceR (Nat.shiftRight (Nat.add l3 u3) 1) fun q =>
  let p := ih (Nat.add pos 4) l0 u0 l1 u1 l2 u2 l3 q l4 u4
  Bool.rec (motive := fun _ => ℕ) (ih p l0 u0 l1 u1 l2 u2 q u3 l4 u4) (0) (Nat.beq p 0)

/-- a split on gap 4: the lower half (`u4 := q`) from `pos + 4`, then the upper half from where it ends -/
def split4 (ih : WF) (pos l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 : ℕ) : ℕ :=
  forceR (Nat.shiftRight (Nat.add l4 u4) 1) fun q =>
  let p := ih (Nat.add pos 4) l0 u0 l1 u1 l2 u2 l3 u3 l4 q
  Bool.rec (motive := fun _ => ℕ) (ih p l0 u0 l1 u1 l2 u2 l3 u3 q u4) (0) (Nat.beq p 0)

/-- a split node: the axis selects the gap -/
def splitAx (ih : WF) (pos ax l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) (split4 ih pos l0 u0 l1 u1 l2 u2 l3 u3 l4 u4) (split3 ih pos l0 u0 l1 u1 l2 u2 l3 u3 l4 u4) (Nat.beq ax 3)) (split2 ih pos l0 u0 l1 u1 l2 u2 l3 u3 l4 u4) (Nat.beq ax 2)) (split1 ih pos l0 u0 l1 u1 l2 u2 l3 u3 l4 u4) (Nat.beq ax 1)) (split0 ih pos l0 u0 l1 u1 l2 u2 l3 u3 l4 u4) (Nat.beq ax 0)

/-- a leaf: in the reflected half-space, or the leaf test -/
def leafStep (top : ℕ) (bk : ℕ → ℕ) (pos l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) (0) (Nat.add pos 1) (leafOK top bk l0 u0 l1 u1 l2 u2 l3 u3 l4 u4)) (Nat.add pos 1) (Nat.ble (Nat.add u4 1) l0)

/-- the bisection walk over the ten box coordinates (`Nat.rec` on the fuel): the node code is
`(bits >>> pos) &&& 15` (bit 0 split, bits 1..3 axis); the position after the subtree, `0` on failure -/
def walk (top : ℕ) (bk : ℕ → ℕ) (bits : ℕ) (fuel : ℕ) : WF :=
  Nat.rec (motive := fun _ => WF) (fun _ _ _ _ _ _ _ _ _ _ _ => 0)
    (fun _ ih pos l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 =>
      let w := Nat.land (Nat.shiftRight bits pos) 15
      Bool.rec (motive := fun _ => ℕ) (leafStep top bk pos l0 u0 l1 u1 l2 u2 l3 u3 l4 u4) (splitAx ih pos (Nat.shiftRight w 1) l0 u0 l1 u1 l2 u2 l3 u3 l4 u4) (Nat.beq (Nat.land w 1) 1))
    fuel

/-- the box `[l_r, u_r] / SC` satisfies the certificate inequality (or lies in the reflected half-space) -/
def Covered (l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 : ℕ) : Prop :=
  ∀ g0 g1 g2 g3 g4 : ℝ, (l0 : ℝ) / SC ≤ g0 → g0 ≤ (u0 : ℝ) / SC → (l1 : ℝ) / SC ≤ g1 → g1 ≤ (u1 : ℝ) / SC → (l2 : ℝ) / SC ≤ g2 → g2 ≤ (u2 : ℝ) / SC → (l3 : ℝ) / SC ≤ g3 → g3 ≤ (u3 : ℝ) / SC → (l4 : ℝ) / SC ≤ g4 → g4 ≤ (u4 : ℝ) / SC → (cN : ℝ) / SA ≤ G g0 g1 g2 g3 g4 ∨ g4 < g0

theorem ee_or {C s : ℕ} {rest : Bool} (h : ee C s rest = true) : C ≤ s ∨ rest = true := by
  unfold ee at h
  cases hc : Nat.ble C s
  · rw [hc] at h; exact Or.inr h
  · exact Or.inl (by rw [← Nat.ble_eq, hc])

theorem leafOK_le (top : ℕ) (bk : ℕ → ℕ) (l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 : ℕ) (h : leafOK top bk l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 = true) :
    114468454400000000000 ≤ 10000000000 * (24896 * l0 + 42034 * l1 + 46137 * l2 + 42034 * l3 + 24896 * l4) + 32768 * (25326800 * lb top bk (l0) (u0) + 62369200 * lb top bk (l0 + l1) (u0 + u1) + 40126500 * lb top bk (l0 + l1 + l2) (u0 + u1 + u2) + 99999900 * lb top bk (l0 + l1 + l2 + l3) (u0 + u1 + u2 + u3) + 200000000 * lb top bk (l0 + l1 + l2 + l3 + l4) (u0 + u1 + u2 + u3 + u4) + 48244400 * lb top bk (l1) (u1) + 37630700 * lb top bk (l1 + l2) (u1 + u2) + 119746800 * lb top bk (l1 + l2 + l3) (u1 + u2 + u3) + 99999900 * lb top bk (l1 + l2 + l3 + l4) (u1 + u2 + u3 + u4) + 52857300 * lb top bk (l2) (u2) + 37630700 * lb top bk (l2 + l3) (u2 + u3) + 40126500 * lb top bk (l2 + l3 + l4) (u2 + u3 + u4) + 48244400 * lb top bk (l3) (u3) + 62369200 * lb top bk (l3 + l4) (u3 + u4) + 25326800 * lb top bk (l4) (u4)) := by
  unfold leafOK at h
  dsimp only at h
  rcases ee_or h with h | h
  · simp only [Nat.add_eq, Nat.mul_eq, Nat.ble_eq] at h ⊢; omega
  rcases ee_or h with h | h
  · simp only [Nat.add_eq, Nat.mul_eq, Nat.ble_eq] at h ⊢; omega
  rcases ee_or h with h | h
  · simp only [Nat.add_eq, Nat.mul_eq, Nat.ble_eq] at h ⊢; omega
  rcases ee_or h with h | h
  · simp only [Nat.add_eq, Nat.mul_eq, Nat.ble_eq] at h ⊢; omega
  rcases ee_or h with h | h
  · simp only [Nat.add_eq, Nat.mul_eq, Nat.ble_eq] at h ⊢; omega
  rcases ee_or h with h | h
  · simp only [Nat.add_eq, Nat.mul_eq, Nat.ble_eq] at h ⊢; omega
  rcases ee_or h with h | h
  · simp only [Nat.add_eq, Nat.mul_eq, Nat.ble_eq] at h ⊢; omega
  rcases ee_or h with h | h
  · simp only [Nat.add_eq, Nat.mul_eq, Nat.ble_eq] at h ⊢; omega
  rcases ee_or h with h | h
  · simp only [Nat.add_eq, Nat.mul_eq, Nat.ble_eq] at h ⊢; omega
  rcases ee_or h with h | h
  · simp only [Nat.add_eq, Nat.mul_eq, Nat.ble_eq] at h ⊢; omega
  rcases ee_or h with h | h
  · simp only [Nat.add_eq, Nat.mul_eq, Nat.ble_eq] at h ⊢; omega
  rcases ee_or h with h | h
  · simp only [Nat.add_eq, Nat.mul_eq, Nat.ble_eq] at h ⊢; omega
  rcases ee_or h with h | h
  · simp only [Nat.add_eq, Nat.mul_eq, Nat.ble_eq] at h ⊢; omega
  rcases ee_or h with h | h
  · simp only [Nat.add_eq, Nat.mul_eq, Nat.ble_eq] at h ⊢; omega
  rcases ee_or h with h | h
  · simp only [Nat.add_eq, Nat.mul_eq, Nat.ble_eq] at h ⊢; omega
  simp only [Nat.add_eq, Nat.mul_eq, Nat.ble_eq] at h ⊢; omega

set_option maxHeartbeats 4000000 in
theorem leaf_sound {top : ℕ} {bk : ℕ → ℕ} (hlb : LBSound top bk) (l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 : ℕ) (h : leafOK top bk l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 = true) :
    ∀ g0 g1 g2 g3 g4 : ℝ, (l0 : ℝ) / SC ≤ g0 → g0 ≤ (u0 : ℝ) / SC → (l1 : ℝ) / SC ≤ g1 → g1 ≤ (u1 : ℝ) / SC → (l2 : ℝ) / SC ≤ g2 → g2 ≤ (u2 : ℝ) / SC → (l3 : ℝ) / SC ≤ g3 → g3 ≤ (u3 : ℝ) / SC → (l4 : ℝ) / SC ≤ g4 → g4 ≤ (u4 : ℝ) / SC → (cN : ℝ) / SA ≤ G g0 g1 g2 g3 g4 := by
  intro g0 g1 g2 g3 g4 h01 h02 h11 h12 h21 h22 h31 h32 h41 h42
  have hq0 := leafOK_le top bk l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 h
  have w0 := hlb (l0) (u0) (g0) (by push_cast; (try simp only [add_div]); linarith [h01]) (by push_cast; (try simp only [add_div]); linarith [h02])
  have w1 := hlb (l0 + l1) (u0 + u1) (g0 + g1) (by push_cast; (try simp only [add_div]); linarith [h01, h11]) (by push_cast; (try simp only [add_div]); linarith [h02, h12])
  have w2 := hlb (l0 + l1 + l2) (u0 + u1 + u2) (g0 + g1 + g2) (by push_cast; (try simp only [add_div]); linarith [h01, h11, h21]) (by push_cast; (try simp only [add_div]); linarith [h02, h12, h22])
  have w3 := hlb (l0 + l1 + l2 + l3) (u0 + u1 + u2 + u3) (g0 + g1 + g2 + g3) (by push_cast; (try simp only [add_div]); linarith [h01, h11, h21, h31]) (by push_cast; (try simp only [add_div]); linarith [h02, h12, h22, h32])
  have w4 := hlb (l0 + l1 + l2 + l3 + l4) (u0 + u1 + u2 + u3 + u4) (g0 + g1 + g2 + g3 + g4) (by push_cast; (try simp only [add_div]); linarith [h01, h11, h21, h31, h41]) (by push_cast; (try simp only [add_div]); linarith [h02, h12, h22, h32, h42])
  have w5 := hlb (l1) (u1) (g1) (by push_cast; (try simp only [add_div]); linarith [h11]) (by push_cast; (try simp only [add_div]); linarith [h12])
  have w6 := hlb (l1 + l2) (u1 + u2) (g1 + g2) (by push_cast; (try simp only [add_div]); linarith [h11, h21]) (by push_cast; (try simp only [add_div]); linarith [h12, h22])
  have w7 := hlb (l1 + l2 + l3) (u1 + u2 + u3) (g1 + g2 + g3) (by push_cast; (try simp only [add_div]); linarith [h11, h21, h31]) (by push_cast; (try simp only [add_div]); linarith [h12, h22, h32])
  have w8 := hlb (l1 + l2 + l3 + l4) (u1 + u2 + u3 + u4) (g1 + g2 + g3 + g4) (by push_cast; (try simp only [add_div]); linarith [h11, h21, h31, h41]) (by push_cast; (try simp only [add_div]); linarith [h12, h22, h32, h42])
  have w9 := hlb (l2) (u2) (g2) (by push_cast; (try simp only [add_div]); linarith [h21]) (by push_cast; (try simp only [add_div]); linarith [h22])
  have w10 := hlb (l2 + l3) (u2 + u3) (g2 + g3) (by push_cast; (try simp only [add_div]); linarith [h21, h31]) (by push_cast; (try simp only [add_div]); linarith [h22, h32])
  have w11 := hlb (l2 + l3 + l4) (u2 + u3 + u4) (g2 + g3 + g4) (by push_cast; (try simp only [add_div]); linarith [h21, h31, h41]) (by push_cast; (try simp only [add_div]); linarith [h22, h32, h42])
  have w12 := hlb (l3) (u3) (g3) (by push_cast; (try simp only [add_div]); linarith [h31]) (by push_cast; (try simp only [add_div]); linarith [h32])
  have w13 := hlb (l3 + l4) (u3 + u4) (g3 + g4) (by push_cast; (try simp only [add_div]); linarith [h31, h41]) (by push_cast; (try simp only [add_div]); linarith [h32, h42])
  have w14 := hlb (l4) (u4) (g4) (by push_cast; (try simp only [add_div]); linarith [h41]) (by push_cast; (try simp only [add_div]); linarith [h42])
  have hq := (Nat.cast_le (α := ℝ)).mpr hq0
  push_cast at hq
  have hSC : (0:ℝ) < SC := by norm_num [SC]
  have hU : (0:ℝ) < 10000000000 := by norm_num
  have hSA : (0:ℝ) < SA := by norm_num [SA]
  set L : ℝ := 24896 * ((l0 : ℝ) / SC) + 42034 * ((l1 : ℝ) / SC) + 46137 * ((l2 : ℝ) / SC) + 42034 * ((l3 : ℝ) / SC) + 24896 * ((l4 : ℝ) / SC) with hL
  set Wt : ℝ := 25326800 * ((lb top bk (l0) (u0) : ℝ) / 10000000000) + 62369200 * ((lb top bk (l0 + l1) (u0 + u1) : ℝ) / 10000000000) + 40126500 * ((lb top bk (l0 + l1 + l2) (u0 + u1 + u2) : ℝ) / 10000000000) + 99999900 * ((lb top bk (l0 + l1 + l2 + l3) (u0 + u1 + u2 + u3) : ℝ) / 10000000000) + 200000000 * ((lb top bk (l0 + l1 + l2 + l3 + l4) (u0 + u1 + u2 + u3 + u4) : ℝ) / 10000000000) + 48244400 * ((lb top bk (l1) (u1) : ℝ) / 10000000000) + 37630700 * ((lb top bk (l1 + l2) (u1 + u2) : ℝ) / 10000000000) + 119746800 * ((lb top bk (l1 + l2 + l3) (u1 + u2 + u3) : ℝ) / 10000000000) + 99999900 * ((lb top bk (l1 + l2 + l3 + l4) (u1 + u2 + u3 + u4) : ℝ) / 10000000000) + 52857300 * ((lb top bk (l2) (u2) : ℝ) / 10000000000) + 37630700 * ((lb top bk (l2 + l3) (u2 + u3) : ℝ) / 10000000000) + 40126500 * ((lb top bk (l2 + l3 + l4) (u2 + u3 + u4) : ℝ) / 10000000000) + 48244400 * ((lb top bk (l3) (u3) : ℝ) / 10000000000) + 62369200 * ((lb top bk (l3 + l4) (u3 + u4) : ℝ) / 10000000000) + 25326800 * ((lb top bk (l4) (u4) : ℝ) / 10000000000) with hWt
  have e : (L + Wt) * (SC * 10000000000) = 10000000000 * (24896 * (l0 : ℝ) + 42034 * (l1 : ℝ) + 46137 * (l2 : ℝ) + 42034 * (l3 : ℝ) + 24896 * (l4 : ℝ)) + 32768 * (25326800 * (lb top bk (l0) (u0) : ℝ) + 62369200 * (lb top bk (l0 + l1) (u0 + u1) : ℝ) + 40126500 * (lb top bk (l0 + l1 + l2) (u0 + u1 + u2) : ℝ) + 99999900 * (lb top bk (l0 + l1 + l2 + l3) (u0 + u1 + u2 + u3) : ℝ) + 200000000 * (lb top bk (l0 + l1 + l2 + l3 + l4) (u0 + u1 + u2 + u3 + u4) : ℝ) + 48244400 * (lb top bk (l1) (u1) : ℝ) + 37630700 * (lb top bk (l1 + l2) (u1 + u2) : ℝ) + 119746800 * (lb top bk (l1 + l2 + l3) (u1 + u2 + u3) : ℝ) + 99999900 * (lb top bk (l1 + l2 + l3 + l4) (u1 + u2 + u3 + u4) : ℝ) + 52857300 * (lb top bk (l2) (u2) : ℝ) + 37630700 * (lb top bk (l2 + l3) (u2 + u3) : ℝ) + 40126500 * (lb top bk (l2 + l3 + l4) (u2 + u3 + u4) : ℝ) + 48244400 * (lb top bk (l3) (u3) : ℝ) + 62369200 * (lb top bk (l3 + l4) (u3 + u4) : ℝ) + 25326800 * (lb top bk (l4) (u4) : ℝ)) := by
    rw [hL, hWt]; field_simp; norm_num [SC]; try ring
  have hq' : (cN : ℝ) ≤ L + Wt := by
    refine le_of_mul_le_mul_right ?_ (by positivity : (0:ℝ) < SC * 10000000000)
    rw [e]
    calc (cN : ℝ) * (SC * 10000000000) = 114468454400000000000 := by norm_num [cN, SC]
      _ ≤ _ := hq
  unfold G
  rw [div_le_iff₀ hSA]
  have eG : ((24896 / (SA:ℝ)) * g0 + (42034 / (SA:ℝ)) * g1 + (46137 / (SA:ℝ)) * g2 + (42034 / (SA:ℝ)) * g3 + (24896 / (SA:ℝ)) * g4
      + (25326800 / (SA:ℝ)) * wfun (g0) + (62369200 / (SA:ℝ)) * wfun (g0 + g1) + (40126500 / (SA:ℝ)) * wfun (g0 + g1 + g2) + (99999900 / (SA:ℝ)) * wfun (g0 + g1 + g2 + g3) + (200000000 / (SA:ℝ)) * wfun (g0 + g1 + g2 + g3 + g4) + (48244400 / (SA:ℝ)) * wfun (g1) + (37630700 / (SA:ℝ)) * wfun (g1 + g2) + (119746800 / (SA:ℝ)) * wfun (g1 + g2 + g3) + (99999900 / (SA:ℝ)) * wfun (g1 + g2 + g3 + g4) + (52857300 / (SA:ℝ)) * wfun (g2) + (37630700 / (SA:ℝ)) * wfun (g2 + g3) + (40126500 / (SA:ℝ)) * wfun (g2 + g3 + g4) + (48244400 / (SA:ℝ)) * wfun (g3) + (62369200 / (SA:ℝ)) * wfun (g3 + g4) + (25326800 / (SA:ℝ)) * wfun (g4)) * SA
      = 24896 * g0 + 42034 * g1 + 46137 * g2 + 42034 * g3 + 24896 * g4 + 25326800 * wfun (g0) + 62369200 * wfun (g0 + g1) + 40126500 * wfun (g0 + g1 + g2) + 99999900 * wfun (g0 + g1 + g2 + g3) + 200000000 * wfun (g0 + g1 + g2 + g3 + g4) + 48244400 * wfun (g1) + 37630700 * wfun (g1 + g2) + 119746800 * wfun (g1 + g2 + g3) + 99999900 * wfun (g1 + g2 + g3 + g4) + 52857300 * wfun (g2) + 37630700 * wfun (g2 + g3) + 40126500 * wfun (g2 + g3 + g4) + 48244400 * wfun (g3) + 62369200 * wfun (g3 + g4) + 25326800 * wfun (g4) := by
    field_simp; try ring
  rw [eG]
  rw [hL, hWt] at hq'
  linarith [hq', mul_le_mul_of_nonneg_left h01 (by positivity : (0:ℝ) ≤ 24896), mul_le_mul_of_nonneg_left h11 (by positivity : (0:ℝ) ≤ 42034), mul_le_mul_of_nonneg_left h21 (by positivity : (0:ℝ) ≤ 46137), mul_le_mul_of_nonneg_left h31 (by positivity : (0:ℝ) ≤ 42034), mul_le_mul_of_nonneg_left h41 (by positivity : (0:ℝ) ≤ 24896), mul_le_mul_of_nonneg_left w0 (by positivity : (0:ℝ) ≤ 25326800), mul_le_mul_of_nonneg_left w1 (by positivity : (0:ℝ) ≤ 62369200), mul_le_mul_of_nonneg_left w2 (by positivity : (0:ℝ) ≤ 40126500), mul_le_mul_of_nonneg_left w3 (by positivity : (0:ℝ) ≤ 99999900), mul_le_mul_of_nonneg_left w4 (by positivity : (0:ℝ) ≤ 200000000), mul_le_mul_of_nonneg_left w5 (by positivity : (0:ℝ) ≤ 48244400), mul_le_mul_of_nonneg_left w6 (by positivity : (0:ℝ) ≤ 37630700), mul_le_mul_of_nonneg_left w7 (by positivity : (0:ℝ) ≤ 119746800), mul_le_mul_of_nonneg_left w8 (by positivity : (0:ℝ) ≤ 99999900), mul_le_mul_of_nonneg_left w9 (by positivity : (0:ℝ) ≤ 52857300), mul_le_mul_of_nonneg_left w10 (by positivity : (0:ℝ) ≤ 37630700), mul_le_mul_of_nonneg_left w11 (by positivity : (0:ℝ) ≤ 40126500), mul_le_mul_of_nonneg_left w12 (by positivity : (0:ℝ) ≤ 48244400), mul_le_mul_of_nonneg_left w13 (by positivity : (0:ℝ) ≤ 62369200), mul_le_mul_of_nonneg_left w14 (by positivity : (0:ℝ) ≤ 25326800)]


/-- a box split on gap 0 at `q` is covered when both halves are -/
theorem covered_split0 {l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 : ℕ} (q : ℕ) (hA : Covered l0 q l1 u1 l2 u2 l3 u3 l4 u4) (hB : Covered q u0 l1 u1 l2 u2 l3 u3 l4 u4) :
    Covered l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 := by
  intro g0 g1 g2 g3 g4 h01 h02 h11 h12 h21 h22 h31 h32 h41 h42
  rcases le_total g0 ((q : ℝ) / SC) with hq | hq
  · exact hA g0 g1 g2 g3 g4 h01 hq h11 h12 h21 h22 h31 h32 h41 h42
  · exact hB g0 g1 g2 g3 g4 hq h02 h11 h12 h21 h22 h31 h32 h41 h42

/-- a box split on gap 1 at `q` is covered when both halves are -/
theorem covered_split1 {l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 : ℕ} (q : ℕ) (hA : Covered l0 u0 l1 q l2 u2 l3 u3 l4 u4) (hB : Covered l0 u0 q u1 l2 u2 l3 u3 l4 u4) :
    Covered l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 := by
  intro g0 g1 g2 g3 g4 h01 h02 h11 h12 h21 h22 h31 h32 h41 h42
  rcases le_total g1 ((q : ℝ) / SC) with hq | hq
  · exact hA g0 g1 g2 g3 g4 h01 h02 h11 hq h21 h22 h31 h32 h41 h42
  · exact hB g0 g1 g2 g3 g4 h01 h02 hq h12 h21 h22 h31 h32 h41 h42

/-- a box split on gap 2 at `q` is covered when both halves are -/
theorem covered_split2 {l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 : ℕ} (q : ℕ) (hA : Covered l0 u0 l1 u1 l2 q l3 u3 l4 u4) (hB : Covered l0 u0 l1 u1 q u2 l3 u3 l4 u4) :
    Covered l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 := by
  intro g0 g1 g2 g3 g4 h01 h02 h11 h12 h21 h22 h31 h32 h41 h42
  rcases le_total g2 ((q : ℝ) / SC) with hq | hq
  · exact hA g0 g1 g2 g3 g4 h01 h02 h11 h12 h21 hq h31 h32 h41 h42
  · exact hB g0 g1 g2 g3 g4 h01 h02 h11 h12 hq h22 h31 h32 h41 h42

/-- a box split on gap 3 at `q` is covered when both halves are -/
theorem covered_split3 {l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 : ℕ} (q : ℕ) (hA : Covered l0 u0 l1 u1 l2 u2 l3 q l4 u4) (hB : Covered l0 u0 l1 u1 l2 u2 q u3 l4 u4) :
    Covered l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 := by
  intro g0 g1 g2 g3 g4 h01 h02 h11 h12 h21 h22 h31 h32 h41 h42
  rcases le_total g3 ((q : ℝ) / SC) with hq | hq
  · exact hA g0 g1 g2 g3 g4 h01 h02 h11 h12 h21 h22 h31 hq h41 h42
  · exact hB g0 g1 g2 g3 g4 h01 h02 h11 h12 h21 h22 hq h32 h41 h42

/-- a box split on gap 4 at `q` is covered when both halves are -/
theorem covered_split4 {l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 : ℕ} (q : ℕ) (hA : Covered l0 u0 l1 u1 l2 u2 l3 u3 l4 q) (hB : Covered l0 u0 l1 u1 l2 u2 l3 u3 q u4) :
    Covered l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 := by
  intro g0 g1 g2 g3 g4 h01 h02 h11 h12 h21 h22 h31 h32 h41 h42
  rcases le_total g4 ((q : ℝ) / SC) with hq | hq
  · exact hA g0 g1 g2 g3 g4 h01 h02 h11 h12 h21 h22 h31 h32 h41 hq
  · exact hB g0 g1 g2 g3 g4 h01 h02 h11 h12 h21 h22 h31 h32 hq h42

/-- a continuation that only returns nonzero on covered boxes -/
def WalkOK (f : WF) : Prop := ∀ pos l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 : ℕ, f pos l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 ≠ 0 → Covered l0 u0 l1 u1 l2 u2 l3 u3 l4 u4

theorem split0_sound {ih : WF} (hih : WalkOK ih) (pos l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 : ℕ) (h : split0 ih pos l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 ≠ 0) :
    Covered l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 := by
  unfold split0 at h
  rw [forceR_eq] at h
  cases hp : Nat.beq (ih (Nat.add pos 4) l0 (Nat.shiftRight (Nat.add l0 u0) 1) l1 u1 l2 u2 l3 u3 l4 u4) 0
  · have h' : ih (ih (Nat.add pos 4) l0 (Nat.shiftRight (Nat.add l0 u0) 1) l1 u1 l2 u2 l3 u3 l4 u4) (Nat.shiftRight (Nat.add l0 u0) 1) u0 l1 u1 l2 u2 l3 u3 l4 u4 ≠ 0 := by
      intro h0; apply h; simp only [hp]; exact h0
    have hA := hih (Nat.add pos 4) l0 (Nat.shiftRight (Nat.add l0 u0) 1) l1 u1 l2 u2 l3 u3 l4 u4 (by intro h0; rw [h0] at hp; exact absurd hp (by decide))
    exact covered_split0 _ hA (hih _ (Nat.shiftRight (Nat.add l0 u0) 1) u0 l1 u1 l2 u2 l3 u3 l4 u4 h')
  · exact absurd (by simp only [hp]) h

theorem split1_sound {ih : WF} (hih : WalkOK ih) (pos l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 : ℕ) (h : split1 ih pos l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 ≠ 0) :
    Covered l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 := by
  unfold split1 at h
  rw [forceR_eq] at h
  cases hp : Nat.beq (ih (Nat.add pos 4) l0 u0 l1 (Nat.shiftRight (Nat.add l1 u1) 1) l2 u2 l3 u3 l4 u4) 0
  · have h' : ih (ih (Nat.add pos 4) l0 u0 l1 (Nat.shiftRight (Nat.add l1 u1) 1) l2 u2 l3 u3 l4 u4) l0 u0 (Nat.shiftRight (Nat.add l1 u1) 1) u1 l2 u2 l3 u3 l4 u4 ≠ 0 := by
      intro h0; apply h; simp only [hp]; exact h0
    have hA := hih (Nat.add pos 4) l0 u0 l1 (Nat.shiftRight (Nat.add l1 u1) 1) l2 u2 l3 u3 l4 u4 (by intro h0; rw [h0] at hp; exact absurd hp (by decide))
    exact covered_split1 _ hA (hih _ l0 u0 (Nat.shiftRight (Nat.add l1 u1) 1) u1 l2 u2 l3 u3 l4 u4 h')
  · exact absurd (by simp only [hp]) h

theorem split2_sound {ih : WF} (hih : WalkOK ih) (pos l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 : ℕ) (h : split2 ih pos l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 ≠ 0) :
    Covered l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 := by
  unfold split2 at h
  rw [forceR_eq] at h
  cases hp : Nat.beq (ih (Nat.add pos 4) l0 u0 l1 u1 l2 (Nat.shiftRight (Nat.add l2 u2) 1) l3 u3 l4 u4) 0
  · have h' : ih (ih (Nat.add pos 4) l0 u0 l1 u1 l2 (Nat.shiftRight (Nat.add l2 u2) 1) l3 u3 l4 u4) l0 u0 l1 u1 (Nat.shiftRight (Nat.add l2 u2) 1) u2 l3 u3 l4 u4 ≠ 0 := by
      intro h0; apply h; simp only [hp]; exact h0
    have hA := hih (Nat.add pos 4) l0 u0 l1 u1 l2 (Nat.shiftRight (Nat.add l2 u2) 1) l3 u3 l4 u4 (by intro h0; rw [h0] at hp; exact absurd hp (by decide))
    exact covered_split2 _ hA (hih _ l0 u0 l1 u1 (Nat.shiftRight (Nat.add l2 u2) 1) u2 l3 u3 l4 u4 h')
  · exact absurd (by simp only [hp]) h

theorem split3_sound {ih : WF} (hih : WalkOK ih) (pos l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 : ℕ) (h : split3 ih pos l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 ≠ 0) :
    Covered l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 := by
  unfold split3 at h
  rw [forceR_eq] at h
  cases hp : Nat.beq (ih (Nat.add pos 4) l0 u0 l1 u1 l2 u2 l3 (Nat.shiftRight (Nat.add l3 u3) 1) l4 u4) 0
  · have h' : ih (ih (Nat.add pos 4) l0 u0 l1 u1 l2 u2 l3 (Nat.shiftRight (Nat.add l3 u3) 1) l4 u4) l0 u0 l1 u1 l2 u2 (Nat.shiftRight (Nat.add l3 u3) 1) u3 l4 u4 ≠ 0 := by
      intro h0; apply h; simp only [hp]; exact h0
    have hA := hih (Nat.add pos 4) l0 u0 l1 u1 l2 u2 l3 (Nat.shiftRight (Nat.add l3 u3) 1) l4 u4 (by intro h0; rw [h0] at hp; exact absurd hp (by decide))
    exact covered_split3 _ hA (hih _ l0 u0 l1 u1 l2 u2 (Nat.shiftRight (Nat.add l3 u3) 1) u3 l4 u4 h')
  · exact absurd (by simp only [hp]) h

theorem split4_sound {ih : WF} (hih : WalkOK ih) (pos l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 : ℕ) (h : split4 ih pos l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 ≠ 0) :
    Covered l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 := by
  unfold split4 at h
  rw [forceR_eq] at h
  cases hp : Nat.beq (ih (Nat.add pos 4) l0 u0 l1 u1 l2 u2 l3 u3 l4 (Nat.shiftRight (Nat.add l4 u4) 1)) 0
  · have h' : ih (ih (Nat.add pos 4) l0 u0 l1 u1 l2 u2 l3 u3 l4 (Nat.shiftRight (Nat.add l4 u4) 1)) l0 u0 l1 u1 l2 u2 l3 u3 (Nat.shiftRight (Nat.add l4 u4) 1) u4 ≠ 0 := by
      intro h0; apply h; simp only [hp]; exact h0
    have hA := hih (Nat.add pos 4) l0 u0 l1 u1 l2 u2 l3 u3 l4 (Nat.shiftRight (Nat.add l4 u4) 1) (by intro h0; rw [h0] at hp; exact absurd hp (by decide))
    exact covered_split4 _ hA (hih _ l0 u0 l1 u1 l2 u2 l3 u3 (Nat.shiftRight (Nat.add l4 u4) 1) u4 h')
  · exact absurd (by simp only [hp]) h

theorem splitAx_sound {ih : WF} (hih : WalkOK ih) (pos ax l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 : ℕ) (h : splitAx ih pos ax l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 ≠ 0) :
    Covered l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 := by
  unfold splitAx at h
  cases ha0 : Nat.beq ax 0
  · rw [ha0] at h
    cases ha1 : Nat.beq ax 1
    · rw [ha1] at h
      cases ha2 : Nat.beq ax 2
      · rw [ha2] at h
        cases ha3 : Nat.beq ax 3
        · rw [ha3] at h
          exact split4_sound hih pos l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 h
        · rw [ha3] at h; exact split3_sound hih pos l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 h
      · rw [ha2] at h; exact split2_sound hih pos l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 h
    · rw [ha1] at h; exact split1_sound hih pos l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 h
  · rw [ha0] at h; exact split0_sound hih pos l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 h

theorem leafStep_sound {top : ℕ} {bk : ℕ → ℕ} (hlb : LBSound top bk) (pos l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 : ℕ) (h : leafStep top bk pos l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 ≠ 0) :
    Covered l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 := by
  unfold leafStep at h
  intro g0 g1 g2 g3 g4 h01 h02 h11 h12 h21 h22 h31 h32 h41 h42
  cases hs : Nat.ble (Nat.add u4 1) l0
  · rw [hs] at h
    cases hl : leafOK top bk l0 u0 l1 u1 l2 u2 l3 u3 l4 u4
    · rw [hl] at h; exact absurd rfl h
    · exact Or.inl (leaf_sound hlb l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 hl g0 g1 g2 g3 g4 h01 h02 h11 h12 h21 h22 h31 h32 h41 h42)
  · right
    have hsk : u4 < l0 := by rw [Nat.ble_eq] at hs; simp only [Nat.add_eq] at hs; omega
    have : (u4 : ℝ) / SC < (l0 : ℝ) / SC := div_lt_div_of_pos_right (by exact_mod_cast hsk) (by norm_num [SC])
    linarith

theorem walk_sound {top : ℕ} {bk : ℕ → ℕ} (hlb : LBSound top bk) (bits : ℕ) : ∀ fuel, WalkOK (walk top bk bits fuel) := by
  intro fuel
  induction fuel with
  | zero => intro pos l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 h; exact absurd rfl h
  | succ fuel ih =>
    intro pos l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 h
    have h' : Bool.rec (motive := fun _ => ℕ) (leafStep top bk pos l0 u0 l1 u1 l2 u2 l3 u3 l4 u4)
        (splitAx (walk top bk bits fuel) pos (Nat.shiftRight (Nat.land (Nat.shiftRight bits pos) 15) 1) l0 u0 l1 u1 l2 u2 l3 u3 l4 u4)
        (Nat.beq (Nat.land (Nat.land (Nat.shiftRight bits pos) 15) 1) 1) ≠ 0 := h
    cases hb : Nat.beq (Nat.land (Nat.land (Nat.shiftRight bits pos) 15) 1) 1
    · rw [hb] at h'; exact leafStep_sound hlb pos l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 h'
    · rw [hb] at h'; exact splitAx_sound ih pos _ l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 h'

theorem covered_of_walk {top : ℕ} {bk : ℕ → ℕ} (hlb : LBSound top bk) (bits fuel l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 e : ℕ)
    (h : walk top bk bits fuel 1 l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 = e) (he : e ≠ 0) : Covered l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 :=
  walk_sound hlb bits fuel 1 l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 (h ▸ he)

/-- per-gap one-dimensional cover: segments `(a, b, clear)` in scaled coordinates; a clear segment's own integer
cell bound must satisfy `aAdj · W ≥ c`, i.e. `aAdjN * WZ ≥ cN * SW` -/
def coverCheck (aAdjN : ℕ) : ℕ → ℕ → List (ℕ × ℕ × Bool) → Bool
  | pos, S, [] => decide (S ≤ pos)
  | pos, S, (a, b, cl) :: rest =>
      decide (a = pos) && decide (a ≤ b) && decide (b < KB)
        && (!cl || Nat.ble (cN * SW) (aAdjN * CellN.WZ ⟨a * KB + b, 0⟩))
        && coverCheck aAdjN b S rest

def badOf (cover : List (ℕ × ℕ × Bool)) : List (ℕ × ℕ) :=
  cover.filterMap fun s => if s.2.2 then none else some (s.1, s.2.1)

theorem cover_sound (aAdjN : ℕ) :
    ∀ (cover : List (ℕ × ℕ × Bool)) (pos S : ℕ), coverCheck aAdjN pos S cover = true →
      ∀ v : ℝ, (pos : ℝ) / SC ≤ v → v < (S : ℝ) / SC →
        (cN : ℝ) / SA ≤ ((aAdjN : ℝ) / SA) * wfun v ∨
          ∃ s ∈ cover, s.2.2 = false ∧ (s.1 : ℝ) / SC ≤ v ∧ v ≤ (s.2.1 : ℝ) / SC := by
  intro cover
  induction cover with
  | nil =>
    intro pos S h v hv1 hv2
    simp only [coverCheck, decide_eq_true_eq] at h
    have : (S : ℝ) / SC ≤ (pos : ℝ) / SC := div_le_div_of_nonneg_right (by exact_mod_cast h) (by norm_num [SC])
    exact absurd (lt_of_le_of_lt (this.trans hv1) hv2) (lt_irrefl _)
  | cons s rest ih =>
    intro pos S h v hv1 hv2
    obtain ⟨a, b, cl⟩ := s
    simp only [coverCheck, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, Bool.not_eq_eq_eq_not,
      Bool.not_true] at h
    obtain ⟨⟨⟨⟨hpos, hab⟩, hbK⟩, hcl⟩, hrest⟩ := h
    rcases le_total v ((b : ℝ) / SC) with hvb | hvb
    · rcases hcl with hcl | hcl
      · right
        exact ⟨(a, b, cl), List.mem_cons_self .., hcl, by rw [hpos]; exact hv1, hvb⟩
      · left
        rw [Nat.ble_eq] at hcl
        have hLN : (⟨a * KB + b, 0⟩ : CellN).LN = a := by
          simp only [CellN.LN]; rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by norm_num [KB]), Nat.div_eq_of_lt hbK, Nat.zero_add]
        have hUN : (⟨a * KB + b, 0⟩ : CellN).UN = b := by
          simp only [CellN.UN]; rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hbK]
        have hW := cellN_soundWZ ⟨a * KB + b, 0⟩ v (by rw [hLN, hpos]; exact hv1) (by rw [hUN]; exact hvb)
        have hq := (Nat.cast_le (α := ℝ)).mpr hcl
        push_cast at hq
        have hSA : (0:ℝ) < SA := by norm_num [SA]
        have hSW : (0:ℝ) < SW := by norm_num [SW]
        rw [div_le_iff₀ hSA]
        have hm2 : (aAdjN : ℝ) * (((⟨a * KB + b, 0⟩ : CellN).WZ : ℝ) / SW) ≤ (aAdjN : ℝ) * wfun v :=
          mul_le_mul_of_nonneg_left hW (by positivity)
        have e : (aAdjN : ℝ) / SA * wfun v * SA = (aAdjN : ℝ) * wfun v := by field_simp
        rw [e]
        calc (cN : ℝ) = (cN : ℝ) * SW / SW := by field_simp
          _ ≤ (aAdjN : ℝ) * ((⟨a * KB + b, 0⟩ : CellN).WZ : ℝ) / SW := by apply div_le_div_of_nonneg_right _ hSW.le; linarith
          _ = (aAdjN : ℝ) * (((⟨a * KB + b, 0⟩ : CellN).WZ : ℝ) / SW) := by ring
          _ ≤ _ := hm2
    · rcases ih b S hrest v hvb hv2 with h | ⟨s', hs', he, h1, h2⟩
      · left; exact h
      · right; exact ⟨s', List.mem_cons_of_mem _ hs', he, h1, h2⟩

theorem badOf_mem {cover : List (ℕ × ℕ × Bool)} {s : ℕ × ℕ × Bool} (hs : s ∈ cover)
    (he : s.2.2 = false) : (s.1, s.2.1) ∈ badOf cover := by
  simp only [badOf, List.mem_filterMap]
  exact ⟨s, hs, by simp [he]⟩

set_option maxHeartbeats 4000000 in
theorem of_check (cover0 cover1 cover2 cover3 cover4 : List (ℕ × ℕ × Bool)) (S0 S1 S2 S3 S4 : ℕ)
    (hS0 : cN * SC ≤ 24896 * S0) (hS1 : cN * SC ≤ 42034 * S1) (hS2 : cN * SC ≤ 46137 * S2) (hS3 : cN * SC ≤ 42034 * S3) (hS4 : cN * SC ≤ 24896 * S4)
    (hcov0 : coverCheck 25326800 (SC / 2) S0 cover0 = true) (hcov1 : coverCheck 48244400 (SC / 2) S1 cover1 = true) (hcov2 : coverCheck 52857300 (SC / 2) S2 cover2 = true) (hcov3 : coverCheck 48244400 (SC / 2) S3 cover3 = true) (hcov4 : coverCheck 25326800 (SC / 2) S4 cover4 = true)
    (hwin : cN * 100 ≤ 19 * 25326800)
    (hrun : ∀ i0 i1 i2 i3 i4, i0 < (badOf cover0).length → i1 < (badOf cover1).length → i2 < (badOf cover2).length → i3 < (badOf cover3).length → i4 < (badOf cover4).length →
      Covered ((badOf cover0).getD i0 (0, 0)).1 ((badOf cover0).getD i0 (0, 0)).2 ((badOf cover1).getD i1 (0, 0)).1 ((badOf cover1).getD i1 (0, 0)).2 ((badOf cover2).getD i2 (0, 0)).1 ((badOf cover2).getD i2 (0, 0)).2 ((badOf cover3).getD i3 (0, 0)).1 ((badOf cover3).getD i3 (0, 0)).2 ((badOf cover4).getD i4 (0, 0)).1 ((badOf cover4).getD i4 (0, 0)).2) :
    ∀ g0 g1 g2 g3 g4 : ℝ, 0 ≤ g0 → 0 ≤ g1 → 0 ≤ g2 → 0 ≤ g3 → 0 ≤ g4 → (cN : ℝ) / SA ≤ G g0 g1 g2 g3 g4 ∨ g4 < g0 := by
  intro g0 g1 g2 g3 g4 hg0 hg1 hg2 hg3 hg4
  have hw := fun v : ℝ => wfun_nonneg v
  have hSA : (0:ℝ) < SA := by norm_num [SA]
  have hSC : (0:ℝ) < SC := by norm_num [SC]
  have hhalf : ((SC / 2 : ℕ) : ℝ) / SC = 1/2 := by norm_num [SC]
  set Lin : ℝ := (24896 / (SA:ℝ)) * g0 + (42034 / (SA:ℝ)) * g1 + (46137 / (SA:ℝ)) * g2 + (42034 / (SA:ℝ)) * g3 + (24896 / (SA:ℝ)) * g4 with hLin
  set Wt : ℝ := (25326800 / (SA:ℝ)) * wfun (g0) + (62369200 / (SA:ℝ)) * wfun (g0 + g1) + (40126500 / (SA:ℝ)) * wfun (g0 + g1 + g2) + (99999900 / (SA:ℝ)) * wfun (g0 + g1 + g2 + g3) + (200000000 / (SA:ℝ)) * wfun (g0 + g1 + g2 + g3 + g4) + (48244400 / (SA:ℝ)) * wfun (g1) + (37630700 / (SA:ℝ)) * wfun (g1 + g2) + (119746800 / (SA:ℝ)) * wfun (g1 + g2 + g3) + (99999900 / (SA:ℝ)) * wfun (g1 + g2 + g3 + g4) + (52857300 / (SA:ℝ)) * wfun (g2) + (37630700 / (SA:ℝ)) * wfun (g2 + g3) + (40126500 / (SA:ℝ)) * wfun (g2 + g3 + g4) + (48244400 / (SA:ℝ)) * wfun (g3) + (62369200 / (SA:ℝ)) * wfun (g3 + g4) + (25326800 / (SA:ℝ)) * wfun (g4) with hWt
  have hG : G g0 g1 g2 g3 g4 = Lin + Wt := by unfold G; rw [hLin, hWt]; ring
  have hb00 : (0:ℝ) ≤ (24896 / (SA:ℝ)) * g0 := mul_nonneg (by positivity) hg0
  have hb10 : (0:ℝ) ≤ (42034 / (SA:ℝ)) * g1 := mul_nonneg (by positivity) hg1
  have hb20 : (0:ℝ) ≤ (46137 / (SA:ℝ)) * g2 := mul_nonneg (by positivity) hg2
  have hb30 : (0:ℝ) ≤ (42034 / (SA:ℝ)) * g3 := mul_nonneg (by positivity) hg3
  have hb40 : (0:ℝ) ≤ (24896 / (SA:ℝ)) * g4 := mul_nonneg (by positivity) hg4
  have ha00 : (0:ℝ) ≤ (25326800 / (SA:ℝ)) * wfun (g0) := mul_nonneg (by positivity) (hw _)
  have ha10 : (0:ℝ) ≤ (62369200 / (SA:ℝ)) * wfun (g0 + g1) := mul_nonneg (by positivity) (hw _)
  have ha20 : (0:ℝ) ≤ (40126500 / (SA:ℝ)) * wfun (g0 + g1 + g2) := mul_nonneg (by positivity) (hw _)
  have ha30 : (0:ℝ) ≤ (99999900 / (SA:ℝ)) * wfun (g0 + g1 + g2 + g3) := mul_nonneg (by positivity) (hw _)
  have ha40 : (0:ℝ) ≤ (200000000 / (SA:ℝ)) * wfun (g0 + g1 + g2 + g3 + g4) := mul_nonneg (by positivity) (hw _)
  have ha50 : (0:ℝ) ≤ (48244400 / (SA:ℝ)) * wfun (g1) := mul_nonneg (by positivity) (hw _)
  have ha60 : (0:ℝ) ≤ (37630700 / (SA:ℝ)) * wfun (g1 + g2) := mul_nonneg (by positivity) (hw _)
  have ha70 : (0:ℝ) ≤ (119746800 / (SA:ℝ)) * wfun (g1 + g2 + g3) := mul_nonneg (by positivity) (hw _)
  have ha80 : (0:ℝ) ≤ (99999900 / (SA:ℝ)) * wfun (g1 + g2 + g3 + g4) := mul_nonneg (by positivity) (hw _)
  have ha90 : (0:ℝ) ≤ (52857300 / (SA:ℝ)) * wfun (g2) := mul_nonneg (by positivity) (hw _)
  have ha100 : (0:ℝ) ≤ (37630700 / (SA:ℝ)) * wfun (g2 + g3) := mul_nonneg (by positivity) (hw _)
  have ha110 : (0:ℝ) ≤ (40126500 / (SA:ℝ)) * wfun (g2 + g3 + g4) := mul_nonneg (by positivity) (hw _)
  have ha120 : (0:ℝ) ≤ (48244400 / (SA:ℝ)) * wfun (g3) := mul_nonneg (by positivity) (hw _)
  have ha130 : (0:ℝ) ≤ (62369200 / (SA:ℝ)) * wfun (g3 + g4) := mul_nonneg (by positivity) (hw _)
  have ha140 : (0:ℝ) ≤ (25326800 / (SA:ℝ)) * wfun (g4) := mul_nonneg (by positivity) (hw _)
  have hLin0 : 0 ≤ Lin := by rw [hLin]; linarith [hb00, hb10, hb20, hb30, hb40]
  have hWt0 : 0 ≤ Wt := by rw [hWt]; linarith [ha00, ha10, ha20, ha30, ha40, ha50, ha60, ha70, ha80, ha90, ha100, ha110, ha120, ha130, ha140]
  have hbL0 : (24896 / (SA:ℝ)) * g0 ≤ Lin := by rw [hLin]; linarith [hb10, hb20, hb30, hb40]
  have hbL1 : (42034 / (SA:ℝ)) * g1 ≤ Lin := by rw [hLin]; linarith [hb00, hb20, hb30, hb40]
  have hbL2 : (46137 / (SA:ℝ)) * g2 ≤ Lin := by rw [hLin]; linarith [hb00, hb10, hb30, hb40]
  have hbL3 : (42034 / (SA:ℝ)) * g3 ≤ Lin := by rw [hLin]; linarith [hb00, hb10, hb20, hb40]
  have hbL4 : (24896 / (SA:ℝ)) * g4 ≤ Lin := by rw [hLin]; linarith [hb00, hb10, hb20, hb30]
  have haW0 : (25326800 / (SA:ℝ)) * wfun (g0) ≤ Wt := by rw [hWt]; linarith [ha10, ha20, ha30, ha40, ha50, ha60, ha70, ha80, ha90, ha100, ha110, ha120, ha130, ha140]
  have haW1 : (62369200 / (SA:ℝ)) * wfun (g0 + g1) ≤ Wt := by rw [hWt]; linarith [ha00, ha20, ha30, ha40, ha50, ha60, ha70, ha80, ha90, ha100, ha110, ha120, ha130, ha140]
  have haW2 : (40126500 / (SA:ℝ)) * wfun (g0 + g1 + g2) ≤ Wt := by rw [hWt]; linarith [ha00, ha10, ha30, ha40, ha50, ha60, ha70, ha80, ha90, ha100, ha110, ha120, ha130, ha140]
  have haW3 : (99999900 / (SA:ℝ)) * wfun (g0 + g1 + g2 + g3) ≤ Wt := by rw [hWt]; linarith [ha00, ha10, ha20, ha40, ha50, ha60, ha70, ha80, ha90, ha100, ha110, ha120, ha130, ha140]
  have haW4 : (200000000 / (SA:ℝ)) * wfun (g0 + g1 + g2 + g3 + g4) ≤ Wt := by rw [hWt]; linarith [ha00, ha10, ha20, ha30, ha50, ha60, ha70, ha80, ha90, ha100, ha110, ha120, ha130, ha140]
  have haW5 : (48244400 / (SA:ℝ)) * wfun (g1) ≤ Wt := by rw [hWt]; linarith [ha00, ha10, ha20, ha30, ha40, ha60, ha70, ha80, ha90, ha100, ha110, ha120, ha130, ha140]
  have haW6 : (37630700 / (SA:ℝ)) * wfun (g1 + g2) ≤ Wt := by rw [hWt]; linarith [ha00, ha10, ha20, ha30, ha40, ha50, ha70, ha80, ha90, ha100, ha110, ha120, ha130, ha140]
  have haW7 : (119746800 / (SA:ℝ)) * wfun (g1 + g2 + g3) ≤ Wt := by rw [hWt]; linarith [ha00, ha10, ha20, ha30, ha40, ha50, ha60, ha80, ha90, ha100, ha110, ha120, ha130, ha140]
  have haW8 : (99999900 / (SA:ℝ)) * wfun (g1 + g2 + g3 + g4) ≤ Wt := by rw [hWt]; linarith [ha00, ha10, ha20, ha30, ha40, ha50, ha60, ha70, ha90, ha100, ha110, ha120, ha130, ha140]
  have haW9 : (52857300 / (SA:ℝ)) * wfun (g2) ≤ Wt := by rw [hWt]; linarith [ha00, ha10, ha20, ha30, ha40, ha50, ha60, ha70, ha80, ha100, ha110, ha120, ha130, ha140]
  have haW10 : (37630700 / (SA:ℝ)) * wfun (g2 + g3) ≤ Wt := by rw [hWt]; linarith [ha00, ha10, ha20, ha30, ha40, ha50, ha60, ha70, ha80, ha90, ha110, ha120, ha130, ha140]
  have haW11 : (40126500 / (SA:ℝ)) * wfun (g2 + g3 + g4) ≤ Wt := by rw [hWt]; linarith [ha00, ha10, ha20, ha30, ha40, ha50, ha60, ha70, ha80, ha90, ha100, ha120, ha130, ha140]
  have haW12 : (48244400 / (SA:ℝ)) * wfun (g3) ≤ Wt := by rw [hWt]; linarith [ha00, ha10, ha20, ha30, ha40, ha50, ha60, ha70, ha80, ha90, ha100, ha110, ha130, ha140]
  have haW13 : (62369200 / (SA:ℝ)) * wfun (g3 + g4) ≤ Wt := by rw [hWt]; linarith [ha00, ha10, ha20, ha30, ha40, ha50, ha60, ha70, ha80, ha90, ha100, ha110, ha120, ha140]
  have haW14 : (25326800 / (SA:ℝ)) * wfun (g4) ≤ Wt := by rw [hWt]; linarith [ha00, ha10, ha20, ha30, ha40, ha50, ha60, ha70, ha80, ha90, ha100, ha110, ha120, ha130]
  -- gap 0: beyond the cutoff the pressure alone pays
  by_cases hcut0 : (S0 : ℝ) / SC ≤ g0
  · have h1 : (cN : ℝ) / SA ≤ (24896 / (SA:ℝ)) * g0 := by
      have hq := (Nat.cast_le (α := ℝ)).mpr hS0; push_cast at hq
      rw [div_le_iff₀ hSA]
      have e : (24896 / (SA:ℝ)) * g0 * SA = 24896 * g0 := by field_simp
      rw [e]
      calc (cN : ℝ) = (cN : ℝ) * SC / SC := by field_simp
        _ ≤ 24896 * S0 / SC := by apply div_le_div_of_nonneg_right _ hSC.le; linarith
        _ = 24896 * ((S0 : ℝ) / SC) := by ring
        _ ≤ 24896 * g0 := mul_le_mul_of_nonneg_left hcut0 (by norm_num)
    left; rw [hG]; linarith [h1, hbL0, hWt0]
  push_neg at hcut0
  rcases le_total g0 ((SC / 2 : ℕ) / (SC : ℝ)) with hwin0 | hwin0
  · have hw19 := wfun_window g0 hg0 (by rw [hhalf] at hwin0; exact hwin0)
    have hq := (Nat.cast_le (α := ℝ)).mpr hwin; push_cast at hq
    have h1 : (cN : ℝ) / SA ≤ (25326800 / (SA:ℝ)) * wfun g0 := by
      rw [div_le_iff₀ hSA]
      have e : (25326800 / (SA:ℝ)) * wfun g0 * SA = 25326800 * wfun g0 := by field_simp
      rw [e]
      have hm := mul_le_mul_of_nonneg_left hw19 (by norm_num : (0:ℝ) ≤ 25326800)
      linarith [hq, hm]
    left; rw [hG]; linarith [h1, haW0, hLin0]
  rcases cover_sound _ cover0 (SC / 2) S0 hcov0 g0 hwin0 hcut0 with hclear0 | ⟨s0, hs0, he0, hb01, hb02⟩
  · left; rw [hG]; linarith [hclear0, haW0, hLin0]
  obtain ⟨i0, hi0, hsi0⟩ := List.mem_iff_getElem.mp (badOf_mem hs0 he0)
  have hb01' : (((badOf cover0).getD i0 (0, 0)).1 : ℝ) / SC ≤ g0 := by
    rw [List.getD_eq_getElem _ _ hi0, hsi0]; exact hb01
  have hb02' : g0 ≤ (((badOf cover0).getD i0 (0, 0)).2 : ℝ) / SC := by
    rw [List.getD_eq_getElem _ _ hi0, hsi0]; exact hb02
  -- gap 1: beyond the cutoff the pressure alone pays
  by_cases hcut1 : (S1 : ℝ) / SC ≤ g1
  · have h1 : (cN : ℝ) / SA ≤ (42034 / (SA:ℝ)) * g1 := by
      have hq := (Nat.cast_le (α := ℝ)).mpr hS1; push_cast at hq
      rw [div_le_iff₀ hSA]
      have e : (42034 / (SA:ℝ)) * g1 * SA = 42034 * g1 := by field_simp
      rw [e]
      calc (cN : ℝ) = (cN : ℝ) * SC / SC := by field_simp
        _ ≤ 42034 * S1 / SC := by apply div_le_div_of_nonneg_right _ hSC.le; linarith
        _ = 42034 * ((S1 : ℝ) / SC) := by ring
        _ ≤ 42034 * g1 := mul_le_mul_of_nonneg_left hcut1 (by norm_num)
    left; rw [hG]; linarith [h1, hbL1, hWt0]
  push_neg at hcut1
  rcases le_total g1 ((SC / 2 : ℕ) / (SC : ℝ)) with hwin1 | hwin1
  · have hw19 := wfun_window g1 hg1 (by rw [hhalf] at hwin1; exact hwin1)
    have hq := (Nat.cast_le (α := ℝ)).mpr hwin; push_cast at hq
    have h1 : (cN : ℝ) / SA ≤ (48244400 / (SA:ℝ)) * wfun g1 := by
      rw [div_le_iff₀ hSA]
      have e : (48244400 / (SA:ℝ)) * wfun g1 * SA = 48244400 * wfun g1 := by field_simp
      rw [e]
      have hm := mul_le_mul_of_nonneg_left hw19 (by norm_num : (0:ℝ) ≤ 48244400)
      linarith [hq, hm]
    left; rw [hG]; linarith [h1, haW5, hLin0]
  rcases cover_sound _ cover1 (SC / 2) S1 hcov1 g1 hwin1 hcut1 with hclear1 | ⟨s1, hs1, he1, hb11, hb12⟩
  · left; rw [hG]; linarith [hclear1, haW5, hLin0]
  obtain ⟨i1, hi1, hsi1⟩ := List.mem_iff_getElem.mp (badOf_mem hs1 he1)
  have hb11' : (((badOf cover1).getD i1 (0, 0)).1 : ℝ) / SC ≤ g1 := by
    rw [List.getD_eq_getElem _ _ hi1, hsi1]; exact hb11
  have hb12' : g1 ≤ (((badOf cover1).getD i1 (0, 0)).2 : ℝ) / SC := by
    rw [List.getD_eq_getElem _ _ hi1, hsi1]; exact hb12
  -- gap 2: beyond the cutoff the pressure alone pays
  by_cases hcut2 : (S2 : ℝ) / SC ≤ g2
  · have h1 : (cN : ℝ) / SA ≤ (46137 / (SA:ℝ)) * g2 := by
      have hq := (Nat.cast_le (α := ℝ)).mpr hS2; push_cast at hq
      rw [div_le_iff₀ hSA]
      have e : (46137 / (SA:ℝ)) * g2 * SA = 46137 * g2 := by field_simp
      rw [e]
      calc (cN : ℝ) = (cN : ℝ) * SC / SC := by field_simp
        _ ≤ 46137 * S2 / SC := by apply div_le_div_of_nonneg_right _ hSC.le; linarith
        _ = 46137 * ((S2 : ℝ) / SC) := by ring
        _ ≤ 46137 * g2 := mul_le_mul_of_nonneg_left hcut2 (by norm_num)
    left; rw [hG]; linarith [h1, hbL2, hWt0]
  push_neg at hcut2
  rcases le_total g2 ((SC / 2 : ℕ) / (SC : ℝ)) with hwin2 | hwin2
  · have hw19 := wfun_window g2 hg2 (by rw [hhalf] at hwin2; exact hwin2)
    have hq := (Nat.cast_le (α := ℝ)).mpr hwin; push_cast at hq
    have h1 : (cN : ℝ) / SA ≤ (52857300 / (SA:ℝ)) * wfun g2 := by
      rw [div_le_iff₀ hSA]
      have e : (52857300 / (SA:ℝ)) * wfun g2 * SA = 52857300 * wfun g2 := by field_simp
      rw [e]
      have hm := mul_le_mul_of_nonneg_left hw19 (by norm_num : (0:ℝ) ≤ 52857300)
      linarith [hq, hm]
    left; rw [hG]; linarith [h1, haW9, hLin0]
  rcases cover_sound _ cover2 (SC / 2) S2 hcov2 g2 hwin2 hcut2 with hclear2 | ⟨s2, hs2, he2, hb21, hb22⟩
  · left; rw [hG]; linarith [hclear2, haW9, hLin0]
  obtain ⟨i2, hi2, hsi2⟩ := List.mem_iff_getElem.mp (badOf_mem hs2 he2)
  have hb21' : (((badOf cover2).getD i2 (0, 0)).1 : ℝ) / SC ≤ g2 := by
    rw [List.getD_eq_getElem _ _ hi2, hsi2]; exact hb21
  have hb22' : g2 ≤ (((badOf cover2).getD i2 (0, 0)).2 : ℝ) / SC := by
    rw [List.getD_eq_getElem _ _ hi2, hsi2]; exact hb22
  -- gap 3: beyond the cutoff the pressure alone pays
  by_cases hcut3 : (S3 : ℝ) / SC ≤ g3
  · have h1 : (cN : ℝ) / SA ≤ (42034 / (SA:ℝ)) * g3 := by
      have hq := (Nat.cast_le (α := ℝ)).mpr hS3; push_cast at hq
      rw [div_le_iff₀ hSA]
      have e : (42034 / (SA:ℝ)) * g3 * SA = 42034 * g3 := by field_simp
      rw [e]
      calc (cN : ℝ) = (cN : ℝ) * SC / SC := by field_simp
        _ ≤ 42034 * S3 / SC := by apply div_le_div_of_nonneg_right _ hSC.le; linarith
        _ = 42034 * ((S3 : ℝ) / SC) := by ring
        _ ≤ 42034 * g3 := mul_le_mul_of_nonneg_left hcut3 (by norm_num)
    left; rw [hG]; linarith [h1, hbL3, hWt0]
  push_neg at hcut3
  rcases le_total g3 ((SC / 2 : ℕ) / (SC : ℝ)) with hwin3 | hwin3
  · have hw19 := wfun_window g3 hg3 (by rw [hhalf] at hwin3; exact hwin3)
    have hq := (Nat.cast_le (α := ℝ)).mpr hwin; push_cast at hq
    have h1 : (cN : ℝ) / SA ≤ (48244400 / (SA:ℝ)) * wfun g3 := by
      rw [div_le_iff₀ hSA]
      have e : (48244400 / (SA:ℝ)) * wfun g3 * SA = 48244400 * wfun g3 := by field_simp
      rw [e]
      have hm := mul_le_mul_of_nonneg_left hw19 (by norm_num : (0:ℝ) ≤ 48244400)
      linarith [hq, hm]
    left; rw [hG]; linarith [h1, haW12, hLin0]
  rcases cover_sound _ cover3 (SC / 2) S3 hcov3 g3 hwin3 hcut3 with hclear3 | ⟨s3, hs3, he3, hb31, hb32⟩
  · left; rw [hG]; linarith [hclear3, haW12, hLin0]
  obtain ⟨i3, hi3, hsi3⟩ := List.mem_iff_getElem.mp (badOf_mem hs3 he3)
  have hb31' : (((badOf cover3).getD i3 (0, 0)).1 : ℝ) / SC ≤ g3 := by
    rw [List.getD_eq_getElem _ _ hi3, hsi3]; exact hb31
  have hb32' : g3 ≤ (((badOf cover3).getD i3 (0, 0)).2 : ℝ) / SC := by
    rw [List.getD_eq_getElem _ _ hi3, hsi3]; exact hb32
  -- gap 4: beyond the cutoff the pressure alone pays
  by_cases hcut4 : (S4 : ℝ) / SC ≤ g4
  · have h1 : (cN : ℝ) / SA ≤ (24896 / (SA:ℝ)) * g4 := by
      have hq := (Nat.cast_le (α := ℝ)).mpr hS4; push_cast at hq
      rw [div_le_iff₀ hSA]
      have e : (24896 / (SA:ℝ)) * g4 * SA = 24896 * g4 := by field_simp
      rw [e]
      calc (cN : ℝ) = (cN : ℝ) * SC / SC := by field_simp
        _ ≤ 24896 * S4 / SC := by apply div_le_div_of_nonneg_right _ hSC.le; linarith
        _ = 24896 * ((S4 : ℝ) / SC) := by ring
        _ ≤ 24896 * g4 := mul_le_mul_of_nonneg_left hcut4 (by norm_num)
    left; rw [hG]; linarith [h1, hbL4, hWt0]
  push_neg at hcut4
  rcases le_total g4 ((SC / 2 : ℕ) / (SC : ℝ)) with hwin4 | hwin4
  · have hw19 := wfun_window g4 hg4 (by rw [hhalf] at hwin4; exact hwin4)
    have hq := (Nat.cast_le (α := ℝ)).mpr hwin; push_cast at hq
    have h1 : (cN : ℝ) / SA ≤ (25326800 / (SA:ℝ)) * wfun g4 := by
      rw [div_le_iff₀ hSA]
      have e : (25326800 / (SA:ℝ)) * wfun g4 * SA = 25326800 * wfun g4 := by field_simp
      rw [e]
      have hm := mul_le_mul_of_nonneg_left hw19 (by norm_num : (0:ℝ) ≤ 25326800)
      linarith [hq, hm]
    left; rw [hG]; linarith [h1, haW14, hLin0]
  rcases cover_sound _ cover4 (SC / 2) S4 hcov4 g4 hwin4 hcut4 with hclear4 | ⟨s4, hs4, he4, hb41, hb42⟩
  · left; rw [hG]; linarith [hclear4, haW14, hLin0]
  obtain ⟨i4, hi4, hsi4⟩ := List.mem_iff_getElem.mp (badOf_mem hs4 he4)
  have hb41' : (((badOf cover4).getD i4 (0, 0)).1 : ℝ) / SC ≤ g4 := by
    rw [List.getD_eq_getElem _ _ hi4, hsi4]; exact hb41
  have hb42' : g4 ≤ (((badOf cover4).getD i4 (0, 0)).2 : ℝ) / SC := by
    rw [List.getD_eq_getElem _ _ hi4, hsi4]; exact hb42
  exact hrun i0 i1 i2 i3 i4 hi0 hi1 hi2 hi3 hi4 g0 g1 g2 g3 g4 hb01' hb02' hb11' hb12' hb21' hb22' hb31' hb32' hb41' hb42'

end Zeta23Ext.Bridge.ThreePoint.SixW25P

end

/-! ###### certificate data `SixW25P`: pyramid table (495 blocks, 7374 finest cells, 14253 entries), 167720 leaves (half-space) ###### -/

noncomputable section

namespace Zeta23Ext.Bridge.ThreePoint.SixW25PData

open Zeta23Ext.Bridge.ThreePoint Zeta23Ext.Bridge.ThreePoint.Pyr Zeta23Ext.Bridge.ThreePoint.SixW25P

set_option maxRecDepth 100000

def TOP : ℕ := 7497405325609820960580801032216102383532393753305385486965402356498315787963785376799552397562623853702260735201149693511676577662584835040084951894272352869716230312993504509467414686500219761419741672674577961796161980608294197556465479455607246419104079064988516021714831321442021498294820367182374547522405222032063139952520693366923086917106452151441302481414143194755492310396130163736213135028026143959416853595066600507652395763513243873823047286497404427160960821558754763658183992077929444871596450043598381582744968759246348843399408587228065272706467653418479017902061776425015037645914587530941408862485117060037772806086618000159251519190253450699032062839655788832379733323151816710470858497271265195789488390433849204128056897144864088291385813040190518903880061756354324827827595637349256013847234133571661982837061116891202816047315464112111618177566713308894517023282595867914245614008153831024302185367045846421619079014444728482586151731805943898665884937615602376502048297454554526590100517025160087404211282903106180024300213963097323622317414657484449233693079927640431518553078778890161090903556474503382536477068223494677249379967077911291161558129924616545919535394954551198623878054440071197154775076188450244434734609735254739529885449634868189194699438262885187675090521794152096471772758577543471413142054472790838468288953870630583461477845034876260279369932187610567230895177244780749178222912653244361546922668051088232838806261741407968374159254783238090267727821792108303955103767005074184085152326066337318584188086664050857788959369315191816184093635667962239606500162024446998318615539492772221467858819639740818217011435316336270693340500507478643713257585421933935530080071833527758613924021076084877596690985794138104301020097222428738203346200030310714191182391349182541827250083330032143696044920160294862688447882459125262859276055554511255984964560606403647433130652009424869940419184853215696253304674324354358866201885018911353868832969991947486971564064779785238376730175519791371186117596946918649692281645390940752676342784216251854509241687135021546719649421503090530726935101251738328499330297225946268542244471378260212588211714666227766619467220296348519996761847633367472763699252859430247485664664994139325104722002180133407143355927302861345270835036822330813055503223156336138918579238096958998593436641871552642743075388350550366469831654258275494668075678138963738495958079956194312828730409971608561563846973529469388061672087177812888071030707102363958114068538731198010430415645306849995437092380890482829640289470664548380347177578514981803031475022352442357880625790016303262618755942520712705731963936995440303975563830686527913278604023534681295387166176668627121550166067687851692657249454221983731377518484073336189631701112250221003998170495046109986351109408918894264325330954203635079758771514966037848340725790132435388885179125342903830136522153231585603881861584857607149518280016505886707497342158134185833547944745687756217197291801408949081592799663859868654191337129111146813454308411263782128173748779354027592202018977711251942505328659284761234594600861905046551335226665466651135769580471148752396166415849214109395988458541982624270086300013530557674147425215961790662212107615526115362993739954426842082150505561952499723987992091167410281981497365385648404731132322316176838805898184676197602019530588350351040372981021074508595737020011728454471285093041304785243492974884898214073044972808594970560413974008912446508979516629280361040366465291905361205736948938318258312242586312120074363946803438958981731627958487103635533269992541755283090928533174466531695552754647038273706122504646085445619992534199846676377270545345489651222218585772792881177542330253116568874086393863001669551872864243189658795810627335251560551043435175029580904730263294276570472042012813811859248863884766307496132167807662070010939186909860040286897606991970657950480172859923562937325356173680978900592039530154858246251160785710062856249139283249515534907403693417104774492454781909641714579768257872558280641872399394129130804459658154401730324855332417490608994719443213073265714993233298077389706354217851378738248252103568104967409530158854360342602534918840647163393671156729638587451291157418440023871823564051007689746827570054990710428588501863997849265221474537342402364515336520388484731722657811579754941314622823462203864333765241892839006527967362633668888108852707694398689771301373824710369142455897620545824060697405464156184040221199832066736287891842598957538165660458167128238575492673634247975954037321501009638403628378382663207456511191716918914596894220019537915590646936783745512015658934708500564136850489536411077339316656472452007221088204520883702169512552894868410525384757013799122322535120090363091984566688436169114420537749242365689714121506056444175037957078701977583980320142088709581243203288939381084521496576
def BK_16 : ℕ := 102514058122
def BK_17 : ℕ := 91636865354
def BK_18 : ℕ := 80773004714
def BK_19 : ℕ := 70169019178
def BK_20 : ℕ := 60020123530
def BK_21 : ℕ := 50479647946
def BK_22 : ℕ := 41665041770
def BK_23 : ℕ := 33662019658
def BK_24 : ℕ := 26527728170
def BK_25 : ℕ := 20293431338
def BK_26 : ℕ := 14966998026
def BK_27 : ℕ := 10535347498
def BK_28 : ℕ := 6966931498
def BK_29 : ℕ := 4214282026
def BK_30 : ℕ := 41811545969353414574171861833
def BK_31 : ℕ := 53883023827468880395310092092182456717905704207294446281006477306192498263600466894940253990568220545547696227036430815025631947800194052334553461675436871864328391357184020334070442723170135542139355451307903495479262462576395544558472096868431041543340118682583946441615395442446986828915050335406569633853978433618887552378828126855676731741071037342796943649146341898368271978629821855737695598755169907951689653915606231068720864084020156682843108896015813914790471935077190178286079870467936385051596256238531152674550367376648172428802315228772169711977356217951653825693468171510062997421962013776613984870729127640528077613451845514629918858505108784253231457800619833278383903349694565496602456222025327915074108863813614614494890228444485367287112749666037550738606052151862717512746168488619673151536965138037362159853310319625298471175145862394642791533088610926222622014946164731557853610939644243253988953476578214834337104028339744620617088770571359342764010750503858228618731852451526780554719673728235009424744079546598811204609494408640970208289117467169709381356999169788221666318470129052213810120899729589619338118386692945779966972404019349695148027427545410456149650430993041985124118690988940231766268252637344486725238485781171827900430371762354441969337784629774743686361272836855521126361836556563798582426959763890456094570632021275771829232054138424259807843246383887368015487828361623169590230145151121222786981610102116753076977380472677025136535953987970613962090359840377509069103606625111723650800896158949712110114946636848244736467867258745796881778194662854132226063485558391215970318878143759148917428265829358934789730675926724646400713156795665333321312348880800530562177244688468970998077230053931311865479200863385107207305411691873615179283863886245308840096902402884261228951746094017126394562247605428228287862457906709084382129707892978525183599724263924238766340299568965463136166452735409790619028757250734491814729332323704791686373860550070381113006202826434741380430031734502030758549533782776603770343014956158456318872967770005208250584737503805245869679882169370817938900003089945299405066354544480758397942498663051101701029832691414288960428631240980072957119063295798015827310078344893000678175685770413165638675126133279248307486876088078463453792942247335026108315560537770120868487907736388355380200395997027086929318982722268919607824583405357384533893393231597781611171049746114658839072661891
def BK_32 : ℕ := 11388858393060686601266988669102067051667994757015173691581194730238504397604191137741905307474957016304102717116673572822251482153611950799308342723597109590360983808299985219050751605212431168962548172922175271674689728056674433943434667298593216092721728398692393957862526078428969439609257163214942442356263850468592761638078671433013671788854160465151635795728045853571070069667984625645172485955942173294475229981453811271862373948152346437194047039251678681562245449713145062170177986177482251671935716112316917754782688691348210221277979389305827564082233709618455110494939396062747461377014847564340760717700891482437760531771553016714243429549332975901269081296575306693264508444199908755089181272425985589911112765521606589581897337522694455991815240609830507668826838231397026378836158719600847544609484998587007701040376492803342454398141138016024398767650995441159528842063756647879434170923303593188484402974165680688140574937051087951221877822971572205887413363962578347515756231442396680182798300381552245477762388127106834742252221717590178405689316846964164815294937272506867460495586412696923526800479310596017215676881949965060178835234778475693357867737887286295296547380431934704631187742322466900422941863276386969685090532259306110049488208296208641083220414454394723555991608198259757296779999898364641519142436183288847776320603384233194079024805810735206118636607360787403894784920719901101388016046139783712284608208484169159501082830699050859595338929436644185468480761402790509153186487766642477612086809454266810513116966457804271660213218559763425469734960367799899893238973164126387983453299594746465816315555278920797305654556694474444667009864050415831093268673446491905120999325120261115504363604231154793926502097937173360751451402019163395100985572962407570543634760423418070739377736937204069628377227436140589499964268948359415381046286081439147585582857880629070777851138441053299901114146826076430711118833832174136215756953908312447994478614524472292164598042990023621090498245571741914750575252847619818400015406400882554314476744312236614636957593416141519022649200137621917994582446770874224175570798286576524218197734769834500416773954915486720448377749445531621795745860304926831655777438642656275495464060635367249589689507401821780052557755651488229640375750884649359840364795856422787698859685963221352018822220442293717767445985705420388441637508876398393067506816003501299327363449594584639357687822623518746605342526774144922887254409955298336616586898508321403493404327135829994827259930848541874847510493109238114378368501165047440045422208670022262323345891115354431975445394339345986116131890229138166234209067823555073801850437657853539763706697491305729823526558461132893115624325037188029652319401294174550353707201109449700664523327094676202169434218673179827614743307209328260146307045748596172855489447909051671796065931696092205918805551279675475700791241206428442153109625739937720457997776217828600244419503068254892624401280511838677584054820986064857216657368782006402763306291904277832757182070745672182369865108755120057547988412624463202430184457856308849159028581135237845548568288940250204133265450665536664541194224447215938030880740724523143381692337484442611564414028624716679979326444005989903525808405164485616217887179154078838356609399722246473851535539178052695681010347461790627403765127755377031118694809164882710844195238868894225706501838991841960665588363187882431797950262601689467517319045912142644890318205708360451255298542117546360529327091567415168956401607293490176228497988628128020786914031691539945697079823215426255742852935332269329683587987915749684884568177774790805164710854572830673411048714569224410590744891835389771660864747670826840535411574759317113302707261081169950596167987260973619189705259319660042436912456405812110629053903883735185598920438417190601338882748557336850125359842429742778475788437593452412744881362967401421222510048934359132095916952102778517892560549457380833580351105913626585779297223278042901894728824068693793650513229324830355357901909352386742892265476733253584065928114363001284019456825813254285136849223779881347057707648204848549124791678226575707807388784510762955074515958074488786466615632994821801460640406205049140672019950402432172952887757269314833960538309816606904043798223487479175932702320689350517338641376750967097761198112487535173230572068703421675962174851581448724800966116111160760494263774503537032176199039193627552596981383887642758815778222910321866315838078473662320332506327681272842714908444543619339642643839657088137146907294398813839060001403201757451074685834174041041455565644871898817739539405776867453682287453181457491372963971897979714360567716753236766665413063939766828034789518077634777903717901818099214313325620845570398938073683299272478587861594807572608499371796371906175025691912802663158866330009367416367933665972755072521440139310242
def BK_33 : ℕ := 408360572645183124819154658488954999534311011155734324797823523478311581975335657728026385859498892180714484690700351869049371217316757871980726298955961010170795786142056517887351784854410316306545011185857834759098178339807151056910334845761924500009168224411679677695403100523519243669529592228355676784062561792941438009004971200179219744154944325504006237086507176204872847750009858048689187150035394303099888127807421918642337898629070141829054417598993218348598767939332573114273861253157424704005174863348954875090683328724282788032770963916689298504298928093979410887388504972845112515769498945658435991230179204940218916061482652926544854131211770214434824449997863769885011754951692062154336003435513530397581541420076109517048372341526341177508277461083699847281545294506542215583628851589486201509876335635533671036625297863486016210669963458688245775738920058832427547297039461593232925498535371138880924448090767176862750818519491956735402851108912423939705740824059067933301997985400984444334387063138222826800549359970588611508994526636085274210267249445130363008167796859035603298196602276495707495348878457591561137812433200358265779737177234889188426791986896946123483394570564380929076559208191635449227793857209592331447207996065073877507496141635033590727178198557203085050773808365421461151765685718572458213894813645695347616245412788405301262850995244706848333483034692031053353920373624180727731547036454705015250174617367910439810927279530029364682275027843106072304769756344133633157178803717049846112366852951303190599803200880772944589044636997062475300970585977156008314267453644025595776286636439114881376907724845810964120873671334787794433670819849720025213532775544011875506436085046162937712686432904684855093363026905550496182817941023986104461287956070080137503453319701959234781303777826919177458695285988267449860390110580935466588570794880835315242482526264135287472274757181627585796157728762162391242264622352559635177787346922559767730926532490470204635837393594366562626637625303101818150231356863530096228932441218069083940976212892065442538771400722049705365784678512241206302632181588071131276300024331878577471377817840533663225271007460829392575232394313097036568807267680307940509676586336302080096602378246615557769496741167091548739422049146038092399449648338324580947007333208251430315434056203526635215537012094892720131168431385035845016965459157778447875909249376014753996737960167956857191512977965149556890197747929667709426078124053186306649768102298157108754284702622287167983032277849123695240030521647728707980905643276448837026857649633822509321712962961837572606783426391742485546082349971451285562100608508659043394061790773237415960872324843190913588102418269217175947934203681594067945253816609501787984922555060342841231671671235944359597471981355996026962472483776803729898015345747687200276200705621562086167795430459671988338637164308376762866725340811105762899452824367558429709538352447853403276563943443753467911256634510145971885091011233531687426127152251103300130322464083493699262193824602246542393195240179583088975265955245945443353107993817125928401474639255571851658908381726462854530039004314469220841522737644075060827260651342694077594434124013224783681667721307116910244383804344060961615693425594474026087657506069898824767973923456193819172951501075974241325072810684375469315997913057111220769089985537107455351426266267932923665911138324620258605718930832453241482061965683338603775039038122765924727751601796007219674554733840160911588914409507936757760447875570178478596872009489534472764530172649169941456559132514948963635247308714283098109430266491957130955658961430548912518147598442793756120375355506726582213683795988040014719736763991235218255412803437324375079901410979572232155685286605870959567438358023304888838934799344682295404690645547827100653936030385481389481215986272169284123264015152837081488884666952118934589142093362291317737299680413004883061835331893850522779815804964104265519871306401038119463475756743088703997248332757841106034362871941250029419386075110790226730257707575621911462811271286294271095060499514802092835712438954367899394839778951205276290703535938032713761123845352788861124705434119250831981195791647107957410718019022804824816097259060589999409061018811573358356224865276771473874492253577567264420201134756261008902952332383197926446007665150094983285544541129899366077594991050797314253846581057324415150432507696874130629731306108117219208625540487631470922545610790566381594144079437868650937990309898009707466241920678589154051456505132811879470444372901074817102503053618043345911021242591724636612561327350735673094359628117535383949300502088977962765008611473523530091481712100139772132868766588534271093916967663390262702436944910143145264821833900678732575389668904520930403555116713966711223831610234886568043604136455331968784927743625858061064972348362700295019429890
def BK_34 : ℕ := 17568851771464122647289318347839055095527858570322560226287404489197562042571658813699397538648481631520922403419437851461663743017491276823408615411643450265548341514942741932619724628540336703521027769436095466725379320468241829153504482278833536358124236810955652979743027969943015020517238954549596592934024619139628434970910334214985558455107062996779039552414893694314883947520649661835303691042959401335343826576578264254928329335547610395449471402090621959641827430275840772772679900109481844709918306514928883803632295889746500889826133708314046512280498691319993600090805557356223001490016292865153491493359191586136703141312759671636901367544080425060261650741211459996082867221974877307593124714764048876251640687301816592215716442023972746010503837820548325432505535982272022018864613990571095179513812694620502967934507193682137706261797267441355677108846193867008260072289234255160351844191179431437502801407776328639267355335368319259382344601273838726601182625758222976410347576657911681966155412615154859466205789576703651033421371569351354018497217212314409257447568648486042449934778164519292118344563975445631693071531209833203824103852098522752064871918743213850308859118999050776655211875687315708397450172164724208870112394800696838028070216551487225475795145239683359181783925771916532018732124479633445526736514561534217874838108400634881945401158197228906489909134523955809312434945855248235052591605417647028120082832237886249206616244466003239994655665207065125770606944432605555928223869074818995222922016113170105363903998250425285282310137347086953993306549033387010120556822300863226679345363393013860054589339182680152219208493080855406997295805605107090027284317357746612660369058169126516583862279631656037287706467033122670739943887598128361847489005354853790920330021624054494842940335002118498361893487670445761676302985589215076593771986376228037953293620689964166750744272250259845971415780698200186234369172897248343698802535857265070900254016226374591581401618366486067541239769456233113234673457144244956220404263514512141763536750567977757132159758436247672870140607550329324423291004372566731686079664699536953683795713699373477305916415162331286875700656510567479256425296783203514766019460458139955571517100088932245718085210275743089536481951875109590535610966287389346719091660925053848326839201403311152689130300992045096219225646469067527412020382228641028848865661091341422232469483308642652270868379523
def BK_35 : ℕ := 1634213128695229542419675073809003976910228002764047378333133783502809578479111735917464511087726387616654061225830280682582559675871291844463672354436775955813325299539812661166101175730179066931110323672543618446497136606458644090360938990539588466922635726965115616167749959356221217839346184406168075295798285549601119142318323414483807290581251330403005412027114681138684611040178124947282487884124111504149688421614992246473131959413334036261578469062015099151777415083625070948686896373656549370545411592143845205800465587546897801400598927619557393696988036006220941106254407814469675211855310852517
def BK_36 : ℕ := 3245725616862855593461555278985070417894368087822264046262026585027256901119166538529532228076058535255180529863855737712300738898785958031510850288879815244813459353833544492329581967655616123479294035532340449874339684580510830703993139910913583744415190541223625340835799867782813118647008272656859396172293634815359814859376988249723613377604319963362611446171989742310256230000486097213776456895984711220036899149131238036015266620959986234728233245376425085696132823495203880924506030810215276368803896647280147291587436060926638110701978789554141073792311321450088426210611569847600165092423642964549
def BK_37 : ℕ := 2047213486126828009745823169192932822967577117254311389744821974555362458436774628003537380673094739185953078691847009560974514771072494649159495
def BK_38 : ℕ := 2694622346
def BK_39 : ℕ := 84432078169263988763751175241
def BK_40 : ℕ := 4906205610
def BK_41 : ℕ := 5989079466
def BK_42 : ℕ := 6985807114
def BK_43 : ℕ := 7854746378
def BK_44 : ℕ := 8563880458
def BK_45 : ℕ := 9090825962
def BK_46 : ℕ := 9422569322
def BK_47 : ℕ := 9554956490
def BK_48 : ℕ := 9400773898
def BK_49 : ℕ := 8982433834
def BK_50 : ℕ := 8416692234
def BK_51 : ℕ := 7730271658
def BK_52 : ℕ := 6952494250
def BK_53 : ℕ := 6114031018
def BK_54 : ℕ := 5245705450
def BK_55 : ℕ := 4377384970
def BK_56 : ℕ := 3536987786
def BK_57 : ℕ := 2749628042
def BK_58 : ℕ := 38500007720591901914451834313
def BK_59 : ℕ := 1071386073926579881875705710685065631971695627160386439010548492724826926879907256202037097729101024829235012899593537887948796804390817160232743
def BK_60 : ℕ := 9140997580323623691073884185996275256120911808401282187874414649929925607489808820589320437099446552126724855773214908589275331769811364256088341449593268822027309194122138657738737840954728992723035233545806521351537678086809276171268497648196077226227852001501717101673845430729045367177014186918
def BK_61 : ℕ := 29411605545069358108619048849560615086607357028625484664341111397063740397232005831196966345147662972154146373615016656306134721772097024211716152707220729600848334501286373975809235743312819151573852186921065094108396434599890972155016748116883849745345836582667287775093015496611490926033577116112021001127267938397444598520134795358844688193054268319965998307238305907228459141377593377731661851576774692556966014570835780269180841200333168060206777738151615022324354573477104231847917900336563960343363270956589719590827750955646323846167808528006152603664950109963346502062290383491034475673332271682603944760761756607125029846945057949279016420307782907463756496759348069269212294583667795160751281625874148986704849561766656644723732003008079222024511486360296078304561169596038908399522099139505576623984770320124767541166238108975466610250195715500351281773541720102923014324252594545219943589506457439466041901453338918897553914142154804459988036594442496970477697597670662515230730183905665712279926137670342701508485308007569823811509677231520388330856752547382746370892699878631521311137264842764444904280324527338941878631711886092262827385753010450172015426906092745145147681331696064703662023404501549368644
def BK_62 : ℕ := 14456149606004455051419053868697060636237029974536939511528448964574788433080656722706172108662707139101832224398136223084308790903930256624448961743764743393056877799092237367246371742324403045199446711809337443557179347614746703210467337080436523698994156819171408577323132365688141635533944263702424878472429736438122224334692355246906866240935719624287081738221384907843159750933165382098589285359960920955012085204572581025771627083990462231246514297740507559338730462743803724941806698480652690493549683004843244073636787263713841637637721060980577558374533867147657929335196973399102312514050202280186807773746405902882707321427896178265934823580158612933993914909430356232523021086847309716418810706203060535931406200438188690197605025966653346205640254587911302413837429507383433100936575008614814277174901432581714279762725127072682338301964820120389351022789052032222072943310603201560380884534821349066865488959361351227861405225606005353454949041508239324153649736136782384480247794184399320338767337231192737135093084353004000611754072759381895071386825486870576942850683008808836364394711671098546008542379954454257509514925077120262785083910726592377144599192144220106410509956065591038868913343820984600225824770510074771524033956406552256375257514897064644042448885582054983813909680651120016751293117434861554435785336616198738616494124938118961954703308262396882884754489791960430521356766947645753365711384344289450510831957359936822997654578636551799295965020633390127936601287036480206080263193110339846877477933474876750268499881479291884510958884565547953478706127760567725558782043975687026448471664845343479272934914273548829393290853705846209015166141503775792962186006097434395631357385190364510779013894606878553888611233169772932815228256265155965265008741728809388119264696968609105134196515763678480088655676247960838465240893688498966605110834556681704386295108651769491832119060791365632956408250047439063705756115224740968930874192148922358687321422980231152041536149767352922868185718685073575242757701174473986980639224838374547116682745886780642083323365736171341032228214617043884861125159331879603692371453436973616830257350913980556853130999561709795208402034971183905566500990078672036930843294762381675738850740311256167212285214845683209039738906232676773324930826748241750440533608746010358706366534344417198255908965352573524194484258611632811213442235213445404198970703111995911815036488104012632137707502381276612489617302102024826775753678277619208344777178521064669587513989259690554560635501798638696753527467179530536833570202633516991516628054941147727655104180277363938205830426710523284902071584269188683553101697216326975010175210441807833909308770698706059678738859679769298114453362751867373747517727133994799622607915331017192689837996249915818170253802450901468588949619316508973780600314841719122706334005370743219405580321087321923195116111887825360005173494103582331194408995226923857852149814216328723099022541657959162480352932437849333603727711848258044783853332359482393908134834129339744357920317389384108580963424012986561906797417755208926907892254286318822617326605821403193037294345991619353221825585454610195179557933322152410269055364466175000654316936704678037065499084247823785237045850746445056167907772433274768883561440286446708360382444086232730507321738029912734441327595429478332161636452566045218404775273581723300126205157947476795243677695435614196954586297104201889595820514528182435573529895189331330475764574722230195662903430150260136615800757208625184831943331034780729758217699098835490651924237689989552431959753712207816290489527890328155333082959387305716592899599929046649649644792127941584280423317851041100140308539456375739615581537186406007402146212317290584304350984259381837477146375654265098907666980314852164238009872170454937926151034387235198628765941701594961523435412520391116132751477876573283441701589063787919837590150412298777025680273879116239139949931249533643945174729322086764589456645878411278268161734541814009827851710805483323352084210382275657962454275414222829788250197402467672697531850938417214407982410910997912813156554253007163844500755805920222099425987169653840032512128644640315605655801915500038249126536696277221609058003042598308103553148123215584132218366882729094269239352954542940311183437763099161179573758413617323511478716465561550349337511454114117406746714247869488024711464482971789605475475871199105347902279759684940310513433957412345529881133332512328354247991068131277719678224581177593111296456123801126092429717358189688680365321630247360606429040302929466613469376737340790538685103378259430726378008950647166725359569903332353670440456294744075439355648540535434280054211684199000815500455782205844448657876102023142202599137666826463678989505079266119339951995118113841761909958366566198134372990288394696812303766115359285808895007079946031845401465289273038707388850946
def BK_63 : ℕ := 3396022062143911735592818672083945341554387404759269380196321471470497641731371145140906903473637929167152374954751081178335311120661944989606581227839409850363813880812375365244538410615597983168655430390379832248595141982196564477272946329271944289190452543082912844357808115016958766762614215105074839386305669936633987367185026497995008624303176786234150997508343014754251681126146035239812257039232848173671735332092664315060119980017538245696719084998854971008971370885853643896247622498233834378386783650600084708652394339257978246241290912910983322951205628734143328513878333081370247842216073336062511674065304197655232778271532361433068181252285314710138752401838971758066853827367616690157487454339067580050133906035766126883786668370593345718835799062583788789800742678786363194442606122991315733040138825252172000912830944604416051889380766873409172493315934525450810099055126525476378369280450067038594460341539623662404679295853091267532099626783846138594962436100164900001384110892128637422211484477116582883430118174135975238194156656635378628232455017529140064576234799357321135345357301007897654720376333022004852075897473470245922436685944658287889527040080991137751445603231034402161724206599549177554232347397118302565845887203752205609920895491728986140639261769821942667838016135110362129906039170754203773699420935367635939083282529609829330040051965295169814669033079736131483422100093877585549011798827364818502320230916739887770432745220920436334235141486345340859694741576792228200683611283335177883941238658008291186389327450437976756606499447578813477778969700787742430933286632601518558027829880133500987568342531095895229298354174271230567647084060835109968034485434636817153391138024054270558665237072756371889763957375378129008736755925669212934491575750919380959089672193952135899724151354092707632263970466279709598215949522111456735380050597641205832944916093153073252722541639891830385634107872563713333019560712486781247214242901942176867126646306555786613546062149781157492707882742807510000252903460325633278480849689482470290913011525814865189004403069738344580670734965467807600586580657239516332830096239509672158942152992397171232003924216710443515764981405267596928294687898121977343580416489113402154762443571286085050931569915996371827883837669641367685487023109077810713355700161388370213541232740093639602723244928881358967765047933878224807872035853411425492398927045366674326773960195244197373229839119297068449088737416093250268138073131877811837574730604790634555931034437094981054235301834265777568693069618699171190442498554023501966358609775584047437658365296223346231997807450722287376793639610293990061113134839313684996197821812608521992624478045018604043172707503078864219552417225502168915651766457917965848145705160007829717754316134021805584407384782753051271563494890715173206965855780862903001805921977420617896708275266541590758456907942976675076073071216591739420409839103711252528894193771758766635824639045551504158547743923314693560079839058396513589548799752046267930741992082390900346725946738573208662815959916142831783903100469422646244806783353048859936995775326395206819579498448251938700827926448940926921352441003717847450503963454280185176205581508696062948930849695210847198689058942715022139850205029032996743609961494958482303105882813234846346943117882782809571286770960069220537133646547656713861041298882744847121998171240546668347271483331347272793630656991176605941797043997874147063627940971483167686742047110010862891017776398744858237962140354917470488329812626738947654153621718688928859170834405163662530963993767522140534288273898998972017729381648756632091852903433723448349007541488320769710717605161956439966767488999524356750282841076567133683929634663238399331815873010968324141722112696065881264501859055594601038132877995128068536100893648800904420734660839728143661070855226330798558263788077396586492348076990150240606395564077942101773394890309475114521934366755442878848886088619628910464627074989719162660987191553454947600768380391985591378365298602726463594736148824058374271433645978336913928533128927424579076535198824380346109798155374603118073421818333326956558682080629415168567301261794815820474541814950495232002308938320684316593141578396864142649432194716307828658198303362883555519171398881873588389595611417783969525281129254543993144331281310926710464442365880215962202359734672882388193308564171062916947244732559974925399368746155835847963723708241981316546979252886153481670717652590159764006866531328306931815562978600307595673299882510816811168264815890051522299931429279389766396992232313648204386043872188862038302995613992310157828519185836840104243357435249301009606594932592399046473489846108177778080707627629407924059025279674012498126833260196270204500034107854749653697082737529520340864217969789949450628490031129016600095511811254432992450826218247275261071377484271780503040192377954
def BK_64 : ℕ := 4098816338786593390316657745772558921788468228760882344274895413847318260055196898660143436806226174750168737072032735842486823750474179523905479291252967566128817584555304482539652274910427167581119186677137767225784355533013544042498671218054029498715732416848286095387672116618658639241447900548013569893957657515203945923576534327855585997656650035762764645337006387437433164518728174796128296748745331217192060771337173214789938786908800682952027008577088609381184395413853662659070262154521236970647475536015210917364770721819039638016798817579817613127869604381407570830621672319261204297214603310652764713950220167465352763053627781567518045625555607864261578140151157818898382875562414378981609940978291397779171135907779586995006590169628141207672039836768429711600056164469805946586619304353110860305067902961033390916024533533005200314429439208386923086806396255132297194950001777163540508328312813344575757495531657608166373742671360919563437447513604631979342448219848979225662164184598459483438778209486510546347735509166204287993616209371365308581713520163569178684659072254893245923490076703313006985119827416393409078356363476301405420194933594873122827981374743815552161430964175267237091821085743456999291046631586622801997308691265687358514348762728746942635116392070876524270451276136431527788968411024980963048590883259082428564094228828903535142818623686455174435403928320571099532023526550061789642772642102347799600310046217323216703775033858981957675883730784198160180709166460846418954535832169187258363758912734752086607578621359331432955339222332955484947316758198330120780008614477718475779948038874833986333593387684229248447490943201888741953403434954268858757225605446665048522880644486458777119664726726223402667922289236372351090080042438902979763586887418691275803866879228679951100058261586323202180167702467365217891081995067358096193798488169036025848433054258607319409851311286282503440655512046656897996270518484341453858107454989152021830200109703908439044365684258367821923431492566688169528065218431154453766737521800554944076268493128124063702584501163924880687004123108284147535192692818924648198955841677042894179018693828804932917984412881909768070421211135716128605066596075400477361598529423636438844466386904437496623767965724506098676490594736724829938142086084436711439355048705006838478431407270876975155365542422261038494438558391304103855312295008795063318280828619537502568576985853301252727369256487922588923569179016852651924834580116435317440378904725966920331508333162700988888550655786741331524946845831442956717900389533553318536724711034242192064771931955015276383748082020999158816242699529235996795540836129301703953199405612012714817495585339853739330657350055110027185318274983995923247795269284735366747090366315119494953150310649685539529865802026505504401831963143350530366997107461187348053979865439430717249527708437750528495877286410174866099478571298519757193627486474061792696018534681559207127099764743921190271176180558183973277155182637099510426454580453922242466569689215614276758562501773939135117125760003892726840081131986785378306891217466892471839435583453401703384510030951072162955249285456983022305303698334307437535323976877648829826999570543278820878185947328291538493943535703412413353785114727030841277824416617418584348423582473413281838121577404240558897978702522850199251916342900719729868231176209920926545461098401123051375131903919944106245004044747544080590631876734317828752547070911041471733893984992319983286583901425865063520085444224896318121552333723178635497391132238059919644185996185030174191401243017884717837224925465246029321929329878457848865424833251328334108028629053409472135661035341998310184843690237500519179184429577879353870320942521042416461769678670925295895898010469848435377665007371271219390238039436312711770283107228210292437433938974188341919741784601310994547832909701133376008562747672996941198210548096552739738962985155225256352692224045276043221722582155953149771966198007371359929857553813391035446285789936029911112667541113431741215960876346979695746978733734450104749107133851059043831850620707305208537634669762350510155049136701436177131547246662711727102012610349907471813630929280720449289606558929772313943734775781363021503984598341232970302529080661988118076386550599252647565524912110908979191713035089327292073882408588728362754992129508475376537552667226889769452829905252226386044846253125978320027711570716361249779899473251873790799667304879250378244595893174106982520135131485732305690444893395021500604638004669262770339717004922390228631084697779169176025444322504767714555939227659852141215626283072000783431559283817538427146981760153509345295341632046468250918527020940857895664420125410123555556826725573549252723180325215133913005067437284485288746921676581490153763898438897056993701650673272016967898008500658671531679565579551688712317356173162848695877634
def BK_65 : ℕ := 3343023441794673615856744341160304134808187053902897624486336599744127380729032352575907905263815653057499183220017155604131720187599224415567252562079492402584431142943144223589649591207734259959836579187631535166147473306039178065971132418987662121149026921230572947465089613306813008813070001053188795658459107694471098961187760785326809704676227451148787312488323196320565293009642302115412354234670017954329958964247341497427319451799768392821294362014707494829070983481794840610570278379251744001164866583680329227695771025841335840540175447471064621332955451993218648992804076348830593009056011277272824872916004619360725717420980330418545155882719301146969281004500386120433591875782459136827693962041810296263521261595788789663740001213860813791894733978978436273517375872230237281060575655208523496291905319624252458165103355817842045361022046061945088205572882864818705924697035583534700081880820034326267788111694232541481347212463896691383139370391285508698956392937478210816700217484655423405585965242413815259354854740997841179129334097381468861518998192116818979196129468532684323670123651791502177854407319479516628067899161315954458562327740372997242673983209137952807838474265363976223967392136564837334830551640960033716778130141593552698704905671261413924142603809580861673159706937014101300992359885247434331922648816797855848079237294916041819669116391186916517488886498065457529468228985113001381495611535878485274088532916662668753387922548513708840676885800536583976654755582409504716075028233425865801482629037593914066350503017764597547081771648669203420810670995463929980123608194263647986418338791619304861340107855210595968923083845229125915321375029037345892069672215176943020175016716827129246442331500912272665409491812332865542368516470258900407747658063827119567109889619620990281167868100764554040759380657535901449088949107963999139189554796245126227333763564836024345541258044826530193530709062468519356284963530659632341248687540056651519141000613932005603208291472822466615756454505642085111758148977342889557066375648353948568877793118650519945286677170615783828371243869977122577977862822751030109043334402560915821508509127241417224145058103427533756684356316130825444667208072478541805799504572432147919413863128147890735730445983151164735546374029396845581020825137885998873973230998144503157148807918071712801543864153256147355957703572093523002532178297546855008611523464047037712845606081448578135921603747
def BK_66 : ℕ := 12456092451063091803962853215756714243413039812390073197574767227909994867971416487836128706429646741194515385548928328922692593190297066462606227322917640469082589257093113453795979975534368203331860862658481539876787745603199514930100816136411300312755348564348510729313102097724670857784699816238180171279776779145065149519150283587130439435608103099091487927399954338451701311328250277587485648519168388855394197890558947274284162261257010402863022474280562514969929674916680809236880363329288359470818082249568265355597380853426155223221503635987864757934201686260306999982713041740064255916282423227640564472952301420678435371503892186996179184216469767262507882863438164720126535253509737353257639476223534801032342938927799441390372723978135802346157231230286899419802007317078492692750551278253801100758104696655928883701720545021507116055485008260610155669189082390478122523510193058611930580019841269668717901787096472332006430238853609421581853242979928160880926008508690659068506510480060075302414610498409442258955460171207611241967371115685346275838976710437610997138770113624822848272841337368702868631199231350352412187257005254534721694182925267381224675152629220530499187792605243430147701732392754777225121621582344069470933056596890878034940858386587870014885733036383817403194008242850690470956015566197889967944616871294437802862038275340859986792677317083407159999727824576144286290494258721209570940390540755337830942420558714119406571411799862318680456276731718054773059578606626900558095948762166266430252378549909493485609481627311578434448271576233550339579768672075054389970738398318498491970653693845304489110572873701082823205111162208737457959392916861471413532699575992287084224976043730641345645463700727720662075967890559190047382670055360984598040525376266603885696137997919689585093457642546379669562401955473262127241420774479021038165683547526889224216134556525009054757695776056970163048934506438147375701436116951977707385048946139121226661666202113130472091046345925198845273854377075954301348759816516967750903389417129007726519294935612932768189039642731053307918839683157382628223826168837558627481452406169415811598518731568880833427068616841527529671640258569808124703209719298394542906772439082438221994356414033723812649848772605139136590176014055240531576327735034097028799723940874224516755258532338285935360102191197921841427265097490061216130836633280940193220765706262451473078259798098750787996585987
def BK_67 : ℕ := 25199937047827597342083131100745248703786961592581212984007029753483457807944119135215658629549659372349640750841562650894604782563079205070324972005471319997415328444776169407598836810047693648663704596466866774117458530805966551532163900982942308411156275511739305908421164778828333453562915257694991226183188534363034407680499880806629019378990168796087619931022526768932895757446597215068231246403628498612825578389274234787268830545518939601602456400107225498863500491366637090943709850651212374452062442208473326771972008004429152349174664585976491631010149604920610485337869453669853899178431860474847701300460669378842518128563274748612481708232685468683002278044340532919004569307812287012239269759900353546497841137463451014059395461133443037783226585979392803575831640141436059364471723523382305131447116562502692353691023145140846936441554854057794025053171791964419991212091883858653832020973285936010099590805941089002742909139534149106124822720190812171289318913108067927178473307118902190637969320602941768776341956970514736251054293279136806582791667091655479101114752751507622366492483846923649070853464374925797795974615545681392610430480121054650806211552247184114746633292955665896046686513779217564292
def BK_68 : ℕ := 1298484969263662200667813223815162904542419732929448438593513452039826528614324345521158079782210296990904421675115978497305411442381443582074805634170097659696972538061159344897752798554515673491061517300458265677095835059613583156981888690230986499550395957438738572953321731866729800077364247044717462761857161068408212739158357361999921566857385696392173091179518655987705437716057663086114153250146778379440163114668282958786874793958926680281615758557353650290382823463277531460733730832902983586745956330816388580481758617638928965453765358699339062615242083914804164328415002435199815086929134896261
def BK_69 : ℕ := 10489861617562598728054088718113510628001887252175555050108163095569893394379272673535617348776259192348834298209806605980786456913334217351086227407994149677351075356860433327676427646593745218744534813358521369347911463857700489734555226618258180432776502283102065499148399650541805699681192590406
def BK_70 : ℕ := 14158563508292513539068278910478916723623764794267032337347956371949497240949928752128856061953637890215816482035475783123671531658367682245201271719973026628698536920476908968293207136215487666711001647250508157964426167486038473584356490983171709808598175627686987915114554966302541385902951057862
def BK_71 : ℕ := 1315480497183967230571488174221240034943956110301796757170083158195444358287080675697267676989323203616447506129749648095168752198498997226732359
def BK_72 : ℕ := 13363773437029698603683769520437555153239506585005323589198460657128
def BK_73 : ℕ := 15622946542926976108929125224416146335375383616969606769764255412232
def BK_74 : ℕ := 17664697114912662322614248913118241380167552013942554174488478204680
def BK_75 : ℕ := 2775171882
def BK_76 : ℕ := 3030944394
def BK_77 : ℕ := 3229804970
def BK_78 : ℕ := 3365296554
def BK_79 : ℕ := 3433727114
def BK_80 : ℕ := 3401165738
def BK_81 : ℕ := 3272246186
def BK_82 : ℕ := 3086926122
def BK_83 : ℕ := 2853445866
def BK_84 : ℕ := 2581500842
def BK_85 : ℕ := 2281813386
def BK_86 : ℕ := 36920766316406437232675398761
def BK_87 : ℕ := 10599388250060422005226681288001836791265609942244828132984226164616
def BK_88 : ℕ := 13381079237881441231961216662002535779985852339502313467911832772050295860898813358031105467269644112470883146865938939111436145400879271736591524543357245041687947172775790047106283740156507067164576366336372557203855609891965062642165020018752531609849665915973284480964148859188430957863205569318
def BK_89 : ℕ := 771914029183800012478041317585488568441190957612321047079924000485543232653546499442730606986660852812242419747153416851869675885408383077782087
def BK_90 : ℕ := 567612758462538952760717108803052855312020869262475629745926390274368304146442545081056079636836842212018730748672684751899088581340568136456647
def BK_91 : ℕ := 940320160872826103349038199801490498174109223621681901878409542247536216013102520270500775065499697052971604639247196001289134655987570796690689013440066462547330282807468476244615426803302939868284020546560899867809230094936978615262412145728035059962710614482627941355315017326843342403030601385524673125425157278906281091465508941289766548951412481882398191483148066872199241965928473743939048388059177920693743687745387389927489768132368771237243777848842446747027587083911681252297022858816929035751149278331736148452731417863304637417497737979652292397445335256240836344959594419410910004974752498309
def BK_92 : ℕ := 18825817867532562577984446359492618819020186452789836946606701632415322818336754704232414295586262652973168191954248407297857056758391417950247844254720555453162140864834476512291547351583641885746157339118584498671722577595776678990242228114433264949097586427692566334018316006511516898327808943327926310864709495579065506783382491659210078088325125023356442631548172974428009653403491633039738451892705812573800382501600055347002997451998731301212081992691266557516330881333701227297887271309578910956744342493997346942764282013930903438248739812775016777894364875811210552741279760043235577295338834981912387154539587195638415657082263994752989517139079470898773246601063587588724912380041707974836024765254319037308634389865728292923824206270073329566129771326490706301406840692100842958824199292968220149663425303717568436745290414887287268429091178282350220202900695568182296590714763053606185847708743051942586273014118301168576785520411318938124365146553194136672373048942992529209169904822695450772569480276131932400305666133742415589576462034746012708351487700943481997152017930722712836737478850352933736737170093025769527821372116979089224656037531548483659463674936141008054008789599894926964807823563011770116
def BK_93 : ℕ := 9906975648350174079457640585634132629946215154521267009684931294636658340662850370268230072032081379080135126886567495205699857775258104937596460357618719997379544465300515495603101537009444670548310402599483692275028728932342852636150085730581366095755043024471027004318423516563755203797471706999397110145279785258484332317673957262904623846748715968584035777241567325597272833082060679840802554643010931383548331947131888985684104204887520408304666590031592245396426207946038816368720195974403792127612241943159891210483707633023490360766036087736959284132049661268908725065106895976488709167510862856821711896226934073735160390213118759724416597239356347692928141004106709032158081463181105816636092845671834787451964407500342582731366916000078047247545564370918226761017654612657427690763092080657028309643947682013776439977754860625722371216365680875249324401306759333238650862440876597205184754663349505836091743834801353778609022362300998985070798580478129323252897555346525779596297043979227535447039755305979130479592034411715540180367945932570226055672800101164226784065182005948184321171565284027368742597290872456203390760156251463009984097287337442690499375732790220427657698335649461435377092809658007948196
def BK_94 : ℕ := 3977759088087180133392267179211513603929312880525234981217438491955464275824221164917171976402593613676238543930184246695091220752953639563089578012486199822088015378477803283574263086956985222083778202417234058521228563972979002912316000131399797553415812596769176828509501801340741104989125960009620856606488817729684691007636697890656180768852499334800002695533790103591032039907955982782018292923686992635124399853433160700302155997814798268636433097235674653838379974209180297386667501515878195172047762519670507217908706906556039721829329874933361269054716897882409285214779582912968025202898490116885636809676352266036116915405787706145762314407626499316114620823908521794471206750957456569252611530736522224859577762945491108397076462129307216223620684978883209653256753481491220331057011985767318456601652146484070894665754567000454332879601103323055177518138335429564488767304967913869119740450730002205484731303435722762888516289055380024320514330488010829065322412280035451128846168352928077119910926506121976135570608788678608652649398282331437218398809657668776975614060550943227225979190364219272040749182066136767597152866142196678954542064974475971181228041076458471024776275760123880335559060596156337982038276161157487553025371304149280035407076288924044948200352013208724914564286057749330296861317574694305577933006789332136024278904395311533849747821833466530577826074100379444973518832844605999662538499229812677533350928264196608834386966946309281940112130866391836455075630587808102745528931469074547817608130671297835179241481958041765632438223324881372008359639567273422364284503106193592963381468712375904285388039557279477700124785943232490129357131052056433755892035431916243097567148188138870537344446484528071793365575867314739578768340453389305206738597347609476699963217304757745444408948195582132005243749656958416237221618404169367603576670672693215501729427083719532399054609249048509151356199230054306049693675879985296639368456326798169479686451076689270747890287711226122140852221187985762880641788874749587858323086530271575660617028961642775846790409695849041277167004491402763923731960934410078304409277604337307728496202039869922631523052137965977099778361026954196548065666289074020823663032626388677315762596032221112831586435988287292163562746091185138597520604902200331545908639268759791264308775646242737303545590513076991339676006530389901795714138799921433007941659534373464648854853561380706137621560547
def BK_95 : ℕ := 606334528846399261948873591494400990676590636846607762617117577202466561565782373823138459322828989638199066998574919646106237441479296878362178165956418742182813695204647651562561935405870837025578013632754701859404758421521550062645089388217754266693333014839342277994198605502440182345229806354900926557831590279285395759204860825517593383405846428965955846077226745417626435770403803592768443103846206200758210843738291382560296050355203767197818727689791418180086015209948929002308907265088452857742142952578028421720380460952625829820163456068400749310075026988465152444720252803132687430222371191096284384243500452973073914923329179107040070219167074526206541889630810198662300966299065088075449217070798752338721456693653392986588115203602522322337183796843804789920786666788215834103628067735490291606162992955648526177650874412394269768502259825627197642390265361115013189864280089005166378475037787473430223995966712093153885304969318390060324506728474683225551896485928102923535450226606827098391397788242949694654938114403470179241579699571059127634867683149761551444701204959962625195106999828135993104145481687168306623781145124239237631067560398056090641943685467952466341651945730711785104843537511394973412250460849825728892257812075985710467660894064458577569943379893470192342408972205228889038487989796355195420412663054767400222392374362645467959958092858957739411322047394977948886045431852383709854554202993351190952041924523181416703626896164304220628077194027312270848225681173882869765760881244558411798035694989796008688819561665176793110139373253201526762921960667907326477279949043914674895991221332582663241132656689440958541786865295597821240993145912461802975597399730021978147682726875730847258905371221503275030471063953740586549246583596635320056501598929417699329497388102006780870931617834935294016023795609014252038806400812992241526767332887047245271634974354397849711988676247454461125742888831276792132188031721504848458563273126097641962529873504498692010360460455341192441418954110966334726495141640602618955963547566421187035009393729969317926020162107425545064691047013274207036214511179810821265404435718649615252150597339320931645242495193616906227630904611701485818765184802878379559061775353024596656538969797685897797670008100524824296905264243331467420093592609711755278667815371947826383014814138284806734172690249412364553713044525522908846826055326995524788043801554645738593906026806169953269217283
def BK_96 : ℕ := 187381537284968587052116138026963357789954915614700990181571548890999513438348192935197906949585580802215653576825912904583068924445154761582247936317083846768289145571555936288240632029360194216289437498207588087218020569321672156436588638903872905464901532393575484500371486933093499142850770399140124201786910488465361148056823609387362478743884545344727193898644283022965874250701557035978376621011564586433154074729364071831322141332050061958408942893070650365953328765205315717244574563605375709007236445397544195116872787548491551549743078648778188767995373020617375789269914943038931003648090040382797068449089428737021181071480770740774861969666314887074065038667784069049346130931000109343388830803832131142276357700257275560036686144188710934081587328201911513759467652621280901069375951649384883749448990172620635855136647813610402052265778903258646329485269007969676059773995794665560080140609563653737342862177140676309710151056849121308985516743314080269986700648350323586574667053107749212676235410262053442374795827084263785056714358200229059657152475083502412625680054033271931200806624043088481116539727737294619699901511326046015259806403233369174817296281400071678236240107001365777926800062132683817321076126811639502521386250666707675231476199212085143006122290470308379784227461298321694396751275172534921430810064686145596422150036390314151322090023964791787875911823936147289664093918268326936732175983164165053628224420088936395292637862123226355329730532810942766288306539379957500250846104434547341742399159181581793040614709461818810458190701577897893164930767699422114991277475274037668367255053617627428093814056952407040271843184836988419728103474423580026333798874838016362307551835776170524696910174456052675704711708023762616518227201335238039683842708436268764535855852034780700257003381284717280099488247735276576203026284840048284624104091136427059929516202791471234772132456825460019095947037929238227752916781412987701148944910215575802748887515476995671932286378615211608627111247519839462749789277946190067442345517977847094935433990360246836547265750731232212106794988079019819959957582737697394414950985892970253216381159058520772941117430723885191456996258802128626186720415762234521701195266154540846206518754178213222608224417845239597719591029323510716187113510641372584812097393907457547547132710026412209000060481033448352439251459148198884714083385870781789212704668474945414196921183356468902676649756511727203349468019329759634071798447097645554873760270572371133439137046625800738714196888480000012346061903934020999497844116787505906589227569607354748641918816912341638118945486404891094889343559671981253462664875551003507752262652837570465089671999808163814554524496082157002689816673523786559080968692374105297537427092846559492977321621092901627713377222951787184896651417508020155876233351299641862685501686961635226507817364318588877206399384353479632301750053990975999751763203138231954143330479730083089863525162147102649533690886124662360676222494222174400845538865519152421468861379339635468876325107355189921929923342320504514297791097001463456316165311084810959712793967045363786229866852344362098505142075383937298011264251717093071478492182547421561525814149592147173090486845043624628272604801238451413088459640079306607553084576397371772467254192553526174127629221030517736712874769312143437000953246318093298711430556362705252617758854729772634348830940794352525586899160900746738460912587102195055096509823581420576481515897770213070037698726912137009638260838703439961123914284892105485766215232974688667082375091324095196347951592106079944874417666031560643556390702260900920685929064832317393565811900608818616149253108049693148276085965759548534596457349479255195720589920432908118933764952875161341689369933867449867677112279282959680398938595996867032250275268917195287431490745035458603220506588571857598073297744269335257096382682549369562426919271288718019953993201623997380008095420894569072322103443219031890371040679631679080885961865817290297824926349146517915886837536443611844779508183268363323484185512447529716069060912418334869408895314818895330738808343671950244962348235143361270944722767066527447977858836951275483329324490399112767800416195257659530431223579925282698920966531999615088863676496759175110789058880640495478043273046557735639626267937828411020466260678590336921770788322991132451018709844370545961739769240291173555808597074549617583986027592744178225838079642195984513325460767239880216224482642661181418741745224191672477773235583673515620482950315227786982387579817414037180099623924001712081991316800658869396796408881406405650793972713361659366722197597853553871239248501162937715782059880970207222993411839289476781296316914845831766121744607837277747444393324043534192343282076802844449707330407414204199472329143328896478637977162963472684874959494297392501670828713336374846415799657172579574406447106
def BK_97 : ℕ := 2734401695631897421536536254530710578989986863165123645070944160166675037639391634882034389877515940477370481129049881930756213335306428343947622407838277811627701140167111396515650998313884203127378837722462897960090746114413175928714384469879336681833837441577003419398825838836092671869259955924504714691643338823892722834893982062704087565464247956515434873816034154731813005804152494587635906746200147075789373203681899358506604772556999845162593516656551349594270494687000192762944907700758539238673628263163552075673817385955528291485800457350253736613072833163251139625015102975707011622782005699952868248208218610026162921676394987508645460740555294772794728280538347699733580215414892640647433453149401093218867266112480401291331372526252163126808427506671319731010534574680481610308455230353542619356816919624407946748558191464504816952655287910530920149730102484954803780466555929705289469095174037468638851334525165931193510262012016004565713881570497068016662321365309500716345616933539797700875095168656647707562472533871855076675430942669044410195511086675225110947352657208755777886251603636118275714667827802448929022260193561384935079240780571391639610106773047941424066285371372627151168089426841582447904691847854706974567257996667588045686691362344254542487246864089163443866241082235208296046056811131006964840464830393172050457966656800517382200268327370651597956830044668100266506918747941007105507605559711425462470391210018853925152652798819176841413219347462093920714713280976386755323849342632215621876483775641211761144450506835098341031020147228212159741275129542858103322820179250492779557942477093948581742602781455217821650013132762823300273131967948661970375978342632076886634439970980718471451390221377548724099568332563006220834574899809224479765850152632742031252078748892312461783342581352325612549857727479799680264053034923755031894311862751932333071968130408534979730035092178400436419501084691341887436609735943961226587820534942392858686402857483774398168983282888056069463179851175254192373913182091462818712258717120453973611525466547787474441378476443409529722671580210605957772411006847632200093310707033769279278694398917458807471309265040217276960603160716346766626306767836236856704704990003124002978599840242378826839937577767931668083972254496427180306984038411756195397036943827636825636729728242550503187072250558966427127811862082428025788105872757164010273217137111606668118754874817476052968369658406958403665797575798081388473543249804307341943468786448305693120539047654026398606652635491489787488529331314396563085150967371644204256616871786296199983790617613965539347979423847460529525890988916639212074246451568932631560787008180706660571323882156963017848442295053385667289343532796343005569345099167115828240766040286666352607240045086702988470267228356404090549930704169014789732731480458190727189310801802815666583171190399572747232929646708529904380105645682398619196468366460758292125077194388787679898955657431377910781817756271089416146303121920796402963633108878445196225911692207153922572180175738073197366248485097650805676316805047278474865892035516529665758434288032396475995525436537221873182706259467446408464764905297324777311479562539223052482080335788072403459740540072148599490183890950358484139866779114600634759041672831395842576146957778741041771261010245542475648675502915946144197283893401216561172298795577588118790217244850076720311978954348849304288765089078277983495442859740840077508563458153852346773429076912571414742808885713619899144157345104151718462691236397121220156667469514936214698706547032157155817755739440232131391021592248389179006729553839690732635735536602773500626230273584733381243115601997661713149248543594629526559738116598955257428505802444557794753626317362517889194869624470224964583356905739426525366243419806503105415384092783491815557855158257055509649227709286177282324275724574111573840522783605064182188669375011456216732646957700939486309200018592429070398362571736094242209027675416153564177307702439582511371766422515876083622971986251313541174466575927359501257748768308136903702053746363751119266584233189750863491768577904586574819419949859408067360324508597936896449145753280107158768963241984506968950902141637417081496749785812227243991960719934856588161045124378438625218162631390389815140546513400051219304567792159475773737011982562367138582293692775420198523614633254485164776974910301311512713274668585912026671879637679440255557358419434058277010286703137033592009885912933916474515708246840348662174538033128156962493429085124041092654321032946325915105662739595694951305643331546517499161134710287703981198462908217497497143356881720364234200358943394803700585480019851238191733274338470053866498993870209953954384551711209323753551292285447755969858927167322503418959319377343753671944884879776453877318178729382894059395463594606734353957685426355418881033317175234103983846806498
def BK_98 : ℕ := 7334513836281563179458070689090598131791179035818355193507377291364516645298893662283896283094134748576836707942629649794631146938397065983407154519741141420369193175536001955865243540328629774966209256694222059781587820973842447997811748042402379102337339632905348664637549996325749285280948387644333021766240786523288884475214137121246036454980642577563535311695344829399376743577868299710064712513069371472217248222740953506395017299824056470530494157548629416509570397409599645018765618650256456234497337355093181433198265394922531058443853564224998237474796785442868772989599961530131161833990087055010040405623432324698053296466791302007604098800465906858922156530348728446792397010210744947716194722189182160889139596423479126156141293139802676985767568325569304517498429356689231237132821433525655345649569623391046096714391244825112081168842847944331862815245800089624689039249968262496105340150744716798063839228781704931136535779335344784039133086917179902692486139714598613782378940110652064486148001279018381517990166391362966901308878428884490761185136864228016486059328221643824646327409142087851013275535377832278014614703589323492554199519791774747000396691161922754389543955793470678943032532382021628615486516656735081973613097936750846844445805424469415867121088016606267951160941354775875233880236238923274442169204759298984963553401314713646799813513526257793572948732366426744289985458700347967336200769265607089019590272758913262543917480446491668234688421649592572082510810142348544507960740672582153388814132597977661260101831884372338212222024154984390661557106997762972492325794880789628527926736146467146181967901717132365431073580317530270503547388655352271080119981842947098335899876078490012429465978082838010351568616261606446277721468642488937289988342558117509054886167464955316112153360305109204803337204965104671577823638358550821500291294997486543870481427066602294805351426266055465784961025364280309413419504091948487876535430498705283409813616201725137345772970664152672873715622081818137460425602640361460879026701065291668384826950948713395750918892909827384476788657378283192558986674723907307608294321894819583672207094187731298229748953870946274532266828091521724771125298130676034722591509190457823860218422678493543858680375295892165506711800969048447710742620610205129999496566521351473591485552944769807362196242894981888105925197276871006876522971886520736682245158643906802607332326616427520032477183875
def BK_99 : ℕ := 419341898560029239562431315193339942545330523832552202084427175096508451641147125008063750704368259769063648313501343966861381243541919426613608321144072772740150791496462759928036365616740282376000645129086333962096926997135199591963094314821971318992475768288791494100527354274127433900714843593565453884413761380262788306312450282768932024150878440916090562676700021927814942265315547663518756769189285472909234678072699230894960943939007885926700601234642886337753275375514647649630062539383034104737534748604894079906368982739886140964889146612290562466080104890659970576374094256568105046816722977381
def BK_100 : ℕ := 678391633733646583042554843027089761985219296502217037681675327871538154041629557853769180131016807240443789394933188133144312559852107136044280118975224895681021576473867598186475850075160463352613555870634410321257745748802251661891863748661469126221574428926349812028872801661843056439173330579333492039696020998366593875643913909249300267210011368263780891290367598078921774221966937877295026162381146489577353173304047770988131510673061043655835784999554301617543780951612355427116140757385843954104944568562342495789629650131196885487528341639680303571551844062267522811649221855199042467423334992165
def BK_101 : ℕ := 5371806377288569898981617294262811975689073612586451777211198726491911831374346063542539963826895752784285413269137364737458591143046813276358369520408844455448540656150869583799637864770598581956219569572090042883988577389240781546191768795491128308698160200785823454235139036929019353360804470566
def BK_102 : ℕ := 524486451428442529321081190657327726362417834157673040258419107461530204818375731515180146262236737420195337692871680705526681913814559384148167
def BK_103 : ℕ := 662147449734619726231232930822414961996873878352402924659903705237282775051767213554799156467205457118707964471490573669215816284505055204808839
def BK_104 : ℕ := 6719642430909574705937279839431125548916951572548628945107720214632
def BK_105 : ℕ := 928176632999190867619986707459512063276602909411460925267388309675833081803913886764559272387951156591316014577451661333596737699428117784543879
def BK_106 : ℕ := 8868958623457699679194562513469295370090365581903964310850433733000
def BK_107 : ℕ := 9756009916900374430381494796981532790124522726011471096746155001576
def BK_108 : ℕ := 10471783107583259430128279200857597434315660280298340650954394717032
def BK_109 : ℕ := 10991117362204785399738269060222393165660835142399840623976420856104
def BK_110 : ℕ := 11297286665259631891757571760036802914064497219089008200336827593064
def BK_111 : ℕ := 33149493296018132529570979689
def BK_112 : ℕ := 11199666786014953074842492477490203283449936811406552227320016986568
def BK_113 : ℕ := 1684845066
def BK_114 : ℕ := 29811446045769603021154775881
def BK_115 : ℕ := 1476792266
def BK_116 : ℕ := 8578431054585719970599129601851401331469597561918395481348677894856
def BK_117 : ℕ := 7594598703542719559673443560266537764905241825185927384921334968936
def BK_118 : ℕ := 6549262405777218188719975242057782205354558618307303889913164881928
def BK_119 : ℕ := 5480906720520101267850561837145420439827564054290085140320827955368
def BK_120 : ℕ := 6906588552873852270467522244120047747100798129618278083574324866102386468116655509241892038729632117466313189043661638909073975275885876636017465064437184217414883586573481202196544957038714391501061641085249316044240208936226475605265132537552727459313528943556607244370305940862918192152864229702
def BK_121 : ℕ := 5343530933443898551807835876770293940999722502328272535927218583602805333313791721036282299555412215904022251184042522953341794242986737178884403217275420241711254975130881709074457278467361546271854197142067431951391815223372157773709733861567930604592213763574315265678117136285541790596186680102
def BK_122 : ℕ := 3912971227043170551204818856364642846428384248766326813992039986771007761436740652061487760739043741226991125936900822628756303856312563747419906795036788247770730101603637150567255414660167487449269313101443466612602687559553216170981721642582811142458371429766954945787359217466481466020432102054
def BK_123 : ℕ := 478582022727971634185165036007741972051532285699010111617800722616253308442340508633502422923374630333029853855553689881944752017808056008334974474040465295031989621563588284277500706448149241403921261210775982079334214053138097861339524154064496849509996253802348010393247370491618169546951375080389269448700699944633429093355941320236468371062565235194039517322017823708135244793797159576149867584829392317466513701497612341797273933532121318694629529750536429548463913048674053397045484150947423364697942536694157056867646672708178119038244097857621043786016775289150490482439242781515075275081176865733
def BK_124 : ℕ := 1622715157408082241805034601244764765565706305080285464468542424815873473865649724018169066797158492263726606323467815094032226829008338244106754550982396967258144174857861361560659383776012391931950820873264979502081195516333814366652297090101785177545132549237014052089998930480930911226805667558
def BK_125 : ℕ := 149013573259170195950844230208003626635425458012222607497544445286401785990853860503881089620280710405148198840543349622497310460383183716476203929453526766611803963060953417606658146681294988796449255671074253230032447761287266786159504451639059749829192069978528084241639924184827117301240549123291443314323229314897940750211287335526087142985678176703214585148890162395544562009313082109180064646253193052756037166984878753786956153607402604497393627521275082098409903428353489144006600140922816348095022398497500666873763612764228185523168716719868628823131471870989838391807549738402469675676271239493
def BK_126 : ℕ := 1793858853054546872422483727101255705960184678144830344922564842692176456928336388777913553648430210456060409928913767479940289208488635466984933052130562399646024386507970197509021173875901305675914168337621677499902493888854753658767279020043375674978961343765301383286292965483796461490144547115608204050823426649816108881142195679747094879738219413964898714939177907451844435527684347635008984723803046973264633640780452747119449964033126110558909063048310084403558346180558361931104495863249679499668715073899547400303280934244893090922556805078972874786323840598354428402887813487704049340951523403326373270244809168503549790239175752862866113786631804240103586173213730937047639826431517515972826781913414093395248700953218197625992251333898417475222215886348937019292216997084493740030311479815746119015774420329825947824428041031636542730572862037800529153906090047658594796890722011823432310928164835812873398002034669596834979812548125409196464770565891796777827405669012848154000634096006640432647727767151809759060543264576884863498558268399185003243043278203058850854086851918054644810337351739416102809860448629007257982461031050672082017317642257588249702674673231641979289974986933423969436229093440767082996785946339422607378858637957692196892508880535139830918051705418796479615595759193039729914657899771058419974869191827969405763880460766056512271090423849184387493682219485686704282716742048234410044425112321650776605272805607070768938420035981107537025996331803726762384756929135036132987458269120173728962869345302015105803142467158528557715978454633604333778202494529423754777393247763445252769194421694377847078416982368828099326279180276755497359368384353938779913298879394469001785639626037650404362959262897856810452797661533243461463697373792333455122157164397160442166981644018112331905690215458165814635222978916402149468865365675608159270397098455828027855246269447106839330797951586952357816905774152578104848205490231230503725101388877198715960228895836642644256667511258181412965832532811078101607775818625021705381686019785224568395395976625910470370695859234273996171923480685603473027465565106371175558860158187469185449912467164538322852959075667421708896708888039479882474458044226023199818680159640598939141166469080853301580189970765546248671422672401270477768602431773713865696724916352799254064193271665420695690153737498175319578347926546139808690028545150080416261011775791621070113478278941202516798270179
def BK_127 : ℕ := 208224410502980203009558726978492503054603840959460839119860178113692399014692594587677758440670718573326554081094035647080425573602731191395557554754142694075944706338749808623220033892596677556403963358818454250383823355643589805958348237243193202701996186799353582791660215135980181793006749509964881320035905470886013493230534750715388035655793948643458399151789712357073947085091107225075952779276415026329165874747024201804413732553479400079582656200172452665138878599138872972811940184486913569870044586573795624754884324988709366365223946728436847260799523250644101015774605891080966723807370094375700601542425423983525128121668025942522051706656371173263178702141518405833040515733184957416410018221557981115961632655068045633794512462365429305109187792607157913342112038635944690292867207395363954092596768935943694827776317891604197927355052284775813361978725530189501460861980787180179109517044218218684710253778633556738356949176833312959725609676958941925028645130855299097268466939857307161211904758962845399828558002895639492326400047596812334796006876213403708797825097959147295939318098490432298139744091062260229013096207124628836026032646845765272338632973717424984195323870612353444026333849088355433932923661902659084114210929677311870254111805043235150898106888404420392487128881263636560513584396012213532490725093997374092762530126545153602265931919552843621715809869375851341373830245443188908750976736666736184630446921261992504003900703492596277247991408675664663351346779599633450930692566076936748102863804608356514423975588800490528279356191646293291765176324207789072097177641470341849605432927143578334968516802374064360435027710506333664461028450603660786074370166531704493058099306449305182913997820612473919793276318190147974787856724224005326401533738043391600157494836251685896708171225226099702304860275432017984501085521538692165040392229490657416966424299936210305971374962580932683908898722320956204742532658587764676309415112837600561056681208327837958732554962927655618916559816494022589796900550941383661391313375838853508816986745463189336353294784435176011079583512196074690624441879574542773410739837216877000027176856534299149837063796577818239855780664207355615133833565160703390998397151560727462544387815177309529250361735992975308378734827418950440073585816844393248836886505001225802355375200045581867556028278549620511769884523314090745999443491807815656242878478328300353060339298702387329688808139067147897400189871733164966434519019008861763715143948514363856496932595456776264327262532689416541466628495067960265105822714144732225621966177544625251102506254796099988232811321818435396161862893275837989111422999031917247191172141780610921563983124029463753988364061667795453238342963975257336774727295602298956194735989875649240308306393911644048055042597788602297438295711630437040846638671493126996792798639912979506649328738121078390794457142677086488303086717734198284345146651099000145668686526221641028363754340479155459012942935421029507355096099991544613396703725895877124968974726667623686675240105744345420780304333216837683147878841718026181704266557215503459939155042319248782296798913276343169882246218037483956526375400439225677877821616267285082381329731100818508276972840795941550283567696427564699250798646147233776149132652411734575913672836925508033091791316510832291934713055956678651773475215544097886999677767214589629242484615034712029035825415602143972308199099048222061951370732701683532756522286808068355406714802225266383115214821841229333707815932614286668629635868142281731065822884115454524661647687853892698180952112227343163201326707781006896337921930522527351519910679146516541339988697143476235357426363745107660969295936594365181047863708231411169877439887064320673121137331540282539986966767173691403333650690744814327614076420528132210150868055198988507011080413592686384838276392538284246935245347892276765413528405189720472791170268765928450141239712325350973521572385788973274276936103189459726460657882235609875341653604866666209735477104164278721526805431454483086062422619479095506475954579177250179858655816303571091252733422566833664240948602538960718171363294889586749444090954066312621847296036784776260596116619472444343820460844465502919543726494134553276626782514189180491754510028057563601867452200466600943155942393913158923193115730975907642373767643040815599153614185006280797486835686590427746072076887377948725580107416241029901050197132728056131129795626976593608260611365559675267776368245714090126091805678060989973746414648714809718194412352438015377774181742382505724730243484413347991635513524766689747437139153607676292073770832309373319076256204164859929093449985584337407097512425174397075395426984616446897547252491920442378171511614034440726432644388073879465445445801317113307512396722114925231521454514740141884522058823904473288316916871532006217824528845302151141904301516421566810291258210
def BK_128 : ℕ := 201301670954678689335884931340760533252430870834260633084244035431021537969477048260287589525397106789985097607598014713670788146237598699831764340997570918158787306998690200651531441922867948832915329442194941070144802991017316956662620700845120131404245086669788676007264408769793433122818997032546642028320245324877081946636931616067767176611963089480025045364385784185338701807757590510319533651513941903349779299601255836517866291475523553741172724105890801353550313592087495102646380350723428210457656060602950552622681088212498557731703921325947981007002093415474528919965845068919013706002024860587208968528763593757423799627917427137607951571169205593451618886692268343845360183287861415635161711150363159591552368321423325273435350849399820158630751293622999711942890184858198257006809167889426402679328552263903929169457883105855640571802596438915762152631278174888055806461193330080090785055444073234465632938615715475321045406510573714371232588832982779327715689627017975431959195274718185857586853855856035326693220169245994433315532406209372318189862555775782397663488892730963821655213051592119205430142677073246512845507051441864177213050959330172888098395137464053350948338064242646931298932169429743501463165911038821174712305532071178954400859587116585330130230148866346240274186198165138271808154920060072382273695744664332241292586368326179538058507807970481805086179242213723469674901576091797799086263309382250013027090870082661335576656774755662023687952454053118228673821810819425472094403630956765404612529446849742228372015097616859691986953643759030821259114372676607602382929686178137503257496205295181153406313067704853594882713739964016023769237931163137029277378031655530488101679658579135838946537990064663762631504367262497975002380023476178931131228668318779681787031998084902490134242575941627780464573736199368952246024237594808427840144401176362150912680783178847989515926606407323552188284894856616427040389966707303026780633765853601851731735179826513946538599363637633662822046247114019501224418983289704428402646968779105071818860675888020475040700143291530467043267496723647594541845775914743128267793605538248956697105671629755906299055073259284658102352007626967826259762882978149591491059507672140878125716297955391772847298087407492221699957619105589126998004970741495650850188517661742428620371453661505393110353053791675591711591449761400928810295605031338482356558590904996039201364878660144666490437635
def BK_129 : ℕ := 1750350838777790469648233833123546212278997550357431703542838507343405769621687309564786269611429565143511711049426639613408187950036184608071049144566432357694423017765667036580612575965407320120676228915881071726388340552074309909241380084478986340079550878481615093453723701439892213603046190990825289039879967832546429300749292170627062877467682890243422543909886955844981246118785832245046916080724633272706965729634968873852168166374142212691169599438586552536244873398132489640389312225706446023415879787282633525890970547883999959322239169498488415484929355070826508639048670539679806732959453379450909312585263062593892035400249515595945027525384973237577610286725124319280910544200225666398090834161774696532516777919551221738223634238767469817984557226933792016162218547615571743669513779743906210617849168859818276673636485653097283837648202933690971065058851009081341035923140976234962044530379461164989259192135178016657564726995900284330481487102764011224041699087228421698082449673781278749822036052945312322013734143448496873730814314079214982143218050799478254236696036520589636907223016711093810466560267965994840198473545596199870631033996418277067730790859354016599013289100189841267899126802132034413719749677064696593930035235916830111346994967148498848921095578838760010640058007166247516728515414802815558666291096923453420655494368286830659413640713622976475781293983346141250548298742352031859990036700372060995598164049855099912040926730601405152442513668078743102584437310008666181307172040025010043330131878769331982439689067303396012498468016731930462632665888727835364693925155646061305047740117788941995889867510785317004220009527126009792328562917020621748052973320203130102527018328152535237585321808895096816145306243374817746205859690991085604251934811635941669140772433989022861395740398538431793661291613920572733336431856143245862671021923251453712439628900702405273986559605807883824357304929880586384576645967092581424310616754906816294134405073402554966189844473081398585976980492585716542135087877908201138212337767063951087331880591233973315346949925203135802915393780334042710382846327150312593600879781938690089286171179984946067806595934621131076403730300132318937056943875828554902020111974814239971241713048534594587684679373816440315266228159362460828005623910514118187982554063166566562518685974341316494352327940161763523866422949941504017257215934339262044253126196868136837395057850819798531233386339
def BK_130 : ℕ := 4713701860862800529407361103395742129383509509402905909000344891036049391785607695836537735780551903791333443609213964310495678629318797698711368888794400216014295441766119897161173070471166706642726516767960486706252426298923297198178784896575983925910851590546162195108852544711894639826463459660994841557169593087578676850918190203894005788582991173907337345252928736871440510374457947131248506734290787653315212110476239299220224067518438356268385662247235286196713741598371622627864104853682209083681229306126631351052168820455836334892473407963042170487566959968817318180328779660006197532901754996825135811388968351875438822376795210721254489676288980537013717419529882027446702422786931794865907158088018101522786447326518237741693245705221251390639099136461330197323642238277206941525131933134869940067302963528886957336070067401053309731269272857592708052898474060900018186031747966669732761403151372488418267280667900633127862417722698312036361424063111629401124804740424437538791378160918321824581469600705092857035227066737614038824376603957014932589344106523031720098160864729181689672290077501928428391836521740662838695326712359955961595924865966309115492966135311852992568438313449671048314221080838585130912589448954946810385340233495841747374721942554900833814145622752908800644893145406140242358376328237676811611855093252695395481345686161235778323454342608837788459369369625226809816373900690052176794026638162916943472063389278811443268857143528222697108846892073769590954201624824160243844911649621584875612557394378468570184870261306315038689388427343529801716460035556284431632503343120648213042066804131525289847774946092024569758476740473520204322324752430389643040953257735020876034181302218856808790033717489572387913054513313400346457557294418935611965566649024815836685545003339053835589813352592112364982071322802586413125342545246405308986978574646213514853245231897235365085703416522373183995810680049880909559201819229092063884785194431162925451341889680188616427735884845752926405989238087099443940323263132765313037203298965781039723479474158765654386998197125011943466511655073020747898243693698626625940654340597815590673336903305470186372857725953980278932851597338490403764082272642178226401626453204465412499859405010985741218355901021675566419838946427014038391526815251886001894041988064224668431112865596266864635543679028396288213867232337784790416971341654518685862829005910868584135574380872996067129970051
def BK_131 : ℕ := 8495767984405538125996514213852759219710629394961712308110726294863951305508201448332089812408700810711017733648826411496595099730885451634673154522740240081397112625661769362301514070176974876400164522752312641547777941082257498369850990998205001128673487955626753805174423667706551933404578839922710477985497507389620977115057609701681666575540701536341457037954705607560455253580935323892934709359920008351368805394375490588078708691212109464099171259258388732733402251199673743605049149208913993232913616563901069927706773306694477752370039853114554586027272040665666425061081668456881144334672586418461114710908486643175462470661810862124180052587662631925399734984197030777344179302869626836438157079553126266192811786746628675412462373120832872505754247029065932404414193213692467775736606656340337823671689763290463048493969788398582425277553166538536164683707021144709240303602562695998125922464373619182323418215359830438047936699249999210209409697696660305983360683755103565353893616650740149938363220697438695378537944046534086573659911576848701172714540204387665719300404979483816325333670320767311028696016164697445953972511216131782490563064574558868174364884430041691176495310491368393819592042708235413540
def BK_132 : ℕ := 414309016080433583356888008290125191542953847109181501600267697274171749970992474400930601797440078802554449687458430499646938437174355119210276184018950741256621641460097426838870710386691862262171508033431183001559916045046218059180732124808395157918627364381461197530676681745136966683296431800913621555327582382726869464343575121256139939586287953500721221827539398313153707047023793205507779866149001386779077147796247418276544696830473902564821881413185377937248830192373609293567576925905103842746864170689374790477005634802964799972941897705108607847598584073507345037802658697030692174573225623045
def BK_133 : ℕ := 3251472721312786865157377417139542171862843455317180407038781030434823200506587024731119287381976886304603040920053612719346361395136282758760572237215229173047199166330192597811568713165476227144236105576829097174128939271192603363144979864476893844793180552778336372107846293660610717792321307174
def BK_134 : ℕ := 4312786066007996874615597445972411330657938271055647040834446435870365457018476329384978930953342086072019609768761314141439909780556872649409142932177798098516874566938283555559915924086047763088249134053987780522139011239590694320862989934936304514299473042394717543606626702322556765949647112710
def BK_135 : ℕ := 397720521385688177836485628705121783316785968483363869759304473959090422021746566464945810033156290914935061225012339421867154259822596813921031
def BK_136 : ℕ := 478966763335977054010576722128945230207571769460709342329592033361613707466834120089424567469929128347172995197658758302328218412091292949721607
def BK_137 : ℕ := 556423744983203712814565095663258774151280173086921642905292521304232268030210624231627613502216166127026552703636956847495432337825107235315335
def BK_138 : ℕ := 5323618218544087941532172226361877924537751937928920172307305501320
def BK_139 : ℕ := 5860109549794149262923428650146475240496546983160504949825377619048
def BK_140 : ℕ := 6296675246545080639735895883612888114198257207117134303400311580616
def BK_141 : ℕ := 19109897148801913273552945097
def BK_142 : ℕ := 19772516002043079576287460873
def BK_143 : ℕ := 20051910683041433283635130921
def BK_144 : ℕ := 19799042124991720824661172809
def BK_145 : ℕ := 19127728804843163160440346153
def BK_146 : ℕ := 18116940496145021225138781033
def BK_147 : ℕ := 16809275305764577877530005129
def BK_148 : ℕ := 5219588866079212695718344351845762598386632314530301425184832233000
def BK_149 : ℕ := 4625750335104106193352298026440534049559659565747365023618729546632
def BK_150 : ℕ := 3991861082904984007658172616830184468486354911306157197833529699656
def BK_151 : ℕ := 5207650071081313959525117408559218294727350572372258902897553950987175611030879585234955971986807271902169326490863653444171787655723291443957704327847156221012872871738276709471984095430308638188402408508771476128071390374781499271042865954709144526988722044260707452686364191531828370880157313414
def BK_152 : ℕ := 313227624596126972488005946541292175577534581830759580022476338299380094455264478758424869994905983603739447288639063669542148654184221700502407
def BK_153 : ℕ := 242018316036025803959823604352400746928098671558352618487833812693481710091696829777565133909430733693919131502173345749355725415025667714107207
def BK_154 : ℕ := 2372384274697338801438750251814835658185879207389051684369037825036787418693475874000788006303485910106714729665629295335739119076912544546007373433203336712083408825598095792486375569103719747506169322501046473339747389502078930002673146788101276199161200262479204703334188380992849989946260493190
def BK_155 : ℕ := 1604272657390371555027308251652275706221157008812794036696513220953012736912144820283769676161531277444895728823386489455172552244216411771941192496875227449267615048971247604918157602180553038909902056698284126729545750664688469526053165531647729562420545419067366412125565789027757607395938788998
def BK_156 : ℕ := 968794607884100007649984347472519953891737343738494461315588058126341703583309747436247634329048232386284699471217880208988983169226680329380307708651416793775421392705688402083607446079533788784987709320804044207514243693937852429619390731042827351761229812070906008884752935964254136296660592006
def BK_157 : ℕ := 484531399464704440912727994200705930207570806960247285052309550471333045786834482471566422853812454322626603578419979126840356770564711773309995705855751443944860031394781755006334176222127319981812737352616537578046758053682245968819867662283487214662258403470581761442211071109787523221200218246
def BK_158 : ℕ := 29478367730480853933681197547623007749833178811566669148691846187797496060192111962758771455471629992605473488810157061659032405641992657660454582915462606294490421988366367956821835620822581888701616667005880941428545676298430283474735227823443645046257794464705005327511420608870978056061639673464308158866831522700769771618414448356204517924912257975431694129739823116684049379957225683535022181909645831754276253053045617831824384618909302525228942763620027114088123842298744201449055154408042560128030551774827579956016978036788276967266846686495134426956951153519019925946686783104451548956099395653
def BK_159 : ℕ := 78013195976977969894918324693980507576950198906922837427827432324032007296546192391176799419888048441041799770653360252399943890056711358403079705116226458708048954004022036606363730483167059277200265480734183937505353783898313790364520426616653508278236491153864372642419467956138032858829004913422542773200480729305098888897695040440308198253742114050550293178414368859872050540374496980949967604233172973593095898383523250744681311587621727476324877086140008378154258521486011972286750173630907940436910746138749285067866237804569794448428594204283481003521978276768572149528327146681908402271357045237721962848916698225724883994028524409326474872592104083872254279364716680248677874117133366673485788414222663339256467775888062293780580103810574628258697162527310669904211988640808743091152522864996884591629322734181201327268131519023557493717180906447796466147977073801735154894561388832702841668536113341936246199680890102362940142078894212397969313953104899219440426456459800801765601560119286051584678085019102103772792569339509075383573153014492397203824237950337251147865720162795749284469361707424294319266076729685669472443142437201348077828414742380124474170470996364899171522812949290558330154830437282893970118023532317177571001935154360022963865634407439568214842377866745725739336278365076030255598824313180085711552906208606608336421083734343407247184221472471905240429831340121541448780392066209291126593972705402064144468551854985938382177317842071331411552219263843532879631549257837493797811679274806127711189537981075097739414258702093712322178078629341040704795378429516203193522595177733495343856412508636804572478163944937418430235129041843870273336310498762526772798742230721317824024238609175843083585753605556929144412506941436557074049496248264889359213925125178544319234480136278337536445489331896430868673772171926379003837007051503135759236027000462170701702576259977189985721698222193035464635172088515659574808136154383093603585777863732085317794219847566748003433623071266624226874515056508840244174667415901955292821049068869441226089299545401134641151361833561288905227866064054253810899096404458506433143627896645888284634253663003309585889793858878141812804903145804481307091959995123652871597623507668676506475877721935284446616606306201830896088219804462327970657381919439239436758449778609180771533778711692512061031587764863757822232448001206178774917167916473283408482074239635784002616127847730181311832515
def BK_160 : ℕ := 182499412201299831364399958977906521076975099979362874824095997182517244169342832093730798501716078792793744091330264457415882077051909243130561565737177515967192599925039754417694111282859548775556697682041381781324947574053472916265651736326231817452201297699839340638900206713974362275863574859276068500831161796857356427112677473844653138387920521111984968234985814625453827618599888662657897974053118313763689472504902336055658482751888264207253276740587027185517516419203825567874074444320561974507757379260932077712715203521254457011094147764518036749995473268912977480278572586897000586143375862887557581621875808088917740106283144898957335356092928631965344376537477367926801693873157285917828099495084328746315316875879712534868792478785172272992035435502595789391803718875078513026698294963564022669970960356193821637725311025867811156234367706692994880527020132468094045973011986575054817662544265533029840553856947530374971343885635673128191990570477847904467406222559365510074791903776475369504538501956171793768213627382486658191965487858591325333634252816506091979874113574659404774195143999835913971126931661323296277270507413019788656898460563760375628279443308265018068061829122239611099835571256247595622276949027829617380270249511016863244751541541176234149824943161248331342328675814755784605364160620077562954500635804593536144006881923798456019344423069040492764135077079811850675444245153894890770758930051437940420825405922883269327912116260554419031066488388932428523165939609275028163013967813425158485550349323820137665856540409074597898254754812292401028580432254393665960436123431453054615597012938496327718301935894660302340802942104380964861242370383038193705023511143646743658324646729518110875039616937952868827060570648943929152688639784052460250084889831477056039324538081496801777067410182598618529401090841331010601151437342365352336584192187354993717315839308959878260986816460423709101467575820757093486621172649058083676029790935611916205288767324393184320659507068332307364538399116129066095139869888254984470356554040517594120438812084050375268931898421987697850623205763106488065072300792775207355508491935272539948638155945684370656594079162652239959880730251137509414183579127958225115505534540055203514327468487028973410701367883102968277873002496144354373404390164673637540446080295319739703101921581159101409677323301342253351333569631393189585569668911188245535116227593214358870557548818368700184788995
def BK_161 : ℕ := 1268578199441660923275375619258240505415243211314637543404525573557496165797229948665514810177658459445417929145549210768980198794814405939344965420994451875926918124332209757008336212873941197140520762251868420020331975400649100141049417833831777455255497945401873838614612451707819759079572309813398985979511428529041590860643358597340023286536466678805478449392846132984859353953923508584166601193185913436871779488003015179513754645104101788133087282830349836037477947708106042097061320703601003977727636768214558627503903826939182435847919767502414489508399100598142477081155252630413016162138816697551394438773377623436788052934439440103277009107248523006954145257478458427522470763298166087977868330685340194595912563479849690700898606650783648029307953009957579098714325943900018018883947012407996342278933428974766033707943971013357727584826759883510272074090492910345272263121301488709226953766438389222973184135972395812963772349469825046920227160370646679859184968934414214031732693952622245652554966973470604749597990584630293736457316616816977323878710654075713448621092222723648331448226028951699658565484948449268767919206614689559953896745435537018791154048575383030046896710833775777009598146554784859603141591466164145700447879751473956195805082027981469131319630881445825057358842680588915759067759097724286703719756695775090781452012890519659977950752042320730642104157837712438495875476810133729604616747295676000434946662715513073404519261614750257056494068816811615400707903138824536068776786092070391757677203580863374350175140943809968387593841019312940972049166405290073565948438667080932840203403947687347076022790033206989469324663518487337135564784905033418947388457402990548207767393462020624970107383142373988864268237185098982402772416430374403428441227050634608241384319530963461517339681239290219587603696889166275135316159254219266795147722511203869041554116789375476473256908147458010970903746424931363166898443272514301775902109525402924390159423975515581159338000322190191322643355902546863760233580614280982587500600031747174657466689954963949118552216757487623495228695537906589956472743072819228233072901005790058661197793750355348571187042017241720585112674054922774957770599009622210393830549653497513271278833114360126230208335736648693191556535056018612684016842701883562459895384218546310767703741066852526775034874538654190901334230864358836983260991611660245504297338025743819986570117181298334738179707395
def BK_162 : ℕ := 3104216611176802297093033081480889245349580884558104634488387590310025624099334718340058063135260990752808051889384938487900467214419725805627405416073959266402370511525621113152462823555515122285441518309024568219064706154921080366045653199474192737358799052743947781242466773922995700024927001632076645602835117509603847377324319219250715033459578250102318131977201320231199523402884423634376433236064616722283183308570880322615360518765473257306385205751829470453938827025144785201486744500368242154527592127876756131314844066797049797147923892708846610442878732032324233200732186235227337743731979098876525992705216175867235529043937563561154822713492319490377846059576260329653126991630675815488579075910124072425096276341277872999036469165047868885980246661912665482877403968197150269215384830314877342906434323077901125647231677780786228073506056822453878485379440049920126676026146144264914909196351666088401052093643820508812241099193115910413560062480567363179253935958034527643183141806512135681603093939752630947224906800516394751744547508871559825015048043778441846640837852366279144422909047415547971022393792739884697369289314109946276366351063174522086749959399700359940940705220390638389480673725639193028
def BK_163 : ℕ := 177000099877484154876251149994096063580359954715578361938930489345195982651732640256961061592347471090096173904252615661008172548622947916031053211220861397095171945024905961056691923603417141716235589871221540293729620707926730457481471015363552633283910166912583926938430588891808061938551350984998464384593083881432541288649543622465937183524811276652458318479293205147164330503329138278121270172132649863410421687155083539222981325494709528299553860808313973158941625956101623900851261620064783294179717257403845413658309354877197610135882460217274229537730907574599682490961037657382478596719332164997
def BK_164 : ℕ := 278715229425936237010340454566622578435127715134442016265749683011816452937115869248434765031596200458015886143864978051656021609217534688003237550520605775317804084501529668522622872039105394522268650175073596494098024969544828017841018185091378034082390259777654509947537305313408340990753319362122407263065290999853251606891769547578808698459145705185519278287530805323934284131198523633799080195351534508492280198172566563349263646591051071887126720050662403174779520669570924698836890482183207423837170495625641620023635406885997224130722881812722323812172455129550208835569375332551475996797670715237
def BK_165 : ℕ := 2176375604480799290723529952290736979958757100146785883849372453972595602726724979675669657628157478930037254524494543017590640382563316422639990674872062063170531489952200954620974664656002277042195174858927140862485065159967957929596043451733953228310020471083568319863863176317665440891649110694
def BK_166 : ℕ := 2877951519150898444323867559225265993754864812569821342053796769603865408562656923449173993560710460839685686270484025575886735588628231599828772931518961915676638199694025087519261142364968395246783895316755538160369776808220802984533992316327626311903927038559429376074568191080264760760850334950
def BK_167 : ℕ := 265076245362448266516478600178236444469192501627795383913188410994338035314299991670081587418814257968680995155601907124334127200527304466483687
def BK_168 : ℕ := 318967464184826168610741828990104649206855041520700594625957107889588548973342109409621036083667378169154810381640020555639762830130767773529159
def BK_169 : ℕ := 3136368244799571415906107806359725499008195526544638636104783679176
def BK_170 : ℕ := 3547561193291023475106592431730087318878211742005554399299309912968
def BK_171 : ℕ := 3906902670162666866196867109586529503051293730236732676734803458984
def BK_172 : ℕ := 4200830720919416555356449343053215436341081119175460388033894536392
def BK_173 : ℕ := 4418599148254871506110433357714372689374176559011144791520733443432
def BK_174 : ℕ := 4552617580315017555811555777010045410971391104651097539745316214824
def BK_175 : ℕ := 13428267506600458174115593833
def BK_176 : ℕ := 13272124820036379684322308553
def BK_177 : ℕ := 12834741597502926290914158153
def BK_178 : ℕ := 4159081867948489005024904582251085937687616473642975486414593862408
def BK_179 : ℕ := 11299497302134077619538409897
def BK_180 : ℕ := 3508098008835542949040930816368590831301508418910192506015895762632
def BK_181 : ℕ := 9102278756575390531184048777
def BK_182 : ℕ := 7858303532643494393377209481
def BK_183 : ℕ := 260885165356631231657387181122839968280587387312667675669209269236074387070484278625685196774719412366604503485040107175842786229674200302672743
def BK_184 : ℕ := 210582576090615734962536281006176322241842104669028515705903625763099120414255344044233767333730120505852271334396037467776383504669156640609831
def BK_185 : ℕ := 162542188041153711800092283348416599840425392681879069160371420566857050894989801867062983094636159971117778600306997716893438174273571183152807
def BK_186 : ℕ := 118446592152417087581072715471063706324289259375554580973989649083990967987121595369336027473719736016256125957635091120975594407221045201639335
def BK_187 : ℕ := 79794006550376818013131052000949969550707610755543897093617775251237180085214759048957806778898408857279388669091977182514229885033028510229767
def BK_188 : ℕ := 47845502236696702508116220659331025179996981598207420872895105892549358748416075112962257972776186163524273844605315004673566607279051466633255
def BK_189 : ℕ := 316479150560403509728670555787934877587401242077638317964108743391985353121603423305013195245283220851633119544867447015681031079970285687723118886879678914214586752410746771986818414200614424469128941815900917663158552043605178899758981652887690037968243000635953813439179401606859599527933872006
def BK_190 : ℕ := 18520334794107998203466676298770238000576812714572418013376180626573941527389330060240030326871357337189836064944697094962771387810014783097557035761639233884096963069839608710915888427917428938632458991837455158354913136391311714119546658920882975329299180398252954263857007767614435385008363125836293859981937375569991760374599363880120943822804265228315333618844821833086614052162762483242728421191674451571149376557244289861772731400731318041701533883309709099317955539607684095154233431131339842218090277957395377094457814035269720543797184189346262379403679895824510524818035527695117401376019271429
def BK_191 : ℕ := 35979064868531743737869551645799431786500834260399424371598945537729396057905634033561807667826022090254245888063180296548742740008025310271393567647837992650385927763467695128622726479822885160150787141535110239379754099237472053083011999324941245112804286829072444477701820887695541463578680511850728804670708813185733371032266858428152154860004991343611396566740575762866292167318693860230305181212621216372599834854452474374517180393916881176513451603434267590634952030065879381751156004772500589651513847161468530680923828536632523448373562140750315577822153270695164092121905804795977499992910710405548281338277349976248145482267742604635581564360216813439314887369558958146637384948947239208028346267081717878246208711282228949173049357074556296672572193454997138597142497774910175001367929045806722653073927885743488308072057529793075465878990505472730684868137739688267100105387734349970934777957826436456529657029525325648451875944632684679407787970634104897099644797111919166921469125432501926858584725651673732111352021961879015186958729587954522985139944819236399560650876476185957604573871718584393139875084303950238605923284225666234316011027271622873882175164838304801303060827439408634970978353758712420
def BK_192 : ℕ := 155318729198914758640125557431677697424594670715936988158313425688792438108745988287457578043334131290549455267517143796660804246424625955049042440426422561259907047202980565136642655648285427062901346664682339222812835669951074675696230808168849221140954807552557451454782343207844752481462561799893349287911550613083066390950388801403025099557320568180118207069306570727848026252731260034521086585110671195616312216632399343254570247055894130268384963192234048089625563281703815821139670935776250146152332257169966397664138154152022067153339141547934302186462953831541578377560870092129778884287257788024366813074802668991808189048371280988988423713971327695997981782413008082127199059645491820796655414009312548734364073306236285396703392883287641710464971205112735367016078971853787818405405193243254724994372552091681928878324807264177373057687576662384801187883489888072661070186708535558892328187474276495514304238124666855953867013174623012982712461213409668730379189775601751760634958240641129362722446535838610871250955458308357448908175993902013212288043117838070658411935182264514542801064175036199011634245547418787487095026860494983499749724235693406660896934815663464343557281177530699291960249533465792308433878230038087066221034084385167055767918328881501341925733489529130539464569423922271417857518049869421812800154824722496898573058413113601477197488393408686906763477811302507126702471983527556998910434108159124467467707980868912379446665700039705362782762951823307390536410357787309906738782440171197611451774122564216134641520063603762360628549986661898194875372951934315763612375288430356227857226461690284966762749925111211121812677647763602463137552791082796502445241203290584144395602337008475886557895321636301084171848863237381645717209645832823651799197844312711326806562488676589312875587356159753267782715300946294956982767008606314012005554678040033445474872352350971518044600112635924292651944946712038256452123403079270175258779794076182743261326430466228945832161576952442564988818104482535586764189452518051550324289175316547845345343193207387564258514379186497914699155298627047432461491859579264281845024766743701690605962905766909814974491134181768183093489318737842398778517516628587290377987209092318872719097414328787626820900156834512337775212823316541025002411272796715217615301172687521932026719691862415962355878798353859861331262633062462597216104647183382254865624054230371611313322803336812132523048963
def BK_193 : ℕ := 954065625220490517747643394773209070039021992067395949155909823649462756521293141529227818149656309135564416813440120801407149468619592635268122678397502052539126543015937162470405305082390870253715709564587745619533185623838687221964515002962421869538838303936208526380235402743812140674582748880494252977072161401167829887006451861544780964033209183639849030194122070843857322035400153117099561094827707234649181408535181118347275954403318554746405691337963889321729599520171048884873478311282669368383953633706069581937249618179487427037056568508110389546002811520050693980045110261018475466514793546870615102263168588488248985626965585634546499860580835260851601746123308790310531435154820189892642345323693094767099802572441445706349342561427821549208982523065441200282663629930974889977558084145140115923344000606469515115054845808203386372068697895305249987242983481953799009449373921174873060580975819240547793401071986876251167209704360313464256864931148533168789845623424055297842573952465732284684277960693025473699423304607012940404978363508927524100903079346612903688566376767594377708087112896851215148313203180256938782385582775747525529479091289094544545676444455403890808784542425398540903974860388666762776950319941772209078835141008624546374707574151394511839731746981578943796343125354262148696459672684809473932639039240906041199659678201861710704002126036105840615819475941317762843389109810187746974300668651550819279811610004336029897101493620709718153117315890163856344787723651079215592245233982875420091671310415565859089543223002066658886198645188377048715694242621946744220988945146964493355227360438929010740294313147532570242776425862215632000936676834099775085566229523003045803413942197754424643274836277471469744095180679477535705811417379682072970316333755312267362441150020258026111543891482804672876526156706031323040618742537842214256784000003387835618844238892303493520295725335650985858914319894334924395702911394056793111900642047043635507476798110200413405155083531886442038311790725503376597894361396648617859323374277215922763358377173615908982486666981961360480952157341713639100233524289000386316179304597753192836536559348406530114177878299641008411505685362278863046397202710715027514160651800791061526686478332689627732400125102415910006608843216027582782134913823692703769098590098480189084255805539709778341832416234271855918014478150093245119457289810534569749582089033836116935743410600711759554217347
def BK_194 : ℕ := 2384009853750617572319863410111543202504373424607712749642285640519294869590181695621281809109211088864108084457400003722120091848546131198542821948525710136174067443485417804701595504879147449120311816330840640833949345536368308564345144900585263221851714714898139663837606113071331664199004530855557480865422758923486610398550408427429767675934462873550874156048635452255744444579836607996450232822570567248420594370286014131438592550562799872750574085335381791325226548213451227968874129252064728518585441959752292858632093919897941775030729659485663602790516486463993791475340073640830210465607512720284208728359713515162197405724999142467966409573247394175639688464731647368963788412935613475950076153339486096979860637512956700215703496306823183757145304975693431549227194406055272958419223486224285639210834419135966963942639987233810264833253638184654537821053827720438239424267812323304770872985555410174792696143571029380596323488374920371117952213549348867647835977140584268295158154200943381261329283960755022721476322068529191221342656826560509246782255684818533949664992288761872407676174461727427034344285984324332461519072322030965864224645932282567366940651632220016184810101034732998749029029866004086748803061941650248731590827404822451805211255718435835710645882926402258667446748177182513601120828207434268576379017124430616739238576407058944198379752542331488641684436382001558651251528459046962188943359955028295010751797962656847725299485503019067900809673427421827539180893578622329587780308712917433673279334422347458915914154931439544328605279132485585841913870095960648776830726263165666783353404128753566288329446640227497993302958290841500490740825805047458831775304724336656084991337669850417286140107030390407256043026330545384893440361817480971565714881534626724441484160442354918003931460074293296680830782492469397613667095637470021746438940669420334608098176903839996504034586240254969982493895651910131031985981169248108158270054176885827853913411515542655673636197914401676975722111529942438878523387141096431679376812879702483610010561152903571155152695265611064638197452990792723227848957488069848206884595781566003280780087590042900580884621556105002702398338147031850939411409033739016506432318480891979197977624340482698552955616335576308563173239818054812884963582238934877732786512860470432167151067676625327568934390576383518728467925808657744509119324965666943618747238947034096177491060886221531244723206627
def BK_195 : ℕ := 4167571088428982698454944761905151440763763248954633172351878559957211632339631200580190014791171648379719736314936206703591055326485187889401266191120128128391335948758121480524851395069103706572286824917370753405746754923156346996197098085598582286785107761479615359283108736043028694011707272999384224863220715657219192853502425913082285809105372435423832681095733741155243303708227252163701821979342186340371730596602007117498834759004495748086792981433472265420631430006636209072418894123473882463375825855107378794206966474714768482640391309356611754980114569205475713429878063949746390821449239413001122298979604723571584649982952485633279437033886908987277141046334048084951817771325333547894663261515915709139305918327222395222752015468403518470298891510644718358078231511649453515333297214052678275131286381519494302443891106681304131501909906590836065424019970709325340528975892030022906008628181181038236395502757431019299983207486775774855637636559609141721020925801771596507622665147860198552613462717567078850002090919839620807375364823863640705998075252306000541570281435981895668458467273511223778034671896803774403996614572251250626044398609333389801673041194372819353726689541750336098522715247503644292
def BK_196 : ℕ := 200140987988216412989237631410631981060962239159011699024841882670353263680293721538887753531048666660355603610635788858714826178467456467791260431377581268872601252790977627901479118716611792909633721858480945428233481091223915853476228647810010883775369543205629031020250216243285467011096595472175665483821117142964348305411310838593295973463096938548773941558670451142307380182831733996823833631339458856847478348513493769511920239557748617900043130571688576274740727004692121134289256175970462522824569268218266445503112465877382612115564993100612636702416357229330735807215964532465409475840335141861
def BK_197 : ℕ := 1557815108257138220908909856496453149744081948133810185518637670081555429299213198156065900762650736329544921732939155254841024894831255087934759195540725295689947719279269547335459207979626003580940174607657377765403797505273993535674720219459294027207231078914210075396288178401511636163572752102
def BK_198 : ℕ := 150772517646985642120045491648263065213762259417648645429763829013617010576760727394800438616193189632057373085887500491283399960206675815910183
def BK_199 : ℕ := 189223100230523905446256526632534144789812933209981762808713681466444176814864241052722046105398647873758359627443840652237013974041233755019783
def BK_200 : ℕ := 227579624068452285521729437753023314257222055485241718185960545107283024883120358949113027604848711625434612661302551431030080849415444881857991
def BK_201 : ℕ := 2238576177482679030203060612005541310344916340844809245167429119624
def BK_202 : ℕ := 2532416650113643546644970917760653889255654569113177625350693918248
def BK_203 : ℕ := 2789880062759855255027511962637505703919026643077838338453085992968
def BK_204 : ℕ := 3001215314499122620222463053221783718208928915241010238494169733128
def BK_205 : ℕ := 3158625943673276683847740555204206106882596142215170260889120809064
def BK_206 : ℕ := 9469239098477669920670884937
def BK_207 : ℕ := 9618706720083155233574337033
def BK_208 : ℕ := 9513382009536077585377478921
def BK_209 : ℕ := 9206094080669852137601047113
def BK_210 : ℕ := 8733463114690291905611704009
def BK_211 : ℕ := 8114925191453109050448314953
def BK_212 : ℕ := 2519041502198298102878633951598861039122307191881921745798493336424
def BK_213 : ℕ := 2234724347024920553229286536906979907372864658164523327004857618536
def BK_214 : ℕ := 1929714048048385735673558637636293355438584075734860860949378818056
def BK_215 : ℕ := 187399909605685143959236409459404110016759744678703239766215034310317832680792156734594939464369877532368203808422969019804604482585546182240135
def BK_216 : ℕ := 1303614026284183312095657948412743062014994971381756624920282982664
def BK_217 : ℕ := 116630867612522502199408960458864688364333065610212810802454839668952530641024987911468876124763682094002313832746246854650784339970213452740967
def BK_218 : ℕ := 84858921147191887770873225973259111567483652369568418977324330701155060533009080732613406618621759296748190598757089736066830154579502825830759
def BK_219 : ℕ := 57004670294955481202615485345776061684613686822720382528273147056106449528364410966967374740920652035955107226929159379942131190547428703778887
def BK_220 : ℕ := 33999561788575214220301607856784556940811646726744465931013979202359937996041239951999223748891019990524225012816317858257467524674254038221799
def BK_221 : ℕ := 222407400497788151094272025063184222677286246533891110051320231099790127713748995703239045935766523912340600699958738601907945716863812767780222340194518769683823928802919030093908540114748424228006423969273576654366111789579199236594623945622786613256048947546719850549087479669259797599314787430
def BK_222 : ℕ := 12633193742733727789258262578380378577066766643860339969109398140045628018459567234708041462085089009547739666995590419737804006194866295240243778188149687551788857821819352198111174869041116381977480759105923163349754246291886242477878816034609486092508031984490986749261485074117947217997824928241022554953919234712564144432290683311306345609023144971530745427060458674424662393747898680510486048156833821455224745366218059835670892399815014794338392855628649827163598515022178747383921184383533133840719613727057209980506081668362566064435889269540068193368563138770242325233355009993551542254916470885
def BK_223 : ℕ := 19405396233865982028752716018012311272393208085751531400321444314697547610083527851979430823592541766804378254770631759323393208456750764655619625534708200351436146987520027178713064508008966499683984812580598260887756817075181188242188985918012063428915970034118670791122127747011993376286063262288925826823352594962308512635732580363545423707319149605414932432398693004416081370511638736556606089882737522216303227820028959508959800716002720706416355629305446422534684518328837875349851473531811553582955917219124920800202399471598441444170644542874757308341765284366434768866322630803856251300739125192269210770696176506363371347840329542221859635235650882465482139566452490203227026198785463712488581293365513382482554620032372684911569651770291605649789495270459333764726716874845246879458630062245477469532772802634031464720595935139725134606983394097216164330569939651204088888781822124127086162617366187068177786424688947090403585562370489866410708045250891964543096483105227972306701622880892009692841736411330108559400949169276674834985649779402288492786942747315995614645717366798514544662638400356981722505299977664275581135086905668212268002897667901650788439902298021278867321144701894616934048636132997860
def BK_224 : ℕ := 122202724425557263452126459050042934421333538101774350668992591779223366618406915207971119716974935315612642261333486999609863273756605142412402167731644179257791263787334320770825681456806785642550565776087352145062011678504978237768999121997784622627837142251397161736699007677685525963816781190850670243437696070099038239752570603980067572141503809620003230567600684840997012776642289782558600946714820285599708849730727208743687553986116566722236114962316624872338537888919946907203071438590966809106140597138766937492580524973720650022192828949654078268474034113280004919494710516378829882924725554313646752777530525213700746649906372525139907278316220722963864384115456102737489766373558348722594904142575102861710338753088358763573876540985076199841864158009617441801380057144636777265910157300430464087836703792136868785665064540929201037403089350079377844570295463239702963276030426386066386828798930126910830199255634417075472009656215365130006585865250596291191271642197062653550207471256190348956325025112600184885885787883609877776289706531704083969250732035972274024196131304192455797131328918884750942932904719440887355235612199914470732925425646830459349633594401119563104533248804676025375687932528033796
def BK_225 : ℕ := 703022122524156486385254828427152321840908209768133688528983465513578851448699352340093420262630111111403583853842332508241420614143117883483801883789108156003718153156641272764189915543692267507639499819627592680302315467196263784351648800758422503963576154607895450882811281398468381081204914501108949121166915946122209138027059715834172331624213343608817078390849684006401462041817264345807212154893928641242757754138171461503508550426921568710634922506125084055636140932872596247890414550364065790182584058425157435958640532968423150570300421037526204047869757190959415761953449125251957324141879060948491530788074020977713030069242029817866688640513095303371422355941391409702949526018560310299226483300379029280140087320266821745886801605158496764944168112450178085399245002599388357613824108058800734852132925491990862296756728049971788914047263431515723561531988848947669932827513287182677321756104832281935497078935685958737153069082304104720484480365862032844200725065855064134772261445213959869655185284533870349931002840837388872323722357280922711909528343164929549099360163783302975634547725812932982948310944210020072031540417722726535313158580640456554537758993218089514573270048697359195962541839143298948
def BK_226 : ℕ := 1729142008850130232746407958839957361675850360580372290201763439410694171531631401867231883474072768461173299544245412751042528165078988516987735164140515033042700168957766979116341784191778175170001731752688034822597903999810304214636599231982242103131213250641706018657612193051122231203581772231406760651661552473126823031681782637649719917058686525132297089942837174912943870780459071292693171196711489926173140189792112599824985250384675275504960759818051647070807153549040610993142710575421960805224089550746570192883518113846839001808886545062422279859280347140934508822403605117196898902250651560988265521246925247112018836098731659202334611014651949665009234518552770971278266894550298254268801032516554884005481342657305469248051731103974554358553837044509310051062138269913909222975205396359460421186238655561355455215061995271718609238358159918773322306391228852080437727503021995989353071130716038836036705488126018049192991316521157574719066510142161922195762997894728936470708397889109808234716438329540392306722591690721762778073642665745570165149193680821826626056952818368183215445747814239006845601617725648227874749016018682634704597993317722167710812332929388206294982098187721210953549613413529872068
def BK_227 : ℕ := 3149339456720180223329461601874107923324532898149820393107972472916413865147210097927640880917123627274666686506483019654330144236690406979790992193511251306618214597506687895839501792746195077773433701332766383892607197284868378383826423443359064351437031880708541210204589501429920540603192959056540760985088044838978494451177706187829000150448384735634649383149087569493513871933492711866442240583191704665028002219209478015221779936320447710645890655141938550277059579168863539216305868657123723061019175073417791289177710337150364752316423352312232318665315116752552227234015125575850611174601429178152009532112024796096910732395527967534251609770397353598894470336004663379124016284772284048209700526800798412790696158735816989449226377113625377934192636282615865642211556260324087662666627646717830110298202795569449884736952614319452992245992659291585155324497173228053898987241868065960568868762742086450680908046841029301793727760451207926859597423321330306443596772399449136358236198017400328629148686373737677860460422141900520284580298101002004352403387318590794514226616428195242810137049709508108892703012561426264626013282745013981589232463246589705710652445843459066560229757884039014413106131265601878692
def BK_228 : ℕ := 150618377422448739141117682373556161229913189395959931543181878830311817613241195368681254791818620038391545479334252299128353171998503729972963092571820003485779899825661229499294388082982839463855490212189391687754178183440916917605006995340783312307306672029447299321241509990737821652611700361657632738707680697158243332431016623262656390423544169120565261607303974940197342440871386363815508072638363525318274706720123340445600713152628198592463239031445626923181048373911024300740214248944440851322676313870710572737873050691776524290661922525893455475023046131083314726957991733295457381395270682725
def BK_229 : ℕ := 1169749843533545404319073597439431691019679932444817783585312798888320838118737870114075246372034697995518980011208259947862965578037589298760012842666709057382211996613732198165854810442397117588020942218389118988604135268961934712786176908023493995715815007960453356642443439301988955102330685670
def BK_230 : ℕ := 113087662567281880580528451515947132429796624711724825967224110312747489853113189926198940299153819572833978023908145177825988347588124864990919
def BK_231 : ℕ := 141821074281647143073699577160709380660820200428399534795346822138131252638298620828241374776448505477349704263708273796334392003365795139728359
def BK_232 : ℕ := 170512015355698349340983855234677609580683191561174678085868692495646840177707815463951984167654312548802382965653592364234452443981826061313031
def BK_233 : ℕ := 1677703779627338816977596610655383651302429399804893326092562976424
def BK_234 : ℕ := 1898142335387844957808380517378411417667209080973702406262132131816
def BK_235 : ℕ := 2091659255485318467754050484947610573183638386926995905852156845672
def BK_236 : ℕ := 2250908221781388844140005694125704377444564327038658913561066455368
def BK_237 : ℕ := 6860176478559076022555920361
def BK_238 : ℕ := 7112066916533343717211275977
def BK_239 : ℕ := 7227859933032096998901756969
def BK_240 : ℕ := 7152303840200306341436997449
def BK_241 : ℕ := 6924699942787899624576252489
def BK_242 : ℕ := 2243816804206742064942082414426836887386655621738555653293576448680
def BK_243 : ℕ := 6109427641542964012996467113
def BK_244 : ℕ := 5554498814247018514818962153
def BK_245 : ℕ := 1682728674919343252925637671398366067664634303622453041498215316648
def BK_246 : ℕ := 1453298296464841961247641684787748247900717373085292615317869872584
def BK_247 : ℕ := 1216630871658570136862660687145827424330922063676870452532141193032
def BK_248 : ℕ := 981516150737414699120496250074832629420676532504714640651319373576
def BK_249 : ℕ := 756548239231347845195560206157917314201639189240723578097660530984
def BK_250 : ℕ := 549800996478410268285532031088776874191603251149355412961086701064
def BK_251 : ℕ := 368530149484685466313268712146327743880492716131160958409264584936
def BK_252 : ℕ := 25386092614993926689977478210624373298799220187491562151133701642738937205182417156301708317516319053622102283709105885513060865778097352667271
def BK_253 : ℕ := 12270177352410653007962514273604874295188737449794496220050405124232532316400220885448038073477205261065553194264131154809451529213638183327655
def BK_254 : ℕ := 50792264790411558163496504364015681121397055071977503808568197484994863513164160022265392733126438339247551367563938812478019203514519800382163330848864503935106293535356506464763402924144246839569834771423756898809843033537411299462500626078994299874617405968852091756742325829708068844389500742
def BK_255 : ℕ := 351783208739242941906963956231108188723337684300771089362350292085466186915418234425762616849413306690425000505884399209691936604559686182552842771510001938054647355329231045724255830931382086446061544407899506086830301316093315776201184601886507554842368516504768239252185082827881187769714400752240669734361924752026681058461411565894988617246548388929220910069906414326684643934611127713593202779553330372565022718585333910596515473802960426734733707045073567573261225244967759748560387792107020653480547225870890302960438663054520448514865571248478540295058287520701241058085802647298319311171686501
def BK_256 : ℕ := 103012923575870310463429733382322536101260580904943380326438628371864090276791873859399060782968761101364784787050817145502656556284117841901618122395904532565476226384078095413904404796132622754574062456470137695502735368617201058811989894796598988534342449482636670301215977890793106057020466029738081161753277053144848694100993050785395257448497522085304664595392105322026684001804916973830855524439501603603456951971793030821835120008062507815883085182701742749636532657480301471759752770576370408128679675616299354983607322802905553286640845736102093466318284182571730374246489029053241159256023329747224690029985726004769502243983341101056024640425790334631870772829687281594875114847477450462766916913030894565248442485186285897466402802298861638001979727911907018176991549882438655948908078973898837529737165046508936250410054535932226239619822679653392426810766259749584603280144277792686675690095691199425582377199408788013594960067692371383185764519261178674350208602119399832761775943959782419258367158718060530890876438005942446702615578725090058598878617579641343738220815993043692328242840081358600545348651736645315931060890390086750365394036844353761007089226533423240235315187764838983890035819778408452
def BK_257 : ℕ := 560828814395379550504555964143182322781494627491558870794972519961352660313428676212932258905286959619595917414867830531273315467417671852263218624929119101500271250185362280341731702973951459643050067207056486771997234078919491689056835892069770033214731564882670824050276090406932052109959550623046083075021187821315077711437730266510004921033143421613747784631754274153148168454237725557190320487257336515038502034077812344133094757146046697958459467597204187331353789651393755520024733551762314975636408252730700294049813225871465833431814032353648831272677730740487670997925384023598775682194252130112714928841716225058057800176925278161537255704112687999931217951342390335277454204585461939957884112646463494638239264492451955841857225307607383423358749231314555486650469364620976337276076976075366658143462911642931239059566233631747177895983944109194296586578901896607039104120534746535518672773787278950626274317653534854431169495325347108650130924430885061944392552143186899980925679882494796371829686207727023000685787501322962876449171031662886802849305790058692459559100986432337566261015179192954327839378236883883924213138065646975237921841622780511512606606827576019587467724302202255410770202704496882020
def BK_258 : ℕ := 1360260119552352654784698766765728451749502609743472525700010312525095887578988820889784986871913767629131031064702083107178339436879194906011956438614779101671557232851681363882653758843453424310868866409336864825052859379555635696013352501259853624567616696950603323577647913394500990887922162477645648386687861256812384528125587268954436275880033987824655971981548070132703302367430773394792843515577497777886430669134692702643211051721067774353738834926730689999858251414881522540834457887834596798287517707691922235742469517518114486492259723399015536017765853999141889957776545457882992303125413315241782078242481801060192350916890916242046527931293664962953302311759763680139553825427679549901661279093038007975284888988075278263640902108696544553044228203867169771507848828892488937113421287855950065119113686643662959966273765306563223659981261433385223691233382325090301314444594694346523226272476363702688955173211226468297543535899645248688425115068209125134854681749644663378742382317436094866514810148325834727311619910830167631201005512239554862713638854779555272045080162355041423396921489422860581470209385353545069644145987438373053495401180557522341132186151340381674613848368499203528449128693969310948
def BK_259 : ℕ := 75587531919331178709826622649018658893651666693400448915691716327098973204532124968804888939308830326635367421792789364570989675642123460974824377520851531117451055162870734607079745731785769869274526710433041858777462126805935093889901666907373161588011861140663493570069816789737872800963541559293562160468628314614442929363433313926957728968241622196243278240244061812587337569533038930614105056412241106964192727685998290758929217227024017360952133982856102215322122718046564687976239155731042516159713033419036114023213952531476258846462874152762356884544704130280542907467561707398893406687746756581
def BK_260 : ℕ := 645034382384891585618897720811913343685769039829008875489971950165899850780426738241643027835952375534782146692170773872560180090229877259136699433564472184216804636310114779425708273905658040876500368231315280757836938853533646274940653845085915123935548572043818021895558192764640361834987943174
def BK_261 : ℕ := 910453700810129260217415325115923617673453661314165626022944175898225383359728617353910304424918859213432080541438204507310318374150415583785343227030192147446798745694713547993185197846496568030525347269286687307336941637474758697491009701651714914540990011817003443025048950304921956260264971654
def BK_262 : ℕ := 87948253201299909459735654916059063987003976482297386017165849539895328453930475592400461588257492436083590742966138487108216747316909389349895
def BK_263 : ℕ := 110233919293909788485092490267291559313096471860711469263493045628443486110987341377034173621701111251461128166224635295843309211601935711350567
def BK_264 : ℕ := 1118436712876510276408588175036601326389831259787260391646061168840
def BK_265 : ℕ := 1304016564235850974124093502246935954217329335279368823930879070472
def BK_266 : ℕ := 1475496940324736574515029937386019492797314888536855381797954779496
def BK_267 : ℕ := 1626252636452356935160095806713255240414433162358153264080823232744
def BK_268 : ℕ := 1750551102011682010457689712226387711766104490186816354531332538888
def BK_269 : ℕ := 5339178382240974993164824841
def BK_270 : ℕ := 5537163597093145431223632105
def BK_271 : ℕ := 5629420929328037779176000585
def BK_272 : ℕ := 5572710620536776469831066473
def BK_273 : ℕ := 5397406341635125263159304521
def BK_274 : ℕ := 5124549777089904008070360489
def BK_275 : ℕ := 4765203070389400748945682185
def BK_276 : ℕ := 4333575231987717163490256457
def BK_277 : ℕ := 3846433614381717100700742153
def BK_278 : ℕ := 3322432745774500710786547849
def BK_279 : ℕ := 2781372328241618625421423241
def BK_280 : ℕ := 765565170332103410098782627012702208565064866469727038109447945320
def BK_281 : ℕ := 589798086142277114042578754863167005961166708443005321082681538632
def BK_282 : ℕ := 428207610249101481051890934396267776730994097289076933232314870344
def BK_283 : ℕ := 286524284587035238316549891106158430769302862936556358054935298184
def BK_284 : ℕ := 169641235502039128881408226801844520815935014176555054648740569096
def BK_285 : ℕ := 9442414202163326347759254091184533419114273632288688385268965461165321315083820164121584844447716600001395295885813463568007241757559823415911
def BK_286 : ℕ := 2858255488487829170310105214167802169675611328019895012272920473857699032757943130830031390900796241566932029150985442717298393911080825651495
def BK_287 : ℕ := 1221204789867929427589355911334162929013164156722432211260947026830852054643569769002108989880495146419153936144186888468377386653679901442205384094644722162732479912743973712215694113207553732913616437118264049618644765908683078488988602374652439129732040472053995461462051012332420820996581766
def BK_288 : ℕ := 2597141148991696035170560640056718385882479320069365309711594891232034029361597474582463280826788773974326753396994342141368670409393667771352128215470434955217846285478081680474461154153138909030557843639723209861223923116883960262726565393897448557813770215267135793451913836241861898562234595711666454056459158541448007215232999788940447256770902095327511685496393592502357115412831876069355125976522032790601077760045169824533639282847346356962627892328569236984022189420149077924928771432602501984246314089712541992367605475461759388974389370762678733900583881574642634137233011838588773028964859909
def BK_289 : ℕ := 13902920896934557729856882122841219654479356192629593182425267797104052176917435077615694735882457265982628578793972817760116680571873294053637907851643362643558281206139938233379084763811711086030971582328499958565800339273107210012567920687988128782153950859807217462394845788356894095896351215350755510811220774738019444386728483401608294063234420878389401703762819570092347300121766189599283106996684982844660750196762615870819654852876281169261272750415660529431251298155046618949083489525591318813178274462994927528557635129690697852099769231288265853329415918096994521706097254346646585039008598117
def BK_290 : ℕ := 33585794081083565985681341915877355429923891512999608594420322097273563773000501711564931202679198898380233374928119963129571371910139701197001121223500795477122461400704958979201349291203281220287728575107989504859222658274763043389620195379812721807763493581209561826077919248366124657525128645027431957855194661606285890117660113076618165157029089329639928447673479547456494435157929747946957515135779432783254982108333339531251000576242902476799295050116909286050769721363575523973842137829675094125285616196027981570927546940121846088191025405107417706742271090060546979798670452413566870127168545093
def BK_291 : ℕ := 332325810765326030589607946406366763415468529215852630326931806832333825665996952014750236242528704161313412779194518216019711258064800193413022191958693022969631273120362356167662789398337967550921771093955052202630266243802024829137926921343261853458909060372538870953748835445320937863425743206
def BK_292 : ℕ := 516954137141848199224824740714472235688732696091381445427758933016371980672509848942191243846777458139765846665780059635580376422229822777791482529046939624559083376749761633102558681035373464657665762829334187590339408451454566377580234850085785472437485598119745794477104590719001176252417109126
def BK_293 : ℕ := 53268463402745029052311672377511739727214890698819473935840152357640213920674541480260676045548056292029203000855647482849694351900335796933799
def BK_294 : ℕ := 70346359108095332723727700072183149244572899892555951518860187371099715942183907133304856517562764937927666403707780428870954046333861740791559
def BK_295 : ℕ := 740568646426517813544252108659046640722014329416737680371848603144
def BK_296 : ℕ := 894257004484344002646736210372999687385329449773532629647076231496
def BK_297 : ℕ := 1042602092676859779227872505047364448751266792473481409042067341640
def BK_298 : ℕ := 1179800855990362035244795414442581461390111067772328227828141973256
def BK_299 : ℕ := 1300555219691661512306899823708102472164945671413829463267822635464
def BK_300 : ℕ := 4034763950853541184354158377
def BK_301 : ℕ := 4273314884095511081801475657
def BK_302 : ℕ := 4433008200014234781688093673
def BK_303 : ℕ := 4508201260956808552558291881
def BK_304 : ℕ := 4464136859310039084814869961
def BK_305 : ℕ := 4324989379390511512391617577
def BK_306 : ℕ := 4107503742459269694320125385
def BK_307 : ℕ := 206024682
def BK_308 : ℕ := 3475151126366928732199490537
def BK_309 : ℕ := 3085006326044706247942855561
def BK_310 : ℕ := 2664961272031646427402495881
def BK_311 : ℕ := 2230918533462421260559802217
def BK_312 : ℕ := 613769584421602852831134585842305024259939100139579039987153501640
def BK_313 : ℕ := 1385498644553970138083888841
def BK_314 : ℕ := 342892457316174141793368880448708053067333441105726917929699739272
def BK_315 : ℕ := 229111200392345402107207860689487340319592230885010756573420384328
def BK_316 : ℕ := 135288113982645436433587694016771112520182840016901392969801195016
def BK_317 : ℕ := 64585652158962108595722272412758210357750397815475873658236108744
def BK_318 : ℕ := 19245694360869874617049775814669452149917436056289760709452941480
def BK_319 : ℕ := 515626245574179818494556532764816147649127467439522290602164456
def BK_320 : ℕ := 4100504154726203478628976547840112740830781262711637460123648008
def BK_321 : ℕ := 31829827051409784788198270789704779163975204619258088622937927368
def BK_322 : ℕ := 84308607109877290133885786444547117654018747684037589145255138056
def BK_323 : ℕ := 159062360608701183765740723361494461971172382195467846079883875208
def BK_324 : ℕ := 252799274963495246287657342194816946355280667799191605565787186824
def BK_325 : ℕ := 361543584584618142707941244893632551755822691234351350856905234536
def BK_326 : ℕ := 480797269017912807663928108505266163256904022504413669302887343080
def BK_327 : ℕ := 605717619598637611748866370903183811512250007419833675683481770408
def BK_328 : ℕ := 2051217140962731513206037001
def BK_329 : ℕ := 2411086849762499072397622569
def BK_330 : ℕ := 2747880124444158369581287625
def BK_331 : ℕ := 3048558511145332986324563657
def BK_332 : ℕ := 3301622457181554840160425161
def BK_333 : ℕ := 3497533962846587945339741545
def BK_334 : ℕ := 3629054230616041828272205961
def BK_335 : ℕ := 3691495131162653055610716617
def BK_336 : ℕ := 3656308778503001771462389129
def BK_337 : ℕ := 3543192163232991007665740841
def BK_338 : ℕ := 181593546
def BK_339 : ℕ := 3131212320889436884615173129
def BK_340 : ℕ := 2848703829540992558055056521
def BK_341 : ℕ := 2529214486255266212875083273
def BK_342 : ℕ := 117890058
def BK_343 : ℕ := 98687530
def BK_344 : ℕ := 1474825748366711658450776713
def BK_345 : ℕ := 1135370239580701835662141449
def BK_346 : ℕ := 823131499727819382186369257
def BK_347 : ℕ := 549350531927492875394640265
def BK_348 : ℕ := 17463242
def BK_349 : ℕ := 153805705513502466314811817
def BK_350 : ℕ := 2439754
def BK_351 : ℕ := 55594
def BK_352 : ℕ := 10
def BK_353 : ℕ := 1174794
def BK_354 : ℕ := 5690666
def BK_355 : ℕ := 339420091014016256650851561
def BK_356 : ℕ := 557302406733438579758748649
def BK_357 : ℕ := 814259353629773322479976457
def BK_358 : ℕ := 51435210
def BK_359 : ℕ := 67358474
def BK_360 : ℕ := 1709095856305794245011626441
def BK_361 : ℕ := 2008859284497340279837365897
def BK_362 : ℕ := 2289560290081879981720622729
def BK_363 : ℕ := 2540337430146172002300409769
def BK_364 : ℕ := 2751596626882063623877900745
def BK_365 : ℕ := 153108298
def BK_366 : ℕ := 160529770
def BK_367 : ℕ := 164941770
def BK_368 : ℕ := 164593994
def BK_369 : ℕ := 159534634
def BK_370 : ℕ := 151576170
def BK_371 : ℕ := 141037162
def BK_372 : ℕ := 128331402
def BK_373 : ℕ := 113951306
def BK_374 : ℕ := 98448138
def BK_375 : ℕ := 82410346
def BK_376 : ℕ := 66440746
def BK_377 : ℕ := 51133226
def BK_378 : ℕ := 37050378
def BK_379 : ℕ := 24702090
def BK_380 : ℕ := 14526762
def BK_381 : ℕ := 6875370
def BK_382 : ℕ := 1998730
def BK_383 : ℕ := 39242
def BK_384 : ℕ := 10
def BK_385 : ℕ := 1024074
def BK_386 : ℕ := 4866474
def BK_387 : ℕ := 11375050
def BK_388 : ℕ := 20258666
def BK_389 : ℕ := 31138442
def BK_390 : ℕ := 43563210
def BK_391 : ℕ := 57027402
def BK_392 : ℕ := 70991050
def BK_393 : ℕ := 84900618
def BK_394 : ℕ := 98210410
def BK_395 : ℕ := 110403178
def BK_396 : ℕ := 121009802
def BK_397 : ℕ := 129626570
def BK_398 : ℕ := 135929930
def BK_399 : ℕ := 139688202
def BK_400 : ℕ := 139416938
def BK_401 : ℕ := 135153706
def BK_402 : ℕ := 128431466
def BK_403 : ℕ := 119518410
def BK_404 : ℕ := 108764042
def BK_405 : ℕ := 96584810
def BK_406 : ℕ := 83447786
def BK_407 : ℕ := 69852042
def BK_408 : ℕ := 56309546
def BK_409 : ℕ := 43325226
def BK_410 : ℕ := 31377962
def BK_411 : ℕ := 20902314
def BK_412 : ℕ := 12272586
def BK_413 : ℕ := 5788906
def BK_414 : ℕ := 1666538
def BK_415 : ℕ := 28490
def BK_416 : ℕ := 10
def BK_417 : ℕ := 899690
def BK_418 : ℕ := 4208330
def BK_419 : ℕ := 9792810
def BK_420 : ℕ := 17406186
def BK_421 : ℕ := 26726282
def BK_422 : ℕ := 37368842
def BK_423 : ℕ := 48902730
def BK_424 : ℕ := 60866794
def BK_425 : ℕ := 72787914
def BK_426 : ℕ := 84199082
def BK_427 : ℕ := 94657258
def BK_428 : ℕ := 103760074
def BK_429 : ℕ := 111160714
def BK_430 : ℕ := 116580874
def BK_431 : ℕ := 119820554
def BK_432 : ℕ := 119604938
def BK_433 : ℕ := 115963786
def BK_434 : ℕ := 110210570
def BK_435 : ℕ := 102574282
def BK_436 : ℕ := 93353898
def BK_437 : ℕ := 82906282
def BK_438 : ℕ := 71632170
def BK_439 : ℕ := 59960266
def BK_440 : ℕ := 48330698
def BK_441 : ℕ := 37178090
def BK_442 : ℕ := 26914922
def BK_443 : ℕ := 17916074
def BK_444 : ℕ := 10504746
def BK_445 : ℕ := 4940554
def BK_446 : ℕ := 1410250
def BK_447 : ℕ := 21194
def BK_448 : ℕ := 10
def BK_449 : ℕ := 796138
def BK_450 : ℕ := 3674698
def BK_451 : ℕ := 8518666
def BK_452 : ℕ := 15115946
def BK_453 : ℕ := 23189258
def BK_454 : ℕ := 32407338
def BK_455 : ℕ := 42398154
def BK_456 : ℕ := 52763402
def BK_457 : ℕ := 63093994
def BK_458 : ℕ := 72985738
def BK_459 : ℕ := 82054858
def BK_460 : ℕ := 89952458
def BK_461 : ℕ := 96377450
def BK_462 : ℕ := 101087818
def BK_463 : ℕ := 103909258
def BK_464 : ℕ := 103735018
def BK_465 : ℕ := 100589162
def BK_466 : ℕ := 95609642
def BK_467 : ℕ := 88994154
def BK_468 : ℕ := 81001450
def BK_469 : ℕ := 71940714
def BK_470 : ℕ := 62159562
def BK_471 : ℕ := 52030154
def BK_472 : ℕ := 41934986
def BK_473 : ℕ := 32252074
def BK_474 : ℕ := 23340426
def BK_475 : ℕ := 15526730
def BK_476 : ℕ := 9092842
def BK_477 : ℕ := 4265610
def BK_478 : ℕ := 1208554
def BK_479 : ℕ := 16074
def BK_480 : ℕ := 10
def BK_481 : ℕ := 709098
def BK_482 : ℕ := 3236138
def BK_483 : ℕ := 7477610
def BK_484 : ℕ := 13249418
def BK_485 : ℕ := 20310346
def BK_486 : ℕ := 28371978
def BK_487 : ℕ := 37109994
def BK_488 : ℕ := 46176810
def BK_489 : ℕ := 55215210
def BK_490 : ℕ := 63872042
def BK_491 : ℕ := 71811594
def BK_492 : ℕ := 78728458
def BK_493 : ℕ := 84358762
def BK_494 : ℕ := 88490186
def BK_495 : ℕ := 90969418
def BK_496 : ℕ := 90826602
def BK_497 : ℕ := 88081514
def BK_498 : ℕ := 83729482
def BK_499 : ℕ := 77942986
def BK_500 : ℕ := 70948074
def BK_501 : ℕ := 63015306
def BK_502 : ℕ := 54449002
def BK_503 : ℕ := 45575306
def BK_504 : ℕ := 36729738
def BK_505 : ℕ := 28243946
def BK_506 : ℕ := 20433418
def BK_507 : ℕ := 13585194
def BK_508 : ℕ := 7947434
def BK_509 : ℕ := 3719914
def BK_510 : ℕ := 1046986
def BKs1_3 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_17 (Nat.beq j 17)) (Bool.rec (motive := fun _ => ℕ) 0 BK_18 (Nat.beq j 18)) (Nat.ble 18 j)
def BKs0_3 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_16 (Nat.beq j 16)) (BKs1_3 j) (Nat.ble 17 j)
def BKs3_5 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_19 (Nat.beq j 19)) (Bool.rec (motive := fun _ => ℕ) 0 BK_20 (Nat.beq j 20)) (Nat.ble 20 j)
def BKs5_7 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_21 (Nat.beq j 21)) (Bool.rec (motive := fun _ => ℕ) 0 BK_22 (Nat.beq j 22)) (Nat.ble 22 j)
def BKs3_7 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs3_5 j) (BKs5_7 j) (Nat.ble 21 j)
def BKs0_7 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs0_3 j) (BKs3_7 j) (Nat.ble 19 j)
def BKs7_9 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_23 (Nat.beq j 23)) (Bool.rec (motive := fun _ => ℕ) 0 BK_24 (Nat.beq j 24)) (Nat.ble 24 j)
def BKs9_11 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_25 (Nat.beq j 25)) (Bool.rec (motive := fun _ => ℕ) 0 BK_26 (Nat.beq j 26)) (Nat.ble 26 j)
def BKs7_11 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs7_9 j) (BKs9_11 j) (Nat.ble 25 j)
def BKs11_13 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_27 (Nat.beq j 27)) (Bool.rec (motive := fun _ => ℕ) 0 BK_28 (Nat.beq j 28)) (Nat.ble 28 j)
def BKs13_15 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_29 (Nat.beq j 29)) (Bool.rec (motive := fun _ => ℕ) 0 BK_30 (Nat.beq j 30)) (Nat.ble 30 j)
def BKs11_15 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs11_13 j) (BKs13_15 j) (Nat.ble 29 j)
def BKs7_15 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs7_11 j) (BKs11_15 j) (Nat.ble 27 j)
def BKs0_15 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs0_7 j) (BKs7_15 j) (Nat.ble 23 j)
def BKs16_18 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_32 (Nat.beq j 32)) (Bool.rec (motive := fun _ => ℕ) 0 BK_33 (Nat.beq j 33)) (Nat.ble 33 j)
def BKs15_18 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_31 (Nat.beq j 31)) (BKs16_18 j) (Nat.ble 32 j)
def BKs18_20 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_34 (Nat.beq j 34)) (Bool.rec (motive := fun _ => ℕ) 0 BK_35 (Nat.beq j 35)) (Nat.ble 35 j)
def BKs20_22 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_36 (Nat.beq j 36)) (Bool.rec (motive := fun _ => ℕ) 0 BK_37 (Nat.beq j 37)) (Nat.ble 37 j)
def BKs18_22 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs18_20 j) (BKs20_22 j) (Nat.ble 36 j)
def BKs15_22 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs15_18 j) (BKs18_22 j) (Nat.ble 34 j)
def BKs22_24 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_38 (Nat.beq j 38)) (Bool.rec (motive := fun _ => ℕ) 0 BK_39 (Nat.beq j 39)) (Nat.ble 39 j)
def BKs24_26 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_40 (Nat.beq j 40)) (Bool.rec (motive := fun _ => ℕ) 0 BK_41 (Nat.beq j 41)) (Nat.ble 41 j)
def BKs22_26 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs22_24 j) (BKs24_26 j) (Nat.ble 40 j)
def BKs26_28 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_42 (Nat.beq j 42)) (Bool.rec (motive := fun _ => ℕ) 0 BK_43 (Nat.beq j 43)) (Nat.ble 43 j)
def BKs28_30 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_44 (Nat.beq j 44)) (Bool.rec (motive := fun _ => ℕ) 0 BK_45 (Nat.beq j 45)) (Nat.ble 45 j)
def BKs26_30 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs26_28 j) (BKs28_30 j) (Nat.ble 44 j)
def BKs22_30 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs22_26 j) (BKs26_30 j) (Nat.ble 42 j)
def BKs15_30 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs15_22 j) (BKs22_30 j) (Nat.ble 38 j)
def BKs0_30 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs0_15 j) (BKs15_30 j) (Nat.ble 31 j)
def BKs31_33 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_47 (Nat.beq j 47)) (Bool.rec (motive := fun _ => ℕ) 0 BK_48 (Nat.beq j 48)) (Nat.ble 48 j)
def BKs30_33 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_46 (Nat.beq j 46)) (BKs31_33 j) (Nat.ble 47 j)
def BKs33_35 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_49 (Nat.beq j 49)) (Bool.rec (motive := fun _ => ℕ) 0 BK_50 (Nat.beq j 50)) (Nat.ble 50 j)
def BKs35_37 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_51 (Nat.beq j 51)) (Bool.rec (motive := fun _ => ℕ) 0 BK_52 (Nat.beq j 52)) (Nat.ble 52 j)
def BKs33_37 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs33_35 j) (BKs35_37 j) (Nat.ble 51 j)
def BKs30_37 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs30_33 j) (BKs33_37 j) (Nat.ble 49 j)
def BKs37_39 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_53 (Nat.beq j 53)) (Bool.rec (motive := fun _ => ℕ) 0 BK_54 (Nat.beq j 54)) (Nat.ble 54 j)
def BKs39_41 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_55 (Nat.beq j 55)) (Bool.rec (motive := fun _ => ℕ) 0 BK_56 (Nat.beq j 56)) (Nat.ble 56 j)
def BKs37_41 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs37_39 j) (BKs39_41 j) (Nat.ble 55 j)
def BKs41_43 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_57 (Nat.beq j 57)) (Bool.rec (motive := fun _ => ℕ) 0 BK_58 (Nat.beq j 58)) (Nat.ble 58 j)
def BKs43_45 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_59 (Nat.beq j 59)) (Bool.rec (motive := fun _ => ℕ) 0 BK_60 (Nat.beq j 60)) (Nat.ble 60 j)
def BKs41_45 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs41_43 j) (BKs43_45 j) (Nat.ble 59 j)
def BKs37_45 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs37_41 j) (BKs41_45 j) (Nat.ble 57 j)
def BKs30_45 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs30_37 j) (BKs37_45 j) (Nat.ble 53 j)
def BKs45_47 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_61 (Nat.beq j 61)) (Bool.rec (motive := fun _ => ℕ) 0 BK_62 (Nat.beq j 62)) (Nat.ble 62 j)
def BKs47_49 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_63 (Nat.beq j 63)) (Bool.rec (motive := fun _ => ℕ) 0 BK_64 (Nat.beq j 64)) (Nat.ble 64 j)
def BKs45_49 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs45_47 j) (BKs47_49 j) (Nat.ble 63 j)
def BKs49_51 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_65 (Nat.beq j 65)) (Bool.rec (motive := fun _ => ℕ) 0 BK_66 (Nat.beq j 66)) (Nat.ble 66 j)
def BKs51_53 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_67 (Nat.beq j 67)) (Bool.rec (motive := fun _ => ℕ) 0 BK_68 (Nat.beq j 68)) (Nat.ble 68 j)
def BKs49_53 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs49_51 j) (BKs51_53 j) (Nat.ble 67 j)
def BKs45_53 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs45_49 j) (BKs49_53 j) (Nat.ble 65 j)
def BKs53_55 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_69 (Nat.beq j 69)) (Bool.rec (motive := fun _ => ℕ) 0 BK_70 (Nat.beq j 70)) (Nat.ble 70 j)
def BKs55_57 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_71 (Nat.beq j 71)) (Bool.rec (motive := fun _ => ℕ) 0 BK_72 (Nat.beq j 72)) (Nat.ble 72 j)
def BKs53_57 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs53_55 j) (BKs55_57 j) (Nat.ble 71 j)
def BKs57_59 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_73 (Nat.beq j 73)) (Bool.rec (motive := fun _ => ℕ) 0 BK_74 (Nat.beq j 74)) (Nat.ble 74 j)
def BKs59_61 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_75 (Nat.beq j 75)) (Bool.rec (motive := fun _ => ℕ) 0 BK_76 (Nat.beq j 76)) (Nat.ble 76 j)
def BKs57_61 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs57_59 j) (BKs59_61 j) (Nat.ble 75 j)
def BKs53_61 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs53_57 j) (BKs57_61 j) (Nat.ble 73 j)
def BKs45_61 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs45_53 j) (BKs53_61 j) (Nat.ble 69 j)
def BKs30_61 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs30_45 j) (BKs45_61 j) (Nat.ble 61 j)
def BKs0_61 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs0_30 j) (BKs30_61 j) (Nat.ble 46 j)
def BKs62_64 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_78 (Nat.beq j 78)) (Bool.rec (motive := fun _ => ℕ) 0 BK_79 (Nat.beq j 79)) (Nat.ble 79 j)
def BKs61_64 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_77 (Nat.beq j 77)) (BKs62_64 j) (Nat.ble 78 j)
def BKs64_66 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_80 (Nat.beq j 80)) (Bool.rec (motive := fun _ => ℕ) 0 BK_81 (Nat.beq j 81)) (Nat.ble 81 j)
def BKs66_68 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_82 (Nat.beq j 82)) (Bool.rec (motive := fun _ => ℕ) 0 BK_83 (Nat.beq j 83)) (Nat.ble 83 j)
def BKs64_68 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs64_66 j) (BKs66_68 j) (Nat.ble 82 j)
def BKs61_68 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs61_64 j) (BKs64_68 j) (Nat.ble 80 j)
def BKs68_70 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_84 (Nat.beq j 84)) (Bool.rec (motive := fun _ => ℕ) 0 BK_85 (Nat.beq j 85)) (Nat.ble 85 j)
def BKs70_72 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_86 (Nat.beq j 86)) (Bool.rec (motive := fun _ => ℕ) 0 BK_87 (Nat.beq j 87)) (Nat.ble 87 j)
def BKs68_72 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs68_70 j) (BKs70_72 j) (Nat.ble 86 j)
def BKs72_74 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_88 (Nat.beq j 88)) (Bool.rec (motive := fun _ => ℕ) 0 BK_89 (Nat.beq j 89)) (Nat.ble 89 j)
def BKs74_76 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_90 (Nat.beq j 90)) (Bool.rec (motive := fun _ => ℕ) 0 BK_91 (Nat.beq j 91)) (Nat.ble 91 j)
def BKs72_76 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs72_74 j) (BKs74_76 j) (Nat.ble 90 j)
def BKs68_76 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs68_72 j) (BKs72_76 j) (Nat.ble 88 j)
def BKs61_76 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs61_68 j) (BKs68_76 j) (Nat.ble 84 j)
def BKs76_78 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_92 (Nat.beq j 92)) (Bool.rec (motive := fun _ => ℕ) 0 BK_93 (Nat.beq j 93)) (Nat.ble 93 j)
def BKs78_80 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_94 (Nat.beq j 94)) (Bool.rec (motive := fun _ => ℕ) 0 BK_95 (Nat.beq j 95)) (Nat.ble 95 j)
def BKs76_80 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs76_78 j) (BKs78_80 j) (Nat.ble 94 j)
def BKs80_82 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_96 (Nat.beq j 96)) (Bool.rec (motive := fun _ => ℕ) 0 BK_97 (Nat.beq j 97)) (Nat.ble 97 j)
def BKs82_84 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_98 (Nat.beq j 98)) (Bool.rec (motive := fun _ => ℕ) 0 BK_99 (Nat.beq j 99)) (Nat.ble 99 j)
def BKs80_84 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs80_82 j) (BKs82_84 j) (Nat.ble 98 j)
def BKs76_84 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs76_80 j) (BKs80_84 j) (Nat.ble 96 j)
def BKs84_86 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_100 (Nat.beq j 100)) (Bool.rec (motive := fun _ => ℕ) 0 BK_101 (Nat.beq j 101)) (Nat.ble 101 j)
def BKs86_88 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_102 (Nat.beq j 102)) (Bool.rec (motive := fun _ => ℕ) 0 BK_103 (Nat.beq j 103)) (Nat.ble 103 j)
def BKs84_88 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs84_86 j) (BKs86_88 j) (Nat.ble 102 j)
def BKs88_90 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_104 (Nat.beq j 104)) (Bool.rec (motive := fun _ => ℕ) 0 BK_105 (Nat.beq j 105)) (Nat.ble 105 j)
def BKs90_92 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_106 (Nat.beq j 106)) (Bool.rec (motive := fun _ => ℕ) 0 BK_107 (Nat.beq j 107)) (Nat.ble 107 j)
def BKs88_92 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs88_90 j) (BKs90_92 j) (Nat.ble 106 j)
def BKs84_92 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs84_88 j) (BKs88_92 j) (Nat.ble 104 j)
def BKs76_92 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs76_84 j) (BKs84_92 j) (Nat.ble 100 j)
def BKs61_92 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs61_76 j) (BKs76_92 j) (Nat.ble 92 j)
def BKs93_95 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_109 (Nat.beq j 109)) (Bool.rec (motive := fun _ => ℕ) 0 BK_110 (Nat.beq j 110)) (Nat.ble 110 j)
def BKs92_95 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_108 (Nat.beq j 108)) (BKs93_95 j) (Nat.ble 109 j)
def BKs95_97 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_111 (Nat.beq j 111)) (Bool.rec (motive := fun _ => ℕ) 0 BK_112 (Nat.beq j 112)) (Nat.ble 112 j)
def BKs97_99 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_113 (Nat.beq j 113)) (Bool.rec (motive := fun _ => ℕ) 0 BK_114 (Nat.beq j 114)) (Nat.ble 114 j)
def BKs95_99 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs95_97 j) (BKs97_99 j) (Nat.ble 113 j)
def BKs92_99 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs92_95 j) (BKs95_99 j) (Nat.ble 111 j)
def BKs99_101 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_115 (Nat.beq j 115)) (Bool.rec (motive := fun _ => ℕ) 0 BK_116 (Nat.beq j 116)) (Nat.ble 116 j)
def BKs101_103 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_117 (Nat.beq j 117)) (Bool.rec (motive := fun _ => ℕ) 0 BK_118 (Nat.beq j 118)) (Nat.ble 118 j)
def BKs99_103 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs99_101 j) (BKs101_103 j) (Nat.ble 117 j)
def BKs103_105 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_119 (Nat.beq j 119)) (Bool.rec (motive := fun _ => ℕ) 0 BK_120 (Nat.beq j 120)) (Nat.ble 120 j)
def BKs105_107 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_121 (Nat.beq j 121)) (Bool.rec (motive := fun _ => ℕ) 0 BK_122 (Nat.beq j 122)) (Nat.ble 122 j)
def BKs103_107 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs103_105 j) (BKs105_107 j) (Nat.ble 121 j)
def BKs99_107 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs99_103 j) (BKs103_107 j) (Nat.ble 119 j)
def BKs92_107 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs92_99 j) (BKs99_107 j) (Nat.ble 115 j)
def BKs107_109 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_123 (Nat.beq j 123)) (Bool.rec (motive := fun _ => ℕ) 0 BK_124 (Nat.beq j 124)) (Nat.ble 124 j)
def BKs109_111 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_125 (Nat.beq j 125)) (Bool.rec (motive := fun _ => ℕ) 0 BK_126 (Nat.beq j 126)) (Nat.ble 126 j)
def BKs107_111 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs107_109 j) (BKs109_111 j) (Nat.ble 125 j)
def BKs111_113 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_127 (Nat.beq j 127)) (Bool.rec (motive := fun _ => ℕ) 0 BK_128 (Nat.beq j 128)) (Nat.ble 128 j)
def BKs113_115 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_129 (Nat.beq j 129)) (Bool.rec (motive := fun _ => ℕ) 0 BK_130 (Nat.beq j 130)) (Nat.ble 130 j)
def BKs111_115 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs111_113 j) (BKs113_115 j) (Nat.ble 129 j)
def BKs107_115 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs107_111 j) (BKs111_115 j) (Nat.ble 127 j)
def BKs115_117 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_131 (Nat.beq j 131)) (Bool.rec (motive := fun _ => ℕ) 0 BK_132 (Nat.beq j 132)) (Nat.ble 132 j)
def BKs117_119 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_133 (Nat.beq j 133)) (Bool.rec (motive := fun _ => ℕ) 0 BK_134 (Nat.beq j 134)) (Nat.ble 134 j)
def BKs115_119 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs115_117 j) (BKs117_119 j) (Nat.ble 133 j)
def BKs119_121 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_135 (Nat.beq j 135)) (Bool.rec (motive := fun _ => ℕ) 0 BK_136 (Nat.beq j 136)) (Nat.ble 136 j)
def BKs121_123 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_137 (Nat.beq j 137)) (Bool.rec (motive := fun _ => ℕ) 0 BK_138 (Nat.beq j 138)) (Nat.ble 138 j)
def BKs119_123 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs119_121 j) (BKs121_123 j) (Nat.ble 137 j)
def BKs115_123 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs115_119 j) (BKs119_123 j) (Nat.ble 135 j)
def BKs107_123 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs107_115 j) (BKs115_123 j) (Nat.ble 131 j)
def BKs92_123 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs92_107 j) (BKs107_123 j) (Nat.ble 123 j)
def BKs61_123 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs61_92 j) (BKs92_123 j) (Nat.ble 108 j)
def BKs0_123 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs0_61 j) (BKs61_123 j) (Nat.ble 77 j)
def BKs124_126 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_140 (Nat.beq j 140)) (Bool.rec (motive := fun _ => ℕ) 0 BK_141 (Nat.beq j 141)) (Nat.ble 141 j)
def BKs123_126 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_139 (Nat.beq j 139)) (BKs124_126 j) (Nat.ble 140 j)
def BKs126_128 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_142 (Nat.beq j 142)) (Bool.rec (motive := fun _ => ℕ) 0 BK_143 (Nat.beq j 143)) (Nat.ble 143 j)
def BKs128_130 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_144 (Nat.beq j 144)) (Bool.rec (motive := fun _ => ℕ) 0 BK_145 (Nat.beq j 145)) (Nat.ble 145 j)
def BKs126_130 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs126_128 j) (BKs128_130 j) (Nat.ble 144 j)
def BKs123_130 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs123_126 j) (BKs126_130 j) (Nat.ble 142 j)
def BKs130_132 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_146 (Nat.beq j 146)) (Bool.rec (motive := fun _ => ℕ) 0 BK_147 (Nat.beq j 147)) (Nat.ble 147 j)
def BKs132_134 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_148 (Nat.beq j 148)) (Bool.rec (motive := fun _ => ℕ) 0 BK_149 (Nat.beq j 149)) (Nat.ble 149 j)
def BKs130_134 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs130_132 j) (BKs132_134 j) (Nat.ble 148 j)
def BKs134_136 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_150 (Nat.beq j 150)) (Bool.rec (motive := fun _ => ℕ) 0 BK_151 (Nat.beq j 151)) (Nat.ble 151 j)
def BKs136_138 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_152 (Nat.beq j 152)) (Bool.rec (motive := fun _ => ℕ) 0 BK_153 (Nat.beq j 153)) (Nat.ble 153 j)
def BKs134_138 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs134_136 j) (BKs136_138 j) (Nat.ble 152 j)
def BKs130_138 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs130_134 j) (BKs134_138 j) (Nat.ble 150 j)
def BKs123_138 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs123_130 j) (BKs130_138 j) (Nat.ble 146 j)
def BKs138_140 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_154 (Nat.beq j 154)) (Bool.rec (motive := fun _ => ℕ) 0 BK_155 (Nat.beq j 155)) (Nat.ble 155 j)
def BKs140_142 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_156 (Nat.beq j 156)) (Bool.rec (motive := fun _ => ℕ) 0 BK_157 (Nat.beq j 157)) (Nat.ble 157 j)
def BKs138_142 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs138_140 j) (BKs140_142 j) (Nat.ble 156 j)
def BKs142_144 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_158 (Nat.beq j 158)) (Bool.rec (motive := fun _ => ℕ) 0 BK_159 (Nat.beq j 159)) (Nat.ble 159 j)
def BKs144_146 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_160 (Nat.beq j 160)) (Bool.rec (motive := fun _ => ℕ) 0 BK_161 (Nat.beq j 161)) (Nat.ble 161 j)
def BKs142_146 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs142_144 j) (BKs144_146 j) (Nat.ble 160 j)
def BKs138_146 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs138_142 j) (BKs142_146 j) (Nat.ble 158 j)
def BKs146_148 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_162 (Nat.beq j 162)) (Bool.rec (motive := fun _ => ℕ) 0 BK_163 (Nat.beq j 163)) (Nat.ble 163 j)
def BKs148_150 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_164 (Nat.beq j 164)) (Bool.rec (motive := fun _ => ℕ) 0 BK_165 (Nat.beq j 165)) (Nat.ble 165 j)
def BKs146_150 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs146_148 j) (BKs148_150 j) (Nat.ble 164 j)
def BKs150_152 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_166 (Nat.beq j 166)) (Bool.rec (motive := fun _ => ℕ) 0 BK_167 (Nat.beq j 167)) (Nat.ble 167 j)
def BKs152_154 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_168 (Nat.beq j 168)) (Bool.rec (motive := fun _ => ℕ) 0 BK_169 (Nat.beq j 169)) (Nat.ble 169 j)
def BKs150_154 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs150_152 j) (BKs152_154 j) (Nat.ble 168 j)
def BKs146_154 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs146_150 j) (BKs150_154 j) (Nat.ble 166 j)
def BKs138_154 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs138_146 j) (BKs146_154 j) (Nat.ble 162 j)
def BKs123_154 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs123_138 j) (BKs138_154 j) (Nat.ble 154 j)
def BKs155_157 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_171 (Nat.beq j 171)) (Bool.rec (motive := fun _ => ℕ) 0 BK_172 (Nat.beq j 172)) (Nat.ble 172 j)
def BKs154_157 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_170 (Nat.beq j 170)) (BKs155_157 j) (Nat.ble 171 j)
def BKs157_159 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_173 (Nat.beq j 173)) (Bool.rec (motive := fun _ => ℕ) 0 BK_174 (Nat.beq j 174)) (Nat.ble 174 j)
def BKs159_161 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_175 (Nat.beq j 175)) (Bool.rec (motive := fun _ => ℕ) 0 BK_176 (Nat.beq j 176)) (Nat.ble 176 j)
def BKs157_161 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs157_159 j) (BKs159_161 j) (Nat.ble 175 j)
def BKs154_161 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs154_157 j) (BKs157_161 j) (Nat.ble 173 j)
def BKs161_163 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_177 (Nat.beq j 177)) (Bool.rec (motive := fun _ => ℕ) 0 BK_178 (Nat.beq j 178)) (Nat.ble 178 j)
def BKs163_165 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_179 (Nat.beq j 179)) (Bool.rec (motive := fun _ => ℕ) 0 BK_180 (Nat.beq j 180)) (Nat.ble 180 j)
def BKs161_165 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs161_163 j) (BKs163_165 j) (Nat.ble 179 j)
def BKs165_167 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_181 (Nat.beq j 181)) (Bool.rec (motive := fun _ => ℕ) 0 BK_182 (Nat.beq j 182)) (Nat.ble 182 j)
def BKs167_169 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_183 (Nat.beq j 183)) (Bool.rec (motive := fun _ => ℕ) 0 BK_184 (Nat.beq j 184)) (Nat.ble 184 j)
def BKs165_169 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs165_167 j) (BKs167_169 j) (Nat.ble 183 j)
def BKs161_169 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs161_165 j) (BKs165_169 j) (Nat.ble 181 j)
def BKs154_169 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs154_161 j) (BKs161_169 j) (Nat.ble 177 j)
def BKs169_171 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_185 (Nat.beq j 185)) (Bool.rec (motive := fun _ => ℕ) 0 BK_186 (Nat.beq j 186)) (Nat.ble 186 j)
def BKs171_173 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_187 (Nat.beq j 187)) (Bool.rec (motive := fun _ => ℕ) 0 BK_188 (Nat.beq j 188)) (Nat.ble 188 j)
def BKs169_173 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs169_171 j) (BKs171_173 j) (Nat.ble 187 j)
def BKs173_175 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_189 (Nat.beq j 189)) (Bool.rec (motive := fun _ => ℕ) 0 BK_190 (Nat.beq j 190)) (Nat.ble 190 j)
def BKs175_177 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_191 (Nat.beq j 191)) (Bool.rec (motive := fun _ => ℕ) 0 BK_192 (Nat.beq j 192)) (Nat.ble 192 j)
def BKs173_177 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs173_175 j) (BKs175_177 j) (Nat.ble 191 j)
def BKs169_177 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs169_173 j) (BKs173_177 j) (Nat.ble 189 j)
def BKs177_179 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_193 (Nat.beq j 193)) (Bool.rec (motive := fun _ => ℕ) 0 BK_194 (Nat.beq j 194)) (Nat.ble 194 j)
def BKs179_181 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_195 (Nat.beq j 195)) (Bool.rec (motive := fun _ => ℕ) 0 BK_196 (Nat.beq j 196)) (Nat.ble 196 j)
def BKs177_181 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs177_179 j) (BKs179_181 j) (Nat.ble 195 j)
def BKs181_183 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_197 (Nat.beq j 197)) (Bool.rec (motive := fun _ => ℕ) 0 BK_198 (Nat.beq j 198)) (Nat.ble 198 j)
def BKs183_185 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_199 (Nat.beq j 199)) (Bool.rec (motive := fun _ => ℕ) 0 BK_200 (Nat.beq j 200)) (Nat.ble 200 j)
def BKs181_185 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs181_183 j) (BKs183_185 j) (Nat.ble 199 j)
def BKs177_185 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs177_181 j) (BKs181_185 j) (Nat.ble 197 j)
def BKs169_185 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs169_177 j) (BKs177_185 j) (Nat.ble 193 j)
def BKs154_185 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs154_169 j) (BKs169_185 j) (Nat.ble 185 j)
def BKs123_185 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs123_154 j) (BKs154_185 j) (Nat.ble 170 j)
def BKs186_188 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_202 (Nat.beq j 202)) (Bool.rec (motive := fun _ => ℕ) 0 BK_203 (Nat.beq j 203)) (Nat.ble 203 j)
def BKs185_188 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_201 (Nat.beq j 201)) (BKs186_188 j) (Nat.ble 202 j)
def BKs188_190 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_204 (Nat.beq j 204)) (Bool.rec (motive := fun _ => ℕ) 0 BK_205 (Nat.beq j 205)) (Nat.ble 205 j)
def BKs190_192 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_206 (Nat.beq j 206)) (Bool.rec (motive := fun _ => ℕ) 0 BK_207 (Nat.beq j 207)) (Nat.ble 207 j)
def BKs188_192 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs188_190 j) (BKs190_192 j) (Nat.ble 206 j)
def BKs185_192 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs185_188 j) (BKs188_192 j) (Nat.ble 204 j)
def BKs192_194 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_208 (Nat.beq j 208)) (Bool.rec (motive := fun _ => ℕ) 0 BK_209 (Nat.beq j 209)) (Nat.ble 209 j)
def BKs194_196 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_210 (Nat.beq j 210)) (Bool.rec (motive := fun _ => ℕ) 0 BK_211 (Nat.beq j 211)) (Nat.ble 211 j)
def BKs192_196 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs192_194 j) (BKs194_196 j) (Nat.ble 210 j)
def BKs196_198 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_212 (Nat.beq j 212)) (Bool.rec (motive := fun _ => ℕ) 0 BK_213 (Nat.beq j 213)) (Nat.ble 213 j)
def BKs198_200 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_214 (Nat.beq j 214)) (Bool.rec (motive := fun _ => ℕ) 0 BK_215 (Nat.beq j 215)) (Nat.ble 215 j)
def BKs196_200 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs196_198 j) (BKs198_200 j) (Nat.ble 214 j)
def BKs192_200 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs192_196 j) (BKs196_200 j) (Nat.ble 212 j)
def BKs185_200 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs185_192 j) (BKs192_200 j) (Nat.ble 208 j)
def BKs200_202 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_216 (Nat.beq j 216)) (Bool.rec (motive := fun _ => ℕ) 0 BK_217 (Nat.beq j 217)) (Nat.ble 217 j)
def BKs202_204 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_218 (Nat.beq j 218)) (Bool.rec (motive := fun _ => ℕ) 0 BK_219 (Nat.beq j 219)) (Nat.ble 219 j)
def BKs200_204 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs200_202 j) (BKs202_204 j) (Nat.ble 218 j)
def BKs204_206 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_220 (Nat.beq j 220)) (Bool.rec (motive := fun _ => ℕ) 0 BK_221 (Nat.beq j 221)) (Nat.ble 221 j)
def BKs206_208 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_222 (Nat.beq j 222)) (Bool.rec (motive := fun _ => ℕ) 0 BK_223 (Nat.beq j 223)) (Nat.ble 223 j)
def BKs204_208 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs204_206 j) (BKs206_208 j) (Nat.ble 222 j)
def BKs200_208 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs200_204 j) (BKs204_208 j) (Nat.ble 220 j)
def BKs208_210 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_224 (Nat.beq j 224)) (Bool.rec (motive := fun _ => ℕ) 0 BK_225 (Nat.beq j 225)) (Nat.ble 225 j)
def BKs210_212 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_226 (Nat.beq j 226)) (Bool.rec (motive := fun _ => ℕ) 0 BK_227 (Nat.beq j 227)) (Nat.ble 227 j)
def BKs208_212 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs208_210 j) (BKs210_212 j) (Nat.ble 226 j)
def BKs212_214 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_228 (Nat.beq j 228)) (Bool.rec (motive := fun _ => ℕ) 0 BK_229 (Nat.beq j 229)) (Nat.ble 229 j)
def BKs214_216 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_230 (Nat.beq j 230)) (Bool.rec (motive := fun _ => ℕ) 0 BK_231 (Nat.beq j 231)) (Nat.ble 231 j)
def BKs212_216 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs212_214 j) (BKs214_216 j) (Nat.ble 230 j)
def BKs208_216 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs208_212 j) (BKs212_216 j) (Nat.ble 228 j)
def BKs200_216 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs200_208 j) (BKs208_216 j) (Nat.ble 224 j)
def BKs185_216 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs185_200 j) (BKs200_216 j) (Nat.ble 216 j)
def BKs217_219 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_233 (Nat.beq j 233)) (Bool.rec (motive := fun _ => ℕ) 0 BK_234 (Nat.beq j 234)) (Nat.ble 234 j)
def BKs216_219 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_232 (Nat.beq j 232)) (BKs217_219 j) (Nat.ble 233 j)
def BKs219_221 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_235 (Nat.beq j 235)) (Bool.rec (motive := fun _ => ℕ) 0 BK_236 (Nat.beq j 236)) (Nat.ble 236 j)
def BKs221_223 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_237 (Nat.beq j 237)) (Bool.rec (motive := fun _ => ℕ) 0 BK_238 (Nat.beq j 238)) (Nat.ble 238 j)
def BKs219_223 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs219_221 j) (BKs221_223 j) (Nat.ble 237 j)
def BKs216_223 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs216_219 j) (BKs219_223 j) (Nat.ble 235 j)
def BKs223_225 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_239 (Nat.beq j 239)) (Bool.rec (motive := fun _ => ℕ) 0 BK_240 (Nat.beq j 240)) (Nat.ble 240 j)
def BKs225_227 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_241 (Nat.beq j 241)) (Bool.rec (motive := fun _ => ℕ) 0 BK_242 (Nat.beq j 242)) (Nat.ble 242 j)
def BKs223_227 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs223_225 j) (BKs225_227 j) (Nat.ble 241 j)
def BKs227_229 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_243 (Nat.beq j 243)) (Bool.rec (motive := fun _ => ℕ) 0 BK_244 (Nat.beq j 244)) (Nat.ble 244 j)
def BKs229_231 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_245 (Nat.beq j 245)) (Bool.rec (motive := fun _ => ℕ) 0 BK_246 (Nat.beq j 246)) (Nat.ble 246 j)
def BKs227_231 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs227_229 j) (BKs229_231 j) (Nat.ble 245 j)
def BKs223_231 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs223_227 j) (BKs227_231 j) (Nat.ble 243 j)
def BKs216_231 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs216_223 j) (BKs223_231 j) (Nat.ble 239 j)
def BKs231_233 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_247 (Nat.beq j 247)) (Bool.rec (motive := fun _ => ℕ) 0 BK_248 (Nat.beq j 248)) (Nat.ble 248 j)
def BKs233_235 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_249 (Nat.beq j 249)) (Bool.rec (motive := fun _ => ℕ) 0 BK_250 (Nat.beq j 250)) (Nat.ble 250 j)
def BKs231_235 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs231_233 j) (BKs233_235 j) (Nat.ble 249 j)
def BKs235_237 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_251 (Nat.beq j 251)) (Bool.rec (motive := fun _ => ℕ) 0 BK_252 (Nat.beq j 252)) (Nat.ble 252 j)
def BKs237_239 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_253 (Nat.beq j 253)) (Bool.rec (motive := fun _ => ℕ) 0 BK_254 (Nat.beq j 254)) (Nat.ble 254 j)
def BKs235_239 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs235_237 j) (BKs237_239 j) (Nat.ble 253 j)
def BKs231_239 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs231_235 j) (BKs235_239 j) (Nat.ble 251 j)
def BKs239_241 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_255 (Nat.beq j 255)) (Bool.rec (motive := fun _ => ℕ) 0 BK_256 (Nat.beq j 256)) (Nat.ble 256 j)
def BKs241_243 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_257 (Nat.beq j 257)) (Bool.rec (motive := fun _ => ℕ) 0 BK_258 (Nat.beq j 258)) (Nat.ble 258 j)
def BKs239_243 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs239_241 j) (BKs241_243 j) (Nat.ble 257 j)
def BKs243_245 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_259 (Nat.beq j 259)) (Bool.rec (motive := fun _ => ℕ) 0 BK_260 (Nat.beq j 260)) (Nat.ble 260 j)
def BKs245_247 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_261 (Nat.beq j 261)) (Bool.rec (motive := fun _ => ℕ) 0 BK_262 (Nat.beq j 262)) (Nat.ble 262 j)
def BKs243_247 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs243_245 j) (BKs245_247 j) (Nat.ble 261 j)
def BKs239_247 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs239_243 j) (BKs243_247 j) (Nat.ble 259 j)
def BKs231_247 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs231_239 j) (BKs239_247 j) (Nat.ble 255 j)
def BKs216_247 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs216_231 j) (BKs231_247 j) (Nat.ble 247 j)
def BKs185_247 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs185_216 j) (BKs216_247 j) (Nat.ble 232 j)
def BKs123_247 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs123_185 j) (BKs185_247 j) (Nat.ble 201 j)
def BKs0_247 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs0_123 j) (BKs123_247 j) (Nat.ble 139 j)
def BKs248_250 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_264 (Nat.beq j 264)) (Bool.rec (motive := fun _ => ℕ) 0 BK_265 (Nat.beq j 265)) (Nat.ble 265 j)
def BKs247_250 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_263 (Nat.beq j 263)) (BKs248_250 j) (Nat.ble 264 j)
def BKs250_252 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_266 (Nat.beq j 266)) (Bool.rec (motive := fun _ => ℕ) 0 BK_267 (Nat.beq j 267)) (Nat.ble 267 j)
def BKs252_254 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_268 (Nat.beq j 268)) (Bool.rec (motive := fun _ => ℕ) 0 BK_269 (Nat.beq j 269)) (Nat.ble 269 j)
def BKs250_254 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs250_252 j) (BKs252_254 j) (Nat.ble 268 j)
def BKs247_254 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs247_250 j) (BKs250_254 j) (Nat.ble 266 j)
def BKs254_256 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_270 (Nat.beq j 270)) (Bool.rec (motive := fun _ => ℕ) 0 BK_271 (Nat.beq j 271)) (Nat.ble 271 j)
def BKs256_258 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_272 (Nat.beq j 272)) (Bool.rec (motive := fun _ => ℕ) 0 BK_273 (Nat.beq j 273)) (Nat.ble 273 j)
def BKs254_258 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs254_256 j) (BKs256_258 j) (Nat.ble 272 j)
def BKs258_260 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_274 (Nat.beq j 274)) (Bool.rec (motive := fun _ => ℕ) 0 BK_275 (Nat.beq j 275)) (Nat.ble 275 j)
def BKs260_262 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_276 (Nat.beq j 276)) (Bool.rec (motive := fun _ => ℕ) 0 BK_277 (Nat.beq j 277)) (Nat.ble 277 j)
def BKs258_262 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs258_260 j) (BKs260_262 j) (Nat.ble 276 j)
def BKs254_262 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs254_258 j) (BKs258_262 j) (Nat.ble 274 j)
def BKs247_262 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs247_254 j) (BKs254_262 j) (Nat.ble 270 j)
def BKs262_264 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_278 (Nat.beq j 278)) (Bool.rec (motive := fun _ => ℕ) 0 BK_279 (Nat.beq j 279)) (Nat.ble 279 j)
def BKs264_266 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_280 (Nat.beq j 280)) (Bool.rec (motive := fun _ => ℕ) 0 BK_281 (Nat.beq j 281)) (Nat.ble 281 j)
def BKs262_266 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs262_264 j) (BKs264_266 j) (Nat.ble 280 j)
def BKs266_268 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_282 (Nat.beq j 282)) (Bool.rec (motive := fun _ => ℕ) 0 BK_283 (Nat.beq j 283)) (Nat.ble 283 j)
def BKs268_270 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_284 (Nat.beq j 284)) (Bool.rec (motive := fun _ => ℕ) 0 BK_285 (Nat.beq j 285)) (Nat.ble 285 j)
def BKs266_270 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs266_268 j) (BKs268_270 j) (Nat.ble 284 j)
def BKs262_270 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs262_266 j) (BKs266_270 j) (Nat.ble 282 j)
def BKs270_272 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_286 (Nat.beq j 286)) (Bool.rec (motive := fun _ => ℕ) 0 BK_287 (Nat.beq j 287)) (Nat.ble 287 j)
def BKs272_274 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_288 (Nat.beq j 288)) (Bool.rec (motive := fun _ => ℕ) 0 BK_289 (Nat.beq j 289)) (Nat.ble 289 j)
def BKs270_274 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs270_272 j) (BKs272_274 j) (Nat.ble 288 j)
def BKs274_276 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_290 (Nat.beq j 290)) (Bool.rec (motive := fun _ => ℕ) 0 BK_291 (Nat.beq j 291)) (Nat.ble 291 j)
def BKs276_278 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_292 (Nat.beq j 292)) (Bool.rec (motive := fun _ => ℕ) 0 BK_293 (Nat.beq j 293)) (Nat.ble 293 j)
def BKs274_278 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs274_276 j) (BKs276_278 j) (Nat.ble 292 j)
def BKs270_278 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs270_274 j) (BKs274_278 j) (Nat.ble 290 j)
def BKs262_278 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs262_270 j) (BKs270_278 j) (Nat.ble 286 j)
def BKs247_278 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs247_262 j) (BKs262_278 j) (Nat.ble 278 j)
def BKs279_281 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_295 (Nat.beq j 295)) (Bool.rec (motive := fun _ => ℕ) 0 BK_296 (Nat.beq j 296)) (Nat.ble 296 j)
def BKs278_281 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_294 (Nat.beq j 294)) (BKs279_281 j) (Nat.ble 295 j)
def BKs281_283 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_297 (Nat.beq j 297)) (Bool.rec (motive := fun _ => ℕ) 0 BK_298 (Nat.beq j 298)) (Nat.ble 298 j)
def BKs283_285 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_299 (Nat.beq j 299)) (Bool.rec (motive := fun _ => ℕ) 0 BK_300 (Nat.beq j 300)) (Nat.ble 300 j)
def BKs281_285 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs281_283 j) (BKs283_285 j) (Nat.ble 299 j)
def BKs278_285 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs278_281 j) (BKs281_285 j) (Nat.ble 297 j)
def BKs285_287 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_301 (Nat.beq j 301)) (Bool.rec (motive := fun _ => ℕ) 0 BK_302 (Nat.beq j 302)) (Nat.ble 302 j)
def BKs287_289 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_303 (Nat.beq j 303)) (Bool.rec (motive := fun _ => ℕ) 0 BK_304 (Nat.beq j 304)) (Nat.ble 304 j)
def BKs285_289 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs285_287 j) (BKs287_289 j) (Nat.ble 303 j)
def BKs289_291 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_305 (Nat.beq j 305)) (Bool.rec (motive := fun _ => ℕ) 0 BK_306 (Nat.beq j 306)) (Nat.ble 306 j)
def BKs291_293 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_307 (Nat.beq j 307)) (Bool.rec (motive := fun _ => ℕ) 0 BK_308 (Nat.beq j 308)) (Nat.ble 308 j)
def BKs289_293 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs289_291 j) (BKs291_293 j) (Nat.ble 307 j)
def BKs285_293 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs285_289 j) (BKs289_293 j) (Nat.ble 305 j)
def BKs278_293 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs278_285 j) (BKs285_293 j) (Nat.ble 301 j)
def BKs293_295 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_309 (Nat.beq j 309)) (Bool.rec (motive := fun _ => ℕ) 0 BK_310 (Nat.beq j 310)) (Nat.ble 310 j)
def BKs295_297 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_311 (Nat.beq j 311)) (Bool.rec (motive := fun _ => ℕ) 0 BK_312 (Nat.beq j 312)) (Nat.ble 312 j)
def BKs293_297 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs293_295 j) (BKs295_297 j) (Nat.ble 311 j)
def BKs297_299 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_313 (Nat.beq j 313)) (Bool.rec (motive := fun _ => ℕ) 0 BK_314 (Nat.beq j 314)) (Nat.ble 314 j)
def BKs299_301 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_315 (Nat.beq j 315)) (Bool.rec (motive := fun _ => ℕ) 0 BK_316 (Nat.beq j 316)) (Nat.ble 316 j)
def BKs297_301 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs297_299 j) (BKs299_301 j) (Nat.ble 315 j)
def BKs293_301 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs293_297 j) (BKs297_301 j) (Nat.ble 313 j)
def BKs301_303 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_317 (Nat.beq j 317)) (Bool.rec (motive := fun _ => ℕ) 0 BK_318 (Nat.beq j 318)) (Nat.ble 318 j)
def BKs303_305 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_319 (Nat.beq j 319)) (Bool.rec (motive := fun _ => ℕ) 0 BK_320 (Nat.beq j 320)) (Nat.ble 320 j)
def BKs301_305 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs301_303 j) (BKs303_305 j) (Nat.ble 319 j)
def BKs305_307 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_321 (Nat.beq j 321)) (Bool.rec (motive := fun _ => ℕ) 0 BK_322 (Nat.beq j 322)) (Nat.ble 322 j)
def BKs307_309 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_323 (Nat.beq j 323)) (Bool.rec (motive := fun _ => ℕ) 0 BK_324 (Nat.beq j 324)) (Nat.ble 324 j)
def BKs305_309 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs305_307 j) (BKs307_309 j) (Nat.ble 323 j)
def BKs301_309 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs301_305 j) (BKs305_309 j) (Nat.ble 321 j)
def BKs293_309 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs293_301 j) (BKs301_309 j) (Nat.ble 317 j)
def BKs278_309 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs278_293 j) (BKs293_309 j) (Nat.ble 309 j)
def BKs247_309 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs247_278 j) (BKs278_309 j) (Nat.ble 294 j)
def BKs310_312 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_326 (Nat.beq j 326)) (Bool.rec (motive := fun _ => ℕ) 0 BK_327 (Nat.beq j 327)) (Nat.ble 327 j)
def BKs309_312 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_325 (Nat.beq j 325)) (BKs310_312 j) (Nat.ble 326 j)
def BKs312_314 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_328 (Nat.beq j 328)) (Bool.rec (motive := fun _ => ℕ) 0 BK_329 (Nat.beq j 329)) (Nat.ble 329 j)
def BKs314_316 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_330 (Nat.beq j 330)) (Bool.rec (motive := fun _ => ℕ) 0 BK_331 (Nat.beq j 331)) (Nat.ble 331 j)
def BKs312_316 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs312_314 j) (BKs314_316 j) (Nat.ble 330 j)
def BKs309_316 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs309_312 j) (BKs312_316 j) (Nat.ble 328 j)
def BKs316_318 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_332 (Nat.beq j 332)) (Bool.rec (motive := fun _ => ℕ) 0 BK_333 (Nat.beq j 333)) (Nat.ble 333 j)
def BKs318_320 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_334 (Nat.beq j 334)) (Bool.rec (motive := fun _ => ℕ) 0 BK_335 (Nat.beq j 335)) (Nat.ble 335 j)
def BKs316_320 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs316_318 j) (BKs318_320 j) (Nat.ble 334 j)
def BKs320_322 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_336 (Nat.beq j 336)) (Bool.rec (motive := fun _ => ℕ) 0 BK_337 (Nat.beq j 337)) (Nat.ble 337 j)
def BKs322_324 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_338 (Nat.beq j 338)) (Bool.rec (motive := fun _ => ℕ) 0 BK_339 (Nat.beq j 339)) (Nat.ble 339 j)
def BKs320_324 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs320_322 j) (BKs322_324 j) (Nat.ble 338 j)
def BKs316_324 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs316_320 j) (BKs320_324 j) (Nat.ble 336 j)
def BKs309_324 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs309_316 j) (BKs316_324 j) (Nat.ble 332 j)
def BKs324_326 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_340 (Nat.beq j 340)) (Bool.rec (motive := fun _ => ℕ) 0 BK_341 (Nat.beq j 341)) (Nat.ble 341 j)
def BKs326_328 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_342 (Nat.beq j 342)) (Bool.rec (motive := fun _ => ℕ) 0 BK_343 (Nat.beq j 343)) (Nat.ble 343 j)
def BKs324_328 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs324_326 j) (BKs326_328 j) (Nat.ble 342 j)
def BKs328_330 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_344 (Nat.beq j 344)) (Bool.rec (motive := fun _ => ℕ) 0 BK_345 (Nat.beq j 345)) (Nat.ble 345 j)
def BKs330_332 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_346 (Nat.beq j 346)) (Bool.rec (motive := fun _ => ℕ) 0 BK_347 (Nat.beq j 347)) (Nat.ble 347 j)
def BKs328_332 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs328_330 j) (BKs330_332 j) (Nat.ble 346 j)
def BKs324_332 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs324_328 j) (BKs328_332 j) (Nat.ble 344 j)
def BKs332_334 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_348 (Nat.beq j 348)) (Bool.rec (motive := fun _ => ℕ) 0 BK_349 (Nat.beq j 349)) (Nat.ble 349 j)
def BKs334_336 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_350 (Nat.beq j 350)) (Bool.rec (motive := fun _ => ℕ) 0 BK_351 (Nat.beq j 351)) (Nat.ble 351 j)
def BKs332_336 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs332_334 j) (BKs334_336 j) (Nat.ble 350 j)
def BKs336_338 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_352 (Nat.beq j 352)) (Bool.rec (motive := fun _ => ℕ) 0 BK_353 (Nat.beq j 353)) (Nat.ble 353 j)
def BKs338_340 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_354 (Nat.beq j 354)) (Bool.rec (motive := fun _ => ℕ) 0 BK_355 (Nat.beq j 355)) (Nat.ble 355 j)
def BKs336_340 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs336_338 j) (BKs338_340 j) (Nat.ble 354 j)
def BKs332_340 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs332_336 j) (BKs336_340 j) (Nat.ble 352 j)
def BKs324_340 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs324_332 j) (BKs332_340 j) (Nat.ble 348 j)
def BKs309_340 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs309_324 j) (BKs324_340 j) (Nat.ble 340 j)
def BKs341_343 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_357 (Nat.beq j 357)) (Bool.rec (motive := fun _ => ℕ) 0 BK_358 (Nat.beq j 358)) (Nat.ble 358 j)
def BKs340_343 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_356 (Nat.beq j 356)) (BKs341_343 j) (Nat.ble 357 j)
def BKs343_345 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_359 (Nat.beq j 359)) (Bool.rec (motive := fun _ => ℕ) 0 BK_360 (Nat.beq j 360)) (Nat.ble 360 j)
def BKs345_347 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_361 (Nat.beq j 361)) (Bool.rec (motive := fun _ => ℕ) 0 BK_362 (Nat.beq j 362)) (Nat.ble 362 j)
def BKs343_347 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs343_345 j) (BKs345_347 j) (Nat.ble 361 j)
def BKs340_347 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs340_343 j) (BKs343_347 j) (Nat.ble 359 j)
def BKs347_349 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_363 (Nat.beq j 363)) (Bool.rec (motive := fun _ => ℕ) 0 BK_364 (Nat.beq j 364)) (Nat.ble 364 j)
def BKs349_351 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_365 (Nat.beq j 365)) (Bool.rec (motive := fun _ => ℕ) 0 BK_366 (Nat.beq j 366)) (Nat.ble 366 j)
def BKs347_351 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs347_349 j) (BKs349_351 j) (Nat.ble 365 j)
def BKs351_353 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_367 (Nat.beq j 367)) (Bool.rec (motive := fun _ => ℕ) 0 BK_368 (Nat.beq j 368)) (Nat.ble 368 j)
def BKs353_355 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_369 (Nat.beq j 369)) (Bool.rec (motive := fun _ => ℕ) 0 BK_370 (Nat.beq j 370)) (Nat.ble 370 j)
def BKs351_355 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs351_353 j) (BKs353_355 j) (Nat.ble 369 j)
def BKs347_355 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs347_351 j) (BKs351_355 j) (Nat.ble 367 j)
def BKs340_355 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs340_347 j) (BKs347_355 j) (Nat.ble 363 j)
def BKs355_357 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_371 (Nat.beq j 371)) (Bool.rec (motive := fun _ => ℕ) 0 BK_372 (Nat.beq j 372)) (Nat.ble 372 j)
def BKs357_359 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_373 (Nat.beq j 373)) (Bool.rec (motive := fun _ => ℕ) 0 BK_374 (Nat.beq j 374)) (Nat.ble 374 j)
def BKs355_359 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs355_357 j) (BKs357_359 j) (Nat.ble 373 j)
def BKs359_361 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_375 (Nat.beq j 375)) (Bool.rec (motive := fun _ => ℕ) 0 BK_376 (Nat.beq j 376)) (Nat.ble 376 j)
def BKs361_363 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_377 (Nat.beq j 377)) (Bool.rec (motive := fun _ => ℕ) 0 BK_378 (Nat.beq j 378)) (Nat.ble 378 j)
def BKs359_363 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs359_361 j) (BKs361_363 j) (Nat.ble 377 j)
def BKs355_363 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs355_359 j) (BKs359_363 j) (Nat.ble 375 j)
def BKs363_365 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_379 (Nat.beq j 379)) (Bool.rec (motive := fun _ => ℕ) 0 BK_380 (Nat.beq j 380)) (Nat.ble 380 j)
def BKs365_367 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_381 (Nat.beq j 381)) (Bool.rec (motive := fun _ => ℕ) 0 BK_382 (Nat.beq j 382)) (Nat.ble 382 j)
def BKs363_367 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs363_365 j) (BKs365_367 j) (Nat.ble 381 j)
def BKs367_369 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_383 (Nat.beq j 383)) (Bool.rec (motive := fun _ => ℕ) 0 BK_384 (Nat.beq j 384)) (Nat.ble 384 j)
def BKs369_371 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_385 (Nat.beq j 385)) (Bool.rec (motive := fun _ => ℕ) 0 BK_386 (Nat.beq j 386)) (Nat.ble 386 j)
def BKs367_371 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs367_369 j) (BKs369_371 j) (Nat.ble 385 j)
def BKs363_371 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs363_367 j) (BKs367_371 j) (Nat.ble 383 j)
def BKs355_371 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs355_363 j) (BKs363_371 j) (Nat.ble 379 j)
def BKs340_371 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs340_355 j) (BKs355_371 j) (Nat.ble 371 j)
def BKs309_371 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs309_340 j) (BKs340_371 j) (Nat.ble 356 j)
def BKs247_371 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs247_309 j) (BKs309_371 j) (Nat.ble 325 j)
def BKs372_374 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_388 (Nat.beq j 388)) (Bool.rec (motive := fun _ => ℕ) 0 BK_389 (Nat.beq j 389)) (Nat.ble 389 j)
def BKs371_374 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_387 (Nat.beq j 387)) (BKs372_374 j) (Nat.ble 388 j)
def BKs374_376 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_390 (Nat.beq j 390)) (Bool.rec (motive := fun _ => ℕ) 0 BK_391 (Nat.beq j 391)) (Nat.ble 391 j)
def BKs376_378 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_392 (Nat.beq j 392)) (Bool.rec (motive := fun _ => ℕ) 0 BK_393 (Nat.beq j 393)) (Nat.ble 393 j)
def BKs374_378 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs374_376 j) (BKs376_378 j) (Nat.ble 392 j)
def BKs371_378 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs371_374 j) (BKs374_378 j) (Nat.ble 390 j)
def BKs378_380 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_394 (Nat.beq j 394)) (Bool.rec (motive := fun _ => ℕ) 0 BK_395 (Nat.beq j 395)) (Nat.ble 395 j)
def BKs380_382 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_396 (Nat.beq j 396)) (Bool.rec (motive := fun _ => ℕ) 0 BK_397 (Nat.beq j 397)) (Nat.ble 397 j)
def BKs378_382 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs378_380 j) (BKs380_382 j) (Nat.ble 396 j)
def BKs382_384 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_398 (Nat.beq j 398)) (Bool.rec (motive := fun _ => ℕ) 0 BK_399 (Nat.beq j 399)) (Nat.ble 399 j)
def BKs384_386 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_400 (Nat.beq j 400)) (Bool.rec (motive := fun _ => ℕ) 0 BK_401 (Nat.beq j 401)) (Nat.ble 401 j)
def BKs382_386 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs382_384 j) (BKs384_386 j) (Nat.ble 400 j)
def BKs378_386 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs378_382 j) (BKs382_386 j) (Nat.ble 398 j)
def BKs371_386 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs371_378 j) (BKs378_386 j) (Nat.ble 394 j)
def BKs386_388 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_402 (Nat.beq j 402)) (Bool.rec (motive := fun _ => ℕ) 0 BK_403 (Nat.beq j 403)) (Nat.ble 403 j)
def BKs388_390 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_404 (Nat.beq j 404)) (Bool.rec (motive := fun _ => ℕ) 0 BK_405 (Nat.beq j 405)) (Nat.ble 405 j)
def BKs386_390 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs386_388 j) (BKs388_390 j) (Nat.ble 404 j)
def BKs390_392 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_406 (Nat.beq j 406)) (Bool.rec (motive := fun _ => ℕ) 0 BK_407 (Nat.beq j 407)) (Nat.ble 407 j)
def BKs392_394 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_408 (Nat.beq j 408)) (Bool.rec (motive := fun _ => ℕ) 0 BK_409 (Nat.beq j 409)) (Nat.ble 409 j)
def BKs390_394 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs390_392 j) (BKs392_394 j) (Nat.ble 408 j)
def BKs386_394 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs386_390 j) (BKs390_394 j) (Nat.ble 406 j)
def BKs394_396 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_410 (Nat.beq j 410)) (Bool.rec (motive := fun _ => ℕ) 0 BK_411 (Nat.beq j 411)) (Nat.ble 411 j)
def BKs396_398 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_412 (Nat.beq j 412)) (Bool.rec (motive := fun _ => ℕ) 0 BK_413 (Nat.beq j 413)) (Nat.ble 413 j)
def BKs394_398 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs394_396 j) (BKs396_398 j) (Nat.ble 412 j)
def BKs398_400 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_414 (Nat.beq j 414)) (Bool.rec (motive := fun _ => ℕ) 0 BK_415 (Nat.beq j 415)) (Nat.ble 415 j)
def BKs400_402 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_416 (Nat.beq j 416)) (Bool.rec (motive := fun _ => ℕ) 0 BK_417 (Nat.beq j 417)) (Nat.ble 417 j)
def BKs398_402 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs398_400 j) (BKs400_402 j) (Nat.ble 416 j)
def BKs394_402 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs394_398 j) (BKs398_402 j) (Nat.ble 414 j)
def BKs386_402 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs386_394 j) (BKs394_402 j) (Nat.ble 410 j)
def BKs371_402 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs371_386 j) (BKs386_402 j) (Nat.ble 402 j)
def BKs403_405 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_419 (Nat.beq j 419)) (Bool.rec (motive := fun _ => ℕ) 0 BK_420 (Nat.beq j 420)) (Nat.ble 420 j)
def BKs402_405 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_418 (Nat.beq j 418)) (BKs403_405 j) (Nat.ble 419 j)
def BKs405_407 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_421 (Nat.beq j 421)) (Bool.rec (motive := fun _ => ℕ) 0 BK_422 (Nat.beq j 422)) (Nat.ble 422 j)
def BKs407_409 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_423 (Nat.beq j 423)) (Bool.rec (motive := fun _ => ℕ) 0 BK_424 (Nat.beq j 424)) (Nat.ble 424 j)
def BKs405_409 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs405_407 j) (BKs407_409 j) (Nat.ble 423 j)
def BKs402_409 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs402_405 j) (BKs405_409 j) (Nat.ble 421 j)
def BKs409_411 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_425 (Nat.beq j 425)) (Bool.rec (motive := fun _ => ℕ) 0 BK_426 (Nat.beq j 426)) (Nat.ble 426 j)
def BKs411_413 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_427 (Nat.beq j 427)) (Bool.rec (motive := fun _ => ℕ) 0 BK_428 (Nat.beq j 428)) (Nat.ble 428 j)
def BKs409_413 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs409_411 j) (BKs411_413 j) (Nat.ble 427 j)
def BKs413_415 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_429 (Nat.beq j 429)) (Bool.rec (motive := fun _ => ℕ) 0 BK_430 (Nat.beq j 430)) (Nat.ble 430 j)
def BKs415_417 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_431 (Nat.beq j 431)) (Bool.rec (motive := fun _ => ℕ) 0 BK_432 (Nat.beq j 432)) (Nat.ble 432 j)
def BKs413_417 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs413_415 j) (BKs415_417 j) (Nat.ble 431 j)
def BKs409_417 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs409_413 j) (BKs413_417 j) (Nat.ble 429 j)
def BKs402_417 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs402_409 j) (BKs409_417 j) (Nat.ble 425 j)
def BKs417_419 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_433 (Nat.beq j 433)) (Bool.rec (motive := fun _ => ℕ) 0 BK_434 (Nat.beq j 434)) (Nat.ble 434 j)
def BKs419_421 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_435 (Nat.beq j 435)) (Bool.rec (motive := fun _ => ℕ) 0 BK_436 (Nat.beq j 436)) (Nat.ble 436 j)
def BKs417_421 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs417_419 j) (BKs419_421 j) (Nat.ble 435 j)
def BKs421_423 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_437 (Nat.beq j 437)) (Bool.rec (motive := fun _ => ℕ) 0 BK_438 (Nat.beq j 438)) (Nat.ble 438 j)
def BKs423_425 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_439 (Nat.beq j 439)) (Bool.rec (motive := fun _ => ℕ) 0 BK_440 (Nat.beq j 440)) (Nat.ble 440 j)
def BKs421_425 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs421_423 j) (BKs423_425 j) (Nat.ble 439 j)
def BKs417_425 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs417_421 j) (BKs421_425 j) (Nat.ble 437 j)
def BKs425_427 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_441 (Nat.beq j 441)) (Bool.rec (motive := fun _ => ℕ) 0 BK_442 (Nat.beq j 442)) (Nat.ble 442 j)
def BKs427_429 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_443 (Nat.beq j 443)) (Bool.rec (motive := fun _ => ℕ) 0 BK_444 (Nat.beq j 444)) (Nat.ble 444 j)
def BKs425_429 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs425_427 j) (BKs427_429 j) (Nat.ble 443 j)
def BKs429_431 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_445 (Nat.beq j 445)) (Bool.rec (motive := fun _ => ℕ) 0 BK_446 (Nat.beq j 446)) (Nat.ble 446 j)
def BKs431_433 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_447 (Nat.beq j 447)) (Bool.rec (motive := fun _ => ℕ) 0 BK_448 (Nat.beq j 448)) (Nat.ble 448 j)
def BKs429_433 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs429_431 j) (BKs431_433 j) (Nat.ble 447 j)
def BKs425_433 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs425_429 j) (BKs429_433 j) (Nat.ble 445 j)
def BKs417_433 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs417_425 j) (BKs425_433 j) (Nat.ble 441 j)
def BKs402_433 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs402_417 j) (BKs417_433 j) (Nat.ble 433 j)
def BKs371_433 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs371_402 j) (BKs402_433 j) (Nat.ble 418 j)
def BKs434_436 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_450 (Nat.beq j 450)) (Bool.rec (motive := fun _ => ℕ) 0 BK_451 (Nat.beq j 451)) (Nat.ble 451 j)
def BKs433_436 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_449 (Nat.beq j 449)) (BKs434_436 j) (Nat.ble 450 j)
def BKs436_438 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_452 (Nat.beq j 452)) (Bool.rec (motive := fun _ => ℕ) 0 BK_453 (Nat.beq j 453)) (Nat.ble 453 j)
def BKs438_440 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_454 (Nat.beq j 454)) (Bool.rec (motive := fun _ => ℕ) 0 BK_455 (Nat.beq j 455)) (Nat.ble 455 j)
def BKs436_440 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs436_438 j) (BKs438_440 j) (Nat.ble 454 j)
def BKs433_440 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs433_436 j) (BKs436_440 j) (Nat.ble 452 j)
def BKs440_442 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_456 (Nat.beq j 456)) (Bool.rec (motive := fun _ => ℕ) 0 BK_457 (Nat.beq j 457)) (Nat.ble 457 j)
def BKs442_444 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_458 (Nat.beq j 458)) (Bool.rec (motive := fun _ => ℕ) 0 BK_459 (Nat.beq j 459)) (Nat.ble 459 j)
def BKs440_444 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs440_442 j) (BKs442_444 j) (Nat.ble 458 j)
def BKs444_446 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_460 (Nat.beq j 460)) (Bool.rec (motive := fun _ => ℕ) 0 BK_461 (Nat.beq j 461)) (Nat.ble 461 j)
def BKs446_448 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_462 (Nat.beq j 462)) (Bool.rec (motive := fun _ => ℕ) 0 BK_463 (Nat.beq j 463)) (Nat.ble 463 j)
def BKs444_448 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs444_446 j) (BKs446_448 j) (Nat.ble 462 j)
def BKs440_448 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs440_444 j) (BKs444_448 j) (Nat.ble 460 j)
def BKs433_448 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs433_440 j) (BKs440_448 j) (Nat.ble 456 j)
def BKs448_450 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_464 (Nat.beq j 464)) (Bool.rec (motive := fun _ => ℕ) 0 BK_465 (Nat.beq j 465)) (Nat.ble 465 j)
def BKs450_452 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_466 (Nat.beq j 466)) (Bool.rec (motive := fun _ => ℕ) 0 BK_467 (Nat.beq j 467)) (Nat.ble 467 j)
def BKs448_452 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs448_450 j) (BKs450_452 j) (Nat.ble 466 j)
def BKs452_454 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_468 (Nat.beq j 468)) (Bool.rec (motive := fun _ => ℕ) 0 BK_469 (Nat.beq j 469)) (Nat.ble 469 j)
def BKs454_456 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_470 (Nat.beq j 470)) (Bool.rec (motive := fun _ => ℕ) 0 BK_471 (Nat.beq j 471)) (Nat.ble 471 j)
def BKs452_456 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs452_454 j) (BKs454_456 j) (Nat.ble 470 j)
def BKs448_456 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs448_452 j) (BKs452_456 j) (Nat.ble 468 j)
def BKs456_458 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_472 (Nat.beq j 472)) (Bool.rec (motive := fun _ => ℕ) 0 BK_473 (Nat.beq j 473)) (Nat.ble 473 j)
def BKs458_460 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_474 (Nat.beq j 474)) (Bool.rec (motive := fun _ => ℕ) 0 BK_475 (Nat.beq j 475)) (Nat.ble 475 j)
def BKs456_460 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs456_458 j) (BKs458_460 j) (Nat.ble 474 j)
def BKs460_462 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_476 (Nat.beq j 476)) (Bool.rec (motive := fun _ => ℕ) 0 BK_477 (Nat.beq j 477)) (Nat.ble 477 j)
def BKs462_464 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_478 (Nat.beq j 478)) (Bool.rec (motive := fun _ => ℕ) 0 BK_479 (Nat.beq j 479)) (Nat.ble 479 j)
def BKs460_464 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs460_462 j) (BKs462_464 j) (Nat.ble 478 j)
def BKs456_464 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs456_460 j) (BKs460_464 j) (Nat.ble 476 j)
def BKs448_464 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs448_456 j) (BKs456_464 j) (Nat.ble 472 j)
def BKs433_464 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs433_448 j) (BKs448_464 j) (Nat.ble 464 j)
def BKs465_467 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_481 (Nat.beq j 481)) (Bool.rec (motive := fun _ => ℕ) 0 BK_482 (Nat.beq j 482)) (Nat.ble 482 j)
def BKs464_467 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_480 (Nat.beq j 480)) (BKs465_467 j) (Nat.ble 481 j)
def BKs467_469 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_483 (Nat.beq j 483)) (Bool.rec (motive := fun _ => ℕ) 0 BK_484 (Nat.beq j 484)) (Nat.ble 484 j)
def BKs469_471 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_485 (Nat.beq j 485)) (Bool.rec (motive := fun _ => ℕ) 0 BK_486 (Nat.beq j 486)) (Nat.ble 486 j)
def BKs467_471 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs467_469 j) (BKs469_471 j) (Nat.ble 485 j)
def BKs464_471 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs464_467 j) (BKs467_471 j) (Nat.ble 483 j)
def BKs471_473 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_487 (Nat.beq j 487)) (Bool.rec (motive := fun _ => ℕ) 0 BK_488 (Nat.beq j 488)) (Nat.ble 488 j)
def BKs473_475 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_489 (Nat.beq j 489)) (Bool.rec (motive := fun _ => ℕ) 0 BK_490 (Nat.beq j 490)) (Nat.ble 490 j)
def BKs471_475 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs471_473 j) (BKs473_475 j) (Nat.ble 489 j)
def BKs475_477 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_491 (Nat.beq j 491)) (Bool.rec (motive := fun _ => ℕ) 0 BK_492 (Nat.beq j 492)) (Nat.ble 492 j)
def BKs477_479 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_493 (Nat.beq j 493)) (Bool.rec (motive := fun _ => ℕ) 0 BK_494 (Nat.beq j 494)) (Nat.ble 494 j)
def BKs475_479 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs475_477 j) (BKs477_479 j) (Nat.ble 493 j)
def BKs471_479 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs471_475 j) (BKs475_479 j) (Nat.ble 491 j)
def BKs464_479 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs464_471 j) (BKs471_479 j) (Nat.ble 487 j)
def BKs479_481 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_495 (Nat.beq j 495)) (Bool.rec (motive := fun _ => ℕ) 0 BK_496 (Nat.beq j 496)) (Nat.ble 496 j)
def BKs481_483 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_497 (Nat.beq j 497)) (Bool.rec (motive := fun _ => ℕ) 0 BK_498 (Nat.beq j 498)) (Nat.ble 498 j)
def BKs479_483 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs479_481 j) (BKs481_483 j) (Nat.ble 497 j)
def BKs483_485 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_499 (Nat.beq j 499)) (Bool.rec (motive := fun _ => ℕ) 0 BK_500 (Nat.beq j 500)) (Nat.ble 500 j)
def BKs485_487 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_501 (Nat.beq j 501)) (Bool.rec (motive := fun _ => ℕ) 0 BK_502 (Nat.beq j 502)) (Nat.ble 502 j)
def BKs483_487 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs483_485 j) (BKs485_487 j) (Nat.ble 501 j)
def BKs479_487 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs479_483 j) (BKs483_487 j) (Nat.ble 499 j)
def BKs487_489 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_503 (Nat.beq j 503)) (Bool.rec (motive := fun _ => ℕ) 0 BK_504 (Nat.beq j 504)) (Nat.ble 504 j)
def BKs489_491 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_505 (Nat.beq j 505)) (Bool.rec (motive := fun _ => ℕ) 0 BK_506 (Nat.beq j 506)) (Nat.ble 506 j)
def BKs487_491 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs487_489 j) (BKs489_491 j) (Nat.ble 505 j)
def BKs491_493 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_507 (Nat.beq j 507)) (Bool.rec (motive := fun _ => ℕ) 0 BK_508 (Nat.beq j 508)) (Nat.ble 508 j)
def BKs493_495 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_509 (Nat.beq j 509)) (Bool.rec (motive := fun _ => ℕ) 0 BK_510 (Nat.beq j 510)) (Nat.ble 510 j)
def BKs491_495 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs491_493 j) (BKs493_495 j) (Nat.ble 509 j)
def BKs487_495 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs487_491 j) (BKs491_495 j) (Nat.ble 507 j)
def BKs479_495 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs479_487 j) (BKs487_495 j) (Nat.ble 503 j)
def BKs464_495 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs464_479 j) (BKs479_495 j) (Nat.ble 495 j)
def BKs433_495 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs433_464 j) (BKs464_495 j) (Nat.ble 480 j)
def BKs371_495 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs371_433 j) (BKs433_495 j) (Nat.ble 449 j)
def BKs247_495 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs247_371 j) (BKs371_495 j) (Nat.ble 387 j)
def BKs0_495 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs0_247 j) (BKs247_495 j) (Nat.ble 263 j)
def BK (j : ℕ) : ℕ := (BKs0_495 j)

theorem top_ok : Pyr.topOk TOP BK = true := by decide +kernel

theorem blk_0 : Pyr.allFrom 0 34 (fun j => Pyr.blockOk (BK j) j) = true := by decide +kernel
theorem blk_1 : Pyr.allFrom 34 30 (fun j => Pyr.blockOk (BK j) j) = true := by decide +kernel
theorem blk_2 : Pyr.allFrom 64 5 (fun j => Pyr.blockOk (BK j) j) = true := by decide +kernel
theorem blk_3 : Pyr.allFrom 69 28 (fun j => Pyr.blockOk (BK j) j) = true := by decide +kernel
theorem blk_4 : Pyr.allFrom 97 26 (fun j => Pyr.blockOk (BK j) j) = true := by decide +kernel
theorem blk_5 : Pyr.allFrom 123 7 (fun j => Pyr.blockOk (BK j) j) = true := by decide +kernel
theorem blk_6 : Pyr.allFrom 130 30 (fun j => Pyr.blockOk (BK j) j) = true := by decide +kernel
theorem blk_7 : Pyr.allFrom 160 31 (fun j => Pyr.blockOk (BK j) j) = true := by decide +kernel
theorem blk_8 : Pyr.allFrom 191 12 (fun j => Pyr.blockOk (BK j) j) = true := by decide +kernel
theorem blk_9 : Pyr.allFrom 203 43 (fun j => Pyr.blockOk (BK j) j) = true := by decide +kernel
theorem blk_10 : Pyr.allFrom 246 46 (fun j => Pyr.blockOk (BK j) j) = true := by decide +kernel
theorem blk_11 : Pyr.allFrom 292 220 (fun j => Pyr.blockOk (BK j) j) = true := by decide +kernel
theorem blk_all : Pyr.allFrom 0 512 (fun j => Pyr.blockOk (BK j) j) = true := by
  have h := (Pyr.allFrom_add (Pyr.allFrom_add (Pyr.allFrom_add (Pyr.allFrom_add (Pyr.allFrom_add (Pyr.allFrom_add (Pyr.allFrom_add (Pyr.allFrom_add (Pyr.allFrom_add (Pyr.allFrom_add (Pyr.allFrom_add blk_0 blk_1) blk_2) blk_3) blk_4) blk_5) blk_6) blk_7) blk_8) blk_9) blk_10) blk_11)
  exact h
theorem lbS : Pyr.LBSound TOP BK := Pyr.lb_sound (Pyr.blocks_of blk_all) top_ok

def cover0 : List (ℕ × ℕ × Bool) := [
  (16384, 24576, true),
  (24576, 28672, true),
  (28672, 29696, true),
  (29696, 30208, true),
  (30208, 30464, true),
  (30464, 30592, true),
  (30592, 30720, true),
  (30720, 40448, false),
  (40448, 40960, true),
  (40960, 43008, true),
  (43008, 45056, true),
  (45056, 49152, true),
  (49152, 53248, true),
  (53248, 55296, true),
  (55296, 56320, true),
  (56320, 56832, true),
  (56832, 57344, true),
  (57344, 466944, false)]
theorem cover0_ok : SixW25P.coverCheck 25326800 (SC / 2) 466944 cover0 = true := by decide +kernel

def cover1 : List (ℕ × ℕ × Bool) := [
  (16384, 24576, true),
  (24576, 28672, true),
  (28672, 30720, true),
  (30720, 31232, true),
  (31232, 38400, false),
  (38400, 38656, true),
  (38656, 38912, true),
  (38912, 40960, true),
  (40960, 49152, true),
  (49152, 57344, true),
  (57344, 59392, true),
  (59392, 59904, true),
  (59904, 75264, false),
  (75264, 75776, true),
  (75776, 77824, true),
  (77824, 81920, true),
  (81920, 86016, true),
  (86016, 87040, true),
  (87040, 87552, true),
  (87552, 88064, true),
  (88064, 278528, false)]
theorem cover1_ok : SixW25P.coverCheck 48244400 (SC / 2) 278528 cover1 = true := by decide +kernel

def cover2 : List (ℕ × ℕ × Bool) := [
  (16384, 24576, true),
  (24576, 28672, true),
  (28672, 30720, true),
  (30720, 31744, true),
  (31744, 38400, false),
  (38400, 38912, true),
  (38912, 40960, true),
  (40960, 49152, true),
  (49152, 57344, true),
  (57344, 59392, true),
  (59392, 59904, true),
  (59904, 60160, true),
  (60160, 60288, true),
  (60288, 60416, true),
  (60416, 74752, false),
  (74752, 75776, true),
  (75776, 77824, true),
  (77824, 81920, true),
  (81920, 86016, true),
  (86016, 88064, true),
  (88064, 88576, true),
  (88576, 253952, false)]
theorem cover2_ok : SixW25P.coverCheck 52857300 (SC / 2) 253952 cover2 = true := by decide +kernel

def cover3 : List (ℕ × ℕ × Bool) := [
  (16384, 24576, true),
  (24576, 28672, true),
  (28672, 30720, true),
  (30720, 31232, true),
  (31232, 38400, false),
  (38400, 38656, true),
  (38656, 38912, true),
  (38912, 40960, true),
  (40960, 49152, true),
  (49152, 57344, true),
  (57344, 59392, true),
  (59392, 59904, true),
  (59904, 75264, false),
  (75264, 75776, true),
  (75776, 77824, true),
  (77824, 81920, true),
  (81920, 86016, true),
  (86016, 87040, true),
  (87040, 87552, true),
  (87552, 88064, true),
  (88064, 278528, false)]
theorem cover3_ok : SixW25P.coverCheck 48244400 (SC / 2) 278528 cover3 = true := by decide +kernel

def cover4 : List (ℕ × ℕ × Bool) := [
  (16384, 24576, true),
  (24576, 28672, true),
  (28672, 29696, true),
  (29696, 30208, true),
  (30208, 30464, true),
  (30464, 30592, true),
  (30592, 30720, true),
  (30720, 40448, false),
  (40448, 40960, true),
  (40960, 43008, true),
  (43008, 45056, true),
  (45056, 49152, true),
  (49152, 53248, true),
  (53248, 55296, true),
  (55296, 56320, true),
  (56320, 56832, true),
  (56832, 57344, true),
  (57344, 466944, false)]
theorem cover4_ok : SixW25P.coverCheck 25326800 (SC / 2) 466944 cover4 = true := by decide +kernel

theorem wk0 : SixW25P.Covered 30720 40448 31232 38400 31744 38400 31232 38400 30720 40448 :=
  SixW25P.covered_of_walk lbS 2856832171680241926645274536812049670077866964640394657543680470856261551348291038467628025196263686170400639479045306684750047727448339889453330405253922145551131629777807544443452434150298509507876816492643411571663763871872750596499425866168965658634991788267270194038131915656430364476619917101203715790445305172264252379189505641989181173304614265855383708947553423268467974348492788920377591937250569531630165066747252036488932682177672182716244049881807222431819758413406039478187324696108611928362626790309409414866823802713201874396772304893224557058537942294314027867099728351005719345620346675746 22 30720 40448 31232 38400 31744 38400 31232 38400 30720 40448 2022 (by decide +kernel) (by decide)
theorem wk1 : SixW25P.Covered 30720 40448 31232 38400 31744 38400 31232 38400 57344 466944 :=
  SixW25P.covered_of_walk lbS 3947756050523836245427366033463311226286033940095104705201094837864761683494000677786828006271482719705992852490553413918624173723193650823758040023670173884840596905146740107640880020055886555335039307144944954793967084550966648440289124177365004035781179738208961670465929856899254349906986204771238349220916416543279619051353337312151618096250996265533394330792897547760329398414070205828781338651044763749263325171588637306587284339912503302734583917852630982939048975009759699581907532971868353915790999958282147957959379417519544579956887135445887915059104197085279885081672644062500271438926400661804416743236390227913566841476863398959156593506230612505642104752449566509062223946966883920505818188967015409096338351658366935972322302680073756591531798888343221267881535543691438550337601597533145896356006084855873309015221959102392194341342912388975234651899087916636253486673942371840825088091122511669563765854851328128690698107200801264910469722063341503306190515215001631117330677914398119758187038362211040045727393419364917631509171507351986406246152759136142684095272843000045334550552574963440381066678941551898027411927480398954630397797464281695784149594564084408693764747584945746142624414941010746974376403143408476350466345330500750668019693547499869648380270852318375679818634005984875500418031557583525537616904848459782340320216564863901532553243940096422929670583374433136975567667979700203722181776730706401857206064093901069591022406539349340222471970917903381124201366471812518381263052446349415061949944117417611322937258026636148594059186503410403094092895819987512022824846515748918604463241011428227687331463662808110195854456850780973781735504322158373187676693608863086383300022503220571629767809915657666495683226273211997279178774982854989099783371046936117513670171540433268385461748801379585623749256628727359729083922158519726125630151642585667994068122970259111530018865449698276146 28 30720 40448 31232 38400 31744 38400 31232 38400 57344 466944 6402 (by decide +kernel) (by decide)
theorem wk2 : SixW25P.Covered 30720 40448 31232 38400 31744 38400 59904 75264 30720 40448 :=
  SixW25P.covered_of_walk lbS 81813430875678885824888405719442662954555396578370873258251088270228499719393577136711320807244229720189078341196020212079166039395201634379045487743472957969891357238212153282004385718850010557608156205390056007434543639950143761859810299622099110559780404708549817001472244120392782447693396241758201401855787291773687098159429085174010724317117371457385877905878916993746593728667120967372456410267245634005195414643281225723712939362038060913538858400991335617634222057274392396250472616257938377129503847040725597419296460199625794130036432056080965573128918801968687888525282156538419282924704134049566849645079339721930791424601291498724257878321975727807475113838388597139518451403215790880273898786085179557308585324876887392750933378180571309608305320777895775968192081010330007076288845731230052905583657472981103667868209537131932554842625854723641826066852951457546536978943898975278072617272923078493450043409099363942831672311403057131100247054418280597627272354465228820318364788152197169093788365919482084348627287628689220288790700877295854876264872611233514573475007046555645719269190089869985273792566946465729106179516215112367829058177217468068031842656789891584438637285152336418771755080154908289238030683835348514891454648416068804800216801922604533281981229546251968029452657330189749656749710627379043462234515199505217021490360092612284705827513741632772712912245969120791468440361210047345663813787242240719082630952868459111715036729243410903148277766459122074040891478770656310632597070021632133813050190206496928927769577587597172009211982639766408327566915129176760794843950210297282174621739651532966520498825036877841711216959328775073135801886566446789289715279976603329412632969413143487896553996791827880677609524005470947121230072425048035363016878939804099621152685608740142951746259999027049645610639746287115088487436640693126388201260614041746321411698508848695010448693485952267649011460061426402328100152923564910687109383920898535939024614475298163286640283021492170610273401089355135667970804064156294842434068280311188685771369731360851059772222224542262092934840156407359972710648044151769894448306081802888116436529559089822784421059270592592395887909653124214622835247986450453892827132450 27 30720 40448 31232 38400 31744 38400 59904 75264 30720 40448 7447 (by decide +kernel) (by decide)
theorem wk3 : SixW25P.Covered 30720 40448 31232 38400 31744 38400 59904 75264 57344 466944 :=
  SixW25P.covered_of_walk lbS 143226827786798431343414023026193118874635812372610856495489598013789034513644546192677156290547582307797842851560275315901908920895228400761175401762230126076689384706658770719754120276597007708624317429033810274952645432118615566996145617767447129866750766295621657893973680936037646083536203735855161364494885315930883795995385379390247154259407721191682190635861670450888231453793783500775891096404259548353170101563252883862993322802686538410301466140664141292269528326545175516987645138726953155517449991153310132421324189629002885909475158163547531936573885410349168502841680394493081092720255001492405211121610012459934610473814112070257177125478959442408663614296853564208098283608062249295757408002875255016868187860288875026386761029528726289020413946879155462238444607040351619413119341869880040446505703182445297064013304456553017425099263620454625790740208177767896362255691592849484889757412755364426361052364130518133101368291742104347224029926450842795325822615403784864593895032507532684882925416428016087923848307362528224627973551965759942762073850937852064386112929359186779728102922832811613554692935823460057935884886705735211811818806560026174255404552660654830329951643052315367660948509429172662026180425801839242950431823355568961021800782682003565822202164857734625354192147228059470897209516694344626920974809446829894270845951462290506328662279932573182974432972870000004731469654152894156220865289983382652475299141847733427551668342909144682765763008480152731740265159151565462010910235602233688396421389088058722542701894002331204279730254769054618275843421814514323865319045871879641155021259592240688011824894565188928379783254644523107393431991728827105277848370974226621268676532797807528013287508932790287006348643585063094287816436088020256015952585097195759981055711906797593590343402587522699381498044005277141444559404921545545393552284729769117696925461172850707450994588052789576375233031394529893263602142140046994618235756654613305814437300398565019501235516964135230248829798318359476347299156317075663744383101481926817665237015801855308120870666858646198717899384459091261147152825043040409340894335711653559230142912180112689555985802054839003956648660174886418403415087154100745208667291478654751098915594062845551216427966129310315830959316873184030859185065859830512777666652979065952339125165932821218704040431950636149868593481344172326493303585860436981581215070694339424364372874876006004408515248732691997296634202467445331143263528437632041888390934977896956293797545891576088680364912093730866408395674712029947687791171245932573545112290421186953533375117232649010 32 30720 40448 31232 38400 31744 38400 59904 75264 57344 466944 8722 (by decide +kernel) (by decide)
theorem wk4 : SixW25P.Covered 30720 40448 31232 38400 31744 38400 88064 278528 30720 40448 :=
  SixW25P.covered_of_walk lbS 6145499380050417277779196010085452728125906620350184269607589817770094633889687318243392471277303783232918721424236932133244101514305422536962605135821582102798604052821827427836119832002426192120327751010451163992073828359488310614467763310672946409464946912073125080801062719872024892817518485901163498347464774702508556859541686717588274222802111758963428238005705444658777285690649778755420418374494214946337030235851347641462804637517993361018790967697805604317233870534976977083514254271240241013795058974328136353889112282427006903269481636257743202923058235940911628531148667667221070330216670925206597428338507097466289188609698524073737919736031056152412098235289541556207681563575031291701461314089155669094857612466497223304295263703501915439864581884645491074424613540641429154494000902484974397722016545852592032924033847291303760944294572540170093486819913454 29 30720 40448 31232 38400 31744 38400 88064 278528 30720 40448 2912 (by decide +kernel) (by decide)
theorem wk5 : SixW25P.Covered 30720 40448 31232 38400 31744 38400 88064 278528 57344 466944 :=
  SixW25P.covered_of_walk lbS 114707780836825919701188950060455858202355886345674676623420118544140124036881345133576275279430640831338909245298059018738761813230356506918132404729734063315353896986669954517027972512906913006956745405173893664091965368788525884581581371824135331057508403768517156544804711387505885100367807029558930800891692982710237454295279107084035794943169514106969005040205947247287648997130078335641119528566615665653036433643899507526607641569025182536531022315521786693762353308248996797378523999468375601484611628430032239289111929515143392320882298986635398646593739714342510893696369907173799572323946024238510834 30 30720 40448 31232 38400 31744 38400 88064 278528 57344 466944 2042 (by decide +kernel) (by decide)
theorem wk6 : SixW25P.Covered 30720 40448 31232 38400 60416 74752 31232 38400 30720 40448 :=
  SixW25P.covered_of_walk lbS 47532769581851826873702474635192421812488692045896221948156881106573338474207137952832173861299146214448883037511299084763596858896953412175739318683166777829933347697147815230390110143873645341450054475995003618362193021273271745706641497623428789749102096635450701802592003102444436574713811837762427553583465449939830241544235068538334194288839586161732122289022303490815395420952967884559073175162346299762153183400558775770653397471718358173032870352535848273917348072136003072348276773955478522722537103066853346733421475034632850466750958099949146547680206418762683719009830788197919125761056588749362151702479643057921353652632675821874908188085012067588879864715994715116541206075121271905411275127354145620586987693633688309160367855484264869544215523646972746731296618214214393386368555236974152099979279194874414372604215518320098043771653242479304027920638805911882019484878311210157894111818419570573456034664129283312984272193993129648810179572551733940851968842888883020559241384396383990875834925465015320013181663451715019191430993672637504826134794803748757385950549820675267754382655963753493485718688289044328224781405948302257371980277775509721765705453661884878242175306293619082619857837471868245216516014833678671000474572820892066552645251985707428329429718863020178374560434729719971057494954964115510197453114350363149845060197981984435923493725654515531834285245194192932722255012391858823184831451988055456920710972772008486874793885809463335009164026147239856193723452811294631789416839578675757311584644355350592356481237691983146304332417705424102309532114688907759736226795936390035501490199452091603360954233913561188831271723916583722667167392004358904424053415693649786104550402927952770410922688708671567592948134574012980467692028499379214195796075359372467098126827532477970011978032006559946150145620766718229233930671886939612933094578899115157976195935363630171048591640146819719073866345981077000310309014969217917117378700796102490923929368694846737339254213022430842211141042729925466326401103469557131276746268994172798181774937429774037321852695566349363300169948080761464402503872660263817534129998381163664023428089930079468537127018250024771430200593776647807537167955015722367467087994321935137450865899650003617050875299348414896410425053003936306290219154913127300889145513635320594187455127990693694386868619133621884325864170702259580475991921490250705553998572686200878510057715438182371832995969217036149435038495334196969657337562512267815647447057987610459361130308257455809691438385728468064337770342232459887561749488428572406498895277007040395634406322318621297322 28 30720 40448 31232 38400 60416 74752 31232 38400 30720 40448 8732 (by decide +kernel) (by decide)
theorem wk7 : SixW25P.Covered 30720 40448 31232 38400 60416 74752 31232 38400 57344 82944 :=
  SixW25P.covered_of_walk lbS 694884445096655169534647657231653683893508760270365501836126538948300920891611185281776787490035577483547517186508524708630391323249230806149350491195063277274546262445090687338308606398705739788605671816226588624591532035662768228007016482365608120147002571052926512927342391046616010534725656642288885826533683108094650809103439439524346249694562161654190891931430975817978721805236739138479604692172808149488455128816509555213858279942339497784554738713319811151284177913048728764786065475043415383565033099370547131394405020806493096392782816713656229148819911341559531230993929657261356450847437531425373464595692111336673498210584368963526872695708010649501032736216340611334892956099226534907186917147941356467436563154429506153169531811961542930994440730684759012817415782488860971326433330586305127162577399893613091169464434611870172178080666665435561207776987460326887814563631143323050619921228032522671563964378962894096466078573140568259495162315163778283984067774437780767347874688230914833621879844174025085838316333584058118049639568989023150854985704390538302020082761338661005040478897884876316060773320256052506232357083194239090896732536744923180635867353313282818685920928491093071226282320848484153025497550099126537536920307912758275161289050606733506944218592992469858170812372122942582016137273243827105667593327595798050034961973491922062156088829493722359463294006662019885278584856336984271584899028613219585603436137030720202513520557177419867605361411378155805990197724453455591456587205111390567067080133980412100068440265644955594562213907086384964578490730381528155457160203609256384375489410129282030029278514704531947865831820754302766690392163591745396213998620967602716690429788418956545431955606745623446367903517548271514874919412160263695510495900426110787500568386183281964280322843250288926924225714442356075537787407286986217576092935571746973331482814295764578467088713437656162993175002706094522532144944565089202480317785488330074111531094222945416683379078820978171945697852689066204786880303383953512719603106582918573423913558013821752039748596446741557090855674504046690897721154118150513691565564838107492934363855285603611890486899170435362560218688482822214329921380698005032284697530592849176133753028396202862086795744395555244620415541314960320155208229673795389627634968465814841931581568075811596855577269084235798807939303237752051694614528999233792536636570860523567965673328081655594083527440674887855544074878747111460363293419779777324313340341164921628959572702372953686695227411214123445503542554464914418417717708995956393726111419330689875682818524727155465496699824058972438305348479745580464920885525307765599036209194437136511711956637176810098689972406481233720307972190133857342492960250268176284974846752440791083426558146974969954967469940877960869557144380335586954740626277751374598690283339255656893270837204011142624554904741594331710747689744819179594822960782567950732942300552395119554294863844242191181052478292354449965288310870659277418990792542671568461817032231273280946979074697849352855110904266172709400972415368445016193782744563315573970031539830023699585618030413728211456108717152905484685493655223210260641720432657078770036855785727311384811327928358270498935564081756967223281952254249247193984694863420027868323561534514496598391449458576607939109938407271284044255232023710772776961600923821697262459085823953417468943324078448021077452172804445689531634499062346745207016802900109857009378349039674459101093688269949045611688155811973155417973204277465538648277141218348574233160365570006742060804543983330125189230669940620804705178101670067416384015019931484472098521348706070905984828403142930665874767861210464720973681064709280001881621027796478172062822092131148390725565693945902077575618299467347546972239846993871321191761768566896781992888853237503881471389982717114389047050592812371498671219703334604065602828564035697371779341609254122637247065031622652386018291554931362701011243590490821062402195010933624061918763320871996375105286571579530151578307405048970706046886886196155448122559594517818260449942427696285443218587409651269891131613135103086899021877119790977975135618318144245579787396677578463976431850650706828446122270728089652917585468910529054684988731462941328107847583025919004914824500770055015478542043706581587003867466768590320248622373238064853205642177283932761740843604105970937806496606988495142923919598803328360002756922651804980851894799212687543323891750558200564619388838836980887778119698000219240001171741792797227908541508099091142295223370596118328426072411436577705297861189233697379811396097538227387684923705753057086471355102750642598799426200580289672996040391948496937031651636380737834658172469852092470093749683806089269383030138587929256188483723120592949243259772032533929311664422478757312724345900361807350828744578314536775902883644449139629193936952617900425337641346950931860937781195097705054360518754437858168299997114189071202280148255263030237668250389522906963520055520252108734315138230874830089656791937726796273322515918019790172782860122956364571691068085091457280056077877240305305554144327150194440322727268968632001610889838582688307684802748371324033418796372148014044766715940138025678673134841957318898982596141807783889189021773679426558705024474425740710816477116425375274248635673415107402074952902101362189336040032782410493626803695056570650463270843741941105255107860742164330621949292648515883114378538145603608850310677306039169366703776735924577891366826419414045950324534592835778073394 32 30720 40448 31232 38400 60416 74752 31232 38400 57344 82944 18522 (by decide +kernel) (by decide)
theorem wk8 : SixW25P.Covered 30720 40448 31232 38400 60416 74752 31232 38400 82944 108544 :=
  SixW25P.covered_of_walk lbS 18019941351952028376107569666498531908378315938358906978773156717953988370319773666070247688675080444431447837530931656790796253261496978697127926565411761570705486394538739277098206190399955544760709883007802653816543185262175965728207413520627090053727263841588292208443175903230620804129388579031705456560019773942331045606789280744092856609196720766843969777768360427226368152730489966058918947485883094938030635162107883163523808806365664713021773555552939577148142456573101857312720626728314492103739094661386349003067756337505919394742318141114555956263287565409641217832312505388098865403092237846285690871586261074675560517827632478398514460479008637964451235522098495904349847017143181316149569777715881487867775507349964587398113960590436139880873998564588655716541026082490916894872379196105190332711282642069268836213174365830913634979020471828586631022429955203387512883832802838587898271975543340315294785828066275071071506681206904509478127096023922566874090099975590779275428371511925739850184213667851915992642957264182851268972599194703279195973070844841895650737021599818325594570408722650923460941684687321501326266112856120733277677243023254928381674980456211752590689017335277900391730 27 30720 40448 31232 38400 60416 74752 31232 38400 82944 108544 4017 (by decide +kernel) (by decide)
theorem wk9 : SixW25P.Covered 30720 40448 31232 38400 60416 74752 31232 38400 108544 159744 :=
  SixW25P.covered_of_walk lbS 13445734661730612144802286841077878028256610132517491474909481287750880063906803282125341496288527478713983762488004206977958791723663582591010818331777423299925391204924671385624118245363464247829925685663067414053743293069348204112908718754312142075392476179044462682149109916105973084793087505699204721631079425351665442485632199294156691543815385385820625986866 23 30720 40448 31232 38400 60416 74752 31232 38400 108544 159744 1217 (by decide +kernel) (by decide)
theorem wk10 : SixW25P.Covered 30720 40448 31232 38400 60416 74752 31232 38400 159744 262144 :=
  SixW25P.covered_of_walk lbS 653665550395606893963883960213213540846576674933006555911692798319824600735590882283047032351011634 20 30720 40448 31232 38400 60416 74752 31232 38400 159744 262144 332 (by decide +kernel) (by decide)
theorem wk11 : SixW25P.Covered 30720 40448 31232 38400 60416 74752 31232 38400 262144 466944 :=
  SixW25P.covered_of_walk lbS 0 2 30720 40448 31232 38400 60416 74752 31232 38400 262144 466944 2 (by decide +kernel) (by decide)
theorem wk12 : SixW25P.Covered 30720 40448 31232 38400 60416 74752 59904 75264 30720 40448 :=
  SixW25P.covered_of_walk lbS 5322841228781091538561121648320067485878887591346477482430735044225083696398684494417395930431943162224138110134602690188728071807518094180658098728697793739596384967047875229470680157301298186543333484846779891409924384977816513441850701602726181882158988333107312744479843450137913693089995593090278276267293513102966050991649786317540453443315764684961616666441462874648743703563526393140369811228256828728996043806766030458292370566234254353732706343827156370794025070166365629458670765817976460500007003313716138083919630348720613824498987517028392130158047547302033913587280265692491944588592315255777663038195780419038778191256713509291181714918745085215336555009512252188655299830314296714103596183926165732089765016664365734453153691905855157115155075877243306034031148645872870048628142501676304236284079822115024147072787942650197852585539321180934298575591792297503454889009010596221669160694845346723587950661964242327856378189943628349337165814552585887120585817300787788148793328785387178105154729880472180646169793806264668649868396041807429261179748345677457594974841376118828279133039120410194995454035918172599191399473662939288485212065596051273134287340270391423641828226823360518534823119854042968128317287130384953486803746736567540306290669235191044183549068234688135094768282755285659991081572945185656092286446870804578966193376914011575684869881364388082746026111794778445341172991370881836020301323198609547196338003255619730177086098904258976138499390834252980920477055206619940215411311551371880241153862682998498345904957702137196791947860847460685100384795996957504757821111524245258910935849707036930792221999061533647746450961457262047231933471399909900633615978531255320859787252041126534582973812216719936236137024209820147113331846724213608316399337505900425758295463870410203790079104746197659822331786528329115565264850177021762890513188017995966949404886682640552992117854524458992273526885336842381096352044314994713225820046784981830957452550817934421810476295342964166934773259076185480329370900887626929302764847507107415292669438046572040143543546033738771411893493498404741970898094408017314099217387459763055785995917330981634992826865307036812382653269297380765098443979311970031861974655492759634586317800787474247850408417329147562026599433247893617620256893164866761168566103569724318151828909334251902133617087130003823061795386300693322538436960941796614647283364867154194824446125783132451009593728833188093264621214535679404155616237558541724717894935859734174157237285475322891707572295894034040481936887130046088001501293959339704502719481886774209030114231544785161505304775216338477279096745828813941850236332414756554580842948870030691926218086886356005337604508805429789847747418954859615558157117425306546473851812075572197957002774963455241543832153835275464453220070094424471389534257017061200071224057286988305312234006626911262063182518178621460588346819645743866015542646676975099473979192624398439620477038103578562533889544990559019013182317413107573492843695068520024788125861981402983014607243067288180049675909767138406669344217887529283966093024734036578533603447157759053034922911160520021139889322794456476315204899360185495628153384605478252310501230166165027451198433584645650436201915509100025540957427203242222574929709715124481142749339114447670621795207679356962517400083196256014779184747289901128250233569562207412217848663232695153646336293738403909653085525763018807773855338434795540022041498013071418721645827614170438727069244476461865878995920412599452378600518297518057116118995281741632877436591887598374247427325453186825240394354149480824058243029133239863738670211938424369974184574656718330423011519614636987341296470109085508051711647337221113289356436820150104919815448816279858744954760058096369615303437629561059775506588499028823066176908335051040754169902793126181760232145570739957880289977917624514592654682234954838132095339981374996906636578159986903841636608947942968703445994486147114213067385142698296461229134326024137817309798711364965244772966039081076818249705438568225469059150433254612278059429416946316755615297686358408806552879392439392142406909325184288114003377339137964245185705933029524877284444680811712217859148339530712502649588039325788661315543722 31 30720 40448 31232 38400 60416 74752 59904 75264 30720 40448 14202 (by decide +kernel) (by decide)
theorem wk13 : SixW25P.Covered 30720 40448 31232 38400 60416 74752 59904 75264 57344 466944 :=
  SixW25P.covered_of_walk lbS 143982382505502634807133962884485168517408791367941964369626176109961009294699924824937031457499483809121792712794869088484153101734507957508713826664225107569301046048403642782743685449141048844526978963786795660699481534454338380526798012111162275410090196684862293745024726426425646387747843065645991528058952565770318943226918414416349743468584416205935020482363531583359531366292985448511578115652280662589350636949190802669254564047774594831710846797993796582078652436024924912438326440599322562077382407292731996489086181662200480618642475375838638681882419267666386723376025908930805649562210240451156121417175919150504990305825176309468095812982690330747051764200934410422936564427811913156847207720186838640171437462242285050103975513685433502867782513295811079557816511908072913047828282565605452778259831444576063902765973969308658391581721783666926585048958006972067332495820815266096364709377622342865077139699611364965386562061071259180719737676326009263430945678519180152191571037955319585753523115003526545575012859032686533149847484489964039439534917143373701577792128352285865497406463060675526947795123209637921735255751540077204454429463870968869729610929759813093726449399360459033304048620537629074390061328745920397282361592105088015285684195178074186858540540776662603326716204284994337753646713071848776436821283685850336999072852026744791789562680952661456331524852660973938006796382023294262233451977704334613578229894719142309727526549143021767125501696379566456150010388389223425975033130502704590058368996848642885233050166250596476662588718800274827692531706358498488755533379418409527259923952696672982602018403122 33 30720 40448 31232 38400 60416 74752 59904 75264 57344 466944 5477 (by decide +kernel) (by decide)
theorem wk14 : SixW25P.Covered 30720 40448 31232 38400 60416 74752 88064 278528 30720 40448 :=
  SixW25P.covered_of_walk lbS 58685846521773510957955551093381713904717761946179239189524723886041953317284661376789844290247225721145535926330028575523620926943132860472753377050383494740309195144763922841690475250041690992757344973991429242493087691766717110361430968911339947412925027306716180206 27 30720 40448 31232 38400 60416 74752 88064 278528 30720 40448 897 (by decide +kernel) (by decide)
theorem wk15 : SixW25P.Covered 30720 40448 31232 38400 60416 74752 88064 278528 57344 466944 :=
  SixW25P.covered_of_walk lbS 20004585390074876873629091462115365808733365842507474326445782399262834811802599261972743779058 24 30720 40448 31232 38400 60416 74752 88064 278528 57344 466944 322 (by decide +kernel) (by decide)
theorem wk16 : SixW25P.Covered 30720 40448 31232 38400 88576 253952 31232 38400 30720 40448 :=
  SixW25P.covered_of_walk lbS 365131730899385941232652423161852982412987929417437328722604738629125794238105325988425812040394955782650034368132715478290832468222688800188878881358985390002437725478686751825699743542711426988219405797318694371432688462023860358990266349885249489494573258567205486168061065134910692549083053229328970083920854790145781110798930085690350231557873164824051844894753611524720419484869678111861322221923206465515272890654646257694590810590379449317684131105537773777226815506350996473122630076361684671701551421402440281109579717082949440767631810025127032225880454588517358599774106818954184609667300460032558976828445484383686449306833222717820784305328036091134773756909896144052447338225559040813942535822298368204764380357977356855048112086811958684447018098804543153067316215918449363278859731456396240356711571987607695285705947500126385709014126230056396211089186225904629587113609526833011647362943186886612419605822972195211263450751859042570384631831827918473921220312181418 29 30720 40448 31232 38400 88576 253952 31232 38400 30720 40448 3272 (by decide +kernel) (by decide)
theorem wk17 : SixW25P.Covered 30720 40448 31232 38400 88576 253952 31232 38400 57344 466944 :=
  SixW25P.covered_of_walk lbS 853204260643805899907169092166151175482860307427737672938680039288036862235875463072117945898146001041809552167746125400679613394571868632679840061977121674024380783466054895519267944289985803526367355756061648903772020616464920332687249898702446202201624059452538677722000339224499485693387855963775513172393333900242665761624850904961859198099785958217332093804762728600270207123813863983638902364465153342874507316453858929684002391091430921078490400191808819066043257515648571545745128721887325597441128684834728018160524075372073325546314882936948199374521140867190680378226789298317778093207591678396739340130918967766982251483953860383201813955013438860279092542556276366069647044479337295517818556760548603746320673903616210539390563012570693612083174423876604718971732632476116217872074225670601422421916454782726260771055625905555703675566312928229404563131138886699517581670992156885091047541955544029430565504081619116536498 33 30720 40448 31232 38400 88576 253952 31232 38400 57344 466944 3127 (by decide +kernel) (by decide)
theorem wk18 : SixW25P.Covered 30720 40448 31232 38400 88576 253952 59904 75264 30720 40448 :=
  SixW25P.covered_of_walk lbS 766275036180851202221629827878395498274936194540506838886284655655051358118079424867860822990940094672355692366411608986536656897878637932956616877967882895285543082340970707327439395172487766600252242408295450543683001156385306480098366815290148242205059754 25 30720 40448 31232 38400 88576 253952 59904 75264 30720 40448 867 (by decide +kernel) (by decide)
theorem wk19 : SixW25P.Covered 30720 40448 31232 38400 88576 253952 59904 75264 57344 466944 :=
  SixW25P.covered_of_walk lbS 18179011236362904442480616038989101310120117244122962878983260148488009710132441778 24 30720 40448 31232 38400 88576 253952 59904 75264 57344 466944 282 (by decide +kernel) (by decide)
theorem wk20 : SixW25P.Covered 30720 40448 31232 38400 88576 253952 88064 278528 30720 40448 :=
  SixW25P.covered_of_walk lbS 64723925485762202438911910391470 18 30720 40448 31232 38400 88576 253952 88064 278528 30720 40448 117 (by decide +kernel) (by decide)
theorem wk21 : SixW25P.Covered 30720 40448 31232 38400 88576 253952 88064 278528 57344 466944 :=
  SixW25P.covered_of_walk lbS 337750636047090 14 30720 40448 31232 38400 88576 253952 88064 278528 57344 466944 62 (by decide +kernel) (by decide)
theorem wk22 : SixW25P.Covered 30720 40448 59904 75264 31744 38400 31232 38400 30720 40448 :=
  SixW25P.covered_of_walk lbS 195861407699780013040586513723657144866689370524948649806651158471665329997097508055054144690523339731660636478980556913717782811962476034587391036868769025006369982518996317676617909440156994057203424044243736191261756653564450583779574705549959226336021725879719898204035454340134599747684968022218313397573248471131086533840374108170573713017575051314457343928850016802551552102316449695368267457031490728509097609969811238865419463014518217307545671127518405920523952006889295474795208909069647420902125142237565353680693596045307148368487131193144659336085081843510173246923319818122994218750554425739267945306914594099456647902968655933807643885991715299626517801788743243792032687409272978159279037261170117182502347471974770521919498167552603380762510461186046442041238781641316534979232424439013960594799659439044121403511212683336654911965411143985292926384865385615568069759162293070199397900304310516597115563238755093249935190046087356629926352335153129108229087193268858077627174583272714858769697891206696787453287758366868275513735658889925004465205107060649671406858228625754427067243184622483135858545100068569223873611813360398248424019746082795106025127142360984853336327782420271743535021875159752357314778797770753117454472964411237484545365365530782532985987460054763634650266868757753192090747826565342350746660474123698215323741906482558167639680592779908878476330585247159987248748915878526133891136525014264930536381749325859060945945710299081164309528288223774365752967516299831096134776701319985360217327837797098452921909491677175788494797820245043295863193985487237972636202536952852651209717103860518978775562197471752107608159381854469338722948489283187068228336785204000613089840594136873912048163618805106469744733091556039620569276896689660896744172692569823660952761545088364192185290164926741597971044257470537040782156979992773324336725255251579168444590563254129668238811735102538647853674079197155346972692569847212419624613384803052270408948277564570251498768058510877490 27 30720 40448 59904 75264 31744 38400 31232 38400 30720 40448 6692 (by decide +kernel) (by decide)
theorem wk23 : SixW25P.Covered 30720 40448 59904 75264 31744 38400 31232 38400 57344 63744 :=
  SixW25P.covered_of_walk lbS 560991309567383960668330684837638249313186392514012135981121518044376162430122731396070822428621680504758154729266410169927937461618420101176108177929033563674480885432360003795576891314618831630081663057037997412933683617247806113635319651668831807262770988776521986891535745737000107826377371162304255821680263499633488076849794168307129762388218482653111922398169129225911132529910128948983484934073098150911840427755154255908059141383862788593806593182975058 26 30720 40448 59904 75264 31744 38400 31232 38400 57344 63744 1542 (by decide +kernel) (by decide)
theorem wk24 : SixW25P.Covered 30720 33152 59904 75264 31744 38400 31232 38400 63744 70144 :=
  SixW25P.covered_of_walk lbS 6628414145830007597002604105148626409713967643223944111330624628630539381245824133867778975492538438117932166244756024761442718250132164689911794540399693306579396931249309354243234005322262091577186828490299551575125990552420222079853110788009776286758 24 30720 33152 59904 75264 31744 38400 31232 38400 63744 70144 847 (by decide +kernel) (by decide)
theorem wk25 : SixW25P.Covered 33152 35584 59904 63744 31744 38400 31232 38400 63744 70144 :=
  SixW25P.covered_of_walk lbS 284996023668719677708626595962122106107321343333266305260238367027896628110695677401357531141849154247530324377643206 19 33152 35584 59904 63744 31744 38400 31232 38400 63744 70144 392 (by decide +kernel) (by decide)
theorem wk26 : SixW25P.Covered 33152 35584 63744 67584 31744 33408 31232 38400 63744 70144 :=
  SixW25P.covered_of_walk lbS 212502966824997434969636055290618433491776242420513413912735212440559073453274367839223152706167930612642820566415634067451514546971582160012797297519640472772679480798122236488613294326018278143191716147801702 19 33152 35584 63744 67584 31744 33408 31232 38400 63744 70144 702 (by decide +kernel) (by decide)
theorem wk27 : SixW25P.Covered 33152 35584 63744 67584 33408 35072 31232 33024 63744 70144 :=
  SixW25P.covered_of_walk lbS 10446 5 33152 35584 63744 67584 33408 35072 31232 33024 63744 70144 17 (by decide +kernel) (by decide)
theorem wk28 : SixW25P.Covered 33152 35584 63744 67584 33408 35072 33024 33920 63744 70144 :=
  SixW25P.covered_of_walk lbS 53019883923284434197014439624044538225849208760470107884297563592414282381870371198726705375144358122995997135765514992677555944079639551077444682821332323211302674451617753613350110147018959112119611475837053310736479294645532285774986553867254242185093997818823627454938563238373148831431891950734991896774663139000190310275797358340495399532138220965272116548503004645920888069318123227566987451633776133799693020521358354278668089723565589794729523366475925068617450927055593656788751612139902145507094798152340546853979760702443530673162655186781639447633646691238143628207840710566677941070965809144871207458608199033242494480298791627176807081961301557487896432839536669339679404984372486282240504894321165576503177222729672321577657701917708901254033872735781776076947971180785178147204149584268183982871554436884758403035203119496255620810159429173266381393602175414156382065156633978283062913064383318527121648278945305281587627406732162792951798295918629277188455595436202962070734282492846331380047209483542659753889567059393997749573498903080467734266066381990066535181557076666279320596815466865464639321979250312589066939896809393047283688229985567775047712199102759939381705043358864705161686348969041265432500671859802946213899755747417823359826038177155203481992486317679013750845524734908898181835492660444499776279753435954862197931338318391214622439590359091555628795811236393647010505870022726882218461859975993207609529655873725335532267059368353734310798954737118351008012872325772949322672420459952981626347329003826050193050464370054095469547865912706324865821788866917603274638709467682427241288362175607901206376390440819202185763936576525220876462110068294549988919315182516471480627784816283497832644037037495916618669626665039650537738613989632689115030552924609994684797502409478512154937018152629474634273588717238126753568909848899845153968360085623245359759325379207107581094625420675865020474307434465959962512206061514267232998111572298039337079202069025588612140372674751167264456934887745696315378725835944985290144251671229943525076099347357349146590355641513305224921573562444127836379572184245170231390385368443377154887404584114445256605563283195483999906163589753905595192768865744375793722797753787069958332504613333919890712086610393692669716077787798369515375700028502199980104037985526101115699919921401788355229087945101415184140826637470437629366910268740875832166217185953770433934164622202154868710841096952311423379801591230729804325864874307229891954604202821919044315432223387863414988686263397913720208808726558035297369262282030381007353426712115020139626291349886177732773804355703602887708433679122353208223008218940811665621585291529551585918059871396448055837573520417070994202496312770026354317403991423497870436454446379765943958872105962550033589534955188986203753066775260890995084233471681476156328297316386144150179938825302840547377078077271365144379151559110723527983379625259713849406584607994820943805920537544497659869262788882352564531814 21 33152 35584 63744 67584 33408 35072 33024 33920 63744 70144 10007 (by decide +kernel) (by decide)
theorem wk29 : SixW25P.Covered 33152 35584 63744 67584 33408 35072 33920 34816 63744 70144 :=
  SixW25P.covered_of_walk lbS 652817688296997419914437037178983502253404626998824174890924257233374180614862283308127996941012609214512853731500616872107242536074677414864332396288330764076703607855614633046677802416710200634932080099441394829211479615271457638143731026164875118677125630754107934118075517386825667675190409576342227903629234257335217066833750897268704644340927429204978088779919748773562264260149428795997846556731688452231918642747757253764229401220170223730957935675265811604474783217568740502591675242539680988525525090373255023008345427388565002608440680804711926550780833171901785991390447505926567532765277750063382331224299331785723209412233935152758116417213528789719124770181698145869487414992733663286408462900888635325965604736990463313768757143455131629990252507199304574882418827027754955360925775720619291950527692366001184109599673635476831402998251490908615083571129786194812668256291594046069446417529300200587543639039172692934155345291707634805908824458344678331021384362417440564712976335644966933980815288922494600027880539700881099587308652638346478131753011044370339301658510694309070088624863311125855718891152458686329379375041864722297459099901014908301489882708602828965713029672833539469462493850980936698211693180270618122298425359959815768743440556913636640543258618077157494573523469808732083420679576796923795860139507305609973000223739794355854026903219556156082905866615625494870167977904590174833701271639187058047106109408183510708289211191759549001246301111621022208266420365797487667366110870692122033199536967984026929696962316558347673533979231495723867067342182006053771414375795154493576192339215987879648363040316430601294140090128299789639621245819352619527692863818048154298035739683611561976601598126888835578736751759979379656923771741134143188119637695358382831642883936442683948357263309611365655220993151892648657655863244808305161284830504488214723930399670197381352511432365768357066825475392528557602185620412143952529073730508695872395359991049830038305081421038767956043667313638114927495354621554426037659830834074907800180696200470074865593450637535195748670127480407821015109975042759435791051841322058570933276865937020831409641625126990421238044370393886893584686860047103151667305837943272111860768253334332052519998372207511345792080031021546525773979555612892099073947040350637188585122615976798290631179530792827732161690686516133143040609083635377865945308758447292193442350811865476366913949187761997662298019998975102595068091913473906390002526806968978287149939304736914105643577439205358245216189979571525043526891598166051076139693386953123781042987037196917646783588815694660518291863324547977345973165833510636803681767706522674349552984227331219163911010403759481998211645872629696072651131846583797144028343804253639588666271945498582911666336622388796075189947147264121130971034004545736782419842215672362663639913856948673143285989185391133857191900073001178330509514779206085088416510176847462273460478672274218650286078784212574953044986413020807686456167022589709498953328864720766159567985148618408542596955343043548075557266075763059013514332671210492750811316854101608380950866425586693316622401563047115171493330579581168191427474543706474400928903692466746792150496063525212129908455642115716883601622338907077205379256357195938084241526915856632196288286084147744920555378568510054903407514336328149952086648128236354848294475799856998918000497194623342584945901612935080875331451627233929320011398334659984481576270122054870093178634107746557877041817799954717406628656857430093896434774871965638977003781245542220599505977517586321701608877902625694717275095650793651121359655834676712098293855759617107262539853328060362170322337684406177067034411926258615362100280613280290678835776634660466 21 33152 35584 63744 67584 33408 35072 33920 34816 63744 70144 12522 (by decide +kernel) (by decide)
theorem wk30 : SixW25P.Covered 33152 35584 63744 67584 33408 35072 34816 38400 63744 70144 :=
  SixW25P.covered_of_walk lbS 95826701227851470287059673222924528214704329843989827012927572523678148649831863090353195136367591003157230 16 33152 35584 63744 67584 33408 35072 34816 38400 63744 70144 362 (by decide +kernel) (by decide)
theorem wk31 : SixW25P.Covered 33152 35584 63744 67584 35072 38400 31232 38400 63744 70144 :=
  SixW25P.covered_of_walk lbS 71510887130032326069969390918870343646114516651754 15 33152 35584 63744 67584 35072 38400 31232 38400 63744 70144 172 (by decide +kernel) (by decide)
theorem wk32 : SixW25P.Covered 33152 35584 67584 75264 31744 38400 31232 38400 63744 70144 :=
  SixW25P.covered_of_walk lbS 31809009003110 9 33152 35584 67584 75264 31744 38400 31232 38400 63744 70144 52 (by decide +kernel) (by decide)
theorem wk33 : SixW25P.Covered 35584 40448 59904 75264 31744 38400 31232 38400 63744 70144 :=
  SixW25P.covered_of_walk lbS 7965377217544580931074859730728592439526012232465646032221306576217470069634564148867296969989311351212717490221423784650338 19 35584 40448 59904 75264 31744 38400 31232 38400 63744 70144 417 (by decide +kernel) (by decide)
theorem wk34 : SixW25P.Covered 30720 40448 59904 75264 31744 38400 31232 38400 70144 82944 :=
  SixW25P.covered_of_walk lbS 61234 6 30720 40448 59904 75264 31744 38400 31232 38400 70144 82944 22 (by decide +kernel) (by decide)
theorem wk35 : SixW25P.Covered 30720 40448 59904 75264 31744 38400 31232 38400 82944 108544 :=
  SixW25P.covered_of_walk lbS 27514081404318828057129162074495534134703755861859660128795865412562471883222768838810640189376245280354951841587476953792789082113309244607508241319969247841088708716443935597552297710737867433801108966450335272495693972951020829298652882780206213253729129132313457082992286650077746593268638741025268122452981056048462467622037941573471314833502670686583123005931114972895686031097420510130881648420224542810751870949788945797868151041404751541530904172616348755811405687831325455702172759185499094971288234943810663744675715076032050573591088793783894962706079864067136927500104000512071881326777242902989166519514787981111212760617676050697842295660048245876239899056975408541475872470750431886411418530071155920172597339317781068223804415838670574805645273407418746875597103110369525873048411247329570012760458855278339712381670112031530127015977791614768989857042306298369511695904888788823523200525457783498547647439974562921441893313112501309577471806647595719197214990211256989966080114267155835816946707257257374958295378816910267773412487561836913554997164562944055557141329030838877244122897931564691837527741696220712431388202411307494549566493359120242387289680181641699754337554216803633254218372705588403574393384077270002134228118462503608302920394953920233747287694324191957926122826762221693306241525420615609639015118447931544404000011481713505863785469424366779379200991695964909119105777736450678752376083848881638332385093332879853497146284029403530459831962150061292358589307949857111264244854404492902104777105681395675477839421144388206477013569627442 28 30720 40448 59904 75264 31744 38400 31232 38400 82944 108544 5242 (by decide +kernel) (by decide)
theorem wk36 : SixW25P.Covered 30720 40448 59904 75264 31744 38400 31232 38400 108544 159744 :=
  SixW25P.covered_of_walk lbS 124406653950857350536660440281612126126117022532486447002861573353260954027526481330861545241024796168188816328175456736272048781533473562296800384980034184428511544658357209010572617680002676590894352091829894507479293043899283871507967193546914725574318671972662958213831379313549278234304224399202814316233969325592706734367921367834956299007141183596811813292139704665500032699880932789820073013893921529608986085746608558325280462494674871602 24 30720 40448 59904 75264 31744 38400 31232 38400 108544 159744 1487 (by decide +kernel) (by decide)
theorem wk37 : SixW25P.Covered 30720 40448 59904 75264 31744 38400 31232 38400 159744 262144 :=
  SixW25P.covered_of_walk lbS 653718449645471629116290559243756675708408763754838253906838089164255038548673204037025839626466098 20 30720 40448 59904 75264 31744 38400 31232 38400 159744 262144 332 (by decide +kernel) (by decide)
theorem wk38 : SixW25P.Covered 30720 40448 59904 75264 31744 38400 31232 38400 262144 466944 :=
  SixW25P.covered_of_walk lbS 0 2 30720 40448 59904 75264 31744 38400 31232 38400 262144 466944 2 (by decide +kernel) (by decide)
theorem wk39 : SixW25P.Covered 30720 33152 59904 75264 31744 38400 59904 75264 30720 40448 :=
  SixW25P.covered_of_walk lbS 31915225420895909766262817058352330641462624096133368571562510443529362352198432271920796292141387455672833986473465092994510253368876010400243712424291662189130655706068820733294669081967692398581923020309455320054054466236240251340410706157274482517887941624453287110958851523463479189027783398274259082046049541106790445836732908100500000951027998647173914764767765253605812611706293614230309678376754 27 30720 33152 59904 75264 31744 38400 59904 75264 30720 40448 1347 (by decide +kernel) (by decide)
theorem wk40 : SixW25P.Covered 33152 35584 59904 63744 31744 38400 59904 75264 30720 40448 :=
  SixW25P.covered_of_walk lbS 1895585856866879917789091210613144662001951921470526075076503234848344549267755152017434182 20 33152 35584 59904 63744 31744 38400 59904 75264 30720 40448 307 (by decide +kernel) (by decide)
theorem wk41 : SixW25P.Covered 33152 35584 63744 67584 31744 38400 59904 75264 30720 33152 :=
  SixW25P.covered_of_walk lbS 2271930166987743999796733141078384179760141376819908448900428122479400346934943562231181458706590629726131242460263680325009122039087391444876116446957030722910831577740127762768635360372397316255229221712866457591086 19 33152 35584 63744 67584 31744 38400 59904 75264 30720 33152 727 (by decide +kernel) (by decide)
theorem wk42 : SixW25P.Covered 33152 35584 63744 67584 31744 38400 59904 63744 33152 35584 :=
  SixW25P.covered_of_walk lbS 1337237893435501899607631503173829327497592606843938502630982267611598 16 33152 35584 63744 67584 31744 38400 59904 63744 33152 35584 237 (by decide +kernel) (by decide)
theorem wk43 : SixW25P.Covered 33152 35584 63744 67584 31744 33408 63744 67584 33152 35584 :=
  SixW25P.covered_of_walk lbS 68574494346588033444382765544053204772789628875609413198915054635970581915669990602 16 33152 35584 63744 67584 31744 33408 63744 67584 33152 35584 282 (by decide +kernel) (by decide)
theorem wk44 : SixW25P.Covered 33152 35584 63744 64224 33408 35072 63744 67584 33152 35584 :=
  SixW25P.covered_of_walk lbS 3481951220151507621185366819492415281726139441925003420599434990943531169024041831789620133846045077201807153003859578600255173708059594729825656630022015048094508532576969756310490042645188906351823977204270712368476591816047039630342712985143954762208368089232629324506695942791289975753280023633054969632698801436479777154815136466726311195154592940716952308973352713013413397408390677869401553849367836960146554461661423019573208474756697541055807571080389125861604857495565527889840548205805742362722122583987473745064659524161851938739604930280711695409810848860624735775003958250000442611346902215282477371448886918777561170551743788568180719302453306502961872295745796267822094868887336684991207024796634473128681175578175799960979169196464293163446663818382072895978145059745852066409501916770797238229345029409052083575605778804225270328946151150 20 33152 35584 63744 64224 33408 35072 63744 67584 33152 35584 2852 (by decide +kernel) (by decide)
theorem wk45 : SixW25P.Covered 33152 35584 64224 64704 33408 35072 63744 64704 33152 35584 :=
  SixW25P.covered_of_walk lbS 1382892424139590206227655729949385039381655732308433373659890128538027800723789213748654362929595682531132111036507210002703049068277779565227581106578864700883899556917552941517851847786198002089696387053338252899863818893406197292916373324698816426295333040950365323049877103678601348842339458385236987452560297747188262993910887316071244910200468922934632548112735997453908467260019856445739585626817588771147661260492627661723348738959502026108408430718240304936941610561596084027542296842906105532421190101886811979826589148035108903355543858083160738567799870696315608028080641213010497642241198265903303839754802773177219858694747177448616550130464018448297331789692976491781158709169360228110493051308476995526063009483899205307132086858919394296136962116105146560861374907175254680326673282300431931900882809767611922407977580099402077632508058692141968982180037843728121523314983946328929276951406685260011733231048393870535410369798663496165672906964357759455243923846634577855700351653262751795184776152285599912775063846412181598203623569447891410086526234609295890858202767494813598885924760151419199606803942062 21 33152 35584 64224 64704 33408 35072 63744 64704 33152 35584 3742 (by decide +kernel) (by decide)
theorem wk46 : SixW25P.Covered 33152 35584 64224 64704 33408 35072 64704 65184 33152 35584 :=
  SixW25P.covered_of_walk lbS 1715879310855500344350594890592154626949243414372429064897236628799227603374741924659929656734453019449477032756624343438968120058898782914590042351920904972693806068679520599026439983322299374095665704823495347751359824490899023190054073763680312906101441563127065415760544389693969598266173506004346327882343233569434316321454440881948105670246630488186789258711960500890229687220508575830520934192166622116934593399497144827890956667487419314197960944191600094510670648438791029789720668264042472486595532753260498668842512599984469594034833938034808241001660936266063782854181023331928780605943551499242977507093348973274523770486498741400506416134644343526412371733892556878767482274525347638832680381541662826153487133610902665832889157100276353770561872877005768546215239550596772123641502129526987942414828197564408883229770965532782795927048210145500299858684603657380095230121682566598242381743787352297653377666878539187383523526757412494231849933890688634670103889815629009043112070562345878927977262835629690388500078324922447062473772415093633563371522969479222455049924877607139241948617262980991261857841170730940016693161204595217616318504931869084089304055135660616434371481029990916849171452977642026352378161918479389228264542038510151970021635407386230121964685730675468215531728328338325811310703391442034279285962643513126544144064872428884210981402780192561738816766514848971140211283374665701614524497650538322859595622768405088240625935946157758092828239592836408195635237073430657406032400324907297499094070099617327370754124033972253008778578979522848950735807230194317078697897282748575432140712995426615669494641213750670093984502854996724317039043380106084538790355577793608410835214578480470155075005317354038668158494373690464642809068564973911695136210518821354967616395527136893642220054723157279649343940461500066011187943446104737245289950359990217610651364285553201201602208967615870229821378485484498361976840200753791892842946079526947583676115338925009846352513537061745639783700983960922021807630623037415851010575891956210350364954522658632337776457702209583715815425279288123160613957390393217917637959292466580027121111716515655059794283809159079478615464524058008280067866295254729916527635342522453655909393007229141659168471174345702116943221447089094197752018369570736436943110645376197989334440761916912133607589076751791045339964886959585873911019924371747940373737994684865434797322429989196456845002141733059992131530418236157926952080590492117593824141336879933781567498455448769624925690554751722083679936531993093811503235527167429628906807237681433083506268642383456614117478133128821099417445558809534160312031074339832147778832866474360779222141060252534914371041687432082917638025706796861642772169939089391000754229563892270468161113566983430272321110054494567852040481929975178673304741246582822912649501349856207776403047687891000466890292797345551029747677468235186110470528426624526666787349470377872299984697414956017693450059380287822040331138168831560182673060410533630893492213653076520330047968260163930356302391707708236415882442919864818415039394176024650903678330125529845419276810328378064013344319141938435774365925020116403383120936117492246271490035977956357373536542158098719821945168051423083943539258324757211253317821801058020330387955055633950420211931214728566668827091678607573544423528908716454191853997941328606727288998487505896350150519772758079777371559591667531011809473082467188080590006596254844241209898632534976706161110770771783300879659017433087869190707222362511223110470736622509016021028421564154972611351338772587079197831463723117366448129414154108232175758651485269519247303206712372640845590082252794659104426720278954696150243160408287683484528844769641387611724871101790862229059781617631903366448766029092227980392280081913745936001275981510318428572118931687481871585189889018266313885310047265607126392006955314201701331502940560142448026185520879540259335033458811343920912186422174949348766848554017818930309649201823643689195468545341081540649316577156354476580470427284523956526019400553178015957639401458231707482105675413749922917769554608031156713991377268235124944706400229969299347887399951264710405685197619134390562347851049720893943519071966477815154582821390678516432773214720795860518529895422259468100749169269028530150446243816905705187003989910589658464761906750975338948964100223778835348522870214363623561701566789395833825269207387403803080768652054666452050494542884780150341550224135267448676984561308239290365593596699223060045109776865554267863882156084117351429249073384842079118344639127032258581963790849814902295991912144734362785539191377250845768927303877658099202184020971714805459855507346917751910978146349363100822803328838411712589838291083275076482710049583143250266153590209815696941197999954931601615178581475637808849018471793674181384045211146316125476079203485450201570035137046832966510941674688865635950988514618188588992905406645111678413517482 22 33152 35584 64224 64704 33408 35072 64704 65184 33152 35584 16597 (by decide +kernel) (by decide)
theorem wk47 : SixW25P.Covered 33152 35584 64224 64704 33408 35072 65184 65664 33152 35584 :=
  SixW25P.covered_of_walk lbS 3111815323325127321725212790013943133039140949574855541086705287455476162944491580867784738050589045379231226873315166291015080675015938487583780526464115055644020170667361010954291740723104972777061830806711277657270983688295271977664984985733789392338029304764446217830262821814204787392178607898077357513436288912752584618256727719761262565800227035716427842350289368529166995170793921390811062959890658267255078416542562708043665920990182403468597623530283431757896563159575147687793408708071002674914581148464992613106918720154119921963631677519096823398930531831913800342319362124393100833091902245829928869656747195723792613601940501302560151970379184612360000645375387749089792990164972081028012589200848331141669827524751950568114682392172081998593300060148205200799823811396207201062231065972563110274929927343100919169104541235960434089923914206656727375504361828801625628972546630381020182504788663182224019400583609369450776994924841481852648246792937698025670880355817207488906960577289612806166745761874229546679863453622867088616040056941400138040375673612294771727065252472382353055994740232195783664408816343046307079331520462484113967210318252302830333958743969004750854042295751942330239634556190893794677648906588086089826845335863784869245372444599296689375681870154755916240747886521204916673464516548942738444190063539774639145812887906537196042136498121167327214207503608663149647080765697547794286691453028321674467963337956226745504334935139333846891479592842626444122867349853067878696045538979367386602310193241820998794065163951291190209463796172737496225045479761405047083878243327853186544407283819380385742821442200584916640477040653757192622490199960841632987524192499286853381368971435689307411956310581996906002478479667210933984078495108162314484649407525915564904335236828851965415515319175792457604878105354209342572392227900241401969017252052720391524085107088873527566716367933363364489945293745855780396759158427951920078333408754222381054989579957628357655434784460352399469302433035274471428223724709958867858775700468077917836863473549616335273191330141527084780624751976037803965837256590341428395735582050879865620494149924094499539657655887563686950420512848338909113810519275423218589678282530548882589166508555869458669121481469767299674160270312791153231986198492103030473640587966623566782665917532333459348660319878846442031791163022002919020101829631418255459599992693576127827275218718438271851366830743797887764652768155157284195287575452387391682215476383862308604945968242440665305069715316574103880034822431436789948172332837880931022669411243532769797471986799945043782297043291808040805515892720220917799755458615337697445101230500660913757125617102405919329293749454089779276763573282695916593008853014754878832404961303972061501108782194494940959808894623528081799662273350721885533751942548089500354156989415947008492660297713217821682316011339469449484295529773936692403850627971061365074346108905163085269818198802738668041649402914979691244629172441381541309055135549508450201796002142860650830532885820074 22 33152 35584 64224 64704 33408 35072 65184 65664 33152 35584 10212 (by decide +kernel) (by decide)
theorem wk48 : SixW25P.Covered 33152 35584 64224 64704 33408 35072 65664 67584 33152 35584 :=
  SixW25P.covered_of_walk lbS 1214929926959834042835772604733627661874360102876015121503522737639050808003931847415730478920749126777125077253952472158485865177249091449672332597304602495081819040112491719200175910320050222980070409299551987406388434024015989679956088314329539868086124512633377915260487582689025752150174014158016413038465786201573030347922675909064211944168687930666667904850815421818274960516022112641982522723667922638700518442264306845476857375386476453222960594411659478883176373323835699324428509784733191544748956967854730252523139526764888345140573494995204999215640009285495964579474759986605736410581843408822620645710642865760530708731683906533722053722485134505196379658894251680224351269682 19 33152 35584 64224 64704 33408 35072 65664 67584 33152 35584 2297 (by decide +kernel) (by decide)
theorem wk49 : SixW25P.Covered 33152 35584 64704 65184 33408 35072 63744 64704 33152 35584 :=
  SixW25P.covered_of_walk lbS 1195472059321027277864981793826183150140740207922027085035578632069682861952743777293399484206248247782123488461131599503741146257125860707341304577019449498471663243197118779179157789913485797508366606594486315963866328369958363701031093853021973565117510007950955485923045223572291417159599106637711815588542778778977792358062485362760151936472823466792796560879991032006350152387029277708068887811987544801361254474217966877543913124114993634333563026601682613594071841705943192192495406888580090037416602270367641835767895733995036226413363613743948777180213648726592663639443017527665014648257291016075025104967708237988987093717294238344560587586054360214068380040493214452267977752421789463983906047262545126447631982237429693806266272891553668688629704030898476611538468566763833875951928486505425007448519135144818408641322734609487906383746962037379008396721030451713111279595689852394874127561386475340027561002119692030045673400382719748988848640663555929580807157573673584867583310454003554771707129279793388351165501621540076082846416777588455868376476090885052118113806456840303022714296681247613148549153259213224628479869768715258668697513722600918275563497261070584564069996031576860533056485409401110134612036137359718438993793189199697087456692641895807267868308618030345027105393453669665013416523428888031497376253850222093295005305901880112164775362741791767604604403046793348943193004626256847019177257789651148787492097844381729843466825085384924230787744804707127774509225510915885684906048024633266649584383393417548057266515106512607931456164282378019432633605313426115937266771970569602707236016897357901421981546647387933204580311008918800552222316443627649882334825226096579705185346879274622953340564064257443477614393516560005351634186254229693693451509537855403062683693744915651867902613291498424158509719506716859683819360266677782042480033672093871935999506614918866044545159945568008482724650467791415595574953865897488314153881972669639917184761466064563141040607705215068345346491225110917960256558164010279984602071575530282035973174222252538304321111361280963062634811744790275407236013290742630123118966562514981697277031070125627473541334641519358498134289931577370666721919152003539205953413831928634354504356244961260227808886990537665132048049909996323108074104534799128848555302226184925484274630245013704507635108827494612953871830335841873342556562339685345626297737424258031596561935673776144935683064722609398307559190120281828576906808907466115771155497125860123299727635027824540017656650198359791810377127908282504987966397960143844277061738756631587141370649632744066901096805112534910514531115480078093077056665270913070791064834188445548954276146387516267984341339439291764207770630768699371076431378824400373594282232443873330754698609417789897353307176627570553833983147622244227681317462468546863873609530458277045591120218034137715062848944736841976706061803747279947235395522102563729819226151441977459008129419333885302109996683834076622576458631278269727038133377468731759666870056074452712701672457483445899321387158043973911217058871285283102268432236643341783026624474161367657331421654179939389209345348483550178831074978232931058881649900992731867769042075786148719329889053901036007423889688296244655535580963543342272343957721095447807687881060924421371290253700954646085782334617597584506288591832424772661352463145570456841008110635209411061328521728069480570746868115839724563359203511998963062345163011878984288807566169984126372184137440249108701242005697066335205581387717373019868564200879280923920190220531454117058808568664003135156545744697025353353969515122970932026198961026312997215488496265058159218233667905514807375812084368526531050788384603408126415421105852890359731295554501811302927518025304334585360653115566716650132858379440828544201983668728340988690403324334875446089532752407493790390636809923518044965045294584651556320521405430537838808322117087345988218092098495651664700617061218711716524019829191011829941086354328486354758880367768320234596733824579768827751746100991973888587549937490866113808876443098774031066405568310968414408065757691458072746236411797374196909836182401243911142068724340613394696768014431561668061447508039118284328593366496607812077823088343945047308662686280126150061072419594882924248605983101946758452708902526096956370829005170291738453273180642396053898230753393756525123017527251863112004390845628167791745755218511739957744583172037393075311113741061750687163968519298650781239255068619636105987188456005965851192790706735388313072239259452474679858662601422007442737505281917627544216323130380043683019787436826806881113769529071363682292010861029835032323697657044025095648801953008166317729919419404421029190114391928339026219341438398206157317746065374089907338336796299820710538330859987582312276285228834956255543581051675349795808794398309136863220577164305211859455055175817313219582566173601041062060992316521027334322329828255279867587885680812309817138408760020511185697937977096845619947356985518255649710346102581954661806316742534975890052122259825917240040200872444503039575274145494520395178384971244035205745810015314599643941401219253837886173051727652439440460975910421094079151733422449863566189157573066160823378522269042619235782187148214256930161136030028613130542955517853548628413002871702542693215338447115322900682716044842124847749299215206613918067648657725075636388663483105313544350117692182424679476160156152804085511602588124875091179622967042018164635906304604051467042987065517831776832035653905575797978751976097429746759616814188911207421282587186901047317251766997651143172653197503551355336120587889406812827738875007415198238356784889098323338743680785358014709447103671093928709775587272855020486629776713189449492067500464303397387890680450787953648650597431659228527739705770479525550769714788491902304876862967857696924871380436667133501655726 23 33152 35584 64704 65184 33408 35072 63744 64704 33152 35584 19677 (by decide +kernel) (by decide)
theorem wk50 : SixW25P.Covered 33152 35584 64704 65184 33408 33824 64704 65184 33152 35584 :=
  SixW25P.covered_of_walk lbS 1286932852530121556274277020344417472741858513311980780655384873099924873506080238468752375879911297672002330748425690825705344325017007193368362710980521263277686541721539176143995205333301270886944382127660023352421734224847018087124351000389085345319622920455127212312374438122595882256349012378019871400482 16 33152 35584 64704 65184 33408 33824 64704 65184 33152 35584 1032 (by decide +kernel) (by decide)
theorem wk51 : SixW25P.Covered 33152 33760 64704 65184 33824 34240 64704 65184 33152 35584 :=
  SixW25P.covered_of_walk lbS 56996358342663777185368996265382282289614790332112379144565154973914075635949807550652089583330409558768792651596215157719828816773440934707400133920707370651542285163021043177248044603540057773320768015210854190110640804491520832328397135287463287721632845763452250718739512228868455502695112352719037518716025822018436339976037168522579263712936609116763153725064358971628201109443518622915157056361208389543629395413548277217902306748501846193541247347413423634544847067206952019073359943592582514000272193191801865274982867851287715991107042327026778222117753268218010939512911526569674196158875691784294599077858815670713113589934839366298273998422079550361819648148947131806788380025470913823999394171620602983434942995341214799631883724848546188713398681957363129341874835153507932462246419463958808579267137381365233056859519184611548917499454418045310803341500600219553881808440916075103046410182701417213427434227331131288508987541921418333420709998472282867559181717858914347628958877933361116522741965425672601503643562031048677058732091191930219910835505110664829684252889478963235126863721532331595144903770834863070762260312866 17 33152 33760 64704 65184 33824 34240 64704 65184 33152 35584 3797 (by decide +kernel) (by decide)
theorem wk52 : SixW25P.Covered 33760 34368 64704 65184 33824 34240 64704 65184 33152 33760 :=
  SixW25P.covered_of_walk lbS 65564085909102873945991325162182917650894726178499228922789099071210892755342169715034153010775123979547023809046586346517862708662431213820836109650 14 33760 34368 64704 65184 33824 34240 64704 65184 33152 33760 502 (by decide +kernel) (by decide)
theorem wk53 : SixW25P.Covered 33760 34368 64704 65184 33824 34032 64704 65184 33760 34368 :=
  SixW25P.covered_of_walk lbS 38664740487842822866055496228328391299395990735014016054225407365140173961363651065988627171979079257039508478880751726951220055281245038526145575633783302057161358456982225901762101178657577770811573152775692357536599188653344260254698072053730529427161158121456882367236430280104077282726483891061499380291686992471110769970706545117390233542866701683868184469345569205436705895111092487133588942540625431312681682298353016588656049971356166562529305909301151017260790253109003673118667368359627239958663960250777918240545008938784426064894618966990323805064342368104568692098259666416567508239504576000590590127399927660447610518505603312489187532802944834455554921966436827280235388477221498055867913147552230491054097100561863959576045362726423522961602820909990486229946921155811697528344180679648045868642871178829450943789297168925411528667799062419108844689401053315944313348025696619678322387224271608610106648765516679597593495382342911715171375200987483563547934688709501863852579042123971194531148636560609808738779967385735836333979575423058959155098032833451152542281490280844711268306192515741543825419767929491886777530165005542243061903192692757928561709636184211628657613654910195276091697634666411191743820686934900874217007508228054954266495583600197728614918491349161410913852332440672371150213693971006539868835131831940160632745660546362843887975855012522643994967000767879137257065976705184008048082265982392584466578857973917771772400815872831292761484315799138 15 33760 34368 64704 65184 33824 34032 64704 65184 33760 34368 4942 (by decide +kernel) (by decide)
theorem wk54 : SixW25P.Covered 33760 34368 64704 64944 34032 34240 64704 65184 33760 34368 :=
  SixW25P.covered_of_walk lbS 84292639469213560441953171840405597685412821002626210806022417031405251640309003548461167998680632455878566413441558186970134966538115637408724614633051922401510021338641144318515292667313164326606702516170255247649258723765095405112138381450302792132494045020094196682735356451391914584948303165932908133665566871324383741331685494914312042256514177013757982064462094470062905266449029944606607987466232478713823534254279662735651377384486913266182886251977832790340181741699436084003645517643309891448654087791215030814472413841976840711165338696120510524140504430494903093902379143233356899837551219188287899932713998167093194858868517210654531817650139341672787257411572351385001960204294210423915539817580953647540378346989820874321912063764825000514747622611723894432956280942679706512570555461975624311674196840095766543882198285135377204580454141410660741957976091922649585124697107563196720795991526425036951348117916487264709133230197775764184601714941776410976182818122351645699964079437623015597163243726253918016788738618135774305375831623048018748264820592858516634837850708577498206001578584700311173906510463540663404015481744474569679086800067518448790119435808612754699900671049686736086671631562948802300068453680577092819712195342343746604378558971296369837162514234600099854753878216440391440746310366839156149829792899436361632066246043768568765735859740108889538107417389788811008115034182784730303254363234520952601625884811214969538647010112663337987110921531038619729249544197119974122651037198276239769695179010480732666938458060069133894039854096332373983337125705245806442402714631236274830410762702475397212012604127372115107170636718156335269941263999526262721108315685522820013062295663018832370254446637976431042178421149995521128153463916609810374927498947681977928628940087873630371643722635241153194414657079674520069947517831400215134115886938459374840276366421830295404235200947096669378797491591011726790681790932037732089419760680836573696043153523717722547667974078060870535933158945195075276573886059312302949300494723829460150210806244056720663500105924310627037609207646315053180224934118853153180845466892537079704793940318767241190774418575748860024626732339874610739493011887607958772753168095576913421441709452201472837753333795175217108907062379633711869542111228185284486448358061637887005437319772897428468374591751641923765110080256455470656904830537076657878926872410699172697840643643951756952172337740225309966000048291058800219682241647936797035500644877626239897621807730958626510945595014740108812099399730333320717542768561166676518618829989734676479623073551851093364297486586853238983781677341638836129536309861681463267825554387686540544456503588200023750905903082355735437962538217439106502135505905937614498608020747821016431336085754575384012768005928855698377697693975270143157096723004928558 15 33760 34368 64704 64944 34032 34240 64704 65184 33760 34368 9497 (by decide +kernel) (by decide)
theorem wk55 : SixW25P.Covered 33760 34368 64944 65184 34032 34240 64704 65184 33760 34368 :=
  SixW25P.covered_of_walk lbS 247308285786580761550590079632650554250225830038182316632667944747404904773248373259532649616486674130069286270554287522778519070577236171655586180759161276737052471565303426449699496534923281065480337573816304039620954067215195998735050223721350710081281060648590938676364719163979444781954447231475680502931577508169596675277878796673736914591585298503985732735192053248104267229754502603231917478252141162599490201505012625673219211599540449899830891605941767520577986541512159248678494343376707019009891084534220874076984746114146047474416071550044547252162782471387419709537452943509373061174868873424839645437907586968197577069308590889860890272561803536059877733530708866328412624007731930344868089694964830570542451430616079467917146551893492648888537510576642766176126801635165915959895439600282178350596639932153323754678238115685453080791816687349041776315942084141200763055448763702488857248141939079766410676692514978775669818830994230661123245537287260336470339039399102241875370105487574392386259172795669477753587143503951882759975269894040748081064423671774402621783413474479936672603777601778970746345750449186824188737221527064308474672981874646562848766124117909394575733332668750779499654961508801472235538055896962067049291720860521530912152599775175308653617104590897970936781314105439627707121767729000525653991713528546110172212268810742740418918526714419664411876997695827001591484301933166831122473899371761946826799743978219101402501451209689004940125004922623949912243405875358140960222025277037051601723298069808129110809962028201785868454946547111357231159541772546674858815324560477908549885972637500287890570209227485630564531788527049620591769778666423649428265752057089854999902692868724175332421064720562167423339749528630538024826623052106148327606371388754142706585632716398232673213351541508143202305353207470664832459466515872957954881794639098511826930732734883176641871193939889439255680038715180729787801883733555901063308813389095105328800864914861233297162690398975241542601477244622681112127609900973892788718213085110889191765559485881269433626694107041224609850850059880886934601626567729378105292485139352852496512195258299943091865266187328071908763865877827366860016561834211083406395622251064869606966619653757799204930518390598588896027319925192946820251064795165956687504169110548523572882711300066359008299570311846983899578720069381007772192568648396115172553476082101747403989253901801873464200853158724613708329324314035715307720052312983324221937018611610124882950532684336075480112256901582706154033606347380980248752400635854862672738285751494622562253206129935176030451764631648960932514506375527608199754782073190050475368381367425595313929033709031877787969012711126061315592573137303345567810458514581394396162103443758049942732678092398384950629628176995935931046364419366520471753089766140919884412299655099909537355243060043793842207414670041601600316761274262864989956979242931361731104881667636376192071688025221403020866250411445658942392444140564196980698477346588112906027958925629828149506204848891664940510697854683777417236058243193378781283730806756249695759086155696277813978358418021049207150139893005003460220813697232086003496694329737566444299135202221113945208288350537603165961661535451323938155452056877360592449569538986365303813773193868391049278636574305885508634525561273447240159194743259722564876257031838262585854397625729204455596800849850630397413224134863063733559287055733928494 15 33760 34368 64944 65184 34032 34240 64704 65184 33760 34368 11542 (by decide +kernel) (by decide)
theorem wk56 : SixW25P.Covered 33760 34368 64704 65184 33824 34240 64704 65184 34368 35584 :=
  SixW25P.covered_of_walk lbS 20281185918962406380872619664203489873671404881502069800817924964334577340615869484919689339360526708839724535366893397330488682665835223964664955574828199329095062133193837037194949966255508444696590344329743285678470229296959424851286929153422879718160877586369536028801272963548886858187661620723467848956702002888035310840701087211833487455357203253132716205090905453601759448881965526945324082120635541148048887162927635867233709857333955208469408089252253143564990845535474024106764605385575763943330155711770064216980195466895296372286027701456130483138429634085979894004628897641459805825162799262880006094365086883856926478563217299598607536604410491124906442473249782275307004499907677417492539212567819467050841711137498910046393780277233227576634825438639003136021469303181506487711539573311832638641668197077155810302689780660889499893867508810750825967095769357880454885049851955324795663193064557582850470192688132943081378411852523235461960121744256690 16 33760 34368 64704 65184 33824 34240 64704 65184 34368 35584 3217 (by decide +kernel) (by decide)
theorem wk57 : SixW25P.Covered 34368 35584 64704 65184 33824 34240 64704 65184 33152 35584 :=
  SixW25P.covered_of_walk lbS 1144400087807536224393976846057120380318802909694770824937220241045604697771331889082690708064239884806505230636990543406791535309776051935075907690177618678543991680936092193519708887462861267001472916793890995284887641436888945314389323869464895250529082496810180456833809323818588174213862539973509841971707536127967293686229724652168169501420306062245557063215919126193596788721083970289657218680114 17 34368 35584 64704 65184 33824 34240 64704 65184 33152 35584 1342 (by decide +kernel) (by decide)
theorem wk58 : SixW25P.Covered 33152 33760 64704 65184 34240 35072 64704 65184 33152 35584 :=
  SixW25P.covered_of_walk lbS 2296224475521298768013693807294617493148053400565961357482718436237697799886164027709155883024443407718974221785133941324077702228237513480948358469086743866536361771642240325018134011677122930682153778759133062170208263806039502806118487911789097711410056132727467075548190934827473377426995588604134420587508776169285552025368330220720797395646087574291208373247895750222801802595669084170420931717533056164630969020460916489981845529428386226787565279976169709315737836781034464664565992160363850499505463733433715596589558170528975536887670253611710480935983925097514434317272702690200664295007964007568956549683369936209268131484932927780552462037190904886415372274593091616921530659783925737804887114802371007899549595020958151418266041163601134737022571125928021131544802823992349586298821467066989693250518579766523184039545100642366993929420216526275154854507395933930537771888222749129495617849411152256391030022210079243371028013097868362665860200083272907969580022262137277950913502519462069856979895821200028030884534181536110412115059340727371675956422096466068438924051474502087032251877852698606109891912001740626251347126410082104106305064320074666540946443064576080113591718587924777741309026936771424441276144032376177205590748732960781316418666604442523173312202647653397282 18 33152 33760 64704 65184 34240 35072 64704 65184 33152 35584 4302 (by decide +kernel) (by decide)
theorem wk59 : SixW25P.Covered 33760 34368 64704 65184 34240 35072 64704 65184 33152 33760 :=
  SixW25P.covered_of_walk lbS 77963319534532603597014866858042553550652154280623378471476721762934762587598903118284502405782549504973372972689385401870230722386811489496112661787068719271758408238546 15 33760 34368 64704 65184 34240 35072 64704 65184 33152 33760 572 (by decide +kernel) (by decide)
theorem wk60 : SixW25P.Covered 33760 34368 64704 64944 34240 34656 64704 65184 33760 34368 :=
  SixW25P.covered_of_walk lbS 504856220172825471660507602630699022584320096443090121702052054233576167677747923047214871587873968718974178252736300586508448769462852352897472574842679355618624029994467690989567225473508840452241771564139115553808978243279466050494161524704483968344602506168243941615350322215622562641399588867042900382289006629520927809035568294707570749842517206396750253846169202570978184025036248044305161790857891872030107138913829047775355281561717450935695110049483465784136602747106880249210331562040927892896776135779713940157302019932896201910736958023197329503195728853428435252895830250874103422186656554125609322768379082526178640272412297573184075123753826542576986527313090816821037727875124483429234817879936283532135127878173126606527282284090981075436387187629195194384293618923234814457620388658380649754591194484829930024147780853415752118026426103399015005977578393517885444692359961291142152931995409562704514989815473058016105453840244204599243996496241526050368388075786646380976518517767197183696683692984496362633212737530204266313921633807367429063457716567990255638753593312683098046539612480062792022891861571087764559087193624710997795862706696148898867859045812090283406915799043858165733940205233276911008680167873501113177304308805996609923750068423716860123993042390108123261191345036118507085556225997737814256547449216538748703301218550430166363767137718633162541373007511689967921124219488476736471914267995912543865373308604132303408504200509176038778526457357947269477265203625526403930976999137389472855670423260467166054827994769759851381876463644648943628948107189525019295414871495585053869462127440492300913628442349977932113072638538711414437792584705231784153183317385291420378459500648808525857238893634553506081746138611262421265737694812460244209662080352791375991443144182325885159131330251081548480754447246591846763740585431428467452094084756457518418363227460453471256095978762828610314588348251521989313339624329549967596676675096540538668869998985705283613440663490986345607838035787194049300329217971842714742062001678067829687541151717527415332186588024255965031868789620385832620116945315752965118699052361773006619932610048156831968124035229659083149207307269483592283105943235315259670510579679833397573607365375128764184828557569766196146843388841173290100642764385135524836682674103045640881284020746460612411805899072675339187504827791009413358959049792917363672320585744921396725250955623158946018179059285241209075069490963502894040148204271043680306682999192259485812157273915128150963529496226542319586066606419150358457261910465949219550829058832476349584002441913930362238645650160954028727073487841075874551367884495270527531775165191021785705165040687276033014516549134751353450852457470125217153949860993254572784094740090105635771511814713339572540737007792793976051444173662534523792488972603752287020520229452790016361353388772500754279080600951741084971782756079132338220983635444645968545530271832186681466114866181493927796823566365688139864554115139544130193488832091728057834694312955342313479820252396064706675353766690208863126180333475549073954835744204309875286202039237572489072175347518957431800855777820531122388542365415313767055012259201477179320004571524804157282547187644881023557846136198087869545446864407431234539955521135168706380787138193445270062 16 33760 34368 64704 64944 34240 34656 64704 65184 33760 34368 11067 (by decide +kernel) (by decide)
theorem wk61 : SixW25P.Covered 33760 34368 64944 65184 34240 34656 64704 65184 33760 34368 :=
  SixW25P.covered_of_walk lbS 3600612419884798282722246023534422059402306843807221946649092040957287641386542463743976675023480513496141953532145329472832986495568937585675343021922350499037915572576716644332428226840183546106828742684173814478277488183630521823155435327498388385891873238088583376882722244423001869401365034905291671818137497663890945011652509477346704722107247957680769413336853771435887653393607056373766755227002914550563273976085004437243025822464903050201117337359634468452249400918693523192964159500396842976825229709261787519427924155141016126676259393140394969416136268733848642032160635186756102026988219691605936340695721733152496647400818306781995455714528286731495817871959861495179616245480242916891422864088811507839604459775776890331117220623980755932779945201470522286735036889407215799625192058486521781550371019450950327205243723552759572067716898384610750603552293232461934455595329331794712777321967295444912462464280710841002882290852153070857520963548415634079601371231803878767832534300260159162640045554043768950044838132651215808141421022431801831018086126627827092490031186939777321859927163219062711461865197488029255402794317785701170397181783749088021280685074643484246324017957611973580747277921024699671110278092658370262873009430294124110609130783754903882351869734690170415520805439525415526439599715175175293804359295413580207415621038181210455478134879710964231678474966581086438711560799871633219597246139406137906770453433056625887604445145412037771238554613897821797316124078815514640096798654722416155386665483719361775387311857352446790177199662264908955858330147037751600805326201886204790151380960116377270415565797198021907497691473357510942015438614796048827035733796217375993308815785108338953557846034382230057162326037872660877848037239119809739048710827964230544165374111320082310273229200667026729888463490331858241722103008094476120594670125896855861588027238227555135853850728679790618450447661216037969912274181793377385020329662676877685426203283444077580303722973880916957962259013603851433427848250341544307506038185631226994163493241666758000785804879701366633199713062632981842315957619055869073453031010322151753268369214440242377027053139433778706152013024731969766453108780661742679040779119999635786827174000914800519053793558551006932973163688303331888656260694702417734593568974962924528924803558528361267308639065054658304809993699698343486450161780959384650906284189680237680346278089639633326026909499918147332655941394950419121698046079845652440492204598299439976485357740545969051825372183180319550700087683861702125890256420003775497068153124804532611893175891730730661824671383646320669389746806458351028193436851545277339444356998214133160635350566819296429135173317551911326771330310243390012557844848494916633626333673593790315941438604690267339315261524559132397979371589533822709428345129447996401560408660225532416137984673103331735494875473108853529280344870697961147803235994378334024418 16 33760 34368 64944 65184 34240 34656 64704 65184 33760 34368 9812 (by decide +kernel) (by decide)
theorem wk62 : SixW25P.Covered 33760 34368 64704 65184 34656 35072 64704 65184 33760 34368 :=
  SixW25P.covered_of_walk lbS 334021078976718998825223118801775586760054370657498484118721534252072274157030544372775108651569846033103644367456294594052003866252634238069666497411359462 11 33760 34368 64704 65184 34656 35072 64704 65184 33760 34368 522 (by decide +kernel) (by decide)
theorem wk63 : SixW25P.Covered 33760 34368 64704 65184 34240 35072 64704 65184 34368 35584 :=
  SixW25P.covered_of_walk lbS 42230707220266759613148995069387491832089860244605828840128573685806949785092650869445168105653305413230265336614551272927623778181862347741152881514471759896668068755141930792027645618871325390619098184053887871876150258809007693923638270870303384071282057027370194743657010851467176674796543691622352718699779554194803855625648578176508197268041387160730010726256861041177743610808570678869636845417450232973039147507288672740486451776455005562590123887892944540497523886347208062457267160257354473261608248623600505182969792541175762344700420423468711794593518709199302515155818590413178348902439318935001789040379248553373362 17 33760 34368 64704 65184 34240 35072 64704 65184 34368 35584 2097 (by decide +kernel) (by decide)
theorem wk64 : SixW25P.Covered 34368 35584 64704 65184 34240 35072 64704 65184 33152 35584 :=
  SixW25P.covered_of_walk lbS 1391784720610863705679916294863748815888325949084048492144131458640102875080512675660695037925587407730001965098409391201135934938109361510559321788433912747308738950103859188428376897061631288423328793683051229208925862213019890837489870410521330994 17 34368 35584 64704 65184 34240 35072 64704 65184 33152 35584 832 (by decide +kernel) (by decide)
theorem wk65 : SixW25P.Covered 33152 35584 64704 65184 33408 34240 65184 65664 33152 35584 :=
  SixW25P.covered_of_walk lbS 190843458650827344518245295071942867567690398622973459890901932148406502954632753580677531331212735020717783699886908620764423592782371703758041081022492687576654542757635830138835047604717450139611460685388504427317088742426208438726519934461923217480864357116873614489316255150228533119398578646561395040268898725826296340124450871309359736295644137791991391646923591530479052237718712271369930406462788633905182977390419242561152231973463215078168747471053605672329129614534201671440310121630735444384952924443294572178291996475372441336293459458718495653151607491898928506202108326648554975657296259867207869107410319810226167213660236574016589905608306967714297131419029857921129620084391202539683607790420704166249294005351300279837237983990239051207365528900460673723861147474664920306113409625477809955672639319359887128054862495951266963721975115488690480135670150854092160376532117803538800885491636741314216421694132005568992163347793760969464716097643291105272744159352244923543676310509076900898131059642299363205987808384119193085833151923977980381322150674919312374458460598174415609610102475725689762811706298176150179931272806086290652209579642203769775359931811492370736099532658819099887532203783331229361298761376971979211649145906681778911117605435362586640791534850513158983541163540377101869274149021714616204849376907606761674714452812745445781126359908254762983885026218279359643431515813911956026829084154362546289795037276554612590082841174367589610516601184162863027931136371322270027131364925632448436675451320506710782008138023908759111561897083672346212401006621058395647995883718619127810783018506909846144277211027892685178522247035985968827748842524884352401866231092251661008765374311923622924851086424944931972318773761552112872740558036145480050490040217235398652276971413774384412839873860174364817338860455713867586456882919493957159646415416803000338282280721712009286589243199064508583136368712120043765999956171634133605724455548682563271963247704054374202583882155269394181672091716039091087627295334363148668157133901362231103961556173208155723762131884633709304784607183029112381919054932602822171480953291612598869207589709556223984650599401820014426600365024108043590093449354417409104314767805888746580618858007866769396692513571409206503854948113928800227460143889657082396562910128261683921412926851261135946367777006911754814769782446158550311442274151920637076170954343066202584133580009658943370799137772172611420206115229276144750871432054412898993040881461499685495859655417719738992815845719194024898064944598804891778782641049716364168485880442881973526960687948297450116336777152181105375136415600373069975277364870167355053193930655445745505047556974801952362552516032789539334828882230343629103342181402056403235673000986943696674719010004628240389430132334809230293257664462976975059878904914190908472002507735429459473258437360944674727452182128661748309792931957572451402551014140595852555178972840555839013954259591125404112455651615036124990315722198291744045321316227355748680964745520033342883688110578812635978326534313541718301679003300280250141681202746379982076029343488637580324497187722863323493503191388753552521501049336315600053248679531838354951203377525454426110316640380780818540844887290174775104970103641293550253035359719273909065977933720062272812745572428058966802229565095421167314678914884241276185782212943245655834193804382621447365550699613545118105201759980642801568874887634225021536995810662793917958900798724315245347654670734238881586892559808260406025864525270146657684574373572019939548843681823737043962954106425039233576309206785462101206562189847054409913567010069436186018954751903791161608927561136864529355720562157451314675964550564653560719157734688870575996793965062996708249975520776322899639869525092512291087792373721835840855675094655476929534046882361525673600557027776259865664839890098783270427543920066244741495629021594931708608460386553844647789243258294379999132612392463450360405317390206680718857855479723593172686646292927252482475882691494219427078897908047526536678712102399582474279716795675541066356854126965694161439322669082070053187914295855011364522619552786886118433761290319985817119273538781589926455355186016228992151536122431750450849116114203035042058195196199265751871244699653485011470942336480982422459753468134072578390833175145961959179748606879984409263441702678903796434783686548303275196669797661781279522335141078820224886621378405591409843617552531731198619185003567182340221767097798849649311668538612109702322899022758655901573955403977044299898973975185808516613829266700761102383465860330078524562778530010930822365357370225228619485486340126863760160308299610718555599683344053859580358180548902076223064322858 21 33152 35584 64704 65184 33408 34240 65184 65664 33152 35584 15807 (by decide +kernel) (by decide)
theorem wk66 : SixW25P.Covered 33152 35584 64704 65184 34240 35072 65184 65664 33152 35584 :=
  SixW25P.covered_of_walk lbS 4657350179237343281197660161744496600379537236809704225650992205786235815447331727618821846263539153486644464605390667680633731533163168157361850672398667917471708329822667812657863279322610596902526091704098427848543025286236724784609452101196659114265917948140440949219025397661642028872826540754871353249660911207702308442679519838717419232759365221607506376304699873946285462421310090913322421247760606916935600762798833531565120540749988159506806162454820151114615685567832401524902541671685622470792280299280337487810482897879352731007672382619977971289345821892802862074715578221319673569809886929854772556845218957048398325848458226439629643775370172465862701949408391936586668040575416065831811348543235509718514759561586513819367662549461773897511261914162568547414608651036329070736804633321423814609189126716499221014160790712235524870378907294296383510752132061362572722345469457489302100161060218051351773398065317843172858704514276088898519647212692421580529374145470378135986199061277778653280885512975151327232751553402608335501326956230379111804949997338971859756643964128772547059747370385023256008339280840581000581598439325908315542227361437361102133679073681287521616524044305370784215985828401607715923045486908961375608491137795994046336179606432097754092717945530768508809740770297480736149054194302664808095049048969343711587863054868269098294091653550482216790648470122965412042999656788713660027032571012033724162361368138645649554625296111279765638410581931184040304003949854153891434851185467774011294171233277601197130384053512477534744270459900103811022196254835336418494281386760589118680980849497753252159514353779049821573721422666342269653735259396308072594715794780741519247271137715617574845809381037405165827867587611244527416066053217464216313033001547198960972750557366167702868521907579774794194733849458312846974063485953342568381205832775988547772775505427392348798865797509690195868657654613855350078656638957057939307621359076958684481320489613740498501024044485553716926016354831471547594593576285629326313708807284216805636547208502497054795927253489562631941571793865386801283760515553942462126122787548617973184560021190519053483371931331527425836158569714245487552675993627773034087153462806262150515946016165087389912387493193050278339731804679812375399614678255566907807705465992140868906831803821088975158498005205475453314818466808603758796170025900652403855262360370 21 33152 35584 64704 65184 34240 35072 65184 65664 33152 35584 8052 (by decide +kernel) (by decide)
theorem wk67 : SixW25P.Covered 33152 35584 64704 65184 33408 35072 65664 67584 33152 35584 :=
  SixW25P.covered_of_walk lbS 13977955267923783927587165863633769623788706115308234240449773418623137163745403029527215414726676343261852068348905291294001194826901852612693154140655287535830762462963069393607065725841255329287176682910194686824620750352206616612141026355902396046053091959815508899090937099421873213921098953497048334920326197689740800065244242360400527306498635715705868757880797942584084755153250003474965249698151149311582238482347918317302211560623351168244088462265066803757513465705016037307054456717619330622273442701886438619839552879942651422532432340008288937578457489595189063618369428016897122014293680061993951798638505740833939536461465417233058379847365853305132539950740717306589576908833578735471124052672273829888521877059174577461890240364106710453726511999515449538499277312421082629110110313965268546031855973933186043409355234473312397703001229330543460821369689671042468383674029072299570574015729262724781357939582541302981000572890270326880402969041280359745611933034882581533497884617394 19 33152 35584 64704 65184 33408 35072 65664 67584 33152 35584 3327 (by decide +kernel) (by decide)
theorem wk68 : SixW25P.Covered 33152 35584 65184 65664 33408 35072 63744 64704 33152 35584 :=
  SixW25P.covered_of_walk lbS 217517032629636064587446847128242964247607265108463606983314555784993660639877582667270245433504071396379586168466978138669393237183950840374803843319643047719410491272724230037876167825007358928074526967952745810023924371901246731217641745350980965620050104507942889564904971733047559142025378476792689958086389940640959668032306408984549851383298891311734188122525428525153605539943568808909269043362327266443773989481266345486760836695632445230647954724473620421507742939829534887475759507599679870683011555210545892739327512670620639001822137957982740606467118564324843533567138049152617686388059897562856081203940000565127165952651818429597387303544114130801731168090610026265214068268563551728498552630796373757253636576549566557092559805836526019673390487628913682772362313150103481321130950182339102850750892395703148175780316762063898183129489365339445870280841351465239136156391083163798089676323893931834282391399717409572546350031480304912143099206327744862997719369256071384093784173973377067607448267686859050839873082518808011022803403103643905448439236723858505433219394998537278459929722779063295924154087947520757999749831550400778996080610409486722655726405934139257787942614504160786298651962766489950046264377195334601080400549118761346810950307059711084557064070721041471821401091217303366153152264702656681062697358854257447138171992310165732602892500460505985833574639991322227740245336049517709491969243056627671767797370499735379192589423617910665229101172414342222617263090558995694375629338349118920248491834926154734721450019703257355609604947170760031838467642106756465553152025670211496577359836327376836705123492050871760308872537461295563605091098784500639075067742374574495773690506685566440041021344952920752645466033705391058171708852312036884479244172605076635873524115020560507630134067045275041035256377906995985454167475647312472981771603172133167325887671503351840643526704598886346755212708279739973009928546629704149534891209412524116214111279480726556815167569929717994655602591371100673163415374759567435370397667084505732573578916464634044845977822305089560670535711474524874328035060302243126910477945521446300317079912588899666006573462787882641717591625583097281524748999868290365630303743398045632307322235929708258733508149377409371269401358244973924493782171792276812566518227366014928081737872921880151310857006792824641318584281318769490260205614974027748126093838415711067076754959672327869881083826469509360743336709863959498326673403323869373345768479460666638860904694372650447713652507608080400026388446378682965479274628373759229244718797069422370120785833808176351887981383370075104776196707330374101301114776804466607123735291668463404286159340043344588944082503766618728187403609684941926755698648976349876884543048369798942394977619598752185879177471457283412995333093798213145410480760845730652856760418110593807355810538965020110781504225729669388634578577295633094201335141814569679883493515933406297687120240373371702125143368495179059737255363476448113418869918591157587528625437433007743963844720132254720789234489278022700426859063687551154458202220195039641741890360482300426901251029650750293086621170914264234192286665122898422288109980267948967903023938500804744221251895131533696264074452026479725589990516463406499140631642125945230407532624625325405417587970293568905548452905744580586387849155681486125392570252241794478008434734206528957671664683130884141967665416808716439357940865903773121495210198219143239215839916998386357559497158470736904641159155615376217019957109974422403709418491507457380672812523502818047991761970177609438618943688175638234077798147919408752847541297687328148161850797316536082231374575853684928675376092826542807189349008770316465186202838384895954693626031191933870771598966766033922441722636842808440795782681792351682488569048782271973853318133962510920949129446072080528312136428448304883096876003357581409068873462533270259384804088871078534981114505530810499131776279361197339844397756212091724688572729633319524900348737507212401963949297037236627471018886206348793197606927076017331621525918829031253801037416559139620569652031873173545604579737661263743816792763548339623130525947728122170593468456768562130574729072867775400653752338756020910 23 33152 35584 65184 65664 33408 35072 63744 64704 33152 35584 14162 (by decide +kernel) (by decide)
theorem wk69 : SixW25P.Covered 33152 35584 65184 65664 33408 33824 64704 65664 33152 35584 :=
  SixW25P.covered_of_walk lbS 2885218291812320985661485064172835866259741499059699762957038713891293889210011849719970817241163523565841584722970737732221863246699140389805540793122346894390740539738425213079417622900115266488034252005350445535132894070542947631923893831023897632818703208301644222006359763551537327938017659753681390207591604396636512543014449888085409652594030777704870149202930078003982463211477969208658409336335341532034664907068622901326250053394699391605913359325763851554989323340864977330605168854769799176632526796016295775575609633793084305902676488109122647557636128413542455211417024806472540825325768362199789870750915586712230679258766661475468054018029849382895173689890 17 33152 35584 65184 65664 33408 33824 64704 65664 33152 35584 2237 (by decide +kernel) (by decide)
theorem wk70 : SixW25P.Covered 33152 33760 65184 65664 33824 34240 64704 65664 33152 35584 :=
  SixW25P.covered_of_walk lbS 559410282728476015642675352342170570884872663118230166531039573152731675315856079286883713218330824297309053565750290252157457190623493869925942626932755667551685029529036419625760235250376875150942563309909368534439355172039837627082010880242479206026866261006985158531219804724583150146389143406985006093157030751134987440190246268407860339072636637640600662740902732250795809674277272474116068340304742920917269458292193048593549585946986899881482424700018430760654382368734176035151486848330544085903088316450428171042130329762598089258458237445081823369661657896141836250549560220993359346054684052738705450067561959980037649437088799466305924423459828120911245362250170882794202941071905172009532992499116150493400559092453413155037503035004541203510114264616953687381499648247641515855863777993056723240056516698926234182233615075525980579607466659298999420206931118091867050248532074911781520346916122488990415887808453029666998678790245592876784754914171726022171893362481302692933688702006294335422881538124765448112646471082811283981594912142371667184275297914184430464315831456969497807230157005028610578487968503788637460364978095279565562285594951657573613511274834335005600808059840319472080930832573010190715207939924361016314105428889309760406917383109093595698386194691604550202674546131217991898933017131238281629892716970271905711373759560371045457151053308919166152963992608390701777736689111267460206006074081383489678186421232353603901814573377504432946521571376710019107673364589817791104135254476452082493697976796211148781541501420718158593624086240695038596540043334248097966885124365528029306935898764591901051833378799213472422906217212951733956386757159245534468584627961423026510808666389399400474360345371075386512437233486223441828581256029617984979165482359416891452562346880631283712208614178 18 33152 33760 65184 65664 33824 34240 64704 65664 33152 35584 6072 (by decide +kernel) (by decide)
theorem wk71 : SixW25P.Covered 33760 34368 65184 65664 33824 34240 64704 65664 33152 35584 :=
  SixW25P.covered_of_walk lbS 20049596221992438748388445642393170298575516673161238653068595053623432198312237464226922037138771730694544869757359400894875346228859850277806080116052446358162816484360552599691250164630266324342412363374239222423611002686381923565179678273848375133810018468976990980271744725559833094371737781374878160831486457508695722981821577363083523289073742700335515544196324567935242587968666194549135354662801730430070407175070419849504636108319263331981356592716936449208701962678947462884027471538988837282139156408229443489648046540290847655419241410864598440513817966252758327643252347767070300046282798072849310793715500583824325032997073854214277426721394813208672024606744944946680157495520021816415258786673297169675576504503905939573881178492484274514500828226462558757074469921408638731983028820426051258665520808790728301358108071601801649464715272597409609288378537676851905309878838593451166536445827106794333733551901965990292325655915012113758977048570859983876301548925863367691393179263482181706891855681378134570657485907376006447486239985716698957454468071055601316163740961417928611078789294743927315957856439231681184103157608201958958692852168840601648862556307405283105229255980989477114356255426386125815498678358548079261329271966717051872710583928137870091111458167297085881799648524953595683221728465596331214568485968348273227027728712286794061381284875697012685228925611612306622144598178350543567310931697232376717145064876322524017252903790569275295384690898428260251584718555696571525653003104390268286782576638387293397051210508257725972813247422266305275241985907880798818097456103500320519251354757782460502703369179769504221294194945465716839107591019149220305425268802032372003879507425663699874863118236917484776811759432096828748233614365604978625414241709561200415037080576517013570923911457413107779997175606599498192958249405374769064333395867784117461413433214125034529376931510005636025102634280164231483684766044061705100802832254666203142014763350702093082089059906054607379102578662586798982748807733245916822729379295053895816245746430373889195537011617618506715929619627735547114495089003574290960060687461993772875120167780663674317862995786737645333249996822050337505729563015330768744409073197913551274618176955553872148506910572613568512117960263861129367592515313211949161948593074424689394229828782280926996049450823999679977825821856633056689970944798112099462480509030243403288628902675463422504181368012484229260172303096066134152819430710662861304080536552567806388823855779241577022048197443922578289384339328003492462619193658469503790059261548447364997324122882082184289041208206490137140387172616893586365555446746907210179132405007607068235422437075156907886441195814132419169563252745467902295710311115717382055768084549463756361102991207034717672423481046714236193720782507881366917950399725312326942779936981318211105578509042360751405168991873811810112647956558185829874812056175375771746403221501707279518071299028570182051964496671739421775094746969195150157960989143583888198035161534748577440552053480418409512937638992866528673703716174542998142034336845202607250484031816983619227549470651223949364842268725088538578225675473201691305356098326833907211714763176059324847802883238229013232800254837608073161531782470414734545776802824829345605000718016521975124165489401052576165411421131547647703312955677849787961763115477969628514528313773679627089575697544534122091002465002885098872674997209533521801446629498045950554062482598619891081817564536453665479736483669285679741287383961743043595485151830543461670463353820548088921197846296707559312194892032817920917789341679617850730512512744674271255864164553933869580988893374001049219324893540785802889480311613717624968331397001747712286526771264117632193879614800513151040631000651788311543251310150290967377726591051432074317471885744784962702413288103910364610835015002564573199198826690555701008824835841669828741912843315608105473130340313025635045748373595283232438819407762322910338639442679209395349902530977858924389874584380929667678631524306860308574551281665085084825120652987390938013097172711053237283685824100380306613709695821256382572289993470563946641967518986053322802243015945159680932122113864348656122064823428190867707717729148826563817845536567486523985826295927404993728872877178983331009555810449140520805640409761576857522394300866110205408726085812461154472776999885593253631025849778101529482333366945151955820658117468533999779813635903808568057349953131298450597478005348445802160170213605878688539498265859081524220200259874458095485509034684775360723013483572924305820704412500152911841981065583409663109204660728577628496611889220405564895607774359257806110308150666000226380977826237197870949345693990056189169748764872795124654434818607799391820940610948381723065844360068119136502846127627133842768149444918832948551167074296601721400220397928316513664826065995345378268717913401679129421207773085753094255478919375629570846011149046853494883463311559311950075392090466730496818 19 33760 34368 65184 65664 33824 34240 64704 65664 33152 35584 16742 (by decide +kernel) (by decide)
theorem wk72 : SixW25P.Covered 34368 35584 65184 65664 33824 34240 64704 65664 33152 35584 :=
  SixW25P.covered_of_walk lbS 3583058425586873167341084930866612522477284266736881631837052543885600817012733570968120056130196060025468604267841279566862267532452978973980801286674524606303651070580206128245715890048409456270875993941853490 16 34368 35584 65184 65664 33824 34240 64704 65664 33152 35584 707 (by decide +kernel) (by decide)
theorem wk73 : SixW25P.Covered 33152 35584 65184 65664 34240 35072 64704 65664 33152 35584 :=
  SixW25P.covered_of_walk lbS 1034813466223177227502453201686185436109690823878509490263643835738887882672018744929060469564398448577694855449416425681637364014849984838020741057112504771716262071426703499266582694576648235205404580964186582429177541547133288865303308071573102293115690870468663698135828824183236949047307649513415169806343391194549883906492648671032022405044596236993080724951678802318942457605962792984678124061826967169339712163658833642730956891377654885947931993261357166753081860287245059057411127752892871232287438955163755218778317849300723229124163635069789003197032846609779817893129434727477574942862083851482302124890280865549213415732517817839137775141118575057431941211208135871161064372712099730912486009716874963559380400772516980465669780120772879602197393288848265565520900482537009897447173938111295716549778669537572803833240220836110899931498093600233985949645905739314042086265206639310785206158483165858198022662026180108647171324358437143960410058882119051977043497229517114278010871127537223813297007937510184403103169742762207595946505799600909547910267404550913301119953334648670792936958263198041208682374401361137673734385315659312434736891730829102795630546152923559291969091409570953121422127902956051625495170676152069538967927200407567664727319164145397901204852954494587477702537162675976852735118136545291679355654416128453289011070919987831457191757236290934204629478715017481701267479174641856417845268949655421894739663207951963049093473818756479379966599315278779043262133565750305187399784541493441887861189691515445100067635317677024728355891675755102075701903317191821263161451007304303417420305981318975147984248816843813311913829952485041505886851015450126146391520430085970145651542602975912541518696799344313698190962250938816807671846776574023380228123964887007556572417564551503289041949608059669352038847558496106983130684594808965803794868703317640101174777553356313713710255821772420421675846490372444718691839408750398375255915489440258015858286793851259543804364089192799073473446690815605510863993995536871230622916243223887631175058184776586943206012467200392032476447887478351205710460106757888256281863729386619670904998727535020346758506769345978262035961214828722990635518586835788080457688800808224657502282121427225962420969281781616078210592666856351774169126556814609921267942839675122706148219964843547604506903735748028190755771595732790910657567543206312848162773562932229815538014440051051253987036460888908736231342101138930079606106715226088361207236118653728926710889986253315896438867106946693872051410519524579394462706611770234673733464108197289554164934730274833547802280225798074429957601304106010683014077320088866057226655556082008986758631471008854437853334711527865776310990162865822825160381996144156729247085923727615323208926898911186151300070198091807582888982054896723807108735381301858980233272590814519857664633110021425445538266824654638256951864404202975245509100057309212242897030904012396353611846347061010986282557417818400652732609214034289414872912494247028254641007211895538140897600409294919239471622936102766651403321833631704878753274653803336041658773653620278105671240168925348216309526142748896670269877606651038191621323340906661309596552785375900432180672228025608310220571293028279189845220584024192520976103802225083121580575764293464733299020399912940937299111748853613576299805517150164340641551761948452849184935892187522029941775547701168495523366663930447919710782288601909021359459650987765649560574252216639724954741659617504161149432354 22 33152 35584 65184 65664 34240 35072 64704 65664 33152 35584 11747 (by decide +kernel) (by decide)
theorem wk74 : SixW25P.Covered 33152 35584 65184 65664 33408 35072 65664 67584 33152 35584 :=
  SixW25P.covered_of_walk lbS 733639935044767886900348565058182769929212872205640557611527291982678032515046035253968966707891919216669506453603264838564909307398495974632097876273664932447896891668483029658326060960746046063035089568414087021300103700901019693703371678281785867924897129801147177828529528733642257513884380146431186909276032809502332610554463408731157828874355218277114777723912572236118656498319244565908598485731084275522698628085178252012870371793912013526406151844649621832579248596352520914200067428873088443215687390588211539124170135087624303714751145505450 18 33152 35584 65184 65664 33408 35072 65664 67584 33152 35584 1837 (by decide +kernel) (by decide)
theorem wk75 : SixW25P.Covered 33152 35584 65664 67584 33408 35072 63744 67584 33152 35584 :=
  SixW25P.covered_of_walk lbS 3078419764893896620391705633707280561963018492085820479113282361797430559979169006661733421208638511617285057261669503984620676731129081206506029446161696166082043060694667832866099767522550773193851802606893342198912982695808729872823252312445281767066380543405111265538729905839026504977102092657252840785711185098792256380765192664427580726420380722432894279266560146183456152009210058628832255201776300463105540508723514214208716144804020300967777720096171660314739982447272051065437238249192583889698869658637588318288103646887907318086455997610877717445655765508402009625448157733581054106898352751932651607734876129766564937803685176148618942504385326031408680360078290363021820643252014359821185992043818767965711953956399156557239799741016951281050273521000184842455152279362441722866736759550250613447416563756587211617535526072252499329074769231428032603217186856747848810322699686005183730889156311617867571289034506985835807297532100068201743000395139477636908850407586890130026121970614425183422571030656019887148491135167140304134406120599794578107884011119007270477911340757874469246885436171451909353585703363169689207009764389310353631813871448165710145418797406460462600125071590004075093312892703612006736673542992293794903398486890281234775667603684784869608459434985422332565110229086066202813392535789723380352101542632722788256295960911168349314408670098554365300914556598950251864950231354899873118191874197799451629517386902143578803712763249301474110081874821399365303190686016109595040350919820207262228205463026889329369204938124043623118979697385474744398908754818290249234713288551865265262746954043805326449660061307019224613634634291484298347115285128575478316092191212366881209395117531535130712799596250780326623439221542200489477981543279967379097213020093551874557882516959001749916397547521703434319686405124718070176492673166275973530894895689808514802281795363889136034930305979453307792427607290418611320710834549167087082839249564537471271064239731925419603047798898706389115811282448189404467002116444443943218197122959961031921423600638508077784597887028598299375593906558553670650505405319347160783839647255737255230122104524189465657389154922526442400867795359726764014623719279053967104537210152183883936292135572415349094534556565046895359539167076077240887416404381600220890275085165561632909209628618232552603414681576332444143406973888973616436273280188790187867306002553896760696235841372092481597440454181527372521660376383287575061245100005673673365667630647058784527051660242705581721711245740397212878675185254612355874230656213894413861294379794772412579039512629158089227382261195416796085362508143487821803632494195504378375469972718847575892678711907840955755488308926532097259585638536318993256706745828393710278980872531138594813577658223814289144901977525503427538495578160802343184101248806940643232575694786771828648684227744195396166613493600440175498909029823595731731126960993709749440273539252688001981192929912182078573126127357285715586919226944375723439231250158 22 33152 35584 65664 67584 33408 35072 63744 67584 33152 35584 10087 (by decide +kernel) (by decide)
theorem wk76 : SixW25P.Covered 33152 35584 63744 67584 35072 38400 63744 67584 33152 35584 :=
  SixW25P.covered_of_walk lbS 302766067283831542172556826292612302125147670921181757568202179096561291274810308955856690702772516543412891409753332929270776829442245325652816647648696569771850414970945966007413585857314703771566804803111207011038652876557137626905054388616326564715730587771162100237710241601602762779245113903361222314 18 33152 35584 63744 67584 35072 38400 63744 67584 33152 35584 1022 (by decide +kernel) (by decide)
theorem wk77 : SixW25P.Covered 33152 35584 63744 67584 31744 38400 67584 75264 33152 35584 :=
  SixW25P.covered_of_walk lbS 1840855558894 11 33152 35584 63744 67584 31744 38400 67584 75264 33152 35584 52 (by decide +kernel) (by decide)
theorem wk78 : SixW25P.Covered 33152 35584 63744 67584 31744 38400 59904 75264 35584 40448 :=
  SixW25P.covered_of_walk lbS 4264921640783159537496894797321022568055764059946416393998917707426491276699459011181957427075007486160626 18 33152 35584 63744 67584 31744 38400 59904 75264 35584 40448 357 (by decide +kernel) (by decide)
theorem wk79 : SixW25P.Covered 33152 35584 67584 75264 31744 38400 59904 75264 30720 40448 :=
  SixW25P.covered_of_walk lbS 71978343681073363739667046 15 33152 35584 67584 75264 31744 38400 59904 75264 30720 40448 92 (by decide +kernel) (by decide)
theorem wk80 : SixW25P.Covered 35584 40448 59904 75264 31744 38400 59904 75264 30720 40448 :=
  SixW25P.covered_of_walk lbS 5808323038004315088211358068473423575746884085716323135554087728227682489991438988494519884660422904115689769370521655903719325244843214435018338 21 35584 40448 59904 75264 31744 38400 59904 75264 30720 40448 487 (by decide +kernel) (by decide)
theorem wk81 : SixW25P.Covered 30720 40448 59904 75264 31744 38400 59904 75264 57344 63744 :=
  SixW25P.covered_of_walk lbS 1370572803038797317755839674886606905359316147062385776169973408021313404207487436672359691851797227075796744333621130532013138 24 30720 40448 59904 75264 31744 38400 59904 75264 57344 63744 427 (by decide +kernel) (by decide)
theorem wk82 : SixW25P.Covered 30720 33152 59904 75264 31744 38400 59904 75264 63744 70144 :=
  SixW25P.covered_of_walk lbS 50894092916852392593461555947367098823974841560269331746339888383188275390307881988979707557919472195624221050058333286 20 30720 33152 59904 75264 31744 38400 59904 75264 63744 70144 402 (by decide +kernel) (by decide)
theorem wk83 : SixW25P.Covered 33152 35584 59904 63744 31744 38400 59904 75264 63744 70144 :=
  SixW25P.covered_of_walk lbS 3847331270 9 33152 35584 59904 63744 31744 38400 59904 75264 63744 70144 37 (by decide +kernel) (by decide)
theorem wk84 : SixW25P.Covered 33152 35584 63744 67584 31744 38400 59904 63744 63744 70144 :=
  SixW25P.covered_of_walk lbS 3320270 7 33152 35584 63744 67584 31744 38400 59904 63744 63744 70144 27 (by decide +kernel) (by decide)
theorem wk85 : SixW25P.Covered 33152 35584 63744 67584 31744 33408 63744 67584 63744 70144 :=
  SixW25P.covered_of_walk lbS 14538 5 33152 35584 63744 67584 31744 33408 63744 67584 63744 70144 17 (by decide +kernel) (by decide)
theorem wk86 : SixW25P.Covered 33152 35584 63744 64704 33408 35072 63744 67584 63744 70144 :=
  SixW25P.covered_of_walk lbS 332068724803096519724808226362882718956573996496179879480757848129160061178785093154886325761704063776349646231502596926313459808541325951698425480433420908861012384000458000975821879917101642847018762751519220781629320732791257277433675426480535593542630230266618848946584009181290117693030185830532581863648594644344901928550780922754135442047250595932891050917674982055326538666153222163513343528869531353495553897261152747449260013909125318067438910472933987645210615635963543732838387696469866821297440068838094083735374822751349372219039075145355475661478890178303509420737026632328868320379079206478127960276673395090616325887519130756480205257177687517854172260836782637111541274994960905752600908380049519751803156426569108777980928692437256894959482457416820725411548884817974485694799855583304511786025454174437494060333688547595942344154073097559124814789916243904267511348922132089363568430162518703954833623676231167371075728853663557080346675246507482977569237316048460078867458037402459174540108723797754036358799925029568551913850320061434390022539350973198305644791931166235390824171145669210185895258189112910870554136206864493442191243718933415561121348129468952218813170767932703780301983433987044423542701727321802959202932181818840772745589987044572643775578884039147620549839846615387509773333341962491931695669480184915064134328159875052261685227401648478615454784357626940921873195317614441496239313920185734857326869756593885486853564290613425952045461521412075305902575514278693498221374707968800506000564312164280412824887795367444464808499937091656103017332963817306572260914812317429776593847137167635132959270139153403653358408859767437490497005040554386838527269344981962856769252859791893831778114939728014110529812213444925578900521192377097095305058437461728377668361675478917696798750205185306924461901502995863054312806771667452459572106128163250205507716919695936879793967500587615898597809942408782026660712469014331222577298982585802681550491383606581803064232315282835843035445325467848050677816065621766600006554240503187388901230306880858737051824786269037147501733705481500358580538070944907162688974652953175905527388283737705328919593857415646260007137930393873358338165814834530108759092499818284437887712036969672561156152672048421477501779563826066308261060793844035386250567052395488565936714730598805446853785956296576657468106388278221401552547798671148410441762024125069632237677654281609687648437399737316621884102439973308805946992239963360976129887509233352491979125970037267070459126760831063798644366736448098344707329263235475623524752438947231385862391221329661971938893551110396648947283443681567957958421968354761190141655645709696096905653977003518078252548135259465043963340622869514696861559051591794342405463964173088504358858595517646129497635353009408790469162543395871370535141520733972530807624142371438816740317771385394477430641054510169232679889522845721805189865239278992309757047018466579925270243187444615744731822610246616354697467378394750367937958880110648907269354857562290709570090074002931542975882208960462637670071623177728502955457440562155580915069285782921144771982926767255184573078011906403634143270365101980760606363840443728827909267609799381142898512291038415291885001860321885866359129769815649538816096766374956029197678029759729612707547604547211355962879764330414803804692865823485405934 25 33152 35584 63744 64704 33408 35072 63744 67584 63744 70144 11247 (by decide +kernel) (by decide)
theorem wk87 : SixW25P.Covered 33152 35584 64704 65664 33408 35072 63744 64704 63744 70144 :=
  SixW25P.covered_of_walk lbS 14206321755263192375274573999209560730888257078421585192311690802669123471444328624325512996488910413993916069217353582828932574390807785297628667322268882349187378560406416521599247421876984569773690181113931686156330874018774775433536959564007138241820054712333090358611869446817704011296029512162748838444250471027745757053843011423479086249146020599002579218030472664009397989335561689384640723022778017033066887741774773548124006203074046194338026120491905751584189170312972993481561505012169893174642184489141485636627522950777187954969093846404432697215459132461769992410023396267459432998201879597249638954 19 33152 35584 64704 65664 33408 35072 63744 64704 63744 70144 2042 (by decide +kernel) (by decide)
theorem wk88 : SixW25P.Covered 33152 34368 64704 65664 33408 33824 64704 65664 63744 66944 :=
  SixW25P.covered_of_walk lbS 36501032477192401688515115206240960157459379078700280398530305267728375826866496132717478743226235516561956109255418241563895072017366651121650548268149218506218594 14 33152 34368 64704 65664 33408 33824 64704 65664 63744 66944 547 (by decide +kernel) (by decide)
theorem wk89 : SixW25P.Covered 33152 33760 64704 65664 33824 34240 64704 65664 63744 66944 :=
  SixW25P.covered_of_walk lbS 5297162978213573840789462165339961060171284478022363756675952058681572814567388623042039757187155690589960496209894753169765312061959993365818991965628498280726250031835739430866657052872982799232428335171674771690974762843389972823299105045873752905761734021114644331530416119486320357668639543246927781312509577403614306367727118718793708186731560000581504508849386616829548545792467884931226961681228186530504430429546261287315702099837170238413863154974118486402016914543960342713000221853251051829527328642518114806354471620622667371644413729146276225828219410996211552947518089370085766168144804502790177030467161527949224188258763639442710056296095832239966709799231967832111642037366872554975919078352183115393402711459959125024281709863683254663873611502251039916975632134768101823951590 17 33152 33760 64704 65664 33824 34240 64704 65664 63744 66944 2647 (by decide +kernel) (by decide)
theorem wk90 : SixW25P.Covered 33760 34368 64704 65184 33824 34240 64704 65664 63744 66944 :=
  SixW25P.covered_of_walk lbS 189071809696701085573106775755482462870590064447849281514582375113801349569578394316865336204737159664576167263385672972588540516950987329238930994220921501178991420316801268952661157916757373611840447178757626490279153936869094588710146788754174802830201028062169046999069742138819373579282121897675552784729208266745110461598508546512178591612150401150800282172431878291126460827984635843916407839645220948290680064288232030188866409002132428417300322182604825355661303674512963741148535638773506827730052015352498425614278012469458779196751306155986539544154172096933137406396242596547201661854743292916539862550246530041727830233986446433647697551659781295666016091712977919435087810768217294271893080026428504232873425915490139445038371562746708007903980082740985986182215636364971263038236049183919549126094688808652332939669922676849488919144143682149731591104257265120457737791449653366766074381093154172784761090028713965699173365144385129533842660809310847179259207638011890285255109338597844234073158887172030381875870752463053389645649588203605575539610449894508820468623382832460318562882787635355365057013405692581421708916227893492793753534218787409410487386724204601680829199795451725181384252588633413681913927127306948648138703035307341609529887495601491063559838134310095303006049107223234342429570134482516203709199556825627515897004827084142510107477835196353777985398450937126506329283561489001763890352465045533877446819395470363514052899612675719976632479637063660808636815132188803344772677132909269849761806319028759644663537899578316435935043029180863690726951596820379603194076051050382335558014291937983222844661538341471721992918658076082882971477512582051239281368790924870572140251382825676998222122073010224140977793342976876588535780359577945612862101345590555296443187878401571610913789659913236161521880321867455867499474095320902269249764762057806149186017843539242966928499563893060972822886251127494937742255550261082137380109077053907055029886629756846912592656309119466449128343985849772635386452595632575385786279492732229214390005248884496901902349099655206595495466123060747696572896154596800597710293379972591072692334094811637614849775405122355789271341782970630962331058806572175102138511313650459448331019133917566949968558095400892275823418098937403655892187250103127005329690576610744961071605026310945405105772213069444775220205271493450892120142990858999432923444605058091827031529042480600183154407223308370268716192297773328905482612533741694817660904218158259333033973113343883259463131191009478731793441530893971803857687441757246495177266623664038439670036222734279772203117398388306370991694667428031146348279331763275766203077524237001576324377821253319605145995340026039901305404782221011406857712488220728061065934160471225204771891016667672871664929362956733703220241842228342237746635348059058639513031265829652575033569419339674584418188160286289177590802656540284886530448654599131461556297438441849875797113239538456215448410590926974473262491709912531804594149533640194492002462977451926474927796732479267730813763057573952817388089357180131527816521493331096634360786093354734605561824841202819607345946029237918610524603477754620102530315512216914401176253874815122879876667143642420169346303501249647612185542826029407612687177452682597959594930755302370777215565109818125065576588369527427509727599020603876135373755918547746247255706020241702745378423627410082644225387803742371197986582517362975078475003625084452787243073755889096970031779443329395046095448731757356265381544359192894481832579824645113891479494958110648846171083108836142050001547805039490215130108448924808107512434915952314397633563004397169567256274162770279939516181736231878831718083564133169656816457455138611409637617339251273471157197002785512141982554985794148118174872002664841333761416801143340420457784492341479640950570640647268819002196039235602443025024205588666835529199083608284112252859889407344967849721867502589148417717281744318509155001309408679923487089272436780148682992803583318686183468811106299797398317314371526457828754042105571994744508564840846404719300532378167747636186050031223613494160818021913942141438746832820085090246267299139989196924347334892793756572051311140690078198540539943296627102935281581075290975550104165838867328205420046447739998743556652508469869376541332472817540272320924832460927003747735095891462102810335999068910783838087850861206720666984685882397486 19 33760 34368 64704 65184 33824 34240 64704 65664 63744 66944 14792 (by decide +kernel) (by decide)
theorem wk91 : SixW25P.Covered 33760 34368 65184 65664 33824 34240 64704 65664 63744 66944 :=
  SixW25P.covered_of_walk lbS 84624347160866917323202068113524053069825891408420181296968784562612768695016515766140477076680735941755189512827422954849860909643548854338130018354103766498990757844559477531243818340799899669361086672918932205505091171160102220307610064516398832481660609865613611585254426567853478288497078991774984032632164536582508122679691937027588037335766641189655560960733819023821188559040507123486874536284580305038257832022669071259591389338853335109533138216128595748057876415436626926807869557155467339721808282893493648606918675409648834471343443692040211236949134502197009522345055312618722756016202220335958009525224793881230972581572227352167977310064825567892006258982285559007542003148303805384628491027475158849041655556652221053044767156507994570737547164434646758193957709169561084077425472484857753870467603899365389777516304479658056657014740685900604193931619444065087301175136784186431435689188071956314621690231030443395519171329146814553115448998025733727985076188801142664063828153449717249118799725250892298918102139616307961821282838464173715826076237139899642637625199437918317964404908724050160425626973986594751802436972352634566840262294357649021449864953926901234393753114737479072492216703531488744065441218852841173534911773645571097610365280257158868244621201724031456005567937820198951431484470840745467195736709270659688403104323095832659262933339741826005947112937652103654250001961676148622206920839575397504157186431606909750401471644297418457235961792296093408494568647913511676196769947430853565973407035901204316768588401340144516484832976459392160929612057398515180528409310779543158158641270803777700715853847021804909967159972988870600009526121199222869634085533210565375621775688904195105130505439416246312207139390426953649718096851358225475698665196145087633676591255361805712320195791491468430486280346253496145916423892062299923683815894599817879954105576023152089449260441319051079209966564964795494565544236818558683288924817770795608406259179803202179724074811851925990222092363349369484146882167015802002040488647397796976272365569822261484655733314810828154921820873237208629487162787329648385896268011303979300868087956282174112796918751705872805057665529077970724080440371042572661924521169058717710873356074683435419006767919257664053390876425746080772951213333636872132216342009702570252606731349271051055963132601238294492789498102639190743404718264699516431144279977960427922078327964775668545852562779930282447187703786181594189235365531585172716597313907187364838078283448808595911922792529095981715194080590130830109997400012142296401209218661258728019183412467241537110990255755254031871985644961861538188258506314178242122209981161743631401926291883214431052815727310518977527356114818239345628069372242948406360269817680911847338721066196783823037645952078710437150286411024267083871905389684874685690170491054736724999926506214719873653481308294767849075541981740331225920635086817109112895036724642555198564488854242469904837059744999957314712991345543205779784567719466072688989545453734138543976219269244264731349893276039893641977448987754787984296022011005954152178236600327637768883549159460365133009288918245709389670123614056099139779248681991645143084101927938955140810052876530520717945925118833239586292138954354932438425107026158629735515735737298114720973007423267996048916801687614687572422445310676135846618223557502808021902451373200134522053252510349278986762027162759288247732409199268141238867893358754624941776522366539021262106401507777416733064320083385123348665981396655410106660483589511145471405563919763826403709503528090871315726599508306822724906660114698056258026792081167542190667341535011551243084692945237591563261709551411965822930028553520120528732770429811584158173638868196537505493806 18 33760 34368 65184 65664 33824 34240 64704 65664 63744 66944 12557 (by decide +kernel) (by decide)
theorem wk92 : SixW25P.Covered 33152 34368 64704 65664 33408 34240 64704 65664 66944 70144 :=
  SixW25P.covered_of_walk lbS 246422010284416633560079225128043827718609464970537487737822464901273052997331886091504961180211270027388800929249110706 13 33152 34368 64704 65664 33408 34240 64704 65664 66944 70144 402 (by decide +kernel) (by decide)
theorem wk93 : SixW25P.Covered 34368 35584 64704 65664 33408 34240 64704 65664 63744 70144 :=
  SixW25P.covered_of_walk lbS 65852363292325683440786189201182841740183456363489859543191270762684830875902287137762171863538095356751126889350213103811730111080072204526822503083969757531872737048919688218948745107350168350962041308313229256458854591228360037199945940953770824143305352175729980979679492344218055930019514994757528835577842844078448871138270721262153904222020285558122672688863000370770496303647466747386461523934518623886782797131665994069355758123300036062471000687116557315543692190171998837972945527978338173926554892294033972683853122260424534679714785581832867335853321404600315974250908246911697502892792423811525498185507111971248953391482022500229472858191853187891687029864060351675870850215325681880024619355949851538137435388918499653240240826153590202277779625421822600117957295109346009445320366861948532151492586764568976923507516655668837290256734031344995054721017855594608084581692228901374701978334794702226089757447761348875582491258333389047775949278856874081751823746307634826978393960147185208606711062528579836728472961698783649703197638877775863651122642893297317925421167423771285932619534320597700448172475760585210151698507021671887447264741620688807127269049112007811857307319511337365967220143677686764877072147824998731538925458157446634863218849951613761171749858703314946363455654013077490776653915454080322975796767988410774449228074908678317755414739084978 20 34368 35584 64704 65664 33408 34240 64704 65664 63744 70144 4587 (by decide +kernel) (by decide)
theorem wk94 : SixW25P.Covered 33152 35584 64704 65184 34240 35072 64704 65184 63744 66944 :=
  SixW25P.covered_of_walk lbS 22264569747921183526949378242601193622667759050457607499405638404250319101407698509338872030476297441652653453745756413824385635983246839307691398355621653935836729060097838651017504547075638418209502889343148134761070946886103417607701776316866529800122751142733871100962247695552605716144980140907275728098272966429597277988730839900216288386369283034363427301656604242542283351983362644421373281223709279906133615837413083337035935259061720211161517686183520760843555781322242728340486603992425155228758341404765698136603493591969087544104287320462836907072702543767727433273534765276211926347657796392638896434124134327116909242501961326124145601223061306087079659085906846482567149031417348615824342069823398527115206281854704518447422668325035451438302685892569534040335953563606139873352521324790705210812922550694981611257287958328371584596890481198695977552366548442137372568688508384399705304721349621546083801007758172195965909995863301002351506928720371194760311435314058180221454362319747163110766900855694860479659598579748429499517326159629367616151747506576518386222361756453807086145348870681221229053805494923561306359845032086497525214425923320792514635055773138492888559219233468368749096023052632824984772222800922464355807630125242435483338954003716842689487978515826619530335773179622868031916494753460918480772075461776805064161782158524182669512623409815282942189044229944285399379521015740646549404904674173383350109861206199686339699584786243325829051531307380123080012877806176718703478403561977230048121664517360319003218952773727986843708928553737767985314104654699749993479584817421169182456104448037027379768414622488080498859842224237916234565154422479328630660430525110473734037857989304558040520501421690689686165298989349733322392622938590325509161861995816121513336805460037931237637136134574616361568169796149124597640700247261076130690845314790631555552742357859229662447888108815136144473269059029591527271327753971909631721050651924388367630244402031230684663945983011290313138216704865839782680355770401338482273768874447585819065402552233754009268820904444521324754947348574602625933491107241032388236810056823556478711690140361195052567492968127548667025254711956033144726633149277741892006997223105374257276669303598066570913836192758932614725828444009040920137450148318365636066765226623932056495640116835542617958213574623617971215984872890034680503765826976436698440829570929458 20 33152 35584 64704 65184 34240 35072 64704 65184 63744 66944 8062 (by decide +kernel) (by decide)
theorem wk95 : SixW25P.Covered 33152 34368 64704 65184 34240 35072 65184 65664 63744 66944 :=
  SixW25P.covered_of_walk lbS 1257093623652806631755714386825575023870543627576273996058782829143121774504488682714904204561935278471512361466485731741438410614793477786710654975980768475681449575331431628520336871506276619293016088400392120002981407698044513236232709751686042167687075594138642029179035512375082776090030627874666056082183401392797939331803364694360975512403396307639526371363568669967967879712773701118308837867151470245227848788525082853267818790502702149981465108326726252275851132317855952166179674212237527060606698170626066678044609196160469966467673928271892941018898617542330321642426244242296890864382153913324276292086169222876132840656716990236590286834293211469706749660412630870607691197627142638069184569755202069616453631510178965267480042017831232142830708584949253657616849270128177842435809260620314734502116003571195827440684550224582101901903344885461442491391216626884773433944088133179653379424075160320574267176967352578915131812061946336996877805091503314778838865472255147004155645354763638362098307728837432421878522447910048430447318357246814561495677164830141797449746761760767996043909140850574303841092703789947068506558870045547190394633957470550793199818081768103954242976156357272735693876029262977144810308160621686846571734209636605585722914582830058449793296995909242776345128853870298544666662740277917531085021761215896014097686184119478021112311122704661624248111164336986634750743880054002928523857954165357143846829496328180186326102626971124892368708099267206973590378294785325342220823172967034219751101798224710281751048089959128472563616786078551699858091018344779148434532190292123487246910914039302212328480346565975065698161183640020856873026746622344839182402554472372672334971365915013042895492996933010859825917867559346600904588602419655264379175843224763854160562160070939140003102770290800211456409866855928869720984779993964012710523431253468026623959851947353847377808483130465154571445981585527067095127721946746735507002291221636411913722511211019057853800098466890703198077255770276759293618639203025554641500346123749762029489898813263312266593861081853239338070878816215572289156619316760030474096025029328872885795128812103180215356692777082444823307522878710133892895423538815759446888358327566335204638317899875554228804653502640724793829974214880935048085437695023480268865374495905594055810593669032248107204659427921091571034457371964569443945269013564763291224318102637688498590674996000919142076896660224790887566708451549575946548835196899091221435955766450765928426894210983165309596826323103124817908064402549805529355570857164800555735750016930312353468388855174004291630193701124408679681303865198843914893090220536934676293432782258774545535400152710364477552308270437040791540857099304076874760514768937715302652817240236969146202118429621780449105553682271420906020246592282159807771022471365698344164489834985287816173709466802590919624751907955743622466616565948756413613829523805261554021377244777078188134222471279955508820197164799951242218966923704544765421415738216794595266805451122427731162835674053617523264403257816600521094656695062441718842838318305654859118130089086527054156926449784582956785573432786479089256722728931979645369716261317232198964716876122716339410339863066215062809083504490809398579436203639346356262107298806990987185703970096722725247395667919922628259857818823495242164910592238094767841945512358178983828010339904044010727695474768658100477039861074633746945518764590799990716148711947095047940514900014579107732181972876831018930308895140761136213774664480751027449094365993897328604610736552534799389917455143549021785658930140418132016193014618663743522241886823685282578411938444055616632931845233127052608965271551288797088474934890847833180565016253298670570348196474580191123801498200160450838436478137080164449938918403974170837943867934439592125025719417876878969285041052763581784625285950086514676846752309335039904564840792162284388141942583280079956370707025724395467092068108195829848685654791794467886520631263507592845372038604142158068599893698630780962038742631898934559382584573316986219820322154413305452965409330970420921981564258315661535853143443836731183689629604558487960947701278798149155525363386332700847895681629141237896325459079313410965655937648734488813688902501524491461437196001455735355846274258247377724423149520786897774508649370352699678587120900377833887050827972683624754666984999413786427202278019689784370408211548086350879145432814835398551148754216837288505474524803676456697811614402592281472567352601922856166299201689887695703890979264093108910840869480346566305486420040204217945012781440077085263417930459093820434631470894538235999284329170125192314545787467977961515587222747625920558036403584167268773561958468984900009679637518101712463722684871314547867414148604841006879558009423173568302272283970254950695116854424892038124364488946096592410475976384713212649026034416637327272756264109675130936780504283868854134502488793300207880153713382198391722966645146759248933316233681284679024585890409086619909132635656253375174487487629348091537310237762431700697678808222230657188291317157361371708291134847839231794119405251880419538903862306513713550816565461757618961079467928535893575666923146541801213660184820461648931142204054424174809204808329437815038069981936829791606732898774630203214345390507454671551697208483779537869564818210 20 33152 34368 64704 65184 34240 35072 65184 65664 63744 66944 17922 (by decide +kernel) (by decide)
theorem wk96 : SixW25P.Covered 34368 35584 64704 65184 34240 35072 65184 65664 63744 66944 :=
  SixW25P.covered_of_walk lbS 344013477098953418022684414241228294699802029207098037326752830098026470329840449494900354557879314025749361378077578837890845746443414473003013358146919260888701150170783791820458877983217873357783762432572400902436035519107011815710093376140354947371002723211610128367027510231904409710786117711011916429685711398600684449677743863865632422447286121103605900077700471280155199365233648800122833841908335623857174997310575549557272567726121444499010010312384208694528204597062321618300166185059994342178523778785973823061738761532911548068916539850774964059521821517373875489641930107991010027559304961046189542896693170302742783409743990893098112641971219344760582946 17 34368 35584 64704 65184 34240 35072 65184 65664 63744 66944 2227 (by decide +kernel) (by decide)
theorem wk97 : SixW25P.Covered 33152 35584 65184 65664 34240 35072 64704 65664 63744 66944 :=
  SixW25P.covered_of_walk lbS 6288921361590694234089102656730761396161626401176324372524169275607496578426698994220528847764305564435000117715427335445348878219332162966261740212929301113679356075423590301317113332890346913415591213319182869599112136643517607154412825353123790118116510469196273870973083076637292181870360460351208832026832079554269915060216783471630863111822534138906554334613973735214033551624310591607169359368258159164615821820861435715387753544867388613169726596275053373138418106854665148462975148371634845179549260160736548118522129126829608717490869444873830601619891200933270378120196015939863639127163486613272512161993216577584764695278504785732376955464764060495271008059610280926983439123626092040162314218129591132081498741060893690891496360656431855848824522230495803747164188938114847782396558664495868826203705405565184323884833395732512325667013854146135663485684548897175805794671808698233286585874158616565379193145475336784931310914055955207339973238713464150373393281139503351550501793562827316101036279122094227842035511446095645147581672168240168247244494698603312768749934183579608433834456171752685176460941292507589952930142750402673314019604604540555375749545584500960864731231057849154824467990337123848078502142147075657987408160086158576704238928267093261295068415364346425633953184370300474474179686891097053183414935281698403214364964864231770248879063704602465202963084070366840229920398238868613959088276206137110401076301630133453051942433820620939533461038126887236069785126107581341715511102040903844447384959435090402316977175856094402981253163361541792568203022077805621079459763130397603035130913234600657988566090294056338394322136347993211855630036743844447346118954607492536267848427480749091738445015486741440986328945357355562392483701234404650036030527674454293191275139467093099157675341389515187951961882169563838050508705333239577385144008292120228745244399575074749864911118960571110197271820220863491314887909079665307097959469814469705034552457490516817234882387927846973899990474616429137220193159430893434687320294487212665124137719298650267080415908716674704714496683541947461362516215121143742954886451899733468042816576702721468305296745186017489467189202513175786567854682105309008427221843841406785425113688651516297445694663491781387615143142147233270120810642887766542897264068419774335852181411426612584667299649245583139989797145038851027924842300704591139950104115947684271812722663236285335223511099924595053442329677664152835683055121195432833271556295483522998318040372456997372349251756079795819228984256267874291257651529128148604722875810483506054465666496900667180722107595662865318488317381044663137322885965586293232040235783672377394320380955062683218919456961165638320553056747356862672567488606776997493751255341913462848321134445448019228474104575974881742688945470247737040671598262445001245370278578236072037360262563851796319194180457024922414677607800574112269655198662916831969155152514562505904876315221062400614375624524864554874871845600106667079338397902126227057486409274013046865008596436789335615672751190374466745921183543461633689349270360768937344405041153494512978941083589379565778916359322805833810589035575098684247071306091443786675226646154550383312720547612202520152876069725013486028577762773147361157724596057379854017735935822501831373971934600169720641332964702452117738930585785146584942680203409864290046423144594949778520971279546943047134602465649352146452758161396212346013153682040197315107754865947056800702056015490824684438530401211695836122737094497140649327608648127366298869371036385630598480083266339696290173195446563900186641924589656828004376652151694349980073530612721028044713711550477866115673878123084279103602822927961875364603141692485206170416871932374754983338187365950228674675245714010483754097574027484271707941434152161355574364899754897813201935548411918887654834233199653641546047702555943046797654318489841435354149757619637671659534370024209291754747353254871522233102094626342699245284437794851978459761455060858182167192845979240189810852389707461796139698182793705072061231658138576875708915498179199116613928049666191792380456914450509068664616319689765550794206559459137346155308358045243252994833903303409033855887694046681353076611410857480828732313780692204854997369984139950615031677122245169207492129508329338960867981098681110721064362071914489778702768909259475339307211906282988050468453243174239720202260515620274168912007182811483901994308755793619833670895893161957301678085269707758792310520171884132674631902519621722517026 21 33152 35584 65184 65664 34240 35072 64704 65664 63744 66944 15167 (by decide +kernel) (by decide)
theorem wk98 : SixW25P.Covered 33152 35584 64704 65664 34240 35072 64704 65664 66944 70144 :=
  SixW25P.covered_of_walk lbS 6458591691683823226156168367369340143455008336180257620117785897393596208032909631325692656231218 13 33152 35584 64704 65664 34240 35072 64704 65664 66944 70144 327 (by decide +kernel) (by decide)
theorem wk99 : SixW25P.Covered 33152 35584 64704 65664 33408 34240 65664 67584 63744 66944 :=
  SixW25P.covered_of_walk lbS 701281132131792162454687552732205170330614638547128581387880860230432842504956385576598311569618190474773581443880410998948055435453966257582574049979102881574139797306991567761163710318519372076842422621064529912290701109431715323845110474059671639669877096633445394589203772832233603863017522615583006810900319630398070109022940565448239611657928052458509512163652038996821051251748069689891886366391282100315754298561721267469513197273041501020403135807202676211986512237630160475673986385636606449327498977219235644763247548882925158128684456366745685307179923554546300436694383663622780788884736251909219954905716980228336677214739080411580052362044100495202754010985550398455962952306437305417961905742841034213545669521378613107317462811066092601412288709710163282803996232679645442210140955907936123880209925476777838065388728987962549482797641005999286265626362244207299024002794058428354261766956164229296344435557231856668418245174755898544787319260519458355359801698780887138861706022468544902516281354224975911593483111044855258088103108714374007578267004363068590048042156102538074284733208302352967776425138427107480516502660207145984105304463824063241708766797090579788709935416055099525800960591430487130757154033113798499332975660883720089988845197647537761571964597536488865462665152594748763613768947534504505329814415506975984053313262442495094174975170983014861512013820718148655253088287222487475850768437684100775809957365108837178962367200040750158172486041321037244043209955249029464984072000886081824478129829351228315742396257660239409355216257329884323593169140475390006653492658564037871744426893162233931607756156355348917729275731962025719759753670488556857689705440372599988523989227724077833859472182694161930378942731530029794169011774517520436966549869290285232030665942369826142606160154355359540335910295526672777738067530835701280265501982969882611861256478600700438186135758622022949061758889145278342349967789140555056309753499865728403660124633921925375339596190280880212287676395280037451785532751662991914252979332207627977101310205989727593835320281777715314666315780251876553892068318183887874055036146008043544233367924239532698548206219591813508592273916782474803103678456634727116317941946794597155827756629431283071842027033137155637699477145388355164638765156522933488289799660759236691081345651439671261223207154791404840072693853513337114875497200588183679913199922071112127031871714115774031360931829565840952865423660589611159237372457219096749590248357466230718090650106088532371465866537154092132861573698471115631267738261006032630260918761240760940413148013365609105731799274870299406801957678207457022394368444473163848858356331507342798973516082659163579769180433114038445276510598880388564494806713487526976599736510873330115543839361980442291275955520562813094564422047110967827648236826770709388130724564090499993441764948422243357456104038248446098195253089436386532183322678079878310458482009121759537867965449521236249803073786260325857344153452389189854117467337901369918067279163767050637861153371501711154229002583308364925780546372055390959055275871194847452882909581723244107124607754225678114435126838059514092108023495440536914980607278846974853357746429526514900449836118043481822317132869092141631734816905523943717014948250509553681547513077415826832290511808821011350110716072472692010448290737967862995293003752232581177737639499622066758360732166657244323736867469317644396183630859865532730462131955657780004956192419705748131627585794296392844319906698336564730915844594499092111463827296303883510637119610042112546390739145419076202 22 33152 35584 64704 65664 33408 34240 65664 67584 63744 66944 12012 (by decide +kernel) (by decide)
theorem wk100 : SixW25P.Covered 33152 35584 64704 65664 34240 35072 65664 67584 63744 66944 :=
  SixW25P.covered_of_walk lbS 782537441821551833818259102684214744421805761351639257647774303238463541222150694683602961655295041433698251607348652459882398851959674166783876417511929796555103558335745905958083052089075489428220227280047109050794910273789736174859913399867245986990249576893289614449810781667060802873666453878315922831364274561864092752188341850687748608866407488565836080351837431082572092942869480539620852823319540690677800235911428812279769238083810370401306766329260780233823927369957794777632587280968241724053077404019260182032654795242717538838508579496890559479940329587038189549729692207211414807759695910545278331958677296753200190158323590258699367339824166957943412466242590127076977857173979206157254069901415601315316767590609322311422269322839149122296228030816918398738265025012435023722939389953506567054178603453309610209456971702816829462354352825333647392728567422545636278387145238156089669251231506102812359987816662570611373433644420582431292612417090735035846236536376683966642951930845478425105983062543802086625252917340494951859289909017453109128564238582153605670292879218840812934781627494678820813294657252790754570717196157582142704474853425551708569687565959542039117376826689007258492590119641350441560656641652659864300879156932806429972765637192841672358106243756472357523748591379445810674303105472200687122587489119779781282998879854698406692569552233063452957745360550440593653133069165398167719547340933380152739562989048864826327733690478781352065931507088433310974480215506794400621469691962154666500522567973046897482797101603669655561001987096986098383686882353564404147091047536502744325942808151864063767798227216443890057132821206416816965972321767775044561423169212303018683143706960604027269019303796069441035642277444837392595815393790301122942793189828057572222136303641908718012822223440441740660812778018473927429110037969891686100174963972428547515001617422685656240356154543540103122075468203743530411752580270050044515111460115278590134802317633772486443330631198446530034443509510043926407248334953598013492468870115744644184808594057273557307879992498588031471968906853519383054454121343692077187839334172132341656677816349368013678795012946167713749542772174226995567098725924614531313243449034755291836219153350008886926334943010644892599843148739489017623222897876435938404197264649649751649204004423460659754572466475370217215781847568780593653622949159534 22 33152 35584 64704 65664 34240 35072 65664 67584 63744 66944 7997 (by decide +kernel) (by decide)
theorem wk101 : SixW25P.Covered 33152 35584 64704 65664 33408 35072 65664 67584 66944 70144 :=
  SixW25P.covered_of_walk lbS 3976383978035374929822583119367403036263235282184946 14 33152 35584 64704 65664 33408 35072 65664 67584 66944 70144 177 (by decide +kernel) (by decide)
theorem wk102 : SixW25P.Covered 33152 35584 65664 67584 33408 35072 63744 67584 63744 70144 :=
  SixW25P.covered_of_walk lbS 796607073472395960592112483961754409951163503994758721010219494340922803105191082308736046970553132960256278257932466220254870890877767162075273451604566951078971098242839678640751135054864079056245728291068862087087058634820710500207770100956210755341845950505362485304020565856885340629900178582082076322020347764662728946655863019111440432229997641690009554340017773494337689784952619453533944542821472247303894529663914009062796615074047228065253587197817298878694539776019436541534245234985635432023256175283901566128468246837019876702241243820635880273418626427154636947513579921690718008431943788493681500477413535598448108228936067140440651727096815687706963478941351192135572444008191466540281017857239784229250243373874567936343214102474281401980378576915068976273628532800073682043053574487855629997258091479393098775466997391194021207547530091229134757670958628913112250887111225346779805953248899735748996286223584755103981004432578000845497547763158032384312488979202848451647043560778810384179250526579724307859206668192674186826692953097376544313409063474427210500389458957058871666543285556479684796079656265247646869528243287035242990801750275253810204833638942308049326679848787912338589458984137351301405518695126428316132304910655625393285677531401570177987408963322912291541146021242796674240466751381593763066460666467246295638317774870093336281183435726891090282331974606089809147199191260566757001964102256397615008727360402786491540084042248845441586703169937772328400806453572416516290855861278900025790309282471602882537224960693242839606747879393245204567961402149397270602117388071623171352771999222315551143757321467813111876171905447458516769415681044264537433311731671108704371894740852252225157947517199673711331186998130004830131196502121800734376707282889783267495116340384956668420916639439844074557750460706890455960088223687154786293136588210412412042018273771907121007988934018371531832709083225004953087946607885668903793964597391300865423045068102760890274823123011671087416486545166256315269080200878268073493405812721259139186740314438394345976589477880243542176806794465468792421780134370957445005054628783805988351794336554118175293032860300816545586516490173873480450508818359388414856732505649855410034046663518690573613280095465994714707389954453977666608846896295466 23 33152 35584 65664 67584 33408 35072 63744 67584 63744 70144 7697 (by decide +kernel) (by decide)
theorem wk103 : SixW25P.Covered 33152 35584 63744 67584 35072 38400 63744 67584 63744 70144 :=
  SixW25P.covered_of_walk lbS 11066285704578101144995694044486317292460710418455212358583083321171785863756712230328961979214089902853373160500628937807341871504514157018993342964151997940262570 16 33152 35584 63744 67584 35072 38400 63744 67584 63744 70144 547 (by decide +kernel) (by decide)
theorem wk104 : SixW25P.Covered 33152 35584 63744 67584 31744 38400 67584 75264 63744 70144 :=
  SixW25P.covered_of_walk lbS 196161777505120070382 13 33152 35584 63744 67584 31744 38400 67584 75264 63744 70144 77 (by decide +kernel) (by decide)
theorem wk105 : SixW25P.Covered 33152 35584 67584 75264 31744 38400 59904 75264 63744 70144 :=
  SixW25P.covered_of_walk lbS 4091389078118 12 33152 35584 67584 75264 31744 38400 59904 75264 63744 70144 52 (by decide +kernel) (by decide)
theorem wk106 : SixW25P.Covered 35584 40448 59904 75264 31744 38400 59904 75264 63744 70144 :=
  SixW25P.covered_of_walk lbS 200854100861508979379475457913922901769424770445934409455996270593634 19 35584 40448 59904 75264 31744 38400 59904 75264 63744 70144 237 (by decide +kernel) (by decide)
theorem wk107 : SixW25P.Covered 30720 40448 59904 75264 31744 38400 59904 75264 70144 82944 :=
  SixW25P.covered_of_walk lbS 31257330 8 30720 40448 59904 75264 31744 38400 59904 75264 70144 82944 32 (by decide +kernel) (by decide)
theorem wk108 : SixW25P.Covered 30720 40448 59904 75264 31744 38400 59904 75264 82944 108544 :=
  SixW25P.covered_of_walk lbS 2961574949427505185662982362577132511158618855313450353560005936457616050469793444926734077514516722462219255422439758370682875157468107757085954577556428649542761407122567473849680816381042400937519620640343889506658139783040075964722055181857520450180049514053588361795013091584822431729884639496967875826700266625621625851748858737246418537186391313247133071586573325052238140302065026844697641177283667671339653176429016191444846987325469765601258471515085835778452375704637203569950982982154972223655697572447618272951986545953472817329651409949786565147479701622252632848339394598812170522974675674783939216655558474052630374749710045070456431128418740227369952605011803969424073224289487390939653367073894324214907065930273657754883567415275852615819621803314 28 30720 40448 59904 75264 31744 38400 59904 75264 82944 108544 2552 (by decide +kernel) (by decide)
theorem wk109 : SixW25P.Covered 30720 40448 59904 75264 31744 38400 59904 75264 108544 159744 :=
  SixW25P.covered_of_walk lbS 207841549733846227965652059761284490130447791322424391650100685124935022384393982685783680306 19 30720 40448 59904 75264 31744 38400 59904 75264 108544 159744 312 (by decide +kernel) (by decide)
theorem wk110 : SixW25P.Covered 30720 40448 59904 75264 31744 38400 59904 75264 159744 262144 :=
  SixW25P.covered_of_walk lbS 214053682 9 30720 40448 59904 75264 31744 38400 59904 75264 159744 262144 37 (by decide +kernel) (by decide)
theorem wk111 : SixW25P.Covered 30720 40448 59904 75264 31744 38400 59904 75264 262144 466944 :=
  SixW25P.covered_of_walk lbS 0 2 30720 40448 59904 75264 31744 38400 59904 75264 262144 466944 2 (by decide +kernel) (by decide)
theorem wk112 : SixW25P.Covered 30720 40448 59904 75264 31744 38400 88064 278528 30720 40448 :=
  SixW25P.covered_of_walk lbS 470123718566004161300911528277401981300693006344508476191560371112217608787526041761269389808419954351228792041243544483869221725221535501709116841127173864893481906913613907899228965706576081963167270202667784121346529754593131295021396998607430671523099689828185858413081817979534811711422778269143272472078493422324383325995347686780276753812231659041050272572641415279904889659785398323918645025137173349799591582182601692036693786221914600379608610008333505484319015272362091018697233193653892442075077500351102554632520374778529126346783711071785317775659848058697184773648365446033527319130748567662612186648990594137872423134126131101629869917014249412361887481802569968800893653465185330145239925074916040476057108790602474750283489317334818210919853216190770796562686913150864534792269594927544118717442078747135877349616942899273554592686272319018064080166103564417152056590511251485242605081189799161296410578872583456604714177640405712224738538576522718963240208883359818703892369583779917908181473644548623930872897060177839899184373338350122571732546027864363266299763524956453172095924265960206781412728530677419544724963643957968012770451013525517216733744224044023151669962544173453674130395972227170199339715381710833166138358018205362755618881998695060087121204997236936699352603854604087992152684480529794574161736249233364832817805642761489490415334379531710122890675669538007071178501870 32 30720 40448 59904 75264 31744 38400 88064 278528 30720 40448 4687 (by decide +kernel) (by decide)
theorem wk113 : SixW25P.Covered 30720 40448 59904 75264 31744 38400 88064 278528 57344 466944 :=
  SixW25P.covered_of_walk lbS 1905803519582338586905077530381850300215306736471893135417405550493850216441323888908871240385445516502760867395530893854308340105410430637856624742855157721397373426506501497227939365922537135727547034717518468666545208235638104716018 31 30720 40448 59904 75264 31744 38400 88064 278528 57344 466944 787 (by decide +kernel) (by decide)
theorem wk114 : SixW25P.Covered 30720 40448 59904 75264 60416 74752 31232 38400 30720 40448 :=
  SixW25P.covered_of_walk lbS 234779730491858951742791336694084537859727242823739985688688183108592670158877089129952816914059294441032941270145342378454056618957238573173334990896596886258645389098414595917999449823937653215632766925435189470246813600842890161030488894190622330593990743060751895678276343611879624339023815626438548920101092930295502597279084716825916459278759240998855343673877749151364857793699576329270810493827628743796825947063798562049416521511979476388349005305029423399882836692435881245907539008918668507870331707626878140161537771554478929420300164565202155771515911058733029830518225724995173983005919254510133063679961669687660934230153542455461967566802063946022963852947235870311406159474637784157120237645575508665614004710730418415253286762477923626619302010233832658111762978448530920438175583407297137257219074470191914350908839764513972718604679694335193270923330477529125958326225838913466297444387859986352597689217828861312489937921885913111626597935838129488745196874141661336414045360729207156992741553959557324999418170995210668880742796448166309344317946143051774423511041228963920014337029529377079067989129820712544559670465462648795830641461942162056516794722675621083373837680011890869941087038247445677288530998726558020066415582267155757738312992468652450013542530093973698377119344359014523264694876332782731465144754231368441644342363216281395925272690457045479827742222845171542364825157851247921323780086374635006201520488846394655631145893509504415375106005026277662309512706269209140381792732850425518521404888212944345330169822559611209072217003119677838330496174944710101147405522285205482202926087275171523310396427066385876158194909252855148790589798367817120933076339568591059974364442834426419205914938330294944439605012049672803506001659151414022513790909468275544779799691982575820736064705093549446396080444575414227571215802610854137827485115068000819195099019425535398022779747357362469399701470059946402762048842420501383697688239853752633266662670067527775052111154339352754442421145529726118395635957716402114748944750880788116811458389692513078477356900010567525009991114499948363593050280767865745785218089767561172518204618106480332034963447382768495356157716472445561877311619884335734637292928659633618941169119570240702703699717737599127815631495445432133511939530209998505872456472700110100768751711149028007141512724511981331524514589280860067430114366697660797517154250171425294403471127780940404429247312629938068812311040399810649438605750006687546974615182256990352028054662850825130464353135222853708849496477747035144457958438482394690263827107284689446823086957513272866807583053826406249566125260316133601688088616218054877036766799890137543894931467607145522769255238093051593540718740916302873935723990839706017768148458381453925936432707529170779580699627170246234369485372027094233944183334814427087253079937899086965595825319045661001555882448234589010363200057980120155429469914456136932070658459924528051979054676299545865251331491265353112776197928868951093248100595199791957187750489892542965176174772229394885248842106613487949640037577185564721301880059362484261129328187063280191846023487138780141792868415403550694410583812958378493270926850172911950605158451556477980293566755304174940933898522000452541188393154999239775810014457512152603588266196255009857680042 31 30720 40448 59904 75264 60416 74752 31232 38400 30720 40448 11077 (by decide +kernel) (by decide)
theorem wk115 : SixW25P.Covered 30720 40448 59904 75264 60416 74752 31232 38400 57344 63744 :=
  SixW25P.covered_of_walk lbS 111808655038964522834811268893249625823103860778281039351560163374049362565653684283383309228246315280333175779214628187938151299775797994884365561105397634957765847366014290 25 30720 40448 59904 75264 60416 74752 31232 38400 57344 63744 582 (by decide +kernel) (by decide)
theorem wk116 : SixW25P.Covered 30720 40448 59904 75264 60416 64000 31232 38400 63744 70144 :=
  SixW25P.covered_of_walk lbS 736416788728866 13 30720 40448 59904 75264 60416 64000 31232 38400 63744 70144 57 (by decide +kernel) (by decide)
theorem wk117 : SixW25P.Covered 30720 33152 59904 75264 64000 67584 31232 38400 63744 70144 :=
  SixW25P.covered_of_walk lbS 8921861946428811367806478252965654043003709138311918122292970914885087628326 18 30720 33152 59904 75264 64000 67584 31232 38400 63744 70144 262 (by decide +kernel) (by decide)
theorem wk118 : SixW25P.Covered 33152 35584 59904 63744 64000 67584 31232 38400 63744 70144 :=
  SixW25P.covered_of_walk lbS 326 4 33152 35584 59904 63744 64000 67584 31232 38400 63744 70144 12 (by decide +kernel) (by decide)
theorem wk119 : SixW25P.Covered 33152 35584 63744 64704 64000 67584 31232 38400 63744 70144 :=
  SixW25P.covered_of_walk lbS 44014121589257354197489551630935394544828487756673365249957163284241101543977133785837693695492534942450976175963866205185743720052834381551725699598511638994042080648752258660643800220450198063935400116437465324019547294327237745886632483611742100503224501783675966110507559630869411887256428588421700678729467399363851694470403117352983951242524991799624884141346181097306472679841359463391844958742389784487436269052677924250281265273885791756639534782661814572438055385785131877438893929387122395740016539380735274796477151158882133099117625244247749774445177499361876660952077920055149347599553830978692001827113226400791518879920080139189814158050979162322700112930798346136774691786376752020390905365269092089777973415075658522108172403840404424130334248684221018168096121144668696909854056327940435046193494092535147296086529061324904925518655085212308657182387481717939328800710672045433421185239747617300782665858496686067783834268333851822063622851409316830361878054285095380935569066 24 33152 35584 63744 64704 64000 67584 31232 38400 63744 70144 3317 (by decide +kernel) (by decide)
theorem wk120 : SixW25P.Covered 33152 35584 64704 65664 64000 64896 31232 38400 63744 70144 :=
  SixW25P.covered_of_walk lbS 1136233491666177550542360247098392381290515976267910101966850417676177803055195848246352667075462342491464881781910800667716761830264153838125493655715568287861810233359944668069046697349571906292481226496239211939247363540828416606571913628889313552714125557862330254926734390760282968439315570340953500326714509842502250516165291199094736082034928615177543721804583453588798938645251059985735107924963844121505636262625417109771117960758811406117710835355629423669381344311516083663650948267006941706974844251632403458713155504920089602915169001587460827149731033013057647015524064903476105697813554028350981445003139442707778723258326026538010663587078459327520471816769598519349976261104765712644549033376589337676571817913423217564560253579588529482921727269182424447321292448319775211016594603860254281433696699272347422344846988268842141513739920513386503055776320132076707767319365235319269567283352362325338446315866912481032543569341703501248609459422937250221970769383737326381556001309342981358 23 33152 35584 64704 65664 64000 64896 31232 38400 63744 70144 3347 (by decide +kernel) (by decide)
theorem wk121 : SixW25P.Covered 33152 35584 64704 65664 64896 65792 31232 33024 63744 70144 :=
  SixW25P.covered_of_walk lbS 0 2 33152 35584 64704 65664 64896 65792 31232 33024 63744 70144 2 (by decide +kernel) (by decide)
theorem wk122 : SixW25P.Covered 33152 35584 64704 65664 64896 65792 33024 33920 63744 70144 :=
  SixW25P.covered_of_walk lbS 82303245802062467861717671776905506579920957132111255101418884758799542306904929196780153451736894209058311291894654047181890090469069584672380333831358758850982406862784311633316190698942035089239282285833106818779783744087745961025334097997661610704727906222436875918986383588640459749866111083044058573408575686067565213171539727982328522493627514347372222379439284141573369221905899981570374822647614502673095875117768942075467134350222520913974767731855097787580329162558700316034953792172813338737298722035531597062876650327143163272885444039694467609293648912195901351821841293031732006409658048683031774612815388274352769574000827593078664152733394443049956510845405627384847431877165330076169868233970 19 33152 35584 64704 65664 64896 65792 33024 33920 63744 70144 2367 (by decide +kernel) (by decide)
theorem wk123 : SixW25P.Covered 33152 35584 64704 65184 64896 65344 33920 34816 63744 66944 :=
  SixW25P.covered_of_walk lbS 128148273022253369308601209829405030608908519700605715598182375854359966464905266629477108479843401515549098708615366492856816839117873249442270393820980452286843310755191637438015182091997589871750289573946112429887613893558946399186121179801215401615322854725984265051465743099172296243079652162876689162733676599621545291222732183444602108368551180036018832305604628589156686459138050968160617108671939902233377738950181803191297947023480517741633527988400773531614106861876627017168066033480761924075012231196437258118214634375082029553293585057280014317807229415805729528577516442834648456072055481012024593840660567540455105970384048606330952086386761756761151297816081320389338276151744776000396846365914647457126043035873322383226414499036406746849152601425921450132646242675883754851010122329854216060622570536647590210524352945489430375628519072402530498366644283560189919432607579804655882642003746519029729044215104487517192039590141292746235055526957111147036069249673706185587702228818750089754389147877149066746184136719741011423333802969773362059589716517590686110853583166354495453872211904251086788531628311588072383056172357344634067368642709724287832050613984451637439035086121208600853877103009614685844549877980752936311649366790192852045195393780084023460709718926042683467932833106736511764650672126891470576132923108176127390795780760698546276057863319869150087533824801190789604921090991294947056702839160484840366425016496135882989557478921168994079899621065254495989849718408617938280018090730826464421440318007955589998236275014368257756216603837193578485286601565247314184985232164942145262962031798711242515351358636793241838694819258763590435263406725671471853581220519016906398835515999535729444574497581723927880519919498379554109745302428965327242839222191454105516002882690849861310695265597301695677956497820310751246478544520131654741365709523705341992310830302986223438334309998145226379557962169318360059243386208507417237815246297086319270550218372494920661643248140973548709345267923108387261323219470066606709094978324281645472290239282 20 33152 35584 64704 65184 64896 65344 33920 34816 63744 66944 6907 (by decide +kernel) (by decide)
theorem wk124 : SixW25P.Covered 33152 35584 64704 65184 65344 65792 33920 34816 63744 66944 :=
  SixW25P.covered_of_walk lbS 658440751541381370887508153748756503692751435271882879303573032669469479928139749910453611382329778431734652224519657790583869754182543339971068145595135378845009822511316465372659831043860528924607472754533149500195187159581919835550619741748538626271780438938714708331478401184611381664307593437928382974761378954476533801288208304449666817285966631411309685158673333192746367384015554290809444503285727439258441969806930095147075112651586642533140275517342510554276841427621951443562799772381250855656363759724397690744917222077469258828080118786843361647764493965008314353771077422305193734350631005724176886549473712737768242743548404294363022068915745881618877053136775348286814302436659091142312687589630507667711767805883188936824784026071475900611058146804956891178565956598626083478540761809648458919723054786785400054553990143464983908913540076310970613922700222784813779043393072237610411674603229091497039050084527415480473149532241161179588592549020580092700998320292488040871600969292353600466642222207600657273655671805673736044764113524583775243362984798382047056196253222701265204230133817944604560448609665128938604414638741934241035864434950291895203174856453286349894396162856675303036030496177309843647984567764386447127991247802828458668269824194985203198071070327925790879568723898107244672361398816435739490599605022209836247569833800885838219635358103962109538489681859683141415066981375573887502403843675032492021801291929936798039769589261295036169156998938091648290612320249025494676358307116364336746849351611866000612894172128930102327581807937232613945684043602473428263171588367778722682288320077173475671437191822773481522984603285687238660847016909042230001270872263523399318758949428902385786273727539525505214081977689832406449696555817103517464461322057261599118109285218665991549363924655561355577972013158470262011749253982965362141055824124168070504084356213995187721097264320544609625315565939943200215945308828360229220493875004511219488713563303384048923008550451276641559133807719212649098677066615297257713275861786990650077878921410217466865693886911347497947601917687207222807311911604147251502058518665127002531112845609066461401849455855761883505890655840768202186858209575393715320790107732349559524502399437576967674654494464570173547100358806242984425417906421190441065706142033194980514703063997984039201829142226820117637299442157958706328990599775517788391255251395899670837744876226765331672015453405883480063020687390962254415098982051834708133339636953147800153903803666743054232071215479435538431957578836949433489454587792532828898601470029147360407628655278733244207931632964605385192328109928500832743958121553891407764744345171503359127276526971918095114213070813427166141757201123209557564375687601964841117229908115773595454006294337146779037793082831290395566623271317167742273925719050789878993478391187866417636933135055964727722277033624418616680020101664298527443757895740118001939478812618893395925258341250492147836016101376174408976507085401149787984598724234684909635288371307195630619329933941707111620318382045211517285613393496601954119379799119583846729561590010100750775951218910243200358374877671037683567060906447898366462736039149512367649481037385797770372060818228329365466847853293896333290685529135071661538670138167728262019799211100245425407268824930600276907591203893267231863920006023982716472242381111060840016148454886077836414597110994182966522777719388102001553367954366714551695795711252726111153667527050677431504871228103218727760776189637913775482812538599712592835329788198536118835576768389466051464731902097331699450704349980466097828346086071453846482821797364772717491588116556048105902194058429124985565901561308676181984145374448072020779733081328695585032697010299743083576099552909525247222256827729547375533278608770939068187878393388309551007172423937465271989375736822566354340300861471617390873783248876835238927164256327856020691469713427394355994704917800218208335070298872326297126383436634948145775287874125139304575132917787071137814194050679137339384546497300043907057350901707803317243092930071610283392383947840864887406652370871773456808423091663415498590599863820257221798669234006552806169183642104593090696965670892278877868949720591351598853931726413050932981054217397897501851944377168436467782159945774433155812284755284715292400886541304562101205611136652600230244464933634754332543627436594380022943481436141351130430672543608771876100570218002759614324957722501002736899686931755941369156015039376009643425985330 21 33152 35584 64704 65184 65344 65792 33920 34816 63744 66944 15092 (by decide +kernel) (by decide)
theorem wk125 : SixW25P.Covered 33152 35584 65184 65664 64896 65344 33920 34816 63744 65344 :=
  SixW25P.covered_of_walk lbS 114696763086329088894513219068941796330840183959189133407436624965865744583106349731022266287811720335871834607019556623018880137035539133214952754137336414251457544072205995495052164683968439383833993962062518037575594226312216035451467145362936987687960789689313311262862032087040252625758921448557894934446852255211911992772008984124438989516418983375237193722191474695588783184047032413107253903967807473435814578442447461862152081719928722091257483648118689233015817967613442823526192180801811952430828662005861327352200471170427193443098761373229318851393158983644554551468968448919662044510606581707360762616622914700649135834673812398732914403521500010450554964325662703325765170664911669055127090456077243027482753015719618167098367807660012221852274433130966081165699737028386145121842316121026248550884559902106616182080651623356507136725124590107835059952669565562307364346988003450348179399592314687290564291466967114039992661401010533688855621883102917054722831550392549694506578238551294741439229598329519928380661747772922092661613304620569515572047393802888684977952575849259778262129628438086802084888489848456638310498364121475049176802116159659888643289154478306991896037555710784823737889248063004898191096724674455698721021031094112670020097745222752579074249075063068912177843081619125912665847112818604556911609164731487270268173227873673528144448454642826953773647819334880720895565210403419197455774502755460247953778508147847068190151292824422125590893487666707262914098264441593106056266072330555384730260707668934613745345125340066033125710656103925212804939742022773181735534161366691549179182513974377097289391567007019299990343102899281616987049553796514922686879417656891715749807022391832141549143972410991812725726583870774404899687386498187794784878882885133726533126439039089147921817044110049403836072991033061649699121272197466306564417450126851188268837449510068660057336891397423474507592680857314836392552379666318227576871309053665953664303658990236531974127380319895413515881349646348558382980803851167532876160256736793982747030842320594505194552102901814538735416332608057710632829711096016637836445294652268714303279744452367213611451797594894190354788087938646565991054820834397337655549357103555219710615718811294733861644090806610248061791995186994464998371945513749905881418235091782943694653079054509725743316521571565149601030762776978266099599665990019575667477912675080819194266364395279041685148630413113798096062409701873983246585311166892530322249336283455286262026769514024301242159304830603674020110611433415075286131942123173061551357286614054316790853710972592418151957667707942268933210828356021656176371908889124792491101196404257712466385839925446170586925198408684940086159306499474747065811035150749087046357830752056939449194642203553196975515339403917664808464152008379023406591467512065144942459650755172210685347512384661614765455905755012335498012817071949345142977237617737162588666142951308426172266287079877868082230554610559046348821478623431097855581497770814526107129807901076477229526424102328711460474641799518115917148547337131495214131531102926243789300814208006461645808482353333783623686244935798554214017983511253614424766641933749264274850537933013172994611410250530347839769620646884535049231461771687890494740700625000855868328370473359413490946189739170562009593966784899957154062026992924163163387405288497821195021217212814630451281217305945133626146766029313844924463629970139523234925896697281866902492049580188197840384590496828168918335781620752493458941092514346689452461507796100646969708893641948968820976182749027077599281573822824256798604671508065202149262033481899491986134882030926765114365193900463195343917718346622567701599449456363420193128310422656024610778712926024355719772726926141862102606718551777613955708271586719240543400196029557315214598434419267162443486669978930636181012888180910070557358621144666199148059008065512643391074106796753476865941391031622402675554702799876451269846066911121729996004129701800057907697883434658187536627224393606771660250756145315203182675178216974396375752812512986293483408470725888712455563828770064604102063256970843412869422264481068967046453748769629527763223272919903077416338812784011874629346889668268381628294639950499872063208049657765235098273086845488472882 20 33152 35584 65184 65664 64896 65344 33920 34816 63744 65344 14352 (by decide +kernel) (by decide)
theorem wk126 : SixW25P.Covered 33152 35584 65184 65664 64896 65344 33920 34816 65344 66944 :=
  SixW25P.covered_of_walk lbS 36502156874027983670009957434857174403109601584282238045714728050698996467705361428541710396403953828932051107618882377672498108897199281445128988384266192931593744599069417411090446235549884540173180652622552849959637019361824274051991603627675177944740013749737845542348836046354674911190467357725140422879245408170451577314527065187732274951672553934855714244836037917234474068667861981413171669013117688706977188403806572803526459224893644691365047375888242781346794064305160205529477617259074003129980393092485859077634466654619068587119056100818287507958012430362164963736174806324146015656586859087184284775765720139699331918597666988914912608239031191014449815960209040271387059092883240874140482289299450694153971277153383933617806782612086339492516904247771882679224003294329852645230678406976605055541715265264768555982967850558162782024157249090814777654813521338926291131552742620822908496957773281008041095258590566830381548992765964502204989905929552639852001060988409198253668027820874177867724186439650237437961928921638200042311146642199330776035452143884688904682799687835238448592826446289280447596198830022934776367417984760762974623185315693323446813435530734946032071981752487946469924583035575653983946726449665360774412238351502712852598172572978302215969340233080423021816752630527603638072079896948916978574813305781299106283862386632901891420020132041177735539324279505914956496235714006793399900016104779802848230236530118935703692223187777380226051838386727156615992503932158655787698708740824152282757042758002799957229949180091975682444504461660909342111931818839476405790159860059447588111254620729264510381665249201522557713751857697139747556839116852716544642915498238992848925439969140790270921237017095707465997808015701593903738610548828714897582579772308205752806954030986223690662135872285357018551116359807556008705167517042416289543897212887751336170951414013753169187965224296288034545133590037408490863348805789695337709324678514683947611367295048995664343152408197930112990677128213746077643157237667652503053998055571162380047824464517330263904437285526824968938870213845999095667059318094403986649191628343850404060534700803771762064079536572574824111250807459268725050038140380871700638732932211512401939261399415301799946293750082031731348386790390053737977392306551115267359124196181047216681327704666860094700828311710673684518586753481872407758316066 19 33152 35584 65184 65664 64896 65344 33920 34816 65344 66944 7982 (by decide +kernel) (by decide)
theorem wk127 : SixW25P.Covered 33152 33760 65184 65664 65344 65792 33920 34816 63744 66944 :=
  SixW25P.covered_of_walk lbS 100126379323850365449883124567191673328075961236844564582137904515984801235813778131521525008614413076857279348058171178567367331767031552503593786224172812196350300729746022755677744252983518155222744106842979505824401024684712587824906849881361941251337805312857460995636779541545787723938588745360547406435663971764093034909550154098042391805780028982601036469902806046587128844485742028648769186490315802306414334048155039444849622862475660709256315971644118040516955755322976225070261141886032608549887305626402406702993426100786 16 33152 33760 65184 65664 65344 65792 33920 34816 63744 66944 1777 (by decide +kernel) (by decide)
theorem wk128 : SixW25P.Covered 33760 34368 65184 65664 65344 65792 33920 34816 63744 66944 :=
  SixW25P.covered_of_walk lbS 812406434311395781276305026841884295335244286032490448147915006829382054830145472441908387321661708693314674603278454074986371657419753700066255081184612962698108942456065876915142274814047403021751228651753677963178034121534365688959103236805795027216958608979435243156678335364487934233929483373593979790122612010660286363948841974594778964428627570633373804323882378989046060702653443742170383781051587954641024188327430473893254332581282197851016427278691001470509047125376286541067889123642026292509052357067692917339925470204570482276781772448277207736769985344078097695532745704810742462600122278630615291332875501733317007324705537821565817596823967762318191988693939118144129677805672118284773720195056033553445859153871454366758432650309734510394205244656818343872793867805212987125257990036558055063394363161469924012323127294454870566771170157794146369706574523974860828003988327378559012279709496052884537529095203145733913647611043717575973827270746564223074824772131472518504499358858991842117630812416711410746038258459551480724008734595524784423654581527249760334718353999216701151280522313680444585895063958966928199926964693682070153285188447021690246823632554565510975920761870977169611644892611815963161694533205486680308280559007482702899300991615950765750957983517965119144362201188700500443676315366805672240697197947543561019969277707858948818275949213473258134293896646785598227599830683612928301886194180890898967522759825907701798592481180331187760190592923704082526971050445265886369354790642370358770660420075303130718906812168053474815733099186128621631616258581309891714266455518531584594208480228133737591477505552909828610286114446122014812983944315061396007393920437175522628534550898891762654601493784009216701657847932342325737583677330583180924800171130819446191791830643065708228804674079919842437800227005670928304734643314848215718744998682779849370693247328267964421268759508080170266066287944462140738331676215606394510521122225043653426796075768716445966182767373190887105229420922371666625012621855631343209641595226299985751525847547471270177703013287078728365502667946134541831951446078230077859811997052172974065938301042274634816963116444675267505042355175911681445618374912273766643043703845458863973236579434882747986067363211976485966245586116431868979622582787260505258782994231580954766796308407288640076024937162699256741677446855147975988896791943457679254155822277784847613123689161036476768214669138109767276440101491962446773453907215218713427023516981668953986958900206521257982563872835226363414155877147432378353291310942147142692834083533104332859767147717487742499227892068578118030556585221780438836931476674122567257959852074384810394847039956620605051166132839891715717136769524969962680940430935139675285283965717883237311009371613008942455433168014624198892246865160948730197425874393415021265844259225809189330197407910497951941527949761630335258242780877416602933787072606251761514166816784304615673731877205888120492061394028113895569295978835556520738663550902180969500561292570239777180394761283113649234552323762110804985033966141534386402702420251971032953711917669022742577741003826980793450602681796647536477110222070879862606716637340724943225009721095546958600571953910274804490856968569254711273788385159334377485510015060094916923325316226766450055168195011833668592571294225989932483526097113060067357307416149437700294292491739536266382623531280197364364026429002016091093239392328661494709926467516536286434405388767060048409635829357639211929799376194090824260662048462223720369510678299286337012129623160190556965190852137388459137256044261575322022599438437423377974286423269993492825430796362271965262444149795836730238029763129650293698221978132284194467346205099685493258039576737256168835924887141193537923626467997850900158195310209543418098150533802538947714508227425655736709160111218605981004680770353765113249468424647711857748153693608845670210849859456016213177580962082157501548372374654026462552600915268671418354707252481021758511064425545667104931634777254573048769568313328397049213790025603626523854001372200145114701290957375740526492884320693238853392200393220714854596534914986448431631301145712866492543011359947382798480034112337324886650188304371392978757208762847452095594506702290474181947087398111183552903609065950531311781864363365588493342061122655800045311515651746727173389296835746875800534529274858754773248782213041768492132758969854699187262368119516606740217426519808366483695535475886874114450868660262285811717339599190944838133442073247819075202394040226594842409953280447657344682518104721815104355967036388417439393730384654910459912976403802144238530696844484301494903695763177097307155968482398020195133342289564133178462264915143485647882481481110716968615550731670655868826853760537584088864235558984440363597634899357593841138285583831241573723474487428428263280831872544475265325847975669641244351608722092423009084616453286396981133256604077369756802735300056257349486046788964878878471517877388804954502639274761465015418028458398696041329132499597755126544837172632479722005309289349401576575874442605739307120767774002629780401009074925242526332270246307670176006900622979449206878400232585501703387725077491099407009074123270839342781068264197404833345455336643090211316283762649588038804210786580012085657070537017046980430472540925961861765566053402254647746046416160790711541003004906315900886558210981463693033153904216657812243046706239288381491040168856373139338238827088772163590037623784622089627632574201331901363698303592800760817291593200084757100253680564634325650968055868178613647575573539897205559754891328688697053676174170760446932545467042252113559003545750817670763582486151480198806879357859894311848463734434637309376636032189865175424391321423392562 19 33760 34368 65184 65664 65344 65792 33920 34816 63744 66944 19312 (by decide +kernel) (by decide)
theorem wk129 : SixW25P.Covered 34368 35584 65184 65664 65344 65792 33920 34816 63744 66944 :=
  SixW25P.covered_of_walk lbS 450266952849424230677227665045264530657873989031921819516569189742227005506292061214164408452139977737411140962004929071718227499307613036290242135641950412892914571406820174373553306370962699682454655475463339635932975263489023055638906393449743925245692303412672873624308976268484371262438731879565449120276970958399873596994588977056679137902223867751465591397261279926202006746545151827470294818313952840596818200309807187505180013030019050579704006140036946100053123867466249304042315368886821408801442055506767226876641404468780681353490977960989581224244617248132004565763476089431783671419219807953605269706995303067893256749942281865001366357768937538790891123219810638071035550007764791059172666458225314914351832681979807325576748507180870940327318095225237217019000757971109790002112143539330544418 18 34368 35584 65184 65664 65344 65792 33920 34816 63744 66944 2697 (by decide +kernel) (by decide)
theorem wk130 : SixW25P.Covered 33152 35584 64704 65664 64896 65792 33920 34816 66944 70144 :=
  SixW25P.covered_of_walk lbS 770350086220687160291122 10 33152 35584 64704 65664 64896 65792 33920 34816 66944 70144 87 (by decide +kernel) (by decide)
theorem wk131 : SixW25P.Covered 33152 35584 64704 65664 64896 65792 34816 38400 63744 70144 :=
  SixW25P.covered_of_walk lbS 75238274010780006980599161589168849128741302028933312977856684602104533730302468852213420197978684167390864023849184001682904651511980933602107787826001281435771559339433349165416197787606535041932169926273337875906827986205610065382871710046795183486928989951799316777981303849496512666100893144946807337710 18 33152 35584 64704 65664 64896 65792 34816 38400 63744 70144 1032 (by decide +kernel) (by decide)
theorem wk132 : SixW25P.Covered 33152 35584 64704 65664 65792 67584 31232 38400 63744 70144 :=
  SixW25P.covered_of_walk lbS 717858317292615116679997380846186128317261003275067059213932459973904136755991435542628391594145895577779489097219622281338382437718011091341370057498060007511690112959637122433749755094967207287186818627804805293799780499964053142073205520339753398012808965520019333684799150658159914109308592948049710605553955730227010462918633066686470454093546692491981154700913616511752902467029913178290037991570354738748399682914865991516609270887945048843884019431906477190156236692025103857244465273890669266634669796093680668001594615643606836289420160839872734360948581616584598451911554045374368573800787421298629055793574006956386176350129987130128263846741131200003580862605233435574604141844282469148071148007742390967631022679936654961913099397769429376372426889796895415599084963793545375163576359977232465868996504119148468645912096731997168894802975889574904467430459955342344876970033143379973563892630549688748549454452931230026209931224017225336913172559239225664240306073194432181193031869886883779254915964316669729552049299254690748230682658734747427487912230678649119569345535721728644162510744200578184388710905265525088011572035886859324354896478699135339200023733663115230767085309885484912113745515053938306142451368529978335196915206859290808774733676634685853244161138099366421405141851880795296412824204518712452826259607974905726212173313222799813762963151513117553019255813572763316674421546167853718796489318279508142599663548605608933573179914785260412598639629875636237297671645728412783518141031845360408020738918570205383352529849982205542448839630390850294948658179513014757676442477023717970982245741693037622756861876006885143842037242561571819157026239317385813110378618085231744129217801098424322952363731184477738913316234239362687670214526032090642250215886580586987311907718941116031797947146367819512948945784164676469544330681277903020191403873204339583004654891296164068183353264910713123648676879300355359711831224189517197046391849858553950744960379430506483565775077933247897302859266859362872397991544602532128268811614516538693632794477427264131278061919074696511135252721179216770434101904273706433418696424613865081767713106805177556678546368967528481461391387793420360358651009524489039787408937366473768247061584652978990670816517693897875426852919369363552527069287774166457146657676177009316677761609291697469338766297623136507288377364028931840711583649375303369346112821600848899031565140185398960658167991955061323226331810206191592862124599139097146338048628474887341858145294892000346470779494765344993017287732506178309990813516105385424041467886139906608174601325049029502708215867022655774125375179510264476192987674712440570907031596029197578905081635881265428914855031502481451469302702180921137836858256451557600144366937480041174152797519918459837724028097956963267804763485429809169240335442567835405924662191886672560268108517291488209898149620396747293749342339087004401464221961309453460491922318545662713304539685993424224782359189732901633115928889913376571063658925861006370588021045485561814656073630817574013756331741796342397763073112982695863713611827747118318 25 33152 35584 64704 65664 65792 67584 31232 38400 63744 70144 10402 (by decide +kernel) (by decide)
theorem wk133 : SixW25P.Covered 33152 35584 65664 67584 64000 67584 31232 38400 63744 70144 :=
  SixW25P.covered_of_walk lbS 7515691615283131184352176972116720879468100970567269678803046871213108014135727851660676074461995204000393494923798274530290171242700695941715216800714407721387434136900065396674113778854917659560927519453923651716540715514986004065683603443047877476640700819126562363449959543942693692178479675015822481461072036994554264912858958001556053033468267098564788274351163518347113865901190467987878482746966812951902759128894775546724226703751209283206317680685342707803871010103657375193686918859425615061574387994093638458452318956061149287971144940972868739407236877131801074872111560339024677232999978290352167932481446807990283057789206634352809299222557407855465477537299561221775773591283809266098525319977404218620962448874150174931134287776974857154503766454146156467684904870420733243678582463788086254370112089382226622818447432423543919067399142965002316447875830432726978751125912228343981837178964750344756719955875545421409415924147774770652916260093357074288057675747433047998757735924635174537522061572523661242643458777924824320634983857286077327666751194228772088531932036235997022460495698515963610089179353979726832652856879703014836572777714728336122674083418683036641709205918382304717545660471255209834596100444521199154432704538011926208110918727512057620780081728537086507211314592191755338425314988242903277384735020038151414833942348101424588433236924196408485032462119873011351181413559496951705400792033849491255085370864075357294628092482247382392377186637121093164692604271566268337402561265673374359049464475900711747134921910745483823185144203689191591012281730002042025962238468621784379042059351404355125755656055563460167493519777935642556171916089048002209688509996994564303458079290714123114199878072710507113958911086561041481560327100050354660385403388273074957582949976374384632357667554552777535436033714965076081170926038046892727653260651243220925193438122475084532915876622105167700562195704269777494317698607589464505707330041758301276956231482013636339952164615933012909241302653644510189527159612211923888314312076935758921474298846352993927879801162017666714974005102857028862230234364875198244341206415972878931678878345126225007790264532781655125565041119096108432019486494467431607390340311105080044548595846744094381448202853826309284418959099343197440980247054360298088568786388195608237648875908620439145572183828123552778377364614809206927721934774134542534794215631316385247570694021597245185483315674929311483913403491705871251392572353947604132039950682417754904074434729076001070450846944400399526729022997677893305655777296663228404138590483470069376445747659055929462555753598864069423421764322698869321101738726080603292589699433985011927596802571944660184788643440998497305499473171470585234826358624342584746476349895302191434584687359258842161728009584081253493974284182018458184759947828438083392041705165296484879773156403445488060131365480484146934507194844144904596759623607720988515318559457000701221739275062766251012515079297932607733724286179623174499657613671774636767332468843914557179207728593755569295683725870918918484139081862786879836989111271665847163350473214980232537503726976892185734870110549562392742361256297047594867910445607077585602385497067023467199416336037303751795678630652140196987045810108863952763218620742864996326526231094514964892618066129268283684323254521986822895304001676152841747152889507669415149394221755027150000694540724211536337047547331334627082803667221767772329936246400283653397216852981791530213795852190333770661484511017669601491089081303395414962743633974502319802840969248925106967511516808679674529031727215131715871976075867072468673281719590159777853485410848399690635046751653183665106566867453472798616562606366099708013036110582413852798423864295751328065230184626572506987777278668216278690330859577801712989492848158210329601648276861282584240564828525051166480391202668080427257796334674527481483509525187082279629626526803372919344375143523872106240553628424311273437440297192547663700078627795300737368254316921659262274508288758635881910002988363857391358080153493971138649214578085490334389282893014669545037294442019892372228122750813928150406212709264903864611623381208350241710316667310073305568891007952854680637794188384083768783202264709231644048025911116563533432632933871733822730271583531732344305955367209047023950487650732823244378867056435148858992830089375354784893002995644383086779196778095521228001498636235028648414739457887170966772953942780730904512251471049399677025141665643555415738797612291587575434864925105498377044624219359307696235736645705816634097556428661290829584804920243303789294076340924529062428067712395447428920159201999935273652439133288469841329595657775232727564139879277191741950096022646959316756478933594561621309445574784160660543641869815985697695392013006753693145566602813701466120417582078208811629824909649147001200639265568412810825072554324892827881955950173101003454791814191987032999040291762518115751623833463853210286752932220973339586168240949195002258351734581802493138880931237720644241105891978713960267545730647962243344101872434037359200800475932777229620581805851759165961535345946590513773815035625634935297875883133892373125228103682265329651338945546994306469734562033756134071413437473262693262414550674998104024523616430952706131715248795755152326661527287111582618539428424145170197388149945968137081864226911789363592172623043824318964313327076769662082571631449302426600518707633160990440154742055594 28 33152 35584 65664 67584 64000 67584 31232 38400 63744 70144 18282 (by decide +kernel) (by decide)
theorem wk134 : SixW25P.Covered 33152 35584 67584 75264 64000 67584 31232 38400 63744 70144 :=
  SixW25P.covered_of_walk lbS 384784115461711462 11 33152 35584 67584 75264 64000 67584 31232 38400 63744 70144 67 (by decide +kernel) (by decide)
theorem wk135 : SixW25P.Covered 35584 40448 59904 75264 64000 67584 31232 38400 63744 70144 :=
  SixW25P.covered_of_walk lbS 1486164542890523881322755061683217547792372428636015852384196249186 17 35584 40448 59904 75264 64000 67584 31232 38400 63744 70144 227 (by decide +kernel) (by decide)
theorem wk136 : SixW25P.Covered 30720 40448 59904 75264 67584 74752 31232 38400 63744 70144 :=
  SixW25P.covered_of_walk lbS 11155411643362501840093844474775146 16 30720 40448 59904 75264 67584 74752 31232 38400 63744 70144 122 (by decide +kernel) (by decide)
theorem wk137 : SixW25P.Covered 30720 40448 59904 75264 60416 74752 31232 38400 70144 82944 :=
  SixW25P.covered_of_walk lbS 61234 6 30720 40448 59904 75264 60416 74752 31232 38400 70144 82944 22 (by decide +kernel) (by decide)
theorem wk138 : SixW25P.Covered 30720 40448 59904 75264 60416 74752 31232 38400 82944 108544 :=
  SixW25P.covered_of_walk lbS 24261219430142408641774559514074409127247037069057766181434941941451310574821958269067067533849870289331394557212170502128460146548163563023835351180802690928588506376364124735282967539737951806556629145049310922589563658481134301236248096913274300487927234310047014950988175251582151032356103121068762211433959527924939578211209189182677226355419490523992592634265284656228070153179173410208133138653696212052385226171071846378138107647798208429536492642971189402827732298175708898612006179025211078335385660557153651603388481095781343575850863066110536968868026847493127303244195224555958335068874095315247701890474986759957061237453798067465327418581548055210707663156173090867942684393578030958578143186499746465518210278768008981408339142667395806772675305120900402 29 30720 40448 59904 75264 60416 74752 31232 38400 82944 108544 2562 (by decide +kernel) (by decide)
theorem wk139 : SixW25P.Covered 30720 40448 59904 75264 60416 74752 31232 38400 108544 159744 :=
  SixW25P.covered_of_walk lbS 176582715121353155536317334999545155977161080829042121769686213240403343861042 18 30720 40448 59904 75264 60416 74752 31232 38400 108544 159744 267 (by decide +kernel) (by decide)
theorem wk140 : SixW25P.Covered 30720 40448 59904 75264 60416 74752 31232 38400 159744 262144 :=
  SixW25P.covered_of_walk lbS 701234 7 30720 40448 59904 75264 60416 74752 31232 38400 159744 262144 27 (by decide +kernel) (by decide)
theorem wk141 : SixW25P.Covered 30720 40448 59904 75264 60416 74752 31232 38400 262144 466944 :=
  SixW25P.covered_of_walk lbS 0 2 30720 40448 59904 75264 60416 74752 31232 38400 262144 466944 2 (by decide +kernel) (by decide)
theorem wk142 : SixW25P.Covered 30720 40448 59904 75264 60416 74752 59904 75264 30720 40448 :=
  SixW25P.covered_of_walk lbS 13721751570832257612662923559522937773121472266203492358500845805153342193585961901512407601125356032187353423079485031479413116324888934012585193281981844809199269970245224342034584985424644054763829640780205050833491140754676424312391660744187076952145486119472261645707238838477180615834779954528078495480772608704883974446986717520256017989763576138851667165221178291992439557612924735573213558299355478437402716065932229141741397698453084708529459759693466523986382672495525785682466587565056398771957330715991270132429293606737844017583003242191406549178016240391681179453249184407162521152813209744185763941029942912036273596156601557906537300242029676225549377392364380606499892159026369305720283252155062271832629147538986137496995604840471742949023615878748860332022302066874336982123566915011779230900155596449722388384880930009238659811493075897262798551659655180634972003473920946932778839121705646435599607415352540298997458777278639361384742844883854003339444188866319725318853604268306983061399318528241629365932418310202189587530050184525745148746195768263984305401164142456955573874228939130106745093875845400624015888023278224056372702652026531061507486794003161954289266260469296356153320246642702360738153735280859489768824164444141744134090349922604941771400982133406920614042655013525046561020484898791482816383965547316194402166384609288247578127934104947624129585682505423713241528845242837493724083617624827243269187806104067414765789561437954657023784596451052110694034756516100353407033261378934219411072046552535920868617206916746223142443098153569232417294888166379897186837060751852520195862184853037018826883653629539796253180816731028492522148080178729608935500746117147468220497964960334280447393630153127289196180072539769641684866633213158733417627216161051562951343926475849898975174573386279505289513248723484684986160619098944090011656461305222466950546767142474799703873994340521711580579349588788231659447747547068492066594178003090540105511213439273327557710273172085413383424270234748262978354730928848416912911991661818970349477382589984834292813975131724215025634353215071422195643892084148925851968431656497067668488821660152298907907119926852792238442440737454583111714759742908977157941054312938233627654073722964868720930580328417697427783777884925151505764505893050526042267245311242063014539862896648213032870266341296331989286897727399273431755425755651570880515020425078270132007978883913862672590216089957292831491389641040691597013914491477464467329512769967593662762858715429913691362740457051714456901252638147241676407719667992840386234613732169836936457810094166023927605233844312486722152686226157569717878081175307836113904715802041077614835257939230841374513428160639463575790303622699422609383672950953355126895705754531972383021820931657282182676819280445030009680431473533953599414871963031865930120016701308987228562090 32 30720 40448 59904 75264 60416 74752 59904 75264 30720 40448 9587 (by decide +kernel) (by decide)
theorem wk143 : SixW25P.Covered 30720 40448 59904 75264 60416 74752 59904 75264 57344 466944 :=
  SixW25P.covered_of_walk lbS 498159396494207006397985942948649727216306332991091731554659003855873488874439308012606364965041475784477613110358136549592649455543258286628319827049663220136310252225443164833748868741146172998394514212543838856648600666007935206724678450 30 30720 40448 59904 75264 60416 74752 59904 75264 57344 466944 802 (by decide +kernel) (by decide)
theorem wk144 : SixW25P.Covered 30720 40448 59904 75264 60416 74752 88064 278528 30720 40448 :=
  SixW25P.covered_of_walk lbS 257556431179804612007242703741562606 18 30720 40448 59904 75264 60416 74752 88064 278528 30720 40448 127 (by decide +kernel) (by decide)
theorem wk145 : SixW25P.Covered 30720 40448 59904 75264 60416 74752 88064 278528 57344 466944 :=
  SixW25P.covered_of_walk lbS 23447081251570 13 30720 40448 59904 75264 60416 74752 88064 278528 57344 466944 57 (by decide +kernel) (by decide)
theorem wk146 : SixW25P.Covered 30720 40448 59904 75264 88576 253952 31232 38400 30720 40448 :=
  SixW25P.covered_of_walk lbS 1791285693213593038875289917859512912989601077832897548644309644561115645754107043771955098934701787287103212444311769875716599682866917940249182536912958574880462778449038594078934186384310864653510233769006379307506423539691075604539680617337004898293852842 25 30720 40448 59904 75264 88576 253952 31232 38400 30720 40448 867 (by decide +kernel) (by decide)
theorem wk147 : SixW25P.Covered 30720 40448 59904 75264 88576 253952 31232 38400 57344 466944 :=
  SixW25P.covered_of_walk lbS 30631573335535656269250894833416417686498372846922759546215677285976200412597218826985492022497332408436199780753221637871606038014126895398403617458 29 30720 40448 59904 75264 88576 253952 31232 38400 57344 466944 502 (by decide +kernel) (by decide)
theorem wk148 : SixW25P.Covered 30720 40448 59904 75264 88576 253952 59904 75264 30720 40448 :=
  SixW25P.covered_of_walk lbS 15716982095485957253763186174634 16 30720 40448 59904 75264 88576 253952 59904 75264 30720 40448 112 (by decide +kernel) (by decide)
theorem wk149 : SixW25P.Covered 30720 40448 59904 75264 88576 253952 59904 75264 57344 466944 :=
  SixW25P.covered_of_walk lbS 82454950578 11 30720 40448 59904 75264 88576 253952 59904 75264 57344 466944 47 (by decide +kernel) (by decide)
theorem wk150 : SixW25P.Covered 30720 40448 59904 75264 88576 253952 88064 278528 30720 40448 :=
  SixW25P.covered_of_walk lbS 0 2 30720 40448 59904 75264 88576 253952 88064 278528 30720 40448 2 (by decide +kernel) (by decide)
theorem wk151 : SixW25P.Covered 30720 40448 59904 75264 88576 253952 88064 278528 57344 466944 :=
  SixW25P.covered_of_walk lbS 0 2 30720 40448 59904 75264 88576 253952 88064 278528 57344 466944 2 (by decide +kernel) (by decide)
theorem wk152 : SixW25P.Covered 30720 40448 88064 278528 31744 38400 31232 38400 30720 40448 :=
  SixW25P.covered_of_walk lbS 7872701631760808654693835793732344030399695681715718123829290558739294628111300925975820775613419383455681506686009598602994215926793571512859713492690376923115711668400556846346059344522557266920021838107744753962642262086284058911659827078486506346269271323601788017109761225910470946829075987108491987941538907115996989792137601699556560966508459143698821797390346140939601459147701063584325977430195362805016425633892384154051420186682697694845465877647575474946047711694914431929950559262808604199406453625447642326880458935235709257376092141927333804151311061301006118231726140962724624478183295331204598274245758533188578503579680924764671195173955440243458295651922086894622483224748764725157200281039338174761062152112865856518638238228130277999083285936830033421560816340209055951926797215334 29 30720 40448 88064 278528 31744 38400 31232 38400 30720 40448 2672 (by decide +kernel) (by decide)
theorem wk153 : SixW25P.Covered 30720 40448 88064 278528 31744 38400 31232 38400 57344 466944 :=
  SixW25P.covered_of_walk lbS 12919177000981534475424619219659051879667691732671027090057469646373758727655082206699831580634408603016704371704704957314855131308181071183554449619503632772257608420037028858360730822787879559212394903801331813969126525080054022674833909150759417449802934067989540989367389768584648735386686454418869469686118731523843738465053787004079474013637101508097622763136895597401981701140248104050382776945469000977230124727033629394595297256196436780443838631974630301833091825845034222886045802938475532195080463422623651909655028670330221815023723586492086784143266276020691295817959079924813970579537678961793167737158853178965584070952466855402480140065442386147588702875685512733215022617644367687283851201675714144364904401432176633229359795029024964932112891086817667994141363411468317950788905928757305708429890805978210143710264529465659583437753187339108961253009512374763212911848335824651332738730757755696824834516416004739818027532916149542792621307973079937765286440387896297985250970649950140267396571070022812553567688696629156881950887536931471530860307598599762272979491987742847057751999424158322228134212521716141541217283917829278236439033199370703015638270927717228336779904799503151766879411295054238940713784717374335262548477046241981421615598094514406205174316692923785906713909055193990808897941494919712530759017264451426614092074670247103583260301415704575718983259749087836239179011872857903364232339448182714581633657936991748539542984368302664382122950687428570388036375191549102561607541371277312742085012035198706432230541263913397715676473075806409635818302812908193897211175456547434390826666941708229578669606155293137878423562702533297278145782026142523788821942622355725688504495193526300705443630662634320579344060281458 36 30720 40448 88064 278528 31744 38400 31232 38400 57344 466944 5847 (by decide +kernel) (by decide)
theorem wk154 : SixW25P.Covered 30720 40448 88064 278528 31744 38400 59904 75264 30720 40448 :=
  SixW25P.covered_of_walk lbS 6297807452506528357815052548666872266234796281081002905655698851294773489282487621446046128706183108475308612335497597836184199171250034195677595911349561653256796601953450661397752062785651992005559765939268908179446889924368049762480338999256147534237546448474686243810453781085190167673443942848145072613431231413413343789811769553491396271701597826094926257865116006770369328153083197855914205802191999727322582284568109309729585260117942424658665833385195265963146454231308067625027828030258755543695927140226489733193898057249809899633568999439551827071368812985766352774866025245304110862222977396128924464853699965667363505917206528575313672235188124856184846762985234612360531779281051921406778473450640097241289671569523819811416666841805392886214556492829428106872263864436521894117694495277738460297537250619085039160758129714398331671507790821575908869555719727638728859483871420665817689610453707016110420848665591831638398172561959662108489037414805419315843683277757103623416717020999942763676332188861104331188066092027253698670019919815567543947001940241411863827276638879296973267495818848954008208907218124938369349635392869597446801264092335749613665713671594707308437779727949164327761269682161304886499218177175693593557479713518310683923405621798581821475382914846274515927596698066681713417415445122327837092901338615941695675978167274341311647207934525769557736528347419628348253798 32 30720 40448 88064 278528 31744 38400 59904 75264 30720 40448 4682 (by decide +kernel) (by decide)
theorem wk155 : SixW25P.Covered 30720 40448 88064 278528 31744 38400 59904 75264 57344 466944 :=
  SixW25P.covered_of_walk lbS 84860956619669606677017704274462591780246544868992166675113421515095864644381335279431370432339038028269981885567700190829166438207633722536636135096012256067045363345771036699430548630744094589280662327569909723635376817141622527409256739169871465910684396924879302192899715698 32 30720 40448 88064 278528 31744 38400 59904 75264 57344 466944 932 (by decide +kernel) (by decide)
theorem wk156 : SixW25P.Covered 30720 40448 88064 278528 31744 38400 88064 278528 30720 40448 :=
  SixW25P.covered_of_walk lbS 609996902297664689134261563496131017777214584145261815526 23 30720 40448 88064 278528 31744 38400 88064 278528 30720 40448 197 (by decide +kernel) (by decide)
theorem wk157 : SixW25P.Covered 30720 40448 88064 278528 31744 38400 88064 278528 57344 466944 :=
  SixW25P.covered_of_walk lbS 920197973456399986 17 30720 40448 88064 278528 31744 38400 88064 278528 57344 466944 77 (by decide +kernel) (by decide)
theorem wk158 : SixW25P.Covered 30720 40448 88064 278528 60416 74752 31232 38400 30720 40448 :=
  SixW25P.covered_of_walk lbS 23425106467561239601852604313233178839520822128935296217203786533498237704391645419406796495382998236440109124559280515363221517739366084239770792033081056609225590847109076432571790733684120179837828891667319597651902485888852494307889010777651814093009102438 27 30720 40448 88064 278528 60416 74752 31232 38400 30720 40448 867 (by decide +kernel) (by decide)
theorem wk159 : SixW25P.Covered 30720 40448 88064 278528 60416 74752 31232 38400 57344 466944 :=
  SixW25P.covered_of_walk lbS 41659012563498186578071650241071273668561794303191242303295336454349080324898134670603719070365818342723314257606070755716706110766052510693305185781965869674755794741147298176732767613554 32 30720 40448 88064 278528 60416 74752 31232 38400 57344 466944 632 (by decide +kernel) (by decide)
theorem wk160 : SixW25P.Covered 30720 40448 88064 278528 60416 74752 59904 75264 30720 40448 :=
  SixW25P.covered_of_walk lbS 600897060950117893267765282848024166 18 30720 40448 88064 278528 60416 74752 59904 75264 30720 40448 127 (by decide +kernel) (by decide)
theorem wk161 : SixW25P.Covered 30720 40448 88064 278528 60416 74752 59904 75264 57344 466944 :=
  SixW25P.covered_of_walk lbS 23447072830066 13 30720 40448 88064 278528 60416 74752 59904 75264 57344 466944 57 (by decide +kernel) (by decide)
theorem wk162 : SixW25P.Covered 30720 40448 88064 278528 60416 74752 88064 278528 30720 40448 :=
  SixW25P.covered_of_walk lbS 0 2 30720 40448 88064 278528 60416 74752 88064 278528 30720 40448 2 (by decide +kernel) (by decide)
theorem wk163 : SixW25P.Covered 30720 40448 88064 278528 60416 74752 88064 278528 57344 466944 :=
  SixW25P.covered_of_walk lbS 0 2 30720 40448 88064 278528 60416 74752 88064 278528 57344 466944 2 (by decide +kernel) (by decide)
theorem wk164 : SixW25P.Covered 30720 40448 88064 278528 88576 253952 31232 38400 30720 40448 :=
  SixW25P.covered_of_walk lbS 150881998968693643456893640418982 18 30720 40448 88064 278528 88576 253952 31232 38400 30720 40448 117 (by decide +kernel) (by decide)
theorem wk165 : SixW25P.Covered 30720 40448 88064 278528 88576 253952 31232 38400 57344 466944 :=
  SixW25P.covered_of_walk lbS 337716275784306 14 30720 40448 88064 278528 88576 253952 31232 38400 57344 466944 62 (by decide +kernel) (by decide)
theorem wk166 : SixW25P.Covered 30720 40448 88064 278528 88576 253952 59904 75264 30720 40448 :=
  SixW25P.covered_of_walk lbS 0 2 30720 40448 88064 278528 88576 253952 59904 75264 30720 40448 2 (by decide +kernel) (by decide)
theorem wk167 : SixW25P.Covered 30720 40448 88064 278528 88576 253952 59904 75264 57344 466944 :=
  SixW25P.covered_of_walk lbS 0 2 30720 40448 88064 278528 88576 253952 59904 75264 57344 466944 2 (by decide +kernel) (by decide)
theorem wk168 : SixW25P.Covered 30720 40448 88064 278528 88576 253952 88064 278528 30720 40448 :=
  SixW25P.covered_of_walk lbS 0 2 30720 40448 88064 278528 88576 253952 88064 278528 30720 40448 2 (by decide +kernel) (by decide)
theorem wk169 : SixW25P.Covered 30720 40448 88064 278528 88576 253952 88064 278528 57344 466944 :=
  SixW25P.covered_of_walk lbS 0 2 30720 40448 88064 278528 88576 253952 88064 278528 57344 466944 2 (by decide +kernel) (by decide)
theorem wk170 : SixW25P.Covered 57344 466944 31232 38400 31744 38400 31232 38400 30720 40448 :=
  SixW25P.covered_of_walk lbS 0 2 57344 466944 31232 38400 31744 38400 31232 38400 30720 40448 2 (by decide +kernel) (by decide)
theorem wk171 : SixW25P.Covered 57344 466944 31232 38400 31744 38400 31232 38400 57344 466944 :=
  SixW25P.covered_of_walk lbS 2160828207899017349097951771210471789882765022326904252902084151754296164997479286165822579365026268748937769754487775509255494208397776545096198927863553228268500657929128075999169071457932127700366217805598321773027939448157357427368022235171159575040800165079251229727710481145951950602087332239958549077947759142749675476249230493748117129587878837614164915364247600870289399957742739346776331591475861051856946677651474287408185354262546325983969954290979448021140004805204711210598505436100807614097589837857744208221551444137610024681178835229251515339834020530186743839585634230824727286009123780594003240439872075360640985825236576912254282241843610095840777969475880765296880818085886647345919362915232732316337968609953523512437823898762746049343635676256287154306737491700460058770791694909854150032882737347177821610843627740709371727443180972025564366373137633395319610025822505724318373206614060623144394031958044359509293485973335191704380359401223377309848399656269257111305251080163201334139114845139539924053326977551935950370371252781858911652896289248761715926624288731814874766405318794485695742233343991111907560333442712229153776322235425866818364502980468225656101179953630980811227575783919140773266701862493077272735934098382764340154498747430140165674270034903401082922481832764903429882279924191944866095539376347599655102860024081060500999153495738308791135227633006484113520478612363313282643582404988382702097191016068537856737734687116149054284274653264967994526364625667071283276715219928373399407832912372417721571857771352783911206502697309958185075312933168499015403233458878313524659130027114732177720261453110209618314040008836454875692889465641925102725779052727471100542986591394816829180433784815702979863280167588632910901438823388256772488281573528780190340700843998162382047740170229940743689652204448331563060843605792095358347649751373154047191297840795618511789592365598568310550157080545592357122220909761725099578269911362953086210477268457476223699812806287778703682337303757056425119878988591417676400804418942849713340602676594302583524503011540282918924468385920735469664835540357402671133786205866162611604829897143573778515675378988685584135427678236178307343143428151530356468466704419489136000027475085176696074678010754269063521724899981555108164723569916204741259816000869919553191380647513446092343304680810497287787445829545225399331029368494655024963809787181336143240058802943736726547873360472300458616339671334997071650148552152751469668565715654354023041655796651582385942149792964025908253834278774085229983882391046901877979446042222729359553383371165040010636181284980614514106347198611581056071031237801988784318382272440788073118668366626 34 57344 466944 31232 38400 31744 38400 31232 38400 57344 466944 9007 (by decide +kernel) (by decide)
theorem wk172 : SixW25P.Covered 57344 466944 31232 38400 31744 38400 59904 75264 30720 40448 :=
  SixW25P.covered_of_walk lbS 0 2 57344 466944 31232 38400 31744 38400 59904 75264 30720 40448 2 (by decide +kernel) (by decide)
theorem wk173 : SixW25P.Covered 57344 466944 31232 38400 31744 38400 59904 75264 57344 466944 :=
  SixW25P.covered_of_walk lbS 634841867209506692891907221532030430748099481368706005659830094976518186097373739956029102546482194853828260537929716049272787317538030891495613232125655918756624766613225615716968505051687321055365001871323158608899007702830556186929510291171175543939734456005892005814300254254189071910014247121939158054825137911386327628782680732707724546771680094654176810184929165316732544302010381924034464083126562074995357629472330351919851802087613362656333485090817640872457712708814683887390689671397720123035833086828709987978959749144750115518189517015531198507509267025965654325602471265477347207449195836812169869363316261261594528906800611746607973283521892552988348424310516972364785920599173863839602858667244394219655307541385366222669690981159622691100745230211364554127613608795315335433761584630945543728779464766216051782797987793364662154607016516444451710432621041015321467147562616714622026339582687096838809152854970685043773511113237405080518284569516237878080844982162581130929668760842977836086188165485021493453190450645219813482711867308956857006307001526630133565972239422164541951365239021747386205808532086282456058316296646611111868901413576487718447487823770305354057031681898920323379840416254363012629706646758436484827704335806429801503781506054230423112979887667827019416977379140217302827321442172618153518775239205277297597400381030011750070963288262327475633465117130248115406634309839405490208014721243052296355797886144470915613629225719952015805196910615359711979785743763421272106844838294583087164034477231825756142413513833175915106063869430290096530004951856315036073995411413222665427560539560936769044586366080350853109113906637215388007934525361307129962131109343308962248714234277151104024199011260812849641973201741353628748605633491330296522993919333929758134091904587077262650440384244716769866172420661013405420702507588965134945469997449863737938589553430223896389560109477046189233035839139806818409130449337661118581280955070025278449460546163293050638297360227337850832286017781971343133503666169388585988150236995984711518338214858626418027219738467663598000799882334186437279198668537419436590046088478899909689390126203827308988940126062991653329774074858913349092260173317923077210523632914782022539442343581776702356867421542978411102532922660295228384394075745221352454878428892476536458695318392616980690077288879644835822220136571095006941606978597962004148840888939015754669104968265185294218222568134249347577800958112367502987943744210068570279306540898658161722879175486230013433916946969114435741379184584984623755950790834485544539575826013559492875888089949180005538897937374238606009989352106378453636967863036896743454356173929832142903649889672423874451522693323645701632991996418162662042998122138942248951761423649908466569711350747581745169172834747731981624781528221855737594358704020165141780729310427270209107130357705324964046251557875602553184016188141941913762206577596926223395510569005655838410866960160761693767046256507893869937508544984731600498651872139350824664737735628156032031862949977251417716234275047248601199676858207124032415221268983926297090847647365850965156958258311954163033658044986490357706495632782991378348428986355477124889895777440404580066682017573289504627060837709093496658106487407932284678938174278618384587751211192036655806052005224904668744532701481617379404543802250068202887248640650616559166313969510823449998123922863958531819818094614563438597398381598719366763930683311470498573282464550458428044216545066467537746354837315533933135975754879112135243741907629745226634681228256241240085981033979049096425609484692308528031068493846165447054746466467597894962206831934055236632429870046171762941349463342213254873974561313345945035405438858826038994279662307419284814151128758422218772723585715669225163810408177081078469271604566855495680303133438170498375805810171140079647662460066894018720969031150729177602009860154278524370043068034879129247949900610658936391250994592885683998996092397883255482966906139011403006618479728560428637107707432688811438040435130441306460715289640344582320551315459747121076173231013333087064386410986236060351433556289994907761374050341784440609430728297298148648181659067844007064152830562652359736104409622871285542039097420357430560764432120909942128436117214833982346447152142735145747635592265274426767038981642005738437366703978828393175347623386296293600440722058552192304919224556602587476673045391979896182064027638235567483195792150277810868718913648246227759543111158266888314778230388485163812215395530412233251296952687423845175232696099703330831282717180367146800271274998813728054305398697475745716022106708622206133635341561822800276506627792987302203630528390262996528447311237843562542781565195344126916972734297801783185323396682570209258005814642829979501726316691734035061110963122569250386841188338913525875344691210133833693420535560150220700314086986551687475687719370293570229727023602739125016536648463338219295123733753997970641032597597135821191262849474849407244854943299759801014521304752125166723183507228604716908300220151905445093963197542982518601624466701322351026817850474378733581215521080392796021538 40 57344 466944 31232 38400 31744 38400 59904 75264 57344 466944 17237 (by decide +kernel) (by decide)
theorem wk174 : SixW25P.Covered 57344 466944 31232 38400 31744 38400 88064 278528 30720 40448 :=
  SixW25P.covered_of_walk lbS 0 2 57344 466944 31232 38400 31744 38400 88064 278528 30720 40448 2 (by decide +kernel) (by decide)
theorem wk175 : SixW25P.Covered 57344 466944 31232 38400 31744 38400 88064 278528 57344 466944 :=
  SixW25P.covered_of_walk lbS 13313864188722269524782417889258025542227268261599152969557536960374392041769229788862530809615291699657297888487843952195192942263003632346326167701635822121962382758260705748480932910108368512623111363924910012334287649963636339942784085257326944057746994334009533791881400256532327205470799205982578980211247025798347180896294725598382678533193368748800179622751345149270472388062459317014595504175925343782806889085869212545724194 36 57344 466944 31232 38400 31744 38400 88064 278528 57344 466944 1447 (by decide +kernel) (by decide)
theorem wk176 : SixW25P.Covered 57344 466944 31232 38400 60416 74752 31232 38400 30720 40448 :=
  SixW25P.covered_of_walk lbS 0 2 57344 466944 31232 38400 60416 74752 31232 38400 30720 40448 2 (by decide +kernel) (by decide)
theorem wk177 : SixW25P.Covered 57344 63744 31232 38400 60416 74752 31232 38400 57344 108544 :=
  SixW25P.covered_of_walk lbS 75952611200958018193897099056379074525923815717008813631344540144962249259419767295389657514525908511370215991720444233001801725227763293283291428472626110894725542786368715459063250903992205945897180262705204326422572681708877362674735625663394020627242932640568075667819809765926473231410845924894062214790515247373509293403632956943958294352840811502229691627926661353206794576946 27 57344 63744 31232 38400 60416 74752 31232 38400 57344 108544 1277 (by decide +kernel) (by decide)
theorem wk178 : SixW25P.Covered 63744 70144 31232 38400 60416 74752 31232 38400 57344 63744 :=
  SixW25P.covered_of_walk lbS 4894399431466127215446123431403005486265133594395653449214788346909873308605506756873513103308021003311335596726981959325174470608174457961515097281771340750627197143044847451609915496222424305524453115457475922 22 63744 70144 31232 38400 60416 74752 31232 38400 57344 63744 707 (by decide +kernel) (by decide)
theorem wk179 : SixW25P.Covered 63744 70144 31232 38400 60416 64000 31232 38400 63744 70144 :=
  SixW25P.covered_of_walk lbS 187851826098284200568098810334311858083723980746890321751923928716273393977901977310856206514737167161501541903844094858878246316556811124423213420815423818 23 63744 70144 31232 38400 60416 64000 31232 38400 63744 70144 522 (by decide +kernel) (by decide)
theorem wk180 : SixW25P.Covered 63744 70144 31232 33024 64000 64896 31232 38400 63744 70144 :=
  SixW25P.covered_of_walk lbS 0 2 63744 70144 31232 33024 64000 64896 31232 38400 63744 70144 2 (by decide +kernel) (by decide)
theorem wk181 : SixW25P.Covered 63744 70144 33024 33920 64000 64896 31232 38400 63744 70144 :=
  SixW25P.covered_of_walk lbS 1526143883853665718327847206837619421460636351851626825997259576869845066833184911211623199007871129693978951395088407132260450502136188342640068304889317524906735391919482840861704694730332646877617106714945151247455174533610210433437379198789374883110563853135445828396488911278809501242464475952945659926665003997534054413327886211921942322590231951172131502301232834048745079184546652555258812496679328433557729787605963621442583593701030200875253943368617595422370799524967908129003883837576110055220588114599587809157647527092265773432136331889343411678497027470167246860248989700586365583236704490525032484351663569629764284712632944703609637888662707309824156263887085003793563813193956896644493037523891722522398047283137063804904089204837949340294890297468508207042099302509135292199335275052555614314046583759894964475606024932296769406700963424854289815581161599251379023951312893010130149564437545699451446966516028411002900345014753978803536843883330652351314937813244112418 25 63744 70144 33024 33920 64000 64896 31232 38400 63744 70144 3287 (by decide +kernel) (by decide)
theorem wk182 : SixW25P.Covered 63744 66944 33920 34816 64000 64896 31232 33024 63744 70144 :=
  SixW25P.covered_of_walk lbS 0 2 63744 66944 33920 34816 64000 64896 31232 33024 63744 70144 2 (by decide +kernel) (by decide)
theorem wk183 : SixW25P.Covered 63744 66944 33920 34816 64000 64896 33024 33920 63744 70144 :=
  SixW25P.covered_of_walk lbS 128672906424131373073873854492438932697981603020294528497016094108710213762952925703725635279352624105427473919298139799939592383480453542785446781136222080925538732029863673672455281504163925084284686516936067026186188073532439889194622642037257047288643117898512991130046261240681094966102864474061112616187393571080655920922468464098214602005592583793358504352078392025890775523893895785357501780997484942309612868998415882127496734594569230065260700379133501975248697292841073628936071171251364622500631765690534102280141187464855318618105764358251331794368832161070802152506811576519166586898682940986590334210614547494559257727671537875402673625678004696690279218462288620512997141631309354457258771526609527248890462596968658792934428944215740183832847003895806065626820543005266523135713470985452075232236039631567039903073254545981890386947073741318186506345325533271676203658292841058034 21 63744 66944 33920 34816 64000 64896 33024 33920 63744 70144 2982 (by decide +kernel) (by decide)
theorem wk184 : SixW25P.Covered 63744 66944 33920 34816 64000 64448 33920 34816 63744 66944 :=
  SixW25P.covered_of_walk lbS 814239624886926379077313227328965171062692665395923340711776192060717904476210146416880087508836839844245695369436598307322409520994274880647483467656931927093147138771578628875420360565135357064194959142076836833733039942123845160857654862151108536027976260070124697634939185393177527187270619286118280222675720450623656469564945208834765585168560177963956351486116958753240424598690102584346339885135608135117765196857659034590570371195303363694259701730767088560486544327715059234870736170360822285334920516168337060949351118599996554932018991273426489918994448362363877105183064025293268813478088624043687789957064620157197456391327661561946107684142847625672930261211655359704381499872354513061410401464763084138789016957513617998096259825332580267828815076227022283384158283799399652687634626770328099246606971284377543277242981530335965475597146695716731295117697315835650246330968053388724282545581656058035103251250594571134570564206451923289206738156946723429583567880537258841108473296014055490354935671094711826702635340243906853424969587538074166092667865800036586484300125611785943943192579941952266641740123289645562972034203920592506628960461557699655753115550367157648154217838399742933832870413651671345259536506286039821467810212689347973488787397695637330062416633996680198807796878541203836704125740973769905471593866846102940658643237648916268262469024176439711235725244626371482340610583025085112262005555244193134046213149103666327498777813960552556173674648418192645008614114138377870064681711501491735179174083807218008453603025411690930722 19 63744 66944 33920 34816 64000 64448 33920 34816 63744 66944 5207 (by decide +kernel) (by decide)
theorem wk185 : SixW25P.Covered 63744 64544 33920 34816 64448 64896 33920 34816 63744 66944 :=
  SixW25P.covered_of_walk lbS 14004040810877584181289145910015513578255284544415911443287983132119914544066621221997169760497843509587295176440419783898658668322504005231909658459533105942074317139720253049975089249618588905418890251869202290511807415273007803389778016694932863915793326178955402857236073759069823520883074374920180997967340114169250490053698532873025076674189755145164075272929276948781264689976327682025704590422717502842948478660287199169585507065269470301165918855179976807822289876564631502426331191849909296350562623239424771084976432689927763718793756580025885309698781794 17 63744 64544 33920 34816 64448 64896 33920 34816 63744 66944 1882 (by decide +kernel) (by decide)
theorem wk186 : SixW25P.Covered 64544 65344 33920 34816 64448 64896 33920 34816 63744 65344 :=
  SixW25P.covered_of_walk lbS 77254761801273885343260855935061901948193693018208108164282416467483372194304778415182407133321607981837707012406876417996512095987179335988799324718405750774742694272671128493900054025494697258780284531312014349689032627301607976898903527652650998933163943786819822774914273234686688135137905020198465893587307379011072163011101768014961519008025966703502806350965476316613695209860569836846109046230981698230710766667496477870006089890665717086441492310443519266648791841765555398620563536860966240934953230067113757224249186527436844491627161080117093527396736634414188069925697612759586299743886191814959959703187912340322118492977965251488979348126771737716167107431524328870271759077013038642175705529818132390789728701158820389243133682547637863492114836477753506569482308497683527106208986867404181497978886504013207681464139214104178764248179095269121574060600657867040181313582773585202666696260624047251902348625243820007835605273711715069543458506798406752915577565009711974650267267153266010072735550833358221518758413364898060727790123507947979472580003236430843597000219857743281270469751878188013451620017453748468099074971837341989171145125947086238207724199704987510854791028513347688468498282610568977086211903678296122741370331118058822348584656642137714831600863186090712716194821446438619926234175868016465365477471097407130596279485686792379561799360071847873244244416579201084780344221795517697729996927011393025707359396560939066975958631244470992657204803473675966374192135544749131419716882549742739988853615425961818327988016638750369209252138793508694086509475771744238230915863382236779665961968654313394766588404156931379174094111594409914731638303075964767983421484209562587576906797036883758000085604921331995970552254570876826853134501511810335497261702734311071478020773275815870835882193834368919154684318188224160519838067641169546605377050732208879315465213367442443995444244890077726434017319009629145946082395627836719055102528680254361217658695226969271527583953648412303511860658317553049968715285575506202025772102237135853279690746278291127691222967433296171941306630780078154621600365064614841902030165509457358849143810818726470974068510627587433408265593277761615666984020573425397772502483154654691837992686796237356446790965869869862958716204432835416419149659177635396216985887718544688899311237943318330835328032604693037802505022840678156966224864698475640226077607873673179420766940897058825451030804772026164742328923916742648491849889101199289027378611944242650610047077521912904402729861791289722697612742262758883965036089698571234941054987054667894191536392237330424869230847705719668345678884041922980167206655546167487663768976995994173713475141739481829132244562193180488894137813312026746883994624705240653673214893811232869592673363228408413310154416325997210599606146226604161332107917716910937005857910782355571679912370156104934069146673596509335317017313168812422656847319376929253374767956861690135398524755796354520974169955014336614104776196449894822093673389871741218195142557105600061633283751144433855830411094297738331356684049225710023186076352269858282520703678289327505497071085041543101443041944158620732440297983942037907418356400341689008880116498876416281870718286928334214880723530693319919895330106046194206166347459067325211520665442563836236525536158502411798973638038258793685321764530808571124419833695288233836737882244676962461835012101546899321313489895446786725618639913177630937588000807528256927844135611854611423251735431502473982955769155226173993773296571016544569104856796239019147471698120142605554949914688142707768138509776182309199921458643393884294175601235075531844815735816506381163285167969642561327936821735653170074293700668695100028193219909150253911704744934024762161143991004329526433476662664233652125787241568398777427599474930042066478591184154651515346970368295264235580372239757268747772142303376427092578710808306355776407031795569717160389985518939563461771666806109955576060561648167338576947171483170347024514694719491992285983498205278137713870584838813247954742907257956051179497476080835831513349204034395304950061843726384178351640496742624529702686480931913240727306976924189917825468900149194394452789257146893748039196215326142776297159460580546182867883667955151518977991040253190312188837104230192609889792450448780777056776029933971174313282051193202691919642446680309497660969526517943777045080292557068555368705174995020968674596118954008783840572800376020375160259656492800390446867706903140206828774906190835849784231287451594747923365404848700714450696931008290618940815476438288670352452986573393235057323258374163504566921773170160605350867117622548590425908513009178273909153270093261648314010309294314736324124999523895461298880683686682835311489884709047358346947704718504523806864467095693641787419059378311266674839978346249956909797409458321410927527530090474720696982846156592706313820979177039234749662514660994834351369249723784491371404897181243918197898487339329892993359944636596369661489056388375475369265456336044370674813429994162 19 64544 65344 33920 34816 64448 64896 33920 34816 63744 65344 16882 (by decide +kernel) (by decide)
theorem wk187 : SixW25P.Covered 64544 65344 33920 34816 64448 64896 33920 34816 65344 66944 :=
  SixW25P.covered_of_walk lbS 34415108783209557846804124677124382026694036646599564422722250840886102173143356275519189511251073444299493157095309566476610344631072644448331419396466745953136325226170296373058346793815033645425321000430892900036163646472267849469781363505879561175386766992152347215746437883136194581137677276539053749081719031309688796470379206978162095579025431267470347494059073047476963167487222044120604633906189768783701274659839262680173851868105462930745328868514440571511700606184148414163113658603298900556774652592526019281572156112485474383147995358037040709402960422107066931240439403407419344122647923862214425315825522266168419646994955710054227922485306113231218259674843793246663755432486225581300868576000096415423778134437234456697335204765177527898451795401224857678080813485421468882141373219434546174667002519566509153021466846980466178711906417233935205800574898032812751873419969067454479925028654735816012328535099019504942882656459863276553634778012022099319548916523503863286803574659425623977364808943256303229157431992683436394575660177300849282995801886679375474457467515919400917120356050082292897119699588383532379194301595390279626621641059823462084356180967379854076793273400179222054742938029501581912888334381200315259064705996351978154754357548919008471810874243893049677242180549411450058118588632105344866398486098202486326576618367980720869924654518451333686946427444166296306251189729483033319061977734886426166059092994088808770156388954038638111510488320885196646961938211636873060162700008618582912490547377514426359361800314161136902649914221902927354118136801592125287766706215231571875406248904705419249621933920553801480792475379645975819282837773779702917858056804098191564126479781485304376907168977924521263783738230510123302035482434414138330323872032670320378906746292367008464538016333837277004851102657305417272402609349792684137826824870071215362072311340159715972661306881274311167832568984103197950436256562463125901786944567921563062319709115290298596553670427322054452594278911337680224003114529248234485047416996558437759039469376107961086669887386566528815747975902364014386102719440946483877703518976538119781827770372026020631944068583122826599000356512803343324614009463681477799507756919325071518243506917039578034281323476826891369419885001892401390307837604181270981659166844090400999264952560936964045205747272516436091721738873146095254840218084738499337975113396138796555262919163078198176056854936462265025970513685136603860378950629394236450550904410159925316639367332544819021843829913565408666265120628046351820376923518334779725660002250340383338487377090290939543104315952126742696889809240066623293719900259397735951362403508583102371028894872406995689163055996178660902787125600370072525625155054845030911492201996116493995944461904580697257938928230115266111761270780138633095183928772713737480741287342395069459688963831105401049790025050716207062123241223909255004481590938212908143666952309245508342638229526273119084370742009970264835842079798672400066100865892184542817569049827698187070631266202441753363225111973274262170350693267033655427155008612595181610691948738204124738418163135773945074350883967295202899529851310378210547826509191769372678875950 19 64544 65344 33920 34816 64448 64896 33920 34816 65344 66944 10722 (by decide +kernel) (by decide)
theorem wk188 : SixW25P.Covered 65344 66944 33920 34816 64448 64896 33920 34816 63744 66944 :=
  SixW25P.covered_of_walk lbS 166297479229440103399009869513529030903829451618275728187197077189778554159061675156685148429177274713980224720433008813044164471949380938647736173355956494007209766469176033895612326087631509349697248359970245891401222124713868299941522303514145844860489543910992631119046160126057884922804355939938749842785584649332300457371802585521715252208678895771516954728475778690724679951797528767315823187190084411626830864455327470990922195445788938509539235133552395222798861077025342248206962942652989428059484887294822925531346521409819307754879993969867241853211261559211148751915552326630694585952982309551251241398287045414090879974248834136781281001100184028904164957613572250523832525774494654278121980983350863384991476018187525032677287700145276193368796732752586670491225522307283682118652874219991254673700481721904654335533094700313957451537045693723456007666204929313483659267344152682397754313502673135987579806077030777644774544344784779653799199403889235263266418788195117553263860042491460189946987270927302339038219479389237630282945263950353259283138458847776986910402871965500637957762243380431979134789522747236935537244829595864110031526526989672930323493618839172865523171802777522355161254089098166073009242467766732117312551634061822589743862575834937358347649240016751665424102024738648742800102769501599733257886175403118725234725811221122747914390596532365928500766301033075676773325152917368407463031221011632722569066780231218597610241719941166704280246682323413619176172670760348593476902005433568983429537504048382795457550332975815505229341803336506520732694534067324344555301123879832576847042860904006766957367870765586242531652748541587964539119470516476603922626752886641989615616318202610408097769485078047539793678019826905060200584604967259434017764875372934537331120992985341653282081245852204024084228291828491329920447542569886768828717071923482871957552701763970202611865270580547949898711066196606464287994413840942931502789622355555684267766442281464289978128088663075771127585604199454042555143838773560444984975230867270105113261142133477698699418421494112846177815120383309781879947603542124441123732160308018071719863550645349650961102191864218609616174998434251591303450410222140786182955818906532472257623889881184616238216146808900929678839631234905487503856804317479413498550172972534529719792422979310061578215323494961428573866216155082908320688546946049734010761118554444702406356202807709344662008038309705118075185887747224400616899490388459998484549962338787103463253898036436099672954175194728099124383572225348977616529284937786256967733301988078848628303375161749947905156925915618607945754977781742365981220930552990550109009328629102454704444555982519428289957705032383008382569568647993649500972188312089126 21 65344 66944 33920 34816 64448 64896 33920 34816 63744 66944 9202 (by decide +kernel) (by decide)
theorem wk189 : SixW25P.Covered 63744 66944 33920 34816 64000 64896 33920 34816 66944 70144 :=
  SixW25P.covered_of_walk lbS 20429034703705578027543346 11 63744 66944 33920 34816 64000 64896 33920 34816 66944 70144 92 (by decide +kernel) (by decide)
theorem wk190 : SixW25P.Covered 63744 66944 33920 34816 64000 64896 34816 38400 63744 70144 :=
  SixW25P.covered_of_walk lbS 642554932441122596046127467453558704325907280204626666522224520376136605783831379721078175434079278197699222324415898123222520360685645810843569066200159787288919776340914926 17 63744 66944 33920 34816 64000 64896 34816 38400 63744 70144 587 (by decide +kernel) (by decide)
theorem wk191 : SixW25P.Covered 66944 70144 33920 34816 64000 64896 31232 38400 63744 70144 :=
  SixW25P.covered_of_walk lbS 29106861521983397993550312465109896930 13 66944 70144 33920 34816 64000 64896 31232 38400 63744 70144 132 (by decide +kernel) (by decide)
theorem wk192 : SixW25P.Covered 63744 70144 34816 38400 64000 64896 31232 38400 63744 70144 :=
  SixW25P.covered_of_walk lbS 18043762037102092736090741275340413525572105976430149484394694029090139293993963661959410817420075015535202432495392676663658022578247706716715017486728318403773448095938743641870290160921878933529359972253502796404617069485009311005808487582171349718988382131184700111343798846098197929976422 21 63744 70144 34816 38400 64000 64896 31232 38400 63744 70144 977 (by decide +kernel) (by decide)
theorem wk193 : SixW25P.Covered 63744 70144 31232 33024 64896 65792 31232 38400 63744 70144 :=
  SixW25P.covered_of_walk lbS 0 2 63744 70144 31232 33024 64896 65792 31232 38400 63744 70144 2 (by decide +kernel) (by decide)
theorem wk194 : SixW25P.Covered 63744 70144 33024 33920 64896 65792 31232 38400 63744 70144 :=
  SixW25P.covered_of_walk lbS 1483241845500370862954535050678518648526307043862690456090631529479201532106042998160066257172513235591128329703767309622002960797632846239919787657365585437985958241032168218161250249147192031091470323856467485048543696512566705650408010314459063520544068047882227344106968531704083841328827461651429014939124951494384511229956083229589406337609019193828480431379892615960375692226703142085834029702636811507480402263008536733151390900815910447414530774270233410521169421424712783720481241547852207801412896914042921614698414081664149608749436306457724938719498745737608535769668997996174895563069149835537814984436423529653993444867634922120472537914661212633024431344278354329226305828595514465165940011192793413915973802830601534190054315536225375647319306571319724696798730808888200110204434963153359606023589177625454671337109179783767024812850335380663229342127712487783400424734783719493096130903223942160944498742429846242937339587518342179164987857150765931895352076423387800148616274466021364757749976639289448053986428302698197405065870330908912811918979871487406222827329952701723050811356891248669212637458360447324047570666432538872838081432853118624184012567043371285333459048881449034648696165329356928699018886465174386095897197746461633124551649642467845709031364293365506689421487303596869961929645048776979610875476786501541244093153798776068042057920061410556642940053960598603502704719783625558182169408933177173748235535022878949694861953869733289080801241251567000863115611556122479982935306922747589502155715219418887874408047366316180125631838155056307401924051937483684337778565474800926175946466293126398857095074823749652646131904339689338247241177062866288344204873082268953434088047077735360467157810443934573141508710520288411197767221927119880088219000117229494150759356296283439806678710550639561436385009976572030851896350335130258886296212942788249038691828620621522519351817481669866629023284914439455855532720533370972942996119261102506063719496739067124822579371550021407233018893568789520946516214152839772049605583291354002685001892584029279940383377000588566155390863852514618027368894580888655151008345989683129599964567167159090933077639253565543463889223769794946894042263505727098700147807843410777186456224764739293311672884050402240299461322214340372321268057638425166033476963813203624926577414249013041283304840707634461323578306400355812312589381030809894428127987363165494596040227795831012201467009553476923266296545523784018389829740441419568571643136472305567779500279304414169003060185029691625294855611602298855880787863200400876401688709764891267220504626794827614923717010645434280126861206799070999633134 26 63744 70144 33024 33920 64896 65792 31232 38400 63744 70144 8857 (by decide +kernel) (by decide)
theorem wk195 : SixW25P.Covered 63744 70144 33920 34816 64896 65792 31232 33024 63744 70144 :=
  SixW25P.covered_of_walk lbS 0 2 63744 70144 33920 34816 64896 65792 31232 33024 63744 70144 2 (by decide +kernel) (by decide)
theorem wk196 : SixW25P.Covered 63744 70144 33920 34816 64896 65792 33024 33920 63744 70144 :=
  SixW25P.covered_of_walk lbS 213300532130078669543582285154978941390290441027173358822200501558266791921328340048778476840741795247344428672172229067001699813953176300057324298202405827341103686257843906876269882314335525114318176687864700584867437183209109716345593542248580599889479519937450656810695527736337323217480955720786240419336733423629484410472719449571173516955518580937979863591138955635335382863522890971376011246815845193690308862503681915426459322024548218133121101796149961540150815264328218739086447739049161937503655002382400589682235898896749506928332877736171898428543118849842079900514228064894626444911706131535107773843432161807448171731331711708461525890743291949070027095015243870831414162039572611752074125246822051854077181511264748996019859284514401699335692375823035538726241795555338801116144160854489179414520631823377348110327247324411339126240775221335542554984326891210665321679201363964984170070440542873179547101740208675732645497479998883868190498085035372454845288799876082068710237653198088101552562118208845877450701365039046177784909944173503841655148071651371227545564005417870423068931374495531586973235473186585574257263014926673003793156466941067798170753618411519246059500026281044889232102399432704043893894951064927643808037783097033598413175164666646191026546758210352346613345260915597030394270700093734232886309231729360477704753241397161964223890848732429168986028088704181374944400916100471715417941063127811727055323008187938623962213582460502533846087861793681406832832263492368080876127581722612687126848507930710939332235019887102138287551130307058664318605101127572399245769821142157247387526568872471363644178332415717527968989588925542711588813897281508581196510108704432289625604121787438854471005321276400342244778530436600543109753602856783478772070424940686014688144410662210280307998420584826565329277288168012099168311895529625536341871443687966976981764524291582436619511792652183552354622276966495328741318651763734875105274801815509462149952047272203574810647596504237834691322418539382294847384243781315002809663029605469024811730976717837822499842806025807315955880741891288176670390208912226580901140342647368298246980997965163156718148649707629428885352402524458571095662767239704039254696623846536399757651155341921338911543792843205285692665937911837298659844157111446066009610985765077473608513554832310897478527012798427386112124902503781528053724382201326257720962850 23 63744 70144 33920 34816 64896 65792 33024 33920 63744 70144 8037 (by decide +kernel) (by decide)
theorem wk197 : SixW25P.Covered 63744 64544 33920 34816 64896 65344 33920 34816 63744 66944 :=
  SixW25P.covered_of_walk lbS 232802353053148926873563579141939470600641753106839754062695282977486835718613170901226926058271708532698973730240693585066210564592218926532500160082942831117213263179608194832411273772896723061567608691988235722119317937766619156390927306484728898426966835014386431599517103587583567236573589867535324862661251828544721170996726108378179325094047124088580473293411773429588493485666290656203300543003185438293119116895603092569283133861122066509766631996041141316647757483479356026455785475529363691882172233310049690446375567759822236313550786621948709540320218932152719880089699301333481388845581752126027884478117789561501514306442642535883799787977824077890953426025923304215950335161872094718760864258375951186387229967652876669933229103562820648885844841242813025845893366333967608888875675023874942795822241234974084238601540145521367167417563457356347220342636120076522284257344497515296809865470915301796211892189777195455485675745477607026047900140918786239577527610173234 17 63744 64544 33920 34816 64896 65344 33920 34816 63744 66944 3272 (by decide +kernel) (by decide)
theorem wk198 : SixW25P.Covered 64544 65344 33920 34368 64896 65344 33920 34368 63744 65344 :=
  SixW25P.covered_of_walk lbS 73534353943803499868675850919695848974048078237279188020160578628892301615790958540711640808072148665485793186707641580316666983307711710829030311824824025258793554261501000367276362303005857418296870384314474439625883957159342272461232908757730327960481572327632671457933440734738877001313911188163773891802534360143645159663656987412024515668194889399585607037590925601712324571056218193555704523823032641767520475162741594096571145886812816308452530204331730087657779021283862337371661481119122807626083708033425232550723064864259106362549470090472851974179121059921382718228785046041891247849871798541373980141884174008979899135166608308789823482844938045775862083279411975520460262826427691679314891943251355268564903998047541329128808824900385948194002356226999370589581476472030070437792246114385427075383384316695146514380913158753894679689159425958077734799282366161300276976400432024531047456581547336306733217621824639196263276834466218996472398020229030085027819776876253920830375803150923079704466061580387190299800303210381846613118135299808174443349933865296598351092871267295107965734270683314695909828184768623356276477618841611326974791324044167497845906405418406646288373464944419554651225190113530342505788338032278057669188220362706531491570139019648485071902038738270896946354122496237341449923287157671096677007305294477978199757570436116204321989736605416364455599590158112740505076007845816664453205405943777324954444250050118342028393750325870943974532724200777198612789889574500267286330784745794182228058407956780679136495217895972302598854704650667873906547184622460102741948485949405174987637115725780476602379558404698938882516942563906969593678065677288653292682538148296179785575454779700896344324567042160585035020637265481255495971352017680605435060329495740239779931498689480315371020406467906117598493521012412238663794845687669406870793208711868293076591793969378539206832811560440081614897357264348890791844241380903912154803999781604737049900151191137452940679406250275434350662717379141934023821393568044558606273744840442860102863737139964710884997979869641442350190352312910282195932942091232890812700078674014569032916404141260449706496801377545638946691465807507080092693539920938471439016161887400813784256635715297749124510327563770096435631711273762585270338587790135752888864570897349918067455983837024789734409478122577273551822559650081381936685644308446768390004562390749989237880024834094504160600503495836091816932291320698869207759926822545033785014745362933418134462704098427163794208537745319880442470868704997353679895398841951798685002947311285040404833906271571607753319572244160464484338831544322961335600886201245891297032570189006408617676347449932409984102690191470701695988801370349565239736405126013768289891060766951816861433519547012300527579110670997038550639280324226807317436279800668205048101331142202390353850343531817032252892851186860457231347980360454947369331165378606777410433950025154124989179815681011326040194746390234979012424830111295929426746416590615436096208302246983767302324940000198405496393077665748866190433654850900839421886489769019041997198559240902007612925514094498002355472129544397702395718458025010871475648139300640712578581649406723009169224363035954162725123778898795261451169905277764269447108755207515446337536199784519594288522668155424705343945618264178957912098047855782651116772443351317003912754425140175156169939857649782170087069784271384221935685687023403711001564157141320815687541209573436807737096490064352786491439763409490082676744515193823771511919993429001599644227304470387736439490409772435278110199771289000036455935372316207533397893896469379251688995404328842418681349796297487856427135925216964431743063664681414444980499965162291618787447869838971689918330787438171483342525957237240178724676461954668749780859780732068216402658894310527720247333657690169362654589927940184965026377599241948583670876048215670104856112163536429961086868354350621324887033346971305840826722910820030796621733130074381559477915928693193216478641573692269468216700390021982812754594179532071385408659122236763781922692754787145849505969731714864848687742332093495554875505187059896582036395310931774786766363855502180927166126492245306207339290137325401918024364654062056058846844047009004582630543481148582522848696732314217941715516512041855872687694374847183479223590221210610310516298207933937282441592328176722826764328758470773895590195802543731896292596365860366079958737198620547582177034765297903753405440766736738207679793368833612583540561859314 17 64544 65344 33920 34368 64896 65344 33920 34368 63744 65344 15157 (by decide +kernel) (by decide)
theorem wk199 : SixW25P.Covered 64544 65344 33920 34368 64896 65344 33920 34368 65344 66944 :=
  SixW25P.covered_of_walk lbS 222934200804756581824333807061805392942898481004160458149024202948989436630143917405284453252964418024754048187585715947474056717702517801870713905011852284660553430051197392819039084596735134401018724983088564097583726679968155763562261895165411790186543777318059149760904297622436820596244815925432142263793185575542666968238162694163932286653465490420648251803293171203740312654472278689251135828518716143514570430924589586531894661486928316706559340893340805998752252048981846044831240655790716101762115689581068767830237020419919965808584845791825220859435885231367787348289547360562425074136615590765243168509931625603527984141478488222070434264541371288441014890097712499035640117596036365935360818739656781540196785403937437439469824904099498123606027746907952816429850811678937402838193222088287422048063548878786871650639270877974475043667187123526599282845920709738430461931954886889646485307459023167286637657671473760101901544621737977569094627066694137122086099968590863533721093009255978511932319066125730133310061333962656829560017360119988386709986101011188984294092710118743131405169631374787614084232514015759903679315293583823331619095336133652434129862909648542665253404350516250720831390480220645735430379050483355336647731576246823223852433413025883201055750170604197646323073531485918237785831840624766186985375708821049277121988775109050806507796982798485454025985774640529282694214938469339619705182518947051242821017664506793663620291423764225189559659018336661173898766476898768600184455797245396022917624307414280779994189484863120790600433827751620697928461459110012468356443856299848346848206543515299658721643612059366270110222519562948650886608783608152704607133811837108690645497364966172600501921926702026666531779790251393766478388938982180565083769235811573667669604187650415867367527001632967303055217967892375854044878287880329578617749929814420318694097667610517860029538911287292971962279787093533403478756751367878151112220966731787885344658575235776011995477869920016491595038827803398557634320443569830438903336227471853490611642870053087213168873634443482817820473871363366109862441017311632305851316017691165253794146674619054992000044508296470590521294837232844141028936491310005074536938244991496826970945729321164813646991305344066030272678716516284962610665192757507436535123509905721122941216498 17 64544 65344 33920 34368 64896 65344 33920 34368 65344 66944 7797 (by decide +kernel) (by decide)
theorem wk200 : SixW25P.Covered 64544 65344 33920 34368 64896 65344 34368 34816 63744 66944 :=
  SixW25P.covered_of_walk lbS 98860276256673732726932909349352596851271295614852362493919443892843163325285536049447299903597300689950690177380735613755660004362663080744134132538962183715615477627747406910433950146098171758621879617096548172165746263621748616166013812595610974565963090049125998288870490991831125183693381052541540070298561480277421523058051247106631342173410141964976754110953845110108106425639530115637058375310106557843435908396521407995875711466896175576861498458168302637250766104459860606596794904516117000454138097700191735134994432306319313713905049142999145508402988285918286580930938747458677981201176291850187772946833181713402802057310106711174812924485828737558968839722197548718802418734777647043447899824481368900557426403878894305439468464342067895407724126798288800878897016621863503819601395511170578787187293813774793851552524249310271861117214291429130728518844293006008984137289877416786366630128365228146554629112526616172938401871504888059561237106065057586 16 64544 65344 33920 34368 64896 65344 34368 34816 63744 66944 3222 (by decide +kernel) (by decide)
theorem wk201 : SixW25P.Covered 64544 65344 34368 34816 64896 65344 33920 34816 63744 66944 :=
  SixW25P.covered_of_walk lbS 585796605745533694436207582575575936457685033286329637683346751808154646280321720464774490964865257521574395307325789645763873313655076183161256222464017123161560911508019067992629877200149318416318064513104088401205981996269917798130349205082727825568699936778925763911802620606616637242448971581345476261444650322952935297614932341667298164875480837567559228223661449022618007493366005682404803023874026159356805064224119625317180741051320118763185171927727513849240088143637054213770217465911468248137576262033695397663249557643050782541892120347666879189408027996878793346097345955376953474640441332007574524114626850796197375339982696114053277427620493109170052578179742032249111583246629726439384836755950456121330115172064177883682409508254526670235011771026266290479767069734272174581169426872680533244439500128033949083334178879312394946508025149854995910671444091383057112328306430801561981287466074567725691275103180625250879950328334184122531820433903482593065581655851490718233850622430390265154226376418088887807773383864328187020349362589251295890339458116017003103285967787166465209910075607332181352022542724168184658269369438511833485656556677388087423183176412299545976613121696010877963433596726016157174112814485595965056398217108885752428431446964620873159243481286667347362268771118 17 64544 65344 34368 34816 64896 65344 33920 34816 63744 66944 4342 (by decide +kernel) (by decide)
theorem wk202 : SixW25P.Covered 65344 66944 33920 34816 64896 65344 33920 34816 63744 66944 :=
  SixW25P.covered_of_walk lbS 645950188608407791759250652327507138632048592351777490085696947001559105799694027026043404719617459280201976206220281699670025033875897295641756427825172047192539411332658306448557995174805672115911838778420026216981562872189159420019989914509066913432919438643877015582866837627459961521972066693989402530537593886234366962362543753722871370897567979483894570123728694640323212651378964680051435265370105185243265839486328108272356182850059192931849744869465299307674170221166678212567637506019505423460557775579390575184643467838581252858243557804360775154457743009913383388178900888850402118847832295070384059389742780688989331419435650665065965254815781817074972749665119890472802756790630425288937118060814195957075876835016364815941948949468415144909844123945931563524295335344970625237101545447408313146803080204602872966541979341097833134866566513498307768823989619248231098991866524664464692690412422927741328691745107827165475255686873304508919377127952757130981720769168892796892296730202237174995412588728240415313414616823833029992300901796239094967169174310312933846639241454835689653713391426141307753474844256249836801691854860243020109524268386876392099957786247861432846612127641543391029138994858538393105165483687806810324993527301842656225367122649280620439362193247402679704806777241220186423743217259107170082787947255401998230583290334951102202400659459301660623848986780579734418309113826273156269102787409291667750658613890354205016261666621621463149181571001637709077932346421181299438357940928413960688258439928479929523256311013326296161885508588641175171810869993453747590231692864356297708077001447062511752209230150170619646002527311366082460486745996218758613279472984668777617384043231960904542082291344398224081737567779970519983998670206367492074112578247139494183501088867756523945167575116628553210033302209292847838890557675208711427544665154204428311050075366817310365751924321795849081151224100512613379413411579713460838023518089545633031935935170018789399645660071922789822274763614244407947758375059389354814421280145833952276364849891405415824658608870 21 65344 66944 33920 34816 64896 65344 33920 34816 63744 66944 6972 (by decide +kernel) (by decide)
theorem wk203 : SixW25P.Covered 63744 66944 33920 34816 65344 65792 33920 34816 63744 66944 :=
  SixW25P.covered_of_walk lbS 45200808588112128503739455348817663893894363454458185988833979980377555953319002784237983258710809054134863645435717359325015302841234439390363953938051832247093539566284298802467579893725829479084930811597232721923832246180532092149753987162714607144739135740805931533944497838609439095116855624278064956189419014216483483591017278593153951796574782755838460726063986916593143513911995588031408343419355419914233637744293697935001539170714440790984625500095145884300893467807881878527448880299377807416379335185540964914111945012806570202524243891287952695933044972333601758328445862413098430998369626483876400029788722436562787308592041860596672983703241122302694646591015056406940896419708338810269089834419775635622504248213599817265331095981945016831071527693588535942054640464456560342436248455330100017681309631143765906979672277205198200982897869368480504077044638950861080262739023818267545650718218141022566700602527585036353744991997675044358660622470852799537081707199135013198336077145058468395301900851983970143774440859143780280192460333721121614021433090705683139881585365482866789979949977986074543686250113697312104660973254190954868080801254907397070800518752456902948943525452589711962325894797009220423175549279995424745222734828833241511388185406739156413852805734693421519631323196760840107561800756349513382771397345536029121170717428347607294491623101750349049502962317666059762059866239498385642319493203286895066557668808573835628986946604935990298835134099420434121707721306775760671223932440451497217788434855599056095298287787674769172695471518599723153351880048962552549897263099655835745025869818714066193725714747381929174831917022996829227483506817521680480592752348145651919889457259126313201103160259997464031593237817997543855106410677203671353478338767582037765210488971309911845822672489273076515625745800150796389573719823771692057365727059257147186403731629900071072861929734126943315040592946890490288836358260215249752741672635751834695752221710076140290576581578627129468255692934467957451331061392434822902751845283880829114001705841871962273871919006256463197299928429984432490483327111260736180265226881077152415873532639545176430632903990505738336656079317810920299098172829939418928134184909222847206 20 63744 66944 33920 34816 65344 65792 33920 34816 63744 66944 7477 (by decide +kernel) (by decide)
theorem wk204 : SixW25P.Covered 63744 66944 33920 34816 64896 65792 33920 34816 66944 70144 :=
  SixW25P.covered_of_walk lbS 2914141341126668082 11 63744 66944 33920 34816 64896 65792 33920 34816 66944 70144 67 (by decide +kernel) (by decide)
theorem wk205 : SixW25P.Covered 66944 70144 33920 34816 64896 65792 33920 34816 63744 70144 :=
  SixW25P.covered_of_walk lbS 1413265122082 9 66944 70144 33920 34816 64896 65792 33920 34816 63744 70144 47 (by decide +kernel) (by decide)
theorem wk206 : SixW25P.Covered 63744 70144 33920 34816 64896 65792 34816 38400 63744 70144 :=
  SixW25P.covered_of_walk lbS 357936908233201280823830849700575631624008616882365736286909335001276013554610067657979507455958297154015867328934638 19 63744 70144 33920 34816 64896 65792 34816 38400 63744 70144 397 (by decide +kernel) (by decide)
theorem wk207 : SixW25P.Covered 63744 70144 34816 38400 64896 65792 31232 38400 63744 70144 :=
  SixW25P.covered_of_walk lbS 2986374179865889468384553708743563359962683350463117860110439902408449723728458530964300284558370359610247634329020941142757159751462363296865324060479403277157415198425793724360274180453275093808822341702307558 22 63744 70144 34816 38400 64896 65792 31232 38400 63744 70144 712 (by decide +kernel) (by decide)
theorem wk208 : SixW25P.Covered 63744 70144 31232 38400 65792 67584 31232 38400 63744 70144 :=
  SixW25P.covered_of_walk lbS 2928961085990420712498621316981629719580156935075213659440361811014443643642526115906569609619923232088611465616274449004277420778805226075391920928935152893196215922809266684457676848188460835465693244439991484666578638800377156162410696737540821038210484343539687514326414180692400294719755701033820030503870126868303635617955453711817157821224570743936798618013993886614180641522863540111245689984871254780807077059273730247479117296534941032282467194447923544074253514518014207189710737412903318777808915815885952377682724309838361806412783709898330595860953957472730425162698424472651804816670670516483136374827459600897231825301652765721126691383682771170296438771937932136164759549395633282246386782367847276947943601480982248974272286806997794972591702642002782463507156298480416748528527383846857146651626190931368609027305148904469720346610040224142331599974 24 63744 70144 31232 38400 65792 67584 31232 38400 63744 70144 2897 (by decide +kernel) (by decide)
theorem wk209 : SixW25P.Covered 63744 70144 31232 38400 67584 74752 31232 38400 63744 70144 :=
  SixW25P.covered_of_walk lbS 5798156069483865770 11 63744 70144 31232 38400 67584 74752 31232 38400 63744 70144 67 (by decide +kernel) (by decide)
theorem wk210 : SixW25P.Covered 63744 70144 31232 38400 60416 74752 31232 38400 70144 82944 :=
  SixW25P.covered_of_walk lbS 61234 6 63744 70144 31232 38400 60416 74752 31232 38400 70144 82944 22 (by decide +kernel) (by decide)
theorem wk211 : SixW25P.Covered 63744 70144 31232 38400 60416 74752 31232 38400 82944 108544 :=
  SixW25P.covered_of_walk lbS 132190588486227009918925492674401007984735624156115400941137262978842276899402312747148743714960209132411826901015693873128855439715411885048422570955675677586447356551573672002290447836623903273674130674471623817286432673101490996186523363097176358654822455164823824520344205995171837842017562689422444106290647657696684375254401538628112537478969122044115888917105238403115899134837121668288502295829499795804134425755001521818997797300287336276555515966837840677944249622569742368642496371742877862035532332742492134649264134434331677689501261273499583276369364392741749046407984626411880263036182151286253677963009486374401143444755399892071332747964468381832904375878520688663157726896810906041458131012969488163135003522230434954858775839388314038429841443662692656836332929757945735555817476096259101750239477058939409105857320007365522180054196008720689983202869661074256166836248881102067687188588321915694240001760509120018285033816968185106074796798101054299546908379885682461482868127755327528566521040548105617476197588749863253623757817792035767879081115589563333383959727434473558399283078487320545259472905539869175632771506745230014135967164291131164307368809147554122406751686428463341331164597751856657075155375954684172220212312509964689645944060238005419108087442262034474536055329857141103218166290535122360509746 28 63744 70144 31232 38400 60416 74752 31232 38400 82944 108544 4437 (by decide +kernel) (by decide)
theorem wk212 : SixW25P.Covered 70144 82944 31232 38400 60416 74752 31232 38400 57344 108544 :=
  SixW25P.covered_of_walk lbS 6697634 8 70144 82944 31232 38400 60416 74752 31232 38400 57344 108544 32 (by decide +kernel) (by decide)
theorem wk213 : SixW25P.Covered 82944 108544 31232 38400 60416 74752 31232 38400 57344 108544 :=
  SixW25P.covered_of_walk lbS 82237726343829737522009168122105501513482770022137861440704498925509929244384118627858873593713991635533760600323234003682590301115885383270723216336116325528020656119267806039198686462627324962 23 82944 108544 31232 38400 60416 74752 31232 38400 57344 108544 647 (by decide +kernel) (by decide)
theorem wk214 : SixW25P.Covered 57344 108544 31232 38400 60416 74752 31232 38400 108544 159744 :=
  SixW25P.covered_of_walk lbS 426722191039552576848840444145962867758023537814286668244121868550621478177308206440033855954734198791164538369170247405022351954075819428168933255611693033666438335042894869149404958944721206336748855256370 24 57344 108544 31232 38400 60416 74752 31232 38400 108544 159744 692 (by decide +kernel) (by decide)
theorem wk215 : SixW25P.Covered 108544 159744 31232 38400 60416 74752 31232 38400 57344 159744 :=
  SixW25P.covered_of_walk lbS 5134942770 7 108544 159744 31232 38400 60416 74752 31232 38400 57344 159744 37 (by decide +kernel) (by decide)
theorem wk216 : SixW25P.Covered 57344 159744 31232 38400 60416 74752 31232 38400 159744 262144 :=
  SixW25P.covered_of_walk lbS 500223170099879416627864354 17 57344 159744 31232 38400 60416 74752 31232 38400 159744 262144 102 (by decide +kernel) (by decide)
theorem wk217 : SixW25P.Covered 159744 262144 31232 38400 60416 74752 31232 38400 57344 262144 :=
  SixW25P.covered_of_walk lbS 4658 5 159744 262144 31232 38400 60416 74752 31232 38400 57344 262144 17 (by decide +kernel) (by decide)
theorem wk218 : SixW25P.Covered 57344 262144 31232 38400 60416 74752 31232 38400 262144 466944 :=
  SixW25P.covered_of_walk lbS 0 2 57344 262144 31232 38400 60416 74752 31232 38400 262144 466944 2 (by decide +kernel) (by decide)
theorem wk219 : SixW25P.Covered 262144 466944 31232 38400 60416 74752 31232 38400 57344 466944 :=
  SixW25P.covered_of_walk lbS 0 2 262144 466944 31232 38400 60416 74752 31232 38400 57344 466944 2 (by decide +kernel) (by decide)
theorem wk220 : SixW25P.Covered 57344 466944 31232 38400 60416 74752 59904 75264 30720 40448 :=
  SixW25P.covered_of_walk lbS 0 2 57344 466944 31232 38400 60416 74752 59904 75264 30720 40448 2 (by decide +kernel) (by decide)
theorem wk221 : SixW25P.Covered 57344 466944 31232 38400 60416 74752 59904 75264 57344 466944 :=
  SixW25P.covered_of_walk lbS 70443594564245699641456974942042938228677224364238070160054576808717386929710215132540745510791542897762633533722192382532010848574015029890407270080245028331479799859853534757172276929430498806970070801872715678344809029758290790091839276097837747567934112595692740944845662411698207668751478509333461203314085341608154682512217498713545486878373904699616626308274810442295871018143657798272972687720206306527571825589346071357066513924207270683181414431522781024661984053935301639327929060130491390843173113317690519007388036318037398644083387541575828183179211224246653146369029955902946187646860801861508791838197470565770006188053821089675512378131097729225368690785965533478164357201669916786472690215082495129570108408713385195252647224207297606914165153417587003339610953862670024973822315843532678505480094708437544144585094862925665113562498561120343898990300765073423092157537119141450543539269375883203226148394104551382962352151200108866552708975668112870732218741201099277265467010373244743715109449042882193220288088200807874002170491146876275894214861490323768368808052239993229494598725902292353910393903437819566540794931437466948125386466783941001572809720534349770500070699449633578873226282734119649631456493047626978631473247837514683678635429471284392296461972895606281125996049298131536717686601416891163530824587413858965656819887063763018367111677682964814210749826960749366562310908509836647753395590926266819360068874934278599487827160776093787159630944896495101616346463802158373215821254693246172328516220249108477356686720173497793406534442007578198813775896777026452634316640986323286981613010067901921497865851750648607203279824311152681563612237636825547827847746967656295482217028463550945346125846211846244920145347050545739486663965849456349373754405508061770973323765261387683521451033908793855585834282109031527677947314955799760149782574848903337002582353746753369457471514302056429154693455245604895829943389439670963721819297310240798404783038188772906901928464311006118095981425705056613022684130210690072270185076796115952301449072623867543482515050097099337211023006185500358074788664239485895769184329802417824412137099262658572220760394500922370589068820552415876378555085314489446275831841901816496222995982537846339071112127250113314 41 57344 466944 31232 38400 60416 74752 59904 75264 57344 466944 7592 (by decide +kernel) (by decide)
theorem wk222 : SixW25P.Covered 57344 466944 31232 38400 60416 74752 88064 278528 30720 40448 :=
  SixW25P.covered_of_walk lbS 0 2 57344 466944 31232 38400 60416 74752 88064 278528 30720 40448 2 (by decide +kernel) (by decide)
theorem wk223 : SixW25P.Covered 57344 466944 31232 38400 60416 74752 88064 278528 57344 466944 :=
  SixW25P.covered_of_walk lbS 4969247866980584185436188450 22 57344 466944 31232 38400 60416 74752 88064 278528 57344 466944 107 (by decide +kernel) (by decide)
theorem wk224 : SixW25P.Covered 57344 466944 31232 38400 88576 253952 31232 38400 30720 40448 :=
  SixW25P.covered_of_walk lbS 0 2 57344 466944 31232 38400 88576 253952 31232 38400 30720 40448 2 (by decide +kernel) (by decide)
theorem wk225 : SixW25P.Covered 57344 466944 31232 38400 88576 253952 31232 38400 57344 466944 :=
  SixW25P.covered_of_walk lbS 23846326593070018497534299196073303770914979816207574300939801529278521865135664121198019304193908086864083011488400799680164631288957740040302980043090895698814251424418067609741150758007973352754393172621436649237329926668889353069613450638969669860213447604397606945882847038315551520706035762620227522126288001256219827837517353729371157510018734833391932457409910282512478792091985141059957646676145924362352365326327697717565871633762917058533815687501878262475312041543267009447373446141378275695928749439153296591980713912236559578344160381200379191766522612556735933725416024257622704628961556488520307252303998929533723682462697105967620283312930 40 57344 466944 31232 38400 88576 253952 31232 38400 57344 466944 2192 (by decide +kernel) (by decide)
theorem wk226 : SixW25P.Covered 57344 466944 31232 38400 88576 253952 59904 75264 30720 40448 :=
  SixW25P.covered_of_walk lbS 0 2 57344 466944 31232 38400 88576 253952 59904 75264 30720 40448 2 (by decide +kernel) (by decide)
theorem wk227 : SixW25P.Covered 57344 466944 31232 38400 88576 253952 59904 75264 57344 466944 :=
  SixW25P.covered_of_walk lbS 155145006409362479697242914 21 57344 466944 31232 38400 88576 253952 59904 75264 57344 466944 102 (by decide +kernel) (by decide)
theorem wk228 : SixW25P.Covered 57344 466944 31232 38400 88576 253952 88064 278528 30720 40448 :=
  SixW25P.covered_of_walk lbS 0 2 57344 466944 31232 38400 88576 253952 88064 278528 30720 40448 2 (by decide +kernel) (by decide)
theorem wk229 : SixW25P.Covered 57344 466944 31232 38400 88576 253952 88064 278528 57344 466944 :=
  SixW25P.covered_of_walk lbS 0 2 57344 466944 31232 38400 88576 253952 88064 278528 57344 466944 2 (by decide +kernel) (by decide)
theorem wk230 : SixW25P.Covered 57344 466944 59904 75264 31744 38400 31232 38400 30720 40448 :=
  SixW25P.covered_of_walk lbS 0 2 57344 466944 59904 75264 31744 38400 31232 38400 30720 40448 2 (by decide +kernel) (by decide)
theorem wk231 : SixW25P.Covered 57344 466944 59904 75264 31744 38400 31232 38400 57344 466944 :=
  SixW25P.covered_of_walk lbS 17675516151095491024420121562488739854674718569968291820712544597569315555785537495055788128506605596151394722192736206268409174735724995432581668776227035737814228345607178341165178767950810989743390443074150635960882582143578334543920449292413324608094716845258233976648440022940656754218857935069628376443155344270263343924853617344155945309150528914364277648116509111508674117517778113113921803702096353888216214274797944080401886728424243873382585355083550637399238569847561065758326173808589644594303807534647154657153788600189608372987352657150137996311725294301141609395468403468296951309628770005037269517641053836934057440534809562363151272542770119360304267073449390776546331837177189268772779233688810887309314360679299042768708524239890982070174177226676744508633337237445556676465716314984775628578443236738029577861334266860689255172292108440179447096096265707066481741422133569105420913801865334774115382201530409959348144980687889837855983839474546770246903195404190976304747689227407231511078657534608037530957789902736552464345982120431903406891470662935580768892332877834650540568480120598376014702900306478772488441609932211308136522534519012043599915048284765942742425960068562203957137017427999903737539553129458015438573641494763088863021017356576438510925235305066792344244866635563964884038165498437872427602910959591301458363615176938099079592422874709156871260197429364352524057186756125108157986998976218718651898694123529253648500719925044626740314823328074411868195861069048482330893713519619461610397255837931849831460662621180385633388116639439539676645275885563168476583679525621179019726019322049604687327387557154649197884054540498969027369282297579811451629852614536065311764180411924940388242426605461997473612682260178536597396982244120972528889037111712549759214610410495578793856040626237727756076375215575122808473574958084690792531898454322973878071716450444997039864780136840318514050093743777124172874785674555291162820675406340837923007826552834125717037315642262713681782772717866132071520504070228079812281792269763828429349590496684687168873993563966845183472620921478695080762897877287988489749676655438114289448793312696514511123771959375324687628488837611542809144540395001525301337667417310813837994204113108653468880752825472639042271753981498108095446469233132791640241802048325313593474572432626611163258287349340793895325177636131637133449594168430606008405405875906892323374807332558846973086620348862222511065540286125151740446637723606055744682024342966352313982832876981560565031434849896538797677539110689406696969231883524128405116769059733496049683635024328916684260239319685308090868895363744091104316568752895997997814940262243929798137575133934958580596042200136091144559372489084530039784386974290448499601173036175795719315801419896533309222378944411340453212150843872907942501647443039674342825220026376785924038727947235672400920128230620337134501429034524476128045942300121707061488965511623205884248328379552972250264235049450298731499753126430214928445511799675386807824537116136301974537586353103107602260354162489644634958898127118332668584399685188719743543578539762960260094310110513034120374789543152584808206007293743620362877980475592962135436525524634012164378976640976570034993715858653237609010692777637570624074090737084302532154777768617544084951772928466188086063500545524994659215583927949277289996935871593024711636328412018710877494823902005321637033128334298116685349153422264399188962632311860967693936771436101276808418033200383039434204325132142998671225725471396290243060161565260351921815800784451432721479307060821409865632674473625476711624694390715695353039564796870262149977278098237913291618760800363555306900507105302238311891958577150624213498008513329243151292827009172290013254991073892134458947867860298884242994050218144701715213811885428435228898727119706910849288546112019867266948753907019542582818006772678223962039981160443674869708486014287379243841665513999280009291443237153309328431416746023021973853390482512614737272965148326455585714228194746750849666905984669307268878674399245521291347904015530312576047188702759134918109021713861196922015240502483017126533347495809751695269756659620690914571507155692421281129293538631321063212175024672609134252812812553589809590929539566799687603448428407495366770152044689299933649625786775804156556547527591624019329257015432235883192508802389954325389011982284569502096939132141722715719457016750745677255570663865266143347751151403097169913776099604858943397182904606545755987892437604780564160970734776801067098834900411041357095318915926990106247071390217267074005725766003617496322020091456768775355849161784264707335887749132995013003085923834821018528361487324619554 40 57344 466944 59904 75264 31744 38400 31232 38400 57344 466944 15727 (by decide +kernel) (by decide)
theorem wk232 : SixW25P.Covered 57344 466944 59904 75264 31744 38400 59904 75264 30720 40448 :=
  SixW25P.covered_of_walk lbS 0 2 57344 466944 59904 75264 31744 38400 59904 75264 30720 40448 2 (by decide +kernel) (by decide)
theorem wk233 : SixW25P.Covered 57344 466944 59904 75264 31744 38400 59904 75264 57344 466944 :=
  SixW25P.covered_of_walk lbS 64387334009763893188718457522186074538097947404343794655449686329489280467983456904357327559634220455003815962247831876703058840721324622020614778781310465063683810116800856560003886353776137808169523106591894155632985399856954839420743955864397473464915717638084365748781469008196726347341068341207504055537984248728846893937359645060406336691230801782734046651374811401798510944116789363473608013052265062651444544758506638286803750595088174426156511370086230121391110008573777184198756158455000394261023488815240867731492813309554426998593846830157487177576102498462937583825151963444393394997984491344144845343398873926644891598726463849296560565323816166748166080517880120828029071393110143320913500798051008223782226803197984289601830671796997945954431172481818341502273342073330741338872329361457960375557178555642315154200677122544760448868709274773201936968083054044751519099576844798785074528519722231932792780276352897826539458803265595537855105113949248180883763320852357192997522281862799663496770510370734959410741667700887082963375136735186178323297652648375692961948463556923630116841352588374200634659703812003374533292024591021181786812079254129417555214128857515157101537886763664202564075658525195724344133419073210856897950937595902060986270200023504873429104154731704724936166044931923417923554598145602696292649426986058250813903408088734039178068829532445054385902319599809944436463563551236338949412194035057932875295647161405708510367980232634322560008303362311629107653519070042625238392428348410744238970540632487161951798051695638432124652418085652197453143098335046089779790829254502920188559823915897199994058852970901107835259547641297983049830823701656840221513467674721540464965649792927253109991194323819598462061051151387279819973319425194487759190763470295372943927197616798322953063266385776023243950962659250557374870490124456523433056183306984808466062517189925526942328503790322632446177689625559815235234522453519736684079283478963822856429455700427990966929598400145709062094718200604969395657637242949349251076543283357000550640042498716811642241251947659669962308487004219623803268085572355591207166073455799987819884903444672939804134680545965792153126068127101933124994488702668321562897204410784943218963205609608115427098092580155788718989011908516585905881214470161185789479250292763936041386182697135568019289802860657316858039368377824848322230444066758539678251592683114790497163834832605720672674185390218924984008459241267458828334139138858623594187047970428362997610239538175363132380894639994662628649034481880354769096539614666727972952187345113160010463085731191300079247195172770925200397448903738434829017404478291253663582391822348602583275680459782802874504288936963021292156907760545476093188838652201261006849513007260562937587807966701232097451030423195829615654068471322956427551479320290888017272393053439726530497063562010862541932754558330042488100488193190837545137656743967544015928680254230178640226239368475469334084116170089164219700504060731816754029578211347922635979319867151302569452969266152659111996982464405191460265663616865634624791296782632014878295354882989345573119816958270411114984832754022526700417408915631670274166801143825001700543987130712485660374404496249953288691813655602717362780951166136592117937382493971962752970311201711454080246508986317736594372863529738284042221967298391317160843659509049804483422761135388332279702224586005850302166406910763676226826748602188709350771346155675021482010232544503464200189292392587750971852503933826534061047529016022020678262664326284793526450309079321862350704234334940773042993399773419290127294025751664821601961726575516273653747964692390108753050091615395155069715387730878632204468255038243772490484206943888214773743943605858003683286089263468936610248234360396501172017434480001910505978485314112753899848724235730972350732083712830058653059207529215585546868945366962658084911772077062115926118371629798943858110356800797768489541078437245613018077015378163067406936339758386961541265139492832780857566068694822780755992891894158058609428833786929805484706031413211618520512853585531723465398355399251573393896492289549937625044780560716724510207298562881809759840783944086571840234690769177044195106026716759035198426469852977825882462925240252362027131219395792350953012756634793590045281612498042856524812022311135087939486655483504839080572534455639759260530688390891697675546718385973040466422831920565913688192531993483041960061254850075532139254252261670517548635414615826633267051389171644367259786161143357471604682711466004915501629671980035718772167637697000175981818617754871043729612655118407486295904491767486278854250770545898323103144681607945967735453276132809557551084346943842811215890913579116111086287964611332478948046396717982013156713948933552609983136399327627728178955630462302675535207722955593142042504179503561638666248994 43 57344 466944 59904 75264 31744 38400 59904 75264 57344 466944 16292 (by decide +kernel) (by decide)
theorem wk234 : SixW25P.Covered 57344 466944 59904 75264 31744 38400 88064 278528 30720 40448 :=
  SixW25P.covered_of_walk lbS 0 2 57344 466944 59904 75264 31744 38400 88064 278528 30720 40448 2 (by decide +kernel) (by decide)
theorem wk235 : SixW25P.Covered 57344 466944 59904 75264 31744 38400 88064 278528 57344 466944 :=
  SixW25P.covered_of_walk lbS 5557885560537739741736340015951650 23 57344 466944 59904 75264 31744 38400 88064 278528 57344 466944 127 (by decide +kernel) (by decide)
theorem wk236 : SixW25P.Covered 57344 466944 59904 75264 60416 74752 31232 38400 30720 40448 :=
  SixW25P.covered_of_walk lbS 0 2 57344 466944 59904 75264 60416 74752 31232 38400 30720 40448 2 (by decide +kernel) (by decide)
theorem wk237 : SixW25P.Covered 57344 466944 59904 75264 60416 74752 31232 38400 57344 466944 :=
  SixW25P.covered_of_walk lbS 20523137913697937746892903779549090189205336067992696232953021473337923597107038010872633799407048479375235443106297462727268010808339158464951662335622683584779597897411869108043029400140417779550636557321362866697595618949813015121294346874028743260488327853967170888288061132884091919062782059268591787622681927289909089201930301563036019714638177391076631732382697936108425551218797388390621068486625883859875754324834158757708248784617520399997170144762662949650913482946096726015411069723552896023231859250342068868369885144319222004596495054135987438969101550742368222032781013749138331611984244089016312249986382187926440151513646869239608626124077258765322659004973431594950448035790605725054587087538524330218337502359861924510472879383803922624309497955778332680968270093259405239946677852745655993563238629713206763051035546350437951768290017483980533982712539577685302517719184698667056869991331155858327763908202661086744175950269196994099319126921380327227009786316153892497697029630792833198633508649049948111918788216787370829903988748566624872520580672178429006767336465211952014699926221555564115016398246879531643170347139811083560452208475477468141097500390046189011659701945571721083001506181319437522172186244053369680370109109753684642876971889267277294609952307606145795866104979688878577912242108902795683207818874032680796053769167449430043350197547450318705058702218871269228051476305659129122807591960922700692629568601978915411015837599110001010906644968516004289851697174791430859879899781663346457204120430992279301188936589101405016336133446993607139336115006555353325944136665192663592707819331425223011397781759739214338563164183098152429878835332981255179416822464447660738875385540215809292406152667437285563758979626836418247353533346380088099345497033255232347739934470917592225137352047940315817778127216154393558111700705976360395020323910292453633023997109495112715926650492594204447020632417078129938787796360008495604798984191318437420209756165415073743385826716497329966161203966086512461310009983417843863271625655781905411338840720212151033516980637239827265324098842255132140322 41 57344 466944 59904 75264 60416 74752 31232 38400 57344 466944 7072 (by decide +kernel) (by decide)
theorem wk238 : SixW25P.Covered 57344 466944 59904 75264 60416 74752 59904 75264 30720 40448 :=
  SixW25P.covered_of_walk lbS 0 2 57344 466944 59904 75264 60416 74752 59904 75264 30720 40448 2 (by decide +kernel) (by decide)
theorem wk239 : SixW25P.Covered 57344 466944 59904 75264 60416 74752 59904 75264 57344 466944 :=
  SixW25P.covered_of_walk lbS 38755930420175922872394530 20 57344 466944 59904 75264 60416 74752 59904 75264 57344 466944 97 (by decide +kernel) (by decide)
theorem wk240 : SixW25P.Covered 57344 466944 59904 75264 60416 74752 88064 278528 30720 40448 :=
  SixW25P.covered_of_walk lbS 0 2 57344 466944 59904 75264 60416 74752 88064 278528 30720 40448 2 (by decide +kernel) (by decide)
theorem wk241 : SixW25P.Covered 57344 466944 59904 75264 60416 74752 88064 278528 57344 466944 :=
  SixW25P.covered_of_walk lbS 0 2 57344 466944 59904 75264 60416 74752 88064 278528 57344 466944 2 (by decide +kernel) (by decide)
theorem wk242 : SixW25P.Covered 57344 466944 59904 75264 88576 253952 31232 38400 30720 40448 :=
  SixW25P.covered_of_walk lbS 0 2 57344 466944 59904 75264 88576 253952 31232 38400 30720 40448 2 (by decide +kernel) (by decide)
theorem wk243 : SixW25P.Covered 57344 466944 59904 75264 88576 253952 31232 38400 57344 466944 :=
  SixW25P.covered_of_walk lbS 155144379220063973572487970 21 57344 466944 59904 75264 88576 253952 31232 38400 57344 466944 102 (by decide +kernel) (by decide)
theorem wk244 : SixW25P.Covered 57344 466944 59904 75264 88576 253952 59904 75264 30720 40448 :=
  SixW25P.covered_of_walk lbS 0 2 57344 466944 59904 75264 88576 253952 59904 75264 30720 40448 2 (by decide +kernel) (by decide)
theorem wk245 : SixW25P.Covered 57344 466944 59904 75264 88576 253952 59904 75264 57344 466944 :=
  SixW25P.covered_of_walk lbS 0 2 57344 466944 59904 75264 88576 253952 59904 75264 57344 466944 2 (by decide +kernel) (by decide)
theorem wk246 : SixW25P.Covered 57344 466944 59904 75264 88576 253952 88064 278528 30720 40448 :=
  SixW25P.covered_of_walk lbS 0 2 57344 466944 59904 75264 88576 253952 88064 278528 30720 40448 2 (by decide +kernel) (by decide)
theorem wk247 : SixW25P.Covered 57344 466944 59904 75264 88576 253952 88064 278528 57344 466944 :=
  SixW25P.covered_of_walk lbS 0 2 57344 466944 59904 75264 88576 253952 88064 278528 57344 466944 2 (by decide +kernel) (by decide)
theorem wk248 : SixW25P.Covered 57344 466944 88064 278528 31744 38400 31232 38400 30720 40448 :=
  SixW25P.covered_of_walk lbS 0 2 57344 466944 88064 278528 31744 38400 31232 38400 30720 40448 2 (by decide +kernel) (by decide)
theorem wk249 : SixW25P.Covered 57344 466944 88064 278528 31744 38400 31232 38400 57344 466944 :=
  SixW25P.covered_of_walk lbS 5191578737880515997474845741791064634309100000285786409114787417877704353639769956808807473117603264154597682872122035253845402808720503833473118679150105715287681615511090371750930342475478495196995925451095067621549947063153838746273214594418097754208466385425996684372612162028436829494686292725410196577432301531839360812804704777371623274206401409215314233180210339576421540936660380827806696629179727724656557434658 36 57344 466944 88064 278528 31744 38400 31232 38400 57344 466944 1407 (by decide +kernel) (by decide)
theorem wk250 : SixW25P.Covered 57344 466944 88064 278528 31744 38400 59904 75264 30720 40448 :=
  SixW25P.covered_of_walk lbS 0 2 57344 466944 88064 278528 31744 38400 59904 75264 30720 40448 2 (by decide +kernel) (by decide)
theorem wk251 : SixW25P.Covered 57344 466944 88064 278528 31744 38400 59904 75264 57344 466944 :=
  SixW25P.covered_of_walk lbS 5558559299412220521497256348755746 23 57344 466944 88064 278528 31744 38400 59904 75264 57344 466944 127 (by decide +kernel) (by decide)
theorem wk252 : SixW25P.Covered 57344 466944 88064 278528 31744 38400 88064 278528 30720 40448 :=
  SixW25P.covered_of_walk lbS 0 2 57344 466944 88064 278528 31744 38400 88064 278528 30720 40448 2 (by decide +kernel) (by decide)
theorem wk253 : SixW25P.Covered 57344 466944 88064 278528 31744 38400 88064 278528 57344 466944 :=
  SixW25P.covered_of_walk lbS 0 2 57344 466944 88064 278528 31744 38400 88064 278528 57344 466944 2 (by decide +kernel) (by decide)
theorem wk254 : SixW25P.Covered 57344 466944 88064 278528 60416 74752 31232 38400 30720 40448 :=
  SixW25P.covered_of_walk lbS 0 2 57344 466944 88064 278528 60416 74752 31232 38400 30720 40448 2 (by decide +kernel) (by decide)
theorem wk255 : SixW25P.Covered 57344 466944 88064 278528 60416 74752 31232 38400 57344 466944 :=
  SixW25P.covered_of_walk lbS 4959255339502831981795878690 22 57344 466944 88064 278528 60416 74752 31232 38400 57344 466944 107 (by decide +kernel) (by decide)
theorem wk256 : SixW25P.Covered 57344 466944 88064 278528 60416 74752 59904 75264 30720 40448 :=
  SixW25P.covered_of_walk lbS 0 2 57344 466944 88064 278528 60416 74752 59904 75264 30720 40448 2 (by decide +kernel) (by decide)
theorem wk257 : SixW25P.Covered 57344 466944 88064 278528 60416 74752 59904 75264 57344 466944 :=
  SixW25P.covered_of_walk lbS 0 2 57344 466944 88064 278528 60416 74752 59904 75264 57344 466944 2 (by decide +kernel) (by decide)
theorem wk258 : SixW25P.Covered 57344 466944 88064 278528 60416 74752 88064 278528 30720 40448 :=
  SixW25P.covered_of_walk lbS 0 2 57344 466944 88064 278528 60416 74752 88064 278528 30720 40448 2 (by decide +kernel) (by decide)
theorem wk259 : SixW25P.Covered 57344 466944 88064 278528 60416 74752 88064 278528 57344 466944 :=
  SixW25P.covered_of_walk lbS 0 2 57344 466944 88064 278528 60416 74752 88064 278528 57344 466944 2 (by decide +kernel) (by decide)
theorem wk260 : SixW25P.Covered 57344 466944 88064 278528 88576 253952 31232 38400 30720 40448 :=
  SixW25P.covered_of_walk lbS 0 2 57344 466944 88064 278528 88576 253952 31232 38400 30720 40448 2 (by decide +kernel) (by decide)
theorem wk261 : SixW25P.Covered 57344 466944 88064 278528 88576 253952 31232 38400 57344 466944 :=
  SixW25P.covered_of_walk lbS 0 2 57344 466944 88064 278528 88576 253952 31232 38400 57344 466944 2 (by decide +kernel) (by decide)
theorem wk262 : SixW25P.Covered 57344 466944 88064 278528 88576 253952 59904 75264 30720 40448 :=
  SixW25P.covered_of_walk lbS 0 2 57344 466944 88064 278528 88576 253952 59904 75264 30720 40448 2 (by decide +kernel) (by decide)
theorem wk263 : SixW25P.Covered 57344 466944 88064 278528 88576 253952 59904 75264 57344 466944 :=
  SixW25P.covered_of_walk lbS 0 2 57344 466944 88064 278528 88576 253952 59904 75264 57344 466944 2 (by decide +kernel) (by decide)
theorem wk264 : SixW25P.Covered 57344 466944 88064 278528 88576 253952 88064 278528 30720 40448 :=
  SixW25P.covered_of_walk lbS 0 2 57344 466944 88064 278528 88576 253952 88064 278528 30720 40448 2 (by decide +kernel) (by decide)
theorem wk265 : SixW25P.Covered 57344 466944 88064 278528 88576 253952 88064 278528 57344 466944 :=
  SixW25P.covered_of_walk lbS 0 2 57344 466944 88064 278528 88576 253952 88064 278528 57344 466944 2 (by decide +kernel) (by decide)
theorem bd0_0 : (SixW25P.badOf cover0).getD 0 (0, 0) = (30720, 40448) := by decide +kernel
theorem bd0_1 : (SixW25P.badOf cover0).getD 1 (0, 0) = (57344, 466944) := by decide +kernel
theorem nb0_eq : (SixW25P.badOf cover0).length = 2 := by decide +kernel
theorem bd1_0 : (SixW25P.badOf cover1).getD 0 (0, 0) = (31232, 38400) := by decide +kernel
theorem bd1_1 : (SixW25P.badOf cover1).getD 1 (0, 0) = (59904, 75264) := by decide +kernel
theorem bd1_2 : (SixW25P.badOf cover1).getD 2 (0, 0) = (88064, 278528) := by decide +kernel
theorem nb1_eq : (SixW25P.badOf cover1).length = 3 := by decide +kernel
theorem bd2_0 : (SixW25P.badOf cover2).getD 0 (0, 0) = (31744, 38400) := by decide +kernel
theorem bd2_1 : (SixW25P.badOf cover2).getD 1 (0, 0) = (60416, 74752) := by decide +kernel
theorem bd2_2 : (SixW25P.badOf cover2).getD 2 (0, 0) = (88576, 253952) := by decide +kernel
theorem nb2_eq : (SixW25P.badOf cover2).length = 3 := by decide +kernel
theorem bd3_0 : (SixW25P.badOf cover3).getD 0 (0, 0) = (31232, 38400) := by decide +kernel
theorem bd3_1 : (SixW25P.badOf cover3).getD 1 (0, 0) = (59904, 75264) := by decide +kernel
theorem bd3_2 : (SixW25P.badOf cover3).getD 2 (0, 0) = (88064, 278528) := by decide +kernel
theorem nb3_eq : (SixW25P.badOf cover3).length = 3 := by decide +kernel
theorem bd4_0 : (SixW25P.badOf cover4).getD 0 (0, 0) = (30720, 40448) := by decide +kernel
theorem bd4_1 : (SixW25P.badOf cover4).getD 1 (0, 0) = (57344, 466944) := by decide +kernel
theorem nb4_eq : (SixW25P.badOf cover4).length = 2 := by decide +kernel
theorem run_ok : ∀ i0 i1 i2 i3 i4, i0 < (SixW25P.badOf cover0).length → i1 < (SixW25P.badOf cover1).length → i2 < (SixW25P.badOf cover2).length → i3 < (SixW25P.badOf cover3).length → i4 < (SixW25P.badOf cover4).length →
    SixW25P.Covered ((SixW25P.badOf cover0).getD i0 (0, 0)).1 ((SixW25P.badOf cover0).getD i0 (0, 0)).2 ((SixW25P.badOf cover1).getD i1 (0, 0)).1 ((SixW25P.badOf cover1).getD i1 (0, 0)).2 ((SixW25P.badOf cover2).getD i2 (0, 0)).1 ((SixW25P.badOf cover2).getD i2 (0, 0)).2 ((SixW25P.badOf cover3).getD i3 (0, 0)).1 ((SixW25P.badOf cover3).getD i3 (0, 0)).2 ((SixW25P.badOf cover4).getD i4 (0, 0)).1 ((SixW25P.badOf cover4).getD i4 (0, 0)).2 := by
  intro i0 i1 i2 i3 i4 hi0 hi1 hi2 hi3 hi4
  rw [nb0_eq] at hi0
  rw [nb1_eq] at hi1
  rw [nb2_eq] at hi2
  rw [nb3_eq] at hi3
  rw [nb4_eq] at hi4
  match i0, i1, i2, i3, i4, hi0, hi1, hi2, hi3, hi4 with
  | 0, 0, 0, 0, 0, _, _, _, _, _ => rw [bd0_0, bd1_0, bd2_0, bd3_0, bd4_0]; exact wk0
  | 0, 0, 0, 0, 1, _, _, _, _, _ => rw [bd0_0, bd1_0, bd2_0, bd3_0, bd4_1]; exact wk1
  | 0, 0, 0, 1, 0, _, _, _, _, _ => rw [bd0_0, bd1_0, bd2_0, bd3_1, bd4_0]; exact wk2
  | 0, 0, 0, 1, 1, _, _, _, _, _ => rw [bd0_0, bd1_0, bd2_0, bd3_1, bd4_1]; exact wk3
  | 0, 0, 0, 2, 0, _, _, _, _, _ => rw [bd0_0, bd1_0, bd2_0, bd3_2, bd4_0]; exact wk4
  | 0, 0, 0, 2, 1, _, _, _, _, _ => rw [bd0_0, bd1_0, bd2_0, bd3_2, bd4_1]; exact wk5
  | 0, 0, 1, 0, 0, _, _, _, _, _ => rw [bd0_0, bd1_0, bd2_1, bd3_0, bd4_0]; exact wk6
  | 0, 0, 1, 0, 1, _, _, _, _, _ => rw [bd0_0, bd1_0, bd2_1, bd3_0, bd4_1]; exact (SixW25P.covered_split4 262144 (SixW25P.covered_split4 159744 (SixW25P.covered_split4 108544 (SixW25P.covered_split4 82944 wk7 wk8) wk9) wk10) wk11)
  | 0, 0, 1, 1, 0, _, _, _, _, _ => rw [bd0_0, bd1_0, bd2_1, bd3_1, bd4_0]; exact wk12
  | 0, 0, 1, 1, 1, _, _, _, _, _ => rw [bd0_0, bd1_0, bd2_1, bd3_1, bd4_1]; exact wk13
  | 0, 0, 1, 2, 0, _, _, _, _, _ => rw [bd0_0, bd1_0, bd2_1, bd3_2, bd4_0]; exact wk14
  | 0, 0, 1, 2, 1, _, _, _, _, _ => rw [bd0_0, bd1_0, bd2_1, bd3_2, bd4_1]; exact wk15
  | 0, 0, 2, 0, 0, _, _, _, _, _ => rw [bd0_0, bd1_0, bd2_2, bd3_0, bd4_0]; exact wk16
  | 0, 0, 2, 0, 1, _, _, _, _, _ => rw [bd0_0, bd1_0, bd2_2, bd3_0, bd4_1]; exact wk17
  | 0, 0, 2, 1, 0, _, _, _, _, _ => rw [bd0_0, bd1_0, bd2_2, bd3_1, bd4_0]; exact wk18
  | 0, 0, 2, 1, 1, _, _, _, _, _ => rw [bd0_0, bd1_0, bd2_2, bd3_1, bd4_1]; exact wk19
  | 0, 0, 2, 2, 0, _, _, _, _, _ => rw [bd0_0, bd1_0, bd2_2, bd3_2, bd4_0]; exact wk20
  | 0, 0, 2, 2, 1, _, _, _, _, _ => rw [bd0_0, bd1_0, bd2_2, bd3_2, bd4_1]; exact wk21
  | 0, 1, 0, 0, 0, _, _, _, _, _ => rw [bd0_0, bd1_1, bd2_0, bd3_0, bd4_0]; exact wk22
  | 0, 1, 0, 0, 1, _, _, _, _, _ => rw [bd0_0, bd1_1, bd2_0, bd3_0, bd4_1]; exact (SixW25P.covered_split4 262144 (SixW25P.covered_split4 159744 (SixW25P.covered_split4 108544 (SixW25P.covered_split4 82944 (SixW25P.covered_split4 70144 (SixW25P.covered_split4 63744 wk23 (SixW25P.covered_split0 35584 (SixW25P.covered_split0 33152 wk24 (SixW25P.covered_split1 67584 (SixW25P.covered_split1 63744 wk25 (SixW25P.covered_split2 35072 (SixW25P.covered_split2 33408 wk26 (SixW25P.covered_split3 34816 (SixW25P.covered_split3 33024 wk27 (SixW25P.covered_split3 33920 wk28 wk29)) wk30)) wk31)) wk32)) wk33)) wk34) wk35) wk36) wk37) wk38)
  | 0, 1, 0, 1, 0, _, _, _, _, _ => rw [bd0_0, bd1_1, bd2_0, bd3_1, bd4_0]; exact (SixW25P.covered_split0 35584 (SixW25P.covered_split0 33152 wk39 (SixW25P.covered_split1 67584 (SixW25P.covered_split1 63744 wk40 (SixW25P.covered_split4 35584 (SixW25P.covered_split4 33152 wk41 (SixW25P.covered_split3 67584 (SixW25P.covered_split3 63744 wk42 (SixW25P.covered_split2 35072 (SixW25P.covered_split2 33408 wk43 (SixW25P.covered_split1 65664 (SixW25P.covered_split1 64704 (SixW25P.covered_split1 64224 wk44 (SixW25P.covered_split3 65664 (SixW25P.covered_split3 64704 wk45 (SixW25P.covered_split3 65184 wk46 wk47)) wk48)) (SixW25P.covered_split1 65184 (SixW25P.covered_split3 65664 (SixW25P.covered_split3 64704 wk49 (SixW25P.covered_split3 65184 (SixW25P.covered_split2 34240 (SixW25P.covered_split2 33824 wk50 (SixW25P.covered_split0 34368 (SixW25P.covered_split0 33760 wk51 (SixW25P.covered_split4 34368 (SixW25P.covered_split4 33760 wk52 (SixW25P.covered_split2 34032 wk53 (SixW25P.covered_split1 64944 wk54 wk55))) wk56)) wk57)) (SixW25P.covered_split0 34368 (SixW25P.covered_split0 33760 wk58 (SixW25P.covered_split4 34368 (SixW25P.covered_split4 33760 wk59 (SixW25P.covered_split2 34656 (SixW25P.covered_split1 64944 wk60 wk61) wk62)) wk63)) wk64)) (SixW25P.covered_split2 34240 wk65 wk66))) wk67) (SixW25P.covered_split3 65664 (SixW25P.covered_split3 64704 wk68 (SixW25P.covered_split2 34240 (SixW25P.covered_split2 33824 wk69 (SixW25P.covered_split0 34368 (SixW25P.covered_split0 33760 wk70 wk71) wk72)) wk73)) wk74))) wk75)) wk76)) wk77)) wk78)) wk79)) wk80)
  | 0, 1, 0, 1, 1, _, _, _, _, _ => rw [bd0_0, bd1_1, bd2_0, bd3_1, bd4_1]; exact (SixW25P.covered_split4 262144 (SixW25P.covered_split4 159744 (SixW25P.covered_split4 108544 (SixW25P.covered_split4 82944 (SixW25P.covered_split4 70144 (SixW25P.covered_split4 63744 wk81 (SixW25P.covered_split0 35584 (SixW25P.covered_split0 33152 wk82 (SixW25P.covered_split1 67584 (SixW25P.covered_split1 63744 wk83 (SixW25P.covered_split3 67584 (SixW25P.covered_split3 63744 wk84 (SixW25P.covered_split2 35072 (SixW25P.covered_split2 33408 wk85 (SixW25P.covered_split1 65664 (SixW25P.covered_split1 64704 wk86 (SixW25P.covered_split3 65664 (SixW25P.covered_split3 64704 wk87 (SixW25P.covered_split2 34240 (SixW25P.covered_split0 34368 (SixW25P.covered_split4 66944 (SixW25P.covered_split2 33824 wk88 (SixW25P.covered_split0 33760 wk89 (SixW25P.covered_split1 65184 wk90 wk91))) wk92) wk93) (SixW25P.covered_split4 66944 (SixW25P.covered_split1 65184 (SixW25P.covered_split3 65184 wk94 (SixW25P.covered_split0 34368 wk95 wk96)) wk97) wk98))) (SixW25P.covered_split4 66944 (SixW25P.covered_split2 34240 wk99 wk100) wk101))) wk102)) wk103)) wk104)) wk105)) wk106)) wk107) wk108) wk109) wk110) wk111)
  | 0, 1, 0, 2, 0, _, _, _, _, _ => rw [bd0_0, bd1_1, bd2_0, bd3_2, bd4_0]; exact wk112
  | 0, 1, 0, 2, 1, _, _, _, _, _ => rw [bd0_0, bd1_1, bd2_0, bd3_2, bd4_1]; exact wk113
  | 0, 1, 1, 0, 0, _, _, _, _, _ => rw [bd0_0, bd1_1, bd2_1, bd3_0, bd4_0]; exact wk114
  | 0, 1, 1, 0, 1, _, _, _, _, _ => rw [bd0_0, bd1_1, bd2_1, bd3_0, bd4_1]; exact (SixW25P.covered_split4 262144 (SixW25P.covered_split4 159744 (SixW25P.covered_split4 108544 (SixW25P.covered_split4 82944 (SixW25P.covered_split4 70144 (SixW25P.covered_split4 63744 wk115 (SixW25P.covered_split2 67584 (SixW25P.covered_split2 64000 wk116 (SixW25P.covered_split0 35584 (SixW25P.covered_split0 33152 wk117 (SixW25P.covered_split1 67584 (SixW25P.covered_split1 63744 wk118 (SixW25P.covered_split1 65664 (SixW25P.covered_split1 64704 wk119 (SixW25P.covered_split2 65792 (SixW25P.covered_split2 64896 wk120 (SixW25P.covered_split3 34816 (SixW25P.covered_split3 33024 wk121 (SixW25P.covered_split3 33920 wk122 (SixW25P.covered_split4 66944 (SixW25P.covered_split1 65184 (SixW25P.covered_split2 65344 wk123 wk124) (SixW25P.covered_split2 65344 (SixW25P.covered_split4 65344 wk125 wk126) (SixW25P.covered_split0 34368 (SixW25P.covered_split0 33760 wk127 wk128) wk129))) wk130))) wk131)) wk132)) wk133)) wk134)) wk135)) wk136)) wk137) wk138) wk139) wk140) wk141)
  | 0, 1, 1, 1, 0, _, _, _, _, _ => rw [bd0_0, bd1_1, bd2_1, bd3_1, bd4_0]; exact wk142
  | 0, 1, 1, 1, 1, _, _, _, _, _ => rw [bd0_0, bd1_1, bd2_1, bd3_1, bd4_1]; exact wk143
  | 0, 1, 1, 2, 0, _, _, _, _, _ => rw [bd0_0, bd1_1, bd2_1, bd3_2, bd4_0]; exact wk144
  | 0, 1, 1, 2, 1, _, _, _, _, _ => rw [bd0_0, bd1_1, bd2_1, bd3_2, bd4_1]; exact wk145
  | 0, 1, 2, 0, 0, _, _, _, _, _ => rw [bd0_0, bd1_1, bd2_2, bd3_0, bd4_0]; exact wk146
  | 0, 1, 2, 0, 1, _, _, _, _, _ => rw [bd0_0, bd1_1, bd2_2, bd3_0, bd4_1]; exact wk147
  | 0, 1, 2, 1, 0, _, _, _, _, _ => rw [bd0_0, bd1_1, bd2_2, bd3_1, bd4_0]; exact wk148
  | 0, 1, 2, 1, 1, _, _, _, _, _ => rw [bd0_0, bd1_1, bd2_2, bd3_1, bd4_1]; exact wk149
  | 0, 1, 2, 2, 0, _, _, _, _, _ => rw [bd0_0, bd1_1, bd2_2, bd3_2, bd4_0]; exact wk150
  | 0, 1, 2, 2, 1, _, _, _, _, _ => rw [bd0_0, bd1_1, bd2_2, bd3_2, bd4_1]; exact wk151
  | 0, 2, 0, 0, 0, _, _, _, _, _ => rw [bd0_0, bd1_2, bd2_0, bd3_0, bd4_0]; exact wk152
  | 0, 2, 0, 0, 1, _, _, _, _, _ => rw [bd0_0, bd1_2, bd2_0, bd3_0, bd4_1]; exact wk153
  | 0, 2, 0, 1, 0, _, _, _, _, _ => rw [bd0_0, bd1_2, bd2_0, bd3_1, bd4_0]; exact wk154
  | 0, 2, 0, 1, 1, _, _, _, _, _ => rw [bd0_0, bd1_2, bd2_0, bd3_1, bd4_1]; exact wk155
  | 0, 2, 0, 2, 0, _, _, _, _, _ => rw [bd0_0, bd1_2, bd2_0, bd3_2, bd4_0]; exact wk156
  | 0, 2, 0, 2, 1, _, _, _, _, _ => rw [bd0_0, bd1_2, bd2_0, bd3_2, bd4_1]; exact wk157
  | 0, 2, 1, 0, 0, _, _, _, _, _ => rw [bd0_0, bd1_2, bd2_1, bd3_0, bd4_0]; exact wk158
  | 0, 2, 1, 0, 1, _, _, _, _, _ => rw [bd0_0, bd1_2, bd2_1, bd3_0, bd4_1]; exact wk159
  | 0, 2, 1, 1, 0, _, _, _, _, _ => rw [bd0_0, bd1_2, bd2_1, bd3_1, bd4_0]; exact wk160
  | 0, 2, 1, 1, 1, _, _, _, _, _ => rw [bd0_0, bd1_2, bd2_1, bd3_1, bd4_1]; exact wk161
  | 0, 2, 1, 2, 0, _, _, _, _, _ => rw [bd0_0, bd1_2, bd2_1, bd3_2, bd4_0]; exact wk162
  | 0, 2, 1, 2, 1, _, _, _, _, _ => rw [bd0_0, bd1_2, bd2_1, bd3_2, bd4_1]; exact wk163
  | 0, 2, 2, 0, 0, _, _, _, _, _ => rw [bd0_0, bd1_2, bd2_2, bd3_0, bd4_0]; exact wk164
  | 0, 2, 2, 0, 1, _, _, _, _, _ => rw [bd0_0, bd1_2, bd2_2, bd3_0, bd4_1]; exact wk165
  | 0, 2, 2, 1, 0, _, _, _, _, _ => rw [bd0_0, bd1_2, bd2_2, bd3_1, bd4_0]; exact wk166
  | 0, 2, 2, 1, 1, _, _, _, _, _ => rw [bd0_0, bd1_2, bd2_2, bd3_1, bd4_1]; exact wk167
  | 0, 2, 2, 2, 0, _, _, _, _, _ => rw [bd0_0, bd1_2, bd2_2, bd3_2, bd4_0]; exact wk168
  | 0, 2, 2, 2, 1, _, _, _, _, _ => rw [bd0_0, bd1_2, bd2_2, bd3_2, bd4_1]; exact wk169
  | 1, 0, 0, 0, 0, _, _, _, _, _ => rw [bd0_1, bd1_0, bd2_0, bd3_0, bd4_0]; exact wk170
  | 1, 0, 0, 0, 1, _, _, _, _, _ => rw [bd0_1, bd1_0, bd2_0, bd3_0, bd4_1]; exact wk171
  | 1, 0, 0, 1, 0, _, _, _, _, _ => rw [bd0_1, bd1_0, bd2_0, bd3_1, bd4_0]; exact wk172
  | 1, 0, 0, 1, 1, _, _, _, _, _ => rw [bd0_1, bd1_0, bd2_0, bd3_1, bd4_1]; exact wk173
  | 1, 0, 0, 2, 0, _, _, _, _, _ => rw [bd0_1, bd1_0, bd2_0, bd3_2, bd4_0]; exact wk174
  | 1, 0, 0, 2, 1, _, _, _, _, _ => rw [bd0_1, bd1_0, bd2_0, bd3_2, bd4_1]; exact wk175
  | 1, 0, 1, 0, 0, _, _, _, _, _ => rw [bd0_1, bd1_0, bd2_1, bd3_0, bd4_0]; exact wk176
  | 1, 0, 1, 0, 1, _, _, _, _, _ => rw [bd0_1, bd1_0, bd2_1, bd3_0, bd4_1]; exact (SixW25P.covered_split0 262144 (SixW25P.covered_split4 262144 (SixW25P.covered_split0 159744 (SixW25P.covered_split4 159744 (SixW25P.covered_split0 108544 (SixW25P.covered_split4 108544 (SixW25P.covered_split0 82944 (SixW25P.covered_split0 70144 (SixW25P.covered_split0 63744 wk177 (SixW25P.covered_split4 82944 (SixW25P.covered_split4 70144 (SixW25P.covered_split4 63744 wk178 (SixW25P.covered_split2 67584 (SixW25P.covered_split2 64000 wk179 (SixW25P.covered_split2 65792 (SixW25P.covered_split2 64896 (SixW25P.covered_split1 34816 (SixW25P.covered_split1 33024 wk180 (SixW25P.covered_split1 33920 wk181 (SixW25P.covered_split0 66944 (SixW25P.covered_split3 34816 (SixW25P.covered_split3 33024 wk182 (SixW25P.covered_split3 33920 wk183 (SixW25P.covered_split4 66944 (SixW25P.covered_split2 64448 wk184 (SixW25P.covered_split0 65344 (SixW25P.covered_split0 64544 wk185 (SixW25P.covered_split4 65344 wk186 wk187)) wk188)) wk189))) wk190) wk191))) wk192) (SixW25P.covered_split1 34816 (SixW25P.covered_split1 33024 wk193 (SixW25P.covered_split1 33920 wk194 (SixW25P.covered_split3 34816 (SixW25P.covered_split3 33024 wk195 (SixW25P.covered_split3 33920 wk196 (SixW25P.covered_split0 66944 (SixW25P.covered_split4 66944 (SixW25P.covered_split2 65344 (SixW25P.covered_split0 65344 (SixW25P.covered_split0 64544 wk197 (SixW25P.covered_split1 34368 (SixW25P.covered_split3 34368 (SixW25P.covered_split4 65344 wk198 wk199) wk200) wk201)) wk202) wk203) wk204) wk205))) wk206))) wk207)) wk208)) wk209)) wk210) wk211)) wk212) wk213) wk214) wk215) wk216) wk217) wk218) wk219)
  | 1, 0, 1, 1, 0, _, _, _, _, _ => rw [bd0_1, bd1_0, bd2_1, bd3_1, bd4_0]; exact wk220
  | 1, 0, 1, 1, 1, _, _, _, _, _ => rw [bd0_1, bd1_0, bd2_1, bd3_1, bd4_1]; exact wk221
  | 1, 0, 1, 2, 0, _, _, _, _, _ => rw [bd0_1, bd1_0, bd2_1, bd3_2, bd4_0]; exact wk222
  | 1, 0, 1, 2, 1, _, _, _, _, _ => rw [bd0_1, bd1_0, bd2_1, bd3_2, bd4_1]; exact wk223
  | 1, 0, 2, 0, 0, _, _, _, _, _ => rw [bd0_1, bd1_0, bd2_2, bd3_0, bd4_0]; exact wk224
  | 1, 0, 2, 0, 1, _, _, _, _, _ => rw [bd0_1, bd1_0, bd2_2, bd3_0, bd4_1]; exact wk225
  | 1, 0, 2, 1, 0, _, _, _, _, _ => rw [bd0_1, bd1_0, bd2_2, bd3_1, bd4_0]; exact wk226
  | 1, 0, 2, 1, 1, _, _, _, _, _ => rw [bd0_1, bd1_0, bd2_2, bd3_1, bd4_1]; exact wk227
  | 1, 0, 2, 2, 0, _, _, _, _, _ => rw [bd0_1, bd1_0, bd2_2, bd3_2, bd4_0]; exact wk228
  | 1, 0, 2, 2, 1, _, _, _, _, _ => rw [bd0_1, bd1_0, bd2_2, bd3_2, bd4_1]; exact wk229
  | 1, 1, 0, 0, 0, _, _, _, _, _ => rw [bd0_1, bd1_1, bd2_0, bd3_0, bd4_0]; exact wk230
  | 1, 1, 0, 0, 1, _, _, _, _, _ => rw [bd0_1, bd1_1, bd2_0, bd3_0, bd4_1]; exact wk231
  | 1, 1, 0, 1, 0, _, _, _, _, _ => rw [bd0_1, bd1_1, bd2_0, bd3_1, bd4_0]; exact wk232
  | 1, 1, 0, 1, 1, _, _, _, _, _ => rw [bd0_1, bd1_1, bd2_0, bd3_1, bd4_1]; exact wk233
  | 1, 1, 0, 2, 0, _, _, _, _, _ => rw [bd0_1, bd1_1, bd2_0, bd3_2, bd4_0]; exact wk234
  | 1, 1, 0, 2, 1, _, _, _, _, _ => rw [bd0_1, bd1_1, bd2_0, bd3_2, bd4_1]; exact wk235
  | 1, 1, 1, 0, 0, _, _, _, _, _ => rw [bd0_1, bd1_1, bd2_1, bd3_0, bd4_0]; exact wk236
  | 1, 1, 1, 0, 1, _, _, _, _, _ => rw [bd0_1, bd1_1, bd2_1, bd3_0, bd4_1]; exact wk237
  | 1, 1, 1, 1, 0, _, _, _, _, _ => rw [bd0_1, bd1_1, bd2_1, bd3_1, bd4_0]; exact wk238
  | 1, 1, 1, 1, 1, _, _, _, _, _ => rw [bd0_1, bd1_1, bd2_1, bd3_1, bd4_1]; exact wk239
  | 1, 1, 1, 2, 0, _, _, _, _, _ => rw [bd0_1, bd1_1, bd2_1, bd3_2, bd4_0]; exact wk240
  | 1, 1, 1, 2, 1, _, _, _, _, _ => rw [bd0_1, bd1_1, bd2_1, bd3_2, bd4_1]; exact wk241
  | 1, 1, 2, 0, 0, _, _, _, _, _ => rw [bd0_1, bd1_1, bd2_2, bd3_0, bd4_0]; exact wk242
  | 1, 1, 2, 0, 1, _, _, _, _, _ => rw [bd0_1, bd1_1, bd2_2, bd3_0, bd4_1]; exact wk243
  | 1, 1, 2, 1, 0, _, _, _, _, _ => rw [bd0_1, bd1_1, bd2_2, bd3_1, bd4_0]; exact wk244
  | 1, 1, 2, 1, 1, _, _, _, _, _ => rw [bd0_1, bd1_1, bd2_2, bd3_1, bd4_1]; exact wk245
  | 1, 1, 2, 2, 0, _, _, _, _, _ => rw [bd0_1, bd1_1, bd2_2, bd3_2, bd4_0]; exact wk246
  | 1, 1, 2, 2, 1, _, _, _, _, _ => rw [bd0_1, bd1_1, bd2_2, bd3_2, bd4_1]; exact wk247
  | 1, 2, 0, 0, 0, _, _, _, _, _ => rw [bd0_1, bd1_2, bd2_0, bd3_0, bd4_0]; exact wk248
  | 1, 2, 0, 0, 1, _, _, _, _, _ => rw [bd0_1, bd1_2, bd2_0, bd3_0, bd4_1]; exact wk249
  | 1, 2, 0, 1, 0, _, _, _, _, _ => rw [bd0_1, bd1_2, bd2_0, bd3_1, bd4_0]; exact wk250
  | 1, 2, 0, 1, 1, _, _, _, _, _ => rw [bd0_1, bd1_2, bd2_0, bd3_1, bd4_1]; exact wk251
  | 1, 2, 0, 2, 0, _, _, _, _, _ => rw [bd0_1, bd1_2, bd2_0, bd3_2, bd4_0]; exact wk252
  | 1, 2, 0, 2, 1, _, _, _, _, _ => rw [bd0_1, bd1_2, bd2_0, bd3_2, bd4_1]; exact wk253
  | 1, 2, 1, 0, 0, _, _, _, _, _ => rw [bd0_1, bd1_2, bd2_1, bd3_0, bd4_0]; exact wk254
  | 1, 2, 1, 0, 1, _, _, _, _, _ => rw [bd0_1, bd1_2, bd2_1, bd3_0, bd4_1]; exact wk255
  | 1, 2, 1, 1, 0, _, _, _, _, _ => rw [bd0_1, bd1_2, bd2_1, bd3_1, bd4_0]; exact wk256
  | 1, 2, 1, 1, 1, _, _, _, _, _ => rw [bd0_1, bd1_2, bd2_1, bd3_1, bd4_1]; exact wk257
  | 1, 2, 1, 2, 0, _, _, _, _, _ => rw [bd0_1, bd1_2, bd2_1, bd3_2, bd4_0]; exact wk258
  | 1, 2, 1, 2, 1, _, _, _, _, _ => rw [bd0_1, bd1_2, bd2_1, bd3_2, bd4_1]; exact wk259
  | 1, 2, 2, 0, 0, _, _, _, _, _ => rw [bd0_1, bd1_2, bd2_2, bd3_0, bd4_0]; exact wk260
  | 1, 2, 2, 0, 1, _, _, _, _, _ => rw [bd0_1, bd1_2, bd2_2, bd3_0, bd4_1]; exact wk261
  | 1, 2, 2, 1, 0, _, _, _, _, _ => rw [bd0_1, bd1_2, bd2_2, bd3_1, bd4_0]; exact wk262
  | 1, 2, 2, 1, 1, _, _, _, _, _ => rw [bd0_1, bd1_2, bd2_2, bd3_1, bd4_1]; exact wk263
  | 1, 2, 2, 2, 0, _, _, _, _, _ => rw [bd0_1, bd1_2, bd2_2, bd3_2, bd4_0]; exact wk264
  | 1, 2, 2, 2, 1, _, _, _, _, _ => rw [bd0_1, bd1_2, bd2_2, bd3_2, bd4_1]; exact wk265
  | i + 2, _, _, _, _, hi, _, _, _, _ => exact absurd hi (by omega)
  | _, i + 3, _, _, _, _, hi, _, _, _ => exact absurd hi (by omega)
  | _, _, i + 3, _, _, _, _, hi, _, _ => exact absurd hi (by omega)
  | _, _, _, i + 3, _, _, _, _, hi, _ => exact absurd hi (by omega)
  | _, _, _, _, i + 2, _, _, _, _, hi => exact absurd hi (by omega)

theorem cert : ∀ g0 g1 g2 g3 g4 : ℝ, 0 ≤ g0 → 0 ≤ g1 → 0 ≤ g2 → 0 ≤ g3 → 0 ≤ g4 → (SixW25P.cN : ℝ) / SixW25P.SA ≤ SixW25P.G g0 g1 g2 g3 g4 ∨ g4 < g0 :=
  SixW25P.of_check cover0 cover1 cover2 cover3 cover4 466944 278528 253952 278528 466944
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) cover0_ok cover1_ok cover2_ok cover3_ok cover4_ok (by decide +kernel) run_ok

end Zeta23Ext.Bridge.ThreePoint.SixW25PData

end

/-! ###### submission layer: constant-independent part ###### -/

noncomputable section

namespace RiemannFail

open Filter
open Zeta23 Zeta23.ThmD Zeta23Ext.Bridge Zeta23Ext.BridgeW

/-- `(√2)⁻¹ = √2/2`. -/
theorem inv_sqrt_two : (Real.sqrt 2)⁻¹ = Real.sqrt 2 / 2 := by
  have hne : Real.sqrt 2 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  rw [inv_eq_one_div, div_eq_div_iff hne two_ne_zero, one_mul,
    Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 2)]

/-- `HD 1 = 3/2 − γ` with `γ = (√2/2)·cot(√2/2)`, the constant `ThreePoint.gam`. -/
theorem HD_one_eq_gam : HD 1 = 3 / 2 - ThreePoint.gam := by
  rw [HD_one, inv_sqrt_two]
  unfold ThreePoint.gam
  ring

/-- `H = HD 1` enclosed to `1.1·10⁻⁸`, from `ThreePoint.gam_bounds`. -/
theorem HD_one_bounds :
    (6725006982 / 10000000000 : ℝ) ≤ HD 1 ∧ HD 1 ≤ 6725007093 / 10000000000 := by
  have hg := ThreePoint.gam_bounds
  rw [HD_one_eq_gam]
  norm_num at hg ⊢
  constructor <;> linarith [hg.1, hg.2]

/-- The library's Theorem-D constant `cStar 1` (division-safe form) equals the challenge's
`cMT` (the tan form at ϑ = 1/√2): by `cStar_eq_tan_form` and unfolding `theta 1 = 1/√2`. -/
theorem cStar_one_eq_cMT : Zeta23.ThmD.cStar 1 = cMT := by
  rw [Zeta23.ThmD.cStar_eq_tan_form zero_le_one le_rfl]
  unfold cMT Zeta23.ThmD.theta
  rfl

/-- Simple on-line zeros are among the distinct on-line zeros. -/
theorem N0simple_le_N0star (T₁ T₂ : ℝ) : Zeta23.N0simple T₁ T₂ ≤ Zeta23.N0star T₁ T₂ := by
  refine Set.ncard_le_ncard Set.inter_subset_left ?_
  refine (Zeta23.zetaSeam.finite_window T₁ T₂).subset ?_
  rintro ρ ⟨⟨h1, h2, h3⟩, _⟩
  exact ⟨h1, h2, h3⟩


end RiemannFail

end

/-! ###### the 6-point weighted bound from the checked certificate `SixW25P` ###### -/

noncomputable section

namespace RiemannFail

open Filter
open Zeta23 Zeta23.ThmD Zeta23Ext.Bridge Zeta23Ext.BridgeW Zeta23Ext.Bridge.ThreePoint

/-- the pair weights `a_ij` (zero unless `i < j`), over `100000000` -/
def aW : Fin 6 → Fin 6 → ℝ
  | 0, 1 => (25326800 : ℝ) / 100000000
  | 0, 2 => (62369200 : ℝ) / 100000000
  | 0, 3 => (40126500 : ℝ) / 100000000
  | 0, 4 => (99999900 : ℝ) / 100000000
  | 0, 5 => (200000000 : ℝ) / 100000000
  | 1, 2 => (48244400 : ℝ) / 100000000
  | 1, 3 => (37630700 : ℝ) / 100000000
  | 1, 4 => (119746800 : ℝ) / 100000000
  | 1, 5 => (99999900 : ℝ) / 100000000
  | 2, 3 => (52857300 : ℝ) / 100000000
  | 2, 4 => (37630700 : ℝ) / 100000000
  | 2, 5 => (40126500 : ℝ) / 100000000
  | 3, 4 => (48244400 : ℝ) / 100000000
  | 3, 5 => (62369200 : ℝ) / 100000000
  | 4, 5 => (25326800 : ℝ) / 100000000
  | _, _ => 0

/-- the per-gap pressures, over `100000000` -/
def bW : Fin 5 → ℝ
  | 0 => (24896 : ℝ) / 100000000
  | 1 => (42034 : ℝ) / 100000000
  | 2 => (46137 : ℝ) / 100000000
  | 3 => (42034 : ℝ) / 100000000
  | 4 => (24896 : ℝ) / 100000000

def WW : WCert 6 := ⟨aW, bW⟩

theorem aW_0_0 : aW 0 0 = 0 := rfl
theorem aW_0_1 : aW 0 1 = (25326800 : ℝ) / 100000000 := rfl
theorem aW_0_2 : aW 0 2 = (62369200 : ℝ) / 100000000 := rfl
theorem aW_0_3 : aW 0 3 = (40126500 : ℝ) / 100000000 := rfl
theorem aW_0_4 : aW 0 4 = (99999900 : ℝ) / 100000000 := rfl
theorem aW_0_5 : aW 0 5 = (200000000 : ℝ) / 100000000 := rfl
theorem aW_1_0 : aW 1 0 = 0 := rfl
theorem aW_1_1 : aW 1 1 = 0 := rfl
theorem aW_1_2 : aW 1 2 = (48244400 : ℝ) / 100000000 := rfl
theorem aW_1_3 : aW 1 3 = (37630700 : ℝ) / 100000000 := rfl
theorem aW_1_4 : aW 1 4 = (119746800 : ℝ) / 100000000 := rfl
theorem aW_1_5 : aW 1 5 = (99999900 : ℝ) / 100000000 := rfl
theorem aW_2_0 : aW 2 0 = 0 := rfl
theorem aW_2_1 : aW 2 1 = 0 := rfl
theorem aW_2_2 : aW 2 2 = 0 := rfl
theorem aW_2_3 : aW 2 3 = (52857300 : ℝ) / 100000000 := rfl
theorem aW_2_4 : aW 2 4 = (37630700 : ℝ) / 100000000 := rfl
theorem aW_2_5 : aW 2 5 = (40126500 : ℝ) / 100000000 := rfl
theorem aW_3_0 : aW 3 0 = 0 := rfl
theorem aW_3_1 : aW 3 1 = 0 := rfl
theorem aW_3_2 : aW 3 2 = 0 := rfl
theorem aW_3_3 : aW 3 3 = 0 := rfl
theorem aW_3_4 : aW 3 4 = (48244400 : ℝ) / 100000000 := rfl
theorem aW_3_5 : aW 3 5 = (62369200 : ℝ) / 100000000 := rfl
theorem aW_4_0 : aW 4 0 = 0 := rfl
theorem aW_4_1 : aW 4 1 = 0 := rfl
theorem aW_4_2 : aW 4 2 = 0 := rfl
theorem aW_4_3 : aW 4 3 = 0 := rfl
theorem aW_4_4 : aW 4 4 = 0 := rfl
theorem aW_4_5 : aW 4 5 = (25326800 : ℝ) / 100000000 := rfl
theorem aW_5_0 : aW 5 0 = 0 := rfl
theorem aW_5_1 : aW 5 1 = 0 := rfl
theorem aW_5_2 : aW 5 2 = 0 := rfl
theorem aW_5_3 : aW 5 3 = 0 := rfl
theorem aW_5_4 : aW 5 4 = 0 := rfl
theorem aW_5_5 : aW 5 5 = 0 := rfl
theorem bW_0 : bW 0 = (24896 : ℝ) / 100000000 := rfl
theorem bW_1 : bW 1 = (42034 : ℝ) / 100000000 := rfl
theorem bW_2 : bW 2 = (46137 : ℝ) / 100000000 := rfl
theorem bW_3 : bW 3 = (42034 : ℝ) / 100000000 := rfl
theorem bW_4 : bW 4 = (24896 : ℝ) / 100000000 := rfl

theorem WW_B : WW.B = (179997 : ℝ) / 100000000 := by
  show (∑ r : Fin 5, bW r) = _
  norm_num [Fin.sum_univ_five, bW_0, bW_1, bW_2, bW_3, bW_4]

theorem WW_a_nonneg : ∀ i j, 0 ≤ WW.a i j := by
  intro i j
  unfold WW
  match i, j with
  | 0, 0 => show (0:ℝ) ≤ aW 0 0; norm_num [aW_0_0]
  | 0, 1 => show (0:ℝ) ≤ aW 0 1; norm_num [aW_0_1]
  | 0, 2 => show (0:ℝ) ≤ aW 0 2; norm_num [aW_0_2]
  | 0, 3 => show (0:ℝ) ≤ aW 0 3; norm_num [aW_0_3]
  | 0, 4 => show (0:ℝ) ≤ aW 0 4; norm_num [aW_0_4]
  | 0, 5 => show (0:ℝ) ≤ aW 0 5; norm_num [aW_0_5]
  | 1, 0 => show (0:ℝ) ≤ aW 1 0; norm_num [aW_1_0]
  | 1, 1 => show (0:ℝ) ≤ aW 1 1; norm_num [aW_1_1]
  | 1, 2 => show (0:ℝ) ≤ aW 1 2; norm_num [aW_1_2]
  | 1, 3 => show (0:ℝ) ≤ aW 1 3; norm_num [aW_1_3]
  | 1, 4 => show (0:ℝ) ≤ aW 1 4; norm_num [aW_1_4]
  | 1, 5 => show (0:ℝ) ≤ aW 1 5; norm_num [aW_1_5]
  | 2, 0 => show (0:ℝ) ≤ aW 2 0; norm_num [aW_2_0]
  | 2, 1 => show (0:ℝ) ≤ aW 2 1; norm_num [aW_2_1]
  | 2, 2 => show (0:ℝ) ≤ aW 2 2; norm_num [aW_2_2]
  | 2, 3 => show (0:ℝ) ≤ aW 2 3; norm_num [aW_2_3]
  | 2, 4 => show (0:ℝ) ≤ aW 2 4; norm_num [aW_2_4]
  | 2, 5 => show (0:ℝ) ≤ aW 2 5; norm_num [aW_2_5]
  | 3, 0 => show (0:ℝ) ≤ aW 3 0; norm_num [aW_3_0]
  | 3, 1 => show (0:ℝ) ≤ aW 3 1; norm_num [aW_3_1]
  | 3, 2 => show (0:ℝ) ≤ aW 3 2; norm_num [aW_3_2]
  | 3, 3 => show (0:ℝ) ≤ aW 3 3; norm_num [aW_3_3]
  | 3, 4 => show (0:ℝ) ≤ aW 3 4; norm_num [aW_3_4]
  | 3, 5 => show (0:ℝ) ≤ aW 3 5; norm_num [aW_3_5]
  | 4, 0 => show (0:ℝ) ≤ aW 4 0; norm_num [aW_4_0]
  | 4, 1 => show (0:ℝ) ≤ aW 4 1; norm_num [aW_4_1]
  | 4, 2 => show (0:ℝ) ≤ aW 4 2; norm_num [aW_4_2]
  | 4, 3 => show (0:ℝ) ≤ aW 4 3; norm_num [aW_4_3]
  | 4, 4 => show (0:ℝ) ≤ aW 4 4; norm_num [aW_4_4]
  | 4, 5 => show (0:ℝ) ≤ aW 4 5; norm_num [aW_4_5]
  | 5, 0 => show (0:ℝ) ≤ aW 5 0; norm_num [aW_5_0]
  | 5, 1 => show (0:ℝ) ≤ aW 5 1; norm_num [aW_5_1]
  | 5, 2 => show (0:ℝ) ≤ aW 5 2; norm_num [aW_5_2]
  | 5, 3 => show (0:ℝ) ≤ aW 5 3; norm_num [aW_5_3]
  | 5, 4 => show (0:ℝ) ≤ aW 5 4; norm_num [aW_5_4]
  | 5, 5 => show (0:ℝ) ≤ aW 5 5; norm_num [aW_5_5]

theorem WW_bmin : ∀ r, ((24896 : ℝ) / 100000000) ≤ WW.b r := by
  intro r
  unfold WW
  match r with
  | 0 => show ((24896 : ℝ) / 100000000) ≤ bW 0; norm_num [bW_0]
  | 1 => show ((24896 : ℝ) / 100000000) ≤ bW 1; norm_num [bW_1]
  | 2 => show ((24896 : ℝ) / 100000000) ≤ bW 2; norm_num [bW_2]
  | 3 => show ((24896 : ℝ) / 100000000) ≤ bW 3; norm_num [bW_3]
  | 4 => show ((24896 : ℝ) / 100000000) ≤ bW 4; norm_num [bW_4]

theorem WW_capacity : ∀ s : ℕ, WW.spanMass s ≤ 2 := by
  intro s
  unfold WCert.spanMass WW
  rcases lt_or_ge s 6 with hs | hs
  · interval_cases s <;> simp (config := { decide := true }) only [Fin.sum_univ_six, aW_0_0, aW_0_1, aW_0_2, aW_0_3, aW_0_4, aW_0_5, aW_1_0, aW_1_1, aW_1_2, aW_1_3, aW_1_4, aW_1_5, aW_2_0, aW_2_1, aW_2_2, aW_2_3, aW_2_4, aW_2_5, aW_3_0, aW_3_1, aW_3_2, aW_3_3, aW_3_4, aW_3_5, aW_4_0, aW_4_1, aW_4_2, aW_4_3, aW_4_4, aW_4_5, aW_5_0, aW_5_1, aW_5_2, aW_5_3, aW_5_4, aW_5_5, if_true, if_false] <;> norm_num
  · have h0 : ∀ i j : Fin 6, ¬ ((i : ℕ) < (j : ℕ) ∧ (j : ℕ) - (i : ℕ) = s) := by
      intro i j ⟨_, h⟩
      have := j.2
      omega
    simp only [h0, if_false, Finset.sum_const_zero]
    norm_num

theorem WW_adm : WW.Adm := ⟨WW_a_nonneg, fun r => le_trans (by norm_num) (WW_bmin r), WW_capacity⟩

private lemma sumQ (f : Fin (6 - 1) → ℝ) : ∑ i, f i = f 0 + f 1 + f 2 + f 3 + f 4 := by
  show ∑ i : Fin 5, f i = f 0 + f 1 + f 2 + f 3 + f 4
  exact Fin.sum_univ_five f

/-- `Fw WW` written out on the gaps: it is the checker's functional `SixW25P.G`. -/
theorem Fw_WW (g : Fin (6 - 1) → ℝ) : Fw WW g = SixW25P.G (g 0) (g 1) (g 2) (g 3) (g 4) := by
  show (∑ r : Fin 5, bW r * g r) + (∑ i : Fin 6, ∑ j : Fin 6, if (i : ℕ) < (j : ℕ) then aW i j * wfun (ptsN 6 g j - ptsN 6 g i) else 0) = _
  unfold SixW25P.G ptsN
  simp only [sumQ, Fin.sum_univ_six, Fin.sum_univ_five, Fin.isValue, aW_0_0, aW_0_1, aW_0_2, aW_0_3, aW_0_4, aW_0_5, aW_1_0, aW_1_1, aW_1_2, aW_1_3, aW_1_4, aW_1_5, aW_2_0, aW_2_1, aW_2_2, aW_2_3, aW_2_4, aW_2_5, aW_3_0, aW_3_1, aW_3_2, aW_3_3, aW_3_4, aW_3_5, aW_4_0, aW_4_1, aW_4_2, aW_4_3, aW_4_4, aW_4_5, aW_5_0, aW_5_1, aW_5_2, aW_5_3, aW_5_4, aW_5_5, bW_0, bW_1, bW_2, bW_3, bW_4]
  norm_num [SixW25P.SA]
  try ring

theorem G_rev (x0 x1 x2 x3 x4 : ℝ) : SixW25P.G x4 x3 x2 x1 x0 = SixW25P.G x0 x1 x2 x3 x4 := by
  unfold SixW25P.G; ring_nf

/-- the half-space certificate, completed by reflection (the weights are symmetric) -/
theorem cert_full : ∀ x0 x1 x2 x3 x4 : ℝ, 0 ≤ x0 → 0 ≤ x1 → 0 ≤ x2 → 0 ≤ x3 → 0 ≤ x4 → (SixW25P.cN : ℝ) / SixW25P.SA ≤ SixW25P.G x0 x1 x2 x3 x4 := by
  intro x0 x1 x2 x3 x4 h0 h1 h2 h3 h4
  rcases lt_or_ge x4 x0 with hlt | hle
  · rcases SixW25PData.cert x4 x3 x2 x1 x0 h4 h3 h2 h1 h0 with h | h
    · rw [← G_rev]; exact h
    · exact absurd h (not_lt.mpr hlt.le)
  · rcases SixW25PData.cert x0 x1 x2 x3 x4 h0 h1 h2 h3 h4 with h | h
    · exact h
    · exact absurd h (not_lt.mpr hle)

/-- the certificate hypothesis of `n_point_bound_w'` at `n = 6` -/
theorem cert_WW : ∀ g : Fin (6 - 1) → ℝ, (∀ i, 0 ≤ g i) → (349330 : ℝ) / 100000000 ≤ Fw WW g := by
  intro g hg
  rw [Fw_WW]
  have h := cert_full (g 0) (g 1) (g 2) (g 3) (g 4) (hg 0) (hg 1) (hg 2) (hg 3) (hg 4)
  simp only [SixW25P.cN, SixW25P.SA] at h
  push_cast at h
  exact h

/-- `Phi_w' 6 c 291 B` as an exact rational in `HD 1` -/
theorem Phi_WW : Phi_w' 6 ((349330 : ℝ) / 100000000) 291 ((179997 : ℝ) / 100000000)
    = (14550000000 * HD 1 - 25739571) / 14500045810 := by
  unfold Phi_w'
  push_cast
  rw [div_eq_div_iff (by norm_num) (by norm_num)]
  ring

/-- **The 6-point weighted bound, unconditional.** -/
theorem bound_WW :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      ((14550000000 * HD 1 - 25739571) / 14500045810 - ε) * (Zeta23.Ncount T (2 * T) : ℝ) ≤ Zeta23.N0simple T (2 * T) := by
  rw [← Phi_WW, ← WW_B]
  exact n_point_bound_w' 6 ((349330 : ℝ) / 100000000) 291 WW (by norm_num) (by norm_num) WW_adm
    (by norm_num : (0 : ℝ) < (24896 : ℝ) / 100000000) WW_bmin (by norm_num) cert_WW (by norm_num)

/-- The candidate rational sits below the proved constant. -/
theorem candidateKappa_le : candidateKappa ≤ (14550000000 * HD 1 - 25739571) / 14500045810 := by
  unfold candidateKappa
  rw [le_div_iff₀ (by norm_num : (0:ℝ) < 14500045810)]
  linarith [HD_one_bounds.1]

/-- The dyadic bound at the candidate rational, in the library's vocabulary. -/
theorem dyadic :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (candidateKappa - ε) * (Zeta23.Ncount T (2 * T) : ℝ) ≤ Zeta23.N0star T (2 * T) := by
  intro ε hε
  obtain ⟨T₀, hT₀⟩ := bound_WW ε hε
  refine ⟨T₀, fun T hT => ?_⟩
  have h1 := hT₀ T hT
  have hN : (0:ℝ) ≤ (Zeta23.Ncount T (2 * T) : ℝ) := Nat.cast_nonneg _
  have h2 : (Zeta23.N0simple T (2 * T) : ℝ) ≤ Zeta23.N0star T (2 * T) := by
    exact_mod_cast N0simple_le_N0star T (2 * T)
  have h0 : (candidateKappa - ε) * (Zeta23.Ncount T (2 * T) : ℝ)
      ≤ ((14550000000 * HD 1 - 25739571) / 14500045810 - ε) * (Zeta23.Ncount T (2 * T) : ℝ) :=
    mul_le_mul_of_nonneg_right (by linarith [candidateKappa_le]) hN
  linarith

/-- The cumulative form, through the library's dyadic-to-cumulative wrapper. -/
theorem cumulative :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (candidateKappa - ε) * (Zeta23.Ncount 0 T : ℝ) ≤ Zeta23.N0star 0 T :=
  Zeta23.cumulative_of_dyadic Zeta23.zetaSeam Zeta23.paperInputs_zeta.RvM
    (fun _ _ _ => Zeta23.N0star_add' Zeta23.zetaSeam) dyadic

/-- Strict improvement over the record.  The board pins `currentRecordKappa` as the exact rational
of the last accepted candidate, so the comparison is decided by `norm_num`; the second branch covers
the original closed form `2 - 1/cMT = HD 1`, through `cStar_one_eq_cMT` and the enclosure of `HD 1`. -/
theorem strict : currentRecordKappa < candidateKappa := by
  unfold currentRecordKappa candidateKappa
  first
    | (norm_num; done)
    | (rw [← cStar_one_eq_cMT]
       have h := HD_one_bounds.2
       unfold Zeta23.ThmD.HD at h
       linarith)

end RiemannFail

end

/-! ###### the three scored theorems, statements as generated by the trusted template ###### -/

noncomputable section

/-- The submitted bound is strictly larger than the current formal record. -/
theorem candidate_strict_improvement :
    currentRecordKappa < candidateKappa :=
  RiemannFail.strict

/-- The candidate proves a larger unconditional critical-line proportion on dyadic windows. -/
theorem candidate_critical_line_bound :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (candidateKappa - ε) * (Ncount T (2 * T) : ℝ) ≤ N0star T (2 * T) :=
  RiemannFail.dyadic

/-- The same unconditional bound in cumulative windows. -/
theorem candidate_critical_line_bound_cumulative :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (candidateKappa - ε) * (Ncount 0 T : ℝ) ≤ N0star 0 T :=
  RiemannFail.cumulative

end

#print axioms candidate_strict_improvement
#print axioms candidate_critical_line_bound
#print axioms candidate_critical_line_bound_cumulative
