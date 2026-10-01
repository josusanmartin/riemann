/-
Riemann.fail submission — an unconditional critical-line proportion of 42057/62500 = 0.6729120,
strictly above the board's current record `currentRecordKappa` (the exact rational of the last accepted
candidate; the original closed form 2 − 1/cMT = 0.67250070… is covered as a fallback).

The mathematics: Ainta's n-point simple-zero refinement of Theorem D of the pinned Zeta23
development (the Montgomery–Taylor window at λ = 1), at n = 6 with pair weights a_ij and
per-gap pressures b_r (the weighted bookkeeping of `n_point_bound_w'`), made unconditional by a
kernel-checked finite certificate `SixW8`: a table of 6814 interval cells, each certified by
an integer pipeline (Taylor enclosures of cos and sin at scale 10¹⁵, `cellN_soundZ`), and a
bisection over the gaps with 18058 leaves over the half-space
g₀ ≤ g₄; the pair weights are symmetric under gap reversal, so the other half follows by
the reflection `G_rev`.  The resulting constant is
`(30800000000·H − 54539091)/30700123625 = 0.67291202…` with `H = HD 1 = 3/2 − (1/√2)cot(1/√2)`, and `H` is
enclosed to `1.1·10⁻⁸` by a twelve-term Taylor argument, which is what places the exact rational
`42057/62500` strictly between the record and the proved constant.

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

/-! ###### natural-number checker for the 6-point weighted certificate `SixW8` ###### -/

section SixW8Defs

namespace Zeta23Ext.Bridge.ThreePoint

structure CellN where
  (key : ℕ) (WN : ℕ)

instance : Inhabited CellN := ⟨⟨0, 0⟩⟩

def SC : ℕ := 32768
def SW : ℕ := 10000000000000
def SC4 : ℕ := 8192

/-- a cell's endpoints are packed into one key `LN * KB + UN` (every coordinate is below `KB`), so the table is
searched with one comparison per level -/
def KB : ℕ := 1048576
def CellN.LN (c : CellN) : ℕ := c.key / KB
def CellN.UN (c : CellN) : ℕ := c.key % KB

/-- the anchor index `k` (anchor at `k/2`) nearest the cell's midpoint, and the side of that anchor the cell lies on -/
def CellN.k (c : CellN) : ℕ := (2 * (c.LN + c.UN) + SC) / (2 * SC)
def CellN.side (c : CellN) : Bool := Nat.ble (c.k * SC) (2 * c.LN)

/-- the rational cell a natural-number cell denotes (the integer check `okZ` is what the table is verified by) -/
def CellN.toQ (c : CellN) : Cell := ⟨(c.LN : ℚ) / SC, (c.UN : ℚ) / SC, c.k, c.side, (c.WN : ℚ) / SW⟩

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

inductive CTN
  | nil
  | node (l : CTN) (c : CellN) (r : CTN)

namespace CTN
def toList : CTN → List CellN
  | nil => []
  | node l c r => l.toList ++ c :: r.toList
def allOk : CTN → Bool
  | nil => true
  | node l c r => l.allOk && c.okZ && r.allOk
def find : CTN → ℕ → Option CellN
  | nil, _ => none
  | node l c r, q =>
      bif Nat.blt q c.key then l.find q
      else bif Nat.blt c.key q then r.find q
      else some c
end CTN

/-- far pieces (start at or beyond `XFARN`) are rounded outward to the fine grid `2^FSH`; the chain check still
verifies coverage, so this only changes which cells are consulted -/
def XFARN : ℕ := 98304
def roundFar (a b : ℕ) : ℕ × ℕ :=
  bif Nat.ble XFARN a then ((a >>> 7) <<< 7, ((b + 127) >>> 7) <<< 7) else (a, b)

def piecesN : ℕ → ℕ → ℕ → List (ℕ × ℕ)
  | 0, a, hi => [(roundFar a hi)]
  | fuel + 1, a, hi =>
      let q := ((a >>> 13) + 1) <<< 13
      bif Nat.blt q hi then (roundFar a q) :: piecesN fuel q hi else [(roundFar a hi)]

def lookupAllN (t : CTN) : List (ℕ × ℕ) → Option (List CellN)
  | [] => some []
  | (a, b) :: rest =>
      match t.find (a * KB + b), lookupAllN t rest with
      | some c, some cs => some (c :: cs)
      | _, _ => none

def chainOKN : ℕ → ℕ → List CellN → Bool
  | lo, hi, [] => Nat.ble hi lo
  | lo, hi, c :: rest => Nat.ble c.LN lo && chainOKN c.UN hi rest

def chainWN : List CellN → ℕ
  | [] => 0
  | c :: rest => bif rest.isEmpty then c.WN else bif Nat.ble c.WN (chainWN rest) then c.WN else chainWN rest

def piecesN' (lo hi : ℕ) : List (ℕ × ℕ) := piecesN 64 lo hi

def termWNcore (t : CTN) (lo hi : ℕ) (ps : List (ℕ × ℕ)) : ℕ :=
  match lookupAllN t ps with
  | some cs => if chainOKN lo hi cs then chainWN cs else 0
  | none => 0

def termWN (t : CTN) (lo hi : ℕ) : ℕ := termWNcore t lo hi (piecesN' lo hi)

end Zeta23Ext.Bridge.ThreePoint

namespace Zeta23Ext.Bridge.ThreePoint.SixW8

def SA : ℕ := 100000000
def cN : ℕ := 329625

structure Box where
  (l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 : ℕ)
  deriving DecidableEq

def Box.widthArg (b : Box) : ℕ :=
  bif Nat.ble (b.u1 - b.l1) (b.u0 - b.l0) && Nat.ble (b.u2 - b.l2) (b.u0 - b.l0) && Nat.ble (b.u3 - b.l3) (b.u0 - b.l0) && Nat.ble (b.u4 - b.l4) (b.u0 - b.l0) then 0
  else bif Nat.ble (b.u2 - b.l2) (b.u1 - b.l1) && Nat.ble (b.u3 - b.l3) (b.u1 - b.l1) && Nat.ble (b.u4 - b.l4) (b.u1 - b.l1) then 1
  else bif Nat.ble (b.u3 - b.l3) (b.u2 - b.l2) && Nat.ble (b.u4 - b.l4) (b.u2 - b.l2) then 2
  else bif Nat.ble (b.u4 - b.l4) (b.u3 - b.l3) then 3
  else 4
def Box.mid (b : Box) : ℕ → ℕ
  | 0 => (b.l0 + b.u0) / 2
  | 1 => (b.l1 + b.u1) / 2
  | 2 => (b.l2 + b.u2) / 2
  | 3 => (b.l3 + b.u3) / 2
  | _ => (b.l4 + b.u4) / 2
def Box.setHi (b : Box) (ax : ℕ) (q : ℕ) : Box :=
  match ax with
  | 0 => { b with u0 := q }
  | 1 => { b with u1 := q }
  | 2 => { b with u2 := q }
  | 3 => { b with u3 := q }
  | _ => { b with u4 := q }
def Box.setLo (b : Box) (ax : ℕ) (q : ℕ) : Box :=
  match ax with
  | 0 => { b with l0 := q }
  | 1 => { b with l1 := q }
  | 2 => { b with l2 := q }
  | 3 => { b with l3 := q }
  | _ => { b with l4 := q }

def leafCheck (tb : CTN) (b : Box) : Bool :=
  Nat.ble (cN * SC * SW) ((24896 * b.l0 + 42034 * b.l1 + 46137 * b.l2 + 42034 * b.l3 + 24896 * b.l4) * SW + (25326800 * termWN tb (b.l0) (b.u0) + 62369200 * termWN tb (b.l0 + b.l1) (b.u0 + b.u1) + 40126500 * termWN tb (b.l0 + b.l1 + b.l2) (b.u0 + b.u1 + b.u2) + 99999900 * termWN tb (b.l0 + b.l1 + b.l2 + b.l3) (b.u0 + b.u1 + b.u2 + b.u3) + 200000000 * termWN tb (b.l0 + b.l1 + b.l2 + b.l3 + b.l4) (b.u0 + b.u1 + b.u2 + b.u3 + b.u4) + 48244400 * termWN tb (b.l1) (b.u1) + 37630700 * termWN tb (b.l1 + b.l2) (b.u1 + b.u2) + 119746800 * termWN tb (b.l1 + b.l2 + b.l3) (b.u1 + b.u2 + b.u3) + 99999900 * termWN tb (b.l1 + b.l2 + b.l3 + b.l4) (b.u1 + b.u2 + b.u3 + b.u4) + 52857300 * termWN tb (b.l2) (b.u2) + 37630700 * termWN tb (b.l2 + b.l3) (b.u2 + b.u3) + 40126500 * termWN tb (b.l2 + b.l3 + b.l4) (b.u2 + b.u3 + b.u4) + 48244400 * termWN tb (b.l3) (b.u3) + 62369200 * termWN tb (b.l3 + b.l4) (b.u3 + b.u4) + 25326800 * termWN tb (b.l4) (b.u4)) * SC)

/-- the bisection axis stored in the three bits after a split marker -/
def axOf (bits pos : ℕ) : ℕ := (bits >>> (pos + 1)) &&& 7

def walk (tb : CTN) (bits : ℕ) : ℕ → ℕ → Box → Option ℕ
  | 0, _, _ => none
  | fuel + 1, pos, b =>
      bif bits.testBit pos then
        let ax := axOf bits pos
        let q := b.mid ax
        match walk tb bits fuel (pos + 4) (b.setHi ax q) with
        | none => none
        | some pos' => walk tb bits fuel pos' (b.setLo ax q)
      else bif Nat.blt b.u4 b.l0 || leafCheck tb b then some (pos + 1) else none

/-- per-gap one-dimensional cover: segments `(a, b, clear)` in scaled coordinates; a clear
segment's cell must satisfy `aAdj · W ≥ c`, i.e. `aAdjN * WN ≥ cN * SW`. -/
def coverCheck (tb : CTN) (aAdjN : ℕ) : ℕ → ℕ → List (ℕ × ℕ × Bool) → Bool
  | pos, S, [] => decide (S ≤ pos)
  | pos, S, (a, b, cl) :: rest =>
      decide (a = pos) && decide (a ≤ b)
        && (!cl || (match tb.find (a * KB + b) with
            | some c => Nat.ble c.LN a && Nat.ble b c.UN && Nat.ble (cN * SW) (aAdjN * c.WN) | none => false))
        && coverCheck tb aAdjN b S rest

def badOf (cover : List (ℕ × ℕ × Bool)) : List (ℕ × ℕ) :=
  cover.filterMap fun s => if s.2.2 then none else some (s.1, s.2.1)

def boxOf (bd0 bd1 bd2 bd3 bd4 : List (ℕ × ℕ)) (i0 i1 i2 i3 i4 : ℕ) : Box :=
  ⟨(bd0.getD i0 (0, 0)).1, (bd0.getD i0 (0, 0)).2, (bd1.getD i1 (0, 0)).1, (bd1.getD i1 (0, 0)).2, (bd2.getD i2 (0, 0)).1, (bd2.getD i2 (0, 0)).2, (bd3.getD i3 (0, 0)).1, (bd3.getD i3 (0, 0)).2, (bd4.getD i4 (0, 0)).1, (bd4.getD i4 (0, 0)).2⟩

end Zeta23Ext.Bridge.ThreePoint.SixW8

end SixW8Defs

noncomputable section

open Real

namespace Zeta23Ext.Bridge.ThreePoint

/-! ### Soundness of the natural-number cell table (through the integer pipeline `cellN_soundZ`) -/

theorem SC_pos : (0:ℚ) < SC := by norm_num [SC]
theorem SW_pos : (0:ℚ) < SW := by norm_num [SW]

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

theorem CTN.find_sound : ∀ (t : CTN) (q : ℕ) (c : CellN), t.find q = some c → c ∈ t.toList := by
  intro t
  induction t with
  | nil => intro q c h; simp [CTN.find] at h
  | node l c0 r ihl ihr =>
    intro q c h
    simp only [CTN.find, Bool.cond_eq_ite, Nat.blt_eq] at h
    split_ifs at h with h1 h2
    · simp [CTN.toList, ihl q c h]
    · simp [CTN.toList, ihr q c h]
    · simp only [Option.some.injEq] at h
      subst h
      simp [CTN.toList]

theorem CTN.allOk_sound : ∀ (t : CTN), t.allOk = true → ∀ c ∈ t.toList, c.okZ = true := by
  intro t
  induction t with
  | nil => intro _ c hc; simp [CTN.toList] at hc
  | node l c0 r ihl ihr =>
    intro h c hc
    simp only [CTN.allOk, Bool.and_eq_true] at h
    simp only [CTN.toList, List.mem_append, List.mem_cons] at hc
    rcases hc with hc | hc | hc
    · exact ihl h.1.1 c hc
    · subst hc; exact h.1.2
    · exact ihr h.2 c hc

theorem lookupAllN_sound (t : CTN) : ∀ (ps : List (ℕ × ℕ)) (cs : List CellN),
    lookupAllN t ps = some cs → ∀ c ∈ cs, c ∈ t.toList := by
  intro ps
  induction ps with
  | nil => intro cs h; simp [lookupAllN] at h; subst h; simp
  | cons ab rest ih =>
    intro cs h
    obtain ⟨a, b⟩ := ab
    cases hf : t.find (a * KB + b) with
    | none => simp [lookupAllN, hf] at h
    | some c =>
      cases hr : lookupAllN t rest with
      | none => simp [lookupAllN, hf, hr] at h
      | some cs' =>
        simp only [lookupAllN, hf, hr, Option.some.injEq] at h
        subst h
        intro d hd
        simp only [List.mem_cons] at hd
        rcases hd with hd | hd
        · subst hd; exact CTN.find_sound t _ d hf
        · exact ih cs' hr d hd

/-- a natural-number cell's bound holds on its interval, read in real coordinates -/
theorem cellN_sound (c : CellN) (hok : c.okZ = true) (x : ℝ)
    (h1 : (c.LN : ℝ) / SC ≤ x) (h2 : x ≤ (c.UN : ℝ) / SC) : (c.WN : ℝ) / SW ≤ wfun x :=
  cellN_soundZ c hok x h1 h2

theorem chainOKN_sound (t : CTN) (hok : t.allOk = true) :
    ∀ (cs : List CellN), (∀ c ∈ cs, c ∈ t.toList) → ∀ (lo hi : ℕ), chainOKN lo hi cs = true →
      ∀ e : ℝ, (lo : ℝ) / SC ≤ e → e ≤ (hi : ℝ) / SC → (chainWN cs : ℝ) / SW ≤ wfun e := by
  intro cs
  induction cs with
  | nil =>
    intro _ lo hi _ e _ _
    simp only [chainWN, Nat.cast_zero, zero_div]; exact wfun_nonneg e
  | cons c rest ih =>
    intro hmem lo hi h e he1 he2
    simp only [chainOKN, Bool.and_eq_true, Nat.ble_eq] at h
    obtain ⟨hL, hrest⟩ := h
    have hcok := CTN.allOk_sound t hok c (hmem c (List.mem_cons_self ..))
    have hL' : (c.LN : ℝ) / SC ≤ e :=
      le_trans (div_le_div_of_nonneg_right (by exact_mod_cast hL) (by norm_num [SC])) he1
    simp only [chainWN, Bool.cond_eq_ite, Nat.ble_eq]
    split_ifs with hempty hle
    · have hU : hi ≤ c.UN := by
        rw [List.isEmpty_iff.mp hempty] at hrest
        simpa [chainOKN, Nat.ble_eq] using hrest
      exact cellN_sound c hcok e hL' (he2.trans (div_le_div_of_nonneg_right (by exact_mod_cast hU) (by norm_num [SC])))
    · rcases le_total e ((c.UN : ℝ) / SC) with hU | hU
      · exact cellN_sound c hcok e hL' hU
      · exact le_trans (div_le_div_of_nonneg_right (by exact_mod_cast hle) (by norm_num [SW]))
          (ih (fun d hd => hmem d (List.mem_cons_of_mem _ hd)) _ _ hrest e hU he2)
    · rcases le_total e ((c.UN : ℝ) / SC) with hU | hU
      · exact le_trans (div_le_div_of_nonneg_right (by exact_mod_cast (not_le.mp hle).le) (by norm_num [SW]))
          (cellN_sound c hcok e hL' hU)
      · exact ih (fun d hd => hmem d (List.mem_cons_of_mem _ hd)) _ _ hrest e hU he2

theorem termWN_sound_gen (t : CTN) (hok : t.allOk = true) (lo hi : ℕ) (ps : List (ℕ × ℕ)) (e : ℝ)
    (he1 : (lo : ℝ) / SC ≤ e) (he2 : e ≤ (hi : ℝ) / SC) :
    (termWNcore t lo hi ps : ℝ) / SW ≤ wfun e := by
  unfold termWNcore
  split
  · rename_i cs hcs
    split_ifs with hch
    · exact chainOKN_sound t hok cs (lookupAllN_sound t _ cs hcs) lo hi hch e he1 he2
    · simp only [Nat.cast_zero, zero_div]; exact wfun_nonneg e
  · simp only [Nat.cast_zero, zero_div]; exact wfun_nonneg e

theorem termWN_sound (t : CTN) (hok : t.allOk = true) (lo hi : ℕ) (e : ℝ)
    (he1 : (lo : ℝ) / SC ≤ e) (he2 : e ≤ (hi : ℝ) / SC) : (termWN t lo hi : ℝ) / SW ≤ wfun e :=
  termWN_sound_gen t hok lo hi (piecesN' lo hi) e he1 he2

end Zeta23Ext.Bridge.ThreePoint

namespace Zeta23Ext.Bridge.ThreePoint.SixW8

open Zeta23Ext.Bridge.ThreePoint

/-- the weighted functional on the gaps, in real form -/
def G (g0 g1 g2 g3 g4 : ℝ) : ℝ :=
  (24896 / (SA:ℝ)) * g0 + (42034 / (SA:ℝ)) * g1 + (46137 / (SA:ℝ)) * g2 + (42034 / (SA:ℝ)) * g3 + (24896 / (SA:ℝ)) * g4
    + (25326800 / (SA:ℝ)) * wfun (g0) + (62369200 / (SA:ℝ)) * wfun (g0 + g1) + (40126500 / (SA:ℝ)) * wfun (g0 + g1 + g2) + (99999900 / (SA:ℝ)) * wfun (g0 + g1 + g2 + g3) + (200000000 / (SA:ℝ)) * wfun (g0 + g1 + g2 + g3 + g4) + (48244400 / (SA:ℝ)) * wfun (g1) + (37630700 / (SA:ℝ)) * wfun (g1 + g2) + (119746800 / (SA:ℝ)) * wfun (g1 + g2 + g3) + (99999900 / (SA:ℝ)) * wfun (g1 + g2 + g3 + g4) + (52857300 / (SA:ℝ)) * wfun (g2) + (37630700 / (SA:ℝ)) * wfun (g2 + g3) + (40126500 / (SA:ℝ)) * wfun (g2 + g3 + g4) + (48244400 / (SA:ℝ)) * wfun (g3) + (62369200 / (SA:ℝ)) * wfun (g3 + g4) + (25326800 / (SA:ℝ)) * wfun (g4)

def Box.mem (b : Box) (g0 g1 g2 g3 g4 : ℝ) : Prop :=
  (b.l0 : ℝ) / SC ≤ g0 ∧ g0 ≤ (b.u0 : ℝ) / SC ∧ (b.l1 : ℝ) / SC ≤ g1 ∧ g1 ≤ (b.u1 : ℝ) / SC ∧ (b.l2 : ℝ) / SC ≤ g2 ∧ g2 ≤ (b.u2 : ℝ) / SC ∧ (b.l3 : ℝ) / SC ≤ g3 ∧ g3 ≤ (b.u3 : ℝ) / SC ∧ (b.l4 : ℝ) / SC ≤ g4 ∧ g4 ≤ (b.u4 : ℝ) / SC

set_option maxHeartbeats 4000000 in
theorem leaf_sound (tb : CTN) (hok : tb.allOk = true) (b : Box) (h : leafCheck tb b = true)
    (g0 g1 g2 g3 g4 : ℝ) (hm : b.mem g0 g1 g2 g3 g4) : (cN : ℝ) / SA ≤ G g0 g1 g2 g3 g4 := by
  obtain ⟨h01, h02, h11, h12, h21, h22, h31, h32, h41, h42⟩ := hm
  have w0 := termWN_sound tb hok (b.l0) (b.u0) (g0) (by push_cast; (try simp only [add_div]); linarith [h01]) (by push_cast; (try simp only [add_div]); linarith [h02])
  have w1 := termWN_sound tb hok (b.l0 + b.l1) (b.u0 + b.u1) (g0 + g1) (by push_cast; (try simp only [add_div]); linarith [h01, h11]) (by push_cast; (try simp only [add_div]); linarith [h02, h12])
  have w2 := termWN_sound tb hok (b.l0 + b.l1 + b.l2) (b.u0 + b.u1 + b.u2) (g0 + g1 + g2) (by push_cast; (try simp only [add_div]); linarith [h01, h11, h21]) (by push_cast; (try simp only [add_div]); linarith [h02, h12, h22])
  have w3 := termWN_sound tb hok (b.l0 + b.l1 + b.l2 + b.l3) (b.u0 + b.u1 + b.u2 + b.u3) (g0 + g1 + g2 + g3) (by push_cast; (try simp only [add_div]); linarith [h01, h11, h21, h31]) (by push_cast; (try simp only [add_div]); linarith [h02, h12, h22, h32])
  have w4 := termWN_sound tb hok (b.l0 + b.l1 + b.l2 + b.l3 + b.l4) (b.u0 + b.u1 + b.u2 + b.u3 + b.u4) (g0 + g1 + g2 + g3 + g4) (by push_cast; (try simp only [add_div]); linarith [h01, h11, h21, h31, h41]) (by push_cast; (try simp only [add_div]); linarith [h02, h12, h22, h32, h42])
  have w5 := termWN_sound tb hok (b.l1) (b.u1) (g1) (by push_cast; (try simp only [add_div]); linarith [h11]) (by push_cast; (try simp only [add_div]); linarith [h12])
  have w6 := termWN_sound tb hok (b.l1 + b.l2) (b.u1 + b.u2) (g1 + g2) (by push_cast; (try simp only [add_div]); linarith [h11, h21]) (by push_cast; (try simp only [add_div]); linarith [h12, h22])
  have w7 := termWN_sound tb hok (b.l1 + b.l2 + b.l3) (b.u1 + b.u2 + b.u3) (g1 + g2 + g3) (by push_cast; (try simp only [add_div]); linarith [h11, h21, h31]) (by push_cast; (try simp only [add_div]); linarith [h12, h22, h32])
  have w8 := termWN_sound tb hok (b.l1 + b.l2 + b.l3 + b.l4) (b.u1 + b.u2 + b.u3 + b.u4) (g1 + g2 + g3 + g4) (by push_cast; (try simp only [add_div]); linarith [h11, h21, h31, h41]) (by push_cast; (try simp only [add_div]); linarith [h12, h22, h32, h42])
  have w9 := termWN_sound tb hok (b.l2) (b.u2) (g2) (by push_cast; (try simp only [add_div]); linarith [h21]) (by push_cast; (try simp only [add_div]); linarith [h22])
  have w10 := termWN_sound tb hok (b.l2 + b.l3) (b.u2 + b.u3) (g2 + g3) (by push_cast; (try simp only [add_div]); linarith [h21, h31]) (by push_cast; (try simp only [add_div]); linarith [h22, h32])
  have w11 := termWN_sound tb hok (b.l2 + b.l3 + b.l4) (b.u2 + b.u3 + b.u4) (g2 + g3 + g4) (by push_cast; (try simp only [add_div]); linarith [h21, h31, h41]) (by push_cast; (try simp only [add_div]); linarith [h22, h32, h42])
  have w12 := termWN_sound tb hok (b.l3) (b.u3) (g3) (by push_cast; (try simp only [add_div]); linarith [h31]) (by push_cast; (try simp only [add_div]); linarith [h32])
  have w13 := termWN_sound tb hok (b.l3 + b.l4) (b.u3 + b.u4) (g3 + g4) (by push_cast; (try simp only [add_div]); linarith [h31, h41]) (by push_cast; (try simp only [add_div]); linarith [h32, h42])
  have w14 := termWN_sound tb hok (b.l4) (b.u4) (g4) (by push_cast; (try simp only [add_div]); linarith [h41]) (by push_cast; (try simp only [add_div]); linarith [h42])
  simp only [leafCheck, Nat.ble_eq] at h
  have hq := (Nat.cast_le (α := ℝ)).mpr h
  push_cast at hq
  have hSC : (0:ℝ) < SC := by norm_num [SC]
  have hSW : (0:ℝ) < SW := by norm_num [SW]
  have hSA : (0:ℝ) < SA := by norm_num [SA]
  have hpos : (0:ℝ) < SC * SW := by positivity
  set L : ℝ := 24896 * ((b.l0 : ℝ) / SC) + 42034 * ((b.l1 : ℝ) / SC) + 46137 * ((b.l2 : ℝ) / SC) + 42034 * ((b.l3 : ℝ) / SC) + 24896 * ((b.l4 : ℝ) / SC) with hL
  set Wt : ℝ := 25326800 * ((termWN tb (b.l0) (b.u0) : ℝ) / SW) + 62369200 * ((termWN tb (b.l0 + b.l1) (b.u0 + b.u1) : ℝ) / SW) + 40126500 * ((termWN tb (b.l0 + b.l1 + b.l2) (b.u0 + b.u1 + b.u2) : ℝ) / SW) + 99999900 * ((termWN tb (b.l0 + b.l1 + b.l2 + b.l3) (b.u0 + b.u1 + b.u2 + b.u3) : ℝ) / SW) + 200000000 * ((termWN tb (b.l0 + b.l1 + b.l2 + b.l3 + b.l4) (b.u0 + b.u1 + b.u2 + b.u3 + b.u4) : ℝ) / SW) + 48244400 * ((termWN tb (b.l1) (b.u1) : ℝ) / SW) + 37630700 * ((termWN tb (b.l1 + b.l2) (b.u1 + b.u2) : ℝ) / SW) + 119746800 * ((termWN tb (b.l1 + b.l2 + b.l3) (b.u1 + b.u2 + b.u3) : ℝ) / SW) + 99999900 * ((termWN tb (b.l1 + b.l2 + b.l3 + b.l4) (b.u1 + b.u2 + b.u3 + b.u4) : ℝ) / SW) + 52857300 * ((termWN tb (b.l2) (b.u2) : ℝ) / SW) + 37630700 * ((termWN tb (b.l2 + b.l3) (b.u2 + b.u3) : ℝ) / SW) + 40126500 * ((termWN tb (b.l2 + b.l3 + b.l4) (b.u2 + b.u3 + b.u4) : ℝ) / SW) + 48244400 * ((termWN tb (b.l3) (b.u3) : ℝ) / SW) + 62369200 * ((termWN tb (b.l3 + b.l4) (b.u3 + b.u4) : ℝ) / SW) + 25326800 * ((termWN tb (b.l4) (b.u4) : ℝ) / SW) with hWt
  have e : (L + Wt) * (SC * SW) = (24896 * (b.l0 : ℝ) + 42034 * (b.l1 : ℝ) + 46137 * (b.l2 : ℝ) + 42034 * (b.l3 : ℝ) + 24896 * (b.l4 : ℝ)) * SW + (25326800 * (termWN tb (b.l0) (b.u0) : ℝ) + 62369200 * (termWN tb (b.l0 + b.l1) (b.u0 + b.u1) : ℝ) + 40126500 * (termWN tb (b.l0 + b.l1 + b.l2) (b.u0 + b.u1 + b.u2) : ℝ) + 99999900 * (termWN tb (b.l0 + b.l1 + b.l2 + b.l3) (b.u0 + b.u1 + b.u2 + b.u3) : ℝ) + 200000000 * (termWN tb (b.l0 + b.l1 + b.l2 + b.l3 + b.l4) (b.u0 + b.u1 + b.u2 + b.u3 + b.u4) : ℝ) + 48244400 * (termWN tb (b.l1) (b.u1) : ℝ) + 37630700 * (termWN tb (b.l1 + b.l2) (b.u1 + b.u2) : ℝ) + 119746800 * (termWN tb (b.l1 + b.l2 + b.l3) (b.u1 + b.u2 + b.u3) : ℝ) + 99999900 * (termWN tb (b.l1 + b.l2 + b.l3 + b.l4) (b.u1 + b.u2 + b.u3 + b.u4) : ℝ) + 52857300 * (termWN tb (b.l2) (b.u2) : ℝ) + 37630700 * (termWN tb (b.l2 + b.l3) (b.u2 + b.u3) : ℝ) + 40126500 * (termWN tb (b.l2 + b.l3 + b.l4) (b.u2 + b.u3 + b.u4) : ℝ) + 48244400 * (termWN tb (b.l3) (b.u3) : ℝ) + 62369200 * (termWN tb (b.l3 + b.l4) (b.u3 + b.u4) : ℝ) + 25326800 * (termWN tb (b.l4) (b.u4) : ℝ)) * SC := by
    rw [hL, hWt]; field_simp; try ring
  have hq' : (cN : ℝ) ≤ L + Wt := by
    refine le_of_mul_le_mul_right ?_ hpos
    calc (cN : ℝ) * (SC * SW) = (cN : ℝ) * SC * SW := by ring
      _ ≤ _ := hq
      _ = (L + Wt) * (SC * SW) := e.symm
  unfold G
  rw [div_le_iff₀ hSA]
  have eG : ((24896 / (SA:ℝ)) * g0 + (42034 / (SA:ℝ)) * g1 + (46137 / (SA:ℝ)) * g2 + (42034 / (SA:ℝ)) * g3 + (24896 / (SA:ℝ)) * g4
      + (25326800 / (SA:ℝ)) * wfun (g0) + (62369200 / (SA:ℝ)) * wfun (g0 + g1) + (40126500 / (SA:ℝ)) * wfun (g0 + g1 + g2) + (99999900 / (SA:ℝ)) * wfun (g0 + g1 + g2 + g3) + (200000000 / (SA:ℝ)) * wfun (g0 + g1 + g2 + g3 + g4) + (48244400 / (SA:ℝ)) * wfun (g1) + (37630700 / (SA:ℝ)) * wfun (g1 + g2) + (119746800 / (SA:ℝ)) * wfun (g1 + g2 + g3) + (99999900 / (SA:ℝ)) * wfun (g1 + g2 + g3 + g4) + (52857300 / (SA:ℝ)) * wfun (g2) + (37630700 / (SA:ℝ)) * wfun (g2 + g3) + (40126500 / (SA:ℝ)) * wfun (g2 + g3 + g4) + (48244400 / (SA:ℝ)) * wfun (g3) + (62369200 / (SA:ℝ)) * wfun (g3 + g4) + (25326800 / (SA:ℝ)) * wfun (g4)) * SA
      = 24896 * g0 + 42034 * g1 + 46137 * g2 + 42034 * g3 + 24896 * g4 + 25326800 * wfun (g0) + 62369200 * wfun (g0 + g1) + 40126500 * wfun (g0 + g1 + g2) + 99999900 * wfun (g0 + g1 + g2 + g3) + 200000000 * wfun (g0 + g1 + g2 + g3 + g4) + 48244400 * wfun (g1) + 37630700 * wfun (g1 + g2) + 119746800 * wfun (g1 + g2 + g3) + 99999900 * wfun (g1 + g2 + g3 + g4) + 52857300 * wfun (g2) + 37630700 * wfun (g2 + g3) + 40126500 * wfun (g2 + g3 + g4) + 48244400 * wfun (g3) + 62369200 * wfun (g3 + g4) + 25326800 * wfun (g4) := by
    field_simp; try ring
  rw [eG]
  rw [hL, hWt] at hq'
  linarith [hq', mul_le_mul_of_nonneg_left h01 (by positivity : (0:ℝ) ≤ 24896), mul_le_mul_of_nonneg_left h11 (by positivity : (0:ℝ) ≤ 42034), mul_le_mul_of_nonneg_left h21 (by positivity : (0:ℝ) ≤ 46137), mul_le_mul_of_nonneg_left h31 (by positivity : (0:ℝ) ≤ 42034), mul_le_mul_of_nonneg_left h41 (by positivity : (0:ℝ) ≤ 24896), mul_le_mul_of_nonneg_left w0 (by positivity : (0:ℝ) ≤ 25326800), mul_le_mul_of_nonneg_left w1 (by positivity : (0:ℝ) ≤ 62369200), mul_le_mul_of_nonneg_left w2 (by positivity : (0:ℝ) ≤ 40126500), mul_le_mul_of_nonneg_left w3 (by positivity : (0:ℝ) ≤ 99999900), mul_le_mul_of_nonneg_left w4 (by positivity : (0:ℝ) ≤ 200000000), mul_le_mul_of_nonneg_left w5 (by positivity : (0:ℝ) ≤ 48244400), mul_le_mul_of_nonneg_left w6 (by positivity : (0:ℝ) ≤ 37630700), mul_le_mul_of_nonneg_left w7 (by positivity : (0:ℝ) ≤ 119746800), mul_le_mul_of_nonneg_left w8 (by positivity : (0:ℝ) ≤ 99999900), mul_le_mul_of_nonneg_left w9 (by positivity : (0:ℝ) ≤ 52857300), mul_le_mul_of_nonneg_left w10 (by positivity : (0:ℝ) ≤ 37630700), mul_le_mul_of_nonneg_left w11 (by positivity : (0:ℝ) ≤ 40126500), mul_le_mul_of_nonneg_left w12 (by positivity : (0:ℝ) ≤ 48244400), mul_le_mul_of_nonneg_left w13 (by positivity : (0:ℝ) ≤ 62369200), mul_le_mul_of_nonneg_left w14 (by positivity : (0:ℝ) ≤ 25326800)]

theorem Box.setHi_mem (b : Box) (ax : ℕ) (q : ℕ) (g0 g1 g2 g3 g4 : ℝ) (hm : b.mem g0 g1 g2 g3 g4)
    (hle : match ax with | 0 => g0 ≤ (q : ℝ) / SC | 1 => g1 ≤ (q : ℝ) / SC | 2 => g2 ≤ (q : ℝ) / SC | 3 => g3 ≤ (q : ℝ) / SC | _ => g4 ≤ (q : ℝ) / SC) :
    (b.setHi ax q).mem g0 g1 g2 g3 g4 := by
  obtain ⟨h01, h02, h11, h12, h21, h22, h31, h32, h41, h42⟩ := hm
  match ax with
  | 0 => exact ⟨h01, hle, h11, h12, h21, h22, h31, h32, h41, h42⟩
  | 1 => exact ⟨h01, h02, h11, hle, h21, h22, h31, h32, h41, h42⟩
  | 2 => exact ⟨h01, h02, h11, h12, h21, hle, h31, h32, h41, h42⟩
  | 3 => exact ⟨h01, h02, h11, h12, h21, h22, h31, hle, h41, h42⟩
  | n + 4 => exact ⟨h01, h02, h11, h12, h21, h22, h31, h32, h41, hle⟩

theorem Box.setLo_mem (b : Box) (ax : ℕ) (q : ℕ) (g0 g1 g2 g3 g4 : ℝ) (hm : b.mem g0 g1 g2 g3 g4)
    (hge : match ax with | 0 => (q : ℝ) / SC ≤ g0 | 1 => (q : ℝ) / SC ≤ g1 | 2 => (q : ℝ) / SC ≤ g2 | 3 => (q : ℝ) / SC ≤ g3 | _ => (q : ℝ) / SC ≤ g4) :
    (b.setLo ax q).mem g0 g1 g2 g3 g4 := by
  obtain ⟨h01, h02, h11, h12, h21, h22, h31, h32, h41, h42⟩ := hm
  match ax with
  | 0 => exact ⟨hge, h02, h11, h12, h21, h22, h31, h32, h41, h42⟩
  | 1 => exact ⟨h01, h02, hge, h12, h21, h22, h31, h32, h41, h42⟩
  | 2 => exact ⟨h01, h02, h11, h12, hge, h22, h31, h32, h41, h42⟩
  | 3 => exact ⟨h01, h02, h11, h12, h21, h22, hge, h32, h41, h42⟩
  | n + 4 => exact ⟨h01, h02, h11, h12, h21, h22, h31, h32, hge, h42⟩

theorem walk_split (tb : CTN) (bits fuel pos : ℕ) (b : Box) (pos1 pos' : ℕ)
    (hbit : bits.testBit pos = true)
    (h1 : walk tb bits fuel (pos + 4) (b.setHi (axOf bits pos) (b.mid (axOf bits pos))) = some pos1)
    (h2 : walk tb bits fuel pos1 (b.setLo (axOf bits pos) (b.mid (axOf bits pos))) = some pos') :
    walk tb bits (fuel + 1) pos b = some pos' := by
  simp only [walk, hbit, cond_true, h1]
  exact h2

theorem walk_sound (tb : CTN) (hok : tb.allOk = true) (bits : ℕ) :
    ∀ (fuel pos : ℕ) (b : Box) (pos' : ℕ), walk tb bits fuel pos b = some pos' →
      ∀ g0 g1 g2 g3 g4 : ℝ, b.mem g0 g1 g2 g3 g4 → (cN : ℝ) / SA ≤ G g0 g1 g2 g3 g4 ∨ g4 < g0 := by
  intro fuel
  induction fuel with
  | zero => intro pos b pos' h; simp [walk] at h
  | succ fuel ih =>
    intro pos b pos' h g0 g1 g2 g3 g4 hm
    simp only [walk, Bool.cond_eq_ite] at h
    split_ifs at h with hbit hleaf
    · split at h
      · exact absurd h (by simp)
      · rename_i pos1 h1
        have hlo := ih (pos + 4) (b.setHi (axOf bits pos) (b.mid (axOf bits pos))) pos1 h1 g0 g1 g2 g3 g4
        have hhi := ih pos1 (b.setLo (axOf bits pos) (b.mid (axOf bits pos))) pos' h g0 g1 g2 g3 g4
        set ax := axOf bits pos with hax
        set q := b.mid ax with hq
        match ax, hlo, hhi with
        | 0, hlo, hhi =>
          rcases le_total g0 ((q : ℝ) / SC) with hs | hs
          · exact hlo (Box.setHi_mem b 0 q g0 g1 g2 g3 g4 hm hs)
          · exact hhi (Box.setLo_mem b 0 q g0 g1 g2 g3 g4 hm hs)
        | 1, hlo, hhi =>
          rcases le_total g1 ((q : ℝ) / SC) with hs | hs
          · exact hlo (Box.setHi_mem b 1 q g0 g1 g2 g3 g4 hm hs)
          · exact hhi (Box.setLo_mem b 1 q g0 g1 g2 g3 g4 hm hs)
        | 2, hlo, hhi =>
          rcases le_total g2 ((q : ℝ) / SC) with hs | hs
          · exact hlo (Box.setHi_mem b 2 q g0 g1 g2 g3 g4 hm hs)
          · exact hhi (Box.setLo_mem b 2 q g0 g1 g2 g3 g4 hm hs)
        | 3, hlo, hhi =>
          rcases le_total g3 ((q : ℝ) / SC) with hs | hs
          · exact hlo (Box.setHi_mem b 3 q g0 g1 g2 g3 g4 hm hs)
          · exact hhi (Box.setLo_mem b 3 q g0 g1 g2 g3 g4 hm hs)
        | n + 4, hlo, hhi =>
          rcases le_total g4 ((q : ℝ) / SC) with hs | hs
          · exact hlo (Box.setHi_mem b (n + 4) q g0 g1 g2 g3 g4 hm hs)
          · exact hhi (Box.setLo_mem b (n + 4) q g0 g1 g2 g3 g4 hm hs)
    · simp only [Bool.or_eq_true, Nat.blt_eq] at hleaf
      rcases hleaf with hskip | hleaf
      · right
        obtain ⟨h01, h02, h11, h12, h21, h22, h31, h32, h41, h42⟩ := hm
        have hsk : ((b.u4 : ℕ) : ℝ) / SC < ((b.l0 : ℕ) : ℝ) / SC :=
          div_lt_div_of_pos_right (by exact_mod_cast hskip) (by norm_num [SC])
        linarith
      · left; exact leaf_sound tb hok b hleaf g0 g1 g2 g3 g4 hm


theorem cover_sound (tb : CTN) (hok : tb.allOk = true) (aAdjN : ℕ) :
    ∀ (cover : List (ℕ × ℕ × Bool)) (pos S : ℕ), coverCheck tb aAdjN pos S cover = true →
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
    obtain ⟨⟨⟨hpos, hab⟩, hcl⟩, hrest⟩ := h
    rcases le_total v ((b : ℝ) / SC) with hvb | hvb
    · rcases hcl with hcl | hcl
      · right
        exact ⟨(a, b, cl), List.mem_cons_self .., hcl, by rw [hpos]; exact hv1, hvb⟩
      · left
        split at hcl
        · rename_i c hfind
          simp only [Bool.and_eq_true, Nat.ble_eq] at hcl
          obtain ⟨⟨hL, hU⟩, hq'⟩ := hcl
          have hmem := CTN.find_sound tb _ c hfind
          have hcok := CTN.allOk_sound tb hok c hmem
          have hW := cellN_sound c hcok v
            (le_trans (div_le_div_of_nonneg_right (by exact_mod_cast (hpos ▸ hL)) (by norm_num [SC])) hv1)
            (hvb.trans (div_le_div_of_nonneg_right (by exact_mod_cast hU) (by norm_num [SC])))
          have hq := (Nat.cast_le (α := ℝ)).mpr hq'
          push_cast at hq
          have hSA : (0:ℝ) < SA := by norm_num [SA]
          have hSW : (0:ℝ) < SW := by norm_num [SW]
          rw [div_le_iff₀ hSA]
          have hm2 : (aAdjN : ℝ) * ((c.WN : ℝ) / SW) ≤ (aAdjN : ℝ) * wfun v :=
            mul_le_mul_of_nonneg_left hW (by positivity)
          have e : (aAdjN : ℝ) / SA * wfun v * SA = (aAdjN : ℝ) * wfun v := by field_simp
          rw [e]
          calc (cN : ℝ) = (cN : ℝ) * SW / SW := by field_simp
            _ ≤ (aAdjN : ℝ) * c.WN / SW := by apply div_le_div_of_nonneg_right _ hSW.le; linarith
            _ = (aAdjN : ℝ) * ((c.WN : ℝ) / SW) := by ring
            _ ≤ _ := hm2
        · exact absurd hcl (by simp)
    · rcases ih b S hrest v hvb hv2 with h | ⟨s', hs', he, h1, h2⟩
      · left; exact h
      · right; exact ⟨s', List.mem_cons_of_mem _ hs', he, h1, h2⟩

theorem badOf_mem {cover : List (ℕ × ℕ × Bool)} {s : ℕ × ℕ × Bool} (hs : s ∈ cover)
    (he : s.2.2 = false) : (s.1, s.2.1) ∈ badOf cover := by
  simp only [badOf, List.mem_filterMap]
  exact ⟨s, hs, by simp [he]⟩

set_option maxHeartbeats 4000000 in
theorem of_check (tb : CTN) (hok : tb.allOk = true) (bits fuel : ℕ)
    (cover0 cover1 cover2 cover3 cover4 : List (ℕ × ℕ × Bool)) (S0 S1 S2 S3 S4 : ℕ)
    (hS0 : cN * SC ≤ 24896 * S0) (hS1 : cN * SC ≤ 42034 * S1) (hS2 : cN * SC ≤ 46137 * S2) (hS3 : cN * SC ≤ 42034 * S3) (hS4 : cN * SC ≤ 24896 * S4)
    (hcov0 : coverCheck tb 25326800 (SC / 2) S0 cover0 = true) (hcov1 : coverCheck tb 48244400 (SC / 2) S1 cover1 = true) (hcov2 : coverCheck tb 52857300 (SC / 2) S2 cover2 = true) (hcov3 : coverCheck tb 48244400 (SC / 2) S3 cover3 = true) (hcov4 : coverCheck tb 25326800 (SC / 2) S4 cover4 = true)
    (hwin : cN * 100 ≤ 19 * 25326800)
    (hrun : ∀ i0 i1 i2 i3 i4, i0 < (badOf cover0).length → i1 < (badOf cover1).length → i2 < (badOf cover2).length → i3 < (badOf cover3).length → i4 < (badOf cover4).length →
      ∃ pos pos', walk tb bits fuel pos (boxOf (badOf cover0) (badOf cover1) (badOf cover2) (badOf cover3) (badOf cover4) i0 i1 i2 i3 i4) = some pos') :
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
  rcases cover_sound tb hok _ cover0 (SC / 2) S0 hcov0 g0 hwin0 hcut0 with hclear0 | ⟨s0, hs0, he0, hb01, hb02⟩
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
  rcases cover_sound tb hok _ cover1 (SC / 2) S1 hcov1 g1 hwin1 hcut1 with hclear1 | ⟨s1, hs1, he1, hb11, hb12⟩
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
  rcases cover_sound tb hok _ cover2 (SC / 2) S2 hcov2 g2 hwin2 hcut2 with hclear2 | ⟨s2, hs2, he2, hb21, hb22⟩
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
  rcases cover_sound tb hok _ cover3 (SC / 2) S3 hcov3 g3 hwin3 hcut3 with hclear3 | ⟨s3, hs3, he3, hb31, hb32⟩
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
  rcases cover_sound tb hok _ cover4 (SC / 2) S4 hcov4 g4 hwin4 hcut4 with hclear4 | ⟨s4, hs4, he4, hb41, hb42⟩
  · left; rw [hG]; linarith [hclear4, haW14, hLin0]
  obtain ⟨i4, hi4, hsi4⟩ := List.mem_iff_getElem.mp (badOf_mem hs4 he4)
  have hb41' : (((badOf cover4).getD i4 (0, 0)).1 : ℝ) / SC ≤ g4 := by
    rw [List.getD_eq_getElem _ _ hi4, hsi4]; exact hb41
  have hb42' : g4 ≤ (((badOf cover4).getD i4 (0, 0)).2 : ℝ) / SC := by
    rw [List.getD_eq_getElem _ _ hi4, hsi4]; exact hb42
  obtain ⟨pos, pos', hwalk⟩ := hrun i0 i1 i2 i3 i4 hi0 hi1 hi2 hi3 hi4
  exact walk_sound tb hok bits fuel pos _ pos' hwalk g0 g1 g2 g3 g4 ⟨hb01', hb02', hb11', hb12', hb21', hb22', hb31', hb32', hb41', hb42'⟩

end Zeta23Ext.Bridge.ThreePoint.SixW8

end

/-! ###### certificate data `SixW8`: 6814 cells, 18058 leaves (axis-coded walk) (half-space) ###### -/

namespace Zeta23Ext.Bridge.ThreePoint.SixW8Data

open Zeta23Ext.Bridge.ThreePoint Zeta23Ext.Bridge.ThreePoint.SixW8

set_option maxRecDepth 100000
local notation "N" => CTN.node
local notation "E" => CTN.nil

noncomputable def tab0 : CTN :=
  (N (N (N (N (N (N (N (N E ⟨17179893760,331038177865⟩ E) ⟨25769832448,242869129569⟩ (N E ⟨30064800768,217716609437⟩ E)) ⟨30064801792,122761883704⟩ (N (N E ⟨31138543616,131696313575⟩ E) ⟨32212286464,69269436296⟩ E)) ⟨32212286592,62652449971⟩ (N (N (N E ⟨32212287488,27393363819⟩ E) ⟨33286029120,34548539408⟩ (N E ⟨33286029312,28203622388⟩ E)) ⟨33420246432,51358482065⟩ (N (N E ⟨33420246720,39350240729⟩ E) ⟨33420247040,28267587364⟩ E))) ⟨33722236608,39582334079⟩ (N (N (N (N E ⟨34024226784,29477834588⟩ E) ⟨34024226816,28450417775⟩ (N E ⟨34158444544,28467564926⟩ E)) ⟨34326216704,28476945188⟩ (N (N E ⟨34359771152,27966906972⟩ E) ⟨34359771360,21788669253⟩ E)) ⟨34359771392,20912356297⟩ (N (N (N E ⟨34359771776,11891897536⟩ E) ⟨34376548576,21788669253⟩ E) ⟨34594652592,16438965712⟩ (N (N E ⟨34594652800,11891897536⟩ E) ⟨34628207136,13892464743⟩ E)))) ⟨34628207424,8384490092⟩ (N (N (N (N (N E ⟨34628208000,1626727581⟩ E) ⟨34812756608,11891897536⟩ (N E ⟨34930197168,10953811162⟩ E)) ⟨34930197312,8384490092⟩ (N (N E ⟨35030860520,9911220876⟩ E) ⟨35030860624,8121431559⟩ E)) ⟨35030860832,5101426618⟩ (N (N (N E ⟨35030861248,1207853390⟩ E) ⟨35081192256,8384490092⟩ (N E ⟨35139912528,8121431559⟩ E)) ⟨35232187344,6175824526⟩ (N (N E ⟨35232187488,4319118251⟩ E) ⟨35232187776,1626727581⟩ E))) ⟨35248964536,6519258779⟩ (N (N (N (N E ⟨35248964640,5101426618⟩ E) ⟨35358016544,5101426618⟩ (N E ⟨35383182432,4319118251⟩ E)) ⟨35467068552,3864654916⟩ (N (N E ⟨35467068656,2805660000⟩ E) ⟨35467068864,1207853390⟩ E)) ⟨35534177520,2805660000⟩ (N (N (N E ⟨35534177664,1626727581⟩ E) ⟨35576120560,2805660000⟩ E) ⟨35685172568,1921155551⟩ (N (N E ⟨35685172608,1626727581⟩ E) ⟨35685172672,1207853390⟩ E))))) ⟨35794224576,1207853390⟩ (N (N (N (N (N (N E ⟨35836167840,237521352⟩ E) ⟨35903276688,281698711⟩ (N E ⟨36339484720,861720⟩ E)) ⟨36339484928,840527⟩ (N (N E ⟨36440148480,76228626⟩ E) ⟨36557588736,330776253⟩ E)) ⟨36775692752,1239113067⟩ (N (N (N E ⟨36775692960,1209025102⟩ E) ⟨36775693376,1151561664⟩ (N E ⟨36775694208,1046595949⟩ E)) ⟨36775695872,870430129⟩ (N (N E ⟨36993796768,2700605352⟩ E) ⟨37044128544,3084636346⟩ E))) ⟨37044128832,2982576597⟩ (N (N (N (N E ⟨37044129408,2790908306⟩ E) ⟨37044130560,2451923401⟩ (N E ⟨37044132864,1916013694⟩ E)) ⟨37211900992,4577595806⟩ (N (N E ⟨37346118720,6108687269⟩ E) ⟨37648109184,9732001830⟩ E)) ⟨37648109440,9452356006⟩ (N (N (N E ⟨38252090112,18591409084⟩ E) ⟨38520526336,22408627075⟩ E) ⟨39460051968,40016092176⟩ (N (N E ⟨40265357312,71849923330⟩ E) ⟨40802230272,75832144115⟩ E)))) ⟨41875971136,130584775202⟩ (N (N (N (N (N E ⟨41943080064,132969615970⟩ E) ⟨42010189056,134466410964⟩ (N E ⟨42144407040,137401505255⟩ E)) ⟨42412843008,143033504697⟩ (N (N E ⟨42949715968,138814108272⟩ E) ⟨42949722112,80226784524⟩ E)) ⟨45097201664,198611196246⟩ (N (N (N E ⟨47244689408,205420959916⟩ E) ⟨51539660800,198637449669⟩ E) ⟨51539664896,86044756753⟩ (N (N E ⟨55834630144,180021136485⟩ E) ⟨57982114816,163928295311⟩ E))) ⟨59055857664,136793280978⟩ (N (N (N (N E ⟨60129601536,81450895201⟩ E) ⟨60129602432,59910509222⟩ (N E ⟨60129605376,13875044252⟩ E)) ⟨62277085696,76332532051⟩ (N (N E ⟨62277086208,63653684247⟩ E) ⟨62813958464,37346344857⟩ E)) ⟨62813960320,12524178889⟩ (N (N (N E ⟨63216610912,52465730530⟩ E) ⟨63216611648,38055582237⟩ E) ⟨63216613120,16802871029⟩ (N (N E ⟨63350829760,31761760685⟩ E) ⟨63350831488,10561059564⟩ E)))))) ⟨63988363584,39372963795⟩ (N (N (N (N (N (N (N E ⟨64760116256,28068512397⟩ E) ⟨64760116448,25219863798⟩ (N E ⟨64760116992,18073087607⟩ E)) ⟨64760117376,13822922534⟩ (N (N E ⟨65162769952,21197196115⟩ E) ⟨65162770816,11542172995⟩ E)) ⟨65498316800,1506819731⟩ (N (N (N E ⟨65531868928,18643111426⟩ E) ⟨65733195440,19784936895⟩ (N E ⟨65733195904,14382857067⟩ E)) ⟨66068740048,16517231195⟩ (N (N E ⟨66068740480,11958745632⟩ E) ⟨66219735168,14637317128⟩ E))) ⟨66303621232,14852891945⟩ (N (N (N (N E ⟨66303621600,11148640680⟩ E) ⟨66303622336,5460741139⟩ (N E ⟨66303623168,1566484433⟩ E)) ⟨66370732032,1570745138⟩ (N (N E ⟨66521725312,12146351030⟩ E) ⟨66572058624,1582848890⟩ E)) ⟨66689497568,11291846796⟩ (N (N (N E ⟨66706274664,12455181737⟩ E) ⟨66706274896,10274232917⟩ E) ⟨66706275360,6599075710⟩ (N (N E ⟨66706276288,1804170120⟩ E) ⟨66706276352,1590346721⟩ E)))) ⟨66949544528,10351402322⟩ (N (N (N (N (N E ⟨66974710360,10287535730⟩ E) ⟨66974710576,8457379249⟩ (N E ⟨66974711008,5380608052⟩ E)) ⟨66974711808,1603951009⟩ (N (N E ⟨67075373904,8227268149⟩ E) ⟨67075374272,5598956948⟩ E)) ⟨67192814392,8446267449⟩ (N (N (N E ⟨67192814624,6695668958⟩ E) ⟨67201202992,8512647331⟩ E) ⟨67427695624,6909605630⟩ (N (N E ⟨67427695840,5447824625⟩ E) ⟨67436084256,6739185667⟩ E))) ⟨67444473856,1623212765⟩ (N (N (N (N E ⟨67461250240,5657170386⟩ E) ⟨67578691584,1627636972⟩ (N E ⟨67654188148,6189035296⟩ E)) ⟨67654188256,5477660057⟩ (N (N E ⟨67679354004,5976774446⟩ E) ⟨67679354120,5229205555⟩ E)) ⟨67679354352,3895806887⟩ (N (N (N E ⟨67679354816,1850310580⟩ E) ⟨67767434464,5491622117⟩ E) ⟨67800988936,5243238134⟩ (N (N E ⟨67847126576,3577306556⟩ E) ⟨67847126944,1971372651⟩ E))))) ⟨67847127040,1635028490⟩ (N (N (N (N (N (N E ⟨67880680780,4836965686⟩ E) ⟨67880680888,4215794124⟩ (N E ⟨67880681104,3110902549⟩ E)) ⟨67880681472,1635815150⟩ (N (N E ⟨67922623868,4558943825⟩ E) ⟨67922623984,3915022730⟩ E)) ⟨67993927096,4224912015⟩ (N (N (N E ⟨68014899200,1638655395⟩ E) ⟨68044258800,3923692751⟩ (N E ⟨68107173520,3122730614⟩ E)) ⟨68165893732,3337264699⟩ (N (N E ⟨68165893848,2794987398⟩ E) ⟨68165894080,1863235879⟩ E))) ⟨68233002912,1981240105⟩ (N (N (N (N E ⟨68287528664,2799418300⟩ E) ⟨68316889088,1643246852⟩ (N E ⟨68333666152,2196937193⟩ E)) ⟨68333666304,1643428677⟩ (N (N E ⟨68409163712,1867112451⟩ E) ⟨68560158720,1645126676⟩ E)) ⟨68618878976,1645336710⟩ (N (N (N E ⟨68652433408,1645414146⟩ E) ⟨68719542336,1436255057⟩ E) ⟨68719542440,1127174177⟩ (N (N E ⟨68719542544,856134880⟩ E) ⟨68719542592,743797997⟩ E)))) ⟨68719542672,574380421⟩ (N (N (N (N (N E ⟨68719542720,483371336⟩ E) ⟨68719542752,427115186⟩ (N E ⟨68719542912,198510502⟩ E)) ⟨68719543136,24319712⟩ (N (N E ⟨68719543168,13164037⟩ E) ⟨68753097568,24319712⟩ E)) ⟨68786651416,836853921⟩ (N (N (N E ⟨68786651632,400308901⟩ E) ⟨68786652064,5411364⟩ E) ⟨68895703440,574380421⟩ (N (N E ⟨69004755584,198510502⟩ E) ⟨69013144048,400308901⟩ E))) ⟨69138973536,24319712⟩ (N (N (N (N E ⟨69239636680,124082051⟩ E) ⟨69239636896,5411364⟩ (N E ⟨69466129312,5411364⟩ E)) ⟨69776508256,833252⟩ (N (N E ⟨69793285824,2367983⟩ E) ⟨69826840368,7848649⟩ E)) ⟨69826840576,7751317⟩ (N (N (N E ⟨69843617440,11908301⟩ E) ⟨69843618688,11053934⟩ E) ⟨69877171776,22464504⟩ (N (N E ⟨69877172064,22078531⟩ E) ⟨69927504096,42603795⟩ E)))))))

noncomputable def tab1 : CTN :=
  (N (N (N (N (N (N (N (N E ⟨69961057936,62768445⟩ E) ⟨69961058144,61988162⟩ (N E ⟨69994613472,79279373⟩ E)) ⟨69994613888,77355470⟩ (N (N E ⟨70044944384,121038901⟩ E) ⟨70061721248,138285081⟩ E)) ⟨70061721456,136566458⟩ (N (N (N E ⟨70061721664,134874514⟩ E) ⟨70061722080,131568687⟩ (N E ⟨70061722496,128363755⟩ E)) ⟨70061722912,125256038⟩ (N (N E ⟨70061723328,122242010⟩ E) ⟨70061724160,116481657⟩ E))) ⟨70061724992,111057344⟩ (N (N (N (N E ⟨70061725824,105945771⟩ E) ⟨70061727488,96576815⟩ (N E ⟨70061727744,95228999⟩ E)) ⟨70095275792,168947619⟩ (N (N E ⟨70095276000,166851467⟩ E) ⟨70095276080,166053938⟩ E)) ⟨70095276288,164002603⟩ (N (N (N E ⟨70095276864,158485379⟩ E) ⟨70095278016,148131178⟩ E) ⟨70112052992,186158274⟩ (N (N E ⟨70162384960,237656889⟩ E) ⟨70179161952,261110623⟩ E)))) ⟨70195940096,266987563⟩ (N (N (N (N (N E ⟨70195940672,258073225⟩ E) ⟨70195940928,254231101⟩ (N E ⟨70195941504,245844939⟩ E)) ⟨70195942592,230928524⟩ (N (N E ⟨70195943168,223490173⟩ E) ⟨70229494272,313929596⟩ E)) ⟨70263048112,372917883⟩ (N (N (N E ⟨70263048320,368302193⟩ E) ⟨70263048400,366546001⟩ (N E ⟨70263048608,362028761⟩ E)) ⟨70263049024,353201598⟩ (N (N E ⟨70263049856,336341561⟩ E) ⟨70279825264,399534449⟩ E))) ⟨70279825472,394584551⟩ (N (N (N (N E ⟨70313379808,449359669⟩ E) ⟨70313380096,441687188⟩ (N E ⟨70330158528,436190422⟩ E)) ⟨70330159360,415560422⟩ (N (N E ⟨70330159680,407952178⟩ E) ⟨70330160512,388971858⟩ E)) ⟨70330161984,358022393⟩ (N (N (N E ⟨70330162176,354216357⟩ E) ⟨70330162816,341890120⟩ E) ⟨70330163200,334751802⟩ (N (N E ⟨70397265968,592236496⟩ E) ⟨70397266176,584920347⟩ E))))) ⟨70430821296,621992890⟩ (N (N (N (N (N (N E ⟨70430821504,614411191⟩ E) ⟨70481152128,754300627⟩ (N E ⟨70481152416,741452336⟩ E)) ⟨70497929280,792783899⟩ (N (N E ⟨70497929488,782992656⟩ E) ⟨70497929696,773352456⟩ E)) ⟨70497929904,763860504⟩ (N (N (N E ⟨70497930112,754514068⟩ E) ⟨70497930944,718530834⟩ (N E ⟨70531484032,850061616⟩ E)) ⟨70531484320,835637430⟩ (N (N E ⟨70531484448,829325160⟩ E) ⟨70531484736,815339532⟩ E))) ⟨70531484896,807697359⟩ (N (N (N (N E ⟨70531485312,788243580⟩ E) ⟨70531486464,737352761⟩ (N E ⟨70565038288,935370151⟩ E)) ⟨70565038496,923842834⟩ (N (N E ⟨70598593120,991130713⟩ E) ⟨70598593184,987374804⟩ E)) ⟨70598593984,941896883⟩ (N (N (N E ⟨70598594112,934865887⟩ E) ⟨70598595712,852286103⟩ E) ⟨70598595968,839934492⟩ (N (N E ⟨70598598656,722853285⟩ E) ⟨70615369984,1053057534⟩ E)))) ⟨70648925312,1078602912⟩ (N (N (N (N (N E ⟨70699256144,1264149027⟩ E) ⟨70699256352,1248599733⟩ (N E ⟨70699256432,1242683087⟩ E)) ⟨70699256640,1227463388⟩ (N (N E ⟨70716033192,1323040638⟩ E) ⟨70716033296,1314851598⟩ E)) ⟨70716033504,1298663154⟩ (N (N (N E ⟨70716033920,1267028524⟩ E) ⟨70732814080,1106621505⟩ E) ⟨70732816384,973352611⟩ (N (N E ⟨70783142304,1493757508⟩ E) ⟨70799920448,1460971638⟩ E))) ⟨70799921280,1391746408⟩ (N (N (N (N E ⟨70799922944,1265194420⟩ E) ⟨70825085200,1633249457⟩ (N E ⟨70833474064,1634100829⟩ E)) ⟨70833474208,1620192477⟩ (N (N E ⟨70833474624,1580837488⟩ E) ⟨70867028752,1712184899⟩ E)) ⟨70867028960,1691264844⟩ (N (N (N E ⟨70867029328,1655030864⟩ E) ⟨70867029536,1634980687⟩ E) ⟨70867029952,1595784993⟩ (N (N E ⟨70867030784,1520862133⟩ E) ⟨70917360160,1899161922⟩ E)))))) ⟨70917360448,1867012835⟩ (N (N (N (N (N (N (N E ⟨70934137208,1974587193⟩ E) ⟨70934137312,1962403517⟩ (N E ⟨70934137416,1950313884⟩ E)) ⟨70934137520,1938317424⟩ (N (N E ⟨70934137728,1914600582⟩ E) ⟨70934137936,1891246201⟩ E)) ⟨70934138144,1868247640⟩ (N (N (N E ⟨70934138368,1843870435⟩ E) ⟨70934138560,1823292115⟩ (N E ⟨70934139392,1737373987⟩ E)) ⟨70934140640,1617784893⟩ (N (N E ⟨70934141056,1580226720⟩ E) ⟨70934142976,1420381457⟩ E))) ⟨70967692064,2037837133⟩ (N (N (N (N E ⟨70967692352,2003471324⟩ E) ⟨70967692928,1936890517⟩ (N E ⟨70984469152,2111171163⟩ E)) ⟨71001246320,2176000580⟩ (N (N E ⟨71001246528,2149350120⟩ E) ⟨71043189216,2346610841⟩ E)) ⟨71043189424,2317809076⟩ (N (N (N E ⟨71068356736,2208936133⟩ E) ⟨71085132768,2428920738⟩ E) ⟨71085133344,2348087889⟩ (N (N E ⟨71135464384,2623426711⟩ E) ⟨71135464672,2579290167⟩ E)))) ⟨71135464800,2559972681⟩ (N (N (N (N (N E ⟨71135465088,2517166723⟩ E) ⟨71152241328,2731960330⟩ (N E ⟨71152241536,2698532640⟩ E)) ⟨71152241952,2633200514⟩ (N (N E ⟨71202574176,2735039188⟩ E) ⟨71202574592,2669775839⟩ E)) ⟨71202575328,2559017152⟩ (N (N (N E ⟨71202575744,2498957102⟩ E) ⟨71202578048,2196479585⟩ E) ⟨71219350336,2978598740⟩ (N (N E ⟨71269682240,3141718842⟩ E) ⟨71303236496,3318572186⟩ E))) ⟨71303236704,3278101702⟩ (N (N (N (N E ⟨71303236784,3262700895⟩ E) ⟨71303236992,3223080944⟩ (N E ⟨71303237360,3154449322⟩ E)) ⟨71303237568,3116466843⟩ (N (N E ⟨71370345344,3619904491⟩ E) ⟨71370345552,3575748739⟩ E)) ⟨71370345760,3532265730⟩ (N (N (N E ⟨71370345968,3489443174⟩ E) ⟨71370346176,3447269043⟩ E) ⟨71370348672,2987709215⟩ (N (N E ⟨71403900800,3553933353⟩ E) ⟨71403901376,3437242548⟩ E))))) ⟨71403901632,3386922060⟩ (N (N (N (N (N (N E ⟨71403902208,3277032161⟩ E) ⟨71403902528,3217910342⟩ (N E ⟨71403903360,3070329399⟩ E)) ⟨71403903872,2983713065⟩ (N (N E ⟨71403905024,2799744336⟩ E) ⟨71437454560,3850470072⟩ E)) ⟨71437454976,3757729650⟩ (N (N (N E ⟨71471009312,3933220645⟩ E) ⟨71471009728,3838928819⟩ (N E ⟨71504563648,4113772714⟩ E)) ⟨71521340512,4281785299⟩ (N (N E ⟨71521340800,4209918379⟩ E) ⟨71521341376,4070661354⟩ E))) ⟨71538119232,3998550689⟩ (N (N (N (N E ⟨71538120064,3812514736⟩ E) ⟨71538121728,3471858065⟩ (N E ⟨71571672416,4465122953⟩ E)) ⟨71571672640,4406916156⟩ (N (N E ⟨71571672704,4390460490⟩ E) ⟨71588449360,4622487389⟩ E)) ⟨71588449568,4566275481⟩ (N (N (N E ⟨71588449984,4456397484⟩ E) ⟨71605226880,4625289584⟩ E) ⟨71638782208,4553028902⟩ (N (N E ⟨71638783360,4261715064⟩ E) ⟨71739445024,5203275136⟩ E)))) ⟨71739445440,5078999552⟩ (N (N (N (N (N E ⟨71739446016,4912999674⟩ E) ⟨71806553584,5666299604⟩ (N E ⟨71806553792,5597815537⟩ E)) ⟨71806554208,5463930158⟩ (N (N E ⟨71806554624,5334032333⟩ E) ⟨71806555456,5085637335⟩ E)) ⟨71806556288,4851563615⟩ (N (N (N E ⟨71806557120,4630829728⟩ E) ⟨71806557952,4422531958⟩ E) ⟨71806558208,4360811591⟩ (N (N E ⟨71873662592,5998074718⟩ E) ⟨71907217344,6078020781⟩ E))) ⟨71940773632,5638381643⟩ (N (N (N (N E ⟨72007881152,6474050494⟩ E) ⟨72007881984,6172294035⟩ (N E ⟨72024657600,6871892121⟩ E)) ⟨72074990240,6783403768⟩ (N (N E ⟨72074990656,6623467806⟩ E) ⟨72074991488,6317518618⟩ E)) ⟨72074991808,6204572262⟩ (N (N (N E ⟨72074992640,5922529203⟩ E) ⟨72074993664,5597080107⟩ E) ⟨72175653056,7601998437⟩ (N (N E ⟨72242761824,8080762806⟩ E) ⟨72242762240,7888653193⟩ E)))))))

noncomputable def tab2 : CTN :=
  (N (N (N (N (N (N (N (N E ⟨72276318592,7267610129⟩ E) ⟨72343425792,8424993733⟩ (N E ⟨72410535040,8681119975⟩ E)) ⟨72410535296,8555310324⟩ (N (N E ⟨72477643712,9232948848⟩ E) ⟨72477645184,8493787431⟩ E)) ⟨72477646848,7745238428⟩ (N (N (N E ⟨72511198272,9396196864⟩ E) ⟨72544753024,9455518097⟩ (N E ⟨72611862080,9814924171⟩ E)) ⟨72611862912,9364788646⟩ (N (N E ⟨72611864576,8539479175⟩ E) ⟨72678969856,10948895995⟩ E))) ⟨72678970688,10439028257⟩ (N (N (N (N E ⟨72678971520,9958557075⟩ E) ⟨72678973184,9077905685⟩ (N E ⟨72746081920,9572541971⟩ E)) ⟨72746082304,9372677031⟩ (N (N E ⟨72947406720,12071904097⟩ E) ⟨72947407872,11317133968⟩ E)) ⟨72947408896,10695245768⟩ (N (N (N E ⟨73148735488,12104668324⟩ E) ⟨73282952192,13853481102⟩ E) ⟨73551388416,15396192461⟩ (N (N E ⟨73551388672,15181324901⟩ E) ⟨73819824128,17420620864⟩ E)))) ⟨74021149056,21052465904⟩ (N (N (N (N (N E ⟨74222477312,21055464219⟩ E) ⟨74490912768,23658131590⟩ (N E ⟨75564654592,35420657086⟩ E)) ⟨77309485504,57060043124⟩ (N (N E ⟨77309485568,56861581616⟩ E) ⟨77309485632,56663983892⟩ E)) ⟨77309486080,55304609886⟩ (N (N (N E ⟨77309486336,54546146546⟩ E) ⟨77309486464,54171800066⟩ (N E ⟨77309487360,51639486278⟩ E)) ⟨77309488128,49585936005⟩ (N (N E ⟨77309489664,45776641928⟩ E) ⟨77309492224,40206618849⟩ E))) ⟨77846356992,62727040513⟩ (N (N (N (N E ⟨78383228416,68470639122⟩ E) ⟨78383228928,66621352329⟩ (N E ⟨78651669504,54003089333⟩ E)) ⟨78920099840,74031506677⟩ (N (N E ⟨79456972800,73216762336⟩ E) ⟨81604460544,81183335634⟩ E)) ⟨84825686016,107303972246⟩ (N (N (N E ⟨85899431936,79111303097⟩ E) ⟨85899432704,71346696851⟩ E) ⟨85899436032,38423148027⟩ (N (N E ⟨90194401280,68661704304⟩ E) ⟨90999709312,51387903848⟩ E))))) ⟨90999709696,47195628655⟩ (N (N (N (N (N (N E ⟨92341885184,70775840107⟩ E) ⟨92341885440,67628919902⟩ (N E ⟨92610320768,69819726310⟩ E)) ⟨92744538624,68541047995⟩ (N (N E ⟨92878756864,62546211739⟩ E) ⟨92878757888,50467184291⟩ E)) ⟨93415628800,51392597158⟩ (N (N (N E ⟨94086717440,52540068776⟩ E) ⟨94489371712,40858138626⟩ (N E ⟨94489373184,26381620498⟩ E)) ⟨94489374240,17848583852⟩ (N (N E ⟨94489374512,15918871062⟩ E) ⟨94489378816,160224349⟩ E))) ⟨95630223136,34538492770⟩ (N (N (N (N E ⟨95630223872,27429919717⟩ E) ⟨96099991552,206735025⟩ (N E ⟨96401975808,28118550046⟩ E)) ⟨96502641600,9680384756⟩ (N (N E ⟨96502643072,3393533954⟩ E) ⟨96502643264,2821495812⟩ E)) ⟨96502644736,217888301⟩ (N (N (N E ⟨96972405120,3469116038⟩ E) ⟨97173729216,16451126589⟩ E) ⟨97173730688,7598528236⟩ (N (N E ⟨97173733376,235753589⟩ E) ⟨97844822016,252482848⟩ E)))) ⟨98046146944,3631726659⟩ (N (N (N (N (N E ⟨98046147328,2484663355⟩ E) ⟨98046148608,257241968⟩ (N E ⟨98247472992,5695899039⟩ E)) ⟨98247473728,3054572517⟩ (N (N E ⟨98247475200,261869607⟩ E) ⟨98281025636,15825248379⟩ E)) ⟨98281026216,11958562382⟩ (N (N (N E ⟨98281027376,5905315798⟩ E) ⟨98281029632,262627654⟩ E) ⟨98381692928,264878549⟩ (N (N E ⟨98448800768,1880376436⟩ E) ⟨98566238678,13407375559⟩ E))) ⟨98566239356,9331508996⟩ (N (N (N (N E ⟨98566240712,3468648824⟩ E) ⟨98717233824,12166587460⟩ (N E ⟨98717234560,8010890900⟩ E)) ⟨98889200296,12177370259⟩ (N (N E ⟨98918562880,1769935915⟩ E) ⟨98918563840,276266374⟩ E)) ⟨99019225664,3145643154⟩ (N (N (N E ⟨99019225856,2584484318⟩ E) ⟨99277173884,9531555910⟩ E) ⟨99354770432,1951279355⟩ (N (N E ⟨99388325600,598685665⟩ E) ⟨99488986496,8197814313⟩ E)))))) ⟨99497374956,8977577317⟩ (N (N (N (N (N (N (N E ⟨99497375536,6141282325⟩ E) ⟨99790977504,3537186848⟩ (N E ⟨99790977824,2565339140⟩ E)) ⟨99790978240,1544767448⟩ (N (N E ⟨99790978336,1347410640⟩ E) ⟨99790978528,994774472⟩ E)) ⟨99790978624,839248655⟩ (N (N (N E ⟨99790979072,292343642⟩ E) ⟨99988109090,6290593817⟩ (N E ⟨99988109768,3638394495⟩ E)) ⟨99992305024,1172995809⟩ (N (N E ⟨99992305312,703443749⟩ E) ⟨99992305408,574336419⟩ E))) ⟨99992305664,295590471⟩ (N (N (N (N E ⟨100105549616,6248061920⟩ E) ⟨100126522656,1363756952⟩ (N E ⟨100126523008,753548141⟩ E)) ⟨100193632032,538984544⟩ (N (N E ⟨100193632064,500195058⟩ E) ⟨100193632256,298653847⟩ E)) ⟨100227185856,1568199795⟩ (N (N (N E ⟨100260739168,4989000245⟩ E) ⟨100260739904,2514038914⟩ E) ⟨100260740960,464243722⟩ (N (N E ⟨100260741120,299633480⟩ E) ⟨100361404416,301063520⟩ E)))) ⟨100562729760,2626055830⟩ (N (N (N (N (N E ⟨100562730176,1584829446⟩ E) ⟨100562731008,303779968⟩ (N E ⟨100663393568,1387556232⟩ E)) ⟨100663394304,305065455⟩ (N (N E ⟨100699044296,3711157959⟩ E) ⟨100713724276,4004866175⟩ E)) ⟨100713724856,2223049757⟩ (N (N (N E ⟨100713725952,305689821⟩ E) ⟨100730502144,2040892769⟩ E) ⟨100730502432,1390322331⟩ (N (N E ⟨100764056688,1774028868⟩ E) ⟨100764057152,869728447⟩ E))) ⟨100764057520,385221871⟩ (N (N (N (N E ⟨100764057600,306301864⟩ E) ⟨100847943680,307294413⟩ (N E ⟨100864720544,726190532⟩ E)) ⟨100864720896,307488777⟩ (N (N E ⟨100898275136,513750807⟩ E) ⟨100965384192,308625792⟩ E)) ⟨100998937792,1604578538⟩ (N (N (N E ⟨101032491840,2567973732⟩ E) ⟨101032491856,2523148433⟩ E) ⟨101066047488,309712523⟩ (N (N E ⟨101099600880,2101279625⟩ E) ⟨101099601296,1184774355⟩ E))))) ⟨101099601312,1154952112⟩ (N (N (N (N (N (N E ⟨101099601536,778823984⟩ E) ⟨101099601728,517048284⟩ (N E ⟨101099601920,310063528⟩ E)) ⟨101133156192,479268296⟩ (N (N E ⟨101133156352,310408892⟩ E) ⟨101250596416,882066557⟩ E)) ⟨101250596864,311573054⟩ (N (N (N E ⟨101300927696,1581791895⟩ E) ⟨101300928160,735419311⟩ (N E ⟨101300928512,312050644⟩ E)) ⟨101321898936,2257837150⟩ (N (N E ⟨101334482064,1726391871⟩ E) ⟨101334482320,1191980066⟩ E))) ⟨101334482432,990448863⟩ (N (N (N (N E ⟨101334482848,409652702⟩ E) ⟨101334482896,359313944⟩ (N E ⟨101334482944,312361894⟩ E)) ⟨101409979502,1808396002⟩ (N (N E ⟨101409980180,577138364⟩ E) ⟨101435146240,313261231⟩ E)) ⟨101519031584,1419238200⟩ (N (N (N E ⟨101535808912,1197718980⟩ E) ⟨101535809344,523287287⟩ E) ⟨101552586144,1168052884⟩ (N (N E ⟨101552586560,523502181⟩ E) ⟨101552586752,314244900⟩ E)))) ⟨101569363808,485016017⟩ (N (N (N (N (N E ⟨101636472752,395599341⟩ E) ⟨101636472832,314904055⟩ (N E ⟨101703581696,315405182⟩ E)) ⟨101720358192,1392480192⟩ (N (N E ⟨101720358400,999412257⟩ E) ⟨101737135728,816001416⟩ E)) ⟨101737136128,315646986⟩ (N (N (N E ⟨101770690096,919289729⟩ E) ⟨101770690256,674336205⟩ E) ⟨101770690464,414134872⟩ (N (N E ⟨101770690560,315882938⟩ E) ⟨101787467424,743958928⟩ E))) ⟨101804244992,316113030⟩ (N (N (N (N E ⟨101821021760,893955304⟩ E) ⟨101821022048,487779370⟩ (N E ⟨101821022208,316225876⟩ E)) ⟨101837799424,316337253⟩ (N (N E ⟨101930074112,316923535⟩ E) ⟨101938462208,1003870403⟩ E)) ⟨101938462672,364552603⟩ (N (N (N E ⟨101972017152,317175288⟩ E) ⟨101988793968,820145335⟩ E) ⟨101988794176,528427774⟩ (N (N E ⟨101988794272,415952081⟩ E) ⟨101988794368,317273404⟩ E)))))))

noncomputable def tab3 : CTN :=
  (N (N (N (N (N (N (N (N E ⟨102005571408,508875017⟩ E) ⟨102005571584,317370043⟩ (N E ⟨102039126016,317558881⟩ E)) ⟨102072680448,317741796⟩ (N (N E ⟨102106234880,317918781⟩ E) ⟨102120914708,586007157⟩ E)) ⟨102123011936,490553211⟩ (N (N (N E ⟨102123012096,318005047⟩ E) ⟨102156566224,679298163⟩ (N E ⟨102156566432,417155373⟩ E)) ⟨102173343552,530124571⟩ (N (N E ⟨102173343744,318254933⟩ E) ⟨102206897984,530408147⟩ E))) ⟨102206898176,318414087⟩ (N (N (N (N E ⟨102223675216,510751953⟩ E) ⟨102223675248,472326304⟩ (N E ⟨102223675392,318491431⟩ E)) ⟨102274007040,318714522⟩ (N (N E ⟨102307561472,318855792⟩ E) ⟨102324338688,318924188⟩ E)) ⟨102374670240,418464951⟩ (N (N (N E ⟨102391447336,562339169⟩ E) ⟨102391447552,319182826⟩ E) ⟨102425001880,427637382⟩ (N (N E ⟨102425001984,319303171⟩ E) ⟨102441779032,502522449⟩ E)))) ⟨102441779200,319361098⟩ (N (N (N (N (N E ⟨102458556416,319417527⟩ E) ⟨102475333632,319472457⟩ (N E ⟨102492110848,319525889⟩ E)) ⟨102542442496,319677185⟩ (N (N E ⟨102609551360,319857900⟩ E) ⟨102634717184,319919471⟩ E)) ⟨102659883008,319977661⟩ (N (N (N E ⟨102668271616,319996305⟩ E) ⟨102676660224,320014574⟩ (N E ⟨102685048832,320032467⟩ E)) ⟨102710214656,320083889⟩ (N (N E ⟨102726991872,320116289⟩ E) ⟨102760546304,320176575⟩ E))) ⟨102794100736,320230839⟩ (N (N (N (N E ⟨102852820992,320311303⟩ E) ⟨102877986816,320340138⟩ (N E ⟨102894764032,320357478⟩ E)) ⟨102903152640,320365582⟩ (N (N E ⟨102911541248,320373310⟩ E) ⟨102928318464,320387635⟩ E)) ⟨102970261504,320416851⟩ (N (N (N E ⟨102978650112,320421564⟩ E) ⟨103079313536,208253265⟩ E) ⟨103079313664,120294753⟩ (N (N E ⟨103079313792,56434938⟩ E) ⟨103079313920,16522152⟩ E))))) ⟨103079314048,391458⟩ (N (N (N (N (N (N E ⟨103213531648,16522152⟩ E) ⟨103213531776,391458⟩ (N E ⟨103347749504,391458⟩ E)) ⟨103884620928,7743374⟩ (N (N E ⟨103884621056,7703420⟩ E) ⟨103884621184,7663724⟩ E)) ⟨103884621312,7624283⟩ (N (N (N E ⟨103884621568,7546161⟩ E) ⟨103884621696,7507476⟩ (N E ⟨103884621824,7469038⟩ E)) ⟨103884621952,7430847⟩ (N (N E ⟨103884622080,7392899⟩ E) ⟨103884622336,7317728⟩ E))) ⟨103884622720,7206757⟩ (N (N (N (N E ⟨103884622848,7170235⟩ E) ⟨103884622976,7133944⟩ (N E ⟨103884623104,7097883⟩ E)) ⟨103884623232,7062050⟩ (N (N E ⟨103884623872,6886241⟩ E) ⟨103884624000,6851738⟩ E)) ⟨103884624128,6817452⟩ (N (N (N E ⟨103884624384,6749522⟩ E) ⟨103884624896,6616182⟩ E) ⟨103884625152,6550749⟩ (N (N E ⟨103884625664,6422292⟩ E) ⟨103884625792,6390672⟩ E)))) ⟨103884625920,6359246⟩ (N (N (N (N (N E ⟨103884627328,6026001⟩ E) ⟨103884627584,5967779⟩ (N E ⟨103884627968,5881758⟩ E)) ⟨104018838784,38153692⟩ (N (N E ⟨104018838912,37957083⟩ E) ⟨104018839040,37761741⟩ E)) ⟨104018839168,37567655⟩ (N (N (N E ⟨104018839296,37374816⟩ E) ⟨104018839424,37183214⟩ E) ⟨104018839552,36992839⟩ (N (N E ⟨104018839680,36803682⟩ E) ⟨104018839808,36615735⟩ E))) ⟨104018839936,36428986⟩ (N (N (N (N E ⟨104018840320,35875847⟩ E) ⟨104018840448,35693806⟩ (N E ⟨104018840576,35512919⟩ E)) ⟨104018840704,35333178⟩ (N (N E ⟨104018840832,35154574⟩ E) ⟨104018841216,34625496⟩ E)) ⟨104018841344,34451354⟩ (N (N (N E ⟨104018841472,34278307⟩ E) ⟨104018841600,34106345⟩ E) ⟨104018842624,32768793⟩ (N (N E ⟨104018843264,31966071⟩ E) ⟨104018844032,31035006⟩ E)))))) ⟨104018845696,29131321⟩ (N (N (N (N (N (N (N E ⟨104153056640,91417168⟩ E) ⟨104153056768,90946698⟩ (N E ⟨104153056896,90479255⟩ E)) ⟨104153057024,90014814⟩ (N (N E ⟨104153057152,89553353⟩ E) ⟨104153057280,89094848⟩ E)) ⟨104153057408,88639277⟩ (N (N (N E ⟨104153057536,88186617⟩ E) ⟨104153057664,87736846⟩ (N E ⟨104153057792,87289942⟩ E)) ⟨104153057920,86845883⟩ (N (N E ⟨104153058048,86404646⟩ E) ⟨104153058176,85966212⟩ E))) ⟨104153058304,85530558⟩ (N (N (N (N E ⟨104153058432,85097663⟩ E) ⟨104153058560,84667506⟩ (N E ⟨104153058816,83815324⟩ E)) ⟨104153059072,82973847⟩ (N (N E ⟨104153059328,82142915⟩ E) ⟨104153059584,81322370⟩ E)) ⟨104153059712,80915943⟩ (N (N (N E ⟨104153059968,80110686⟩ E) ⟨104153060096,79711817⟩ E) ⟨104153060480,78530030⟩ (N (N E ⟨104153060736,77754336⟩ E) ⟨104153061376,75856633⟩ E)))) ⟨104153061888,74380043⟩ (N (N (N (N (N E ⟨104153062144,73655234⟩ E) ⟨104153063424,70160892⟩ (N E ⟨104287274624,166462218⟩ E)) ⟨104287274752,165607748⟩ (N (N E ⟨104287274880,164758759⟩ E) ⟨104287275008,163915209⟩ E)) ⟨104287275136,163077057⟩ (N (N (N E ⟨104287275264,162244261⟩ E) ⟨104287275392,161416780⟩ E) ⟨104287275776,158965821⟩ (N (N E ⟨104287276288,155769859⟩ E) ⟨104287276416,154983463⟩ E))) ⟨104287276672,153425518⟩ (N (N (N (N E ⟨104287276928,151887121⟩ E) ⟨104287277056,151125160⟩ (N E ⟨104287277312,149615534⟩ E)) ⟨104287277824,146652467⟩ (N (N E ⟨104287278720,141641611⟩ E) ⟨104287279104,139559762⟩ E)) ⟨104287279488,137516060⟩ (N (N (N E ⟨104421492480,264281444⟩ E) ⟨104421492608,262926604⟩ E) ⟨104421492736,261580444⟩ (N (N E ⟨104421492864,260242897⟩ E) ⟨104421492992,258913898⟩ E))))) ⟨104421493120,257593381⟩ (N (N (N (N (N (N E ⟨104421493248,256281280⟩ E) ⟨104421493376,254977533⟩ (N E ⟨104421493504,253682074⟩ E)) ⟨104421493632,252394840⟩ (N (N E ⟨104421493760,251115769⟩ E) ⟨104421493888,249844799⟩ E)) ⟨104421494016,248581868⟩ (N (N (N E ⟨104421494144,247326916⟩ E) ⟨104421494272,246079881⟩ (N E ⟨104421494656,242385686⟩ E)) ⟨104421494784,241169728⟩ (N (N E ⟨104421495040,238760624⟩ E) ⟨104421495168,237567365⟩ E))) ⟨104421495424,235203148⟩ (N (N (N (N E ⟨104421495680,232868298⟩ E) ⟨104421495808,231711749⟩ (N E ⟨104421496320,227156804⟩ E)) ⟨104421496576,224921345⟩ (N (N E ⟨104421496832,222713345⟩ E) ⟨104421498880,205990782⟩ E)) ⟨104555710336,384170219⟩ (N (N (N E ⟨104555710464,382203303⟩ E) ⟨104555710592,380248972⟩ E) ⟨104555710720,378307131⟩ (N (N E ⟨104555710848,376377682⟩ E) ⟨104555710976,374460531⟩ E)))) ⟨104555711104,372555585⟩ (N (N (N (N (N E ⟨104555711232,370662749⟩ E) ⟨104555711360,368781933⟩ (N E ⟨104555711488,366913043⟩ E)) ⟨104555711616,365055989⟩ (N (N E ⟨104555711744,363210682⟩ E) ⟨104555711872,361377031⟩ E)) ⟨104555712000,359554950⟩ (N (N (N E ⟨104555712256,355945144⟩ E) ⟨104555712384,354157247⟩ E) ⟨104555712512,352380573⟩ (N (N E ⟨104555712896,347117049⟩ E) ⟨104555713024,345384429⟩ E))) ⟨104555713664,336881845⟩ (N (N (N (N E ⟨104555714176,330267653⟩ E) ⟨104555716608,300979524⟩ (N E ⟨104689928192,525882631⟩ E)) ⟨104689928320,523193621⟩ (N (N E ⟨104689928448,520521794⟩ E) ⟨104689928576,517867020⟩ E)) ⟨104689928704,515229167⟩ (N (N (N E ⟨104689928832,512608105⟩ E) ⟨104689928960,510003708⟩ E) ⟨104689929088,507415847⟩ (N (N E ⟨104689929216,504844397⟩ E) ⟨104689929344,502289233⟩ E)))))))

noncomputable def tab4 : CTN :=
  (N (N (N (N (N (N (N (N E ⟨104689929600,497227267⟩ E) ⟨104689929728,494720222⟩ (N E ⟨104689929856,492228974⟩ E)) ⟨104689930112,487293394⟩ (N (N E ⟨104689930240,484848826⟩ E) ⟨104689930368,482419584⟩ E)) ⟨104689930496,480005552⟩ (N (N (N E ⟨104689930880,472853584⟩ E) ⟨104689931008,470499263⟩ (N E ⟨104689931264,465834458⟩ E)) ⟨104689931392,463523757⟩ (N (N E ⟨104689931648,458945221⟩ E) ⟨104689931904,454423133⟩ E))) ⟨104689932032,452182996⟩ (N (N (N (N E ⟨104689932160,449956660⟩ E) ⟨104689932544,443359438⟩ (N E ⟨104689932672,441187293⟩ E)) ⟨104689933312,430524113⟩ (N (N E ⟨104689934208,416131538⟩ E) ⟨104689934336,414124897⟩ E)) ⟨104824146176,685641829⟩ (N (N (N E ⟨104824146304,682144906⟩ E) ⟨104824146432,678670273⟩ E) ⟨104824146560,675217758⟩ (N (N E ⟨104824146688,671787193⟩ E) ⟨104824146816,668378410⟩ E)))) ⟨104824146944,664991244⟩ (N (N (N (N (N E ⟨104824147072,661625530⟩ E) ⟨104824147328,654957807⟩ (N E ⟨104824147456,651655476⟩ E)) ⟨104824148992,613606564⟩ (N (N E ⟨104824152064,545493685⟩ E) ⟨104958364160,864853062⟩ E)) ⟨104958364416,856081715⟩ (N (N (N E ⟨104958364544,851737785⟩ E) ⟨104958364672,847421402⟩ (N E ⟨104958364800,843132356⟩ E)) ⟨104958365056,834635445⟩ (N (N E ⟨104958365184,830427171⟩ E) ⟨104958365312,826245413⟩ E))) ⟨104958365440,822089973⟩ (N (N (N (N E ⟨104958365568,817960650⟩ E) ⟨104958365696,813857248⟩ (N E ⟨104958365952,805727429⟩ E)) ⟨104958366208,797698973⟩ (N (N E ⟨104958366336,793722283⟩ E) ⟨104958366464,789770367⟩ E)) ⟨104958366720,781940122⟩ (N (N (N E ⟨104958367104,770375990⟩ E) ⟨104958368256,736944104⟩ E) ⟨105092582144,1062941942⟩ (N (N E ⟨105092582272,1057548362⟩ E) ⟨105092582400,1052188985⟩ E))))) ⟨105092582528,1046863551⟩ (N (N (N (N (N (N E ⟨105092582656,1041571801⟩ E) ⟨105092582784,1036313480⟩ (N E ⟨105092582912,1031088334⟩ E)) ⟨105092583040,1025896114⟩ (N (N E ⟨105092583168,1020736569⟩ E) ⟨105092583296,1015609453⟩ E)) ⟨105092583424,1010514521⟩ (N (N (N E ⟨105092583552,1005451532⟩ E) ⟨105092583680,1000420244⟩ (N E ⟨105092583808,995420420⟩ E)) ⟨105092583936,990451824⟩ (N (N E ⟨105092584192,980607380⟩ E) ⟨105092584448,970885066⟩ E))) ⟨105092584576,966069138⟩ (N (N (N (N E ⟨105092584832,956526622⟩ E) ⟨105092585088,947101756⟩ (N E ⟨105092585472,933181255⟩ E)) ⟨105092585728,924042973⟩ (N (N E ⟨105092586240,906099859⟩ E) ⟨105092587136,875735766⟩ E)) ⟨105092587520,863112789⟩ (N (N (N E ⟨105226800000,1285850659⟩ E) ⟨105226800128,1279334306⟩ E) ⟨105226800256,1272859223⟩ (N (N E ⟨105226800384,1266425096⟩ E) ⟨105226800512,1260031615⟩ E)))) ⟨105226800640,1253678471⟩ (N (N (N (N (N E ⟨105226800768,1247365360⟩ E) ⟨105226801024,1234858027⟩ (N E ⟨105226801280,1222507226⟩ E)) ⟨105226801408,1216389790⟩ (N (N E ⟨105226801536,1210310610⟩ E) ⟨105226801792,1198265872⟩ E)) ⟨105226801920,1192299748⟩ (N (N (N E ⟨105226802176,1180478592⟩ E) ⟨105226802432,1168803722⟩ E) ⟨105226802688,1157272969⟩ (N (N E ⟨105226802816,1151560969⟩ E) ⟨105226802944,1145884202⟩ E))) ⟨105226803328,1129062703⟩ (N (N (N (N E ⟨105226803584,1118019814⟩ E) ⟨105226804480,1080418470⟩ (N E ⟨105226805120,1054525624⟩ E)) ⟨105226805248,1049440563⟩ (N (N E ⟨105361017728,1536671226⟩ E) ⟨105361017856,1528883780⟩ E)) ⟨105361017984,1521145654⟩ (N (N (N E ⟨105361018240,1505815868⟩ E) ⟨105361018368,1498223468⟩ E) ⟨105361018624,1483181829⟩ (N (N E ⟨105361018880,1468328677⟩ E) ⟨105361019136,1453661183⟩ E)))))) ⟨105361019520,1432001978⟩ (N (N (N (N (N (N (N E ⟨105361019776,1417786566⟩ E) ⟨105361020160,1396792882⟩ (N E ⟨105361020288,1389881531⟩ E)) ⟨105361020544,1376186724⟩ (N (N E ⟨105361020672,1369402636⟩ E) ⟨105361021440,1329565060⟩ E)) ⟨105361021824,1310190052⟩ (N (N (N E ⟨105361022208,1291167028⟩ E) ⟨105361022592,1272488333⟩ (N E ⟨105361022976,1254146509⟩ E)) ⟨105495235840,1782678246⟩ (N (N E ⟨105495235968,1773678488⟩ E) ⟨105495236096,1764735511⟩ E))) ⟨105495236224,1755848885⟩ (N (N (N (N E ⟨105495236352,1747018185⟩ E) ⟨105495236480,1738242987⟩ (N E ⟨105495236608,1729522875⟩ E)) ⟨105495236736,1720857432⟩ (N (N E ⟨105495236864,1712246247⟩ E) ⟨105495236992,1703688913⟩ E)) ⟨105495237120,1695185027⟩ (N (N (N E ⟨105495237248,1686734186⟩ E) ⟨105495237376,1678335996⟩ E) ⟨105495237504,1669990061⟩ (N (N E ⟨105495237760,1653453401⟩ E) ⟨105495238016,1637121129⟩ E)))) ⟨105495238272,1620990215⟩ (N (N (N (N (N E ⟨105495238528,1605057687⟩ E) ⟨105495238656,1597164902⟩ (N E ⟨105495238912,1581524485⟩ E)) ⟨105495239680,1535739104⟩ (N (N E ⟨105495239936,1520846759⟩ E) ⟨105495240704,1477240831⟩ E)) ⟨105629453696,2063617883⟩ (N (N (N E ⟨105629453824,2053213016⟩ E) ⟨105629453952,2042873713⟩ E) ⟨105629454080,2032599477⟩ (N (N E ⟨105629454208,2022389817⟩ E) ⟨105629454336,2012244247⟩ E))) ⟨105629454464,2002162282⟩ (N (N (N (N E ⟨105629454592,1992143446⟩ E) ⟨105629454848,1972293265⟩ (N E ⟨105629455232,1942979732⟩ E)) ⟨105629455360,1933329849⟩ (N (N E ⟨105629455488,1923739861⟩ E) ⟨105629455744,1904737787⟩ E)) ⟨105629456128,1876672858⟩ (N (N (N E ⟨105629456256,1867433004⟩ E) ⟨105629456896,1822078178⟩ E) ⟨105629457280,1795526053⟩ (N (N E ⟨105629457792,1760871750⟩ E) ⟨105629458048,1743858420⟩ E))))) ⟨105629458432,1718722202⟩ (N (N (N (N (N (N E ⟨105763671552,2363640563⟩ E) ⟨105763671808,2339910440⟩ (N E ⟨105763672064,2316477679⟩ E)) ⟨105763672192,2304871412⟩ (N (N E ⟨105763672832,2247919313⟩ E) ⟨105763672960,2236740986⟩ E)) ⟨105763673088,2225632127⟩ (N (N (N E ⟨105763673728,2171111876⟩ E) ⟨105763674112,2139200874⟩ (N E ⟨105763674368,2118252510⟩ E)) ⟨105763675136,2056928768⟩ (N (N E ⟨105763676160,1978577712⟩ E) ⟨105897889280,2695988834⟩ E))) ⟨105897889408,2682412724⟩ (N (N (N (N E ⟨105897889536,2668922051⟩ E) ⟨105897889664,2655516170⟩ (N E ⟨105897889792,2642194442⟩ E)) ⟨105897889920,2628956233⟩ (N (N E ⟨105897890048,2615800915⟩ E) ⟨105897890176,2602727864⟩ E)) ⟨105897890304,2589736465⟩ (N (N (N E ⟨105897890432,2576826105⟩ E) ⟨105897890560,2563996177⟩ E) ⟨105897890688,2551246081⟩ (N (N E ⟨105897890816,2538575220⟩ E) ⟨105897890944,2525983004⟩ E)))) ⟨105897891200,2501032169⟩ (N (N (N (N (N E ⟨105897891456,2476388951⟩ E) ⟨105897891584,2464181276⟩ (N E ⟨105897891712,2452048806⟩ E)) ⟨105897891840,2439990988⟩ (N (N E ⟨105897892096,2416097102⟩ E) ⟨105897892608,2369181205⟩ E)) ⟨105897892864,2346150713⟩ (N (N (N E ⟨105897893888,2256782822⟩ E) ⟨106032107264,3019591488⟩ E) ⟨106032107392,3004424210⟩ (N (N E ⟨106032107520,2989352141⟩ E) ⟨106032107648,2974374565⟩ E))) ⟨106032107776,2959490771⟩ (N (N (N (N E ⟨106032107904,2944700053⟩ E) ⟨106032108160,2915395064⟩ (N E ⟨106032108288,2900879413⟩ E)) ⟨106032109952,2720155454⟩ (N (N E ⟨106032111616,2553301322⟩ E) ⟨106166325120,3374824912⟩ E)) ⟨106166325248,3357894682⟩ (N (N (N E ⟨106166325376,3341070594⟩ E) ⟨106166325504,3324351850⟩ E) ⟨106166325632,3307737658⟩ (N (N E ⟨106166325760,3291227234⟩ E) ⟨106166326016,3258514586⟩ E)))))))

noncomputable def tab5 : CTN :=
  (N (N (N (N (N (N (N (N E ⟨106166326400,3210204655⟩ E) ⟨106166326784,3162787592⟩ (N E ⟨106166327168,3116243648⟩ E)) ⟨106166327424,3085689896⟩ (N (N E ⟨106166327808,3040558638⟩ E) ⟨106166327936,3025698648⟩ E)) ⟨106166328320,2981660576⟩ (N (N (N E ⟨106166328704,2938421563⟩ E) ⟨106166328960,2910030890⟩ (N E ⟨106166329344,2868085299⟩ E)) ⟨106300542976,3747752238⟩ (N (N E ⟨106300543104,3728974843⟩ E) ⟨106300543232,3710315023⟩ E))) ⟨106300543360,3691771894⟩ (N (N (N (N E ⟨106300543488,3673344580⟩ E) ⟨106300543616,3655032214⟩ (N E ⟨106300543744,3636833936⟩ E)) ⟨106300543872,3618748892⟩ (N (N E ⟨106300544000,3600776238⟩ E) ⟨106300544128,3582915136⟩ E)) ⟨106300544384,3547524270⟩ (N (N (N E ⟨106300544640,3512569736⟩ E) ⟨106300545024,3460941988⟩ E) ⟨106300545280,3427050325⟩ (N (N E ⟨106300547072,3201075113⟩ E) ⟨106434760832,4138004154⟩ E)))) ⟨106434760960,4117297548⟩ (N (N (N (N (N E ⟨106434761216,4076271836⟩ E) ⟨106434761344,4055950796⟩ (N E ⟨106434761600,4015687576⟩ E)) ⟨106434761728,3995743510⟩ (N (N E ⟨106434761856,3975923233⟩ E) ⟨106434761984,3956225821⟩ E)) ⟨106434762112,3936650362⟩ (N (N (N E ⟨106434762240,3917195948⟩ E) ⟨106434762368,3897861683⟩ (N E ⟨106434762496,3878646676⟩ E)) ⟨106434762624,3859550045⟩ (N (N E ⟨106434762752,3840570914⟩ E) ⟨106434762880,3821708416⟩ E))) ⟨106434763520,3729115588⟩ (N (N (N (N E ⟨106434763776,3692865356⟩ E) ⟨106434764288,3621678004⟩ (N E ⟨106434764416,3604150098⟩ E)) ⟨106434764672,3569411550⟩ (N (N E ⟨106434764800,3552199377⟩ E) ⟨106568978816,4522487385⟩ E)) ⟨106568979200,4455187392⟩ (N (N (N E ⟨106568979328,4433032887⟩ E) ⟨106568979584,4389135886⟩ E) ⟨106568979840,4345781435⟩ (N (N E ⟨106568980096,4302961499⟩ E) ⟨106568980352,4260668180⟩ E))))) ⟨106568980992,4157188238⟩ (N (N (N (N (N (N E ⟨106568981504,4076660164⟩ E) ⟨106568982528,3921374948⟩ (N E ⟨106703197056,4870677540⟩ E)) ⟨106703197312,4822446873⟩ (N (N E ⟨106703197440,4798555637⟩ E) ⟨106703197568,4774812318⟩ E)) ⟨106703197824,4727765046⟩ (N (N (N E ⟨106703198080,4681296382⟩ E) ⟨106703198208,4658276357⟩ (N E ⟨106703198464,4612659663⟩ E)) ⟨106703199232,4479122445⟩ (N (N E ⟨106703200256,4308506924⟩ E) ⟨106837414656,5355130656⟩ E))) ⟨106837414912,5302036761⟩ (N (N (N (N E ⟨106837415040,5275736814⟩ E) ⟨106837415296,5223624809⟩ (N E ⟨106837415424,5197810335⟩ E)) ⟨106837415552,5172155289⟩ (N (N E ⟨106837415680,5146658489⟩ E) ⟨106837415808,5121318764⟩ E)) ⟨106837415936,5096134953⟩ (N (N (N E ⟨106837416448,4996935979⟩ E) ⟨106837416704,4948242519⟩ E) ⟨106837417600,4782423161⟩ (N (N E ⟨106837417984,4713488648⟩ E) ⟨106971633024,5692087695⟩ E)))) ⟨106971633536,5580606683⟩ (N (N (N (N (N E ⟨106971634176,5445069055⟩ E) ⟨106971635072,5262160751⟩ (N E ⟨106971635712,5136201722⟩ E)) ⟨107105851648,5970182008⟩ (N (N E ⟨107105852416,5797344305⟩ E) ⟨107105852672,5741126388⟩ E)) ⟨107105852800,5713273219⟩ (N (N (N E ⟨107105853312,5603537017⟩ E) ⟨107105853440,5576516022⟩ E) ⟨107240069120,6524160155⟩ (N (N E ⟨107240070144,6273245712⟩ E) ⟨107240070400,6212412891⟩ E))) ⟨107240070656,6152316377⟩ (N (N (N (N E ⟨107240071040,6063528870⟩ E) ⟨107240071168,6034289734⟩ (N E ⟨107374288256,6669003657⟩ E)) ⟨107374288896,6509369379⟩ (N (N E ⟨107508504960,7459132497⟩ E) ⟨107508505856,7208266270⟩ E)) ⟨107508505984,7173295248⟩ (N (N (N E ⟨107508506240,7103987736⟩ E) ⟨107508506624,7001589868⟩ E) ⟨107642722944,7923523178⟩ (N (N E ⟨107642723072,7884846377⟩ E) ⟨107642723328,7808198844⟩ E)))))) ⟨107642723968,7620619198⟩ (N (N (N (N (N (N (N E ⟨107642724352,7510774532⟩ E) ⟨107776942080,8036735203⟩ (N E ⟨107911159808,8579272269⟩ E)) ⟨108045377536,9138174746⟩ (N (N E ⟨108179595264,9713220361⟩ E) ⟨108313812224,10608339407⟩ E)) ⟨108582248448,11532825879⟩ (N (N (N E ⟨108850683904,12822037504⟩ E) ⟨108984901632,13488654132⟩ (N E ⟨109119119360,14169550279⟩ E)) ⟨109253337088,14864417181⟩ (N (N E ⟨109521772544,16294777226⟩ E) ⟨109924425728,18536799524⟩ E))) ⟨110058643456,19308445686⟩ (N (N (N (N E ⟨111669256320,29210021225⟩ E) ⟨111669256448,29069507059⟩ (N E ⟨111669256576,28929837604⟩ E)) ⟨111669256832,28653008511⟩ (N (N E ⟨111669256960,28515836841⟩ E) ⟨111669257216,28243949556⟩ E)) ⟨111669257344,28109222210⟩ (N (N (N E ⟨111669257472,27975297990⟩ E) ⟨111669257856,27578286886⟩ E) ⟨111669257984,27447518209⟩ (N (N E ⟨111669258112,27317524415⟩ E) ⟨111669258240,27188299995⟩ E)))) ⟨111669258368,27059839487⟩ (N (N (N (N (N E ⟨111669258496,26932137472⟩ E) ⟨111669258752,26678987475⟩ (N E ⟨111669258880,26553528882⟩ E)) ⟨111669259008,26428807555⟩ (N (N E ⟨111669259136,26304818298⟩ E) ⟨111669259520,25937191605⟩ E)) ⟨111669259648,25816079498⟩ (N (N (N E ⟨111669259776,25695674104⟩ E) ⟨111669259904,25575970478⟩ E) ⟨111669260032,25456963711⟩ (N (N E ⟨111669260160,25338648938⟩ E) ⟨111669260672,24872213820⟩ E))) ⟨111669260800,24757287385⟩ (N (N (N (N E ⟨111669261440,24192518009⟩ E) ⟨111669261568,24081505030⟩ (N E ⟨111669261824,23861384437⟩ E)) ⟨111669262336,23428643310⟩ (N (N E ⟨111669262848,23005676080⟩ E) ⟨111669263104,22797774870⟩ E)) ⟨111669263232,22694705692⟩ (N (N (N E ⟨111669264128,21989307075⟩ E) ⟨111669264384,21792819594⟩ E) ⟨111937699840,23117506447⟩ (N (N E ⟨112877223936,27861269372⟩ E) ⟨115561578496,41335503011⟩ E))))) ⟨115695796224,41967572529⟩ (N (N (N (N (N (N E ⟨118111715328,51817339464⟩ E) ⟨120259199360,56270327501⟩ (N E ⟨120259199488,55960566098⟩ E)) ⟨120259200512,52971284238⟩ (N (N E ⟨120259201024,51165131437⟩ E) ⟨120259203584,39840126277⟩ E)) ⟨120259205504,30034008531⟩ (N (N (N E ⟨120259207168,21644686635⟩ E) ⟨121601384448,22548890975⟩ (N E ⟨121869816192,42293980288⟩ E)) ⟨121869819136,26691853011⟩ (N (N E ⟨121869819904,22731392413⟩ E) ⟨124285739008,24386598882⟩ E))) ⟨124956826880,29102448749⟩ (N (N (N (N E ⟨125091045376,24938999025⟩ E) ⟨126030569472,25580482236⟩ (N E ⟨126164787200,25671723688⟩ E)) ⟨126970093568,26216360309⟩ (N (N E ⟨127372746752,26486543020⟩ E) ⟨127775399936,26755041422⟩ E)) ⟨127909617664,26844133108⟩ (N (N (N E ⟨128043835392,26933009019⟩ E) ⟨128849142528,23037612545⟩ E) ⟨128849143936,15665427419⟩ (N (N E ⟨128849144064,15052086325⟩ E) ⟨128849144960,11062741126⟩ E)))) ⟨128849145088,10538428373⟩ (N (N (N (N (N E ⟨128849145216,10025994745⟩ E) ⟨128849145472,9037318363⟩ (N E ⟨128849145728,8097739006⟩ E)) ⟨128849146368,5969173862⟩ (N (N E ⟨128849146624,5207672845⟩ E) ⟨128849146880,4498307474⟩ E)) ⟨128849147008,4163282560⟩ (N (N (N E ⟨128849148288,1537105649⟩ E) ⟨128849148416,1346617606⟩ E) ⟨128849148544,1169098096⟩ (N (N E ⟨128849149952,50445805⟩ E) ⟨129117585280,94128392⟩ E))) ⟨129520232576,15935715654⟩ (N (N (N (N E ⟨129788672128,2034921410⟩ E) ⟨129788673920,102542944⟩ (N E ⟨129922889472,2796285224⟩ E)) ⟨129922889856,2045727040⟩ (N (N E ⟨130057109504,61498544⟩ E) ⟨130459762688,65089451⟩ E)) ⟨130593976448,7578121817⟩ (N (N (N E ⟨130593977088,5495736718⟩ E) ⟨130728195456,3764077601⟩ E) ⟨130728196864,1101043296⟩ (N (N E ⟨130862414464,1282987978⟩ E) ⟨130862415872,68601001⟩ E)))))))

noncomputable def tab6 : CTN :=
  (N (N (N (N (N (N (N (N E ⟨131130848256,4831140569⟩ E) ⟨131265067008,2394281607⟩ (N E ⟨131399283456,5620512261⟩ E)) ⟨131399283584,5237290437⟩ (N (N E ⟨131399284480,2938163676⟩ E) ⟨131399286272,342094870⟩ E)) ⟨131533501824,3856114824⟩ (N (N (N E ⟨131533503744,556924746⟩ E) ⟨131667720448,1944224752⟩ (N E ⟨131801937664,2974474863⟩ E)) ⟨131801938048,2187674061⟩ (N (N E ⟨131801938304,1731972741⟩ E) ⟨131801939072,690988973⟩ E))) ⟨131801939456,350277720⟩ (N (N (N (N E ⟨131936157696,77434193⟩ E) ⟨132070374144,1162519187⟩ (N E ⟨132204590464,3929010649⟩ E)) ⟨132204591360,1978573199⟩ (N (N E ⟨132204592000,999780431⟩ E) ⟨132204592128,844802039⟩ E)) ⟨132204592768,269232762⟩ (N (N (N E ⟨132338807808,4990676240⟩ E) ⟨132338808448,3314513400⟩ E) ⟨132338808576,3021132809⟩ (N (N E ⟨132338809216,1763026526⟩ E) ⟨132607242624,7057908263⟩ E)))) ⟨132607243264,5024304284⟩ (N (N (N (N (N E ⟨132741462528,1573177989⟩ E) ⟨133009897728,2026914939⟩ (N E ⟨133009899136,281287949⟩ E)) ⟨133009899264,203040122⟩ (N (N E ⟨133144114944,3087113633⟩ E) ⟨133144116224,874825748⟩ E)) ⟨133144116352,729644308⟩ (N (N (N E ⟨133278333312,1813460213⟩ E) ⟨133278334976,86981035⟩ (N E ⟨133412549632,5120902355⟩ E)) ⟨133412551552,1042578316⟩ (N (N E ⟨133412552192,379221544⟩ E) ⟨133546769024,1409046459⟩ E))) ⟨133546769152,1221055338⟩ (N (N (N (N E ⟨133546769408,886594086⟩ E) ⟨133546769792,487432336⟩ (N E ⟨133546770432,88643818⟩ E)) ⟨133680986368,2064080127⟩ (N (N E ⟨133680986624,1616911689⟩ E) ⟨133680987008,1051198023⟩ E)) ⟨133680987264,743260291⟩ (N (N (N E ⟨133680987776,290226547⟩ E) ⟨133680988160,89440943⟩ E) ⟨133815204864,894053282⟩ (N (N E ⟨133815205248,492263255⟩ E) ⟨133815205504,291885065⟩ E))))) ⟨133815205760,144422286⟩ (N (N (N (N (N (N E ⟨133815205888,90214579⟩ E) ⟨133949422080,1628465951⟩ (N E ⟨133949422336,1235162357⟩ E)) ⟨133949422720,749642439⟩ (N (N E ⟨133949423232,293499006⟩ E) ⟨133949423488,145432769⟩ E)) ⟨133949423616,90964259⟩ (N (N (N E ⟨134083639424,2331678402⟩ E) ⟨134083639552,2084941570⟩ (N E ⟨134083640192,1063483878⟩ E)) ⟨134083640832,389261070⟩ (N (N E ⟨134083641344,91689533⟩ E) ⟨134217857664,1434799465⟩ E))) ⟨134217858432,499069489⟩ (N (N (N (N E ⟨134217858944,147359326⟩ E) ⟨134352075904,758664282⟩ (N E ⟨134352076160,501218036⟩ E)) ⟨134486293248,1252643901⟩ (N (N E ⟨134486293376,1074974784⟩ E) ⟨134486293760,625557927⟩ E)) ⟨134486294016,394656437⟩ (N (N (N E ⟨134486294272,217706316⟩ E) ⟨134486294400,149156825⟩ E) ⟨134486294528,93714619⟩ (N (N E ⟨134620510976,1256770849⟩ E) ⟨134620511488,627946919⟩ E)))) ⟨134620511872,300879273⟩ (N (N (N (N (N E ⟨134620512000,218808388⟩ E) ⟨134620512256,94338048⟩ (N E ⟨134754729088,767005716⟩ E)) ⟨134754729856,150821679⟩ (N (N E ⟨134754729984,94935037⟩ E) ⟨134888946432,1264726435⟩ E)) ⟨134888946560,1085647256⟩ (N (N (N E ⟨134888946944,632514968⟩ E) ⟨134888947072,509193770⟩ E) ⟨134888947200,399560138⟩ (N (N E ⟨134888947712,95505228⟩ E) ⟨135023164544,772179014⟩ E))) ⟨135023164672,634692757⟩ (N (N (N (N E ⟨135023165184,221868200⟩ E) ⟨135157382528,512802130⟩ (N E ⟨135157383040,153063066⟩ E)) ⟨135157383168,96563856⟩ (N (N E ⟨135291600000,777035984⟩ E) ⟨135291600512,307061088⟩ E)) ⟨135291600768,153740452⟩ (N (N (N E ⟨135291600896,97051656⟩ E) ⟨135425817856,640794050⟩ E) ⟨135425818112,405308227⟩ (N (N E ⟨135425818368,224549458⟩ E) ⟨135425818624,97511382⟩ E)))))) ⟨135560035456,781571749⟩ (N (N (N (N (N (N (N E ⟨135560035584,642681946⟩ E) ⟨135560035968,309184911⟩ (N E ⟨135560036352,97942758⟩ E)) ⟨135694253696,310170411⟩ (N (N E ⟨135694254080,98345523⟩ E) ⟨135828471808,98719435⟩ E)) ⟨135962688896,522058204⟩ (N (N (N E ⟨135962689152,311986785⟩ E) ⟨135962689408,156589595⟩ (N E ⟨135962689536,99064269⟩ E)) ⟨136096907008,228149927⟩ (N (N E ⟨136096907136,157049895⟩ E) ⟨136096907264,99379817⟩ E))) ⟨136231124352,524608512⟩ (N (N (N (N E ⟨136231124608,313594832⟩ E) ⟨136231124864,157473116⟩ (N E ⟨136231124992,99665889⟩ E)) ⟨136365342464,229279073⟩ (N (N E ⟨136365342720,99922313⟩ E) ⟨136499560064,314992258⟩ E)) ⟨136499560320,158207513⟩ (N (N (N E ⟨136499560448,100148933⟩ E) ⟨136633778048,158518332⟩ E) ⟨136633778176,100345615⟩ (N (N E ⟨136767995904,100512239⟩ E) ⟨136902213632,100648704⟩ E)))) ⟨137170649088,100830851⟩ (N (N (N (N (N E ⟨137439084672,55697681⟩ E) ⟨137439084800,23869645⟩ (N E ⟨137439084928,5347966⟩ E)) ⟨137975956864,63678⟩ (N (N E ⟨137975956992,63431⟩ E) ⟨137975957120,63186⟩ E)) ⟨137975957248,62942⟩ (N (N (N E ⟨137975957376,62700⟩ E) ⟨137975957504,62458⟩ E) ⟨137975957632,62218⟩ (N (N E ⟨137975957760,61978⟩ E) ⟨137975957888,61740⟩ E))) ⟨137975958016,61503⟩ (N (N (N (N E ⟨137975958144,61268⟩ E) ⟨137975958272,61033⟩ (N E ⟨137975958400,60799⟩ E)) ⟨137975958528,60567⟩ (N (N E ⟨137975958656,60336⟩ E) ⟨137975958784,60105⟩ E)) ⟨137975958912,59876⟩ (N (N (N E ⟨137975959040,59648⟩ E) ⟨137975959168,59421⟩ E) ⟨137975959296,59195⟩ (N (N E ⟨137975959424,58971⟩ E) ⟨137975959552,58747⟩ E))))) ⟨137975959680,58524⟩ (N (N (N (N (N (N E ⟨137975959808,58303⟩ E) ⟨137975959936,58082⟩ (N E ⟨137975960192,57644⟩ E)) ⟨137975960448,57210⟩ (N (N E ⟨137975960832,56567⟩ E) ⟨137975960960,56355⟩ E)) ⟨137975961216,55933⟩ (N (N (N E ⟨137975961472,55515⟩ E) ⟨137975961600,55308⟩ (N E ⟨137975962496,53882⟩ E)) ⟨137975963264,52697⟩ (N (N E ⟨137975963648,52116⟩ E) ⟨138110174592,7763984⟩ E))) ⟨138110174720,7733958⟩ (N (N (N (N E ⟨138110174848,7704077⟩ E) ⟨138110174976,7674340⟩ (N E ⟨138110175104,7644747⟩ E)) ⟨138110175232,7615296⟩ (N (N E ⟨138110175360,7585987⟩ E) ⟨138110175488,7556819⟩ E)) ⟨138110175616,7527791⟩ (N (N (N E ⟨138110175744,7498902⟩ E) ⟨138110175872,7470152⟩ E) ⟨138110176000,7441540⟩ (N (N E ⟨138110176128,7413064⟩ E) ⟨138110176256,7384725⟩ E)))) ⟨138110176384,7356521⟩ (N (N (N (N (N E ⟨138110176512,7328452⟩ E) ⟨138110176640,7300517⟩ (N E ⟨138110176768,7272714⟩ E)) ⟨138110176896,7245044⟩ (N (N E ⟨138110177024,7217506⟩ E) ⟨138110177152,7190098⟩ E)) ⟨138110177408,7135672⟩ (N (N (N E ⟨138110177536,7108652⟩ E) ⟨138110177664,7081760⟩ E) ⟨138110177792,7054995⟩ (N (N E ⟨138110177920,7028357⟩ E) ⟨138110178048,7001844⟩ E))) ⟨138110178304,6949193⟩ (N (N (N (N E ⟨138110178432,6923053⟩ E) ⟨138110178560,6897036⟩ (N E ⟨138110178688,6871141⟩ E)) ⟨138110178816,6845367⟩ (N (N E ⟨138110178944,6819715⟩ E) ⟨138110179328,6743475⟩ E)) ⟨138110179456,6718298⟩ (N (N (N E ⟨138110179712,6668298⟩ E) ⟨138110179968,6618762⟩ E) ⟨138110180096,6594166⟩ (N (N E ⟨138110180224,6569685⟩ E) ⟨138110180352,6545317⟩ E)))))))

noncomputable def tab7 : CTN :=
  (N (N (N (N (N (N (N (N E ⟨138110181376,6354389⟩ E) ⟨138244392448,28245033⟩ (N E ⟨138244392576,28135904⟩ E)) ⟨138244392704,28027303⟩ (N (N E ⟨138244392832,27919226⟩ E) ⟨138244392960,27811669⟩ E)) ⟨138244393088,27704630⟩ (N (N (N E ⟨138244393216,27598106⟩ E) ⟨138244393344,27492093⟩ (N E ⟨138244393472,27386590⟩ E)) ⟨138244393600,27281592⟩ (N (N E ⟨138244393728,27177098⟩ E) ⟨138244393856,27073103⟩ E))) ⟨138244393984,26969606⟩ (N (N (N (N E ⟨138244394112,26866603⟩ E) ⟨138244394240,26764092⟩ (N E ⟨138244394368,26662069⟩ E)) ⟨138244394496,26560533⟩ (N (N E ⟨138244394624,26459480⟩ E) ⟨138244394752,26358907⟩ E)) ⟨138244394880,26258811⟩ (N (N (N E ⟨138244395008,26159191⟩ E) ⟨138244395392,25863153⟩ E) ⟨138244395648,25668120⟩ (N (N E ⟨138244395776,25571293⟩ E) ⟨138244395904,25474923⟩ E)))) ⟨138244396160,25283541⟩ (N (N (N (N (N E ⟨138244396416,25093954⟩ E) ⟨138244396544,24999828⟩ (N E ⟨138244396800,24812895⟩ E)) ⟨138244396928,24720085⟩ (N (N E ⟨138244397440,24353156⟩ E) ⟨138244397568,24262490⟩ E)) ⟨138244398208,23815441⟩ (N (N (N E ⟨138244398592,23552152⟩ E) ⟨138244399104,23206737⟩ (N E ⟨138378610304,61420221⟩ E)) ⟨138378610432,61183146⟩ (N (N E ⟨138378610560,60947215⟩ E) ⟨138378610688,60712420⟩ E))) ⟨138378610816,60478756⟩ (N (N (N (N E ⟨138378610944,60246216⟩ E) ⟨138378611072,60014792⟩ (N E ⟨138378611200,59784480⟩ E)) ⟨138378611328,59555272⟩ (N (N E ⟨138378611456,59327162⟩ E) ⟨138378611584,59100144⟩ E)) ⟨138378611712,58874211⟩ (N (N (N E ⟨138378611840,58649357⟩ E) ⟨138378611968,58425577⟩ E) ⟨138378612096,58202864⟩ (N (N E ⟨138378612224,57981211⟩ E) ⟨138378612352,57760613⟩ E))))) ⟨138378612480,57541064⟩ (N (N (N (N (N (N E ⟨138378612608,57322558⟩ E) ⟨138378612736,57105088⟩ (N E ⟨138378612864,56888649⟩ E)) ⟨138378612992,56673236⟩ (N (N E ⟨138378613376,56033088⟩ E) ⟨138378613504,55821716⟩ E)) ⟨138378613632,55611342⟩ (N (N (N E ⟨138378614144,54779693⟩ E) ⟨138378614400,54369703⟩ (N E ⟨138378614528,54166146⟩ E)) ⟨138378614656,53963542⟩ (N (N E ⟨138378615040,53361391⟩ E) ⟨138378615296,52964621⟩ E))) ⟨138378615680,52376359⟩ (N (N (N (N E ⟨138378615808,52182089⟩ E) ⟨138378616192,51604663⟩ (N E ⟨138378616320,51413965⟩ E)) ⟨138378616832,50659929⟩ (N (N E ⟨138512828160,107195495⟩ E) ⟨138512828288,106782133⟩ E)) ⟨138512828416,106370763⟩ (N (N (N E ⟨138512828544,105961373⟩ E) ⟨138512828672,105553952⟩ E) ⟨138512828800,105148488⟩ (N (N E ⟨138512828928,104744971⟩ E) ⟨138512829056,104343389⟩ E)))) ⟨138512829184,103943730⟩ (N (N (N (N (N E ⟨138512829312,103545985⟩ E) ⟨138512829440,103150141⟩ (N E ⟨138512829568,102756188⟩ E)) ⟨138512829696,102364115⟩ (N (N E ⟨138512829824,101973911⟩ E) ⟨138512829952,101585567⟩ E)) ⟨138512830080,101199070⟩ (N (N (N E ⟨138512830208,100814410⟩ E) ⟨138512830336,100431578⟩ E) ⟨138512830464,100050562⟩ (N (N E ⟨138512830592,99671352⟩ E) ⟨138512830720,99293938⟩ E))) ⟨138512830848,98918310⟩ (N (N (N (N E ⟨138512830976,98544458⟩ E) ⟨138512831104,98172371⟩ (N E ⟨138512831232,97802040⟩ E)) ⟨138512831616,96701480⟩ (N (N E ⟨138512831744,96338072⟩ E) ⟨138512831872,95976371⟩ E)) ⟨138512832000,95616366⟩ (N (N (N E ⟨138512832128,95258049⟩ E) ⟨138512832384,94546439⟩ E) ⟨138512832512,94193128⟩ (N (N E ⟨138512832640,93841466⟩ E) ⟨138512832768,93491444⟩ E)))))) ⟨138512832896,93143054⟩ (N (N (N (N (N (N (N E ⟨138512833024,92796286⟩ E) ⟨138512833280,92107581⟩ (N E ⟨138512833408,91765626⟩ E)) ⟨138512833536,91425257⟩ (N (N E ⟨138512833664,91086466⟩ E) ⟨138512834304,89415867⟩ E)) ⟨138512834432,89086358⟩ (N (N (N E ⟨138512834560,88758367⟩ E) ⟨138647046016,165469675⟩ (N E ⟨138647046144,164832215⟩ E)) ⟨138647046272,164197824⟩ (N (N E ⟨138647046400,163566485⟩ E) ⟨138647046528,162938178⟩ E))) ⟨138647046656,162312887⟩ (N (N (N (N E ⟨138647046784,161690595⟩ E) ⟨138647046912,161071284⟩ (N E ⟨138647047040,160454937⟩ E)) ⟨138647047168,159841537⟩ (N (N E ⟨138647047296,159231067⟩ E) ⟨138647047424,158623511⟩ E)) ⟨138647047552,158018851⟩ (N (N (N E ⟨138647047680,157417072⟩ E) ⟨138647047808,156818156⟩ E) ⟨138647047936,156222087⟩ (N (N E ⟨138647048064,155628850⟩ E) ⟨138647048192,155038427⟩ E)))) ⟨138647048320,154450803⟩ (N (N (N (N (N E ⟨138647048448,153865963⟩ E) ⟨138647048704,152704567⟩ (N E ⟨138647048832,152127981⟩ E)) ⟨138647048960,151554116⟩ (N (N E ⟨138647049088,150982955⟩ E) ⟨138647049344,149848687⟩ E)) ⟨138647049728,148167195⟩ (N (N (N E ⟨138647049856,147611946⟩ E) ⟨138647049984,147059298⟩ E) ⟨138647050240,145961743⟩ (N (N E ⟨138647050496,144874414⟩ E) ⟨138647050624,144334548⟩ E))) ⟨138647050752,143797197⟩ (N (N (N (N E ⟨138647051392,141147657⟩ E) ⟨138647052160,138048289⟩ (N E ⟨138647052288,137540034⟩ E)) ⟨138781263872,236134548⟩ (N (N E ⟨138781264000,235225735⟩ E) ⟨138781264128,234321293⟩ E)) ⟨138781264256,233421197⟩ (N (N (N E ⟨138781264384,232525421⟩ E) ⟨138781264512,231633940⟩ E) ⟨138781264640,230746731⟩ (N (N E ⟨138781264768,229863767⟩ E) ⟨138781264896,228985026⟩ E))))) ⟨138781265024,228110482⟩ (N (N (N (N (N (N E ⟨138781265152,227240112⟩ E) ⟨138781265280,226373891⟩ (N E ⟨138781265408,225511797⟩ E)) ⟨138781265536,224653805⟩ (N (N E ⟨138781265664,223799892⟩ E) ⟨138781265792,222950034⟩ E)) ⟨138781265920,222104209⟩ (N (N (N E ⟨138781266048,221262394⟩ E) ⟨138781266176,220424566⟩ (N E ⟨138781266304,219590702⟩ E)) ⟨138781266432,218760780⟩ (N (N E ⟨138781266560,217934777⟩ E) ⟨138781266816,216294440⟩ E))) ⟨138781266944,215480063⟩ (N (N (N (N E ⟨138781267072,214669517⟩ E) ⟨138781267200,213862781⟩ (N E ⟨138781267328,213059833⟩ E)) ⟨138781267456,212260652⟩ (N (N E ⟨138781267584,211465217⟩ E) ⟨138781267840,209885500⟩ E)) ⟨138781267968,209101176⟩ (N (N (N E ⟨138781268096,208320515⟩ E) ⟨138781268224,207543496⟩ E) ⟨138781268480,206000301⟩ (N (N E ⟨138781268864,203712318⟩ E) ⟨138781268992,202956727⟩ E)))) ⟨138781269120,202204637⟩ (N (N (N (N (N E ⟨138781269248,201456030⟩ E) ⟨138781269504,199969186⟩ (N E ⟨138781269632,199230911⟩ E)) ⟨138781269888,197764559⟩ (N (N E ⟨138781270016,197036445⟩ E) ⟨138915481728,319074957⟩ E)) ⟨138915481856,317848115⟩ (N (N (N E ⟨138915481984,316627168⟩ E) ⟨138915482112,315412081⟩ E) ⟨138915482240,314202821⟩ (N (N E ⟨138915482368,312999354⟩ E) ⟨138915482496,311801647⟩ E))) ⟨138915482624,310609667⟩ (N (N (N (N E ⟨138915482752,309423381⟩ E) ⟨138915482880,308242756⟩ (N E ⟨138915483008,307067760⟩ E)) ⟨138915483136,305898361⟩ (N (N E ⟨138915483264,304734526⟩ E) ⟨138915483392,303576225⟩ E)) ⟨138915483520,302423425⟩ (N (N (N E ⟨138915483648,301276095⟩ E) ⟨138915483776,300134204⟩ E) ⟨138915483904,298997722⟩ (N (N E ⟨138915484160,296740857⟩ E) ⟨138915484288,295620415⟩ E)))))))

noncomputable def tab8 : CTN :=
  (N (N (N (N (N (N (N (N E ⟨138915484800,291191212⟩ E) ⟨138915484928,290096904⟩ (N E ⟨138915485056,289007735⟩ E)) ⟨138915485184,287923676⟩ (N (N E ⟨138915485312,286844698⟩ E) ⟨138915485696,283637965⟩ E)) ⟨138915485952,281525029⟩ (N (N (N E ⟨138915486080,280475944⟩ E) ⟨138915486208,279431743⟩ (N E ⟨138915486464,277357888⟩ E)) ⟨138915486720,275303247⟩ (N (N E ⟨138915486848,274283066⟩ E) ⟨138915486976,273267608⟩ E))) ⟨138915487232,271250759⟩ (N (N (N (N E ⟨138915487744,267272605⟩ E) ⟨139049699456,415767520⟩ (N E ⟨139049699584,414168896⟩ E)) ⟨139049699712,412577953⟩ (N (N E ⟨139049699840,410994646⟩ E) ⟨139049699968,409418931⟩ E)) ⟨139049700096,407850765⟩ (N (N (N E ⟨139049700224,406290105⟩ E) ⟨139049700352,404736907⟩ E) ⟨139049700480,403191128⟩ (N (N E ⟨139049700608,401652726⟩ E) ⟨139049700736,400121659⟩ E)))) ⟨139049700864,398597885⟩ (N (N (N (N (N E ⟨139049700992,397081362⟩ E) ⟨139049701120,395572049⟩ (N E ⟨139049701248,394069904⟩ E)) ⟨139049701376,392574887⟩ (N (N E ⟨139049701504,391086957⟩ E) ⟨139049701632,389606074⟩ E)) ⟨139049701888,386665289⟩ (N (N (N E ⟨139049702016,385205308⟩ E) ⟨139049702144,383752215⟩ (N E ⟨139049702400,380866538⟩ E)) ⟨139049702528,379433877⟩ (N (N E ⟨139049702656,378007950⟩ E) ⟨139049702784,376588719⟩ E))) ⟨139049702912,375176147⟩ (N (N (N (N E ⟨139049703296,370978005⟩ E) ⟨139049703680,366838452⟩ (N E ⟨139049703808,365471452⟩ E)) ⟨139049703936,364110816⟩ (N (N E ⟨139049704320,360066748⟩ E) ⟨139049704576,357401882⟩ E)) ⟨139049705088,352145745⟩ (N (N (N E ⟨139049705472,348266970⟩ E) ⟨139183917312,523297751⟩ E) ⟨139183917440,521287612⟩ (N (N E ⟨139183917568,519287121⟩ E) ⟨139183917696,517296223⟩ E))))) ⟨139183917824,515314863⟩ (N (N (N (N (N (N E ⟨139183917952,513342986⟩ E) ⟨139183918080,511380538⟩ (N E ⟨139183918208,509427464⟩ E)) ⟨139183918336,507483711⟩ (N (N E ⟨139183918464,505549225⟩ E) ⟨139183918592,503623953⟩ E)) ⟨139183918720,501707843⟩ (N (N (N E ⟨139183918848,499800843⟩ E) ⟨139183918976,497902900⟩ (N E ⟨139183919104,496013963⟩ E)) ⟨139183919232,494133980⟩ (N (N E ⟨139183919360,492262901⟩ E) ⟨139183919488,490400675⟩ E))) ⟨139183919616,488547252⟩ (N (N (N (N E ⟨139183919744,486702582⟩ E) ⟨139183919872,484866616⟩ (N E ⟨139183920000,483039303⟩ E)) ⟨139183920128,481220596⟩ (N (N E ⟨139183920384,477608802⟩ E) ⟨139183920512,475815620⟩ E)) ⟨139183920640,474030850⟩ (N (N (N E ⟨139183920768,472254445⟩ E) ⟨139183920896,470486359⟩ E) ⟨139183921152,466974955⟩ (N (N E ⟨139183921408,463496266⟩ E) ⟨139183921536,461769076⟩ E)))) ⟨139183921664,460049929⟩ (N (N (N (N (N E ⟨139183921920,456635582⟩ E) ⟨139183922048,454940294⟩ (N E ⟨139183922560,448237348⟩ E)) ⟨139183922816,444932195⟩ (N (N E ⟨139183923200,440031407⟩ E) ⟨139318135168,642762364⟩ E)) ⟨139318135296,640295702⟩ (N (N (N E ⟨139318135424,637840869⟩ E) ⟨139318135552,635397796⟩ E) ⟨139318135680,632966416⟩ (N (N E ⟨139318135808,630546662⟩ E) ⟨139318135936,628138466⟩ E))) ⟨139318136064,625741763⟩ (N (N (N (N E ⟨139318136192,623356488⟩ E) ⟨139318136320,620982573⟩ (N E ⟨139318136448,618619956⟩ E)) ⟨139318136576,616268570⟩ (N (N E ⟨139318136704,613928353⟩ E) ⟨139318136832,611599240⟩ E)) ⟨139318136960,609281168⟩ (N (N (N E ⟨139318137088,606974075⟩ E) ⟨139318137216,604677898⟩ E) ⟨139318137344,602392575⟩ (N (N E ⟨139318137472,600118045⟩ E) ⟨139318137600,597854246⟩ E)))))) ⟨139318137728,595601118⟩ (N (N (N (N (N (N (N E ⟨139318137856,593358600⟩ E) ⟨139318138112,588905156⟩ (N E ⟨139318138240,586694112⟩ E)) ⟨139318138368,584493440⟩ (N (N E ⟨139318138624,580122983⟩ E) ⟨139318138752,577953081⟩ E)) ⟨139318139008,573643647⟩ (N (N (N E ⟨139318139136,571504001⟩ E) ⟨139318139264,569374327⟩ (N E ⟨139318139392,567254570⟩ E)) ⟨139318139520,565144673⟩ (N (N E ⟨139318139648,563044583⟩ E) ⟨139318139776,560954245⟩ E))) ⟨139318139904,558873603⟩ (N (N (N (N E ⟨139318140032,556802605⟩ E) ⟨139318140672,546590397⟩ (N E ⟨139318140928,542571166⟩ E)) ⟨139452353024,774018741⟩ (N (N E ⟨139452353152,771051226⟩ E) ⟨139452353280,768097928⟩ E)) ⟨139452353408,765158764⟩ (N (N (N E ⟨139452353536,762233654⟩ E) ⟨139452353664,759322518⟩ E) ⟨139452353792,756425274⟩ (N (N E ⟨139452353920,753541843⟩ E) ⟨139452354048,750672147⟩ E)))) ⟨139452354176,747816106⟩ (N (N (N (N (N E ⟨139452354304,744973644⟩ E) ⟨139452354432,742144682⟩ (N E ⟨139452354560,739329144⟩ E)) ⟨139452354688,736526953⟩ (N (N E ⟨139452354816,733738033⟩ E) ⟨139452354944,730962309⟩ E)) ⟨139452355072,728199706⟩ (N (N (N E ⟨139452355200,725450150⟩ E) ⟨139452355456,719989882⟩ E) ⟨139452355584,717279024⟩ (N (N E ⟨139452355712,714580920⟩ E) ⟨139452355840,711895497⟩ E))) ⟨139452355968,709222686⟩ (N (N (N (N E ⟨139452356096,706562413⟩ E) ⟨139452356224,703914609⟩ (N E ⟨139452356352,701279204⟩ E)) ⟨139452356608,696045312⟩ (N (N E ⟨139452356736,693446687⟩ E) ⟨139452356864,690860185⟩ E)) ⟨139452356992,688285737⟩ (N (N (N E ⟨139452357248,683172738⟩ E) ⟨139452357504,678107157⟩ E) ⟨139452357760,673088464⟩ (N (N E ⟨139452357888,670596539⟩ E) ⟨139452358272,663189676⟩ E))))) ⟨139452358400,660743480⟩ (N (N (N (N (N (N E ⟨139452358656,655884850⟩ E) ⟨139586570880,916917811⟩ (N E ⟨139586571008,913405811⟩ E)) ⟨139586571136,909910620⟩ (N (N E ⟨139586571264,906432141⟩ E) ⟨139586571392,902970279⟩ E)) ⟨139586571520,899524937⟩ (N (N (N E ⟨139586571648,896096023⟩ E) ⟨139586571776,892683441⟩ (N E ⟨139586571904,889287098⟩ E)) ⟨139586572032,885906902⟩ (N (N E ⟨139586572160,882542760⟩ E) ⟨139586572288,879194582⟩ E))) ⟨139586572416,875862275⟩ (N (N (N (N E ⟨139586572544,872545751⟩ E) ⟨139586572672,869244919⟩ (N E ⟨139586572800,865959690⟩ E)) ⟨139586572928,862689976⟩ (N (N E ⟨139586573184,856196740⟩ E) ⟨139586573312,852973045⟩ E)) ⟨139586573440,849764517⟩ (N (N (N E ⟨139586573568,846571069⟩ E) ⟨139586573696,843392618⟩ E) ⟨139586573824,840229078⟩ (N (N E ⟨139586573952,837080366⟩ E) ⟨139586574080,833946398⟩ E)))) ⟨139586574208,830827091⟩ (N (N (N (N (N E ⟨139586574464,824632134⟩ E) ⟨139586574592,821556320⟩ (N E ⟨139586574848,815447619⟩ E)) ⟨139586575744,794509586⟩ (N (N E ⟨139586576256,782846616⟩ E) ⟨139586576384,779964392⟩ E)) ⟨139720788608,1075423275⟩ (N (N (N E ⟨139720788736,1071304164⟩ E) ⟨139720788864,1067204767⟩ E) ⟨139720788992,1063124972⟩ (N (N E ⟨139720789120,1059064665⟩ E) ⟨139720789248,1055023736⟩ E))) ⟨139720789376,1051002072⟩ (N (N (N (N E ⟨139720789504,1046999565⟩ E) ⟨139720789632,1043016104⟩ (N E ⟨139720789760,1039051582⟩ E)) ⟨139720789888,1035105889⟩ (N (N E ⟨139720790016,1031178918⟩ E) ⟨139720790144,1027270564⟩ E)) ⟨139720790272,1023380719⟩ (N (N (N E ⟨139720790400,1019509280⟩ E) ⟨139720790528,1015656141⟩ E) ⟨139720790656,1011821199⟩ (N (N E ⟨139720790912,1004205493⟩ E) ⟨139720791040,1000424525⟩ E)))))))

noncomputable def tab9 : CTN :=
  (N (N (N (N (N (N (N (N E ⟨139720791296,992915855⟩ E) ⟨139720791424,989187952⟩ (N E ⟨139720791552,985477538⟩ E)) ⟨139720791680,981784515⟩ (N (N E ⟨139720791808,978108786⟩ E) ⟨139720791936,974450252⟩ E)) ⟨139720792064,970808817⟩ (N (N (N E ⟨139720792320,963576864⟩ E) ⟨139720792448,959986155⟩ (N E ⟨139720792576,956412165⟩ E)) ⟨139720792832,949313973⟩ (N (N E ⟨139720792960,945789585⟩ E) ⟨139720793088,942281546⟩ E))) ⟨139720793344,935314156⟩ (N (N (N (N E ⟨139720793728,924983437⟩ E) ⟨139720793984,918175502⟩ (N E ⟨139720794112,914795035⟩ E)) ⟨139855006720,1232287203⟩ (N (N E ⟨139855006848,1227580829⟩ E) ⟨139855006976,1222896915⟩ E)) ⟨139855007104,1218235333⟩ (N (N (N E ⟨139855007232,1213595956⟩ E) ⟨139855007360,1208978655⟩ E) ⟨139855007488,1204383306⟩ (N (N E ⟨139855007616,1199809782⟩ E) ⟨139855007744,1195257960⟩ E)))) ⟨139855007872,1190727717⟩ (N (N (N (N (N E ⟨139855008000,1186218928⟩ E) ⟨139855008128,1181731474⟩ (N E ⟨139855008256,1177265231⟩ E)) ⟨139855008384,1172820081⟩ (N (N E ⟨139855008512,1168395904⟩ E) ⟨139855008640,1163992580⟩ E)) ⟨139855008768,1159609993⟩ (N (N (N E ⟨139855009152,1146585479⟩ E) ⟨139855009536,1133743419⟩ (N E ⟨139855009792,1125281895⟩ E)) ⟨139855009920,1121080752⟩ (N (N E ⟨139855010176,1112737153⟩ E) ⟨139855010432,1104471074⟩ E))) ⟨139855011072,1084139396⟩ (N (N (N (N E ⟨139855011456,1072164875⟩ E) ⟨139855011712,1064273676⟩ (N E ⟨139855011840,1060355316⟩ E)) ⟨139989224576,1408486147⟩ (N (N E ⟨139989224704,1403111977⟩ E) ⟨139989224832,1397763430⟩ E)) ⟨139989224960,1392440360⟩ (N (N (N E ⟨139989225088,1387142620⟩ E) ⟨139989225216,1381870066⟩ E) ⟨139989225344,1376622554⟩ (N (N E ⟨139989225472,1371399943⟩ E) ⟨139989225600,1366202089⟩ E))))) ⟨139989225728,1361028853⟩ (N (N (N (N (N (N E ⟨139989225856,1355880094⟩ E) ⟨139989225984,1350755673⟩ (N E ⟨139989226112,1345655453⟩ E)) ⟨139989226240,1340579296⟩ (N (N E ⟨139989226368,1335527067⟩ E) ⟨139989226496,1330498629⟩ E)) ⟨139989226624,1325493849⟩ (N (N (N E ⟨139989227008,1310620122⟩ E) ⟨139989227136,1305708645⟩ (N E ⟨139989227264,1300820167⟩ E)) ⟨139989227520,1291111691⟩ (N (N E ⟨139989227648,1286291437⟩ E) ⟨139989227776,1281493669⟩ E))) ⟨139989228032,1271965093⟩ (N (N (N (N E ⟨139989228416,1257837762⟩ E) ⟨139989228544,1253172302⟩ (N E ⟨139989228928,1239305181⟩ E)) ⟨139989229568,1216617055⟩ (N (N E ⟨140123442304,1601740208⟩ E) ⟨140123442432,1595628665⟩ E)) ⟨140123442560,1589546261⟩ (N (N (N E ⟨140123442688,1583492828⟩ E) ⟨140123442816,1577468201⟩ E) ⟨140123442944,1571472217⟩ (N (N E ⟨140123443072,1565504710⟩ E) ⟨140123443200,1559565520⟩ E)))) ⟨140123443328,1553654485⟩ (N (N (N (N (N E ⟨140123443456,1547771445⟩ E) ⟨140123443584,1541916240⟩ (N E ⟨140123443712,1536088714⟩ E)) ⟨140123443840,1530288708⟩ (N (N E ⟨140123443968,1524516067⟩ E) ⟨140123444096,1518770637⟩ E)) ⟨140123444224,1513052263⟩ (N (N (N E ⟨140123444352,1507360792⟩ E) ⟨140123444480,1501696073⟩ E) ⟨140123444608,1496057954⟩ (N (N E ⟨140123444736,1490446287⟩ E) ⟨140123444864,1484860921⟩ E))) ⟨140123444992,1479301710⟩ (N (N (N (N E ⟨140123445248,1468261163⟩ E) ⟨140123445504,1457323483⟩ (N E ⟨140123445632,1451892858⟩ E)) ⟨140123445760,1446487520⟩ (N (N E ⟨140123446144,1430421821⟩ E) ⟨140123446400,1419835225⟩ E)) ⟨140123446656,1409346442⟩ (N (N (N E ⟨140123446912,1398954390⟩ E) ⟨140123447296,1383545347⟩ E) ⟨140257660288,1793535994⟩ (N (N E ⟨140257660544,1779907933⟩ E) ⟨140257660672,1773142471⟩ E)))))) ⟨140257660800,1766409142⟩ (N (N (N (N (N (N (N E ⟨140257660928,1759707763⟩ E) ⟨140257661056,1753038153⟩ (N E ⟨140257661184,1746400130⟩ E)) ⟨140257661312,1739793515⟩ (N (N E ⟨140257661440,1733218130⟩ E) ⟨140257661568,1726673798⟩ E)) ⟨140257661696,1720160343⟩ (N (N (N E ⟨140257661824,1713677589⟩ E) ⟨140257661952,1707225364⟩ (N E ⟨140257662080,1700803495⟩ E)) ⟨140257662208,1694411811⟩ (N (N E ⟨140257662336,1688050141⟩ E) ⟨140257662464,1681718317⟩ E))) ⟨140257662720,1669143534⟩ (N (N (N (N E ⟨140257662848,1662900242⟩ E) ⟨140257663104,1650501037⟩ (N E ⟨140257663232,1644344796⟩ E)) ⟨140257663616,1626047589⟩ (N (N E ⟨140257663872,1613990788⟩ E) ⟨140257664000,1608004318⟩ E)) ⟨140257664128,1602045592⟩ (N (N (N E ⟨140257664256,1596114459⟩ E) ⟨140257664384,1590210763⟩ E) ⟨140257664512,1584334353⟩ (N (N E ⟨140257664768,1572662787⟩ E) ⟨140257664896,1566867331⟩ E)))) ⟨140257665024,1561098561⟩ (N (N (N (N (N E ⟨140391878016,2009677071⟩ E) ⟨140391878272,1994406676⟩ (N E ⟨140391878400,1986825901⟩ E)) ⟨140391878528,1979281131⟩ (N (N E ⟨140391878656,1971772162⟩ E) ⟨140391878784,1964298789⟩ E)) ⟨140391878912,1956860810⟩ (N (N (N E ⟨140391879040,1949458024⟩ E) ⟨140391879168,1942090232⟩ E) ⟨140391879296,1934757235⟩ (N (N E ⟨140391879424,1927458836⟩ E) ⟨140391879552,1920194838⟩ E))) ⟨140391879808,1905769273⟩ (N (N (N (N E ⟨140391879936,1898607319⟩ E) ⟨140391880064,1891478997⟩ (N E ⟨140391880320,1877322492⟩ E)) ⟨140391880448,1870293933⟩ (N (N E ⟨140391880576,1863298255⟩ E) ⟨140391880704,1856335274⟩ E)) ⟨140391880960,1842506671⟩ (N (N (N E ⟨140391881216,1828806669⟩ E) ⟨140391881600,1808494667⟩ E) ⟨140391881856,1795109942⟩ (N (N E ⟨140391882112,1781848883⟩ E) ⟨140391882624,1755692307⟩ E))))) ⟨140391882752,1749228337⟩ (N (N (N (N (N (N E ⟨140526096128,2212459945⟩ E) ⟨140526096384,2195696626⟩ (N E ⟨140526096512,2187374539⟩ E)) ⟨140526096640,2179091866⟩ (N (N E ⟨140526096768,2170848383⟩ E) ⟨140526096896,2162643867⟩ E)) ⟨140526097024,2154478097⟩ (N (N (N E ⟨140526097152,2146350854⟩ E) ⟨140526097280,2138261920⟩ (N E ⟨140526097408,2130211079⟩ E)) ⟨140526097536,2122198114⟩ (N (N E ⟨140526097664,2114222813⟩ E) ⟨140526097792,2106284963⟩ E))) ⟨140526097920,2098384352⟩ (N (N (N (N E ⟨140526098176,2082694015⟩ E) ⟨140526098304,2074903872⟩ (N E ⟨140526098560,2059432613⟩ E)) ⟨140526098688,2051751090⟩ (N (N E ⟨140526098944,2036495247⟩ E) ⟨140526099072,2028920528⟩ E)) ⟨140526099328,2013876510⟩ (N (N (N E ⟨140526099456,2006406819⟩ E) ⟨140526099584,1998971747⟩ E) ⟨140526099712,1991571104⟩ (N (N E ⟨140526099840,1984204696⟩ E) ⟨140526099968,1976872334⟩ E)))) ⟨140526100096,1969573830⟩ (N (N (N (N (N E ⟨140526100352,1955077646⟩ E) ⟨140526100480,1947879594⟩ (N E ⟨140660314368,2413024171⟩ E)) ⟨140660314496,2403895724⟩ (N (N E ⟨140660314624,2394810428⟩ E) ⟨140660314752,2385768037⟩ E)) ⟨140660314880,2376768310⟩ (N (N (N E ⟨140660315008,2367811004⟩ E) ⟨140660315136,2358895879⟩ E) ⟨140660315264,2350022698⟩ (N (N E ⟨140660315520,2332401220⟩ E) ⟨140660315648,2323652454⟩ E))) ⟨140660315904,2306277710⟩ (N (N (N (N E ⟨140660316160,2289065152⟩ E) ⟨140660316416,2272012966⟩ (N E ⟨140660316544,2263546451⟩ E)) ⟨140660316800,2246731472⟩ (N (N E ⟨140660316928,2238382569⟩ E) ⟨140660317056,2230072432⟩ E)) ⟨140660317312,2213567596⟩ (N (N (N E ⟨140660317440,2205372470⟩ E) ⟨140660317696,2189095743⟩ E) ⟨140660317824,2181013722⟩ (N (N E ⟨140660318208,2156990541⟩ E) ⟨140794532480,2628551302⟩ E)))))))

noncomputable def tab10 : CTN :=
  (N (N (N (N (N (N (N (N E ⟨140794532992,2589168404⟩ E) ⟨140794533248,2569753709⟩ (N E ⟨140794533504,2550520753⟩ E)) ⟨140794534144,2503220156⟩ (N (N E ⟨140794534272,2493892063⟩ E) ⟨140794534912,2447898293⟩ E)) ⟨140794535552,2402960542⟩ (N (N (N E ⟨140794535808,2385274605⟩ E) ⟨140794535936,2376492688⟩ (N E ⟨140928750208,2882744747⟩ E)) ⟨140928750336,2871870296⟩ (N (N E ⟨140928750464,2861047103⟩ E) ⟨140928750592,2850274879⟩ E))) ⟨140928750720,2839553335⟩ (N (N (N (N E ⟨140928750848,2828882186⟩ E) ⟨140928750976,2818261147⟩ (N E ⟨140928751104,2807689935⟩ E)) ⟨140928751232,2797168272⟩ (N (N E ⟨140928751360,2786695877⟩ E) ⟨140928751616,2765897790⟩ E)) ⟨140928751744,2755571550⟩ (N (N (N E ⟨140928751872,2745293482⟩ E) ⟨140928752000,2735063317⟩ E) ⟨140928752128,2724880788⟩ (N (N E ⟨140928752512,2694616362⟩ E) ⟨140928752640,2684621731⟩ E)))) ⟨140928752896,2664771179⟩ (N (N (N (N (N E ⟨140928753024,2654914744⟩ E) ⟨140928753280,2635338285⟩ (N E ⟨140928753664,2606310863⟩ E)) ⟨141062968320,3112797384⟩ (N (N E ⟨141062968576,3089434332⟩ E) ⟨141062968704,3077835050⟩ E)) ⟨141062968832,3066290185⟩ (N (N (N E ⟨141062969088,3043362484⟩ E) ⟨141062969344,3020648805⟩ (N E ⟨141062969728,2986974345⟩ E)) ⟨141062970112,2953768102⟩ (N (N E ⟨141062970752,2899443745⟩ E) ⟨141062970880,2888729241⟩ E))) ⟨141062971392,2846363239⟩ (N (N (N (N E ⟨141197186432,3348379765⟩ E) ⟨141197186816,3310877028⟩ (N E ⟨141197186944,3298492970⟩ E)) ⟨141197187072,3286166793⟩ (N (N E ⟨141197187328,3261686787⟩ E) ⟨141197187584,3237434439⟩ E)) ⟨141197187712,3225392842⟩ (N (N (N E ⟨141197188480,3154307690⟩ E) ⟨141197188864,3119499903⟩ E) ⟨141197189120,3096561355⟩ (N (N E ⟨141331404800,3562350875⟩ E) ⟨141331405056,3535813460⟩ E))))) ⟨141331405184,3522637472⟩ (N (N (N (N (N (N E ⟨141331405312,3509522837⟩ E) ⟨141331405696,3470543628⟩ (N E ⟨141331405952,3444858027⟩ E)) ⟨141331406336,3406773777⟩ (N (N E ⟨141331406464,3394196156⟩ E) ⟨141331406720,3369214663⟩ E)) ⟨141331406848,3356810152⟩ (N (N (N E ⟨141465622272,3878036344⟩ E) ⟨141465622656,3834722943⟩ (N E ⟨141465622784,3820419725⟩ E)) ⟨141465623168,3777908561⟩ (N (N E ⟨141465623680,3722143067⟩ E) ⟨141465623808,3708362854⟩ E))) ⟨141465623936,3694646391⟩ (N (N (N (N E ⟨141465624064,3680993322⟩ E) ⟨141465624192,3667403297⟩ (N E ⟨141465624448,3640410984⟩ E)) ⟨141465624576,3627008003⟩ (N (N E ⟨141599840000,4177456819⟩ E) ⟨141599840512,4115391661⟩ E)) ⟨141599841024,4054475523⟩ (N (N (N E ⟨141599841408,4009527131⟩ E) ⟨141599841920,3950560942⟩ E) ⟨141599842176,3921484571⟩ (N (N E ⟨141599842304,3907046756⟩ E) ⟨141734058880,4339005694⟩ E)))) ⟨141734059264,4290947491⟩ (N (N (N (N (N E ⟨141734059648,4243553178⟩ E) ⟨141734060032,4196811774⟩ (N E ⟨141868275328,4825432678⟩ E)) ⟨141868276992,4597032668⟩ (N (N E ⟨141868277760,4496181990⟩ E) ⟨142002495488,4805029944⟩ E)) ⟨142136713216,5123221857⟩ (N (N (N E ⟨142270930944,5450617679⟩ E) ⟨142405148672,5787071159⟩ E) ⟨142539366400,6132429910⟩ (N (N E ⟨142673584128,6486535485⟩ E) ⟨142807801856,6849223449⟩ E))) ⟨142942019584,7220323464⟩ (N (N (N (N E ⟨143076237312,7599659374⟩ E) ⟨143210455040,7987049288⟩ (N E ⟨143344672768,8382305677⟩ E)) ⟨143478890496,8785235472⟩ (N (N E ⟨143613108224,9195640158⟩ E) ⟨143747325952,9613315884⟩ E)) ⟨143881543680,10038053565⟩ (N (N (N E ⟨144015761408,10469639000⟩ E) ⟨144149979136,10907852980⟩ E) ⟨144284196864,11352471411⟩ (N (N E ⟨144418414592,11803265435⟩ E) ⟨145089503232,14141541911⟩ E)))))) ⟨145223720960,14624332832⟩ (N (N (N (N (N (N (N E ⟨146029027456,17540496856⟩ E) ⟨146029027584,17476036621⟩ (N E ⟨146029027712,17411872388⟩ E)) ⟨146029027840,17348002527⟩ (N (N E ⟨146029027968,17284425416⟩ E) ⟨146029028096,17221139448⟩ E)) ⟨146029028224,17158143022⟩ (N (N (N E ⟨146029028352,17095434549⟩ E) ⟨146029028480,17033012451⟩ (N E ⟨146029028608,16970875159⟩ E)) ⟨146029028736,16909021113⟩ (N (N E ⟨146029028864,16847448766⟩ E) ⟨146029028992,16786156578⟩ E))) ⟨146029029120,16725143020⟩ (N (N (N (N E ⟨146029029248,16664406573⟩ E) ⟨146029029376,16603945726⟩ (N E ⟨146029029504,16543758980⟩ E)) ⟨146029029632,16483844845⟩ (N (N E ⟨146029029760,16424201838⟩ E) ⟨146029029888,16364828489⟩ E)) ⟨146029030016,16305723334⟩ (N (N (N E ⟨146029030144,16246884921⟩ E) ⟨146029030272,16188311805⟩ E) ⟨146029030400,16130002552⟩ (N (N E ⟨146029030528,16071955735⟩ E) ⟨146029030656,16014169939⟩ E)))) ⟨146029030784,15956643754⟩ (N (N (N (N (N E ⟨146029030912,15899375782⟩ E) ⟨146029031040,15842364632⟩ (N E ⟨146029031296,15729107282⟩ E)) ⟨146029031424,15672858345⟩ (N (N E ⟨146029031552,15616860755⟩ E) ⟨146029031808,15505614239⟩ E)) ⟨146029031936,15450362643⟩ (N (N (N E ⟨146029032064,15395357056⟩ E) ⟨146029032192,15340596165⟩ E) ⟨146029032320,15286078662⟩ (N (N E ⟨146029032448,15231803251⟩ E) ⟨146029032576,15177768643⟩ E))) ⟨146029032832,15070416714⟩ (N (N (N (N E ⟨146029032960,15017096854⟩ E) ⟨146029033088,14964012717⟩ (N E ⟨146029033216,14911163054⟩ E)) ⟨146029033344,14858546622⟩ (N (N E ⟨146029033600,14754008520⟩ E) ⟨146029033728,14702084403⟩ E)) ⟨146029033856,14650388624⟩ (N (N (N E ⟨146029033984,14598919978⟩ E) ⟨146029034112,14547677269⟩ E) ⟨146029034240,14496659306⟩ (N (N E ⟨146029034624,14344942108⟩ E) ⟨146029034752,14294811379⟩ E))))) ⟨146029034880,14244899557⟩ (N (N (N (N (N (N E ⟨146029035136,14145728051⟩ E) ⟨146029035264,14096466096⟩ (N E ⟨146029035520,13998584151⟩ E)) ⟨146565906432,15626583152⟩ (N (N E ⟨147639648256,18932070952⟩ E) ⟨147773865984,19345330096⟩ E)) ⟨148847607808,22603371489⟩ (N (N (N E ⟨148981825536,23001038007⟩ E) ⟨149652914176,24940820940⟩ (N E ⟨151397744640,29436848512⟩ E)) ⟨151800397824,30325936625⟩ (N (N E ⟨153813663744,33677254131⟩ E) ⟨154618970240,34309130482⟩ E))) ⟨154618970368,34174620589⟩ (N (N (N (N E ⟨154618970496,34030483220⟩ E) ⟨154618970880,33541516667⟩ (N E ⟨154618971136,33169706406⟩ E)) ⟨154618971392,32762527531⟩ (N (N E ⟨154618971520,32546044844⟩ E) ⟨154618971776,32088070159⟩ E)) ⟨154618972032,31597833051⟩ (N (N (N E ⟨154618972160,31341036723⟩ E) ⟨154618972416,30804961588⟩ E) ⟨154618972800,29947363174⟩ (N (N E ⟨154618972928,29647981632⟩ E) ⟨154618973184,29030101448⟩ E)))) ⟨154618973696,27723448008⟩ (N (N (N (N (N E ⟨154618974208,26333212918⟩ E) ⟨154618974464,25610966402⟩ (N E ⟨154618975232,23356458401⟩ E)) ⟨154618975488,22581543192⟩ (N (N E ⟨154618975744,21797860699⟩ E) ⟨154618976128,20609757442⟩ E)) ⟨154618976384,19811865526⟩ (N (N (N E ⟨154618977024,17809445717⟩ E) ⟨154618977280,17009903431⟩ E) ⟨154618977792,15422488092⟩ (N (N E ⟨154618978304,13861447354⟩ E) ⟨155155849216,14040504136⟩ E))) ⟨156095373312,14356012415⟩ (N (N (N (N E ⟨158242856960,15082071680⟩ E) ⟨158913945600,15308711174⟩ (N E ⟨159182381056,15399148975⟩ E)) ⟨161061429248,16026017701⟩ (N (N E ⟨161329864704,16114355173⟩ E) ⟨161732517888,16246130011⟩ E)) ⟨161866735616,16289846493⟩ (N (N (N E ⟨163074695168,16677959410⟩ E) ⟨163208914560,11174556605⟩ E) ⟨163208914688,10778946325⟩ (N (N E ⟨163208914816,10388658651⟩ E) ⟨163208914944,10003856588⟩ E)))))))

noncomputable def tab11 : CTN :=
  (N (N (N (N (N (N (N (N E ⟨163208915968,7141055887⟩ E) ⟨163208916352,6175341094⟩ (N E ⟨163208916864,4987473700⟩ E)) ⟨163208917248,4174759615⟩ (N (N E ⟨163208917376,3919189493⟩ E) ⟨163208917760,3199452127⟩ E)) ⟨163208917888,2975394930⟩ (N (N (N E ⟨163208918400,2159724198⟩ E) ⟨163208918528,1976130397⟩ (N E ⟨163208918784,1633520237⟩ E)) ⟨163208919424,920934879⟩ (N (N E ⟨163208920448,206700442⟩ E) ⟨163208920576,153739518⟩ E))) ⟨163208920704,108707281⟩ (N (N (N (N E ⟨163208920832,71549112⟩ E) ⟨163477354752,1057242830⟩ (N E ⟨163880005504,5066185737⟩ E)) ⟨163880007040,2201824020⟩ (N (N E ⟨164416876800,4296954703⟩ E) ⟨164416878208,1866373344⟩ E)) ⟨164551093888,5736041210⟩ (N (N (N E ⟨164551094656,4048183235⟩ E) ⟨164551098368,25624568⟩ E) ⟨164685315584,170128683⟩ (N (N E ⟨164819531008,2456500599⟩ E) ⟨164819531520,1714326413⟩ E)))) ⟨164819531776,1393513926⟩ (N (N (N (N (N E ⟨164819533440,123301814⟩ E) ⟨164953751552,27082111⟩ (N E ⟨165087968768,174323996⟩ E)) ⟨165087969280,27560556⟩ (N (N E ⟨165356401152,3864075436⟩ E) ⟨165490618752,4133677072⟩ E)) ⟨165490621312,549197685⟩ (N (N (N E ⟨165624838144,1425862249⟩ E) ⟨165624838528,1000475536⟩ (N E ⟨165624839168,460820721⟩ E)) ⟨165759055616,1757979055⟩ (N (N E ⟨165759057024,380180618⟩ E) ⟨165759057536,131068466⟩ E))) ⟨165893272448,3177893625⟩ (N (N (N (N E ⟨165893273216,1940622941⟩ E) ⟨165893274880,307291085⟩ (N E ⟨165893275648,30333473⟩ E)) ⟨166027493376,30776735⟩ (N (N E ⟨166161708032,2968240132⟩ E) ⟨166161708928,1606807836⟩ E)) ⟨166161709184,1294476500⟩ (N (N (N E ⟨166161710208,386270569⟩ E) ⟨166161710336,310788498⟩ E) ⟨166295926144,2341066995⟩ (N (N E ⟨166295927296,893603569⟩ E) ⟨166295928320,186023393⟩ E))))) ⟨166295928832,31644633⟩ (N (N (N (N (N (N E ⟨166430145536,474604818⟩ E) ⟨166564363904,137160058⟩ (N E ⟨166698581376,249359918⟩ E)) ⟨166698582016,32896024⟩ (N (N E ⟨166832797312,1983879964⟩ E) ⟨166832797440,1804212308⟩ E)) ⟨166832798336,787795500⟩ (N (N (N E ⟨166832798592,574773826⟩ E) ⟨166832799744,33298690⟩ (N E ⟨166967015296,1638231375⟩ E)) ⟨166967016832,252076644⟩ (N (N E ⟨166967017472,33693717⟩ E) ⟨167235451776,581743186⟩ E))) ⟨167235452800,62041333⟩ (N (N (N (N E ⟨167235452928,34459903⟩ E) ⟨167369668608,1489094847⟩ (N E ⟨167369669504,583989286⟩ E)) ⟨167369669760,402960169⟩ (N (N E ⟨167369669888,325230237⟩ E) ⟨167369670528,62564527⟩ E)) ⟨167503887616,326695355⟩ (N (N (N E ⟨167638104192,1341886732⟩ E) ⟨167638104448,1055971760⟩ E) ⟨167638104576,926065130⟩ (N (N E ⟨167638105344,328131092⟩ E) ⟨167638106112,35546092⟩ E)))) ⟨167772322432,807520352⟩ (N (N (N (N (N E ⟨167772323712,64061469⟩ E) ⟨167906540160,810151152⟩ (N E ⟨167906540288,697029154⟩ E)) ⟨167906541056,199154239⟩ (N (N E ⟨167906541312,101083510⟩ E) ⟨167906541568,36225613⟩ E)) ⟨168040757760,934838728⟩ (N (N (N E ⟨168040758528,332258276⟩ E) ⟨168040759040,101693630⟩ E) ⟨168174976128,412648101⟩ (N (N E ⟨168309193600,598585114⟩ E) ⟨168309193856,414143212⟩ E))) ⟨168309193984,334856115⟩ (N (N (N (N E ⟨168309194752,37173895⟩ E) ⟨168443411328,600503934⟩ (N E ⟨168443412224,103423199⟩ E)) ⟨168443412352,66300202⟩ (N (N E ⟨168443412480,37470289⟩ E) ⟨168577629440,337327874⟩ E)) ⟨168577630208,37756530⟩ (N (N (N E ⟨168711847424,204491259⟩ E) ⟨168711847808,67100971⟩ E) ⟨168711847936,38032446⟩ (N (N E ⟨168846064896,339670987⟩ E) ⟨168846065536,67480260⟩ E)))))) ⟨168980282880,206072326⟩ (N (N (N (N (N (N (N E ⟨168980283264,67845240⟩ E) ⟨168980283392,38552644⟩ (N E ⟨169114500224,422363847⟩ E)) ⟨169114500736,152145026⟩ (N (N E ⟨169114500992,68195736⟩ E) ⟨169114501120,38796613⟩ E)) ⟨169248718848,39029630⟩ (N (N (N E ⟨169382936064,208251407⟩ E) ⟨169382936320,106842258⟩ (N E ⟨169382936448,68852609⟩ E)) ⟨169382936576,39251555⟩ (N (N E ⟨169517153792,208925522⟩ E) ⟨169517154176,69158670⟩ E))) ⟨169517154304,39462254⟩ (N (N (N (N E ⟨169651371648,154340311⟩ E) ⟨169651372032,39661600⟩ (N E ⟨169785589376,154832452⟩ E)) ⟨169785589760,39849474⟩ (N (N E ⟨169919807360,69985616⟩ E) ⟨169919807488,40025762⟩ E)) ⟨170054025216,40190358⟩ (N (N (N E ⟨170188242816,70459584⟩ E) ⟨170188242944,40343163⟩ E) ⟨170322460416,109345446⟩ (N (N E ⟨170322460544,70673019⟩ E) ⟨170322460672,40484085⟩ E)))) ⟨170456678144,109625194⟩ (N (N (N (N (N E ⟨170456678400,40613038⟩ E) ⟨170590896128,40729946⟩ (N E ⟨170725113856,40834737⟩ E)) ⟨170859331584,40927349⟩ (N (N E ⟨170993549312,41007726⟩ E) ⟨171127767040,41075819⟩ E)) ⟨171261984768,41131588⟩ (N (N (N E ⟨171530420224,41206024⟩ E) ⟨171798855808,19042279⟩ E) ⟨171798855936,5331210⟩ (N (N E ⟨171798856064,66057⟩ E) ⟨172335727744,3160659⟩ E))) ⟨172335727872,3150850⟩ (N (N (N (N E ⟨172335728000,3141079⟩ E) ⟨172335728128,3131346⟩ (N E ⟨172335728256,3121651⟩ E)) ⟨172335728384,3111994⟩ (N (N E ⟨172335728512,3102374⟩ E) ⟨172335728640,3092790⟩ E)) ⟨172335728768,3083244⟩ (N (N (N E ⟨172335728896,3073735⟩ E) ⟨172335729024,3064262⟩ E) ⟨172335729152,3054826⟩ (N (N E ⟨172335729280,3045426⟩ E) ⟨172335729408,3036063⟩ E))))) ⟨172335729536,3026735⟩ (N (N (N (N (N (N E ⟨172335729664,3017443⟩ E) ⟨172335729792,3008187⟩ (N E ⟨172335729920,2998966⟩ E)) ⟨172335730048,2989781⟩ (N (N E ⟨172335730176,2980630⟩ E) ⟨172335730304,2971515⟩ E)) ⟨172335730432,2962434⟩ (N (N (N E ⟨172335730560,2953389⟩ E) ⟨172335730688,2944377⟩ (N E ⟨172335730816,2935400⟩ E)) ⟨172335730944,2926458⟩ (N (N E ⟨172335731072,2917549⟩ E) ⟨172335731200,2908674⟩ E))) ⟨172335731328,2899833⟩ (N (N (N (N E ⟨172335731456,2891025⟩ E) ⟨172335731584,2882251⟩ (N E ⟨172335731712,2873511⟩ E)) ⟨172335732096,2847486⟩ (N (N E ⟨172335732224,2838877⟩ E) ⟨172335732352,2830300⟩ E)) ⟨172335732480,2821756⟩ (N (N (N E ⟨172335732864,2796316⟩ E) ⟨172335733248,2771162⟩ E) ⟨172335733376,2762840⟩ (N (N E ⟨172335733504,2754549⟩ E) ⟨172335733760,2738062⟩ E)))) ⟨172335734016,2721697⟩ (N (N (N (N (N E ⟨172335734144,2713560⟩ E) ⟨172335734272,2705454⟩ (N E ⟨172335734400,2697378⟩ E)) ⟨172335734784,2673331⟩ (N (N E ⟨172469945728,14450104⟩ E) ⟨172469945856,14405330⟩ E)) ⟨172469945984,14360729⟩ (N (N (N E ⟨172469946112,14316301⟩ E) ⟨172469946240,14272044⟩ E) ⟨172469946368,14227959⟩ (N (N E ⟨172469946496,14184043⟩ E) ⟨172469946624,14140297⟩ E))) ⟨172469946752,14096720⟩ (N (N (N (N E ⟨172469946880,14053310⟩ E) ⟨172469947008,14010067⟩ (N E ⟨172469947136,13966991⟩ E)) ⟨172469947264,13924080⟩ (N (N E ⟨172469947392,13881334⟩ E) ⟨172469947520,13838751⟩ E)) ⟨172469947648,13796332⟩ (N (N (N E ⟨172469947776,13754076⟩ E) ⟨172469947904,13711981⟩ E) ⟨172469948032,13670047⟩ (N (N E ⟨172469948160,13628274⟩ E) ⟨172469948288,13586660⟩ E)))))))

noncomputable def tab12 : CTN :=
  (N (N (N (N (N (N (N (N E ⟨172469948544,13503907⟩ E) ⟨172469948672,13462767⟩ (N E ⟨172469948800,13421784⟩ E)) ⟨172469948928,13380956⟩ (N (N E ⟨172469949056,13340284⟩ E) ⟨172469949184,13299766⟩ E)) ⟨172469949312,13259402⟩ (N (N (N E ⟨172469949440,13219191⟩ E) ⟨172469949568,13179133⟩ (N E ⟨172469949824,13099470⟩ E)) ⟨172469949952,13059864⟩ (N (N E ⟨172469950080,13020409⟩ E) ⟨172469950208,12981102⟩ E))) ⟨172469950336,12941943⟩ (N (N (N (N E ⟨172469950464,12902932⟩ E) ⟨172469950592,12864067⟩ (N E ⟨172469950720,12825350⟩ E)) ⟨172469950848,12786777⟩ (N (N E ⟨172469950976,12748350⟩ E) ⟨172469951104,12710067⟩ E)) ⟨172469951232,12671927⟩ (N (N (N E ⟨172469951488,12596077⟩ E) ⟨172469951616,12558365⟩ E) ⟨172469952000,12446072⟩ (N (N E ⟨172469952384,12335031⟩ E) ⟨172469952512,12298293⟩ E)))) ⟨172604163584,33917505⟩ (N (N (N (N (N E ⟨172604163712,33812491⟩ E) ⟨172604163840,33707884⟩ (N E ⟨172604163968,33603682⟩ E)) ⟨172604164096,33499882⟩ (N (N E ⟨172604164224,33396482⟩ E) ⟨172604164352,33293481⟩ E)) ⟨172604164480,33190878⟩ (N (N (N E ⟨172604164608,33088669⟩ E) ⟨172604164736,32986854⟩ (N E ⟨172604164864,32885430⟩ E)) ⟨172604164992,32784395⟩ (N (N E ⟨172604165120,32683749⟩ E) ⟨172604165248,32583489⟩ E))) ⟨172604165376,32483613⟩ (N (N (N (N E ⟨172604165504,32384119⟩ E) ⟨172604165632,32285007⟩ (N E ⟨172604165760,32186273⟩ E)) ⟨172604165888,32087917⟩ (N (N E ⟨172604166016,31989936⟩ E) ⟨172604166144,31892329⟩ E)) ⟨172604166272,31795094⟩ (N (N (N E ⟨172604166400,31698230⟩ E) ⟨172604166528,31601734⟩ E) ⟨172604166656,31505605⟩ (N (N E ⟨172604166784,31409842⟩ E) ⟨172604166912,31314443⟩ E))))) ⟨172604167040,31219405⟩ (N (N (N (N (N (N E ⟨172604167168,31124728⟩ E) ⟨172604167296,31030410⟩ (N E ⟨172604167424,30936449⟩ E)) ⟨172604167552,30842843⟩ (N (N E ⟨172604167680,30749591⟩ E) ⟨172604167808,30656692⟩ E)) ⟨172604167936,30564143⟩ (N (N (N E ⟨172604168064,30471943⟩ E) ⟨172604168192,30380091⟩ (N E ⟨172604168320,30288585⟩ E)) ⟨172604168448,30197423⟩ (N (N E ⟨172604168704,30016127⟩ E) ⟨172604168832,29925989⟩ E))) ⟨172604168960,29836189⟩ (N (N (N (N E ⟨172604169216,29657598⟩ E) ⟨172604169344,29568804⟩ (N E ⟨172604169600,29392211⟩ E)) ⟨172604169856,29216935⟩ (N (N E ⟨172604170240,28956464⟩ E) ⟨172738381440,61503221⟩ E)) ⟨172738381696,61123406⟩ (N (N (N E ⟨172738381824,60934599⟩ E) ⟨172738381952,60746521⟩ E) ⟨172738382080,60559168⟩ (N (N E ⟨172738382208,60372537⟩ E) ⟨172738382336,60186624⟩ E)))) ⟨172738382464,60001427⟩ (N (N (N (N (N E ⟨172738382592,59816942⟩ E) ⟨172738382720,59633166⟩ (N E ⟨172738382848,59450095⟩ E)) ⟨172738382976,59267727⟩ (N (N E ⟨172738383104,59086058⟩ E) ⟨172738383232,58905084⟩ E)) ⟨172738383360,58724803⟩ (N (N (N E ⟨172738383488,58545211⟩ E) ⟨172738383616,58366306⟩ E) ⟨172738383744,58188084⟩ (N (N E ⟨172738383872,58010542⟩ E) ⟨172738384000,57833677⟩ E))) ⟨172738384128,57657485⟩ (N (N (N (N E ⟨172738384256,57481964⟩ E) ⟨172738384384,57307111⟩ (N E ⟨172738384512,57132923⟩ E)) ⟨172738384640,56959396⟩ (N (N E ⟨172738384768,56786527⟩ E) ⟨172738384896,56614314⟩ E)) ⟨172738385024,56442754⟩ (N (N (N E ⟨172738385152,56271844⟩ E) ⟨172738385280,56101580⟩ E) ⟨172738385408,55931959⟩ (N (N E ⟨172738385536,55762980⟩ E) ⟨172738385792,55426932⟩ E)))))) ⟨172738385920,55259857⟩ (N (N (N (N (N (N (N E ⟨172738386048,55093412⟩ E) ⟨172738386176,54927594⟩ (N E ⟨172738386304,54762398⟩ E)) ⟨172738386560,54433868⟩ (N (N E ⟨172738386688,54270527⟩ E) ⟨172738386944,53945679⟩ E)) ⟨172738387072,53784167⟩ (N (N (N E ⟨172738387328,53462953⟩ E) ⟨172738387712,52985617⟩ (N E ⟨172738387968,52670351⟩ E)) ⟨172872599296,97152731⟩ (N (N E ⟨172872599424,96852398⟩ E) ⟨172872599552,96553226⟩ E))) ⟨172872599680,96255209⟩ (N (N (N (N E ⟨172872599808,95958340⟩ E) ⟨172872599936,95662616⟩ (N E ⟨172872600064,95368031⟩ E)) ⟨172872600192,95074579⟩ (N (N E ⟨172872600320,94782256⟩ E) ⟨172872600448,94491055⟩ E)) ⟨172872600576,94200972⟩ (N (N (N E ⟨172872600704,93912003⟩ E) ⟨172872600832,93624140⟩ E) ⟨172872600960,93337381⟩ (N (N E ⟨172872601088,93051719⟩ E) ⟨172872601216,92767149⟩ E)))) ⟨172872601344,92483667⟩ (N (N (N (N (N E ⟨172872601472,92201267⟩ E) ⟨172872601600,91919944⟩ (N E ⟨172872601728,91639694⟩ E)) ⟨172872601856,91360512⟩ (N (N E ⟨172872601984,91082393⟩ E) ⟨172872602112,90805331⟩ E)) ⟨172872602240,90529323⟩ (N (N (N E ⟨172872602368,90254363⟩ E) ⟨172872602496,89980446⟩ E) ⟨172872602624,89707568⟩ (N (N E ⟨172872602752,89435724⟩ E) ⟨172872602880,89164910⟩ E))) ⟨172872603008,88895120⟩ (N (N (N (N E ⟨172872603136,88626350⟩ E) ⟨172872603264,88358596⟩ (N E ⟨172872603392,88091852⟩ E)) ⟨172872603520,87826114⟩ (N (N E ⟨172872603648,87561378⟩ E) ⟨172872603776,87297640⟩ E)) ⟨172872603904,87034894⟩ (N (N (N E ⟨172872604032,86773136⟩ E) ⟨172872604160,86512361⟩ E) ⟨172872604416,85993746⟩ (N (N E ⟨172872604800,85223091⟩ E) ⟨172872605056,84714115⟩ E))))) ⟨172872605696,83458205⟩ (N (N (N (N (N (N E ⟨173006817280,140371923⟩ E) ⟨173006817408,139938656⟩ (N E ⟨173006817536,139507060⟩ E)) ⟨173006817664,139077128⟩ (N (N E ⟨173006817792,138648851⟩ E) ⟨173006817920,138222222⟩ E)) ⟨173006818048,137797234⟩ (N (N (N E ⟨173006818176,137373878⟩ E) ⟨173006818304,136952147⟩ (N E ⟨173006818432,136532034⟩ E)) ⟨173006818560,136113532⟩ (N (N E ⟨173006818688,135696632⟩ E) ⟨173006818816,135281328⟩ E))) ⟨173006818944,134867612⟩ (N (N (N (N E ⟨173006819072,134455477⟩ E) ⟨173006819200,134044916⟩ (N E ⟨173006819328,133635921⟩ E)) ⟨173006819456,133228486⟩ (N (N E ⟨173006819584,132822602⟩ E) ⟨173006819712,132418264⟩ E)) ⟨173006819840,132015464⟩ (N (N (N E ⟨173006819968,131614195⟩ E) ⟨173006820224,130816221⟩ E) ⟨173006820352,130419504⟩ (N (N E ⟨173006820480,130024289⟩ E) ⟨173006820608,129630571⟩ E)))) ⟨173006820736,129238342⟩ (N (N (N (N (N E ⟨173006820864,128847597⟩ E) ⟨173006820992,128458327⟩ (N E ⟨173006821248,127684191⟩ E)) ⟨173006821376,127299310⟩ (N (N E ⟨173006821504,126915879⟩ E) ⟨173006821760,126153339⟩ E)) ⟨173006821888,125774218⟩ (N (N (N E ⟨173006822144,125020240⟩ E) ⟨173006822656,123529163⟩ E) ⟨173006822784,123159874⟩ (N (N E ⟨173006822912,122791964⟩ E) ⟨173006823040,122425427⟩ E))) ⟨173006823424,121333996⟩ (N (N (N (N E ⟨173141035264,191216440⟩ E) ⟨173141035392,190627150⟩ (N E ⟨173141035520,190040129⟩ E)) ⟨173141035648,189455366⟩ (N (N E ⟨173141035776,188872852⟩ E) ⟨173141035904,188292576⟩ E)) ⟨173141036032,187714528⟩ (N (N (N E ⟨173141036160,187138697⟩ E) ⟨173141036288,186565073⟩ E) ⟨173141036416,185993647⟩ (N (N E ⟨173141036544,185424407⟩ E) ⟨173141036672,184857344⟩ E)))))))

noncomputable def tab13 : CTN :=
  (N (N (N (N (N (N (N (N E ⟨173141036928,183729709⟩ E) ⟨173141037056,183169117⟩ (N E ⟨173141037184,182610663⟩ E)) ⟨173141037312,182054335⟩ (N (N E ⟨173141037440,181500126⟩ E) ⟨173141037568,180948025⟩ E)) ⟨173141037696,180398022⟩ (N (N (N E ⟨173141037824,179850108⟩ E) ⟨173141037952,179304274⟩ (N E ⟨173141038080,178760509⟩ E)) ⟨173141038208,178218805⟩ (N (N E ⟨173141038336,177679153⟩ E) ⟨173141038464,177141542⟩ E))) ⟨173141038592,176605963⟩ (N (N (N (N E ⟨173141038720,176072408⟩ E) ⟨173141038848,175540867⟩ (N E ⟨173141038976,175011331⟩ E)) ⟨173141039104,174483792⟩ (N (N E ⟨173141039232,173958239⟩ E) ⟨173141039488,172913058⟩ E)) ⟨173141039616,172393412⟩ (N (N (N E ⟨173141039744,171875718⟩ E) ⟨173141039872,171359966⟩ E) ⟨173141040000,170846148⟩ (N (N E ⟨173141040128,170334255⟩ E) ⟨173141040256,169824279⟩ E)))) ⟨173141040384,169316210⟩ (N (N (N (N (N E ⟨173141040640,168305763⟩ E) ⟨173141040768,167803366⟩ (N E ⟨173141040896,167302844⟩ E)) ⟨173141041024,166804187⟩ (N (N E ⟨173141041152,166307388⟩ E) ⟨173275253120,250318805⟩ E)) ⟨173275253248,249547968⟩ (N (N (N E ⟨173275253376,248780098⟩ E) ⟨173275253504,248015179⟩ (N E ⟨173275253632,247253200⟩ E)) ⟨173275253760,246494146⟩ (N (N E ⟨173275253888,245738003⟩ E) ⟨173275254016,244984759⟩ E))) ⟨173275254144,244234399⟩ (N (N (N (N E ⟨173275254272,243486912⟩ E) ⟨173275254400,242742283⟩ (N E ⟨173275254528,242000499⟩ E)) ⟨173275254656,241261548⟩ (N (N E ⟨173275254784,240525416⟩ E) ⟨173275254912,239792091⟩ E)) ⟨173275255040,239061560⟩ (N (N (N E ⟨173275255168,238333809⟩ E) ⟨173275255296,237608827⟩ E) ⟨173275255424,236886600⟩ (N (N E ⟨173275255552,236167116⟩ E) ⟨173275255680,235450363⟩ E))))) ⟨173275255808,234736328⟩ (N (N (N (N (N (N E ⟨173275255936,234024998⟩ E) ⟨173275256064,233316362⟩ (N E ⟨173275256192,232610408⟩ E)) ⟨173275256320,231907122⟩ (N (N E ⟨173275256448,231206493⟩ E) ⟨173275256576,230508509⟩ E)) ⟨173275256704,229813158⟩ (N (N (N E ⟨173275256832,229120428⟩ E) ⟨173275256960,228430308⟩ (N E ⟨173275257088,227742784⟩ E)) ⟨173275257216,227057846⟩ (N (N E ⟨173275257344,226375482⟩ E) ⟨173275257600,225018430⟩ E))) ⟨173275257728,224343719⟩ (N (N (N (N E ⟨173275257856,223671535⟩ E) ⟨173275257984,223001869⟩ (N E ⟨173275258240,221670039⟩ E)) ⟨173275258496,220348142⟩ (N (N E ⟨173275258880,218383722⟩ E) ⟨173409471104,316197559⟩ E)) ⟨173409471232,315225354⟩ (N (N (N E ⟨173409471360,314256884⟩ E) ⟨173409471488,313292131⟩ E) ⟨173409471616,312331080⟩ (N (N E ⟨173409471744,311373712⟩ E) ⟨173409471872,310420012⟩ E)))) ⟨173409472000,309469961⟩ (N (N (N (N (N E ⟨173409472128,308523543⟩ E) ⟨173409472256,307580742⟩ (N E ⟨173409472384,306641541⟩ E)) ⟨173409472512,305705923⟩ (N (N E ⟨173409472640,304773873⟩ E) ⟨173409472768,303845373⟩ E)) ⟨173409472896,302920407⟩ (N (N (N E ⟨173409473152,301081016⟩ E) ⟨173409473280,300166558⟩ E) ⟨173409473408,299255570⟩ (N (N E ⟨173409473536,298348037⟩ E) ⟨173409473664,297443943⟩ E))) ⟨173409473792,296543272⟩ (N (N (N (N E ⟨173409473920,295646009⟩ E) ⟨173409474048,294752139⟩ (N E ⟨173409474176,293861645⟩ E)) ⟨173409474304,292974513⟩ (N (N E ⟨173409474432,292090727⟩ E) ⟨173409474560,291210273⟩ E)) ⟨173409474688,290333135⟩ (N (N (N E ⟨173409474816,289459298⟩ E) ⟨173409474944,288588747⟩ E) ⟨173409475072,287721468⟩ (N (N E ⟨173409475200,286857445⟩ E) ⟨173409475328,285996665⟩ E)))))) ⟨173409475456,285139112⟩ (N (N (N (N (N (N (N E ⟨173409475712,283433631⟩ E) ⟨173409475840,282585674⟩ (N E ⟨173409475968,281740887⟩ E)) ⟨173409476224,280060765⟩ (N (N E ⟨173409476352,279225402⟩ E) ⟨173409476480,278393153⟩ E)) ⟨173409476608,277564003⟩ (N (N (N E ⟨173543688832,391703933⟩ E) ⟨173543688960,390499570⟩ (N E ⟨173543689088,389299835⟩ E)) ⟨173543689216,388104705⟩ (N (N E ⟨173543689344,386914159⟩ E) ⟨173543689472,385728177⟩ E))) ⟨173543689600,384546737⟩ (N (N (N (N E ⟨173543689728,383369819⟩ E) ⟨173543689856,382197402⟩ (N E ⟨173543689984,381029465⟩ E)) ⟨173543690112,379865987⟩ (N (N E ⟨173543690240,378706948⟩ E) ⟨173543690368,377552329⟩ E)) ⟨173543690496,376402108⟩ (N (N (N E ⟨173543690624,375256266⟩ E) ⟨173543690752,374114782⟩ E) ⟨173543690880,372977637⟩ (N (N E ⟨173543691008,371844811⟩ E) ⟨173543691136,370716284⟩ E)))) ⟨173543691264,369592036⟩ (N (N (N (N (N E ⟨173543691392,368472049⟩ E) ⟨173543691520,367356303⟩ (N E ⟨173543691648,366244778⟩ E)) ⟨173543691904,364034316⟩ (N (N E ⟨173543692032,362935342⟩ E) ⟨173543692160,361840512⟩ E)) ⟨173543692288,360749810⟩ (N (N (N E ⟨173543692416,359663216⟩ E) ⟨173543692672,357502277⟩ E) ⟨173543692928,355357550⟩ (N (N E ⟨173543693056,354291219⟩ E) ⟨173543693312,352170535⟩ E))) ⟨173543693568,350065701⟩ (N (N (N (N E ⟨173543694208,344872027⟩ E) ⟨173543694336,343844881⟩ (N E ⟨173677906944,470923159⟩ E)) ⟨173677907072,469478560⟩ (N (N E ⟨173677907200,468039499⟩ E) ⟨173677907328,466605949⟩ E)) ⟨173677907456,465177886⟩ (N (N (N E ⟨173677907584,463755284⟩ E) ⟨173677907712,462338118⟩ E) ⟨173677907840,460926364⟩ (N (N E ⟨173677907968,459519996⟩ E) ⟨173677908096,458118990⟩ E))))) ⟨173677908224,456723321⟩ (N (N (N (N (N (N E ⟨173677908352,455332965⟩ E) ⟨173677908480,453947898⟩ (N E ⟨173677908608,452568095⟩ E)) ⟨173677908736,451193533⟩ (N (N E ⟨173677908864,449824187⟩ E) ⟨173677908992,448460034⟩ E)) ⟨173677909120,447101051⟩ (N (N (N E ⟨173677909248,445747213⟩ E) ⟨173677909376,444398497⟩ (N E ⟨173677909504,443054881⟩ E)) ⟨173677909632,441716341⟩ (N (N E ⟨173677909760,440382854⟩ E) ⟨173677909888,439054397⟩ E))) ⟨173677910016,437730947⟩ (N (N (N (N E ⟨173677910144,436412482⟩ E) ⟨173677910272,435098980⟩ (N E ⟨173677910400,433790417⟩ E)) ⟨173677910528,432486771⟩ (N (N E ⟨173677910784,429894145⟩ E) ⟨173677911040,427320924⟩ E)) ⟨173677911168,426041536⟩ (N (N (N E ⟨173677911424,423497097⟩ E) ⟨173677911552,422232004⟩ E) ⟨173677911936,418464972⟩ (N (N E ⟨173677912064,417218641⟩ E) ⟨173812124544,563463655⟩ E)))) ⟨173812124672,561733851⟩ (N (N (N (N (N E ⟨173812124800,560010683⟩ E) ⟨173812124928,558294119⟩ (N E ⟨173812125056,556584131⟩ E)) ⟨173812125184,554880686⟩ (N (N E ⟨173812125312,553183756⟩ E) ⟨173812125440,551493311⟩ E)) ⟨173812125568,549809320⟩ (N (N (N E ⟨173812125696,548131754⟩ E) ⟨173812125824,546460584⟩ E) ⟨173812125952,544795781⟩ (N (N E ⟨173812126080,543137315⟩ E) ⟨173812126208,541485158⟩ E))) ⟨173812126336,539839280⟩ (N (N (N (N E ⟨173812126464,538199653⟩ E) ⟨173812126592,536566249⟩ (N E ⟨173812126720,534939039⟩ E)) ⟨173812126848,533317995⟩ (N (N E ⟨173812126976,531703090⟩ E) ⟨173812127104,530094294⟩ E)) ⟨173812127232,528491581⟩ (N (N (N E ⟨173812127488,525304292⟩ E) ⟨173812127616,523719661⟩ E) ⟨173812127744,522141004⟩ (N (N E ⟨173812127872,520568292⟩ E) ⟨173812128000,519001499⟩ E)))))))

noncomputable def tab14 : CTN :=
  (N (N (N (N (N (N (N (N E ⟨173812128256,515885565⟩ E) ⟨173812128384,514336370⟩ (N E ⟨173812128512,512792988⟩ E)) ⟨173812128640,511255393⟩ (N (N E ⟨173812128768,509723558⟩ E) ⟨173812128896,508197459⟩ E)) ⟨173812129024,506677069⟩ (N (N (N E ⟨173812129280,503653314⟩ E) ⟨173812129408,502149898⟩ (N E ⟨173812129536,500652090⟩ E)) ⟨173812129792,497673197⟩ (N (N E ⟨173946342400,660518198⟩ E) ⟨173946342528,658492000⟩ E))) ⟨173946342656,656473569⟩ (N (N (N (N E ⟨173946342784,654462868⟩ E) ⟨173946342912,652459862⟩ (N E ⟨173946343040,650464517⟩ E)) ⟨173946343168,648476796⟩ (N (N E ⟨173946343296,646496665⟩ E) ⟨173946343424,644524089⟩ E)) ⟨173946343552,642559034⟩ (N (N (N E ⟨173946343680,640601464⟩ E) ⟨173946343808,638651347⟩ E) ⟨173946343936,636708648⟩ (N (N E ⟨173946344064,634773332⟩ E) ⟨173946344192,632845367⟩ E)))) ⟨173946344320,630924719⟩ (N (N (N (N (N E ⟨173946344448,629011354⟩ E) ⟨173946344576,627105240⟩ (N E ⟨173946344704,625206343⟩ E)) ⟨173946344832,623314631⟩ (N (N E ⟨173946344960,621430071⟩ E) ⟨173946345088,619552631⟩ E)) ⟨173946345216,617682278⟩ (N (N (N E ⟨173946345344,615818980⟩ E) ⟨173946345472,613962706⟩ (N E ⟨173946345600,612113423⟩ E)) ⟨173946345728,610271100⟩ (N (N E ⟨173946345856,608435706⟩ E) ⟨173946345984,606607209⟩ E))) ⟨173946346112,604785579⟩ (N (N (N (N E ⟨173946346240,602970783⟩ E) ⟨173946346368,601162793⟩ (N E ⟨173946346496,599361576⟩ E)) ⟨173946346624,597567103⟩ (N (N E ⟨173946346752,595779343⟩ E) ⟨173946346880,593998266⟩ E)) ⟨173946347008,592223842⟩ (N (N (N E ⟨173946347264,588694835⟩ E) ⟨173946347392,586940192⟩ E) ⟨173946347520,585192084⟩ (N (N E ⟨174080560256,764899055⟩ E) ⟨174080560512,760218847⟩ E))))) ⟨174080560640,757892172⟩ (N (N (N (N (N (N E ⟨174080560768,755574395⟩ E) ⟨174080560896,753265474⟩ (N E ⟨174080561024,750965370⟩ E)) ⟨174080561152,748674041⟩ (N (N E ⟨174080561280,746391449⟩ E) ⟨174080561408,744117552⟩ E)) ⟨174080561536,741852311⟩ (N (N (N E ⟨174080561664,739595687⟩ E) ⟨174080561792,737347640⟩ (N E ⟨174080561920,735108131⟩ E)) ⟨174080562048,732877121⟩ (N (N E ⟨174080562176,730654572⟩ E) ⟨174080562304,728440445⟩ E))) ⟨174080562432,726234702⟩ (N (N (N (N E ⟨174080562560,724037304⟩ E) ⟨174080562688,721848214⟩ (N E ⟨174080562816,719667394⟩ E)) ⟨174080562944,717494807⟩ (N (N E ⟨174080563072,715330415⟩ E) ⟨174080563200,713174182⟩ E)) ⟨174080563328,711026070⟩ (N (N (N E ⟨174080563456,708886043⟩ E) ⟨174080563584,706754063⟩ E) ⟨174080563712,704630096⟩ (N (N E ⟨174080563840,702514105⟩ E) ⟨174080563968,700406053⟩ E)))) ⟨174080564096,698305905⟩ (N (N (N (N (N E ⟨174080564224,696213626⟩ E) ⟨174080564352,694129181⟩ (N E ⟨174080564480,692052533⟩ E)) ⟨174080564608,689983648⟩ (N (N E ⟨174080564736,687922492⟩ E) ⟨174080564864,685869029⟩ E)) ⟨174080564992,683823225⟩ (N (N (N E ⟨174080565120,681785046⟩ E) ⟨174080565248,679754458⟩ E) ⟨174214778112,876508497⟩ (N (N E ⟨174214778240,873823856⟩ E) ⟨174214778368,871149488⟩ E))) ⟨174214778496,868485349⟩ (N (N (N (N E ⟨174214778624,865831389⟩ E) ⟨174214778752,863187564⟩ (N E ⟨174214778880,860553826⟩ E)) ⟨174214779008,857930129⟩ (N (N E ⟨174214779136,855316427⟩ E) ⟨174214779264,852712675⟩ E)) ⟨174214779392,850118827⟩ (N (N (N E ⟨174214779520,847534838⟩ E) ⟨174214779648,844960663⟩ E) ⟨174214779776,842396257⟩ (N (N E ⟨174214779904,839841577⟩ E) ⟨174214780032,837296576⟩ E)))))) ⟨174214780160,834761213⟩ (N (N (N (N (N (N (N E ⟨174214780288,832235442⟩ E) ⟨174214780416,829719221⟩ (N E ⟨174214780544,827212505⟩ E)) ⟨174214780672,824715253⟩ (N (N E ⟨174214780800,822227420⟩ E) ⟨174214780928,819748965⟩ E)) ⟨174214781056,817279845⟩ (N (N (N E ⟨174214781184,814820018⟩ E) ⟨174214781312,812369442⟩ (N E ⟨174214781440,809928075⟩ E)) ⟨174214781568,807495875⟩ (N (N E ⟨174214781696,805072802⟩ E) ⟨174214781824,802658814⟩ E))) ⟨174214782080,797857931⟩ (N (N (N (N E ⟨174214782208,795470955⟩ E) ⟨174214782464,790723732⟩ (N E ⟨174214782592,788363405⟩ E)) ⟨174214782720,786011882⟩ (N (N E ⟨174214782848,783669123⟩ E) ⟨174214782976,781335090⟩ E)) ⟨174348995968,995244781⟩ (N (N (N E ⟨174348996096,992198801⟩ E) ⟨174348996224,989164469⟩ E) ⟨174348996352,986141733⟩ (N (N E ⟨174348996480,983130539⟩ E) ⟨174348996608,980130833⟩ E)))) ⟨174348996736,977142564⟩ (N (N (N (N (N E ⟨174348996864,974165679⟩ E) ⟨174348996992,971200127⟩ (N E ⟨174348997120,968245854⟩ E)) ⟨174348997248,965302811⟩ (N (N E ⟨174348997376,962370945⟩ E) ⟨174348997504,959450206⟩ E)) ⟨174348997632,956540544⟩ (N (N (N E ⟨174348997760,953641907⟩ E) ⟨174348997888,950754245⟩ E) ⟨174348998016,947877510⟩ (N (N E ⟨174348998144,945011651⟩ E) ⟨174348998272,942156618⟩ E))) ⟨174348998400,939312363⟩ (N (N (N (N E ⟨174348998528,936478838⟩ E) ⟨174348998656,933655993⟩ (N E ⟨174348998784,930843780⟩ E)) ⟨174348998912,928042151⟩ (N (N E ⟨174348999040,925251058⟩ E) ⟨174348999168,922470454⟩ E)) ⟨174348999296,919700292⟩ (N (N (N E ⟨174348999424,916940525⟩ E) ⟨174348999552,914191105⟩ E) ⟨174348999680,911451986⟩ (N (N E ⟨174348999808,908723122⟩ E) ⟨174348999936,906004467⟩ E))))) ⟨174349000064,903295975⟩ (N (N (N (N (N (N E ⟨174349000320,897909298⟩ E) ⟨174349000448,895231022⟩ (N E ⟨174349000704,889904373⟩ E)) ⟨174483213824,1121002223⟩ (N (N E ⟨174483213952,1117573986⟩ E) ⟨174483214080,1114158849⟩ E)) ⟨174483214208,1110756753⟩ (N (N (N E ⟨174483214336,1107367638⟩ E) ⟨174483214464,1103991443⟩ (N E ⟨174483214592,1100628111⟩ E)) ⟨174483214720,1097277581⟩ (N (N E ⟨174483214848,1093939797⟩ E) ⟨174483214976,1090614699⟩ E))) ⟨174483215104,1087302230⟩ (N (N (N (N E ⟨174483215232,1084002332⟩ E) ⟨174483215360,1080714948⟩ (N E ⟨174483215488,1077440021⟩ E)) ⟨174483215616,1074177495⟩ (N (N E ⟨174483215744,1070927312⟩ E) ⟨174483215872,1067689418⟩ E)) ⟨174483216000,1064463756⟩ (N (N (N E ⟨174483216128,1061250272⟩ E) ⟨174483216256,1058048909⟩ E) ⟨174483216384,1054859613⟩ (N (N E ⟨174483216512,1051682329⟩ E) ⟨174483216640,1048517003⟩ E)))) ⟨174483216768,1045363582⟩ (N (N (N (N (N E ⟨174483216896,1042222011⟩ E) ⟨174483217024,1039092237⟩ (N E ⟨174483217152,1035974207⟩ E)) ⟨174483217280,1032867868⟩ (N (N E ⟨174483217408,1029773167⟩ E) ⟨174483217536,1026690053⟩ E)) ⟨174483217664,1023618472⟩ (N (N (N E ⟨174483217792,1020558374⟩ E) ⟨174483217920,1017509707⟩ E) ⟨174483218048,1014472420⟩ (N (N E ⟨174483218304,1008431780⟩ E) ⟨174483218432,1005428326⟩ E))) ⟨174617431680,1253671273⟩ (N (N (N (N E ⟨174617431808,1249840244⟩ E) ⟨174617431936,1246023843⟩ (N E ⟨174617432064,1242222003⟩ E)) ⟨174617432192,1238434658⟩ (N (N E ⟨174617432320,1234661742⟩ E) ⟨174617432448,1230903188⟩ E)) ⟨174617432576,1227158930⟩ (N (N (N E ⟨174617432704,1223428905⟩ E) ⟨174617432832,1219713046⟩ E) ⟨174617432960,1216011289⟩ (N (N E ⟨174617433088,1212323570⟩ E) ⟨174617433216,1208649825⟩ E)))))))

noncomputable def tab15 : CTN :=
  (N (N (N (N (N (N (N (N E ⟨174617433472,1201344004⟩ E) ⟨174617433600,1197711801⟩ (N E ⟨174617433728,1194093321⟩ E)) ⟨174617433856,1190488501⟩ (N (N E ⟨174617433984,1186897278⟩ E) ⟨174617434112,1183319592⟩ E)) ⟨174617434368,1176204585⟩ (N (N (N E ⟨174617434496,1172667142⟩ E) ⟨174617434624,1169142993⟩ (N E ⟨174617434752,1165632078⟩ E)) ⟨174617434880,1162134337⟩ (N (N E ⟨174617435008,1158649710⟩ E) ⟨174617435264,1151719565⟩ E))) ⟨174617435392,1148273930⟩ (N (N (N (N E ⟨174617435520,1144841176⟩ E) ⟨174617435776,1138014078⟩ (N E ⟨174617436032,1131237814⟩ E)) ⟨174617436160,1127868602⟩ (N (N E ⟨174751649536,1393138594⟩ E) ⟨174751649792,1384646897⟩ E)) ⟨174751649920,1380425320⟩ (N (N (N E ⟨174751650048,1376219826⟩ E) ⟨174751650176,1372030341⟩ E) ⟨174751650304,1367856792⟩ (N (N E ⟨174751650432,1363699107⟩ E) ⟨174751650560,1359557212⟩ E)))) ⟨174751650688,1355431036⟩ (N (N (N (N (N E ⟨174751650816,1351320508⟩ E) ⟨174751650944,1347225556⟩ (N E ⟨174751651072,1343146110⟩ E)) ⟨174751651200,1339082098⟩ (N (N E ⟨174751651328,1335033452⟩ E) ⟨174751651456,1331000101⟩ E)) ⟨174751651712,1322979007⟩ (N (N (N E ⟨174751651840,1318991128⟩ E) ⟨174751651968,1315018268⟩ (N E ⟨174751652096,1311060361⟩ E)) ⟨174751652352,1303189135⟩ (N (N E ⟨174751652608,1295376912⟩ E) ⟨174751652736,1291492761⟩ E))) ⟨174751652992,1283768053⟩ (N (N (N (N E ⟨174751653120,1279927364⟩ E) ⟨174751653248,1276101033⟩ (N E ⟨174751653376,1272288995⟩ E)) ⟨174751653888,1257182497⟩ (N (N E ⟨174885867776,1525250863⟩ E) ⟨174885867904,1520607698⟩ E)) ⟨174885868032,1515982195⟩ (N (N (N E ⟨174885868160,1511374273⟩ E) ⟨174885868288,1506783852⟩ E) ⟨174885868416,1502210852⟩ (N (N E ⟨174885868544,1497655194⟩ E) ⟨174885868672,1493116799⟩ E))))) ⟨174885868800,1488595589⟩ (N (N (N (N (N (N E ⟨174885868928,1484091485⟩ E) ⟨174885869184,1475134287⟩ (N E ⟨174885869312,1470681038⟩ E)) ⟨174885869440,1466244588⟩ (N (N E ⟨174885869568,1461824860⟩ E) ⟨174885869696,1457421779⟩ E)) ⟨174885869824,1453035270⟩ (N (N (N E ⟨174885869952,1448665257⟩ E) ⟨174885870080,1444311667⟩ (N E ⟨174885870208,1439974425⟩ E)) ⟨174885870336,1435653458⟩ (N (N E ⟨174885870464,1431348692⟩ E) ⟨174885870592,1427060055⟩ E))) ⟨174885870720,1422787474⟩ (N (N (N (N E ⟨174885871104,1410065347⟩ E) ⟨174885871232,1405856272⟩ (N E ⟨174885871360,1401662897⟩ E)) ⟨174885871488,1397485151⟩ (N (N E ⟨174885871616,1393322965⟩ E) ⟨175020085376,1686837598⟩ E)) ⟨175020085504,1681698613⟩ (N (N (N E ⟨175020085632,1676579190⟩ E) ⟨175020085760,1671479241⟩ E) ⟨175020086016,1661337407⟩ (N (N E ⟨175020086144,1656295346⟩ E) ⟨175020086400,1646268500⟩ E)))) ⟨175020086528,1641283541⟩ (N (N (N (N (N E ⟨175020086656,1636317443⟩ E) ⟨175020086784,1631370121⟩ (N E ⟨175020087040,1621531463⟩ E)) ⟨175020087168,1616639958⟩ (N (N E ⟨175020087296,1611766891⟩ E) ⟨175020087552,1602075736⟩ E)) ⟨175020087680,1597257483⟩ (N (N (N E ⟨175020087808,1592457337⟩ E) ⟨175020087936,1587675217⟩ E) ⟨175020088064,1582911040⟩ (N (N E ⟨175020088576,1564032164⟩ E) ⟨175020088704,1559356504⟩ E))) ⟨175020088960,1550057503⟩ (N (N (N (N E ⟨175020089088,1545434006⟩ E) ⟨175020089344,1536238631⟩ (N E ⟨175154303616,1828711918⟩ E)) ⟨175154303744,1823157663⟩ (N (N E ⟨175154303872,1817624488⟩ E) ⟨175154304000,1812112295⟩ E)) ⟨175154304128,1806620990⟩ (N (N (N E ⟨175154304256,1801150478⟩ E) ⟨175154304384,1795700664⟩ E) ⟨175154304512,1790271455⟩ (N (N E ⟨175154304640,1784862757⟩ E) ⟨175154304768,1779474476⟩ E)))))) ⟨175154304896,1774106521⟩ (N (N (N (N (N (N (N E ⟨175154305024,1768758799⟩ E) ⟨175154305280,1758123692⟩ (N E ⟨175154305536,1747568426⟩ E)) ⟨175154305664,1742320510⟩ (N (N E ⟨175154305792,1737092285⟩ E) ⟨175154305920,1731883663⟩ E)) ⟨175154306048,1726694557⟩ (N (N (N E ⟨175154306176,1721524877⟩ E) ⟨175154306304,1716374538⟩ (N E ⟨175154306688,1701038695⟩ E)) ⟨175154306944,1690909921⟩ (N (N E ⟨175154307072,1685873815⟩ E) ⟨175288521472,1992179768⟩ E))) ⟨175288521728,1980110401⟩ (N (N (N (N E ⟨175288521856,1974110006⟩ E) ⟨175288521984,1968132331⟩ (N E ⟨175288522112,1962177274⟩ E)) ⟨175288522240,1956244731⟩ (N (N E ⟨175288522368,1950334600⟩ E) ⟨175288522496,1944446781⟩ E)) ⟨175288522624,1938581171⟩ (N (N (N E ⟨175288522752,1932737670⟩ E) ⟨175288522880,1926916179⟩ E) ⟨175288523136,1915338828⟩ (N (N E ⟨175288523264,1909582771⟩ E) ⟨175288523648,1892443898⟩ E)))) ⟨175288523776,1886773717⟩ (N (N (N (N (N E ⟨175288524416,1858739341⟩ E) ⟨175288524544,1853195110⟩ (N E ⟨175288524800,1842168548⟩ E)) ⟨175422739456,2155197683⟩ (N (N E ⟨175422739584,2148666715⟩ E) ⟨175422739712,2142160477⟩ E)) ⟨175422739840,2135678855⟩ (N (N (N E ⟨175422740096,2122789017⟩ E) ⟨175422740224,2116380579⟩ E) ⟨175422740352,2109996314⟩ (N (N E ⟨175422740480,2103636114⟩ E) ⟨175422740608,2097299870⟩ E))) ⟨175422740736,2090987472⟩ (N (N (N (N E ⟨175422740864,2084698814⟩ E) ⟨175422740992,2078433789⟩ (N E ⟨175422741120,2072192290⟩ E)) ⟨175422741248,2065974211⟩ (N (N E ⟨175422741632,2047459442⟩ E) ⟨175422742144,2023094631⟩ E)) ⟨175422742400,2011048186⟩ (N (N (N E ⟨175422742528,2005058599⟩ E) ⟨175556957440,2323161767⟩ E) ⟨175556957568,2316132482⟩ (N (N E ⟨175556957696,2309129774⟩ E) ⟨175556957952,2295203603⟩ E))))) ⟨175556958080,2288279902⟩ (N (N (N (N (N (N E ⟨175556958592,2260844896⟩ E) ⟨175556958976,2240538162⟩ (N E ⟨175556959104,2233819972⟩ E)) ⟨175556959360,2220458992⟩ (N (N E ⟨175556959488,2213815976⟩ E) ⟨175556959744,2200604333⟩ E)) ⟨175556959872,2194035483⟩ (N (N (N E ⟨175556960128,2180971177⟩ E) ⟨175556960256,2174475502⟩ (N E ⟨175691175424,2495891661⟩ E)) ⟨175691175552,2488351170⟩ (N (N E ⟨175691175936,2465899976⟩ E) ⟨175691176064,2458472577⟩ E))) ⟨175691176192,2451073131⟩ (N (N (N (N E ⟨175691176320,2443701514⟩ E) ⟨175691176704,2421752375⟩ (N E ⟨175691176832,2414490820⟩ E)) ⟨175691176960,2407256471⟩ (N (N E ⟨175691177216,2392868906⟩ E) ⟨175691177728,2364414917⟩ E)) ⟨175691177984,2350346583⟩ (N (N (N E ⟨175825393664,2657108522⟩ E) ⟨175825393920,2641131988⟩ E) ⟨175825394560,2601713045⟩ (N (N E ⟨175825394816,2586151614⟩ E) ⟨175825394944,2578414544⟩ E)))) ⟨175825395328,2555376355⟩ (N (N (N (N (N E ⟨175825395712,2532594994⟩ E) ⟨175959611136,2872218956⟩ (N E ⟨175959611264,2863554633⟩ E)) ⟨175959612544,2778683512⟩ (N (N E ⟨175959612928,2753837382⟩ E) ⟨175959613312,2729268440⟩ E)) ⟨175959613440,2721139749⟩ (N (N (N E ⟨176093828992,3068503488⟩ E) ⟨176093829888,3004483481⟩ E) ⟨176093830400,2968649963⟩ (N (N E ⟨176093831168,2915895760⟩ E) ⟨176228048768,3126084422⟩ E))) ⟨176228048896,3116773877⟩ (N (N (N (N E ⟨176362266496,3333609555⟩ E) ⟨176362266624,3323680930⟩ (N E ⟨176496484352,3536519776⟩ E)) ⟨176630702080,3755189350⟩ (N (N E ⟨176764919808,3979584708⟩ E) ⟨176899137408,4222172155⟩ E)) ⟨176899137536,4209597088⟩ (N (N (N E ⟨177033355264,4445113958⟩ E) ⟨177167572992,4686019082⟩ E) ⟨177301790720,4932192574⟩ (N (N E ⟨177436008448,5183510966⟩ E) ⟨177570226176,5439847270⟩ E)))))))

noncomputable def tab16 : CTN :=
  (N (N (N (N (N (N (N (N E ⟨177838661632,5967048477⟩ E) ⟨177972879360,6237642433⟩ (N E ⟨178107097088,6512712553⟩ E)) ⟨178375532544,7075704133⟩ (N (N E ⟨178509750272,7363329404⟩ E) ⟨178912403456,8248884841⟩ E)) ⟨179180838912,8856567762⟩ (N (N (N E ⟨179851927552,10426706991⟩ E) ⟨180120363008,11071513823⟩ (N E ⟨180254580736,11396796783⟩ E)) ⟨180388798592,11688866092⟩ (N (N E ⟨180388798720,11654104527⟩ E) ⟨180388798848,11619472136⟩ E))) ⟨180388798976,11584968342⟩ (N (N (N (N E ⟨180388799104,11550592573⟩ E) ⟨180388799232,11516344258⟩ (N E ⟨180388799360,11482222831⟩ E)) ⟨180388799488,11448227727⟩ (N (N E ⟨180388799616,11414358387⟩ E) ⟨180388799744,11380614252⟩ E)) ⟨180388799872,11346994766⟩ (N (N (N E ⟨180388800000,11313499377⟩ E) ⟨180388800128,11280127536⟩ E) ⟨180388800256,11246878697⟩ (N (N E ⟨180388800384,11213752314⟩ E) ⟨180388800512,11180747848⟩ E)))) ⟨180388800640,11147864760⟩ (N (N (N (N (N E ⟨180388800768,11115102515⟩ E) ⟨180388800896,11082460580⟩ (N E ⟨180388801024,11049938424⟩ E)) ⟨180388801152,11017535522⟩ (N (N E ⟨180388801280,10985251347⟩ E) ⟨180388801408,10953085379⟩ E)) ⟨180388801536,10921037098⟩ (N (N (N E ⟨180388801664,10889105988⟩ E) ⟨180388801792,10857291534⟩ (N E ⟨180388801920,10825593226⟩ E)) ⟨180388802048,10794010555⟩ (N (N E ⟨180388802176,10762543015⟩ E) ⟨180388802304,10731190103⟩ E))) ⟨180388802432,10699951317⟩ (N (N (N (N E ⟨180388802560,10668826159⟩ E) ⟨180388802688,10637814134⟩ (N E ⟨180388802816,10606914747⟩ E)) ⟨180388802944,10576127510⟩ (N (N E ⟨180388803072,10545451932⟩ E) ⟨180388803200,10514887529⟩ E)) ⟨180388803328,10484433817⟩ (N (N (N E ⟨180388803456,10454090316⟩ E) ⟨180388803584,10423856546⟩ E) ⟨180388803712,10393732032⟩ (N (N E ⟨180388803840,10363716300⟩ E) ⟨180388803968,10333808879⟩ E))))) ⟨180388804096,10304009300⟩ (N (N (N (N (N (N E ⟨180388804224,10274317097⟩ E) ⟨180388804352,10244731805⟩ (N E ⟨180388804480,10215252963⟩ E)) ⟨180388804608,10185880112⟩ (N (N E ⟨180388804736,10156612794⟩ E) ⟨180388804864,10127450554⟩ E)) ⟨180388804992,10098392940⟩ (N (N (N E ⟨180388805120,10069439501⟩ E) ⟨180388805248,10040589791⟩ (N E ⟨180388805376,10011843362⟩ E)) ⟨180388805504,9983199771⟩ (N (N E ⟨180388805632,9954658577⟩ E) ⟨180388805760,9926219341⟩ E))) ⟨180388805888,9897881626⟩ (N (N (N (N E ⟨180388806144,9841509023⟩ E) ⟨180388806272,9813473271⟩ (N E ⟨180388806400,9785537314⟩ E)) ⟨180388806656,9729963084⟩ (N (N E ⟨181865201664,12762482876⟩ E) ⟨182267854848,13588085150⟩ E)) ⟨182938943488,14942444246⟩ (N (N (N E ⟨183610032128,16252480520⟩ E) ⟨184683773952,18207818693⟩ E) ⟨188441870336,22748370843⟩ (N (N E ⟨188978741504,22868327409⟩ E) ⟨188978741632,22786289547⟩ E)))) ⟨188978741760,22697744874⟩ (N (N (N (N (N E ⟨188978741888,22602764358⟩ E) ⟨188978742016,22501422485⟩ (N E ⟨188978742144,22393797195⟩ E)) ⟨188978742272,22279969817⟩ (N (N E ⟨188978742400,22160024998⟩ E) ⟨188978742656,21902137809⟩ E)) ⟨188978742784,21764380703⟩ (N (N (N E ⟨188978743040,21471725482⟩ E) ⟨188978743168,21317030601⟩ E) ⟨188978743296,21156897754⟩ (N (N E ⟨188978743424,20991435527⟩ E) ⟨188978743552,20820755150⟩ E))) ⟨188978743680,20644970417⟩ (N (N (N (N E ⟨188978743808,20464197604⟩ E) ⟨188978743936,20278555381⟩ (N E ⟨188978744192,19893148878⟩ E)) ⟨188978744320,19693633166⟩ (N (N E ⟨188978744576,19281613785⟩ E) ⟨188978744832,18853148956⟩ E)) ⟨188978744960,18633083148⟩ (N (N (N E ⟨188978745088,18409309687⟩ E) ⟨188978745216,18181966454⟩ E) ⟨188978745344,17951192761⟩ (N (N E ⟨188978745472,17717129255⟩ E) ⟨188978745600,17479917837⟩ E)))))) ⟨188978745728,17239701561⟩ (N (N (N (N (N (N (N E ⟨188978745984,16750831874⟩ E) ⟨188978746112,16502469524⟩ (N E ⟨188978746240,16251684254⟩ E)) ⟨188978746368,15998623519⟩ (N (N E ⟨188978746496,15743435378⟩ E) ⟨188978746880,14966594275⟩ E)) ⟨188978747008,14704386007⟩ (N (N (N E ⟨188978747648,13375620595⟩ E) ⟨188978747904,12838633661⟩ (N E ⟨188978748160,12300299849⟩ E)) ⟨188978748288,12030996690⟩ (N (N E ⟨188978748544,11492849466⟩ E) ⟨188978748672,11224295565⟩ E))) ⟨188978748800,10956280011⟩ (N (N (N (N E ⟨188978749184,10156883789⟩ E) ⟨188978749440,9629227507⟩ (N E ⟨189381402624,9705467214⟩ E)) ⟨189784054272,13031008444⟩ (N (N E ⟨189918273536,9807504934⟩ E) ⟨190857797632,9986803866⟩ E)) ⟨192199974912,10243462948⟩ (N (N (N E ⟨192736845824,10345928746⟩ E) ⟨193944805376,10575211708⟩ E) ⟨194615894016,10701435097⟩ (N (N E ⟨195152764928,10801615209⟩ E) ⟨195689635840,10900955939⟩ E)))) ⟨195958071296,10950274600⟩ (N (N (N (N (N E ⟨196763377664,11096649244⟩ E) ⟨197568684288,10648370487⟩ (N E ⟨197568684416,10354926600⟩ E)) ⟨197568685056,8918944300⟩ (N (N E ⟨197568685440,8087331212⟩ E) ⟨197568685568,7815921159⟩ E)) ⟨197568685824,7282552018⟩ (N (N (N E ⟨197568686592,5766613749⟩ E) ⟨197568687104,4834930976⟩ E) ⟨197568687232,4612801060⟩ (N (N E ⟨197568687744,3770125012⟩ E) ⟨197568688000,3377422809⟩ E))) ⟨197568688128,3188490500⟩ (N (N (N (N E ⟨197568688384,2825797799⟩ E) ⟨197568688640,2483741266⟩ (N E ⟨197568689152,1863247807⟩ E)) ⟨197568689280,1721645940⟩ (N (N E ⟨197568689664,1329888956⟩ E) ⟨197568690048,988290955⟩ E)) ⟨197568690816,457388911⟩ (N (N (N E ⟨197568690944,388714969⟩ E) ⟨197568691072,325691933⟩ E) ⟨197568691328,216552079⟩ (N (N E ⟨197568691456,170403893⟩ E) ⟨197568691584,129843933⟩ E))))) ⟨197568691712,94848521⟩ (N (N (N (N (N (N E ⟨197568692096,22965865⟩ E) ⟨197568692224,9929527⟩ (N E ⟨197837123072,3994108024⟩ E)) ⟨197837124608,1874752748⟩ (N (N E ⟨197837124992,1464558888⟩ E) ⟨198105561728,466088833⟩ E)) ⟨198373998592,11386492⟩ (N (N (N E ⟨198508214784,548325482⟩ E) ⟨198910867584,819212070⟩ (N E ⟨198910869120,71967346⟩ E)) ⟨199045083392,2909774475⟩ (N (N E ⟨199179303168,730791735⟩ E) ⟨199179304704,47521256⟩ E))) ⟨199313518720,3107956139⟩ (N (N (N (N E ⟨199313519616,1935399304⟩ E) ⟨199447738880,563971012⟩ (N E ⟨199581955968,1040704766⟩ E)) ⟨199581956736,488549031⟩ (N (N E ⟨199716173184,1528239640⟩ E) ⟨199850392704,238350679⟩ E)) ⟨199850393600,13953383⟩ (N (N (N E ⟨200253043712,1971394340⟩ E) ⟨200387263232,426828851⟩ E) ⟨200387263616,242915733⟩ (N (N E ⟨200387264512,14823774⟩ E) ⟨200521480832,501551222⟩ E)))) ⟨200655698816,362558751⟩ (N (N (N (N (N E ⟨200789916800,246175590⟩ E) ⟨200924134528,247229637⟩ (N E ⟨200924135296,31647849⟩ E)) ⟨201192569344,590030147⟩ (N (N E ⟨201192570112,198682581⟩ E) ⟨201192570880,16038487⟩ E)) ⟨201326786688,867395147⟩ (N (N (N E ⟨201326787328,437608215⟩ E) ⟨201326788224,82100334⟩ E) ⟨201326788608,16228754⟩ (N (N E ⟨201595222912,371857624⟩ E) ⟨201595223808,55199094⟩ E))) ⟨201863658624,254127487⟩ (N (N (N (N E ⟨201863659392,33583596⟩ E) ⟨201997875968,444615456⟩ (N E ⟨201997876480,203625213⟩ E)) ⟨201997877248,17120960⟩ (N (N E ⟨202266312704,17448255⟩ E) ⟨202400530176,57230749⟩ E)) ⟨202400530432,17605157⟩ (N (N (N E ⟨202668965376,120881981⟩ E) ⟨202668965760,35002095⟩ E) ⟨202668965888,17905000⟩ (N (N E ⟨203071618688,87551757⟩ E) ⟨203071618944,35619903⟩ E)))))))

noncomputable def tab17 : CTN :=
  (N (N (N (N (N (N (N (N E ⟨203876925440,19007200⟩ E) ⟨204279578624,19278617⟩ (N E ⟨204413796352,19357895⟩ E)) ⟨206158626944,7536840⟩ (N (N E ⟨206158627072,1073573⟩ E) ⟨206561281408,440967⟩ E)) ⟨206561281664,438691⟩ (N (N (N E ⟨206561281920,436429⟩ E) ⟨206561282048,435304⟩ (N E ⟨206561282176,434182⟩ E)) ⟨206561282304,433064⟩ (N (N E ⟨206561282432,431950⟩ E) ⟨206561282560,430839⟩ E))) ⟨206561282688,429732⟩ (N (N (N (N E ⟨206561282816,428628⟩ E) ⟨206561282944,427528⟩ (N E ⟨206561283072,426431⟩ E)) ⟨206561283200,425338⟩ (N (N E ⟨206561283328,424248⟩ E) ⟨206561283456,423162⟩ E)) ⟨206561283584,422079⟩ (N (N (N E ⟨206561283712,421000⟩ E) ⟨206561283840,419924⟩ E) ⟨206561283968,418852⟩ (N (N E ⟨206561284096,417783⟩ E) ⟨206561284224,416718⟩ E)))) ⟨206561284352,415656⟩ (N (N (N (N (N E ⟨206561284480,414597⟩ E) ⟨206561284736,412489⟩ (N E ⟨206561284864,411441⟩ E)) ⟨206561284992,410395⟩ (N (N E ⟨206561285120,409353⟩ E) ⟨206561285248,408315⟩ E)) ⟨206561285376,407279⟩ (N (N (N E ⟨206561285504,406247⟩ E) ⟨206561285632,405218⟩ (N E ⟨206561285760,404193⟩ E)) ⟨206561285888,403170⟩ (N (N E ⟨206561286016,402151⟩ E) ⟨206561286144,401135⟩ E))) ⟨206561286400,399113⟩ (N (N (N (N E ⟨206561286784,396104⟩ E) ⟨206561286912,395107⟩ (N E ⟨206561287040,394113⟩ E)) ⟨206561287296,392135⟩ (N (N E ⟨206561287680,389191⟩ E) ⟨206561288192,385309⟩ E)) ⟨206695499264,5528367⟩ (N (N (N E ⟨206695499392,5514085⟩ E) ⟨206695499520,5499850⟩ E) ⟨206695499648,5485660⟩ (N (N E ⟨206695499776,5471516⟩ E) ⟨206695499904,5457417⟩ E))))) ⟨206695500032,5443364⟩ (N (N (N (N (N (N E ⟨206695500160,5429356⟩ E) ⟨206695500288,5415393⟩ (N E ⟨206695500416,5401475⟩ E)) ⟨206695500544,5387602⟩ (N (N E ⟨206695500672,5373773⟩ E) ⟨206695500800,5359988⟩ E)) ⟨206695500928,5346248⟩ (N (N (N E ⟨206695501056,5332552⟩ E) ⟨206695501184,5318899⟩ (N E ⟨206695501312,5305291⟩ E)) ⟨206695501440,5291725⟩ (N (N E ⟨206695501568,5278204⟩ E) ⟨206695501696,5264725⟩ E))) ⟨206695501824,5251289⟩ (N (N (N (N E ⟨206695501952,5237896⟩ E) ⟨206695502080,5224546⟩ (N E ⟨206695502208,5211238⟩ E)) ⟨206695502336,5197973⟩ (N (N E ⟨206695502464,5184750⟩ E) ⟨206695502592,5171569⟩ E)) ⟨206695502720,5158430⟩ (N (N (N E ⟨206695502848,5145332⟩ E) ⟨206695502976,5132276⟩ E) ⟨206695503104,5119262⟩ (N (N E ⟨206695503360,5093356⟩ E) ⟨206695503488,5080465⟩ E)))) ⟨206695503616,5067614⟩ (N (N (N (N (N E ⟨206695503872,5042035⟩ E) ⟨206695504000,5029306⟩ (N E ⟨206695504128,5016617⟩ E)) ⟨206695504256,5003968⟩ (N (N E ⟨206695504384,4991359⟩ E) ⟨206695504512,4978789⟩ E)) ⟨206695504768,4953769⟩ (N (N (N E ⟨206695505024,4928905⟩ E) ⟨206695505152,4916532⟩ E) ⟨206695505536,4879645⟩ (N (N E ⟨206695505920,4843103⟩ E) ⟨206829717376,16204586⟩ E))) ⟨206829717504,16162804⟩ (N (N (N (N E ⟨206829717632,16121157⟩ E) ⟨206829717760,16079645⟩ (N E ⟨206829717888,16038265⟩ E)) ⟨206829718016,15997019⟩ (N (N E ⟨206829718144,15955905⟩ E) ⟨206829718272,15914924⟩ E)) ⟨206829718400,15874073⟩ (N (N (N E ⟨206829718528,15833354⟩ E) ⟨206829718656,15792766⟩ E) ⟨206829718784,15752307⟩ (N (N E ⟨206829718912,15711978⟩ E) ⟨206829719040,15671778⟩ E)))))) ⟨206829719168,15631706⟩ (N (N (N (N (N (N (N E ⟨206829719296,15591763⟩ E) ⟨206829719424,15551947⟩ (N E ⟨206829719552,15512258⟩ E)) ⟨206829719680,15472695⟩ (N (N E ⟨206829719808,15433259⟩ E) ⟨206829719936,15393948⟩ E)) ⟨206829720064,15354763⟩ (N (N (N E ⟨206829720192,15315702⟩ E) ⟨206829720320,15276765⟩ (N E ⟨206829720448,15237952⟩ E)) ⟨206829720704,15160695⟩ (N (N E ⟨206829720832,15122250⟩ E) ⟨206829720960,15083927⟩ E))) ⟨206829721088,15045725⟩ (N (N (N (N E ⟨206829721216,15007644⟩ E) ⟨206829721344,14969684⟩ (N E ⟨206829721472,14931844⟩ E)) ⟨206829721600,14894123⟩ (N (N E ⟨206829721728,14856521⟩ E) ⟨206829721856,14819038⟩ E)) ⟨206829721984,14781673⟩ (N (N (N E ⟨206829722112,14744425⟩ E) ⟨206829722368,14670282⟩ E) ⟨206829723008,14486953⟩ (N (N E ⟨206829723136,14450632⟩ E) ⟨206829723264,14414425⟩ E)))) ⟨206829723648,14306480⟩ (N (N (N (N (N E ⟨206963934976,32693060⟩ E) ⟨206963935104,32608710⟩ (N E ⟨206963935232,32524633⟩ E)) ⟨206963935360,32440826⟩ (N (N E ⟨206963935488,32357289⟩ E) ⟨206963935616,32274021⟩ E)) ⟨206963935744,32191020⟩ (N (N (N E ⟨206963935872,32108287⟩ E) ⟨206963936000,32025819⟩ E) ⟨206963936128,31943615⟩ (N (N E ⟨206963936256,31861675⟩ E) ⟨206963936384,31779998⟩ E))) ⟨206963936512,31698583⟩ (N (N (N (N E ⟨206963936640,31617428⟩ E) ⟨206963936768,31536533⟩ (N E ⟨206963936896,31455896⟩ E)) ⟨206963937024,31375517⟩ (N (N E ⟨206963937152,31295395⟩ E) ⟨206963937280,31215528⟩ E)) ⟨206963937408,31135917⟩ (N (N (N E ⟨206963937536,31056558⟩ E) ⟨206963937664,30977453⟩ E) ⟨206963937792,30898599⟩ (N (N E ⟨206963937920,30819996⟩ E) ⟨206963938048,30741643⟩ E))))) ⟨206963938176,30663539⟩ (N (N (N (N (N (N E ⟨206963938304,30585683⟩ E) ⟨206963938432,30508074⟩ (N E ⟨206963938560,30430710⟩ E)) ⟨206963938688,30353592⟩ (N (N E ⟨206963938816,30276719⟩ E) ⟨206963938944,30200088⟩ E)) ⟨206963939072,30123700⟩ (N (N (N E ⟨206963939200,30047553⟩ E) ⟨206963939328,29971647⟩ (N E ⟨206963939584,29820552⟩ E)) ⟨206963939712,29745362⟩ (N (N E ⟨206963939840,29670409⟩ E) ⟨206963939968,29595692⟩ E))) ⟨206963940096,29521210⟩ (N (N (N (N E ⟨206963940224,29446962⟩ E) ⟨206963940352,29372947⟩ (N E ⟨206963940480,29299165⟩ E)) ⟨206963940736,29152295⟩ (N (N E ⟨206963940864,29079205⟩ E) ⟨206963941376,28789126⟩ E)) ⟨207098152832,54710106⟩ (N (N (N E ⟨207098152960,54569042⟩ E) ⟨207098153088,54428433⟩ E) ⟨207098153216,54288277⟩ (N (N E ⟨207098153344,54148572⟩ E) ⟨207098153472,54009316⟩ E)))) ⟨207098153600,53870507⟩ (N (N (N (N (N E ⟨207098153728,53732144⟩ E) ⟨207098153856,53594225⟩ (N E ⟨207098153984,53456749⟩ E)) ⟨207098154112,53319713⟩ (N (N E ⟨207098154240,53183116⟩ E) ⟨207098154368,53046957⟩ E)) ⟨207098154496,52911233⟩ (N (N (N E ⟨207098154624,52775943⟩ E) ⟨207098154752,52641085⟩ E) ⟨207098154880,52506657⟩ (N (N E ⟨207098155008,52372659⟩ E) ⟨207098155136,52239088⟩ E))) ⟨207098155264,52105943⟩ (N (N (N (N E ⟨207098155392,51973221⟩ E) ⟨207098155520,51840923⟩ (N E ⟨207098155648,51709045⟩ E)) ⟨207098155776,51577586⟩ (N (N E ⟨207098155904,51446544⟩ E) ⟨207098156032,51315919⟩ E)) ⟨207098156160,51185708⟩ (N (N (N E ⟨207098156288,51055910⟩ E) ⟨207098156416,50926524⟩ E) ⟨207098156544,50797547⟩ (N (N E ⟨207098156672,50668978⟩ E) ⟨207098156928,50413058⟩ E)))))))

noncomputable def tab18 : CTN :=
  (N (N (N (N (N (N (N (N E ⟨207098157184,50158753⟩ E) ⟨207098157312,50032202⟩ (N E ⟨207098157440,49906050⟩ E)) ⟨207098157696,49654936⟩ (N (N E ⟨207098157824,49529972⟩ E) ⟨207098157952,49405401⟩ E)) ⟨207098158080,49281221⟩ (N (N (N E ⟨207098158208,49157431⟩ E) ⟨207098158336,49034030⟩ (N E ⟨207098158720,48666143⟩ E)) ⟨207098159104,48301700⟩ (N (N E ⟨207232370560,82517401⟩ E) ⟨207232370688,82304640⟩ E))) ⟨207232370816,82092564⟩ (N (N (N (N E ⟨207232370944,81881171⟩ E) ⟨207232371072,81670458⟩ (N E ⟨207232371200,81460423⟩ E)) ⟨207232371328,81251062⟩ (N (N E ⟨207232371456,81042374⟩ E) ⟨207232371584,80834356⟩ E)) ⟨207232371712,80627005⟩ (N (N (N E ⟨207232371840,80420319⟩ E) ⟨207232371968,80214294⟩ E) ⟨207232372096,80008929⟩ (N (N E ⟨207232372224,79804221⟩ E) ⟨207232372352,79600168⟩ E)))) ⟨207232372480,79396766⟩ (N (N (N (N (N E ⟨207232372608,79194014⟩ E) ⟨207232372736,78991909⟩ (N E ⟨207232372992,78589630⟩ E)) ⟨207232373120,78389451⟩ (N (N E ⟨207232373376,77991002⟩ E) ⟨207232373632,77595082⟩ E)) ⟨207232373760,77398064⟩ (N (N (N E ⟨207232373888,77201672⟩ E) ⟨207232374016,77005902⟩ (N E ⟨207232374144,76810752⟩ E)) ⟨207232374272,76616220⟩ (N (N E ⟨207232374400,76422304⟩ E) ⟨207232374528,76229002⟩ E))) ⟨207232374656,76036310⟩ (N (N (N (N E ⟨207232374784,75844227⟩ E) ⟨207232374912,75652750⟩ (N E ⟨207232375040,75461877⟩ E)) ⟨207232375168,75271606⟩ (N (N E ⟨207232375296,75081935⟩ E) ⟨207232375424,74892860⟩ E)) ⟨207232375552,74704381⟩ (N (N (N E ⟨207232375680,74516494⟩ E) ⟨207232375808,74329198⟩ E) ⟨207232375936,74142490⟩ (N (N E ⟨207232376064,73956368⟩ E) ⟨207232376192,73770830⟩ E))))) ⟨207232376320,73585873⟩ (N (N (N (N (N (N E ⟨207232376448,73401496⟩ E) ⟨207232376576,73217696⟩ (N E ⟨207232376704,73034472⟩ E)) ⟨207232376832,72851820⟩ (N (N E ⟨207366588416,115736581⟩ E) ⟨207366588544,115438360⟩ E)) ⟨207366588672,115141100⟩ (N (N (N E ⟨207366588800,114844796⟩ E) ⟨207366588928,114549445⟩ (N E ⟨207366589056,114255043⟩ E)) ⟨207366589184,113961586⟩ (N (N E ⟨207366589312,113669072⟩ E) ⟨207366589440,113377495⟩ E))) ⟨207366589568,113086853⟩ (N (N (N (N E ⟨207366589696,112797142⟩ E) ⟨207366589824,112508359⟩ (N E ⟨207366589952,112220499⟩ E)) ⟨207366590080,111933559⟩ (N (N E ⟨207366590208,111647537⟩ E) ⟨207366590336,111362427⟩ E)) ⟨207366590464,111078227⟩ (N (N (N E ⟨207366590592,110794934⟩ E) ⟨207366590720,110512543⟩ E) ⟨207366590848,110231052⟩ (N (N E ⟨207366590976,109950457⟩ E) ⟨207366591104,109670754⟩ E)))) ⟨207366591232,109391940⟩ (N (N (N (N (N E ⟨207366591360,109114012⟩ E) ⟨207366591488,108836966⟩ (N E ⟨207366591744,108285508⟩ E)) ⟨207366591872,108011089⟩ (N (N E ⟨207366592000,107737540⟩ E) ⟨207366592128,107464855⟩ E)) ⟨207366592256,107193034⟩ (N (N (N E ⟨207366592384,106922071⟩ E) ⟨207366592512,106651964⟩ E) ⟨207366592640,106382710⟩ (N (N E ⟨207366592768,106114305⟩ E) ⟨207366592896,105846746⟩ E))) ⟨207366593024,105580031⟩ (N (N (N (N E ⟨207366593152,105314155⟩ E) ⟨207366593536,104521534⟩ (N E ⟨207366593664,104258986⟩ E)) ⟨207366593792,103997262⟩ (N (N E ⟨207366593920,103736358⟩ E) ⟨207366594048,103476273⟩ E)) ⟨207366594176,103217002⟩ (N (N (N E ⟨207366594304,102958543⟩ E) ⟨207366594560,102444049⟩ E) ⟨207500806272,154467512⟩ (N (N E ⟨207500806400,154069749⟩ E) ⟨207500806528,153673267⟩ E)))))) ⟨207500806656,153278059⟩ (N (N (N (N (N (N (N E ⟨207500806784,152884121⟩ E) ⟨207500806912,152491448⟩ (N E ⟨207500807040,152100035⟩ E)) ⟨207500807168,151709878⟩ (N (N E ⟨207500807296,151320972⟩ E) ⟨207500807424,150933311⟩ E)) ⟨207500807552,150546891⟩ (N (N (N E ⟨207500807680,150161707⟩ E) ⟨207500807808,149777755⟩ (N E ⟨207500807936,149395029⟩ E)) ⟨207500808064,149013525⟩ (N (N E ⟨207500808192,148633239⟩ E) ⟨207500808320,148254166⟩ E))) ⟨207500808448,147876300⟩ (N (N (N (N E ⟨207500808576,147499638⟩ E) ⟨207500808704,147124175⟩ (N E ⟨207500808832,146749906⟩ E)) ⟨207500808960,146376826⟩ (N (N E ⟨207500809088,146004932⟩ E) ⟨207500809216,145634218⟩ E)) ⟨207500809344,145264681⟩ (N (N (N E ⟨207500809472,144896315⟩ E) ⟨207500809600,144529117⟩ E) ⟨207500809728,144163081⟩ (N (N E ⟨207500809856,143798203⟩ E) ⟨207500809984,143434480⟩ E)))) ⟨207500810112,143071906⟩ (N (N (N (N (N E ⟨207500810240,142710477⟩ E) ⟨207500810368,142350190⟩ (N E ⟨207500810496,141991038⟩ E)) ⟨207500810624,141633020⟩ (N (N E ⟨207500810752,141276129⟩ E) ⟨207500810880,140920361⟩ E)) ⟨207500811008,140565714⟩ (N (N (N E ⟨207500811136,140212181⟩ E) ⟨207500811264,139859760⟩ E) ⟨207500811392,139508445⟩ (N (N E ⟨207500811648,138809119⟩ E) ⟨207500811776,138461100⟩ E))) ⟨207500811904,138114172⟩ (N (N (N (N E ⟨207500812032,137768329⟩ E) ⟨207500812160,137423569⟩ (N E ⟨207500812288,137079886⟩ E)) ⟨207635024128,198665350⟩ (N (N E ⟨207635024256,198154105⟩ E) ⟨207635024384,197644504⟩ E)) ⟨207635024512,197136540⟩ (N (N (N E ⟨207635024640,196630208⟩ E) ⟨207635024768,196125501⟩ E) ⟨207635024896,195622412⟩ (N (N E ⟨207635025024,195120936⟩ E) ⟨207635025152,194621067⟩ E))))) ⟨207635025280,194122797⟩ (N (N (N (N (N (N E ⟨207635025408,193626122⟩ E) ⟨207635025536,193131034⟩ (N E ⟨207635025664,192637528⟩ E)) ⟨207635025792,192145598⟩ (N (N E ⟨207635025920,191655238⟩ E) ⟨207635026048,191166441⟩ E)) ⟨207635026176,190679202⟩ (N (N (N E ⟨207635026304,190193515⟩ E) ⟨207635026432,189709374⟩ (N E ⟨207635026560,189226772⟩ E)) ⟨207635026688,188745705⟩ (N (N E ⟨207635026816,188266165⟩ E) ⟨207635027072,187311648⟩ E))) ⟨207635027200,186836659⟩ (N (N (N (N E ⟨207635027328,186363174⟩ E) ⟨207635027456,185891189⟩ (N E ⟨207635027584,185420698⟩ E)) ⟨207635027712,184951694⟩ (N (N E ⟨207635027840,184484173⟩ E) ⟨207635027968,184018129⟩ E)) ⟨207635028096,183553555⟩ (N (N (N E ⟨207635028224,183090448⟩ E) ⟨207635028352,182628800⟩ E) ⟨207635028480,182168606⟩ (N (N E ⟨207635028608,181709862⟩ E) ⟨207635028736,181252561⟩ E)))) ⟨207635028864,180796698⟩ (N (N (N (N (N E ⟨207635028992,180342268⟩ E) ⟨207635029120,179889265⟩ (N E ⟨207635029376,178987520⟩ E)) ⟨207635029760,177645472⟩ (N (N E ⟨207635029888,177200920⟩ E) ⟨207635030016,176757759⟩ E)) ⟨207769241984,248282094⟩ (N (N (N E ⟨207769242112,247643577⟩ E) ⟨207769242240,247007111⟩ E) ⟨207769242368,246372690⟩ (N (N E ⟨207769242496,245740304⟩ E) ⟨207769242624,245109947⟩ E))) ⟨207769242752,244481611⟩ (N (N (N (N E ⟨207769242880,243855286⟩ E) ⟨207769243008,243230967⟩ (N E ⟨207769243136,242608646⟩ E)) ⟨207769243264,241988313⟩ (N (N E ⟨207769243392,241369963⟩ E) ⟨207769243520,240753587⟩ E)) ⟨207769243648,240139178⟩ (N (N (N E ⟨207769243776,239526728⟩ E) ⟨207769243904,238916230⟩ E) ⟨207769244032,238307676⟩ (N (N E ⟨207769244160,237701059⟩ E) ⟨207769244288,237096371⟩ E)))))))

noncomputable def tab19 : CTN :=
  (N (N (N (N (N (N (N (N E ⟨207769244544,235892755⟩ E) ⟨207769244672,235293812⟩ (N E ⟨207769244800,234696769⟩ E)) ⟨207769244928,234101620⟩ (N (N E ⟨207769245056,233508356⟩ E) ⟨207769245184,232916970⟩ E)) ⟨207769245312,232327456⟩ (N (N (N E ⟨207769245440,231739807⟩ E) ⟨207769245568,231154014⟩ (N E ⟨207769245696,230570072⟩ E)) ⟨207769245824,229987974⟩ (N (N E ⟨207769245952,229407711⟩ E) ⟨207769246080,228829278⟩ E))) ⟨207769246208,228252668⟩ (N (N (N (N E ⟨207769246336,227677873⟩ E) ⟨207769246464,227104886⟩ (N E ⟨207769246592,226533702⟩ E)) ⟨207769246720,225964312⟩ (N (N E ⟨207769246848,225396711⟩ E) ⟨207769247104,224266846⟩ E)) ⟨207769247488,222585294⟩ (N (N (N E ⟨207769247616,222028282⟩ E) ⟨207769247744,221473012⟩ E) ⟨207903459840,303266624⟩ (N (N E ⟨207903459968,302487202⟩ E) ⟨207903460096,301710284⟩ E)))) ⟨207903460224,300935859⟩ (N (N (N (N (N E ⟨207903460352,300163918⟩ E) ⟨207903460480,299394451⟩ (N E ⟨207903460608,298627449⟩ E)) ⟨207903460736,297862902⟩ (N (N E ⟨207903460864,297100800⟩ E) ⟨207903460992,296341136⟩ E)) ⟨207903461120,295583898⟩ (N (N (N E ⟨207903461248,294829078⟩ E) ⟨207903461376,294076667⟩ (N E ⟨207903461504,293326655⟩ E)) ⟨207903461632,292579034⟩ (N (N E ⟨207903461760,291833793⟩ E) ⟨207903461888,291090924⟩ E))) ⟨207903462016,290350418⟩ (N (N (N (N E ⟨207903462144,289612266⟩ E) ⟨207903462272,288876459⟩ (N E ⟨207903462400,288142988⟩ E)) ⟨207903462528,287411843⟩ (N (N E ⟨207903462656,286683017⟩ E) ⟨207903462784,285956501⟩ E)) ⟨207903462912,285232285⟩ (N (N (N E ⟨207903463040,284510360⟩ E) ⟨207903463168,283790719⟩ E) ⟨207903463296,283073353⟩ (N (N E ⟨207903463424,282358252⟩ E) ⟨207903463552,281645409⟩ E))))) ⟨207903463680,280934814⟩ (N (N (N (N (N (N E ⟨207903463808,280226459⟩ E) ⟨207903463936,279520337⟩ (N E ⟨207903464064,278816437⟩ E)) ⟨207903464192,278114753⟩ (N (N E ⟨207903464320,277415275⟩ E) ⟨207903464448,276717995⟩ E)) ⟨207903464576,276022906⟩ (N (N (N E ⟨207903464704,275329997⟩ E) ⟨207903464832,274639263⟩ (N E ⟨207903464960,273950694⟩ E)) ⟨207903465088,273264282⟩ (N (N E ⟨207903465216,272580019⟩ E) ⟨207903465344,271897897⟩ E))) ⟨207903465472,271217907⟩ (N (N (N (N E ⟨208037677824,362630946⟩ E) ⟨208037677952,361700151⟩ (N E ⟨208037678080,360772341⟩ E)) ⟨208037678208,359847505⟩ (N (N E ⟨208037678336,358925632⟩ E) ⟨208037678464,358006709⟩ E)) ⟨208037678592,357090726⟩ (N (N (N E ⟨208037678720,356177672⟩ E) ⟨208037678848,355267534⟩ E) ⟨208037678976,354360303⟩ (N (N E ⟨208037679104,353455967⟩ E) ⟨208037679232,352554514⟩ E)))) ⟨208037679360,351655934⟩ (N (N (N (N (N E ⟨208037679488,350760216⟩ E) ⟨208037679616,349867349⟩ (N E ⟨208037679744,348977322⟩ E)) ⟨208037679872,348090124⟩ (N (N E ⟨208037680000,347205744⟩ E) ⟨208037680128,346324172⟩ E)) ⟨208037680256,345445397⟩ (N (N (N E ⟨208037680384,344569408⟩ E) ⟨208037680512,343696195⟩ E) ⟨208037680640,342825746⟩ (N (N E ⟨208037680768,341958053⟩ E) ⟨208037680896,341093103⟩ E))) ⟨208037681024,340230888⟩ (N (N (N (N E ⟨208037681152,339371396⟩ E) ⟨208037681280,338514616⟩ (N E ⟨208037681408,337660540⟩ E)) ⟨208037681536,336809156⟩ (N (N E ⟨208037681664,335960455⟩ E) ⟨208037681792,335114426⟩ E)) ⟨208037681920,334271059⟩ (N (N (N E ⟨208037682048,333430344⟩ E) ⟨208037682304,331756830⟩ E) ⟨208037682432,330924012⟩ (N (N E ⟨208037682560,330093806⟩ E) ⟨208037682688,329266202⟩ E)))))) ⟨208037682816,328441191⟩ (N (N (N (N (N (N (N E ⟨208037682944,327618763⟩ E) ⟨208037683072,326798909⟩ (N E ⟨208037683200,325981618⟩ E)) ⟨208171895680,428017739⟩ (N (N E ⟨208171895808,426919816⟩ E) ⟨208171895936,425825412⟩ E)) ⟨208171896064,424734513⟩ (N (N (N E ⟨208171896192,423647106⟩ E) ⟨208171896320,422563178⟩ (N E ⟨208171896448,421482715⟩ E)) ⟨208171896576,420405705⟩ (N (N E ⟨208171896704,419332133⟩ E) ⟨208171896832,418261987⟩ E))) ⟨208171896960,417195253⟩ (N (N (N (N E ⟨208171897088,416131919⟩ E) ⟨208171897216,415071972⟩ (N E ⟨208171897344,414015398⟩ E)) ⟨208171897472,412962184⟩ (N (N E ⟨208171897600,411912319⟩ E) ⟨208171897728,410865788⟩ E)) ⟨208171897856,409822580⟩ (N (N (N E ⟨208171897984,408782682⟩ E) ⟨208171898112,407746081⟩ E) ⟨208171898240,406712764⟩ (N (N E ⟨208171898368,405682720⟩ E) ⟨208171898496,404655935⟩ E)))) ⟨208171898624,403632397⟩ (N (N (N (N (N E ⟨208171898752,402612095⟩ E) ⟨208171898880,401595015⟩ (N E ⟨208171899008,400581146⟩ E)) ⟨208171899136,399570475⟩ (N (N E ⟨208171899264,398562990⟩ E) ⟨208171899392,397558679⟩ E)) ⟨208171899520,396557531⟩ (N (N (N E ⟨208171899648,395559533⟩ E) ⟨208171899776,394564673⟩ E) ⟨208171899904,393572940⟩ (N (N E ⟨208171900032,392584322⟩ E) ⟨208171900160,391598806⟩ E))) ⟨208171900288,390616382⟩ (N (N (N (N E ⟨208171900672,387687542⟩ E) ⟨208171900800,386717367⟩ (N E ⟨208171900928,385750226⟩ E)) ⟨208306113664,497309398⟩ (N (N E ⟨208306113792,496035368⟩ E) ⟨208306113920,494765417⟩ E)) ⟨208306114048,493499528⟩ (N (N (N E ⟨208306114176,492237687⟩ E) ⟨208306114304,490979877⟩ E) ⟨208306114432,489726083⟩ (N (N E ⟨208306114560,488476289⟩ E) ⟨208306114688,487230481⟩ E))))) ⟨208306114816,485988644⟩ (N (N (N (N (N (N E ⟨208306114944,484750761⟩ E) ⟨208306115072,483516818⟩ (N E ⟨208306115200,482286800⟩ E)) ⟨208306115328,481060692⟩ (N (N E ⟨208306115456,479838479⟩ E) ⟨208306115584,478620146⟩ E)) ⟨208306115712,477405678⟩ (N (N (N E ⟨208306115840,476195061⟩ E) ⟨208306115968,474988280⟩ (N E ⟨208306116096,473785320⟩ E)) ⟨208306116224,472586168⟩ (N (N E ⟨208306116352,471390807⟩ E) ⟨208306116480,470199225⟩ E))) ⟨208306116608,469011406⟩ (N (N (N (N E ⟨208306116736,467827337⟩ E) ⟨208306116864,466647003⟩ (N E ⟨208306116992,465470390⟩ E)) ⟨208306117120,464297485⟩ (N (N E ⟨208306117248,463128272⟩ E) ⟨208306117376,461962738⟩ E)) ⟨208306117504,460800870⟩ (N (N (N E ⟨208306117632,459642653⟩ E) ⟨208306117760,458488074⟩ E) ⟨208306117888,457337118⟩ (N (N E ⟨208306118016,456189773⟩ E) ⟨208306118144,455046024⟩ E)))) ⟨208306118272,453905859⟩ (N (N (N (N (N E ⟨208306118400,452769263⟩ E) ⟨208306118528,451636224⟩ (N E ⟨208306118656,450506728⟩ E)) ⟨208440331392,574277286⟩ (N (N E ⟨208440331520,572806076⟩ E) ⟨208440331648,571339576⟩ E)) ⟨208440331776,569877768⟩ (N (N (N E ⟨208440331904,568420633⟩ E) ⟨208440332032,566968153⟩ E) ⟨208440332160,565520311⟩ (N (N E ⟨208440332288,564077089⟩ E) ⟨208440332416,562638469⟩ E))) ⟨208440332544,561204434⟩ (N (N (N (N E ⟨208440332672,559774966⟩ E) ⟨208440332800,558350048⟩ (N E ⟨208440332928,556929662⟩ E)) ⟨208440333056,555513790⟩ (N (N E ⟨208440333184,554102417⟩ E) ⟨208440333312,552695524⟩ E)) ⟨208440333440,551293095⟩ (N (N (N E ⟨208440333568,549895112⟩ E) ⟨208440333696,548501559⟩ E) ⟨208440333824,547112419⟩ (N (N E ⟨208440333952,545727675⟩ E) ⟨208440334080,544347311⟩ E)))))))

noncomputable def tab20 : CTN :=
  (N (N (N (N (N (N (N (N E ⟨208440334336,541599653⟩ E) ⟨208440334464,540232327⟩ (N E ⟨208440334592,538869315⟩ E)) ⟨208440334720,537510599⟩ (N (N E ⟨208440334848,536156164⟩ E) ⟨208440334976,534805994⟩ E)) ⟨208440335104,533460073⟩ (N (N (N E ⟨208440335232,532118383⟩ E) ⟨208440335360,530780911⟩ (N E ⟨208440335488,529447639⟩ E)) ⟨208440335616,528118552⟩ (N (N E ⟨208440335744,526793633⟩ E) ⟨208440335872,525472868⟩ E))) ⟨208440336000,524156241⟩ (N (N (N (N E ⟨208440336128,522843736⟩ E) ⟨208440336256,521535338⟩ (N E ⟨208440336384,520231031⟩ E)) ⟨208574549504,651672512⟩ (N (N E ⟨208574549760,648345280⟩ E) ⟨208574549888,646689628⟩ E)) ⟨208574550016,645039260⟩ (N (N (N E ⟨208574550144,643394155⟩ E) ⟨208574550272,641754292⟩ E) ⟨208574550400,640119652⟩ (N (N E ⟨208574550528,638490215⟩ E) ⟨208574550656,636865960⟩ E)))) ⟨208574550784,635246868⟩ (N (N (N (N (N E ⟨208574550912,633632920⟩ E) ⟨208574551040,632024096⟩ (N E ⟨208574551168,630420375⟩ E)) ⟨208574551296,628821740⟩ (N (N E ⟨208574551424,627228170⟩ E) ⟨208574551552,625639646⟩ E)) ⟨208574551680,624056149⟩ (N (N (N E ⟨208574551936,620904160⟩ E) ⟨208574552064,619335630⟩ (N E ⟨208574552192,617772052⟩ E)) ⟨208574552320,616213406⟩ (N (N E ⟨208574552448,614659673⟩ E) ⟨208574552576,613110836⟩ E))) ⟨208574552704,611566875⟩ (N (N (N (N E ⟨208574552832,610027773⟩ E) ⟨208574553088,606964071⟩ (N E ⟨208574553216,605439434⟩ E)) ⟨208574553344,603919582⟩ (N (N E ⟨208574553472,602404498⟩ E) ⟨208574553600,600894163⟩ E)) ⟨208574553856,597887671⟩ (N (N (N E ⟨208574553984,596391478⟩ E) ⟨208574554112,594899963⟩ E) ⟨208708767360,736965811⟩ (N (N E ⟨208708767616,733205501⟩ E) ⟨208708767744,731334342⟩ E))))) ⟨208708767872,729469150⟩ (N (N (N (N (N (N E ⟨208708768000,727609902⟩ E) ⟨208708768128,725756576⟩ (N E ⟨208708768256,723909148⟩ E)) ⟨208708768384,722067596⟩ (N (N E ⟨208708768512,720231898⟩ E) ⟨208708768640,718402031⟩ E)) ⟨208708768768,716577974⟩ (N (N (N E ⟨208708768896,714759704⟩ E) ⟨208708769024,712947198⟩ (N E ⟨208708769152,711140436⟩ E)) ⟨208708769280,709339395⟩ (N (N E ⟨208708769408,707544054⟩ E) ⟨208708769536,705754391⟩ E))) ⟨208708769664,703970384⟩ (N (N (N (N E ⟨208708769792,702192012⟩ E) ⟨208708769920,700419253⟩ (N E ⟨208708770048,698652087⟩ E)) ⟨208708770176,696890493⟩ (N (N E ⟨208708770432,693383932⟩ E) ⟨208708770688,689899405⟩ E)) ⟨208708770816,688165352⟩ (N (N (N E ⟨208708770944,686436745⟩ E) ⟨208708771072,684713563⟩ E) ⟨208708771200,682995787⟩ (N (N E ⟨208708771328,681283396⟩ E) ⟨208708771456,679576369⟩ E)))) ⟨208708771584,677874687⟩ (N (N (N (N (N E ⟨208708771712,676178329⟩ E) ⟨208708771840,674487275⟩ (N E ⟨208842985216,827148315⟩ E)) ⟨208842985344,825036062⟩ (N (N E ⟨208842985472,822930549⟩ E) ⟨208842985600,820831751⟩ E)) ⟨208842985728,818739641⟩ (N (N (N E ⟨208842985856,816654193⟩ E) ⟨208842985984,814575384⟩ E) ⟨208842986112,812503186⟩ (N (N E ⟨208842986240,810437576⟩ E) ⟨208842986368,808378527⟩ E))) ⟨208842986496,806326015⟩ (N (N (N (N E ⟨208842986624,804280014⟩ E) ⟨208842986752,802240501⟩ (N E ⟨208842986880,800207451⟩ E)) ⟨208842987008,798180838⟩ (N (N E ⟨208842987136,796160639⟩ E) ⟨208842987264,794146828⟩ E)) ⟨208842987392,792139383⟩ (N (N (N E ⟨208842987520,790138278⟩ E) ⟨208842987648,788143490⟩ E) ⟨208842987776,786154995⟩ (N (N E ⟨208842987904,784172768⟩ E) ⟨208842988032,782196787⟩ E)))))) ⟨208842988160,780227027⟩ (N (N (N (N (N (N (N E ⟨208842988288,778263466⟩ E) ⟨208842988416,776306079⟩ (N E ⟨208842988544,774354844⟩ E)) ⟨208842988672,772409737⟩ (N (N E ⟨208842988800,770470735⟩ E) ⟨208842989056,766610955⟩ E)) ⟨208842989184,764690132⟩ (N (N (N E ⟨208842989312,762775322⟩ E) ⟨208842989568,758963653⟩ (N E ⟨208977203200,919792780⟩ E)) ⟨208977203328,917446945⟩ (N (N E ⟨208977203456,915108585⟩ E) ⟨208977203584,912777672⟩ E))) ⟨208977203712,910454178⟩ (N (N (N (N E ⟨208977203840,908138075⟩ E) ⟨208977203968,905829333⟩ (N E ⟨208977204096,903527926⟩ E)) ⟨208977204224,901233825⟩ (N (N E ⟨208977204352,898947003⟩ E) ⟨208977204480,896667431⟩ E)) ⟨208977204608,894395082⟩ (N (N (N E ⟨208977204736,892129929⟩ E) ⟨208977204864,889871944⟩ E) ⟨208977205120,885377370⟩ (N (N E ⟨208977205248,883140727⟩ E) ⟨208977205376,880911144⟩ E)))) ⟨208977205504,878688595⟩ (N (N (N (N (N E ⟨208977205632,876473053⟩ E) ⟨208977205760,874264491⟩ (N E ⟨208977205888,872062882⟩ E)) ⟨208977206144,867680423⟩ (N (N E ⟨208977206272,865499519⟩ E) ⟨208977206656,858997803⟩ E)) ⟨208977206784,856844144⟩ (N (N (N E ⟨208977206912,854697231⟩ E) ⟨208977207040,852557041⟩ E) ⟨208977207168,850423546⟩ (N (N E ⟨208977207296,848296723⟩ E) ⟨209111421056,1019276428⟩ E))) ⟨209111421184,1016678529⟩ (N (N (N (N E ⟨209111421440,1011507519⟩ E) ⟨209111421568,1008934346⟩ (N E ⟨209111421696,1006369352⟩ E)) ⟨209111421824,1003812507⟩ (N (N E ⟨209111421952,1001263779⟩ E) ⟨209111422080,998723136⟩ E)) ⟨209111422208,996190550⟩ (N (N (N E ⟨209111422464,991149420⟩ E) ⟨209111422592,988640816⟩ E) ⟨209111422720,986140146⟩ (N (N E ⟨209111422848,983647380⟩ E) ⟨209111422976,981162487⟩ E))))) ⟨209111423104,978685438⟩ (N (N (N (N (N (N E ⟨209111423232,976216203⟩ E) ⟨209111423360,973754753⟩ (N E ⟨209111423488,971301057⟩ E)) ⟨209111423616,968855088⟩ (N (N E ⟨209111423744,966416815⟩ E) ⟨209111423872,963986209⟩ E)) ⟨209111424000,961563243⟩ (N (N (N E ⟨209111424128,959147886⟩ E) ⟨209111424384,954339887⟩ (N E ⟨209111424512,951947188⟩ E)) ⟨209111424640,949561984⟩ (N (N E ⟨209111424768,947184249⟩ E) ⟨209111424896,944813953⟩ E))) ⟨209111425024,942451069⟩ (N (N (N (N E ⟨209245639296,1114850841⟩ E) ⟨209245639424,1112016578⟩ (N E ⟨209245639552,1109191318⟩ E)) ⟨209245639680,1106375028⟩ (N (N E ⟨209245639808,1103567673⟩ E) ⟨209245639936,1100769219⟩ E)) ⟨209245640064,1097979632⟩ (N (N (N E ⟨209245640320,1092426925⟩ E) ⟨209245640448,1089663738⟩ E) ⟨209245640576,1086909285⟩ (N (N E ⟨209245640704,1084163531⟩ E) ⟨209245640832,1081426445⟩ E)))) ⟨209245640960,1078697993⟩ (N (N (N (N (N E ⟨209245641088,1075978143⟩ E) ⟨209245641216,1073266863⟩ (N E ⟨209245641472,1067869879⟩ E)) ⟨209245641600,1065184112⟩ (N (N E ⟨209245641728,1062506786⟩ E) ⟨209245641856,1059837868⟩ E)) ⟨209245641984,1057177328⟩ (N (N (N E ⟨209245642112,1054525132⟩ E) ⟨209245642240,1051881251⟩ E) ⟨209245642368,1049245653⟩ (N (N E ⟨209245642624,1043999180⟩ E) ⟨209245642752,1041388244⟩ E))) ⟨209379857152,1222726734⟩ (N (N (N (N E ⟨209379857536,1213436673⟩ E) ⟨209379857792,1207292298⟩ (N E ⟨209379857920,1204234698⟩ E)) ⟨209379858176,1198148491⟩ (N (N E ⟨209379858304,1195119809⟩ E) ⟨209379858432,1192100694⟩ E)) ⟨209379858688,1186091018⟩ (N (N (N E ⟨209379858816,1183100385⟩ E) ⟨209379858944,1180119175⟩ E) ⟨209379859072,1177147351⟩ (N (N E ⟨209379859200,1174184879⟩ E) ⟨209379859328,1171231722⟩ E)))))))

noncomputable def tab21 : CTN :=
  (N (N (N (N (N (N (N (N E ⟨209379859584,1165353217⟩ E) ⟨209379859840,1159511555⟩ (N E ⟨209379859968,1156604455⟩ E)) ⟨209379860480,1145066785⟩ (N (N E ⟨209514075136,1331662030⟩ E) ⟨209514075264,1328283024⟩ E)) ⟨209514075520,1321557111⟩ (N (N (N E ⟨209514075648,1318210123⟩ E) ⟨209514075776,1314873727⟩ (N E ⟨209514076032,1308232551⟩ E)) ⟨209514076160,1304927690⟩ (N (N E ⟨209514076288,1301633261⟩ E) ⟨209514076544,1295075542⟩ E))) ⟨209514076672,1291812173⟩ (N (N (N (N E ⟨209514076800,1288559080⟩ E) ⟨209514076928,1285316223⟩ (N E ⟨209514077184,1278861063⟩ E)) ⟨209514077312,1275648683⟩ (N (N E ⟨209514077440,1272446387⟩ E) ⟨209514077568,1269254135⟩ E)) ⟨209514077696,1266071890⟩ (N (N (N E ⟨209514077952,1259737271⟩ E) ⟨209514078080,1256584822⟩ E) ⟨209514078208,1253442231⟩ (N (N E ⟨209648292992,1448056455⟩ E) ⟨209648293632,1429812279⟩ E)))) ⟨209648293760,1426197998⟩ (N (N (N (N (N E ⟨209648293888,1422595132⟩ E) ⟨209648294016,1419003640⟩ (N E ⟨209648294144,1415423477⟩ E)) ⟨209648294272,1411854601⟩ (N (N E ⟨209648294400,1408296969⟩ E) ⟨209648294528,1404750538⟩ E)) ⟨209648294656,1401215267⟩ (N (N (N E ⟨209648294784,1397691114⟩ E) ⟨209648295040,1390675990⟩ (N E ⟨209648295168,1387184938⟩ E)) ⟨209648295424,1380235642⟩ (N (N E ⟨209648295552,1376777318⟩ E) ⟨209648295680,1373329821⟩ E))) ⟨209648295936,1366467147⟩ (N (N (N (N E ⟨209782511744,1541149915⟩ E) ⟨209782511872,1537261575⟩ (N E ⟨209782512256,1525669922⟩ E)) ⟨209782512384,1521830339⟩ (N (N E ⟨209782512512,1518002830⟩ E) ⟨209782512768,1510383853⟩ E)) ⟨209782512896,1506592294⟩ (N (N (N E ⟨209782513024,1502812628⟩ E) ⟨209782513280,1495288797⟩ E) ⟨209782513664,1484091138⟩ (N (N E ⟨209916730368,1638834599⟩ E) ⟨209916730496,1634717999⟩ E))))) ⟨209916730752,1626523515⟩ (N (N (N (N (N (N E ⟨209916730880,1622445533⟩ E) ⟨209916731136,1614327847⟩ (N E ⟨209916731264,1610288047⟩ E)) ⟨209916731392,1606260880⟩ (N (N E ⟨210050947584,1785967694⟩ E) ⟨210050947840,1776986855⟩ E)) ⟨210050948352,1759193934⟩ (N (N (N E ⟨210050948480,1754780554⟩ E) ⟨210050948608,1750381008⟩ (N E ⟨210050948736,1745995246⟩ E)) ⟨210050948864,1741623214⟩ (N (N E ⟨210050949120,1732920140⟩ E) ⟨210185164928,1935675294⟩ E))) ⟨210185165952,1897033299⟩ (N (N (N (N E ⟨210185166080,1892271123⟩ E) ⟨210185166848,1864009804⟩ (N E ⟨210319384192,2014554151⟩ E)) ⟨210319384576,1999467908⟩ (N (N E ⟨210453602304,2139229668⟩ E) ⟨210587820032,2283227512⟩ E)) ⟨210722037760,2431391112⟩ (N (N (N E ⟨210856255488,2583647426⟩ E) ⟨210990473216,2739920731⟩ E) ⟨211124690944,2900132663⟩ (N (N E ⟨211258908672,3064202262⟩ E) ⟨211393126400,3232046011⟩ E)))) ⟨211527344128,3403577882⟩ (N (N (N (N (N E ⟨211661561856,3578709384⟩ E) ⟨211795779584,3757349609⟩ (N E ⟨211929997312,3939405282⟩ E)) ⟨212064215040,4124780812⟩ (N (N E ⟨212198432768,4313378347⟩ E) ⟨212332650496,4505097824⟩ E)) ⟨212601085952,4897491654⟩ (N (N (N E ⟨212735303680,5097955349⟩ E) ⟨212869521408,5301119791⟩ E) ⟨213003739136,5506874740⟩ (N (N E ⟨213137956864,5715108105⟩ E) ⟨213406392320,6138552830⟩ E))) ⟨213540610048,6353531323⟩ (N (N (N (N E ⟨213943263232,7010060751⟩ E) ⟨214480134144,7907901185⟩ (N E ⟨214748569728,8343278283⟩ E)) ⟨214748569856,8322438682⟩ (N (N E ⟨214748569984,8301664123⟩ E) ⟨214748570112,8280954363⟩ E)) ⟨214748570240,8260309158⟩ (N (N (N E ⟨214748570368,8239728268⟩ E) ⟨214748570496,8219211452⟩ E) ⟨214748570624,8198758471⟩ (N (N E ⟨214748570752,8178369086⟩ E) ⟨214748570880,8158043061⟩ E)))))) ⟨214748571008,8137780160⟩ (N (N (N (N (N (N (N E ⟨214748571136,8117580146⟩ E) ⟨214748571264,8097442786⟩ (N E ⟨214748571392,8077367847⟩ E)) ⟨214748571520,8057355097⟩ (N (N E ⟨214748571648,8037404305⟩ E) ⟨214748571776,8017515240⟩ E)) ⟨214748571904,7997687674⟩ (N (N (N E ⟨214748572032,7977921378⟩ E) ⟨214748572160,7958216125⟩ (N E ⟨214748572288,7938571689⟩ E)) ⟨214748572416,7918987845⟩ (N (N E ⟨214748572544,7899464369⟩ E) ⟨214748572672,7880001038⟩ E))) ⟨214748572800,7860597628⟩ (N (N (N (N E ⟨214748572928,7841253920⟩ E) ⟨214748573056,7821969692⟩ (N E ⟨214748573184,7802744726⟩ E)) ⟨214748573312,7783578802⟩ (N (N E ⟨214748573440,7764471704⟩ E) ⟨214748573568,7745423214⟩ E)) ⟨214748573696,7726433117⟩ (N (N (N E ⟨214748573824,7707501199⟩ E) ⟨214748573952,7688627245⟩ E) ⟨214748574080,7669811042⟩ (N (N E ⟨214748574208,7651052380⟩ E) ⟨214748574336,7632351046⟩ E)))) ⟨214748574464,7613706830⟩ (N (N (N (N (N E ⟨214748574592,7595119523⟩ E) ⟨214748574720,7576588917⟩ (N E ⟨214748574848,7558114805⟩ E)) ⟨214748574976,7539696979⟩ (N (N E ⟨214748575104,7521335234⟩ E) ⟨214748575232,7503029365⟩ E)) ⟨214748575360,7484779168⟩ (N (N (N E ⟨214748575488,7466584440⟩ E) ⟨214748575616,7448444979⟩ E) ⟨214748575744,7430360584⟩ (N (N E ⟨214748575872,7412331053⟩ E) ⟨214748576000,7394356188⟩ E))) ⟨214748576128,7376435789⟩ (N (N (N (N E ⟨214748576256,7358569658⟩ E) ⟨214748576384,7340757599⟩ (N E ⟨214748576512,7322999415⟩ E)) ⟨214748576640,7305294910⟩ (N (N E ⟨214748576768,7287643890⟩ E) ⟨214748576896,7270046162⟩ E)) ⟨214748577024,7252501531⟩ (N (N (N E ⟨214748577152,7235009806⟩ E) ⟨214748577280,7217570796⟩ E) ⟨214748577408,7200184310⟩ (N (N E ⟨214748577536,7182850157⟩ E) ⟨214748577664,7165568150⟩ E))))) ⟨214748577792,7148338100⟩ (N (N (N (N (N (N E ⟨216896061440,10300402336⟩ E) ⟨220654157824,14892878876⟩ (N E ⟨223070076928,16387501929⟩ E)) ⟨223338512512,16418769270⟩ (N (N E ⟨223338512640,16371937440⟩ E) ⟨223338512768,16320343345⟩ E)) ⟨223338512896,16264029169⟩ (N (N (N E ⟨223338513024,16203039755⟩ E) ⟨223338513152,16137422570⟩ (N E ⟨223338513280,16067227664⟩ E)) ⟨223338513408,15992507623⟩ (N (N E ⟨223338513536,15913317533⟩ E) ⟨223338513664,15829714926⟩ E))) ⟨223338513792,15741759742⟩ (N (N (N (N E ⟨223338513920,15649514276⟩ E) ⟨223338514048,15553043132⟩ (N E ⟨223338514176,15452413173⟩ E)) ⟨223338514304,15347693469⟩ (N (N E ⟨223338514560,15126271841⟩ E) ⟨223338514688,15009718625⟩ E)) ⟨223338514816,14889372976⟩ (N (N (N E ⟨223338514944,14765314206⟩ E) ⟨223338515072,14637623509⟩ E) ⟨223338515200,14506383906⟩ (N (N E ⟨223338515328,14371680180⟩ E) ⟨223338515456,14233598825⟩ E)))) ⟨223338515584,14092227980⟩ (N (N (N (N (N E ⟨223338515712,13947657371⟩ E) ⟨223338515840,13799978251⟩ (N E ⟨223338515968,13649283334⟩ E)) ⟨223338516096,13495666739⟩ (N (N E ⟨223338516224,13339223920⟩ E) ⟨223338516352,13180051607⟩ E)) ⟨223338516480,13018247744⟩ (N (N (N E ⟨223338516608,12853911416⟩ E) ⟨223338516736,12687142798⟩ E) ⟨223338516864,12518043076⟩ (N (N E ⟨223338517120,12173259767⟩ E) ⟨223338517248,11997783053⟩ E))) ⟨223338517376,11820388852⟩ (N (N (N (N E ⟨223338517504,11641182452⟩ E) ⟨223338517760,11277757267⟩ (N E ⟨223338518016,10908361077⟩ E)) ⟨223338518272,10533854239⟩ (N (N E ⟨223338518400,10344954523⟩ E) ⟨223338518528,10155101777⟩ E)) ⟨223338518784,9772971268⟩ (N (N (N E ⟨223338519040,9388330754⟩ E) ⟨223338519168,9195340124⟩ E) ⟨223338519296,9002046665⟩ (N (N E ⟨223338519424,8808558093⟩ E) ⟨223338519552,8614981766⟩ E)))))))

noncomputable def tab22 : CTN :=
  (N (N (N (N (N (N (N (N E ⟨223338519808,8227993137⟩ E) ⟨223338519936,8034793215⟩ (N E ⟨223338520064,7841930177⟩ E)) ⟨223338520192,7649508679⟩ (N (N E ⟨223338520576,7075928778⟩ E) ⟨225486004224,7329773290⟩ E)) ⟨225620221952,7345683265⟩ (N (N (N E ⟨226828181504,7488662772⟩ E) ⟨228975665152,7739906568⟩ (N E ⟨229244100608,7770860326⟩ E)) ⟨229512536064,7801683290⟩ (N (N E ⟨230988931072,7968473783⟩ E) ⟨231391584256,8013036458⟩ E))) ⟨231928455552,7442223137⟩ (N (N (N (N E ⟨231928455680,7234651425⟩ E) ⟨231928455936,6823550428⟩ (N E ⟨231928456064,6620229385⟩ E)) ⟨231928456192,6418531221⟩ (N (N E ⟨231928456320,6218556595⟩ E) ⟨231928456832,5437853764⟩ E)) ⟨231928456960,5247953102⟩ (N (N (N E ⟨231928457088,5060347058⟩ E) ⟨231928457216,4875124875⟩ E) ⟨231928457472,4512179917⟩ (N (N E ⟨231928457728,4159794995⟩ E) ⟨231928457856,3987765561⟩ E)))) ⟨231928457984,3818615749⟩ (N (N (N (N (N E ⟨231928458112,3652421196⟩ E) ⟨231928458368,3329189908⟩ (N E ⟨231928458624,3018634276⟩ E)) ⟨231928458752,2868276071⟩ (N (N E ⟨231928458880,2721281800⟩ E) ⟨231928459264,2301074089⟩ E)) ⟨231928459392,2168115445⟩ (N (N (N E ⟨231928459520,2038798994⟩ E) ⟨231928460032,1558890242⟩ (N E ⟨231928460288,1341936689⟩ E)) ⟨231928460544,1140705033⟩ (N (N E ⟨231928461056,786333379⟩ E) ⟨231928461184,707895599⟩ E))) ⟨231928461312,633556508⟩ (N (N (N (N E ⟨231928461440,563330048⟩ E) ⟨231928461568,497227664⟩ (N E ⟨231928461696,435258306⟩ E)) ⟨231928462208,228803353⟩ (N (N E ⟨231928462336,187546703⟩ E) ⟨231928463232,13897474⟩ E)) ⟨231928463360,5355706⟩ (N (N (N E ⟨232331113344,1459747535⟩ E) ⟨232599551104,154558612⟩ E) ⟨232599552000,6011301⟩ (N (N E ⟨232733766144,1817441496⟩ E) ⟨232733768960,121685537⟩ E))))) ⟨232867986688,122373632⟩ (N (N (N (N (N (N E ⟨232867986816,92735134⟩ E) ⟨232867987200,28584681⟩ (N E ⟨233002203136,650034288⟩ E)) ⟨233136420736,727824318⟩ (N (N E ⟨233539073280,1177504977⟩ E) ⟨233941728768,70917365⟩ E)) ⟨234075944704,823388355⟩ (N (N (N E ⟨234075945472,399928575⟩ E) ⟨234478599040,247865528⟩ (N E ⟨234612816384,405010027⟩ E)) ⟨234612817280,99756767⟩ (N (N E ⟨234612817920,7880369⟩ E) ⟨234747034368,297596405⟩ E))) ⟨234747035264,50845870⟩ (N (N (N (N E ⟨234881251840,407459510⟩ E) ⟨234881252096,298579292⟩ (N E ⟨234881253376,8109089⟩ E)) ⟨235418124288,8546097⟩ (N (N E ⟨235552341376,103048563⟩ E) ⟨235686559360,52987042⟩ E)) ⟨235820777088,53270739⟩ (N (N (N E ⟨235820777472,8853908⟩ E) ⟨236357648384,9234561⟩ E) ⟨236491866112,9324023⟩ (N (N E ⟨236894519168,20607884⟩ E) ⟨237297171968,79892391⟩ E)))) ⟨237297172480,9808813⟩ (N (N (N (N (N E ⟨238102478848,10197208⟩ E) ⟨240518398080,3268915⟩ (N E ⟨240518398208,118725⟩ E)) ⟨240921053056,1215488⟩ (N (N E ⟨240921053184,1212798⟩ E) ⟨240921053312,1210116⟩ E)) ⟨240921053440,1207441⟩ (N (N (N E ⟨240921053568,1204774⟩ E) ⟨240921053696,1202114⟩ E) ⟨240921053824,1199461⟩ (N (N E ⟨240921053952,1196816⟩ E) ⟨240921054080,1194177⟩ E))) ⟨240921054208,1191547⟩ (N (N (N (N E ⟨240921054336,1188923⟩ E) ⟨240921054464,1186307⟩ (N E ⟨240921054592,1183697⟩ E)) ⟨240921054720,1181096⟩ (N (N E ⟨240921054848,1178501⟩ E) ⟨240921054976,1175913⟩ E)) ⟨240921055104,1173332⟩ (N (N (N E ⟨240921055232,1170759⟩ E) ⟨240921055360,1168192⟩ E) ⟨240921055488,1165633⟩ (N (N E ⟨240921055616,1163080⟩ E) ⟨240921055872,1157996⟩ E)))))) ⟨240921056000,1155465⟩ (N (N (N (N (N (N (N E ⟨240921056128,1152940⟩ E) ⟨240921056256,1150422⟩ (N E ⟨240921056384,1147911⟩ E)) ⟨240921056512,1145407⟩ (N (N E ⟨240921056640,1142910⟩ E) ⟨240921056768,1140420⟩ E)) ⟨240921057024,1135459⟩ (N (N (N E ⟨240921057152,1132989⟩ E) ⟨240921057280,1130526⟩ (N E ⟨240921057408,1128069⟩ E)) ⟨240921057536,1125619⟩ (N (N E ⟨240921057664,1123175⟩ E) ⟨240921057792,1120739⟩ E))) ⟨240921057920,1118308⟩ (N (N (N (N E ⟨240921058048,1115885⟩ E) ⟨240921058176,1113468⟩ (N E ⟨240921058304,1111057⟩ E)) ⟨240921058560,1106256⟩ (N (N E ⟨240921058944,1099102⟩ E) ⟨240921059072,1096731⟩ E)) ⟨240921059328,1092006⟩ (N (N (N E ⟨241055270912,6467986⟩ E) ⟨241055271040,6453681⟩ E) ⟨241055271168,6439416⟩ (N (N E ⟨241055271296,6425191⟩ E) ⟨241055271424,6411004⟩ E)))) ⟨241055271552,6396857⟩ (N (N (N (N (N E ⟨241055271680,6382749⟩ E) ⟨241055271808,6368680⟩ (N E ⟨241055271936,6354650⟩ E)) ⟨241055272064,6340658⟩ (N (N E ⟨241055272192,6326704⟩ E) ⟨241055272320,6312789⟩ E)) ⟨241055272448,6298913⟩ (N (N (N E ⟨241055272576,6285074⟩ E) ⟨241055272704,6271273⟩ E) ⟨241055272832,6257511⟩ (N (N E ⟨241055272960,6243786⟩ E) ⟨241055273088,6230098⟩ E))) ⟨241055273216,6216448⟩ (N (N (N (N E ⟨241055273344,6202836⟩ E) ⟨241055273472,6189260⟩ (N E ⟨241055273600,6175722⟩ E)) ⟨241055273728,6162221⟩ (N (N E ⟨241055273856,6148757⟩ E) ⟨241055273984,6135329⟩ E)) ⟨241055274112,6121938⟩ (N (N (N E ⟨241055274240,6108584⟩ E) ⟨241055274368,6095266⟩ E) ⟨241055274496,6081984⟩ (N (N E ⟨241055274624,6068739⟩ E) ⟨241055274752,6055529⟩ E))))) ⟨241055274880,6042356⟩ (N (N (N (N (N (N E ⟨241055275136,6016116⟩ E) ⟨241055275264,6003050⟩ (N E ⟨241055275392,5990019⟩ E)) ⟨241055275520,5977023⟩ (N (N E ⟨241055275648,5964063⟩ E) ⟨241055275776,5951137⟩ E)) ⟨241055275904,5938247⟩ (N (N (N E ⟨241055276032,5925392⟩ E) ⟨241055276160,5912571⟩ (N E ⟨241055276672,5861634⟩ E)) ⟨241055276800,5848985⟩ (N (N E ⟨241055276928,5836371⟩ E) ⟨241055277056,5823791⟩ E))) ⟨241189488768,15856187⟩ (N (N (N (N E ⟨241189488896,15821140⟩ E) ⟨241189489024,15786189⟩ (N E ⟨241189489152,15751334⟩ E)) ⟨241189489280,15716576⟩ (N (N E ⟨241189489408,15681913⟩ E) ⟨241189489536,15647347⟩ E)) ⟨241189489664,15612875⟩ (N (N (N E ⟨241189489792,15578498⟩ E) ⟨241189489920,15544216⟩ E) ⟨241189490048,15510028⟩ (N (N E ⟨241189490176,15475934⟩ E) ⟨241189490304,15441933⟩ E)))) ⟨241189490432,15408026⟩ (N (N (N (N (N E ⟨241189490560,15374212⟩ E) ⟨241189490688,15340491⟩ (N E ⟨241189490816,15306862⟩ E)) ⟨241189490944,15273325⟩ (N (N E ⟨241189491072,15239880⟩ E) ⟨241189491200,15206527⟩ E)) ⟨241189491328,15173265⟩ (N (N (N E ⟨241189491456,15140093⟩ E) ⟨241189491584,15107013⟩ E) ⟨241189491968,15008311⟩ (N (N E ⟨241189492096,14975590⟩ E) ⟨241189492224,14942958⟩ E))) ⟨241189492352,14910415⟩ (N (N (N (N E ⟨241189492480,14877960⟩ E) ⟨241189492608,14845594⟩ (N E ⟨241189492736,14813316⟩ E)) ⟨241189492864,14781125⟩ (N (N E ⟨241189492992,14749022⟩ E) ⟨241189493120,14717005⟩ E)) ⟨241189493248,14685076⟩ (N (N (N E ⟨241189493376,14653233⟩ E) ⟨241189493504,14621477⟩ E) ⟨241189493632,14589807⟩ (N (N E ⟨241189494016,14495308⟩ E) ⟨241189494144,14463979⟩ E)))))))

noncomputable def tab23 : CTN :=
  (N (N (N (N (N (N (N (N E ⟨241189494784,14308597⟩ E) ⟨241323706624,29360747⟩ (N E ⟨241323706752,29295886⟩ E)) ⟨241323706880,29231203⟩ (N (N E ⟨241323707008,29166699⟩ E) ⟨241323707136,29102372⟩ E)) ⟨241323707264,29038223⟩ (N (N (N E ⟨241323707392,28974251⟩ E) ⟨241323707520,28910455⟩ (N E ⟨241323707648,28846834⟩ E)) ⟨241323707776,28783388⟩ (N (N E ⟨241323707904,28720116⟩ E) ⟨241323708032,28657019⟩ E))) ⟨241323708160,28594094⟩ (N (N (N (N E ⟨241323708288,28531343⟩ E) ⟨241323708416,28468763⟩ (N E ⟨241323708544,28406355⟩ E)) ⟨241323708672,28344117⟩ (N (N E ⟨241323708800,28282051⟩ E) ⟨241323708928,28220154⟩ E)) ⟨241323709056,28158426⟩ (N (N (N E ⟨241323709184,28096867⟩ E) ⟨241323709312,28035476⟩ E) ⟨241323709568,27913196⟩ (N (N E ⟨241323709696,27852307⟩ E) ⟨241323709824,27791583⟩ E)))) ⟨241323709952,27731025⟩ (N (N (N (N (N E ⟨241323710080,27670631⟩ E) ⟨241323710208,27610402⟩ (N E ⟨241323710336,27550337⟩ E)) ⟨241323710464,27490435⟩ (N (N E ⟨241323710592,27430696⟩ E) ⟨241323710848,27311704⟩ E)) ⟨241323710976,27252450⟩ (N (N (N E ⟨241323711104,27193356⟩ E) ⟨241323711232,27134423⟩ (N E ⟨241323711360,27075649⟩ E)) ⟨241323711488,27017034⟩ (N (N E ⟨241323711616,26958578⟩ E) ⟨241323711744,26900280⟩ E))) ⟨241323711872,26842139⟩ (N (N (N (N E ⟨241323712128,26726329⟩ E) ⟨241323712512,26553782⟩ (N E ⟨241457924480,46959894⟩ E)) ⟨241457924608,46856210⟩ (N (N E ⟨241457924736,46752813⟩ E) ⟨241457924864,46649701⟩ E)) ⟨241457924992,46546873⟩ (N (N (N E ⟨241457925120,46444328⟩ E) ⟨241457925248,46342066⟩ E) ⟨241457925376,46240085⟩ (N (N E ⟨241457925504,46138384⟩ E) ⟨241457925632,46036963⟩ E))))) ⟨241457925760,45935821⟩ (N (N (N (N (N (N E ⟨241457925888,45834956⟩ E) ⟨241457926016,45734368⟩ (N E ⟨241457926144,45634056⟩ E)) ⟨241457926272,45534018⟩ (N (N E ⟨241457926400,45434255⟩ E) ⟨241457926528,45334765⟩ E)) ⟨241457926656,45235547⟩ (N (N (N E ⟨241457926784,45136600⟩ E) ⟨241457926912,45037924⟩ (N E ⟨241457927040,44939517⟩ E)) ⟨241457927168,44841379⟩ (N (N E ⟨241457927296,44743509⟩ E) ⟨241457927424,44645906⟩ E))) ⟨241457927552,44548569⟩ (N (N (N (N E ⟨241457927808,44354689⟩ E) ⟨241457927936,44258145⟩ (N E ⟨241457928064,44161863⟩ E)) ⟨241457928192,44065843⟩ (N (N E ⟨241457928320,43970084⟩ E) ⟨241457928448,43874585⟩ E)) ⟨241457928576,43779346⟩ (N (N (N E ⟨241457928704,43684364⟩ E) ⟨241457928832,43589640⟩ E) ⟨241457928960,43495173⟩ (N (N E ⟨241457929088,43400961⟩ E) ⟨241457929216,43307005⟩ E)))) ⟨241457929344,43213302⟩ (N (N (N (N (N E ⟨241457929472,43119853⟩ E) ⟨241457929600,43026657⟩ (N E ⟨241457929856,42841018⟩ E)) ⟨241457929984,42748574⟩ (N (N E ⟨241457930112,42656379⟩ E) ⟨241457930240,42564433⟩ E)) ⟨241592142336,68629448⟩ (N (N (N E ⟨241592142464,68478004⟩ E) ⟨241592142592,68326977⟩ E) ⟨241592142720,68176367⟩ (N (N E ⟨241592142848,68026172⟩ E) ⟨241592142976,67876390⟩ E))) ⟨241592143104,67727020⟩ (N (N (N (N E ⟨241592143232,67578061⟩ E) ⟨241592143360,67429512⟩ (N E ⟨241592143488,67281370⟩ E)) ⟨241592143616,67133635⟩ (N (N E ⟨241592143744,66986305⟩ E) ⟨241592143872,66839380⟩ E)) ⟨241592144000,66692857⟩ (N (N (N E ⟨241592144128,66546735⟩ E) ⟨241592144256,66401014⟩ E) ⟨241592144384,66255691⟩ (N (N E ⟨241592144512,66110766⟩ E) ⟨241592144640,65966237⟩ E)))))) ⟨241592144768,65822102⟩ (N (N (N (N (N (N (N E ⟨241592144896,65678361⟩ E) ⟨241592145024,65535013⟩ (N E ⟨241592145152,65392055⟩ E)) ⟨241592145280,65249487⟩ (N (N E ⟨241592145408,65107307⟩ E) ⟨241592145536,64965515⟩ E)) ⟨241592145664,64824108⟩ (N (N (N E ⟨241592145792,64683086⟩ E) ⟨241592145920,64542448⟩ (N E ⟨241592146048,64402191⟩ E)) ⟨241592146176,64262315⟩ (N (N E ⟨241592146304,64122819⟩ E) ⟨241592146432,63983702⟩ E))) ⟨241592146560,63844961⟩ (N (N (N (N E ⟨241592146688,63706596⟩ E) ⟨241592146816,63568606⟩ (N E ⟨241592146944,63430990⟩ E)) ⟨241592147072,63293746⟩ (N (N E ⟨241592147328,63020369⟩ E) ⟨241592147456,62884235⟩ E)) ⟨241592147584,62748468⟩ (N (N (N E ⟨241592147712,62613067⟩ E) ⟨241592147968,62343359⟩ E) ⟨241726360192,94342845⟩ (N (N E ⟨241726360320,94134774⟩ E) ⟨241726360448,93927277⟩ E)))) ⟨241726360576,93720351⟩ (N (N (N (N (N E ⟨241726360704,93513995⟩ E) ⟨241726360832,93308207⟩ (N E ⟨241726360960,93102985⟩ E)) ⟨241726361088,92898326⟩ (N (N E ⟨241726361216,92694230⟩ E) ⟨241726361344,92490694⟩ E)) ⟨241726361472,92287717⟩ (N (N (N E ⟨241726361600,92085296⟩ E) ⟨241726361728,91883430⟩ E) ⟨241726361856,91682117⟩ (N (N E ⟨241726361984,91481355⟩ E) ⟨241726362112,91281142⟩ E))) ⟨241726362240,91081477⟩ (N (N (N (N E ⟨241726362368,90882357⟩ E) ⟨241726362496,90683782⟩ (N E ⟨241726362624,90485749⟩ E)) ⟨241726362880,90091302⟩ (N (N E ⟨241726363008,89894884⟩ E) ⟨241726363136,89699002⟩ E)) ⟨241726363264,89503653⟩ (N (N (N E ⟨241726363392,89308836⟩ E) ⟨241726363520,89114548⟩ E) ⟨241726363776,88727556⟩ (N (N E ⟨241726363904,88534848⟩ E) ⟨241726364032,88342663⟩ E))))) ⟨241726364160,88150999⟩ (N (N (N (N (N (N E ⟨241726364288,87959854⟩ E) ⟨241726364416,87769228⟩ (N E ⟨241726364544,87579118⟩ E)) ⟨241726364672,87389522⟩ (N (N E ⟨241726364928,87011868⟩ E) ⟨241726365056,86823806⟩ E)) ⟨241726365184,86636252⟩ (N (N (N E ⟨241726365312,86449204⟩ E) ⟨241726365440,86262661⟩ (N E ⟨241726365568,86076621⟩ E)) ⟨241726365696,85891082⟩ (N (N E ⟨241860578048,124071153⟩ E) ⟨241860578304,123524937⟩ E))) ⟨241860578432,123252957⟩ (N (N (N (N E ⟨241860578560,122981724⟩ E) ⟨241860578688,122711238⟩ (N E ⟨241860578816,122441495⟩ E)) ⟨241860578944,122172493⟩ (N (N E ⟨241860579072,121904229⟩ E) ⟨241860579200,121636702⟩ E)) ⟨241860579328,121369908⟩ (N (N (N E ⟨241860579456,121103845⟩ E) ⟨241860579584,120838511⟩ E) ⟨241860579712,120573903⟩ (N (N E ⟨241860579840,120310020⟩ E) ⟨241860579968,120046858⟩ E)))) ⟨241860580096,119784416⟩ (N (N (N (N (N E ⟨241860580224,119522690⟩ E) ⟨241860580352,119261679⟩ (N E ⟨241860580480,119001380⟩ E)) ⟨241860580608,118741791⟩ (N (N E ⟨241860580736,118482910⟩ E) ⟨241860580992,117967261⟩ E)) ⟨241860581248,117454414⟩ (N (N (N E ⟨241860581376,117199036⟩ E) ⟨241860581504,116944352⟩ E) ⟨241860581632,116690360⟩ (N (N E ⟨241860581760,116437057⟩ E) ⟨241860581888,116184441⟩ E))) ⟨241860582016,115932509⟩ (N (N (N (N E ⟨241860582144,115681261⟩ E) ⟨241860582272,115430692⟩ (N E ⟨241860582400,115180802⟩ E)) ⟨241860582528,114931588⟩ (N (N E ⟨241860582656,114683048⟩ E) ⟨241860582784,114435179⟩ E)) ⟨241860582912,114187980⟩ (N (N (N E ⟨241860583040,113941448⟩ E) ⟨241860583168,113695581⟩ E) ⟨241860583424,113205834⟩ (N (N E ⟨241994795776,158131662⟩ E) ⟨241994795904,157783099⟩ E)))))))

noncomputable def tab24 : CTN :=
  (N (N (N (N (N (N (N (N E ⟨241994796160,157088851⟩ E) ⟨241994796288,156743159⟩ (N E ⟨241994796416,156398417⟩ E)) ⟨241994796544,156054623⟩ (N (N E ⟨241994796672,155711773⟩ E) ⟨241994796800,155369865⟩ E)) ⟨241994796928,155028895⟩ (N (N (N E ⟨241994797056,154688859⟩ E) ⟨241994797184,154349756⟩ (N E ⟨241994797312,154011581⟩ E)) ⟨241994797440,153674333⟩ (N (N E ⟨241994797568,153338007⟩ E) ⟨241994797696,153002601⟩ E))) ⟨241994797824,152668112⟩ (N (N (N (N E ⟨241994797952,152334536⟩ E) ⟨241994798080,152001871⟩ (N E ⟨241994798208,151670114⟩ E)) ⟨241994798336,151339262⟩ (N (N E ⟨241994798464,151009311⟩ E) ⟨241994798592,150680260⟩ E)) ⟨241994798720,150352104⟩ (N (N (N E ⟨241994798848,150024842⟩ E) ⟨241994799104,149372984⟩ E) ⟨241994799232,149048383⟩ (N (N E ⟨241994799360,148724663⟩ E) ⟨241994799488,148401822⟩ E)))) ⟨241994799616,148079857⟩ (N (N (N (N (N E ⟨241994799744,147758765⟩ E) ⟨241994799872,147438542⟩ (N E ⟨241994800000,147119187⟩ E)) ⟨241994800128,146800696⟩ (N (N E ⟨241994800256,146483067⟩ E) ⟨241994800384,146166296⟩ E)) ⟨241994800512,145850382⟩ (N (N (N E ⟨241994800640,145535320⟩ E) ⟨241994800768,145221109⟩ (N E ⟨241994800896,144907746⟩ E)) ⟨241994801024,144595228⟩ (N (N E ⟨241994801152,144283552⟩ E) ⟨242129013632,195876612⟩ E))) ⟨242129013760,195445088⟩ (N (N (N (N E ⟨242129014016,194585599⟩ E) ⟨242129014144,194157627⟩ (N E ⟨242129014272,193730831⟩ E)) ⟨242129014400,193305207⟩ (N (N E ⟨242129014528,192880752⟩ E) ⟨242129014656,192457461⟩ E)) ⟨242129014784,192035331⟩ (N (N (N E ⟨242129014912,191614359⟩ E) ⟨242129015040,191194539⟩ E) ⟨242129015168,190775868⟩ (N (N E ⟨242129015296,190358343⟩ E) ⟨242129015424,189941960⟩ E))))) ⟨242129015552,189526715⟩ (N (N (N (N (N (N E ⟨242129015680,189112605⟩ E) ⟨242129015808,188699625⟩ (N E ⟨242129015936,188287772⟩ E)) ⟨242129016064,187877042⟩ (N (N E ⟨242129016192,187467432⟩ E) ⟨242129016320,187058937⟩ E)) ⟨242129016448,186651555⟩ (N (N (N E ⟨242129016576,186245282⟩ E) ⟨242129016704,185840113⟩ (N E ⟨242129016832,185436046⟩ E)) ⟨242129016960,185033077⟩ (N (N E ⟨242129017088,184631202⟩ E) ⟨242129017344,183830721⟩ E))) ⟨242129017472,183432107⟩ (N (N (N (N E ⟨242129017600,183034573⟩ E) ⟨242129017728,182638116⟩ (N E ⟨242129017856,182242732⟩ E)) ⟨242129017984,181848418⟩ (N (N E ⟨242129018112,181455169⟩ E) ⟨242129018368,180671857⟩ E)) ⟨242129018624,179892768⟩ (N (N (N E ⟨242129018752,179504798⟩ E) ⟨242129018880,179117874⟩ E) ⟨242263231360,238068739⟩ (N (N E ⟨242263231488,237544264⟩ E) ⟨242263231616,237021232⟩ E)))) ⟨242263231744,236499640⟩ (N (N (N (N (N E ⟨242263231872,235979482⟩ E) ⟨242263232000,235460753⟩ (N E ⟨242263232128,234943450⟩ E)) ⟨242263232256,234427566⟩ (N (N E ⟨242263232384,233913098⟩ E) ⟨242263232512,233400041⟩ E)) ⟨242263232640,232888389⟩ (N (N (N E ⟨242263232768,232378140⟩ E) ⟨242263232896,231869287⟩ E) ⟨242263233024,231361827⟩ (N (N E ⟨242263233152,230855754⟩ E) ⟨242263233280,230351065⟩ E))) ⟨242263233408,229847754⟩ (N (N (N (N E ⟨242263233536,229345818⟩ E) ⟨242263233664,228845251⟩ (N E ⟨242263233792,228346049⟩ E)) ⟨242263233920,227848208⟩ (N (N E ⟨242263234048,227351723⟩ E) ⟨242263234176,226856591⟩ E)) ⟨242263234304,226362805⟩ (N (N (N E ⟨242263234560,225379259⟩ E) ⟨242263234688,224889490⟩ E) ⟨242263234816,224401050⟩ (N (N E ⟨242263234944,223913936⟩ E) ⟨242263235072,223428144⟩ E)))))) ⟨242263235200,222943668⟩ (N (N (N (N (N (N (N E ⟨242263235328,222460505⟩ E) ⟨242263235456,221978651⟩ (N E ⟨242263235584,221498100⟩ E)) ⟨242263235712,221018850⟩ (N (N E ⟨242263235840,220540895⟩ E) ⟨242263235968,220064232⟩ E)) ⟨242263236224,219114764⟩ (N (N (N E ⟨242263236352,218641950⟩ E) ⟨242263236480,218170411⟩ (N E ⟨242263236608,217700143⟩ E)) ⟨242397449344,283096363⟩ (N (N E ⟨242397449472,282473377⟩ E) ⟨242397449600,281852104⟩ E))) ⟨242397449728,281232539⟩ (N (N (N (N E ⟨242397449856,280614675⟩ E) ⟨242397449984,279998507⟩ (N E ⟨242397450112,279384031⟩ E)) ⟨242397450240,278771239⟩ (N (N E ⟨242397450368,278160126⟩ E) ⟨242397450496,277550688⟩ E)) ⟨242397450624,276942918⟩ (N (N (N E ⟨242397450752,276336812⟩ E) ⟨242397450880,275732362⟩ E) ⟨242397451008,275129565⟩ (N (N E ⟨242397451136,274528415⟩ E) ⟨242397451264,273928906⟩ E)))) ⟨242397451392,273331032⟩ (N (N (N (N (N E ⟨242397451520,272734790⟩ E) ⟨242397451648,272140172⟩ (N E ⟨242397451776,271547175⟩ E)) ⟨242397451904,270955792⟩ (N (N E ⟨242397452032,270366018⟩ E) ⟨242397452160,269777849⟩ E)) ⟨242397452288,269191278⟩ (N (N (N E ⟨242397452416,268606301⟩ E) ⟨242397452544,268022913⟩ E) ⟨242397452672,267441108⟩ (N (N E ⟨242397452800,266860881⟩ E) ⟨242397452928,266282227⟩ E))) ⟨242397453056,265705141⟩ (N (N (N (N E ⟨242397453184,265129617⟩ E) ⟨242397453440,263983238⟩ (N E ⟨242397453568,263412373⟩ E)) ⟨242397453696,262843050⟩ (N (N E ⟨242397453824,262275265⟩ E) ⟨242397453952,261709012⟩ E)) ⟨242397454080,261144287⟩ (N (N (N E ⟨242397454208,260581085⟩ E) ⟨242397454336,260019400⟩ E) ⟨242531667072,333225713⟩ (N (N E ⟨242531667200,332492411⟩ E) ⟨242531667328,331761126⟩ E))))) ⟨242531667456,331031851⟩ (N (N (N (N (N (N E ⟨242531667584,330304579⟩ E) ⟨242531667712,329579304⟩ (N E ⟨242531667840,328856018⟩ E)) ⟨242531667968,328134716⟩ (N (N E ⟨242531668096,327415391⟩ E) ⟨242531668224,326698036⟩ E)) ⟨242531668352,325982645⟩ (N (N (N E ⟨242531668480,325269212⟩ E) ⟨242531668608,324557730⟩ (N E ⟨242531668736,323848192⟩ E)) ⟨242531668864,323140593⟩ (N (N E ⟨242531668992,322434926⟩ E) ⟨242531669120,321731184⟩ E))) ⟨242531669248,321029362⟩ (N (N (N (N E ⟨242531669376,320329452⟩ E) ⟨242531669504,319631449⟩ (N E ⟨242531669632,318935347⟩ E)) ⟨242531669760,318241139⟩ (N (N E ⟨242531669888,317548820⟩ E) ⟨242531670016,316858382⟩ E)) ⟨242531670144,316169820⟩ (N (N (N E ⟨242531670272,315483128⟩ E) ⟨242531670400,314798300⟩ E) ⟨242531670528,314115329⟩ (N (N E ⟨242531670656,313434210⟩ E) ⟨242531670784,312754936⟩ E)))) ⟨242531670912,312077501⟩ (N (N (N (N (N E ⟨242531671040,311401901⟩ E) ⟨242531671296,310056176⟩ (N E ⟨242531671424,309386040⟩ E)) ⟨242531671552,308717714⟩ (N (N E ⟨242531671680,308051192⟩ E) ⟨242531671808,307386468⟩ E)) ⟨242531671936,306723537⟩ (N (N (N E ⟨242531672064,306062392⟩ E) ⟨242665884928,386539853⟩ E) ⟨242665885056,385689695⟩ (N (N E ⟨242665885184,384841875⟩ E) ⟨242665885312,383996383⟩ E))) ⟨242665885440,383153212⟩ (N (N (N (N E ⟨242665885568,382312355⟩ E) ⟨242665885696,381473804⟩ (N E ⟨242665885824,380637550⟩ E)) ⟨242665885952,379803588⟩ (N (N E ⟨242665886080,378971909⟩ E) ⟨242665886208,378142505⟩ E)) ⟨242665886336,377315370⟩ (N (N (N E ⟨242665886464,376490495⟩ E) ⟨242665886592,375667874⟩ E) ⟨242665886720,374847499⟩ (N (N E ⟨242665886848,374029362⟩ E) ⟨242665886976,373213456⟩ E)))))))

noncomputable def tab25 : CTN :=
  (N (N (N (N (N (N (N (N E ⟨242665887232,371588310⟩ E) ⟨242665887360,370779055⟩ (N E ⟨242665887488,369972002⟩ E)) ⟨242665887616,369167144⟩ (N (N E ⟨242665887744,368364474⟩ E) ⟨242665887872,367563985⟩ E)) ⟨242665888128,365969521⟩ (N (N (N E ⟨242665888384,364383694⟩ E) ⟨242665888512,363594003⟩ (N E ⟨242665888640,362806450⟩ E)) ⟨242665888768,362021029⟩ (N (N E ⟨242665888896,361237732⟩ E) ⟨242665889024,360456553⟩ E))) ⟨242665889280,358900521⟩ (N (N (N (N E ⟨242665889408,358125654⟩ E) ⟨242665889664,356582186⟩ (N E ⟨242665889792,355813570⟩ E)) ⟨242800102784,443618477⟩ (N (N E ⟨242800102912,442643317⟩ E) ⟨242800103040,441670837⟩ E)) ⟨242800103168,440701026⟩ (N (N (N E ⟨242800103296,439733876⟩ E) ⟨242800103424,438769378⟩ E) ⟨242800103552,437807523⟩ (N (N E ⟨242800103680,436848304⟩ E) ⟨242800103808,435891710⟩ E)))) ⟨242800103936,434937734⟩ (N (N (N (N (N E ⟨242800104064,433986367⟩ E) ⟨242800104192,433037600⟩ (N E ⟨242800104320,432091425⟩ E)) ⟨242800104448,431147833⟩ (N (N E ⟨242800104576,430206816⟩ E) ⟨242800104704,429268365⟩ E)) ⟨242800104832,428332473⟩ (N (N (N E ⟨242800104960,427399130⟩ E) ⟨242800105088,426468328⟩ (N E ⟨242800105216,425540060⟩ E)) ⟨242800105344,424614316⟩ (N (N E ⟨242800105728,421852151⟩ E) ⟨242800105856,420936424⟩ E))) ⟨242800105984,420023181⟩ (N (N (N (N E ⟨242800106240,418204115⟩ E) ⟨242800106368,417298275⟩ (N E ⟨242800106624,415493943⟩ E)) ⟨242800106752,414595435⟩ (N (N E ⟨242800107136,411914446⟩ E) ⟨242800107264,411025603⟩ E)) ⟨242800107392,410139156⟩ (N (N (N E ⟨242800107520,409255098⟩ E) ⟨242934320512,505525661⟩ E) ⟨242934320640,504414417⟩ (N (N E ⟨242934320768,503306226⟩ E) ⟨242934320896,502201078⟩ E))))) ⟨242934321024,501098961⟩ (N (N (N (N (N (N E ⟨242934321152,499999867⟩ E) ⟨242934321280,498903786⟩ (N E ⟨242934321408,497810706⟩ E)) ⟨242934321536,496720620⟩ (N (N E ⟨242934321664,495633516⟩ E) ⟨242934321792,494549385⟩ E)) ⟨242934321920,493468217⟩ (N (N (N E ⟨242934322048,492390002⟩ E) ⟨242934322176,491314732⟩ (N E ⟨242934322304,490242396⟩ E)) ⟨242934322432,489172984⟩ (N (N E ⟨242934322560,488106487⟩ E) ⟨242934322688,487042896⟩ E))) ⟨242934322816,485982200⟩ (N (N (N (N E ⟨242934322944,484924391⟩ E) ⟨242934323072,483869460⟩ (N E ⟨242934323200,482817396⟩ E)) ⟨242934323328,481768190⟩ (N (N E ⟨242934323456,480721833⟩ E) ⟨242934323840,477599765⟩ E)) ⟨242934323968,476564712⟩ (N (N (N E ⟨242934324096,475532462⟩ E) ⟨242934324224,474503005⟩ E) ⟨242934324480,472452439⟩ (N (N E ⟨242934324608,471431310⟩ E) ⟨242934324736,470412939⟩ E)))) ⟨242934324864,469397317⟩ (N (N (N (N (N E ⟨242934324992,468384434⟩ E) ⟨242934325120,467374283⟩ (N E ⟨242934325248,466366854⟩ E)) ⟨243068538368,570130951⟩ (N (N E ⟨243068538496,568878382⟩ E) ⟨243068538624,567629251⟩ E)) ⟨243068538752,566383548⟩ (N (N (N E ⟨243068538880,565141261⟩ E) ⟨243068539008,563902378⟩ E) ⟨243068539136,562666890⟩ (N (N E ⟨243068539264,561434783⟩ E) ⟨243068539392,560206048⟩ E))) ⟨243068539520,558980674⟩ (N (N (N (N E ⟨243068539648,557758648⟩ E) ⟨243068539776,556539961⟩ (N E ⟨243068539904,555324601⟩ E)) ⟨243068540032,554112558⟩ (N (N E ⟨243068540160,552903820⟩ E) ⟨243068540288,551698377⟩ E)) ⟨243068540416,550496218⟩ (N (N (N E ⟨243068540544,549297333⟩ E) ⟨243068540672,548101709⟩ E) ⟨243068540800,546909338⟩ (N (N E ⟨243068540928,545720208⟩ E) ⟨243068541056,544534309⟩ E)))))) ⟨243068541184,543351630⟩ (N (N (N (N (N (N (N E ⟨243068541312,542172161⟩ E) ⟨243068541440,540995891⟩ (N E ⟨243068541568,539822810⟩ E)) ⟨243068541696,538652907⟩ (N (N E ⟨243068541952,536322596⟩ E) ⟨243068542080,535162167⟩ E)) ⟨243068542208,534004875⟩ (N (N (N E ⟨243068542336,532850711⟩ E) ⟨243068542464,531699664⟩ (N E ⟨243068542592,530551723⟩ E)) ⟨243068542720,529406880⟩ (N (N E ⟨243068542848,528265124⟩ E) ⟨243068542976,527126444⟩ E))) ⟨243202756224,638360685⟩ (N (N (N (N E ⟨243202756352,636958987⟩ E) ⟨243202756480,635561135⟩ (N E ⟨243202756608,634167116⟩ E)) ⟨243202756736,632776917⟩ (N (N E ⟨243202756864,631390527⟩ E) ⟨243202756992,630007933⟩ E)) ⟨243202757120,628629121⟩ (N (N (N E ⟨243202757248,627254080⟩ E) ⟨243202757376,625882798⟩ E) ⟨243202757504,624515261⟩ (N (N E ⟨243202757632,623151458⟩ E) ⟨243202757760,621791377⟩ E)))) ⟨243202757888,620435005⟩ (N (N (N (N (N E ⟨243202758016,619082330⟩ E) ⟨243202758144,617733341⟩ (N E ⟨243202758272,616388024⟩ E)) ⟨243202758400,615046369⟩ (N (N E ⟨243202758528,613708362⟩ E) ⟨243202758656,612373993⟩ E)) ⟨243202758784,611043249⟩ (N (N (N E ⟨243202758912,609716119⟩ E) ⟨243202759040,608392590⟩ E) ⟨243202759168,607072652⟩ (N (N E ⟨243202759296,605756291⟩ E) ⟨243202759424,604443498⟩ E))) ⟨243202759552,603134259⟩ (N (N (N (N E ⟨243202759680,601828565⟩ E) ⟨243202759808,600526402⟩ (N E ⟨243202759936,599227760⟩ E)) ⟨243202760064,597932627⟩ (N (N E ⟨243202760192,596640992⟩ E) ⟨243202760320,595352843⟩ E)) ⟨243202760576,592786960⟩ (N (N (N E ⟨243202760704,591509203⟩ E) ⟨243336974208,708602796⟩ E) ⟨243336974336,707048570⟩ (N (N E ⟨243336974464,705498604⟩ E) ⟨243336974592,703952883⟩ E))))) ⟨243336974720,702411394⟩ (N (N (N (N (N (N E ⟨243336974848,700874123⟩ E) ⟨243336974976,699341056⟩ (N E ⟨243336975104,697812179⟩ E)) ⟨243336975232,696287479⟩ (N (N E ⟨243336975360,694766942⟩ E) ⟨243336975488,693250553⟩ E)) ⟨243336975616,691738301⟩ (N (N (N E ⟨243336975744,690230170⟩ E) ⟨243336975872,688726149⟩ (N E ⟨243336976000,687226222⟩ E)) ⟨243336976128,685730377⟩ (N (N E ⟨243336976256,684238601⟩ E) ⟨243336976384,682750879⟩ E))) ⟨243336976512,681267200⟩ (N (N (N (N E ⟨243336976640,679787550⟩ E) ⟨243336976768,678311915⟩ (N E ⟨243336976896,676840283⟩ E)) ⟨243336977024,675372641⟩ (N (N E ⟨243336977152,673908975⟩ E) ⟨243336977280,672449272⟩ E)) ⟨243336977792,666649844⟩ (N (N (N E ⟨243336978048,663773579⟩ E) ⟨243336978176,662341265⟩ E) ⟨243336978304,660912813⟩ (N (N E ⟨243336978432,659488210⟩ E) ⟨243471192192,782036235⟩ E)))) ⟨243471192320,780322823⟩ (N (N (N (N (N E ⟨243471192448,778614103⟩ E) ⟨243471192576,776910057⟩ (N E ⟨243471192704,775210672⟩ E)) ⟨243471192832,773515932⟩ (N (N E ⟨243471192960,771825821⟩ E) ⟨243471193088,770140324⟩ E)) ⟨243471193216,768459427⟩ (N (N (N E ⟨243471193344,766783115⟩ E) ⟨243471193472,765111371⟩ E) ⟨243471193600,763444182⟩ (N (N E ⟨243471193728,761781532⟩ E) ⟨243471193856,760123407⟩ E))) ⟨243471193984,758469792⟩ (N (N (N (N E ⟨243471194112,756820672⟩ E) ⟨243471194240,755176033⟩ (N E ⟨243471194368,753535859⟩ E)) ⟨243471194496,751900137⟩ (N (N E ⟨243471194624,750268851⟩ E) ⟨243471194752,748641988⟩ E)) ⟨243471194880,747019533⟩ (N (N (N E ⟨243471195008,745401472⟩ E) ⟨243471195136,743787790⟩ E) ⟨243471195264,742178473⟩ (N (N E ⟨243471195520,738972879⟩ E) ⟨243471195648,737376573⟩ E)))))))

noncomputable def tab26 : CTN :=
  (N (N (N (N (N (N (N (N E ⟨243471195904,734196874⟩ E) ⟨243471196032,732613453⟩ (N E ⟨243471196160,731034299⟩ E)) ⟨243605410048,860466832⟩ (N (N E ⟨243605410304,856703554⟩ E) ⟨243605410432,854829631⟩ E)) ⟨243605410560,852960830⟩ (N (N (N E ⟨243605410688,851097135⟩ E) ⟨243605410816,849238527⟩ (N E ⟨243605410944,847384992⟩ E)) ⟨243605411072,845536511⟩ (N (N E ⟨243605411200,843693069⟩ E) ⟨243605411328,841854649⟩ E))) ⟨243605411456,840021235⟩ (N (N (N (N E ⟨243605411584,838192811⟩ E) ⟨243605411712,836369359⟩ (N E ⟨243605411840,834550864⟩ E)) ⟨243605411968,832737310⟩ (N (N E ⟨243605412096,830928680⟩ E) ⟨243605412352,827326130⟩ E)) ⟨243605412480,825532178⟩ (N (N (N E ⟨243605412608,823743087⟩ E) ⟨243605412736,821958841⟩ E) ⟨243605412864,820179423⟩ (N (N E ⟨243605412992,818404820⟩ E) ⟨243605413120,816635014⟩ E)))) ⟨243605413504,811354230⟩ (N (N (N (N (N E ⟨243605413632,809603461⟩ E) ⟨243605413760,807857412⟩ (N E ⟨243605413888,806116070⟩ E)) ⟨243739627904,942281126⟩ (N (N E ⟨243739628032,940218885⟩ E) ⟨243739628160,938162284⟩ E)) ⟨243739628288,936111304⟩ (N (N (N E ⟨243739628416,934065926⟩ E) ⟨243739628544,932026134⟩ (N E ⟨243739628672,929991907⟩ E)) ⟨243739628800,927963228⟩ (N (N E ⟨243739628928,925940079⟩ E) ⟨243739629056,923922442⟩ E))) ⟨243739629184,921910299⟩ (N (N (N (N E ⟨243739629312,919903631⟩ E) ⟨243739629440,917902421⟩ (N E ⟨243739629568,915906651⟩ E)) ⟨243739629696,913916303⟩ (N (N E ⟨243739629824,911931360⟩ E) ⟨243739629952,909951804⟩ E)) ⟨243739630080,907977617⟩ (N (N (N E ⟨243739630208,906008783⟩ E) ⟨243739630336,904045283⟩ E) ⟨243739630464,902087100⟩ (N (N E ⟨243739630592,900134217⟩ E) ⟨243739630720,898186617⟩ E))))) ⟨243739630976,894307197⟩ (N (N (N (N (N (N E ⟨243739631104,892375343⟩ E) ⟨243739631232,890448704⟩ (N E ⟨243739631360,888527262⟩ E)) ⟨243739631488,886611001⟩ (N (N E ⟨243739631616,884699904⟩ E) ⟨243873845888,1025170644⟩ E)) ⟨243873846016,1022929449⟩ (N (N (N E ⟨243873846144,1020694377⟩ E) ⟨243873846272,1018465407⟩ (N E ⟨243873846528,1014025694⟩ E)) ⟨243873846656,1011814911⟩ (N (N E ⟨243873846784,1009610151⟩ E) ⟨243873846912,1007411394⟩ E))) ⟨243873847040,1005218621⟩ (N (N (N (N E ⟨243873847168,1003031812⟩ E) ⟨243873847296,1000850948⟩ (N E ⟨243873847552,996506975⟩ E)) ⟨243873847680,994343828⟩ (N (N E ⟨243873847936,990035118⟩ E) ⟨243873848192,985749725⟩ E)) ⟨243873848320,983615725⟩ (N (N (N E ⟨243873848576,979365025⟩ E) ⟨243873848704,977248288⟩ E) ⟨243873848832,975137267⟩ (N (N E ⟨243873848960,973031944⟩ E) ⟨243873849216,968838320⟩ E)))) ⟨243873849344,966749982⟩ (N (N (N (N (N E ⟨244008064000,1108516306⟩ E) ⟨244008064128,1106096874⟩ (N E ⟨244008064384,1101277785⟩ E)) ⟨244008064512,1098878084⟩ (N (N E ⟨244008064640,1096484917⟩ E) ⟨244008064768,1094098263⟩ E)) ⟨244008064896,1091718100⟩ (N (N (N E ⟨244008065152,1086977164⟩ E) ⟨244008065280,1084616349⟩ E) ⟨244008065408,1082261940⟩ (N (N E ⟨244008065664,1077572261⟩ E) ⟨244008065792,1075236949⟩ E))) ⟨244008066176,1068268877⟩ (N (N (N (N E ⟨244008066304,1065958738⟩ E) ⟨244008066560,1061357169⟩ (N E ⟨244008067072,1052228295⟩ E)) ⟨244142281984,1196896132⟩ (N (N E ⟨244142282112,1194286654⟩ E) ⟨244142282368,1189089003⟩ E)) ⟨244142282496,1186500783⟩ (N (N (N E ⟨244142282752,1181345439⟩ E) ⟨244142283008,1176218070⟩ E) ⟨244142283264,1171118493⟩ (N (N E ⟨244142283392,1168579071⟩ E) ⟨244142283520,1166046529⟩ E)))))) ⟨244142283648,1163520846⟩ (N (N (N (N (N (N (N E ⟨244142283904,1158489965⟩ E) ⟨244142284032,1155984723⟩ (N E ⟨244142284288,1150994526⟩ E)) ⟨244142284416,1148509528⟩ (N (N E ⟨244142284544,1146031233⟩ E) ⟨244142284800,1141094669⟩ E)) ⟨244276500480,1276810226⟩ (N (N (N E ⟨244276500608,1274035603⟩ E) ⟨244276500992,1265756839⟩ (N E ⟨244276501248,1260275008⟩ E)) ⟨244276501504,1254822828⟩ (N (N E ⟨244276501632,1252107796⟩ E) ⟨244276501888,1246699731⟩ E))) ⟨244276502016,1244006650⟩ (N (N (N (N E ⟨244276502144,1241320838⟩ E) ⟨244276502400,1235970928⟩ (N E ⟨244276502528,1233306783⟩ E)) ⟨244410718464,1369721862⟩ (N (N E ⟨244410718848,1360826145⟩ E) ⟨244410718976,1357876966⟩ E)) ⟨244410719488,1346159857⟩ (N (N (N E ⟨244410720128,1331690657⟩ E) ⟨244410720256,1328820187⟩ E) ⟨244544937344,1443091055⟩ (N (N E ⟨244544937984,1427588329⟩ E) ⟨244679155584,1532866682⟩ E)))) ⟨244679155712,1529562576⟩ (N (N (N (N (N E ⟨244813373440,1634692240⟩ E) ⟨244947591168,1742924605⟩ (N E ⟨245081808896,1854204952⟩ E)) ⟨245216026624,1968476591⟩ (N (N E ⟨245350244352,2085680892⟩ E) ⟨245484462080,2205757314⟩ E)) ⟨245618679808,2328643438⟩ (N (N (N E ⟨245752897536,2454275003⟩ E) ⟨245887115264,2582585939⟩ E) ⟨246021332992,2713508404⟩ (N (N E ⟨246155550720,2846972824⟩ E) ⟨246289768448,2982907926⟩ E))) ⟨246423986176,3121240784⟩ (N (N (N (N E ⟨246558203904,3261896857⟩ E) ⟨246692421632,3404800031⟩ (N E ⟨246826639360,3549872660⟩ E)) ⟨247229292544,3997308832⟩ (N (N E ⟨247766163456,4619303288⟩ E) ⟨249108340864,6252832886⟩ E)) ⟨249108340992,6239369381⟩ (N (N (N E ⟨249108341120,6225942100⟩ E) ⟨249108341248,6212550927⟩ E) ⟨249108341376,6199195745⟩ (N (N E ⟨249108341504,6185876437⟩ E) ⟨249108341632,6172592889⟩ E))))) ⟨249108341760,6159344984⟩ (N (N (N (N (N (N E ⟨249108341888,6146132609⟩ E) ⟨249108342016,6132955649⟩ (N E ⟨249108342144,6119813990⟩ E)) ⟨249108342272,6106707518⟩ (N (N E ⟨249108342400,6093636122⟩ E) ⟨249108342528,6080599687⟩ E)) ⟨249108342656,6067598102⟩ (N (N (N E ⟨249108342784,6054631256⟩ E) ⟨249108342912,6041699036⟩ (N E ⟨249108343040,6028801332⟩ E)) ⟨249108343168,6015938033⟩ (N (N E ⟨249108343296,6003109029⟩ E) ⟨249108343424,5990314211⟩ E))) ⟨249108343552,5977553470⟩ (N (N (N (N E ⟨249108343680,5964826696⟩ E) ⟨249108343808,5952133780⟩ (N E ⟨249108343936,5939474616⟩ E)) ⟨249108344064,5926849095⟩ (N (N E ⟨249108344192,5914257110⟩ E) ⟨249108344320,5901698554⟩ E)) ⟨249108344448,5889173320⟩ (N (N (N E ⟨249108344576,5876681304⟩ E) ⟨249108344704,5864222398⟩ E) ⟨249108344832,5851796498⟩ (N (N E ⟨249108344960,5839403498⟩ E) ⟨249108345088,5827043295⟩ E)))) ⟨249108345216,5814715784⟩ (N (N (N (N (N E ⟨249108345344,5802420861⟩ E) ⟨249108345472,5790158424⟩ (N E ⟨249108345600,5777928368⟩ E)) ⟨249108345728,5765730593⟩ (N (N E ⟨249108345856,5753564994⟩ E) ⟨249108345984,5741431471⟩ E)) ⟨249108346112,5729329922⟩ (N (N (N E ⟨249108346240,5717260246⟩ E) ⟨249108346368,5705222343⟩ E) ⟨249108346496,5693216111⟩ (N (N E ⟨249108346624,5681241451⟩ E) ⟨249108346752,5669298264⟩ E))) ⟨249108346880,5657386450⟩ (N (N (N (N E ⟨249108347008,5645505910⟩ E) ⟨249108347264,5621838259⟩ (N E ⟨249108347392,5610050953⟩ E)) ⟨249108347520,5598294529⟩ (N (N E ⟨249108347648,5586568890⟩ E) ⟨249108347776,5574873941⟩ E)) ⟨249108347904,5563209583⟩ (N (N (N E ⟨249108348032,5551575722⟩ E) ⟨249108348160,5539972262⟩ E) ⟨249108348288,5528399107⟩ (N (N E ⟨249108348416,5516856162⟩ E) ⟨249108348544,5505343334⟩ E)))))))

noncomputable def tab27 : CTN :=
  (N (N (N (N (N (N (N (N E ⟨249108348800,5482407647⟩ E) ⟨249108348928,5470984602⟩ (N E ⟨250182090752,6660691590⟩ E)) ⟨250987397120,7547166973⟩ (N (N E ⟨253940187136,10439771379⟩ E) ⟨257698283648,12328914849⟩ E)) ⟨257698283776,12297695318⟩ (N (N (N E ⟨257698283904,12262871751⟩ E) ⟨257698284160,12182527748⟩ (N E ⟨257698284288,12137070023⟩ E)) ⟨257698284416,12088133631⟩ (N (N E ⟨257698284544,12035754896⟩ E) ⟨257698284672,11979972077⟩ E))) ⟨257698284800,11920825333⟩ (N (N (N (N E ⟨257698284928,11858356700⟩ E) ⟨257698285056,11792610047⟩ (N E ⟨257698285184,11723631051⟩ E)) ⟨257698285312,11651467159⟩ (N (N E ⟨257698285440,11576167549⟩ E) ⟨257698285568,11497783098⟩ E)) ⟨257698285824,11331971444⟩ (N (N (N E ⟨257698285952,11244654140⟩ E) ⟨257698286080,11154471714⟩ E) ⟨257698286208,11061482951⟩ (N (N E ⟨257698286336,10965748097⟩ E) ⟨257698286464,10867328815⟩ E)))) ⟨257698286592,10766288143⟩ (N (N (N (N (N E ⟨257698286720,10662690453⟩ E) ⟨257698286976,10448087897⟩ (N E ⟨257698287104,10337218034⟩ E)) ⟨257698287232,10224061067⟩ (N (N E ⟨257698287360,10108687356⟩ E) ⟨257698287488,9991168320⟩ E)) ⟨257698287616,9871576391⟩ (N (N (N E ⟨257698287744,9749984964⟩ E) ⟨257698287872,9626468354⟩ (N E ⟨257698288000,9501101744⟩ E)) ⟨257698288384,9114665747⟩ (N (N E ⟨257698288640,8849204752⟩ E) ⟨257698289024,8440838759⟩ E))) ⟨257698289152,8302324476⟩ (N (N (N (N E ⟨257698289280,8162748999⟩ E) ⟨257698289408,8022193814⟩ (N E ⟨257698289536,7880740680⟩ E)) ⟨257698289664,7738471579⟩ (N (N E ⟨257698289792,7595468668⟩ E) ⟨257698290048,7307590603⟩ E)) ⟨257698290176,7162880181⟩ (N (N (N E ⟨257698290304,7017765309⟩ E) ⟨257698290432,6872328267⟩ E) ⟨257698290560,6726651207⟩ (N (N E ⟨257698290688,6580816113⟩ E) ⟨257698290816,6434904745⟩ E))))) ⟨257698290944,6288998599⟩ (N (N (N (N (N (N E ⟨257698291072,6143178849⟩ E) ⟨257698291200,5997526311⟩ (N E ⟨257698291328,5852121386⟩ E)) ⟨257698291712,5418189199⟩ (N (N E ⟨260114210816,5607512166⟩ E) ⟨260651081728,5649592974⟩ E)) ⟨262530129920,5795757696⟩ (N (N (N E ⟨265617137664,6027753152⟩ E) ⟨266288226560,5761840971⟩ (N E ⟨266288226688,5605762311⟩ E)) ⟨266288226816,5450507304⟩ (N (N E ⟨266288226944,5296157293⟩ E) ⟨266288227072,5142792756⟩ E))) ⟨266288227328,4839337425⟩ (N (N (N (N E ⟨266288227584,4540766178⟩ E) ⟨266288227968,4103392706⟩ (N E ⟨266288228480,3542846008⟩ E)) ⟨266288228608,3407211498⟩ (N (N E ⟨266288228736,3273510876⟩ E) ⟨266288228864,3141808217⟩ E)) ⟨266288228992,3012166152⟩ (N (N (N E ⟨266288229120,2884645835⟩ E) ⟨266288229248,2759306914⟩ E) ⟨266288230016,2056225992⟩ (N (N E ⟨266288230144,1947694536⟩ E) ⟨266288230400,1738479639⟩ E)))) ⟨266288231168,1176628374⟩ (N (N (N (N (N E ⟨266288231552,934512692⟩ E) ⟨266288231680,859762868⟩ (N E ⟨266288231936,719347841⟩ E)) ⟨266288232064,653726513⟩ (N (N E ⟨266288232192,591188723⟩ E) ⟨266288232448,475430545⟩ E)) ⟨266288232960,281544275⟩ (N (N (N E ⟨266288233856,64007355⟩ E) ⟨266288233984,45574600⟩ E) ⟨266288234240,18122334⟩ (N (N E ⟨266288234496,3137894⟩ E) ⟨266825105024,31310444⟩ E))) ⟨267361975424,114604019⟩ (N (N (N (N E ⟨267630411648,10388162⟩ E) ⟨269106806784,4684556⟩ (N E ⟨275146606592,2966⟩ E)) ⟨275146606848,2954⟩ (N (N E ⟨275146606976,2949⟩ E) ⟨275146607104,2943⟩ E)) ⟨275146607232,2937⟩ (N (N (N E ⟨275146607360,2931⟩ E) ⟨275146607488,2926⟩ E) ⟨275146607616,2920⟩ (N (N E ⟨275146607744,2915⟩ E) ⟨275146607872,2909⟩ E)))))) ⟨275146608000,2903⟩ (N (N (N (N (N (N (N E ⟨275146608128,2898⟩ E) ⟨275146608256,2892⟩ (N E ⟨275146608384,2887⟩ E)) ⟨275146608512,2881⟩ (N (N E ⟨275146608640,2875⟩ E) ⟨275146608768,2870⟩ E)) ⟨275146608896,2864⟩ (N (N (N E ⟨275146609024,2859⟩ E) ⟨275146609152,2853⟩ (N E ⟨275146609408,2842⟩ E)) ⟨275146609536,2837⟩ (N (N E ⟨275146610048,2815⟩ E) ⟨275146610176,2810⟩ E))) ⟨275146610304,2805⟩ (N (N (N (N E ⟨275146610432,2799⟩ E) ⟨275146610688,2789⟩ (N E ⟨275146610816,2783⟩ E)) ⟨275146610944,2778⟩ (N (N E ⟨275146611072,2773⟩ E) ⟨275146611200,2767⟩ E)) ⟨275146611456,2757⟩ (N (N (N E ⟨275146612736,2705⟩ E) ⟨275280824448,1730703⟩ E) ⟨275280824576,1727352⟩ (N (N E ⟨275280824704,1724009⟩ E) ⟨275280824832,1720674⟩ E)))) ⟨275280824960,1717348⟩ (N (N (N (N (N E ⟨275280825088,1714029⟩ E) ⟨275280825216,1710718⟩ (N E ⟨275280825344,1707415⟩ E)) ⟨275280825472,1704121⟩ (N (N E ⟨275280825600,1700834⟩ E) ⟨275280825728,1697555⟩ E)) ⟨275280825856,1694284⟩ (N (N (N E ⟨275280825984,1691021⟩ E) ⟨275280826112,1687766⟩ E) ⟨275280826240,1684518⟩ (N (N E ⟨275280826368,1681279⟩ E) ⟨275280826496,1678047⟩ E))) ⟨275280826624,1674823⟩ (N (N (N (N E ⟨275280826752,1671606⟩ E) ⟨275280826880,1668398⟩ (N E ⟨275280827008,1665197⟩ E)) ⟨275280827264,1658818⟩ (N (N E ⟨275280827392,1655640⟩ E) ⟨275280827520,1652470⟩ E)) ⟨275280827648,1649307⟩ (N (N (N E ⟨275280827776,1646152⟩ E) ⟨275280827904,1643004⟩ E) ⟨275280828032,1639864⟩ (N (N E ⟨275280828416,1630489⟩ E) ⟨275280828544,1627378⟩ E))))) ⟨275280828928,1618092⟩ (N (N (N (N (N (N E ⟨275280829056,1615011⟩ E) ⟨275280829696,1599717⟩ (N E ⟨275280830080,1590628⟩ E)) ⟨275280830336,1584604⟩ (N (N E ⟨275280830464,1581602⟩ E) ⟨275415042304,6631892⟩ E)) ⟨275415042432,6619058⟩ (N (N (N E ⟨275415042560,6606254⟩ E) ⟨275415042688,6593482⟩ (N E ⟨275415042816,6580740⟩ E)) ⟨275415042944,6568029⟩ (N (N E ⟨275415043200,6542699⟩ E) ⟨275415043328,6530080⟩ E))) ⟨275415043456,6517492⟩ (N (N (N (N E ⟨275415043584,6504933⟩ E) ⟨275415043712,6492405⟩ (N E ⟨275415043840,6479907⟩ E)) ⟨275415043968,6467439⟩ (N (N E ⟨275415044096,6455001⟩ E) ⟨275415044224,6442593⟩ E)) ⟨275415044352,6430215⟩ (N (N (N E ⟨275415044480,6417866⟩ E) ⟨275415044608,6405547⟩ E) ⟨275415044736,6393258⟩ (N (N E ⟨275415044992,6368768⟩ E) ⟨275415045120,6356566⟩ E)))) ⟨275415045248,6344394⟩ (N (N (N (N (N E ⟨275415045376,6332251⟩ E) ⟨275415045632,6308053⟩ (N E ⟨275415045760,6295997⟩ E)) ⟨275415046016,6271971⟩ (N (N E ⟨275415046272,6248060⟩ E) ⟨275415046400,6236147⟩ E)) ⟨275415046784,6200578⟩ (N (N (N E ⟨275415046912,6188778⟩ E) ⟨275415047040,6177006⟩ E) ⟨275415047296,6153547⟩ (N (N E ⟨275415047552,6130198⟩ E) ⟨275415047936,6095383⟩ E))) ⟨275415048192,6072310⟩ (N (N (N (N E ⟨275549260032,14722893⟩ E) ⟨275549260160,14694400⟩ (N E ⟨275549260288,14665976⟩ E)) ⟨275549260416,14637621⟩ (N (N E ⟨275549260544,14609334⟩ E) ⟨275549260672,14581116⟩ E)) ⟨275549260800,14552966⟩ (N (N (N E ⟨275549260928,14524883⟩ E) ⟨275549261056,14496869⟩ E) ⟨275549261184,14468922⟩ (N (N E ⟨275549261312,14441042⟩ E) ⟨275549261440,14413229⟩ E)))))))

noncomputable def tab28 : CTN :=
  (N (N (N (N (N (N (N (N E ⟨275549261696,14357804⟩ E) ⟨275549261824,14330192⟩ (N E ⟨275549261952,14302646⟩ E)) ⟨275549262080,14275166⟩ (N (N E ⟨275549262208,14247752⟩ E) ⟨275549262336,14220404⟩ E)) ⟨275549262464,14193121⟩ (N (N (N E ⟨275549262592,14165904⟩ E) ⟨275549262720,14138752⟩ (N E ⟨275549263104,14057686⟩ E)) ⟨275549263360,14003964⟩ (N (N E ⟨275549263488,13977200⟩ E) ⟨275549263616,13950499⟩ E))) ⟨275549263744,13923862⟩ (N (N (N (N E ⟨275549264000,13870779⟩ E) ⟨275549264128,13844332⟩ (N E ⟨275549264256,13817949⟩ E)) ⟨275549264384,13791628⟩ (N (N E ⟨275549264512,13765369⟩ E) ⟨275549264640,13739174⟩ E)) ⟨275549264896,13686969⟩ (N (N (N E ⟨275549265024,13660959⟩ E) ⟨275549265152,13635012⟩ E) ⟨275549265280,13609125⟩ (N (N E ⟨275549265408,13583301⟩ E) ⟨275549265664,13531835⟩ E)))) ⟨275549265792,13506193⟩ (N (N (N (N (N E ⟨275549265920,13480613⟩ E) ⟨275683477760,26004749⟩ (N E ⟨275683478144,25854136⟩ E)) ⟨275683478272,25804173⟩ (N (N E ⟨275683478400,25754332⟩ E) ⟨275683478528,25704611⟩ E)) ⟨275683478656,25655009⟩ (N (N (N E ⟨275683478784,25605528⟩ E) ⟨275683478912,25556165⟩ (N E ⟨275683479040,25506922⟩ E)) ⟨275683479168,25457797⟩ (N (N E ⟨275683479296,25408790⟩ E) ⟨275683479424,25359901⟩ E))) ⟨275683479552,25311130⟩ (N (N (N (N E ⟨275683479680,25262476⟩ E) ⟨275683479808,25213939⟩ (N E ⟨275683479936,25165518⟩ E)) ⟨275683480064,25117213⟩ (N (N E ⟨275683480192,25069025⟩ E) ⟨275683480320,25020952⟩ E)) ⟨275683480448,24972994⟩ (N (N (N E ⟨275683480576,24925151⟩ E) ⟨275683480704,24877422⟩ E) ⟨275683480832,24829808⟩ (N (N E ⟨275683480960,24782307⟩ E) ⟨275683481088,24734921⟩ E))))) ⟨275683481472,24593438⟩ (N (N (N (N (N (N E ⟨275683481600,24546502⟩ E) ⟨275683481728,24499678⟩ (N E ⟨275683481856,24452966⟩ E)) ⟨275683481984,24406365⟩ (N (N E ⟨275683482112,24359874⟩ E) ⟨275683482240,24313495⟩ E)) ⟨275683482496,24221067⟩ (N (N (N E ⟨275683482624,24175018⟩ E) ⟨275683482880,24083247⟩ (N E ⟨275683483008,24037525⟩ E)) ⟨275683483392,23901008⟩ (N (N E ⟨275683483648,23810535⟩ E) ⟨275817695872,40245479⟩ E))) ⟨275817696000,40167706⟩ (N (N (N (N E ⟨275817696128,40090121⟩ E) ⟨275817696256,40012723⟩ (N E ⟨275817696384,39935512⟩ E)) ⟨275817696512,39858487⟩ (N (N E ⟨275817696640,39781648⟩ E) ⟨275817696768,39704993⟩ E)) ⟨275817696896,39628524⟩ (N (N (N E ⟨275817697024,39552238⟩ E) ⟨275817697152,39476136⟩ E) ⟨275817697280,39400217⟩ (N (N E ⟨275817697408,39324480⟩ E) ⟨275817697536,39248925⟩ E)))) ⟨275817697664,39173552⟩ (N (N (N (N (N E ⟨275817697792,39098359⟩ E) ⟨275817698048,38948515⟩ (N E ⟨275817698176,38873862⟩ E)) ⟨275817698304,38799388⟩ (N (N E ⟨275817698432,38725092⟩ E) ⟨275817698560,38650974⟩ E)) ⟨275817698816,38503269⟩ (N (N (N E ⟨275817698944,38429681⟩ E) ⟨275817699072,38356269⟩ E) ⟨275817699200,38283032⟩ (N (N E ⟨275817699584,38064368⟩ E) ⟨275817699712,37991827⟩ E))) ⟨275817699968,37847263⟩ (N (N (N (N E ⟨275817700224,37703386⟩ E) ⟨275817700352,37631703⟩ (N E ⟨275817700480,37560192⟩ E)) ⟨275817700608,37488850⟩ (N (N E ⟨275817700736,37417677⟩ E) ⟨275817701248,37134670⟩ E)) ⟨275817701376,37064337⟩ (N (N (N E ⟨275951913344,58036435⟩ E) ⟨275951913472,57924173⟩ E) ⟨275951913728,57700463⟩ (N (N E ⟨275951913984,57477832⟩ E) ⟨275951914112,57366919⟩ E)))))) ⟨275951914240,57256273⟩ (N (N (N (N (N (N (N E ⟨275951914368,57145894⟩ E) ⟨275951914496,57035781⟩ (N E ⟨275951914624,56925933⟩ E)) ⟨275951914880,56707030⟩ (N (N E ⟨275951915008,56597973⟩ E) ⟨275951915136,56489178⟩ E)) ⟨275951915264,56380645⟩ (N (N (N E ⟨275951915392,56272372⟩ E) ⟨275951915520,56164358⟩ (N E ⟨275951915648,56056604⟩ E)) ⟨275951915776,55949108⟩ (N (N E ⟨275951915904,55841870⟩ E) ⟨275951916032,55734889⟩ E))) ⟨275951916288,55521694⟩ (N (N (N (N E ⟨275951916416,55415478⟩ E) ⟨275951916544,55309517⟩ (N E ⟨275951916672,55203809⟩ E)) ⟨275951916800,55098353⟩ (N (N E ⟨275951916928,54993149⟩ E) ⟨275951917056,54888196⟩ E)) ⟨275951917184,54783494⟩ (N (N (N E ⟨275951917312,54679041⟩ E) ⟨275951917440,54574836⟩ E) ⟨275951917696,54367172⟩ (N (N E ⟨275951917824,54263710⟩ E) ⟨275951917952,54160494⟩ E)))) ⟨275951918080,54057523⟩ (N (N (N (N (N E ⟨275951918208,53954797⟩ E) ⟨275951918336,53852316⟩ (N E ⟨275951918720,53546326⟩ E)) ⟨275951919104,53242508⟩ (N (N E ⟨276086131328,78552853⟩ E) ⟨276086131584,78249618⟩ E)) ⟨276086131712,78098550⟩ (N (N (N E ⟨276086131840,77947846⟩ E) ⟨276086131968,77797505⟩ E) ⟨276086132096,77647527⟩ (N (N E ⟨276086132224,77497910⟩ E) ⟨276086132352,77348653⟩ E))) ⟨276086132480,77199755⟩ (N (N (N (N E ⟨276086132608,77051216⟩ E) ⟨276086132736,76903034⟩ (N E ⟨276086132864,76755207⟩ E)) ⟨276086132992,76607736⟩ (N (N E ⟨276086133120,76460619⟩ E) ⟨276086133248,76313855⟩ E)) ⟨276086133376,76167443⟩ (N (N (N E ⟨276086133504,76021383⟩ E) ⟨276086133632,75875672⟩ E) ⟨276086133760,75730310⟩ (N (N E ⟨276086133888,75585296⟩ E) ⟨276086134016,75440629⟩ E))))) ⟨276086134144,75296308⟩ (N (N (N (N (N (N E ⟨276086134272,75152332⟩ E) ⟨276086134528,74865411⟩ (N E ⟨276086134784,74579858⟩ E)) ⟨276086134912,74437592⟩ (N (N E ⟨276086135040,74295666⟩ E) ⟨276086135168,74154077⟩ E)) ⟨276086135296,74012826⟩ (N (N (N E ⟨276086135424,73871911⟩ E) ⟨276086135680,73591086⟩ (N E ⟨276086135808,73451173⟩ E)) ⟨276086135936,73311594⟩ (N (N E ⟨276086136064,73172345⟩ E) ⟨276086136192,73033427⟩ E))) ⟨276086136320,72894839⟩ (N (N (N (N E ⟨276086136832,72343763⟩ E) ⟨276220349440,101871573⟩ (N E ⟨276220349568,101674995⟩ E)) ⟨276220349696,101478891⟩ (N (N E ⟨276220349824,101283259⟩ E) ⟨276220349952,101088099⟩ E)) ⟨276220350080,100893409⟩ (N (N (N E ⟨276220350336,100505433⟩ E) ⟨276220350464,100312144⟩ E) ⟨276220350592,100119320⟩ (N (N E ⟨276220350720,99926959⟩ E) ⟨276220350848,99735060⟩ E)))) ⟨276220350976,99543622⟩ (N (N (N (N (N E ⟨276220351104,99352642⟩ E) ⟨276220351232,99162121⟩ (N E ⟨276220351360,98972056⟩ E)) ⟨276220351488,98782446⟩ (N (N E ⟨276220351616,98593290⟩ E) ⟨276220351744,98404587⟩ E)) ⟨276220352000,98028533⟩ (N (N (N E ⟨276220352128,97841180⟩ E) ⟨276220352384,97467814⟩ E) ⟨276220352512,97281800⟩ (N (N E ⟨276220352896,96726412⟩ E) ⟨276220353152,96358355⟩ E))) ⟨276220353280,96174983⟩ (N (N (N (N E ⟨276220353408,95992047⟩ E) ⟨276220353536,95809546⟩ (N E ⟨276220353664,95627478⟩ E)) ⟨276220354048,95083865⟩ (N (N E ⟨276220354304,94723601⟩ E) ⟨276220354560,94365042⟩ E)) ⟨276354566912,129290532⟩ (N (N (N E ⟨276354567296,128543153⟩ E) ⟨276354567552,128047899⟩ E) ⟨276354567680,127801167⟩ (N (N E ⟨276354567808,127555029⟩ E) ⟨276354567936,127309483⟩ E)))))))

noncomputable def tab29 : CTN :=
  (N (N (N (N (N (N (N (N E ⟨276354568192,126820162⟩ E) ⟨276354568320,126576383⟩ (N E ⟨276354568448,126333190⟩ E)) ⟨276354568576,126090580⟩ (N (N E ⟨276354568704,125848553⟩ E) ⟨276354568832,125607106⟩ E)) ⟨276354568960,125366238⟩ (N (N (N E ⟨276354569088,125125948⟩ E) ⟨276354569216,124886232⟩ (N E ⟨276354569344,124647091⟩ E)) ⟨276354569472,124408522⟩ (N (N E ⟨276354569600,124170523⟩ E) ⟨276354569728,123933094⟩ E))) ⟨276354569856,123696232⟩ (N (N (N (N E ⟨276354569984,123459935⟩ E) ⟨276354570112,123224202⟩ (N E ⟨276354570368,122754423⟩ E)) ⟨276354570624,122286881⟩ (N (N E ⟨276354570752,122053944⟩ E) ⟨276354570880,121821562⟩ E)) ⟨276354571008,121589733⟩ (N (N (N E ⟨276354571264,121127728⟩ E) ⟨276354571392,120897548⟩ E) ⟨276354571520,120667914⟩ (N (N E ⟨276354571648,120438826⟩ E) ⟨276354571776,120210281⟩ E)))) ⟨276354571904,119982279⟩ (N (N (N (N (N E ⟨276354572288,119301506⟩ E) ⟨276488785152,158239398⟩ (N E ⟨276488785280,157934343⟩ E)) ⟨276488785408,157630024⟩ (N (N E ⟨276488785536,157326437⟩ E) ⟨276488785664,157023580⟩ E)) ⟨276488785792,156721453⟩ (N (N (N E ⟨276488785920,156420051⟩ E) ⟨276488786048,156119374⟩ (N E ⟨276488786176,155819420⟩ E)) ⟨276488786304,155520185⟩ (N (N E ⟨276488786432,155221668⟩ E) ⟨276488786560,154923868⟩ E))) ⟨276488786688,154626781⟩ (N (N (N (N E ⟨276488786816,154330407⟩ E) ⟨276488786944,154034742⟩ (N E ⟨276488787072,153739785⟩ E)) ⟨276488787200,153445533⟩ (N (N E ⟨276488787328,153151986⟩ E) ⟨276488787456,152859140⟩ E)) ⟨276488787712,152275546⟩ (N (N (N E ⟨276488787840,151984793⟩ E) ⟨276488787968,151694734⟩ E) ⟨276488788096,151405367⟩ (N (N E ⟨276488788224,151116690⟩ E) ⟨276488788352,150828700⟩ E))))) ⟨276488788608,150254776⟩ (N (N (N (N (N (N E ⟨276488788736,149968838⟩ E) ⟨276488788864,149683580⟩ (N E ⟨276488788992,149399000⟩ E)) ⟨276488789248,148831866⟩ (N (N E ⟨276488789376,148549309⟩ E) ⟨276488789504,148267421⟩ E)) ⟨276488789632,147986203⟩ (N (N (N E ⟨276488789760,147705650⟩ E) ⟨276488789888,147425763⟩ (N E ⟨276488790016,147146538⟩ E)) ⟨276623003008,190933581⟩ (N (N E ⟨276623003136,190565676⟩ E) ⟨276623003264,190198656⟩ E))) ⟨276623003392,189832521⟩ (N (N (N (N E ⟨276623003520,189467265⟩ E) ⟨276623003648,189102888⟩ (N E ⟨276623003776,188739387⟩ E)) ⟨276623003904,188376759⟩ (N (N E ⟨276623004032,188015001⟩ E) ⟨276623004160,187654112⟩ E)) ⟨276623004288,187294088⟩ (N (N (N E ⟨276623004416,186934928⟩ E) ⟨276623004544,186576628⟩ E) ⟨276623004672,186219186⟩ (N (N E ⟨276623004800,185862599⟩ E) ⟨276623004928,185506867⟩ E)))) ⟨276623005056,185151984⟩ (N (N (N (N (N E ⟨276623005184,184797951⟩ E) ⟨276623005312,184444763⟩ (N E ⟨276623005440,184092418⟩ E)) ⟨276623005568,183740915⟩ (N (N E ⟨276623005696,183390250⟩ E) ⟨276623005824,183040422⟩ E)) ⟨276623005952,182691428⟩ (N (N (N E ⟨276623006080,182343265⟩ E) ⟨276623006208,181995931⟩ E) ⟨276623006336,181649424⟩ (N (N E ⟨276623006464,181303741⟩ E) ⟨276623007104,179587611⟩ E))) ⟨276623007232,179246826⟩ (N (N (N (N E ⟨276623007616,178229308⟩ E) ⟨276623007744,177891741⟩ (N E ⟨276757220864,226597227⟩ E)) ⟨276757220992,226160813⟩ (N (N E ⟨276757221120,225725449⟩ E) ⟨276757221248,225291133⟩ E)) ⟨276757221376,224857860⟩ (N (N (N E ⟨276757221504,224425629⟩ E) ⟨276757221760,223564279⟩ E) ⟨276757222016,222707058⟩ (N (N E ⟨276757222144,222279988⟩ E) ⟨276757222272,221853942⟩ E)))))) ⟨276757222400,221428916⟩ (N (N (N (N (N (N (N E ⟨276757222528,221004908⟩ E) ⟨276757222656,220581914⟩ (N E ⟨276757222784,220159932⟩ E)) ⟨276757222912,219738959⟩ (N (N E ⟨276757223040,219318991⟩ E) ⟨276757223168,218900027⟩ E)) ⟨276757223296,218482062⟩ (N (N (N E ⟨276757223424,218065095⟩ E) ⟨276757223552,217649122⟩ (N E ⟨276757223680,217234141⟩ E)) ⟨276757223808,216820149⟩ (N (N E ⟨276757223936,216407142⟩ E) ⟨276757224064,215995118⟩ E))) ⟨276757224192,215584075⟩ (N (N (N (N E ⟨276757224320,215174009⟩ E) ⟨276757224448,214764918⟩ (N E ⟨276757224704,213949648⟩ E)) ⟨276757224960,213138244⟩ (N (N E ⟨276757225088,212733985⟩ E) ⟨276757225216,212330684⟩ E)) ⟨276757225344,211928338⟩ (N (N (N E ⟨276757225472,211526945⟩ E) ⟨276891438720,265200134⟩ E) ⟨276891438976,264180332⟩ (N (N E ⟨276891439104,263672269⟩ E) ⟨276891439232,263165428⟩ E)))) ⟨276891439360,262659804⟩ (N (N (N (N (N E ⟨276891439488,262155393⟩ E) ⟨276891439744,261150201⟩ (N E ⟨276891439872,260649411⟩ E)) ⟨276891440000,260149822⟩ (N (N E ⟨276891440128,259651429⟩ E) ⟨276891440256,259154230⟩ E)) ⟨276891440384,258658220⟩ (N (N (N E ⟨276891440512,258163396⟩ E) ⟨276891440640,257669755⟩ E) ⟨276891440768,257177294⟩ (N (N E ⟨276891440896,256686009⟩ E) ⟨276891441024,256195897⟩ E))) ⟨276891441152,255706954⟩ (N (N (N (N E ⟨276891441280,255219177⟩ E) ⟨276891441408,254732562⟩ (N E ⟨276891441536,254247107⟩ E)) ⟨276891441664,253762809⟩ (N (N E ⟨276891441792,253279663⟩ E) ⟨276891441920,252797666⟩ E)) ⟨276891442176,251837108⟩ (N (N (N E ⟨276891442304,251358540⟩ E) ⟨276891442432,250881109⟩ E) ⟨276891442688,249929642⟩ (N (N E ⟨276891442816,249455601⟩ E) ⟨276891442944,248982683⟩ E))))) ⟨276891443200,248040204⟩ (N (N (N (N (N (N E ⟨277025656576,306710395⟩ E) ⟨277025656704,306120256⟩ (N E ⟨277025656832,305531536⟩ E)) ⟨277025656960,304944231⟩ (N (N E ⟨277025657088,304358336⟩ E) ⟨277025657216,303773849⟩ E)) ⟨277025657472,302609077⟩ (N (N (N E ⟨277025657600,302028785⟩ E) ⟨277025657728,301449883⟩ (N E ⟨277025657856,300872368⟩ E)) ⟨277025657984,300296236⟩ (N (N E ⟨277025658112,299721482⟩ E) ⟨277025658240,299148102⟩ E))) ⟨277025658368,298576094⟩ (N (N (N (N E ⟨277025658496,298005452⟩ E) ⟨277025658752,296868253⟩ (N E ⟨277025658880,296301687⟩ E)) ⟨277025659008,295736473⟩ (N (N E ⟨277025659136,295172607⟩ E) ⟨277025659264,294610084⟩ E)) ⟨277025659392,294048900⟩ (N (N (N E ⟨277025659520,293489052⟩ E) ⟨277025659648,292930536⟩ E) ⟨277025660032,291262942⟩ (N (N E ⟨277025660288,290157803⟩ E) ⟨277025660672,288509905⟩ E)))) ⟨277025660800,287963208⟩ (N (N (N (N (N E ⟨277025660928,287417804⟩ E) ⟨277159874816,349073644⟩ (N E ⟨277159874944,348403285⟩ E)) ⟨277159875072,347734535⟩ (N (N E ⟨277159875200,347067389⟩ E) ⟨277159875328,346401842⟩ E)) ⟨277159875584,345075528⟩ (N (N (N E ⟨277159875712,344414752⟩ E) ⟨277159875840,343755558⟩ E) ⟨277159875968,343097939⟩ (N (N E ⟨277159876096,342441893⟩ E) ⟨277159876224,341787414⟩ E))) ⟨277159876352,341134499⟩ (N (N (N (N E ⟨277159876608,339833339⟩ E) ⟨277159876736,339185085⟩ (N E ⟨277159876864,338538377⟩ E)) ⟨277159876992,337893210⟩ (N (N E ⟨277159877120,337249579⟩ E) ⟨277159877248,336607480⟩ E)) ⟨277159877504,335327861⟩ (N (N (N E ⟨277159877888,333419814⟩ E) ⟨277159878016,332786815⟩ E) ⟨277159878144,332155319⟩ (N (N E ⟨277159878272,331525320⟩ E) ⟨277159878400,330896814⟩ E)))))))

noncomputable def tab30 : CTN :=
  (N (N (N (N (N (N (N (N E ⟨277294092544,396787471⟩ E) ⟨277294092672,396025483⟩ (N E ⟨277294092800,395265323⟩ E)) ⟨277294092928,394506987⟩ (N (N E ⟨277294093056,393750469⟩ E) ⟨277294093312,392242865⟩ E)) ⟨277294093440,391491770⟩ (N (N (N E ⟨277294093696,389994965⟩ E) ⟨277294093824,389249246⟩ (N E ⟨277294093952,388505309⟩ E)) ⟨277294094080,387763148⟩ (N (N E ⟨277294094208,387022759⟩ E) ⟨277294094464,385547275⟩ E))) ⟨277294094592,384812171⟩ (N (N (N (N E ⟨277294094848,383347211⟩ E) ⟨277294094976,382617345⟩ (N E ⟨277294095104,381889216⟩ E)) ⟨277294095360,380438148⟩ (N (N E ⟨277294095488,379715198⟩ E) ⟨277294095616,378993966⟩ E)) ⟨277294095744,378274445⟩ (N (N (N E ⟨277294095872,377556631⟩ E) ⟨277294096128,376126105⟩ E) ⟨277294096384,374702349⟩ (N (N E ⟨277428310656,444907878⟩ E) ⟨277428310784,444054710⟩ E)))) ⟨277428310912,443203586⟩ (N (N (N (N (N E ⟨277428311040,442354500⟩ E) ⟨277428311296,440662421⟩ (N E ⟨277428311424,439819416⟩ E)) ⟨277428311552,438978426⟩ (N (N E ⟨277428311808,437302469⟩ E) ⟨277428311936,436467490⟩ E)) ⟨277428312064,435634504⟩ (N (N (N E ⟨277428312192,434803504⟩ E) ⟨277428312320,433974485⟩ (N E ⟨277428312448,433147441⟩ E)) ⟨277428312576,432322366⟩ (N (N E ⟨277428312704,431499256⟩ E) ⟨277428312960,429858904⟩ E))) ⟨277428313088,429041651⟩ (N (N (N (N E ⟨277428313216,428226340⟩ E) ⟨277428313344,427412966⟩ (N E ⟨277428313472,426601521⟩ E)) ⟨277428313600,425792002⟩ (N (N E ⟨277428313856,424178717⟩ E) ⟨277428313984,423374940⟩ E)) ⟨277428314112,422573066⟩ (N (N (N E ⟨277562528640,496339612⟩ E) ⟨277562529024,493493786⟩ E) ⟨277562529152,492549712⟩ (N (N E ⟨277562529408,490668329⟩ E) ⟨277562529536,489731006⟩ E))))) ⟨277562529664,488795921⟩ (N (N (N (N (N (N E ⟨277562529792,487863067⟩ E) ⟨277562529920,486932438⟩ (N E ⟨277562530048,486004027⟩ E)) ⟨277562530560,482312440⟩ (N (N E ⟨277562530816,480479793⟩ E) ⟨277562531072,478655842⟩ E)) ⟨277562531200,477747113⟩ (N (N (N E ⟨277562531584,475033837⟩ E) ⟨277562531712,474133694⟩ (N E ⟨277562531840,473235683⟩ E)) ⟨277696747264,545025509⟩ (N (N E ⟨277696747776,540877725⟩ E) ⟨277696747904,539846951⟩ E))) ⟨277696748160,537792759⟩ (N (N (N (N E ⟨277696748288,536769328⟩ E) ⟨277696748416,535748331⟩ (N E ⟨277696748544,534729760⟩ E)) ⟨277696749184,529673068⟩ (N (N E ⟨277696749568,526667734⟩ E) ⟨277830964992,603160944⟩ E)) ⟨277830965376,599714180⟩ (N (N (N E ⟨277830965760,596292006⟩ E) ⟨277830965888,595156709⟩ E) ⟨277830966144,592894210⟩ (N (N E ⟨277830966272,591766993⟩ E) ⟨277830966784,587284829⟩ E)))) ⟨277830967040,585059662⟩ (N (N (N (N (N E ⟨277830967168,583951032⟩ E) ⟨277830967296,582845026⟩ (N E ⟨277965183360,657800459⟩ E)) ⟨277965184256,649091784⟩ (N (N E ⟨277965184896,642959425⟩ E) ⟨277965185024,641741658⟩ E)) ⟨278099401728,714096329⟩ (N (N (N E ⟨278099402496,706002468⟩ E) ⟨278099402752,703330025⟩ E) ⟨278233619840,774898307⟩ (N (N E ⟨278233619968,773427859⟩ E) ⟨278233620096,771960898⟩ E))) ⟨278233620352,769037398⟩ (N (N (N (N E ⟨278233620480,767580838⟩ E) ⟨278367838080,836046611⟩ (N E ⟨278367838208,834463136⟩ E)) ⟨278502055808,905659624⟩ (N (N E ⟨278502055936,903944301⟩ E) ⟨278636273664,975990077⟩ E)) ⟨278770491392,1050564584⟩ (N (N (N E ⟨278904709120,1127630341⟩ E) ⟨279038926848,1207148283⟩ E) ⟨279173144576,1289077782⟩ (N (N E ⟨279307362304,1373376670⟩ E) ⟨279441580032,1460001260⟩ E)))))) ⟨279575797760,1548906371⟩ (N (N (N (N (N (N (N E ⟨279710015488,1640045351⟩ E) ⟨279844233216,1733370107⟩ (N E ⟨280112668672,1926377499⟩ E)) ⟨280246886400,2025956968⟩ (N (N E ⟨280917975040,2552429823⟩ E) ⟨281052192768,2663037788⟩ E)) ⟨283468112000,4859954717⟩ (N (N (N E ⟨283468112128,4850758660⟩ E) ⟨283468112256,4841584346⟩ (N E ⟨283468112384,4832431715⟩ E)) ⟨283468112512,4823300705⟩ (N (N E ⟨283468112640,4814191254⟩ E) ⟨283468112768,4805103302⟩ E))) ⟨283468112896,4796036788⟩ (N (N (N (N E ⟨283468113024,4786991651⟩ E) ⟨283468113152,4777967830⟩ (N E ⟨283468113280,4768965266⟩ E)) ⟨283468113408,4759983897⟩ (N (N E ⟨283468113536,4751023666⟩ E) ⟨283468113664,4742084510⟩ E)) ⟨283468113792,4733166372⟩ (N (N (N E ⟨283468113920,4724269192⟩ E) ⟨283468114048,4715392911⟩ E) ⟨283468114176,4706537470⟩ (N (N E ⟨283468114304,4697702810⟩ E) ⟨283468114432,4688888873⟩ E)))) ⟨283468114560,4680095600⟩ (N (N (N (N (N E ⟨283468114688,4671322934⟩ E) ⟨283468114816,4662570816⟩ (N E ⟨283468114944,4653839189⟩ E)) ⟨283468115072,4645127994⟩ (N (N E ⟨283468115200,4636437176⟩ E) ⟨283468115328,4627766676⟩ E)) ⟨283468115456,4619116438⟩ (N (N (N E ⟨283468115584,4610486405⟩ E) ⟨283468115712,4601876519⟩ E) ⟨283468115840,4593286726⟩ (N (N E ⟨283468115968,4584716968⟩ E) ⟨283468116096,4576167189⟩ E))) ⟨283468116224,4567637334⟩ (N (N (N (N E ⟨283468116352,4559127347⟩ E) ⟨283468116480,4550637173⟩ (N E ⟨283468116608,4542166755⟩ E)) ⟨283468116736,4533716039⟩ (N (N E ⟨283468116864,4525284970⟩ E) ⟨283468116992,4516873494⟩ E)) ⟨283468117120,4508481554⟩ (N (N (N E ⟨283468117248,4500109098⟩ E) ⟨283468117376,4491756071⟩ E) ⟨283468117504,4483422418⟩ (N (N E ⟨283468117632,4475108086⟩ E) ⟨283468117760,4466813021⟩ E))))) ⟨283468117888,4458537170⟩ (N (N (N (N (N (N E ⟨283468118016,4450280479⟩ E) ⟨283468118144,4442042895⟩ (N E ⟨283468118272,4433824364⟩ E)) ⟨283468118528,4417444254⟩ (N (N E ⟨283468118656,4409282568⟩ E) ⟨283468118784,4401139726⟩ E)) ⟨283468118912,4393015675⟩ (N (N (N E ⟨283468119040,4384910364⟩ E) ⟨283468119168,4376823740⟩ (N E ⟨283468119296,4368755751⟩ E)) ⟨283468119552,4352675475⟩ (N (N E ⟨283468119936,4328693546⟩ E) ⟨283468120064,4320736295⟩ E))) ⟨287226216448,7436001894⟩ (N (N (N (N E ⟨292058054784,9597161408⟩ E) ⟨292058054912,9575208023⟩ (N E ⟨292058055040,9550434133⟩ E)) ⟨292058055168,9522859734⟩ (N (N E ⟨292058055552,9423557641⟩ E) ⟨292058055680,9385013290⟩ E)) ⟨292058055808,9343792325⟩ (N (N (N E ⟨292058055936,9299924162⟩ E) ⟨292058056192,9204371355⟩ E) ⟨292058056320,9152752914⟩ (N (N E ⟨292058056448,9098619634⟩ E) ⟨292058056576,9042008151⟩ E)))) ⟨292058056704,8982956468⟩ (N (N (N (N (N E ⟨292058056832,8921503925⟩ E) ⟨292058056960,8857691173⟩ (N E ⟨292058057088,8791560142⟩ E)) ⟨292058057216,8723154014⟩ (N (N E ⟨292058057344,8652517190⟩ E) ⟨292058057472,8579695262⟩ E)) ⟨292058057728,8427684207⟩ (N (N (N E ⟨292058057984,8267508144⟩ E) ⟨292058058112,8184483924⟩ E) ⟨292058058368,8012823281⟩ (N (N E ⟨292058058496,7924293774⟩ E) ⟨292058058880,7648568596⟩ E))) ⟨292058059520,7158669834⟩ (N (N (N (N E ⟨292058059648,7056667314⟩ E) ⟨292058059776,6953465123⟩ (N E ⟨292058060032,6743708678⟩ E)) ⟨292058060160,6637279038⟩ (N (N E ⟨292058060288,6529898878⟩ E) ⟨292058060416,6421631471⟩ E)) ⟨292058061440,5531229986⟩ (N (N (N E ⟨292058061824,5190464847⟩ E) ⟨292058061952,5076561304⟩ E) ⟨292058062464,4621084718⟩ (N (N E ⟨292058062848,4281402733⟩ E) ⟨295681941504,4479017847⟩ E)))))))

noncomputable def tab31 : CTN :=
  (N (N (N (N (N (N (N (N E ⟨300647997696,4494939674⟩ E) ⟨300647997952,4253388679⟩ (N E ⟨300647998080,4133565213⟩ E)) ⟨300647998720,3546494959⟩ (N (N E ⟨300647999360,2985075450⟩ E) ⟨300647999616,2769316193⟩ E)) ⟨300647999872,2559248457⟩ (N (N (N E ⟨300648000000,2456479654⟩ E) ⟨300648000640,1967268314⟩ (N E ⟨300648001536,1359554913⟩ E)) ⟨300648002048,1057381282⟩ (N (N E ⟨300648002176,987302496⟩ E) ⟨300648002304,919468625⟩ E))) ⟨300648002688,729699503⟩ (N (N (N (N E ⟨300648003072,561020055⟩ E) ⟨300648003200,509575479⟩ (N E ⟨300648003712,328141884⟩ E)) ⟨300648003840,288934345⟩ (N (N E ⟨300648004864,65040651⟩ E) ⟨300648005632,1958320⟩ E)) ⟨309506380672,82047⟩ (N (N (N E ⟨309506381952,80660⟩ E) ⟨309506382592,79977⟩ E) ⟨309506383872,78634⟩ (N (N E ⟨309640596736,1969769⟩ E) ⟨309640597888,1939609⟩ E)))) ⟨309640600192,1880999⟩ (N (N (N (N (N E ⟨309640601344,1852525⟩ E) ⟨309640601600,1846271⟩ (N E ⟨309774816128,6201069⟩ E)) ⟨309774816512,6169391⟩ (N (N E ⟨309774817792,6065251⟩ E) ⟨309774817920,6054958⟩ E)) ⟨309774818304,6024210⟩ (N (N (N E ⟨309774818688,5993658⟩ E) ⟨309774819328,5943166⟩ E) ⟨309909032960,13065343⟩ (N (N E ⟨309909033344,12998401⟩ E) ⟨309909034240,12843862⟩ E))) ⟨309909034624,12778335⟩ (N (N (N (N E ⟨309909035648,12605627⟩ E) ⟨309909036928,12393825⟩ (N E ⟨309909037056,12372891⟩ E)) ⟨310043253376,21535210⟩ (N (N E ⟨310043253760,21425853⟩ E) ⟨310043254784,21137608⟩ E)) ⟨310177469824,33408172⟩ (N (N (N E ⟨310177471232,32788760⟩ E) ⟨310177471872,32511957⟩ E) ⟨310177472512,32238069⟩ (N (N E ⟨310311687680,47250737⟩ E) ⟨310311687808,47170279⟩ E))))) ⟨310311688960,46453808⟩ (N (N (N (N (N (N E ⟨310311690240,45673612⟩ E) ⟨310445903744,64992069⟩ (N E ⟨310445906176,62917804⟩ E)) ⟨310445906816,62385753⟩ (N (N E ⟨310445906944,62280019⟩ E) ⟨310445907072,62174509⟩ E)) ⟨310445907328,61964157⟩ (N (N (N E ⟨310445907584,61754695⟩ E) ⟨310445907968,61442158⟩ (N E ⟨310580124416,80898916⟩ E)) ⟨310580125184,80080243⟩ (N (N E ⟨310580125440,79809656⟩ E) ⟨310580125696,79540211⟩ E))) ⟨310714340992,103238513⟩ (N (N (N (N E ⟨310714341248,102887449⟩ E) ⟨310714341504,102537877⟩ (N E ⟨310714342656,100983052⟩ E)) ⟨310714343424,99962856⟩ (N (N E ⟨310848559744,125011844⟩ E) ⟨310848560512,123746228⟩ E)) ⟨310848560768,123327919⟩ (N (N (N E ⟨310848560896,123119427⟩ E) ⟨310848561152,122703764⟩ E) ⟨310982776704,152078030⟩ (N (N E ⟨310982778752,148005184⟩ E) ⟨310982778880,147755186⟩ E)))) ⟨311116996608,175107963⟩ (N (N (N (N (N E ⟨311251214336,204751524⟩ E) ⟨311385431552,238280772⟩ (N E ⟨311385432064,236673892⟩ E)) ⟨311519649792,270861689⟩ (N (N E ⟨311653867520,307300140⟩ E) ⟨311788084480,349503998⟩ E)) ⟨311788085248,345973083⟩ (N (N (N E ⟨311922302976,386862971⟩ E) ⟨312190738432,475216546⟩ E) ⟨312324956160,522638312⟩ (N (N E ⟨312459173888,572193205⟩ E) ⟨312593391616,623856911⟩ E))) ⟨312727609344,677603799⟩ (N (N (N (N E ⟨312996044800,791238073⟩ E) ⟨313130262528,851067722⟩ (N E ⟨313264480256,912865110⟩ E)) ⟨313398697984,976598221⟩ (N (N E ⟨313532915712,1042233817⟩ E) ⟨313667133440,1109737447⟩ E)) ⟨314338222080,1473988139⟩ (N (N (N E ⟨314472439808,1551911270⟩ E) ⟨314606657536,1631429101⟩ E) ⟨314875092992,1795074314⟩ (N (N E ⟨315143528448,1964564700⟩ E) ⟨317827883136,3885544523⟩ E)))))) ⟨317827883264,3878986917⟩ (N (N (N (N (N (N (N E ⟨317827883392,3872443141⟩ E) ⟨317827883520,3865913159⟩ (N E ⟨317827883648,3859396938⟩ E)) ⟨317827883776,3852894441⟩ (N (N E ⟨317827883904,3846405636⟩ E) ⟨317827884032,3839930486⟩ E)) ⟨317827884160,3833468957⟩ (N (N (N E ⟨317827884288,3827021016⟩ E) ⟨317827884416,3820586627⟩ (N E ⟨317827884544,3814165757⟩ E)) ⟨317827884672,3807758371⟩ (N (N E ⟨317827884800,3801364436⟩ E) ⟨317827884928,3794983918⟩ E))) ⟨317827885056,3788616783⟩ (N (N (N (N E ⟨317827885184,3782262996⟩ E) ⟨317827885312,3775922526⟩ (N E ⟨317827885440,3769595338⟩ E)) ⟨317827885696,3756980674⟩ (N (N E ⟨317827885824,3750693133⟩ E) ⟨317827886080,3738157464⟩ E)) ⟨317827886208,3731909272⟩ (N (N (N E ⟨317827886336,3725674130⟩ E) ⟨317827886464,3719452006⟩ E) ⟨317827886592,3713242867⟩ (N (N E ⟨317827886720,3707046681⟩ E) ⟨317827887104,3688535515⟩ E)))) ⟨317827887616,3664033345⟩ (N (N (N (N (N E ⟨317827887744,3657939622⟩ E) ⟨317827888000,3645790137⟩ (N E ⟨317827888128,3639734313⟩ E)) ⟨317827888256,3633691059⟩ (N (N E ⟨317827888512,3621642135⟩ E) ⟨317827888896,3603662244⟩ E)) ⟨317827889152,3591737619⟩ (N (N (N E ⟨317827889280,3585793805⟩ E) ⟨317827889408,3579862283⟩ E) ⟨317827889536,3573943022⟩ (N (N E ⟨317827889664,3568035991⟩ E) ⟨317827889792,3562141161⟩ E))) ⟨317827889920,3556258500⟩ (N (N (N (N E ⟨317827890688,3521216428⟩ E) ⟨317827890944,3509631742⟩ (N E ⟨317827891072,3503857266⟩ E)) ⟨317827891200,3498094663⟩ (N (N E ⟨326417825920,7682384680⟩ E) ⟨326417826176,7647939783⟩ E)) ⟨326417827072,7457388810⟩ (N (N (N E ⟨326417827328,7383602295⟩ E) ⟨326417827584,7301568583⟩ E) ⟨326417828736,6836709276⟩ (N (N E ⟨326417828992,6713739383⟩ E) ⟨326417830400,5930101347⟩ E))))) ⟨326417830656,5770967704⟩ (N (N (N (N (N (N E ⟨326417830784,5689805104⟩ E) ⟨326417830912,5607643480⟩ (N E ⟨326417831296,5355658432⟩ E)) ⟨326417831680,5096476453⟩ (N (N E ⟨326417831808,5008720248⟩ E) ⟨326417832064,4831472902⟩ E)) ⟨326417832320,4652257523⟩ (N (N (N E ⟨326417832448,4562041784⟩ E) ⟨326417832576,4471490174⟩ (N E ⟨326417833728,3650009968⟩ E)) ⟨326417833984,3468145225⟩ (N (N E ⟨335007768832,3604226111⟩ E) ⟨335007769344,3220520518⟩ E))) ⟨335007769984,2754687635⟩ (N (N (N (N E ⟨335007770240,2573923713⟩ E) ⟨335007771392,1812133475⟩ (N E ⟨335007771648,1656374456⟩ E)) ⟨335007773184,849208411⟩ (N (N E ⟨335007774720,295826098⟩ E) ⟨335007776128,37698133⟩ E)) ⟨343866155008,178934⟩ (N (N (N E ⟨344403025920,18725853⟩ E) ⟨344537243648,28133016⟩ E) ⟨344671461376,39447622⟩ (N (N E ⟨345074114560,84806424⟩ E) ⟨345342550016,124508209⟩ E)))) ⟨345476767744,147176846⟩ (N (N (N (N (N E ⟨345610985472,171711948⟩ E) ⟨347355815936,654223094⟩ (N E ⟨352187656576,3091606465⟩ E)) ⟨352187657344,3063678277⟩ (N (N E ⟨352187657984,3040645350⟩ E) ⟨352187658752,3013290833⟩ E)) ⟨352187660288,2959498522⟩ (N (N (N E ⟨352187661952,2902571181⟩ E) ⟨352187662336,2889629010⟩ E) ⟨360777598208,6112875783⟩ (N (N E ⟨360777599232,5838364816⟩ E) ⟨360777599744,5662938429⟩ E))) ⟨360777600768,5244730707⟩ (N (N (N (N E ⟨360777600896,5186767810⟩ E) ⟨360777602560,4342476136⟩ (N E ⟨360777604096,3465703138⟩ E)) ⟨360777605120,2866362512⟩ (N (N E ⟨369367540480,2640786562⟩ E) ⟨369367542016,1755793092⟩ E)) ⟨369367543296,1118197918⟩ (N (N (N E ⟨369367543552,1004813598⟩ E) ⟨369367543808,896679162⟩ E) ⟨369367544704,562364930⟩ (N (N E ⟨369367545472,334468394⟩ E) ⟨369367547136,41088933⟩ E)))))))

noncomputable def table : CTN :=
  (N (N (N (N (N tab0 ⟨69927504384,41879149⟩ tab1) ⟨72276317440,7756885020⟩ (N tab2 ⟨102005571200,795598303⟩ tab3)) ⟨104689929472,499750230⟩ (N (N tab4 ⟨106166326272,3226207768⟩ tab5) ⟨131130846848,9609015681⟩ (N tab6 ⟨138110180992,6425160⟩ tab7))) ⟨138915484544,293395360⟩ (N (N (N tab8 ⟨139720791168,996661346⟩ tab9) ⟨140794532864,2598944548⟩ (N tab10 ⟨163208915712,7818828574⟩ tab11)) ⟨172469948416,13545204⟩ (N (N tab12 ⟨173141036800,184292448⟩ tab13) ⟨173812128128,517440599⟩ (N tab14 ⟨174617433344,1204989991⟩ tab15)))) ⟨177704443904,5701071046⟩ (N (N (N (N tab16 ⟨203608489984,18798824⟩ tab17) ⟨207098157056,50285705⟩ (N tab18 ⟨207769244416,236493606⟩ tab19)) ⟨208440334208,542971309⟩ (N (N tab20 ⟨209379859456,1168287846⟩ tab21) ⟨223338519680,8421424628⟩ (N tab22 ⟨241189494272,14432735⟩ tab23))) ⟨241994796032,157435496⟩ (N (N (N tab24 ⟨242665887104,372399775⟩ tab25) ⟨243471195776,735784576⟩ (N tab26 ⟨249108348672,5493860527⟩ tab27)) ⟨275549261568,14385483⟩ (N (N tab28 ⟨276354568064,127064528⟩ tab29) ⟨277159878656,329644265⟩ (N tab30 ⟨300647997568,4616538007⟩ tab31)))))

theorem tab0_ok : tab0.allOk = true := by decide +kernel

theorem tab1_ok : tab1.allOk = true := by decide +kernel

theorem tab2_ok : tab2.allOk = true := by decide +kernel

theorem tab3_ok : tab3.allOk = true := by decide +kernel

theorem tab4_ok : tab4.allOk = true := by decide +kernel

theorem tab5_ok : tab5.allOk = true := by decide +kernel

theorem tab6_ok : tab6.allOk = true := by decide +kernel

theorem tab7_ok : tab7.allOk = true := by decide +kernel

theorem tab8_ok : tab8.allOk = true := by decide +kernel

theorem tab9_ok : tab9.allOk = true := by decide +kernel

theorem tab10_ok : tab10.allOk = true := by decide +kernel

theorem tab11_ok : tab11.allOk = true := by decide +kernel

theorem tab12_ok : tab12.allOk = true := by decide +kernel

theorem tab13_ok : tab13.allOk = true := by decide +kernel

theorem tab14_ok : tab14.allOk = true := by decide +kernel

theorem tab15_ok : tab15.allOk = true := by decide +kernel

theorem tab16_ok : tab16.allOk = true := by decide +kernel

theorem tab17_ok : tab17.allOk = true := by decide +kernel

theorem tab18_ok : tab18.allOk = true := by decide +kernel

theorem tab19_ok : tab19.allOk = true := by decide +kernel

theorem tab20_ok : tab20.allOk = true := by decide +kernel

theorem tab21_ok : tab21.allOk = true := by decide +kernel

theorem tab22_ok : tab22.allOk = true := by decide +kernel

theorem tab23_ok : tab23.allOk = true := by decide +kernel

theorem tab24_ok : tab24.allOk = true := by decide +kernel

theorem tab25_ok : tab25.allOk = true := by decide +kernel

theorem tab26_ok : tab26.allOk = true := by decide +kernel

theorem tab27_ok : tab27.allOk = true := by decide +kernel

theorem tab28_ok : tab28.allOk = true := by decide +kernel

theorem tab29_ok : tab29.allOk = true := by decide +kernel

theorem tab30_ok : tab30.allOk = true := by decide +kernel

theorem tab31_ok : tab31.allOk = true := by decide +kernel

theorem table_ok : table.allOk = true := by
  simp only [table, CTN.allOk, tab0_ok, tab1_ok, tab2_ok, tab3_ok, tab4_ok, tab5_ok, tab6_ok, tab7_ok, tab8_ok, tab9_ok, tab10_ok, tab11_ok, tab12_ok, tab13_ok, tab14_ok, tab15_ok, tab16_ok, tab17_ok, tab18_ok, tab19_ok, tab20_ok, tab21_ok, tab22_ok, tab23_ok, tab24_ok, tab25_ok, tab26_ok, tab27_ok, tab28_ok, tab29_ok, tab30_ok, tab31_ok, Bool.true_and, Bool.and_true]
  decide +kernel

def cover0 : List (ℕ × ℕ × Bool) := [
  (16384, 24576, true),
  (24576, 28672, true),
  (28672, 29696, true),
  (29696, 30720, true),
  (30720, 39936, false),
  (39936, 40000, true),
  (40000, 40064, true),
  (40064, 40192, true),
  (40192, 40448, true),
  (40448, 40960, true),
  (40960, 43008, true),
  (43008, 45056, true),
  (45056, 49152, true),
  (49152, 53248, true),
  (53248, 55296, true),
  (55296, 56320, true),
  (56320, 57344, true),
  (57344, 434176, false)]

theorem cover0_ok : SixW8.coverCheck table 25326800 (SC / 2) 434176 cover0 = true := by decide +kernel

def cover1 : List (ℕ × ℕ × Bool) := [
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
  (59904, 74752, false),
  (74752, 75264, true),
  (75264, 75776, true),
  (75776, 77824, true),
  (77824, 81920, true),
  (81920, 86016, true),
  (86016, 88064, true),
  (88064, 88320, true),
  (88320, 88448, true),
  (88448, 88576, true),
  (88576, 262144, false)]

theorem cover1_ok : SixW8.coverCheck table 48244400 (SC / 2) 262144 cover1 = true := by decide +kernel

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
  (59392, 60416, true),
  (60416, 74240, false),
  (74240, 74752, true),
  (74752, 75776, true),
  (75776, 77824, true),
  (77824, 81920, true),
  (81920, 86016, true),
  (86016, 88064, true),
  (88064, 88576, true),
  (88576, 89088, true),
  (89088, 237568, false)]

theorem cover2_ok : SixW8.coverCheck table 52857300 (SC / 2) 237568 cover2 = true := by decide +kernel

def cover3 : List (ℕ × ℕ × Bool) := [
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
  (59904, 74752, false),
  (74752, 75264, true),
  (75264, 75776, true),
  (75776, 77824, true),
  (77824, 81920, true),
  (81920, 86016, true),
  (86016, 88064, true),
  (88064, 88320, true),
  (88320, 88448, true),
  (88448, 88576, true),
  (88576, 262144, false)]

theorem cover3_ok : SixW8.coverCheck table 48244400 (SC / 2) 262144 cover3 = true := by decide +kernel

def cover4 : List (ℕ × ℕ × Bool) := [
  (16384, 24576, true),
  (24576, 28672, true),
  (28672, 29696, true),
  (29696, 30720, true),
  (30720, 39936, false),
  (39936, 40000, true),
  (40000, 40064, true),
  (40064, 40192, true),
  (40192, 40448, true),
  (40448, 40960, true),
  (40960, 43008, true),
  (43008, 45056, true),
  (45056, 49152, true),
  (49152, 53248, true),
  (53248, 55296, true),
  (55296, 56320, true),
  (56320, 57344, true),
  (57344, 434176, false)]

theorem cover4_ok : SixW8.coverCheck table 25326800 (SC / 2) 434176 cover4 = true := by decide +kernel

def bits : ℕ := 714196486872305309507537918541579078935894399290220882582730491405598423369369569860256896411157630721740636476623462421400535317374034166226675064678721562453674782514060715850810914977372358055016570114114816423355481044472744476104090702390559702146486298987373076115024206934843155282789821228980263742523092520739790787004218691425688778000631623645007856932103238980574809254591257664379817589436610275449035782177132405294740710499193237430597055720351770446701125213000432114201219574440181266666568326230358417593808972721662006741441884408750140910540699259997542095634960014256027756254104524549207032651428627639891250433974489150153438595837092055226312888608805754030665459144974452447213695612158900041218021227743864905198364895726842859178614042311921132644854613517991097405558786169968537745526892057573423414403082230402512751129129745990942513984980737831206402927972650012442314576099234323391705056525375807141237073261068617699047103061445586948635452341993682307497273629572792195778876435489702864305229098780822636368216337990045276893290718634487558580551555017131756061759585604260798579529355308067857537735932837711939056905322045149150376135871209081374171697685462705616527223817993653499857972200322231034904022369758824342103634113809521200169243791181181770229611616845292513583250169670444602350513089275080760069418351944136542762271012988309366464275945951282062380834103601463769179532883958866995549494769629839173115883946055625727867145785758762001438747332423366693747321532392973515506609094264951690771832384353335662828054169951842604790140465216054140612543851799904140899239290235902921248697227070051121810975130586601573795726807118631114076064090569861647484035933618480255774739052043046172022194793679455164532745323364099674077309322518926985260234617205245300086361126680998911355328301865926610082618617676089444375896450556083987667951371081045593290202343480228229122344060155864081765233306724108708287726153850551539611006944903204699634347579352988995004672623833127341364492731851689368365254259414759172102651342794663677169547417671742342266669790507460095588319317129856125754704365015857422284644722773225160592686917170406350113420107587611888928039204936826002518365258024999503415141413090439110828225141317401866277424455185317622877142851672210012619485667128747025914926553840476802469020986550423326574456396213571193063422463741511286791862840527467961584378238094899690177661795819332992249606475499436446200214984637658737510587491390891758736012637540009050364261785073772016638168927397025652459757192571994711094540219814570386247365809372602679403444155498690920399942009690265645747508665104480588568970644221831594190490992214416104136161652388272165065606390743118298564618129688699160793910749238418328234897211923668872921658543636115458254116992613979120223142846514592457027445773666441713537294209806509859383631150688301096431807312166186996063553938992532581495941375759390800253844762475533221033013514596226292293165134929488228464140691673887583106630285930819382105866841195922695442758174676972773188913401174773944947970522820937833774374328502554433830257160479875260386448055414049623107083452706216074623498088413726694507393697848605548169737984393028710676893132042667644800075540732126012981001011324835493089401498548804703454871709937459592842721288902790652254363986334722841901070121006012343933860487766439865787353496298614611602591472726364203219292929326813555650991716628677186065148219162596752181127256792781795317997543988120851393119763967872787871562457145134665650567311272946307499052015863292562549430643474911805987013855548369118297248587487475486915848201732273808449145701616668648940647243199121616061039296719377470477952983976349591571856629346267969076693018802851857355903521069056122030125984825542535896747678774223890200913692415844361805298855629858400362218755204812816753212390399251806936572136404022769548755579881432457454694077587636914353652017158717108364063495607236607668082306155484857271274210133216293893640818487227424275263332480484793831447651284535805962142081380056140723389294711579460125405096126514603050310237649215423294820754144290137562108224177889540484617894915859023538795645877172644473197738232739057445349337708306538839829008622445959326862227444169288419573541525924501896479819250195853660969899378512087947775444409982997913940562986448813320124613383830639609624588401789407803122205255805322336799446898191733960846738126109960901605719599742236987557601964450076454085002425377371451456194443890471889433721307387597119933307038736148843188202043858231227830245509610325753439135478902609800583168539296266557243832036648214491255775296789396717251752715845692458811476289415931697568069117530973802642745191252461136282161039227768937103735178080013282385980714530708184269722903052856911492872185038311174611132260074703501414233987444913584448281026438970348952163063167448887416925183056430440061272439427912358944224279596812137582978697818971263118812018466690045384176199741789840011653099157187582090956183877052665296011760688163839717643005257239830064099139346459658997764222772308912950202875333493481568555214957341010717800186774849243637634510442121634424771201362956026995612361874899622616289837828549880776604482881993473228312360878313319202014927475584167187627112335304899489469119687425568416617425520097246499566172059151503956405782065622345089113506447010929547453092409623998905935390957813073255798286673471516704802085384567866658814170467089469554675527538292973518705960090564350329640221671712517377350231289960060837648352709402769515079969526894719121000732451590060464883863118506168302728854158657055454626532583149895716347262103287513106329743147917390188639697649701254514396187370190399288732445072444871405976605018837287796078719101657423257045787517404551383159102074139481443291673010508097152535810965559056378955962848792978076444746899114159869988090244029332005091441533312253253455994905402575464555899396175355377011277428215272495583656423608006358760942549627180959275532762999630058713815807318074121529503161119247792605522820421750329132115208705085802373134727183037619303357106565401278345165095052568074612035942397197748384518764970068413170198542542786353650123417574280479596598557063952118215750461294989013723120840498190891143677144744246299334371613593895508497056608452546098853307753121038595526454600180727349879945059040147328764906006802738254071438063948470315600131284563260854471953244026891905113873091566172608031242045629832419453809943055611679855120511467283783103206951921151145613193489491382845086972571422547471474514939237218019948032750074995397712508736884702428136165608510520457182332651030006356256687112834332795489192396086078417552752783085466716360370581658409171432930742264984634814361779040227164907911555727661208217758989179930044265707017126569647005134171445537103126478124429399014597755953210017609623448225201809928892016650925069652280601400674973311448680422942103878550147355845382141542679970131337972096312705941096955537297080020848238470537157789410061365571238818828571657507454432881818310332847427164576483538813824525651015478514489344085831554225938936569856692435884845700875853105612326265412018369213746909867130621815422902892390613983717782743562732144585617030270053153182236227916104827691018169615577246405241714843857349743726913504786891035889431927135914965035655453610893129705812698633764036161745378070876666117282903639594562545634767834482535209361002030703182773505153858766826699687000534123152711112321248730083249965495558683704976870878150276524624436570278124021397594449072779479953599794530625528133480397851466496782361632693681596156059178979512506169260826554438444292130325542733948881822816525274590608581235276881308450950235036375425825792886980997145676611999240945454318383984059775800049672215716835526937168412049971995604833619183392558443909098926808698716334906057762751086280406808540984547596176191059373799373961553121399664416905378724967307114162627188750570458639845992903896387863101451578948303676344650496753320646788508784235925294798850883526298382630655514237248254814554818957479565200603963693067470445735366739493395687768074318720509943246018981315200171997323715904917814824761517581505123313141304592323980074347528418808990157240551912163208384178114763841158419220702866745628248103480844001839341087256418482161979763283412752306578638777500122232539265532388869364326197913472088107376039656741106292935354117227460250552959842546759978270587326093185578852265100048682910921039800820703347953767191253435408466527705515699889398034263014727018816653651889698459056273332079921139125778775126516470326988931852687081966312027228955992604688709673966499298855133893482689704478887127006645429348059501331311034023395875192927533117284919353141858865155754644438145436507989831871887831882547319723664143845721157032579051484838810813035582794296546523595299320358039793844234359323089916267701466707323346663435678223466086843089127431418764724087585158426264099230268972049795801160652648298823034905268101191627834233308076157629680706499599972490177725799842208430325099808588631742927421148610957909846531603193231738404482966249373918301015457844720156102908147976011228581191697156045117015541475883901837446301654158588569182799075504899054269393987121209657647067844585397704939816030012981199425852233691099327229211939684766778468413909748642360828531826119578270718156255141267561181575320253460988047606743691437340629190704431767388893582543470277903312539647454395888777186688162349192232491938650300378994252419771616703367851958397138857642234906814785604986701423721225713079104326827049431105143438924314751679867691760360082093716262359484788735695209369557123558658724455136422367591560337422299723861761260318360899833852306722672937941399690804440754545817119364806330675323935858891178393627329151998145198421860704280551235419441308736451705476018338773098744578277169426035098139556271610218524863641414216688499566744582601873486510663319343583055064705421226446841295796073564515981460854120902312559414269959457625034644454747524346984584431535753370111878198387985836763932095051469391665970968381948009430240721951875476619888378061873525247059935291055241275300687644666644274377892945306309679855972800184313687005559218649314319564557466401966465300332176152111723408458217929302901935705164319488483068895435572973298048557548262233807760590862163494300570439207366782014783251067723986264848300397475298889666466963231132559486412052886489463568280011316650453643721509730203406244300772162059555920152337009451916836200674204941177673037848690364721757482071331085947236212386840078941578624232165909143832822192441753663133694638719021266565686955579263507181602027009710702732983158171905588180520865753456095209530181545236596831112641551082582552227831286539984421573291900309588992277804090208684277007469038582078167207042165760753963130671424791087440859868043748326659002667684016634949967754729548048725326735992723324536933446089293949971769048336558368115325892966214689453250256661122054127031462398943537508816889393193894861480709714263402919673647848759611952969365755998148294355847338818594555152829036585496496004080344704081864190645537935559904239209480629485223042002512282668828901228024601952459747291720002016466449802375210760883442820865906674736445141494751600176197545091744117916353924037794038621910877604742301376586847533486341377108371721936005349138575573543114102641346290071600666443071010289644866070021899881558744599140186905970412327635885917535172018994894832075413743377800801558967464790229655356545573641313452765557182409065429324197099539479612436865477053581919286836544156276941633933049433342882271198835548040691330077539245777366901599085787335117066929459683769594024486499316623446079027953361219277271984871024649859480312835855119545106793547139980301186889974265738734551972856871766674588160951140319250669391960566319898470976265394984304146206567118164306069207774217214163613217666335484337833709323881253845683188690200985406811210166728127114415226406689369410196517253801863666382247903784680520187061414552068558808832148494655494701365597205717184815152272494792698858832374430773807002161057390008591373936215255344477123297639491531617637142700450395892672252426570921719363664515954652576338642798629401276334780594314005100976875303713248714852298453547041751507395386964782915158024033183011647450189883974730693070675549316164872391041740265631496736007525533800960232654817254380372561151693373065315534946392034628284241065699675767636897824346676241444275179476815141232357537534335191039899207104158981715233438876341225628953135565990865939830962896392607929698931820677375954742078471802036744483492592516314129857657953560039388006311965597276015823813704229779858696987563016953510256938068826465623169689826626920699128771264958404721311572983053992924528800877039915288015419196076881887175783024786982762935085980959721642999232359939033875406508546066706050034836631857425661476512776656865066361799448861800980537800029417657757499763263137811085859029820884083088269073792428480572320403455369051932151726581001691109997369981928475883238231199335681852260475878112500432217350393387693386184904110749254667534998503852290132517247483159212445761586627811892552968743250107981065351634129462633050650153433221375774786048861855825867017674988581457669040437133681488855655263766777305154048585274098587056848508776364391162925775494739133566306228883868601380840500792549132039533109829512491086557291482764776558169204745081716296123384589136624739406086968230600026982718837361921446029818316345404374395396733103555849995891357582576827055103109343909761434967312642761541147714678686780848152062142819723759363589815095972892546522886437922974804745108329327670456521737771939243119507384964084364712578970187695836212057047547679021658560714376458799236081350810025846462889331166225258859739163127200595585143808079379484006778546441868509603943631119289386065232593550150950104623248313325284939524794332706971099186351660720614220251259457997529091787924320354856722584018363468010207155038358117701534144388142559207615066762234287480984661263586980133567408643754943853996132963979243797064943384297602505603428206246772028639561532059738969473611472532036651659727182768623719890109474721402696289889380608916153558395444093439332883105550701333269352190009193753613361385726667196274998359422112352877886436248946005545124712236948938992016775146806727281764240839464326154550854052005239281657823276671369089150846199069917855948925735301816283368448046883172384792245526609193808155789717494945769207978980709344447855484891856896236731861945792302936529153823195703568655238350046396865804409672988546022086728411235004254153232801491745340298845692838580381364051616785944124891800442038903441562210477872968900854217416782222681576430163810278359495006388573266405889363579219036879958900433423329703794150168832561441846902914835516282393761629777584835458207461635440180179694459583822456896013875074673483345471105126490744416310608994310692332232545377049647802872832000327934135635329442056964772987545116005813130920759658791283232426913587054455831915260013651792560298032203289545995042264114167911240120716205042244365980175242794016464193932157549710230435967734970481395002197228053475706655853429805762611752195001872005404048421983733561671179891899698793321045585752205991603238123461172775630046696714597122426583397576664080044427546377838930858513591493237952521897441949593036527213190424365061300937976857634204091654279870716643058336632500926718984495433592875983029257997693627296241182994956664593308175897898784742989803783136577058685252296068567855441804618882285491868500397502281610671331626899606516669412497507700330545523144242669378978746357006460960064324371881283244371731816500132523009911364302315367911092709096153306984361305106038348059528422436647736523968237314351287836224352541092107630775599061966530504695555458181426062244073596571878124241705913199739934984251572088366702556041591186636742512333740019845329537822707976089789544649168867679608629249956349922283207530635778229647427673865610055287692970998351141324488664814538092060814836652415336782543595908423637770003903190265643376438253703074701597472302782545481626459637100296300059020096010623295115048459003569632080889430786898049968341607361658053527305536680292438112342606749715449373850609029421944112338899576209600067368253594434712569234593948538050985701699867930134427953777791440440978972462061429273878378633322471749683594297548081065019173540101461874821972130313105768986762162969964245073031096685761739320553792231157655986902416779011812136888359236050531680251228806220616449724467850376225275720124283846011479334154831218180821434958119483220650537391892781950597766883852471301711511993321266578849819088794769466043060273319845004303770275130137229532721599065503303621760463260751833607755052671220047858883971260938228811597720274560360191006477452949833052366895491786098280295866707304504286595379227101271354200095085780922657926955733148359345656417869132436922310403860643793868993997790830725448582835006344572839537455056649507069871743232767350155336390047549281627734240963613351704494556865605085419211070211922980390349350260435311937929102316169628117756937237323979456580596013599694527727765889159148873659050327668446495877307366939866863414705685444184899126346508117880074214034369791939304165187978501542612500998276422584830060193665392417512616012949915156068206946517819502050922008380181224052578281039078439084379793478409763995368873584479020778323381976514428173853572147893952308943122478758564286375624494767674943582749107410114434746192196284909137884185033523978800610118523076284771002023802982974095736614708723871492763143809645326393711991030742562273841802226836239940019438945560472408028760214548084978053160702955499796876198145375937813530273306544642087605883560795554362039296995233327581576436184571333776012828962949633832019370579072991454164168561766791595925989687331452873385990371401557592329797397164432144836871666442064035383441825795188714904083422373759176207223326008785832918057954865758120362438491528380984976246175015916639550859680124284943931975868648631787209005180948457206775607748250062019543294326448292729483561722755044438082624511134936427447976011387131653375229637663118609572466595744276047993291851744747227069136334467401302472156869165089786467174053515453503685541775128204919407545078883548284834152272288370595753819799213831414405358259596525702383437807246661095099366921104294318953342158663508454986733221148713978288540542989856025818359037846074929085789122847567005059587907719028760327867446421400325912512732626637427215627474109772384038580810823197189200628860048807370527097892289339932724368400289775845923414881556996686398022411993898527773016552301552373186953810052493705820891650238068320260308246651368595828542372462947395034875307507957134195673795229125038637923528720991073527392248435218410264106102294434505396253213575059062818075034498982874347146335972002071948582009677193254325369817776660938071237152834234218828652734307101644068301549571353432387559001548450619138482432679334590802990074245091546389737201417291104557319138445723027001754219196976218846052942910950392080178265900570018209200900597262466841941025365534581013708843422542316376077683877541579000377991835037396099049253374374775461657029201567322105244664315815451522162750991248305343168589419306235924796536594349783033299692144095047848459741047766176924149537720420579528332916732399937726390068599787235589684876621602199146858255572910028348169738047077799669893235011839297512469067560810980932614294270421852459786842556619144002829322818474308487790680830975562487108276885894363257599044620068714000839317879710562843390938231490984753335058125209202165679158616441812375648430520771706865215036675657757106669668564394664595127590500999816613741376192756818190016545168876001450597684437906825663684527929051057158262954722428308267741372203570673249258652913800297830716121490211529787687364579256056355208901200943172431197226182801909725367797317701213222862160567821546744432268150250691820880446144926600277811797714959127823878767005712831950885819102681062870291681031058067404624172387020568019917037263006397401750401453041236769424163136877552526803852050175688417132269912190484587491555232967021290788786596096315670878562989100836018274506027912760792620660011230216607296779421045966904678389394553988100183589575045700868985581690881858781081513045871822501956063312590784206919508355939545770802980568224288044107183606341457428101032091986769833679546689938237238694863296760358994956725888332707763083958907910949120728855501990788610005562990888602741438772646095774557628383746308935012474495070753752376376168389656820860776046491694741109031122669146159505566278729195576251439356602422825902922436830916315554647512782754841964014838905811929620409707216678718774872909248292289593485110636542198536876013184392844256399738633019299640984120723449128352415924325030648734697713548014913077225301060431581287987007161970968310418499869793857548566048131348466493522811385398006860447614118727231725894367812719593756976241960064575593002869270369774206833542794835876943622326153738141195505684774458312624069273201782341686229767945204049737490823711727155207100061135250543894191267826943716933482038459375349832962532201502079443487506248512710490088765089195177303156264935065648211350257301124619955921035105035684144326488744173212995087171760829451335200134831471166393766863315539289614507806592202573041773461509295853809174753966003181002793036201419161719843189075404701002456343356133239706490887238087131710536788507749305688689064714431849905640255942689901419569627878591677160160023112635754241487528738460932858575363549702767754136341028026751716688734230373280721023464710345619989061091921278083183150316024996365872787749607664375126493685369269181444392590969954537159277506272089253638187500533114168100222063671668516608189343599385659099579478929061394957825020809198959092969261348830729754761497884303965880815260951128014617329000313924016390756373237160305715558037237973003521782920387963643381460722618632533655450207052046382727336452556654886955264087638800034724880839015789149103800855760115642193058802229481237368425429482795593408190565725150044812684286167829189970359654711579559651441543713348342389797474013846964292522807112682721319423001945549119140757980229395630747797572322177528519088098309812091399565268710036836559915731313113454800140368281124738268379029315717323513696298968529474037956516699828934370517616409306361535441146656381819436443384967553661641740869579636690249675572854473747001838158888611430549164713777905891637869971678937852386860755207168258178638513505401351176239309894657476045540166053077460795238769393446943405532439075401872628103631307890574772782474204062455541487196443760894703023952484252394634564694822444052283364209011451333977932913542686782437857204180523624548748637841451402666389683566585562095534305136491573708751791312398494686938538753676568438095997730354711341953793626925021061764766295022721346791691722067113577305206769733208599549310221150101885203782188258713713445921450650616519467603186179842504955224989605457191582688884475510225744275786906047770737720768660251755110051432200610975267551609376604916548751099546150219531252000538625349630696500330607160366699596629125360923413326650530077867706196570799810058265159567502550642207882854046635768293740724489165613720928974660211942162730101929718362924630905680648137552043027264729211872531345159235051253700370144475554164291663325948268692630889442206979292607218787039057692402279532073583216287136585985866227274616976523031025141296469158141215979753918614237508292116817368480546387159766077289122033915728965089077550278302120815388268761713810937626876059981032014901599994264172960369445351126442611577874855172801860993254088125857489327776924813485669639392665336733452614403867491918144941643086664623587916496781810714252008919464569391954412944331261695600229364414225587139632821487723908216489818819894423170203985995645168899828516420582987066489592846066967402173630973795687201269550157633136619676824390970140999024235573608637882267218367866955395344094583867149518448546110239527891875522277599991232118293629744349873486794780835163943877688862236725471062654647775354041659961121450100889695409609331716040769743823224745931146389609977218648389956517374224767401697514636573187180913511575239749617406556353240101201561976957803975840971440807044602128884715718784728261018817289906546122151551726820314902956892488728352187186742854857832829596193082099472212385577689346674967331879600654424199120680813208218926827137636861895671069309418783776992728420180430655166519475701545940660925247068473060544431298270411984718314593404311407878434974232205568949545509233156979455046429257021253334139602860845563951265791261752078633009599443085643327302324403911374414400300289786855807878695745228000142750549275406674751339507373463589838038586232480161395152449534692691953359131380170509301069446425633971974396270086713742990461437281216223907843854308144769626503742054256992830321038964242624918275869233400754276685092653359174981947900798490622212468865323853490437477077396362705450136899779891325429070694218548656151154074363105498093061030132533594771075890958272728751564510627249039660223812311048344563572916459355584833597471368845134476286806043476456771788610030651742956062448760287134303684486887050202303307662344452685341237493057036452764805391219481756241068006982732812174829423618581273193212314088411731681323948367796961005422311479154951605921168978749289296117248769180867610251158051040806403577514923808950832288444022757846972427652714400852040080743305187382281666217495438824311057915473693264741735018599628309751326199314867792404141019348693870043124941986612994425864793954959917337684908982985143483673808113462804874920612743519595216744609466175661294771134610622705646619548027555488097322235019933966095656570550334285284224799537726415079093811689351132668842566013669065893290538560700275101862856768104982693638680423806495056141351940767846044254668603806932700523953150306078283534779643253006276255996595964630960205636226703026269523751751347913678471615078509196548342365889898987017990671039373766857389396607569075140430702372028188401529458160399436609429152874455268589214361196635979238126580489287765589888779357205343198422526678082233287215577021845408513932115735782013735651769198975664916007521831716116397463997835072472677765389387824491148855592171366615511386985378581109635624360462156509928820078661990843789172843935804198704066810990590192609305316394475793

noncomputable def bx0 : SixW8.Box := (SixW8.Box.mk 30720 39936 31744 38400 31744 38400 31744 38400 30720 39936)

theorem wk0 : SixW8.walk table bits 64 0 bx0 = some 1351 := by decide +kernel

noncomputable def bx1 : SixW8.Box := (SixW8.Box.mk 30720 39936 31744 38400 31744 38400 31744 38400 57344 434176)

theorem wk1 : SixW8.walk table bits 64 1351 bx1 = some 4927 := by decide +kernel

noncomputable def bx2 : SixW8.Box := (SixW8.Box.mk 30720 39936 31744 38400 31744 38400 59904 74752 30720 39936)

theorem wk2 : SixW8.walk table bits 64 4927 bx2 = some 8288 := by decide +kernel

noncomputable def bx3 : SixW8.Box := (SixW8.Box.mk 30720 39936 31744 38400 31744 38400 59904 74752 57344 434176)

theorem wk3 : SixW8.walk table bits 64 8288 bx3 = some 12009 := by decide +kernel

noncomputable def bx4 : SixW8.Box := (SixW8.Box.mk 30720 39936 31744 38400 31744 38400 88576 262144 30720 39936)

theorem wk4 : SixW8.walk table bits 64 12009 bx4 = some 13460 := by decide +kernel

noncomputable def bx5 : SixW8.Box := (SixW8.Box.mk 30720 39936 31744 38400 31744 38400 88576 262144 57344 434176)

theorem wk5 : SixW8.walk table bits 64 13460 bx5 = some 14371 := by decide +kernel

noncomputable def bx6 : SixW8.Box := (SixW8.Box.mk 30720 39936 31744 38400 60416 74240 31744 38400 30720 39936)

theorem wk6 : SixW8.walk table bits 64 14371 bx6 = some 17857 := by decide +kernel

noncomputable def bx7 : SixW8.Box := (SixW8.Box.mk 30720 39936 31744 38400 60416 74240 31744 38400 57344 434176)

noncomputable def bx8 : SixW8.Box := (bx7).setHi (SixW8.axOf bits 17857) (SixW8.Box.mid bx7 (SixW8.axOf bits 17857))

noncomputable def bx9 : SixW8.Box := (bx8).setHi (SixW8.axOf bits 17861) (SixW8.Box.mid bx8 (SixW8.axOf bits 17861))

noncomputable def bx10 : SixW8.Box := (bx9).setHi (SixW8.axOf bits 17865) (SixW8.Box.mid bx9 (SixW8.axOf bits 17865))

noncomputable def bx11 : SixW8.Box := (bx10).setHi (SixW8.axOf bits 17869) (SixW8.Box.mid bx10 (SixW8.axOf bits 17869))

theorem wk11 : SixW8.walk table bits 60 17873 bx11 = some 22039 := by decide +kernel

noncomputable def bx12 : SixW8.Box := (bx10).setLo (SixW8.axOf bits 17869) (SixW8.Box.mid bx10 (SixW8.axOf bits 17869))

theorem wk12 : SixW8.walk table bits 60 22039 bx12 = some 23030 := by decide +kernel

theorem wk10 : SixW8.walk table bits 61 17869 bx10 = some 23030 :=
  SixW8.walk_split table bits 60 17869 bx10 22039 23030 (by decide +kernel) wk11 wk12

noncomputable def bx13 : SixW8.Box := (bx9).setLo (SixW8.axOf bits 17865) (SixW8.Box.mid bx9 (SixW8.axOf bits 17865))

theorem wk13 : SixW8.walk table bits 61 23030 bx13 = some 23466 := by decide +kernel

theorem wk9 : SixW8.walk table bits 62 17865 bx9 = some 23466 :=
  SixW8.walk_split table bits 61 17865 bx9 23030 23466 (by decide +kernel) wk10 wk13

noncomputable def bx14 : SixW8.Box := (bx8).setLo (SixW8.axOf bits 17861) (SixW8.Box.mid bx8 (SixW8.axOf bits 17861))

theorem wk14 : SixW8.walk table bits 62 23466 bx14 = some 23602 := by decide +kernel

theorem wk8 : SixW8.walk table bits 63 17861 bx8 = some 23602 :=
  SixW8.walk_split table bits 62 17861 bx8 23466 23602 (by decide +kernel) wk9 wk14

noncomputable def bx15 : SixW8.Box := (bx7).setLo (SixW8.axOf bits 17857) (SixW8.Box.mid bx7 (SixW8.axOf bits 17857))

theorem wk15 : SixW8.walk table bits 63 23602 bx15 = some 23603 := by decide +kernel

theorem wk7 : SixW8.walk table bits 64 17857 bx7 = some 23603 :=
  SixW8.walk_split table bits 63 17857 bx7 23602 23603 (by decide +kernel) wk8 wk15

noncomputable def bx16 : SixW8.Box := (SixW8.Box.mk 30720 39936 31744 38400 60416 74240 59904 74752 30720 39936)

theorem wk16 : SixW8.walk table bits 64 23603 bx16 = some 26339 := by decide +kernel

noncomputable def bx17 : SixW8.Box := (SixW8.Box.mk 30720 39936 31744 38400 60416 74240 59904 74752 57344 434176)

theorem wk17 : SixW8.walk table bits 64 26339 bx17 = some 27580 := by decide +kernel

noncomputable def bx18 : SixW8.Box := (SixW8.Box.mk 30720 39936 31744 38400 60416 74240 88576 262144 30720 39936)

theorem wk18 : SixW8.walk table bits 64 27580 bx18 = some 27991 := by decide +kernel

noncomputable def bx19 : SixW8.Box := (SixW8.Box.mk 30720 39936 31744 38400 60416 74240 88576 262144 57344 434176)

theorem wk19 : SixW8.walk table bits 64 27991 bx19 = some 28102 := by decide +kernel

noncomputable def bx20 : SixW8.Box := (SixW8.Box.mk 30720 39936 31744 38400 89088 237568 31744 38400 30720 39936)

theorem wk20 : SixW8.walk table bits 64 28102 bx20 = some 29438 := by decide +kernel

noncomputable def bx21 : SixW8.Box := (SixW8.Box.mk 30720 39936 31744 38400 89088 237568 31744 38400 57344 434176)

theorem wk21 : SixW8.walk table bits 64 29438 bx21 = some 30309 := by decide +kernel

noncomputable def bx22 : SixW8.Box := (SixW8.Box.mk 30720 39936 31744 38400 89088 237568 59904 74752 30720 39936)

theorem wk22 : SixW8.walk table bits 64 30309 bx22 = some 30685 := by decide +kernel

noncomputable def bx23 : SixW8.Box := (SixW8.Box.mk 30720 39936 31744 38400 89088 237568 59904 74752 57344 434176)

theorem wk23 : SixW8.walk table bits 64 30685 bx23 = some 30776 := by decide +kernel

noncomputable def bx24 : SixW8.Box := (SixW8.Box.mk 30720 39936 31744 38400 89088 237568 88576 262144 30720 39936)

theorem wk24 : SixW8.walk table bits 64 30776 bx24 = some 30817 := by decide +kernel

noncomputable def bx25 : SixW8.Box := (SixW8.Box.mk 30720 39936 31744 38400 89088 237568 88576 262144 57344 434176)

theorem wk25 : SixW8.walk table bits 64 30817 bx25 = some 30818 := by decide +kernel

noncomputable def bx26 : SixW8.Box := (SixW8.Box.mk 30720 39936 59904 74752 31744 38400 31744 38400 30720 39936)

theorem wk26 : SixW8.walk table bits 64 30818 bx26 = some 33979 := by decide +kernel

noncomputable def bx27 : SixW8.Box := (SixW8.Box.mk 30720 39936 59904 74752 31744 38400 31744 38400 57344 434176)

noncomputable def bx28 : SixW8.Box := (bx27).setHi (SixW8.axOf bits 33979) (SixW8.Box.mid bx27 (SixW8.axOf bits 33979))

noncomputable def bx29 : SixW8.Box := (bx28).setHi (SixW8.axOf bits 33983) (SixW8.Box.mid bx28 (SixW8.axOf bits 33983))

noncomputable def bx30 : SixW8.Box := (bx29).setHi (SixW8.axOf bits 33987) (SixW8.Box.mid bx29 (SixW8.axOf bits 33987))

noncomputable def bx31 : SixW8.Box := (bx30).setHi (SixW8.axOf bits 33991) (SixW8.Box.mid bx30 (SixW8.axOf bits 33991))

noncomputable def bx32 : SixW8.Box := (bx31).setHi (SixW8.axOf bits 33995) (SixW8.Box.mid bx31 (SixW8.axOf bits 33995))

noncomputable def bx33 : SixW8.Box := (bx32).setHi (SixW8.axOf bits 33999) (SixW8.Box.mid bx32 (SixW8.axOf bits 33999))

theorem wk33 : SixW8.walk table bits 58 34003 bx33 = some 34284 := by decide +kernel

noncomputable def bx34 : SixW8.Box := (bx32).setLo (SixW8.axOf bits 33999) (SixW8.Box.mid bx32 (SixW8.axOf bits 33999))

noncomputable def bx35 : SixW8.Box := (bx34).setHi (SixW8.axOf bits 34284) (SixW8.Box.mid bx34 (SixW8.axOf bits 34284))

noncomputable def bx36 : SixW8.Box := (bx35).setHi (SixW8.axOf bits 34288) (SixW8.Box.mid bx35 (SixW8.axOf bits 34288))

theorem wk36 : SixW8.walk table bits 56 34292 bx36 = some 34388 := by decide +kernel

noncomputable def bx37 : SixW8.Box := (bx35).setLo (SixW8.axOf bits 34288) (SixW8.Box.mid bx35 (SixW8.axOf bits 34288))

noncomputable def bx38 : SixW8.Box := (bx37).setHi (SixW8.axOf bits 34388) (SixW8.Box.mid bx37 (SixW8.axOf bits 34388))

theorem wk38 : SixW8.walk table bits 55 34392 bx38 = some 38273 := by decide +kernel

noncomputable def bx39 : SixW8.Box := (bx37).setLo (SixW8.axOf bits 34388) (SixW8.Box.mid bx37 (SixW8.axOf bits 34388))

theorem wk39 : SixW8.walk table bits 55 38273 bx39 = some 39479 := by decide +kernel

theorem wk37 : SixW8.walk table bits 56 34388 bx37 = some 39479 :=
  SixW8.walk_split table bits 55 34388 bx37 38273 39479 (by decide +kernel) wk38 wk39

theorem wk35 : SixW8.walk table bits 57 34288 bx35 = some 39479 :=
  SixW8.walk_split table bits 56 34288 bx35 34388 39479 (by decide +kernel) wk36 wk37

noncomputable def bx40 : SixW8.Box := (bx34).setLo (SixW8.axOf bits 34284) (SixW8.Box.mid bx34 (SixW8.axOf bits 34284))

theorem wk40 : SixW8.walk table bits 57 39479 bx40 = some 39580 := by decide +kernel

theorem wk34 : SixW8.walk table bits 58 34284 bx34 = some 39580 :=
  SixW8.walk_split table bits 57 34284 bx34 39479 39580 (by decide +kernel) wk35 wk40

theorem wk32 : SixW8.walk table bits 59 33999 bx32 = some 39580 :=
  SixW8.walk_split table bits 58 33999 bx32 34284 39580 (by decide +kernel) wk33 wk34

noncomputable def bx41 : SixW8.Box := (bx31).setLo (SixW8.axOf bits 33995) (SixW8.Box.mid bx31 (SixW8.axOf bits 33995))

theorem wk41 : SixW8.walk table bits 59 39580 bx41 = some 39626 := by decide +kernel

theorem wk31 : SixW8.walk table bits 60 33995 bx31 = some 39626 :=
  SixW8.walk_split table bits 59 33995 bx31 39580 39626 (by decide +kernel) wk32 wk41

noncomputable def bx42 : SixW8.Box := (bx30).setLo (SixW8.axOf bits 33991) (SixW8.Box.mid bx30 (SixW8.axOf bits 33991))

theorem wk42 : SixW8.walk table bits 60 39626 bx42 = some 40907 := by decide +kernel

theorem wk30 : SixW8.walk table bits 61 33991 bx30 = some 40907 :=
  SixW8.walk_split table bits 60 33991 bx30 39626 40907 (by decide +kernel) wk31 wk42

noncomputable def bx43 : SixW8.Box := (bx29).setLo (SixW8.axOf bits 33987) (SixW8.Box.mid bx29 (SixW8.axOf bits 33987))

theorem wk43 : SixW8.walk table bits 61 40907 bx43 = some 41513 := by decide +kernel

theorem wk29 : SixW8.walk table bits 62 33987 bx29 = some 41513 :=
  SixW8.walk_split table bits 61 33987 bx29 40907 41513 (by decide +kernel) wk30 wk43

noncomputable def bx44 : SixW8.Box := (bx28).setLo (SixW8.axOf bits 33983) (SixW8.Box.mid bx28 (SixW8.axOf bits 33983))

theorem wk44 : SixW8.walk table bits 62 41513 bx44 = some 41699 := by decide +kernel

theorem wk28 : SixW8.walk table bits 63 33983 bx28 = some 41699 :=
  SixW8.walk_split table bits 62 33983 bx28 41513 41699 (by decide +kernel) wk29 wk44

noncomputable def bx45 : SixW8.Box := (bx27).setLo (SixW8.axOf bits 33979) (SixW8.Box.mid bx27 (SixW8.axOf bits 33979))

theorem wk45 : SixW8.walk table bits 63 41699 bx45 = some 41700 := by decide +kernel

theorem wk27 : SixW8.walk table bits 64 33979 bx27 = some 41700 :=
  SixW8.walk_split table bits 63 33979 bx27 41699 41700 (by decide +kernel) wk28 wk45

noncomputable def bx46 : SixW8.Box := (SixW8.Box.mk 30720 39936 59904 74752 31744 38400 59904 74752 30720 39936)

noncomputable def bx47 : SixW8.Box := (bx46).setHi (SixW8.axOf bits 41700) (SixW8.Box.mid bx46 (SixW8.axOf bits 41700))

noncomputable def bx48 : SixW8.Box := (bx47).setHi (SixW8.axOf bits 41704) (SixW8.Box.mid bx47 (SixW8.axOf bits 41704))

theorem wk48 : SixW8.walk table bits 62 41708 bx48 = some 41764 := by decide +kernel

noncomputable def bx49 : SixW8.Box := (bx47).setLo (SixW8.axOf bits 41704) (SixW8.Box.mid bx47 (SixW8.axOf bits 41704))

noncomputable def bx50 : SixW8.Box := (bx49).setHi (SixW8.axOf bits 41764) (SixW8.Box.mid bx49 (SixW8.axOf bits 41764))

noncomputable def bx51 : SixW8.Box := (bx50).setHi (SixW8.axOf bits 41768) (SixW8.Box.mid bx50 (SixW8.axOf bits 41768))

theorem wk51 : SixW8.walk table bits 60 41772 bx51 = some 41813 := by decide +kernel

noncomputable def bx52 : SixW8.Box := (bx50).setLo (SixW8.axOf bits 41768) (SixW8.Box.mid bx50 (SixW8.axOf bits 41768))

noncomputable def bx53 : SixW8.Box := (bx52).setHi (SixW8.axOf bits 41813) (SixW8.Box.mid bx52 (SixW8.axOf bits 41813))

noncomputable def bx54 : SixW8.Box := (bx53).setHi (SixW8.axOf bits 41817) (SixW8.Box.mid bx53 (SixW8.axOf bits 41817))

theorem wk54 : SixW8.walk table bits 58 41821 bx54 = some 46517 := by decide +kernel

noncomputable def bx55 : SixW8.Box := (bx53).setLo (SixW8.axOf bits 41817) (SixW8.Box.mid bx53 (SixW8.axOf bits 41817))

theorem wk55 : SixW8.walk table bits 58 46517 bx55 = some 48498 := by decide +kernel

theorem wk53 : SixW8.walk table bits 59 41817 bx53 = some 48498 :=
  SixW8.walk_split table bits 58 41817 bx53 46517 48498 (by decide +kernel) wk54 wk55

noncomputable def bx56 : SixW8.Box := (bx52).setLo (SixW8.axOf bits 41813) (SixW8.Box.mid bx52 (SixW8.axOf bits 41813))

theorem wk56 : SixW8.walk table bits 59 48498 bx56 = some 51194 := by decide +kernel

theorem wk52 : SixW8.walk table bits 60 41813 bx52 = some 51194 :=
  SixW8.walk_split table bits 59 41813 bx52 48498 51194 (by decide +kernel) wk53 wk56

theorem wk50 : SixW8.walk table bits 61 41768 bx50 = some 51194 :=
  SixW8.walk_split table bits 60 41768 bx50 41813 51194 (by decide +kernel) wk51 wk52

noncomputable def bx57 : SixW8.Box := (bx49).setLo (SixW8.axOf bits 41764) (SixW8.Box.mid bx49 (SixW8.axOf bits 41764))

theorem wk57 : SixW8.walk table bits 61 51194 bx57 = some 51290 := by decide +kernel

theorem wk49 : SixW8.walk table bits 62 41764 bx49 = some 51290 :=
  SixW8.walk_split table bits 61 41764 bx49 51194 51290 (by decide +kernel) wk50 wk57

theorem wk47 : SixW8.walk table bits 63 41704 bx47 = some 51290 :=
  SixW8.walk_split table bits 62 41704 bx47 41764 51290 (by decide +kernel) wk48 wk49

noncomputable def bx58 : SixW8.Box := (bx46).setLo (SixW8.axOf bits 41700) (SixW8.Box.mid bx46 (SixW8.axOf bits 41700))

theorem wk58 : SixW8.walk table bits 63 51290 bx58 = some 51436 := by decide +kernel

theorem wk46 : SixW8.walk table bits 64 41700 bx46 = some 51436 :=
  SixW8.walk_split table bits 63 41700 bx46 51290 51436 (by decide +kernel) wk47 wk58

noncomputable def bx59 : SixW8.Box := (SixW8.Box.mk 30720 39936 59904 74752 31744 38400 59904 74752 57344 434176)

theorem wk59 : SixW8.walk table bits 64 51436 bx59 = some 55637 := by decide +kernel

noncomputable def bx60 : SixW8.Box := (SixW8.Box.mk 30720 39936 59904 74752 31744 38400 88576 262144 30720 39936)

theorem wk60 : SixW8.walk table bits 64 55637 bx60 = some 56418 := by decide +kernel

noncomputable def bx61 : SixW8.Box := (SixW8.Box.mk 30720 39936 59904 74752 31744 38400 88576 262144 57344 434176)

theorem wk61 : SixW8.walk table bits 64 56418 bx61 = some 56564 := by decide +kernel

noncomputable def bx62 : SixW8.Box := (SixW8.Box.mk 30720 39936 59904 74752 60416 74240 31744 38400 30720 39936)

theorem wk62 : SixW8.walk table bits 64 56564 bx62 = some 59095 := by decide +kernel

noncomputable def bx63 : SixW8.Box := (SixW8.Box.mk 30720 39936 59904 74752 60416 74240 31744 38400 57344 434176)

theorem wk63 : SixW8.walk table bits 64 59095 bx63 = some 62606 := by decide +kernel

noncomputable def bx64 : SixW8.Box := (SixW8.Box.mk 30720 39936 59904 74752 60416 74240 59904 74752 30720 39936)

theorem wk64 : SixW8.walk table bits 64 62606 bx64 = some 63372 := by decide +kernel

noncomputable def bx65 : SixW8.Box := (SixW8.Box.mk 30720 39936 59904 74752 60416 74240 59904 74752 57344 434176)

theorem wk65 : SixW8.walk table bits 64 63372 bx65 = some 63483 := by decide +kernel

noncomputable def bx66 : SixW8.Box := (SixW8.Box.mk 30720 39936 59904 74752 60416 74240 88576 262144 30720 39936)

theorem wk66 : SixW8.walk table bits 64 63483 bx66 = some 63514 := by decide +kernel

noncomputable def bx67 : SixW8.Box := (SixW8.Box.mk 30720 39936 59904 74752 60416 74240 88576 262144 57344 434176)

theorem wk67 : SixW8.walk table bits 64 63514 bx67 = some 63515 := by decide +kernel

noncomputable def bx68 : SixW8.Box := (SixW8.Box.mk 30720 39936 59904 74752 89088 237568 31744 38400 30720 39936)

theorem wk68 : SixW8.walk table bits 64 63515 bx68 = some 63886 := by decide +kernel

noncomputable def bx69 : SixW8.Box := (SixW8.Box.mk 30720 39936 59904 74752 89088 237568 31744 38400 57344 434176)

theorem wk69 : SixW8.walk table bits 64 63886 bx69 = some 63977 := by decide +kernel

noncomputable def bx70 : SixW8.Box := (SixW8.Box.mk 30720 39936 59904 74752 89088 237568 59904 74752 30720 39936)

theorem wk70 : SixW8.walk table bits 64 63977 bx70 = some 64003 := by decide +kernel

noncomputable def bx71 : SixW8.Box := (SixW8.Box.mk 30720 39936 59904 74752 89088 237568 59904 74752 57344 434176)

theorem wk71 : SixW8.walk table bits 64 64003 bx71 = some 64004 := by decide +kernel

noncomputable def bx72 : SixW8.Box := (SixW8.Box.mk 30720 39936 59904 74752 89088 237568 88576 262144 30720 39936)

theorem wk72 : SixW8.walk table bits 64 64004 bx72 = some 64005 := by decide +kernel

noncomputable def bx73 : SixW8.Box := (SixW8.Box.mk 30720 39936 59904 74752 89088 237568 88576 262144 57344 434176)

theorem wk73 : SixW8.walk table bits 64 64005 bx73 = some 64006 := by decide +kernel

noncomputable def bx74 : SixW8.Box := (SixW8.Box.mk 30720 39936 88576 262144 31744 38400 31744 38400 30720 39936)

theorem wk74 : SixW8.walk table bits 64 64006 bx74 = some 65387 := by decide +kernel

noncomputable def bx75 : SixW8.Box := (SixW8.Box.mk 30720 39936 88576 262144 31744 38400 31744 38400 57344 434176)

theorem wk75 : SixW8.walk table bits 64 65387 bx75 = some 66783 := by decide +kernel

noncomputable def bx76 : SixW8.Box := (SixW8.Box.mk 30720 39936 88576 262144 31744 38400 59904 74752 30720 39936)

theorem wk76 : SixW8.walk table bits 64 66783 bx76 = some 67564 := by decide +kernel

noncomputable def bx77 : SixW8.Box := (SixW8.Box.mk 30720 39936 88576 262144 31744 38400 59904 74752 57344 434176)

theorem wk77 : SixW8.walk table bits 64 67564 bx77 = some 67710 := by decide +kernel

noncomputable def bx78 : SixW8.Box := (SixW8.Box.mk 30720 39936 88576 262144 31744 38400 88576 262144 30720 39936)

theorem wk78 : SixW8.walk table bits 64 67710 bx78 = some 67761 := by decide +kernel

noncomputable def bx79 : SixW8.Box := (SixW8.Box.mk 30720 39936 88576 262144 31744 38400 88576 262144 57344 434176)

theorem wk79 : SixW8.walk table bits 64 67761 bx79 = some 67762 := by decide +kernel

noncomputable def bx80 : SixW8.Box := (SixW8.Box.mk 30720 39936 88576 262144 60416 74240 31744 38400 30720 39936)

theorem wk80 : SixW8.walk table bits 64 67762 bx80 = some 68163 := by decide +kernel

noncomputable def bx81 : SixW8.Box := (SixW8.Box.mk 30720 39936 88576 262144 60416 74240 31744 38400 57344 434176)

theorem wk81 : SixW8.walk table bits 64 68163 bx81 = some 68274 := by decide +kernel

noncomputable def bx82 : SixW8.Box := (SixW8.Box.mk 30720 39936 88576 262144 60416 74240 59904 74752 30720 39936)

theorem wk82 : SixW8.walk table bits 64 68274 bx82 = some 68305 := by decide +kernel

noncomputable def bx83 : SixW8.Box := (SixW8.Box.mk 30720 39936 88576 262144 60416 74240 59904 74752 57344 434176)

theorem wk83 : SixW8.walk table bits 64 68305 bx83 = some 68306 := by decide +kernel

noncomputable def bx84 : SixW8.Box := (SixW8.Box.mk 30720 39936 88576 262144 60416 74240 88576 262144 30720 39936)

theorem wk84 : SixW8.walk table bits 64 68306 bx84 = some 68307 := by decide +kernel

noncomputable def bx85 : SixW8.Box := (SixW8.Box.mk 30720 39936 88576 262144 60416 74240 88576 262144 57344 434176)

theorem wk85 : SixW8.walk table bits 64 68307 bx85 = some 68308 := by decide +kernel

noncomputable def bx86 : SixW8.Box := (SixW8.Box.mk 30720 39936 88576 262144 89088 237568 31744 38400 30720 39936)

theorem wk86 : SixW8.walk table bits 64 68308 bx86 = some 68349 := by decide +kernel

noncomputable def bx87 : SixW8.Box := (SixW8.Box.mk 30720 39936 88576 262144 89088 237568 31744 38400 57344 434176)

theorem wk87 : SixW8.walk table bits 64 68349 bx87 = some 68350 := by decide +kernel

noncomputable def bx88 : SixW8.Box := (SixW8.Box.mk 30720 39936 88576 262144 89088 237568 59904 74752 30720 39936)

theorem wk88 : SixW8.walk table bits 64 68350 bx88 = some 68351 := by decide +kernel

noncomputable def bx89 : SixW8.Box := (SixW8.Box.mk 30720 39936 88576 262144 89088 237568 59904 74752 57344 434176)

theorem wk89 : SixW8.walk table bits 64 68351 bx89 = some 68352 := by decide +kernel

noncomputable def bx90 : SixW8.Box := (SixW8.Box.mk 30720 39936 88576 262144 89088 237568 88576 262144 30720 39936)

theorem wk90 : SixW8.walk table bits 64 68352 bx90 = some 68353 := by decide +kernel

noncomputable def bx91 : SixW8.Box := (SixW8.Box.mk 30720 39936 88576 262144 89088 237568 88576 262144 57344 434176)

theorem wk91 : SixW8.walk table bits 64 68353 bx91 = some 68354 := by decide +kernel

noncomputable def bx92 : SixW8.Box := (SixW8.Box.mk 57344 434176 31744 38400 31744 38400 31744 38400 30720 39936)

theorem wk92 : SixW8.walk table bits 64 68354 bx92 = some 68355 := by decide +kernel

noncomputable def bx93 : SixW8.Box := (SixW8.Box.mk 57344 434176 31744 38400 31744 38400 31744 38400 57344 434176)

theorem wk93 : SixW8.walk table bits 64 68355 bx93 = some 72406 := by decide +kernel

noncomputable def bx94 : SixW8.Box := (SixW8.Box.mk 57344 434176 31744 38400 31744 38400 59904 74752 30720 39936)

theorem wk94 : SixW8.walk table bits 64 72406 bx94 = some 72407 := by decide +kernel

noncomputable def bx95 : SixW8.Box := (SixW8.Box.mk 57344 434176 31744 38400 31744 38400 59904 74752 57344 434176)

theorem wk95 : SixW8.walk table bits 64 72407 bx95 = some 76268 := by decide +kernel

noncomputable def bx96 : SixW8.Box := (SixW8.Box.mk 57344 434176 31744 38400 31744 38400 88576 262144 30720 39936)

theorem wk96 : SixW8.walk table bits 64 76268 bx96 = some 76269 := by decide +kernel

noncomputable def bx97 : SixW8.Box := (SixW8.Box.mk 57344 434176 31744 38400 31744 38400 88576 262144 57344 434176)

theorem wk97 : SixW8.walk table bits 64 76269 bx97 = some 76615 := by decide +kernel

noncomputable def bx98 : SixW8.Box := (SixW8.Box.mk 57344 434176 31744 38400 60416 74240 31744 38400 30720 39936)

theorem wk98 : SixW8.walk table bits 64 76615 bx98 = some 76616 := by decide +kernel

noncomputable def bx99 : SixW8.Box := (SixW8.Box.mk 57344 434176 31744 38400 60416 74240 31744 38400 57344 434176)

noncomputable def bx100 : SixW8.Box := (bx99).setHi (SixW8.axOf bits 76616) (SixW8.Box.mid bx99 (SixW8.axOf bits 76616))

noncomputable def bx101 : SixW8.Box := (bx100).setHi (SixW8.axOf bits 76620) (SixW8.Box.mid bx100 (SixW8.axOf bits 76620))

noncomputable def bx102 : SixW8.Box := (bx101).setHi (SixW8.axOf bits 76624) (SixW8.Box.mid bx101 (SixW8.axOf bits 76624))

noncomputable def bx103 : SixW8.Box := (bx102).setHi (SixW8.axOf bits 76628) (SixW8.Box.mid bx102 (SixW8.axOf bits 76628))

noncomputable def bx104 : SixW8.Box := (bx103).setHi (SixW8.axOf bits 76632) (SixW8.Box.mid bx103 (SixW8.axOf bits 76632))

noncomputable def bx105 : SixW8.Box := (bx104).setHi (SixW8.axOf bits 76636) (SixW8.Box.mid bx104 (SixW8.axOf bits 76636))

noncomputable def bx106 : SixW8.Box := (bx105).setHi (SixW8.axOf bits 76640) (SixW8.Box.mid bx105 (SixW8.axOf bits 76640))

noncomputable def bx107 : SixW8.Box := (bx106).setHi (SixW8.axOf bits 76644) (SixW8.Box.mid bx106 (SixW8.axOf bits 76644))

noncomputable def bx108 : SixW8.Box := (bx107).setHi (SixW8.axOf bits 76648) (SixW8.Box.mid bx107 (SixW8.axOf bits 76648))

theorem wk108 : SixW8.walk table bits 55 76652 bx108 = some 76793 := by decide +kernel

noncomputable def bx109 : SixW8.Box := (bx107).setLo (SixW8.axOf bits 76648) (SixW8.Box.mid bx107 (SixW8.axOf bits 76648))

noncomputable def bx110 : SixW8.Box := (bx109).setHi (SixW8.axOf bits 76793) (SixW8.Box.mid bx109 (SixW8.axOf bits 76793))

noncomputable def bx111 : SixW8.Box := (bx110).setHi (SixW8.axOf bits 76797) (SixW8.Box.mid bx110 (SixW8.axOf bits 76797))

noncomputable def bx112 : SixW8.Box := (bx111).setHi (SixW8.axOf bits 76801) (SixW8.Box.mid bx111 (SixW8.axOf bits 76801))

theorem wk112 : SixW8.walk table bits 52 76805 bx112 = some 76911 := by decide +kernel

noncomputable def bx113 : SixW8.Box := (bx111).setLo (SixW8.axOf bits 76801) (SixW8.Box.mid bx111 (SixW8.axOf bits 76801))

noncomputable def bx114 : SixW8.Box := (bx113).setHi (SixW8.axOf bits 76911) (SixW8.Box.mid bx113 (SixW8.axOf bits 76911))

noncomputable def bx115 : SixW8.Box := (bx114).setHi (SixW8.axOf bits 76915) (SixW8.Box.mid bx114 (SixW8.axOf bits 76915))

theorem wk115 : SixW8.walk table bits 50 76919 bx115 = some 76935 := by decide +kernel

noncomputable def bx116 : SixW8.Box := (bx114).setLo (SixW8.axOf bits 76915) (SixW8.Box.mid bx114 (SixW8.axOf bits 76915))

noncomputable def bx117 : SixW8.Box := (bx116).setHi (SixW8.axOf bits 76935) (SixW8.Box.mid bx116 (SixW8.axOf bits 76935))

theorem wk117 : SixW8.walk table bits 49 76939 bx117 = some 81240 := by decide +kernel

noncomputable def bx118 : SixW8.Box := (bx116).setLo (SixW8.axOf bits 76935) (SixW8.Box.mid bx116 (SixW8.axOf bits 76935))

theorem wk118 : SixW8.walk table bits 49 81240 bx118 = some 82251 := by decide +kernel

theorem wk116 : SixW8.walk table bits 50 76935 bx116 = some 82251 :=
  SixW8.walk_split table bits 49 76935 bx116 81240 82251 (by decide +kernel) wk117 wk118

theorem wk114 : SixW8.walk table bits 51 76915 bx114 = some 82251 :=
  SixW8.walk_split table bits 50 76915 bx114 76935 82251 (by decide +kernel) wk115 wk116

noncomputable def bx119 : SixW8.Box := (bx113).setLo (SixW8.axOf bits 76911) (SixW8.Box.mid bx113 (SixW8.axOf bits 76911))

theorem wk119 : SixW8.walk table bits 51 82251 bx119 = some 82292 := by decide +kernel

theorem wk113 : SixW8.walk table bits 52 76911 bx113 = some 82292 :=
  SixW8.walk_split table bits 51 76911 bx113 82251 82292 (by decide +kernel) wk114 wk119

theorem wk111 : SixW8.walk table bits 53 76801 bx111 = some 82292 :=
  SixW8.walk_split table bits 52 76801 bx111 76911 82292 (by decide +kernel) wk112 wk113

noncomputable def bx120 : SixW8.Box := (bx110).setLo (SixW8.axOf bits 76797) (SixW8.Box.mid bx110 (SixW8.axOf bits 76797))

theorem wk120 : SixW8.walk table bits 53 82292 bx120 = some 82313 := by decide +kernel

theorem wk110 : SixW8.walk table bits 54 76797 bx110 = some 82313 :=
  SixW8.walk_split table bits 53 76797 bx110 82292 82313 (by decide +kernel) wk111 wk120

noncomputable def bx121 : SixW8.Box := (bx109).setLo (SixW8.axOf bits 76793) (SixW8.Box.mid bx109 (SixW8.axOf bits 76793))

theorem wk121 : SixW8.walk table bits 54 82313 bx121 = some 83019 := by decide +kernel

theorem wk109 : SixW8.walk table bits 55 76793 bx109 = some 83019 :=
  SixW8.walk_split table bits 54 76793 bx109 82313 83019 (by decide +kernel) wk110 wk121

theorem wk107 : SixW8.walk table bits 56 76648 bx107 = some 83019 :=
  SixW8.walk_split table bits 55 76648 bx107 76793 83019 (by decide +kernel) wk108 wk109

noncomputable def bx122 : SixW8.Box := (bx106).setLo (SixW8.axOf bits 76644) (SixW8.Box.mid bx106 (SixW8.axOf bits 76644))

theorem wk122 : SixW8.walk table bits 56 83019 bx122 = some 83065 := by decide +kernel

theorem wk106 : SixW8.walk table bits 57 76644 bx106 = some 83065 :=
  SixW8.walk_split table bits 56 76644 bx106 83019 83065 (by decide +kernel) wk107 wk122

noncomputable def bx123 : SixW8.Box := (bx105).setLo (SixW8.axOf bits 76640) (SixW8.Box.mid bx105 (SixW8.axOf bits 76640))

theorem wk123 : SixW8.walk table bits 57 83065 bx123 = some 83211 := by decide +kernel

theorem wk105 : SixW8.walk table bits 58 76640 bx105 = some 83211 :=
  SixW8.walk_split table bits 57 76640 bx105 83065 83211 (by decide +kernel) wk106 wk123

noncomputable def bx124 : SixW8.Box := (bx104).setLo (SixW8.axOf bits 76636) (SixW8.Box.mid bx104 (SixW8.axOf bits 76636))

theorem wk124 : SixW8.walk table bits 58 83211 bx124 = some 83382 := by decide +kernel

theorem wk104 : SixW8.walk table bits 59 76636 bx104 = some 83382 :=
  SixW8.walk_split table bits 58 76636 bx104 83211 83382 (by decide +kernel) wk105 wk124

noncomputable def bx125 : SixW8.Box := (bx103).setLo (SixW8.axOf bits 76632) (SixW8.Box.mid bx103 (SixW8.axOf bits 76632))

theorem wk125 : SixW8.walk table bits 59 83382 bx125 = some 83403 := by decide +kernel

theorem wk103 : SixW8.walk table bits 60 76632 bx103 = some 83403 :=
  SixW8.walk_split table bits 59 76632 bx103 83382 83403 (by decide +kernel) wk104 wk125

noncomputable def bx126 : SixW8.Box := (bx102).setLo (SixW8.axOf bits 76628) (SixW8.Box.mid bx102 (SixW8.axOf bits 76628))

theorem wk126 : SixW8.walk table bits 60 83403 bx126 = some 83429 := by decide +kernel

theorem wk102 : SixW8.walk table bits 61 76628 bx102 = some 83429 :=
  SixW8.walk_split table bits 60 76628 bx102 83403 83429 (by decide +kernel) wk103 wk126

noncomputable def bx127 : SixW8.Box := (bx101).setLo (SixW8.axOf bits 76624) (SixW8.Box.mid bx101 (SixW8.axOf bits 76624))

theorem wk127 : SixW8.walk table bits 61 83429 bx127 = some 83445 := by decide +kernel

theorem wk101 : SixW8.walk table bits 62 76624 bx101 = some 83445 :=
  SixW8.walk_split table bits 61 76624 bx101 83429 83445 (by decide +kernel) wk102 wk127

noncomputable def bx128 : SixW8.Box := (bx100).setLo (SixW8.axOf bits 76620) (SixW8.Box.mid bx100 (SixW8.axOf bits 76620))

theorem wk128 : SixW8.walk table bits 62 83445 bx128 = some 83446 := by decide +kernel

theorem wk100 : SixW8.walk table bits 63 76620 bx100 = some 83446 :=
  SixW8.walk_split table bits 62 76620 bx100 83445 83446 (by decide +kernel) wk101 wk128

noncomputable def bx129 : SixW8.Box := (bx99).setLo (SixW8.axOf bits 76616) (SixW8.Box.mid bx99 (SixW8.axOf bits 76616))

theorem wk129 : SixW8.walk table bits 63 83446 bx129 = some 83447 := by decide +kernel

theorem wk99 : SixW8.walk table bits 64 76616 bx99 = some 83447 :=
  SixW8.walk_split table bits 63 76616 bx99 83446 83447 (by decide +kernel) wk100 wk129

noncomputable def bx130 : SixW8.Box := (SixW8.Box.mk 57344 434176 31744 38400 60416 74240 59904 74752 30720 39936)

theorem wk130 : SixW8.walk table bits 64 83447 bx130 = some 83448 := by decide +kernel

noncomputable def bx131 : SixW8.Box := (SixW8.Box.mk 57344 434176 31744 38400 60416 74240 59904 74752 57344 434176)

theorem wk131 : SixW8.walk table bits 64 83448 bx131 = some 83934 := by decide +kernel

noncomputable def bx132 : SixW8.Box := (SixW8.Box.mk 57344 434176 31744 38400 60416 74240 88576 262144 30720 39936)

theorem wk132 : SixW8.walk table bits 64 83934 bx132 = some 83935 := by decide +kernel

noncomputable def bx133 : SixW8.Box := (SixW8.Box.mk 57344 434176 31744 38400 60416 74240 88576 262144 57344 434176)

theorem wk133 : SixW8.walk table bits 64 83935 bx133 = some 83996 := by decide +kernel

noncomputable def bx134 : SixW8.Box := (SixW8.Box.mk 57344 434176 31744 38400 89088 237568 31744 38400 30720 39936)

theorem wk134 : SixW8.walk table bits 64 83996 bx134 = some 83997 := by decide +kernel

noncomputable def bx135 : SixW8.Box := (SixW8.Box.mk 57344 434176 31744 38400 89088 237568 31744 38400 57344 434176)

theorem wk135 : SixW8.walk table bits 64 83997 bx135 = some 84273 := by decide +kernel

noncomputable def bx136 : SixW8.Box := (SixW8.Box.mk 57344 434176 31744 38400 89088 237568 59904 74752 30720 39936)

theorem wk136 : SixW8.walk table bits 64 84273 bx136 = some 84274 := by decide +kernel

noncomputable def bx137 : SixW8.Box := (SixW8.Box.mk 57344 434176 31744 38400 89088 237568 59904 74752 57344 434176)

theorem wk137 : SixW8.walk table bits 64 84274 bx137 = some 84275 := by decide +kernel

noncomputable def bx138 : SixW8.Box := (SixW8.Box.mk 57344 434176 31744 38400 89088 237568 88576 262144 30720 39936)

theorem wk138 : SixW8.walk table bits 64 84275 bx138 = some 84276 := by decide +kernel

noncomputable def bx139 : SixW8.Box := (SixW8.Box.mk 57344 434176 31744 38400 89088 237568 88576 262144 57344 434176)

theorem wk139 : SixW8.walk table bits 64 84276 bx139 = some 84277 := by decide +kernel

noncomputable def bx140 : SixW8.Box := (SixW8.Box.mk 57344 434176 59904 74752 31744 38400 31744 38400 30720 39936)

theorem wk140 : SixW8.walk table bits 64 84277 bx140 = some 84278 := by decide +kernel

noncomputable def bx141 : SixW8.Box := (SixW8.Box.mk 57344 434176 59904 74752 31744 38400 31744 38400 57344 434176)

theorem wk141 : SixW8.walk table bits 64 84278 bx141 = some 87894 := by decide +kernel

noncomputable def bx142 : SixW8.Box := (SixW8.Box.mk 57344 434176 59904 74752 31744 38400 59904 74752 30720 39936)

theorem wk142 : SixW8.walk table bits 64 87894 bx142 = some 87895 := by decide +kernel

noncomputable def bx143 : SixW8.Box := (SixW8.Box.mk 57344 434176 59904 74752 31744 38400 59904 74752 57344 434176)

theorem wk143 : SixW8.walk table bits 64 87895 bx143 = some 88736 := by decide +kernel

noncomputable def bx144 : SixW8.Box := (SixW8.Box.mk 57344 434176 59904 74752 31744 38400 88576 262144 30720 39936)

theorem wk144 : SixW8.walk table bits 64 88736 bx144 = some 88737 := by decide +kernel

noncomputable def bx145 : SixW8.Box := (SixW8.Box.mk 57344 434176 59904 74752 31744 38400 88576 262144 57344 434176)

theorem wk145 : SixW8.walk table bits 64 88737 bx145 = some 88813 := by decide +kernel

noncomputable def bx146 : SixW8.Box := (SixW8.Box.mk 57344 434176 59904 74752 60416 74240 31744 38400 30720 39936)

theorem wk146 : SixW8.walk table bits 64 88813 bx146 = some 88814 := by decide +kernel

noncomputable def bx147 : SixW8.Box := (SixW8.Box.mk 57344 434176 59904 74752 60416 74240 31744 38400 57344 434176)

theorem wk147 : SixW8.walk table bits 64 88814 bx147 = some 89310 := by decide +kernel

noncomputable def bx148 : SixW8.Box := (SixW8.Box.mk 57344 434176 59904 74752 60416 74240 59904 74752 30720 39936)

theorem wk148 : SixW8.walk table bits 64 89310 bx148 = some 89311 := by decide +kernel

noncomputable def bx149 : SixW8.Box := (SixW8.Box.mk 57344 434176 59904 74752 60416 74240 59904 74752 57344 434176)

theorem wk149 : SixW8.walk table bits 64 89311 bx149 = some 89357 := by decide +kernel

noncomputable def bx150 : SixW8.Box := (SixW8.Box.mk 57344 434176 59904 74752 60416 74240 88576 262144 30720 39936)

theorem wk150 : SixW8.walk table bits 64 89357 bx150 = some 89358 := by decide +kernel

noncomputable def bx151 : SixW8.Box := (SixW8.Box.mk 57344 434176 59904 74752 60416 74240 88576 262144 57344 434176)

theorem wk151 : SixW8.walk table bits 64 89358 bx151 = some 89359 := by decide +kernel

noncomputable def bx152 : SixW8.Box := (SixW8.Box.mk 57344 434176 59904 74752 89088 237568 31744 38400 30720 39936)

theorem wk152 : SixW8.walk table bits 64 89359 bx152 = some 89360 := by decide +kernel

noncomputable def bx153 : SixW8.Box := (SixW8.Box.mk 57344 434176 59904 74752 89088 237568 31744 38400 57344 434176)

theorem wk153 : SixW8.walk table bits 64 89360 bx153 = some 89361 := by decide +kernel

noncomputable def bx154 : SixW8.Box := (SixW8.Box.mk 57344 434176 59904 74752 89088 237568 59904 74752 30720 39936)

theorem wk154 : SixW8.walk table bits 64 89361 bx154 = some 89362 := by decide +kernel

noncomputable def bx155 : SixW8.Box := (SixW8.Box.mk 57344 434176 59904 74752 89088 237568 59904 74752 57344 434176)

theorem wk155 : SixW8.walk table bits 64 89362 bx155 = some 89363 := by decide +kernel

noncomputable def bx156 : SixW8.Box := (SixW8.Box.mk 57344 434176 59904 74752 89088 237568 88576 262144 30720 39936)

theorem wk156 : SixW8.walk table bits 64 89363 bx156 = some 89364 := by decide +kernel

noncomputable def bx157 : SixW8.Box := (SixW8.Box.mk 57344 434176 59904 74752 89088 237568 88576 262144 57344 434176)

theorem wk157 : SixW8.walk table bits 64 89364 bx157 = some 89365 := by decide +kernel

noncomputable def bx158 : SixW8.Box := (SixW8.Box.mk 57344 434176 88576 262144 31744 38400 31744 38400 30720 39936)

theorem wk158 : SixW8.walk table bits 64 89365 bx158 = some 89366 := by decide +kernel

noncomputable def bx159 : SixW8.Box := (SixW8.Box.mk 57344 434176 88576 262144 31744 38400 31744 38400 57344 434176)

theorem wk159 : SixW8.walk table bits 64 89366 bx159 = some 89707 := by decide +kernel

noncomputable def bx160 : SixW8.Box := (SixW8.Box.mk 57344 434176 88576 262144 31744 38400 59904 74752 30720 39936)

theorem wk160 : SixW8.walk table bits 64 89707 bx160 = some 89708 := by decide +kernel

noncomputable def bx161 : SixW8.Box := (SixW8.Box.mk 57344 434176 88576 262144 31744 38400 59904 74752 57344 434176)

theorem wk161 : SixW8.walk table bits 64 89708 bx161 = some 89784 := by decide +kernel

noncomputable def bx162 : SixW8.Box := (SixW8.Box.mk 57344 434176 88576 262144 31744 38400 88576 262144 30720 39936)

theorem wk162 : SixW8.walk table bits 64 89784 bx162 = some 89785 := by decide +kernel

noncomputable def bx163 : SixW8.Box := (SixW8.Box.mk 57344 434176 88576 262144 31744 38400 88576 262144 57344 434176)

theorem wk163 : SixW8.walk table bits 64 89785 bx163 = some 89786 := by decide +kernel

noncomputable def bx164 : SixW8.Box := (SixW8.Box.mk 57344 434176 88576 262144 60416 74240 31744 38400 30720 39936)

theorem wk164 : SixW8.walk table bits 64 89786 bx164 = some 89787 := by decide +kernel

noncomputable def bx165 : SixW8.Box := (SixW8.Box.mk 57344 434176 88576 262144 60416 74240 31744 38400 57344 434176)

theorem wk165 : SixW8.walk table bits 64 89787 bx165 = some 89848 := by decide +kernel

noncomputable def bx166 : SixW8.Box := (SixW8.Box.mk 57344 434176 88576 262144 60416 74240 59904 74752 30720 39936)

theorem wk166 : SixW8.walk table bits 64 89848 bx166 = some 89849 := by decide +kernel

noncomputable def bx167 : SixW8.Box := (SixW8.Box.mk 57344 434176 88576 262144 60416 74240 59904 74752 57344 434176)

theorem wk167 : SixW8.walk table bits 64 89849 bx167 = some 89850 := by decide +kernel

noncomputable def bx168 : SixW8.Box := (SixW8.Box.mk 57344 434176 88576 262144 60416 74240 88576 262144 30720 39936)

theorem wk168 : SixW8.walk table bits 64 89850 bx168 = some 89851 := by decide +kernel

noncomputable def bx169 : SixW8.Box := (SixW8.Box.mk 57344 434176 88576 262144 60416 74240 88576 262144 57344 434176)

theorem wk169 : SixW8.walk table bits 64 89851 bx169 = some 89852 := by decide +kernel

noncomputable def bx170 : SixW8.Box := (SixW8.Box.mk 57344 434176 88576 262144 89088 237568 31744 38400 30720 39936)

theorem wk170 : SixW8.walk table bits 64 89852 bx170 = some 89853 := by decide +kernel

noncomputable def bx171 : SixW8.Box := (SixW8.Box.mk 57344 434176 88576 262144 89088 237568 31744 38400 57344 434176)

theorem wk171 : SixW8.walk table bits 64 89853 bx171 = some 89854 := by decide +kernel

noncomputable def bx172 : SixW8.Box := (SixW8.Box.mk 57344 434176 88576 262144 89088 237568 59904 74752 30720 39936)

theorem wk172 : SixW8.walk table bits 64 89854 bx172 = some 89855 := by decide +kernel

noncomputable def bx173 : SixW8.Box := (SixW8.Box.mk 57344 434176 88576 262144 89088 237568 59904 74752 57344 434176)

theorem wk173 : SixW8.walk table bits 64 89855 bx173 = some 89856 := by decide +kernel

noncomputable def bx174 : SixW8.Box := (SixW8.Box.mk 57344 434176 88576 262144 89088 237568 88576 262144 30720 39936)

theorem wk174 : SixW8.walk table bits 64 89856 bx174 = some 89857 := by decide +kernel

noncomputable def bx175 : SixW8.Box := (SixW8.Box.mk 57344 434176 88576 262144 89088 237568 88576 262144 57344 434176)

theorem wk175 : SixW8.walk table bits 64 89857 bx175 = some 89858 := by decide +kernel

theorem nb0_eq : (SixW8.badOf cover0).length = 2 := by decide +kernel

theorem nb1_eq : (SixW8.badOf cover1).length = 3 := by decide +kernel

theorem nb2_eq : (SixW8.badOf cover2).length = 3 := by decide +kernel

theorem nb3_eq : (SixW8.badOf cover3).length = 3 := by decide +kernel

theorem nb4_eq : (SixW8.badOf cover4).length = 2 := by decide +kernel

theorem root_00000 : SixW8.walk table bits 64 0 (SixW8.boxOf (SixW8.badOf cover0) (SixW8.badOf cover1) (SixW8.badOf cover2) (SixW8.badOf cover3) (SixW8.badOf cover4) 0 0 0 0 0) = some 1351 := by
  rw [show SixW8.boxOf (SixW8.badOf cover0) (SixW8.badOf cover1) (SixW8.badOf cover2) (SixW8.badOf cover3) (SixW8.badOf cover4) 0 0 0 0 0 = bx0 from by decide +kernel]; exact wk0

theorem root_00001 : SixW8.walk table bits 64 1351 (SixW8.boxOf (SixW8.badOf cover0) (SixW8.badOf cover1) (SixW8.badOf cover2) (SixW8.badOf cover3) (SixW8.badOf cover4) 0 0 0 0 1) = some 4927 := by
  rw [show SixW8.boxOf (SixW8.badOf cover0) (SixW8.badOf cover1) (SixW8.badOf cover2) (SixW8.badOf cover3) (SixW8.badOf cover4) 0 0 0 0 1 = bx1 from by decide +kernel]; exact wk1

theorem root_00010 : SixW8.walk table bits 64 4927 (SixW8.boxOf (SixW8.badOf cover0) (SixW8.badOf cover1) (SixW8.badOf cover2) (SixW8.badOf cover3) (SixW8.badOf cover4) 0 0 0 1 0) = some 8288 := by
  rw [show SixW8.boxOf (SixW8.badOf cover0) (SixW8.badOf cover1) (SixW8.badOf cover2) (SixW8.badOf cover3) (SixW8.badOf cover4) 0 0 0 1 0 = bx2 from by decide +kernel]; exact wk2

theorem root_00011 : SixW8.walk table bits 64 8288 (SixW8.boxOf (SixW8.badOf cover0) (SixW8.badOf cover1) (SixW8.badOf cover2) (SixW8.badOf cover3) (SixW8.badOf cover4) 0 0 0 1 1) = some 12009 := by
  rw [show SixW8.boxOf (SixW8.badOf cover0) (SixW8.badOf cover1) (SixW8.badOf cover2) (SixW8.badOf cover3) (SixW8.badOf cover4) 0 0 0 1 1 = bx3 from by decide +kernel]; exact wk3

theorem root_00020 : SixW8.walk table bits 64 12009 (SixW8.boxOf (SixW8.badOf cover0) (SixW8.badOf cover1) (SixW8.badOf cover2) (SixW8.badOf cover3) (SixW8.badOf cover4) 0 0 0 2 0) = some 13460 := by
  rw [show SixW8.boxOf (SixW8.badOf cover0) (SixW8.badOf cover1) (SixW8.badOf cover2) (SixW8.badOf cover3) (SixW8.badOf cover4) 0 0 0 2 0 = bx4 from by decide +kernel]; exact wk4

theorem root_00021 : SixW8.walk table bits 64 13460 (SixW8.boxOf (SixW8.badOf cover0) (SixW8.badOf cover1) (SixW8.badOf cover2) (SixW8.badOf cover3) (SixW8.badOf cover4) 0 0 0 2 1) = some 14371 := by
  rw [show SixW8.boxOf (SixW8.badOf cover0) (SixW8.badOf cover1) (SixW8.badOf cover2) (SixW8.badOf cover3) (SixW8.badOf cover4) 0 0 0 2 1 = bx5 from by decide +kernel]; exact wk5

theorem root_00100 : SixW8.walk table bits 64 14371 (SixW8.boxOf (SixW8.badOf cover0) (SixW8.badOf cover1) (SixW8.badOf cover2) (SixW8.badOf cover3) (SixW8.badOf cover4) 0 0 1 0 0) = some 17857 := by
  rw [show SixW8.boxOf (SixW8.badOf cover0) (SixW8.badOf cover1) (SixW8.badOf cover2) (SixW8.badOf cover3) (SixW8.badOf cover4) 0 0 1 0 0 = bx6 from by decide +kernel]; exact wk6

theorem root_00101 : SixW8.walk table bits 64 17857 (SixW8.boxOf (SixW8.badOf cover0) (SixW8.badOf cover1) (SixW8.badOf cover2) (SixW8.badOf cover3) (SixW8.badOf cover4) 0 0 1 0 1) = some 23603 := by
  rw [show SixW8.boxOf (SixW8.badOf cover0) (SixW8.badOf cover1) (SixW8.badOf cover2) (SixW8.badOf cover3) (SixW8.badOf cover4) 0 0 1 0 1 = bx7 from by decide +kernel]; exact wk7

theorem root_00110 : SixW8.walk table bits 64 23603 (SixW8.boxOf (SixW8.badOf cover0) (SixW8.badOf cover1) (SixW8.badOf cover2) (SixW8.badOf cover3) (SixW8.badOf cover4) 0 0 1 1 0) = some 26339 := by
  rw [show SixW8.boxOf (SixW8.badOf cover0) (SixW8.badOf cover1) (SixW8.badOf cover2) (SixW8.badOf cover3) (SixW8.badOf cover4) 0 0 1 1 0 = bx16 from by decide +kernel]; exact wk16

theorem root_00111 : SixW8.walk table bits 64 26339 (SixW8.boxOf (SixW8.badOf cover0) (SixW8.badOf cover1) (SixW8.badOf cover2) (SixW8.badOf cover3) (SixW8.badOf cover4) 0 0 1 1 1) = some 27580 := by
  rw [show SixW8.boxOf (SixW8.badOf cover0) (SixW8.badOf cover1) (SixW8.badOf cover2) (SixW8.badOf cover3) (SixW8.badOf cover4) 0 0 1 1 1 = bx17 from by decide +kernel]; exact wk17

theorem root_00120 : SixW8.walk table bits 64 27580 (SixW8.boxOf (SixW8.badOf cover0) (SixW8.badOf cover1) (SixW8.badOf cover2) (SixW8.badOf cover3) (SixW8.badOf cover4) 0 0 1 2 0) = some 27991 := by
  rw [show SixW8.boxOf (SixW8.badOf cover0) (SixW8.badOf cover1) (SixW8.badOf cover2) (SixW8.badOf cover3) (SixW8.badOf cover4) 0 0 1 2 0 = bx18 from by decide +kernel]; exact wk18

theorem root_00121 : SixW8.walk table bits 64 27991 (SixW8.boxOf (SixW8.badOf cover0) (SixW8.badOf cover1) (SixW8.badOf cover2) (SixW8.badOf cover3) (SixW8.badOf cover4) 0 0 1 2 1) = some 28102 := by
  rw [show SixW8.boxOf (SixW8.badOf cover0) (SixW8.badOf cover1) (SixW8.badOf cover2) (SixW8.badOf cover3) (SixW8.badOf cover4) 0 0 1 2 1 = bx19 from by decide +kernel]; exact wk19

theorem root_00200 : SixW8.walk table bits 64 28102 (SixW8.boxOf (SixW8.badOf cover0) (SixW8.badOf cover1) (SixW8.badOf cover2) (SixW8.badOf cover3) (SixW8.badOf cover4) 0 0 2 0 0) = some 29438 := by
  rw [show SixW8.boxOf (SixW8.badOf cover0) (SixW8.badOf cover1) (SixW8.badOf cover2) (SixW8.badOf cover3) (SixW8.badOf cover4) 0 0 2 0 0 = bx20 from by decide +kernel]; exact wk20

theorem root_00201 : SixW8.walk table bits 64 29438 (SixW8.boxOf (SixW8.badOf cover0) (SixW8.badOf cover1) (SixW8.badOf cover2) (SixW8.badOf cover3) (SixW8.badOf cover4) 0 0 2 0 1) = some 30309 := by
  rw [show SixW8.boxOf (SixW8.badOf cover0) (SixW8.badOf cover1) (SixW8.badOf cover2) (SixW8.badOf cover3) (SixW8.badOf cover4) 0 0 2 0 1 = bx21 from by decide +kernel]; exact wk21

theorem root_00210 : SixW8.walk table bits 64 30309 (SixW8.boxOf (SixW8.badOf cover0) (SixW8.badOf cover1) (SixW8.badOf cover2) (SixW8.badOf cover3) (SixW8.badOf cover4) 0 0 2 1 0) = some 30685 := by
  rw [show SixW8.boxOf (SixW8.badOf cover0) (SixW8.badOf cover1) (SixW8.badOf cover2) (SixW8.badOf cover3) (SixW8.badOf cover4) 0 0 2 1 0 = bx22 from by decide +kernel]; exact wk22

theorem root_00211 : SixW8.walk table bits 64 30685 (SixW8.boxOf (SixW8.badOf cover0) (SixW8.badOf cover1) (SixW8.badOf cover2) (SixW8.badOf cover3) (SixW8.badOf cover4) 0 0 2 1 1) = some 30776 := by
  rw [show SixW8.boxOf (SixW8.badOf cover0) (SixW8.badOf cover1) (SixW8.badOf cover2) (SixW8.badOf cover3) (SixW8.badOf cover4) 0 0 2 1 1 = bx23 from by decide +kernel]; exact wk23

theorem root_00220 : SixW8.walk table bits 64 30776 (SixW8.boxOf (SixW8.badOf cover0) (SixW8.badOf cover1) (SixW8.badOf cover2) (SixW8.badOf cover3) (SixW8.badOf cover4) 0 0 2 2 0) = some 30817 := by
  rw [show SixW8.boxOf (SixW8.badOf cover0) (SixW8.badOf cover1) (SixW8.badOf cover2) (SixW8.badOf cover3) (SixW8.badOf cover4) 0 0 2 2 0 = bx24 from by decide +kernel]; exact wk24

theorem root_00221 : SixW8.walk table bits 64 30817 (SixW8.boxOf (SixW8.badOf cover0) (SixW8.badOf cover1) (SixW8.badOf cover2) (SixW8.badOf cover3) (SixW8.badOf cover4) 0 0 2 2 1) = some 30818 := by
  rw [show SixW8.boxOf (SixW8.badOf cover0) (SixW8.badOf cover1) (SixW8.badOf cover2) (SixW8.badOf cover3) (SixW8.badOf cover4) 0 0 2 2 1 = bx25 from by decide +kernel]; exact wk25

theorem root_01000 : SixW8.walk table bits 64 30818 (SixW8.boxOf (SixW8.badOf cover0) (SixW8.badOf cover1) (SixW8.badOf cover2) (SixW8.badOf cover3) (SixW8.badOf cover4) 0 1 0 0 0) = some 33979 := by
  rw [show SixW8.boxOf (SixW8.badOf cover0) (SixW8.badOf cover1) (SixW8.badOf cover2) (SixW8.badOf cover3) (SixW8.badOf cover4) 0 1 0 0 0 = bx26 from by decide +kernel]; exact wk26

theorem root_01001 : SixW8.walk table bits 64 33979 (SixW8.boxOf (SixW8.badOf cover0) (SixW8.badOf cover1) (SixW8.badOf cover2) (SixW8.badOf cover3) (SixW8.badOf cover4) 0 1 0 0 1) = some 41700 := by
  rw [show SixW8.boxOf (SixW8.badOf cover0) (SixW8.badOf cover1) (SixW8.badOf cover2) (SixW8.badOf cover3) (SixW8.badOf cover4) 0 1 0 0 1 = bx27 from by decide +kernel]; exact wk27

theorem root_01010 : SixW8.walk table bits 64 41700 (SixW8.boxOf (SixW8.badOf cover0) (SixW8.badOf cover1) (SixW8.badOf cover2) (SixW8.badOf cover3) (SixW8.badOf cover4) 0 1 0 1 0) = some 51436 := by
  rw [show SixW8.boxOf (SixW8.badOf cover0) (SixW8.badOf cover1) (SixW8.badOf cover2) (SixW8.badOf cover3) (SixW8.badOf cover4) 0 1 0 1 0 = bx46 from by decide +kernel]; exact wk46

theorem root_01011 : SixW8.walk table bits 64 51436 (SixW8.boxOf (SixW8.badOf cover0) (SixW8.badOf cover1) (SixW8.badOf cover2) (SixW8.badOf cover3) (SixW8.badOf cover4) 0 1 0 1 1) = some 55637 := by
  rw [show SixW8.boxOf (SixW8.badOf cover0) (SixW8.badOf cover1) (SixW8.badOf cover2) (SixW8.badOf cover3) (SixW8.badOf cover4) 0 1 0 1 1 = bx59 from by decide +kernel]; exact wk59

theorem root_01020 : SixW8.walk table bits 64 55637 (SixW8.boxOf (SixW8.badOf cover0) (SixW8.badOf cover1) (SixW8.badOf cover2) (SixW8.badOf cover3) (SixW8.badOf cover4) 0 1 0 2 0) = some 56418 := by
  rw [show SixW8.boxOf (SixW8.badOf cover0) (SixW8.badOf cover1) (SixW8.badOf cover2) (SixW8.badOf cover3) (SixW8.badOf cover4) 0 1 0 2 0 = bx60 from by decide +kernel]; exact wk60

theorem root_01021 : SixW8.walk table bits 64 56418 (SixW8.boxOf (SixW8.badOf cover0) (SixW8.badOf cover1) (SixW8.badOf cover2) (SixW8.badOf cover3) (SixW8.badOf cover4) 0 1 0 2 1) = some 56564 := by
  rw [show SixW8.boxOf (SixW8.badOf cover0) (SixW8.badOf cover1) (SixW8.badOf cover2) (SixW8.badOf cover3) (SixW8.badOf cover4) 0 1 0 2 1 = bx61 from by decide +kernel]; exact wk61

theorem root_01100 : SixW8.walk table bits 64 56564 (SixW8.boxOf (SixW8.badOf cover0) (SixW8.badOf cover1) (SixW8.badOf cover2) (SixW8.badOf cover3) (SixW8.badOf cover4) 0 1 1 0 0) = some 59095 := by
  rw [show SixW8.boxOf (SixW8.badOf cover0) (SixW8.badOf cover1) (SixW8.badOf cover2) (SixW8.badOf cover3) (SixW8.badOf cover4) 0 1 1 0 0 = bx62 from by decide +kernel]; exact wk62

theorem root_01101 : SixW8.walk table bits 64 59095 (SixW8.boxOf (SixW8.badOf cover0) (SixW8.badOf cover1) (SixW8.badOf cover2) (SixW8.badOf cover3) (SixW8.badOf cover4) 0 1 1 0 1) = some 62606 := by
  rw [show SixW8.boxOf (SixW8.badOf cover0) (SixW8.badOf cover1) (SixW8.badOf cover2) (SixW8.badOf cover3) (SixW8.badOf cover4) 0 1 1 0 1 = bx63 from by decide +kernel]; exact wk63

theorem root_01110 : SixW8.walk table bits 64 62606 (SixW8.boxOf (SixW8.badOf cover0) (SixW8.badOf cover1) (SixW8.badOf cover2) (SixW8.badOf cover3) (SixW8.badOf cover4) 0 1 1 1 0) = some 63372 := by
  rw [show SixW8.boxOf (SixW8.badOf cover0) (SixW8.badOf cover1) (SixW8.badOf cover2) (SixW8.badOf cover3) (SixW8.badOf cover4) 0 1 1 1 0 = bx64 from by decide +kernel]; exact wk64

theorem root_01111 : SixW8.walk table bits 64 63372 (SixW8.boxOf (SixW8.badOf cover0) (SixW8.badOf cover1) (SixW8.badOf cover2) (SixW8.badOf cover3) (SixW8.badOf cover4) 0 1 1 1 1) = some 63483 := by
  rw [show SixW8.boxOf (SixW8.badOf cover0) (SixW8.badOf cover1) (SixW8.badOf cover2) (SixW8.badOf cover3) (SixW8.badOf cover4) 0 1 1 1 1 = bx65 from by decide +kernel]; exact wk65

theorem root_01120 : SixW8.walk table bits 64 63483 (SixW8.boxOf (SixW8.badOf cover0) (SixW8.badOf cover1) (SixW8.badOf cover2) (SixW8.badOf cover3) (SixW8.badOf cover4) 0 1 1 2 0) = some 63514 := by
  rw [show SixW8.boxOf (SixW8.badOf cover0) (SixW8.badOf cover1) (SixW8.badOf cover2) (SixW8.badOf cover3) (SixW8.badOf cover4) 0 1 1 2 0 = bx66 from by decide +kernel]; exact wk66

theorem root_01121 : SixW8.walk table bits 64 63514 (SixW8.boxOf (SixW8.badOf cover0) (SixW8.badOf cover1) (SixW8.badOf cover2) (SixW8.badOf cover3) (SixW8.badOf cover4) 0 1 1 2 1) = some 63515 := by
  rw [show SixW8.boxOf (SixW8.badOf cover0) (SixW8.badOf cover1) (SixW8.badOf cover2) (SixW8.badOf cover3) (SixW8.badOf cover4) 0 1 1 2 1 = bx67 from by decide +kernel]; exact wk67

theorem root_01200 : SixW8.walk table bits 64 63515 (SixW8.boxOf (SixW8.badOf cover0) (SixW8.badOf cover1) (SixW8.badOf cover2) (SixW8.badOf cover3) (SixW8.badOf cover4) 0 1 2 0 0) = some 63886 := by
  rw [show SixW8.boxOf (SixW8.badOf cover0) (SixW8.badOf cover1) (SixW8.badOf cover2) (SixW8.badOf cover3) (SixW8.badOf cover4) 0 1 2 0 0 = bx68 from by decide +kernel]; exact wk68

theorem root_01201 : SixW8.walk table bits 64 63886 (SixW8.boxOf (SixW8.badOf cover0) (SixW8.badOf cover1) (SixW8.badOf cover2) (SixW8.badOf cover3) (SixW8.badOf cover4) 0 1 2 0 1) = some 63977 := by
  rw [show SixW8.boxOf (SixW8.badOf cover0) (SixW8.badOf cover1) (SixW8.badOf cover2) (SixW8.badOf cover3) (SixW8.badOf cover4) 0 1 2 0 1 = bx69 from by decide +kernel]; exact wk69

theorem root_01210 : SixW8.walk table bits 64 63977 (SixW8.boxOf (SixW8.badOf cover0) (SixW8.badOf cover1) (SixW8.badOf cover2) (SixW8.badOf cover3) (SixW8.badOf cover4) 0 1 2 1 0) = some 64003 := by
  rw [show SixW8.boxOf (SixW8.badOf cover0) (SixW8.badOf cover1) (SixW8.badOf cover2) (SixW8.badOf cover3) (SixW8.badOf cover4) 0 1 2 1 0 = bx70 from by decide +kernel]; exact wk70

theorem root_01211 : SixW8.walk table bits 64 64003 (SixW8.boxOf (SixW8.badOf cover0) (SixW8.badOf cover1) (SixW8.badOf cover2) (SixW8.badOf cover3) (SixW8.badOf cover4) 0 1 2 1 1) = some 64004 := by
  rw [show SixW8.boxOf (SixW8.badOf cover0) (SixW8.badOf cover1) (SixW8.badOf cover2) (SixW8.badOf cover3) (SixW8.badOf cover4) 0 1 2 1 1 = bx71 from by decide +kernel]; exact wk71

theorem root_01220 : SixW8.walk table bits 64 64004 (SixW8.boxOf (SixW8.badOf cover0) (SixW8.badOf cover1) (SixW8.badOf cover2) (SixW8.badOf cover3) (SixW8.badOf cover4) 0 1 2 2 0) = some 64005 := by
  rw [show SixW8.boxOf (SixW8.badOf cover0) (SixW8.badOf cover1) (SixW8.badOf cover2) (SixW8.badOf cover3) (SixW8.badOf cover4) 0 1 2 2 0 = bx72 from by decide +kernel]; exact wk72

theorem root_01221 : SixW8.walk table bits 64 64005 (SixW8.boxOf (SixW8.badOf cover0) (SixW8.badOf cover1) (SixW8.badOf cover2) (SixW8.badOf cover3) (SixW8.badOf cover4) 0 1 2 2 1) = some 64006 := by
  rw [show SixW8.boxOf (SixW8.badOf cover0) (SixW8.badOf cover1) (SixW8.badOf cover2) (SixW8.badOf cover3) (SixW8.badOf cover4) 0 1 2 2 1 = bx73 from by decide +kernel]; exact wk73

theorem root_02000 : SixW8.walk table bits 64 64006 (SixW8.boxOf (SixW8.badOf cover0) (SixW8.badOf cover1) (SixW8.badOf cover2) (SixW8.badOf cover3) (SixW8.badOf cover4) 0 2 0 0 0) = some 65387 := by
  rw [show SixW8.boxOf (SixW8.badOf cover0) (SixW8.badOf cover1) (SixW8.badOf cover2) (SixW8.badOf cover3) (SixW8.badOf cover4) 0 2 0 0 0 = bx74 from by decide +kernel]; exact wk74

theorem root_02001 : SixW8.walk table bits 64 65387 (SixW8.boxOf (SixW8.badOf cover0) (SixW8.badOf cover1) (SixW8.badOf cover2) (SixW8.badOf cover3) (SixW8.badOf cover4) 0 2 0 0 1) = some 66783 := by
  rw [show SixW8.boxOf (SixW8.badOf cover0) (SixW8.badOf cover1) (SixW8.badOf cover2) (SixW8.badOf cover3) (SixW8.badOf cover4) 0 2 0 0 1 = bx75 from by decide +kernel]; exact wk75

theorem root_02010 : SixW8.walk table bits 64 66783 (SixW8.boxOf (SixW8.badOf cover0) (SixW8.badOf cover1) (SixW8.badOf cover2) (SixW8.badOf cover3) (SixW8.badOf cover4) 0 2 0 1 0) = some 67564 := by
  rw [show SixW8.boxOf (SixW8.badOf cover0) (SixW8.badOf cover1) (SixW8.badOf cover2) (SixW8.badOf cover3) (SixW8.badOf cover4) 0 2 0 1 0 = bx76 from by decide +kernel]; exact wk76

theorem root_02011 : SixW8.walk table bits 64 67564 (SixW8.boxOf (SixW8.badOf cover0) (SixW8.badOf cover1) (SixW8.badOf cover2) (SixW8.badOf cover3) (SixW8.badOf cover4) 0 2 0 1 1) = some 67710 := by
  rw [show SixW8.boxOf (SixW8.badOf cover0) (SixW8.badOf cover1) (SixW8.badOf cover2) (SixW8.badOf cover3) (SixW8.badOf cover4) 0 2 0 1 1 = bx77 from by decide +kernel]; exact wk77

theorem root_02020 : SixW8.walk table bits 64 67710 (SixW8.boxOf (SixW8.badOf cover0) (SixW8.badOf cover1) (SixW8.badOf cover2) (SixW8.badOf cover3) (SixW8.badOf cover4) 0 2 0 2 0) = some 67761 := by
  rw [show SixW8.boxOf (SixW8.badOf cover0) (SixW8.badOf cover1) (SixW8.badOf cover2) (SixW8.badOf cover3) (SixW8.badOf cover4) 0 2 0 2 0 = bx78 from by decide +kernel]; exact wk78

theorem root_02021 : SixW8.walk table bits 64 67761 (SixW8.boxOf (SixW8.badOf cover0) (SixW8.badOf cover1) (SixW8.badOf cover2) (SixW8.badOf cover3) (SixW8.badOf cover4) 0 2 0 2 1) = some 67762 := by
  rw [show SixW8.boxOf (SixW8.badOf cover0) (SixW8.badOf cover1) (SixW8.badOf cover2) (SixW8.badOf cover3) (SixW8.badOf cover4) 0 2 0 2 1 = bx79 from by decide +kernel]; exact wk79

theorem root_02100 : SixW8.walk table bits 64 67762 (SixW8.boxOf (SixW8.badOf cover0) (SixW8.badOf cover1) (SixW8.badOf cover2) (SixW8.badOf cover3) (SixW8.badOf cover4) 0 2 1 0 0) = some 68163 := by
  rw [show SixW8.boxOf (SixW8.badOf cover0) (SixW8.badOf cover1) (SixW8.badOf cover2) (SixW8.badOf cover3) (SixW8.badOf cover4) 0 2 1 0 0 = bx80 from by decide +kernel]; exact wk80

theorem root_02101 : SixW8.walk table bits 64 68163 (SixW8.boxOf (SixW8.badOf cover0) (SixW8.badOf cover1) (SixW8.badOf cover2) (SixW8.badOf cover3) (SixW8.badOf cover4) 0 2 1 0 1) = some 68274 := by
  rw [show SixW8.boxOf (SixW8.badOf cover0) (SixW8.badOf cover1) (SixW8.badOf cover2) (SixW8.badOf cover3) (SixW8.badOf cover4) 0 2 1 0 1 = bx81 from by decide +kernel]; exact wk81

theorem root_02110 : SixW8.walk table bits 64 68274 (SixW8.boxOf (SixW8.badOf cover0) (SixW8.badOf cover1) (SixW8.badOf cover2) (SixW8.badOf cover3) (SixW8.badOf cover4) 0 2 1 1 0) = some 68305 := by
  rw [show SixW8.boxOf (SixW8.badOf cover0) (SixW8.badOf cover1) (SixW8.badOf cover2) (SixW8.badOf cover3) (SixW8.badOf cover4) 0 2 1 1 0 = bx82 from by decide +kernel]; exact wk82

theorem root_02111 : SixW8.walk table bits 64 68305 (SixW8.boxOf (SixW8.badOf cover0) (SixW8.badOf cover1) (SixW8.badOf cover2) (SixW8.badOf cover3) (SixW8.badOf cover4) 0 2 1 1 1) = some 68306 := by
  rw [show SixW8.boxOf (SixW8.badOf cover0) (SixW8.badOf cover1) (SixW8.badOf cover2) (SixW8.badOf cover3) (SixW8.badOf cover4) 0 2 1 1 1 = bx83 from by decide +kernel]; exact wk83

theorem root_02120 : SixW8.walk table bits 64 68306 (SixW8.boxOf (SixW8.badOf cover0) (SixW8.badOf cover1) (SixW8.badOf cover2) (SixW8.badOf cover3) (SixW8.badOf cover4) 0 2 1 2 0) = some 68307 := by
  rw [show SixW8.boxOf (SixW8.badOf cover0) (SixW8.badOf cover1) (SixW8.badOf cover2) (SixW8.badOf cover3) (SixW8.badOf cover4) 0 2 1 2 0 = bx84 from by decide +kernel]; exact wk84

theorem root_02121 : SixW8.walk table bits 64 68307 (SixW8.boxOf (SixW8.badOf cover0) (SixW8.badOf cover1) (SixW8.badOf cover2) (SixW8.badOf cover3) (SixW8.badOf cover4) 0 2 1 2 1) = some 68308 := by
  rw [show SixW8.boxOf (SixW8.badOf cover0) (SixW8.badOf cover1) (SixW8.badOf cover2) (SixW8.badOf cover3) (SixW8.badOf cover4) 0 2 1 2 1 = bx85 from by decide +kernel]; exact wk85

theorem root_02200 : SixW8.walk table bits 64 68308 (SixW8.boxOf (SixW8.badOf cover0) (SixW8.badOf cover1) (SixW8.badOf cover2) (SixW8.badOf cover3) (SixW8.badOf cover4) 0 2 2 0 0) = some 68349 := by
  rw [show SixW8.boxOf (SixW8.badOf cover0) (SixW8.badOf cover1) (SixW8.badOf cover2) (SixW8.badOf cover3) (SixW8.badOf cover4) 0 2 2 0 0 = bx86 from by decide +kernel]; exact wk86

theorem root_02201 : SixW8.walk table bits 64 68349 (SixW8.boxOf (SixW8.badOf cover0) (SixW8.badOf cover1) (SixW8.badOf cover2) (SixW8.badOf cover3) (SixW8.badOf cover4) 0 2 2 0 1) = some 68350 := by
  rw [show SixW8.boxOf (SixW8.badOf cover0) (SixW8.badOf cover1) (SixW8.badOf cover2) (SixW8.badOf cover3) (SixW8.badOf cover4) 0 2 2 0 1 = bx87 from by decide +kernel]; exact wk87

theorem root_02210 : SixW8.walk table bits 64 68350 (SixW8.boxOf (SixW8.badOf cover0) (SixW8.badOf cover1) (SixW8.badOf cover2) (SixW8.badOf cover3) (SixW8.badOf cover4) 0 2 2 1 0) = some 68351 := by
  rw [show SixW8.boxOf (SixW8.badOf cover0) (SixW8.badOf cover1) (SixW8.badOf cover2) (SixW8.badOf cover3) (SixW8.badOf cover4) 0 2 2 1 0 = bx88 from by decide +kernel]; exact wk88

theorem root_02211 : SixW8.walk table bits 64 68351 (SixW8.boxOf (SixW8.badOf cover0) (SixW8.badOf cover1) (SixW8.badOf cover2) (SixW8.badOf cover3) (SixW8.badOf cover4) 0 2 2 1 1) = some 68352 := by
  rw [show SixW8.boxOf (SixW8.badOf cover0) (SixW8.badOf cover1) (SixW8.badOf cover2) (SixW8.badOf cover3) (SixW8.badOf cover4) 0 2 2 1 1 = bx89 from by decide +kernel]; exact wk89

theorem root_02220 : SixW8.walk table bits 64 68352 (SixW8.boxOf (SixW8.badOf cover0) (SixW8.badOf cover1) (SixW8.badOf cover2) (SixW8.badOf cover3) (SixW8.badOf cover4) 0 2 2 2 0) = some 68353 := by
  rw [show SixW8.boxOf (SixW8.badOf cover0) (SixW8.badOf cover1) (SixW8.badOf cover2) (SixW8.badOf cover3) (SixW8.badOf cover4) 0 2 2 2 0 = bx90 from by decide +kernel]; exact wk90

theorem root_02221 : SixW8.walk table bits 64 68353 (SixW8.boxOf (SixW8.badOf cover0) (SixW8.badOf cover1) (SixW8.badOf cover2) (SixW8.badOf cover3) (SixW8.badOf cover4) 0 2 2 2 1) = some 68354 := by
  rw [show SixW8.boxOf (SixW8.badOf cover0) (SixW8.badOf cover1) (SixW8.badOf cover2) (SixW8.badOf cover3) (SixW8.badOf cover4) 0 2 2 2 1 = bx91 from by decide +kernel]; exact wk91

theorem root_10000 : SixW8.walk table bits 64 68354 (SixW8.boxOf (SixW8.badOf cover0) (SixW8.badOf cover1) (SixW8.badOf cover2) (SixW8.badOf cover3) (SixW8.badOf cover4) 1 0 0 0 0) = some 68355 := by
  rw [show SixW8.boxOf (SixW8.badOf cover0) (SixW8.badOf cover1) (SixW8.badOf cover2) (SixW8.badOf cover3) (SixW8.badOf cover4) 1 0 0 0 0 = bx92 from by decide +kernel]; exact wk92

theorem root_10001 : SixW8.walk table bits 64 68355 (SixW8.boxOf (SixW8.badOf cover0) (SixW8.badOf cover1) (SixW8.badOf cover2) (SixW8.badOf cover3) (SixW8.badOf cover4) 1 0 0 0 1) = some 72406 := by
  rw [show SixW8.boxOf (SixW8.badOf cover0) (SixW8.badOf cover1) (SixW8.badOf cover2) (SixW8.badOf cover3) (SixW8.badOf cover4) 1 0 0 0 1 = bx93 from by decide +kernel]; exact wk93

theorem root_10010 : SixW8.walk table bits 64 72406 (SixW8.boxOf (SixW8.badOf cover0) (SixW8.badOf cover1) (SixW8.badOf cover2) (SixW8.badOf cover3) (SixW8.badOf cover4) 1 0 0 1 0) = some 72407 := by
  rw [show SixW8.boxOf (SixW8.badOf cover0) (SixW8.badOf cover1) (SixW8.badOf cover2) (SixW8.badOf cover3) (SixW8.badOf cover4) 1 0 0 1 0 = bx94 from by decide +kernel]; exact wk94

theorem root_10011 : SixW8.walk table bits 64 72407 (SixW8.boxOf (SixW8.badOf cover0) (SixW8.badOf cover1) (SixW8.badOf cover2) (SixW8.badOf cover3) (SixW8.badOf cover4) 1 0 0 1 1) = some 76268 := by
  rw [show SixW8.boxOf (SixW8.badOf cover0) (SixW8.badOf cover1) (SixW8.badOf cover2) (SixW8.badOf cover3) (SixW8.badOf cover4) 1 0 0 1 1 = bx95 from by decide +kernel]; exact wk95

theorem root_10020 : SixW8.walk table bits 64 76268 (SixW8.boxOf (SixW8.badOf cover0) (SixW8.badOf cover1) (SixW8.badOf cover2) (SixW8.badOf cover3) (SixW8.badOf cover4) 1 0 0 2 0) = some 76269 := by
  rw [show SixW8.boxOf (SixW8.badOf cover0) (SixW8.badOf cover1) (SixW8.badOf cover2) (SixW8.badOf cover3) (SixW8.badOf cover4) 1 0 0 2 0 = bx96 from by decide +kernel]; exact wk96

theorem root_10021 : SixW8.walk table bits 64 76269 (SixW8.boxOf (SixW8.badOf cover0) (SixW8.badOf cover1) (SixW8.badOf cover2) (SixW8.badOf cover3) (SixW8.badOf cover4) 1 0 0 2 1) = some 76615 := by
  rw [show SixW8.boxOf (SixW8.badOf cover0) (SixW8.badOf cover1) (SixW8.badOf cover2) (SixW8.badOf cover3) (SixW8.badOf cover4) 1 0 0 2 1 = bx97 from by decide +kernel]; exact wk97

theorem root_10100 : SixW8.walk table bits 64 76615 (SixW8.boxOf (SixW8.badOf cover0) (SixW8.badOf cover1) (SixW8.badOf cover2) (SixW8.badOf cover3) (SixW8.badOf cover4) 1 0 1 0 0) = some 76616 := by
  rw [show SixW8.boxOf (SixW8.badOf cover0) (SixW8.badOf cover1) (SixW8.badOf cover2) (SixW8.badOf cover3) (SixW8.badOf cover4) 1 0 1 0 0 = bx98 from by decide +kernel]; exact wk98

theorem root_10101 : SixW8.walk table bits 64 76616 (SixW8.boxOf (SixW8.badOf cover0) (SixW8.badOf cover1) (SixW8.badOf cover2) (SixW8.badOf cover3) (SixW8.badOf cover4) 1 0 1 0 1) = some 83447 := by
  rw [show SixW8.boxOf (SixW8.badOf cover0) (SixW8.badOf cover1) (SixW8.badOf cover2) (SixW8.badOf cover3) (SixW8.badOf cover4) 1 0 1 0 1 = bx99 from by decide +kernel]; exact wk99

theorem root_10110 : SixW8.walk table bits 64 83447 (SixW8.boxOf (SixW8.badOf cover0) (SixW8.badOf cover1) (SixW8.badOf cover2) (SixW8.badOf cover3) (SixW8.badOf cover4) 1 0 1 1 0) = some 83448 := by
  rw [show SixW8.boxOf (SixW8.badOf cover0) (SixW8.badOf cover1) (SixW8.badOf cover2) (SixW8.badOf cover3) (SixW8.badOf cover4) 1 0 1 1 0 = bx130 from by decide +kernel]; exact wk130

theorem root_10111 : SixW8.walk table bits 64 83448 (SixW8.boxOf (SixW8.badOf cover0) (SixW8.badOf cover1) (SixW8.badOf cover2) (SixW8.badOf cover3) (SixW8.badOf cover4) 1 0 1 1 1) = some 83934 := by
  rw [show SixW8.boxOf (SixW8.badOf cover0) (SixW8.badOf cover1) (SixW8.badOf cover2) (SixW8.badOf cover3) (SixW8.badOf cover4) 1 0 1 1 1 = bx131 from by decide +kernel]; exact wk131

theorem root_10120 : SixW8.walk table bits 64 83934 (SixW8.boxOf (SixW8.badOf cover0) (SixW8.badOf cover1) (SixW8.badOf cover2) (SixW8.badOf cover3) (SixW8.badOf cover4) 1 0 1 2 0) = some 83935 := by
  rw [show SixW8.boxOf (SixW8.badOf cover0) (SixW8.badOf cover1) (SixW8.badOf cover2) (SixW8.badOf cover3) (SixW8.badOf cover4) 1 0 1 2 0 = bx132 from by decide +kernel]; exact wk132

theorem root_10121 : SixW8.walk table bits 64 83935 (SixW8.boxOf (SixW8.badOf cover0) (SixW8.badOf cover1) (SixW8.badOf cover2) (SixW8.badOf cover3) (SixW8.badOf cover4) 1 0 1 2 1) = some 83996 := by
  rw [show SixW8.boxOf (SixW8.badOf cover0) (SixW8.badOf cover1) (SixW8.badOf cover2) (SixW8.badOf cover3) (SixW8.badOf cover4) 1 0 1 2 1 = bx133 from by decide +kernel]; exact wk133

theorem root_10200 : SixW8.walk table bits 64 83996 (SixW8.boxOf (SixW8.badOf cover0) (SixW8.badOf cover1) (SixW8.badOf cover2) (SixW8.badOf cover3) (SixW8.badOf cover4) 1 0 2 0 0) = some 83997 := by
  rw [show SixW8.boxOf (SixW8.badOf cover0) (SixW8.badOf cover1) (SixW8.badOf cover2) (SixW8.badOf cover3) (SixW8.badOf cover4) 1 0 2 0 0 = bx134 from by decide +kernel]; exact wk134

theorem root_10201 : SixW8.walk table bits 64 83997 (SixW8.boxOf (SixW8.badOf cover0) (SixW8.badOf cover1) (SixW8.badOf cover2) (SixW8.badOf cover3) (SixW8.badOf cover4) 1 0 2 0 1) = some 84273 := by
  rw [show SixW8.boxOf (SixW8.badOf cover0) (SixW8.badOf cover1) (SixW8.badOf cover2) (SixW8.badOf cover3) (SixW8.badOf cover4) 1 0 2 0 1 = bx135 from by decide +kernel]; exact wk135

theorem root_10210 : SixW8.walk table bits 64 84273 (SixW8.boxOf (SixW8.badOf cover0) (SixW8.badOf cover1) (SixW8.badOf cover2) (SixW8.badOf cover3) (SixW8.badOf cover4) 1 0 2 1 0) = some 84274 := by
  rw [show SixW8.boxOf (SixW8.badOf cover0) (SixW8.badOf cover1) (SixW8.badOf cover2) (SixW8.badOf cover3) (SixW8.badOf cover4) 1 0 2 1 0 = bx136 from by decide +kernel]; exact wk136

theorem root_10211 : SixW8.walk table bits 64 84274 (SixW8.boxOf (SixW8.badOf cover0) (SixW8.badOf cover1) (SixW8.badOf cover2) (SixW8.badOf cover3) (SixW8.badOf cover4) 1 0 2 1 1) = some 84275 := by
  rw [show SixW8.boxOf (SixW8.badOf cover0) (SixW8.badOf cover1) (SixW8.badOf cover2) (SixW8.badOf cover3) (SixW8.badOf cover4) 1 0 2 1 1 = bx137 from by decide +kernel]; exact wk137

theorem root_10220 : SixW8.walk table bits 64 84275 (SixW8.boxOf (SixW8.badOf cover0) (SixW8.badOf cover1) (SixW8.badOf cover2) (SixW8.badOf cover3) (SixW8.badOf cover4) 1 0 2 2 0) = some 84276 := by
  rw [show SixW8.boxOf (SixW8.badOf cover0) (SixW8.badOf cover1) (SixW8.badOf cover2) (SixW8.badOf cover3) (SixW8.badOf cover4) 1 0 2 2 0 = bx138 from by decide +kernel]; exact wk138

theorem root_10221 : SixW8.walk table bits 64 84276 (SixW8.boxOf (SixW8.badOf cover0) (SixW8.badOf cover1) (SixW8.badOf cover2) (SixW8.badOf cover3) (SixW8.badOf cover4) 1 0 2 2 1) = some 84277 := by
  rw [show SixW8.boxOf (SixW8.badOf cover0) (SixW8.badOf cover1) (SixW8.badOf cover2) (SixW8.badOf cover3) (SixW8.badOf cover4) 1 0 2 2 1 = bx139 from by decide +kernel]; exact wk139

theorem root_11000 : SixW8.walk table bits 64 84277 (SixW8.boxOf (SixW8.badOf cover0) (SixW8.badOf cover1) (SixW8.badOf cover2) (SixW8.badOf cover3) (SixW8.badOf cover4) 1 1 0 0 0) = some 84278 := by
  rw [show SixW8.boxOf (SixW8.badOf cover0) (SixW8.badOf cover1) (SixW8.badOf cover2) (SixW8.badOf cover3) (SixW8.badOf cover4) 1 1 0 0 0 = bx140 from by decide +kernel]; exact wk140

theorem root_11001 : SixW8.walk table bits 64 84278 (SixW8.boxOf (SixW8.badOf cover0) (SixW8.badOf cover1) (SixW8.badOf cover2) (SixW8.badOf cover3) (SixW8.badOf cover4) 1 1 0 0 1) = some 87894 := by
  rw [show SixW8.boxOf (SixW8.badOf cover0) (SixW8.badOf cover1) (SixW8.badOf cover2) (SixW8.badOf cover3) (SixW8.badOf cover4) 1 1 0 0 1 = bx141 from by decide +kernel]; exact wk141

theorem root_11010 : SixW8.walk table bits 64 87894 (SixW8.boxOf (SixW8.badOf cover0) (SixW8.badOf cover1) (SixW8.badOf cover2) (SixW8.badOf cover3) (SixW8.badOf cover4) 1 1 0 1 0) = some 87895 := by
  rw [show SixW8.boxOf (SixW8.badOf cover0) (SixW8.badOf cover1) (SixW8.badOf cover2) (SixW8.badOf cover3) (SixW8.badOf cover4) 1 1 0 1 0 = bx142 from by decide +kernel]; exact wk142

theorem root_11011 : SixW8.walk table bits 64 87895 (SixW8.boxOf (SixW8.badOf cover0) (SixW8.badOf cover1) (SixW8.badOf cover2) (SixW8.badOf cover3) (SixW8.badOf cover4) 1 1 0 1 1) = some 88736 := by
  rw [show SixW8.boxOf (SixW8.badOf cover0) (SixW8.badOf cover1) (SixW8.badOf cover2) (SixW8.badOf cover3) (SixW8.badOf cover4) 1 1 0 1 1 = bx143 from by decide +kernel]; exact wk143

theorem root_11020 : SixW8.walk table bits 64 88736 (SixW8.boxOf (SixW8.badOf cover0) (SixW8.badOf cover1) (SixW8.badOf cover2) (SixW8.badOf cover3) (SixW8.badOf cover4) 1 1 0 2 0) = some 88737 := by
  rw [show SixW8.boxOf (SixW8.badOf cover0) (SixW8.badOf cover1) (SixW8.badOf cover2) (SixW8.badOf cover3) (SixW8.badOf cover4) 1 1 0 2 0 = bx144 from by decide +kernel]; exact wk144

theorem root_11021 : SixW8.walk table bits 64 88737 (SixW8.boxOf (SixW8.badOf cover0) (SixW8.badOf cover1) (SixW8.badOf cover2) (SixW8.badOf cover3) (SixW8.badOf cover4) 1 1 0 2 1) = some 88813 := by
  rw [show SixW8.boxOf (SixW8.badOf cover0) (SixW8.badOf cover1) (SixW8.badOf cover2) (SixW8.badOf cover3) (SixW8.badOf cover4) 1 1 0 2 1 = bx145 from by decide +kernel]; exact wk145

theorem root_11100 : SixW8.walk table bits 64 88813 (SixW8.boxOf (SixW8.badOf cover0) (SixW8.badOf cover1) (SixW8.badOf cover2) (SixW8.badOf cover3) (SixW8.badOf cover4) 1 1 1 0 0) = some 88814 := by
  rw [show SixW8.boxOf (SixW8.badOf cover0) (SixW8.badOf cover1) (SixW8.badOf cover2) (SixW8.badOf cover3) (SixW8.badOf cover4) 1 1 1 0 0 = bx146 from by decide +kernel]; exact wk146

theorem root_11101 : SixW8.walk table bits 64 88814 (SixW8.boxOf (SixW8.badOf cover0) (SixW8.badOf cover1) (SixW8.badOf cover2) (SixW8.badOf cover3) (SixW8.badOf cover4) 1 1 1 0 1) = some 89310 := by
  rw [show SixW8.boxOf (SixW8.badOf cover0) (SixW8.badOf cover1) (SixW8.badOf cover2) (SixW8.badOf cover3) (SixW8.badOf cover4) 1 1 1 0 1 = bx147 from by decide +kernel]; exact wk147

theorem root_11110 : SixW8.walk table bits 64 89310 (SixW8.boxOf (SixW8.badOf cover0) (SixW8.badOf cover1) (SixW8.badOf cover2) (SixW8.badOf cover3) (SixW8.badOf cover4) 1 1 1 1 0) = some 89311 := by
  rw [show SixW8.boxOf (SixW8.badOf cover0) (SixW8.badOf cover1) (SixW8.badOf cover2) (SixW8.badOf cover3) (SixW8.badOf cover4) 1 1 1 1 0 = bx148 from by decide +kernel]; exact wk148

theorem root_11111 : SixW8.walk table bits 64 89311 (SixW8.boxOf (SixW8.badOf cover0) (SixW8.badOf cover1) (SixW8.badOf cover2) (SixW8.badOf cover3) (SixW8.badOf cover4) 1 1 1 1 1) = some 89357 := by
  rw [show SixW8.boxOf (SixW8.badOf cover0) (SixW8.badOf cover1) (SixW8.badOf cover2) (SixW8.badOf cover3) (SixW8.badOf cover4) 1 1 1 1 1 = bx149 from by decide +kernel]; exact wk149

theorem root_11120 : SixW8.walk table bits 64 89357 (SixW8.boxOf (SixW8.badOf cover0) (SixW8.badOf cover1) (SixW8.badOf cover2) (SixW8.badOf cover3) (SixW8.badOf cover4) 1 1 1 2 0) = some 89358 := by
  rw [show SixW8.boxOf (SixW8.badOf cover0) (SixW8.badOf cover1) (SixW8.badOf cover2) (SixW8.badOf cover3) (SixW8.badOf cover4) 1 1 1 2 0 = bx150 from by decide +kernel]; exact wk150

theorem root_11121 : SixW8.walk table bits 64 89358 (SixW8.boxOf (SixW8.badOf cover0) (SixW8.badOf cover1) (SixW8.badOf cover2) (SixW8.badOf cover3) (SixW8.badOf cover4) 1 1 1 2 1) = some 89359 := by
  rw [show SixW8.boxOf (SixW8.badOf cover0) (SixW8.badOf cover1) (SixW8.badOf cover2) (SixW8.badOf cover3) (SixW8.badOf cover4) 1 1 1 2 1 = bx151 from by decide +kernel]; exact wk151

theorem root_11200 : SixW8.walk table bits 64 89359 (SixW8.boxOf (SixW8.badOf cover0) (SixW8.badOf cover1) (SixW8.badOf cover2) (SixW8.badOf cover3) (SixW8.badOf cover4) 1 1 2 0 0) = some 89360 := by
  rw [show SixW8.boxOf (SixW8.badOf cover0) (SixW8.badOf cover1) (SixW8.badOf cover2) (SixW8.badOf cover3) (SixW8.badOf cover4) 1 1 2 0 0 = bx152 from by decide +kernel]; exact wk152

theorem root_11201 : SixW8.walk table bits 64 89360 (SixW8.boxOf (SixW8.badOf cover0) (SixW8.badOf cover1) (SixW8.badOf cover2) (SixW8.badOf cover3) (SixW8.badOf cover4) 1 1 2 0 1) = some 89361 := by
  rw [show SixW8.boxOf (SixW8.badOf cover0) (SixW8.badOf cover1) (SixW8.badOf cover2) (SixW8.badOf cover3) (SixW8.badOf cover4) 1 1 2 0 1 = bx153 from by decide +kernel]; exact wk153

theorem root_11210 : SixW8.walk table bits 64 89361 (SixW8.boxOf (SixW8.badOf cover0) (SixW8.badOf cover1) (SixW8.badOf cover2) (SixW8.badOf cover3) (SixW8.badOf cover4) 1 1 2 1 0) = some 89362 := by
  rw [show SixW8.boxOf (SixW8.badOf cover0) (SixW8.badOf cover1) (SixW8.badOf cover2) (SixW8.badOf cover3) (SixW8.badOf cover4) 1 1 2 1 0 = bx154 from by decide +kernel]; exact wk154

theorem root_11211 : SixW8.walk table bits 64 89362 (SixW8.boxOf (SixW8.badOf cover0) (SixW8.badOf cover1) (SixW8.badOf cover2) (SixW8.badOf cover3) (SixW8.badOf cover4) 1 1 2 1 1) = some 89363 := by
  rw [show SixW8.boxOf (SixW8.badOf cover0) (SixW8.badOf cover1) (SixW8.badOf cover2) (SixW8.badOf cover3) (SixW8.badOf cover4) 1 1 2 1 1 = bx155 from by decide +kernel]; exact wk155

theorem root_11220 : SixW8.walk table bits 64 89363 (SixW8.boxOf (SixW8.badOf cover0) (SixW8.badOf cover1) (SixW8.badOf cover2) (SixW8.badOf cover3) (SixW8.badOf cover4) 1 1 2 2 0) = some 89364 := by
  rw [show SixW8.boxOf (SixW8.badOf cover0) (SixW8.badOf cover1) (SixW8.badOf cover2) (SixW8.badOf cover3) (SixW8.badOf cover4) 1 1 2 2 0 = bx156 from by decide +kernel]; exact wk156

theorem root_11221 : SixW8.walk table bits 64 89364 (SixW8.boxOf (SixW8.badOf cover0) (SixW8.badOf cover1) (SixW8.badOf cover2) (SixW8.badOf cover3) (SixW8.badOf cover4) 1 1 2 2 1) = some 89365 := by
  rw [show SixW8.boxOf (SixW8.badOf cover0) (SixW8.badOf cover1) (SixW8.badOf cover2) (SixW8.badOf cover3) (SixW8.badOf cover4) 1 1 2 2 1 = bx157 from by decide +kernel]; exact wk157

theorem root_12000 : SixW8.walk table bits 64 89365 (SixW8.boxOf (SixW8.badOf cover0) (SixW8.badOf cover1) (SixW8.badOf cover2) (SixW8.badOf cover3) (SixW8.badOf cover4) 1 2 0 0 0) = some 89366 := by
  rw [show SixW8.boxOf (SixW8.badOf cover0) (SixW8.badOf cover1) (SixW8.badOf cover2) (SixW8.badOf cover3) (SixW8.badOf cover4) 1 2 0 0 0 = bx158 from by decide +kernel]; exact wk158

theorem root_12001 : SixW8.walk table bits 64 89366 (SixW8.boxOf (SixW8.badOf cover0) (SixW8.badOf cover1) (SixW8.badOf cover2) (SixW8.badOf cover3) (SixW8.badOf cover4) 1 2 0 0 1) = some 89707 := by
  rw [show SixW8.boxOf (SixW8.badOf cover0) (SixW8.badOf cover1) (SixW8.badOf cover2) (SixW8.badOf cover3) (SixW8.badOf cover4) 1 2 0 0 1 = bx159 from by decide +kernel]; exact wk159

theorem root_12010 : SixW8.walk table bits 64 89707 (SixW8.boxOf (SixW8.badOf cover0) (SixW8.badOf cover1) (SixW8.badOf cover2) (SixW8.badOf cover3) (SixW8.badOf cover4) 1 2 0 1 0) = some 89708 := by
  rw [show SixW8.boxOf (SixW8.badOf cover0) (SixW8.badOf cover1) (SixW8.badOf cover2) (SixW8.badOf cover3) (SixW8.badOf cover4) 1 2 0 1 0 = bx160 from by decide +kernel]; exact wk160

theorem root_12011 : SixW8.walk table bits 64 89708 (SixW8.boxOf (SixW8.badOf cover0) (SixW8.badOf cover1) (SixW8.badOf cover2) (SixW8.badOf cover3) (SixW8.badOf cover4) 1 2 0 1 1) = some 89784 := by
  rw [show SixW8.boxOf (SixW8.badOf cover0) (SixW8.badOf cover1) (SixW8.badOf cover2) (SixW8.badOf cover3) (SixW8.badOf cover4) 1 2 0 1 1 = bx161 from by decide +kernel]; exact wk161

theorem root_12020 : SixW8.walk table bits 64 89784 (SixW8.boxOf (SixW8.badOf cover0) (SixW8.badOf cover1) (SixW8.badOf cover2) (SixW8.badOf cover3) (SixW8.badOf cover4) 1 2 0 2 0) = some 89785 := by
  rw [show SixW8.boxOf (SixW8.badOf cover0) (SixW8.badOf cover1) (SixW8.badOf cover2) (SixW8.badOf cover3) (SixW8.badOf cover4) 1 2 0 2 0 = bx162 from by decide +kernel]; exact wk162

theorem root_12021 : SixW8.walk table bits 64 89785 (SixW8.boxOf (SixW8.badOf cover0) (SixW8.badOf cover1) (SixW8.badOf cover2) (SixW8.badOf cover3) (SixW8.badOf cover4) 1 2 0 2 1) = some 89786 := by
  rw [show SixW8.boxOf (SixW8.badOf cover0) (SixW8.badOf cover1) (SixW8.badOf cover2) (SixW8.badOf cover3) (SixW8.badOf cover4) 1 2 0 2 1 = bx163 from by decide +kernel]; exact wk163

theorem root_12100 : SixW8.walk table bits 64 89786 (SixW8.boxOf (SixW8.badOf cover0) (SixW8.badOf cover1) (SixW8.badOf cover2) (SixW8.badOf cover3) (SixW8.badOf cover4) 1 2 1 0 0) = some 89787 := by
  rw [show SixW8.boxOf (SixW8.badOf cover0) (SixW8.badOf cover1) (SixW8.badOf cover2) (SixW8.badOf cover3) (SixW8.badOf cover4) 1 2 1 0 0 = bx164 from by decide +kernel]; exact wk164

theorem root_12101 : SixW8.walk table bits 64 89787 (SixW8.boxOf (SixW8.badOf cover0) (SixW8.badOf cover1) (SixW8.badOf cover2) (SixW8.badOf cover3) (SixW8.badOf cover4) 1 2 1 0 1) = some 89848 := by
  rw [show SixW8.boxOf (SixW8.badOf cover0) (SixW8.badOf cover1) (SixW8.badOf cover2) (SixW8.badOf cover3) (SixW8.badOf cover4) 1 2 1 0 1 = bx165 from by decide +kernel]; exact wk165

theorem root_12110 : SixW8.walk table bits 64 89848 (SixW8.boxOf (SixW8.badOf cover0) (SixW8.badOf cover1) (SixW8.badOf cover2) (SixW8.badOf cover3) (SixW8.badOf cover4) 1 2 1 1 0) = some 89849 := by
  rw [show SixW8.boxOf (SixW8.badOf cover0) (SixW8.badOf cover1) (SixW8.badOf cover2) (SixW8.badOf cover3) (SixW8.badOf cover4) 1 2 1 1 0 = bx166 from by decide +kernel]; exact wk166

theorem root_12111 : SixW8.walk table bits 64 89849 (SixW8.boxOf (SixW8.badOf cover0) (SixW8.badOf cover1) (SixW8.badOf cover2) (SixW8.badOf cover3) (SixW8.badOf cover4) 1 2 1 1 1) = some 89850 := by
  rw [show SixW8.boxOf (SixW8.badOf cover0) (SixW8.badOf cover1) (SixW8.badOf cover2) (SixW8.badOf cover3) (SixW8.badOf cover4) 1 2 1 1 1 = bx167 from by decide +kernel]; exact wk167

theorem root_12120 : SixW8.walk table bits 64 89850 (SixW8.boxOf (SixW8.badOf cover0) (SixW8.badOf cover1) (SixW8.badOf cover2) (SixW8.badOf cover3) (SixW8.badOf cover4) 1 2 1 2 0) = some 89851 := by
  rw [show SixW8.boxOf (SixW8.badOf cover0) (SixW8.badOf cover1) (SixW8.badOf cover2) (SixW8.badOf cover3) (SixW8.badOf cover4) 1 2 1 2 0 = bx168 from by decide +kernel]; exact wk168

theorem root_12121 : SixW8.walk table bits 64 89851 (SixW8.boxOf (SixW8.badOf cover0) (SixW8.badOf cover1) (SixW8.badOf cover2) (SixW8.badOf cover3) (SixW8.badOf cover4) 1 2 1 2 1) = some 89852 := by
  rw [show SixW8.boxOf (SixW8.badOf cover0) (SixW8.badOf cover1) (SixW8.badOf cover2) (SixW8.badOf cover3) (SixW8.badOf cover4) 1 2 1 2 1 = bx169 from by decide +kernel]; exact wk169

theorem root_12200 : SixW8.walk table bits 64 89852 (SixW8.boxOf (SixW8.badOf cover0) (SixW8.badOf cover1) (SixW8.badOf cover2) (SixW8.badOf cover3) (SixW8.badOf cover4) 1 2 2 0 0) = some 89853 := by
  rw [show SixW8.boxOf (SixW8.badOf cover0) (SixW8.badOf cover1) (SixW8.badOf cover2) (SixW8.badOf cover3) (SixW8.badOf cover4) 1 2 2 0 0 = bx170 from by decide +kernel]; exact wk170

theorem root_12201 : SixW8.walk table bits 64 89853 (SixW8.boxOf (SixW8.badOf cover0) (SixW8.badOf cover1) (SixW8.badOf cover2) (SixW8.badOf cover3) (SixW8.badOf cover4) 1 2 2 0 1) = some 89854 := by
  rw [show SixW8.boxOf (SixW8.badOf cover0) (SixW8.badOf cover1) (SixW8.badOf cover2) (SixW8.badOf cover3) (SixW8.badOf cover4) 1 2 2 0 1 = bx171 from by decide +kernel]; exact wk171

theorem root_12210 : SixW8.walk table bits 64 89854 (SixW8.boxOf (SixW8.badOf cover0) (SixW8.badOf cover1) (SixW8.badOf cover2) (SixW8.badOf cover3) (SixW8.badOf cover4) 1 2 2 1 0) = some 89855 := by
  rw [show SixW8.boxOf (SixW8.badOf cover0) (SixW8.badOf cover1) (SixW8.badOf cover2) (SixW8.badOf cover3) (SixW8.badOf cover4) 1 2 2 1 0 = bx172 from by decide +kernel]; exact wk172

theorem root_12211 : SixW8.walk table bits 64 89855 (SixW8.boxOf (SixW8.badOf cover0) (SixW8.badOf cover1) (SixW8.badOf cover2) (SixW8.badOf cover3) (SixW8.badOf cover4) 1 2 2 1 1) = some 89856 := by
  rw [show SixW8.boxOf (SixW8.badOf cover0) (SixW8.badOf cover1) (SixW8.badOf cover2) (SixW8.badOf cover3) (SixW8.badOf cover4) 1 2 2 1 1 = bx173 from by decide +kernel]; exact wk173

theorem root_12220 : SixW8.walk table bits 64 89856 (SixW8.boxOf (SixW8.badOf cover0) (SixW8.badOf cover1) (SixW8.badOf cover2) (SixW8.badOf cover3) (SixW8.badOf cover4) 1 2 2 2 0) = some 89857 := by
  rw [show SixW8.boxOf (SixW8.badOf cover0) (SixW8.badOf cover1) (SixW8.badOf cover2) (SixW8.badOf cover3) (SixW8.badOf cover4) 1 2 2 2 0 = bx174 from by decide +kernel]; exact wk174

theorem root_12221 : SixW8.walk table bits 64 89857 (SixW8.boxOf (SixW8.badOf cover0) (SixW8.badOf cover1) (SixW8.badOf cover2) (SixW8.badOf cover3) (SixW8.badOf cover4) 1 2 2 2 1) = some 89858 := by
  rw [show SixW8.boxOf (SixW8.badOf cover0) (SixW8.badOf cover1) (SixW8.badOf cover2) (SixW8.badOf cover3) (SixW8.badOf cover4) 1 2 2 2 1 = bx175 from by decide +kernel]; exact wk175

theorem run_ok : ∀ i0 i1 i2 i3 i4, i0 < (SixW8.badOf cover0).length → i1 < (SixW8.badOf cover1).length → i2 < (SixW8.badOf cover2).length → i3 < (SixW8.badOf cover3).length → i4 < (SixW8.badOf cover4).length →
    ∃ pos pos', SixW8.walk table bits 64 pos (SixW8.boxOf (SixW8.badOf cover0) (SixW8.badOf cover1) (SixW8.badOf cover2) (SixW8.badOf cover3) (SixW8.badOf cover4) i0 i1 i2 i3 i4) = some pos' := by
  intro i0 i1 i2 i3 i4 hi0 hi1 hi2 hi3 hi4
  rw [nb0_eq] at hi0
  rw [nb1_eq] at hi1
  rw [nb2_eq] at hi2
  rw [nb3_eq] at hi3
  rw [nb4_eq] at hi4
  match i0, i1, i2, i3, i4, hi0, hi1, hi2, hi3, hi4 with
  | 0, 0, 0, 0, 0, _, _, _, _, _ => exact ⟨_, _, root_00000⟩
  | 0, 0, 0, 0, 1, _, _, _, _, _ => exact ⟨_, _, root_00001⟩
  | 0, 0, 0, 1, 0, _, _, _, _, _ => exact ⟨_, _, root_00010⟩
  | 0, 0, 0, 1, 1, _, _, _, _, _ => exact ⟨_, _, root_00011⟩
  | 0, 0, 0, 2, 0, _, _, _, _, _ => exact ⟨_, _, root_00020⟩
  | 0, 0, 0, 2, 1, _, _, _, _, _ => exact ⟨_, _, root_00021⟩
  | 0, 0, 1, 0, 0, _, _, _, _, _ => exact ⟨_, _, root_00100⟩
  | 0, 0, 1, 0, 1, _, _, _, _, _ => exact ⟨_, _, root_00101⟩
  | 0, 0, 1, 1, 0, _, _, _, _, _ => exact ⟨_, _, root_00110⟩
  | 0, 0, 1, 1, 1, _, _, _, _, _ => exact ⟨_, _, root_00111⟩
  | 0, 0, 1, 2, 0, _, _, _, _, _ => exact ⟨_, _, root_00120⟩
  | 0, 0, 1, 2, 1, _, _, _, _, _ => exact ⟨_, _, root_00121⟩
  | 0, 0, 2, 0, 0, _, _, _, _, _ => exact ⟨_, _, root_00200⟩
  | 0, 0, 2, 0, 1, _, _, _, _, _ => exact ⟨_, _, root_00201⟩
  | 0, 0, 2, 1, 0, _, _, _, _, _ => exact ⟨_, _, root_00210⟩
  | 0, 0, 2, 1, 1, _, _, _, _, _ => exact ⟨_, _, root_00211⟩
  | 0, 0, 2, 2, 0, _, _, _, _, _ => exact ⟨_, _, root_00220⟩
  | 0, 0, 2, 2, 1, _, _, _, _, _ => exact ⟨_, _, root_00221⟩
  | 0, 1, 0, 0, 0, _, _, _, _, _ => exact ⟨_, _, root_01000⟩
  | 0, 1, 0, 0, 1, _, _, _, _, _ => exact ⟨_, _, root_01001⟩
  | 0, 1, 0, 1, 0, _, _, _, _, _ => exact ⟨_, _, root_01010⟩
  | 0, 1, 0, 1, 1, _, _, _, _, _ => exact ⟨_, _, root_01011⟩
  | 0, 1, 0, 2, 0, _, _, _, _, _ => exact ⟨_, _, root_01020⟩
  | 0, 1, 0, 2, 1, _, _, _, _, _ => exact ⟨_, _, root_01021⟩
  | 0, 1, 1, 0, 0, _, _, _, _, _ => exact ⟨_, _, root_01100⟩
  | 0, 1, 1, 0, 1, _, _, _, _, _ => exact ⟨_, _, root_01101⟩
  | 0, 1, 1, 1, 0, _, _, _, _, _ => exact ⟨_, _, root_01110⟩
  | 0, 1, 1, 1, 1, _, _, _, _, _ => exact ⟨_, _, root_01111⟩
  | 0, 1, 1, 2, 0, _, _, _, _, _ => exact ⟨_, _, root_01120⟩
  | 0, 1, 1, 2, 1, _, _, _, _, _ => exact ⟨_, _, root_01121⟩
  | 0, 1, 2, 0, 0, _, _, _, _, _ => exact ⟨_, _, root_01200⟩
  | 0, 1, 2, 0, 1, _, _, _, _, _ => exact ⟨_, _, root_01201⟩
  | 0, 1, 2, 1, 0, _, _, _, _, _ => exact ⟨_, _, root_01210⟩
  | 0, 1, 2, 1, 1, _, _, _, _, _ => exact ⟨_, _, root_01211⟩
  | 0, 1, 2, 2, 0, _, _, _, _, _ => exact ⟨_, _, root_01220⟩
  | 0, 1, 2, 2, 1, _, _, _, _, _ => exact ⟨_, _, root_01221⟩
  | 0, 2, 0, 0, 0, _, _, _, _, _ => exact ⟨_, _, root_02000⟩
  | 0, 2, 0, 0, 1, _, _, _, _, _ => exact ⟨_, _, root_02001⟩
  | 0, 2, 0, 1, 0, _, _, _, _, _ => exact ⟨_, _, root_02010⟩
  | 0, 2, 0, 1, 1, _, _, _, _, _ => exact ⟨_, _, root_02011⟩
  | 0, 2, 0, 2, 0, _, _, _, _, _ => exact ⟨_, _, root_02020⟩
  | 0, 2, 0, 2, 1, _, _, _, _, _ => exact ⟨_, _, root_02021⟩
  | 0, 2, 1, 0, 0, _, _, _, _, _ => exact ⟨_, _, root_02100⟩
  | 0, 2, 1, 0, 1, _, _, _, _, _ => exact ⟨_, _, root_02101⟩
  | 0, 2, 1, 1, 0, _, _, _, _, _ => exact ⟨_, _, root_02110⟩
  | 0, 2, 1, 1, 1, _, _, _, _, _ => exact ⟨_, _, root_02111⟩
  | 0, 2, 1, 2, 0, _, _, _, _, _ => exact ⟨_, _, root_02120⟩
  | 0, 2, 1, 2, 1, _, _, _, _, _ => exact ⟨_, _, root_02121⟩
  | 0, 2, 2, 0, 0, _, _, _, _, _ => exact ⟨_, _, root_02200⟩
  | 0, 2, 2, 0, 1, _, _, _, _, _ => exact ⟨_, _, root_02201⟩
  | 0, 2, 2, 1, 0, _, _, _, _, _ => exact ⟨_, _, root_02210⟩
  | 0, 2, 2, 1, 1, _, _, _, _, _ => exact ⟨_, _, root_02211⟩
  | 0, 2, 2, 2, 0, _, _, _, _, _ => exact ⟨_, _, root_02220⟩
  | 0, 2, 2, 2, 1, _, _, _, _, _ => exact ⟨_, _, root_02221⟩
  | 1, 0, 0, 0, 0, _, _, _, _, _ => exact ⟨_, _, root_10000⟩
  | 1, 0, 0, 0, 1, _, _, _, _, _ => exact ⟨_, _, root_10001⟩
  | 1, 0, 0, 1, 0, _, _, _, _, _ => exact ⟨_, _, root_10010⟩
  | 1, 0, 0, 1, 1, _, _, _, _, _ => exact ⟨_, _, root_10011⟩
  | 1, 0, 0, 2, 0, _, _, _, _, _ => exact ⟨_, _, root_10020⟩
  | 1, 0, 0, 2, 1, _, _, _, _, _ => exact ⟨_, _, root_10021⟩
  | 1, 0, 1, 0, 0, _, _, _, _, _ => exact ⟨_, _, root_10100⟩
  | 1, 0, 1, 0, 1, _, _, _, _, _ => exact ⟨_, _, root_10101⟩
  | 1, 0, 1, 1, 0, _, _, _, _, _ => exact ⟨_, _, root_10110⟩
  | 1, 0, 1, 1, 1, _, _, _, _, _ => exact ⟨_, _, root_10111⟩
  | 1, 0, 1, 2, 0, _, _, _, _, _ => exact ⟨_, _, root_10120⟩
  | 1, 0, 1, 2, 1, _, _, _, _, _ => exact ⟨_, _, root_10121⟩
  | 1, 0, 2, 0, 0, _, _, _, _, _ => exact ⟨_, _, root_10200⟩
  | 1, 0, 2, 0, 1, _, _, _, _, _ => exact ⟨_, _, root_10201⟩
  | 1, 0, 2, 1, 0, _, _, _, _, _ => exact ⟨_, _, root_10210⟩
  | 1, 0, 2, 1, 1, _, _, _, _, _ => exact ⟨_, _, root_10211⟩
  | 1, 0, 2, 2, 0, _, _, _, _, _ => exact ⟨_, _, root_10220⟩
  | 1, 0, 2, 2, 1, _, _, _, _, _ => exact ⟨_, _, root_10221⟩
  | 1, 1, 0, 0, 0, _, _, _, _, _ => exact ⟨_, _, root_11000⟩
  | 1, 1, 0, 0, 1, _, _, _, _, _ => exact ⟨_, _, root_11001⟩
  | 1, 1, 0, 1, 0, _, _, _, _, _ => exact ⟨_, _, root_11010⟩
  | 1, 1, 0, 1, 1, _, _, _, _, _ => exact ⟨_, _, root_11011⟩
  | 1, 1, 0, 2, 0, _, _, _, _, _ => exact ⟨_, _, root_11020⟩
  | 1, 1, 0, 2, 1, _, _, _, _, _ => exact ⟨_, _, root_11021⟩
  | 1, 1, 1, 0, 0, _, _, _, _, _ => exact ⟨_, _, root_11100⟩
  | 1, 1, 1, 0, 1, _, _, _, _, _ => exact ⟨_, _, root_11101⟩
  | 1, 1, 1, 1, 0, _, _, _, _, _ => exact ⟨_, _, root_11110⟩
  | 1, 1, 1, 1, 1, _, _, _, _, _ => exact ⟨_, _, root_11111⟩
  | 1, 1, 1, 2, 0, _, _, _, _, _ => exact ⟨_, _, root_11120⟩
  | 1, 1, 1, 2, 1, _, _, _, _, _ => exact ⟨_, _, root_11121⟩
  | 1, 1, 2, 0, 0, _, _, _, _, _ => exact ⟨_, _, root_11200⟩
  | 1, 1, 2, 0, 1, _, _, _, _, _ => exact ⟨_, _, root_11201⟩
  | 1, 1, 2, 1, 0, _, _, _, _, _ => exact ⟨_, _, root_11210⟩
  | 1, 1, 2, 1, 1, _, _, _, _, _ => exact ⟨_, _, root_11211⟩
  | 1, 1, 2, 2, 0, _, _, _, _, _ => exact ⟨_, _, root_11220⟩
  | 1, 1, 2, 2, 1, _, _, _, _, _ => exact ⟨_, _, root_11221⟩
  | 1, 2, 0, 0, 0, _, _, _, _, _ => exact ⟨_, _, root_12000⟩
  | 1, 2, 0, 0, 1, _, _, _, _, _ => exact ⟨_, _, root_12001⟩
  | 1, 2, 0, 1, 0, _, _, _, _, _ => exact ⟨_, _, root_12010⟩
  | 1, 2, 0, 1, 1, _, _, _, _, _ => exact ⟨_, _, root_12011⟩
  | 1, 2, 0, 2, 0, _, _, _, _, _ => exact ⟨_, _, root_12020⟩
  | 1, 2, 0, 2, 1, _, _, _, _, _ => exact ⟨_, _, root_12021⟩
  | 1, 2, 1, 0, 0, _, _, _, _, _ => exact ⟨_, _, root_12100⟩
  | 1, 2, 1, 0, 1, _, _, _, _, _ => exact ⟨_, _, root_12101⟩
  | 1, 2, 1, 1, 0, _, _, _, _, _ => exact ⟨_, _, root_12110⟩
  | 1, 2, 1, 1, 1, _, _, _, _, _ => exact ⟨_, _, root_12111⟩
  | 1, 2, 1, 2, 0, _, _, _, _, _ => exact ⟨_, _, root_12120⟩
  | 1, 2, 1, 2, 1, _, _, _, _, _ => exact ⟨_, _, root_12121⟩
  | 1, 2, 2, 0, 0, _, _, _, _, _ => exact ⟨_, _, root_12200⟩
  | 1, 2, 2, 0, 1, _, _, _, _, _ => exact ⟨_, _, root_12201⟩
  | 1, 2, 2, 1, 0, _, _, _, _, _ => exact ⟨_, _, root_12210⟩
  | 1, 2, 2, 1, 1, _, _, _, _, _ => exact ⟨_, _, root_12211⟩
  | 1, 2, 2, 2, 0, _, _, _, _, _ => exact ⟨_, _, root_12220⟩
  | 1, 2, 2, 2, 1, _, _, _, _, _ => exact ⟨_, _, root_12221⟩
  | i + 2, _, _, _, _, hi, _, _, _, _ => exact absurd hi (by omega)
  | _, i + 3, _, _, _, _, hi, _, _, _ => exact absurd hi (by omega)
  | _, _, i + 3, _, _, _, _, hi, _, _ => exact absurd hi (by omega)
  | _, _, _, i + 3, _, _, _, _, hi, _ => exact absurd hi (by omega)
  | _, _, _, _, i + 2, _, _, _, _, hi => exact absurd hi (by omega)

theorem cert : ∀ g0 g1 g2 g3 g4 : ℝ, 0 ≤ g0 → 0 ≤ g1 → 0 ≤ g2 → 0 ≤ g3 → 0 ≤ g4 → (SixW8.cN : ℝ) / SixW8.SA ≤ SixW8.G g0 g1 g2 g3 g4 ∨ g4 < g0 :=
  SixW8.of_check table table_ok bits 64 cover0 cover1 cover2 cover3 cover4 434176 262144 237568 262144 434176
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) cover0_ok cover1_ok cover2_ok cover3_ok cover4_ok (by decide +kernel) run_ok


end Zeta23Ext.Bridge.ThreePoint.SixW8Data

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

/-! ###### the 6-point weighted bound from the checked certificate `SixW8` ###### -/

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

/-- `Fw WW` written out on the gaps: it is the checker's functional `SixW8.G`. -/
theorem Fw_WW (g : Fin (6 - 1) → ℝ) : Fw WW g = SixW8.G (g 0) (g 1) (g 2) (g 3) (g 4) := by
  show (∑ r : Fin 5, bW r * g r) + (∑ i : Fin 6, ∑ j : Fin 6, if (i : ℕ) < (j : ℕ) then aW i j * wfun (ptsN 6 g j - ptsN 6 g i) else 0) = _
  unfold SixW8.G ptsN
  simp only [sumQ, Fin.sum_univ_six, Fin.sum_univ_five, Fin.isValue, aW_0_0, aW_0_1, aW_0_2, aW_0_3, aW_0_4, aW_0_5, aW_1_0, aW_1_1, aW_1_2, aW_1_3, aW_1_4, aW_1_5, aW_2_0, aW_2_1, aW_2_2, aW_2_3, aW_2_4, aW_2_5, aW_3_0, aW_3_1, aW_3_2, aW_3_3, aW_3_4, aW_3_5, aW_4_0, aW_4_1, aW_4_2, aW_4_3, aW_4_4, aW_4_5, aW_5_0, aW_5_1, aW_5_2, aW_5_3, aW_5_4, aW_5_5, bW_0, bW_1, bW_2, bW_3, bW_4]
  norm_num [SixW8.SA]
  try ring

theorem G_rev (x0 x1 x2 x3 x4 : ℝ) : SixW8.G x4 x3 x2 x1 x0 = SixW8.G x0 x1 x2 x3 x4 := by
  unfold SixW8.G; ring_nf

/-- the half-space certificate, completed by reflection (the weights are symmetric) -/
theorem cert_full : ∀ x0 x1 x2 x3 x4 : ℝ, 0 ≤ x0 → 0 ≤ x1 → 0 ≤ x2 → 0 ≤ x3 → 0 ≤ x4 → (SixW8.cN : ℝ) / SixW8.SA ≤ SixW8.G x0 x1 x2 x3 x4 := by
  intro x0 x1 x2 x3 x4 h0 h1 h2 h3 h4
  rcases lt_or_ge x4 x0 with hlt | hle
  · rcases SixW8Data.cert x4 x3 x2 x1 x0 h4 h3 h2 h1 h0 with h | h
    · rw [← G_rev]; exact h
    · exact absurd h (not_lt.mpr hlt.le)
  · rcases SixW8Data.cert x0 x1 x2 x3 x4 h0 h1 h2 h3 h4 with h | h
    · exact h
    · exact absurd h (not_lt.mpr hle)

/-- the certificate hypothesis of `n_point_bound_w'` at `n = 6` -/
theorem cert_WW : ∀ g : Fin (6 - 1) → ℝ, (∀ i, 0 ≤ g i) → (329625 : ℝ) / 100000000 ≤ Fw WW g := by
  intro g hg
  rw [Fw_WW]
  have h := cert_full (g 0) (g 1) (g 2) (g 3) (g 4) (hg 0) (hg 1) (hg 2) (hg 3) (hg 4)
  simp only [SixW8.cN, SixW8.SA] at h
  push_cast at h
  exact h

/-- `Phi_w' 6 c 308 B` as an exact rational in `HD 1` -/
theorem Phi_WW : Phi_w' 6 ((329625 : ℝ) / 100000000) 308 ((179997 : ℝ) / 100000000)
    = (30800000000 * HD 1 - 54539091) / 30700123625 := by
  unfold Phi_w'
  push_cast
  rw [div_eq_div_iff (by norm_num) (by norm_num)]
  ring

/-- **The 6-point weighted bound, unconditional.** -/
theorem bound_WW :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      ((30800000000 * HD 1 - 54539091) / 30700123625 - ε) * (Zeta23.Ncount T (2 * T) : ℝ) ≤ Zeta23.N0simple T (2 * T) := by
  rw [← Phi_WW, ← WW_B]
  exact n_point_bound_w' 6 ((329625 : ℝ) / 100000000) 308 WW (by norm_num) (by norm_num) WW_adm
    (by norm_num : (0 : ℝ) < (24896 : ℝ) / 100000000) WW_bmin (by norm_num) cert_WW (by norm_num)

/-- The candidate rational sits below the proved constant. -/
theorem candidateKappa_le : candidateKappa ≤ (30800000000 * HD 1 - 54539091) / 30700123625 := by
  unfold candidateKappa
  rw [le_div_iff₀ (by norm_num : (0:ℝ) < 30700123625)]
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
      ≤ ((30800000000 * HD 1 - 54539091) / 30700123625 - ε) * (Zeta23.Ncount T (2 * T) : ℝ) :=
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
