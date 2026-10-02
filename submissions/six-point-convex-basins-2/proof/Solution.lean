/-
Unconditional critical-line proportion via the weighted six-point refinement of the pinned Zeta23
Theorem D at c within 10⁻⁴ of the weighted functional's minimum.

Built on attempt-009 (Samuel Lavery, Apache-2.0): its single-file port of the Zeta Lab bridge, its
integer cell pipeline, pyramid oracle, six-point leaf test, walk and orthant theorem, and its weights,
used here unchanged except that a walk leaf may also lie in a certified convex basin. Pyramid table
originally from five-point-pyramid-2 (typh). The convex-basin layer (`Riemann.Deriv`, `Riemann.Encl`,
`Riemann.BasinC`, `Riemann.Basin6`) is by typh: `w` differentiated twice from the
closed form of `kfun`, rational enclosures of `w'` and `w''` on cells, a PSD check by exact `LDLᵀ`,
and the tangent plane at each near-minimal local minimum.
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



/-! ###### convex-basin layer ###### -/

section

/-!
# Derivatives of `wfun` and a second-order lower bound

Away from the poles of the closed form (`1 − 2(πx)² ≠ 0`), `kfun x = N(πx) / D(πx)` with
`N θ = cos θ − 2γ θ sin θ` and `D θ = 1 − 2θ²`. This file differentiates that twice and proves
`w s ≥ w t + w'(t)(s − t) + l(s − t)²/2` on intervals where `w'' ≥ l`.
-/

noncomputable section

namespace Riemann.Deriv

open Zeta23Ext.Bridge Zeta23Ext.Bridge.ThreePoint

def Nf (θ : ℝ) : ℝ := Real.cos θ - 2 * gam * θ * Real.sin θ
def N1f (θ : ℝ) : ℝ := -(1 + 2 * gam) * Real.sin θ - 2 * gam * θ * Real.cos θ
def N2f (θ : ℝ) : ℝ := -(1 + 4 * gam) * Real.cos θ + 2 * gam * θ * Real.sin θ
def Df (θ : ℝ) : ℝ := 1 - 2 * θ ^ 2

/-- `d/dθ (N/D)` and `d²/dθ² (N/D)`. -/
def K1f (θ : ℝ) : ℝ := N1f θ / Df θ + 4 * θ * Nf θ / Df θ ^ 2
def K2f (θ : ℝ) : ℝ :=
  N2f θ / Df θ + 8 * θ * N1f θ / Df θ ^ 2 + 4 * Nf θ / Df θ ^ 2 + 32 * θ ^ 2 * Nf θ / Df θ ^ 3

lemma hasDerivAt_Nf (θ : ℝ) : HasDerivAt Nf (N1f θ) θ := by
  unfold Nf
  refine ((Real.hasDerivAt_cos θ).sub
    (((hasDerivAt_id' θ).const_mul (2 * gam)).mul (Real.hasDerivAt_sin θ))).congr_deriv ?_
  simp only [N1f]; ring

lemma hasDerivAt_N1f (θ : ℝ) : HasDerivAt N1f (N2f θ) θ := by
  unfold N1f
  refine (((Real.hasDerivAt_sin θ).const_mul (-(1 + 2 * gam))).sub
    (((hasDerivAt_id' θ).const_mul (2 * gam)).mul (Real.hasDerivAt_cos θ))).congr_deriv ?_
  simp only [N2f]; ring

lemma hasDerivAt_Df (θ : ℝ) : HasDerivAt Df (-4 * θ) θ := by
  unfold Df
  refine (((hasDerivAt_pow 2 θ).const_mul 2).const_sub 1).congr_deriv ?_
  simp; ring

lemma hasDerivAt_Kf {θ : ℝ} (hD : Df θ ≠ 0) : HasDerivAt (fun t => Nf t / Df t) (K1f θ) θ := by
  refine ((hasDerivAt_Nf θ).div (hasDerivAt_Df θ) hD).congr_deriv ?_
  unfold K1f
  field_simp
  ring

lemma hasDerivAt_K1f {θ : ℝ} (hD : Df θ ≠ 0) : HasDerivAt K1f (K2f θ) θ := by
  have hD2 : Df θ ^ 2 ≠ 0 := pow_ne_zero 2 hD
  unfold K1f
  refine (((hasDerivAt_N1f θ).div (hasDerivAt_Df θ) hD).add
    ((((hasDerivAt_id' θ).const_mul 4).mul (hasDerivAt_Nf θ)).div
      ((hasDerivAt_Df θ).pow 2) hD2)).congr_deriv ?_
  simp only [Pi.pow_apply, Pi.mul_apply]
  unfold K2f
  field_simp
  ring

/-- The closed form agrees with `kfun` near every non-pole. -/
lemma kfun_eventually {x : ℝ} (hD : Df (Real.pi * x) ≠ 0) :
    (fun y => Nf (Real.pi * y) / Df (Real.pi * y)) =ᶠ[nhds x] kfun := by
  have hc : Continuous fun y => Df (Real.pi * y) := by unfold Df; fun_prop
  filter_upwards [hc.continuousAt.eventually_ne hD] with y hy
  rw [kfun_closed y (by simpa [Df] using hy)]
  simp [Nf, Df]

def k1 (x : ℝ) : ℝ := Real.pi * K1f (Real.pi * x)
def k2 (x : ℝ) : ℝ := Real.pi ^ 2 * K2f (Real.pi * x)

lemma hasDerivAt_kfun {x : ℝ} (hD : Df (Real.pi * x) ≠ 0) : HasDerivAt kfun (k1 x) x := by
  have h := (hasDerivAt_Kf hD).comp x ((hasDerivAt_id' x).const_mul Real.pi)
  have h' : HasDerivAt (fun y => Nf (Real.pi * y) / Df (Real.pi * y)) (k1 x) x :=
    h.congr_deriv (by unfold k1; ring)
  exact h'.congr_of_eventuallyEq (kfun_eventually hD).symm

lemma hasDerivAt_k1 {x : ℝ} (hD : Df (Real.pi * x) ≠ 0) : HasDerivAt k1 (k2 x) x := by
  have h := ((hasDerivAt_K1f hD).comp x ((hasDerivAt_id' x).const_mul Real.pi)).const_mul Real.pi
  unfold k1
  exact h.congr_deriv (by unfold k2; ring)

def w1 (x : ℝ) : ℝ := 2 * kfun x * k1 x
def w2 (x : ℝ) : ℝ := 2 * (k1 x * k1 x + kfun x * k2 x)

lemma hasDerivAt_wfun {x : ℝ} (hD : Df (Real.pi * x) ≠ 0) : HasDerivAt wfun (w1 x) x := by
  unfold wfun
  exact ((hasDerivAt_kfun hD).pow 2).congr_deriv (by unfold w1; simp)

lemma hasDerivAt_w1 {x : ℝ} (hD : Df (Real.pi * x) ≠ 0) : HasDerivAt w1 (w2 x) x := by
  unfold w1
  exact (((hasDerivAt_kfun hD).const_mul 2).mul (hasDerivAt_k1 hD)).congr_deriv (by unfold w2; ring)

/-- No poles from `1/2` on: `2(πx)² ≥ π²/2 > 1`. -/
lemma Df_ne {x : ℝ} (hx : 1 / 2 ≤ x) : Df (Real.pi * x) ≠ 0 := by
  have hpi := Real.pi_gt_three
  have : (3 / 2 : ℝ) ≤ Real.pi * x := by nlinarith
  unfold Df; nlinarith

/-- Second-order lower bound from a lower bound on the second derivative. -/
theorem taylor2_lower {f f1 f2 : ℝ → ℝ} {a b l : ℝ}
    (hf : ∀ x ∈ Set.Icc a b, HasDerivAt f (f1 x) x)
    (hf1 : ∀ x ∈ Set.Icc a b, HasDerivAt f1 (f2 x) x)
    (hl : ∀ x ∈ Set.Icc a b, l ≤ f2 x) {s t : ℝ} (hs : s ∈ Set.Icc a b) (ht : t ∈ Set.Icc a b) :
    f t + f1 t * (s - t) + l / 2 * (s - t) ^ 2 ≤ f s := by
  set g : ℝ → ℝ := fun u => f u - f t - f1 t * (u - t) - l / 2 * (u - t) ^ 2 with hg
  set g1 : ℝ → ℝ := fun u => f1 u - f1 t - l * (u - t) with hg1
  have hgd : ∀ u ∈ Set.Icc a b, HasDerivAt g (g1 u) u := by
    intro u hu
    exact ((((hf u hu).sub_const (f t)).sub
      (((hasDerivAt_id' u).sub_const t).const_mul (f1 t))).sub
      ((((hasDerivAt_id' u).sub_const t).pow 2).const_mul (l / 2))).congr_deriv (by simp [hg1]; ring)
  have hg1d : ∀ u ∈ Set.Icc a b, HasDerivAt g1 (f2 u - l) u := by
    intro u hu
    exact (((hf1 u hu).sub_const (f1 t)).sub
      (((hasDerivAt_id' u).sub_const t).const_mul l)).congr_deriv (by simp)
  have hconv : Convex ℝ (Set.Icc a b) := convex_Icc a b
  have hint : interior (Set.Icc a b) ⊆ Set.Icc a b := interior_subset
  -- `g1` is monotone, vanishing at `t`
  have hmono1 : MonotoneOn g1 (Set.Icc a b) :=
    monotoneOn_of_deriv_nonneg hconv
      (fun u hu => (hg1d u hu).continuousAt.continuousWithinAt)
      (fun u hu => (hg1d u (hint hu)).differentiableAt.differentiableWithinAt)
      (fun u hu => by rw [(hg1d u (hint hu)).deriv]; linarith [hl u (hint hu)])
  have hg1t : g1 t = 0 := by simp [hg1]
  have hgt : g t = 0 := by simp [hg]
  -- `g` decreases up to `t` and increases after it
  rcases le_total t s with hts | hst
  · have hD : Convex ℝ (Set.Icc t b) := convex_Icc t b
    have hsub : Set.Icc t b ⊆ Set.Icc a b := Set.Icc_subset_Icc ht.1 le_rfl
    have hint2 : interior (Set.Icc t b) ⊆ Set.Icc t b := interior_subset
    have hm : MonotoneOn g (Set.Icc t b) :=
      monotoneOn_of_deriv_nonneg hD
        (fun u hu => (hgd u (hsub hu)).continuousAt.continuousWithinAt)
        (fun u hu => (hgd u (hsub (hint2 hu))).differentiableAt.differentiableWithinAt)
        (fun u hu => by
          rw [(hgd u (hsub (hint2 hu))).deriv, ← hg1t]
          exact hmono1 ht (hsub (hint2 hu)) (hint2 hu).1)
    have := hm ⟨le_rfl, ht.2⟩ ⟨hts, hs.2⟩ hts
    rw [hgt] at this
    simp only [hg] at this
    linarith
  · have hD : Convex ℝ (Set.Icc a t) := convex_Icc a t
    have hsub : Set.Icc a t ⊆ Set.Icc a b := Set.Icc_subset_Icc le_rfl ht.2
    have hint2 : interior (Set.Icc a t) ⊆ Set.Icc a t := interior_subset
    have hm : AntitoneOn g (Set.Icc a t) :=
      antitoneOn_of_deriv_nonpos hD
        (fun u hu => (hgd u (hsub hu)).continuousAt.continuousWithinAt)
        (fun u hu => (hgd u (hsub (hint2 hu))).differentiableAt.differentiableWithinAt)
        (fun u hu => by
          rw [(hgd u (hsub (hint2 hu))).deriv, ← hg1t]
          exact hmono1 (hsub (hint2 hu)) ht (hint2 hu).2)
    have := hm ⟨hs.1, hst⟩ ⟨ht.1, le_rfl⟩ hst
    rw [hgt] at this
    simp only [hg] at this
    linarith

/-- The bound for `wfun` on `[a, b] ⊆ [1/2, ∞)`. -/
theorem wfun_taylor2 {a b l : ℝ} (ha : 1 / 2 ≤ a) (hl : ∀ x ∈ Set.Icc a b, l ≤ w2 x)
    {s t : ℝ} (hs : s ∈ Set.Icc a b) (ht : t ∈ Set.Icc a b) :
    wfun t + w1 t * (s - t) + l / 2 * (s - t) ^ 2 ≤ wfun s :=
  taylor2_lower (fun x hx => hasDerivAt_wfun (Df_ne (ha.trans hx.1)))
    (fun x hx => hasDerivAt_w1 (Df_ne (ha.trans hx.1))) hl hs ht

end Riemann.Deriv

end

section

/-!
# Enclosures of `w`, `w'` and `w''` on a cell

Rational interval arithmetic, rounded outward to `10⁻¹²` after products, over the record's
cos/sin enclosures of a `Cell` (anchor `k/2`, side, Taylor bounds). `Encl.sound` gives
`kfun x ∈ K`, `w1 x ∈ W1` and `w2 x ∈ W2` for every `x` in a cell passing `okD`.
-/

noncomputable section

namespace Riemann.Encl

open Zeta23Ext.Bridge Zeta23Ext.Bridge.ThreePoint Riemann.Deriv

abbrev IQ := ℚ × ℚ

def Mem (I : IQ) (x : ℝ) : Prop := (I.1 : ℝ) ≤ x ∧ x ≤ I.2

def cst (q : ℚ) : IQ := (q, q)
def ineg (I : IQ) : IQ := (-I.2, -I.1)
def iscale (q : ℚ) (I : IQ) : IQ := if 0 ≤ q then (q * I.1, q * I.2) else (q * I.2, q * I.1)
def imul (I J : IQ) : IQ :=
  (floorD (min (min (I.1 * J.1) (I.1 * J.2)) (min (I.2 * J.1) (I.2 * J.2))),
    ceilD (max (max (I.1 * J.1) (I.1 * J.2)) (max (I.2 * J.1) (I.2 * J.2))))
/-- Reciprocal of an interval of negative numbers. -/
def iinvN (J : IQ) : IQ := (floorD (1 / J.2), ceilD (1 / J.1))

lemma mem_congr {I : IQ} {x y : ℝ} (h : Mem I x) (e : x = y) : Mem I y := e ▸ h

lemma mem_cst (q : ℚ) : Mem (cst q) q := ⟨le_rfl, le_rfl⟩

lemma mem_ineg {I : IQ} {x : ℝ} (h : Mem I x) : Mem (ineg I) (-x) := by
  unfold ineg Mem; push_cast; exact ⟨by linarith [h.2], by linarith [h.1]⟩

lemma mem_iadd {I J : IQ} {x y : ℝ} (hx : Mem I x) (hy : Mem J y) : Mem (iadd I J) (x + y) :=
  iadd_sound I J hx hy

lemma mem_isub {I J : IQ} {x y : ℝ} (hx : Mem I x) (hy : Mem J y) : Mem (isub I J) (x - y) :=
  isub_sound I J hx hy

lemma mem_iscale (q : ℚ) {I : IQ} {x : ℝ} (h : Mem I x) : Mem (iscale q I) (q * x) := by
  unfold iscale Mem
  split_ifs with hq
  · have : (0 : ℝ) ≤ q := by exact_mod_cast hq
    push_cast
    exact ⟨mul_le_mul_of_nonneg_left h.1 this, mul_le_mul_of_nonneg_left h.2 this⟩
  · have : (q : ℝ) ≤ 0 := by exact_mod_cast (not_le.mp hq).le
    push_cast
    exact ⟨mul_le_mul_of_nonpos_left h.2 this, mul_le_mul_of_nonpos_left h.1 this⟩

lemma mul_between {x a b y : ℝ} (h1 : a ≤ x) (h2 : x ≤ b) :
    min (a * y) (b * y) ≤ x * y ∧ x * y ≤ max (a * y) (b * y) := by
  rcases le_total 0 y with hy | hy
  · exact ⟨(min_le_left _ _).trans (mul_le_mul_of_nonneg_right h1 hy),
      (mul_le_mul_of_nonneg_right h2 hy).trans (le_max_right _ _)⟩
  · exact ⟨(min_le_right _ _).trans (mul_le_mul_of_nonpos_right h2 hy),
      (mul_le_mul_of_nonpos_right h1 hy).trans (le_max_left _ _)⟩

lemma mul_between' {y c d a : ℝ} (h1 : c ≤ y) (h2 : y ≤ d) :
    min (a * c) (a * d) ≤ a * y ∧ a * y ≤ max (a * c) (a * d) := by
  obtain ⟨h3, h4⟩ := mul_between (y := a) h1 h2
  rw [mul_comm c, mul_comm d, mul_comm y] at *
  exact ⟨h3, h4⟩

lemma mem_imul {I J : IQ} {x y : ℝ} (hx : Mem I x) (hy : Mem J y) : Mem (imul I J) (x * y) := by
  obtain ⟨hx1, hx2⟩ := mul_between (y := y) hx.1 hx.2
  obtain ⟨ha1, ha2⟩ := mul_between' (a := (I.1 : ℝ)) hy.1 hy.2
  obtain ⟨hb1, hb2⟩ := mul_between' (a := (I.2 : ℝ)) hy.1 hy.2
  constructor
  · refine (floorD_le' _).trans ?_
    rw [Rat.cast_min, Rat.cast_min, Rat.cast_min, Rat.cast_mul, Rat.cast_mul, Rat.cast_mul,
      Rat.cast_mul]
    exact (min_le_min ha1 hb1).trans hx1
  · refine le_trans ?_ (le_ceilD' _)
    rw [Rat.cast_max, Rat.cast_max, Rat.cast_max, Rat.cast_mul, Rat.cast_mul, Rat.cast_mul,
      Rat.cast_mul]
    exact hx2.trans (max_le_max ha2 hb2)

lemma mem_iinvN {J : IQ} {y : ℝ} (hy : Mem J y) (hneg : J.2 < 0) : Mem (iinvN J) (1 / y) := by
  have h2 : (J.2 : ℝ) < 0 := by exact_mod_cast hneg
  have hy0 : y < 0 := hy.2.trans_lt h2
  have hJ1 : (J.1 : ℝ) < 0 := hy.1.trans_lt hy0
  constructor
  · refine (floorD_le' _).trans ?_
    push_cast
    exact (one_div_le_one_div_of_neg h2 hy0).mpr hy.2
  · refine le_trans ?_ (le_ceilD' _)
    push_cast
    exact (one_div_le_one_div_of_neg hy0 hJ1).mpr hy.1

/-! ### Cells -/

/-- The record's cell conditions (without its bound `W`), from `1/2` on. -/
def okD (c : Cell) : Bool :=
  decide (1 / 2 ≤ c.L) && decide (c.L ≤ c.U) && decide (0 ≤ c.rlo) && decide (c.TU ≤ 1)
    && decide (0 ≤ c.TL) && decide (0 ≤ c.BL)

/-- `cos (πx)`, `sin (πx)` and `πx` on a cell, as in `cell_sound`. -/
theorem cell_cs (c : Cell) (h : okD c = true) (x : ℝ) (hx1 : (c.L : ℝ) ≤ x) (hx2 : x ≤ c.U) :
    Mem c.CX (Real.cos (Real.pi * x)) ∧ Mem c.SX (Real.sin (Real.pi * x))
      ∧ Mem (c.BL, c.BU) (Real.pi * x) := by
  simp only [okD, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨hL, hLU⟩, hr0⟩, hTU⟩, hTL0q⟩, hBL0q⟩ := h
  have h0 : (0 : ℚ) ≤ c.L := le_trans (by norm_num) hL
  have h0' : (0:ℝ) ≤ c.L := Rat.cast_nonneg.mpr h0
  have hr0' : (0:ℝ) ≤ c.rlo := Rat.cast_nonneg.mpr hr0
  have hTL0 : (0:ℝ) ≤ c.TL := Rat.cast_nonneg.mpr hTL0q
  have hBL0 : (0:ℝ) ≤ c.BL := Rat.cast_nonneg.mpr hBL0q
  have hTU' : (c.TU : ℝ) ≤ 1 := by
    have := (Rat.cast_le (K := ℝ)).mpr hTU; simpa using this
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
  have hcs := cos_sin_half c.k
  have eA : (c.A : ℝ) = (c.k : ℝ) / 2 := by simp [Cell.A]
  refine ⟨?_, ?_, ?_⟩
  · cases hsd : c.side
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
  · cases hsd : c.side
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
  · constructor
    · have h1 : (c.BL : ℝ) ≤ ((piLoQ * c.L : ℚ) : ℝ) := floorD_le' _
      rw [Rat.cast_mul] at h1
      exact h1.trans (mul_ge_of piLoQ_le hx1 piLoQ_nonneg h0' le_rfl)
    · have h1 : ((piHiQ * c.U : ℚ) : ℝ) ≤ (c.BU : ℝ) := le_ceilD' _
      rw [Rat.cast_mul] at h1
      exact (mul_le_of piHiQ_ge hx2 Real.pi_pos.le (h0'.trans hx1) le_rfl).trans h1

/-! ### The enclosures, from the cell's `cos`, `sin` and `θ = πx` -/

def Gq : IQ := (gamLoQ, gamHiQ)
def Pq : IQ := (piLoQ, piHiQ)

/-- `(K, W1, W2)` enclosing `kfun`, `w1`, `w2` from enclosures `C, S, T` of `cos θ, sin θ, θ`. -/
def enc (C S T : IQ) : IQ × IQ × IQ :=
  let G2T := iscale 2 (imul Gq T)
  let N := isub C (imul G2T S)
  let N1 := isub (imul (ineg (iadd (cst 1) (iscale 2 Gq))) S) (imul G2T C)
  let N2 := iadd (imul (ineg (iadd (cst 1) (iscale 4 Gq))) C) (imul G2T S)
  let T2 := imul T T
  let iD := iinvN (isub (cst 1) (iscale 2 T2))
  let iD2 := imul iD iD
  let K := imul N iD
  let K1 := iadd (imul N1 iD) (imul (iscale 4 (imul T N)) iD2)
  let K2 := iadd (iadd (iadd (imul N2 iD) (imul (iscale 8 (imul T N1)) iD2))
    (imul (iscale 4 N) iD2)) (imul (iscale 32 (imul T2 N)) (imul iD2 iD))
  (K, iscale 2 (imul Pq (imul K K1)), iscale 2 (imul (imul Pq Pq) (iadd (imul K1 K1) (imul K K2))))

/-- The denominator enclosure is negative. -/
def negD (T : IQ) : Bool := decide ((isub (cst 1) (iscale 2 (imul T T))).2 < 0)

theorem enc_sound {C S T : IQ} {x : ℝ} (hC : Mem C (Real.cos (Real.pi * x)))
    (hS : Mem S (Real.sin (Real.pi * x))) (hT : Mem T (Real.pi * x)) (hneg : negD T = true) :
    Mem (enc C S T).1 (kfun x) ∧ Mem (enc C S T).2.1 (w1 x) ∧ Mem (enc C S T).2.2 (w2 x) := by
  simp only [negD, decide_eq_true_eq] at hneg
  set θ := Real.pi * x with hθ
  have hG : Mem Gq gam := ⟨gamLoQ_le, gamHiQ_ge⟩
  have hP : Mem Pq Real.pi := ⟨piLoQ_le, piHiQ_ge⟩
  have hG2T := mem_iscale 2 (mem_imul hG hT)
  have hN : Mem (isub C (imul (iscale 2 (imul Gq T)) S)) (Nf θ) := by
    have := mem_isub hC (mem_imul hG2T hS)
    refine mem_congr this ?_; unfold Nf; push_cast; ring
  have hN1 : Mem (isub (imul (ineg (iadd (cst 1) (iscale 2 Gq))) S) (imul (iscale 2 (imul Gq T)) C))
      (N1f θ) := by
    have := mem_isub (mem_imul (mem_ineg (mem_iadd (mem_cst 1) (mem_iscale 2 hG))) hS)
      (mem_imul hG2T hC)
    refine mem_congr this ?_; unfold N1f; push_cast; ring
  have hN2 : Mem (iadd (imul (ineg (iadd (cst 1) (iscale 4 Gq))) C) (imul (iscale 2 (imul Gq T)) S))
      (N2f θ) := by
    have := mem_iadd (mem_imul (mem_ineg (mem_iadd (mem_cst 1) (mem_iscale 4 hG))) hC)
      (mem_imul hG2T hS)
    refine mem_congr this ?_; unfold N2f; push_cast; ring
  have hT2 := mem_imul hT hT
  have hDm : Mem (isub (cst 1) (iscale 2 (imul T T))) (Df θ) := by
    have := mem_isub (mem_cst 1) (mem_iscale 2 hT2)
    refine mem_congr this ?_; unfold Df; push_cast; ring
  have hiD := mem_iinvN hDm hneg
  have hD0 : Df θ ≠ 0 := by
    have : Df θ < 0 := hDm.2.trans_lt (by exact_mod_cast hneg)
    exact this.ne
  have hiD2 := mem_imul hiD hiD
  have hK := mem_imul hN hiD
  have hK1 := mem_iadd (mem_imul hN1 hiD) (mem_imul (mem_iscale 4 (mem_imul hT hN)) hiD2)
  have hK2 := mem_iadd (mem_iadd (mem_iadd (mem_imul hN2 hiD)
    (mem_imul (mem_iscale 8 (mem_imul hT hN1)) hiD2)) (mem_imul (mem_iscale 4 hN) hiD2))
    (mem_imul (mem_iscale 32 (mem_imul hT2 hN)) (mem_imul hiD2 hiD))
  have ek : kfun x = Nf θ * (1 / Df θ) := by
    rw [kfun_closed x (by simpa [Df, hθ] using hD0)]; simp [Nf, Df, hθ]; ring
  have ek1 : k1 x = Real.pi * (N1f θ * (1 / Df θ) + 4 * (θ * Nf θ) * (1 / Df θ * (1 / Df θ))) := by
    unfold k1 K1f; rw [← hθ]; field_simp
  have ek2 : k2 x = Real.pi ^ 2 * (N2f θ * (1 / Df θ) + 8 * (θ * N1f θ) * (1 / Df θ * (1 / Df θ))
      + 4 * Nf θ * (1 / Df θ * (1 / Df θ)) + 32 * (θ * θ * Nf θ) * (1 / Df θ * (1 / Df θ) * (1 / Df θ))) := by
    unfold k2 K2f; rw [← hθ]; field_simp
  refine ⟨?_, ?_, ?_⟩
  · rw [ek]; exact hK
  · refine mem_congr (mem_iscale 2 (mem_imul hP (mem_imul hK hK1))) ?_
    unfold w1; rw [ek, ek1]; push_cast; ring
  · refine mem_congr (mem_iscale 2 (mem_imul (mem_imul hP hP)
      (mem_iadd (mem_imul hK1 hK1) (mem_imul hK hK2)))) ?_
    unfold w2; rw [ek, ek1, ek2]; push_cast; ring

/-- Enclosures on a cell. -/
def cellEnc (c : Cell) : IQ × IQ × IQ := enc c.CX c.SX (c.BL, c.BU)

theorem cellEnc_sound (c : Cell) (h : okD c = true) (hn : negD (c.BL, c.BU) = true) (x : ℝ)
    (hx1 : (c.L : ℝ) ≤ x) (hx2 : x ≤ c.U) :
    Mem (cellEnc c).1 (kfun x) ∧ Mem (cellEnc c).2.1 (w1 x) ∧ Mem (cellEnc c).2.2 (w2 x) := by
  obtain ⟨hC, hS, hT⟩ := cell_cs c h x hx1 hx2
  exact enc_sound hC hS hT hn

end Riemann.Encl

end

section

/-!
# Convex-basin certificates: dimension-free parts

Grid cells of `2⁻³²`, chains of cells carrying `l ≤ w''`, the second-order bound of one pair at an
expansion point, and positive semidefinite quadratic forms by `LDLᵀ`.
-/

noncomputable section

namespace Riemann.BasinC

open Zeta23Ext.Bridge Zeta23Ext.Bridge.ThreePoint Riemann.Deriv Riemann.Encl

def Dq : ℕ := 4294967296

/-- Grid coordinates over `2³²`. -/
def toRq (n : ℕ) : ℝ := (n : ℝ) / Dq

lemma Dq_pos : (0 : ℝ) < Dq := by norm_num [Dq]

lemma toRq_le_toRq {a b : ℕ} : toRq a ≤ toRq b ↔ a ≤ b := by
  unfold toRq
  rw [div_le_div_iff_of_pos_right Dq_pos]
  exact Nat.cast_le

lemma toRq_add (a b : ℕ) : toRq (a + b) = toRq a + toRq b := by
  unfold toRq; push_cast; ring

/-! ### Grid cells and chains -/

/-- The cell `[a, b]` (grid units), anchored at the half-integer nearest its midpoint. -/
def segCell (a b : ℕ) : Cell :=
  ⟨(a : ℚ) / 4294967296, (b : ℚ) / 4294967296, (a + b + 2147483648) / 4294967296,
    decide ((a + b + 2147483648) / 4294967296 * 4294967296 ≤ 2 * a), 0⟩

lemma segCell_L (a b : ℕ) : (((segCell a b).L : ℚ) : ℝ) = toRq a := by
  simp [segCell, toRq, Dq]

lemma segCell_U (a b : ℕ) : (((segCell a b).U : ℚ) : ℝ) = toRq b := by
  simp [segCell, toRq, Dq]

def cellOk (c : Cell) : Bool := okD c && negD (c.BL, c.BU)

/-- Every cell of the chain `a = x₀ < x₁ < … ` has `l ≤ w''`. -/
def chainGe (l : ℚ) : ℕ → List ℕ → Bool
  | _, [] => true
  | a, b :: rest => cellOk (segCell a b) && decide (l ≤ (cellEnc (segCell a b)).2.2.1)
      && chainGe l b rest

def chainLast : ℕ → List ℕ → ℕ
  | a, [] => a
  | _, b :: rest => chainLast b rest

theorem chainGe_sound (l : ℚ) :
    ∀ (rest : List ℕ) (a b : ℕ), chainGe l a (b :: rest) = true →
      ∀ x : ℝ, toRq a ≤ x → x ≤ toRq (chainLast b rest) → (l : ℝ) ≤ w2 x := by
  intro rest
  induction rest with
  | nil =>
    intro a b h x h1 h2
    simp only [chainGe, Bool.and_eq_true, decide_eq_true_eq] at h
    simp only [cellOk, Bool.and_eq_true] at h
    obtain ⟨⟨⟨hok, hneg⟩, hl⟩, -⟩ := h
    have hx1 : (((segCell a b).L : ℚ) : ℝ) ≤ x := by rw [segCell_L]; exact h1
    have hx2 : x ≤ (((segCell a b).U : ℚ) : ℝ) := by rw [segCell_U]; simpa [chainLast] using h2
    exact (Rat.cast_le.mpr hl).trans (cellEnc_sound _ hok hneg x hx1 hx2).2.2.1
  | cons c rest ih =>
    intro a b h x h1 h2
    rw [chainGe, Bool.and_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨hc, hl⟩, hrest⟩ := h
    rw [cellOk, Bool.and_eq_true] at hc
    obtain ⟨hok, hneg⟩ := hc
    rcases le_total x (toRq b) with hxb | hxb
    · have hx1 : (((segCell a b).L : ℚ) : ℝ) ≤ x := by rw [segCell_L]; exact h1
      have hx2 : x ≤ (((segCell a b).U : ℚ) : ℝ) := by rw [segCell_U]; exact hxb
      exact (Rat.cast_le.mpr hl).trans (cellEnc_sound _ hok hneg x hx1 hx2).2.2.1
    · exact ih b c hrest x hxb (by simpa [chainLast] using h2)

/-! ### One pair: the second-order bound at an expansion point -/

def wloK (K : IQ) : ℚ := if 0 ≤ K.1 then K.1 * K.1 else if K.2 ≤ 0 then K.2 * K.2 else 0

lemma wloK_le {K : IQ} {k : ℝ} (h : Mem K k) : (wloK K : ℝ) ≤ k ^ 2 := by
  unfold wloK
  split_ifs with h1 h2
  · have : (0 : ℝ) ≤ K.1 := by exact_mod_cast h1
    push_cast; nlinarith [h.1]
  · have : (K.2 : ℝ) ≤ 0 := by exact_mod_cast h2
    push_cast; nlinarith [h.2]
  · push_cast; positivity

def ptCell (T : ℕ) : Cell := segCell T T

def encK (T : ℕ) : IQ := (cellEnc (ptCell T)).1
def encW1 (T : ℕ) : IQ := (cellEnc (ptCell T)).2.1

/-- A pair's data: the chain `a, b :: rest` with `l ≤ w''` on it. -/
structure Chain where
  (a b : ℕ) (rest : List ℕ) (l : ℚ)

def Chain.last (c : Chain) : ℕ := chainLast c.b c.rest

/-- The chain is valid, covers `[lo, hi]` and the expansion point `T`, from `1/2` on. -/
def pairOk (c : Chain) (lo hi T : ℕ) : Bool :=
  chainGe c.l c.a (c.b :: c.rest) && Nat.ble 2147483648 c.a && Nat.ble c.a lo && Nat.ble hi c.last
    && Nat.ble c.a T && Nat.ble T c.last && cellOk (ptCell T)

theorem pair_sound {c : Chain} {lo hi T : ℕ} (h : pairOk c lo hi T = true) :
    Mem (encW1 T) (w1 (toRq T)) ∧
      ∀ s : ℝ, toRq lo ≤ s → s ≤ toRq hi →
        (wloK (encK T) : ℝ) + w1 (toRq T) * (s - toRq T)
          + (c.l : ℝ) / 2 * (s - toRq T) ^ 2 ≤ wfun s := by
  simp only [pairOk, Bool.and_eq_true, Nat.ble_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨hch, ha⟩, halo⟩, hhi⟩, haT⟩, hTl⟩, hpt⟩ := h
  rw [cellOk, Bool.and_eq_true] at hpt
  have hT1 : (((ptCell T).L : ℚ) : ℝ) ≤ toRq T := by rw [ptCell, segCell_L]
  have hT2 : toRq T ≤ (((ptCell T).U : ℚ) : ℝ) := by rw [ptCell, segCell_U]
  have henc := cellEnc_sound _ hpt.1 hpt.2 (toRq T) hT1 hT2
  refine ⟨henc.2.1, fun s hs1 hs2 => ?_⟩
  have ha' : (1 / 2 : ℝ) ≤ toRq c.a :=
    le_trans (le_of_eq (by norm_num [toRq, Dq])) (toRq_le_toRq.mpr ha)
  have hl : ∀ x ∈ Set.Icc (toRq c.a) (toRq c.last), (c.l : ℝ) ≤ w2 x :=
    fun x hx => chainGe_sound c.l c.rest c.a c.b hch x hx.1 hx.2
  have hsI : s ∈ Set.Icc (toRq c.a) (toRq c.last) :=
    ⟨(toRq_le_toRq.mpr halo).trans hs1, hs2.trans (toRq_le_toRq.mpr hhi)⟩
  have htI : toRq T ∈ Set.Icc (toRq c.a) (toRq c.last) :=
    ⟨toRq_le_toRq.mpr haT, toRq_le_toRq.mpr hTl⟩
  have htay := wfun_taylor2 ha' hl hsI htI
  have hw : (wloK (encK T) : ℝ) ≤ wfun (toRq T) := by
    have := wloK_le henc.1; simpa [wfun, encK] using this
  linarith

/-! ### Positive semidefinite 4×4 forms -/

def form2 (p q r x y : ℝ) : ℝ := p * x ^ 2 + 2 * q * x * y + r * y ^ 2
def form3 (a11 a12 a13 a22 a23 a33 x y z : ℝ) : ℝ :=
  a11 * x ^ 2 + a22 * y ^ 2 + a33 * z ^ 2 + 2 * (a12 * x * y + a13 * x * z + a23 * y * z)
def form4 (m00 m01 m02 m03 m11 m12 m13 m22 m23 m33 d0 d1 d2 d3 : ℝ) : ℝ :=
  m00 * d0 ^ 2 + m11 * d1 ^ 2 + m22 * d2 ^ 2 + m33 * d3 ^ 2
    + 2 * (m01 * d0 * d1 + m02 * d0 * d2 + m03 * d0 * d3 + m12 * d1 * d2 + m13 * d1 * d3
      + m23 * d2 * d3)

lemma form2_nonneg {p q r : ℝ} (hp : 0 < p) (hs : 0 ≤ r - q * q / p) (x y : ℝ) :
    0 ≤ form2 p q r x y := by
  have e : form2 p q r x y = p * (x + q / p * y) ^ 2 + (r - q * q / p) * y ^ 2 := by
    unfold form2; field_simp; ring
  rw [e]; positivity

lemma form3_nonneg {a11 a12 a13 a22 a23 a33 : ℝ} (h1 : 0 < a11)
    (h2 : 0 < a22 - a12 * a12 / a11)
    (h3 : 0 ≤ (a33 - a13 * a13 / a11) - (a23 - a12 * a13 / a11) * (a23 - a12 * a13 / a11)
      / (a22 - a12 * a12 / a11))
    (x y z : ℝ) : 0 ≤ form3 a11 a12 a13 a22 a23 a33 x y z := by
  have e : form3 a11 a12 a13 a22 a23 a33 x y z = a11 * (x + (a12 * y + a13 * z) / a11) ^ 2
      + form2 (a22 - a12 * a12 / a11) (a23 - a12 * a13 / a11) (a33 - a13 * a13 / a11) y z := by
    unfold form3 form2; field_simp; ring
  rw [e]
  have := form2_nonneg h2 h3 y z
  positivity

/-- LDLᵀ on the upper triangle: positive leading pivots, nonnegative last one. -/
def psd4 (m00 m01 m02 m03 m11 m12 m13 m22 m23 m33 : ℚ) : Bool :=
  let a11 := m11 - m01 * m01 / m00
  let a12 := m12 - m01 * m02 / m00
  let a13 := m13 - m01 * m03 / m00
  let a22 := m22 - m02 * m02 / m00
  let a23 := m23 - m02 * m03 / m00
  let a33 := m33 - m03 * m03 / m00
  let b22 := a22 - a12 * a12 / a11
  let b23 := a23 - a12 * a13 / a11
  let b33 := a33 - a13 * a13 / a11
  decide (0 < m00) && decide (0 < a11) && decide (0 < b22) && decide (0 ≤ b33 - b23 * b23 / b22)

theorem psd4_sound {m00 m01 m02 m03 m11 m12 m13 m22 m23 m33 : ℚ}
    (h : psd4 m00 m01 m02 m03 m11 m12 m13 m22 m23 m33 = true) (d0 d1 d2 d3 : ℝ) :
    0 ≤ form4 m00 m01 m02 m03 m11 m12 m13 m22 m23 m33 d0 d1 d2 d3 := by
  simp only [psd4, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨h0, h1⟩, h2⟩, h3⟩ := h
  have h0' : (0 : ℝ) < m00 := by exact_mod_cast h0
  have h1' : (0 : ℝ) < (m11 : ℝ) - m01 * m01 / m00 := by
    have := (Rat.cast_lt (K := ℝ)).mpr h1; push_cast at this; exact this
  have h2' := (Rat.cast_lt (K := ℝ)).mpr h2
  have h3' := (Rat.cast_le (K := ℝ)).mpr h3
  push_cast at h2' h3'
  have e : form4 m00 m01 m02 m03 m11 m12 m13 m22 m23 m33 d0 d1 d2 d3
      = m00 * (d0 + (m01 * d1 + m02 * d2 + m03 * d3) / m00) ^ 2
        + form3 (m11 - m01 * m01 / m00) (m12 - m01 * m02 / m00) (m13 - m01 * m03 / m00)
          (m22 - m02 * m02 / m00) (m23 - m02 * m03 / m00) (m33 - m03 * m03 / m00) d1 d2 d3 := by
    unfold form4 form3; field_simp; ring
  rw [e]
  have := form3_nonneg h1' h2' h3' d1 d2 d3
  have hsq : 0 ≤ (m00 : ℝ) * (d0 + (m01 * d1 + m02 * d2 + m03 * d3) / m00) ^ 2 := by positivity
  linarith


/-! ### Sums of gradient terms, offsets, and five-dimensional forms -/

def sumI : List (ℕ × ℕ) → IQ
  | [] => cst 0
  | (w, T) :: rest => iadd (iscale w (encW1 T)) (sumI rest)

def sumR : List (ℕ × ℕ) → ℝ
  | [] => 0
  | (w, T) :: rest => (w : ℝ) * w1 (toRq T) + sumR rest

lemma mem_sumI : ∀ ts : List (ℕ × ℕ), (∀ wt ∈ ts, Mem (encW1 wt.2) (w1 (toRq wt.2))) →
    Mem (sumI ts) (sumR ts)
  | [], _ => by simpa [sumI, sumR] using mem_cst 0
  | (w, T) :: rest, h => by
    simp only [sumI, sumR]
    have h1 := mem_iscale (w : ℚ) (h (w, T) List.mem_cons_self)
    push_cast at h1
    exact mem_iadd h1 (mem_sumI rest fun wt hwt => h wt (List.mem_cons_of_mem _ hwt))

/-- Enclosure of `P + Σ w · w1(T)`. -/
def gradI (P : ℕ) (ts : List (ℕ × ℕ)) : IQ := iadd (cst (P : ℚ)) (sumI ts)

lemma mem_gradI (P : ℕ) (ts : List (ℕ × ℕ)) (h : ∀ wt ∈ ts, Mem (encW1 wt.2) (w1 (toRq wt.2))) :
    Mem (gradI P ts) ((P : ℝ) + sumR ts) := by
  have := mem_iadd (mem_cst (P : ℚ)) (mem_sumI ts h)
  unfold gradI; refine mem_congr this ?_; push_cast; ring

/-- The offsets `g − q` on `[lo, hi]` (grid units). -/
def offI (lo hi q : ℕ) : IQ := (((lo : ℚ) - q) / 4294967296, ((hi : ℚ) - q) / 4294967296)

lemma mem_offI {lo hi q : ℕ} {x : ℝ} (h1 : toRq lo ≤ x) (h2 : x ≤ toRq hi) :
    Mem (offI lo hi q) (x - toRq q) := by
  unfold offI Mem toRq Dq at *
  push_cast at *
  constructor <;> [skip; skip] <;> rw [sub_div] <;> linarith

def form5 (m00 m01 m02 m03 m04 m11 m12 m13 m14 m22 m23 m24 m33 m34 m44 d0 d1 d2 d3 d4 : ℝ) : ℝ :=
  m00 * d0 ^ 2 + 2 * (m01 * d0 * d1 + m02 * d0 * d2 + m03 * d0 * d3 + m04 * d0 * d4)
    + form4 m11 m12 m13 m14 m22 m23 m24 m33 m34 m44 d1 d2 d3 d4

/-- One elimination step, then `psd4` on the Schur complement. -/
def psd5 (m00 m01 m02 m03 m04 m11 m12 m13 m14 m22 m23 m24 m33 m34 m44 : ℚ) : Bool :=
  decide (0 < m00) && psd4 (m11 - m01 * m01 / m00) (m12 - m01 * m02 / m00) (m13 - m01 * m03 / m00)
    (m14 - m01 * m04 / m00) (m22 - m02 * m02 / m00) (m23 - m02 * m03 / m00)
    (m24 - m02 * m04 / m00) (m33 - m03 * m03 / m00) (m34 - m03 * m04 / m00)
    (m44 - m04 * m04 / m00)

theorem psd5_sound {m00 m01 m02 m03 m04 m11 m12 m13 m14 m22 m23 m24 m33 m34 m44 : ℚ}
    (h : psd5 m00 m01 m02 m03 m04 m11 m12 m13 m14 m22 m23 m24 m33 m34 m44 = true)
    (d0 d1 d2 d3 d4 : ℝ) :
    0 ≤ form5 m00 m01 m02 m03 m04 m11 m12 m13 m14 m22 m23 m24 m33 m34 m44 d0 d1 d2 d3 d4 := by
  simp only [psd5, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨h0, h4⟩ := h
  have h0' : (0 : ℝ) < m00 := by exact_mod_cast h0
  have hs := psd4_sound h4 d1 d2 d3 d4
  push_cast at hs
  have e : form5 m00 m01 m02 m03 m04 m11 m12 m13 m14 m22 m23 m24 m33 m34 m44 d0 d1 d2 d3 d4
      = m00 * (d0 + (m01 * d1 + m02 * d2 + m03 * d3 + m04 * d4) / m00) ^ 2
        + form4 (m11 - m01 * m01 / m00) (m12 - m01 * m02 / m00) (m13 - m01 * m03 / m00)
          (m14 - m01 * m04 / m00) (m22 - m02 * m02 / m00) (m23 - m02 * m03 / m00)
          (m24 - m02 * m04 / m00) (m33 - m03 * m03 / m00) (m34 - m03 * m04 / m00)
          (m44 - m04 * m04 / m00) d1 d2 d3 d4 := by
    unfold form5 form4; field_simp; ring
  rw [e]
  have hsq : 0 ≤ (m00 : ℝ) * (d0 + (m01 * d1 + m02 * d2 + m03 * d3 + m04 * d4) / m00) ^ 2 := by
    positivity
  linarith

end Riemann.BasinC

end

section

/-!
# Convex-basin boxes for the six-point functional

`basin6_sound`: on a box (units `2⁻¹⁵`) whose pairs carry `w''` bounds making the quadratic form
PSD, the tangent plane at a grid point `q` (units `2⁻³²`) bounds `LW6` from below.
-/

noncomputable section

namespace Riemann.Basin6

open Zeta23Ext.Bridge Zeta23Ext.Bridge.ThreePoint Riemann.Deriv Riemann.Encl Riemann.BasinC

/-- Gap pressures and pair weights. -/
structure Wts6 where
  (p0 p1 p2 p3 p4 a01 a02 a03 a04 a05 a12 a13 a14 a15 a23 a24 a25 a34 a35 a45 : ℕ)

def LW6 (V : Wts6) (g0 g1 g2 g3 g4 : ℝ) : ℝ :=
  V.p0 * g0
    + V.p1 * g1
    + V.p2 * g2
    + V.p3 * g3
    + V.p4 * g4
    + V.a01 * wfun (g0)
    + V.a02 * wfun (g0 + g1)
    + V.a03 * wfun (g0 + g1 + g2)
    + V.a04 * wfun (g0 + g1 + g2 + g3)
    + V.a05 * wfun (g0 + g1 + g2 + g3 + g4)
    + V.a12 * wfun (g1)
    + V.a13 * wfun (g1 + g2)
    + V.a14 * wfun (g1 + g2 + g3)
    + V.a15 * wfun (g1 + g2 + g3 + g4)
    + V.a23 * wfun (g2)
    + V.a24 * wfun (g2 + g3)
    + V.a25 * wfun (g2 + g3 + g4)
    + V.a34 * wfun (g3)
    + V.a35 * wfun (g3 + g4)
    + V.a45 * wfun (g4)

structure Box6 where
  (l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 : ℕ)

def Box6.mem (b : Box6) (g0 g1 g2 g3 g4 : ℝ) : Prop :=
  (b.l0 : ℝ) / 32768 ≤ g0 ∧ g0 ≤ (b.u0 : ℝ) / 32768 ∧ (b.l1 : ℝ) / 32768 ≤ g1 ∧ g1 ≤ (b.u1 : ℝ) / 32768 ∧ (b.l2 : ℝ) / 32768 ≤ g2 ∧ g2 ≤ (b.u2 : ℝ) / 32768 ∧ (b.l3 : ℝ) / 32768 ≤ g3 ∧ g3 ≤ (b.u3 : ℝ) / 32768 ∧ (b.l4 : ℝ) / 32768 ≤ g4 ∧ g4 ≤ (b.u4 : ℝ) / 32768

structure BasinD6 where
  (box : Box6) (q0 q1 q2 q3 q4 : ℕ)
  (c01 c02 c03 c04 c05 c12 c13 c14 c15 c23 c24 c25 c34 c35 c45 : Chain)

def BasinD6.pairsOk (d : BasinD6) : Bool :=
  let b := d.box
  pairOk d.c01 (131072 * (b.l0)) (131072 * (b.u0)) (d.q0)
    && pairOk d.c02 (131072 * (b.l0 + b.l1)) (131072 * (b.u0 + b.u1)) (d.q0 + d.q1)
    && pairOk d.c03 (131072 * (b.l0 + b.l1 + b.l2)) (131072 * (b.u0 + b.u1 + b.u2)) (d.q0 + d.q1 + d.q2)
    && pairOk d.c04 (131072 * (b.l0 + b.l1 + b.l2 + b.l3)) (131072 * (b.u0 + b.u1 + b.u2 + b.u3)) (d.q0 + d.q1 + d.q2 + d.q3)
    && pairOk d.c05 (131072 * (b.l0 + b.l1 + b.l2 + b.l3 + b.l4)) (131072 * (b.u0 + b.u1 + b.u2 + b.u3 + b.u4)) (d.q0 + d.q1 + d.q2 + d.q3 + d.q4)
    && pairOk d.c12 (131072 * (b.l1)) (131072 * (b.u1)) (d.q1)
    && pairOk d.c13 (131072 * (b.l1 + b.l2)) (131072 * (b.u1 + b.u2)) (d.q1 + d.q2)
    && pairOk d.c14 (131072 * (b.l1 + b.l2 + b.l3)) (131072 * (b.u1 + b.u2 + b.u3)) (d.q1 + d.q2 + d.q3)
    && pairOk d.c15 (131072 * (b.l1 + b.l2 + b.l3 + b.l4)) (131072 * (b.u1 + b.u2 + b.u3 + b.u4)) (d.q1 + d.q2 + d.q3 + d.q4)
    && pairOk d.c23 (131072 * (b.l2)) (131072 * (b.u2)) (d.q2)
    && pairOk d.c24 (131072 * (b.l2 + b.l3)) (131072 * (b.u2 + b.u3)) (d.q2 + d.q3)
    && pairOk d.c25 (131072 * (b.l2 + b.l3 + b.l4)) (131072 * (b.u2 + b.u3 + b.u4)) (d.q2 + d.q3 + d.q4)
    && pairOk d.c34 (131072 * (b.l3)) (131072 * (b.u3)) (d.q3)
    && pairOk d.c35 (131072 * (b.l3 + b.l4)) (131072 * (b.u3 + b.u4)) (d.q3 + d.q4)
    && pairOk d.c45 (131072 * (b.l4)) (131072 * (b.u4)) (d.q4)

def BasinD6.psd (V : Wts6) (d : BasinD6) : Bool :=
  let e01 := (V.a01 : ℚ) * d.c01.l
  let e02 := (V.a02 : ℚ) * d.c02.l
  let e03 := (V.a03 : ℚ) * d.c03.l
  let e04 := (V.a04 : ℚ) * d.c04.l
  let e05 := (V.a05 : ℚ) * d.c05.l
  let e12 := (V.a12 : ℚ) * d.c12.l
  let e13 := (V.a13 : ℚ) * d.c13.l
  let e14 := (V.a14 : ℚ) * d.c14.l
  let e15 := (V.a15 : ℚ) * d.c15.l
  let e23 := (V.a23 : ℚ) * d.c23.l
  let e24 := (V.a24 : ℚ) * d.c24.l
  let e25 := (V.a25 : ℚ) * d.c25.l
  let e34 := (V.a34 : ℚ) * d.c34.l
  let e35 := (V.a35 : ℚ) * d.c35.l
  let e45 := (V.a45 : ℚ) * d.c45.l
  psd5 (e01 + e02 + e03 + e04 + e05) (e02 + e03 + e04 + e05) (e03 + e04 + e05) (e04 + e05) (e05) (e02 + e03 + e04 + e05 + e12 + e13 + e14 + e15) (e03 + e04 + e05 + e13 + e14 + e15) (e04 + e05 + e14 + e15) (e05 + e15) (e03 + e04 + e05 + e13 + e14 + e15 + e23 + e24 + e25) (e04 + e05 + e14 + e15 + e24 + e25) (e05 + e15 + e25) (e04 + e05 + e14 + e15 + e24 + e25 + e34 + e35) (e05 + e15 + e25 + e35) (e05 + e15 + e25 + e35 + e45)

def BasinD6.bound (V : Wts6) (d : BasinD6) : ℚ :=
  let b := d.box
  ((V.p0 * d.q0 + V.p1 * d.q1 + V.p2 * d.q2 + V.p3 * d.q3 + V.p4 * d.q4 : ℕ) : ℚ) / 4294967296
    + ((V.a01 : ℚ) * wloK (encK (d.q0))
      + (V.a02 : ℚ) * wloK (encK (d.q0 + d.q1))
      + (V.a03 : ℚ) * wloK (encK (d.q0 + d.q1 + d.q2))
      + (V.a04 : ℚ) * wloK (encK (d.q0 + d.q1 + d.q2 + d.q3))
      + (V.a05 : ℚ) * wloK (encK (d.q0 + d.q1 + d.q2 + d.q3 + d.q4))
      + (V.a12 : ℚ) * wloK (encK (d.q1))
      + (V.a13 : ℚ) * wloK (encK (d.q1 + d.q2))
      + (V.a14 : ℚ) * wloK (encK (d.q1 + d.q2 + d.q3))
      + (V.a15 : ℚ) * wloK (encK (d.q1 + d.q2 + d.q3 + d.q4))
      + (V.a23 : ℚ) * wloK (encK (d.q2))
      + (V.a24 : ℚ) * wloK (encK (d.q2 + d.q3))
      + (V.a25 : ℚ) * wloK (encK (d.q2 + d.q3 + d.q4))
      + (V.a34 : ℚ) * wloK (encK (d.q3))
      + (V.a35 : ℚ) * wloK (encK (d.q3 + d.q4))
      + (V.a45 : ℚ) * wloK (encK (d.q4)))
    + (imul (gradI V.p0 [(V.a01, d.q0), (V.a02, d.q0 + d.q1), (V.a03, d.q0 + d.q1 + d.q2), (V.a04, d.q0 + d.q1 + d.q2 + d.q3), (V.a05, d.q0 + d.q1 + d.q2 + d.q3 + d.q4)])
        (offI (131072 * b.l0) (131072 * b.u0) d.q0)).1
    + (imul (gradI V.p1 [(V.a02, d.q0 + d.q1), (V.a03, d.q0 + d.q1 + d.q2), (V.a04, d.q0 + d.q1 + d.q2 + d.q3), (V.a05, d.q0 + d.q1 + d.q2 + d.q3 + d.q4), (V.a12, d.q1), (V.a13, d.q1 + d.q2), (V.a14, d.q1 + d.q2 + d.q3), (V.a15, d.q1 + d.q2 + d.q3 + d.q4)])
        (offI (131072 * b.l1) (131072 * b.u1) d.q1)).1
    + (imul (gradI V.p2 [(V.a03, d.q0 + d.q1 + d.q2), (V.a04, d.q0 + d.q1 + d.q2 + d.q3), (V.a05, d.q0 + d.q1 + d.q2 + d.q3 + d.q4), (V.a13, d.q1 + d.q2), (V.a14, d.q1 + d.q2 + d.q3), (V.a15, d.q1 + d.q2 + d.q3 + d.q4), (V.a23, d.q2), (V.a24, d.q2 + d.q3), (V.a25, d.q2 + d.q3 + d.q4)])
        (offI (131072 * b.l2) (131072 * b.u2) d.q2)).1
    + (imul (gradI V.p3 [(V.a04, d.q0 + d.q1 + d.q2 + d.q3), (V.a05, d.q0 + d.q1 + d.q2 + d.q3 + d.q4), (V.a14, d.q1 + d.q2 + d.q3), (V.a15, d.q1 + d.q2 + d.q3 + d.q4), (V.a24, d.q2 + d.q3), (V.a25, d.q2 + d.q3 + d.q4), (V.a34, d.q3), (V.a35, d.q3 + d.q4)])
        (offI (131072 * b.l3) (131072 * b.u3) d.q3)).1
    + (imul (gradI V.p4 [(V.a05, d.q0 + d.q1 + d.q2 + d.q3 + d.q4), (V.a15, d.q1 + d.q2 + d.q3 + d.q4), (V.a25, d.q2 + d.q3 + d.q4), (V.a35, d.q3 + d.q4), (V.a45, d.q4)])
        (offI (131072 * b.l4) (131072 * b.u4) d.q4)).1

def basinOk6 (V : Wts6) (C : ℕ) (d : BasinD6) : Bool :=
  d.pairsOk && d.psd V && decide ((C : ℚ) ≤ d.bound V)

lemma toRq_sc (n : ℕ) : toRq (131072 * n) = (n : ℝ) / 32768 := by
  unfold toRq Dq; push_cast; ring

lemma toRq_eq (n : ℕ) : toRq n = (n : ℝ) / 4294967296 := by
  unfold toRq Dq; push_cast; ring

set_option maxHeartbeats 8000000 in
theorem basin6_sound (V : Wts6) (C : ℕ) (d : BasinD6) (h : basinOk6 V C d = true) :
    ∀ g0 g1 g2 g3 g4 : ℝ, d.box.mem g0 g1 g2 g3 g4 → (C : ℝ) ≤ LW6 V g0 g1 g2 g3 g4 := by
  simp only [basinOk6, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hp, hpsd⟩, hb⟩ := h
  simp only [BasinD6.pairsOk, Bool.and_eq_true] at hp
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨p01, p02⟩, p03⟩, p04⟩, p05⟩, p12⟩, p13⟩, p14⟩, p15⟩, p23⟩, p24⟩, p25⟩, p34⟩, p35⟩, p45⟩ := hp
  intro g0 g1 g2 g3 g4 hm
  obtain ⟨h0a, h0b, h1a, h1b, h2a, h2b, h3a, h3b, h4a, h4b⟩ := hm
  simp only [← toRq_sc] at h0a h0b h1a h1b h2a h2b h3a h3b h4a h4b
  obtain ⟨e01, b01⟩ := pair_sound p01
  obtain ⟨e02, b02⟩ := pair_sound p02
  obtain ⟨e03, b03⟩ := pair_sound p03
  obtain ⟨e04, b04⟩ := pair_sound p04
  obtain ⟨e05, b05⟩ := pair_sound p05
  obtain ⟨e12, b12⟩ := pair_sound p12
  obtain ⟨e13, b13⟩ := pair_sound p13
  obtain ⟨e14, b14⟩ := pair_sound p14
  obtain ⟨e15, b15⟩ := pair_sound p15
  obtain ⟨e23, b23⟩ := pair_sound p23
  obtain ⟨e24, b24⟩ := pair_sound p24
  obtain ⟨e25, b25⟩ := pair_sound p25
  obtain ⟨e34, b34⟩ := pair_sound p34
  obtain ⟨e35, b35⟩ := pair_sound p35
  obtain ⟨e45, b45⟩ := pair_sound p45
  simp only [toRq_add, Nat.mul_add] at b01 b02 b03 b04 b05 b12 b13 b14 b15 b23 b24 b25 b34 b35 b45
  have i01 := b01 (g0) (by linarith [h0a]) (by linarith [h0b])
  have i02 := b02 (g0 + g1) (by linarith [h0a, h1a]) (by linarith [h0b, h1b])
  have i03 := b03 (g0 + g1 + g2) (by linarith [h0a, h1a, h2a]) (by linarith [h0b, h1b, h2b])
  have i04 := b04 (g0 + g1 + g2 + g3) (by linarith [h0a, h1a, h2a, h3a]) (by linarith [h0b, h1b, h2b, h3b])
  have i05 := b05 (g0 + g1 + g2 + g3 + g4) (by linarith [h0a, h1a, h2a, h3a, h4a]) (by linarith [h0b, h1b, h2b, h3b, h4b])
  have i12 := b12 (g1) (by linarith [h1a]) (by linarith [h1b])
  have i13 := b13 (g1 + g2) (by linarith [h1a, h2a]) (by linarith [h1b, h2b])
  have i14 := b14 (g1 + g2 + g3) (by linarith [h1a, h2a, h3a]) (by linarith [h1b, h2b, h3b])
  have i15 := b15 (g1 + g2 + g3 + g4) (by linarith [h1a, h2a, h3a, h4a]) (by linarith [h1b, h2b, h3b, h4b])
  have i23 := b23 (g2) (by linarith [h2a]) (by linarith [h2b])
  have i24 := b24 (g2 + g3) (by linarith [h2a, h3a]) (by linarith [h2b, h3b])
  have i25 := b25 (g2 + g3 + g4) (by linarith [h2a, h3a, h4a]) (by linarith [h2b, h3b, h4b])
  have i34 := b34 (g3) (by linarith [h3a]) (by linarith [h3b])
  have i35 := b35 (g3 + g4) (by linarith [h3a, h4a]) (by linarith [h3b, h4b])
  have i45 := b45 (g4) (by linarith [h4a]) (by linarith [h4b])
  try simp only [toRq_add] at i01 i02 i03 i04 i05 i12 i13 i14 i15 i23 i24 i25 i34 i35 i45
  have hm0 : ∀ wt ∈ [(V.a01, d.q0), (V.a02, d.q0 + d.q1), (V.a03, d.q0 + d.q1 + d.q2), (V.a04, d.q0 + d.q1 + d.q2 + d.q3), (V.a05, d.q0 + d.q1 + d.q2 + d.q3 + d.q4)],
      Mem (encW1 wt.2) (w1 (toRq wt.2)) := by
    intro wt hwt; simp only [List.mem_cons, List.not_mem_nil, or_false] at hwt
    rcases hwt with rfl | rfl | rfl | rfl | rfl
    exacts [e01, e02, e03, e04, e05]
  have gr0 := (mem_imul (mem_gradI V.p0 _ hm0) (mem_offI (q := d.q0) h0a h0b)).1
  have hm1 : ∀ wt ∈ [(V.a02, d.q0 + d.q1), (V.a03, d.q0 + d.q1 + d.q2), (V.a04, d.q0 + d.q1 + d.q2 + d.q3), (V.a05, d.q0 + d.q1 + d.q2 + d.q3 + d.q4), (V.a12, d.q1), (V.a13, d.q1 + d.q2), (V.a14, d.q1 + d.q2 + d.q3), (V.a15, d.q1 + d.q2 + d.q3 + d.q4)],
      Mem (encW1 wt.2) (w1 (toRq wt.2)) := by
    intro wt hwt; simp only [List.mem_cons, List.not_mem_nil, or_false] at hwt
    rcases hwt with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [e02, e03, e04, e05, e12, e13, e14, e15]
  have gr1 := (mem_imul (mem_gradI V.p1 _ hm1) (mem_offI (q := d.q1) h1a h1b)).1
  have hm2 : ∀ wt ∈ [(V.a03, d.q0 + d.q1 + d.q2), (V.a04, d.q0 + d.q1 + d.q2 + d.q3), (V.a05, d.q0 + d.q1 + d.q2 + d.q3 + d.q4), (V.a13, d.q1 + d.q2), (V.a14, d.q1 + d.q2 + d.q3), (V.a15, d.q1 + d.q2 + d.q3 + d.q4), (V.a23, d.q2), (V.a24, d.q2 + d.q3), (V.a25, d.q2 + d.q3 + d.q4)],
      Mem (encW1 wt.2) (w1 (toRq wt.2)) := by
    intro wt hwt; simp only [List.mem_cons, List.not_mem_nil, or_false] at hwt
    rcases hwt with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [e03, e04, e05, e13, e14, e15, e23, e24, e25]
  have gr2 := (mem_imul (mem_gradI V.p2 _ hm2) (mem_offI (q := d.q2) h2a h2b)).1
  have hm3 : ∀ wt ∈ [(V.a04, d.q0 + d.q1 + d.q2 + d.q3), (V.a05, d.q0 + d.q1 + d.q2 + d.q3 + d.q4), (V.a14, d.q1 + d.q2 + d.q3), (V.a15, d.q1 + d.q2 + d.q3 + d.q4), (V.a24, d.q2 + d.q3), (V.a25, d.q2 + d.q3 + d.q4), (V.a34, d.q3), (V.a35, d.q3 + d.q4)],
      Mem (encW1 wt.2) (w1 (toRq wt.2)) := by
    intro wt hwt; simp only [List.mem_cons, List.not_mem_nil, or_false] at hwt
    rcases hwt with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [e04, e05, e14, e15, e24, e25, e34, e35]
  have gr3 := (mem_imul (mem_gradI V.p3 _ hm3) (mem_offI (q := d.q3) h3a h3b)).1
  have hm4 : ∀ wt ∈ [(V.a05, d.q0 + d.q1 + d.q2 + d.q3 + d.q4), (V.a15, d.q1 + d.q2 + d.q3 + d.q4), (V.a25, d.q2 + d.q3 + d.q4), (V.a35, d.q3 + d.q4), (V.a45, d.q4)],
      Mem (encW1 wt.2) (w1 (toRq wt.2)) := by
    intro wt hwt; simp only [List.mem_cons, List.not_mem_nil, or_false] at hwt
    rcases hwt with rfl | rfl | rfl | rfl | rfl
    exacts [e05, e15, e25, e35, e45]
  have gr4 := (mem_imul (mem_gradI V.p4 _ hm4) (mem_offI (q := d.q4) h4a h4b)).1
  try simp only [sumR, toRq_add] at gr0 gr1 gr2 gr3 gr4
  have hq := psd5_sound hpsd (g0 - toRq d.q0) (g1 - toRq d.q1) (g2 - toRq d.q2) (g3 - toRq d.q3) (g4 - toRq d.q4)
  have hq' : 0 ≤ (1 : ℝ) / 2 * form5 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (g0 - toRq d.q0) (g1 - toRq d.q1) (g2 - toRq d.q2) (g3 - toRq d.q3) (g4 - toRq d.q4) := mul_nonneg (by norm_num) hq
  have hb' : (C : ℝ) ≤ (d.bound V : ℝ) := by exact_mod_cast hb
  simp only [BasinD6.bound] at hb'
  push_cast at hb' hq'
  have hw : ∀ (W : ℕ) {x y : ℝ}, x ≤ y → (W : ℝ) * x ≤ W * y := fun W x y hxy =>
    mul_le_mul_of_nonneg_left hxy (Nat.cast_nonneg _)
  have hT0 := toRq_eq d.q0
  have hT1 := toRq_eq d.q1
  have hT2 := toRq_eq d.q2
  have hT3 := toRq_eq d.q3
  have hT4 := toRq_eq d.q4
  unfold LW6
  unfold form5 form4 at hq'
  linear_combination hb'
    + gr0
    + gr1
    + gr2
    + gr3
    + gr4
    + hw V.a01 i01
    + hw V.a02 i02
    + hw V.a03 i03
    + hw V.a04 i04
    + hw V.a05 i05
    + hw V.a12 i12
    + hw V.a13 i13
    + hw V.a14 i14
    + hw V.a15 i15
    + hw V.a23 i23
    + hw V.a24 i24
    + hw V.a25 i25
    + hw V.a34 i34
    + hw V.a35 i35
    + hw V.a45 i45
    + hq'
    - (V.p0 : ℝ) * hT0
    - (V.p1 : ℝ) * hT1
    - (V.p2 : ℝ) * hT2
    - (V.p3 : ℝ) * hT3
    - (V.p4 : ℝ) * hT4

end Riemann.Basin6

end

/-! ###### the 6-point weighted certificate `SixW25P` on the pyramid oracle: leaf test, walk, cover ###### -/

noncomputable section

namespace Zeta23Ext.Bridge.ThreePoint.SixW25P

open Zeta23Ext.Bridge.ThreePoint Zeta23Ext.Bridge.ThreePoint.Pyr

def SA : ℕ := 100000000
def cN : ℕ := 548021

/-- the weighted functional on the gaps, in real form -/
def G (g0 g1 g2 g3 g4 : ℝ) : ℝ :=
  (50125 / (SA:ℝ)) * g0 + (71659 / (SA:ℝ)) * g1 + (62043 / (SA:ℝ)) * g2 + (71659 / (SA:ℝ)) * g3 + (50125 / (SA:ℝ)) * g4
    + (25193671 / (SA:ℝ)) * wfun (g0) + (93418335 / (SA:ℝ)) * wfun (g0 + g1) + (54983399 / (SA:ℝ)) * wfun (g0 + g1 + g2) + (100000000 / (SA:ℝ)) * wfun (g0 + g1 + g2 + g3) + (200000000 / (SA:ℝ)) * wfun (g0 + g1 + g2 + g3 + g4) + (49170450 / (SA:ℝ)) * wfun (g1) + (6581664 / (SA:ℝ)) * wfun (g1 + g2) + (90033200 / (SA:ℝ)) * wfun (g1 + g2 + g3) + (100000000 / (SA:ℝ)) * wfun (g1 + g2 + g3 + g4) + (51271755 / (SA:ℝ)) * wfun (g2) + (6581664 / (SA:ℝ)) * wfun (g2 + g3) + (54983399 / (SA:ℝ)) * wfun (g2 + g3 + g4) + (49170450 / (SA:ℝ)) * wfun (g3) + (93418335 / (SA:ℝ)) * wfun (g3 + g4) + (25193671 / (SA:ℝ)) * wfun (g4)

/-- early exit: `true` once the running sum `s` reaches `C`, else the rest of the test -/
def ee (C s : ℕ) (rest : Bool) : Bool := Bool.rec (motive := fun _ => Bool) rest true (Nat.ble C s)

/-- the leaf test `cN·SC·U ≤ U·Σ b_r l_r + SC·Σ a_t lb_t` (U = 10¹⁰), the terms added in a fixed order and the
running sum tested after each -/
def leafOK (top : ℕ) (bk : ℕ → ℕ) (l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 : ℕ) : Bool :=
  let s0 := Nat.mul (Nat.add (Nat.add (Nat.add (Nat.add (Nat.mul 50125 l0) (Nat.mul 71659 l1)) (Nat.mul 62043 l2)) (Nat.mul 71659 l3)) (Nat.mul 50125 l4)) 10000000000
  ee 179575521280000000000 s0 (
  let s1 := Nat.add s0 (Nat.mul 1611217305600 (lb top bk l1 u1))
  ee 179575521280000000000 s1 (
  let s2 := Nat.add s1 (Nat.mul 1611217305600 (lb top bk l3 u3))
  ee 179575521280000000000 s2 (
  let s3 := Nat.add s2 (Nat.mul 1680072867840 (lb top bk l2 u2))
  ee 179575521280000000000 s3 (
  let s4 := Nat.add s3 (Nat.mul 825546211328 (lb top bk l0 u0))
  ee 179575521280000000000 s4 (
  let s5 := Nat.add s4 (Nat.mul 6553600000000 (lb top bk (Nat.add (Nat.add (Nat.add (Nat.add l0 l1) l2) l3) l4) (Nat.add (Nat.add (Nat.add (Nat.add u0 u1) u2) u3) u4)))
  ee 179575521280000000000 s5 (
  let s6 := Nat.add s5 (Nat.mul 825546211328 (lb top bk l4 u4))
  ee 179575521280000000000 s6 (
  let s7 := Nat.add s6 (Nat.mul 3276800000000 (lb top bk (Nat.add (Nat.add (Nat.add l0 l1) l2) l3) (Nat.add (Nat.add (Nat.add u0 u1) u2) u3)))
  ee 179575521280000000000 s7 (
  let s8 := Nat.add s7 (Nat.mul 2950207897600 (lb top bk (Nat.add (Nat.add l1 l2) l3) (Nat.add (Nat.add u1 u2) u3)))
  ee 179575521280000000000 s8 (
  let s9 := Nat.add s8 (Nat.mul 1801696018432 (lb top bk (Nat.add (Nat.add l0 l1) l2) (Nat.add (Nat.add u0 u1) u2)))
  ee 179575521280000000000 s9 (
  let s10 := Nat.add s9 (Nat.mul 3276800000000 (lb top bk (Nat.add (Nat.add (Nat.add l1 l2) l3) l4) (Nat.add (Nat.add (Nat.add u1 u2) u3) u4)))
  ee 179575521280000000000 s10 (
  let s11 := Nat.add s10 (Nat.mul 3061132001280 (lb top bk (Nat.add l0 l1) (Nat.add u0 u1)))
  ee 179575521280000000000 s11 (
  let s12 := Nat.add s11 (Nat.mul 1801696018432 (lb top bk (Nat.add (Nat.add l2 l3) l4) (Nat.add (Nat.add u2 u3) u4)))
  ee 179575521280000000000 s12 (
  let s13 := Nat.add s12 (Nat.mul 215667965952 (lb top bk (Nat.add l2 l3) (Nat.add u2 u3)))
  ee 179575521280000000000 s13 (
  let s14 := Nat.add s13 (Nat.mul 3061132001280 (lb top bk (Nat.add l3 l4) (Nat.add u3 u4)))
  ee 179575521280000000000 s14 (
  let s15 := Nat.add s14 (Nat.mul 215667965952 (lb top bk (Nat.add l1 l2) (Nat.add u1 u2)))
  Nat.ble 179575521280000000000 s15)))))))))))))))

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

/-- the box lies inside one of the certified convex basins -/
def inBas (bas : List Riemann.Basin6.Box6) (l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 : ℕ) : Bool :=
  bas.any fun B => Nat.ble B.l0 l0 && Nat.ble u0 B.u0 && Nat.ble B.l1 l1 && Nat.ble u1 B.u1
    && Nat.ble B.l2 l2 && Nat.ble u2 B.u2 && Nat.ble B.l3 l3 && Nat.ble u3 B.u3
    && Nat.ble B.l4 l4 && Nat.ble u4 B.u4

/-- a leaf: in the reflected half-space, passing the leaf test, or in a certified basin -/
def leafStep (top : ℕ) (bk : ℕ → ℕ) (bas : List Riemann.Basin6.Box6) (pos l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => ℕ)
    (Bool.rec (motive := fun _ => ℕ)
      (Bool.rec (motive := fun _ => ℕ) (0) (Nat.add pos 1) (inBas bas l0 u0 l1 u1 l2 u2 l3 u3 l4 u4))
      (Nat.add pos 1) (leafOK top bk l0 u0 l1 u1 l2 u2 l3 u3 l4 u4))
    (Nat.add pos 1) (Nat.ble (Nat.add u4 1) l0)

/-- the bisection walk over the ten box coordinates (`Nat.rec` on the fuel): the node code is
`(bits >>> pos) &&& 15` (bit 0 split, bits 1..3 axis); the position after the subtree, `0` on failure -/
def walk (top : ℕ) (bk : ℕ → ℕ) (bas : List Riemann.Basin6.Box6) (bits : ℕ) (fuel : ℕ) : WF :=
  Nat.rec (motive := fun _ => WF) (fun _ _ _ _ _ _ _ _ _ _ _ => 0)
    (fun _ ih pos l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 =>
      let w := Nat.land (Nat.shiftRight bits pos) 15
      Bool.rec (motive := fun _ => ℕ) (leafStep top bk bas pos l0 u0 l1 u1 l2 u2 l3 u3 l4 u4) (splitAx ih pos (Nat.shiftRight w 1) l0 u0 l1 u1 l2 u2 l3 u3 l4 u4) (Nat.beq (Nat.land w 1) 1))
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
    179575521280000000000 ≤ 10000000000 * (50125 * l0 + 71659 * l1 + 62043 * l2 + 71659 * l3 + 50125 * l4) + 32768 * (25193671 * lb top bk (l0) (u0) + 93418335 * lb top bk (l0 + l1) (u0 + u1) + 54983399 * lb top bk (l0 + l1 + l2) (u0 + u1 + u2) + 100000000 * lb top bk (l0 + l1 + l2 + l3) (u0 + u1 + u2 + u3) + 200000000 * lb top bk (l0 + l1 + l2 + l3 + l4) (u0 + u1 + u2 + u3 + u4) + 49170450 * lb top bk (l1) (u1) + 6581664 * lb top bk (l1 + l2) (u1 + u2) + 90033200 * lb top bk (l1 + l2 + l3) (u1 + u2 + u3) + 100000000 * lb top bk (l1 + l2 + l3 + l4) (u1 + u2 + u3 + u4) + 51271755 * lb top bk (l2) (u2) + 6581664 * lb top bk (l2 + l3) (u2 + u3) + 54983399 * lb top bk (l2 + l3 + l4) (u2 + u3 + u4) + 49170450 * lb top bk (l3) (u3) + 93418335 * lb top bk (l3 + l4) (u3 + u4) + 25193671 * lb top bk (l4) (u4)) := by
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
  set L : ℝ := 50125 * ((l0 : ℝ) / SC) + 71659 * ((l1 : ℝ) / SC) + 62043 * ((l2 : ℝ) / SC) + 71659 * ((l3 : ℝ) / SC) + 50125 * ((l4 : ℝ) / SC) with hL
  set Wt : ℝ := 25193671 * ((lb top bk (l0) (u0) : ℝ) / 10000000000) + 93418335 * ((lb top bk (l0 + l1) (u0 + u1) : ℝ) / 10000000000) + 54983399 * ((lb top bk (l0 + l1 + l2) (u0 + u1 + u2) : ℝ) / 10000000000) + 100000000 * ((lb top bk (l0 + l1 + l2 + l3) (u0 + u1 + u2 + u3) : ℝ) / 10000000000) + 200000000 * ((lb top bk (l0 + l1 + l2 + l3 + l4) (u0 + u1 + u2 + u3 + u4) : ℝ) / 10000000000) + 49170450 * ((lb top bk (l1) (u1) : ℝ) / 10000000000) + 6581664 * ((lb top bk (l1 + l2) (u1 + u2) : ℝ) / 10000000000) + 90033200 * ((lb top bk (l1 + l2 + l3) (u1 + u2 + u3) : ℝ) / 10000000000) + 100000000 * ((lb top bk (l1 + l2 + l3 + l4) (u1 + u2 + u3 + u4) : ℝ) / 10000000000) + 51271755 * ((lb top bk (l2) (u2) : ℝ) / 10000000000) + 6581664 * ((lb top bk (l2 + l3) (u2 + u3) : ℝ) / 10000000000) + 54983399 * ((lb top bk (l2 + l3 + l4) (u2 + u3 + u4) : ℝ) / 10000000000) + 49170450 * ((lb top bk (l3) (u3) : ℝ) / 10000000000) + 93418335 * ((lb top bk (l3 + l4) (u3 + u4) : ℝ) / 10000000000) + 25193671 * ((lb top bk (l4) (u4) : ℝ) / 10000000000) with hWt
  have e : (L + Wt) * (SC * 10000000000) = 10000000000 * (50125 * (l0 : ℝ) + 71659 * (l1 : ℝ) + 62043 * (l2 : ℝ) + 71659 * (l3 : ℝ) + 50125 * (l4 : ℝ)) + 32768 * (25193671 * (lb top bk (l0) (u0) : ℝ) + 93418335 * (lb top bk (l0 + l1) (u0 + u1) : ℝ) + 54983399 * (lb top bk (l0 + l1 + l2) (u0 + u1 + u2) : ℝ) + 100000000 * (lb top bk (l0 + l1 + l2 + l3) (u0 + u1 + u2 + u3) : ℝ) + 200000000 * (lb top bk (l0 + l1 + l2 + l3 + l4) (u0 + u1 + u2 + u3 + u4) : ℝ) + 49170450 * (lb top bk (l1) (u1) : ℝ) + 6581664 * (lb top bk (l1 + l2) (u1 + u2) : ℝ) + 90033200 * (lb top bk (l1 + l2 + l3) (u1 + u2 + u3) : ℝ) + 100000000 * (lb top bk (l1 + l2 + l3 + l4) (u1 + u2 + u3 + u4) : ℝ) + 51271755 * (lb top bk (l2) (u2) : ℝ) + 6581664 * (lb top bk (l2 + l3) (u2 + u3) : ℝ) + 54983399 * (lb top bk (l2 + l3 + l4) (u2 + u3 + u4) : ℝ) + 49170450 * (lb top bk (l3) (u3) : ℝ) + 93418335 * (lb top bk (l3 + l4) (u3 + u4) : ℝ) + 25193671 * (lb top bk (l4) (u4) : ℝ)) := by
    rw [hL, hWt]; field_simp; norm_num [SC]; try ring
  have hq' : (cN : ℝ) ≤ L + Wt := by
    refine le_of_mul_le_mul_right ?_ (by positivity : (0:ℝ) < SC * 10000000000)
    rw [e]
    calc (cN : ℝ) * (SC * 10000000000) = 179575521280000000000 := by norm_num [cN, SC]
      _ ≤ _ := hq
  unfold G
  rw [div_le_iff₀ hSA]
  have eG : ((50125 / (SA:ℝ)) * g0 + (71659 / (SA:ℝ)) * g1 + (62043 / (SA:ℝ)) * g2 + (71659 / (SA:ℝ)) * g3 + (50125 / (SA:ℝ)) * g4
      + (25193671 / (SA:ℝ)) * wfun (g0) + (93418335 / (SA:ℝ)) * wfun (g0 + g1) + (54983399 / (SA:ℝ)) * wfun (g0 + g1 + g2) + (100000000 / (SA:ℝ)) * wfun (g0 + g1 + g2 + g3) + (200000000 / (SA:ℝ)) * wfun (g0 + g1 + g2 + g3 + g4) + (49170450 / (SA:ℝ)) * wfun (g1) + (6581664 / (SA:ℝ)) * wfun (g1 + g2) + (90033200 / (SA:ℝ)) * wfun (g1 + g2 + g3) + (100000000 / (SA:ℝ)) * wfun (g1 + g2 + g3 + g4) + (51271755 / (SA:ℝ)) * wfun (g2) + (6581664 / (SA:ℝ)) * wfun (g2 + g3) + (54983399 / (SA:ℝ)) * wfun (g2 + g3 + g4) + (49170450 / (SA:ℝ)) * wfun (g3) + (93418335 / (SA:ℝ)) * wfun (g3 + g4) + (25193671 / (SA:ℝ)) * wfun (g4)) * SA
      = 50125 * g0 + 71659 * g1 + 62043 * g2 + 71659 * g3 + 50125 * g4 + 25193671 * wfun (g0) + 93418335 * wfun (g0 + g1) + 54983399 * wfun (g0 + g1 + g2) + 100000000 * wfun (g0 + g1 + g2 + g3) + 200000000 * wfun (g0 + g1 + g2 + g3 + g4) + 49170450 * wfun (g1) + 6581664 * wfun (g1 + g2) + 90033200 * wfun (g1 + g2 + g3) + 100000000 * wfun (g1 + g2 + g3 + g4) + 51271755 * wfun (g2) + 6581664 * wfun (g2 + g3) + 54983399 * wfun (g2 + g3 + g4) + 49170450 * wfun (g3) + 93418335 * wfun (g3 + g4) + 25193671 * wfun (g4) := by
    field_simp; try ring
  rw [eG]
  rw [hL, hWt] at hq'
  linarith [hq', mul_le_mul_of_nonneg_left h01 (by positivity : (0:ℝ) ≤ 50125), mul_le_mul_of_nonneg_left h11 (by positivity : (0:ℝ) ≤ 71659), mul_le_mul_of_nonneg_left h21 (by positivity : (0:ℝ) ≤ 62043), mul_le_mul_of_nonneg_left h31 (by positivity : (0:ℝ) ≤ 71659), mul_le_mul_of_nonneg_left h41 (by positivity : (0:ℝ) ≤ 50125), mul_le_mul_of_nonneg_left w0 (by positivity : (0:ℝ) ≤ 25193671), mul_le_mul_of_nonneg_left w1 (by positivity : (0:ℝ) ≤ 93418335), mul_le_mul_of_nonneg_left w2 (by positivity : (0:ℝ) ≤ 54983399), mul_le_mul_of_nonneg_left w3 (by positivity : (0:ℝ) ≤ 100000000), mul_le_mul_of_nonneg_left w4 (by positivity : (0:ℝ) ≤ 200000000), mul_le_mul_of_nonneg_left w5 (by positivity : (0:ℝ) ≤ 49170450), mul_le_mul_of_nonneg_left w6 (by positivity : (0:ℝ) ≤ 6581664), mul_le_mul_of_nonneg_left w7 (by positivity : (0:ℝ) ≤ 90033200), mul_le_mul_of_nonneg_left w8 (by positivity : (0:ℝ) ≤ 100000000), mul_le_mul_of_nonneg_left w9 (by positivity : (0:ℝ) ≤ 51271755), mul_le_mul_of_nonneg_left w10 (by positivity : (0:ℝ) ≤ 6581664), mul_le_mul_of_nonneg_left w11 (by positivity : (0:ℝ) ≤ 54983399), mul_le_mul_of_nonneg_left w12 (by positivity : (0:ℝ) ≤ 49170450), mul_le_mul_of_nonneg_left w13 (by positivity : (0:ℝ) ≤ 93418335), mul_le_mul_of_nonneg_left w14 (by positivity : (0:ℝ) ≤ 25193671)]


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

theorem leafStep_sound {top : ℕ} {bk : ℕ → ℕ} (hlb : LBSound top bk) {bas : List Riemann.Basin6.Box6}
    (hbas : ∀ B ∈ bas, Covered B.l0 B.u0 B.l1 B.u1 B.l2 B.u2 B.l3 B.u3 B.l4 B.u4)
    (pos l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 : ℕ) (h : leafStep top bk bas pos l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 ≠ 0) :
    Covered l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 := by
  unfold leafStep at h
  intro g0 g1 g2 g3 g4 h01 h02 h11 h12 h21 h22 h31 h32 h41 h42
  cases hs : Nat.ble (Nat.add u4 1) l0
  · rw [hs] at h
    cases hl : leafOK top bk l0 u0 l1 u1 l2 u2 l3 u3 l4 u4
    · rw [hl] at h
      cases hb : inBas bas l0 u0 l1 u1 l2 u2 l3 u3 l4 u4
      · rw [hb] at h; exact absurd rfl h
      simp only [inBas, List.any_eq_true, Bool.and_eq_true, Nat.ble_eq] at hb
      obtain ⟨B, hB, ⟨⟨⟨⟨⟨⟨⟨⟨⟨c1, c2⟩, c3⟩, c4⟩, c5⟩, c6⟩, c7⟩, c8⟩, c9⟩, c10⟩⟩ := hb
      have hSC : (0:ℝ) < SC := by norm_num [SC]
      have m : ∀ a b : ℕ, a ≤ b → (a : ℝ) / SC ≤ (b : ℝ) / SC := fun a b hab =>
        div_le_div_of_nonneg_right (by exact_mod_cast hab) hSC.le
      exact hbas B hB g0 g1 g2 g3 g4 ((m _ _ c1).trans h01) (h02.trans (m _ _ c2))
        ((m _ _ c3).trans h11) (h12.trans (m _ _ c4)) ((m _ _ c5).trans h21) (h22.trans (m _ _ c6))
        ((m _ _ c7).trans h31) (h32.trans (m _ _ c8)) ((m _ _ c9).trans h41) (h42.trans (m _ _ c10))
    · exact Or.inl (leaf_sound hlb l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 hl g0 g1 g2 g3 g4 h01 h02 h11 h12 h21 h22 h31 h32 h41 h42)
  · right
    have hsk : u4 < l0 := by rw [Nat.ble_eq] at hs; simp only [Nat.add_eq] at hs; omega
    have : (u4 : ℝ) / SC < (l0 : ℝ) / SC := div_lt_div_of_pos_right (by exact_mod_cast hsk) (by norm_num [SC])
    linarith

theorem walk_sound {top : ℕ} {bk : ℕ → ℕ} (hlb : LBSound top bk) {bas : List Riemann.Basin6.Box6}
    (hbas : ∀ B ∈ bas, Covered B.l0 B.u0 B.l1 B.u1 B.l2 B.u2 B.l3 B.u3 B.l4 B.u4) (bits : ℕ) :
    ∀ fuel, WalkOK (walk top bk bas bits fuel) := by
  intro fuel
  induction fuel with
  | zero => intro pos l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 h; exact absurd rfl h
  | succ fuel ih =>
    intro pos l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 h
    have h' : Bool.rec (motive := fun _ => ℕ) (leafStep top bk bas pos l0 u0 l1 u1 l2 u2 l3 u3 l4 u4)
        (splitAx (walk top bk bas bits fuel) pos (Nat.shiftRight (Nat.land (Nat.shiftRight bits pos) 15) 1) l0 u0 l1 u1 l2 u2 l3 u3 l4 u4)
        (Nat.beq (Nat.land (Nat.land (Nat.shiftRight bits pos) 15) 1) 1) ≠ 0 := h
    cases hb : Nat.beq (Nat.land (Nat.land (Nat.shiftRight bits pos) 15) 1) 1
    · rw [hb] at h'; exact leafStep_sound hlb hbas pos l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 h'
    · rw [hb] at h'; exact splitAx_sound ih pos _ l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 h'

theorem covered_of_walk {top : ℕ} {bk : ℕ → ℕ} (hlb : LBSound top bk) {bas : List Riemann.Basin6.Box6}
    (hbas : ∀ B ∈ bas, Covered B.l0 B.u0 B.l1 B.u1 B.l2 B.u2 B.l3 B.u3 B.l4 B.u4)
    (bits fuel l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 e : ℕ)
    (h : walk top bk bas bits fuel 1 l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 = e) (he : e ≠ 0) : Covered l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 :=
  walk_sound hlb hbas bits fuel 1 l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 (h ▸ he)

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
    (hS0 : cN * SC ≤ 50125 * S0) (hS1 : cN * SC ≤ 71659 * S1) (hS2 : cN * SC ≤ 62043 * S2) (hS3 : cN * SC ≤ 71659 * S3) (hS4 : cN * SC ≤ 50125 * S4)
    (hcov0 : coverCheck 25193671 (SC / 2) S0 cover0 = true) (hcov1 : coverCheck 49170450 (SC / 2) S1 cover1 = true) (hcov2 : coverCheck 51271755 (SC / 2) S2 cover2 = true) (hcov3 : coverCheck 49170450 (SC / 2) S3 cover3 = true) (hcov4 : coverCheck 25193671 (SC / 2) S4 cover4 = true)
    (hwin : cN * 100 ≤ 19 * 25193671)
    (hrun : ∀ i0 i1 i2 i3 i4, i0 < (badOf cover0).length → i1 < (badOf cover1).length → i2 < (badOf cover2).length → i3 < (badOf cover3).length → i4 < (badOf cover4).length →
      Covered ((badOf cover0).getD i0 (0, 0)).1 ((badOf cover0).getD i0 (0, 0)).2 ((badOf cover1).getD i1 (0, 0)).1 ((badOf cover1).getD i1 (0, 0)).2 ((badOf cover2).getD i2 (0, 0)).1 ((badOf cover2).getD i2 (0, 0)).2 ((badOf cover3).getD i3 (0, 0)).1 ((badOf cover3).getD i3 (0, 0)).2 ((badOf cover4).getD i4 (0, 0)).1 ((badOf cover4).getD i4 (0, 0)).2) :
    ∀ g0 g1 g2 g3 g4 : ℝ, 0 ≤ g0 → 0 ≤ g1 → 0 ≤ g2 → 0 ≤ g3 → 0 ≤ g4 → (cN : ℝ) / SA ≤ G g0 g1 g2 g3 g4 ∨ g4 < g0 := by
  intro g0 g1 g2 g3 g4 hg0 hg1 hg2 hg3 hg4
  have hw := fun v : ℝ => wfun_nonneg v
  have hSA : (0:ℝ) < SA := by norm_num [SA]
  have hSC : (0:ℝ) < SC := by norm_num [SC]
  have hhalf : ((SC / 2 : ℕ) : ℝ) / SC = 1/2 := by norm_num [SC]
  set Lin : ℝ := (50125 / (SA:ℝ)) * g0 + (71659 / (SA:ℝ)) * g1 + (62043 / (SA:ℝ)) * g2 + (71659 / (SA:ℝ)) * g3 + (50125 / (SA:ℝ)) * g4 with hLin
  set Wt : ℝ := (25193671 / (SA:ℝ)) * wfun (g0) + (93418335 / (SA:ℝ)) * wfun (g0 + g1) + (54983399 / (SA:ℝ)) * wfun (g0 + g1 + g2) + (100000000 / (SA:ℝ)) * wfun (g0 + g1 + g2 + g3) + (200000000 / (SA:ℝ)) * wfun (g0 + g1 + g2 + g3 + g4) + (49170450 / (SA:ℝ)) * wfun (g1) + (6581664 / (SA:ℝ)) * wfun (g1 + g2) + (90033200 / (SA:ℝ)) * wfun (g1 + g2 + g3) + (100000000 / (SA:ℝ)) * wfun (g1 + g2 + g3 + g4) + (51271755 / (SA:ℝ)) * wfun (g2) + (6581664 / (SA:ℝ)) * wfun (g2 + g3) + (54983399 / (SA:ℝ)) * wfun (g2 + g3 + g4) + (49170450 / (SA:ℝ)) * wfun (g3) + (93418335 / (SA:ℝ)) * wfun (g3 + g4) + (25193671 / (SA:ℝ)) * wfun (g4) with hWt
  have hG : G g0 g1 g2 g3 g4 = Lin + Wt := by unfold G; rw [hLin, hWt]; ring
  have hb00 : (0:ℝ) ≤ (50125 / (SA:ℝ)) * g0 := mul_nonneg (by positivity) hg0
  have hb10 : (0:ℝ) ≤ (71659 / (SA:ℝ)) * g1 := mul_nonneg (by positivity) hg1
  have hb20 : (0:ℝ) ≤ (62043 / (SA:ℝ)) * g2 := mul_nonneg (by positivity) hg2
  have hb30 : (0:ℝ) ≤ (71659 / (SA:ℝ)) * g3 := mul_nonneg (by positivity) hg3
  have hb40 : (0:ℝ) ≤ (50125 / (SA:ℝ)) * g4 := mul_nonneg (by positivity) hg4
  have ha00 : (0:ℝ) ≤ (25193671 / (SA:ℝ)) * wfun (g0) := mul_nonneg (by positivity) (hw _)
  have ha10 : (0:ℝ) ≤ (93418335 / (SA:ℝ)) * wfun (g0 + g1) := mul_nonneg (by positivity) (hw _)
  have ha20 : (0:ℝ) ≤ (54983399 / (SA:ℝ)) * wfun (g0 + g1 + g2) := mul_nonneg (by positivity) (hw _)
  have ha30 : (0:ℝ) ≤ (100000000 / (SA:ℝ)) * wfun (g0 + g1 + g2 + g3) := mul_nonneg (by positivity) (hw _)
  have ha40 : (0:ℝ) ≤ (200000000 / (SA:ℝ)) * wfun (g0 + g1 + g2 + g3 + g4) := mul_nonneg (by positivity) (hw _)
  have ha50 : (0:ℝ) ≤ (49170450 / (SA:ℝ)) * wfun (g1) := mul_nonneg (by positivity) (hw _)
  have ha60 : (0:ℝ) ≤ (6581664 / (SA:ℝ)) * wfun (g1 + g2) := mul_nonneg (by positivity) (hw _)
  have ha70 : (0:ℝ) ≤ (90033200 / (SA:ℝ)) * wfun (g1 + g2 + g3) := mul_nonneg (by positivity) (hw _)
  have ha80 : (0:ℝ) ≤ (100000000 / (SA:ℝ)) * wfun (g1 + g2 + g3 + g4) := mul_nonneg (by positivity) (hw _)
  have ha90 : (0:ℝ) ≤ (51271755 / (SA:ℝ)) * wfun (g2) := mul_nonneg (by positivity) (hw _)
  have ha100 : (0:ℝ) ≤ (6581664 / (SA:ℝ)) * wfun (g2 + g3) := mul_nonneg (by positivity) (hw _)
  have ha110 : (0:ℝ) ≤ (54983399 / (SA:ℝ)) * wfun (g2 + g3 + g4) := mul_nonneg (by positivity) (hw _)
  have ha120 : (0:ℝ) ≤ (49170450 / (SA:ℝ)) * wfun (g3) := mul_nonneg (by positivity) (hw _)
  have ha130 : (0:ℝ) ≤ (93418335 / (SA:ℝ)) * wfun (g3 + g4) := mul_nonneg (by positivity) (hw _)
  have ha140 : (0:ℝ) ≤ (25193671 / (SA:ℝ)) * wfun (g4) := mul_nonneg (by positivity) (hw _)
  have hLin0 : 0 ≤ Lin := by rw [hLin]; linarith [hb00, hb10, hb20, hb30, hb40]
  have hWt0 : 0 ≤ Wt := by rw [hWt]; linarith [ha00, ha10, ha20, ha30, ha40, ha50, ha60, ha70, ha80, ha90, ha100, ha110, ha120, ha130, ha140]
  have hbL0 : (50125 / (SA:ℝ)) * g0 ≤ Lin := by rw [hLin]; linarith [hb10, hb20, hb30, hb40]
  have hbL1 : (71659 / (SA:ℝ)) * g1 ≤ Lin := by rw [hLin]; linarith [hb00, hb20, hb30, hb40]
  have hbL2 : (62043 / (SA:ℝ)) * g2 ≤ Lin := by rw [hLin]; linarith [hb00, hb10, hb30, hb40]
  have hbL3 : (71659 / (SA:ℝ)) * g3 ≤ Lin := by rw [hLin]; linarith [hb00, hb10, hb20, hb40]
  have hbL4 : (50125 / (SA:ℝ)) * g4 ≤ Lin := by rw [hLin]; linarith [hb00, hb10, hb20, hb30]
  have haW0 : (25193671 / (SA:ℝ)) * wfun (g0) ≤ Wt := by rw [hWt]; linarith [ha10, ha20, ha30, ha40, ha50, ha60, ha70, ha80, ha90, ha100, ha110, ha120, ha130, ha140]
  have haW1 : (93418335 / (SA:ℝ)) * wfun (g0 + g1) ≤ Wt := by rw [hWt]; linarith [ha00, ha20, ha30, ha40, ha50, ha60, ha70, ha80, ha90, ha100, ha110, ha120, ha130, ha140]
  have haW2 : (54983399 / (SA:ℝ)) * wfun (g0 + g1 + g2) ≤ Wt := by rw [hWt]; linarith [ha00, ha10, ha30, ha40, ha50, ha60, ha70, ha80, ha90, ha100, ha110, ha120, ha130, ha140]
  have haW3 : (100000000 / (SA:ℝ)) * wfun (g0 + g1 + g2 + g3) ≤ Wt := by rw [hWt]; linarith [ha00, ha10, ha20, ha40, ha50, ha60, ha70, ha80, ha90, ha100, ha110, ha120, ha130, ha140]
  have haW4 : (200000000 / (SA:ℝ)) * wfun (g0 + g1 + g2 + g3 + g4) ≤ Wt := by rw [hWt]; linarith [ha00, ha10, ha20, ha30, ha50, ha60, ha70, ha80, ha90, ha100, ha110, ha120, ha130, ha140]
  have haW5 : (49170450 / (SA:ℝ)) * wfun (g1) ≤ Wt := by rw [hWt]; linarith [ha00, ha10, ha20, ha30, ha40, ha60, ha70, ha80, ha90, ha100, ha110, ha120, ha130, ha140]
  have haW6 : (6581664 / (SA:ℝ)) * wfun (g1 + g2) ≤ Wt := by rw [hWt]; linarith [ha00, ha10, ha20, ha30, ha40, ha50, ha70, ha80, ha90, ha100, ha110, ha120, ha130, ha140]
  have haW7 : (90033200 / (SA:ℝ)) * wfun (g1 + g2 + g3) ≤ Wt := by rw [hWt]; linarith [ha00, ha10, ha20, ha30, ha40, ha50, ha60, ha80, ha90, ha100, ha110, ha120, ha130, ha140]
  have haW8 : (100000000 / (SA:ℝ)) * wfun (g1 + g2 + g3 + g4) ≤ Wt := by rw [hWt]; linarith [ha00, ha10, ha20, ha30, ha40, ha50, ha60, ha70, ha90, ha100, ha110, ha120, ha130, ha140]
  have haW9 : (51271755 / (SA:ℝ)) * wfun (g2) ≤ Wt := by rw [hWt]; linarith [ha00, ha10, ha20, ha30, ha40, ha50, ha60, ha70, ha80, ha100, ha110, ha120, ha130, ha140]
  have haW10 : (6581664 / (SA:ℝ)) * wfun (g2 + g3) ≤ Wt := by rw [hWt]; linarith [ha00, ha10, ha20, ha30, ha40, ha50, ha60, ha70, ha80, ha90, ha110, ha120, ha130, ha140]
  have haW11 : (54983399 / (SA:ℝ)) * wfun (g2 + g3 + g4) ≤ Wt := by rw [hWt]; linarith [ha00, ha10, ha20, ha30, ha40, ha50, ha60, ha70, ha80, ha90, ha100, ha120, ha130, ha140]
  have haW12 : (49170450 / (SA:ℝ)) * wfun (g3) ≤ Wt := by rw [hWt]; linarith [ha00, ha10, ha20, ha30, ha40, ha50, ha60, ha70, ha80, ha90, ha100, ha110, ha130, ha140]
  have haW13 : (93418335 / (SA:ℝ)) * wfun (g3 + g4) ≤ Wt := by rw [hWt]; linarith [ha00, ha10, ha20, ha30, ha40, ha50, ha60, ha70, ha80, ha90, ha100, ha110, ha120, ha140]
  have haW14 : (25193671 / (SA:ℝ)) * wfun (g4) ≤ Wt := by rw [hWt]; linarith [ha00, ha10, ha20, ha30, ha40, ha50, ha60, ha70, ha80, ha90, ha100, ha110, ha120, ha130]
  -- gap 0: beyond the cutoff the pressure alone pays
  by_cases hcut0 : (S0 : ℝ) / SC ≤ g0
  · have h1 : (cN : ℝ) / SA ≤ (50125 / (SA:ℝ)) * g0 := by
      have hq := (Nat.cast_le (α := ℝ)).mpr hS0; push_cast at hq
      rw [div_le_iff₀ hSA]
      have e : (50125 / (SA:ℝ)) * g0 * SA = 50125 * g0 := by field_simp
      rw [e]
      calc (cN : ℝ) = (cN : ℝ) * SC / SC := by field_simp
        _ ≤ 50125 * S0 / SC := by apply div_le_div_of_nonneg_right _ hSC.le; linarith
        _ = 50125 * ((S0 : ℝ) / SC) := by ring
        _ ≤ 50125 * g0 := mul_le_mul_of_nonneg_left hcut0 (by norm_num)
    left; rw [hG]; linarith [h1, hbL0, hWt0]
  push_neg at hcut0
  rcases le_total g0 ((SC / 2 : ℕ) / (SC : ℝ)) with hwin0 | hwin0
  · have hw19 := wfun_window g0 hg0 (by rw [hhalf] at hwin0; exact hwin0)
    have hq := (Nat.cast_le (α := ℝ)).mpr hwin; push_cast at hq
    have h1 : (cN : ℝ) / SA ≤ (25193671 / (SA:ℝ)) * wfun g0 := by
      rw [div_le_iff₀ hSA]
      have e : (25193671 / (SA:ℝ)) * wfun g0 * SA = 25193671 * wfun g0 := by field_simp
      rw [e]
      have hm := mul_le_mul_of_nonneg_left hw19 (by norm_num : (0:ℝ) ≤ 25193671)
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
  · have h1 : (cN : ℝ) / SA ≤ (71659 / (SA:ℝ)) * g1 := by
      have hq := (Nat.cast_le (α := ℝ)).mpr hS1; push_cast at hq
      rw [div_le_iff₀ hSA]
      have e : (71659 / (SA:ℝ)) * g1 * SA = 71659 * g1 := by field_simp
      rw [e]
      calc (cN : ℝ) = (cN : ℝ) * SC / SC := by field_simp
        _ ≤ 71659 * S1 / SC := by apply div_le_div_of_nonneg_right _ hSC.le; linarith
        _ = 71659 * ((S1 : ℝ) / SC) := by ring
        _ ≤ 71659 * g1 := mul_le_mul_of_nonneg_left hcut1 (by norm_num)
    left; rw [hG]; linarith [h1, hbL1, hWt0]
  push_neg at hcut1
  rcases le_total g1 ((SC / 2 : ℕ) / (SC : ℝ)) with hwin1 | hwin1
  · have hw19 := wfun_window g1 hg1 (by rw [hhalf] at hwin1; exact hwin1)
    have hq := (Nat.cast_le (α := ℝ)).mpr hwin; push_cast at hq
    have h1 : (cN : ℝ) / SA ≤ (49170450 / (SA:ℝ)) * wfun g1 := by
      rw [div_le_iff₀ hSA]
      have e : (49170450 / (SA:ℝ)) * wfun g1 * SA = 49170450 * wfun g1 := by field_simp
      rw [e]
      have hm := mul_le_mul_of_nonneg_left hw19 (by norm_num : (0:ℝ) ≤ 49170450)
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
  · have h1 : (cN : ℝ) / SA ≤ (62043 / (SA:ℝ)) * g2 := by
      have hq := (Nat.cast_le (α := ℝ)).mpr hS2; push_cast at hq
      rw [div_le_iff₀ hSA]
      have e : (62043 / (SA:ℝ)) * g2 * SA = 62043 * g2 := by field_simp
      rw [e]
      calc (cN : ℝ) = (cN : ℝ) * SC / SC := by field_simp
        _ ≤ 62043 * S2 / SC := by apply div_le_div_of_nonneg_right _ hSC.le; linarith
        _ = 62043 * ((S2 : ℝ) / SC) := by ring
        _ ≤ 62043 * g2 := mul_le_mul_of_nonneg_left hcut2 (by norm_num)
    left; rw [hG]; linarith [h1, hbL2, hWt0]
  push_neg at hcut2
  rcases le_total g2 ((SC / 2 : ℕ) / (SC : ℝ)) with hwin2 | hwin2
  · have hw19 := wfun_window g2 hg2 (by rw [hhalf] at hwin2; exact hwin2)
    have hq := (Nat.cast_le (α := ℝ)).mpr hwin; push_cast at hq
    have h1 : (cN : ℝ) / SA ≤ (51271755 / (SA:ℝ)) * wfun g2 := by
      rw [div_le_iff₀ hSA]
      have e : (51271755 / (SA:ℝ)) * wfun g2 * SA = 51271755 * wfun g2 := by field_simp
      rw [e]
      have hm := mul_le_mul_of_nonneg_left hw19 (by norm_num : (0:ℝ) ≤ 51271755)
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
  · have h1 : (cN : ℝ) / SA ≤ (71659 / (SA:ℝ)) * g3 := by
      have hq := (Nat.cast_le (α := ℝ)).mpr hS3; push_cast at hq
      rw [div_le_iff₀ hSA]
      have e : (71659 / (SA:ℝ)) * g3 * SA = 71659 * g3 := by field_simp
      rw [e]
      calc (cN : ℝ) = (cN : ℝ) * SC / SC := by field_simp
        _ ≤ 71659 * S3 / SC := by apply div_le_div_of_nonneg_right _ hSC.le; linarith
        _ = 71659 * ((S3 : ℝ) / SC) := by ring
        _ ≤ 71659 * g3 := mul_le_mul_of_nonneg_left hcut3 (by norm_num)
    left; rw [hG]; linarith [h1, hbL3, hWt0]
  push_neg at hcut3
  rcases le_total g3 ((SC / 2 : ℕ) / (SC : ℝ)) with hwin3 | hwin3
  · have hw19 := wfun_window g3 hg3 (by rw [hhalf] at hwin3; exact hwin3)
    have hq := (Nat.cast_le (α := ℝ)).mpr hwin; push_cast at hq
    have h1 : (cN : ℝ) / SA ≤ (49170450 / (SA:ℝ)) * wfun g3 := by
      rw [div_le_iff₀ hSA]
      have e : (49170450 / (SA:ℝ)) * wfun g3 * SA = 49170450 * wfun g3 := by field_simp
      rw [e]
      have hm := mul_le_mul_of_nonneg_left hw19 (by norm_num : (0:ℝ) ≤ 49170450)
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
  · have h1 : (cN : ℝ) / SA ≤ (50125 / (SA:ℝ)) * g4 := by
      have hq := (Nat.cast_le (α := ℝ)).mpr hS4; push_cast at hq
      rw [div_le_iff₀ hSA]
      have e : (50125 / (SA:ℝ)) * g4 * SA = 50125 * g4 := by field_simp
      rw [e]
      calc (cN : ℝ) = (cN : ℝ) * SC / SC := by field_simp
        _ ≤ 50125 * S4 / SC := by apply div_le_div_of_nonneg_right _ hSC.le; linarith
        _ = 50125 * ((S4 : ℝ) / SC) := by ring
        _ ≤ 50125 * g4 := mul_le_mul_of_nonneg_left hcut4 (by norm_num)
    left; rw [hG]; linarith [h1, hbL4, hWt0]
  push_neg at hcut4
  rcases le_total g4 ((SC / 2 : ℕ) / (SC : ℝ)) with hwin4 | hwin4
  · have hw19 := wfun_window g4 hg4 (by rw [hhalf] at hwin4; exact hwin4)
    have hq := (Nat.cast_le (α := ℝ)).mpr hwin; push_cast at hq
    have h1 : (cN : ℝ) / SA ≤ (25193671 / (SA:ℝ)) * wfun g4 := by
      rw [div_le_iff₀ hSA]
      have e : (25193671 / (SA:ℝ)) * wfun g4 * SA = 25193671 * wfun g4 := by field_simp
      rw [e]
      have hm := mul_le_mul_of_nonneg_left hw19 (by norm_num : (0:ℝ) ≤ 25193671)
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

def V6 : Riemann.Basin6.Wts6 := ⟨50125, 71659, 62043, 71659, 50125, 25193671, 93418335, 54983399, 100000000, 200000000, 49170450, 6581664, 90033200, 100000000, 51271755, 6581664, 54983399, 49170450, 93418335, 25193671⟩

theorem G_eq (g0 g1 g2 g3 g4 : ℝ) :
    SixW25P.G g0 g1 g2 g3 g4 = Riemann.Basin6.LW6 V6 g0 g1 g2 g3 g4 / SixW25P.SA := by
  simp only [SixW25P.G, Riemann.Basin6.LW6, V6]
  push_cast
  ring

theorem basin_cov (d : Riemann.Basin6.BasinD6) (h : Riemann.Basin6.basinOk6 V6 SixW25P.cN d = true) :
    SixW25P.Covered d.box.l0 d.box.u0 d.box.l1 d.box.u1 d.box.l2 d.box.u2 d.box.l3 d.box.u3 d.box.l4 d.box.u4 := by
  intro g0 g1 g2 g3 g4 h01 h02 h11 h12 h21 h22 h31 h32 h41 h42
  left
  have e : ((SC : ℕ) : ℝ) = 32768 := by norm_num [SC]
  rw [e] at h01 h02 h11 h12 h21 h22 h31 h32 h41 h42
  have hb := Riemann.Basin6.basin6_sound V6 SixW25P.cN d h g0 g1 g2 g3 g4
    ⟨h01, h02, h11, h12, h21, h22, h31, h32, h41, h42⟩
  rw [G_eq]
  have hSA : (0 : ℝ) < SixW25P.SA := by norm_num [SixW25P.SA]
  exact div_le_div_of_nonneg_right hb hSA.le

def bd0 : Riemann.Basin6.BasinD6 := ⟨⟨32552, 35502, 63447, 66397, 32724, 35674, 63447, 66397, 32552, 35502⟩, 4460038523, 8509510798, 4482588361, 8509510794, 4460038527,
    ⟨4266655744, 4294967296, [4653318144], (312468664783 / 500000000000 : ℚ)⟩,
    ⟨12582780928, 12884901888, [13356105728], (939351831 / 12500000000 : ℚ)⟩,
    ⟨16871981056, 17179869184, [18031968256], (-2852732081 / 500000000000 : ℚ)⟩,
    ⟨25188106240, 25769803776, [26734755840], (-1176973583 / 250000000000 : ℚ)⟩,
    ⟨29454761984, 30064771072, [30726422528, 31388073984], (-715054727 / 50000000000 : ℚ)⟩,
    ⟨8316125184, 8589934592, [8702787584], (72932479693 / 250000000000 : ℚ)⟩,
    ⟨12605325312, 12884901888, [13378650112], (34796344073 / 500000000000 : ℚ)⟩,
    ⟨20921450496, 21474836480, [22081437696], (2235127801 / 100000000000 : ℚ)⟩,
    ⟨25188106240, 25769803776, [26734755840], (-1176973583 / 250000000000 : ℚ)⟩,
    ⟨4289200128, 4294967296, [4675862528], (254980839379 / 500000000000 : ℚ)⟩,
    ⟨12605325312, 12884901888, [13378650112], (34796344073 / 500000000000 : ℚ)⟩,
    ⟨16871981056, 17179869184, [18031968256], (-2852732081 / 500000000000 : ℚ)⟩,
    ⟨8316125184, 8589934592, [8702787584], (72932479693 / 250000000000 : ℚ)⟩,
    ⟨12582780928, 12884901888, [13356105728], (939351831 / 12500000000 : ℚ)⟩,
    ⟨4266655744, 4294967296, [4653318144], (312468664783 / 500000000000 : ℚ)⟩⟩

theorem bas0 : SixW25P.Covered bd0.box.l0 bd0.box.u0 bd0.box.l1 bd0.box.u1 bd0.box.l2 bd0.box.u2 bd0.box.l3 bd0.box.u3 bd0.box.l4 bd0.box.u4 :=
  basin_cov bd0 (by decide +kernel)

def bd1 : Riemann.Basin6.BasinD6 := ⟨⟨63521, 66471, 32741, 35691, 63483, 66433, 32741, 35691, 63521, 66471⟩, 8519190090, 4484703874, 8514162388, 4484703865, 8519190098,
    ⟨8325824512, 8589934592, [8712486912], (148094137667 / 500000000000 : ℚ)⟩,
    ⟨12617252864, 12884901888, [13390577664], (8326023181 / 125000000000 : ℚ)⟩,
    ⟨20938096640, 21474836480, [22098083840], (10489452667 / 500000000000 : ℚ)⟩,
    ⟨25229524992, 25769803776, [26776174592], (-3678359733 / 500000000000 : ℚ)⟩,
    ⟨33555349504, 34359738368, [34924199936, 35488661504], (-284981511 / 62500000000 : ℚ)⟩,
    ⟨4291428352, 4294967296, [4678090752], (6231005467 / 12500000000 : ℚ)⟩,
    ⟨12612272128, 12884901888, [13385596928], (33929105093 / 500000000000 : ℚ)⟩,
    ⟨16903700480, 17179869184, [18063687680], (-2652339559 / 250000000000 : ℚ)⟩,
    ⟨25229524992, 25769803776, [26776174592], (-3678359733 / 500000000000 : ℚ)⟩,
    ⟨8320843776, 8589934592, [8707506176], (73477698669 / 250000000000 : ℚ)⟩,
    ⟨12612272128, 12884901888, [13385596928], (33929105093 / 500000000000 : ℚ)⟩,
    ⟨20938096640, 21474836480, [22098083840], (10489452667 / 500000000000 : ℚ)⟩,
    ⟨4291428352, 4294967296, [4678090752], (6231005467 / 12500000000 : ℚ)⟩,
    ⟨12617252864, 12884901888, [13390577664], (8326023181 / 125000000000 : ℚ)⟩,
    ⟨8325824512, 8589934592, [8712486912], (148094137667 / 500000000000 : ℚ)⟩⟩

theorem bas1 : SixW25P.Covered bd1.box.l0 bd1.box.u0 bd1.box.l1 bd1.box.u1 bd1.box.l2 bd1.box.u2 bd1.box.l3 bd1.box.u3 bd1.box.l4 bd1.box.u4 :=
  basin_cov bd1 (by decide +kernel)

def bd2 : Riemann.Basin6.BasinD6 := ⟨⟨32569, 35519, 63120, 66070, 32575, 35525, 32630, 35580, 63238, 66188⟩, 4462186109, 8466545361, 4463041671, 4470203332, 8482001924,
    ⟨4268883968, 4294967296, [4655546368], (599287663 / 976562500 : ℚ)⟩,
    ⟨12542148608, 12884901888, [13315473408], (21216714163 / 250000000000 : ℚ)⟩,
    ⟨16811819008, 17179869184, [17971806208], (434891191 / 125000000000 : ℚ)⟩,
    ⟨21088698368, 21474836480, [22055092224, 22635347968], (-9314457847 / 500000000000 : ℚ)⟩,
    ⟨29377429504, 30064771072, [30687756288, 31310741504], (-1409423823 / 125000000000 : ℚ)⟩,
    ⟨8273264640, 8589934592, [8659927040], (135440421831 / 500000000000 : ℚ)⟩,
    ⟨12542935040, 12884901888, [13316259840], (423412273 / 5000000000 : ℚ)⟩,
    ⟨16819814400, 17179869184, [17979801600], (226880563 / 100000000000 : ℚ)⟩,
    ⟨25108545536, 25769803776, [26655195136], (42954497 / 125000000000 : ℚ)⟩,
    ⟨4269670400, 4294967296, [4656332800], (304844469089 / 500000000000 : ℚ)⟩,
    ⟨8546549760, 8589934592, [9319874560], (-33893883881 / 500000000000 : ℚ)⟩,
    ⟨16835280896, 17179869184, [17995268096], (-8198949 / 100000000000 : ℚ)⟩,
    ⟨4276879360, 4294967296, [4663541760], (143266645603 / 250000000000 : ℚ)⟩,
    ⟨12565610496, 12884901888, [13338935296], (9912769703 / 125000000000 : ℚ)⟩,
    ⟨8288731136, 8589934592, [8675393536], (139310337913 / 500000000000 : ℚ)⟩⟩

theorem bas2 : SixW25P.Covered bd2.box.l0 bd2.box.u0 bd2.box.l1 bd2.box.u1 bd2.box.l2 bd2.box.u2 bd2.box.l3 bd2.box.u3 bd2.box.l4 bd2.box.u4 :=
  basin_cov bd2 (by decide +kernel)

def bd3 : Riemann.Basin6.BasinD6 := ⟨⟨32015, 34965, 32401, 35351, 63260, 66210, 32722, 35672, 63477, 66427⟩, 4389594359, 4440223524, 8485002558, 4482332261, 8513432075,
    ⟨4196270080, 4294967296, [4582932480], (121186022721 / 125000000000 : ℚ)⟩,
    ⟨8443133952, 8589934592, [9216458752], (13545487 / 1000000000 : ℚ)⟩,
    ⟨16734748672, 17179869184, [17894735872], (3736623309 / 250000000000 : ℚ)⟩,
    ⟨21023686656, 21474836480, [22022586368, 22570336256], (-165464791 / 12500000000 : ℚ)⟩,
    ⟨29343744000, 30064771072, [30670913536, 31277056000], (-2479569489 / 250000000000 : ℚ)⟩,
    ⟨4246863872, 4294967296, [4633526272], (362031304257 / 500000000000 : ℚ)⟩,
    ⟨12538478592, 12884901888, [13311803392], (8572542631 / 100000000000 : ℚ)⟩,
    ⟨16827416576, 17179869184, [17987403776], (278714519 / 250000000000 : ℚ)⟩,
    ⟨25147473920, 25769803776, [26694123520], (-105975127 / 50000000000 : ℚ)⟩,
    ⟨8291614720, 8589934592, [8678277120], (70009162171 / 250000000000 : ℚ)⟩,
    ⟨12580552704, 12884901888, [13353877504], (18922758347 / 250000000000 : ℚ)⟩,
    ⟨20900610048, 21474836480, [22060597248], (12022064421 / 500000000000 : ℚ)⟩,
    ⟨4288937984, 4294967296, [4675600384], (255655518597 / 500000000000 : ℚ)⟩,
    ⟨12608995328, 12884901888, [13382320128], (4292354323 / 62500000000 : ℚ)⟩,
    ⟨8320057344, 8589934592, [8706719744], (36693610959 / 125000000000 : ℚ)⟩⟩

theorem bas3 : SixW25P.Covered bd3.box.l0 bd3.box.u0 bd3.box.l1 bd3.box.u1 bd3.box.l2 bd3.box.u2 bd3.box.l3 bd3.box.u3 bd3.box.l4 bd3.box.u4 :=
  basin_cov bd3 (by decide +kernel)

def bd4 : Riemann.Basin6.BasinD6 := ⟨⟨32648, 35598, 63692, 66642, 63894, 66844, 32835, 35785, 63510, 66460⟩, 4472617463, 8541577987, 8568072348, 4497072326, 8517659225,
    ⟨4279238656, 4294967296, [4665901056], (35064542309 / 62500000000 : ℚ)⟩,
    ⟨12627476480, 12884901888, [13400801280], (32012856091 / 500000000000 : ℚ)⟩,
    ⟨21002190848, 21474836480, [22162178048], (3884930987 / 250000000000 : ℚ)⟩,
    ⟨25305939968, 25769803776, [26311196672, 26852589568], (-71322939 / 10000000000 : ℚ)⟩,
    ⟨33630322688, 34359738368, [34961686528, 35563634688], (-865123199 / 125000000000 : ℚ)⟩,
    ⟨8348237824, 8589934592, [8734900224], (153062729603 / 500000000000 : ℚ)⟩,
    ⟨16722952192, 17179869184, [17496276992], (28662113011 / 500000000000 : ℚ)⟩,
    ⟨21026701312, 21474836480, [22186688512], (1340031789 / 100000000000 : ℚ)⟩,
    ⟨29351084032, 30064771072, [30897733632], (458337643 / 125000000000 : ℚ)⟩,
    ⟨8374714368, 8589934592, [8761376768], (19193681639 / 62500000000 : ℚ)⟩,
    ⟨12678463488, 12884901888, [13451788288], (25412645099 / 500000000000 : ℚ)⟩,
    ⟨21002846208, 21474836480, [22162833408], (7741461339 / 500000000000 : ℚ)⟩,
    ⟨4303749120, 4690411520, [], (225953918933 / 500000000000 : ℚ)⟩,
    ⟨12628131840, 12884901888, [13401456640], (798242663 / 12500000000 : ℚ)⟩,
    ⟨8324382720, 8589934592, [8711045120], (73882899211 / 250000000000 : ℚ)⟩⟩

theorem bas4 : SixW25P.Covered bd4.box.l0 bd4.box.u0 bd4.box.l1 bd4.box.u1 bd4.box.l2 bd4.box.u2 bd4.box.l3 bd4.box.u3 bd4.box.l4 bd4.box.u4 :=
  basin_cov bd4 (by decide +kernel)

def bd5 : Riemann.Basin6.BasinD6 := ⟨⟨32017, 34967, 32479, 35429, 63677, 66627, 63661, 66611, 32621, 35571⟩, 4389912735, 4450447938, 8539588373, 8537515174, 4469004860,
    ⟨4196532224, 4294967296, [4583194624], (96824677509 / 100000000000 : ℚ)⟩,
    ⟨8453619712, 8589934592, [9226944512], (2741043787 / 500000000000 : ℚ)⟩,
    ⟨16799891456, 17179869184, [17959878656], (527811171 / 100000000000 : ℚ)⟩,
    ⟨25144066048, 25769803776, [26690715648], (-951558939 / 500000000000 : ℚ)⟩,
    ⟨29419765760, 30064771072, [30708924416, 31353077760], (-6474374553 / 500000000000 : ℚ)⟩,
    ⟨4257087488, 4294967296, [4643749888], (336536505163 / 500000000000 : ℚ)⟩,
    ⟨12603359232, 12884901888, [13376684032], (273756503 / 3906250000 : ℚ)⟩,
    ⟨20947533824, 21474836480, [22107521024], (2019316627 / 100000000000 : ℚ)⟩,
    ⟨25223233536, 25769803776, [26769883136], (-3477010477 / 500000000000 : ℚ)⟩,
    ⟨8346271744, 8589934592, [8732934144], (19079633619 / 62500000000 : ℚ)⟩,
    ⟨16690446336, 17179869184, [17463771136], (6708166141 / 125000000000 : ℚ)⟩,
    ⟨20966146048, 21474836480, [22126133248], (9313873003 / 500000000000 : ℚ)⟩,
    ⟨8344174592, 8589934592, [8730836992], (30436175103 / 100000000000 : ℚ)⟩,
    ⟨12619874304, 12884901888, [13393199104], (32974067997 / 500000000000 : ℚ)⟩,
    ⟨4275699712, 4294967296, [4662362112], (144768651023 / 250000000000 : ℚ)⟩⟩

theorem bas5 : SixW25P.Covered bd5.box.l0 bd5.box.u0 bd5.box.l1 bd5.box.u1 bd5.box.l2 bd5.box.u2 bd5.box.l3 bd5.box.u3 bd5.box.l4 bd5.box.u4 :=
  basin_cov bd5 (by decide +kernel)

def bd6 : Riemann.Basin6.BasinD6 := ⟨⟨32621, 35571, 63661, 66611, 63677, 66627, 32479, 35429, 32017, 34967⟩, 4469004868, 8537515179, 8539588371, 4450447940, 4389912737,
    ⟨4275699712, 4294967296, [4662362112], (144768651023 / 250000000000 : ℚ)⟩,
    ⟨12619874304, 12884901888, [13393199104], (32974067997 / 500000000000 : ℚ)⟩,
    ⟨20966146048, 21474836480, [22126133248], (9313873003 / 500000000000 : ℚ)⟩,
    ⟨25223233536, 25769803776, [26769883136], (-3477010477 / 500000000000 : ℚ)⟩,
    ⟨29419765760, 30064771072, [30708924416, 31353077760], (-6474374553 / 500000000000 : ℚ)⟩,
    ⟨8344174592, 8589934592, [8730836992], (30436175103 / 100000000000 : ℚ)⟩,
    ⟨16690446336, 17179869184, [17463771136], (6708166141 / 125000000000 : ℚ)⟩,
    ⟨20947533824, 21474836480, [22107521024], (2019316627 / 100000000000 : ℚ)⟩,
    ⟨25144066048, 25769803776, [26690715648], (-951558939 / 500000000000 : ℚ)⟩,
    ⟨8346271744, 8589934592, [8732934144], (19079633619 / 62500000000 : ℚ)⟩,
    ⟨12603359232, 12884901888, [13376684032], (273756503 / 3906250000 : ℚ)⟩,
    ⟨16799891456, 17179869184, [17959878656], (527811171 / 100000000000 : ℚ)⟩,
    ⟨4257087488, 4294967296, [4643749888], (336536505163 / 500000000000 : ℚ)⟩,
    ⟨8453619712, 8589934592, [9226944512], (2741043787 / 500000000000 : ℚ)⟩,
    ⟨4196532224, 4294967296, [4583194624], (96824677509 / 100000000000 : ℚ)⟩⟩

theorem bas6 : SixW25P.Covered bd6.box.l0 bd6.box.u0 bd6.box.l1 bd6.box.u1 bd6.box.l2 bd6.box.u2 bd6.box.l3 bd6.box.u3 bd6.box.l4 bd6.box.u4 :=
  basin_cov bd6 (by decide +kernel)

def bd7 : Riemann.Basin6.BasinD6 := ⟨⟨31984, 34934, 32384, 35334, 63032, 65982, 32384, 35334, 31984, 34934⟩, 4385581218, 4437963202, 8455065229, 4437963204, 4385581214,
    ⟨4192206848, 4294967296, [4578869248], (494344504697 / 500000000000 : ℚ)⟩,
    ⟨8436842496, 8589934592, [9210167296], (918095001 / 50000000000 : ℚ)⟩,
    ⟨16698572800, 17179869184, [17858560000], (2018417129 / 100000000000 : ℚ)⟩,
    ⟨20943208448, 21474836480, [22489858048], (-7377848167 / 500000000000 : ℚ)⟩,
    ⟨25135415296, 25769803776, [26419265536, 27068727296], (-9590766867 / 500000000000 : ℚ)⟩,
    ⟨4244635648, 4294967296, [4631298048], (367557242367 / 500000000000 : ℚ)⟩,
    ⟨12506365952, 12884901888, [13279690752], (1454640089 / 15625000000 : ℚ)⟩,
    ⟨16751001600, 17179869184, [17910988800], (6280537091 / 500000000000 : ℚ)⟩,
    ⟨20943208448, 21474836480, [22489858048], (-7377848167 / 500000000000 : ℚ)⟩,
    ⟨8261730304, 8589934592, [8648392704], (13247468511 / 50000000000 : ℚ)⟩,
    ⟨12506365952, 12884901888, [13279690752], (1454640089 / 15625000000 : ℚ)⟩,
    ⟨16698572800, 17179869184, [17858560000], (2018417129 / 100000000000 : ℚ)⟩,
    ⟨4244635648, 4294967296, [4631298048], (367557242367 / 500000000000 : ℚ)⟩,
    ⟨8436842496, 8589934592, [9210167296], (918095001 / 50000000000 : ℚ)⟩,
    ⟨4192206848, 4294967296, [4578869248], (494344504697 / 500000000000 : ℚ)⟩⟩

theorem bas7 : SixW25P.Covered bd7.box.l0 bd7.box.u0 bd7.box.l1 bd7.box.u1 bd7.box.l2 bd7.box.u2 bd7.box.l3 bd7.box.u3 bd7.box.l4 bd7.box.u4 :=
  basin_cov bd7 (by decide +kernel)

def bd8 : Riemann.Basin6.BasinD6 := ⟨⟨64124, 67074, 63602, 66552, 32644, 35594, 32654, 35604, 63287, 66237⟩, 8598249579, 8529740501, 4472012748, 4473388010, 8488516528,
    ⟨8404860928, 8589934592, [8791523328], (145806871297 / 500000000000 : ℚ)⟩,
    ⟨16741302272, 17179869184, [17514627072], (14827250783 / 250000000000 : ℚ)⟩,
    ⟨21020016640, 21474836480, [22180003840], (87417531 / 6250000000 : ℚ)⟩,
    ⟨25300041728, 25769803776, [26308247552, 26846691328], (-848967609 / 125000000000 : ℚ)⟩,
    ⟨33595195392, 34359738368, [34944122880, 35528507392], (-2910790611 / 500000000000 : ℚ)⟩,
    ⟨8336441344, 8589934592, [8723103744], (75239709071 / 250000000000 : ℚ)⟩,
    ⟨12615155712, 12884901888, [13388480512], (16783790821 / 250000000000 : ℚ)⟩,
    ⟨16895180800, 17179869184, [18055168000], (-4644366559 / 500000000000 : ℚ)⟩,
    ⟨25190334464, 25769803776, [26736984064], (-606275231 / 125000000000 : ℚ)⟩,
    ⟨4278714368, 4294967296, [4665376768], (281854466957 / 500000000000 : ℚ)⟩,
    ⟨8558739456, 8589934592, [9332064256], (-7761656733 / 100000000000 : ℚ)⟩,
    ⟨16853893120, 17179869184, [18013880320], (-58528263 / 20000000000 : ℚ)⟩,
    ⟨4280025088, 4294967296, [4666687488], (69627011449 / 125000000000 : ℚ)⟩,
    ⟨12575178752, 12884901888, [13348503552], (962446103 / 12500000000 : ℚ)⟩,
    ⟨8295153664, 8589934592, [8681816064], (17610176717 / 62500000000 : ℚ)⟩⟩

theorem bas8 : SixW25P.Covered bd8.box.l0 bd8.box.u0 bd8.box.l1 bd8.box.u1 bd8.box.l2 bd8.box.u2 bd8.box.l3 bd8.box.u3 bd8.box.l4 bd8.box.u4 :=
  basin_cov bd8 (by decide +kernel)

def bd9 : Riemann.Basin6.BasinD6 := ⟨⟨63287, 66237, 32654, 35604, 32644, 35594, 63602, 66552, 64124, 67074⟩, 8488516525, 4473388008, 4472012754, 8529740489, 8598249588,
    ⟨8295153664, 8589934592, [8681816064], (17610176717 / 62500000000 : ℚ)⟩,
    ⟨12575178752, 12884901888, [13348503552], (962446103 / 12500000000 : ℚ)⟩,
    ⟨16853893120, 17179869184, [18013880320], (-58528263 / 20000000000 : ℚ)⟩,
    ⟨25190334464, 25769803776, [26736984064], (-606275231 / 125000000000 : ℚ)⟩,
    ⟨33595195392, 34359738368, [34944122880, 35528507392], (-2910790611 / 500000000000 : ℚ)⟩,
    ⟨4280025088, 4294967296, [4666687488], (69627011449 / 125000000000 : ℚ)⟩,
    ⟨8558739456, 8589934592, [9332064256], (-7761656733 / 100000000000 : ℚ)⟩,
    ⟨16895180800, 17179869184, [18055168000], (-4644366559 / 500000000000 : ℚ)⟩,
    ⟨25300041728, 25769803776, [26308247552, 26846691328], (-848967609 / 125000000000 : ℚ)⟩,
    ⟨4278714368, 4294967296, [4665376768], (281854466957 / 500000000000 : ℚ)⟩,
    ⟨12615155712, 12884901888, [13388480512], (16783790821 / 250000000000 : ℚ)⟩,
    ⟨21020016640, 21474836480, [22180003840], (87417531 / 6250000000 : ℚ)⟩,
    ⟨8336441344, 8589934592, [8723103744], (75239709071 / 250000000000 : ℚ)⟩,
    ⟨16741302272, 17179869184, [17514627072], (14827250783 / 250000000000 : ℚ)⟩,
    ⟨8404860928, 8589934592, [8791523328], (145806871297 / 500000000000 : ℚ)⟩⟩

theorem bas9 : SixW25P.Covered bd9.box.l0 bd9.box.u0 bd9.box.l1 bd9.box.u1 bd9.box.l2 bd9.box.u2 bd9.box.l3 bd9.box.u3 bd9.box.l4 bd9.box.u4 :=
  basin_cov bd9 (by decide +kernel)

def bd10 : Riemann.Basin6.BasinD6 := ⟨⟨32526, 35476, 63030, 65980, 32438, 35388, 32253, 35203, 31843, 34793⟩, 4456639760, 8454857557, 4445076359, 4420787876, 4367068806,
    ⟨4263247872, 4294967296, [4649910272], (321063616773 / 500000000000 : ℚ)⟩,
    ⟨12524716032, 12884901888, [13298040832], (44457937867 / 500000000000 : ℚ)⟩,
    ⟨16776429568, 17179869184, [17936416768], (549516467 / 62500000000 : ℚ)⟩,
    ⟨21003894784, 21474836480, [22012690432, 22550544384], (-5788812891 / 500000000000 : ℚ)⟩,
    ⟨25177620480, 25769803776, [26440368128, 27110932480], (-10692447049 / 500000000000 : ℚ)⟩,
    ⟨8261468160, 8589934592, [8648130560], (26481297957 / 100000000000 : ℚ)⟩,
    ⟨12513181696, 12884901888, [13286506496], (45776907713 / 500000000000 : ℚ)⟩,
    ⟨16740646912, 17179869184, [17900634112], (880189103 / 62500000000 : ℚ)⟩,
    ⟨20914372608, 21474836480, [22461022208], (-3001823119 / 250000000000 : ℚ)⟩,
    ⟨4251713536, 4294967296, [4638375936], (13998652259 / 20000000000 : ℚ)⟩,
    ⟨8479178752, 8589934592, [9252503552], (-287106387 / 20000000000 : ℚ)⟩,
    ⟨12652904448, 12884901888, [13812891648], (-2686676093 / 50000000000 : ℚ)⟩,
    ⟨4227465216, 4294967296, [4614127616], (8195359533 / 10000000000 : ℚ)⟩,
    ⟨8401190912, 8589934592, [9174515712], (1416777247 / 31250000000 : ℚ)⟩,
    ⟨4173725696, 4294967296, [4560388096], (67190227437 / 62500000000 : ℚ)⟩⟩

theorem bas10 : SixW25P.Covered bd10.box.l0 bd10.box.u0 bd10.box.l1 bd10.box.u1 bd10.box.l2 bd10.box.u2 bd10.box.l3 bd10.box.u3 bd10.box.l4 bd10.box.u4 :=
  basin_cov bd10 (by decide +kernel)

def bd11 : Riemann.Basin6.BasinD6 := ⟨⟨31843, 34793, 32253, 35203, 32438, 35388, 63030, 65980, 32526, 35476⟩, 4367068793, 4420787877, 4445076359, 8454857556, 4456639759,
    ⟨4173725696, 4294967296, [4560388096], (67190227437 / 62500000000 : ℚ)⟩,
    ⟨8401190912, 8589934592, [9174515712], (1416777247 / 31250000000 : ℚ)⟩,
    ⟨12652904448, 12884901888, [13812891648], (-2686676093 / 50000000000 : ℚ)⟩,
    ⟨20914372608, 21474836480, [22461022208], (-3001823119 / 250000000000 : ℚ)⟩,
    ⟨25177620480, 25769803776, [26440368128, 27110932480], (-10692447049 / 500000000000 : ℚ)⟩,
    ⟨4227465216, 4294967296, [4614127616], (8195359533 / 10000000000 : ℚ)⟩,
    ⟨8479178752, 8589934592, [9252503552], (-287106387 / 20000000000 : ℚ)⟩,
    ⟨16740646912, 17179869184, [17900634112], (880189103 / 62500000000 : ℚ)⟩,
    ⟨21003894784, 21474836480, [22012690432, 22550544384], (-5788812891 / 500000000000 : ℚ)⟩,
    ⟨4251713536, 4294967296, [4638375936], (13998652259 / 20000000000 : ℚ)⟩,
    ⟨12513181696, 12884901888, [13286506496], (45776907713 / 500000000000 : ℚ)⟩,
    ⟨16776429568, 17179869184, [17936416768], (549516467 / 62500000000 : ℚ)⟩,
    ⟨8261468160, 8589934592, [8648130560], (26481297957 / 100000000000 : ℚ)⟩,
    ⟨12524716032, 12884901888, [13298040832], (44457937867 / 500000000000 : ℚ)⟩,
    ⟨4263247872, 4294967296, [4649910272], (321063616773 / 500000000000 : ℚ)⟩⟩

theorem bas11 : SixW25P.Covered bd11.box.l0 bd11.box.u0 bd11.box.l1 bd11.box.u1 bd11.box.l2 bd11.box.u2 bd11.box.l3 bd11.box.u3 bd11.box.l4 bd11.box.u4 :=
  basin_cov bd11 (by decide +kernel)

def bd12 : Riemann.Basin6.BasinD6 := ⟨⟨32581, 35531, 63484, 66434, 32785, 35735, 63984, 66934, 64060, 67010⟩, 4463820389, 8514317419, 4490520554, 8579901747, 8589763354,
    ⟨4270456832, 4294967296, [4657119232], (302852319899 / 500000000000 : ℚ)⟩,
    ⟨12591431680, 12884901888, [13364756480], (36514910761 / 500000000000 : ℚ)⟩,
    ⟨16888627200, 17179869184, [18048614400], (-1034315979 / 125000000000 : ℚ)⟩,
    ⟨25275138048, 25769803776, [26821787648], (-321123613 / 31250000000 : ℚ)⟩,
    ⟨33671610368, 34359738368, [34982330368, 35604922368], (-256062997 / 31250000000 : ℚ)⟩,
    ⟨8320974848, 8589934592, [8707637248], (18373190711 / 62500000000 : ℚ)⟩,
    ⟨12618170368, 12884901888, [13391495168], (1659433389 / 25000000000 : ℚ)⟩,
    ⟨21004681216, 21474836480, [22164668416], (153237591 / 10000000000 : ℚ)⟩,
    ⟨29401153536, 30064771072, [30947803136], (711975239 / 500000000000 : ℚ)⟩,
    ⟨4297195520, 4683857920, [], (59124624801 / 125000000000 : ℚ)⟩,
    ⟨12683706368, 12884901888, [13457031168], (24719408399 / 500000000000 : ℚ)⟩,
    ⟨21080178688, 21474836480, [22240165888], (2158387063 / 250000000000 : ℚ)⟩,
    ⟨8386510848, 8589934592, [8773173248], (150559622229 / 500000000000 : ℚ)⟩,
    ⟨16782983168, 17179869184, [17556307968], (7337644849 / 125000000000 : ℚ)⟩,
    ⟨8396472320, 8589934592, [8783134720], (73997412747 / 250000000000 : ℚ)⟩⟩

theorem bas12 : SixW25P.Covered bd12.box.l0 bd12.box.u0 bd12.box.l1 bd12.box.u1 bd12.box.l2 bd12.box.u2 bd12.box.l3 bd12.box.u3 bd12.box.l4 bd12.box.u4 :=
  basin_cov bd12 (by decide +kernel)

def bd13 : Riemann.Basin6.BasinD6 := ⟨⟨32641, 35591, 63854, 66804, 64155, 67105, 63854, 66804, 32641, 35591⟩, 4471670140, 8562828537, 8602253097, 8562828546, 4471670139,
    ⟨4278321152, 4294967296, [4664983552], (141428839043 / 250000000000 : ℚ)⟩,
    ⟨12647792640, 12884901888, [13421117440], (1838401183 / 31250000000 : ℚ)⟩,
    ⟨21056716800, 21474836480, [22216704000], (1074056811 / 100000000000 : ℚ)⟩,
    ⟨29426188288, 30064771072, [30972837888], (14532419 / 50000000000 : ℚ)⟩,
    ⟨33704509440, 34359738368, [34998779904, 35637821440], (-2297666279 / 250000000000 : ℚ)⟩,
    ⟨8369471488, 8589934592, [8756133888], (77430797593 / 250000000000 : ℚ)⟩,
    ⟨16778395648, 17179869184, [17551720448], (29598395263 / 500000000000 : ℚ)⟩,
    ⟨25147867136, 25769803776, [26307854336], (4711925047 / 250000000000 : ℚ)⟩,
    ⟨29426188288, 30064771072, [30972837888], (14532419 / 50000000000 : ℚ)⟩,
    ⟨8408924160, 8589934592, [8795586560], (72368957743 / 250000000000 : ℚ)⟩,
    ⟨16778395648, 17179869184, [17551720448], (29598395263 / 500000000000 : ℚ)⟩,
    ⟨21056716800, 21474836480, [22216704000], (1074056811 / 100000000000 : ℚ)⟩,
    ⟨8369471488, 8589934592, [8756133888], (77430797593 / 250000000000 : ℚ)⟩,
    ⟨12647792640, 12884901888, [13421117440], (1838401183 / 31250000000 : ℚ)⟩,
    ⟨4278321152, 4294967296, [4664983552], (141428839043 / 250000000000 : ℚ)⟩⟩

theorem bas13 : SixW25P.Covered bd13.box.l0 bd13.box.u0 bd13.box.l1 bd13.box.u1 bd13.box.l2 bd13.box.u2 bd13.box.l3 bd13.box.u3 bd13.box.l4 bd13.box.u4 :=
  basin_cov bd13 (by decide +kernel)

def bd14 : Riemann.Basin6.BasinD6 := ⟨⟨32071, 35021, 32513, 35463, 95068, 98018, 32513, 35463, 32071, 35021⟩, 4396881035, 4454842168, 12654146654, 4454842169, 4396881033,
    ⟨4203610112, 4294967296, [4590272512], (233652025351 / 250000000000 : ℚ)⟩,
    ⟨8465154048, 8589934592, [9238478848], (-343860837 / 100000000000 : ℚ)⟩,
    ⟨20925906944, 21474836480, [22085894144], (1374099929 / 62500000000 : ℚ)⟩,
    ⟨25187450880, 25769803776, [26734100480], (-46660449 / 10000000000 : ℚ)⟩,
    ⟨29391060992, 30064771072, [30694572032, 31324372992], (-738643709 / 62500000000 : ℚ)⟩,
    ⟨4261543936, 4294967296, [4648206336], (325351630547 / 500000000000 : ℚ)⟩,
    ⟨16722296832, 17179869184, [17495621632], (3578265937 / 62500000000 : ℚ)⟩,
    ⟨20983840768, 21474836480, [22143827968], (1712081059 / 100000000000 : ℚ)⟩,
    ⟨25187450880, 25769803776, [26734100480], (-46660449 / 10000000000 : ℚ)⟩,
    ⟨12460752896, 12847415296, [], (26690792989 / 250000000000 : ℚ)⟩,
    ⟨16722296832, 17179869184, [17495621632], (3578265937 / 62500000000 : ℚ)⟩,
    ⟨20925906944, 21474836480, [22085894144], (1374099929 / 62500000000 : ℚ)⟩,
    ⟨4261543936, 4294967296, [4648206336], (325351630547 / 500000000000 : ℚ)⟩,
    ⟨8465154048, 8589934592, [9238478848], (-343860837 / 100000000000 : ℚ)⟩,
    ⟨4203610112, 4294967296, [4590272512], (233652025351 / 250000000000 : ℚ)⟩⟩

theorem bas14 : SixW25P.Covered bd14.box.l0 bd14.box.u0 bd14.box.l1 bd14.box.u1 bd14.box.l2 bd14.box.u2 bd14.box.l3 bd14.box.u3 bd14.box.l4 bd14.box.u4 :=
  basin_cov bd14 (by decide +kernel)

def basList : List Riemann.Basin6.Box6 := [⟨32552, 35502, 63447, 66397, 32724, 35674, 63447, 66397, 32552, 35502⟩, ⟨63521, 66471, 32741, 35691, 63483, 66433, 32741, 35691, 63521, 66471⟩, ⟨32569, 35519, 63120, 66070, 32575, 35525, 32630, 35580, 63238, 66188⟩, ⟨32015, 34965, 32401, 35351, 63260, 66210, 32722, 35672, 63477, 66427⟩, ⟨32648, 35598, 63692, 66642, 63894, 66844, 32835, 35785, 63510, 66460⟩, ⟨32017, 34967, 32479, 35429, 63677, 66627, 63661, 66611, 32621, 35571⟩, ⟨32621, 35571, 63661, 66611, 63677, 66627, 32479, 35429, 32017, 34967⟩, ⟨31984, 34934, 32384, 35334, 63032, 65982, 32384, 35334, 31984, 34934⟩, ⟨64124, 67074, 63602, 66552, 32644, 35594, 32654, 35604, 63287, 66237⟩, ⟨63287, 66237, 32654, 35604, 32644, 35594, 63602, 66552, 64124, 67074⟩, ⟨32526, 35476, 63030, 65980, 32438, 35388, 32253, 35203, 31843, 34793⟩, ⟨31843, 34793, 32253, 35203, 32438, 35388, 63030, 65980, 32526, 35476⟩, ⟨32581, 35531, 63484, 66434, 32785, 35735, 63984, 66934, 64060, 67010⟩, ⟨32641, 35591, 63854, 66804, 64155, 67105, 63854, 66804, 32641, 35591⟩, ⟨32071, 35021, 32513, 35463, 95068, 98018, 32513, 35463, 32071, 35021⟩]

theorem hbas : ∀ B ∈ basList, SixW25P.Covered B.l0 B.u0 B.l1 B.u1 B.l2 B.u2 B.l3 B.u3 B.l4 B.u4 := by
  intro B hB
  simp only [basList, List.mem_cons, List.not_mem_nil, or_false] at hB
  rcases hB with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [bas0, bas1, bas2, bas3, bas4, bas5, bas6, bas7, bas8, bas9, bas10, bas11, bas12, bas13, bas14]

def cover0 : List (ℕ × ℕ × Bool) := [
  (16384, 20480, true),
  (20480, 24576, true),
  (24576, 28672, true),
  (28672, 29696, true),
  (29696, 29824, true),
  (29824, 29840, true),
  (29840, 29848, true),
  (29848, 42312, false),
  (42312, 42320, true),
  (42320, 42336, true),
  (42336, 42368, true),
  (42368, 42432, true),
  (42432, 42496, true),
  (42496, 42752, true),
  (42752, 43008, true),
  (43008, 44032, true),
  (44032, 45056, true),
  (45056, 47104, true),
  (47104, 49152, true),
  (49152, 51200, true),
  (51200, 53248, true),
  (53248, 53760, true),
  (53760, 54272, true),
  (54272, 54528, true),
  (54528, 54656, true),
  (54656, 54688, true),
  (54688, 54720, true),
  (54720, 54736, true),
  (54736, 358256, false)]

theorem cover0_ok : SixW25P.coverCheck 25193671 (SC / 2) 358256 cover0 = true := by decide +kernel

def cover1 : List (ℕ × ℕ × Bool) := [
  (16384, 20480, true),
  (20480, 24576, true),
  (24576, 28672, true),
  (28672, 30720, true),
  (30720, 30976, true),
  (30976, 31040, true),
  (31040, 31072, true),
  (31072, 31088, true),
  (31088, 31096, true),
  (31096, 39408, false),
  (39408, 39424, true),
  (39424, 39488, true),
  (39488, 39552, true),
  (39552, 39680, true),
  (39680, 39936, true),
  (39936, 40960, true),
  (40960, 45056, true),
  (45056, 49152, true),
  (49152, 53248, true),
  (53248, 57344, true),
  (57344, 57856, true),
  (57856, 58368, true),
  (58368, 58496, true),
  (58496, 58528, true),
  (58528, 58544, true),
  (58544, 58552, true),
  (58552, 80144, false),
  (80144, 80152, true),
  (80152, 80160, true),
  (80160, 80176, true),
  (80176, 80192, true),
  (80192, 80208, true),
  (80208, 80224, true),
  (80224, 80256, true),
  (80256, 80288, true),
  (80288, 80320, true),
  (80320, 80384, true),
  (80384, 80448, true),
  (80448, 80512, true),
  (80512, 80640, true),
  (80640, 80768, true),
  (80768, 80896, true),
  (80896, 81152, true),
  (81152, 81408, true),
  (81408, 81664, true),
  (81664, 81920, true),
  (81920, 82048, true),
  (82048, 82176, true),
  (82176, 82304, true),
  (82304, 82368, true),
  (82368, 82432, true),
  (82432, 82496, true),
  (82496, 82528, true),
  (82528, 82560, true),
  (82560, 82592, true),
  (82592, 82608, true),
  (82608, 82616, true),
  (82616, 82624, true),
  (82624, 82632, true),
  (82632, 250598, false)]

theorem cover1_ok : SixW25P.coverCheck 49170450 (SC / 2) 250598 cover1 = true := by decide +kernel

def cover2 : List (ℕ × ℕ × Bool) := [
  (16384, 20480, true),
  (20480, 24576, true),
  (24576, 28672, true),
  (28672, 30720, true),
  (30720, 30976, true),
  (30976, 31104, true),
  (31104, 31136, true),
  (31136, 31152, true),
  (31152, 31168, true),
  (31168, 39280, false),
  (39280, 39296, true),
  (39296, 39360, true),
  (39360, 39424, true),
  (39424, 39680, true),
  (39680, 39936, true),
  (39936, 40960, true),
  (40960, 45056, true),
  (45056, 49152, true),
  (49152, 53248, true),
  (53248, 57344, true),
  (57344, 58368, true),
  (58368, 58624, true),
  (58624, 58688, true),
  (58688, 58720, true),
  (58720, 58728, true),
  (58728, 78968, false),
  (78968, 78976, true),
  (78976, 78992, true),
  (78992, 79008, true),
  (79008, 79040, true),
  (79040, 79104, true),
  (79104, 79232, true),
  (79232, 79360, true),
  (79360, 79616, true),
  (79616, 79872, true),
  (79872, 80384, true),
  (80384, 80896, true),
  (80896, 81920, true),
  (81920, 82432, true),
  (82432, 82944, true),
  (82944, 83200, true),
  (83200, 83456, true),
  (83456, 83584, true),
  (83584, 83712, true),
  (83712, 83776, true),
  (83776, 83808, true),
  (83808, 83824, true),
  (83824, 83840, true),
  (83840, 83848, true),
  (83848, 289438, false)]

theorem cover2_ok : SixW25P.coverCheck 51271755 (SC / 2) 289438 cover2 = true := by decide +kernel

def cover3 : List (ℕ × ℕ × Bool) := [
  (16384, 20480, true),
  (20480, 24576, true),
  (24576, 28672, true),
  (28672, 30720, true),
  (30720, 30976, true),
  (30976, 31040, true),
  (31040, 31072, true),
  (31072, 31088, true),
  (31088, 31096, true),
  (31096, 39408, false),
  (39408, 39424, true),
  (39424, 39488, true),
  (39488, 39552, true),
  (39552, 39680, true),
  (39680, 39936, true),
  (39936, 40960, true),
  (40960, 45056, true),
  (45056, 49152, true),
  (49152, 53248, true),
  (53248, 57344, true),
  (57344, 57856, true),
  (57856, 58368, true),
  (58368, 58496, true),
  (58496, 58528, true),
  (58528, 58544, true),
  (58544, 58552, true),
  (58552, 80144, false),
  (80144, 80152, true),
  (80152, 80160, true),
  (80160, 80176, true),
  (80176, 80192, true),
  (80192, 80208, true),
  (80208, 80224, true),
  (80224, 80256, true),
  (80256, 80288, true),
  (80288, 80320, true),
  (80320, 80384, true),
  (80384, 80448, true),
  (80448, 80512, true),
  (80512, 80640, true),
  (80640, 80768, true),
  (80768, 80896, true),
  (80896, 81152, true),
  (81152, 81408, true),
  (81408, 81664, true),
  (81664, 81920, true),
  (81920, 82048, true),
  (82048, 82176, true),
  (82176, 82304, true),
  (82304, 82368, true),
  (82368, 82432, true),
  (82432, 82496, true),
  (82496, 82528, true),
  (82528, 82560, true),
  (82560, 82592, true),
  (82592, 82608, true),
  (82608, 82616, true),
  (82616, 82624, true),
  (82624, 82632, true),
  (82632, 250598, false)]

theorem cover3_ok : SixW25P.coverCheck 49170450 (SC / 2) 250598 cover3 = true := by decide +kernel

def cover4 : List (ℕ × ℕ × Bool) := [
  (16384, 20480, true),
  (20480, 24576, true),
  (24576, 28672, true),
  (28672, 29696, true),
  (29696, 29824, true),
  (29824, 29840, true),
  (29840, 29848, true),
  (29848, 42312, false),
  (42312, 42320, true),
  (42320, 42336, true),
  (42336, 42368, true),
  (42368, 42432, true),
  (42432, 42496, true),
  (42496, 42752, true),
  (42752, 43008, true),
  (43008, 44032, true),
  (44032, 45056, true),
  (45056, 47104, true),
  (47104, 49152, true),
  (49152, 51200, true),
  (51200, 53248, true),
  (53248, 53760, true),
  (53760, 54272, true),
  (54272, 54528, true),
  (54528, 54656, true),
  (54656, 54688, true),
  (54688, 54720, true),
  (54720, 54736, true),
  (54736, 358256, false)]

theorem cover4_ok : SixW25P.coverCheck 25193671 (SC / 2) 358256 cover4 = true := by decide +kernel

theorem wk0llllll : SixW25P.Covered 29848 36080 31096 33174 31168 35224 31096 35252 29848 36080 :=
  SixW25P.covered_of_walk lbS hbas 9082039264673742862743069335614586430982941756347394250551116377127234312741019248327302221576684895366128020269845696602249474582765437244846986946262306661254487749109905878449235431830636694651783790403435574155735519941895378161542424287132555841117640637364514186733030560590171286934253710216500766207718197873287820912306752778319917357953426676778347655645628479720317524164522054242103702121027541858043959501332226077877209884156410997079169051273334552076559022515173440874274538378357898518358788410478590512652886982078191028115902069785765346716095713578711969649918060709937306469341304809925139467970530651535563828740642141114561885458918915563027749127135820165911208377166060387253555124621551742537335611569198532588430978717232326523626659775214692244052268389507920304427612363773955094386935793868414875375476610700776960233082644172141988898 200 29848 36080 31096 33174 31168 35224 31096 35252 29848 36080 2877
    (by decide +kernel) (by decide)
theorem wk0lllllrl : SixW25P.Covered 29848 32964 33174 35252 31168 35224 31096 35252 29848 36080 :=
  SixW25P.covered_of_walk lbS hbas 1058932097146762145474455516340122330278952920516055274467666368642614638035013773329745891622504489870493203923703237104981097469082456764129455180656519451096534356027792640275461319317559471220304454403230557850692177815023306103333044682959073944343999812006912933597728604444817258911871058136465696899248464826950686552855524065756170821405966491174360391315405775882306862300471018288477282042901163857279360502523473245081215890704910469663227040188943824043531083027749893836572540177119774184063630906826101354396736646454022813710664763932417340778475515475486546273028348265874260401186948060578916699271997990231400529818767904770414621580783701410155491558419981552908217483841681984731162931712936489005533646814555194910021829138646924167846776301257391032948222866130252286179139002380685897250094959519103490332675075434012808251979402230297983620206690839690632142776966688340276266376500086935973262104433188292616429519566135123788428364622351774400110524840089842873714179256759457603224970187143029814449137106900496870292749719825986287080461109675942886142560392666072970236263744032612849383059624524784236871108895202893065966114363073865329415151981357027984815185709041107780094453000947474424134493832430 200 29848 32964 33174 35252 31168 35224 31096 35252 29848 36080 4102
    (by decide +kernel) (by decide)
theorem wk0lllllrr : SixW25P.Covered 32964 36080 33174 35252 31168 35224 31096 35252 29848 36080 :=
  SixW25P.covered_of_walk lbS hbas 7865565990001585519336663952428312487979817674867782468577118841320522116926928946894868038546240526205950435142162962797038294719068320256610604235251147779681806296806861031818032220295691804479236335658259136224639562991924534141152023390953561336027455815306977156300870489796974755974619856188731036995453964842053548616033841827457108978799633190673665344048089715198766351141655669369630407417950240215911252581276051206959686869401764763513994068305426885137298125907272808468644465796695344801465403828352663178743780727844754297618231474366973432988508998402368293767275348539376776065418127516486799973315861995220200901138072890494756507175080109439703435797239444426954609487973114979651586500740707280836935572247333118882806077433050229569932629072818862079171573152705994067482109736445520117283820290379762983356396385580324640821423215265848167649822902957537175081312042055248638126103987299129913372184491129921017945613498545001938989865918761001745204685279356670494027044493277533663963253647396560280033983702311627533150792403809704537602304768542302803374243909803615644882846916761968421228661751156251646428842306994030005078476143974519843744539155642942844722889164464497239352498744555242138959919144567503998146208932548262665243328823076379366563235082304304582546531498068027325222085973654746043660021019128328964736444762219142421994078366358516206031341865510666546960007476419068807398562114769306467612576188230637479590588022682536986858728912968067934980753337417428328107749549330569208405914747257685609859745318531278563696613763656033908960389306672036830953491265271770778744780312810067629979551486393143229739221811136942450336084739009016304305472305042371726295899464319382807086321193128379093882292695744302574653083379219021964181252454263138486849396263656677824140376484204521582289109611617986602487863316222357264037193217094640660815804539198761729678579481644585391062881667502748844871186775680336232043196701855621402583268466655511785179908140578606256331195748843176601565861065127496507659668065580478021209672837634723768278629469061636574483758922772246958697425886706654869579226282 200 32964 36080 33174 35252 31168 35224 31096 35252 29848 36080 7147
    (by decide +kernel) (by decide)
theorem wk0lllllr : SixW25P.Covered 29848 36080 33174 35252 31168 35224 31096 35252 29848 36080 :=
  SixW25P.covered_split0 32964 wk0lllllrl wk0lllllrr
theorem wk0lllll : SixW25P.Covered 29848 36080 31096 35252 31168 35224 31096 35252 29848 36080 :=
  SixW25P.covered_split1 33174 wk0llllll wk0lllllr
theorem wk0llllr : SixW25P.Covered 29848 36080 31096 35252 35224 39280 31096 35252 29848 36080 :=
  SixW25P.covered_of_walk lbS hbas 14461848413172778513998969824968634036902118977921516721721691145014335938775877710174337302191698338489057527402 200 29848 36080 31096 35252 35224 39280 31096 35252 29848 36080 377
    (by decide +kernel) (by decide)
theorem wk0llll : SixW25P.Covered 29848 36080 31096 35252 31168 39280 31096 35252 29848 36080 :=
  SixW25P.covered_split2 35224 wk0lllll wk0llllr
theorem wk0lllr : SixW25P.Covered 29848 36080 31096 35252 31168 39280 35252 39408 29848 36080 :=
  SixW25P.covered_of_walk lbS hbas 3696838339884919624243741792279104577076293353177050180341388566951197289951857201770419172900607745741277532697322 200 29848 36080 31096 35252 31168 39280 35252 39408 29848 36080 387
    (by decide +kernel) (by decide)
theorem wk0lll : SixW25P.Covered 29848 36080 31096 35252 31168 39280 31096 39408 29848 36080 :=
  SixW25P.covered_split3 35252 wk0llll wk0lllr
theorem wk0llr : SixW25P.Covered 29848 36080 35252 39408 31168 39280 31096 39408 29848 36080 :=
  SixW25P.covered_of_walk lbS hbas 494598339921019699813813220778307706525436555229311187383721443807166236383007600581534817184122738881252549443985427612696570373806 200 29848 36080 35252 39408 31168 39280 31096 39408 29848 36080 447
    (by decide +kernel) (by decide)
theorem wk0ll : SixW25P.Covered 29848 36080 31096 39408 31168 39280 31096 39408 29848 36080 :=
  SixW25P.covered_split1 35252 wk0lll wk0llr
theorem wk0lr : SixW25P.Covered 29848 36080 31096 39408 31168 39280 31096 39408 36080 42312 :=
  SixW25P.covered_of_walk lbS hbas 2944869354729741616833756884321960896302 200 29848 36080 31096 39408 31168 39280 31096 39408 36080 42312 142
    (by decide +kernel) (by decide)
theorem wk0l : SixW25P.Covered 29848 36080 31096 39408 31168 39280 31096 39408 29848 42312 :=
  SixW25P.covered_split4 36080 wk0ll wk0lr
theorem wk0r : SixW25P.Covered 36080 42312 31096 39408 31168 39280 31096 39408 29848 42312 :=
  SixW25P.covered_of_walk lbS hbas 5658502399530638652673830093627375251149763843398614225400418 200 36080 42312 31096 39408 31168 39280 31096 39408 29848 42312 212
    (by decide +kernel) (by decide)
theorem wk0 : SixW25P.Covered 29848 42312 31096 39408 31168 39280 31096 39408 29848 42312 :=
  SixW25P.covered_split0 36080 wk0l wk0r
theorem wk1lllllllll : SixW25P.Covered 29848 36080 31096 35252 31168 35224 31096 35252 54736 64221 :=
  SixW25P.covered_of_walk lbS hbas 748190190076285049550478652532739889196069640229215551117754264342436757019964449333929749608353144883889014584708223864084897882989168344743665055965646898297853032113084466100671476337535410384614901665722237051618725282183182164757602111766331646347982064149549236962047680209110454586473430514448210068521746877049611917639053853312417418457825655151209259450971090042491229390573157875957876992691871416725001938583108288573694830933744915774093612424515611871101898628194066175900760708702431191401689313907542868418702897062794937290811210642622196443157073025995374304528643246683583479902462176383439054455429603672190975442199892668757325058872123232256149165005213996221284587535947884167891150900898505247041100650900651440665174403100229824774335380327196278152572773622310460828994331256212283527027845820530442804451859744604581461560547128481728505706170557482803206066786039272465047760085381601619367766068041901620256294952760235201161688234606754326696500019155969527867579353912135798297808977566653219060056981695159298165175171304700027919291486926527627534756431492675753327905283170716587928536452857456786301411162489703010401454526264373232713520130115673235141255975977415359187371597054590503129656212548994637842207356656096931504903291269037780600116770033529404412766167762906663711598685945448979174960903589541298855214480853680075510975145077649531654951635298802752630080111959553516125534368560659773462204400112145609748122894963114735427046796301106194992377344660032829448862186428749284554720708712885210950720352549782913716088272815646632425827549040806239446886557898593579744695434400915270046249655256101608292030121668065666396945164998680311912542132075225160560312072850951133384024590414795139094805497636948657847116292844628162454980531408669891765240830607797624825213694684907607348948799550662472806770512999350328922891414355916928314357254444745702095539740513848724422803893802111313362 200 29848 36080 31096 35252 31168 35224 31096 35252 54736 64221 6462
    (by decide +kernel) (by decide)
theorem wk1llllllllrll : SixW25P.Covered 29848 36080 31096 35252 31168 35224 31096 33174 64221 68963 :=
  SixW25P.covered_of_walk lbS hbas 12345284206154433904880112480241891885446085420373429429641536803054737580481512017308590201636477913174404478358963198931079622379439978759839317814098865184376047983761283206772687814196898066790444927088871714603535394979178916240014355251036257100768209743000444511374732683812966898733630723636324995716943694033887996718400403496851911993336040654 200 29848 36080 31096 35252 31168 35224 31096 33174 64221 68963 1177
    (by decide +kernel) (by decide)
theorem wk1llllllllrlrl : SixW25P.Covered 29848 36080 31096 33174 31168 35224 33174 35252 64221 68963 :=
  SixW25P.covered_of_walk lbS hbas 347746052544423371849842699583819391349453315504967645799258565185849343213117241706943025520494440048039919858491569645275618767355049781847886973830098963880821299323935257661898944985663401259159377908953781205133937999113251249728943488186351808107379860464155205862390363884096911277477952335891290402943125617942303053239222842264609790834243427719582269768759454077782264084015008487258844220038753907218203966931369498279416436182865775913478103146892208639324533713071558375948141023824160271191778579039117735832174039233889350 200 29848 36080 31096 33174 31168 35224 33174 35252 64221 68963 1787
    (by decide +kernel) (by decide)
theorem wk1llllllllrlrrl : SixW25P.Covered 29848 36080 33174 35252 31168 33196 33174 35252 64221 68963 :=
  SixW25P.covered_of_walk lbS hbas 247108336757490972492100057990435626309765329272105468495699222462750899085369190788387807126884020838322461554262427372433983729304870739137357873991674188967142687522005196920008268559035110091134812999738911643692847195230088103216395358545360350088588436518497143700619610958767764349916108738740978215061843362977520280136487246805664333203670094384117201290216477294574264266469110357617619189122499658 200 29848 36080 33174 35252 31168 33196 33174 35252 64221 68963 1357
    (by decide +kernel) (by decide)
theorem wk1llllllllrlrrrl : SixW25P.Covered 29848 32964 33174 35252 33196 35224 33174 35252 64221 68963 :=
  SixW25P.covered_of_walk lbS hbas 185677312302003819801088145297479592257640720274183315326195295552729761176657458213410857042196922812513567917710093089605411478965054108823884269111708931359421961486332331094660160194354846295144334522769703829464094117341871008079308437950933697534775562327423248016965971020827823791204680940917633272605937366502754644850009270773494155921516091710368793411485299384984597719100175484536954251670182078286499988868221924623903712626079139978881179180619312158376846613472760658535462112157299089515089217527773999611773368806530940241447717855004614945694022991856506657199410625320321134556959257484856368699033534053884363599987585791224437301916197990434539395260106178232931713798133356412480133914090224782922178302134078973216407280434233491034790561892694287394 200 29848 32964 33174 35252 33196 35224 33174 35252 64221 68963 2577
    (by decide +kernel) (by decide)
theorem wk1llllllllrlrrrrllll : SixW25P.Covered 32964 34522 33174 34213 33196 34210 33174 35252 64221 66592 :=
  SixW25P.covered_of_walk lbS hbas 121638040836410527300890823236354937989872913689199824302755625303590624281229102701768171796587244783342791370919970291862358276516690416398244460000049023029912165865953700533877944727960411062248958667238712866186844512800955289288868080167840719729879144130521428095703827432281921975633694593974732984058820099345037489608016053471267110649510468244644859856234043519161446923308406924314297920952494369403298830330461474459926633768615411433571652903871905959528925979952569059229541387507669891420059746337338406537794235092518396418718934001899717377411237569794855008209541460597649498936419316342576056144505100073464535684856928172387312431059953599189114051944496816286995708465883912719431709682820889155032310081437928390736507157167368262250218654932320891345035629145616102497835843448111824141283904589663427683898386459123112133028021076665330320100035926139238502274480149993847374711497577697254038290513322462767042764629144266011959561349611303408640899077228418226017731966684336905428837972375885772064571339633488046228397717175797076033408351926411698158553616709182739372758304441756913857654362235095803798226861864070694091736888975571999685617036646189278601294631457761393612791610363068975030960482716046099833002533208204005166847742356622427556644168033606775433863427049494962247327802089984749209761594944359546306550451373590771696452188755574721236439208472663573755503315406710123913734304612235156908358082526958971657252292216124185177808078135431281749427429286975512558257360128460521145830678290736848929983892177302664033076270457549964278386222469178287424149925733223796890819734724333530560640279130697151767942988232754063356964999124934751638184191523270171175519250838315363908607337346423525454432002734723058238784376295699235215443937485177503469194649693721074423131488827594127137538042075665648714706275150699362264325210257651293409835446300078571370897818570865984580868614174065691715347364152005884548765687551398298651050555330135202201595421319554264287991611665689699767076396834443192528983869008440053258398318 200 32964 34522 33174 34213 33196 34210 33174 35252 64221 66592 6902
    (by decide +kernel) (by decide)
theorem wk1llllllllrlrrrrlllr : SixW25P.Covered 32964 34522 33174 34213 34210 35224 33174 35252 64221 66592 :=
  SixW25P.covered_of_walk lbS hbas 3489976299192407392045329827445779004331841661341849971106692416047846355166907087820412675258611103338280304617710548705106122585526319946343304192626100844195084365800412533655907264029294 200 32964 34522 33174 34213 34210 35224 33174 35252 64221 66592 637
    (by decide +kernel) (by decide)
theorem wk1llllllllrlrrrrlll : SixW25P.Covered 32964 34522 33174 34213 33196 35224 33174 35252 64221 66592 :=
  SixW25P.covered_split2 34210 wk1llllllllrlrrrrllll wk1llllllllrlrrrrlllr
theorem wk1llllllllrlrrrrllr : SixW25P.Covered 32964 34522 33174 34213 33196 35224 33174 35252 66592 68963 :=
  SixW25P.covered_of_walk lbS hbas 4866738390614762744837988119368483767618907911145925953602230766260472714761920737966 200 32964 34522 33174 34213 33196 35224 33174 35252 66592 68963 287
    (by decide +kernel) (by decide)
theorem wk1llllllllrlrrrrll : SixW25P.Covered 32964 34522 33174 34213 33196 35224 33174 35252 64221 68963 :=
  SixW25P.covered_split4 66592 wk1llllllllrlrrrrlll wk1llllllllrlrrrrllr
theorem wk1llllllllrlrrrrlr : SixW25P.Covered 34522 36080 33174 34213 33196 35224 33174 35252 64221 68963 :=
  SixW25P.covered_of_walk lbS hbas 760739120633203921543988775058279314354040313046376604921522 200 34522 36080 33174 34213 33196 35224 33174 35252 64221 68963 207
    (by decide +kernel) (by decide)
theorem wk1llllllllrlrrrrl : SixW25P.Covered 32964 36080 33174 34213 33196 35224 33174 35252 64221 68963 :=
  SixW25P.covered_split0 34522 wk1llllllllrlrrrrll wk1llllllllrlrrrrlr
theorem wk1llllllllrlrrrrr : SixW25P.Covered 32964 36080 34213 35252 33196 35224 33174 35252 64221 68963 :=
  SixW25P.covered_of_walk lbS hbas 530783098318763462402924397644567571760870227271813708144556854999643773936287599942635332166581125668367614282980693162250417067379476839096576802 200 32964 36080 34213 35252 33196 35224 33174 35252 64221 68963 492
    (by decide +kernel) (by decide)
theorem wk1llllllllrlrrrr : SixW25P.Covered 32964 36080 33174 35252 33196 35224 33174 35252 64221 68963 :=
  SixW25P.covered_split1 34213 wk1llllllllrlrrrrl wk1llllllllrlrrrrr
theorem wk1llllllllrlrrr : SixW25P.Covered 29848 36080 33174 35252 33196 35224 33174 35252 64221 68963 :=
  SixW25P.covered_split0 32964 wk1llllllllrlrrrl wk1llllllllrlrrrr
theorem wk1llllllllrlrr : SixW25P.Covered 29848 36080 33174 35252 31168 35224 33174 35252 64221 68963 :=
  SixW25P.covered_split2 33196 wk1llllllllrlrrl wk1llllllllrlrrr
theorem wk1llllllllrlr : SixW25P.Covered 29848 36080 31096 35252 31168 35224 33174 35252 64221 68963 :=
  SixW25P.covered_split1 33174 wk1llllllllrlrl wk1llllllllrlrr
theorem wk1llllllllrl : SixW25P.Covered 29848 36080 31096 35252 31168 35224 31096 35252 64221 68963 :=
  SixW25P.covered_split3 33174 wk1llllllllrll wk1llllllllrlr
theorem wk1llllllllrr : SixW25P.Covered 29848 36080 31096 35252 31168 35224 31096 35252 68963 73706 :=
  SixW25P.covered_of_walk lbS hbas 587474068036490478 200 29848 36080 31096 35252 31168 35224 31096 35252 68963 73706 67
    (by decide +kernel) (by decide)
theorem wk1llllllllr : SixW25P.Covered 29848 36080 31096 35252 31168 35224 31096 35252 64221 73706 :=
  SixW25P.covered_split4 68963 wk1llllllllrl wk1llllllllrr
theorem wk1llllllll : SixW25P.Covered 29848 36080 31096 35252 31168 35224 31096 35252 54736 73706 :=
  SixW25P.covered_split4 64221 wk1lllllllll wk1llllllllr
theorem wk1lllllllr : SixW25P.Covered 29848 36080 31096 35252 31168 35224 35252 39408 54736 73706 :=
  SixW25P.covered_of_walk lbS hbas 128131745794689333301778656022915671734024799279522698537726925814494632282040118223338843933383753461770811861445224511466551737656567220905788101362 200 29848 36080 31096 35252 31168 35224 35252 39408 54736 73706 507
    (by decide +kernel) (by decide)
theorem wk1lllllll : SixW25P.Covered 29848 36080 31096 35252 31168 35224 31096 39408 54736 73706 :=
  SixW25P.covered_split3 35252 wk1llllllll wk1lllllllr
theorem wk1llllllr : SixW25P.Covered 29848 36080 31096 35252 35224 39280 31096 39408 54736 73706 :=
  SixW25P.covered_of_walk lbS hbas 15288784526095269213584640197855674517747259835011750603082361783891395716905173754671657482287230459286660895285577279265346502424735240112910002 200 29848 36080 31096 35252 35224 39280 31096 39408 54736 73706 492
    (by decide +kernel) (by decide)
theorem wk1llllll : SixW25P.Covered 29848 36080 31096 35252 31168 39280 31096 39408 54736 73706 :=
  SixW25P.covered_split2 35224 wk1lllllll wk1llllllr
theorem wk1lllllr : SixW25P.Covered 29848 36080 35252 39408 31168 39280 31096 39408 54736 73706 :=
  SixW25P.covered_of_walk lbS hbas 2507720523430928292904452501790458472897097623362458154375778135655706538671252687482399795395798671186319126168180379651868412030570 200 29848 36080 35252 39408 31168 39280 31096 39408 54736 73706 447
    (by decide +kernel) (by decide)
theorem wk1lllll : SixW25P.Covered 29848 36080 31096 39408 31168 39280 31096 39408 54736 73706 :=
  SixW25P.covered_split1 35252 wk1llllll wk1lllllr
theorem wk1llllr : SixW25P.Covered 36080 42312 31096 39408 31168 39280 31096 39408 54736 73706 :=
  SixW25P.covered_of_walk lbS hbas 482282240405697189800486 200 36080 42312 31096 39408 31168 39280 31096 39408 54736 73706 87
    (by decide +kernel) (by decide)
theorem wk1llll : SixW25P.Covered 29848 42312 31096 39408 31168 39280 31096 39408 54736 73706 :=
  SixW25P.covered_split0 36080 wk1lllll wk1llllr
theorem wk1lllr : SixW25P.Covered 29848 42312 31096 39408 31168 39280 31096 39408 73706 92676 :=
  SixW25P.covered_of_walk lbS hbas 4237577970676345893122996396067752530 200 29848 42312 31096 39408 31168 39280 31096 39408 73706 92676 127
    (by decide +kernel) (by decide)
theorem wk1lll : SixW25P.Covered 29848 42312 31096 39408 31168 39280 31096 39408 54736 92676 :=
  SixW25P.covered_split4 73706 wk1llll wk1lllr
theorem wk1llr : SixW25P.Covered 29848 42312 31096 39408 31168 39280 31096 39408 92676 130616 :=
  SixW25P.covered_of_walk lbS hbas 619503939102711729667612222355716185492711614537954488890219993886120176928627952447438781661602997296127622281394183821715103752468082389745453785404464587176664175622883559482819643339074782657857044755964188545618978891298387631970607181836208709413752390605289229413270424971216289911698757848402962811117183152891829989809857915744764747743158557924484846000582610825381591689297454274896477154785212591743257965289427801442394044115767128235052262786547579134140873225574603820927576329493687800061473328413074398666125857402777898119757513627432373765079691615172236216611357440995251735587332609477071417346752985534951839778126701380274179130393002558842762585985364287211877214417379169068055701616990557717299494614753431579898231188501307069527572231395121746994657425028214523629288398561698232356258176600028720683663930835904165916657067335401872581576202351475202045643644565539563853287159825681302439738336158421933757447754429386788463272218912560110517039911708761953445328901416332116714293702448166530037224108469966855125523680019458617601150628923221637863509953520159988980810365998377121396410291887975934705003835984355859821923784612998406054350468469887742228671224791849295165579320155317000589658384695950134930929902246710665851998957451471083806389481025885917493319743044538149749520689892231180737325519585061118290588234963487342914146 200 29848 42312 31096 39408 31168 39280 31096 39408 92676 130616 4562
    (by decide +kernel) (by decide)
theorem wk1ll : SixW25P.Covered 29848 42312 31096 39408 31168 39280 31096 39408 54736 130616 :=
  SixW25P.covered_split4 92676 wk1lll wk1llr
theorem wk1lr : SixW25P.Covered 29848 42312 31096 39408 31168 39280 31096 39408 130616 206496 :=
  SixW25P.covered_of_walk lbS hbas 104195728722464678479579025405301827390591226738895561966191707558854145987245398331483567276676562844336773429156000851106742727607076314831653567013615663165781692413502950865685109652360539262531664284380885602865345147442 200 29848 42312 31096 39408 31168 39280 31096 39408 130616 206496 747
    (by decide +kernel) (by decide)
theorem wk1l : SixW25P.Covered 29848 42312 31096 39408 31168 39280 31096 39408 54736 206496 :=
  SixW25P.covered_split4 130616 wk1ll wk1lr
theorem wk1r : SixW25P.Covered 29848 42312 31096 39408 31168 39280 31096 39408 206496 358256 :=
  SixW25P.covered_of_walk lbS hbas 0 200 29848 42312 31096 39408 31168 39280 31096 39408 206496 358256 2
    (by decide +kernel) (by decide)
theorem wk1 : SixW25P.Covered 29848 42312 31096 39408 31168 39280 31096 39408 54736 358256 :=
  SixW25P.covered_split4 206496 wk1l wk1r
theorem wk2lll : SixW25P.Covered 29848 36080 31096 39408 31168 39280 58552 63950 29848 42312 :=
  SixW25P.covered_of_walk lbS hbas 198056049589838419127483793626276529919724294064272041105382113193621716988680744997958418303232113210007784098687979949158013057346106574764705044690720996463816163920813858231445671057604171045973337887805261835347311626803938709578426774486212738042437619111461090895410645459946686362210116927522794870765442537181226546237684397890287444920332588077677107218927471945406536142943614662653152420986685247720191522068173274267835262153502900319746506968143255866590668883899734002946760713790688918477238473413228456033768858060775121355963390599143234086151532203469847807534895102753751937215487705972954410585189887355359320679024939314020011492059786906413649596783889389612089758289861681778276450735409540195194536548786563566365856443886421979098665135745727925698193195238974191379221222556376599386076389363975093777802167493400572611571422742014134268565575282316802208814534559367311285728353169421063646270819558606 200 29848 36080 31096 39408 31168 39280 58552 63950 29848 42312 3097
    (by decide +kernel) (by decide)
theorem wk2llrll : SixW25P.Covered 29848 36080 31096 35252 31168 39280 63950 69348 29848 36080 :=
  SixW25P.covered_of_walk lbS hbas 233108358231828876212375412184719219133820564666843675069459126447610080358548333413258571722991603273746809311785065934318849792596858194927621424427321980079880748601684025430433672227795541022326711635507198396798798401502394172283125060481985624334129468212943311473745873782234386815763645152651663265918565166590064980313493996246718361180777976851912508456559806734416689883348598902524507554279669807662638340538584352624246881556228393284232999133104078530580667336859437954333947048470539257214606456407608671462014202510300955325689298911144354580050630762098234447810258771195626538132575416310278684277351231820311078833417123025334693618324250287965801542568979250631453134413618005567521321184776267993175647734545045696906283652074080111965914325584154425103280848810328444176352697536065560910404152252855013783776076378975914683652989448884386930467209032378420691309359355316629781893959086919193160410458990975670725694360586522534633933490246854362675752529824096620319890893865608224033523250540120136541080627286129077506688063941675547348996344661197833936544035225470262961526195812859801091759629591279737783781176041391479524518634410956153060081552626335807814177900502795156597595865766884149788786377853612008992414649287984175267184055494670535882596013057634291055945690547388148033146455281340828902017864065670758718037400957082728579347442005306185906633203599790489052243775123130567166210694113871077229025148084796151223425610588239021584280984028750495879903199005305784039278498301975775649927451175152800649507028969386896191415711365041905666262088404768033141982928186378759728339194316120936480297628969921820196187798423980379443835635360854425965808372343467802161035001996510045903857204786316616454332414761204752598516638366654281992642048930116359895379687037318166172208599478005952774421081291042160933274598846744018834909817195402507695479412465482703473717802279602078200297256065301858683664269941273150179695978300081826601524808037047271209593047726436182819745212901348921755178727566582183151980454737497923992375789342739458020758996593287715336712239051073136970627518915276252542528671845876783502695120340083709163170750060031633313731790203054809551668004458 200 29848 36080 31096 35252 31168 39280 63950 69348 29848 36080 7397
    (by decide +kernel) (by decide)
theorem wk2llrlr : SixW25P.Covered 29848 36080 35252 39408 31168 39280 63950 69348 29848 36080 :=
  SixW25P.covered_of_walk lbS hbas 154494034080001177429962798858322883564059271831769562873878143864111565514177292072945665594106534 200 29848 36080 35252 39408 31168 39280 63950 69348 29848 36080 332
    (by decide +kernel) (by decide)
theorem wk2llrl : SixW25P.Covered 29848 36080 31096 39408 31168 39280 63950 69348 29848 36080 :=
  SixW25P.covered_split1 35252 wk2llrll wk2llrlr
theorem wk2llrr : SixW25P.Covered 29848 36080 31096 39408 31168 39280 63950 69348 36080 42312 :=
  SixW25P.covered_of_walk lbS hbas 22478593145832011015497096279003469851976262677052238450885007963833035285535811809888649493178755754610 200 29848 36080 31096 39408 31168 39280 63950 69348 36080 42312 352
    (by decide +kernel) (by decide)
theorem wk2llr : SixW25P.Covered 29848 36080 31096 39408 31168 39280 63950 69348 29848 42312 :=
  SixW25P.covered_split4 36080 wk2llrl wk2llrr
theorem wk2ll : SixW25P.Covered 29848 36080 31096 39408 31168 39280 58552 69348 29848 42312 :=
  SixW25P.covered_split3 63950 wk2lll wk2llr
theorem wk2lr : SixW25P.Covered 36080 42312 31096 39408 31168 39280 58552 69348 29848 42312 :=
  SixW25P.covered_of_walk lbS hbas 7110372860516199078777037313223734780454 200 36080 42312 31096 39408 31168 39280 58552 69348 29848 42312 142
    (by decide +kernel) (by decide)
theorem wk2l : SixW25P.Covered 29848 42312 31096 39408 31168 39280 58552 69348 29848 42312 :=
  SixW25P.covered_split0 36080 wk2ll wk2lr
theorem wk2r : SixW25P.Covered 29848 42312 31096 39408 31168 39280 69348 80144 29848 42312 :=
  SixW25P.covered_of_walk lbS hbas 2598652905831936750 200 29848 42312 31096 39408 31168 39280 69348 80144 29848 42312 67
    (by decide +kernel) (by decide)
theorem wk2 : SixW25P.Covered 29848 42312 31096 39408 31168 39280 58552 80144 29848 42312 :=
  SixW25P.covered_split3 69348 wk2l wk2r
theorem wk3llllllll : SixW25P.Covered 29848 36080 31096 35252 31168 39280 58552 69348 54736 64221 :=
  SixW25P.covered_of_walk lbS hbas 127661136643191190678434031062306981781135447109479516716112474071029155913803239493086685181957669915405600385490474885847045788284058435360436875086129461551457713294493110652353087972087978566704743338776671084410002234623925940466592991014861382097052415663218695338870074441471282611150506231559231241575963332906381282150659872802702034911759507830384432297325300629623419060017240893434464454584087360498403881081314681789102543142902486840012966430032177514070922626534952943826203389802950267104666879324497754011127846370167538420063555200498248479375095398519735628895614953747621031659394256350284103705389682384132152786 200 29848 36080 31096 35252 31168 39280 58552 69348 54736 64221 2107
    (by decide +kernel) (by decide)
theorem wk3lllllllrl : SixW25P.Covered 29848 36080 31096 35252 31168 39280 58552 63950 64221 73706 :=
  SixW25P.covered_of_walk lbS hbas 194310327619117580000789219211046664719020774712670728034926446275935613927300295741988934814103675898757039534645134848952562298277436291011745372389993273099641616822570113927928298761716155976173540291554803012095310 200 29848 36080 31096 35252 31168 39280 58552 63950 64221 73706 737
    (by decide +kernel) (by decide)
theorem wk3lllllllrrlll : SixW25P.Covered 29848 36080 31096 33174 31168 35224 63950 69348 64221 68963 :=
  SixW25P.covered_of_walk lbS hbas 326500132331794022464812632267276685701738834051922406050875444292106237189966307957260998659363113158 200 29848 36080 31096 33174 31168 35224 63950 69348 64221 68963 347
    (by decide +kernel) (by decide)
theorem wk3lllllllrrllrl : SixW25P.Covered 29848 32964 33174 35252 31168 35224 63950 69348 64221 68963 :=
  SixW25P.covered_of_walk lbS hbas 4230013410236491270504613597873028266359065439656608124643029724829950272588271445998618142560037103055952236165614495771958720102147632273019433620700374458043856375614322759405747402727404860832907610008888051269007859317196298551414145869618072617968156951199822264191428695112593974245863991486995713417511646479790333238881755523127409842953559894702415742485192984927224536309413598262254398094869484445151643706884588048325535415934330920133761215613918979378723822929624541305446514211444197728046919683388125404491876426 200 29848 32964 33174 35252 31168 35224 63950 69348 64221 68963 1762
    (by decide +kernel) (by decide)
theorem wk3lllllllrrllrrl : SixW25P.Covered 32964 36080 33174 35252 31168 33196 63950 69348 64221 68963 :=
  SixW25P.covered_of_walk lbS hbas 6349492087777577929038822943233432875355912522 200 32964 36080 33174 35252 31168 33196 63950 69348 64221 68963 162
    (by decide +kernel) (by decide)
theorem wk3lllllllrrllrrrlllll : SixW25P.Covered 32964 34522 33174 34213 33196 34210 63950 65299 64221 68963 :=
  SixW25P.covered_of_walk lbS hbas 160160375753472310286255600223766562623016662611220674366632606001426659925008462584869114018106413670224591457629985812817376564882648908977980059655233975554608142799252526637738748799784912982865455145660226364485900792331049337227054753784906754504455224859636058973104663682733145156495945313361957933239456327879715430626986429311123337798103305213428211467876337582264602172189432965182745325602343806122114839483964477860687752327724364064229539763757019642506925184944637566645342096860926864598647169176776986488472023423633280578112206934934154669114064538713289934037770788279243804269039721139616802583347513920563504652324119230517185403974863472861301976750107309154336780907348507854152632833622315387678572146975546286177576468167486370138509826471812199370630952810823150013704828719643558698008283875766038116323348484901861051434492944193542710789472578046083190666117877650923930006428457412736826966381112520224966028853187409830084948919841988989365358038562041911196640683879496236130072378963350557081033200642857152080906242551840795036401134827382823885879306806496418956333766933356387608713650868165695139910549126097962660330878057305134899937469391089174982683581335286781333541733860561369226714094737132688379811842102749965429428915659404990962927155278339636784544487684815246062914288879704057170818009524762746229907977238028504606980930360141519790263411293571407090334261052065903595903132103593360886724873307732837965609897191064014805795900324879998030133959171106707039132170440577031018943636839124958603167613790184460301210260212828079515414604330811910197041033186009040925167987472310419332632426212649454606424339894110745251053108513228916836976152076740330893580977865757694675532326067050509147233166816852027421633126832150529486913117585331178719711175262210042466 200 32964 34522 33174 34213 33196 34210 63950 65299 64221 68963 6042
    (by decide +kernel) (by decide)
theorem wk3lllllllrrllrrrllllr : SixW25P.Covered 32964 34522 33174 34213 33196 34210 65299 66649 64221 68963 :=
  SixW25P.covered_of_walk lbS hbas 58678592359770120771630959532610944459465932872124075065130858598715132985246528412097266507474415404229860282746477834690224953341356398977604105792065616645315492790868687172344635090183279626877891659653655679928287111305865770731666058060873461036979385602489907836672445741186419719189078534251227777382486485426847651521647581335785538237656853250909454061189364587316521253851334638396391348666742821509743738402473976019726616770283131338717658475057394958847019222111907702192180261598276974282652614915472317078232280107977201178697131470864135129707284116432454340209245682446090610000527139598297290964188561889765402412576332425647342613736393120224960069829176724833082207531818390185727744428198307150128990183783649006757699549553119383121651046546326420723714202732049309483667220712713617508104312336808219715955159313613750002322487891819535535511828229265111539502244915239564318201083340890136895507049957682774616802804100490017861262606850808790363535279152060103253727099500069574368397438345270460649891590923851509072086387476663456303973817262934705029644579387526897308203917938 200 32964 34522 33174 34213 33196 34210 65299 66649 64221 68963 3682
    (by decide +kernel) (by decide)
theorem wk3lllllllrrllrrrllll : SixW25P.Covered 32964 34522 33174 34213 33196 34210 63950 66649 64221 68963 :=
  SixW25P.covered_split3 65299 wk3lllllllrrllrrrlllll wk3lllllllrrllrrrllllr
theorem wk3lllllllrrllrrrlllr : SixW25P.Covered 32964 34522 33174 34213 34210 35224 63950 66649 64221 68963 :=
  SixW25P.covered_of_walk lbS hbas 11127993724564919380484755057323070389372255095955359789861948337029722597399014822515113680945419264508187584777477397133409367967720704011501146911805117004958073333833492787190410840698762246818702426693717937385787782254592602331274140639613376728291041544918130706753357513519294274642178037179371602626757567832401875955342779322607755279353830059005520010209203227358623108035450625075944512240453426827195023992177804468738770775938679634350843804725324519120912768889108714426203117596571042625066714307692034798611442026411487817243289970275094466471990510188823474314486366952187849639219726291594360298947509499114279999406118332592490613525521518902308976879589029254806892507603476006354003829659915122029189973749955040923760902047565817409299856659210046742905283570637976782141145655055797606555312902996829773901337008340747955347476943341716260991736960041456687724434292771723071971994990377893325251586490652265639001338060154426610444744976344490606 200 32964 34522 33174 34213 34210 35224 63950 66649 64221 68963 3232
    (by decide +kernel) (by decide)
theorem wk3lllllllrrllrrrlll : SixW25P.Covered 32964 34522 33174 34213 33196 35224 63950 66649 64221 68963 :=
  SixW25P.covered_split2 34210 wk3lllllllrrllrrrllll wk3lllllllrrllrrrlllr
theorem wk3lllllllrrllrrrllr : SixW25P.Covered 32964 34522 34213 35252 33196 35224 63950 66649 64221 68963 :=
  SixW25P.covered_of_walk lbS hbas 304967672907013375886063609378310412346388780332169193328565311569667725795272666470310483175550567819181586101844480941476201172394921413584185639465499186952221633678215238010101598593998255997027883951404813210944045157883223330373245811672722226163085430267110926081708139601762698333493026159447667062964660795465122570103817258688023734931394605406910818389654155677135232570793271602341463393016969274221314358655542283860781108233229472255120984174142186 200 32964 34522 34213 35252 33196 35224 63950 66649 64221 68963 1542
    (by decide +kernel) (by decide)
theorem wk3lllllllrrllrrrll : SixW25P.Covered 32964 34522 33174 35252 33196 35224 63950 66649 64221 68963 :=
  SixW25P.covered_split1 34213 wk3lllllllrrllrrrlll wk3lllllllrrllrrrllr
theorem wk3lllllllrrllrrrlr : SixW25P.Covered 34522 36080 33174 35252 33196 35224 63950 66649 64221 68963 :=
  SixW25P.covered_of_walk lbS hbas 8337393116265442393817836019734061975512430853542221079206 200 34522 36080 33174 35252 33196 35224 63950 66649 64221 68963 197
    (by decide +kernel) (by decide)
theorem wk3lllllllrrllrrrl : SixW25P.Covered 32964 36080 33174 35252 33196 35224 63950 66649 64221 68963 :=
  SixW25P.covered_split0 34522 wk3lllllllrrllrrrll wk3lllllllrrllrrrlr
theorem wk3lllllllrrllrrrr : SixW25P.Covered 32964 36080 33174 35252 33196 35224 66649 69348 64221 68963 :=
  SixW25P.covered_of_walk lbS hbas 323273893513240934567511438871790194344671262293489081324145849638816857109325767201472142677398774293222 200 32964 36080 33174 35252 33196 35224 66649 69348 64221 68963 357
    (by decide +kernel) (by decide)
theorem wk3lllllllrrllrrr : SixW25P.Covered 32964 36080 33174 35252 33196 35224 63950 69348 64221 68963 :=
  SixW25P.covered_split3 66649 wk3lllllllrrllrrrl wk3lllllllrrllrrrr
theorem wk3lllllllrrllrr : SixW25P.Covered 32964 36080 33174 35252 31168 35224 63950 69348 64221 68963 :=
  SixW25P.covered_split2 33196 wk3lllllllrrllrrl wk3lllllllrrllrrr
theorem wk3lllllllrrllr : SixW25P.Covered 29848 36080 33174 35252 31168 35224 63950 69348 64221 68963 :=
  SixW25P.covered_split0 32964 wk3lllllllrrllrl wk3lllllllrrllrr
theorem wk3lllllllrrll : SixW25P.Covered 29848 36080 31096 35252 31168 35224 63950 69348 64221 68963 :=
  SixW25P.covered_split1 33174 wk3lllllllrrlll wk3lllllllrrllr
theorem wk3lllllllrrlr : SixW25P.Covered 29848 36080 31096 35252 31168 35224 63950 69348 68963 73706 :=
  SixW25P.covered_of_walk lbS hbas 87072767191184944230140727791272562 200 29848 36080 31096 35252 31168 35224 63950 69348 68963 73706 127
    (by decide +kernel) (by decide)
theorem wk3lllllllrrl : SixW25P.Covered 29848 36080 31096 35252 31168 35224 63950 69348 64221 73706 :=
  SixW25P.covered_split4 68963 wk3lllllllrrll wk3lllllllrrlr
theorem wk3lllllllrrr : SixW25P.Covered 29848 36080 31096 35252 35224 39280 63950 69348 64221 73706 :=
  SixW25P.covered_of_walk lbS hbas 26633166439309170284841261612289416643766577075548455854941670861474128487924330 200 29848 36080 31096 35252 35224 39280 63950 69348 64221 73706 272
    (by decide +kernel) (by decide)
theorem wk3lllllllrr : SixW25P.Covered 29848 36080 31096 35252 31168 39280 63950 69348 64221 73706 :=
  SixW25P.covered_split2 35224 wk3lllllllrrl wk3lllllllrrr
theorem wk3lllllllr : SixW25P.Covered 29848 36080 31096 35252 31168 39280 58552 69348 64221 73706 :=
  SixW25P.covered_split3 63950 wk3lllllllrl wk3lllllllrr
theorem wk3lllllll : SixW25P.Covered 29848 36080 31096 35252 31168 39280 58552 69348 54736 73706 :=
  SixW25P.covered_split4 64221 wk3llllllll wk3lllllllr
theorem wk3llllllr : SixW25P.Covered 29848 36080 35252 39408 31168 39280 58552 69348 54736 73706 :=
  SixW25P.covered_of_walk lbS hbas 27319941254391119753871763461232728023442438280801656678797030 200 29848 36080 35252 39408 31168 39280 58552 69348 54736 73706 212
    (by decide +kernel) (by decide)
theorem wk3llllll : SixW25P.Covered 29848 36080 31096 39408 31168 39280 58552 69348 54736 73706 :=
  SixW25P.covered_split1 35252 wk3lllllll wk3llllllr
theorem wk3lllllr : SixW25P.Covered 36080 42312 31096 39408 31168 39280 58552 69348 54736 73706 :=
  SixW25P.covered_of_walk lbS hbas 13696967206 200 36080 42312 31096 39408 31168 39280 58552 69348 54736 73706 42
    (by decide +kernel) (by decide)
theorem wk3lllll : SixW25P.Covered 29848 42312 31096 39408 31168 39280 58552 69348 54736 73706 :=
  SixW25P.covered_split0 36080 wk3llllll wk3lllllr
theorem wk3llllr : SixW25P.Covered 29848 42312 31096 39408 31168 39280 58552 69348 73706 92676 :=
  SixW25P.covered_of_walk lbS hbas 120442937385773578120802 200 29848 42312 31096 39408 31168 39280 58552 69348 73706 92676 82
    (by decide +kernel) (by decide)
theorem wk3llll : SixW25P.Covered 29848 42312 31096 39408 31168 39280 58552 69348 54736 92676 :=
  SixW25P.covered_split4 73706 wk3lllll wk3llllr
theorem wk3lllr : SixW25P.Covered 29848 42312 31096 39408 31168 39280 69348 80144 54736 92676 :=
  SixW25P.covered_of_walk lbS hbas 15054373116621159018226 200 29848 42312 31096 39408 31168 39280 69348 80144 54736 92676 82
    (by decide +kernel) (by decide)
theorem wk3lll : SixW25P.Covered 29848 42312 31096 39408 31168 39280 58552 80144 54736 92676 :=
  SixW25P.covered_split3 69348 wk3llll wk3lllr
theorem wk3llr : SixW25P.Covered 29848 42312 31096 39408 31168 39280 58552 80144 92676 130616 :=
  SixW25P.covered_of_walk lbS hbas 7151758731125477977118814475515634836988472284691692068432490277951166701913878812562059830248579613124337533869406097187750778885652687103946903103613938531373434824326524719489594015144842841825781842046440414279870022124773654945186352225864698334218938708892757065089229439873501020920649303708412433737361411918268170331664916744004245616568118603950862173596969388264896949831012873009586583727833777591863663524522125241994538974635707278894 200 29848 42312 31096 39408 31168 39280 58552 80144 92676 130616 1497
    (by decide +kernel) (by decide)
theorem wk3ll : SixW25P.Covered 29848 42312 31096 39408 31168 39280 58552 80144 54736 130616 :=
  SixW25P.covered_split4 92676 wk3lll wk3llr
theorem wk3lr : SixW25P.Covered 29848 42312 31096 39408 31168 39280 58552 80144 130616 206496 :=
  SixW25P.covered_of_walk lbS hbas 76857143872400625386734 200 29848 42312 31096 39408 31168 39280 58552 80144 130616 206496 92
    (by decide +kernel) (by decide)
theorem wk3l : SixW25P.Covered 29848 42312 31096 39408 31168 39280 58552 80144 54736 206496 :=
  SixW25P.covered_split4 130616 wk3ll wk3lr
theorem wk3r : SixW25P.Covered 29848 42312 31096 39408 31168 39280 58552 80144 206496 358256 :=
  SixW25P.covered_of_walk lbS hbas 0 200 29848 42312 31096 39408 31168 39280 58552 80144 206496 358256 2
    (by decide +kernel) (by decide)
theorem wk3 : SixW25P.Covered 29848 42312 31096 39408 31168 39280 58552 80144 54736 358256 :=
  SixW25P.covered_split4 206496 wk3l wk3r
theorem wk4 : SixW25P.Covered 29848 42312 31096 39408 31168 39280 82632 250598 29848 42312 :=
  SixW25P.covered_of_walk lbS hbas 14471543036474344633475930547983489696733262065831634631593633202070902553454704715045859207375331220218794682295628972844162840190433610584064817540164358872276174018677890333385054929320434368639787117524231525549492380267983169992943980472681020548647251025279307617879002014810313328194791405728087716357773253048279826635674389850763823643608637002442782892716912799268946461762848811826239601544395748906851308402926755628617015265163568426623144036293586807514085107816923261430433913638710289110221516766654055282871335553551083481387605371183881305478074369239155803693779912108667052426331964689755690839003967960033083055475615745876583527223634691268995706150610145594500196362774198132548260796488089090170042504544814006015251702225155629329713506191075556790225213202908626085683493720552163631696971395471921831948253511662842508167835643447366351997474929203398911647936969678392389520783458419620145798939123335592427769001164883719784926200903603287291761766495335240658774333996767626990981271478241371843673153273826946803283956429132776398744361100612837529030097229439213078390748080686781328592406904960983722059753169357626126258760226358525830756660400538549893061383001720158071508613103857571138257284775110280185249147106437986840454512027045170525085255569977611301934663103509281872412193977688106927654465093940884100515882454484268349284058737470608861362793583081597029014492289051675995949013760024263257142305143924567063890699964961336518653767623398692606105617618143228402692362937126963941444242664654579327393140906176155247781020488835487951702034264843970371286439320518046912905756017150094464582976539874270805971155078191529959694362677230537421289557597813838299000045054991445911803278107043506205951702206271392448300042397475572076598218598636569810878431565592595327365355093060519852484703694574 200 29848 42312 31096 39408 31168 39280 82632 250598 29848 42312 6137
    (by decide +kernel) (by decide)
theorem wk5 : SixW25P.Covered 29848 42312 31096 39408 31168 39280 82632 250598 54736 358256 :=
  SixW25P.covered_of_walk lbS hbas 12773059956987034238375209646216711488364316173893727478185859504861954535368320703598605129304053795498290536125159865065783992452805506999062128355959648029149931540046301965208135061318705007269581605936528745835983662 200 29848 42312 31096 39408 31168 39280 82632 250598 54736 358256 742
    (by decide +kernel) (by decide)
theorem wk6llllll : SixW25P.Covered 29848 36080 31096 35252 58728 63788 31096 35252 29848 36080 :=
  SixW25P.covered_of_walk lbS hbas 538591988438324341068050795004723251629930086984021580902551076300341357797095884305893524277793095573690011862736371876960953164062757459454142470621862771009238974715706824160684733848588513171909039601983057771289523684153206459095462856104459825890444030525563381278965048763285886805856504069923088594264753617348240352575153642940785211927482502118840542472157731922729468965202403092511976768503773650632613102025347996959197126610267686532631561936147386468443960688735518204884499029908574430701205515503894093297482099864264180868070822054199838374636568339239393328704662592372664832442702009126037435221406620530578771099818421284557531506366794207808478809290 200 29848 36080 31096 35252 58728 63788 31096 35252 29848 36080 2237
    (by decide +kernel) (by decide)
theorem wk6lllllrl : SixW25P.Covered 29848 36080 31096 33174 63788 68848 31096 35252 29848 36080 :=
  SixW25P.covered_of_walk lbS hbas 26837360480072680061191851427672657692994639326785805696765796231306939477595289605369141790738707366039147871942438653262452879960971471144213926187132749947165276426495649998637480929291460942335652213527150595950492406523206438966544177444531159768251807986898518082026431103075195337598387131347900777793748603945184557419031309485627012236152331277208963611694314073823268944345499132515107524779934790 200 29848 36080 31096 33174 63788 68848 31096 35252 29848 36080 1362
    (by decide +kernel) (by decide)
theorem wk6lllllrrl : SixW25P.Covered 29848 32964 33174 35252 63788 68848 31096 35252 29848 36080 :=
  SixW25P.covered_of_walk lbS hbas 19201282515953853400183437024197371577012187360897690738527743761318863691256792924372099093238870288632982512636555895131431706329631740409198129714097109497203311562351767053980047209968221760118773933940548874278653399717934941825870541644569665156640241485051946347229055290466113378068533093079075788114520797371069526711621488704954429134753278784491324913898566527897264520473747387329032776113663717735176364030670935255704472386034173273129940543233783673743891157501998681991097499262490605865221400015210209092832261217416289982122076256765066669152938850209369716372923783838940482844239321613916715273960302535638268902495462448794259295076392548457060090966813098537312493733499654079627266837093323057222576045165853955889136708766884291113274224678834151460520641532101441472618780595956551100427725333375579701417124729677223056337449307200714572648156273585299151459887162295342 200 29848 32964 33174 35252 63788 68848 31096 35252 29848 36080 2982
    (by decide +kernel) (by decide)
theorem wk6lllllrrrl : SixW25P.Covered 32964 36080 33174 35252 63788 68848 31096 33174 29848 36080 :=
  SixW25P.covered_of_walk lbS hbas 1153228919727539606442838716815044141059706773481922625410737576278274826868669222947642584522538165304861106545106050441693716041163393256262460618077249085471432062019475243055205539939035637928936417796795129681067603281830947176419439893180648487297680201499122348393554985850667093439360368393410629506663791322031156468295315696937162610829031450952822014984228989462263893160643591583969093198 200 32964 36080 33174 35252 63788 68848 31096 33174 29848 36080 1337
    (by decide +kernel) (by decide)
theorem wk6lllllrrrrl : SixW25P.Covered 32964 36080 33174 35252 63788 68848 33174 35252 29848 32964 :=
  SixW25P.covered_of_walk lbS hbas 44616551165240349979448947728459384453399150410811104838738 200 32964 36080 33174 35252 63788 68848 33174 35252 29848 32964 212
    (by decide +kernel) (by decide)
theorem wk6lllllrrrrrl : SixW25P.Covered 32964 36080 33174 35252 63788 66318 33174 35252 32964 36080 :=
  SixW25P.covered_of_walk lbS hbas 12370873567483371253030934973481203905436805806763321398539218464015541906907006633324299558432436156650221384100779282329168074181639656819661720892934913277658481013324431625329512847442065876941404520283965426621931774008460556947032488369129985219854144880381901192414415986318977915186129439960547965957056427663669553721288944971868998437079591288916457499361490309064243517141045618034083690332576768807855559691833166691212399681264995879837793195651060480230621897281488454671163957121756364392735916007611555160687448067269580195979203658952055794970999025199446781368136878796609793413527922826120122820356433831539771633689378152916974098216902022557625857673649720268607559280211621937339133801966462375129074923142563872719653843492544111613550424120751845101683142372055157965085120918527906919141447336523748296778291194554510471477401148681359793296827615306378676804432204962765368601310612335683739341598494609523215372151533170743611941086413510031471947295244383550292670959723130947735156350502308998130156874943524195691909045569404860554664909124123503633245265498214345886436656674069683824426452700544399006440595896561107004830606611981215523977424122565048949393995595131440953279760871236612218645463617221842781146751285455153053030064791536281783101421039039122272505988979689091419122124889525167301640498338456754342418172053900260033626155871530317290207372009185790813256993760331036061547844011766913919487677166843496525502446294496904051054886018312538319155510893356128792894891910081919299309409852643266680202723841931557637754234012706786454385569153236324490415467646466740066769166743472890633902904348314403591313060233360065719534815959329905170948516484584063117403621165202214250387024809883534846737291961074245189713955955222206586735906111421063157303418200351808778928564054425227503373207415813929269091906478249035472906452632504146632505731623837025617854576744081184316411949868071158104308348803538472958279895842 200 32964 36080 33174 35252 63788 66318 33174 35252 32964 36080 6547
    (by decide +kernel) (by decide)
theorem wk6lllllrrrrrr : SixW25P.Covered 32964 36080 33174 35252 66318 68848 33174 35252 32964 36080 :=
  SixW25P.covered_of_walk lbS hbas 15447397809306657012080356255535094819654635969515558217069371759249164989042948932793041290665590743940908015935718988210754590292475474729435965193571085828739341890866301768841408469815756372249429044560702634486357879434101568187514765706763061047097923402894918354925911336541470515530788543750679236398504523366596946369913574 200 32964 36080 33174 35252 66318 68848 33174 35252 32964 36080 1107
    (by decide +kernel) (by decide)
theorem wk6lllllrrrrr : SixW25P.Covered 32964 36080 33174 35252 63788 68848 33174 35252 32964 36080 :=
  SixW25P.covered_split2 66318 wk6lllllrrrrrl wk6lllllrrrrrr
theorem wk6lllllrrrr : SixW25P.Covered 32964 36080 33174 35252 63788 68848 33174 35252 29848 36080 :=
  SixW25P.covered_split4 32964 wk6lllllrrrrl wk6lllllrrrrr
theorem wk6lllllrrr : SixW25P.Covered 32964 36080 33174 35252 63788 68848 31096 35252 29848 36080 :=
  SixW25P.covered_split3 33174 wk6lllllrrrl wk6lllllrrrr
theorem wk6lllllrr : SixW25P.Covered 29848 36080 33174 35252 63788 68848 31096 35252 29848 36080 :=
  SixW25P.covered_split0 32964 wk6lllllrrl wk6lllllrrr
theorem wk6lllllr : SixW25P.Covered 29848 36080 31096 35252 63788 68848 31096 35252 29848 36080 :=
  SixW25P.covered_split1 33174 wk6lllllrl wk6lllllrr
theorem wk6lllll : SixW25P.Covered 29848 36080 31096 35252 58728 68848 31096 35252 29848 36080 :=
  SixW25P.covered_split2 63788 wk6llllll wk6lllllr
theorem wk6llllr : SixW25P.Covered 29848 36080 31096 35252 58728 68848 35252 39408 29848 36080 :=
  SixW25P.covered_of_walk lbS hbas 1627097538870135765741648111584545491286843776182841021071204518533132784750909923351574811487683236316739254986547941594243648147232932075168075405298854343207599952875374294214938019541550862684723132605881390678523398830 200 29848 36080 31096 35252 58728 68848 35252 39408 29848 36080 747
    (by decide +kernel) (by decide)
theorem wk6llll : SixW25P.Covered 29848 36080 31096 35252 58728 68848 31096 39408 29848 36080 :=
  SixW25P.covered_split3 35252 wk6lllll wk6llllr
theorem wk6lllr : SixW25P.Covered 29848 36080 35252 39408 58728 68848 31096 39408 29848 36080 :=
  SixW25P.covered_of_walk lbS hbas 26746315052963205802144082113244850648020676131477236294591252265438810834932385689341511404692540294853439908103477052489354023532126980042834768787672242095113006303187117955744477270471374494879521378274348133230358051094745481929805978855143749480841202976394548427820972626043353074112098597256435763366566 200 29848 36080 35252 39408 58728 68848 31096 39408 29848 36080 1037
    (by decide +kernel) (by decide)
theorem wk6lll : SixW25P.Covered 29848 36080 31096 39408 58728 68848 31096 39408 29848 36080 :=
  SixW25P.covered_split1 35252 wk6llll wk6lllr
theorem wk6llr : SixW25P.Covered 29848 36080 31096 39408 58728 68848 31096 39408 36080 42312 :=
  SixW25P.covered_of_walk lbS hbas 8988385990259466815452735646510 200 29848 36080 31096 39408 58728 68848 31096 39408 36080 42312 112
    (by decide +kernel) (by decide)
theorem wk6ll : SixW25P.Covered 29848 36080 31096 39408 58728 68848 31096 39408 29848 42312 :=
  SixW25P.covered_split4 36080 wk6lll wk6llr
theorem wk6lr : SixW25P.Covered 36080 42312 31096 39408 58728 68848 31096 39408 29848 42312 :=
  SixW25P.covered_of_walk lbS hbas 5642149021939802629668026684804487225136750717177495171682 200 36080 42312 31096 39408 58728 68848 31096 39408 29848 42312 202
    (by decide +kernel) (by decide)
theorem wk6l : SixW25P.Covered 29848 42312 31096 39408 58728 68848 31096 39408 29848 42312 :=
  SixW25P.covered_split0 36080 wk6ll wk6lr
theorem wk6r : SixW25P.Covered 29848 42312 31096 39408 68848 78968 31096 39408 29848 42312 :=
  SixW25P.covered_of_walk lbS hbas 294393612158986517230240263623075696728748225066 200 29848 42312 31096 39408 68848 78968 31096 39408 29848 42312 167
    (by decide +kernel) (by decide)
theorem wk6 : SixW25P.Covered 29848 42312 31096 39408 58728 78968 31096 39408 29848 42312 :=
  SixW25P.covered_split2 68848 wk6l wk6r
theorem wk7llllllll : SixW25P.Covered 29848 36080 31096 35252 58728 63788 31096 39408 54736 73706 :=
  SixW25P.covered_of_walk lbS hbas 246516395761227718339716699231582234307392653798177315843337830301257208496510634101963036108438374619113538084507648713518073817298612760920830378003029398210601950226643409825324301581600172132202687187474020730244484957029035431338723844360170456225651829651944724478775903956844242200233304786550772394384482410106311503169111246840224203531230599364155584771733072411679738629662444059140815124759061108237660285205931420516547363160521840389099894097157124436869007432842651778607352800441152336969950746243950283737568591530460924933440531855345062189540849693928764820651410587161010309020034313881291311670031731689004154305982075257500874065695520480721490583330592019994918764223368033465006819679019194749207724844817491530 200 29848 36080 31096 35252 58728 63788 31096 39408 54736 73706 2447
    (by decide +kernel) (by decide)
theorem wk7lllllllrll : SixW25P.Covered 29848 36080 31096 35252 63788 68848 31096 39408 54736 59478 :=
  SixW25P.covered_of_walk lbS hbas 0 200 29848 36080 31096 35252 63788 68848 31096 39408 54736 59478 2
    (by decide +kernel) (by decide)
theorem wk7lllllllrlrll : SixW25P.Covered 29848 36080 31096 35252 63788 68848 31096 33174 59478 64221 :=
  SixW25P.covered_of_walk lbS hbas 28887717113170130 200 29848 36080 31096 35252 63788 68848 31096 33174 59478 64221 62
    (by decide +kernel) (by decide)
theorem wk7lllllllrlrlrl : SixW25P.Covered 29848 36080 31096 33174 63788 68848 33174 35252 59478 64221 :=
  SixW25P.covered_of_walk lbS hbas 14078828661617475927565980610892405342822680646 200 29848 36080 31096 33174 63788 68848 33174 35252 59478 64221 162
    (by decide +kernel) (by decide)
theorem wk7lllllllrlrlrrl : SixW25P.Covered 29848 32964 33174 35252 63788 68848 33174 35252 59478 64221 :=
  SixW25P.covered_of_walk lbS hbas 221188648234361510895369179338657335918665953331043449457552274125471947760654322535486790654407068662133269011338571120732763969578362581531189076230852588476329343920238935655976811837590082 200 29848 32964 33174 35252 63788 68848 33174 35252 59478 64221 642
    (by decide +kernel) (by decide)
theorem wk7lllllllrlrlrrrl : SixW25P.Covered 32964 36080 33174 35252 63788 68848 33174 35252 59478 61849 :=
  SixW25P.covered_of_walk lbS hbas 19547470 200 32964 36080 33174 35252 63788 68848 33174 35252 59478 61849 32
    (by decide +kernel) (by decide)
theorem wk7lllllllrlrlrrrrl : SixW25P.Covered 32964 36080 33174 35252 63788 66318 33174 35252 61849 64221 :=
  SixW25P.covered_of_walk lbS hbas 23119510185366854757468059948609216794745202232035094061984736980386721572911817339489700057727967952228254116486745132971131270336332676383364937003242275863806769489398615264410394467818343209899846000136769222012752121421955943632761467108003907799416613454306457418339707270661739496776805663053791687900972267444838435636877736686471476476974365342365094842583508850825390709344580944593832388219588685621093636870639298983453674744324037228623243213619848097781514780670967812745901094630909841131528990085475924943803101868980724382429859562404270382049653888714420874107517532825776976831747829708106744258513104883711475213536962239952262575158703040152306471203638026214297085832459330838182513521616702531655963243685033867478850644636672118367075408438767082680857623847648222868972318836161647453594560897914576734160491355282290197097561066517046199551115456758810431270930428558669212258409655503308309799535189135027472996092832547110057211118198813400464055061449980153626802412885954898001985440976020769083902337253642750624941148771922763255768976415921458915667497424608855720196295322852281927274549890430735374111741512711842145959821271821084615188695467962808726736740970647049436319010307298086744878277283958680112584178597688813760650148452834407389140321961761547744533278853486997398353739128073528701996967656939619263514392594743058976908361321412389053018122694004012789133435427836222984823977364765001137515380546787007393900846885632831522256742737816001092158084413510345539741590886608432075682699532190309566681647261812029600310180056130105872483366667765301545488698515984373194539964907554932027540376006115124695266793323736556471629261654540834737394237628725127911334065936402539404689128327774184951096668343915269963790534491908851358658413544643680516186798235954162625204648923888729488877861225106451865080411535970717008442513173995102599022797880806360198559153625109484487141630085718392877638407052435928953066631847715019797118056142988357913739566626059286448370502509925027439455567819313441861309072600811753884170401204198426530128066337914904855930678882 200 32964 36080 33174 35252 63788 66318 33174 35252 61849 64221 7027
    (by decide +kernel) (by decide)
theorem wk7lllllllrlrlrrrrr : SixW25P.Covered 32964 36080 33174 35252 66318 68848 33174 35252 61849 64221 :=
  SixW25P.covered_of_walk lbS hbas 29081275941774578908102373775675589177483203455470163243366022739900126700852640598080225024252920118221841585474573986055107118145111855018257420159847743298864775209893810228342310 200 32964 36080 33174 35252 66318 68848 33174 35252 61849 64221 607
    (by decide +kernel) (by decide)
theorem wk7lllllllrlrlrrrr : SixW25P.Covered 32964 36080 33174 35252 63788 68848 33174 35252 61849 64221 :=
  SixW25P.covered_split2 66318 wk7lllllllrlrlrrrrl wk7lllllllrlrlrrrrr
theorem wk7lllllllrlrlrrr : SixW25P.Covered 32964 36080 33174 35252 63788 68848 33174 35252 59478 64221 :=
  SixW25P.covered_split4 61849 wk7lllllllrlrlrrrl wk7lllllllrlrlrrrr
theorem wk7lllllllrlrlrr : SixW25P.Covered 29848 36080 33174 35252 63788 68848 33174 35252 59478 64221 :=
  SixW25P.covered_split0 32964 wk7lllllllrlrlrrl wk7lllllllrlrlrrr
theorem wk7lllllllrlrlr : SixW25P.Covered 29848 36080 31096 35252 63788 68848 33174 35252 59478 64221 :=
  SixW25P.covered_split1 33174 wk7lllllllrlrlrl wk7lllllllrlrlrr
theorem wk7lllllllrlrl : SixW25P.Covered 29848 36080 31096 35252 63788 68848 31096 35252 59478 64221 :=
  SixW25P.covered_split3 33174 wk7lllllllrlrll wk7lllllllrlrlr
theorem wk7lllllllrlrr : SixW25P.Covered 29848 36080 31096 35252 63788 68848 35252 39408 59478 64221 :=
  SixW25P.covered_of_walk lbS hbas 13707667325998598955702505963847762894910574337372390130764503489956238891043416036857079087890065784389092582446141300979819021641598333185211417728315420667989731554091543021965601997115215588570470357589058969612887758126273053294 200 29848 36080 31096 35252 63788 68848 35252 39408 59478 64221 782
    (by decide +kernel) (by decide)
theorem wk7lllllllrlr : SixW25P.Covered 29848 36080 31096 35252 63788 68848 31096 39408 59478 64221 :=
  SixW25P.covered_split3 35252 wk7lllllllrlrl wk7lllllllrlrr
theorem wk7lllllllrl : SixW25P.Covered 29848 36080 31096 35252 63788 68848 31096 39408 54736 64221 :=
  SixW25P.covered_split4 59478 wk7lllllllrll wk7lllllllrlr
theorem wk7lllllllrrlll : SixW25P.Covered 29848 36080 31096 33174 63788 68848 31096 35252 64221 68963 :=
  SixW25P.covered_of_walk lbS hbas 42023902751001306648781169772293990938497687146372398404851721793664155343614392261433973176728246611085187379862288980064694498309523976503309773199084159863612552891480493954256155392051658873485688321103958547190855878 200 29848 36080 31096 33174 63788 68848 31096 35252 64221 68963 737
    (by decide +kernel) (by decide)
theorem wk7lllllllrrllrl : SixW25P.Covered 29848 32964 33174 35252 63788 68848 31096 35252 64221 68963 :=
  SixW25P.covered_of_walk lbS hbas 137702814747354217528490822744269493424414247369607595118277174911145104904486635592948645177000010956415852634201355170857079747788944756866767605195105007675233138078416549765099979693803060270097492923529560772202435907258482872949276662625035515632170099912374952656025339127804681323441616864290375494493432167548696721701479403101101627279240489960122407330124643295927216167204971308172883613960885450478557038203582455682754539059067096106554757321350019421000600371921916018977374418219746956463111437902310736319730565306624849499046782653925432636018071752089937258494668100393827633084614875758419276837773047676225500041324830146 200 29848 32964 33174 35252 63788 68848 31096 35252 64221 68963 2137
    (by decide +kernel) (by decide)
theorem wk7lllllllrrllrrl : SixW25P.Covered 32964 36080 33174 35252 63788 68848 31096 33174 64221 68963 :=
  SixW25P.covered_of_walk lbS hbas 2580997049623990126449115774846982105118163029074065596312049944415535090632009320380828531308510755789131473917356494 200 32964 36080 33174 35252 63788 68848 31096 33174 64221 68963 397
    (by decide +kernel) (by decide)
theorem wk7lllllllrrllrrrlllll : SixW25P.Covered 32964 34522 33174 34213 63788 65053 33174 35252 64221 66592 :=
  SixW25P.covered_of_walk lbS hbas 46916075529980852373588051505870845544568347348367987369533810495792865175584620768646081912803254042735705924118766191690220865285943742876068333495890728824201695283642763188818806418389588923590328200511675725095397980757441101029442767828378110134162083646586649237544696352173448204728278735877478789947615467184553805324046587127722626582678631114377126138466727632089586324444188119876048240563157370697012547986198315299222116451160054150838677041375281626534311882573528597577130374602922023305160777546762561906938920925754491513973284248347249065880447448664932156603682863920446620421203048983585340143931470042589494976263723611763524034457812310485643325259179600035083190938335909426686386683295350403944182201616081230627565183604013693599143683243344462597317671830086412350937476976684210622898564066451098895081325483026504065923264594091987725120182584172818708597897526381976142266334753496270013912783009539140731069456583424336045541203221935129314691836578873786685341139927867904737242861526565282699684265033177106213229496330723866569077404487925882586305282884079893340817119102349893814679724255076365892962859922919914256217853506290169910834870033241085948464420615924309405079716047128647821754505696819158814368584585635460754963758447047083029422550353033405152181540544455100912866771587005581473167274616583612716445924837261285387337745933307576970482455397081248452153746959772087979443679329843382306913404703409478173818266547951562238894415698112111438934259062011170818903474345282357056522007895048098433681541754821918267885892356690 200 32964 34522 33174 34213 63788 65053 33174 35252 64221 66592 5242
    (by decide +kernel) (by decide)
theorem wk7lllllllrrllrrrllllr : SixW25P.Covered 32964 34522 33174 34213 65053 66318 33174 35252 64221 66592 :=
  SixW25P.covered_of_walk lbS hbas 272560574052557145371366609911606866923299140417310658907011473670099572614484164581150790151043419551108311220921753142652117113763902924308975406708796597763237956819044247484544458791674286433171534700972488758375288122735193007303379791734432676264699943351200397723443152063185010751629386016626000479301451118235101202382677518880965851064660147168438822139007276036548791776574922316287792112722315102166553818888896561782520366512035275481036551971312259192995769038291867075262813045149898720190144075125159785103831244039393386775643155098476233512550415395297263427733240682234999645773026022990823828223792559809709142761663692464945380535667082735027165374749516937352111194234505778628876339296414938974958812525479799448373019385442840119235628434600906758596673520774683154549609709878649390830267652322050318288701467712601103816231419344541491115993374058277807523036845773748873786877596486621732053429320102269017930064742092002292629898902314306160256004679459981410150180030512760058117131930226233348992602196212066940750741432575629245778861629835569532876542176764927082655161595943237097520797337738546359218650010949323253385115769901173978240219895541022905066969908834593623760341456032258086905746047197258829059932267006038831469244346687279066724260586090503267056844380005365582155874986750124202779180122505663996436512355367641946978295766416488062482414655955566 200 32964 34522 33174 34213 65053 66318 33174 35252 64221 66592 4647
    (by decide +kernel) (by decide)
theorem wk7lllllllrrllrrrllll : SixW25P.Covered 32964 34522 33174 34213 63788 66318 33174 35252 64221 66592 :=
  SixW25P.covered_split2 65053 wk7lllllllrrllrrrlllll wk7lllllllrrllrrrllllr
theorem wk7lllllllrrllrrrlllr : SixW25P.Covered 32964 34522 33174 34213 63788 66318 33174 35252 66592 68963 :=
  SixW25P.covered_of_walk lbS hbas 64547749994830462049266027324003513434214304289103856962545091262389558274036943396333017025402347492683127690792678222739334746806279270463350031351634487737605806795596877453037487870866874118671640051018918298302763936292327646088309390334981233828518594148570708222964999226567733773246424771852885106245571355734706349423536787989858709382687798589445595861192397771400279049573503750166191246356127888940764391311644986405682736104340494288536933515186639058377497060292586583412753815105881537879640108333310811240111005378425561609795670323500590883670588552052589459484867079568531675700588178441911486136536182250199888626984317926692201743428873027317016803329837682689743788958236998268390371400101982453555355281800323650623259189410389716208989876051660190656619588581239403861812051875873620926867082706896726587876868933318879499975767407497064293176818866331646421134016914401492740289398511199240685061192104914668710013597582459482038984796983875832679989136719770286 200 32964 34522 33174 34213 63788 66318 33174 35252 66592 68963 3282
    (by decide +kernel) (by decide)
theorem wk7lllllllrrllrrrlll : SixW25P.Covered 32964 34522 33174 34213 63788 66318 33174 35252 64221 68963 :=
  SixW25P.covered_split4 66592 wk7lllllllrrllrrrllll wk7lllllllrrllrrrlllr
theorem wk7lllllllrrllrrrllr : SixW25P.Covered 32964 34522 34213 35252 63788 66318 33174 35252 64221 68963 :=
  SixW25P.covered_of_walk lbS hbas 183213643330667712336991581062054746934180715408032695997441950782163968315053627622038452500741377605017087719116476631093832192462023757201997205361615307731763456502672898519786817359289917840691818936083379311468466869255895745795464007910711939445845717818368306084538866320177392608811279688321372954754040632770422425463177227707955430988086701559706505166065872262921714278466433010834856107756833301407728749951717309350832402791590274243270315939031167906642612006911956751894820211042183050765154449567546838164840139959625543635256488643790685504327762391320251647245635777262554136282822584034892369372561078973886028402243456542611318401963767155029540087511089065949386135829465323370471444483425571290325201725454356730546 200 32964 34522 34213 35252 63788 66318 33174 35252 64221 68963 2457
    (by decide +kernel) (by decide)
theorem wk7lllllllrrllrrrll : SixW25P.Covered 32964 34522 33174 35252 63788 66318 33174 35252 64221 68963 :=
  SixW25P.covered_split1 34213 wk7lllllllrrllrrrlll wk7lllllllrrllrrrllr
theorem wk7lllllllrrllrrrlr : SixW25P.Covered 34522 36080 33174 35252 63788 66318 33174 35252 64221 68963 :=
  SixW25P.covered_of_walk lbS hbas 436536710749085488466923015668102463695192603074467464540517968028519392244621575860105222433570692584330048438887898641854327419802397740527359274103557225173120194913238535735909231729796336842204270735045044513553289691853257266510366317888727181075217950238007504566850402794603111403028359974 200 34522 36080 33174 35252 63788 66318 33174 35252 64221 68963 992
    (by decide +kernel) (by decide)
theorem wk7lllllllrrllrrrl : SixW25P.Covered 32964 36080 33174 35252 63788 66318 33174 35252 64221 68963 :=
  SixW25P.covered_split0 34522 wk7lllllllrrllrrrll wk7lllllllrrllrrrlr
theorem wk7lllllllrrllrrrr : SixW25P.Covered 32964 36080 33174 35252 66318 68848 33174 35252 64221 68963 :=
  SixW25P.covered_of_walk lbS hbas 1853706566953077436877783339376050762754753118000807913335379191705111086910520261996091011571182689248461202069919420083289289154696660577418770471857199442213027413843929213687072509089200771754380209307455577655367648159659691095704955327986909817166903638862787927604165073704765946338949270945571674821530193667414772671265753262042025566321384288319589646250155204451807559683435429810845501726399712553400995398820837097299688469030 200 32964 36080 33174 35252 66318 68848 33174 35252 64221 68963 1462
    (by decide +kernel) (by decide)
theorem wk7lllllllrrllrrr : SixW25P.Covered 32964 36080 33174 35252 63788 68848 33174 35252 64221 68963 :=
  SixW25P.covered_split2 66318 wk7lllllllrrllrrrl wk7lllllllrrllrrrr
theorem wk7lllllllrrllrr : SixW25P.Covered 32964 36080 33174 35252 63788 68848 31096 35252 64221 68963 :=
  SixW25P.covered_split3 33174 wk7lllllllrrllrrl wk7lllllllrrllrrr
theorem wk7lllllllrrllr : SixW25P.Covered 29848 36080 33174 35252 63788 68848 31096 35252 64221 68963 :=
  SixW25P.covered_split0 32964 wk7lllllllrrllrl wk7lllllllrrllrr
theorem wk7lllllllrrll : SixW25P.Covered 29848 36080 31096 35252 63788 68848 31096 35252 64221 68963 :=
  SixW25P.covered_split1 33174 wk7lllllllrrlll wk7lllllllrrllr
theorem wk7lllllllrrlr : SixW25P.Covered 29848 36080 31096 35252 63788 68848 31096 35252 68963 73706 :=
  SixW25P.covered_of_walk lbS hbas 1047457802241778 200 29848 36080 31096 35252 63788 68848 31096 35252 68963 73706 57
    (by decide +kernel) (by decide)
theorem wk7lllllllrrl : SixW25P.Covered 29848 36080 31096 35252 63788 68848 31096 35252 64221 73706 :=
  SixW25P.covered_split4 68963 wk7lllllllrrll wk7lllllllrrlr
theorem wk7lllllllrrr : SixW25P.Covered 29848 36080 31096 35252 63788 68848 35252 39408 64221 73706 :=
  SixW25P.covered_of_walk lbS hbas 41992658535062293488246344917237871923700467618271161727756926587712715257086074583558704219383040883412653323954763628379226321738902372622796504950813870551948733643773199898862184085688297906901547793572427201237971959449206724894156590 200 29848 36080 31096 35252 63788 68848 35252 39408 64221 73706 802
    (by decide +kernel) (by decide)
theorem wk7lllllllrr : SixW25P.Covered 29848 36080 31096 35252 63788 68848 31096 39408 64221 73706 :=
  SixW25P.covered_split3 35252 wk7lllllllrrl wk7lllllllrrr
theorem wk7lllllllr : SixW25P.Covered 29848 36080 31096 35252 63788 68848 31096 39408 54736 73706 :=
  SixW25P.covered_split4 64221 wk7lllllllrl wk7lllllllrr
theorem wk7lllllll : SixW25P.Covered 29848 36080 31096 35252 58728 68848 31096 39408 54736 73706 :=
  SixW25P.covered_split2 63788 wk7llllllll wk7lllllllr
theorem wk7llllllr : SixW25P.Covered 29848 36080 35252 39408 58728 68848 31096 39408 54736 73706 :=
  SixW25P.covered_of_walk lbS hbas 564181590210144559209503211735065343897922403641420582813431076052285146482503889295919224100286140136544947895525616276983053755713609526290942740631494032902822 200 29848 36080 35252 39408 58728 68848 31096 39408 54736 73706 547
    (by decide +kernel) (by decide)
theorem wk7llllll : SixW25P.Covered 29848 36080 31096 39408 58728 68848 31096 39408 54736 73706 :=
  SixW25P.covered_split1 35252 wk7lllllll wk7llllllr
theorem wk7lllllr : SixW25P.Covered 36080 42312 31096 39408 58728 68848 31096 39408 54736 73706 :=
  SixW25P.covered_of_walk lbS hbas 2480503431718 200 36080 42312 31096 39408 58728 68848 31096 39408 54736 73706 47
    (by decide +kernel) (by decide)
theorem wk7lllll : SixW25P.Covered 29848 42312 31096 39408 58728 68848 31096 39408 54736 73706 :=
  SixW25P.covered_split0 36080 wk7llllll wk7lllllr
theorem wk7llllr : SixW25P.Covered 29848 42312 31096 39408 68848 78968 31096 39408 54736 73706 :=
  SixW25P.covered_of_walk lbS hbas 33111192764951381621538484871389866 200 29848 42312 31096 39408 68848 78968 31096 39408 54736 73706 122
    (by decide +kernel) (by decide)
theorem wk7llll : SixW25P.Covered 29848 42312 31096 39408 58728 78968 31096 39408 54736 73706 :=
  SixW25P.covered_split2 68848 wk7lllll wk7llllr
theorem wk7lllr : SixW25P.Covered 29848 42312 31096 39408 58728 78968 31096 39408 73706 92676 :=
  SixW25P.covered_of_walk lbS hbas 32763324746322 200 29848 42312 31096 39408 58728 78968 31096 39408 73706 92676 52
    (by decide +kernel) (by decide)
theorem wk7lll : SixW25P.Covered 29848 42312 31096 39408 58728 78968 31096 39408 54736 92676 :=
  SixW25P.covered_split4 73706 wk7llll wk7lllr
theorem wk7llr : SixW25P.Covered 29848 42312 31096 39408 58728 78968 31096 39408 92676 130616 :=
  SixW25P.covered_of_walk lbS hbas 11084080705907265743680767163388527933262981740571088983388271625430693325877777256618197579302515413014743439416620364237889932460190062883621240495136517630411016264990392236580530582873450572760608390479388669377790579207462702602125786708025117122214635629770985308374448966191491361228014077482977130010356027458837128622841492640452010957903901813890507629435215760518156961134274146713407095413621755723075815984339276265782211962617053169735154810672404334396054701129332730810235359274255983980192015470582203403831031900954115440235602386862108483050624440580033152660559801875156352509801586101636111577967159854511420237762783410551805342694433756072419391747729625022214246900329517583299749065687734805520124862996914021321604680885393666525657632595567771778052148996372357658061243388703011238477887151107382673226485355845060333042638779775850136317394374163698492490369358468946206672749141043755852164669414258295085189050378461594410696871653943580271641120599779402142412806257883840014779403188188539909582489087803892870773366693677722141332936238107200173235721221470528683433008707143109753895888474922860259093341686930653650987943456032024269754396505227499712500951843518855164029617917982060944443100623774780873858798301482900761265572149395779231540999754000697080283874881836270256428631103850841706042763314096736238413603856963914819423489731532658787222366826524161795236156627773729870842854401430664416633212308088054011928294723901682051389955841339943498536723658493563097438009488925352190635602349616478231014534926949990743103839053632866331521472305273329803347611728615047206563790507150047694543108954377609689766909653016730958306918266748634126532047858913798404258866730 200 29848 42312 31096 39408 58728 78968 31096 39408 92676 130616 5712
    (by decide +kernel) (by decide)
theorem wk7ll : SixW25P.Covered 29848 42312 31096 39408 58728 78968 31096 39408 54736 130616 :=
  SixW25P.covered_split4 92676 wk7lll wk7llr
theorem wk7lr : SixW25P.Covered 29848 42312 31096 39408 58728 78968 31096 39408 130616 206496 :=
  SixW25P.covered_of_walk lbS hbas 25479140205148958179302198531657287905158835189598898 200 29848 42312 31096 39408 58728 78968 31096 39408 130616 206496 182
    (by decide +kernel) (by decide)
theorem wk7l : SixW25P.Covered 29848 42312 31096 39408 58728 78968 31096 39408 54736 206496 :=
  SixW25P.covered_split4 130616 wk7ll wk7lr
theorem wk7r : SixW25P.Covered 29848 42312 31096 39408 58728 78968 31096 39408 206496 358256 :=
  SixW25P.covered_of_walk lbS hbas 0 200 29848 42312 31096 39408 58728 78968 31096 39408 206496 358256 2
    (by decide +kernel) (by decide)
theorem wk7 : SixW25P.Covered 29848 42312 31096 39408 58728 78968 31096 39408 54736 358256 :=
  SixW25P.covered_split4 206496 wk7l wk7r
theorem wk8llll : SixW25P.Covered 29848 36080 31096 39408 58728 68848 58552 63950 29848 42312 :=
  SixW25P.covered_of_walk lbS hbas 87914186488195440986730631847184066002973026106155092059295001840066326741443734172782969293863907194928584861801732191660136053479283918825125723763025335011970426320413933179538994123259078512004242963404132889796558824013201036428192542754635260664007250233597259927119445309275391621777482459192658616888458924285556198484007499284196606343706304254055524941332188573162966242510 200 29848 36080 31096 39408 58728 68848 58552 63950 29848 42312 1282
    (by decide +kernel) (by decide)
theorem wk8lllrlll : SixW25P.Covered 29848 36080 31096 35252 58728 63788 63950 69348 29848 36080 :=
  SixW25P.covered_of_walk lbS hbas 23941085942284950052746214870961997710590844509146848820557324919986826046936760703364999154222087468434949556382854113812693198143472642470142084671364768064660456263054862538 200 29848 36080 31096 35252 58728 63788 63950 69348 29848 36080 587
    (by decide +kernel) (by decide)
theorem wk8lllrllrl : SixW25P.Covered 29848 36080 31096 33174 63788 68848 63950 69348 29848 36080 :=
  SixW25P.covered_of_walk lbS hbas 76071849978849304999295944734884620038284781250534856173747189059302379410818287686 200 29848 36080 31096 33174 63788 68848 63950 69348 29848 36080 282
    (by decide +kernel) (by decide)
theorem wk8lllrllrrl : SixW25P.Covered 29848 32964 33174 35252 63788 68848 63950 69348 29848 36080 :=
  SixW25P.covered_of_walk lbS hbas 16037024265091850390168241246230433144570425689312377523395853376028180829530460769134187112567643360106536108983831456854294563189846241712488411569111793934164721915279345181701977058477312732106845421801428431432422474180384919529456503040191340271683784788261310453472295376608673664354120336312395906321805900806870419892832880706 200 29848 32964 33174 35252 63788 68848 63950 69348 29848 36080 1117
    (by decide +kernel) (by decide)
theorem wk8lllrllrrrl : SixW25P.Covered 32964 36080 33174 35252 63788 68848 63950 69348 29848 32964 :=
  SixW25P.covered_of_walk lbS hbas 57495955242763346 200 32964 36080 33174 35252 63788 68848 63950 69348 29848 32964 72
    (by decide +kernel) (by decide)
theorem wk8lllrllrrrrll : SixW25P.Covered 32964 36080 33174 35252 63788 66318 63950 66649 32964 36080 :=
  SixW25P.covered_of_walk lbS hbas 248189215901953879326793553272390049902700518752614272591671684224000357714746666972808613010716448491155352630083445075406234089252021973115925975769807529940481446393865208191894658054540752875674076857828720759747678751545145735388406678817912528486853994685977030978999078469092287240427008921489101005509965668952850754810922325348395950912231941451055597309763051809291871008635485104935611762956958572313017419492682656812237349551685430701393231451667457951968079908916951961252518283844163662725843289126018033804129135920704964077090916817892757146759885436252233006785163233063600159421402809572534743909143539395462700074678184600069394028191729432277238643799590059163825449016243241645059938941596886869766020237320683004921435255615393162823853806253445380845401704826806783821215731655038257101230699579492910817178287498207598816961944731594521447841495775574748047026818382314299774625221645109932653346202734428218024509848903264872086980881996130715573421664095779171591000170188320549135360676432479701827823115471574653905241556663076360487844003120308498870797421249644802067910700642 200 32964 36080 33174 35252 63788 66318 63950 66649 32964 36080 3682
    (by decide +kernel) (by decide)
theorem wk8lllrllrrrrlr : SixW25P.Covered 32964 36080 33174 35252 66318 68848 63950 66649 32964 36080 :=
  SixW25P.covered_of_walk lbS hbas 9746316378505596966019129013887255829050997571073773054360780618154412462732163130526309910172090182533413187007274525754825121937516366133083242330311583847260736349165889507898073111784238057627715612443019163547094780820476269857424374473790243795240567335649503180350541888576422355265354494664453156616982430197232737063372436164627186024768775943496080606081813300657984980192314470040835239724944212251424303893071373684955596781463166317786105399660699865821959695693711243158233040994557429712177229248742644567610719270243987233447009342126066655998734967854249634045933049571570535958340588665545365167704034852530088840620172557566555862615078692396810078624048984506387972237554928532457173195263159483757131517503434432998517131229976479295364614183723838897934459023360122449446437252619537635748301322232256867949557160597053918340821877801173503745026440328512757016665936390693813181633266713643937904662495925764617031739333933302087088891621046404215391602760728261896879186998539525461964885054275261012829986447558208769337429401086588513424613172369429674511532126979325578862567400829939973988148565763630616123469493451033637286407054661099528518373744411949344277305638416313585845327716481992168809781758676738508746806886922228572302314362772653410266722 200 32964 36080 33174 35252 66318 68848 63950 66649 32964 36080 4267
    (by decide +kernel) (by decide)
theorem wk8lllrllrrrrl : SixW25P.Covered 32964 36080 33174 35252 63788 68848 63950 66649 32964 36080 :=
  SixW25P.covered_split2 66318 wk8lllrllrrrrll wk8lllrllrrrrlr
theorem wk8lllrllrrrrr : SixW25P.Covered 32964 36080 33174 35252 63788 68848 66649 69348 32964 36080 :=
  SixW25P.covered_of_walk lbS hbas 9339279391198213160151391113815510035109444542362568921714483393381747504318404034899184162512245033784056139632004837963675595012342605816263309835722531482988387913793483027841322132278656894245433821112542317746841924973202878615830377027889397331017639458365548213252986093185087852251986103996834991931109867025598439389445295314879284541108744056211296395809342268980131759696224247375567378093173123951916439338322925830391252542516078604841121783586839924840450693899069558765870485328363391302204705967487385643396119138732761834 200 32964 36080 33174 35252 63788 68848 66649 69348 32964 36080 1797
    (by decide +kernel) (by decide)
theorem wk8lllrllrrrr : SixW25P.Covered 32964 36080 33174 35252 63788 68848 63950 69348 32964 36080 :=
  SixW25P.covered_split3 66649 wk8lllrllrrrrl wk8lllrllrrrrr
theorem wk8lllrllrrr : SixW25P.Covered 32964 36080 33174 35252 63788 68848 63950 69348 29848 36080 :=
  SixW25P.covered_split4 32964 wk8lllrllrrrl wk8lllrllrrrr
theorem wk8lllrllrr : SixW25P.Covered 29848 36080 33174 35252 63788 68848 63950 69348 29848 36080 :=
  SixW25P.covered_split0 32964 wk8lllrllrrl wk8lllrllrrr
theorem wk8lllrllr : SixW25P.Covered 29848 36080 31096 35252 63788 68848 63950 69348 29848 36080 :=
  SixW25P.covered_split1 33174 wk8lllrllrl wk8lllrllrr
theorem wk8lllrll : SixW25P.Covered 29848 36080 31096 35252 58728 68848 63950 69348 29848 36080 :=
  SixW25P.covered_split2 63788 wk8lllrlll wk8lllrllr
theorem wk8lllrlr : SixW25P.Covered 29848 36080 35252 39408 58728 68848 63950 69348 29848 36080 :=
  SixW25P.covered_of_walk lbS hbas 67344122201374321917717396460798359136354942931068957245990 200 29848 36080 35252 39408 58728 68848 63950 69348 29848 36080 207
    (by decide +kernel) (by decide)
theorem wk8lllrl : SixW25P.Covered 29848 36080 31096 39408 58728 68848 63950 69348 29848 36080 :=
  SixW25P.covered_split1 35252 wk8lllrll wk8lllrlr
theorem wk8lllrr : SixW25P.Covered 29848 36080 31096 39408 58728 68848 63950 69348 36080 42312 :=
  SixW25P.covered_of_walk lbS hbas 9980585393959773635289800440208113685878308769835464447025977436428018326762792088676146 200 29848 36080 31096 39408 58728 68848 63950 69348 36080 42312 302
    (by decide +kernel) (by decide)
theorem wk8lllr : SixW25P.Covered 29848 36080 31096 39408 58728 68848 63950 69348 29848 42312 :=
  SixW25P.covered_split4 36080 wk8lllrl wk8lllrr
theorem wk8lll : SixW25P.Covered 29848 36080 31096 39408 58728 68848 58552 69348 29848 42312 :=
  SixW25P.covered_split3 63950 wk8llll wk8lllr
theorem wk8llr : SixW25P.Covered 36080 42312 31096 39408 58728 68848 58552 69348 29848 42312 :=
  SixW25P.covered_of_walk lbS hbas 428270118 200 36080 42312 31096 39408 58728 68848 58552 69348 29848 42312 37
    (by decide +kernel) (by decide)
theorem wk8ll : SixW25P.Covered 29848 42312 31096 39408 58728 68848 58552 69348 29848 42312 :=
  SixW25P.covered_split0 36080 wk8lll wk8llr
theorem wk8lr : SixW25P.Covered 29848 42312 31096 39408 68848 78968 58552 69348 29848 42312 :=
  SixW25P.covered_of_walk lbS hbas 1034724898403993439682376646189738 200 29848 42312 31096 39408 68848 78968 58552 69348 29848 42312 117
    (by decide +kernel) (by decide)
theorem wk8l : SixW25P.Covered 29848 42312 31096 39408 58728 78968 58552 69348 29848 42312 :=
  SixW25P.covered_split2 68848 wk8ll wk8lr
theorem wk8r : SixW25P.Covered 29848 42312 31096 39408 58728 78968 69348 80144 29848 42312 :=
  SixW25P.covered_of_walk lbS hbas 649821698831609518 200 29848 42312 31096 39408 58728 78968 69348 80144 29848 42312 67
    (by decide +kernel) (by decide)
theorem wk8 : SixW25P.Covered 29848 42312 31096 39408 58728 78968 58552 80144 29848 42312 :=
  SixW25P.covered_split3 69348 wk8l wk8r
theorem wk9 : SixW25P.Covered 29848 42312 31096 39408 58728 78968 58552 80144 54736 358256 :=
  SixW25P.covered_of_walk lbS hbas 160928838639879686251990796140075902005616622584436685711246021290716581017880577275113376858829183544616734211575906203570457609597974054424997608206735143200236527516933294451721946979680352469854223154731658813756455142675484099996690761917848469888745137264741665451227905967749267186047058388670684925849285333815397074828174207433679399266703722492048885820416574012190117255208190720376498137095444059539514280131461428440537026939585327705807261619233873660158839002125816902107710540340091049733695443071433340098923580393693604243139914681432350088848190770575334201746782294135801249342900811072911131884722747588364191086023483924723102376434274192540525995075690137150627385456448390406081631709503019321257631343629403888959674016165604057607718548612310601345280666153582062789498432618909680251285845208441359125475632318878720141182642033493371509311804676192743661410247119069448116628112888971116590898938623590052907416623643987413798873613894351834445454168411352901101220203825848331300434742177429753581716795923834747383410689285341593703417798937431846966862132637627169287498677204115944059698 200 29848 42312 31096 39408 58728 78968 58552 80144 54736 358256 3727
    (by decide +kernel) (by decide)
theorem wk10 : SixW25P.Covered 29848 42312 31096 39408 58728 78968 82632 250598 29848 42312 :=
  SixW25P.covered_of_walk lbS hbas 94779655982636745032079759670572064398896914842498256045534161409672347957118001509431860404239528968483291229083340895333550318003134140624231788876885851662069212579536498749606331437870830 200 29848 42312 31096 39408 58728 78968 82632 250598 29848 42312 642
    (by decide +kernel) (by decide)
theorem wk11 : SixW25P.Covered 29848 42312 31096 39408 58728 78968 82632 250598 54736 358256 :=
  SixW25P.covered_of_walk lbS hbas 242480987349432872750 200 29848 42312 31096 39408 58728 78968 82632 250598 54736 358256 82
    (by decide +kernel) (by decide)
theorem wk12 : SixW25P.Covered 29848 42312 31096 39408 83848 289438 31096 39408 29848 42312 :=
  SixW25P.covered_of_walk lbS hbas 995710343061964232669538895371873332353456548556686717392701604567168311940403614632010828855318941914989798124740672013326070757353300107714575311455392607993003161326690606133833996478428537029478314012331032158191152443825454761458072562017689971188622838217330772902067511320606345048081320999833088564866546911054931744572080369418978287418581929079793633756142880473612308843017611844540594761345975013036036727183150194209651745883163398920936351277762352574658961385161286876142829380384796862006951663566323376061764528189734127999143989568683052449377757270890698481127792036613649269567283065754995974712778506069146055194685088894532908591682919869710678524480801659557373094104800672243155461977397032438711455212615341628906614235548606801567221198852809147170299977311283559282459710760141770190571750257956665176879483354449698333545858737281878591170046864206593388037812249905539596403536035662543958018741671085440933164656146609080180877488058458745825940293794069434145359059733590895964668107768818872302432978987368640624862891724603026462472991866772933562504141925059544027869140704430961647813713693956922993723514931044616025576310458430543403129750978799743467335797251398266860517493547444706871499376053424698761572963380217205471017805499458817571893540415751501737710897631361179205298614497643215135743967942134586254114270346916204937388160583462112217477187986005721683982921460425556111026497332091751444654440620998272535681471994627017318214807156632356891207647553231523045448994891126257377785981129448110525914253716440854716364688082031693427915784032956438425550252559351931480979832095324817324363947595866932416241030048060128552694695832085595781722671975193139007781722635091751995030510106199643579905153591249993942691977822304090881338796785050822479427476161389966863752537847807415681040216970860894503014843486899670992082575092359925651914588834004487703606078933373278376591685000673447256176460860776544859726047231108201306223921590296029866 200 29848 42312 31096 39408 83848 289438 31096 39408 29848 42312 6647
    (by decide +kernel) (by decide)
theorem wk13 : SixW25P.Covered 29848 42312 31096 39408 83848 289438 31096 39408 54736 358256 :=
  SixW25P.covered_of_walk lbS hbas 30605856875752029388817755043351093968537653729267211596584368591229447451060105024801257117757400797167639616619094388563438415990185182144690105317064708655486211738220952719082244627737399127456180765882293005713845406381896937839322080486615085780213021178572629843467193657582835907268396751220466326479076895906520177244263150788735175220303287610581027571444059212714768579537808979888854929373826112671662312418592987273320455001836532163920798543097528306011820316964306649709027652621234213861037020822614319820132808314633711998536699329050652278713625880865756715455095052438678775342682928173920617354878856344716557521993489296495240738405041571490522684391173790232353116591938053157427342469490056016808748627575668560087183628108636092559891970769173644144018324136249038005402548150703712323678202208057683559177723751859767321786739392183771678259394197886868462372566942259031896631486696920346611294723376984823123543474852984972428322452913534045160932278786029617933432189085877286366862438315352600997395772616444390768230922204165112353045024103547431960612219519997179912598691363304754843374292371663332314153859250980022486233594194900962745737970028128330342654061511306180207198019631981865797628176417952575473243228694057548544336679361342084849798285876867748255163123084132575391715272907430926824886375138594742480623973973839849240604565627426522408640692801464031020237361939654181705976960877335148036576525366984056852330571479501171250555841659759238871327591752713338925167976370801808681015881317376063170038705315600768470354073858532740478535313988945410281084267444930265691859414400381364269270293398228227221388383235350148669933675242849437868410367875453648710990712620634687628275809080830667920344222652741183321367437024357800687039231155693025741205108790957109543713030368080945285863217776587382256374650459773273124098730118622685994 200 29848 42312 31096 39408 83848 289438 31096 39408 54736 358256 6287
    (by decide +kernel) (by decide)
theorem wk14 : SixW25P.Covered 29848 42312 31096 39408 83848 289438 58552 80144 29848 42312 :=
  SixW25P.covered_of_walk lbS hbas 104183233907071400690886256074954536045483526642759119635698404805190319865235257316251966509400117879864866835387598471781068114385854975174419556155696723073142153722615423761365820385811036392250039270733787895933034039538960382207573670075472910255659204471745382854576851687766659555310662195605444995069795056476211720433519218632879227922728077120400997066153157175360209897581226 200 29848 42312 31096 39408 83848 289438 58552 80144 29848 42312 1287
    (by decide +kernel) (by decide)
theorem wk15 : SixW25P.Covered 29848 42312 31096 39408 83848 289438 58552 80144 54736 358256 :=
  SixW25P.covered_of_walk lbS hbas 613192324924698250394882819291041636494122 200 29848 42312 31096 39408 83848 289438 58552 80144 54736 358256 147
    (by decide +kernel) (by decide)
theorem wk16 : SixW25P.Covered 29848 42312 31096 39408 83848 289438 82632 250598 29848 42312 :=
  SixW25P.covered_of_walk lbS hbas 46747848978154 200 29848 42312 31096 39408 83848 289438 82632 250598 29848 42312 57
    (by decide +kernel) (by decide)
theorem wk17 : SixW25P.Covered 29848 42312 31096 39408 83848 289438 82632 250598 54736 358256 :=
  SixW25P.covered_of_walk lbS hbas 2871718634 200 29848 42312 31096 39408 83848 289438 82632 250598 54736 358256 42
    (by decide +kernel) (by decide)
theorem wk18lll : SixW25P.Covered 29848 42312 58552 63950 31168 39280 31096 39408 29848 36080 :=
  SixW25P.covered_of_walk lbS hbas 7156878854042782491777758254281962483766436052812867166303469127480901621590883792714889803336822961674918195698368587398324932288125136710423177598636930439452450017416569062764382420988575436230282871848245325920246593788472374743356739465735909296549233937382115316278720080465249579725597188653456886832490570887829576786059414236209879938529117949513938982871990284016248529528036543506410211129436047445223807608708129058874243219306032739870034644559128058917372468726253842957669496145475509317127782754455134126951858492846392774 200 29848 42312 58552 63950 31168 39280 31096 39408 29848 36080 1797
    (by decide +kernel) (by decide)
theorem wk18llr : SixW25P.Covered 29848 42312 63950 69348 31168 39280 31096 39408 29848 36080 :=
  SixW25P.covered_of_walk lbS hbas 61989197623884988796706176914150756037401154311149582027718129718785911545874318881512754151361691757724768726519554793280753994938286114892139238141573249664099974834563489183167430360677232215287540326763373487165358249979629784478120499363976620015340897944426172071363251403425266955480435865568788670965212302148013146951111688559939503432223550194968332479543621732594699300475954965267449126242988732119614284769565771028363923674074248119039090837395196257146253740460893492346167884794303026372995339604421799821950841937208432846517830660702955136386327672085202755440576871879025792735339787634431411724017965001871429777358171720586567407378882437796871608572998463884351714552535419914668360078537723786412791823782207511272337687797144957629956125535882343839661450699068189819270693246082861924729084542120145653604447794197339731915176729395070858915995005246428338302995763852413267659192760294723750930709906502649946404575797077343097197356781052113037994582512790241865626745268883581310984727648565719262401985768579345352758333790977661361412510751843866045462430449641826260421212361953181893389944476070037958367374675316179978152423978341061333583063352862047378425069870738513393751201826026153036686304484451028197254067967187283711241717113501521361893067750924922530502543060112042593733760272172918884220611627443205976134420576726489250359333818545447883179095170305383091535076924918398449206861346371372221612408711653164639514956400691765570278337515053525000873066261813079225449782017237971144129893745320484521314973094898910771538316848036093543896717433024957276344587510493959523928039586339138706532195604610913143931369836884597572856315577026855217107360269369009043640897589855901974911811522685650990655020139193037079751177699317346695464548683459008342285041352467445530551971560163655970994577746394286579123881318184816680588564544675621268898067397781743519268241710256974586041634215237194535237573889207132980002998797969921217553139652377604041229863138201742108945665558337339105262999419702005293647238458082 200 29848 42312 63950 69348 31168 39280 31096 39408 29848 36080 6872
    (by decide +kernel) (by decide)
theorem wk18ll : SixW25P.Covered 29848 42312 58552 69348 31168 39280 31096 39408 29848 36080 :=
  SixW25P.covered_split1 63950 wk18lll wk18llr
theorem wk18lr : SixW25P.Covered 29848 42312 58552 69348 31168 39280 31096 39408 36080 42312 :=
  SixW25P.covered_of_walk lbS hbas 6737649229941458764231504686 200 29848 42312 58552 69348 31168 39280 31096 39408 36080 42312 102
    (by decide +kernel) (by decide)
theorem wk18l : SixW25P.Covered 29848 42312 58552 69348 31168 39280 31096 39408 29848 42312 :=
  SixW25P.covered_split4 36080 wk18ll wk18lr
theorem wk18r : SixW25P.Covered 29848 42312 69348 80144 31168 39280 31096 39408 29848 42312 :=
  SixW25P.covered_of_walk lbS hbas 34340023147990820450 200 29848 42312 69348 80144 31168 39280 31096 39408 29848 42312 72
    (by decide +kernel) (by decide)
theorem wk18 : SixW25P.Covered 29848 42312 58552 80144 31168 39280 31096 39408 29848 42312 :=
  SixW25P.covered_split1 69348 wk18l wk18r
theorem wk19llllll : SixW25P.Covered 29848 42312 58552 63950 31168 39280 31096 39408 54736 73706 :=
  SixW25P.covered_of_walk lbS hbas 26772014747593860305950779834075850252384704641435942068199494963262528245760349614653988237313825356205375978575968615106458699112027196484269252778036751722990648574143524077779260180488389926298766878686929671666742178089100447187283376690959538559495759719485986003364453945783955057006158642003283350500981603931028327596362686478704064187584119601973225261597326226003314422133010456340040089579983821605521421003805879419185690110551721985131249434509401072195258577170961360139180905993711605083576963241425167833898315302793839901421561456747844102583805385520897570233358796582014847847623172084506113017517002242728315794771662034161857958836351356898352462849510128243028706223840908827829257733317768208809232839281284560870714659561882965249355267681779266112567647873520895743098010059354446594036706038390768806548574271672516101342590366465870800626418259043127150918168477315022593112826950 200 29848 42312 58552 63950 31168 39280 31096 39408 54736 73706 3022
    (by decide +kernel) (by decide)
theorem wk19lllllrll : SixW25P.Covered 29848 36080 63950 69348 31168 39280 31096 39408 54736 64221 :=
  SixW25P.covered_of_walk lbS hbas 28151723428764367620162491039844010582176578739780775203593024364364782964964406205418445213513794452095480992434882091989754325936853393082128904294841696652663760087756988340648419734215847790055226246617385221517088723108202337120306109467285825781224766399287953157667092022614922124860454227229425863563528462161853696332455777304523603149067544892217024252311962669593525985086248631734103059572810227762290284130031288130876169285471139475153676275802770406462318787393142779797710111842573328496744766851523106668818317827638957215785648762823545460136946881408008448606257412160528082279417762602337167381637163699869578456278638723251629630108276480277651890238125153951464880646159963227453697102587839616095437371736246555837254163437085585346054827259210959244084470814133824611702598946658437170658425185663854760002801475484813134215751311706552187705719078225389270989317321535683085483287180146282276358495650429482391040910232023627527903562339276022781085247299890939678947869794579656017998279169472939452568195706895216657440461390440714173533793797669354278117513351483355795596153076961867872396547376804420862522713387510343791803070498980764304902013567156212970192311451654512871791574607614498627055978764500824294615716903046531369590166556322629934559444885177326585249308270491794472966388728494087214820986492154578722019094120537485866275271571259780212348993079756033832623921924529539013631299058998013132034867916383946168089288710774972354626309082188660530807990844688094168164761763510331817509890495607487168900730336044540063933306311393700959219269604114030001381226270638598865835237876870982632254264868077016677479783858307824384556271015654286867599425870914539077478693051856658172120893397213721588008307583725295629825841748713874705898577477005941738668572202294548150167428289678521911625719068872308025603040974636129013457342259536198881639164841624258848011973172124472666114993280667071805257454864811207271111359819838594378029043490170578721360267022315519425926561902648786 200 29848 36080 63950 69348 31168 39280 31096 39408 54736 64221 6752
    (by decide +kernel) (by decide)
theorem wk19lllllrlrllll : SixW25P.Covered 29848 36080 63950 69348 31168 35224 31096 33174 64221 68963 :=
  SixW25P.covered_of_walk lbS hbas 822913824166284828264905586706710048821698484285671875768390732883717343225742448951969635446206151540856220555317545418 200 29848 36080 63950 69348 31168 35224 31096 33174 64221 68963 407
    (by decide +kernel) (by decide)
theorem wk19lllllrlrlllrl : SixW25P.Covered 29848 36080 63950 69348 31168 33196 33174 35252 64221 68963 :=
  SixW25P.covered_of_walk lbS hbas 6332720107059453380099017960880250510710365972611224781848484745258125262141013392566845030662351170 200 29848 36080 63950 69348 31168 33196 33174 35252 64221 68963 342
    (by decide +kernel) (by decide)
theorem wk19lllllrlrlllrrl : SixW25P.Covered 29848 32964 63950 69348 33196 35224 33174 35252 64221 68963 :=
  SixW25P.covered_of_walk lbS hbas 34578412668901457576234806136830567919166242658192817462729800085846906761756479564878404797905719008823987236174519727280084829012738827218834760458753580641387270567066423068185805013607073504083381767034453269913920307333648717069434829326683584223759255442971662236855453016168514 200 29848 32964 63950 69348 33196 35224 33174 35252 64221 68963 947
    (by decide +kernel) (by decide)
theorem wk19lllllrlrlllrrrlllll : SixW25P.Covered 32964 36080 63950 65299 33196 34210 33174 34213 64221 66592 :=
  SixW25P.covered_of_walk lbS hbas 6737032281599655022853049395587505663668193649176412952277036565561115462787744254754754434698969021720287660613715119396849670565716263302790139888094891060244407708083802524307711224872214522962670402344298733220254317086120276431626887528990219024335034736120092746109576104104866793851413901338332446823483656646987252454481264352318945008089509576582428323586004475797370681335136320592823374321723153520062091694869555524224826129395968542655395437134760189749419719225208199771652476306019472615466139442543381516074385682635574251822451013951500009306885589785254607796422791083176315194129300859616054923386211012460677837993182357409982905535563309796596936225835749778662615187352348301910130543016704756523262152810135855720321918480586097671076045632734768875806464068379907744838107506437407037890696817175430558350212920230048340715028885938211067093090611613554634876195469219057024371713491053438484457686927863957013291069022618262933381743838761975383790523200888277959241428353277481315621513422363597868783209530518662219206224910874981930534720529284703441756799239070324662476565116002590197904834147092412475442927780973381129424934387877854814004694765235278523699862194876823174152754482670489713016428975892580718937656146528086830351505363937866545574559946483095443357596661774868980690253716755741159024817459393193619727161142693306719350486857265132502765800505596023854682460961669942793374777200748083609341922297342557220330731732477429126726029944447321548646052875481015473137500700472242588445969379396898042224479371223144730352417558870399494829598626680830246995906857129616117429983916304944941992691550510363455894954163874466450308353421631360471755770004848103217623743233796441562618138223695354711453259526904297504997662246865953553826095767774384532834974437241698578076398957980099306 200 32964 36080 63950 65299 33196 34210 33174 34213 64221 66592 6097
    (by decide +kernel) (by decide)
theorem wk19lllllrlrlllrrrllllr : SixW25P.Covered 32964 36080 63950 65299 34210 35224 33174 34213 64221 66592 :=
  SixW25P.covered_of_walk lbS hbas 2865150432996805491414482273162365054690247974502927046090342969519949384190115388761014291838812414015163949237548266737175671661030821505573379932661956619528932295823288329810913342917688787483586102774897498110432475320251690193328300832000807945528872785108836660005544361050469607851157774624355344762885007115662645088212416598746704857219182796412103499058326149983376519890278040379120080653786239002007170951190879817857545141261626613668309504815474403370283274508283775665051840641943464108833870889594241986369138981029238652024957879787170245072508826690704375011293766946 200 32964 36080 63950 65299 34210 35224 33174 34213 64221 66592 1952
    (by decide +kernel) (by decide)
theorem wk19lllllrlrlllrrrllll : SixW25P.Covered 32964 36080 63950 65299 33196 35224 33174 34213 64221 66592 :=
  SixW25P.covered_split2 34210 wk19lllllrlrlllrrrlllll wk19lllllrlrlllrrrllllr
theorem wk19lllllrlrlllrrrlllr : SixW25P.Covered 32964 36080 63950 65299 33196 35224 34213 35252 64221 66592 :=
  SixW25P.covered_of_walk lbS hbas 8221065360400872165267439485755034969667288993326213432737196129360988846700628318308224019549016622689450974559792616570298960326786977008159531580261678871487595920524469281689609190235093354377988865320339577702284042966178394554857229442153735413720244122404580054288664768099748401656265935467852642181583885304103129609280494399652986127808225433107271022988452557159816288049450033199482185674477908288663008885457887914 200 32964 36080 63950 65299 33196 35224 34213 35252 64221 66592 1422
    (by decide +kernel) (by decide)
theorem wk19lllllrlrlllrrrlll : SixW25P.Covered 32964 36080 63950 65299 33196 35224 33174 35252 64221 66592 :=
  SixW25P.covered_split3 34213 wk19lllllrlrlllrrrllll wk19lllllrlrlllrrrlllr
theorem wk19lllllrlrlllrrrllr : SixW25P.Covered 32964 36080 65299 66649 33196 35224 33174 35252 64221 66592 :=
  SixW25P.covered_of_walk lbS hbas 15166815121605486857819777579458460010741273334599019308288730634031204708590199818766349656551817542676549392379889036585745817165352714560843161120870261326948520894567188503200341168204671689568691367718316144640514312145235196253245314863056484522049355691971766041781799265154026524826990397918206436261784192177252342461427459819189395510870663126460116486417205208333554853567582946886627416529259651485130569172327224954699651989326112374763155246867152744454456808058444251682178240515658914672992822215402999970006327818962806424485564702467869684777141987612562059418560953412427049992003432584840018453335765283035414708920728803677905308733520421130196344534485435114711826601495620406613337342647250040133542021074256703161388873110415722244779205574689666255869605820959989961835515632189499596692670046296125380767290322590681693659934161700605998125953564933251458887406930372165854809783966907573920242172202940162595234866467801186150427861791611272894461874597226703939448608153662580622294204749110305673707224119674367755921322014730610162935591482189114568184798714391671066713252582609232326096299924385729371704726466230369565979169590831048123523355943190774475696096123226027176254303493645695463896329706021944447540705272554 200 32964 36080 65299 66649 33196 35224 33174 35252 64221 66592 4167
    (by decide +kernel) (by decide)
theorem wk19lllllrlrlllrrrll : SixW25P.Covered 32964 36080 63950 66649 33196 35224 33174 35252 64221 66592 :=
  SixW25P.covered_split1 65299 wk19lllllrlrlllrrrlll wk19lllllrlrlllrrrllr
theorem wk19lllllrlrlllrrrlr : SixW25P.Covered 32964 36080 63950 66649 33196 35224 33174 35252 66592 68963 :=
  SixW25P.covered_of_walk lbS hbas 66151510323544726291107164921261878380819401230867303197082836888745532717424933531680197996485891167443229324294677192824070837237123134353600028199664421226043508349437616982486402247801565391318882591018175479351020809123335842786555002053061308015819158268078550957232692413141499459428275715496147396911277663948458067953024648253580084619879575507005423270752828565613087355759620709387447435174783088830577110602955128934047704262468410188527014572522685426424053324350620459872459004942008747332454886570737538670277669827079659714966923886 200 32964 36080 63950 66649 33196 35224 33174 35252 66592 68963 1827
    (by decide +kernel) (by decide)
theorem wk19lllllrlrlllrrrl : SixW25P.Covered 32964 36080 63950 66649 33196 35224 33174 35252 64221 68963 :=
  SixW25P.covered_split4 66592 wk19lllllrlrlllrrrll wk19lllllrlrlllrrrlr
theorem wk19lllllrlrlllrrrr : SixW25P.Covered 32964 36080 66649 69348 33196 35224 33174 35252 64221 68963 :=
  SixW25P.covered_of_walk lbS hbas 11603280630381498357786323461580292922151837973847555752908365911387174449648209238342002189094 200 32964 36080 66649 69348 33196 35224 33174 35252 64221 68963 317
    (by decide +kernel) (by decide)
theorem wk19lllllrlrlllrrr : SixW25P.Covered 32964 36080 63950 69348 33196 35224 33174 35252 64221 68963 :=
  SixW25P.covered_split1 66649 wk19lllllrlrlllrrrl wk19lllllrlrlllrrrr
theorem wk19lllllrlrlllrr : SixW25P.Covered 29848 36080 63950 69348 33196 35224 33174 35252 64221 68963 :=
  SixW25P.covered_split0 32964 wk19lllllrlrlllrrl wk19lllllrlrlllrrr
theorem wk19lllllrlrlllr : SixW25P.Covered 29848 36080 63950 69348 31168 35224 33174 35252 64221 68963 :=
  SixW25P.covered_split2 33196 wk19lllllrlrlllrl wk19lllllrlrlllrr
theorem wk19lllllrlrlll : SixW25P.Covered 29848 36080 63950 69348 31168 35224 31096 35252 64221 68963 :=
  SixW25P.covered_split3 33174 wk19lllllrlrllll wk19lllllrlrlllr
theorem wk19lllllrlrllr : SixW25P.Covered 29848 36080 63950 69348 31168 35224 31096 35252 68963 73706 :=
  SixW25P.covered_of_walk lbS hbas 38914802 200 29848 36080 63950 69348 31168 35224 31096 35252 68963 73706 32
    (by decide +kernel) (by decide)
theorem wk19lllllrlrll : SixW25P.Covered 29848 36080 63950 69348 31168 35224 31096 35252 64221 73706 :=
  SixW25P.covered_split4 68963 wk19lllllrlrlll wk19lllllrlrllr
theorem wk19lllllrlrlr : SixW25P.Covered 29848 36080 63950 69348 35224 39280 31096 35252 64221 73706 :=
  SixW25P.covered_of_walk lbS hbas 42936819585781407507386460365154551946900490458613099031937807720615823566734469818189157718216471623866412292760029842744866467319105270976440541353567184499434 200 29848 36080 63950 69348 35224 39280 31096 35252 64221 73706 547
    (by decide +kernel) (by decide)
theorem wk19lllllrlrl : SixW25P.Covered 29848 36080 63950 69348 31168 39280 31096 35252 64221 73706 :=
  SixW25P.covered_split2 35224 wk19lllllrlrll wk19lllllrlrlr
theorem wk19lllllrlrr : SixW25P.Covered 29848 36080 63950 69348 31168 39280 35252 39408 64221 73706 :=
  SixW25P.covered_of_walk lbS hbas 1079712606773630130359632420475201918438188152267827121909475130305556149376324991049069195654426774291613936774746488323615534 200 29848 36080 63950 69348 31168 39280 35252 39408 64221 73706 427
    (by decide +kernel) (by decide)
theorem wk19lllllrlr : SixW25P.Covered 29848 36080 63950 69348 31168 39280 31096 39408 64221 73706 :=
  SixW25P.covered_split3 35252 wk19lllllrlrl wk19lllllrlrr
theorem wk19lllllrl : SixW25P.Covered 29848 36080 63950 69348 31168 39280 31096 39408 54736 73706 :=
  SixW25P.covered_split4 64221 wk19lllllrll wk19lllllrlr
theorem wk19lllllrr : SixW25P.Covered 36080 42312 63950 69348 31168 39280 31096 39408 54736 73706 :=
  SixW25P.covered_of_walk lbS hbas 36713445805218329136190493119431624474133139536898798548034792958620194 200 36080 42312 63950 69348 31168 39280 31096 39408 54736 73706 242
    (by decide +kernel) (by decide)
theorem wk19lllllr : SixW25P.Covered 29848 42312 63950 69348 31168 39280 31096 39408 54736 73706 :=
  SixW25P.covered_split0 36080 wk19lllllrl wk19lllllrr
theorem wk19lllll : SixW25P.Covered 29848 42312 58552 69348 31168 39280 31096 39408 54736 73706 :=
  SixW25P.covered_split1 63950 wk19llllll wk19lllllr
theorem wk19llllr : SixW25P.Covered 29848 42312 69348 80144 31168 39280 31096 39408 54736 73706 :=
  SixW25P.covered_of_walk lbS hbas 7982496611477030 200 29848 42312 69348 80144 31168 39280 31096 39408 54736 73706 62
    (by decide +kernel) (by decide)
theorem wk19llll : SixW25P.Covered 29848 42312 58552 80144 31168 39280 31096 39408 54736 73706 :=
  SixW25P.covered_split1 69348 wk19lllll wk19llllr
theorem wk19lllr : SixW25P.Covered 29848 42312 58552 80144 31168 39280 31096 39408 73706 92676 :=
  SixW25P.covered_of_walk lbS hbas 750127260966 200 29848 42312 58552 80144 31168 39280 31096 39408 73706 92676 47
    (by decide +kernel) (by decide)
theorem wk19lll : SixW25P.Covered 29848 42312 58552 80144 31168 39280 31096 39408 54736 92676 :=
  SixW25P.covered_split4 73706 wk19llll wk19lllr
theorem wk19llr : SixW25P.Covered 29848 42312 58552 80144 31168 39280 31096 39408 92676 130616 :=
  SixW25P.covered_of_walk lbS hbas 157755153490845034344916889591153378992478074250917652336596633066374254643576072651632114192733725999302145547564927728256527256058367755460355690056440932120170637827045764944547602506080606429107745681741378221247570106687982875448231676574144815726845815393925772203396791985771239209288729798870154338707353373675222131697701472481155299085497892814695222632094052252974483544841205075628566443183778228351420486567901946502300947899510738820327292260623682438512665105798483139491043218865819976209170314211386368113772512341539412140296593852083947311664889596359517377489335808521030384645055229084320366142787224672182970789218289434950793882030071660818257114073284562879881535994121279501034080685183786834148285982278443737136978268906240091352722120105171521036436517150858183275318497029082745757492580091961225750574358792414981257678430093258689882355835126348858198707492059618841270124392925202025808703934792387283439975714113451740495871073819442043059239513174888168842049703247186033128571899905135142308874857276168401383248403225247796582212220187751704057257764521879740321888177976328164319296667419553657776888317939065555761424558077079398329273260555561320671893652368236284928510409546444446106161883686146449280101734764403123341998369210974435178443080788567596779786477795727194040490609407136497286022818732287743884011282797793983219994062868932792480118546693980237865262412157124018306430302829473116712248756310559568076470873523477433192085368609224853504372876810462017755948516133285060167875437814323972047854602402245586775886395958523985020977404239698529496798988916927245312717249110701430962669676485579312496978765503981980100176551795995271835717587738361146141219351334575017261181760038080633631138497763902871824805905461615819021083920056814869785853202880680488634119260135246931595848681537138684651536223802481675162111499766602923303816185081083671785845857155171035689819209773184215787396445051020412773633307499994779037711623646270091443443509037883056517285865603502671709798 200 29848 42312 58552 80144 31168 39280 31096 39408 92676 130616 6772
    (by decide +kernel) (by decide)
theorem wk19ll : SixW25P.Covered 29848 42312 58552 80144 31168 39280 31096 39408 54736 130616 :=
  SixW25P.covered_split4 92676 wk19lll wk19llr
theorem wk19lr : SixW25P.Covered 29848 42312 58552 80144 31168 39280 31096 39408 130616 206496 :=
  SixW25P.covered_of_walk lbS hbas 3143273586936056090513829149599725032589094 200 29848 42312 58552 80144 31168 39280 31096 39408 130616 206496 147
    (by decide +kernel) (by decide)
theorem wk19l : SixW25P.Covered 29848 42312 58552 80144 31168 39280 31096 39408 54736 206496 :=
  SixW25P.covered_split4 130616 wk19ll wk19lr
theorem wk19r : SixW25P.Covered 29848 42312 58552 80144 31168 39280 31096 39408 206496 358256 :=
  SixW25P.covered_of_walk lbS hbas 0 200 29848 42312 58552 80144 31168 39280 31096 39408 206496 358256 2
    (by decide +kernel) (by decide)
theorem wk19 : SixW25P.Covered 29848 42312 58552 80144 31168 39280 31096 39408 54736 358256 :=
  SixW25P.covered_split4 206496 wk19l wk19r
theorem wk20lllll : SixW25P.Covered 29848 36080 58552 63950 31168 39280 58552 69348 29848 36080 :=
  SixW25P.covered_of_walk lbS hbas 30854958911537880713689675982636286574364556000336208386760489588445081336779248798058892407299540240371888811077531382039723610503826827168144165074307009293304807345506458711192043362947877761624004466431980386882140808419597206782479383168375678172511310491919075314427422372083726010058970595655376876099992986914326563376732015640663367464945233789209181250219443149105951448518 200 29848 36080 58552 63950 31168 39280 58552 69348 29848 36080 1277
    (by decide +kernel) (by decide)
theorem wk20llllrl : SixW25P.Covered 29848 36080 63950 69348 31168 39280 58552 63950 29848 36080 :=
  SixW25P.covered_of_walk lbS hbas 3175093500447107541036567693680035092400945562331629676406130327306606349008771747108649966811763559859861609769147985380118609807091806865584198684831038976633561446736946404677537899462454960344665139132225931228231963120440200908983762089866065590035266303239274666476728081477315635831614079110338014363204490043012316617667178395712375988128672229529018753666960685319338354624102397146509210200913175546430324502919723598 200 29848 36080 63950 69348 31168 39280 58552 63950 29848 36080 1422
    (by decide +kernel) (by decide)
theorem wk20llllrrll : SixW25P.Covered 29848 36080 63950 69348 31168 33196 63950 69348 29848 36080 :=
  SixW25P.covered_of_walk lbS hbas 12285027435990488304030566343963819299827952194 200 29848 36080 63950 69348 31168 33196 63950 69348 29848 36080 162
    (by decide +kernel) (by decide)
theorem wk20llllrrlrl : SixW25P.Covered 29848 32964 63950 69348 33196 35224 63950 69348 29848 36080 :=
  SixW25P.covered_of_walk lbS hbas 57349476237569672061888966170771237911857696970308722132921505567158041938866807256769705379956446832559166333266427513426882973546790710000740809401810147689688229451177088982486783329143191889285608459520066 200 29848 32964 63950 69348 33196 35224 63950 69348 29848 36080 702
    (by decide +kernel) (by decide)
theorem wk20llllrrlrrl : SixW25P.Covered 32964 36080 63950 69348 33196 35224 63950 69348 29848 32964 :=
  SixW25P.covered_of_walk lbS hbas 4010505684050 200 32964 36080 63950 69348 33196 35224 63950 69348 29848 32964 52
    (by decide +kernel) (by decide)
theorem wk20llllrrlrrrl : SixW25P.Covered 32964 36080 63950 66649 33196 35224 63950 69348 32964 36080 :=
  SixW25P.covered_of_walk lbS hbas 14480595437146718263694682787667632949882414674144072626025464967663445578557648438739334607182943981723416447290684828139122292658759008552448472302689386531967555173602409747146813040153579648453549567956894004105759931639583189209211230486340975523906018460222113485604608969356375651396868830794640850759649837200427359158598851413325498232463977069885345568379482509028497986729883425368689889363423349302082013131644686912367085978987653971495918184361753477756468347602620342153047457246394465156239834531770764053313274602585373875141493846381938922360905347237898665349367043742356305267382456348203986706662939650335603399822464662979034634099922351379098112223160699980648374497571921266839259606810784706674217580516589356912139129442446229480990394119066146884520392265270738043845344106701250373511558321503017966668092773593232700287131417964994956301218221482710414114127198077925648858961138325117822058481355411726888120425839341787041381639422296452270128496803078681141992988641248153709788642750017590525890362212378059562108448747605659789852621698467660726222039543838958367490503245487974702618386700698463362341928316034382651780771449071584325332556995391181717840695092793351596620741837818840467491610399329965731020120885434663094695961574533021021839161241056837719154429540433424677715357942945489087388493730839021007050296525862049670369738175673175860644566637487370511827741829355763950688223648366594871748838317441044880929020917478033683694836532710245497414299134133423385878202336219099130586779096536567605215566660613038124754832407369968717136857319908132486527198611530669220416696996213006787797714818658128049126635481720993462950973115092335001265480041082001995001759381308238826337087770075184622863083251033501863262306862897056630076341119320893545192173220900811808810112037084666435542679991550557083481616791051386712026125782520185836217608100248130516671589230560952262539339006441197704691702096076319947879683284111489692813102537858893258414346234688109476821595631023696988208674521595757997476224525831298282643276496628808287043723682097944925312658353774 200 32964 36080 63950 66649 33196 35224 63950 69348 32964 36080 7037
    (by decide +kernel) (by decide)
theorem wk20llllrrlrrrr : SixW25P.Covered 32964 36080 66649 69348 33196 35224 63950 69348 32964 36080 :=
  SixW25P.covered_of_walk lbS hbas 97077409599083873442203275043842832776105667758009917479038041959988656473663066075944059557391378013130312811004047668366156818787663855926672400801935104663956293765694908108960395712670164532636949986183111644536500037907800043334315457278295689256673054237600227661647289442926 200 32964 36080 66649 69348 33196 35224 63950 69348 32964 36080 942
    (by decide +kernel) (by decide)
theorem wk20llllrrlrrr : SixW25P.Covered 32964 36080 63950 69348 33196 35224 63950 69348 32964 36080 :=
  SixW25P.covered_split1 66649 wk20llllrrlrrrl wk20llllrrlrrrr
theorem wk20llllrrlrr : SixW25P.Covered 32964 36080 63950 69348 33196 35224 63950 69348 29848 36080 :=
  SixW25P.covered_split4 32964 wk20llllrrlrrl wk20llllrrlrrr
theorem wk20llllrrlr : SixW25P.Covered 29848 36080 63950 69348 33196 35224 63950 69348 29848 36080 :=
  SixW25P.covered_split0 32964 wk20llllrrlrl wk20llllrrlrr
theorem wk20llllrrl : SixW25P.Covered 29848 36080 63950 69348 31168 35224 63950 69348 29848 36080 :=
  SixW25P.covered_split2 33196 wk20llllrrll wk20llllrrlr
theorem wk20llllrrr : SixW25P.Covered 29848 36080 63950 69348 35224 39280 63950 69348 29848 36080 :=
  SixW25P.covered_of_walk lbS hbas 2551187518061395205189495676752395776612695590827242659174713333779998669079002971713973709679979953766788212036691749432726149917210839766323191220770620347726730460801443979054428595446259453510299882448131925687049508152385633981710004035539290673418079684179917588220535162556970 200 29848 36080 63950 69348 35224 39280 63950 69348 29848 36080 952
    (by decide +kernel) (by decide)
theorem wk20llllrr : SixW25P.Covered 29848 36080 63950 69348 31168 39280 63950 69348 29848 36080 :=
  SixW25P.covered_split2 35224 wk20llllrrl wk20llllrrr
theorem wk20llllr : SixW25P.Covered 29848 36080 63950 69348 31168 39280 58552 69348 29848 36080 :=
  SixW25P.covered_split3 63950 wk20llllrl wk20llllrr
theorem wk20llll : SixW25P.Covered 29848 36080 58552 69348 31168 39280 58552 69348 29848 36080 :=
  SixW25P.covered_split1 63950 wk20lllll wk20llllr
theorem wk20lllr : SixW25P.Covered 29848 36080 58552 69348 31168 39280 58552 69348 36080 42312 :=
  SixW25P.covered_of_walk lbS hbas 1448254049516397017526640973629754792377608390379709153291028210 200 29848 36080 58552 69348 31168 39280 58552 69348 36080 42312 217
    (by decide +kernel) (by decide)
theorem wk20lll : SixW25P.Covered 29848 36080 58552 69348 31168 39280 58552 69348 29848 42312 :=
  SixW25P.covered_split4 36080 wk20llll wk20lllr
theorem wk20llr : SixW25P.Covered 36080 42312 58552 69348 31168 39280 58552 69348 29848 42312 :=
  SixW25P.covered_of_walk lbS hbas 590625031936254224614829160255011168944524108098336616508732507037257314 200 36080 42312 58552 69348 31168 39280 58552 69348 29848 42312 247
    (by decide +kernel) (by decide)
theorem wk20ll : SixW25P.Covered 29848 42312 58552 69348 31168 39280 58552 69348 29848 42312 :=
  SixW25P.covered_split0 36080 wk20lll wk20llr
theorem wk20lr : SixW25P.Covered 29848 42312 58552 69348 31168 39280 69348 80144 29848 42312 :=
  SixW25P.covered_of_walk lbS hbas 7532334 200 29848 42312 58552 69348 31168 39280 69348 80144 29848 42312 32
    (by decide +kernel) (by decide)
theorem wk20l : SixW25P.Covered 29848 42312 58552 69348 31168 39280 58552 80144 29848 42312 :=
  SixW25P.covered_split3 69348 wk20ll wk20lr
theorem wk20r : SixW25P.Covered 29848 42312 69348 80144 31168 39280 58552 80144 29848 42312 :=
  SixW25P.covered_of_walk lbS hbas 14836334 200 29848 42312 69348 80144 31168 39280 58552 80144 29848 42312 32
    (by decide +kernel) (by decide)
theorem wk20 : SixW25P.Covered 29848 42312 58552 80144 31168 39280 58552 80144 29848 42312 :=
  SixW25P.covered_split1 69348 wk20l wk20r
theorem wk21 : SixW25P.Covered 29848 42312 58552 80144 31168 39280 58552 80144 54736 358256 :=
  SixW25P.covered_of_walk lbS hbas 50671184332515180041763268120073574127489332364492291159030915407337779654058090840981787048805322320758639334210618489940595238490839304291662075954396846067105716641555012567477524252218883472265990001048120130795770067442145459464600183251836799977599198475541982828665429122030495001958027749816313135975406185733880484581923034775488264607513087407826157428356745870779193766149093511383251531431169451487329497105743925107555227527702487565969075310616989425487970238194673981348270805603479051718044120589818707424972007161758184031353472400338348264911726783009253255353013974958674252647177938729655683306701148216344437986617231298312519723331912989098719577382392488234287046420537620618690614916888280330890835248521969300093354444737548428807841480233820093050500248366576449944777212578775515158563127336007226329558945847685635342437868264806000988640987169221818154706906413807616982867145522 200 29848 42312 58552 80144 31168 39280 58552 80144 54736 358256 3027
    (by decide +kernel) (by decide)
theorem wk22 : SixW25P.Covered 29848 42312 58552 80144 31168 39280 82632 250598 29848 42312 :=
  SixW25P.covered_of_walk lbS hbas 7688787921873830160556765550512456129869631027416046371962922662495769860600927785530356919368310352038096298510680810359902916428839096955894220027562983989793869816242135144285072618944683656356137457152388100960540075505075095410400095982 200 29848 42312 58552 80144 31168 39280 82632 250598 29848 42312 812
    (by decide +kernel) (by decide)
theorem wk23 : SixW25P.Covered 29848 42312 58552 80144 31168 39280 82632 250598 54736 358256 :=
  SixW25P.covered_of_walk lbS hbas 5783771243818798 200 29848 42312 58552 80144 31168 39280 82632 250598 54736 358256 67
    (by decide +kernel) (by decide)
theorem wk24llll : SixW25P.Covered 29848 42312 58552 63950 58728 68848 31096 39408 29848 36080 :=
  SixW25P.covered_of_walk lbS hbas 9411802257668827509185316314089643230574204494222974259865399217650936783366566128593453918393261907759282446478949093335843663094848664092558880729100319562122646270916065754542431923360866723242300334988340913643346529852228710028969972380009122655635850417606 200 29848 42312 58552 63950 58728 68848 31096 39408 29848 36080 877
    (by decide +kernel) (by decide)
theorem wk24lllrlll : SixW25P.Covered 29848 36080 63950 69348 58728 63788 31096 35252 29848 36080 :=
  SixW25P.covered_of_walk lbS hbas 1787581477021276639949210529609359459650238089881534080555405963399181431178684719981129509519965852186914583839097107448840317044166155297692339155201484856281437327778146494922 200 29848 36080 63950 69348 58728 63788 31096 35252 29848 36080 592
    (by decide +kernel) (by decide)
theorem wk24lllrllrl : SixW25P.Covered 29848 36080 63950 69348 63788 68848 31096 33174 29848 36080 :=
  SixW25P.covered_of_walk lbS hbas 2521832170217472475352144509545467450897585457577912839678533733633693094790465841465934 200 29848 36080 63950 69348 63788 68848 31096 33174 29848 36080 297
    (by decide +kernel) (by decide)
theorem wk24lllrllrrl : SixW25P.Covered 29848 36080 63950 69348 63788 68848 33174 35252 29848 32964 :=
  SixW25P.covered_of_walk lbS hbas 18009884226719158098873510038098 200 29848 36080 63950 69348 63788 68848 33174 35252 29848 32964 117
    (by decide +kernel) (by decide)
theorem wk24lllrllrrrl : SixW25P.Covered 29848 32964 63950 69348 63788 68848 33174 35252 32964 36080 :=
  SixW25P.covered_of_walk lbS hbas 465932382159269338037866753881278759407349966789834622411983309690496445837901379567777979364676216554627433948761592452370550457668815364354265568873255218143093635897840463233728636164922353298981848169782068451000088931483184742617603500554617134576448612418 200 29848 32964 63950 69348 63788 68848 33174 35252 32964 36080 872
    (by decide +kernel) (by decide)
theorem wk24lllrllrrrr : SixW25P.Covered 32964 36080 63950 69348 63788 68848 33174 35252 32964 36080 :=
  SixW25P.covered_of_walk lbS hbas 439807864236084329075452021067320424688804059004938949011769726537038737670224348776176861445061808858014594716522112769042050612251405307741148046129474514715411047125665701966571895922840385083789635208300914854243311509749764969325236705793795414967953872696702756147674075390544062666027984470244536619831505178812968238938406942651520029548296280794308705688565985174736027516288760881457501669432729642806228607552518670699507701626550492421836138934527359746334591392262938351427332413129157846175966901500980402492728506116469838483362042326406766034710543863434094180938081633811740416854040058944230538580406059107045435851140574713482494776279441681482205599542323975343694798989801849395405661332868590416351744198553926646004974871297978861058906539435013452749790689041310601660661447867449681232521554535391478692515269614870246780926194627480393820933256078690343411839081421146060212703513090397377700482507371378300756951569272843176341662484080055202453953484044149556797233834511024326768126590502966999416099164614101168509938098832151965675449810863550961647594571869835079858805071104420878268939639171149107101892846901180462416221107820461139743667307291747377001857608496912349249152619732695824770779861932751401514787401072648504017064537291929841558320620493134702628668858590062117777840948430319940415617518135702891614012604015770152370791810456010714993178575387132128347745235228490964909324481810272243454415922056500840285371825861504114020795157433832573080015672692888482741138400926813871301380592769543519675139996366389586337163346567507306255442047787682987907595672951770919870891619856652081475681958172253935986894184532249279899272500129093020141691578254613899148248023243994706435125718777675608421198668843457882446694566248305865956452064016241902847366785771707294997264895246650403248982542089867301743494560451949286602803315020829188922864927834361965471032850960260268270141376648861007449940657029218724320758201003708355481683895682719022388577159503344334556075661278952908300937788334624418032352161391698933904038 200 32964 36080 63950 69348 63788 68848 33174 35252 32964 36080 6892
    (by decide +kernel) (by decide)
theorem wk24lllrllrrr : SixW25P.Covered 29848 36080 63950 69348 63788 68848 33174 35252 32964 36080 :=
  SixW25P.covered_split0 32964 wk24lllrllrrrl wk24lllrllrrrr
theorem wk24lllrllrr : SixW25P.Covered 29848 36080 63950 69348 63788 68848 33174 35252 29848 36080 :=
  SixW25P.covered_split4 32964 wk24lllrllrrl wk24lllrllrrr
theorem wk24lllrllr : SixW25P.Covered 29848 36080 63950 69348 63788 68848 31096 35252 29848 36080 :=
  SixW25P.covered_split3 33174 wk24lllrllrl wk24lllrllrr
theorem wk24lllrll : SixW25P.Covered 29848 36080 63950 69348 58728 68848 31096 35252 29848 36080 :=
  SixW25P.covered_split2 63788 wk24lllrlll wk24lllrllr
theorem wk24lllrlr : SixW25P.Covered 29848 36080 63950 69348 58728 68848 35252 39408 29848 36080 :=
  SixW25P.covered_of_walk lbS hbas 8357090863536350100933108251171272544095634945558607900462 200 29848 36080 63950 69348 58728 68848 35252 39408 29848 36080 202
    (by decide +kernel) (by decide)
theorem wk24lllrl : SixW25P.Covered 29848 36080 63950 69348 58728 68848 31096 39408 29848 36080 :=
  SixW25P.covered_split3 35252 wk24lllrll wk24lllrlr
theorem wk24lllrr : SixW25P.Covered 36080 42312 63950 69348 58728 68848 31096 39408 29848 36080 :=
  SixW25P.covered_of_walk lbS hbas 1101284047031429373239842 200 36080 42312 63950 69348 58728 68848 31096 39408 29848 36080 97
    (by decide +kernel) (by decide)
theorem wk24lllr : SixW25P.Covered 29848 42312 63950 69348 58728 68848 31096 39408 29848 36080 :=
  SixW25P.covered_split0 36080 wk24lllrl wk24lllrr
theorem wk24lll : SixW25P.Covered 29848 42312 58552 69348 58728 68848 31096 39408 29848 36080 :=
  SixW25P.covered_split1 63950 wk24llll wk24lllr
theorem wk24llr : SixW25P.Covered 29848 42312 58552 69348 58728 68848 31096 39408 36080 42312 :=
  SixW25P.covered_of_walk lbS hbas 999191342 200 29848 42312 58552 69348 58728 68848 31096 39408 36080 42312 37
    (by decide +kernel) (by decide)
theorem wk24ll : SixW25P.Covered 29848 42312 58552 69348 58728 68848 31096 39408 29848 42312 :=
  SixW25P.covered_split4 36080 wk24lll wk24llr
theorem wk24lr : SixW25P.Covered 29848 42312 58552 69348 68848 78968 31096 39408 29848 42312 :=
  SixW25P.covered_of_walk lbS hbas 35789739826774387289733969842959018 200 29848 42312 58552 69348 68848 78968 31096 39408 29848 42312 122
    (by decide +kernel) (by decide)
theorem wk24l : SixW25P.Covered 29848 42312 58552 69348 58728 78968 31096 39408 29848 42312 :=
  SixW25P.covered_split2 68848 wk24ll wk24lr
theorem wk24r : SixW25P.Covered 29848 42312 69348 80144 58728 78968 31096 39408 29848 42312 :=
  SixW25P.covered_of_walk lbS hbas 82368010641647202 200 29848 42312 69348 80144 58728 78968 31096 39408 29848 42312 67
    (by decide +kernel) (by decide)
theorem wk24 : SixW25P.Covered 29848 42312 58552 80144 58728 78968 31096 39408 29848 42312 :=
  SixW25P.covered_split1 69348 wk24l wk24r
theorem wk25lllllll : SixW25P.Covered 29848 42312 58552 63950 58728 68848 31096 39408 54736 73706 :=
  SixW25P.covered_of_walk lbS hbas 85395146798933998726781482724038982 200 29848 42312 58552 63950 58728 68848 31096 39408 54736 73706 122
    (by decide +kernel) (by decide)
theorem wk25llllllrll : SixW25P.Covered 29848 36080 63950 69348 58728 63788 31096 39408 54736 73706 :=
  SixW25P.covered_of_walk lbS hbas 5753429895490 200 29848 36080 63950 69348 58728 63788 31096 39408 54736 73706 47
    (by decide +kernel) (by decide)
theorem wk25llllllrlrl : SixW25P.Covered 29848 36080 63950 69348 63788 68848 31096 39408 54736 64221 :=
  SixW25P.covered_of_walk lbS hbas 27654170936322785400781387791948403999793752642338655890663459057020459719446218218673915828692725735589252616039545772619568996216530645526525205633486260308319597201353474461351135931958842526090565614156141712498953853530474981559439146277874391838878597106310016737759296755339129784932065805947334409504721664431138656448053525082536777109285794880020054418787871175691795839564370 200 29848 36080 63950 69348 63788 68848 31096 39408 54736 64221 1287
    (by decide +kernel) (by decide)
theorem wk25llllllrlrr : SixW25P.Covered 29848 36080 63950 69348 63788 68848 31096 39408 64221 73706 :=
  SixW25P.covered_of_walk lbS hbas 10655251115298033987042855925413495572316154061438160098067936676046266645567948472804314851741279951824234169771467767281656906370471455477147038535031126566459614696472528388968870511846126188831483550288464619696484344022624246811031101087382727144576764247316461260565184925515953056683029491990024279173460022499668297616271887946841000523791101405713361198645345497703871834450906946652833769420595147665992029494659413787054787936737088075964999954972739444313659235955406445988213844288786718538865533280854171493690964712116726923160629595510015226736927722557763436489520313320676550833133644588687696876610470019506456599020828184128697847176006235744939674231431504837547633990737094617139717218921254962356962845545902492911602869583434924273811967804879707097212177354506781794735712471721410181574161195887675708352805659604625855324937193682272608216902535068147127953529364608118989791147163370166787850898060224067432105554729015228950645426755960344101926081670752854841082374002599596351748053710928984114169605254354217134365855191508618735598682982041830068086863154222730008846635758885178716166049351861298631201639486430944245875456116499901279998999785999021382507427559807087928858776775368783717380431201696288397904460026822828649136989838513513805651860937640712819400373104595371795904012713560746478880421110298636949396123794491830109379344756859033204875673124313761181840771829206448424002655474214055938099892899758913385585276558434864612226416748157531078458135493873815010146282045874094308024893529620094393657234023080130396813569992033481570563194717087318753559502545300904237655739237410391959783604763081664774096538306290218294361264111259012309990394401150640680608788710569895130921530735430212368433050539448917349197687966958609034479728480103150209828068724254970590622935552810024499298532894902479786097905358503895725134161554438400829949053860396966314409998852191793390333218167227569590258642734 200 29848 36080 63950 69348 63788 68848 31096 39408 64221 73706 6492
    (by decide +kernel) (by decide)
theorem wk25llllllrlr : SixW25P.Covered 29848 36080 63950 69348 63788 68848 31096 39408 54736 73706 :=
  SixW25P.covered_split4 64221 wk25llllllrlrl wk25llllllrlrr
theorem wk25llllllrl : SixW25P.Covered 29848 36080 63950 69348 58728 68848 31096 39408 54736 73706 :=
  SixW25P.covered_split2 63788 wk25llllllrll wk25llllllrlr
theorem wk25llllllrr : SixW25P.Covered 36080 42312 63950 69348 58728 68848 31096 39408 54736 73706 :=
  SixW25P.covered_of_walk lbS hbas 58316317115827362 200 36080 42312 63950 69348 58728 68848 31096 39408 54736 73706 67
    (by decide +kernel) (by decide)
theorem wk25llllllr : SixW25P.Covered 29848 42312 63950 69348 58728 68848 31096 39408 54736 73706 :=
  SixW25P.covered_split0 36080 wk25llllllrl wk25llllllrr
theorem wk25llllll : SixW25P.Covered 29848 42312 58552 69348 58728 68848 31096 39408 54736 73706 :=
  SixW25P.covered_split1 63950 wk25lllllll wk25llllllr
theorem wk25lllllr : SixW25P.Covered 29848 42312 58552 69348 68848 78968 31096 39408 54736 73706 :=
  SixW25P.covered_of_walk lbS hbas 10151851738794 200 29848 42312 58552 69348 68848 78968 31096 39408 54736 73706 52
    (by decide +kernel) (by decide)
theorem wk25lllll : SixW25P.Covered 29848 42312 58552 69348 58728 78968 31096 39408 54736 73706 :=
  SixW25P.covered_split2 68848 wk25llllll wk25lllllr
theorem wk25llllr : SixW25P.Covered 29848 42312 69348 80144 58728 78968 31096 39408 54736 73706 :=
  SixW25P.covered_of_walk lbS hbas 8810 200 29848 42312 69348 80144 58728 78968 31096 39408 54736 73706 22
    (by decide +kernel) (by decide)
theorem wk25llll : SixW25P.Covered 29848 42312 58552 80144 58728 78968 31096 39408 54736 73706 :=
  SixW25P.covered_split1 69348 wk25lllll wk25llllr
theorem wk25lllr : SixW25P.Covered 29848 42312 58552 80144 58728 78968 31096 39408 73706 92676 :=
  SixW25P.covered_of_walk lbS hbas 119462 200 29848 42312 58552 80144 58728 78968 31096 39408 73706 92676 22
    (by decide +kernel) (by decide)
theorem wk25lll : SixW25P.Covered 29848 42312 58552 80144 58728 78968 31096 39408 54736 92676 :=
  SixW25P.covered_split4 73706 wk25llll wk25lllr
theorem wk25llr : SixW25P.Covered 29848 42312 58552 80144 58728 78968 31096 39408 92676 130616 :=
  SixW25P.covered_of_walk lbS hbas 619764851178594694319229983878177006101416056034991886052075224941465051000092578918 200 29848 42312 58552 80144 58728 78968 31096 39408 92676 130616 292
    (by decide +kernel) (by decide)
theorem wk25ll : SixW25P.Covered 29848 42312 58552 80144 58728 78968 31096 39408 54736 130616 :=
  SixW25P.covered_split4 92676 wk25lll wk25llr
theorem wk25lr : SixW25P.Covered 29848 42312 58552 80144 58728 78968 31096 39408 130616 206496 :=
  SixW25P.covered_of_walk lbS hbas 0 200 29848 42312 58552 80144 58728 78968 31096 39408 130616 206496 2
    (by decide +kernel) (by decide)
theorem wk25l : SixW25P.Covered 29848 42312 58552 80144 58728 78968 31096 39408 54736 206496 :=
  SixW25P.covered_split4 130616 wk25ll wk25lr
theorem wk25r : SixW25P.Covered 29848 42312 58552 80144 58728 78968 31096 39408 206496 358256 :=
  SixW25P.covered_of_walk lbS hbas 0 200 29848 42312 58552 80144 58728 78968 31096 39408 206496 358256 2
    (by decide +kernel) (by decide)
theorem wk25 : SixW25P.Covered 29848 42312 58552 80144 58728 78968 31096 39408 54736 358256 :=
  SixW25P.covered_split4 206496 wk25l wk25r
theorem wk26 : SixW25P.Covered 29848 42312 58552 80144 58728 78968 58552 80144 29848 42312 :=
  SixW25P.covered_of_walk lbS hbas 169895737187695791496754772245447524374096129895017290578505659034148400638082484515335680788115019251538196255917538352154366507524288672112079903721850948392854581630416108881494188460081273488918874986323506484307899302531831517550642393390816799934129733471640410295321538286106444245140476105306474784246998140268230318357512802439555166471317347236567727512780543556527517092028663917378566799296051427529549015690988649082121615890795212474189848734131775498982 200 29848 42312 58552 80144 58728 78968 58552 80144 29848 42312 1562
    (by decide +kernel) (by decide)
theorem wk27 : SixW25P.Covered 29848 42312 58552 80144 58728 78968 58552 80144 54736 358256 :=
  SixW25P.covered_of_walk lbS hbas 83044551672099634 200 29848 42312 58552 80144 58728 78968 58552 80144 54736 358256 67
    (by decide +kernel) (by decide)
theorem wk28 : SixW25P.Covered 29848 42312 58552 80144 58728 78968 82632 250598 29848 42312 :=
  SixW25P.covered_of_walk lbS hbas 175645814510 200 29848 42312 58552 80144 58728 78968 82632 250598 29848 42312 47
    (by decide +kernel) (by decide)
theorem wk29 : SixW25P.Covered 29848 42312 58552 80144 58728 78968 82632 250598 54736 358256 :=
  SixW25P.covered_of_walk lbS hbas 0 200 29848 42312 58552 80144 58728 78968 82632 250598 54736 358256 2
    (by decide +kernel) (by decide)
theorem wk30 : SixW25P.Covered 29848 42312 58552 80144 83848 289438 31096 39408 29848 42312 :=
  SixW25P.covered_of_walk lbS hbas 2757772197435699289537195756606777991040672825718005418269348680391044835127580234443264470460431842005620568157495984518245628944785006942884600987245502791003198161167119378324527443770201155350956971293264121098037988556446779690124513881039182142512494310757389523781825154755403438908335866585284963140824146848876697183126268321854099546389222898570632522410 200 29848 42312 58552 80144 83848 289438 31096 39408 29848 42312 1212
    (by decide +kernel) (by decide)
theorem wk31 : SixW25P.Covered 29848 42312 58552 80144 83848 289438 31096 39408 54736 358256 :=
  SixW25P.covered_of_walk lbS hbas 271094038838774072446619393066636950974704306 200 29848 42312 58552 80144 83848 289438 31096 39408 54736 358256 157
    (by decide +kernel) (by decide)
theorem wk32 : SixW25P.Covered 29848 42312 58552 80144 83848 289438 58552 80144 29848 42312 :=
  SixW25P.covered_of_walk lbS hbas 5739224394410 200 29848 42312 58552 80144 83848 289438 58552 80144 29848 42312 52
    (by decide +kernel) (by decide)
theorem wk33 : SixW25P.Covered 29848 42312 58552 80144 83848 289438 58552 80144 54736 358256 :=
  SixW25P.covered_of_walk lbS hbas 179514154 200 29848 42312 58552 80144 83848 289438 58552 80144 54736 358256 37
    (by decide +kernel) (by decide)
theorem wk34 : SixW25P.Covered 29848 42312 58552 80144 83848 289438 82632 250598 29848 42312 :=
  SixW25P.covered_of_walk lbS hbas 0 200 29848 42312 58552 80144 83848 289438 82632 250598 29848 42312 2
    (by decide +kernel) (by decide)
theorem wk35 : SixW25P.Covered 29848 42312 58552 80144 83848 289438 82632 250598 54736 358256 :=
  SixW25P.covered_of_walk lbS hbas 0 200 29848 42312 58552 80144 83848 289438 82632 250598 54736 358256 2
    (by decide +kernel) (by decide)
theorem wk36 : SixW25P.Covered 29848 42312 82632 250598 31168 39280 31096 39408 29848 42312 :=
  SixW25P.covered_of_walk lbS hbas 1755839542217672843436907129507181448647490728695829934438156475035719804108122690639124392580964830621282858011594273725945009515446065251175595777698249317531856421026938301287111613632774052535212272183094238692736711665094647070250913638186239985959637399183507964192708612021293861695999263745424095826076132113575879934966082026047232376019441632659908609416910123688849360122216853515545261298860397606695878172738017770573084127055746882157021468811494920048496095658416399430033879860147768531212129886413835877404504164982431506910498566968169361589637755745463039927240258286705183756083431814817331374749958406691919067720041923310027908865581508691008371056498214360023748990431303665951023466918859944379940063181582555684858474520009232315031825440610170709167205593782490549350691835168644360656051319056835642588226759875801487349088957552463107515849701967646118347122359484034077880851349855441608115048515662763449932932807945049581029989134901573861686020061132954567459847662866658505687248914220816204365872068313806973849889965585462852176331739879904986032869966650619370390847849080803889036174832632502984537620462120137230501068942767925907866450658630843903336906733596044836415065114120819800101758969599494787114598 200 29848 42312 82632 250598 31168 39280 31096 39408 29848 42312 4142
    (by decide +kernel) (by decide)
theorem wk37 : SixW25P.Covered 29848 42312 82632 250598 31168 39280 31096 39408 54736 358256 :=
  SixW25P.covered_of_walk lbS hbas 351831861315006412741461351108871319313302075216450981833154918354354732898439710339975495751552327681576819113416902598735423161478920296578523791510565525438401522220723307854192560911606698283697834853328707505828921829761962742690234637385809664445500735854856330657540078151235114923135012833190202899498096120853415952684167739286686067164793007187415846388078501621417718106330678412588388984306879162033080808353674737095272960080363113805153175975923479883134578798202455883143916882519113291096602728956644072051598603561949599634795369211408704610869766586272437266127331025006569140656461059336058010635941673062280694659554046194517374629918210954835032311359066475347713530819962290388866014375227118510668080815348177657706864322562053379628335882293141959753159501775265064626925964369071198410611528011908477481797097563562766675860154044016819484101082156839590471240739166700859178203542928586277655271527693678649942491637919991782231622187852406383340262084253866169449243980876860220698472392953273964394196609321088202038872800603155738910191588176789926694 200 29848 42312 82632 250598 31168 39280 31096 39408 54736 358256 3597
    (by decide +kernel) (by decide)
theorem wk38 : SixW25P.Covered 29848 42312 82632 250598 31168 39280 58552 80144 29848 42312 :=
  SixW25P.covered_of_walk lbS hbas 923504451879396838137913821883066244595979488761578516441302455442931886877302512932279422483496138067439207129720488612403076442269073109727949091670388432752586421653900585980127852000101728307632858049220651019068284715369215290209232486 200 29848 42312 82632 250598 31168 39280 58552 80144 29848 42312 812
    (by decide +kernel) (by decide)
theorem wk39 : SixW25P.Covered 29848 42312 82632 250598 31168 39280 58552 80144 54736 358256 :=
  SixW25P.covered_of_walk lbS hbas 41522261838472998 200 29848 42312 82632 250598 31168 39280 58552 80144 54736 358256 67
    (by decide +kernel) (by decide)
theorem wk40 : SixW25P.Covered 29848 42312 82632 250598 31168 39280 82632 250598 29848 42312 :=
  SixW25P.covered_of_walk lbS hbas 7631988454 200 29848 42312 82632 250598 31168 39280 82632 250598 29848 42312 42
    (by decide +kernel) (by decide)
theorem wk41 : SixW25P.Covered 29848 42312 82632 250598 31168 39280 82632 250598 54736 358256 :=
  SixW25P.covered_of_walk lbS hbas 0 200 29848 42312 82632 250598 31168 39280 82632 250598 54736 358256 2
    (by decide +kernel) (by decide)
theorem wk42 : SixW25P.Covered 29848 42312 82632 250598 58728 78968 31096 39408 29848 42312 :=
  SixW25P.covered_of_walk lbS hbas 112533079889909032437563551675006391102761029989024848464921233363549606720304104844575764135037239009865997264624620205696759211852902417462632654685862906887010909802275088733385236410781098190639776076019295846 200 29848 42312 82632 250598 58728 78968 31096 39408 29848 42312 712
    (by decide +kernel) (by decide)
theorem wk43 : SixW25P.Covered 29848 42312 82632 250598 58728 78968 31096 39408 54736 358256 :=
  SixW25P.covered_of_walk lbS hbas 1948525654021668642170662 200 29848 42312 82632 250598 58728 78968 31096 39408 54736 358256 97
    (by decide +kernel) (by decide)
theorem wk44 : SixW25P.Covered 29848 42312 82632 250598 58728 78968 58552 80144 29848 42312 :=
  SixW25P.covered_of_walk lbS hbas 41964463718 200 29848 42312 82632 250598 58728 78968 58552 80144 29848 42312 47
    (by decide +kernel) (by decide)
theorem wk45 : SixW25P.Covered 29848 42312 82632 250598 58728 78968 58552 80144 54736 358256 :=
  SixW25P.covered_of_walk lbS hbas 0 200 29848 42312 82632 250598 58728 78968 58552 80144 54736 358256 2
    (by decide +kernel) (by decide)
theorem wk46 : SixW25P.Covered 29848 42312 82632 250598 58728 78968 82632 250598 29848 42312 :=
  SixW25P.covered_of_walk lbS hbas 0 200 29848 42312 82632 250598 58728 78968 82632 250598 29848 42312 2
    (by decide +kernel) (by decide)
theorem wk47 : SixW25P.Covered 29848 42312 82632 250598 58728 78968 82632 250598 54736 358256 :=
  SixW25P.covered_of_walk lbS hbas 0 200 29848 42312 82632 250598 58728 78968 82632 250598 54736 358256 2
    (by decide +kernel) (by decide)
theorem wk48 : SixW25P.Covered 29848 42312 82632 250598 83848 289438 31096 39408 29848 42312 :=
  SixW25P.covered_of_walk lbS hbas 747969970611818 200 29848 42312 82632 250598 83848 289438 31096 39408 29848 42312 62
    (by decide +kernel) (by decide)
theorem wk49 : SixW25P.Covered 29848 42312 82632 250598 83848 289438 31096 39408 54736 358256 :=
  SixW25P.covered_of_walk lbS hbas 107636402 200 29848 42312 82632 250598 83848 289438 31096 39408 54736 358256 37
    (by decide +kernel) (by decide)
theorem wk50 : SixW25P.Covered 29848 42312 82632 250598 83848 289438 58552 80144 29848 42312 :=
  SixW25P.covered_of_walk lbS hbas 0 200 29848 42312 82632 250598 83848 289438 58552 80144 29848 42312 2
    (by decide +kernel) (by decide)
theorem wk51 : SixW25P.Covered 29848 42312 82632 250598 83848 289438 58552 80144 54736 358256 :=
  SixW25P.covered_of_walk lbS hbas 0 200 29848 42312 82632 250598 83848 289438 58552 80144 54736 358256 2
    (by decide +kernel) (by decide)
theorem wk52 : SixW25P.Covered 29848 42312 82632 250598 83848 289438 82632 250598 29848 42312 :=
  SixW25P.covered_of_walk lbS hbas 0 200 29848 42312 82632 250598 83848 289438 82632 250598 29848 42312 2
    (by decide +kernel) (by decide)
theorem wk53 : SixW25P.Covered 29848 42312 82632 250598 83848 289438 82632 250598 54736 358256 :=
  SixW25P.covered_of_walk lbS hbas 0 200 29848 42312 82632 250598 83848 289438 82632 250598 54736 358256 2
    (by decide +kernel) (by decide)
theorem wk54 : SixW25P.Covered 54736 358256 31096 39408 31168 39280 31096 39408 29848 42312 :=
  SixW25P.covered_of_walk lbS hbas 0 200 54736 358256 31096 39408 31168 39280 31096 39408 29848 42312 2
    (by decide +kernel) (by decide)
theorem wk55llllllllllll : SixW25P.Covered 54736 59478 31096 35252 31168 35224 31096 39408 54736 73706 :=
  SixW25P.covered_of_walk lbS hbas 0 200 54736 59478 31096 35252 31168 35224 31096 39408 54736 73706 2
    (by decide +kernel) (by decide)
theorem wk55lllllllllllrl : SixW25P.Covered 59478 64221 31096 33174 31168 35224 31096 39408 54736 73706 :=
  SixW25P.covered_of_walk lbS hbas 23982597107783026943197657985555044418 200 59478 64221 31096 33174 31168 35224 31096 39408 54736 73706 127
    (by decide +kernel) (by decide)
theorem wk55lllllllllllrr : SixW25P.Covered 59478 64221 33174 35252 31168 35224 31096 39408 54736 73706 :=
  SixW25P.covered_of_walk lbS hbas 23696657598498468442950280685572052309703230991469998157232585057331680084291084710035411976112668448416275598131404082903326856702774782895390072329599026427434841627634805129332783939734614202339150481872625597570019176183208099539523926542459592298404271620617524086639174639303172095227830818202427259128420920758848941121681646768483375363260430920562288498381159828176617466564726243162172676682107917939968350229211277060183970034006961770820946561980168502371884977988802606623867685945991598277563413001018794682686177304643027334218553826566752241223231532827812099364752652379250526479785680276390464170555423285850724902318944353102997561150642400014720828577172452378386636370364983681913779963861379458519597783084549167093003046026748708690670243259596810856383225046960665015615162078610432627568041460435377533601077488402218730915644992044438360074970403264802435744824458816550492039230451678760610878139152853045634518313840234376298858731467656158842201924089150503284468175050306050686748476029532050892654440298927811330857574120948810488408046741938118901136903762740869760148436375483369112390138290565465035328433458599806621592489264697109875491451304514340586963762835257232127168810531244331459692737559050061526465907201620204262574304561356815437106131055979631399790609059119898821971035659113482111105215964202439737352276464306501973699248386020508369779184666332007679711589820442156245131793652097913567394237259640075247116196409565511512876500573428889575981753592352870390924285359869896097918810353703735740193363357304133703717571710396550326137494788557448534647185879708382734255122974800991555943199387400950974478255461137401870725200916081469731839746545061450716207842977427933430604464789887724520477526429251014058182491432192222903983103568501591618165883748633097783541972591714582547654806340564123875563064136799508124115249587504778143600891446071079119982515177814524174649749363325223029186420711194940288629909272995725374032434784986483932483252749466547821757010518158051626896384451338546984072446744244741533130781199279964300514706445343598150420908443956869550259836610172106248833458451144662315885195178199090297156244146735199608435622426152776388991322907398668569829728060231001788767538 200 59478 64221 33174 35252 31168 35224 31096 39408 54736 73706 7497
    (by decide +kernel) (by decide)
theorem wk55lllllllllllr : SixW25P.Covered 59478 64221 31096 35252 31168 35224 31096 39408 54736 73706 :=
  SixW25P.covered_split1 33174 wk55lllllllllllrl wk55lllllllllllrr
theorem wk55lllllllllll : SixW25P.Covered 54736 64221 31096 35252 31168 35224 31096 39408 54736 73706 :=
  SixW25P.covered_split0 59478 wk55llllllllllll wk55lllllllllllr
theorem wk55llllllllllrl : SixW25P.Covered 64221 73706 31096 35252 31168 35224 31096 39408 54736 64221 :=
  SixW25P.covered_of_walk lbS hbas 23714108584915741505643659643847302943398869383312159773332176508357890693847025059386590227078285919482049610295037273784627151820280067128215762131066474173483825892963235180542453968151074 200 64221 73706 31096 35252 31168 35224 31096 39408 54736 64221 652
    (by decide +kernel) (by decide)
theorem wk55llllllllllrrllll : SixW25P.Covered 64221 68963 31096 33174 31168 35224 31096 35252 64221 68963 :=
  SixW25P.covered_of_walk lbS hbas 647173368171924341251215734592344854585702114160653182941576549731250870374360703226222787114551304367213311901330847228344414256400130583030246214066992541215427612752698751174 200 64221 68963 31096 33174 31168 35224 31096 35252 64221 68963 592
    (by decide +kernel) (by decide)
theorem wk55llllllllllrrlllrl : SixW25P.Covered 64221 68963 33174 35252 31168 35224 31096 33174 64221 68963 :=
  SixW25P.covered_of_walk lbS hbas 686329876727803166462036543593501391351341717856441346694666280753088612115455399240374822798547068870685673068865345880497219936635592552562003255395837077946081296041013277890794568138 200 64221 68963 33174 35252 31168 35224 31096 33174 64221 68963 622
    (by decide +kernel) (by decide)
theorem wk55llllllllllrrlllrrl : SixW25P.Covered 64221 68963 33174 35252 31168 33196 33174 35252 64221 68963 :=
  SixW25P.covered_of_walk lbS hbas 15069348232432179057393765559987619008869218479054755140464192149715187989646328138612697135066597752345219958766376448649148428237706087019802146703144989273765282444276743833930 200 64221 68963 33174 35252 31168 33196 33174 35252 64221 68963 597
    (by decide +kernel) (by decide)
theorem wk55llllllllllrrlllrrrllllll : SixW25P.Covered 64221 66592 33174 34213 33196 33703 33174 34213 64221 66592 :=
  SixW25P.covered_of_walk lbS hbas 74813011873836926670689253797902771912789717738324869055745055053753688904701640377865095710135119441662156352396915606350419656425475894565080737673686909536990118617689258572192218855293306693391899391466165530315228199761230495947709141984698524214078595664006591313080326708109948703509145671380839171651270842447487098637506574970977962023261407416536301824040634684652056847240104998874653730700231737200628422524403010306218853263754559275074900335239354096381547923907344809957366747795046904979716979909627109769367219439188196169114017220165356376914864251913657820818447023035010217223652239463335353118588567575205195292764062726786388379381720525985192490123597012010716064686774345117399227189503552437003567347090226401050928090593922815403491318573179859977804980724112575128290669749165028738463075487191669719258455338025280045377160929367099017321285819621839390564845004027789742468975926909155023735055609010937340586284878283413219005134940788679582435670978935764661490535056890407731779136831182322006568162041168913218472674099973777630508597869294700748655081210646606790722015948080444976985061459957385440968755751805382349355692169609800070062433603983268234930774498980930135356174714761983768646626274487045269330600817989425846004104184010617680114594541955641535206 200 64221 66592 33174 34213 33196 33703 33174 34213 64221 66592 4317
    (by decide +kernel) (by decide)
theorem wk55llllllllllrrlllrrrlllllrl : SixW25P.Covered 64221 66592 33174 33693 33703 34210 33174 34213 64221 66592 :=
  SixW25P.covered_of_walk lbS hbas 50545451547042175582358802932389551556421711098146619019747918748181934267537155834233008523546747317883161509581296008637779912257364917544665115455465412291044240193668564790876864467927074430731851564830255477845846924395876546174569608447636117367033137596277338491074870019589171202675528902974772243497766715160545851828700359812614543703529499881855718433618880961295620185838185227264920362133940255356232774019833935434088127013625595803441440086032801725750124437877093923049486022016636867945046047567808968768285191304625041838131523587655685831124780339647759054621634094054631627065426524555875777266523580846747856286993464575904012445319203819890803995662286471351226117528962480490281247186654121193747533042769924699591368467672712802207826143809577989979915626115630 200 64221 66592 33174 33693 33703 34210 33174 34213 64221 66592 2612
    (by decide +kernel) (by decide)
theorem wk55llllllllllrrlllrrrlllllrr : SixW25P.Covered 64221 66592 33693 34213 33703 34210 33174 34213 64221 66592 :=
  SixW25P.covered_of_walk lbS hbas 5375074219841460474148143854895683329286624399425914136048368596649533713788296195757264954975936088790107157331471647281758234226236106235452893647977972375282047681674325524692075723610702559581874505659326167250531091722801903061284779713576931792873748285706689603643787575107194518684027676298185582142237017856331416463357313524708041717603845220655133847440980045789609388679410879438931299349009746502468779869529625170081844438534750408657514489325209892229855667468807658893525068302521434984534427375156516283048985554958880033776329070290613626453142053115944732007981107976774684074172192704426336121899916914323172566095898499933670789655319476235392782218440484284674402754903952152790937699571177658207941603808453145214983523648320114112490175811408684399561394299020220100525272463379472214474460167545626583489880598159393006801496210103250426919941859462502109539791918510573775748865536704670731753955494032292426741735581442366423850877846711483919578915247955098801744488626512882593587708852586713776887333957101058247741755266481103290889059239063267967075260692844461305487654848901756422877550899672164380312799813495809655766710220635064999508561002294176583175885908455840485791565872410222566603625186366049562883000533618744643301207008346483811776830604632833822861673143487897211850395548300734735199818993678753112007358086933397584542862101129441813263428796103072337989483925128150301293411289239323908903382133647493106051024172603505723622779501540821137722400138063821323838435944134749552031062437283175439163974443544888723076962162605205086801791504692033244169761338099806067727872889118219759207647718188497641420807326095479599662 200 64221 66592 33693 34213 33703 34210 33174 34213 64221 66592 5567
    (by decide +kernel) (by decide)
theorem wk55llllllllllrrlllrrrlllllr : SixW25P.Covered 64221 66592 33174 34213 33703 34210 33174 34213 64221 66592 :=
  SixW25P.covered_split1 33693 wk55llllllllllrrlllrrrlllllrl wk55llllllllllrrlllrrrlllllrr
theorem wk55llllllllllrrlllrrrlllll : SixW25P.Covered 64221 66592 33174 34213 33196 34210 33174 34213 64221 66592 :=
  SixW25P.covered_split2 33703 wk55llllllllllrrlllrrrllllll wk55llllllllllrrlllrrrlllllr
theorem wk55llllllllllrrlllrrrllllr : SixW25P.Covered 64221 66592 33174 34213 33196 34210 34213 35252 64221 66592 :=
  SixW25P.covered_of_walk lbS hbas 335605121747722253959307897845276265333792368092754637424662230804598074675340624556701141887906919713792671219568038536930381169226702119776198346136818151364438130860770306079039875507828973265887117010622209652526463602267801529018458238367678549426874705775430292702682812303662857849584601333607393580586513793054566570182624406407159630701323540294322897758665910949859502905759402429291613994803292785525074346297478977369376918456996928520570496367834927461928459638963942026120579110177100102853534895052382287152790470887251428812490679711651156006990409321046962108959635703772747929282131970844050007667306 200 64221 66592 33174 34213 33196 34210 34213 35252 64221 66592 2057
    (by decide +kernel) (by decide)
theorem wk55llllllllllrrlllrrrllll : SixW25P.Covered 64221 66592 33174 34213 33196 34210 33174 35252 64221 66592 :=
  SixW25P.covered_split3 34213 wk55llllllllllrrlllrrrlllll wk55llllllllllrrlllrrrllllr
theorem wk55llllllllllrrlllrrrlllr : SixW25P.Covered 64221 66592 34213 35252 33196 34210 33174 35252 64221 66592 :=
  SixW25P.covered_of_walk lbS hbas 107135014675608065326461027314897924183063552565575192679102584335672290441071820643734236959158067402729390054574161547756697375805825169468516986470875687350781950467940634789440449806392709277232465778041128032930842427559168201845385197755789781772905182235504854324250065229298103784988800792547461231780162893675498201905828171032808805799213145869089355834653975184162711322380529033030193981338456305787487069478382480716813046694730047535725371226457017829994866430616525629994530961970920605300166887018043334246950257071256344249550719613346085267639519855159075405571530091419414027707286627457866858401222511835043914287884815304167141610282224047720479896096517967474874752726695178641245125153693422247155910114112792710473546084014 200 64221 66592 34213 35252 33196 34210 33174 35252 64221 66592 2482
    (by decide +kernel) (by decide)
theorem wk55llllllllllrrlllrrrlll : SixW25P.Covered 64221 66592 33174 35252 33196 34210 33174 35252 64221 66592 :=
  SixW25P.covered_split1 34213 wk55llllllllllrrlllrrrllll wk55llllllllllrrlllrrrlllr
theorem wk55llllllllllrrlllrrrllr : SixW25P.Covered 64221 66592 33174 35252 34210 35224 33174 35252 64221 66592 :=
  SixW25P.covered_of_walk lbS hbas 3515114966013838846979873481294981222887154080412420123769347570862325978150840041723407886285566961711437237514232606949171346259577697028558787523944781876670631272082519042802349019220812853534630782806106634790034359286905916953131403808916670522412818509160144130071561919551686007154446374668394030340694354561411249042765610352191627403398828275880289373325245128302174053331051034160087279775698491500337029990797106714481042973401159221339235941173577194052846874042761769194724672385004369618348568163952511631383335442706758760611321479427609677164824918327290184129529435914893725943190192165531086911168502640136216693211816194648150303248492462845991918655387580717010251973079686963897942916975697900004870335564511110886 200 64221 66592 33174 35252 34210 35224 33174 35252 64221 66592 2452
    (by decide +kernel) (by decide)
theorem wk55llllllllllrrlllrrrll : SixW25P.Covered 64221 66592 33174 35252 33196 35224 33174 35252 64221 66592 :=
  SixW25P.covered_split2 34210 wk55llllllllllrrlllrrrlll wk55llllllllllrrlllrrrllr
theorem wk55llllllllllrrlllrrrlr : SixW25P.Covered 64221 66592 33174 35252 33196 35224 33174 35252 66592 68963 :=
  SixW25P.covered_of_walk lbS hbas 8141221847960973478517853143012924910770923794886904670489537238808204047616425996316226422335239733881198448676567312705198 200 64221 66592 33174 35252 33196 35224 33174 35252 66592 68963 417
    (by decide +kernel) (by decide)
theorem wk55llllllllllrrlllrrrl : SixW25P.Covered 64221 66592 33174 35252 33196 35224 33174 35252 64221 68963 :=
  SixW25P.covered_split4 66592 wk55llllllllllrrlllrrrll wk55llllllllllrrlllrrrlr
theorem wk55llllllllllrrlllrrrr : SixW25P.Covered 66592 68963 33174 35252 33196 35224 33174 35252 64221 68963 :=
  SixW25P.covered_of_walk lbS hbas 456297372461141065888029842765554388871400844245501953039376204107677464828483245541555315494 200 66592 68963 33174 35252 33196 35224 33174 35252 64221 68963 312
    (by decide +kernel) (by decide)
theorem wk55llllllllllrrlllrrr : SixW25P.Covered 64221 68963 33174 35252 33196 35224 33174 35252 64221 68963 :=
  SixW25P.covered_split0 66592 wk55llllllllllrrlllrrrl wk55llllllllllrrlllrrrr
theorem wk55llllllllllrrlllrr : SixW25P.Covered 64221 68963 33174 35252 31168 35224 33174 35252 64221 68963 :=
  SixW25P.covered_split2 33196 wk55llllllllllrrlllrrl wk55llllllllllrrlllrrr
theorem wk55llllllllllrrlllr : SixW25P.Covered 64221 68963 33174 35252 31168 35224 31096 35252 64221 68963 :=
  SixW25P.covered_split3 33174 wk55llllllllllrrlllrl wk55llllllllllrrlllrr
theorem wk55llllllllllrrlll : SixW25P.Covered 64221 68963 31096 35252 31168 35224 31096 35252 64221 68963 :=
  SixW25P.covered_split1 33174 wk55llllllllllrrllll wk55llllllllllrrlllr
theorem wk55llllllllllrrllr : SixW25P.Covered 64221 68963 31096 35252 31168 35224 31096 35252 68963 73706 :=
  SixW25P.covered_of_walk lbS hbas 3392719602 200 64221 68963 31096 35252 31168 35224 31096 35252 68963 73706 37
    (by decide +kernel) (by decide)
theorem wk55llllllllllrrll : SixW25P.Covered 64221 68963 31096 35252 31168 35224 31096 35252 64221 73706 :=
  SixW25P.covered_split4 68963 wk55llllllllllrrlll wk55llllllllllrrllr
theorem wk55llllllllllrrlr : SixW25P.Covered 68963 73706 31096 35252 31168 35224 31096 35252 64221 73706 :=
  SixW25P.covered_of_walk lbS hbas 5604401762 200 68963 73706 31096 35252 31168 35224 31096 35252 64221 73706 37
    (by decide +kernel) (by decide)
theorem wk55llllllllllrrl : SixW25P.Covered 64221 73706 31096 35252 31168 35224 31096 35252 64221 73706 :=
  SixW25P.covered_split0 68963 wk55llllllllllrrll wk55llllllllllrrlr
theorem wk55llllllllllrrr : SixW25P.Covered 64221 73706 31096 35252 31168 35224 35252 39408 64221 73706 :=
  SixW25P.covered_of_walk lbS hbas 25829157845655663393596312332159420645821949742 200 64221 73706 31096 35252 31168 35224 35252 39408 64221 73706 162
    (by decide +kernel) (by decide)
theorem wk55llllllllllrr : SixW25P.Covered 64221 73706 31096 35252 31168 35224 31096 39408 64221 73706 :=
  SixW25P.covered_split3 35252 wk55llllllllllrrl wk55llllllllllrrr
theorem wk55llllllllllr : SixW25P.Covered 64221 73706 31096 35252 31168 35224 31096 39408 54736 73706 :=
  SixW25P.covered_split4 64221 wk55llllllllllrl wk55llllllllllrr
theorem wk55llllllllll : SixW25P.Covered 54736 73706 31096 35252 31168 35224 31096 39408 54736 73706 :=
  SixW25P.covered_split0 64221 wk55lllllllllll wk55llllllllllr
theorem wk55lllllllllr : SixW25P.Covered 54736 73706 35252 39408 31168 35224 31096 39408 54736 73706 :=
  SixW25P.covered_of_walk lbS hbas 4723035731078277412039551287686659016480346674322144614421849717339375092232751002317656763400442609794670181901970250245363458475890860569802096276560640428968923721805712441894 200 54736 73706 35252 39408 31168 35224 31096 39408 54736 73706 597
    (by decide +kernel) (by decide)
theorem wk55lllllllll : SixW25P.Covered 54736 73706 31096 39408 31168 35224 31096 39408 54736 73706 :=
  SixW25P.covered_split1 35252 wk55llllllllll wk55lllllllllr
theorem wk55llllllllr : SixW25P.Covered 54736 73706 31096 39408 35224 39280 31096 39408 54736 73706 :=
  SixW25P.covered_of_walk lbS hbas 4460125144552368456051728491881442121484543266487181778803686313762375027507576920161437956792663762034246129974530564302780598147796019808206341699045691215966246793766360679457138703316860050129450 200 54736 73706 31096 39408 35224 39280 31096 39408 54736 73706 672
    (by decide +kernel) (by decide)
theorem wk55llllllll : SixW25P.Covered 54736 73706 31096 39408 31168 39280 31096 39408 54736 73706 :=
  SixW25P.covered_split2 35224 wk55lllllllll wk55llllllllr
theorem wk55lllllllr : SixW25P.Covered 54736 73706 31096 39408 31168 39280 31096 39408 73706 92676 :=
  SixW25P.covered_of_walk lbS hbas 2924001839698 200 54736 73706 31096 39408 31168 39280 31096 39408 73706 92676 47
    (by decide +kernel) (by decide)
theorem wk55lllllll : SixW25P.Covered 54736 73706 31096 39408 31168 39280 31096 39408 54736 92676 :=
  SixW25P.covered_split4 73706 wk55llllllll wk55lllllllr
theorem wk55llllllr : SixW25P.Covered 73706 92676 31096 39408 31168 39280 31096 39408 54736 92676 :=
  SixW25P.covered_of_walk lbS hbas 578 200 73706 92676 31096 39408 31168 39280 31096 39408 54736 92676 12
    (by decide +kernel) (by decide)
theorem wk55llllll : SixW25P.Covered 54736 92676 31096 39408 31168 39280 31096 39408 54736 92676 :=
  SixW25P.covered_split0 73706 wk55lllllll wk55llllllr
theorem wk55lllllr : SixW25P.Covered 54736 92676 31096 39408 31168 39280 31096 39408 92676 130616 :=
  SixW25P.covered_of_walk lbS hbas 132090720107971246396700649009690901149695748540347001827785197351050690760612048030537191731011383035953713659393757152852547718554063756760462651570692907883306679609064340853512005750245756265344679584542377231155806235636900433776623761850805373269404516276618228868466025072663828147332481391365134998273744920467974428126082126274913005271005266596886381193721060050774291794913097879839185704450276559202181780582419789541910050693181686436024988965436913020594279012094831176282013959355348333940844805026734529643931696066061814730994221448086340636078835762682806455188991318554703664114743219828705873264407035648683846610130804275189712031222838317952959140241308251967149318275358088430265003342137121438394169862633602398475171344565349179409579691862612444897329186596175552293574032561472014037800175018674261113034784073506103672016819103786352248909257365368916881494690082674925385049917780405456784499744689135314028451121156296331889946402 200 54736 92676 31096 39408 31168 39280 31096 39408 92676 130616 3192
    (by decide +kernel) (by decide)
theorem wk55lllll : SixW25P.Covered 54736 92676 31096 39408 31168 39280 31096 39408 54736 130616 :=
  SixW25P.covered_split4 92676 wk55llllll wk55lllllr
theorem wk55llllr : SixW25P.Covered 92676 130616 31096 39408 31168 39280 31096 39408 54736 130616 :=
  SixW25P.covered_of_walk lbS hbas 115291154113245981750043401358038792218705344728968563866741960116975260609605029715716299067621142418000812582579283248341234867620625338063240381999721349497174692092683570 200 92676 130616 31096 39408 31168 39280 31096 39408 54736 130616 582
    (by decide +kernel) (by decide)
theorem wk55llll : SixW25P.Covered 54736 130616 31096 39408 31168 39280 31096 39408 54736 130616 :=
  SixW25P.covered_split0 92676 wk55lllll wk55llllr
theorem wk55lllr : SixW25P.Covered 54736 130616 31096 39408 31168 39280 31096 39408 130616 206496 :=
  SixW25P.covered_of_walk lbS hbas 56682138774920307914895253616648472261147761776649187915671217275866986565391502900422882383758342959650 200 54736 130616 31096 39408 31168 39280 31096 39408 130616 206496 357
    (by decide +kernel) (by decide)
theorem wk55lll : SixW25P.Covered 54736 130616 31096 39408 31168 39280 31096 39408 54736 206496 :=
  SixW25P.covered_split4 130616 wk55llll wk55lllr
theorem wk55llr : SixW25P.Covered 130616 206496 31096 39408 31168 39280 31096 39408 54736 206496 :=
  SixW25P.covered_of_walk lbS hbas 9522 200 130616 206496 31096 39408 31168 39280 31096 39408 54736 206496 17
    (by decide +kernel) (by decide)
theorem wk55ll : SixW25P.Covered 54736 206496 31096 39408 31168 39280 31096 39408 54736 206496 :=
  SixW25P.covered_split0 130616 wk55lll wk55llr
theorem wk55lr : SixW25P.Covered 54736 206496 31096 39408 31168 39280 31096 39408 206496 358256 :=
  SixW25P.covered_of_walk lbS hbas 0 200 54736 206496 31096 39408 31168 39280 31096 39408 206496 358256 2
    (by decide +kernel) (by decide)
theorem wk55l : SixW25P.Covered 54736 206496 31096 39408 31168 39280 31096 39408 54736 358256 :=
  SixW25P.covered_split4 206496 wk55ll wk55lr
theorem wk55r : SixW25P.Covered 206496 358256 31096 39408 31168 39280 31096 39408 54736 358256 :=
  SixW25P.covered_of_walk lbS hbas 0 200 206496 358256 31096 39408 31168 39280 31096 39408 54736 358256 2
    (by decide +kernel) (by decide)
theorem wk55 : SixW25P.Covered 54736 358256 31096 39408 31168 39280 31096 39408 54736 358256 :=
  SixW25P.covered_split0 206496 wk55l wk55r
theorem wk56 : SixW25P.Covered 54736 358256 31096 39408 31168 39280 58552 80144 29848 42312 :=
  SixW25P.covered_of_walk lbS hbas 0 200 54736 358256 31096 39408 31168 39280 58552 80144 29848 42312 2
    (by decide +kernel) (by decide)
theorem wk57 : SixW25P.Covered 54736 358256 31096 39408 31168 39280 58552 80144 54736 358256 :=
  SixW25P.covered_of_walk lbS hbas 3550094944036992240339147084897552813147821832618661702892933944340860149275179147616991358647471899193624627938560451988978828932293942076819668309465149882663122961241507813173808218382820336484566161822005034827482312984808841068632861459076311202809105395703321140050673165587692391196811692610147272922124513771971205112480855343751229624461361129900318152688007735810877846530354671022246645741676195627486581207958477835852305230459164258883163397669671308857333456842350242870082028712265270967924290843939067810156174837163305703126102543957473589395534462342477357588986291248198283465261818583637028068863404840769227697096448397992712987767061936598183518908087793380350596928652529760177356081455796069615516188605635325644688960265488363069710104593332720721210617940519161609161198095196547463518578534823376122887366488678187790487156854086271555825143399532797963032579388569684035756845568853214170029952896824064234107057951395669843843730712828288915116394149581863074547850687790889610058674898381371547182428227646698880304498412892467697899804940808914833291925985352413641240599674304367559665560530694640022892605305417505430708105826030010884892059364084228131775099368223634562190009597210407774126975894429575238563354163137103344295737465037120073999653234409184363601336782564099391209696701192686758050239328902829470479681269317906501742930855052681832570153800606115589747649900522994471134816264101488675444298260143213958226787403718548230507839655892070848377938657162537346556840512898334651323071756614021541916937245809291246187636846640373678635906359721388697719188990846167590087307436609766449207375697600962948593321680495919358510667724274585376947440162693358277942169622787747777449362120998214619840537714781413570761118571601812773260055616218738722971984646753600287522 200 54736 358256 31096 39408 31168 39280 58552 80144 54736 358256 6052
    (by decide +kernel) (by decide)
theorem wk58 : SixW25P.Covered 54736 358256 31096 39408 31168 39280 82632 250598 29848 42312 :=
  SixW25P.covered_of_walk lbS hbas 0 200 54736 358256 31096 39408 31168 39280 82632 250598 29848 42312 2
    (by decide +kernel) (by decide)
theorem wk59 : SixW25P.Covered 54736 358256 31096 39408 31168 39280 82632 250598 54736 358256 :=
  SixW25P.covered_of_walk lbS hbas 2725107089742415305939040324619635088572106891522786 200 54736 358256 31096 39408 31168 39280 82632 250598 54736 358256 187
    (by decide +kernel) (by decide)
theorem wk60 : SixW25P.Covered 54736 358256 31096 39408 58728 78968 31096 39408 29848 42312 :=
  SixW25P.covered_of_walk lbS hbas 0 200 54736 358256 31096 39408 58728 78968 31096 39408 29848 42312 2
    (by decide +kernel) (by decide)
theorem wk61llllllllll : SixW25P.Covered 54736 73706 31096 39408 58728 63788 31096 39408 54736 73706 :=
  SixW25P.covered_of_walk lbS hbas 109028593578533004779587504251759250011054869253339485505507945672928315031737840798910465391771794366645446323229795049048394 200 54736 73706 31096 39408 58728 63788 31096 39408 54736 73706 427
    (by decide +kernel) (by decide)
theorem wk61lllllllllrl : SixW25P.Covered 54736 64221 31096 39408 63788 68848 31096 39408 54736 73706 :=
  SixW25P.covered_of_walk lbS hbas 1195825733268487878546070801152363266743195107933487677729220486949953959534052946214331886538128940913935057526310713646250449355459642688290122730940298882664683572218955615735275122057239949589619215531022211983611099692620560024949134954067641105910644768760142557441276988003183002560106679218721479398625384775193465325733660580159391962101528154234802375932502156602032466411005905119132477049982075091574830196832280390001418826941922156819043324807456344224459307088069634465029650188468875465754793753108337497559615697114000084265751881300222137656231299714701231660106492358949379574020320982411726401419555335625390468574584665958993534094060269709353643447735614863953601952925484116823313144386609921246601107962043162636368895305425013346956064911855020801841508866455594641774352171897838937029885090391094713892362912099106081353405760350609944810092862195077456607156195799968656940090079055281841379931830950430844526187628219538472185513881055704432217623606003278219993777568989499766665039494138963974509509041343682 200 54736 64221 31096 39408 63788 68848 31096 39408 54736 73706 3457
    (by decide +kernel) (by decide)
theorem wk61lllllllllrrll : SixW25P.Covered 64221 73706 31096 35252 63788 68848 31096 39408 54736 64221 :=
  SixW25P.covered_of_walk lbS hbas 4204808781828232449295158302628053828673221871889617061692498 200 64221 73706 31096 35252 63788 68848 31096 39408 54736 64221 222
    (by decide +kernel) (by decide)
theorem wk61lllllllllrrlrllll : SixW25P.Covered 64221 68963 31096 33174 63788 68848 31096 35252 64221 68963 :=
  SixW25P.covered_of_walk lbS hbas 2811566286 200 64221 68963 31096 33174 63788 68848 31096 35252 64221 68963 37
    (by decide +kernel) (by decide)
theorem wk61lllllllllrrlrlllrl : SixW25P.Covered 64221 68963 33174 35252 63788 68848 31096 33174 64221 68963 :=
  SixW25P.covered_of_walk lbS hbas 85502414 200 64221 68963 33174 35252 63788 68848 31096 33174 64221 68963 32
    (by decide +kernel) (by decide)
theorem wk61lllllllllrrlrlllrrl : SixW25P.Covered 64221 68963 33174 35252 63788 66318 33174 35252 64221 68963 :=
  SixW25P.covered_of_walk lbS hbas 1357894010687126340102255058126436883952493850536044388604569896814585044418642849438363268282826063461824695579825113122852916130549284878670794998200184987564440234235620016623487095371687125248701423583348174650971490797932524879632619216720585517067197929007348845994791887616011561893861575346474139906766651496043779281511348349341866299010613759417818529714137954833883719582382882608609493752152184860686818318895329686118739014445293809925645619320719481819054951618732058682243559152382836863573397881620902006931967556321057788955044666326747113423451127134207761748258304896791836950125591952349289435564799968121057181811812074734434421941131627339070373962985386244765531764906626522277456880599028591901893423004128456846650725966602941102193546776068164043037344326082986673103425958052649332347839244633443010566271390478798124561231305554382858165161615124170776421030900615501963977342697090144787107857351041770107822199865749614475350541172985111184947241440320698282083834859944907135575716242985387416643321326906649812228654420625620182751675029782180408336469699225028984284725705743526598847781582433508080031737620997811170611298079052961895291939976597624133173145425919391049535529229451563232931335784574510481933219539515381445841491482077994812710128181295636946883335106912740717620718461499891420554327038841006601134371908300267442518097877993427322098719733159886095234193923493232132211095394465709668100078337656552696943833360465268767010063670259332327347683540442783990494744411407545088442297566247296213130147570688514812252461898910331624987792426284190782526102274076715201811530039565951516848357393748243115261590816227814932045835005256977611735064006887028219480019916541225240331177188065717982460309753334897862525037414236000134613200260602907255185188344066306347335370559645834037975345606109898677463553376920130974163766667131833801160413357279669215351378705470032386022628731767975609361299256991438712321612955343726641419942034917403705505954597961413457966783003375904712509227970965760791723897587037683556639934421405843013418671365521634883634359074 200 64221 68963 33174 35252 63788 66318 33174 35252 64221 68963 7022
    (by decide +kernel) (by decide)
theorem wk61lllllllllrrlrlllrrr : SixW25P.Covered 64221 68963 33174 35252 66318 68848 33174 35252 64221 68963 :=
  SixW25P.covered_of_walk lbS hbas 265393294639160842695603336784037647124500866282372406140175592407315478458214770049529167663253560102135781089467393969093530173237945698577023404397603599509970132471669029757148814310894231535884512008987603276895188170866084967058366697885299834858439765829762748060650678333462411320958904900569109150889016902172782054897530243721197129202389756933150369532242085256251376158156399377135706585670405344481416719561527348874304039582727917082792157179177762 200 64221 68963 33174 35252 66318 68848 33174 35252 64221 68963 1537
    (by decide +kernel) (by decide)
theorem wk61lllllllllrrlrlllrr : SixW25P.Covered 64221 68963 33174 35252 63788 68848 33174 35252 64221 68963 :=
  SixW25P.covered_split2 66318 wk61lllllllllrrlrlllrrl wk61lllllllllrrlrlllrrr
theorem wk61lllllllllrrlrlllr : SixW25P.Covered 64221 68963 33174 35252 63788 68848 31096 35252 64221 68963 :=
  SixW25P.covered_split3 33174 wk61lllllllllrrlrlllrl wk61lllllllllrrlrlllrr
theorem wk61lllllllllrrlrlll : SixW25P.Covered 64221 68963 31096 35252 63788 68848 31096 35252 64221 68963 :=
  SixW25P.covered_split1 33174 wk61lllllllllrrlrllll wk61lllllllllrrlrlllr
theorem wk61lllllllllrrlrllr : SixW25P.Covered 64221 68963 31096 35252 63788 68848 31096 35252 68963 73706 :=
  SixW25P.covered_of_walk lbS hbas 206 200 64221 68963 31096 35252 63788 68848 31096 35252 68963 73706 12
    (by decide +kernel) (by decide)
theorem wk61lllllllllrrlrll : SixW25P.Covered 64221 68963 31096 35252 63788 68848 31096 35252 64221 73706 :=
  SixW25P.covered_split4 68963 wk61lllllllllrrlrlll wk61lllllllllrrlrllr
theorem wk61lllllllllrrlrlr : SixW25P.Covered 68963 73706 31096 35252 63788 68848 31096 35252 64221 73706 :=
  SixW25P.covered_of_walk lbS hbas 454 200 68963 73706 31096 35252 63788 68848 31096 35252 64221 73706 12
    (by decide +kernel) (by decide)
theorem wk61lllllllllrrlrl : SixW25P.Covered 64221 73706 31096 35252 63788 68848 31096 35252 64221 73706 :=
  SixW25P.covered_split0 68963 wk61lllllllllrrlrll wk61lllllllllrrlrlr
theorem wk61lllllllllrrlrr : SixW25P.Covered 64221 73706 31096 35252 63788 68848 35252 39408 64221 73706 :=
  SixW25P.covered_of_walk lbS hbas 1928383527040148209655853976269032507203637462585309857952764063902564664683736444282780263657750517150585876270 200 64221 73706 31096 35252 63788 68848 35252 39408 64221 73706 382
    (by decide +kernel) (by decide)
theorem wk61lllllllllrrlr : SixW25P.Covered 64221 73706 31096 35252 63788 68848 31096 39408 64221 73706 :=
  SixW25P.covered_split3 35252 wk61lllllllllrrlrl wk61lllllllllrrlrr
theorem wk61lllllllllrrl : SixW25P.Covered 64221 73706 31096 35252 63788 68848 31096 39408 54736 73706 :=
  SixW25P.covered_split4 64221 wk61lllllllllrrll wk61lllllllllrrlr
theorem wk61lllllllllrrr : SixW25P.Covered 64221 73706 35252 39408 63788 68848 31096 39408 54736 73706 :=
  SixW25P.covered_of_walk lbS hbas 289182290085156525684413741422352300303461819051442430289101869580095194579068031553694167602259884316655176840335544081441571267875752748045504891022619234 200 64221 73706 35252 39408 63788 68848 31096 39408 54736 73706 532
    (by decide +kernel) (by decide)
theorem wk61lllllllllrr : SixW25P.Covered 64221 73706 31096 39408 63788 68848 31096 39408 54736 73706 :=
  SixW25P.covered_split1 35252 wk61lllllllllrrl wk61lllllllllrrr
theorem wk61lllllllllr : SixW25P.Covered 54736 73706 31096 39408 63788 68848 31096 39408 54736 73706 :=
  SixW25P.covered_split0 64221 wk61lllllllllrl wk61lllllllllrr
theorem wk61lllllllll : SixW25P.Covered 54736 73706 31096 39408 58728 68848 31096 39408 54736 73706 :=
  SixW25P.covered_split2 63788 wk61llllllllll wk61lllllllllr
theorem wk61llllllllr : SixW25P.Covered 54736 73706 31096 39408 68848 78968 31096 39408 54736 73706 :=
  SixW25P.covered_of_walk lbS hbas 144264027369972426927661738 200 54736 73706 31096 39408 68848 78968 31096 39408 54736 73706 97
    (by decide +kernel) (by decide)
theorem wk61llllllll : SixW25P.Covered 54736 73706 31096 39408 58728 78968 31096 39408 54736 73706 :=
  SixW25P.covered_split2 68848 wk61lllllllll wk61llllllllr
theorem wk61lllllllr : SixW25P.Covered 54736 73706 31096 39408 58728 78968 31096 39408 73706 92676 :=
  SixW25P.covered_of_walk lbS hbas 40234 200 54736 73706 31096 39408 58728 78968 31096 39408 73706 92676 22
    (by decide +kernel) (by decide)
theorem wk61lllllll : SixW25P.Covered 54736 73706 31096 39408 58728 78968 31096 39408 54736 92676 :=
  SixW25P.covered_split4 73706 wk61llllllll wk61lllllllr
theorem wk61llllllr : SixW25P.Covered 73706 92676 31096 39408 58728 78968 31096 39408 54736 92676 :=
  SixW25P.covered_of_walk lbS hbas 50 200 73706 92676 31096 39408 58728 78968 31096 39408 54736 92676 12
    (by decide +kernel) (by decide)
theorem wk61llllll : SixW25P.Covered 54736 92676 31096 39408 58728 78968 31096 39408 54736 92676 :=
  SixW25P.covered_split0 73706 wk61lllllll wk61llllllr
theorem wk61lllllr : SixW25P.Covered 54736 92676 31096 39408 58728 78968 31096 39408 92676 130616 :=
  SixW25P.covered_of_walk lbS hbas 61215543518969079687478075040260641392117763766707160420326005821934403575040958601790027539909805896224981912343538977130333114928524267969000967491769786720165230689699025356250111991574631137545373700365162695905786655003744136370852394849039073692898378414066621299293721626094289854226562975056428050922055412404928716154034399906 200 54736 92676 31096 39408 58728 78968 31096 39408 92676 130616 1122
    (by decide +kernel) (by decide)
theorem wk61lllll : SixW25P.Covered 54736 92676 31096 39408 58728 78968 31096 39408 54736 130616 :=
  SixW25P.covered_split4 92676 wk61llllll wk61lllllr
theorem wk61llllr : SixW25P.Covered 54736 92676 31096 39408 58728 78968 31096 39408 130616 206496 :=
  SixW25P.covered_of_walk lbS hbas 4926242 200 54736 92676 31096 39408 58728 78968 31096 39408 130616 206496 32
    (by decide +kernel) (by decide)
theorem wk61llll : SixW25P.Covered 54736 92676 31096 39408 58728 78968 31096 39408 54736 206496 :=
  SixW25P.covered_split4 130616 wk61lllll wk61llllr
theorem wk61lllr : SixW25P.Covered 92676 130616 31096 39408 58728 78968 31096 39408 54736 206496 :=
  SixW25P.covered_of_walk lbS hbas 2409798210354 200 92676 130616 31096 39408 58728 78968 31096 39408 54736 206496 52
    (by decide +kernel) (by decide)
theorem wk61lll : SixW25P.Covered 54736 130616 31096 39408 58728 78968 31096 39408 54736 206496 :=
  SixW25P.covered_split0 92676 wk61llll wk61lllr
theorem wk61llr : SixW25P.Covered 130616 206496 31096 39408 58728 78968 31096 39408 54736 206496 :=
  SixW25P.covered_of_walk lbS hbas 306 200 130616 206496 31096 39408 58728 78968 31096 39408 54736 206496 12
    (by decide +kernel) (by decide)
theorem wk61ll : SixW25P.Covered 54736 206496 31096 39408 58728 78968 31096 39408 54736 206496 :=
  SixW25P.covered_split0 130616 wk61lll wk61llr
theorem wk61lr : SixW25P.Covered 54736 206496 31096 39408 58728 78968 31096 39408 206496 358256 :=
  SixW25P.covered_of_walk lbS hbas 0 200 54736 206496 31096 39408 58728 78968 31096 39408 206496 358256 2
    (by decide +kernel) (by decide)
theorem wk61l : SixW25P.Covered 54736 206496 31096 39408 58728 78968 31096 39408 54736 358256 :=
  SixW25P.covered_split4 206496 wk61ll wk61lr
theorem wk61r : SixW25P.Covered 206496 358256 31096 39408 58728 78968 31096 39408 54736 358256 :=
  SixW25P.covered_of_walk lbS hbas 0 200 206496 358256 31096 39408 58728 78968 31096 39408 54736 358256 2
    (by decide +kernel) (by decide)
theorem wk61 : SixW25P.Covered 54736 358256 31096 39408 58728 78968 31096 39408 54736 358256 :=
  SixW25P.covered_split0 206496 wk61l wk61r
theorem wk62 : SixW25P.Covered 54736 358256 31096 39408 58728 78968 58552 80144 29848 42312 :=
  SixW25P.covered_of_walk lbS hbas 0 200 54736 358256 31096 39408 58728 78968 58552 80144 29848 42312 2
    (by decide +kernel) (by decide)
theorem wk63 : SixW25P.Covered 54736 358256 31096 39408 58728 78968 58552 80144 54736 358256 :=
  SixW25P.covered_of_walk lbS hbas 54300392010922164029556327812725879768897046743926040418436762491507608340857923282303665369655075244848448262523780944367902513050402 200 54736 358256 31096 39408 58728 78968 58552 80144 54736 358256 452
    (by decide +kernel) (by decide)
theorem wk64 : SixW25P.Covered 54736 358256 31096 39408 58728 78968 82632 250598 29848 42312 :=
  SixW25P.covered_of_walk lbS hbas 0 200 54736 358256 31096 39408 58728 78968 82632 250598 29848 42312 2
    (by decide +kernel) (by decide)
theorem wk65 : SixW25P.Covered 54736 358256 31096 39408 58728 78968 82632 250598 54736 358256 :=
  SixW25P.covered_of_walk lbS hbas 16433118638818 200 54736 358256 31096 39408 58728 78968 82632 250598 54736 358256 57
    (by decide +kernel) (by decide)
theorem wk66 : SixW25P.Covered 54736 358256 31096 39408 83848 289438 31096 39408 29848 42312 :=
  SixW25P.covered_of_walk lbS hbas 0 200 54736 358256 31096 39408 83848 289438 31096 39408 29848 42312 2
    (by decide +kernel) (by decide)
theorem wk67 : SixW25P.Covered 54736 358256 31096 39408 83848 289438 31096 39408 54736 358256 :=
  SixW25P.covered_of_walk lbS hbas 749534330509064826697025773702071147217374354394953104555136251945797179442157988895918112339393717609781402555827551884001930415974910128154190449156945644339876991869618274884095291990362386217935483434 200 54736 358256 31096 39408 83848 289438 31096 39408 54736 358256 687
    (by decide +kernel) (by decide)
theorem wk68 : SixW25P.Covered 54736 358256 31096 39408 83848 289438 58552 80144 29848 42312 :=
  SixW25P.covered_of_walk lbS hbas 0 200 54736 358256 31096 39408 83848 289438 58552 80144 29848 42312 2
    (by decide +kernel) (by decide)
theorem wk69 : SixW25P.Covered 54736 358256 31096 39408 83848 289438 58552 80144 54736 358256 :=
  SixW25P.covered_of_walk lbS hbas 94279420410507818 200 54736 358256 31096 39408 83848 289438 58552 80144 54736 358256 72
    (by decide +kernel) (by decide)
theorem wk70 : SixW25P.Covered 54736 358256 31096 39408 83848 289438 82632 250598 29848 42312 :=
  SixW25P.covered_of_walk lbS hbas 0 200 54736 358256 31096 39408 83848 289438 82632 250598 29848 42312 2
    (by decide +kernel) (by decide)
theorem wk71 : SixW25P.Covered 54736 358256 31096 39408 83848 289438 82632 250598 54736 358256 :=
  SixW25P.covered_of_walk lbS hbas 0 200 54736 358256 31096 39408 83848 289438 82632 250598 54736 358256 2
    (by decide +kernel) (by decide)
theorem wk72 : SixW25P.Covered 54736 358256 58552 80144 31168 39280 31096 39408 29848 42312 :=
  SixW25P.covered_of_walk lbS hbas 0 200 54736 358256 58552 80144 31168 39280 31096 39408 29848 42312 2
    (by decide +kernel) (by decide)
theorem wk73 : SixW25P.Covered 54736 358256 58552 80144 31168 39280 31096 39408 54736 358256 :=
  SixW25P.covered_of_walk lbS hbas 20992125223637213828768283564509670671338878148736920045243090521965196622366835456559184995925226950861693890582642040206237034013882933774136872794684612521632577167018212704155136402227959536664778465412807681156144775827676405019434954105762278952712400986578082512293669668476112854856265398364097340377849207894587137629059022404215607471743535308978024034657252376756021079251499413439905288494812659517626255533588571646287524471263636172585904795408579056450691671114617142017780112938695403191437461073142230974177579270607455983277915068637373268566521225121857520048882754048991803433765982828871716901271165314196447616664029963216952612698800113198176445129389216737819452471805420226873410412457918753558005714559067849787194306565179195711713628044667131098266607629828407540001358409788872484893959742108960288502730927333394865275036441072704435348304568893082120340978796248428279805307083129483891671053039772794805989770159783387033064549641686997989078602530101266826861456273523658050503766931282188891373087895981612941991967973042520047320456351366940038834969107810256613905443674161070160991724712459264298431948160831342041354209306107955093291199072643527454865539112097302144944093075310424387261401984766073811766029480431452840159086174754454158017517318780605812927571534727929492493519661871504369348199909872206907972661282048305443109739525105854265716942425398611448859262459322086616854060825574674302168051623544289250497172864206870559018907436378067092460300414665715824079788644876508572795906283291834025456065196449118762171750739494506228228497970 200 54736 358256 58552 80144 31168 39280 31096 39408 54736 358256 5292
    (by decide +kernel) (by decide)
theorem wk74 : SixW25P.Covered 54736 358256 58552 80144 31168 39280 58552 80144 29848 42312 :=
  SixW25P.covered_of_walk lbS hbas 0 200 54736 358256 58552 80144 31168 39280 58552 80144 29848 42312 2
    (by decide +kernel) (by decide)
theorem wk75 : SixW25P.Covered 54736 358256 58552 80144 31168 39280 58552 80144 54736 358256 :=
  SixW25P.covered_of_walk lbS hbas 4501482415082239164693555907447076593693333970690850 200 54736 358256 58552 80144 31168 39280 58552 80144 54736 358256 182
    (by decide +kernel) (by decide)
theorem wk76 : SixW25P.Covered 54736 358256 58552 80144 31168 39280 82632 250598 29848 42312 :=
  SixW25P.covered_of_walk lbS hbas 0 200 54736 358256 58552 80144 31168 39280 82632 250598 29848 42312 2
    (by decide +kernel) (by decide)
theorem wk77 : SixW25P.Covered 54736 358256 58552 80144 31168 39280 82632 250598 54736 358256 :=
  SixW25P.covered_of_walk lbS hbas 1027086672686 200 54736 358256 58552 80144 31168 39280 82632 250598 54736 358256 52
    (by decide +kernel) (by decide)
theorem wk78 : SixW25P.Covered 54736 358256 58552 80144 58728 78968 31096 39408 29848 42312 :=
  SixW25P.covered_of_walk lbS hbas 0 200 54736 358256 58552 80144 58728 78968 31096 39408 29848 42312 2
    (by decide +kernel) (by decide)
theorem wk79 : SixW25P.Covered 54736 358256 58552 80144 58728 78968 31096 39408 54736 358256 :=
  SixW25P.covered_of_walk lbS hbas 2108192430820687855332269299791803570481574240091833260579458451511327065075735973505249673516909652893583454834877745604521566770 200 54736 358256 58552 80144 58728 78968 31096 39408 54736 358256 442
    (by decide +kernel) (by decide)
theorem wk80 : SixW25P.Covered 54736 358256 58552 80144 58728 78968 58552 80144 29848 42312 :=
  SixW25P.covered_of_walk lbS hbas 0 200 54736 358256 58552 80144 58728 78968 58552 80144 29848 42312 2
    (by decide +kernel) (by decide)
theorem wk81 : SixW25P.Covered 54736 358256 58552 80144 58728 78968 58552 80144 54736 358256 :=
  SixW25P.covered_of_walk lbS hbas 589505314 200 54736 358256 58552 80144 58728 78968 58552 80144 54736 358256 42
    (by decide +kernel) (by decide)
theorem wk82 : SixW25P.Covered 54736 358256 58552 80144 58728 78968 82632 250598 29848 42312 :=
  SixW25P.covered_of_walk lbS hbas 0 200 54736 358256 58552 80144 58728 78968 82632 250598 29848 42312 2
    (by decide +kernel) (by decide)
theorem wk83 : SixW25P.Covered 54736 358256 58552 80144 58728 78968 82632 250598 54736 358256 :=
  SixW25P.covered_of_walk lbS hbas 0 200 54736 358256 58552 80144 58728 78968 82632 250598 54736 358256 2
    (by decide +kernel) (by decide)
theorem wk84 : SixW25P.Covered 54736 358256 58552 80144 83848 289438 31096 39408 29848 42312 :=
  SixW25P.covered_of_walk lbS hbas 0 200 54736 358256 58552 80144 83848 289438 31096 39408 29848 42312 2
    (by decide +kernel) (by decide)
theorem wk85 : SixW25P.Covered 54736 358256 58552 80144 83848 289438 31096 39408 54736 358256 :=
  SixW25P.covered_of_walk lbS hbas 91869364187472682 200 54736 358256 58552 80144 83848 289438 31096 39408 54736 358256 72
    (by decide +kernel) (by decide)
theorem wk86 : SixW25P.Covered 54736 358256 58552 80144 83848 289438 58552 80144 29848 42312 :=
  SixW25P.covered_of_walk lbS hbas 0 200 54736 358256 58552 80144 83848 289438 58552 80144 29848 42312 2
    (by decide +kernel) (by decide)
theorem wk87 : SixW25P.Covered 54736 358256 58552 80144 83848 289438 58552 80144 54736 358256 :=
  SixW25P.covered_of_walk lbS hbas 0 200 54736 358256 58552 80144 83848 289438 58552 80144 54736 358256 2
    (by decide +kernel) (by decide)
theorem wk88 : SixW25P.Covered 54736 358256 58552 80144 83848 289438 82632 250598 29848 42312 :=
  SixW25P.covered_of_walk lbS hbas 0 200 54736 358256 58552 80144 83848 289438 82632 250598 29848 42312 2
    (by decide +kernel) (by decide)
theorem wk89 : SixW25P.Covered 54736 358256 58552 80144 83848 289438 82632 250598 54736 358256 :=
  SixW25P.covered_of_walk lbS hbas 0 200 54736 358256 58552 80144 83848 289438 82632 250598 54736 358256 2
    (by decide +kernel) (by decide)
theorem wk90 : SixW25P.Covered 54736 358256 82632 250598 31168 39280 31096 39408 29848 42312 :=
  SixW25P.covered_of_walk lbS hbas 0 200 54736 358256 82632 250598 31168 39280 31096 39408 29848 42312 2
    (by decide +kernel) (by decide)
theorem wk91 : SixW25P.Covered 54736 358256 82632 250598 31168 39280 31096 39408 54736 358256 :=
  SixW25P.covered_of_walk lbS hbas 1141022181084163711142331253296476461053890862932594 200 54736 358256 82632 250598 31168 39280 31096 39408 54736 358256 187
    (by decide +kernel) (by decide)
theorem wk92 : SixW25P.Covered 54736 358256 82632 250598 31168 39280 58552 80144 29848 42312 :=
  SixW25P.covered_of_walk lbS hbas 0 200 54736 358256 82632 250598 31168 39280 58552 80144 29848 42312 2
    (by decide +kernel) (by decide)
theorem wk93 : SixW25P.Covered 54736 358256 82632 250598 31168 39280 58552 80144 54736 358256 :=
  SixW25P.covered_of_walk lbS hbas 438928831014 200 54736 358256 82632 250598 31168 39280 58552 80144 54736 358256 52
    (by decide +kernel) (by decide)
theorem wk94 : SixW25P.Covered 54736 358256 82632 250598 31168 39280 82632 250598 29848 42312 :=
  SixW25P.covered_of_walk lbS hbas 0 200 54736 358256 82632 250598 31168 39280 82632 250598 29848 42312 2
    (by decide +kernel) (by decide)
theorem wk95 : SixW25P.Covered 54736 358256 82632 250598 31168 39280 82632 250598 54736 358256 :=
  SixW25P.covered_of_walk lbS hbas 0 200 54736 358256 82632 250598 31168 39280 82632 250598 54736 358256 2
    (by decide +kernel) (by decide)
theorem wk96 : SixW25P.Covered 54736 358256 82632 250598 58728 78968 31096 39408 29848 42312 :=
  SixW25P.covered_of_walk lbS hbas 0 200 54736 358256 82632 250598 58728 78968 31096 39408 29848 42312 2
    (by decide +kernel) (by decide)
theorem wk97 : SixW25P.Covered 54736 358256 82632 250598 58728 78968 31096 39408 54736 358256 :=
  SixW25P.covered_of_walk lbS hbas 7023129420402 200 54736 358256 82632 250598 58728 78968 31096 39408 54736 358256 57
    (by decide +kernel) (by decide)
theorem wk98 : SixW25P.Covered 54736 358256 82632 250598 58728 78968 58552 80144 29848 42312 :=
  SixW25P.covered_of_walk lbS hbas 0 200 54736 358256 82632 250598 58728 78968 58552 80144 29848 42312 2
    (by decide +kernel) (by decide)
theorem wk99 : SixW25P.Covered 54736 358256 82632 250598 58728 78968 58552 80144 54736 358256 :=
  SixW25P.covered_of_walk lbS hbas 0 200 54736 358256 82632 250598 58728 78968 58552 80144 54736 358256 2
    (by decide +kernel) (by decide)
theorem wk100 : SixW25P.Covered 54736 358256 82632 250598 58728 78968 82632 250598 29848 42312 :=
  SixW25P.covered_of_walk lbS hbas 0 200 54736 358256 82632 250598 58728 78968 82632 250598 29848 42312 2
    (by decide +kernel) (by decide)
theorem wk101 : SixW25P.Covered 54736 358256 82632 250598 58728 78968 82632 250598 54736 358256 :=
  SixW25P.covered_of_walk lbS hbas 0 200 54736 358256 82632 250598 58728 78968 82632 250598 54736 358256 2
    (by decide +kernel) (by decide)
theorem wk102 : SixW25P.Covered 54736 358256 82632 250598 83848 289438 31096 39408 29848 42312 :=
  SixW25P.covered_of_walk lbS hbas 0 200 54736 358256 82632 250598 83848 289438 31096 39408 29848 42312 2
    (by decide +kernel) (by decide)
theorem wk103 : SixW25P.Covered 54736 358256 82632 250598 83848 289438 31096 39408 54736 358256 :=
  SixW25P.covered_of_walk lbS hbas 0 200 54736 358256 82632 250598 83848 289438 31096 39408 54736 358256 2
    (by decide +kernel) (by decide)
theorem wk104 : SixW25P.Covered 54736 358256 82632 250598 83848 289438 58552 80144 29848 42312 :=
  SixW25P.covered_of_walk lbS hbas 0 200 54736 358256 82632 250598 83848 289438 58552 80144 29848 42312 2
    (by decide +kernel) (by decide)
theorem wk105 : SixW25P.Covered 54736 358256 82632 250598 83848 289438 58552 80144 54736 358256 :=
  SixW25P.covered_of_walk lbS hbas 0 200 54736 358256 82632 250598 83848 289438 58552 80144 54736 358256 2
    (by decide +kernel) (by decide)
theorem wk106 : SixW25P.Covered 54736 358256 82632 250598 83848 289438 82632 250598 29848 42312 :=
  SixW25P.covered_of_walk lbS hbas 0 200 54736 358256 82632 250598 83848 289438 82632 250598 29848 42312 2
    (by decide +kernel) (by decide)
theorem wk107 : SixW25P.Covered 54736 358256 82632 250598 83848 289438 82632 250598 54736 358256 :=
  SixW25P.covered_of_walk lbS hbas 0 200 54736 358256 82632 250598 83848 289438 82632 250598 54736 358256 2
    (by decide +kernel) (by decide)
theorem bd0_0 : (SixW25P.badOf cover0).getD 0 (0, 0) = (29848, 42312) := by decide +kernel
theorem bd0_1 : (SixW25P.badOf cover0).getD 1 (0, 0) = (54736, 358256) := by decide +kernel
theorem nb0_eq : (SixW25P.badOf cover0).length = 2 := by decide +kernel
theorem bd1_0 : (SixW25P.badOf cover1).getD 0 (0, 0) = (31096, 39408) := by decide +kernel
theorem bd1_1 : (SixW25P.badOf cover1).getD 1 (0, 0) = (58552, 80144) := by decide +kernel
theorem bd1_2 : (SixW25P.badOf cover1).getD 2 (0, 0) = (82632, 250598) := by decide +kernel
theorem nb1_eq : (SixW25P.badOf cover1).length = 3 := by decide +kernel
theorem bd2_0 : (SixW25P.badOf cover2).getD 0 (0, 0) = (31168, 39280) := by decide +kernel
theorem bd2_1 : (SixW25P.badOf cover2).getD 1 (0, 0) = (58728, 78968) := by decide +kernel
theorem bd2_2 : (SixW25P.badOf cover2).getD 2 (0, 0) = (83848, 289438) := by decide +kernel
theorem nb2_eq : (SixW25P.badOf cover2).length = 3 := by decide +kernel
theorem bd3_0 : (SixW25P.badOf cover3).getD 0 (0, 0) = (31096, 39408) := by decide +kernel
theorem bd3_1 : (SixW25P.badOf cover3).getD 1 (0, 0) = (58552, 80144) := by decide +kernel
theorem bd3_2 : (SixW25P.badOf cover3).getD 2 (0, 0) = (82632, 250598) := by decide +kernel
theorem nb3_eq : (SixW25P.badOf cover3).length = 3 := by decide +kernel
theorem bd4_0 : (SixW25P.badOf cover4).getD 0 (0, 0) = (29848, 42312) := by decide +kernel
theorem bd4_1 : (SixW25P.badOf cover4).getD 1 (0, 0) = (54736, 358256) := by decide +kernel
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
  | 0, 0, 1, 0, 1, _, _, _, _, _ => rw [bd0_0, bd1_0, bd2_1, bd3_0, bd4_1]; exact wk7
  | 0, 0, 1, 1, 0, _, _, _, _, _ => rw [bd0_0, bd1_0, bd2_1, bd3_1, bd4_0]; exact wk8
  | 0, 0, 1, 1, 1, _, _, _, _, _ => rw [bd0_0, bd1_0, bd2_1, bd3_1, bd4_1]; exact wk9
  | 0, 0, 1, 2, 0, _, _, _, _, _ => rw [bd0_0, bd1_0, bd2_1, bd3_2, bd4_0]; exact wk10
  | 0, 0, 1, 2, 1, _, _, _, _, _ => rw [bd0_0, bd1_0, bd2_1, bd3_2, bd4_1]; exact wk11
  | 0, 0, 2, 0, 0, _, _, _, _, _ => rw [bd0_0, bd1_0, bd2_2, bd3_0, bd4_0]; exact wk12
  | 0, 0, 2, 0, 1, _, _, _, _, _ => rw [bd0_0, bd1_0, bd2_2, bd3_0, bd4_1]; exact wk13
  | 0, 0, 2, 1, 0, _, _, _, _, _ => rw [bd0_0, bd1_0, bd2_2, bd3_1, bd4_0]; exact wk14
  | 0, 0, 2, 1, 1, _, _, _, _, _ => rw [bd0_0, bd1_0, bd2_2, bd3_1, bd4_1]; exact wk15
  | 0, 0, 2, 2, 0, _, _, _, _, _ => rw [bd0_0, bd1_0, bd2_2, bd3_2, bd4_0]; exact wk16
  | 0, 0, 2, 2, 1, _, _, _, _, _ => rw [bd0_0, bd1_0, bd2_2, bd3_2, bd4_1]; exact wk17
  | 0, 1, 0, 0, 0, _, _, _, _, _ => rw [bd0_0, bd1_1, bd2_0, bd3_0, bd4_0]; exact wk18
  | 0, 1, 0, 0, 1, _, _, _, _, _ => rw [bd0_0, bd1_1, bd2_0, bd3_0, bd4_1]; exact wk19
  | 0, 1, 0, 1, 0, _, _, _, _, _ => rw [bd0_0, bd1_1, bd2_0, bd3_1, bd4_0]; exact wk20
  | 0, 1, 0, 1, 1, _, _, _, _, _ => rw [bd0_0, bd1_1, bd2_0, bd3_1, bd4_1]; exact wk21
  | 0, 1, 0, 2, 0, _, _, _, _, _ => rw [bd0_0, bd1_1, bd2_0, bd3_2, bd4_0]; exact wk22
  | 0, 1, 0, 2, 1, _, _, _, _, _ => rw [bd0_0, bd1_1, bd2_0, bd3_2, bd4_1]; exact wk23
  | 0, 1, 1, 0, 0, _, _, _, _, _ => rw [bd0_0, bd1_1, bd2_1, bd3_0, bd4_0]; exact wk24
  | 0, 1, 1, 0, 1, _, _, _, _, _ => rw [bd0_0, bd1_1, bd2_1, bd3_0, bd4_1]; exact wk25
  | 0, 1, 1, 1, 0, _, _, _, _, _ => rw [bd0_0, bd1_1, bd2_1, bd3_1, bd4_0]; exact wk26
  | 0, 1, 1, 1, 1, _, _, _, _, _ => rw [bd0_0, bd1_1, bd2_1, bd3_1, bd4_1]; exact wk27
  | 0, 1, 1, 2, 0, _, _, _, _, _ => rw [bd0_0, bd1_1, bd2_1, bd3_2, bd4_0]; exact wk28
  | 0, 1, 1, 2, 1, _, _, _, _, _ => rw [bd0_0, bd1_1, bd2_1, bd3_2, bd4_1]; exact wk29
  | 0, 1, 2, 0, 0, _, _, _, _, _ => rw [bd0_0, bd1_1, bd2_2, bd3_0, bd4_0]; exact wk30
  | 0, 1, 2, 0, 1, _, _, _, _, _ => rw [bd0_0, bd1_1, bd2_2, bd3_0, bd4_1]; exact wk31
  | 0, 1, 2, 1, 0, _, _, _, _, _ => rw [bd0_0, bd1_1, bd2_2, bd3_1, bd4_0]; exact wk32
  | 0, 1, 2, 1, 1, _, _, _, _, _ => rw [bd0_0, bd1_1, bd2_2, bd3_1, bd4_1]; exact wk33
  | 0, 1, 2, 2, 0, _, _, _, _, _ => rw [bd0_0, bd1_1, bd2_2, bd3_2, bd4_0]; exact wk34
  | 0, 1, 2, 2, 1, _, _, _, _, _ => rw [bd0_0, bd1_1, bd2_2, bd3_2, bd4_1]; exact wk35
  | 0, 2, 0, 0, 0, _, _, _, _, _ => rw [bd0_0, bd1_2, bd2_0, bd3_0, bd4_0]; exact wk36
  | 0, 2, 0, 0, 1, _, _, _, _, _ => rw [bd0_0, bd1_2, bd2_0, bd3_0, bd4_1]; exact wk37
  | 0, 2, 0, 1, 0, _, _, _, _, _ => rw [bd0_0, bd1_2, bd2_0, bd3_1, bd4_0]; exact wk38
  | 0, 2, 0, 1, 1, _, _, _, _, _ => rw [bd0_0, bd1_2, bd2_0, bd3_1, bd4_1]; exact wk39
  | 0, 2, 0, 2, 0, _, _, _, _, _ => rw [bd0_0, bd1_2, bd2_0, bd3_2, bd4_0]; exact wk40
  | 0, 2, 0, 2, 1, _, _, _, _, _ => rw [bd0_0, bd1_2, bd2_0, bd3_2, bd4_1]; exact wk41
  | 0, 2, 1, 0, 0, _, _, _, _, _ => rw [bd0_0, bd1_2, bd2_1, bd3_0, bd4_0]; exact wk42
  | 0, 2, 1, 0, 1, _, _, _, _, _ => rw [bd0_0, bd1_2, bd2_1, bd3_0, bd4_1]; exact wk43
  | 0, 2, 1, 1, 0, _, _, _, _, _ => rw [bd0_0, bd1_2, bd2_1, bd3_1, bd4_0]; exact wk44
  | 0, 2, 1, 1, 1, _, _, _, _, _ => rw [bd0_0, bd1_2, bd2_1, bd3_1, bd4_1]; exact wk45
  | 0, 2, 1, 2, 0, _, _, _, _, _ => rw [bd0_0, bd1_2, bd2_1, bd3_2, bd4_0]; exact wk46
  | 0, 2, 1, 2, 1, _, _, _, _, _ => rw [bd0_0, bd1_2, bd2_1, bd3_2, bd4_1]; exact wk47
  | 0, 2, 2, 0, 0, _, _, _, _, _ => rw [bd0_0, bd1_2, bd2_2, bd3_0, bd4_0]; exact wk48
  | 0, 2, 2, 0, 1, _, _, _, _, _ => rw [bd0_0, bd1_2, bd2_2, bd3_0, bd4_1]; exact wk49
  | 0, 2, 2, 1, 0, _, _, _, _, _ => rw [bd0_0, bd1_2, bd2_2, bd3_1, bd4_0]; exact wk50
  | 0, 2, 2, 1, 1, _, _, _, _, _ => rw [bd0_0, bd1_2, bd2_2, bd3_1, bd4_1]; exact wk51
  | 0, 2, 2, 2, 0, _, _, _, _, _ => rw [bd0_0, bd1_2, bd2_2, bd3_2, bd4_0]; exact wk52
  | 0, 2, 2, 2, 1, _, _, _, _, _ => rw [bd0_0, bd1_2, bd2_2, bd3_2, bd4_1]; exact wk53
  | 1, 0, 0, 0, 0, _, _, _, _, _ => rw [bd0_1, bd1_0, bd2_0, bd3_0, bd4_0]; exact wk54
  | 1, 0, 0, 0, 1, _, _, _, _, _ => rw [bd0_1, bd1_0, bd2_0, bd3_0, bd4_1]; exact wk55
  | 1, 0, 0, 1, 0, _, _, _, _, _ => rw [bd0_1, bd1_0, bd2_0, bd3_1, bd4_0]; exact wk56
  | 1, 0, 0, 1, 1, _, _, _, _, _ => rw [bd0_1, bd1_0, bd2_0, bd3_1, bd4_1]; exact wk57
  | 1, 0, 0, 2, 0, _, _, _, _, _ => rw [bd0_1, bd1_0, bd2_0, bd3_2, bd4_0]; exact wk58
  | 1, 0, 0, 2, 1, _, _, _, _, _ => rw [bd0_1, bd1_0, bd2_0, bd3_2, bd4_1]; exact wk59
  | 1, 0, 1, 0, 0, _, _, _, _, _ => rw [bd0_1, bd1_0, bd2_1, bd3_0, bd4_0]; exact wk60
  | 1, 0, 1, 0, 1, _, _, _, _, _ => rw [bd0_1, bd1_0, bd2_1, bd3_0, bd4_1]; exact wk61
  | 1, 0, 1, 1, 0, _, _, _, _, _ => rw [bd0_1, bd1_0, bd2_1, bd3_1, bd4_0]; exact wk62
  | 1, 0, 1, 1, 1, _, _, _, _, _ => rw [bd0_1, bd1_0, bd2_1, bd3_1, bd4_1]; exact wk63
  | 1, 0, 1, 2, 0, _, _, _, _, _ => rw [bd0_1, bd1_0, bd2_1, bd3_2, bd4_0]; exact wk64
  | 1, 0, 1, 2, 1, _, _, _, _, _ => rw [bd0_1, bd1_0, bd2_1, bd3_2, bd4_1]; exact wk65
  | 1, 0, 2, 0, 0, _, _, _, _, _ => rw [bd0_1, bd1_0, bd2_2, bd3_0, bd4_0]; exact wk66
  | 1, 0, 2, 0, 1, _, _, _, _, _ => rw [bd0_1, bd1_0, bd2_2, bd3_0, bd4_1]; exact wk67
  | 1, 0, 2, 1, 0, _, _, _, _, _ => rw [bd0_1, bd1_0, bd2_2, bd3_1, bd4_0]; exact wk68
  | 1, 0, 2, 1, 1, _, _, _, _, _ => rw [bd0_1, bd1_0, bd2_2, bd3_1, bd4_1]; exact wk69
  | 1, 0, 2, 2, 0, _, _, _, _, _ => rw [bd0_1, bd1_0, bd2_2, bd3_2, bd4_0]; exact wk70
  | 1, 0, 2, 2, 1, _, _, _, _, _ => rw [bd0_1, bd1_0, bd2_2, bd3_2, bd4_1]; exact wk71
  | 1, 1, 0, 0, 0, _, _, _, _, _ => rw [bd0_1, bd1_1, bd2_0, bd3_0, bd4_0]; exact wk72
  | 1, 1, 0, 0, 1, _, _, _, _, _ => rw [bd0_1, bd1_1, bd2_0, bd3_0, bd4_1]; exact wk73
  | 1, 1, 0, 1, 0, _, _, _, _, _ => rw [bd0_1, bd1_1, bd2_0, bd3_1, bd4_0]; exact wk74
  | 1, 1, 0, 1, 1, _, _, _, _, _ => rw [bd0_1, bd1_1, bd2_0, bd3_1, bd4_1]; exact wk75
  | 1, 1, 0, 2, 0, _, _, _, _, _ => rw [bd0_1, bd1_1, bd2_0, bd3_2, bd4_0]; exact wk76
  | 1, 1, 0, 2, 1, _, _, _, _, _ => rw [bd0_1, bd1_1, bd2_0, bd3_2, bd4_1]; exact wk77
  | 1, 1, 1, 0, 0, _, _, _, _, _ => rw [bd0_1, bd1_1, bd2_1, bd3_0, bd4_0]; exact wk78
  | 1, 1, 1, 0, 1, _, _, _, _, _ => rw [bd0_1, bd1_1, bd2_1, bd3_0, bd4_1]; exact wk79
  | 1, 1, 1, 1, 0, _, _, _, _, _ => rw [bd0_1, bd1_1, bd2_1, bd3_1, bd4_0]; exact wk80
  | 1, 1, 1, 1, 1, _, _, _, _, _ => rw [bd0_1, bd1_1, bd2_1, bd3_1, bd4_1]; exact wk81
  | 1, 1, 1, 2, 0, _, _, _, _, _ => rw [bd0_1, bd1_1, bd2_1, bd3_2, bd4_0]; exact wk82
  | 1, 1, 1, 2, 1, _, _, _, _, _ => rw [bd0_1, bd1_1, bd2_1, bd3_2, bd4_1]; exact wk83
  | 1, 1, 2, 0, 0, _, _, _, _, _ => rw [bd0_1, bd1_1, bd2_2, bd3_0, bd4_0]; exact wk84
  | 1, 1, 2, 0, 1, _, _, _, _, _ => rw [bd0_1, bd1_1, bd2_2, bd3_0, bd4_1]; exact wk85
  | 1, 1, 2, 1, 0, _, _, _, _, _ => rw [bd0_1, bd1_1, bd2_2, bd3_1, bd4_0]; exact wk86
  | 1, 1, 2, 1, 1, _, _, _, _, _ => rw [bd0_1, bd1_1, bd2_2, bd3_1, bd4_1]; exact wk87
  | 1, 1, 2, 2, 0, _, _, _, _, _ => rw [bd0_1, bd1_1, bd2_2, bd3_2, bd4_0]; exact wk88
  | 1, 1, 2, 2, 1, _, _, _, _, _ => rw [bd0_1, bd1_1, bd2_2, bd3_2, bd4_1]; exact wk89
  | 1, 2, 0, 0, 0, _, _, _, _, _ => rw [bd0_1, bd1_2, bd2_0, bd3_0, bd4_0]; exact wk90
  | 1, 2, 0, 0, 1, _, _, _, _, _ => rw [bd0_1, bd1_2, bd2_0, bd3_0, bd4_1]; exact wk91
  | 1, 2, 0, 1, 0, _, _, _, _, _ => rw [bd0_1, bd1_2, bd2_0, bd3_1, bd4_0]; exact wk92
  | 1, 2, 0, 1, 1, _, _, _, _, _ => rw [bd0_1, bd1_2, bd2_0, bd3_1, bd4_1]; exact wk93
  | 1, 2, 0, 2, 0, _, _, _, _, _ => rw [bd0_1, bd1_2, bd2_0, bd3_2, bd4_0]; exact wk94
  | 1, 2, 0, 2, 1, _, _, _, _, _ => rw [bd0_1, bd1_2, bd2_0, bd3_2, bd4_1]; exact wk95
  | 1, 2, 1, 0, 0, _, _, _, _, _ => rw [bd0_1, bd1_2, bd2_1, bd3_0, bd4_0]; exact wk96
  | 1, 2, 1, 0, 1, _, _, _, _, _ => rw [bd0_1, bd1_2, bd2_1, bd3_0, bd4_1]; exact wk97
  | 1, 2, 1, 1, 0, _, _, _, _, _ => rw [bd0_1, bd1_2, bd2_1, bd3_1, bd4_0]; exact wk98
  | 1, 2, 1, 1, 1, _, _, _, _, _ => rw [bd0_1, bd1_2, bd2_1, bd3_1, bd4_1]; exact wk99
  | 1, 2, 1, 2, 0, _, _, _, _, _ => rw [bd0_1, bd1_2, bd2_1, bd3_2, bd4_0]; exact wk100
  | 1, 2, 1, 2, 1, _, _, _, _, _ => rw [bd0_1, bd1_2, bd2_1, bd3_2, bd4_1]; exact wk101
  | 1, 2, 2, 0, 0, _, _, _, _, _ => rw [bd0_1, bd1_2, bd2_2, bd3_0, bd4_0]; exact wk102
  | 1, 2, 2, 0, 1, _, _, _, _, _ => rw [bd0_1, bd1_2, bd2_2, bd3_0, bd4_1]; exact wk103
  | 1, 2, 2, 1, 0, _, _, _, _, _ => rw [bd0_1, bd1_2, bd2_2, bd3_1, bd4_0]; exact wk104
  | 1, 2, 2, 1, 1, _, _, _, _, _ => rw [bd0_1, bd1_2, bd2_2, bd3_1, bd4_1]; exact wk105
  | 1, 2, 2, 2, 0, _, _, _, _, _ => rw [bd0_1, bd1_2, bd2_2, bd3_2, bd4_0]; exact wk106
  | 1, 2, 2, 2, 1, _, _, _, _, _ => rw [bd0_1, bd1_2, bd2_2, bd3_2, bd4_1]; exact wk107
  | i + 2, _, _, _, _, hi, _, _, _, _ => exact absurd hi (by omega)
  | _, i + 3, _, _, _, _, hi, _, _, _ => exact absurd hi (by omega)
  | _, _, i + 3, _, _, _, _, hi, _, _ => exact absurd hi (by omega)
  | _, _, _, i + 3, _, _, _, _, hi, _ => exact absurd hi (by omega)
  | _, _, _, _, i + 2, _, _, _, _, hi => exact absurd hi (by omega)

theorem cert : ∀ g0 g1 g2 g3 g4 : ℝ, 0 ≤ g0 → 0 ≤ g1 → 0 ≤ g2 → 0 ≤ g3 → 0 ≤ g4 → (SixW25P.cN : ℝ) / SixW25P.SA ≤ SixW25P.G g0 g1 g2 g3 g4 ∨ g4 < g0 :=
  SixW25P.of_check cover0 cover1 cover2 cover3 cover4 358256 250598 289438 250598 358256
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
  | 0, 1 => (25193671 : ℝ) / 100000000
  | 0, 2 => (93418335 : ℝ) / 100000000
  | 0, 3 => (54983399 : ℝ) / 100000000
  | 0, 4 => (100000000 : ℝ) / 100000000
  | 0, 5 => (200000000 : ℝ) / 100000000
  | 1, 2 => (49170450 : ℝ) / 100000000
  | 1, 3 => (6581664 : ℝ) / 100000000
  | 1, 4 => (90033200 : ℝ) / 100000000
  | 1, 5 => (100000000 : ℝ) / 100000000
  | 2, 3 => (51271755 : ℝ) / 100000000
  | 2, 4 => (6581664 : ℝ) / 100000000
  | 2, 5 => (54983399 : ℝ) / 100000000
  | 3, 4 => (49170450 : ℝ) / 100000000
  | 3, 5 => (93418335 : ℝ) / 100000000
  | 4, 5 => (25193671 : ℝ) / 100000000
  | _, _ => 0

/-- the per-gap pressures, over `100000000` -/
def bW : Fin 5 → ℝ
  | 0 => (50125 : ℝ) / 100000000
  | 1 => (71659 : ℝ) / 100000000
  | 2 => (62043 : ℝ) / 100000000
  | 3 => (71659 : ℝ) / 100000000
  | 4 => (50125 : ℝ) / 100000000

def WW : WCert 6 := ⟨aW, bW⟩

theorem aW_0_0 : aW 0 0 = 0 := rfl
theorem aW_0_1 : aW 0 1 = (25193671 : ℝ) / 100000000 := rfl
theorem aW_0_2 : aW 0 2 = (93418335 : ℝ) / 100000000 := rfl
theorem aW_0_3 : aW 0 3 = (54983399 : ℝ) / 100000000 := rfl
theorem aW_0_4 : aW 0 4 = (100000000 : ℝ) / 100000000 := rfl
theorem aW_0_5 : aW 0 5 = (200000000 : ℝ) / 100000000 := rfl
theorem aW_1_0 : aW 1 0 = 0 := rfl
theorem aW_1_1 : aW 1 1 = 0 := rfl
theorem aW_1_2 : aW 1 2 = (49170450 : ℝ) / 100000000 := rfl
theorem aW_1_3 : aW 1 3 = (6581664 : ℝ) / 100000000 := rfl
theorem aW_1_4 : aW 1 4 = (90033200 : ℝ) / 100000000 := rfl
theorem aW_1_5 : aW 1 5 = (100000000 : ℝ) / 100000000 := rfl
theorem aW_2_0 : aW 2 0 = 0 := rfl
theorem aW_2_1 : aW 2 1 = 0 := rfl
theorem aW_2_2 : aW 2 2 = 0 := rfl
theorem aW_2_3 : aW 2 3 = (51271755 : ℝ) / 100000000 := rfl
theorem aW_2_4 : aW 2 4 = (6581664 : ℝ) / 100000000 := rfl
theorem aW_2_5 : aW 2 5 = (54983399 : ℝ) / 100000000 := rfl
theorem aW_3_0 : aW 3 0 = 0 := rfl
theorem aW_3_1 : aW 3 1 = 0 := rfl
theorem aW_3_2 : aW 3 2 = 0 := rfl
theorem aW_3_3 : aW 3 3 = 0 := rfl
theorem aW_3_4 : aW 3 4 = (49170450 : ℝ) / 100000000 := rfl
theorem aW_3_5 : aW 3 5 = (93418335 : ℝ) / 100000000 := rfl
theorem aW_4_0 : aW 4 0 = 0 := rfl
theorem aW_4_1 : aW 4 1 = 0 := rfl
theorem aW_4_2 : aW 4 2 = 0 := rfl
theorem aW_4_3 : aW 4 3 = 0 := rfl
theorem aW_4_4 : aW 4 4 = 0 := rfl
theorem aW_4_5 : aW 4 5 = (25193671 : ℝ) / 100000000 := rfl
theorem aW_5_0 : aW 5 0 = 0 := rfl
theorem aW_5_1 : aW 5 1 = 0 := rfl
theorem aW_5_2 : aW 5 2 = 0 := rfl
theorem aW_5_3 : aW 5 3 = 0 := rfl
theorem aW_5_4 : aW 5 4 = 0 := rfl
theorem aW_5_5 : aW 5 5 = 0 := rfl
theorem bW_0 : bW 0 = (50125 : ℝ) / 100000000 := rfl
theorem bW_1 : bW 1 = (71659 : ℝ) / 100000000 := rfl
theorem bW_2 : bW 2 = (62043 : ℝ) / 100000000 := rfl
theorem bW_3 : bW 3 = (71659 : ℝ) / 100000000 := rfl
theorem bW_4 : bW 4 = (50125 : ℝ) / 100000000 := rfl

theorem WW_B : WW.B = (305611 : ℝ) / 100000000 := by
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

theorem WW_bmin : ∀ r, ((50125 : ℝ) / 100000000) ≤ WW.b r := by
  intro r
  unfold WW
  match r with
  | 0 => show ((50125 : ℝ) / 100000000) ≤ bW 0; norm_num [bW_0]
  | 1 => show ((50125 : ℝ) / 100000000) ≤ bW 1; norm_num [bW_1]
  | 2 => show ((50125 : ℝ) / 100000000) ≤ bW 2; norm_num [bW_2]
  | 3 => show ((50125 : ℝ) / 100000000) ≤ bW 3; norm_num [bW_3]
  | 4 => show ((50125 : ℝ) / 100000000) ≤ bW 4; norm_num [bW_4]

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
theorem cert_WW : ∀ g : Fin (6 - 1) → ℝ, (∀ i, 0 ≤ g i) → (548021 : ℝ) / 100000000 ≤ Fw WW g := by
  intro g hg
  rw [Fw_WW]
  have h := cert_full (g 0) (g 1) (g 2) (g 3) (g 4) (hg 0) (hg 1) (hg 2) (hg 3) (hg 4)
  simp only [SixW25P.cN, SixW25P.SA] at h
  push_cast at h
  exact h

/-- `Phi_w' 6 c 187 B` as an exact rational in `HD 1` -/
theorem Phi_WW : Phi_w' 6 ((548021 : ℝ) / 100000000) 187 ((305611 : ℝ) / 100000000)
    = (9350000000 * HD 1 - 27810601) / 9300130089 := by
  unfold Phi_w'
  push_cast
  rw [div_eq_div_iff (by norm_num) (by norm_num)]
  ring

/-- **The 6-point weighted bound, unconditional.** -/
theorem bound_WW :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      ((9350000000 * HD 1 - 27810601) / 9300130089 - ε) * (Zeta23.Ncount T (2 * T) : ℝ) ≤ Zeta23.N0simple T (2 * T) := by
  rw [← Phi_WW, ← WW_B]
  exact n_point_bound_w' 6 ((548021 : ℝ) / 100000000) 187 WW (by norm_num) (by norm_num) WW_adm
    (by norm_num : (0 : ℝ) < (50125 : ℝ) / 100000000) WW_bmin (by norm_num) cert_WW (by norm_num)

/-- The candidate rational sits below the proved constant. -/
theorem candidateKappa_le : candidateKappa ≤ (9350000000 * HD 1 - 27810601) / 9300130089 := by
  unfold candidateKappa
  rw [le_div_iff₀ (by norm_num : (0:ℝ) < 9300130089)]
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
      ≤ ((9350000000 * HD 1 - 27810601) / 9300130089 - ε) * (Zeta23.Ncount T (2 * T) : ℝ) :=
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


