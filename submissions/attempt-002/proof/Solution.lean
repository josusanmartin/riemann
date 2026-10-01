/-
Riemann.fail submission — an unconditional critical-line proportion of 0.6727382,
strictly above the pinned record 2 − 1/cMT = 0.67250070…

The mathematics: Ainta's n-point simple-zero refinement of Theorem D of the pinned
Zeta23 development (the Montgomery–Taylor window at λ = 1), specialised to n = 3 and made
unconditional by a kernel-checked finite certificate (`three_point_cert`: 368 interval cell
lemmas and 487 leaves of a two-dimensional bisection), assembled with the window-count
pressure bookkeeping (`n_point_bound_w'`).  The resulting constant is
`(447000000·H − 297200)/446400399 = 0.67273822…` with `H = HD 1 = 3/2 − (1/√2)cot(1/√2)`,
and `H` is enclosed to `1.1·10⁻⁸` by a twelve-term Taylor argument, which is what places
the exact rational `3363691/5000000` strictly between the record and the proved constant.

Every declaration below is proved from the pinned `anthropics/zeta-23-lean` and Mathlib;
no placeholders, no `native_decide`, no additional axioms.  Sources: the Zeta Lab bridge
(`Zeta23Ext.Bridge`, `Zeta23Ext.BridgeW`, `ThreePoint`), MIT-licensed, ported here into one
file; the counting functions and `cMT` are those of `ChallengeDeps`.
-/
import ChallengeDeps.CandidateSpec
import Zeta23.ZeroSide.RankTraceMult
import Zeta23.ThmD.Mult
import Zeta23.ThmD.ZeroSideD
import Zeta23.PrimeSideA.EndsE1
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Analysis.Real.Pi.Bounds
import Zeta23.Main
import Zeta23.Final
import Zeta23.Statement.SeamClosed
import Zeta23.ThmD.Functional

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

/-! ###### verified certificate checker: rational cells, chains, boxes, cover ###### -/

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

/-! ### Boxes and bisection trees for the four-point functional -/

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

/-- The four-point functional written out on the three gaps. -/
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

/-! ### The four-point certificate from a checked table -/

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

/-- The four-point functional, written out. -/
lemma F4_eq (p : ℕ) (g : Fin 3 → ℝ) :
    F 4 p g = (1 / (p : ℝ)) * (g 0 + g 1 + g 2)
      + 2/3 * wfun (g 0) + 2/3 * wfun (g 1) + 2/3 * wfun (g 2)
      + wfun (g 0 + g 1) + wfun (g 1 + g 2) + 2 * wfun (g 0 + g 1 + g 2) := by
  simp only [F, ptsN, sum3, Fin.sum_univ_four, Fin.isValue]
  norm_num
  try ring

end Zeta23Ext.Bridge.ThreePoint

end

/-! ###### five-point checker: cell search tree, quarter pieces, bit-encoded bisection ###### -/

section Checker5Defs

namespace Zeta23Ext.Bridge.ThreePoint

/-- A binary search tree of cells keyed by `(L, U)`. -/
inductive CT
  | nil
  | node (l : CT) (c : Cell) (r : CT)

namespace CT
def toList : CT → List Cell
  | nil => []
  | node l c r => l.toList ++ c :: r.toList

def allOk : CT → Bool
  | nil => true
  | node l c r => l.allOk && c.ok && r.allOk

def find : CT → ℚ → ℚ → Option Cell
  | nil, _, _ => none
  | node l c r, a, b =>
      if a < c.L then l.find a b
      else if c.L < a then r.find a b
      else if b < c.U then l.find a b
      else if c.U < b then r.find a b
      else some c
end CT

/-- Quarter pieces of `[a, hi]`: cut at the multiples of `1/4` strictly inside. -/
def piecesAux : ℕ → ℚ → ℚ → List (ℚ × ℚ)
  | 0, a, hi => [(a, hi)]
  | fuel + 1, a, hi =>
      let q : ℚ := ((⌊4 * a⌋ : ℤ) + 1) / 4
      if q < hi then (a, q) :: piecesAux fuel q hi else [(a, hi)]

def pieces (lo hi : ℚ) : List (ℚ × ℚ) := piecesAux 64 lo hi

/-- Look every piece up; `none` if any piece is missing from the table. -/
def lookupAll (t : CT) : List (ℚ × ℚ) → Option (List Cell)
  | [] => some []
  | (a, b) :: rest =>
      match t.find a b, lookupAll t rest with
      | some c, some cs => some (c :: cs)
      | _, _ => none

/-- The chain covers `[lo, hi]`: first cell starts at or before `lo`, consecutive cells touch,
last cell reaches `hi`. -/
def chainOKC : ℚ → ℚ → List Cell → Bool
  | lo, hi, [] => decide (hi ≤ lo)
  | lo, hi, c :: rest => decide (c.L ≤ lo) && chainOKC c.U hi rest

def chainWC : List Cell → ℚ
  | [] => 0
  | c :: rest => if rest.isEmpty then c.W else min c.W (chainWC rest)

/-- The bound the table gives for `wfun` on `[lo, hi]` (`0` when the table has no chain). -/
def termW5 (t : CT) (lo hi : ℚ) : ℚ :=
  match lookupAll t (pieces lo hi) with
  | some cs => if chainOKC lo hi cs then chainWC cs else 0
  | none => 0

structure Box5 where
  (xl xu yl yu zl zu ul uu : ℚ)
  deriving DecidableEq

def Box5.widthArg (b : Box5) : ℕ :=
  let w0 := b.xu - b.xl; let w1 := b.yu - b.yl; let w2 := b.zu - b.zl; let w3 := b.uu - b.ul
  if w1 ≤ w0 ∧ w2 ≤ w0 ∧ w3 ≤ w0 then 0
  else if w2 ≤ w1 ∧ w3 ≤ w1 then 1
  else if w3 ≤ w2 then 2 else 3

def Box5.mid (b : Box5) : ℕ → ℚ
  | 0 => (b.xl + b.xu) / 2
  | 1 => (b.yl + b.yu) / 2
  | 2 => (b.zl + b.zu) / 2
  | _ => (b.ul + b.uu) / 2

def Box5.setHi (b : Box5) (ax : ℕ) (q : ℚ) : Box5 :=
  match ax with
  | 0 => { b with xu := q }
  | 1 => { b with yu := q }
  | 2 => { b with zu := q }
  | _ => { b with uu := q }

def Box5.setLo (b : Box5) (ax : ℕ) (q : ℚ) : Box5 :=
  match ax with
  | 0 => { b with xl := q }
  | 1 => { b with yl := q }
  | 2 => { b with zl := q }
  | _ => { b with ul := q }

def leafCheck5 (t : CT) (c p : ℚ) (b : Box5) : Bool :=
  decide (c ≤ (b.xl + b.yl + b.zl + b.ul) / p
    + 1/2 * termW5 t b.xl b.xu + 1/2 * termW5 t b.yl b.yu + 1/2 * termW5 t b.zl b.zu
    + 1/2 * termW5 t b.ul b.uu
    + 2/3 * termW5 t (b.xl + b.yl) (b.xu + b.yu) + 2/3 * termW5 t (b.yl + b.zl) (b.yu + b.zu)
    + 2/3 * termW5 t (b.zl + b.ul) (b.zu + b.uu)
    + termW5 t (b.xl + b.yl + b.zl) (b.xu + b.yu + b.zu)
    + termW5 t (b.yl + b.zl + b.ul) (b.yu + b.zu + b.uu)
    + 2 * termW5 t (b.xl + b.yl + b.zl + b.ul) (b.xu + b.yu + b.zu + b.uu))

/-- Walk the bit-encoded tree (`1` = split at the widest side's midpoint, `0` = leaf) from bit
`pos`; returns the position after the subtree when every leaf checks. -/
def walk5 (t : CT) (c p : ℚ) (bits : ℕ) : ℕ → ℕ → Box5 → Option ℕ
  | 0, _, _ => none
  | fuel + 1, pos, b =>
      if bits.testBit pos then
        let ax := b.widthArg
        let q := b.mid ax
        match walk5 t c p bits fuel (pos + 1) (b.setHi ax q) with
        | none => none
        | some pos' => walk5 t c p bits fuel pos' (b.setLo ax q)
      else if leafCheck5 t c p b then some (pos + 1) else none

def allTuples (nb : ℕ) : List (ℕ × ℕ × ℕ × ℕ) :=
  (List.range nb).flatMap fun i => (List.range nb).flatMap fun j =>
    (List.range nb).flatMap fun k => (List.range nb).map fun l => (i, j, k, l)

def boxOf5 (bad : List (ℚ × ℚ)) (i j k l : ℕ) : Box5 :=
  ⟨(bad.getD i (0, 0)).1, (bad.getD i (0, 0)).2, (bad.getD j (0, 0)).1, (bad.getD j (0, 0)).2,
    (bad.getD k (0, 0)).1, (bad.getD k (0, 0)).2, (bad.getD l (0, 0)).1, (bad.getD l (0, 0)).2⟩

/-- Consume the trees of all tuples in order. -/
def runTuples (t : CT) (c p : ℚ) (bits : ℕ) (fuel : ℕ) (bad : List (ℚ × ℚ)) :
    List (ℕ × ℕ × ℕ × ℕ) → ℕ → Option ℕ
  | [], pos => some pos
  | (i, j, k, l) :: rest, pos =>
      match walk5 t c p bits fuel pos (boxOf5 bad i j k l) with
      | none => none
      | some pos' => runTuples t c p bits fuel bad rest pos'

/-- The one-dimensional cover: segments `(a, b, clear)`; a clear segment's cell is looked up. -/
def coverCheck5 (t : CT) (lvl : ℚ) : ℚ → ℚ → List (ℚ × ℚ × Bool) → Bool
  | pos, S, [] => decide (S ≤ pos)
  | pos, S, (a, b, cl) :: rest =>
      decide (a = pos) && decide (a ≤ b)
        && (!cl || (match t.find a b with | some c => decide (lvl ≤ c.W) | none => false))
        && coverCheck5 t lvl b S rest

def badOf5 (cover : List (ℚ × ℚ × Bool)) : List (ℚ × ℚ) :=
  cover.filterMap fun s => if s.2.2 then none else some (s.1, s.2.1)

end Zeta23Ext.Bridge.ThreePoint

end Checker5Defs

noncomputable section

open Real

namespace Zeta23Ext.Bridge.ThreePoint

/-! ### Soundness: the search tree -/

theorem CT.find_sound : ∀ (t : CT) (a b : ℚ) (c : Cell), t.find a b = some c →
    c ∈ t.toList ∧ c.L = a ∧ c.U = b := by
  intro t
  induction t with
  | nil => intro a b c h; simp [CT.find] at h
  | node l c0 r ihl ihr =>
    intro a b c h
    simp only [CT.find] at h
    split_ifs at h with h1 h2 h3 h4
    · obtain ⟨hm, hL, hU⟩ := ihl a b c h
      exact ⟨by simp [CT.toList, hm], hL, hU⟩
    · obtain ⟨hm, hL, hU⟩ := ihr a b c h
      exact ⟨by simp [CT.toList, hm], hL, hU⟩
    · obtain ⟨hm, hL, hU⟩ := ihl a b c h
      exact ⟨by simp [CT.toList, hm], hL, hU⟩
    · obtain ⟨hm, hL, hU⟩ := ihr a b c h
      exact ⟨by simp [CT.toList, hm], hL, hU⟩
    · simp only [Option.some.injEq] at h
      subst h
      exact ⟨by simp [CT.toList], le_antisymm (not_lt.mp h1) (not_lt.mp h2),
        le_antisymm (not_lt.mp h3) (not_lt.mp h4)⟩

theorem CT.allOk_sound : ∀ (t : CT), t.allOk = true → ∀ c ∈ t.toList, c.ok = true := by
  intro t
  induction t with
  | nil => intro _ c hc; simp [CT.toList] at hc
  | node l c0 r ihl ihr =>
    intro h c hc
    simp only [CT.allOk, Bool.and_eq_true] at h
    simp only [CT.toList, List.mem_append, List.mem_cons] at hc
    rcases hc with hc | hc | hc
    · exact ihl h.1.1 c hc
    · subst hc; exact h.1.2
    · exact ihr h.2 c hc

theorem lookupAll_sound (t : CT) : ∀ (ps : List (ℚ × ℚ)) (cs : List Cell),
    lookupAll t ps = some cs → ∀ c ∈ cs, c ∈ t.toList := by
  intro ps
  induction ps with
  | nil => intro cs h; simp [lookupAll] at h; subst h; simp
  | cons ab rest ih =>
    intro cs h
    obtain ⟨a, b⟩ := ab
    cases hf : t.find a b with
    | none => simp [lookupAll, hf] at h
    | some c =>
      cases hr : lookupAll t rest with
      | none => simp [lookupAll, hf, hr] at h
      | some cs' =>
        simp only [lookupAll, hf, hr, Option.some.injEq] at h
        subst h
        intro d hd
        simp only [List.mem_cons] at hd
        rcases hd with hd | hd
        · subst hd; exact (CT.find_sound t a b d hf).1
        · exact ih cs' hr d hd

/-! ### Soundness: chains of cells -/

theorem chainOKC_sound (t : CT) (hok : t.allOk = true) :
    ∀ (cs : List Cell), (∀ c ∈ cs, c ∈ t.toList) → ∀ (lo hi : ℚ), chainOKC lo hi cs = true →
      ∀ e : ℝ, (lo : ℝ) ≤ e → e ≤ hi → (chainWC cs : ℝ) ≤ wfun e := by
  intro cs
  induction cs with
  | nil =>
    intro _ lo hi _ e _ _
    simp only [chainWC, Rat.cast_zero]; exact wfun_nonneg e
  | cons c rest ih =>
    intro hmem lo hi h e he1 he2
    simp only [chainOKC, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨hL, hrest⟩ := h
    have hcok : c.ok = true := CT.allOk_sound t hok c (hmem c (List.mem_cons_self ..))
    have hL' : (c.L : ℝ) ≤ e := le_trans (by exact_mod_cast hL) he1
    simp only [chainWC]
    split_ifs with hempty
    · have hU : hi ≤ c.U := by
        rw [List.isEmpty_iff.mp hempty] at hrest
        simpa [chainOKC] using hrest
      exact cell_sound c hcok e hL' (he2.trans (by exact_mod_cast hU))
    · rw [Rat.cast_min]
      rcases le_total e (c.U : ℝ) with hU | hU
      · exact (min_le_left _ _).trans (cell_sound c hcok e hL' hU)
      · exact (min_le_right _ _).trans
          (ih (fun d hd => hmem d (List.mem_cons_of_mem _ hd)) _ _ hrest e hU he2)

theorem termW5_sound (t : CT) (hok : t.allOk = true) (lo hi : ℚ) (e : ℝ)
    (he1 : (lo : ℝ) ≤ e) (he2 : e ≤ hi) : (termW5 t lo hi : ℝ) ≤ wfun e := by
  unfold termW5
  split
  · rename_i cs hcs
    split_ifs with hch
    · exact chainOKC_sound t hok cs (lookupAll_sound t _ cs hcs) lo hi hch e he1 he2
    · simp only [Rat.cast_zero]; exact wfun_nonneg e
  · simp only [Rat.cast_zero]; exact wfun_nonneg e

/-! ### Soundness: leaves and the bit-encoded tree -/

/-- The five-point functional written out on the four gaps. -/
def G5 (p : ℚ) (x y z u : ℝ) : ℝ :=
  (1 / (p : ℝ)) * (x + y + z + u)
    + 1/2 * wfun x + 1/2 * wfun y + 1/2 * wfun z + 1/2 * wfun u
    + 2/3 * wfun (x + y) + 2/3 * wfun (y + z) + 2/3 * wfun (z + u)
    + wfun (x + y + z) + wfun (y + z + u)
    + 2 * wfun (x + y + z + u)

def Box5.mem (b : Box5) (x y z u : ℝ) : Prop :=
  (b.xl : ℝ) ≤ x ∧ x ≤ b.xu ∧ (b.yl : ℝ) ≤ y ∧ y ≤ b.yu ∧ (b.zl : ℝ) ≤ z ∧ z ≤ b.zu
    ∧ (b.ul : ℝ) ≤ u ∧ u ≤ b.uu

theorem leaf5_sound (t : CT) (hok : t.allOk = true) (c p : ℚ) (hp : 0 < p) (b : Box5)
    (h : leafCheck5 t c p b = true) (x y z u : ℝ) (hm : b.mem x y z u) :
    (c : ℝ) ≤ G5 p x y z u := by
  obtain ⟨hx1, hx2, hy1, hy2, hz1, hz2, hu1, hu2⟩ := hm
  simp only [leafCheck5, decide_eq_true_eq] at h
  have w0 := termW5_sound t hok _ _ x hx1 hx2
  have w1 := termW5_sound t hok _ _ y hy1 hy2
  have w2 := termW5_sound t hok _ _ z hz1 hz2
  have w3 := termW5_sound t hok _ _ u hu1 hu2
  have w4 := termW5_sound t hok (b.xl + b.yl) (b.xu + b.yu) (x + y) (by push_cast; linarith) (by push_cast; linarith)
  have w5 := termW5_sound t hok (b.yl + b.zl) (b.yu + b.zu) (y + z) (by push_cast; linarith) (by push_cast; linarith)
  have w6 := termW5_sound t hok (b.zl + b.ul) (b.zu + b.uu) (z + u) (by push_cast; linarith) (by push_cast; linarith)
  have w7 := termW5_sound t hok (b.xl + b.yl + b.zl) (b.xu + b.yu + b.zu) (x + y + z) (by push_cast; linarith) (by push_cast; linarith)
  have w8 := termW5_sound t hok (b.yl + b.zl + b.ul) (b.yu + b.zu + b.uu) (y + z + u) (by push_cast; linarith) (by push_cast; linarith)
  have w9 := termW5_sound t hok (b.xl + b.yl + b.zl + b.ul) (b.xu + b.yu + b.zu + b.uu) (x + y + z + u) (by push_cast; linarith) (by push_cast; linarith)
  have hineq' := (Rat.cast_le (K := ℝ)).mpr h
  push_cast at hineq'
  have hp' : (0:ℝ) < p := by exact_mod_cast hp
  have hlin : ((b.xl : ℝ) + b.yl + b.zl + b.ul) / (p : ℝ) ≤ (1 / (p : ℝ)) * (x + y + z + u) := by
    rw [div_eq_mul_one_div, mul_comm]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    linarith
  unfold G5
  linarith

theorem setHi_mem (b : Box5) (ax : ℕ) (q : ℚ) (x y z u : ℝ) (hm : b.mem x y z u)
    (hle : match ax with | 0 => x ≤ q | 1 => y ≤ q | 2 => z ≤ q | _ => u ≤ q) :
    (b.setHi ax q).mem x y z u := by
  obtain ⟨hx1, hx2, hy1, hy2, hz1, hz2, hu1, hu2⟩ := hm
  match ax with
  | 0 => exact ⟨hx1, hle, hy1, hy2, hz1, hz2, hu1, hu2⟩
  | 1 => exact ⟨hx1, hx2, hy1, hle, hz1, hz2, hu1, hu2⟩
  | 2 => exact ⟨hx1, hx2, hy1, hy2, hz1, hle, hu1, hu2⟩
  | n + 3 => exact ⟨hx1, hx2, hy1, hy2, hz1, hz2, hu1, hle⟩

theorem setLo_mem (b : Box5) (ax : ℕ) (q : ℚ) (x y z u : ℝ) (hm : b.mem x y z u)
    (hge : match ax with | 0 => (q : ℝ) ≤ x | 1 => (q : ℝ) ≤ y | 2 => (q : ℝ) ≤ z | _ => (q : ℝ) ≤ u) :
    (b.setLo ax q).mem x y z u := by
  obtain ⟨hx1, hx2, hy1, hy2, hz1, hz2, hu1, hu2⟩ := hm
  match ax with
  | 0 => exact ⟨hge, hx2, hy1, hy2, hz1, hz2, hu1, hu2⟩
  | 1 => exact ⟨hx1, hx2, hge, hy2, hz1, hz2, hu1, hu2⟩
  | 2 => exact ⟨hx1, hx2, hy1, hy2, hge, hz2, hu1, hu2⟩
  | n + 3 => exact ⟨hx1, hx2, hy1, hy2, hz1, hz2, hge, hu2⟩

/-- A split node's walk from the walks of its two children (used to chunk the kernel checks). -/
theorem walk5_split (t : CT) (c p : ℚ) (bits fuel pos : ℕ) (b : Box5) (pos1 pos' : ℕ)
    (hbit : bits.testBit pos = true)
    (h1 : walk5 t c p bits fuel (pos + 1) (b.setHi b.widthArg (b.mid b.widthArg)) = some pos1)
    (h2 : walk5 t c p bits fuel pos1 (b.setLo b.widthArg (b.mid b.widthArg)) = some pos') :
    walk5 t c p bits (fuel + 1) pos b = some pos' := by
  simp only [walk5, hbit, if_true, h1]
  exact h2

theorem walk5_sound (t : CT) (hok : t.allOk = true) (c p : ℚ) (hp : 0 < p) (bits : ℕ) :
    ∀ (fuel pos : ℕ) (b : Box5) (pos' : ℕ), walk5 t c p bits fuel pos b = some pos' →
      ∀ x y z u : ℝ, b.mem x y z u → (c : ℝ) ≤ G5 p x y z u := by
  intro fuel
  induction fuel with
  | zero => intro pos b pos' h; simp [walk5] at h
  | succ fuel ih =>
    intro pos b pos' h x y z u hm
    simp only [walk5] at h
    split_ifs at h with hbit hleaf
    · -- a split
      split at h
      · exact absurd h (by simp)
      · rename_i pos1 h1
        have hlo := ih (pos + 1) (b.setHi b.widthArg (b.mid b.widthArg)) pos1 h1 x y z u
        have hhi := ih pos1 (b.setLo b.widthArg (b.mid b.widthArg)) pos' h x y z u
        -- case on the split axis and side
        set ax := b.widthArg with hax
        set q := b.mid ax with hq
        match ax, hlo, hhi with
        | 0, hlo, hhi =>
          rcases le_total x (q : ℝ) with hs | hs
          · exact hlo (setHi_mem b 0 q x y z u hm hs)
          · exact hhi (setLo_mem b 0 q x y z u hm hs)
        | 1, hlo, hhi =>
          rcases le_total y (q : ℝ) with hs | hs
          · exact hlo (setHi_mem b 1 q x y z u hm hs)
          · exact hhi (setLo_mem b 1 q x y z u hm hs)
        | 2, hlo, hhi =>
          rcases le_total z (q : ℝ) with hs | hs
          · exact hlo (setHi_mem b 2 q x y z u hm hs)
          · exact hhi (setLo_mem b 2 q x y z u hm hs)
        | n + 3, hlo, hhi =>
          rcases le_total u (q : ℝ) with hs | hs
          · exact hlo (setHi_mem b (n + 3) q x y z u hm hs)
          · exact hhi (setLo_mem b (n + 3) q x y z u hm hs)
    · exact leaf5_sound t hok c p hp b hleaf x y z u hm

theorem runTuples_sound (t : CT) (hok : t.allOk = true) (c p : ℚ) (hp : 0 < p) (bits fuel : ℕ)
    (bad : List (ℚ × ℚ)) :
    ∀ (tuples : List (ℕ × ℕ × ℕ × ℕ)) (pos pos' : ℕ),
      runTuples t c p bits fuel bad tuples pos = some pos' →
      ∀ i j k l, (i, j, k, l) ∈ tuples → ∀ x y z u : ℝ, (boxOf5 bad i j k l).mem x y z u →
        (c : ℝ) ≤ G5 p x y z u := by
  intro tuples
  induction tuples with
  | nil => intro _ _ _ i j k l hmem; simp at hmem
  | cons hd rest ih =>
    intro pos pos' h i j k l hmem x y z u hm
    obtain ⟨i0, j0, k0, l0⟩ := hd
    simp only [runTuples] at h
    split at h
    · exact absurd h (by simp)
    · rename_i pos1 hw
      simp only [List.mem_cons, Prod.mk.injEq] at hmem
      rcases hmem with ⟨rfl, rfl, rfl, rfl⟩ | hmem
      · exact walk5_sound t hok c p hp bits fuel pos _ pos1 hw x y z u hm
      · exact ih pos1 pos' h i j k l hmem x y z u hm

/-! ### Soundness: the cover -/

theorem cover5_sound (t : CT) (hok : t.allOk = true) (lvl : ℚ) :
    ∀ (cover : List (ℚ × ℚ × Bool)) (pos S : ℚ), coverCheck5 t lvl pos S cover = true →
      ∀ v : ℝ, (pos : ℝ) ≤ v → v < S →
        (lvl : ℝ) ≤ wfun v ∨ ∃ s ∈ cover, s.2.2 = false ∧ (s.1 : ℝ) ≤ v ∧ v ≤ s.2.1 := by
  intro cover
  induction cover with
  | nil =>
    intro pos S h v hv1 hv2
    simp only [coverCheck5, decide_eq_true_eq] at h
    have : (S : ℝ) ≤ pos := by exact_mod_cast h
    exact absurd (lt_of_le_of_lt (this.trans hv1) hv2) (lt_irrefl _)
  | cons s rest ih =>
    intro pos S h v hv1 hv2
    obtain ⟨a, b, cl⟩ := s
    simp only [coverCheck5, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, Bool.not_eq_eq_eq_not,
      Bool.not_true] at h
    obtain ⟨⟨⟨hpos, hab⟩, hcl⟩, hrest⟩ := h
    rcases le_total v (b : ℝ) with hvb | hvb
    · rcases hcl with hcl | hcl
      · right
        exact ⟨(a, b, cl), List.mem_cons_self .., hcl, by rw [hpos]; exact hv1, hvb⟩
      · left
        split at hcl
        · rename_i c hfind
          obtain ⟨hmem, hL, hU⟩ := CT.find_sound t a b c hfind
          have hcok := CT.allOk_sound t hok c hmem
          have hW := cell_sound c hcok v (by rw [hL, hpos]; exact hv1) (by rw [hU]; exact hvb)
          exact le_trans (by exact_mod_cast (decide_eq_true_eq.mp hcl)) hW
        · exact absurd hcl (by simp)
    · rcases ih b S hrest v hvb hv2 with h | ⟨s', hs', he, h1, h2⟩
      · left; exact h
      · right; exact ⟨s', List.mem_cons_of_mem _ hs', he, h1, h2⟩

theorem badOf5_mem {cover : List (ℚ × ℚ × Bool)} {s : ℚ × ℚ × Bool} (hs : s ∈ cover)
    (he : s.2.2 = false) : (s.1, s.2.1) ∈ badOf5 cover := by
  simp only [badOf5, List.mem_filterMap]
  exact ⟨s, hs, by simp [he]⟩

theorem mem_allTuples {nb i j k l : ℕ} (hi : i < nb) (hj : j < nb) (hk : k < nb) (hl : l < nb) :
    (i, j, k, l) ∈ allTuples nb := by
  simp only [allTuples, List.mem_flatMap, List.mem_map, List.mem_range]
  exact ⟨i, hi, j, hj, k, hk, l, hl, rfl⟩

/-! ### The five-point certificate from a checked table -/

theorem five_point_of_check (t : CT) (cover : List (ℚ × ℚ × Bool)) (bits fuel : ℕ)
    (c p S : ℚ) (hS : S = c * p) (hp : 0 < p)
    (hwin : 2 * c ≤ 19/100) (hok : t.allOk = true)
    (hcov : coverCheck5 t (2 * c) (1/2) S cover = true)
    (hrun : ∀ i j k l, i < (badOf5 cover).length → j < (badOf5 cover).length →
      k < (badOf5 cover).length → l < (badOf5 cover).length →
      ∃ pos pos', walk5 t c p bits fuel pos (boxOf5 (badOf5 cover) i j k l) = some pos') :
    ∀ x y z u : ℝ, 0 ≤ x → 0 ≤ y → 0 ≤ z → 0 ≤ u → (c : ℝ) ≤ G5 p x y z u := by
  intro x y z u hx hy hz hu
  have hw := fun v : ℝ => wfun_nonneg v
  have hp' : (0:ℝ) < p := by exact_mod_cast hp
  have hlin : (0:ℝ) ≤ (1 / (p : ℝ)) * (x + y + z + u) := by positivity
  by_cases hsum : (S : ℝ) ≤ x + y + z + u
  · have hS' : (S : ℝ) = c * p := by exact_mod_cast hS
    have : (c : ℝ) ≤ (1 / (p : ℝ)) * (x + y + z + u) := by
      rw [one_div, inv_mul_eq_div, le_div_iff₀ hp']; linarith
    unfold G5
    linarith [hw x, hw y, hw z, hw u, hw (x + y), hw (y + z), hw (z + u), hw (x + y + z),
      hw (y + z + u), hw (x + y + z + u)]
  push_neg at hsum
  set bad := badOf5 cover with hbad
  have key : ∀ v : ℝ, 0 ≤ v → v < S →
      (c : ℝ) ≤ 1/2 * wfun v ∨ ∃ i, i < bad.length ∧
        ((bad.getD i (0, 0)).1 : ℝ) ≤ v ∧ v ≤ (bad.getD i (0, 0)).2 := by
    intro v hv0 hvS
    rcases le_total v (1/2 : ℝ) with hv | hv
    · left
      have := wfun_window v hv0 hv
      have hwin' := (Rat.cast_le (K := ℝ)).mpr hwin
      push_cast at hwin'
      linarith
    · rcases cover5_sound t hok _ cover (1/2) S hcov v (by push_cast; exact hv) hvS with
        h | ⟨s, hs, he, h1, h2⟩
      · left; push_cast at h; linarith
      · right
        have hmem := badOf5_mem hs he
        obtain ⟨i, hi, hsi⟩ := List.mem_iff_getElem.mp hmem
        refine ⟨i, hi, ?_, ?_⟩
        · rw [List.getD_eq_getElem _ _ hi, hsi]; exact h1
        · rw [List.getD_eq_getElem _ _ hi, hsi]; exact h2
  rcases key x hx (by linarith) with hc | ⟨i, hi, hi1, hi2⟩
  · unfold G5; linarith [hw y, hw z, hw u, hw (x + y), hw (y + z), hw (z + u), hw (x + y + z), hw (y + z + u), hw (x + y + z + u)]
  rcases key y hy (by linarith) with hc | ⟨j, hj, hj1, hj2⟩
  · unfold G5; linarith [hw x, hw z, hw u, hw (x + y), hw (y + z), hw (z + u), hw (x + y + z), hw (y + z + u), hw (x + y + z + u)]
  rcases key z hz (by linarith) with hc | ⟨k, hk, hk1, hk2⟩
  · unfold G5; linarith [hw x, hw y, hw u, hw (x + y), hw (y + z), hw (z + u), hw (x + y + z), hw (y + z + u), hw (x + y + z + u)]
  rcases key u hu (by linarith) with hc | ⟨l, hl, hl1, hl2⟩
  · unfold G5; linarith [hw x, hw y, hw z, hw (x + y), hw (y + z), hw (z + u), hw (x + y + z), hw (y + z + u), hw (x + y + z + u)]
  obtain ⟨pos, pos', hwalk⟩ := hrun i j k l hi hj hk hl
  exact walk5_sound t hok c p hp bits fuel pos _ pos' hwalk x y z u
    ⟨hi1, hi2, hj1, hj2, hk1, hk2, hl1, hl2⟩

private lemma sum4 (f : Fin (5 - 1) → ℝ) : ∑ i, f i = f 0 + f 1 + f 2 + f 3 := by
  show ∑ i : Fin 4, f i = f 0 + f 1 + f 2 + f 3
  exact Fin.sum_univ_four f

/-- The five-point functional, written out. -/
lemma F5_eq (p : ℕ) (g : Fin 4 → ℝ) :
    F 5 p g = (1 / (p : ℝ)) * (g 0 + g 1 + g 2 + g 3)
      + 1/2 * wfun (g 0) + 1/2 * wfun (g 1) + 1/2 * wfun (g 2) + 1/2 * wfun (g 3)
      + 2/3 * wfun (g 0 + g 1) + 2/3 * wfun (g 1 + g 2) + 2/3 * wfun (g 2 + g 3)
      + wfun (g 0 + g 1 + g 2) + wfun (g 1 + g 2 + g 3)
      + 2 * wfun (g 0 + g 1 + g 2 + g 3) := by
  simp only [F, ptsN, sum4, Fin.sum_univ_five, Fin.isValue]
  norm_num
  try ring

end Zeta23Ext.Bridge.ThreePoint

end

/-! ###### four-point checker in the bit-walk format (reuses the cell search tree) ###### -/

section Checker4Defs

namespace Zeta23Ext.Bridge.ThreePoint

def Box.widthArg (b : Box) : ℕ :=
  let w0 := b.xu - b.xl; let w1 := b.yu - b.yl; let w2 := b.zu - b.zl
  if w1 ≤ w0 ∧ w2 ≤ w0 then 0 else if w2 ≤ w1 then 1 else 2

def Box.mid (b : Box) : ℕ → ℚ
  | 0 => (b.xl + b.xu) / 2
  | 1 => (b.yl + b.yu) / 2
  | _ => (b.zl + b.zu) / 2

def Box.setHi (b : Box) (ax : ℕ) (q : ℚ) : Box :=
  match ax with
  | 0 => { b with xu := q }
  | 1 => { b with yu := q }
  | _ => { b with zu := q }

def Box.setLo (b : Box) (ax : ℕ) (q : ℚ) : Box :=
  match ax with
  | 0 => { b with xl := q }
  | 1 => { b with yl := q }
  | _ => { b with zl := q }

def leafCheck4 (t : CT) (c p : ℚ) (b : Box) : Bool :=
  decide (c ≤ (b.xl + b.yl + b.zl) / p
    + 2/3 * termW5 t b.xl b.xu + 2/3 * termW5 t b.yl b.yu + 2/3 * termW5 t b.zl b.zu
    + termW5 t (b.xl + b.yl) (b.xu + b.yu) + termW5 t (b.yl + b.zl) (b.yu + b.zu)
    + 2 * termW5 t (b.xl + b.yl + b.zl) (b.xu + b.yu + b.zu))

def walk4 (t : CT) (c p : ℚ) (bits : ℕ) : ℕ → ℕ → Box → Option ℕ
  | 0, _, _ => none
  | fuel + 1, pos, b =>
      if bits.testBit pos then
        let ax := b.widthArg
        let q := b.mid ax
        match walk4 t c p bits fuel (pos + 1) (b.setHi ax q) with
        | none => none
        | some pos' => walk4 t c p bits fuel pos' (b.setLo ax q)
      else if leafCheck4 t c p b then some (pos + 1) else none

def boxOf4 (bad : List (ℚ × ℚ)) (i j k : ℕ) : Box :=
  ⟨(bad.getD i (0, 0)).1, (bad.getD i (0, 0)).2, (bad.getD j (0, 0)).1, (bad.getD j (0, 0)).2,
    (bad.getD k (0, 0)).1, (bad.getD k (0, 0)).2⟩

end Zeta23Ext.Bridge.ThreePoint

end Checker4Defs

noncomputable section

open Real

namespace Zeta23Ext.Bridge.ThreePoint

def Box.mem (b : Box) (x y z : ℝ) : Prop :=
  (b.xl : ℝ) ≤ x ∧ x ≤ b.xu ∧ (b.yl : ℝ) ≤ y ∧ y ≤ b.yu ∧ (b.zl : ℝ) ≤ z ∧ z ≤ b.zu

theorem leaf4_sound (t : CT) (hok : t.allOk = true) (c p : ℚ) (hp : 0 < p) (b : Box)
    (h : leafCheck4 t c p b = true) (x y z : ℝ) (hm : b.mem x y z) : (c : ℝ) ≤ G4 p x y z := by
  obtain ⟨hx1, hx2, hy1, hy2, hz1, hz2⟩ := hm
  simp only [leafCheck4, decide_eq_true_eq] at h
  have w0 := termW5_sound t hok _ _ x hx1 hx2
  have w1 := termW5_sound t hok _ _ y hy1 hy2
  have w2 := termW5_sound t hok _ _ z hz1 hz2
  have w3 := termW5_sound t hok (b.xl + b.yl) (b.xu + b.yu) (x + y) (by push_cast; linarith) (by push_cast; linarith)
  have w4 := termW5_sound t hok (b.yl + b.zl) (b.yu + b.zu) (y + z) (by push_cast; linarith) (by push_cast; linarith)
  have w5 := termW5_sound t hok (b.xl + b.yl + b.zl) (b.xu + b.yu + b.zu) (x + y + z) (by push_cast; linarith) (by push_cast; linarith)
  have hineq' := (Rat.cast_le (K := ℝ)).mpr h
  push_cast at hineq'
  have hp' : (0:ℝ) < p := by exact_mod_cast hp
  have hlin : ((b.xl : ℝ) + b.yl + b.zl) / (p : ℝ) ≤ (1 / (p : ℝ)) * (x + y + z) := by
    rw [div_eq_mul_one_div, mul_comm]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    linarith
  unfold G4
  linarith

theorem Box.setHi_mem (b : Box) (ax : ℕ) (q : ℚ) (x y z : ℝ) (hm : b.mem x y z)
    (hle : match ax with | 0 => x ≤ q | 1 => y ≤ q | _ => z ≤ q) : (b.setHi ax q).mem x y z := by
  obtain ⟨hx1, hx2, hy1, hy2, hz1, hz2⟩ := hm
  match ax with
  | 0 => exact ⟨hx1, hle, hy1, hy2, hz1, hz2⟩
  | 1 => exact ⟨hx1, hx2, hy1, hle, hz1, hz2⟩
  | n + 2 => exact ⟨hx1, hx2, hy1, hy2, hz1, hle⟩

theorem Box.setLo_mem (b : Box) (ax : ℕ) (q : ℚ) (x y z : ℝ) (hm : b.mem x y z)
    (hge : match ax with | 0 => (q : ℝ) ≤ x | 1 => (q : ℝ) ≤ y | _ => (q : ℝ) ≤ z) :
    (b.setLo ax q).mem x y z := by
  obtain ⟨hx1, hx2, hy1, hy2, hz1, hz2⟩ := hm
  match ax with
  | 0 => exact ⟨hge, hx2, hy1, hy2, hz1, hz2⟩
  | 1 => exact ⟨hx1, hx2, hge, hy2, hz1, hz2⟩
  | n + 2 => exact ⟨hx1, hx2, hy1, hy2, hge, hz2⟩

theorem walk4_split (t : CT) (c p : ℚ) (bits fuel pos : ℕ) (b : Box) (pos1 pos' : ℕ)
    (hbit : bits.testBit pos = true)
    (h1 : walk4 t c p bits fuel (pos + 1) (b.setHi b.widthArg (b.mid b.widthArg)) = some pos1)
    (h2 : walk4 t c p bits fuel pos1 (b.setLo b.widthArg (b.mid b.widthArg)) = some pos') :
    walk4 t c p bits (fuel + 1) pos b = some pos' := by
  simp only [walk4, hbit, if_true, h1]
  exact h2

theorem walk4_sound (t : CT) (hok : t.allOk = true) (c p : ℚ) (hp : 0 < p) (bits : ℕ) :
    ∀ (fuel pos : ℕ) (b : Box) (pos' : ℕ), walk4 t c p bits fuel pos b = some pos' →
      ∀ x y z : ℝ, b.mem x y z → (c : ℝ) ≤ G4 p x y z := by
  intro fuel
  induction fuel with
  | zero => intro pos b pos' h; simp [walk4] at h
  | succ fuel ih =>
    intro pos b pos' h x y z hm
    simp only [walk4] at h
    split_ifs at h with hbit hleaf
    · split at h
      · exact absurd h (by simp)
      · rename_i pos1 h1
        have hlo := ih (pos + 1) (b.setHi b.widthArg (b.mid b.widthArg)) pos1 h1 x y z
        have hhi := ih pos1 (b.setLo b.widthArg (b.mid b.widthArg)) pos' h x y z
        set ax := b.widthArg with hax
        set q := b.mid ax with hq
        match ax, hlo, hhi with
        | 0, hlo, hhi =>
          rcases le_total x (q : ℝ) with hs | hs
          · exact hlo (Box.setHi_mem b 0 q x y z hm hs)
          · exact hhi (Box.setLo_mem b 0 q x y z hm hs)
        | 1, hlo, hhi =>
          rcases le_total y (q : ℝ) with hs | hs
          · exact hlo (Box.setHi_mem b 1 q x y z hm hs)
          · exact hhi (Box.setLo_mem b 1 q x y z hm hs)
        | n + 2, hlo, hhi =>
          rcases le_total z (q : ℝ) with hs | hs
          · exact hlo (Box.setHi_mem b (n + 2) q x y z hm hs)
          · exact hhi (Box.setLo_mem b (n + 2) q x y z hm hs)
    · exact leaf4_sound t hok c p hp b hleaf x y z hm

theorem four_point_of_check' (t : CT) (cover : List (ℚ × ℚ × Bool)) (bits fuel : ℕ)
    (c p S : ℚ) (hS : S = c * p) (hp : 0 < p)
    (hwin : 3/2 * c ≤ 19/100) (hok : t.allOk = true)
    (hcov : coverCheck5 t (3/2 * c) (1/2) S cover = true)
    (hrun : ∀ i j k, i < (badOf5 cover).length → j < (badOf5 cover).length →
      k < (badOf5 cover).length →
      ∃ pos pos', walk4 t c p bits fuel pos (boxOf4 (badOf5 cover) i j k) = some pos') :
    ∀ x y z : ℝ, 0 ≤ x → 0 ≤ y → 0 ≤ z → (c : ℝ) ≤ G4 p x y z := by
  intro x y z hx hy hz
  have hw := fun v : ℝ => wfun_nonneg v
  have hp' : (0:ℝ) < p := by exact_mod_cast hp
  have hlin : (0:ℝ) ≤ (1 / (p : ℝ)) * (x + y + z) := by positivity
  by_cases hsum : (S : ℝ) ≤ x + y + z
  · have hS' : (S : ℝ) = c * p := by exact_mod_cast hS
    have : (c : ℝ) ≤ (1 / (p : ℝ)) * (x + y + z) := by
      rw [one_div, inv_mul_eq_div, le_div_iff₀ hp']; linarith
    unfold G4; linarith [hw x, hw y, hw z, hw (x + y), hw (y + z), hw (x + y + z)]
  push_neg at hsum
  set bad := badOf5 cover with hbad
  have key : ∀ v : ℝ, 0 ≤ v → v < S →
      (c : ℝ) ≤ 2/3 * wfun v ∨ ∃ i, i < bad.length ∧
        ((bad.getD i (0, 0)).1 : ℝ) ≤ v ∧ v ≤ (bad.getD i (0, 0)).2 := by
    intro v hv0 hvS
    rcases le_total v (1/2 : ℝ) with hv | hv
    · left
      have := wfun_window v hv0 hv
      have hwin' := (Rat.cast_le (K := ℝ)).mpr hwin
      push_cast at hwin'
      linarith
    · rcases cover5_sound t hok _ cover (1/2) S hcov v (by push_cast; exact hv) hvS with
        h | ⟨s, hs, he, h1, h2⟩
      · left; push_cast at h; linarith
      · right
        have hmem := badOf5_mem hs he
        obtain ⟨i, hi, hsi⟩ := List.mem_iff_getElem.mp hmem
        refine ⟨i, hi, ?_, ?_⟩
        · rw [List.getD_eq_getElem _ _ hi, hsi]; exact h1
        · rw [List.getD_eq_getElem _ _ hi, hsi]; exact h2
  rcases key x hx (by linarith) with hc | ⟨i, hi, hi1, hi2⟩
  · unfold G4; linarith [hw y, hw z, hw (x + y), hw (y + z), hw (x + y + z)]
  rcases key y hy (by linarith) with hc | ⟨j, hj, hj1, hj2⟩
  · unfold G4; linarith [hw x, hw z, hw (x + y), hw (y + z), hw (x + y + z)]
  rcases key z hz (by linarith) with hc | ⟨k, hk, hk1, hk2⟩
  · unfold G4; linarith [hw x, hw y, hw (x + y), hw (y + z), hw (x + y + z)]
  obtain ⟨pos, pos', hwalk⟩ := hrun i j k hi hj hk
  exact walk4_sound t hok c p hp bits fuel pos _ pos' hwalk x y z ⟨hi1, hi2, hj1, hj2, hk1, hk2⟩

end Zeta23Ext.Bridge.ThreePoint

end

/-! ###### four-point certificate data (bit-walk): c = 2310/10^6, p = 2500 ###### -/

namespace Zeta23Ext.Bridge.ThreePoint.FourDataB

set_option maxRecDepth 100000

def tab0 : CT :=
  (CT.node (CT.node (CT.node (CT.node (CT.node (CT.node CT.nil ⟨(1/2), (3/4), 1, true, (66207635573/2000000000000)⟩ CT.nil) ⟨(3/4), (7/8), 2, false, (242869129569/10000000000000)⟩ (CT.node CT.nil ⟨(7/8), (15/16), 2, false, (15345235463/1250000000000)⟩ CT.nil)) ⟨(15/16), (31/32), 2, false, (8658679537/1250000000000)⟩ (CT.node (CT.node CT.nil ⟨(31/32), (63/64), 2, false, (46969344551/10000000000000)⟩ CT.nil) ⟨(63/64), 1, 2, false, (14204325221/5000000000000)⟩ (CT.node CT.nil ⟨1, (257/256), 2, true, (12267823741/5000000000000)⟩ CT.nil))) ⟨1, (131/128), 2, true, (2370342229/2500000000000)⟩ (CT.node (CT.node (CT.node CT.nil ⟨(257/256), (519/512), 2, true, (4015256583/2500000000000)⟩ CT.nil) ⟨(257/256), (131/128), 2, true, (2370342229/2500000000000)⟩ (CT.node CT.nil ⟨(519/512), (131/128), 2, true, (2370342229/2500000000000)⟩ CT.nil)) ⟨(131/128), (1053/1024), 2, true, (3436255003/5000000000000)⟩ (CT.node (CT.node CT.nil ⟨(131/128), (529/512), 2, true, (1175437333/2500000000000)⟩ CT.nil) ⟨(131/128), (267/256), 2, true, (1626727581/10000000000000)⟩ (CT.node CT.nil ⟨(1053/1024), (529/512), 2, true, (1175437333/2500000000000)⟩ CT.nil)))) ⟨(529/512), (2121/2048), 2, true, (1888462017/5000000000000)⟩ (CT.node (CT.node (CT.node (CT.node CT.nil ⟨(529/512), (1063/1024), 2, true, (2957142633/10000000000000)⟩ CT.nil) ⟨(529/512), (267/256), 2, true, (1626727581/10000000000000)⟩ (CT.node CT.nil ⟨(2121/2048), (1063/1024), 2, true, (2957142633/10000000000000)⟩ CT.nil)) ⟨(1063/1024), (4257/4096), 2, true, (2586175977/10000000000000)⟩ (CT.node (CT.node CT.nil ⟨(1063/1024), (2131/2048), 2, true, (560227329/2500000000000)⟩ CT.nil) ⟨(1063/1024), (267/256), 2, true, (1626727581/10000000000000)⟩ (CT.node CT.nil ⟨(4257/4096), (2131/2048), 2, true, (560227329/2500000000000)⟩ CT.nil))) ⟨(2131/2048), (4267/4096), 2, true, (1921155551/10000000000000)⟩ (CT.node (CT.node (CT.node CT.nil ⟨(2131/2048), (267/256), 2, true, (1626727581/10000000000000)⟩ CT.nil) ⟨(4267/4096), (267/256), 2, true, (1626727581/10000000000000)⟩ (CT.node CT.nil ⟨(267/256), (8549/8192), 2, true, (1488952289/10000000000000)⟩ CT.nil)) ⟨(267/256), (4277/4096), 2, true, (135743827/1000000000000)⟩ (CT.node (CT.node CT.nil ⟨(267/256), (2141/2048), 2, true, (139137559/1250000000000)⟩ CT.nil) ⟨(267/256), (1073/1024), 2, true, (349265369/5000000000000)⟩ (CT.node CT.nil ⟨(267/256), (539/512), 2, true, (160574441/10000000000000)⟩ CT.nil))))) ⟨(8549/8192), (4277/4096), 2, true, (135743827/1000000000000)⟩ (CT.node (CT.node (CT.node (CT.node (CT.node CT.nil ⟨(4277/4096), (8559/8192), 2, true, (1232162133/10000000000000)⟩ CT.nil) ⟨(4277/4096), (2141/2048), 2, true, (139137559/1250000000000)⟩ (CT.node CT.nil ⟨(8559/8192), (2141/2048), 2, true, (139137559/1250000000000)⟩ CT.nil)) ⟨(2141/2048), (8569/8192), 2, true, (1000229897/10000000000000)⟩ (CT.node (CT.node CT.nil ⟨(2141/2048), (4287/4096), 2, true, (446763507/5000000000000)⟩ CT.nil) ⟨(2141/2048), (1073/1024), 2, true, (349265369/5000000000000)⟩ (CT.node CT.nil ⟨(8569/8192), (4287/4096), 2, true, (446763507/5000000000000)⟩ CT.nil))) ⟨(4287/4096), (8579/8192), 2, true, (396484213/5000000000000)⟩ (CT.node (CT.node (CT.node CT.nil ⟨(4287/4096), (1073/1024), 2, true, (349265369/5000000000000)⟩ CT.nil) ⟨(8579/8192), (1073/1024), 2, true, (349265369/5000000000000)⟩ (CT.node CT.nil ⟨(1073/1024), (8589/8192), 2, true, (3813691/62500000000)⟩ CT.nil)) ⟨(1073/1024), (4297/4096), 2, true, (65990561/1250000000000)⟩ (CT.node (CT.node CT.nil ⟨(1073/1024), (2151/2048), 2, true, (76304221/2000000000000)⟩ CT.nil) ⟨(1073/1024), (539/512), 2, true, (160574441/10000000000000)⟩ (CT.node CT.nil ⟨(8589/8192), (4297/4096), 2, true, (65990561/1250000000000)⟩ CT.nil)))) ⟨(4297/4096), (8599/8192), 2, true, (225854567/5000000000000)⟩ (CT.node (CT.node (CT.node (CT.node CT.nil ⟨(4297/4096), (2151/2048), 2, true, (76304221/2000000000000)⟩ CT.nil) ⟨(8599/8192), (2151/2048), 2, true, (76304221/2000000000000)⟩ (CT.node CT.nil ⟨(2151/2048), (4307/4096), 2, true, (259133459/10000000000000)⟩ CT.nil)) ⟨(2151/2048), (539/512), 2, true, (160574441/10000000000000)⟩ (CT.node (CT.node CT.nil ⟨(4307/4096), (539/512), 2, true, (160574441/10000000000000)⟩ CT.nil) ⟨(539/512), (4317/4096), 2, true, (85656967/10000000000000)⟩ (CT.node CT.nil ⟨(539/512), (2161/2048), 2, true, (6838799/2000000000000)⟩ CT.nil))) ⟨(4317/4096), (2161/2048), 2, true, (6838799/2000000000000)⟩ (CT.node (CT.node (CT.node CT.nil ⟨(1083/1024), (2171/2048), 2, true, (875097/10000000000000)⟩ CT.nil) ⟨(1083/1024), (17/16), 2, true, (433353/5000000000000)⟩ (CT.node CT.nil ⟨(2171/2048), (17/16), 2, true, (5858063/1000000000000)⟩ CT.nil)) ⟨(17/16), (1093/1024), 2, true, (40709377/2000000000000)⟩ (CT.node (CT.node CT.nil ⟨(17/16), (549/512), 2, true, (9984781/500000000000)⟩ CT.nil) ⟨(17/16), (277/256), 2, true, (38452957/2000000000000)⟩ (CT.node CT.nil ⟨(17/16), (141/128), 2, true, (44604923/2500000000000)⟩ CT.nil))))))

def tab1 : CT :=
  (CT.node (CT.node (CT.node (CT.node (CT.node (CT.node CT.nil ⟨(1093/1024), (549/512), 2, true, (753911279/10000000000000)⟩ CT.nil) ⟨(549/512), (277/256), 2, true, (1609622259/10000000000000)⟩ (CT.node CT.nil ⟨(277/256), (141/128), 2, true, (4137262453/10000000000000)⟩ CT.nil)) ⟨(141/128), (73/64), 2, true, (11778340313/10000000000000)⟩ (CT.node (CT.node CT.nil ⟨(73/64), (37/32), 2, true, (41297698399/10000000000000)⟩ CT.nil) ⟨(37/32), (19/16), 2, true, (52910124749/10000000000000)⟩ (CT.node CT.nil ⟨(19/16), (5/4), 2, true, (15166428823/2000000000000)⟩ CT.nil))) ⟨(5/4), (3/2), 3, false, (20056696131/2500000000000)⟩ (CT.node (CT.node (CT.node CT.nil ⟨(3/2), (7/4), 3, true, (86044756753/10000000000000)⟩ CT.nil) ⟨(7/4), (15/8), 4, false, (1500513453/400000000000)⟩ (CT.node CT.nil ⟨(15/8), (121/64), 4, false, (18300645841/5000000000000)⟩ CT.nil)) ⟨(121/64), (247/128), 4, false, (9113139537/5000000000000)⟩ (CT.node (CT.node CT.nil ⟨(121/64), (63/32), 4, false, (795663039/1250000000000)⟩ CT.nil) ⟨(247/128), (499/256), 4, false, (6028900351/5000000000000)⟩ (CT.node CT.nil ⟨(247/128), (63/32), 4, false, (6731724963/10000000000000)⟩ CT.nil)))) ⟨(499/256), (1003/512), 4, false, (9381492901/10000000000000)⟩ (CT.node (CT.node (CT.node (CT.node CT.nil ⟨(499/256), (63/32), 4, false, (688065547/1000000000000)⟩ CT.nil) ⟨(1003/512), (2011/1024), 4, false, (8154586159/10000000000000)⟩ (CT.node CT.nil ⟨(1003/512), (63/32), 4, false, (694601603/1000000000000)⟩ CT.nil)) ⟨(2011/1024), (4027/2048), 4, false, (118281741/156250000000)⟩ (CT.node (CT.node CT.nil ⟨(2011/1024), (63/32), 4, false, (697636487/1000000000000)⟩ CT.nil) ⟨(4027/2048), (63/32), 4, false, (6990950273/10000000000000)⟩ (CT.node CT.nil ⟨(63/32), (4037/2048), 4, false, (6435510271/10000000000000)⟩ CT.nil))) ⟨(63/32), (2021/1024), 4, false, (2946158453/5000000000000)⟩ (CT.node (CT.node (CT.node CT.nil ⟨(63/32), (1013/512), 4, false, (4884069333/10000000000000)⟩ CT.nil) ⟨(63/32), (509/256), 4, false, (396477691/1250000000000)⟩ (CT.node CT.nil ⟨(63/32), 2, 4, false, (325933483/2000000000000)⟩ CT.nil)) ⟨(4037/2048), (8079/4096), 4, false, (6172561523/10000000000000)⟩ (CT.node (CT.node CT.nil ⟨(4037/2048), (2021/1024), 4, false, (5903663357/10000000000000)⟩ CT.nil) ⟨(8079/4096), (2021/1024), 4, false, (5909199941/10000000000000)⟩ (CT.node CT.nil ⟨(2021/1024), (8089/4096), 4, false, (2825867677/5000000000000)⟩ CT.nil))))) ⟨(2021/1024), (4047/2048), 4, false, (107907129/200000000000)⟩ (CT.node (CT.node (CT.node (CT.node (CT.node CT.nil ⟨(2021/1024), (1013/512), 4, false, (4902043129/10000000000000)⟩ CT.nil) ⟨(8089/4096), (4047/2048), 4, false, (337510039/625000000000)⟩ (CT.node CT.nil ⟨(4047/2048), (8099/4096), 4, false, (1030893657/2000000000000)⟩ CT.nil)) ⟨(4047/2048), (1013/512), 4, false, (1227632877/2500000000000)⟩ (CT.node (CT.node CT.nil ⟨(8099/4096), (1013/512), 4, false, (2457325291/5000000000000)⟩ CT.nil) ⟨(1013/512), (16213/8192), 4, false, (1199722203/2500000000000)⟩ (CT.node CT.nil ⟨(1013/512), (8109/4096), 4, false, (4680699447/10000000000000)⟩ CT.nil))) ⟨(1013/512), (4057/2048), 4, false, (2224562793/5000000000000)⟩ (CT.node (CT.node (CT.node CT.nil ⟨(1013/512), (2031/1024), 4, false, (200253263/500000000000)⟩ CT.nil) ⟨(1013/512), (509/256), 4, false, (3192232409/10000000000000)⟩ (CT.node CT.nil ⟨(16213/8192), (8109/4096), 4, false, (4682565917/10000000000000)⟩ CT.nil)) ⟨(8109/4096), (16223/8192), 4, false, (4567709043/10000000000000)⟩ (CT.node (CT.node CT.nil ⟨(8109/4096), (4057/2048), 4, false, (4452606511/10000000000000)⟩ CT.nil) ⟨(16223/8192), (4057/2048), 4, false, (44543171/100000000000)⟩ (CT.node CT.nil ⟨(4057/2048), (16233/8192), 4, false, (2171194499/5000000000000)⟩ CT.nil)))) ⟨(4057/2048), (8119/4096), 4, false, (1057590771/2500000000000)⟩ (CT.node (CT.node (CT.node (CT.node CT.nil ⟨(4057/2048), (2031/1024), 4, false, (2005535413/5000000000000)⟩ CT.nil) ⟨(16233/8192), (8119/4096), 4, false, (4231923619/10000000000000)⟩ (CT.node CT.nil ⟨(8119/4096), (16243/8192), 4, false, (4122919829/10000000000000)⟩ CT.nil)) ⟨(8119/4096), (2031/1024), 4, false, (4013960191/10000000000000)⟩ (CT.node (CT.node CT.nil ⟨(16243/8192), (2031/1024), 4, false, (2007688237/5000000000000)⟩ CT.nil) ⟨(2031/1024), (16253/8192), 4, false, (1954646193/5000000000000)⟩ (CT.node CT.nil ⟨(2031/1024), (8129/4096), 4, false, (3803388551/10000000000000)⟩ CT.nil))) ⟨(2031/1024), (4067/2048), 4, false, (71925891/200000000000)⟩ (CT.node (CT.node (CT.node CT.nil ⟨(2031/1024), (509/256), 4, false, (400103387/1250000000000)⟩ CT.nil) ⟨(16253/8192), (8129/4096), 4, false, (1902333181/5000000000000)⟩ (CT.node CT.nil ⟨(8129/4096), (4067/2048), 4, false, (359863857/1000000000000)⟩ CT.nil)) ⟨(4067/2048), (8139/4096), 4, false, (339970037/1000000000000)⟩ (CT.node (CT.node CT.nil ⟨(4067/2048), (509/256), 4, false, (3204719257/10000000000000)⟩ CT.nil) ⟨(8139/4096), (509/256), 4, false, (3206563771/10000000000000)⟩ CT.nil)))))

def tab2 : CT :=
  (CT.node (CT.node (CT.node (CT.node (CT.node (CT.node CT.nil ⟨(509/256), (4077/2048), 4, false, (2836262683/10000000000000)⟩ CT.nil) ⟨(509/256), (2041/1024), 4, false, (248869577/1000000000000)⟩ (CT.node CT.nil ⟨(509/256), (1023/512), 4, false, (1865845891/10000000000000)⟩ CT.nil)) ⟨(509/256), 2, 4, false, (410811713/2500000000000)⟩ (CT.node (CT.node CT.nil ⟨(8149/4096), (4077/2048), 4, false, (354706643/1250000000000)⟩ CT.nil) ⟨(4077/2048), (8159/4096), 4, false, (2661857281/10000000000000)⟩ (CT.node CT.nil ⟨(4077/2048), (2041/1024), 4, false, (1245418929/5000000000000)⟩ CT.nil))) ⟨(8159/4096), (2041/1024), 4, false, (1245909663/5000000000000)⟩ (CT.node (CT.node (CT.node CT.nil ⟨(2041/1024), (4087/2048), 4, false, (1084176557/5000000000000)⟩ CT.nil) ⟨(2041/1024), (1023/512), 4, false, (1867963109/10000000000000)⟩ (CT.node CT.nil ⟨(4087/2048), (1023/512), 4, false, (1868712167/10000000000000)⟩ CT.nil)) ⟨(1023/512), 2, 4, false, (822707073/5000000000000)⟩ (CT.node (CT.node CT.nil ⟨2, (4097/2048), 4, true, (1591808227/10000000000000)⟩ CT.nil) ⟨2, (2051/1024), 4, true, (1337086167/10000000000000)⟩ (CT.node CT.nil ⟨2, (257/128), 4, true, (179073511/2000000000000)⟩ CT.nil)))) ⟨(4097/2048), (2051/1024), 4, true, (1337086167/10000000000000)⟩ (CT.node (CT.node (CT.node (CT.node CT.nil ⟨(2051/1024), (4107/2048), 4, true, (1104977691/10000000000000)⟩ CT.nil) ⟨(2051/1024), (257/128), 4, true, (179073511/2000000000000)⟩ (CT.node CT.nil ⟨(4107/2048), (257/128), 4, true, (179073511/2000000000000)⟩ CT.nil)) ⟨(257/128), (4117/2048), 4, true, (708136113/10000000000000)⟩ (CT.node (CT.node CT.nil ⟨(257/128), (2061/1024), 4, true, (543159341/10000000000000)⟩ CT.nil) ⟨(257/128), (1033/512), 4, true, (27945219/1000000000000)⟩ (CT.node CT.nil ⟨(257/128), (519/256), 4, true, (13164037/10000000000000)⟩ CT.nil))) ⟨(4117/2048), (2061/1024), 4, true, (543159341/10000000000000)⟩ (CT.node (CT.node (CT.node CT.nil ⟨(2061/1024), (4127/2048), 4, true, (400308901/10000000000000)⟩ CT.nil) ⟨(2061/1024), (1033/512), 4, true, (27945219/1000000000000)⟩ (CT.node CT.nil ⟨(4127/2048), (1033/512), 4, true, (27945219/1000000000000)⟩ CT.nil)) ⟨(1033/512), (2071/1024), 4, true, (103168503/10000000000000)⟩ (CT.node (CT.node CT.nil ⟨(1033/512), (519/256), 4, true, (13164037/10000000000000)⟩ CT.nil) ⟨(2071/1024), (519/256), 4, true, (13164037/10000000000000)⟩ (CT.node CT.nil ⟨(2081/1024), (1043/512), 4, true, (8149981/10000000000000)⟩ CT.nil))))) ⟨(1043/512), (131/64), 4, true, (21355581/2500000000000)⟩ (CT.node (CT.node (CT.node (CT.node (CT.node CT.nil ⟨(1043/512), (1053/512), 4, true, (83791953/10000000000000)⟩ CT.nil) ⟨(1043/512), (529/256), 4, true, (1284381/156250000000)⟩ (CT.node CT.nil ⟨(131/64), (529/256), 4, true, (94460693/2000000000000)⟩ CT.nil)) ⟨(131/64), (1063/512), 4, true, (115843823/2500000000000)⟩ (CT.node (CT.node CT.nil ⟨(131/64), (267/128), 4, true, (18186303/400000000000)⟩ CT.nil) ⟨(131/64), (539/256), 4, true, (437829947/10000000000000)⟩ (CT.node CT.nil ⟨(131/64), (17/8), 4, true, (42177537/1000000000000)⟩ CT.nil))) ⟨(131/64), (277/128), 4, true, (12244337/312500000000)⟩ (CT.node (CT.node (CT.node CT.nil ⟨(131/64), (141/64), 4, true, (182240171/5000000000000)⟩ CT.nil) ⟨(131/64), (9/4), 4, true, (167375901/5000000000000)⟩ (CT.node CT.nil ⟨(1053/512), (1063/512), 4, true, (291856019/2500000000000)⟩ CT.nil)) ⟨(1053/512), (267/128), 4, true, (1145460727/10000000000000)⟩ (CT.node (CT.node CT.nil ⟨(529/256), (2131/1024), 4, true, (54451693/250000000000)⟩ CT.nil) ⟨(529/256), (267/128), 4, true, (269688311/1250000000000)⟩ (CT.node CT.nil ⟨(529/256), (1073/512), 4, true, (264638553/1250000000000)⟩ CT.nil)))) ⟨(529/256), (539/256), 4, true, (259706701/1250000000000)⟩ (CT.node (CT.node (CT.node (CT.node CT.nil ⟨(529/256), (17/8), 4, true, (2001469121/10000000000000)⟩ CT.nil) ⟨(2121/1024), (267/128), 4, true, (1392763463/5000000000000)⟩ (CT.node CT.nil ⟨(1063/512), (1073/512), 4, true, (343008739/1000000000000)⟩ CT.nil)) ⟨(1063/512), (539/256), 4, true, (3366163659/10000000000000)⟩ (CT.node (CT.node CT.nil ⟨(267/128), (17/8), 4, true, (4789633321/10000000000000)⟩ CT.nil) ⟨(267/128), (549/256), 4, true, (4615617497/10000000000000)⟩ (CT.node CT.nil ⟨(267/128), (277/128), 4, true, (1112362433/2500000000000)⟩ CT.nil))) ⟨(267/128), (141/64), 4, true, (129343671/312500000000)⟩ (CT.node (CT.node (CT.node CT.nil ⟨(539/256), (549/256), 4, true, (4243616393/5000000000000)⟩ CT.nil) ⟨(539/256), (277/128), 4, true, (2045420557/2500000000000)⟩ (CT.node CT.nil ⟨(17/8), (141/64), 4, true, (48584483/40000000000)⟩ CT.nil)) ⟨(17/8), (9/4), 4, true, (2788858101/2500000000000)⟩ (CT.node (CT.node CT.nil ⟨(141/64), (71/32), 4, true, (39186989529/10000000000000)⟩ CT.nil) ⟨(71/32), (9/4), 4, true, (21886858333/5000000000000)⟩ (CT.node CT.nil ⟨(9/4), (73/32), 5, false, (27652304943/5000000000000)⟩ CT.nil))))))

def tab3 : CT :=
  (CT.node (CT.node (CT.node (CT.node (CT.node (CT.node CT.nil ⟨(5/2), (11/4), 5, true, (38423148027/10000000000000)⟩ CT.nil) ⟨(11/4), (89/32), 6, false, (41549598057/10000000000000)⟩ (CT.node CT.nil ⟨(89/32), (179/64), 6, false, (37442452611/10000000000000)⟩ CT.nil)) ⟨(179/64), (747/256), 6, false, (1457053011/2000000000000)⟩ (CT.node (CT.node CT.nil ⟨(23/8), (383/128), 6, false, (269743281/5000000000000)⟩ CT.nil) ⟨(373/128), (383/128), 6, false, (288828359/5000000000000)⟩ (CT.node CT.nil ⟨(747/256), (6007/2048), 6, false, (2995265257/5000000000000)⟩ CT.nil))) ⟨(747/256), (3019/1024), 6, false, (100676353/250000000000)⟩ (CT.node (CT.node (CT.node CT.nil ⟨(747/256), (1525/512), 6, false, (261299809/2000000000000)⟩ CT.nil) ⟨(6007/2048), (3019/1024), 6, false, (816631931/2000000000000)⟩ (CT.node CT.nil ⟨(3019/1024), (12107/4096), 6, false, (3285883949/10000000000000)⟩ CT.nil)) ⟨(3019/1024), (6069/2048), 6, false, (2539642107/10000000000000)⟩ (CT.node (CT.node CT.nil ⟨(3019/1024), (1525/512), 6, false, (67339097/500000000000)⟩ CT.nil) ⟨(189/64), (383/128), 6, false, (15105971/250000000000)⟩ (CT.node CT.nil ⟨(189/64), 3, 6, false, (156774751/5000000000000)⟩ CT.nil)))) ⟨(12107/4096), (24245/8192), 6, false, (2917054281/10000000000000)⟩ (CT.node (CT.node (CT.node (CT.node CT.nil ⟨(12107/4096), (6069/2048), 6, false, (319327517/1250000000000)⟩ CT.nil) ⟨(24245/8192), (6069/2048), 6, false, (2561735901/10000000000000)⟩ (CT.node CT.nil ⟨(6069/2048), (24307/8192), 6, false, (2229636307/10000000000000)⟩ CT.nil)) ⟨(6069/2048), (12169/4096), 6, false, (239478321/1250000000000)⟩ (CT.node (CT.node CT.nil ⟨(6069/2048), (1525/512), 6, false, (1362675081/10000000000000)⟩ CT.nil) ⟨(24307/8192), (12169/4096), 6, false, (240095521/1250000000000)⟩ (CT.node CT.nil ⟨(12169/4096), (24369/8192), 6, false, (1635115293/10000000000000)⟩ CT.nil))) ⟨(12169/4096), (1525/512), 6, false, (136952521/1000000000000)⟩ (CT.node (CT.node (CT.node CT.nil ⟨(761/256), 3, 6, false, (318089829/10000000000000)⟩ CT.nil) ⟨(24369/8192), (1525/512), 6, false, (686336349/5000000000000)⟩ (CT.node CT.nil ⟨(1525/512), (12231/4096), 6, false, (183106839/2000000000000)⟩ CT.nil)) ⟨(1525/512), (6131/2048), 6, false, (137922559/2500000000000)⟩ (CT.node (CT.node CT.nil ⟨(1525/512), 3, 6, false, (318991089/10000000000000)⟩ CT.nil) ⟨(1527/512), 3, 6, false, (319472457/10000000000000)⟩ (CT.node CT.nil ⟨(12231/4096), (6131/2048), 6, false, (5534703/100000000000)⟩ CT.nil))))) ⟨(383/128), 3, 6, false, (10007991/312500000000)⟩ (CT.node (CT.node (CT.node (CT.node (CT.node CT.nil ⟨(6131/2048), 3, 6, false, (80080323/2500000000000)⟩ CT.nil) ⟨(3069/1024), 3, 6, false, (80105391/2500000000000)⟩ (CT.node CT.nil ⟨3, (1537/512), 6, true, (13065663/500000000000)⟩ CT.nil)) ⟨3, (3079/1024), 6, true, (70009749/5000000000000)⟩ (CT.node (CT.node CT.nil ⟨3, (3081/1024), 6, true, (102076243/10000000000000)⟩ CT.nil) ⟨3, (771/256), 6, true, (28217469/5000000000000)⟩ (CT.node CT.nil ⟨(1537/512), (6163/2048), 6, true, (93531111/10000000000000)⟩ CT.nil))) ⟨(1537/512), (771/256), 6, true, (28217469/5000000000000)⟩ (CT.node (CT.node (CT.node CT.nil ⟨(1537/512), (3089/1024), 6, true, (128333/125000000000)⟩ CT.nil) ⟨(6153/2048), (771/256), 6, true, (28217469/5000000000000)⟩ (CT.node CT.nil ⟨(3079/1024), (771/256), 6, true, (28217469/5000000000000)⟩ CT.nil)) ⟨(3079/1024), (6173/2048), 6, true, (3586667/1250000000000)⟩ (CT.node (CT.node CT.nil ⟨(3079/1024), (3089/1024), 6, true, (128333/125000000000)⟩ CT.nil) ⟨(6163/2048), (6173/2048), 6, true, (3586667/1250000000000)⟩ (CT.node CT.nil ⟨(6163/2048), (3089/1024), 6, true, (128333/125000000000)⟩ CT.nil)))) ⟨(771/256), (3089/1024), 6, true, (128333/125000000000)⟩ (CT.node (CT.node (CT.node (CT.node CT.nil ⟨(771/256), (6183/2048), 6, true, (278293/2500000000000)⟩ CT.nil) ⟨(6173/2048), (12361/4096), 6, true, (906687/2000000000000)⟩ (CT.node CT.nil ⟨(6173/2048), (6183/2048), 6, true, (278293/2500000000000)⟩ CT.nil)) ⟨(12351/4096), (6183/2048), 6, true, (278293/2500000000000)⟩ (CT.node (CT.node CT.nil ⟨(3089/1024), (6183/2048), 6, true, (278293/2500000000000)⟩ CT.nil) ⟨(12371/4096), (12381/4096), 6, true, (329/10000000000000)⟩ (CT.node CT.nil ⟨(12371/4096), (6193/2048), 6, true, (41/1250000000000)⟩ CT.nil))) ⟨(1547/512), (24767/8192), 6, true, (593183/5000000000000)⟩ (CT.node (CT.node (CT.node CT.nil ⟨(1547/512), (6193/2048), 6, true, (1185403/10000000000000)⟩ CT.nil) ⟨(1547/512), (12391/4096), 6, true, (29587/250000000000)⟩ (CT.node CT.nil ⟨(1547/512), (3099/1024), 6, true, (1181561/10000000000000)⟩ CT.nil)) ⟨(1547/512), (6203/2048), 6, true, (235547/2000000000000)⟩ (CT.node (CT.node CT.nil ⟨(1547/512), (97/32), 6, true, (293481/2500000000000)⟩ CT.nil) ⟨(1547/512), (3109/1024), 6, true, (1166349/10000000000000)⟩ CT.nil)))))

def tab4 : CT :=
  (CT.node (CT.node (CT.node (CT.node (CT.node (CT.node CT.nil ⟨(1547/512), (781/256), 6, true, (285997/2500000000000)⟩ CT.nil) ⟨(24757/8192), (6193/2048), 6, true, (2638657/10000000000000)⟩ (CT.node CT.nil ⟨(12381/4096), (24777/8192), 6, true, (4662827/10000000000000)⟩ CT.nil)) ⟨(12381/4096), (12391/4096), 6, true, (931809/2000000000000)⟩ (CT.node (CT.node CT.nil ⟨(12381/4096), (3099/1024), 6, true, (465149/1000000000000)⟩ CT.nil) ⟨(24767/8192), (12391/4096), 6, true, (7258139/10000000000000)⟩ (CT.node CT.nil ⟨(6193/2048), (24787/8192), 6, true, (5211923/5000000000000)⟩ CT.nil))) ⟨(6193/2048), (3099/1024), 6, true, (10415393/10000000000000)⟩ (CT.node (CT.node (CT.node CT.nil ⟨(6193/2048), (12401/4096), 6, true, (649907/625000000000)⟩ CT.nil) ⟨(6193/2048), (6203/2048), 6, true, (2076333/2000000000000)⟩ (CT.node CT.nil ⟨(6193/2048), (97/32), 6, true, (5174037/5000000000000)⟩ CT.nil)) ⟨(24777/8192), (24787/8192), 6, true, (221417/156250000000)⟩ (CT.node (CT.node CT.nil ⟨(24777/8192), (3099/1024), 6, true, (3539799/2500000000000)⟩ CT.nil) ⟨(12391/4096), (3099/1024), 6, true, (4619603/2500000000000)⟩ (CT.node CT.nil ⟨(12391/4096), (24797/8192), 6, true, (1846343/1000000000000)⟩ CT.nil)))) ⟨(12391/4096), (12401/4096), 6, true, (18448463/10000000000000)⟩ (CT.node (CT.node (CT.node (CT.node CT.nil ⟨(12391/4096), (6203/2048), 6, true, (736743/400000000000)⟩ CT.nil) ⟨(24787/8192), (24797/8192), 6, true, (23354711/10000000000000)⟩ (CT.node CT.nil ⟨(24787/8192), (12401/4096), 6, true, (23335779/10000000000000)⟩ CT.nil)) ⟨(3099/1024), (12401/4096), 6, true, (28798809/10000000000000)⟩ (CT.node (CT.node CT.nil ⟨(3099/1024), (24807/8192), 6, true, (28775469/10000000000000)⟩ CT.nil) ⟨(3099/1024), (6203/2048), 6, true, (3594019/1250000000000)⟩ (CT.node CT.nil ⟨(3099/1024), (12411/4096), 6, true, (2870559/1000000000000)⟩ CT.nil))) ⟨(3099/1024), (97/32), 6, true, (14329561/5000000000000)⟩ (CT.node (CT.node (CT.node CT.nil ⟨(3099/1024), (6213/2048), 6, true, (7141617/2500000000000)⟩ CT.nil) ⟨(3099/1024), (3109/1024), 6, true, (28474189/10000000000000)⟩ (CT.node CT.nil ⟨(3099/1024), (1557/512), 6, true, (28290747/10000000000000)⟩ CT.nil)) ⟨(24797/8192), (24807/8192), 6, true, (17404961/5000000000000)⟩ (CT.node (CT.node CT.nil ⟨(24797/8192), (6203/2048), 6, true, (6956343/2000000000000)⟩ CT.nil) ⟨(12401/4096), (6203/2048), 6, true, (20693629/5000000000000)⟩ (CT.node CT.nil ⟨(12401/4096), (24817/8192), 6, true, (4135373/1000000000000)⟩ CT.nil))))) ⟨(12401/4096), (12411/4096), 6, true, (8264047/2000000000000)⟩ (CT.node (CT.node (CT.node (CT.node (CT.node CT.nil ⟨(12401/4096), (97/32), 6, true, (20626673/5000000000000)⟩ CT.nil) ⟨(24807/8192), (24817/8192), 6, true, (2426501/500000000000)⟩ (CT.node CT.nil ⟨(24807/8192), (12411/4096), 6, true, (48490713/10000000000000)⟩ CT.nil)) ⟨(6203/2048), (12411/4096), 6, true, (56237401/10000000000000)⟩ (CT.node (CT.node CT.nil ⟨(6203/2048), (24827/8192), 6, true, (2809593/500000000000)⟩ CT.nil) ⟨(6203/2048), (97/32), 6, true, (11229273/2000000000000)⟩ (CT.node CT.nil ⟨(6203/2048), (12421/4096), 6, true, (28027757/5000000000000)⟩ CT.nil))) ⟨(6203/2048), (6213/2048), 6, true, (55964847/10000000000000)⟩ (CT.node (CT.node (CT.node CT.nil ⟨(6203/2048), (3109/1024), 6, true, (27892031/5000000000000)⟩ CT.nil) ⟨(24817/8192), (24827/8192), 6, true, (64508587/10000000000000)⟩ (CT.node CT.nil ⟨(24817/8192), (97/32), 6, true, (64456359/10000000000000)⟩ CT.nil)) ⟨(12411/4096), (97/32), 6, true, (36671379/5000000000000)⟩ (CT.node (CT.node CT.nil ⟨(12411/4096), (24837/8192), 6, true, (73283389/10000000000000)⟩ CT.nil) ⟨(12411/4096), (12421/4096), 6, true, (73224081/10000000000000)⟩ (CT.node CT.nil ⟨(12411/4096), (6213/2048), 6, true, (18276411/2500000000000)⟩ CT.nil)))) ⟨(24827/8192), (24837/8192), 6, true, (20684771/2500000000000)⟩ (CT.node (CT.node (CT.node (CT.node CT.nil ⟨(24827/8192), (12421/4096), 6, true, (82672123/10000000000000)⟩ CT.nil) ⟨(97/32), (12421/4096), 6, true, (92696731/10000000000000)⟩ (CT.node CT.nil ⟨(97/32), (24847/8192), 6, true, (46310863/5000000000000)⟩ CT.nil)) ⟨(97/32), (6213/2048), 6, true, (46273399/5000000000000)⟩ (CT.node (CT.node CT.nil ⟨(97/32), (12431/4096), 6, true, (5774823/625000000000)⟩ CT.nil) ⟨(97/32), (3109/1024), 6, true, (92247841/10000000000000)⟩ (CT.node CT.nil ⟨(97/32), (6223/2048), 6, true, (22987523/2500000000000)⟩ CT.nil))) ⟨(97/32), (1557/512), 6, true, (11456693/1250000000000)⟩ (CT.node (CT.node (CT.node CT.nil ⟨(97/32), (3119/1024), 6, true, (91064031/10000000000000)⟩ CT.nil) ⟨(97/32), (781/256), 6, true, (18095851/2000000000000)⟩ (CT.node CT.nil ⟨(97/32), (1567/512), 6, true, (22330933/2500000000000)⟩ CT.nil)) ⟨(97/32), (393/128), 6, true, (88186617/10000000000000)⟩ (CT.node (CT.node CT.nil ⟨(97/32), (791/256), 6, true, (21491553/2500000000000)⟩ CT.nil) ⟨(97/32), (199/64), 6, true, (20953831/2500000000000)⟩ (CT.node CT.nil ⟨(97/32), (801/256), 6, true, (40865677/5000000000000)⟩ CT.nil))))))

def tab5 : CT :=
  (CT.node (CT.node (CT.node (CT.node (CT.node (CT.node CT.nil ⟨(97/32), (51/16), 6, true, (75856633/10000000000000)⟩ CT.nil) ⟨(97/32), (13/4), 6, true, (17540223/2500000000000)⟩ (CT.node CT.nil ⟨(24837/8192), (6213/2048), 6, true, (25782839/2500000000000)⟩ CT.nil)) ⟨(12421/4096), (24857/8192), 6, true, (114200161/10000000000000)⟩ (CT.node (CT.node CT.nil ⟨(12421/4096), (12431/4096), 6, true, (57053907/5000000000000)⟩ CT.nil) ⟨(12421/4096), (3109/1024), 6, true, (569617/50000000000)⟩ (CT.node CT.nil ⟨(24847/8192), (12431/4096), 6, true, (15728411/1250000000000)⟩ CT.nil))) ⟨(6213/2048), (3109/1024), 6, true, (17237539/1250000000000)⟩ (CT.node (CT.node (CT.node CT.nil ⟨(6213/2048), (12441/4096), 6, true, (4302423/312500000000)⟩ CT.nil) ⟨(6213/2048), (6223/2048), 6, true, (13745521/1000000000000)⟩ (CT.node CT.nil ⟨(6213/2048), (1557/512), 6, true, (2140811/156250000000)⟩ CT.nil)) ⟨(12431/4096), (12441/4096), 6, true, (32783471/2000000000000)⟩ (CT.node (CT.node CT.nil ⟨(12431/4096), (6223/2048), 6, true, (163652657/10000000000000)⟩ CT.nil) ⟨(3109/1024), (6223/2048), 6, true, (192151891/10000000000000)⟩ (CT.node CT.nil ⟨(3109/1024), (12451/4096), 6, true, (47960431/2500000000000)⟩ CT.nil)))) ⟨(3109/1024), (1557/512), 6, true, (23941523/1250000000000)⟩ (CT.node (CT.node (CT.node (CT.node CT.nil ⟨(3109/1024), (6233/2048), 6, true, (7636599/400000000000)⟩ CT.nil) ⟨(3109/1024), (3119/1024), 6, true, (190300253/10000000000000)⟩ (CT.node CT.nil ⟨(3109/1024), (781/256), 6, true, (189078223/10000000000000)⟩ CT.nil)) ⟨(12441/4096), (12451/4096), 6, true, (890387/40000000000)⟩ (CT.node (CT.node CT.nil ⟨(12441/4096), (1557/512), 6, true, (111118793/5000000000000)⟩ CT.nil) ⟨(6223/2048), (1557/512), 6, true, (255244651/10000000000000)⟩ (CT.node CT.nil ⟨(6223/2048), (12461/4096), 6, true, (10193319/400000000000)⟩ CT.nil))) ⟨(6223/2048), (6233/2048), 6, true, (25442213/1000000000000)⟩ (CT.node (CT.node (CT.node CT.nil ⟨(6223/2048), (3119/1024), 6, true, (63400731/2500000000000)⟩ CT.nil) ⟨(389/128), (1587/512), 6, true, (249212333/10000000000000)⟩ (CT.node CT.nil ⟨(389/128), (809/256), 6, true, (115281189/5000000000000)⟩ CT.nil)) ⟨(12451/4096), (12461/4096), 6, true, (290088193/10000000000000)⟩ (CT.node (CT.node CT.nil ⟨(12451/4096), (6233/2048), 6, true, (289620509/10000000000000)⟩ CT.nil) ⟨(1557/512), (3119/1024), 6, true, (326066581/10000000000000)⟩ (CT.node CT.nil ⟨(1557/512), (6243/2048), 6, true, (325017537/10000000000000)⟩ CT.nil))))) ⟨(1557/512), (781/256), 6, true, (161986357/5000000000000)⟩ (CT.node (CT.node (CT.node (CT.node (CT.node CT.nil ⟨(1557/512), (3129/1024), 6, true, (160947823/5000000000000)⟩ CT.nil) ⟨(1557/512), (1567/512), 6, true, (63967043/2000000000000)⟩ (CT.node CT.nil ⟨(1557/512), (393/128), 6, true, (157881813/5000000000000)⟩ CT.nil)) ⟨(6233/2048), (6243/2048), 6, true, (406405247/10000000000000)⟩ (CT.node (CT.node CT.nil ⟨(6233/2048), (781/256), 6, true, (405098789/10000000000000)⟩ CT.nil) ⟨(3119/1024), (781/256), 6, true, (495376037/10000000000000)⟩ (CT.node CT.nil ⟨(3119/1024), (6253/2048), 6, true, (493784853/10000000000000)⟩ CT.nil))) ⟨(3119/1024), (3129/1024), 6, true, (24610003/500000000000)⟩ (CT.node (CT.node (CT.node CT.nil ⟨(3119/1024), (1567/512), 6, true, (489049523/10000000000000)⟩ CT.nil) ⟨(6243/2048), (6253/2048), 6, true, (148228771/2500000000000)⟩ (CT.node CT.nil ⟨(6243/2048), (3129/1024), 6, true, (295506067/5000000000000)⟩ CT.nil)) ⟨(781/256), (1567/512), 6, true, (694482783/10000000000000)⟩ (CT.node (CT.node CT.nil ⟨(781/256), (3139/1024), 6, true, (172511147/2500000000000)⟩ CT.nil) ⟨(781/256), (393/128), 6, true, (685641829/10000000000000)⟩ (CT.node CT.nil ⟨(781/256), (1577/512), 6, true, (676941261/10000000000000)⟩ CT.nil)))) ⟨(781/256), (791/256), 6, true, (66837841/1000000000000)⟩ (CT.node (CT.node (CT.node (CT.node CT.nil ⟨(781/256), (1587/512), 6, true, (329975333/5000000000000)⟩ CT.nil) ⟨(781/256), (199/64), 6, true, (162913869/2500000000000)⟩ (CT.node CT.nil ⟨(781/256), (801/256), 6, true, (635452827/10000000000000)⟩ CT.nil)) ⟨(3129/1024), (3139/1024), 6, true, (930293373/10000000000000)⟩ (CT.node (CT.node CT.nil ⟨(3129/1024), (393/128), 6, true, (924357731/10000000000000)⟩ CT.nil) ⟨(1567/512), (393/128), 6, true, (9367789/78125000000)⟩ (CT.node CT.nil ⟨(1567/512), (1577/512), 6, true, (591930551/5000000000000)⟩ CT.nil))) ⟨(1567/512), (791/256), 6, true, (1168886057/10000000000000)⟩ (CT.node (CT.node (CT.node CT.nil ⟨(1567/512), (1587/512), 6, true, (288536823/2500000000000)⟩ CT.nil) ⟨(1567/512), (199/64), 6, true, (569820171/5000000000000)⟩ (CT.node CT.nil ⟨(393/128), (791/256), 6, true, (1810022563/10000000000000)⟩ CT.nil)) ⟨(393/128), (199/64), 6, true, (1764735511/10000000000000)⟩ (CT.node (CT.node CT.nil ⟨(393/128), (801/256), 6, true, (215107179/1250000000000)⟩ CT.nil) ⟨(393/128), (403/128), 6, true, (419583999/2500000000000)⟩ CT.nil)))))

def tab6 : CT :=
  (CT.node (CT.node (CT.node (CT.node (CT.node (CT.node CT.nil ⟨(393/128), (51/16), 6, true, (798582451/5000000000000)⟩ CT.nil) ⟨(393/128), (413/128), 6, true, (1520846759/10000000000000)⟩ (CT.node CT.nil ⟨(393/128), (13/4), 6, true, (1477240831/10000000000000)⟩ CT.nil)) ⟨(1577/512), (1597/512), 6, true, (124770657/500000000000)⟩ (CT.node (CT.node CT.nil ⟨(791/256), (801/256), 6, true, (1670535297/5000000000000)⟩ CT.nil) ⟨(791/256), (403/128), 6, true, (1629257293/5000000000000)⟩ (CT.node CT.nil ⟨(791/256), (811/256), 6, true, (1589247651/5000000000000)⟩ CT.nil))) ⟨(791/256), (51/16), 6, true, (3100919687/10000000000000)⟩ (CT.node (CT.node (CT.node CT.nil ⟨(1587/512), (809/256), 6, true, (2090005161/5000000000000)⟩ CT.nil) ⟨(199/64), (811/256), 6, true, (5223624809/10000000000000)⟩ (CT.node CT.nil ⟨(199/64), (51/16), 6, true, (5096134953/10000000000000)⟩ CT.nil)) ⟨(199/64), (413/128), 6, true, (37911123/78125000000)⟩ (CT.node (CT.node CT.nil ⟨(199/64), (13/4), 6, true, (589186081/1250000000000)⟩ CT.nil) ⟨(403/128), (13/4), 6, true, (9713220361/10000000000000)⟩ (CT.node CT.nil ⟨(809/256), (13/4), 6, true, (11532825879/10000000000000)⟩ CT.nil)))) ⟨(13/4), (209/64), 7, false, (1799437923/625000000000)⟩ (CT.node (CT.node (CT.node (CT.node CT.nil ⟨(13/4), (105/32), 7, false, (7060987389/2500000000000)⟩ CT.nil) ⟨(13/4), (423/128), 7, false, (27447518209/10000000000000)⟩ (CT.node CT.nil ⟨(13/4), (107/32), 7, false, (5236311191/2000000000000)⟩ CT.nil)) ⟨(13/4), (219/64), 7, false, (23861384437/10000000000000)⟩ (CT.node (CT.node CT.nil ⟨(105/32), (421/128), 7, false, (34886068921/10000000000000)⟩ CT.nil) ⟨(421/128), (211/64), 7, false, (9074663383/2500000000000)⟩ (CT.node CT.nil ⟨(211/64), (53/16), 7, false, (37331393477/10000000000000)⟩ CT.nil))) ⟨(53/16), (27/8), 7, false, (7562713/2000000000)⟩ (CT.node (CT.node (CT.node CT.nil ⟨(27/8), (7/2), 7, false, (43210796373/10000000000000)⟩ CT.nil) ⟨(7/2), (29/8), 7, true, (1058437871/250000000000)⟩ (CT.node CT.nil ⟨(29/8), (59/16), 7, true, (9010606921/2500000000000)⟩ CT.nil)) ⟨(59/16), (237/64), 7, true, (35001008619/10000000000000)⟩ (CT.node (CT.node CT.nil ⟨(237/64), (15/4), 7, true, (26396659657/10000000000000)⟩ CT.nil) ⟨(15/4), (10143/2560), 8, false, (957611737/10000000000000)⟩ (CT.node CT.nil ⟨(999/256), 4, 8, false, (91689533/10000000000000)⟩ CT.nil))))) ⟨(63/16), (509/128), 8, false, (319416431/5000000000000)⟩ (CT.node (CT.node (CT.node (CT.node (CT.node CT.nil ⟨(63/16), (1023/256), 8, false, (38435113/2500000000000)⟩ CT.nil) ⟨(1009/256), (4087/1024), 8, false, (122092393/5000000000000)⟩ (CT.node CT.nil ⟨(1009/256), 4, 8, false, (48755691/5000000000000)⟩ CT.nil)) ⟨(1013/256), (2041/512), 8, false, (71867913/2000000000000)⟩ (CT.node (CT.node CT.nil ⟨(1013/256), (1023/256), 8, false, (31317919/2000000000000)⟩ CT.nil) ⟨(507/128), (8183/2048), 8, false, (82600037/5000000000000)⟩ (CT.node CT.nil ⟨(507/128), 4, 8, false, (99379817/10000000000000)⟩ CT.nil))) ⟨(2031/512), (2041/512), 8, false, (11299473/312500000000)⟩ (CT.node (CT.node (CT.node CT.nil ⟨(2031/512), (1023/256), 8, false, (157670757/10000000000000)⟩ CT.nil) ⟨(4067/1024), (8185/2048), 8, false, (30026951/2000000000000)⟩ (CT.node CT.nil ⟨(4067/1024), 4, 8, false, (2502377/250000000000)⟩ CT.nil)) ⟨(8143/2048), 4, 8, false, (100322671/10000000000000)⟩ (CT.node (CT.node CT.nil ⟨(509/128), (4087/1024), 8, false, (250286237/10000000000000)⟩ CT.nil) ⟨(509/128), (1023/256), 8, false, (39629583/2500000000000)⟩ (CT.node CT.nil ⟨(509/128), 4, 8, false, (20069123/2000000000000)⟩ CT.nil)))) ⟨(1019/256), 4, 8, false, (100512239/10000000000000)⟩ (CT.node (CT.node (CT.node (CT.node CT.nil ⟨(4077/1024), (4087/1024), 8, false, (250833039/10000000000000)⟩ CT.nil) ⟨(4077/1024), (1023/256), 8, false, (2482089/156250000000)⟩ (CT.node CT.nil ⟨(4077/1024), (16379/4096), 8, false, (23464061/2000000000000)⟩ CT.nil)) ⟨(4077/1024), 4, 8, false, (50274593/5000000000000)⟩ (CT.node (CT.node CT.nil ⟨(8163/2048), 4, 8, false, (50346043/5000000000000)⟩ CT.nil) ⟨(2041/512), (1023/256), 8, false, (39782441/2500000000000)⟩ (CT.node CT.nil ⟨(2041/512), 4, 8, false, (100705601/10000000000000)⟩ CT.nil))) ⟨(8165/2048), 4, 8, false, (100718643/10000000000000)⟩ (CT.node (CT.node (CT.node CT.nil ⟨(16339/4096), 4, 8, false, (4030859/400000000000)⟩ CT.nil) ⟨(4087/1024), 4, 8, false, (50407357/5000000000000)⟩ (CT.node CT.nil ⟨(1023/256), 4, 8, false, (100876421/10000000000000)⟩ CT.nil)) ⟨(8185/2048), 4, 8, false, (50439991/5000000000000)⟩ (CT.node (CT.node CT.nil ⟨(8189/2048), 4, 8, false, (50444739/5000000000000)⟩ CT.nil) ⟨(16379/4096), 4, 8, false, (100890131/10000000000000)⟩ CT.nil)))))

def tab7 : CT :=
  (CT.node (CT.node (CT.node (CT.node (CT.node (CT.node CT.nil ⟨4, (2049/512), 8, true, (76620491/10000000000000)⟩ CT.nil) ⟨4, (8199/2048), 8, true, (30307419/5000000000000)⟩ (CT.node CT.nil ⟨4, (16399/4096), 8, true, (29065073/5000000000000)⟩ CT.nil)) ⟨4, (2051/512), 8, true, (19058233/5000000000000)⟩ (CT.node (CT.node CT.nil ⟨4, (8205/2048), 8, true, (34242453/10000000000000)⟩ CT.nil) ⟨4, (16419/4096), 8, true, (9692591/5000000000000)⟩ (CT.node CT.nil ⟨4, (16421/4096), 8, true, (8327617/5000000000000)⟩ CT.nil))) ⟨4, (4107/1024), 8, true, (436723/500000000000)⟩ (CT.node (CT.node (CT.node CT.nil ⟨4, (8215/2048), 8, true, (6937709/10000000000000)⟩ CT.nil) ⟨4, (1027/256), 8, true, (2673983/5000000000000)⟩ (CT.node CT.nil ⟨4, (16441/4096), 8, true, (752127/10000000000000)⟩ CT.nil)) ⟨4, (8223/2048), 8, true, (4221/10000000000000)⟩ (CT.node (CT.node CT.nil ⟨(4097/1024), (2051/512), 8, true, (19058233/5000000000000)⟩ CT.nil) ⟨(4097/1024), (8209/2048), 8, true, (1301753/625000000000)⟩ (CT.node CT.nil ⟨(4097/1024), (4107/1024), 8, true, (436723/500000000000)⟩ CT.nil)))) ⟨(4097/1024), (16439/4096), 8, true, (70603/500000000000)⟩ (CT.node (CT.node (CT.node (CT.node CT.nil ⟨(8195/2048), (16441/4096), 8, true, (752127/10000000000000)⟩ CT.nil) ⟨(8199/2048), (8209/2048), 8, true, (1301753/625000000000)⟩ (CT.node CT.nil ⟨(8199/2048), (4107/1024), 8, true, (436723/500000000000)⟩ CT.nil)) ⟨(16399/4096), (32869/8192), 8, true, (730337/2000000000000)⟩ (CT.node (CT.node CT.nil ⟨(2051/512), (4107/1024), 8, true, (436723/500000000000)⟩ CT.nil) ⟨(2051/512), (8219/2048), 8, true, (113713/625000000000)⟩ (CT.node CT.nil ⟨(8205/2048), (32891/8192), 8, true, (5269/2500000000000)⟩ CT.nil))) ⟨(8209/2048), (8219/2048), 8, true, (113713/625000000000)⟩ (CT.node (CT.node (CT.node CT.nil ⟨(257/64), (2061/512), 8, true, (64801/10000000000000)⟩ CT.nil) ⟨(257/64), (4127/1024), 8, true, (32243/5000000000000)⟩ (CT.node CT.nil ⟨(257/64), (1033/256), 8, true, (32087/5000000000000)⟩ CT.nil)) ⟨(257/64), (2071/512), 8, true, (31777/5000000000000)⟩ (CT.node (CT.node CT.nil ⟨(257/64), (519/128), 8, true, (31471/5000000000000)⟩ CT.nil) ⟨(257/64), (2081/512), 8, true, (31169/5000000000000)⟩ (CT.node CT.nil ⟨(257/64), (1043/256), 8, true, (3087/500000000000)⟩ CT.nil))))) ⟨(257/64), (131/32), 8, true, (60567/10000000000000)⟩ (CT.node (CT.node (CT.node (CT.node (CT.node CT.nil ⟨(257/64), (1053/256), 8, true, (59421/10000000000000)⟩ CT.nil) ⟨(257/64), (529/128), 8, true, (58303/10000000000000)⟩ (CT.node CT.nil ⟨(257/64), (267/64), 8, true, (56143/10000000000000)⟩ CT.nil)) ⟨(257/64), (17/4), 8, true, (13029/2500000000000)⟩ (CT.node (CT.node CT.nil ⟨(8225/2048), (32971/8192), 8, true, (32949/1000000000000)⟩ CT.nil) ⟨(8225/2048), (16501/4096), 8, true, (1313/40000000000)⟩ (CT.node CT.nil ⟨(8225/2048), (16521/4096), 8, true, (163329/5000000000000)⟩ CT.nil))) ⟨(8225/2048), (2069/512), 8, true, (32421/1000000000000)⟩ (CT.node (CT.node (CT.node CT.nil ⟨(4113/1024), (16503/4096), 8, true, (198721/2500000000000)⟩ CT.nil) ⟨(8227/2048), (4139/1024), 8, true, (36159/250000000000)⟩ (CT.node CT.nil ⟨(8227/2048), (4149/1024), 8, true, (1432423/10000000000000)⟩ CT.nil)) ⟨(32913/8192), (4123/1024), 8, true, (1298021/5000000000000)⟩ (CT.node (CT.node CT.nil ⟨(16459/4096), (8265/2048), 8, true, (2002543/5000000000000)⟩ CT.nil) ⟨(16461/4096), (32993/8192), 8, true, (21693/40000000000)⟩ (CT.node CT.nil ⟨(16461/4096), (129/32), 8, true, (1350713/2500000000000)⟩ CT.nil)))) ⟨(16463/4096), (8267/2048), 8, true, (1737357/2500000000000)⟩ (CT.node (CT.node (CT.node (CT.node CT.nil ⟨(1029/256), (2109/512), 8, true, (1440757/2000000000000)⟩ CT.nil) ⟨(32931/8192), (16501/4096), 8, true, (2319419/2500000000000)⟩ (CT.node CT.nil ⟨(4117/1024), (4127/1024), 8, true, (11849221/10000000000000)⟩ CT.nil)) ⟨(4117/1024), (1033/256), 8, true, (11791793/10000000000000)⟩ (CT.node (CT.node CT.nil ⟨(4117/1024), (8285/2048), 8, true, (11672323/10000000000000)⟩ CT.nil) ⟨(8235/2048), (16521/4096), 8, true, (3526053/2500000000000)⟩ (CT.node CT.nil ⟨(2059/512), (16523/4096), 8, true, (16592229/10000000000000)⟩ CT.nil))) ⟨(2059/512), (16543/4096), 8, true, (16511887/10000000000000)⟩ (CT.node (CT.node (CT.node CT.nil ⟨(2059/512), (8287/2048), 8, true, (4097079/2500000000000)⟩ CT.nil) ⟨(2059/512), (8307/2048), 8, true, (8115287/5000000000000)⟩ (CT.node CT.nil ⟨(2059/512), (4169/1024), 8, true, (999363/625000000000)⟩ CT.nil)) ⟨(32953/8192), (129/32), 8, true, (11506103/5000000000000)⟩ (CT.node (CT.node CT.nil ⟨(515/128), (2111/512), 8, true, (13104471/5000000000000)⟩ CT.nil) ⟨(515/128), (2131/512), 8, true, (25235977/10000000000000)⟩ CT.nil)))))

def tab8 : CT :=
  (CT.node (CT.node (CT.node (CT.node (CT.node (CT.node CT.nil ⟨(515/128), (17/4), 8, true, (23206737/10000000000000)⟩ CT.nil) ⟨(16481/4096), (4133/1024), 8, true, (30275949/10000000000000)⟩ (CT.node CT.nil ⟨(16481/4096), (2069/512), 8, true, (7532357/2500000000000)⟩ CT.nil)) ⟨(2061/512), (1033/256), 8, true, (43842579/10000000000000)⟩ (CT.node (CT.node CT.nil ⟨(2061/512), (2071/512), 8, true, (43419407/10000000000000)⟩ CT.nil) ⟨(2061/512), (519/128), 8, true, (10750333/2500000000000)⟩ (CT.node CT.nil ⟨(2061/512), (2081/512), 8, true, (1064707/250000000000)⟩ CT.nil))) ⟨(8245/2048), (1037/256), 8, true, (9485773/2000000000000)⟩ (CT.node (CT.node (CT.node CT.nil ⟨(8245/2048), (2079/512), 8, true, (11743211/2500000000000)⟩ CT.nil) ⟨(4123/1024), (16543/4096), 8, true, (52510613/10000000000000)⟩ (CT.node CT.nil ⟨(8247/2048), (4149/1024), 8, true, (6897/1220703125)⟩ CT.nil)) ⟨(16501/4096), (2069/512), 8, true, (75190749/10000000000000)⟩ (CT.node (CT.node CT.nil ⟨(16503/4096), (8277/2048), 8, true, (80777393/10000000000000)⟩ CT.nil) ⟨(16503/4096), (8287/2048), 8, true, (5024187/625000000000)⟩ (CT.node CT.nil ⟨(4127/1024), (4137/1024), 8, true, (47933289/5000000000000)⟩ CT.nil)))) ⟨(4127/1024), (2071/512), 8, true, (47701541/5000000000000)⟩ (CT.node (CT.node (CT.node (CT.node CT.nil ⟨(4127/1024), (2089/512), 8, true, (92147329/10000000000000)⟩ CT.nil) ⟨(129/32), (16583/4096), 8, true, (107845387/10000000000000)⟩ (CT.node CT.nil ⟨(129/32), (8307/2048), 8, true, (428161/40000000000)⟩ CT.nil)) ⟨(4129/1024), (1045/256), 8, true, (58750599/5000000000000)⟩ (CT.node (CT.node CT.nil ⟨(4129/1024), (525/128), 8, true, (7204521/625000000000)⟩ CT.nil) ⟨(16523/4096), (8287/2048), 8, true, (36879733/2500000000000)⟩ (CT.node CT.nil ⟨(1033/256), (519/128), 8, true, (8305511/500000000000)⟩ CT.nil))) ⟨(1033/256), (4157/1024), 8, true, (165310021/10000000000000)⟩ (CT.node (CT.node (CT.node CT.nil ⟨(1033/256), (2081/512), 8, true, (164514637/10000000000000)⟩ CT.nil) ⟨(1033/256), (1043/256), 8, true, (81469089/5000000000000)⟩ (CT.node CT.nil ⟨(1033/256), (2091/512), 8, true, (20172571/1250000000000)⟩ CT.nil)) ⟨(1033/256), (131/32), 8, true, (159841537/10000000000000)⟩ (CT.node (CT.node CT.nil ⟨(1033/256), (1053/256), 8, true, (39204539/2500000000000)⟩ CT.nil) ⟨(1033/256), (529/128), 8, true, (153865963/10000000000000)⟩ (CT.node CT.nil ⟨(8265/2048), (2079/512), 8, true, (86688141/5000000000000)⟩ CT.nil))))) ⟨(8267/2048), (4159/1024), 8, true, (95123723/5000000000000)⟩ (CT.node (CT.node (CT.node (CT.node (CT.node CT.nil ⟨(8267/2048), (4169/1024), 8, true, (188423087/10000000000000)⟩ CT.nil) ⟨(16543/4096), (8307/2048), 8, true, (14547321/625000000000)⟩ (CT.node CT.nil ⟨(4137/1024), (519/128), 8, true, (128977417/5000000000000)⟩ CT.nil)) ⟨(4137/1024), (4157/1024), 8, true, (128356097/5000000000000)⟩ (CT.node (CT.node CT.nil ⟨(4137/1024), (2081/512), 8, true, (255477031/10000000000000)⟩ CT.nil) ⟨(2069/512), (4189/1024), 8, true, (134503623/5000000000000)⟩ (CT.node CT.nil ⟨(2069/512), (4209/1024), 8, true, (263915387/10000000000000)⟩ CT.nil))) ⟨(2069/512), (265/64), 8, true, (64064721/2500000000000)⟩ (CT.node (CT.node (CT.node CT.nil ⟨(2069/512), (535/128), 8, true, (246785359/10000000000000)⟩ CT.nil) ⟨(2071/512), (8309/2048), 8, true, (184591317/5000000000000)⟩ (CT.node CT.nil ⟨(2071/512), (4157/1024), 8, true, (184146301/5000000000000)⟩ CT.nil)) ⟨(2071/512), (2081/512), 8, true, (183260287/5000000000000)⟩ (CT.node (CT.node CT.nil ⟨(2071/512), (4167/1024), 8, true, (182379599/5000000000000)⟩ CT.nil) ⟨(2071/512), (1043/256), 8, true, (90752099/2500000000000)⟩ (CT.node CT.nil ⟨(2071/512), (2091/512), 8, true, (89884553/2500000000000)⟩ CT.nil)))) ⟨(2071/512), (131/32), 8, true, (17805471/500000000000)⟩ (CT.node (CT.node (CT.node (CT.node CT.nil ⟨(8287/2048), (4169/1024), 8, true, (200521187/5000000000000)⟩ CT.nil) ⟨(8289/2048), (4157/1024), 8, true, (431662129/10000000000000)⟩ (CT.node CT.nil ⟨(4147/1024), (4157/1024), 8, true, (20003551/400000000000)⟩ CT.nil)) ⟨(4147/1024), (8319/2048), 8, true, (498883881/10000000000000)⟩ (CT.node (CT.node CT.nil ⟨(4147/1024), (2081/512), 8, true, (99536523/2000000000000)⟩ CT.nil) ⟨(4147/1024), (4167/1024), 8, true, (495290917/10000000000000)⟩ (CT.node CT.nil ⟨(4149/1024), (525/128), 8, true, (267941559/5000000000000)⟩ CT.nil))) ⟨(8299/2048), (8319/2048), 8, true, (572192259/10000000000000)⟩ (CT.node (CT.node (CT.node CT.nil ⟨(8299/2048), (2081/512), 8, true, (570814473/10000000000000)⟩ CT.nil) ⟨(519/128), (8319/2048), 8, true, (162636919/2500000000000)⟩ (CT.node CT.nil ⟨(519/128), (2081/512), 8, true, (648981217/10000000000000)⟩ CT.nil)) ⟨(519/128), (8329/2048), 8, true, (323709737/5000000000000)⟩ (CT.node (CT.node CT.nil ⟨(519/128), (4167/1024), 8, true, (645862429/10000000000000)⟩ CT.nil) ⟨(519/128), (1043/256), 8, true, (160690591/2500000000000)⟩ (CT.node CT.nil ⟨(519/128), (4177/1024), 8, true, (79960111/1250000000000)⟩ CT.nil))))))

def tab9 : CT :=
  (CT.node (CT.node (CT.node (CT.node (CT.node (CT.node CT.nil ⟨(519/128), (131/32), 8, true, (315273331/5000000000000)⟩ CT.nil) ⟨(519/128), (2101/512), 8, true, (624547701/10000000000000)⟩ (CT.node CT.nil ⟨(519/128), (1053/256), 8, true, (154654989/2500000000000)⟩ CT.nil)) ⟨(519/128), (529/128), 8, true, (24278963/400000000000)⟩ (CT.node (CT.node CT.nil ⟨(519/128), (1063/256), 8, true, (297800559/5000000000000)⟩ CT.nil) ⟨(519/128), (267/64), 8, true, (913271/15625000000)⟩ (CT.node CT.nil ⟨(519/128), (539/128), 8, true, (563044583/10000000000000)⟩ CT.nil))) ⟨(519/128), (17/4), 8, true, (271285583/5000000000000)⟩ (CT.node (CT.node (CT.node CT.nil ⟨(8309/2048), (2081/512), 8, true, (183045519/2500000000000)⟩ CT.nil) ⟨(8309/2048), (8329/2048), 8, true, (730420113/10000000000000)⟩ (CT.node CT.nil ⟨(4157/1024), (16653/4096), 8, true, (81942717/1000000000000)⟩ CT.nil)) ⟨(4157/1024), (8329/2048), 8, true, (12788137/156250000000)⟩ (CT.node (CT.node CT.nil ⟨(4157/1024), (4167/1024), 8, true, (25514763/312500000000)⟩ CT.nil) ⟨(4157/1024), (8339/2048), 8, true, (407254991/5000000000000)⟩ (CT.node CT.nil ⟨(4157/1024), (1043/256), 8, true, (812553443/10000000000000)⟩ CT.nil)))) ⟨(4157/1024), (4177/1024), 8, true, (808657969/10000000000000)⟩ (CT.node (CT.node (CT.node (CT.node CT.nil ⟨(4157/1024), (2091/512), 8, true, (402392913/5000000000000)⟩ CT.nil) ⟨(2079/512), (4209/1024), 8, true, (32774279/400000000000)⟩ (CT.node CT.nil ⟨(16633/4096), (16653/4096), 8, true, (865374359/10000000000000)⟩ CT.nil)) ⟨(16633/4096), (8329/2048), 8, true, (864332647/10000000000000)⟩ (CT.node (CT.node CT.nil ⟨(8319/2048), (8329/2048), 8, true, (227869559/2500000000000)⟩ CT.nil) ⟨(8319/2048), (16663/4096), 8, true, (910381357/10000000000000)⟩ (CT.node CT.nil ⟨(8319/2048), (4167/1024), 8, true, (56830383/625000000000)⟩ CT.nil))) ⟨(8319/2048), (8339/2048), 8, true, (907100611/10000000000000)⟩ (CT.node (CT.node (CT.node CT.nil ⟨(8319/2048), (1043/256), 8, true, (45246083/500000000000)⟩ CT.nil) ⟨(65/16), (2131/512), 8, true, (848165913/10000000000000)⟩ (CT.node CT.nil ⟨(16643/4096), (8329/2048), 8, true, (959876941/10000000000000)⟩ CT.nil)) ⟨(16643/4096), (16663/4096), 8, true, (958721819/10000000000000)⟩ (CT.node (CT.node CT.nil ⟨(16643/4096), (4167/1024), 8, true, (191513687/2000000000000)⟩ CT.nil) ⟨(2081/512), (16663/4096), 8, true, (126039153/1250000000000)⟩ (CT.node CT.nil ⟨(2081/512), (4167/1024), 8, true, (1007100179/10000000000000)⟩ CT.nil))))) ⟨(2081/512), (16673/4096), 8, true, (1005888959/10000000000000)⟩ (CT.node (CT.node (CT.node (CT.node (CT.node CT.nil ⟨(2081/512), (8339/2048), 8, true, (1004679561/10000000000000)⟩ CT.nil) ⟨(2081/512), (1043/256), 8, true, (200453243/2000000000000)⟩ (CT.node CT.nil ⟨(2081/512), (8349/2048), 8, true, (199972023/2000000000000)⟩ CT.nil)) ⟨(2081/512), (4177/1024), 8, true, (249365309/2500000000000)⟩ (CT.node (CT.node CT.nil ⟨(2081/512), (2091/512), 8, true, (198537007/2000000000000)⟩ CT.nil) ⟨(2081/512), (4187/1024), 8, true, (197587481/2000000000000)⟩ (CT.node CT.nil ⟨(2081/512), (131/32), 8, true, (49160907/500000000000)⟩ CT.nil))) ⟨(2081/512), (2101/512), 8, true, (973863897/10000000000000)⟩ (CT.node (CT.node (CT.node CT.nil ⟨(2081/512), (1053/256), 8, true, (9646207/100000000000)⟩ CT.nil) ⟨(16653/4096), (4167/1024), 8, true, (1057880619/10000000000000)⟩ (CT.node CT.nil ⟨(16653/4096), (16673/4096), 8, true, (528304163/5000000000000)⟩ CT.nil)) ⟨(16653/4096), (8339/2048), 8, true, (1055337947/10000000000000)⟩ (CT.node (CT.node CT.nil ⟨(8329/2048), (33341/8192), 8, true, (554620627/5000000000000)⟩ CT.nil) ⟨(8329/2048), (16673/4096), 8, true, (1108574073/10000000000000)⟩ (CT.node CT.nil ⟨(8329/2048), (8339/2048), 8, true, (553620607/5000000000000)⟩ CT.nil)))) ⟨(8329/2048), (16683/4096), 8, true, (1105910359/10000000000000)⟩ (CT.node (CT.node (CT.node (CT.node CT.nil ⟨(8329/2048), (1043/256), 8, true, (8629543/78125000000)⟩ CT.nil) ⟨(8329/2048), (8349/2048), 8, true, (55096489/500000000000)⟩ (CT.node CT.nil ⟨(8329/2048), (4177/1024), 8, true, (549643007/5000000000000)⟩ CT.nil)) ⟨(33321/8192), (16673/4096), 8, true, (1135024061/10000000000000)⟩ (CT.node (CT.node CT.nil ⟨(16663/4096), (33351/8192), 8, true, (36283957/312500000000)⟩ CT.nil) ⟨(16663/4096), (8339/2048), 8, true, (290097117/2500000000000)⟩ (CT.node CT.nil ⟨(16663/4096), (16683/4096), 8, true, (1158993733/10000000000000)⟩ CT.nil))) ⟨(16663/4096), (1043/256), 8, true, (1157601093/10000000000000)⟩ (CT.node (CT.node (CT.node CT.nil ⟨(33331/8192), (8339/2048), 8, true, (118742829/1000000000000)⟩ CT.nil) ⟨(4167/1024), (33361/8192), 8, true, (303512103/2500000000000)⟩ (CT.node CT.nil ⟨(4167/1024), (16683/4096), 8, true, (1213318631/10000000000000)⟩ CT.nil)) ⟨(4167/1024), (1043/256), 8, true, (242372143/2000000000000)⟩ (CT.node (CT.node CT.nil ⟨(4167/1024), (16693/4096), 8, true, (121040499/1000000000000)⟩ CT.nil) ⟨(4167/1024), (8349/2048), 8, true, (1208951451/10000000000000)⟩ CT.nil)))))

def tab10 : CT :=
  (CT.node (CT.node (CT.node (CT.node (CT.node (CT.node CT.nil ⟨(4167/1024), (8359/2048), 8, true, (1203159081/10000000000000)⟩ CT.nil) ⟨(4167/1024), (2091/512), 8, true, (600137957/5000000000000)⟩ (CT.node CT.nil ⟨(4167/1024), (4187/1024), 8, true, (37329233/312500000000)⟩ CT.nil)) ⟨(4167/1024), (131/32), 8, true, (74301831/625000000000)⟩ (CT.node (CT.node CT.nil ⟨(33341/8192), (33361/8192), 8, true, (155211591/1250000000000)⟩ CT.nil) ⟨(33341/8192), (16683/4096), 8, true, (124094633/1000000000000)⟩ (CT.node CT.nil ⟨(16673/4096), (16683/4096), 8, true, (634442007/5000000000000)⟩ CT.nil))) ⟨(16673/4096), (33371/8192), 8, true, (634060693/5000000000000)⟩ (CT.node (CT.node (CT.node CT.nil ⟨(16673/4096), (1043/256), 8, true, (1267359331/10000000000000)⟩ CT.nil) ⟨(16673/4096), (16693/4096), 8, true, (1265836939/10000000000000)⟩ (CT.node CT.nil ⟨(16673/4096), (8349/2048), 8, true, (1264316833/10000000000000)⟩ CT.nil)) ⟨(33351/8192), (33371/8192), 8, true, (648175967/5000000000000)⟩ (CT.node (CT.node CT.nil ⟨(33351/8192), (1043/256), 8, true, (647786457/5000000000000)⟩ CT.nil) ⟨(4169/1024), (265/64), 8, true, (1219525351/10000000000000)⟩ (CT.node CT.nil ⟨(8339/2048), (1043/256), 8, true, (1324095821/10000000000000)⟩ CT.nil)))) ⟨(8339/2048), (33381/8192), 8, true, (1323300249/10000000000000)⟩ (CT.node (CT.node (CT.node (CT.node CT.nil ⟨(8339/2048), (16693/4096), 8, true, (52900211/400000000000)⟩ CT.nil) ⟨(8339/2048), (8349/2048), 8, true, (660458559/5000000000000)⟩ (CT.node CT.nil ⟨(8339/2048), (16703/4096), 8, true, (659665673/5000000000000)⟩ CT.nil)) ⟨(8339/2048), (4177/1024), 8, true, (263549591/2000000000000)⟩ (CT.node (CT.node CT.nil ⟨(8339/2048), (8359/2048), 8, true, (262917659/2000000000000)⟩ CT.nil) ⟨(8339/2048), (2091/512), 8, true, (655719053/5000000000000)⟩ (CT.node CT.nil ⟨(33361/8192), (33381/8192), 8, true, (338028751/2500000000000)⟩ CT.nil))) ⟨(33361/8192), (16693/4096), 8, true, (1351302719/10000000000000)⟩ (CT.node (CT.node (CT.node CT.nil ⟨(16683/4096), (16693/4096), 8, true, (690204403/5000000000000)⟩ CT.nil) ⟨(16683/4096), (33391/8192), 8, true, (1379579649/10000000000000)⟩ (CT.node CT.nil ⟨(16683/4096), (8349/2048), 8, true, (275750223/2000000000000)⟩ CT.nil)) ⟨(16683/4096), (16703/4096), 8, true, (172136989/1250000000000)⟩ (CT.node (CT.node CT.nil ⟨(16683/4096), (4177/1024), 8, true, (275088639/2000000000000)⟩ CT.nil) ⟨(33371/8192), (33391/8192), 8, true, (176122069/1250000000000)⟩ (CT.node CT.nil ⟨(33371/8192), (8349/2048), 8, true, (1408130363/10000000000000)⟩ CT.nil))))) ⟨(1043/256), (8349/2048), 8, true, (718908779/5000000000000)⟩ (CT.node (CT.node (CT.node (CT.node (CT.node CT.nil ⟨(1043/256), (33401/8192), 8, true, (718477089/5000000000000)⟩ CT.nil) ⟨(1043/256), (16703/4096), 8, true, (718045723/5000000000000)⟩ (CT.node CT.nil ⟨(1043/256), (4177/1024), 8, true, (57374717/400000000000)⟩ CT.nil)) ⟨(1043/256), (16713/4096), 8, true, (1432646991/10000000000000)⟩ (CT.node (CT.node CT.nil ⟨(1043/256), (8359/2048), 8, true, (715464319/5000000000000)⟩ CT.nil) ⟨(1043/256), (2091/512), 8, true, (1427499659/10000000000000)⟩ (CT.node CT.nil ⟨(1043/256), (8369/2048), 8, true, (1424080951/10000000000000)⟩ CT.nil))) ⟨(1043/256), (4187/1024), 8, true, (1420672477/10000000000000)⟩ (CT.node (CT.node (CT.node CT.nil ⟨(1043/256), (131/32), 8, true, (1413886087/10000000000000)⟩ CT.nil) ⟨(1043/256), (4197/1024), 8, true, (703570097/5000000000000)⟩ (CT.node CT.nil ⟨(1043/256), (2101/512), 8, true, (140043451/1000000000000)⟩ CT.nil)) ⟨(1043/256), (1053/256), 8, true, (69357131/500000000000)⟩ (CT.node (CT.node CT.nil ⟨(1043/256), (2111/512), 8, true, (274801629/2000000000000)⟩ CT.nil) ⟨(1043/256), (529/128), 8, true, (1361028853/10000000000000)⟩ (CT.node CT.nil ⟨(1043/256), (1063/256), 8, true, (1335527067/10000000000000)⟩ CT.nil)))) ⟨(1043/256), (267/64), 8, true, (655310061/5000000000000)⟩ (CT.node (CT.node (CT.node (CT.node CT.nil ⟨(33381/8192), (33401/8192), 8, true, (1466931139/10000000000000)⟩ CT.nil) ⟨(33381/8192), (16703/4096), 8, true, (1466050409/10000000000000)⟩ (CT.node CT.nil ⟨(16693/4096), (16703/4096), 8, true, (748158303/5000000000000)⟩ CT.nil)) ⟨(16693/4096), (33411/8192), 8, true, (1495418369/10000000000000)⟩ (CT.node (CT.node CT.nil ⟨(16693/4096), (4177/1024), 8, true, (747260403/5000000000000)⟩ CT.nil) ⟨(16693/4096), (16713/4096), 8, true, (1492727701/10000000000000)⟩ (CT.node CT.nil ⟨(16693/4096), (8359/2048), 8, true, (298187457/2000000000000)⟩ CT.nil))) ⟨(33391/8192), (33411/8192), 8, true, (305194653/2000000000000)⟩ (CT.node (CT.node (CT.node CT.nil ⟨(33391/8192), (4177/1024), 8, true, (1525057363/10000000000000)⟩ CT.nil) ⟨(8349/2048), (4177/1024), 8, true, (77795021/500000000000)⟩ (CT.node CT.nil ⟨(8349/2048), (33421/8192), 8, true, (194370837/1250000000000)⟩ CT.nil)) ⟨(8349/2048), (16713/4096), 8, true, (1554033673/10000000000000)⟩ (CT.node (CT.node CT.nil ⟨(8349/2048), (8359/2048), 8, true, (62086789/400000000000)⟩ CT.nil) ⟨(8349/2048), (16723/4096), 8, true, (775154287/5000000000000)⟩ (CT.node CT.nil ⟨(8349/2048), (2091/512), 8, true, (1548450213/10000000000000)⟩ CT.nil))))))

def tab11 : CT :=
  (CT.node (CT.node (CT.node (CT.node (CT.node (CT.node CT.nil ⟨(8349/2048), (4187/1024), 8, true, (1541044571/10000000000000)⟩ CT.nil) ⟨(33401/8192), (33421/8192), 8, true, (793048687/5000000000000)⟩ (CT.node CT.nil ⟨(33401/8192), (16713/4096), 8, true, (1585145671/10000000000000)⟩ CT.nil)) ⟨(16703/4096), (33431/8192), 8, true, (100974599/625000000000)⟩ (CT.node (CT.node CT.nil ⟨(16703/4096), (8359/2048), 8, true, (807312237/5000000000000)⟩ CT.nil) ⟨(16703/4096), (16723/4096), 8, true, (322537687/2000000000000)⟩ (CT.node CT.nil ⟨(16703/4096), (2091/512), 8, true, (1610755299/10000000000000)⟩ CT.nil))) ⟨(33411/8192), (8359/2048), 8, true, (51447179/312500000000)⟩ (CT.node (CT.node (CT.node CT.nil ⟨(4177/1024), (33441/8192), 8, true, (335458679/2000000000000)⟩ CT.nil) ⟨(4177/1024), (16723/4096), 8, true, (838143789/5000000000000)⟩ (CT.node CT.nil ⟨(4177/1024), (2091/512), 8, true, (334855641/2000000000000)⟩ CT.nil)) ⟨(4177/1024), (16733/4096), 8, true, (418067961/2500000000000)⟩ (CT.node (CT.node CT.nil ⟨(4177/1024), (8369/2048), 8, true, (1670268489/10000000000000)⟩ CT.nil) ⟨(4177/1024), (4187/1024), 8, true, (1666270777/10000000000000)⟩ (CT.node CT.nil ⟨(4177/1024), (8379/2048), 8, true, (66491401/400000000000)⟩ CT.nil)))) ⟨(4177/1024), (131/32), 8, true, (1658311191/10000000000000)⟩ (CT.node (CT.node (CT.node (CT.node CT.nil ⟨(4177/1024), (4197/1024), 8, true, (12893743/78125000000)⟩ CT.nil) ⟨(4177/1024), (2101/512), 8, true, (1642534177/10000000000000)⟩ (CT.node CT.nil ⟨(33421/8192), (16723/4096), 8, true, (1708543871/10000000000000)⟩ CT.nil)) ⟨(2089/512), (535/128), 8, true, (1572805651/10000000000000)⟩ (CT.node (CT.node CT.nil ⟨(16713/4096), (2091/512), 8, true, (1739017297/10000000000000)⟩ CT.nil) ⟨(16713/4096), (16733/4096), 8, true, (434233339/2500000000000)⟩ (CT.node CT.nil ⟨(16713/4096), (8369/2048), 8, true, (867426269/5000000000000)⟩ CT.nil))) ⟨(8359/2048), (16733/4096), 8, true, (112675493/625000000000)⟩ (CT.node (CT.node (CT.node CT.nil ⟨(8359/2048), (8369/2048), 8, true, (1800648153/10000000000000)⟩ CT.nil) ⟨(8359/2048), (16743/4096), 8, true, (1798491653/10000000000000)⟩ (CT.node CT.nil ⟨(8359/2048), (4187/1024), 8, true, (1796338383/10000000000000)⟩ CT.nil)) ⟨(8359/2048), (8379/2048), 8, true, (1792041507/10000000000000)⟩ (CT.node (CT.node CT.nil ⟨(8359/2048), (131/32), 8, true, (1787757479/10000000000000)⟩ CT.nil) ⟨(16723/4096), (8369/2048), 8, true, (933826779/5000000000000)⟩ (CT.node CT.nil ⟨(16723/4096), (16743/4096), 8, true, (1865416811/10000000000000)⟩ CT.nil))))) ⟨(16723/4096), (4187/1024), 8, true, (1863183413/10000000000000)⟩ (CT.node (CT.node (CT.node (CT.node (CT.node CT.nil ⟨(2091/512), (4187/1024), 8, true, (965616743/5000000000000)⟩ CT.nil) ⟨(2091/512), (16753/4096), 8, true, (964460991/5000000000000)⟩ (CT.node CT.nil ⟨(2091/512), (8379/2048), 8, true, (963306969/5000000000000)⟩ CT.nil)) ⟨(2091/512), (131/32), 8, true, (1922008203/10000000000000)⟩ (CT.node (CT.node CT.nil ⟨(2091/512), (8389/2048), 8, true, (1917416231/10000000000000)⟩ CT.nil) ⟨(2091/512), (4197/1024), 8, true, (1912837973/10000000000000)⟩ (CT.node CT.nil ⟨(2091/512), (2101/512), 8, true, (951861201/5000000000000)⟩ CT.nil))) ⟨(2091/512), (4207/1024), 8, true, (947330549/5000000000000)⟩ (CT.node (CT.node (CT.node CT.nil ⟨(2091/512), (1053/256), 8, true, (942826837/5000000000000)⟩ CT.nil) ⟨(2091/512), (2111/512), 8, true, (933899467/5000000000000)⟩ (CT.node CT.nil ⟨(2091/512), (529/128), 8, true, (1850155147/10000000000000)⟩ CT.nil)) ⟨(2091/512), (1081/256), 8, true, (1697224391/10000000000000)⟩ (CT.node (CT.node CT.nil ⟨(16733/4096), (16753/4096), 8, true, (49952307/250000000000)⟩ CT.nil) ⟨(16733/4096), (8379/2048), 8, true, (1995701471/10000000000000)⟩ (CT.node CT.nil ⟨(8369/2048), (131/32), 8, true, (2061048329/10000000000000)⟩ CT.nil)))) ⟨(8369/2048), (8389/2048), 8, true, (2056124169/10000000000000)⟩ (CT.node (CT.node (CT.node (CT.node CT.nil ⟨(8369/2048), (4197/1024), 8, true, (410242943/2000000000000)⟩ CT.nil) ⟨(4187/1024), (8389/2048), 8, true, (1099796941/5000000000000)⟩ (CT.node CT.nil ⟨(4187/1024), (4197/1024), 8, true, (2194341861/10000000000000)⟩ CT.nil)) ⟨(4187/1024), (8399/2048), 8, true, (2189105517/10000000000000)⟩ (CT.node (CT.node CT.nil ⟨(4187/1024), (2101/512), 8, true, (272985599/1250000000000)⟩ CT.nil) ⟨(4187/1024), (4207/1024), 8, true, (271686247/1250000000000)⟩ (CT.node CT.nil ⟨(4187/1024), (1053/256), 8, true, (216315697/1000000000000)⟩ CT.nil))) ⟨(8379/2048), (8399/2048), 8, true, (2336612903/10000000000000)⟩ (CT.node (CT.node (CT.node CT.nil ⟨(8379/2048), (2101/512), 8, true, (291380049/1250000000000)⟩ CT.nil) ⟨(131/32), (4207/1024), 8, true, (3861047/15625000000)⟩ (CT.node CT.nil ⟨(131/32), (1053/256), 8, true, (1229661173/5000000000000)⟩ CT.nil)) ⟨(131/32), (4217/1024), 8, true, (2447644383/10000000000000)⟩ (CT.node (CT.node CT.nil ⟨(131/32), (2111/512), 8, true, (1218017847/5000000000000)⟩ CT.nil) ⟨(131/32), (529/128), 8, true, (2413024171/10000000000000)⟩ CT.nil)))))

def tab12 : CT :=
  (CT.node (CT.node (CT.node (CT.node (CT.node (CT.node CT.nil ⟨(131/32), (267/64), 8, true, (1161826227/5000000000000)⟩ CT.nil) ⟨(131/32), (1073/256), 8, true, (18244153/80000000000)⟩ (CT.node CT.nil ⟨(131/32), (539/128), 8, true, (2238382569/10000000000000)⟩ CT.nil)) ⟨(131/32), (17/4), 8, true, (2156990541/10000000000000)⟩ (CT.node (CT.node CT.nil ⟨(4197/1024), (4217/1024), 8, true, (690206739/2500000000000)⟩ CT.nil) ⟨(4197/1024), (2111/512), 8, true, (549546581/2000000000000)⟩ (CT.node CT.nil ⟨(525/128), (17/4), 8, true, (2606310863/10000000000000)⟩ CT.nil))) ⟨(2101/512), (529/128), 8, true, (3048526697/10000000000000)⟩ (CT.node (CT.node (CT.node CT.nil ⟨(2101/512), (2121/512), 8, true, (3019797449/10000000000000)⟩ CT.nil) ⟨(2101/512), (1063/256), 8, true, (2991406031/10000000000000)⟩ (CT.node CT.nil ⟨(1053/256), (267/64), 8, true, (1808088631/5000000000000)⟩ CT.nil)) ⟨(1053/256), (1073/256), 8, true, (709810229/2000000000000)⟩ (CT.node (CT.node CT.nil ⟨(1053/256), (539/128), 8, true, (1741738127/5000000000000)⟩ CT.nil) ⟨(529/128), (17/4), 8, true, (600628743/1250000000000)⟩ (CT.node CT.nil ⟨(1061/256), (17/4), 8, true, (5787071159/10000000000000)⟩ CT.nil)))) ⟨(267/64), (17/4), 8, true, (8382305677/10000000000000)⟩ (CT.node (CT.node (CT.node (CT.node CT.nil ⟨(17/4), (549/128), 9, false, (16970875159/10000000000000)⟩ CT.nil) ⟨(17/4), (1101/256), 9, false, (8393078289/5000000000000)⟩ (CT.node CT.nil ⟨(17/4), (277/64), 9, false, (16364828489/10000000000000)⟩ CT.nil)) ⟨(17/4), (141/32), 9, false, (15231803251/10000000000000)⟩ (CT.node (CT.node CT.nil ⟨(17/4), (283/64), 9, false, (7508548427/5000000000000)⟩ CT.nil) ⟨(17/4), (287/64), 9, false, (7097602747/5000000000000)⟩ (CT.node CT.nil ⟨(75/16), (19/4), 9, true, (16026017701/10000000000000)⟩ CT.nil))) ⟨(19/4), (1271/256), 10, false, (498772193/10000000000000)⟩ (CT.node (CT.node (CT.node CT.nil ⟨(5135/1024), (10341/2048), 10, true, (796707/5000000000000)⟩ CT.nil) ⟨(5135/1024), (10361/2048), 10, true, (790561/5000000000000)⟩ (CT.node CT.nil ⟨(5135/1024), (2603/512), 10, true, (155031/1000000000000)⟩ CT.nil)) ⟨(10279/2048), (5175/1024), 10, true, (194973/156250000000)⟩ (CT.node (CT.node CT.nil ⟨(1285/256), (5165/1024), 10, true, (2887779/2000000000000)⟩ CT.nil) ⟨(1285/256), (2585/512), 10, true, (449469/312500000000)⟩ (CT.node CT.nil ⟨(1285/256), (1295/256), 10, true, (3568011/2500000000000)⟩ CT.nil))))) ⟨(1285/256), (2595/512), 10, true, (14162149/10000000000000)⟩ (CT.node (CT.node (CT.node (CT.node (CT.node CT.nil ⟨(1285/256), (325/64), 10, true, (1405331/1000000000000)⟩ CT.nil) ⟨(1285/256), (1305/256), 10, true, (13838751/10000000000000)⟩ (CT.node CT.nil ⟨(1285/256), (655/128), 10, true, (6814137/5000000000000)⟩ CT.nil)) ⟨(643/128), (10399/2048), 10, true, (33101423/10000000000000)⟩ (CT.node (CT.node CT.nil ⟨(643/128), (5235/1024), 10, true, (32210921/10000000000000)⟩ CT.nil) ⟨(5145/1024), (5165/1024), 10, true, (10044841/2500000000000)⟩ (CT.node CT.nil ⟨(5145/1024), (2585/512), 10, true, (5002981/1250000000000)⟩ CT.nil))) ⟨(5145/1024), (20691/4096), 10, true, (7987727/2000000000000)⟩ (CT.node (CT.node (CT.node CT.nil ⟨(5145/1024), (10361/2048), 10, true, (39699707/10000000000000)⟩ CT.nil) ⟨(2573/512), (10383/2048), 10, true, (45928559/10000000000000)⟩ (CT.node CT.nil ⟨(2573/512), (10403/2048), 10, true, (4557569/1000000000000)⟩ CT.nil)) ⟨(2573/512), (661/128), 10, true, (42660549/10000000000000)⟩ (CT.node (CT.node CT.nil ⟨(2573/512), (333/64), 10, true, (41391449/10000000000000)⟩ CT.nil) ⟨(10299/2048), (5185/1024), 10, true, (9159361/1250000000000)⟩ (CT.node CT.nil ⟨(2575/512), (2585/512), 10, true, (314267/40000000000)⟩ CT.nil)))) ⟨(2575/512), (5175/1024), 10, true, (19565737/2500000000000)⟩ (CT.node (CT.node (CT.node (CT.node CT.nil ⟨(2575/512), (1295/256), 10, true, (38980307/5000000000000)⟩ CT.nil) ⟨(2575/512), (2595/512), 10, true, (38680157/5000000000000)⟩ (CT.node CT.nil ⟨(2575/512), (325/64), 10, true, (76765783/10000000000000)⟩ CT.nil)) ⟨(10301/2048), (2593/512), 10, true, (82109019/10000000000000)⟩ (CT.node (CT.node CT.nil ⟨(10301/2048), (1299/256), 10, true, (81477507/10000000000000)⟩ CT.nil) ⟨(20611/4096), (10361/2048), 10, true, (208853/20000000000)⟩ (CT.node CT.nil ⟨(5155/1024), (2585/512), 10, true, (16256217/1250000000000)⟩ CT.nil))) ⟨(5155/1024), (5175/1024), 10, true, (6477343/500000000000)⟩ (CT.node (CT.node (CT.node CT.nil ⟨(5155/1024), (20711/4096), 10, true, (64635657/5000000000000)⟩ CT.nil) ⟨(5155/1024), (10381/2048), 10, true, (128003319/10000000000000)⟩ (CT.node CT.nil ⟨(5155/1024), (10421/2048), 10, true, (31511369/2500000000000)⟩ CT.nil)) ⟨(5155/1024), (2613/512), 10, true, (2491077/200000000000)⟩ (CT.node (CT.node CT.nil ⟨(1289/256), (10383/2048), 10, true, (139560919/10000000000000)⟩ CT.nil) ⟨(10319/2048), (5195/1024), 10, true, (91940011/5000000000000)⟩ (CT.node CT.nil ⟨(10319/2048), (5215/1024), 10, true, (181069953/10000000000000)⟩ CT.nil))))))

def tab13 : CT :=
  (CT.node (CT.node (CT.node (CT.node (CT.node (CT.node CT.nil ⟨(645/128), (5175/1024), 10, true, (38749297/2000000000000)⟩ CT.nil) ⟨(645/128), (20711/4096), 10, true, (48333597/2500000000000)⟩ (CT.node CT.nil ⟨(645/128), (1295/256), 10, true, (12062377/625000000000)⟩ CT.nil)) ⟨(645/128), (5185/1024), 10, true, (19225319/1000000000000)⟩ (CT.node (CT.node CT.nil ⟨(645/128), (2595/512), 10, true, (191511939/10000000000000)⟩ CT.nil) ⟨(645/128), (325/64), 10, true, (190040129/10000000000000)⟩ (CT.node CT.nil ⟨(645/128), (2605/512), 10, true, (37716487/2000000000000)⟩ CT.nil))) ⟨(645/128), (1305/256), 10, true, (187138697/10000000000000)⟩ (CT.node (CT.node (CT.node CT.nil ⟨(645/128), (655/128), 10, true, (5759139/312500000000)⟩ CT.nil) ⟨(645/128), (1315/256), 10, true, (90750063/5000000000000)⟩ (CT.node CT.nil ⟨(645/128), (165/32), 10, true, (178760509/10000000000000)⟩ CT.nil)) ⟨(645/128), (665/128), 10, true, (21679333/1250000000000)⟩ (CT.node (CT.node CT.nil ⟨(645/128), (335/64), 10, true, (168305763/10000000000000)⟩ CT.nil) ⟨(10321/2048), (20733/4096), 10, true, (99799521/5000000000000)⟩ (CT.node CT.nil ⟨(10321/2048), (1299/256), 10, true, (19764329/1000000000000)⟩ CT.nil)))) ⟨(10323/2048), (5207/1024), 10, true, (42053501/2000000000000)⟩ (CT.node (CT.node (CT.node (CT.node CT.nil ⟨(10323/2048), (5217/1024), 10, true, (8346273/400000000000)⟩ CT.nil) ⟨(10325/2048), (5175/1024), 10, true, (115347177/5000000000000)⟩ (CT.node CT.nil ⟨(20651/4096), (10361/2048), 10, true, (116785217/5000000000000)⟩ CT.nil)) ⟨(1291/256), (5235/1024), 10, true, (242928173/10000000000000)⟩ (CT.node (CT.node CT.nil ⟨(1291/256), (5275/1024), 10, true, (14726831/625000000000)⟩ CT.nil) ⟨(1291/256), (2653/512), 10, true, (46032101/2000000000000)⟩ (CT.node CT.nil ⟨(1291/256), (21/4), 10, true, (109191861/5000000000000)⟩ CT.nil))) ⟨(5165/1024), (10355/2048), 10, true, (67587843/2500000000000)⟩ (CT.node (CT.node (CT.node CT.nil ⟨(5165/1024), (1295/256), 10, true, (134914401/5000000000000)⟩ CT.nil) ⟨(5165/1024), (20731/4096), 10, true, (269255433/10000000000000)⟩ (CT.node CT.nil ⟨(5165/1024), (5185/1024), 10, true, (53757489/2000000000000)⟩ CT.nil)) ⟨(5165/1024), (20751/4096), 10, true, (268216841/10000000000000)⟩ (CT.node (CT.node CT.nil ⟨(5165/1024), (2595/512), 10, true, (26775111/1000000000000)⟩ CT.nil) ⟨(10331/2048), (20753/4096), 10, true, (138225741/5000000000000)⟩ (CT.node CT.nil ⟨(2583/512), (10403/2048), 10, true, (282019961/10000000000000)⟩ CT.nil))))) ⟨(2583/512), (10423/2048), 10, true, (55971473/2000000000000)⟩ (CT.node (CT.node (CT.node (CT.node (CT.node CT.nil ⟨(2583/512), (5237/1024), 10, true, (274435871/10000000000000)⟩ CT.nil) ⟨(10335/2048), (10355/2048), 10, true, (313680999/10000000000000)⟩ (CT.node CT.nil ⟨(10335/2048), (1295/256), 10, true, (12522987/400000000000)⟩ CT.nil)) ⟨(20671/4096), (10371/2048), 10, true, (79057119/2500000000000)⟩ (CT.node (CT.node CT.nil ⟨(323/64), (2655/512), 10, true, (72912521/2500000000000)⟩ CT.nil) ⟨(20673/4096), (5191/1024), 10, true, (10122207/312500000000)⟩ (CT.node CT.nil ⟨(2585/512), (1295/256), 10, true, (359539763/10000000000000)⟩ CT.nil))) ⟨(2585/512), (10365/2048), 10, true, (71769027/2000000000000)⟩ (CT.node (CT.node (CT.node CT.nil ⟨(2585/512), (5185/1024), 10, true, (358152183/10000000000000)⟩ CT.nil) ⟨(2585/512), (20751/4096), 10, true, (89347967/2500000000000)⟩ (CT.node CT.nil ⟨(2585/512), (2595/512), 10, true, (356771293/10000000000000)⟩ CT.nil)) ⟨(2585/512), (20771/4096), 10, true, (356014641/10000000000000)⟩ (CT.node (CT.node CT.nil ⟨(2585/512), (5195/1024), 10, true, (71079411/2000000000000)⟩ CT.nil) ⟨(2585/512), (325/64), 10, true, (354029429/10000000000000)⟩ (CT.node CT.nil ⟨(2585/512), (2605/512), 10, true, (43914233/1250000000000)⟩ CT.nil)))) ⟨(2585/512), (1305/256), 10, true, (43578037/1250000000000)⟩ (CT.node (CT.node (CT.node (CT.node CT.nil ⟨(10341/2048), (20753/4096), 10, true, (183435743/5000000000000)⟩ CT.nil) ⟨(10341/2048), (20793/4096), 10, true, (364051049/10000000000000)⟩ (CT.node CT.nil ⟨(10341/2048), (2603/512), 10, true, (1130887/31250000000)⟩ CT.nil)) ⟨(10341/2048), (163/32), 10, true, (14364449/400000000000)⟩ (CT.node (CT.node CT.nil ⟨(10343/2048), (5217/1024), 10, true, (189012269/5000000000000)⟩ CT.nil) ⟨(10345/2048), (10365/2048), 10, true, (408431653/10000000000000)⟩ (CT.node CT.nil ⟨(10345/2048), (5185/1024), 10, true, (407642947/10000000000000)⟩ CT.nil))) ⟨(20691/4096), (41493/8192), 10, true, (51531267/1250000000000)⟩ (CT.node (CT.node (CT.node CT.nil ⟨(20691/4096), (10381/2048), 10, true, (82203603/2000000000000)⟩ CT.nil) ⟨(20691/4096), (10391/2048), 10, true, (409434977/10000000000000)⟩ (CT.node CT.nil ⟨(20693/4096), (1299/256), 10, true, (209768083/5000000000000)⟩ CT.nil)) ⟨(5175/1024), (5185/1024), 10, true, (460336147/10000000000000)⟩ (CT.node (CT.node CT.nil ⟨(5175/1024), (10375/2048), 10, true, (11486191/250000000000)⟩ CT.nil) ⟨(5175/1024), (2595/512), 10, true, (458561277/10000000000000)⟩ CT.nil)))))

def tab14 : CT :=
  (CT.node (CT.node (CT.node (CT.node (CT.node (CT.node CT.nil ⟨(5175/1024), (325/64), 10, true, (91007427/2000000000000)⟩ CT.nil) ⟨(5175/1024), (20811/4096), 10, true, (227036969/5000000000000)⟩ (CT.node CT.nil ⟨(5175/1024), (2623/512), 10, true, (439255509/10000000000000)⟩ CT.nil)) ⟨(5175/1024), (2633/512), 10, true, (432607663/10000000000000)⟩ (CT.node (CT.node CT.nil ⟨(10351/2048), (41515/8192), 10, true, (23483423/500000000000)⟩ CT.nil) ⟨(647/128), (20795/4096), 10, true, (238608519/5000000000000)⟩ (CT.node CT.nil ⟨(647/128), (10423/2048), 10, true, (236277491/5000000000000)⟩ CT.nil))) ⟨(41413/8192), (10381/2048), 10, true, (494198099/10000000000000)⟩ (CT.node (CT.node (CT.node CT.nil ⟨(5177/1024), (41/8), 10, true, (480942433/10000000000000)⟩ CT.nil) ⟨(10355/2048), (10375/2048), 10, true, (103046413/2000000000000)⟩ (CT.node CT.nil ⟨(10355/2048), (2595/512), 10, true, (257119041/5000000000000)⟩ CT.nil)) ⟨(20711/4096), (41533/8192), 10, true, (519328881/10000000000000)⟩ (CT.node (CT.node CT.nil ⟨(20711/4096), (10391/2048), 10, true, (32361139/625000000000)⟩ CT.nil) ⟨(20713/4096), (1299/256), 10, true, (529106123/10000000000000)⟩ (CT.node CT.nil ⟨(20713/4096), (2603/512), 10, true, (13126113/250000000000)⟩ CT.nil)))) ⟨(41435/8192), (20773/4096), 10, true, (69585763/1250000000000)⟩ (CT.node (CT.node (CT.node (CT.node CT.nil ⟨(1295/256), (10385/2048), 10, true, (571992483/10000000000000)⟩ CT.nil) ⟨(1295/256), (5195/1024), 10, true, (114178013/2000000000000)⟩ (CT.node CT.nil ⟨(1295/256), (325/64), 10, true, (568693187/10000000000000)⟩ CT.nil)) ⟨(1295/256), (5205/1024), 10, true, (566506871/10000000000000)⟩ (CT.node (CT.node CT.nil ⟨(1295/256), (2605/512), 10, true, (112866211/2000000000000)⟩ CT.nil) ⟨(1295/256), (1305/256), 10, true, (560010683/10000000000000)⟩ (CT.node CT.nil ⟨(1295/256), (2615/512), 10, true, (69466449/1250000000000)⟩ CT.nil))) ⟨(1295/256), (655/128), 10, true, (551493311/10000000000000)⟩ (CT.node (CT.node (CT.node CT.nil ⟨(1295/256), (1315/256), 10, true, (108627463/2000000000000)⟩ CT.nil) ⟨(1295/256), (165/32), 10, true, (534939039/10000000000000)⟩ (CT.node CT.nil ⟨(10361/2048), (41555/8192), 10, true, (11665557/200000000000)⟩ CT.nil)) ⟨(10361/2048), (20793/4096), 10, true, (581537173/10000000000000)⟩ (CT.node (CT.node CT.nil ⟨(10361/2048), (20813/4096), 10, true, (144825181/2500000000000)⟩ CT.nil) ⟨(10361/2048), (163/32), 10, true, (57364627/1000000000000)⟩ (CT.node CT.nil ⟨(10361/2048), (2613/512), 10, true, (569259631/10000000000000)⟩ CT.nil))))) ⟨(5181/1024), (20815/4096), 10, true, (147807153/2500000000000)⟩ (CT.node (CT.node (CT.node (CT.node (CT.node CT.nil ⟨(10363/2048), (5217/1024), 10, true, (298692789/5000000000000)⟩ CT.nil) ⟨(10363/2048), (5227/1024), 10, true, (592818281/10000000000000)⟩ (CT.node CT.nil ⟨(41453/8192), (10391/2048), 10, true, (15261593/250000000000)⟩ CT.nil)) ⟨(10365/2048), (5195/1024), 10, true, (316344203/5000000000000)⟩ (CT.node (CT.node CT.nil ⟨(20731/4096), (10401/2048), 10, true, (318168869/5000000000000)⟩ CT.nil) ⟨(20731/4096), (10421/2048), 10, true, (63145721/1000000000000)⟩ (CT.node CT.nil ⟨(20733/4096), (41577/8192), 10, true, (650776829/10000000000000)⟩ CT.nil))) ⟨(20735/4096), (10423/2048), 10, true, (82047199/1250000000000)⟩ (CT.node (CT.node (CT.node CT.nil ⟨(41475/8192), (20793/4096), 10, true, (5435249/80000000000)⟩ CT.nil) ⟨(5185/1024), (325/64), 10, true, (694962061/10000000000000)⟩ (CT.node CT.nil ⟨(5185/1024), (5205/1024), 10, true, (692290309/10000000000000)⟩ CT.nil)) ⟨(5185/1024), (2605/512), 10, true, (68963139/1000000000000)⟩ (CT.node (CT.node CT.nil ⟨(5185/1024), (10441/2048), 10, true, (342044549/5000000000000)⟩ CT.nil) ⟨(5185/1024), (10461/2048), 10, true, (339431207/5000000000000)⟩ (CT.node CT.nil ⟨(10371/2048), (41595/8192), 10, true, (354311107/5000000000000)⟩ CT.nil)))) ⟨(10371/2048), (20813/4096), 10, true, (706509509/10000000000000)⟩ (CT.node (CT.node (CT.node (CT.node CT.nil ⟨(2593/512), (20815/4096), 10, true, (359821577/5000000000000)⟩ CT.nil) ⟨(2593/512), (10443/2048), 10, true, (709888559/10000000000000)⟩ (CT.node CT.nil ⟨(2593/512), (5257/1024), 10, true, (345435191/5000000000000)⟩ CT.nil)) ⟨(2593/512), (5277/1024), 10, true, (340218131/5000000000000)⟩ (CT.node (CT.node CT.nil ⟨(2593/512), (333/64), 10, true, (327353763/5000000000000)⟩ CT.nil) ⟨(2593/512), (671/128), 10, true, (635374807/10000000000000)⟩ (CT.node CT.nil ⟨(41497/8192), (5201/1024), 10, true, (751854739/10000000000000)⟩ CT.nil))) ⟨(20753/4096), (41617/8192), 10, true, (782495959/10000000000000)⟩ (CT.node (CT.node (CT.node CT.nil ⟨(20753/4096), (2603/512), 10, true, (780164241/10000000000000)⟩ CT.nil) ⟨(20753/4096), (5211/1024), 10, true, (155433679/2000000000000)⟩ (CT.node CT.nil ⟨(41515/8192), (20813/4096), 10, true, (50857271/625000000000)⟩ CT.nil)) ⟨(2595/512), (5205/1024), 10, true, (830590517/10000000000000)⟩ (CT.node (CT.node CT.nil ⟨(2595/512), (2605/512), 10, true, (827400419/10000000000000)⟩ CT.nil) ⟨(2595/512), (5215/1024), 10, true, (824225629/10000000000000)⟩ CT.nil)))))

def tab15 : CT :=
  (CT.node (CT.node (CT.node (CT.node (CT.node (CT.node CT.nil ⟨(2595/512), (2615/512), 10, true, (814792219/10000000000000)⟩ CT.nil) ⟨(2595/512), (655/128), 10, true, (404289107/5000000000000)⟩ (CT.node CT.nil ⟨(2595/512), (21/4), 10, true, (18241731/250000000000)⟩ CT.nil)) ⟨(10381/2048), (20833/4096), 10, true, (168599037/2000000000000)⟩ (CT.node (CT.node CT.nil ⟨(10381/2048), (20873/4096), 10, true, (418269633/5000000000000)⟩ CT.nil) ⟨(10381/2048), (2613/512), 10, true, (831578409/10000000000000)⟩ (CT.node CT.nil ⟨(10381/2048), (1309/256), 10, true, (165046307/2000000000000)⟩ CT.nil))) ⟨(5191/1024), (20835/4096), 10, true, (214317369/2500000000000)⟩ (CT.node (CT.node (CT.node CT.nil ⟨(10383/2048), (5227/1024), 10, true, (429927023/5000000000000)⟩ CT.nil) ⟨(10383/2048), (5237/1024), 10, true, (853292617/10000000000000)⟩ (CT.node CT.nil ⟨(41537/8192), (2603/512), 10, true, (55778547/625000000000)⟩ CT.nil)) ⟨(20773/4096), (5211/1024), 10, true, (461449393/5000000000000)⟩ (CT.node (CT.node CT.nil ⟨(20773/4096), (163/32), 10, true, (459679121/5000000000000)⟩ CT.nil) ⟨(20775/4096), (10433/2048), 10, true, (23354863/250000000000)⟩ (CT.node CT.nil ⟨(5195/1024), (5215/1024), 10, true, (486913799/5000000000000)⟩ CT.nil)))) ⟨(5195/1024), (1305/256), 10, true, (194018909/2000000000000)⟩ (CT.node (CT.node (CT.node (CT.node CT.nil ⟨(5195/1024), (2633/512), 10, true, (936576257/10000000000000)⟩ CT.nil) ⟨(5195/1024), (2653/512), 10, true, (908599599/10000000000000)⟩ (CT.node CT.nil ⟨(1299/256), (20855/4096), 10, true, (251547891/2500000000000)⟩ CT.nil)) ⟨(1299/256), (20895/4096), 10, true, (499246979/5000000000000)⟩ (CT.node (CT.node CT.nil ⟨(5197/1024), (1317/256), 10, true, (199185017/2000000000000)⟩ CT.nil) ⟨(5197/1024), (661/128), 10, true, (245228749/2500000000000)⟩ (CT.node CT.nil ⟨(20793/4096), (2613/512), 10, true, (534301079/5000000000000)⟩ CT.nil))) ⟨(20795/4096), (10443/2048), 10, true, (13608131/125000000000)⟩ (CT.node (CT.node (CT.node CT.nil ⟨(325/64), (2615/512), 10, true, (140340159/1250000000000)⟩ CT.nil) ⟨(325/64), (655/128), 10, true, (1114158849/10000000000000)⟩ (CT.node CT.nil ⟨(325/64), (1315/256), 10, true, (1097277581/10000000000000)⟩ CT.nil)) ⟨(325/64), (165/32), 10, true, (270178737/2500000000000)⟩ (CT.node (CT.node CT.nil ⟨(325/64), (665/128), 10, true, (1048517003/10000000000000)⟩ CT.nil) ⟨(325/64), (335/64), 10, true, (1017509707/10000000000000)⟩ (CT.node CT.nil ⟨(325/64), (21/4), 10, true, (502714163/5000000000000)⟩ CT.nil))))) ⟨(10401/2048), (1309/256), 10, true, (1134166649/10000000000000)⟩ (CT.node (CT.node (CT.node (CT.node (CT.node CT.nil ⟨(10401/2048), (2623/512), 10, true, (1125526841/10000000000000)⟩ CT.nil) ⟨(10403/2048), (5247/1024), 10, true, (578965893/5000000000000)⟩ (CT.node CT.nil ⟨(20815/4096), (10463/2048), 10, true, (1249238179/10000000000000)⟩ CT.nil)) ⟨(1301/256), (2673/512), 10, true, (1153447231/10000000000000)⟩ (CT.node (CT.node CT.nil ⟨(1301/256), (21/4), 10, true, (563934301/5000000000000)⟩ CT.nil) ⟨(2603/512), (10483/2048), 10, true, (1319026531/10000000000000)⟩ (CT.node CT.nil ⟨(2603/512), (5277/1024), 10, true, (641911203/5000000000000)⟩ CT.nil))) ⟨(2603/512), (5297/1024), 10, true, (252901217/2000000000000)⟩ (CT.node (CT.node (CT.node CT.nil ⟨(651/128), (2675/512), 10, true, (128184591/1000000000000)⟩ CT.nil) ⟨(651/128), (21/4), 10, true, (1257182497/10000000000000)⟩ (CT.node CT.nil ⟨(10423/2048), (5257/1024), 10, true, (1505067239/10000000000000)⟩ CT.nil)) ⟨(5217/1024), (661/128), 10, true, (1680579671/10000000000000)⟩ (CT.node (CT.node CT.nil ⟨(5217/1024), (333/64), 10, true, (815292227/5000000000000)⟩ CT.nil) ⟨(2613/512), (671/128), 10, true, (1934302493/10000000000000)⟩ (CT.node CT.nil ⟨(2613/512), (21/4), 10, true, (96139667/500000000000)⟩ CT.nil)))) ⟨(655/128), (21/4), 10, true, (1266297497/5000000000000)⟩ (CT.node (CT.node (CT.node (CT.node CT.nil ⟨(1313/256), (21/4), 10, true, (3116773877/10000000000000)⟩ CT.nil) ⟨(165/32), (21/4), 10, true, (2343009541/5000000000000)⟩ (CT.node CT.nil ⟨(21/4), (2693/512), 11, false, (11636772221/10000000000000)⟩ CT.nil)) ⟨(21/4), (675/128), 11, false, (5758172129/5000000000000)⟩ (CT.node (CT.node CT.nil ⟨(21/4), (1353/256), 11, false, (11414358387/10000000000000)⟩ CT.nil) ⟨(21/4), (85/16), 11, false, (1397593481/1250000000000)⟩ (CT.node CT.nil ⟨(21/4), (681/128), 11, false, (2223020503/2000000000000)⟩ CT.nil))) ⟨(21/4), (1373/256), 11, false, (2152508603/2000000000000)⟩ (CT.node (CT.node (CT.node CT.nil ⟨(21/4), (345/64), 11, false, (2636362983/2500000000000)⟩ CT.nil) ⟨(21/4), (1393/256), 11, false, (5078306397/5000000000000)⟩ (CT.node CT.nil ⟨(21/4), (175/32), 11, false, (9954658577/10000000000000)⟩ CT.nil)) ⟨(21/4), (11/2), 11, false, (2432490771/2500000000000)⟩ (CT.node (CT.node CT.nil ⟨(11/2), (355/64), 11, true, (21764380703/10000000000000)⟩ CT.nil) ⟨(11/2), (89/16), 11, true, (10578448877/5000000000000)⟩ CT.nil)))))

def table : CT :=
  (CT.node (CT.node (CT.node (CT.node tab0 ⟨(17/16), (73/64), 2, true, (15429929/1000000000000)⟩ tab1) ⟨(509/256), (8149/4096), 4, false, (1509609143/5000000000000)⟩ (CT.node tab2 ⟨(9/4), (5/2), 5, false, (38217750111/10000000000000)⟩ tab3)) ⟨(1547/512), (1557/512), 6, true, (231767/2000000000000)⟩ (CT.node (CT.node tab4 ⟨(97/32), (403/128), 6, true, (79711817/10000000000000)⟩ tab5) ⟨(393/128), (811/256), 6, true, (1637121129/10000000000000)⟩ (CT.node tab6 ⟨4, (4097/1024), 8, true, (11042139/1250000000000)⟩ tab7))) ⟨(515/128), (1081/256), 8, true, (23815441/10000000000000)⟩ (CT.node (CT.node (CT.node tab8 ⟨(519/128), (2091/512), 8, true, (636617867/10000000000000)⟩ tab9) ⟨(4167/1024), (4177/1024), 8, true, (1206050917/10000000000000)⟩ (CT.node tab10 ⟨(8349/2048), (8369/2048), 8, true, (1544741841/10000000000000)⟩ tab11)) ⟨(131/32), (1063/256), 8, true, (591952751/2500000000000)⟩ (CT.node (CT.node tab12 ⟨(645/128), (10345/2048), 10, true, (194122073/10000000000000)⟩ tab13) ⟨(5175/1024), (5195/1024), 10, true, (114198739/2500000000000)⟩ (CT.node tab14 ⟨(2595/512), (1305/256), 10, true, (821066057/10000000000000)⟩ tab15))))

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

theorem table_ok : table.allOk = true := by
  simp only [table, CT.allOk, tab0_ok, tab1_ok, tab2_ok, tab3_ok, tab4_ok, tab5_ok, tab6_ok, tab7_ok, tab8_ok, tab9_ok, tab10_ok, tab11_ok, tab12_ok, tab13_ok, tab14_ok, tab15_ok, Bool.true_and, Bool.and_true]
  decide +kernel

def cover : List (ℚ × ℚ × Bool) := [
  ((1/2), (3/4), true),
  ((3/4), (7/8), true),
  ((7/8), (15/16), true),
  ((15/16), (31/32), true),
  ((31/32), (63/64), true),
  ((63/64), (73/64), false),
  ((73/64), (37/32), true),
  ((37/32), (19/16), true),
  ((19/16), (5/4), true),
  ((5/4), (3/2), true),
  ((3/2), (7/4), true),
  ((7/4), (15/8), true),
  ((15/8), (121/64), true),
  ((121/64), (141/64), false),
  ((141/64), (71/32), true),
  ((71/32), (9/4), true),
  ((9/4), (5/2), true),
  ((5/2), (11/4), true),
  ((11/4), (89/32), true),
  ((89/32), (179/64), true),
  ((179/64), (105/32), false),
  ((105/32), (421/128), true),
  ((421/128), (211/64), true),
  ((211/64), (53/16), true),
  ((53/16), (27/8), true),
  ((27/8), (7/2), true),
  ((7/2), (29/8), true),
  ((29/8), (59/16), true),
  ((59/16), (237/64), true),
  ((237/64), (231/40), false)]

def bits : ℕ := 1884198863657120266743531255210328444374751531643304129970017429557488535600455132433662526568830877682558885001604257154107795748064024777446460416946410921623945793627313682796279395892621154992622911021059867615218562055123871738558337978984225683030379252448551512401959376534000000190282446877051784650396884620335182100081381783000128471292577180035591538500528339542715900729838023353414595297114673573558396689078162594703598272268266322691195748723663945182062816518429994046281169069506170864844311229304644085456882296363906545934872558898133259598875698041364065742439249953133342024330163131755455506500186754806665663979748312360868699123296235931710261340360291520074971851930261303903611809134610016151063319070548978539417929110653303886039261576482216171532978647270028005554429447037738536332747238092070025718518868515219768861233810681726586890159515872974663757338506594382025089562936356210280048112037956945475276211937157928198658530035340424185840516560505014314728326162473387354527603767394237852424948392089287364448180829350470142520787264038246877498958397901040039127487705757935662159732079423613398200568435524919299359536551752007407316146431768545018562530557138373956016047006605941888816189286864161031344240993333440412417330577449455330307539482446848030621629886114857098302713863312208388118851197289917171970868045716836913511327394397101575724433449112605642495377244746081006054564038925439255738920843950756724305523831910471848128321312846192722157478870588229345707495236017781635072408004712544185575972130170457743639416521239428584607723966445537918110727605330390529616686891066590318185855084502585435014292777289909517407957863779388091459167638986819105665453325761951482331869838419699169108942742517416301409198947936328193123182303011993509724371226514937573059257343901362014394541937348772475667923701509929543350170045834264357269278230029909144137036489175034468911531305589788462281555406185652008936464880948024552298793372746285095298679785330189144072901102443684599927690950464738433941535926017386153000032307805498122831851167003439168378816422411523334122533362584604332231647345596448138920126690803020665089189397363278294052873877838506544426221152954173531264163212446638187346079405835910015189956034630497152146783

def cQ : ℚ := 2310/1000000
def pQ : ℚ := 2500
def SQ : ℚ := (231/40)

theorem wk0 : walk4 table cQ pQ bits 64 0 ⟨(63/64), (73/64), (63/64), (73/64), (63/64), (73/64)⟩ = some 113 := by decide +kernel

theorem wk1 : walk4 table cQ pQ bits 64 113 ⟨(63/64), (73/64), (63/64), (73/64), (121/64), (141/64)⟩ = some 296 := by decide +kernel

theorem wk2 : walk4 table cQ pQ bits 64 296 ⟨(63/64), (73/64), (63/64), (73/64), (179/64), (105/32)⟩ = some 369 := by decide +kernel

theorem wk3 : walk4 table cQ pQ bits 64 369 ⟨(63/64), (73/64), (63/64), (73/64), (237/64), (231/40)⟩ = some 376 := by decide +kernel

theorem wk7 : walk4 table cQ pQ bits 61 379 ⟨(63/64), (17/16), (121/64), (63/32), (63/64), (73/64)⟩ = some 576 := by decide +kernel

theorem wk10 : walk4 table cQ pQ bits 59 578 ⟨(63/64), (131/128), (63/32), (131/64), (63/64), (17/16)⟩ = some 597 := by decide +kernel

theorem wk13 : walk4 table cQ pQ bits 57 599 ⟨(131/128), (17/16), (63/32), (257/128), (63/64), (131/128)⟩ = some 606 := by decide +kernel

theorem wk17 : walk4 table cQ pQ bits 54 609 ⟨(131/128), (267/256), (63/32), (509/256), (131/128), (267/256)⟩ = some 744 := by decide +kernel

theorem wk18 : walk4 table cQ pQ bits 54 744 ⟨(131/128), (267/256), (63/32), (509/256), (267/256), (17/16)⟩ = some 1231 := by decide +kernel

theorem wk16 : walk4 table cQ pQ bits 55 608 ⟨(131/128), (267/256), (63/32), (509/256), (131/128), (17/16)⟩ = some 1231 :=
  walk4_split table cQ pQ bits 54 608 ⟨(131/128), (267/256), (63/32), (509/256), (131/128), (17/16)⟩ 744 1231 (by decide +kernel)
    (by rw [show (⟨(131/128), (267/256), (63/32), (509/256), (131/128), (17/16)⟩ : Box).setHi (Box.widthArg ⟨(131/128), (267/256), (63/32), (509/256), (131/128), (17/16)⟩) (Box.mid ⟨(131/128), (267/256), (63/32), (509/256), (131/128), (17/16)⟩ (Box.widthArg ⟨(131/128), (267/256), (63/32), (509/256), (131/128), (17/16)⟩)) = ⟨(131/128), (267/256), (63/32), (509/256), (131/128), (267/256)⟩ from by decide +kernel]; exact wk17)
    (by rw [show (⟨(131/128), (267/256), (63/32), (509/256), (131/128), (17/16)⟩ : Box).setLo (Box.widthArg ⟨(131/128), (267/256), (63/32), (509/256), (131/128), (17/16)⟩) (Box.mid ⟨(131/128), (267/256), (63/32), (509/256), (131/128), (17/16)⟩ (Box.widthArg ⟨(131/128), (267/256), (63/32), (509/256), (131/128), (17/16)⟩)) = ⟨(131/128), (267/256), (63/32), (509/256), (267/256), (17/16)⟩ from by decide +kernel]; exact wk18)

theorem wk19 : walk4 table cQ pQ bits 55 1231 ⟨(131/128), (267/256), (509/256), (257/128), (131/128), (17/16)⟩ = some 1614 := by decide +kernel

theorem wk15 : walk4 table cQ pQ bits 56 607 ⟨(131/128), (267/256), (63/32), (257/128), (131/128), (17/16)⟩ = some 1614 :=
  walk4_split table cQ pQ bits 55 607 ⟨(131/128), (267/256), (63/32), (257/128), (131/128), (17/16)⟩ 1231 1614 (by decide +kernel)
    (by rw [show (⟨(131/128), (267/256), (63/32), (257/128), (131/128), (17/16)⟩ : Box).setHi (Box.widthArg ⟨(131/128), (267/256), (63/32), (257/128), (131/128), (17/16)⟩) (Box.mid ⟨(131/128), (267/256), (63/32), (257/128), (131/128), (17/16)⟩ (Box.widthArg ⟨(131/128), (267/256), (63/32), (257/128), (131/128), (17/16)⟩)) = ⟨(131/128), (267/256), (63/32), (509/256), (131/128), (17/16)⟩ from by decide +kernel]; exact wk16)
    (by rw [show (⟨(131/128), (267/256), (63/32), (257/128), (131/128), (17/16)⟩ : Box).setLo (Box.widthArg ⟨(131/128), (267/256), (63/32), (257/128), (131/128), (17/16)⟩) (Box.mid ⟨(131/128), (267/256), (63/32), (257/128), (131/128), (17/16)⟩ (Box.widthArg ⟨(131/128), (267/256), (63/32), (257/128), (131/128), (17/16)⟩)) = ⟨(131/128), (267/256), (509/256), (257/128), (131/128), (17/16)⟩ from by decide +kernel]; exact wk19)

theorem wk23 : walk4 table cQ pQ bits 53 1617 ⟨(267/256), (539/512), (63/32), (509/256), (131/128), (267/256)⟩ = some 2100 := by decide +kernel

theorem wk24 : walk4 table cQ pQ bits 53 2100 ⟨(539/512), (17/16), (63/32), (509/256), (131/128), (267/256)⟩ = some 2191 := by decide +kernel

theorem wk22 : walk4 table cQ pQ bits 54 1616 ⟨(267/256), (17/16), (63/32), (509/256), (131/128), (267/256)⟩ = some 2191 :=
  walk4_split table cQ pQ bits 53 1616 ⟨(267/256), (17/16), (63/32), (509/256), (131/128), (267/256)⟩ 2100 2191 (by decide +kernel)
    (by rw [show (⟨(267/256), (17/16), (63/32), (509/256), (131/128), (267/256)⟩ : Box).setHi (Box.widthArg ⟨(267/256), (17/16), (63/32), (509/256), (131/128), (267/256)⟩) (Box.mid ⟨(267/256), (17/16), (63/32), (509/256), (131/128), (267/256)⟩ (Box.widthArg ⟨(267/256), (17/16), (63/32), (509/256), (131/128), (267/256)⟩)) = ⟨(267/256), (539/512), (63/32), (509/256), (131/128), (267/256)⟩ from by decide +kernel]; exact wk23)
    (by rw [show (⟨(267/256), (17/16), (63/32), (509/256), (131/128), (267/256)⟩ : Box).setLo (Box.widthArg ⟨(267/256), (17/16), (63/32), (509/256), (131/128), (267/256)⟩) (Box.mid ⟨(267/256), (17/16), (63/32), (509/256), (131/128), (267/256)⟩ (Box.widthArg ⟨(267/256), (17/16), (63/32), (509/256), (131/128), (267/256)⟩)) = ⟨(539/512), (17/16), (63/32), (509/256), (131/128), (267/256)⟩ from by decide +kernel]; exact wk24)

theorem wk29 : walk4 table cQ pQ bits 50 2195 ⟨(267/256), (1073/1024), (63/32), (1013/512), (267/256), (539/512)⟩ = some 2486 := by decide +kernel

theorem wk30 : walk4 table cQ pQ bits 50 2486 ⟨(1073/1024), (539/512), (63/32), (1013/512), (267/256), (539/512)⟩ = some 2767 := by decide +kernel

theorem wk28 : walk4 table cQ pQ bits 51 2194 ⟨(267/256), (539/512), (63/32), (1013/512), (267/256), (539/512)⟩ = some 2767 :=
  walk4_split table cQ pQ bits 50 2194 ⟨(267/256), (539/512), (63/32), (1013/512), (267/256), (539/512)⟩ 2486 2767 (by decide +kernel)
    (by rw [show (⟨(267/256), (539/512), (63/32), (1013/512), (267/256), (539/512)⟩ : Box).setHi (Box.widthArg ⟨(267/256), (539/512), (63/32), (1013/512), (267/256), (539/512)⟩) (Box.mid ⟨(267/256), (539/512), (63/32), (1013/512), (267/256), (539/512)⟩ (Box.widthArg ⟨(267/256), (539/512), (63/32), (1013/512), (267/256), (539/512)⟩)) = ⟨(267/256), (1073/1024), (63/32), (1013/512), (267/256), (539/512)⟩ from by decide +kernel]; exact wk29)
    (by rw [show (⟨(267/256), (539/512), (63/32), (1013/512), (267/256), (539/512)⟩ : Box).setLo (Box.widthArg ⟨(267/256), (539/512), (63/32), (1013/512), (267/256), (539/512)⟩) (Box.mid ⟨(267/256), (539/512), (63/32), (1013/512), (267/256), (539/512)⟩ (Box.widthArg ⟨(267/256), (539/512), (63/32), (1013/512), (267/256), (539/512)⟩)) = ⟨(1073/1024), (539/512), (63/32), (1013/512), (267/256), (539/512)⟩ from by decide +kernel]; exact wk30)

theorem wk31 : walk4 table cQ pQ bits 51 2767 ⟨(267/256), (539/512), (63/32), (1013/512), (539/512), (17/16)⟩ = some 2832 := by decide +kernel

theorem wk27 : walk4 table cQ pQ bits 52 2193 ⟨(267/256), (539/512), (63/32), (1013/512), (267/256), (17/16)⟩ = some 2832 :=
  walk4_split table cQ pQ bits 51 2193 ⟨(267/256), (539/512), (63/32), (1013/512), (267/256), (17/16)⟩ 2767 2832 (by decide +kernel)
    (by rw [show (⟨(267/256), (539/512), (63/32), (1013/512), (267/256), (17/16)⟩ : Box).setHi (Box.widthArg ⟨(267/256), (539/512), (63/32), (1013/512), (267/256), (17/16)⟩) (Box.mid ⟨(267/256), (539/512), (63/32), (1013/512), (267/256), (17/16)⟩ (Box.widthArg ⟨(267/256), (539/512), (63/32), (1013/512), (267/256), (17/16)⟩)) = ⟨(267/256), (539/512), (63/32), (1013/512), (267/256), (539/512)⟩ from by decide +kernel]; exact wk28)
    (by rw [show (⟨(267/256), (539/512), (63/32), (1013/512), (267/256), (17/16)⟩ : Box).setLo (Box.widthArg ⟨(267/256), (539/512), (63/32), (1013/512), (267/256), (17/16)⟩) (Box.mid ⟨(267/256), (539/512), (63/32), (1013/512), (267/256), (17/16)⟩ (Box.widthArg ⟨(267/256), (539/512), (63/32), (1013/512), (267/256), (17/16)⟩)) = ⟨(267/256), (539/512), (63/32), (1013/512), (539/512), (17/16)⟩ from by decide +kernel]; exact wk31)

theorem wk36 : walk4 table cQ pQ bits 48 2836 ⟨(267/256), (1073/1024), (1013/512), (2031/1024), (267/256), (1073/1024)⟩ = some 3163 := by decide +kernel

theorem wk37 : walk4 table cQ pQ bits 48 3163 ⟨(267/256), (1073/1024), (1013/512), (2031/1024), (1073/1024), (539/512)⟩ = some 3356 := by decide +kernel

theorem wk35 : walk4 table cQ pQ bits 49 2835 ⟨(267/256), (1073/1024), (1013/512), (2031/1024), (267/256), (539/512)⟩ = some 3356 :=
  walk4_split table cQ pQ bits 48 2835 ⟨(267/256), (1073/1024), (1013/512), (2031/1024), (267/256), (539/512)⟩ 3163 3356 (by decide +kernel)
    (by rw [show (⟨(267/256), (1073/1024), (1013/512), (2031/1024), (267/256), (539/512)⟩ : Box).setHi (Box.widthArg ⟨(267/256), (1073/1024), (1013/512), (2031/1024), (267/256), (539/512)⟩) (Box.mid ⟨(267/256), (1073/1024), (1013/512), (2031/1024), (267/256), (539/512)⟩ (Box.widthArg ⟨(267/256), (1073/1024), (1013/512), (2031/1024), (267/256), (539/512)⟩)) = ⟨(267/256), (1073/1024), (1013/512), (2031/1024), (267/256), (1073/1024)⟩ from by decide +kernel]; exact wk36)
    (by rw [show (⟨(267/256), (1073/1024), (1013/512), (2031/1024), (267/256), (539/512)⟩ : Box).setLo (Box.widthArg ⟨(267/256), (1073/1024), (1013/512), (2031/1024), (267/256), (539/512)⟩) (Box.mid ⟨(267/256), (1073/1024), (1013/512), (2031/1024), (267/256), (539/512)⟩ (Box.widthArg ⟨(267/256), (1073/1024), (1013/512), (2031/1024), (267/256), (539/512)⟩)) = ⟨(267/256), (1073/1024), (1013/512), (2031/1024), (1073/1024), (539/512)⟩ from by decide +kernel]; exact wk37)

theorem wk38 : walk4 table cQ pQ bits 49 3356 ⟨(267/256), (1073/1024), (2031/1024), (509/256), (267/256), (539/512)⟩ = some 3721 := by decide +kernel

theorem wk34 : walk4 table cQ pQ bits 50 2834 ⟨(267/256), (1073/1024), (1013/512), (509/256), (267/256), (539/512)⟩ = some 3721 :=
  walk4_split table cQ pQ bits 49 2834 ⟨(267/256), (1073/1024), (1013/512), (509/256), (267/256), (539/512)⟩ 3356 3721 (by decide +kernel)
    (by rw [show (⟨(267/256), (1073/1024), (1013/512), (509/256), (267/256), (539/512)⟩ : Box).setHi (Box.widthArg ⟨(267/256), (1073/1024), (1013/512), (509/256), (267/256), (539/512)⟩) (Box.mid ⟨(267/256), (1073/1024), (1013/512), (509/256), (267/256), (539/512)⟩ (Box.widthArg ⟨(267/256), (1073/1024), (1013/512), (509/256), (267/256), (539/512)⟩)) = ⟨(267/256), (1073/1024), (1013/512), (2031/1024), (267/256), (539/512)⟩ from by decide +kernel]; exact wk35)
    (by rw [show (⟨(267/256), (1073/1024), (1013/512), (509/256), (267/256), (539/512)⟩ : Box).setLo (Box.widthArg ⟨(267/256), (1073/1024), (1013/512), (509/256), (267/256), (539/512)⟩) (Box.mid ⟨(267/256), (1073/1024), (1013/512), (509/256), (267/256), (539/512)⟩ (Box.widthArg ⟨(267/256), (1073/1024), (1013/512), (509/256), (267/256), (539/512)⟩)) = ⟨(267/256), (1073/1024), (2031/1024), (509/256), (267/256), (539/512)⟩ from by decide +kernel]; exact wk38)

theorem wk40 : walk4 table cQ pQ bits 49 3722 ⟨(1073/1024), (539/512), (1013/512), (2031/1024), (267/256), (539/512)⟩ = some 4041 := by decide +kernel

theorem wk41 : walk4 table cQ pQ bits 49 4041 ⟨(1073/1024), (539/512), (2031/1024), (509/256), (267/256), (539/512)⟩ = some 4222 := by decide +kernel

theorem wk39 : walk4 table cQ pQ bits 50 3721 ⟨(1073/1024), (539/512), (1013/512), (509/256), (267/256), (539/512)⟩ = some 4222 :=
  walk4_split table cQ pQ bits 49 3721 ⟨(1073/1024), (539/512), (1013/512), (509/256), (267/256), (539/512)⟩ 4041 4222 (by decide +kernel)
    (by rw [show (⟨(1073/1024), (539/512), (1013/512), (509/256), (267/256), (539/512)⟩ : Box).setHi (Box.widthArg ⟨(1073/1024), (539/512), (1013/512), (509/256), (267/256), (539/512)⟩) (Box.mid ⟨(1073/1024), (539/512), (1013/512), (509/256), (267/256), (539/512)⟩ (Box.widthArg ⟨(1073/1024), (539/512), (1013/512), (509/256), (267/256), (539/512)⟩)) = ⟨(1073/1024), (539/512), (1013/512), (2031/1024), (267/256), (539/512)⟩ from by decide +kernel]; exact wk40)
    (by rw [show (⟨(1073/1024), (539/512), (1013/512), (509/256), (267/256), (539/512)⟩ : Box).setLo (Box.widthArg ⟨(1073/1024), (539/512), (1013/512), (509/256), (267/256), (539/512)⟩) (Box.mid ⟨(1073/1024), (539/512), (1013/512), (509/256), (267/256), (539/512)⟩ (Box.widthArg ⟨(1073/1024), (539/512), (1013/512), (509/256), (267/256), (539/512)⟩)) = ⟨(1073/1024), (539/512), (2031/1024), (509/256), (267/256), (539/512)⟩ from by decide +kernel]; exact wk41)

theorem wk33 : walk4 table cQ pQ bits 51 2833 ⟨(267/256), (539/512), (1013/512), (509/256), (267/256), (539/512)⟩ = some 4222 :=
  walk4_split table cQ pQ bits 50 2833 ⟨(267/256), (539/512), (1013/512), (509/256), (267/256), (539/512)⟩ 3721 4222 (by decide +kernel)
    (by rw [show (⟨(267/256), (539/512), (1013/512), (509/256), (267/256), (539/512)⟩ : Box).setHi (Box.widthArg ⟨(267/256), (539/512), (1013/512), (509/256), (267/256), (539/512)⟩) (Box.mid ⟨(267/256), (539/512), (1013/512), (509/256), (267/256), (539/512)⟩ (Box.widthArg ⟨(267/256), (539/512), (1013/512), (509/256), (267/256), (539/512)⟩)) = ⟨(267/256), (1073/1024), (1013/512), (509/256), (267/256), (539/512)⟩ from by decide +kernel]; exact wk34)
    (by rw [show (⟨(267/256), (539/512), (1013/512), (509/256), (267/256), (539/512)⟩ : Box).setLo (Box.widthArg ⟨(267/256), (539/512), (1013/512), (509/256), (267/256), (539/512)⟩) (Box.mid ⟨(267/256), (539/512), (1013/512), (509/256), (267/256), (539/512)⟩ (Box.widthArg ⟨(267/256), (539/512), (1013/512), (509/256), (267/256), (539/512)⟩)) = ⟨(1073/1024), (539/512), (1013/512), (509/256), (267/256), (539/512)⟩ from by decide +kernel]; exact wk39)

theorem wk42 : walk4 table cQ pQ bits 51 4222 ⟨(267/256), (539/512), (1013/512), (509/256), (539/512), (17/16)⟩ = some 4301 := by decide +kernel

theorem wk32 : walk4 table cQ pQ bits 52 2832 ⟨(267/256), (539/512), (1013/512), (509/256), (267/256), (17/16)⟩ = some 4301 :=
  walk4_split table cQ pQ bits 51 2832 ⟨(267/256), (539/512), (1013/512), (509/256), (267/256), (17/16)⟩ 4222 4301 (by decide +kernel)
    (by rw [show (⟨(267/256), (539/512), (1013/512), (509/256), (267/256), (17/16)⟩ : Box).setHi (Box.widthArg ⟨(267/256), (539/512), (1013/512), (509/256), (267/256), (17/16)⟩) (Box.mid ⟨(267/256), (539/512), (1013/512), (509/256), (267/256), (17/16)⟩ (Box.widthArg ⟨(267/256), (539/512), (1013/512), (509/256), (267/256), (17/16)⟩)) = ⟨(267/256), (539/512), (1013/512), (509/256), (267/256), (539/512)⟩ from by decide +kernel]; exact wk33)
    (by rw [show (⟨(267/256), (539/512), (1013/512), (509/256), (267/256), (17/16)⟩ : Box).setLo (Box.widthArg ⟨(267/256), (539/512), (1013/512), (509/256), (267/256), (17/16)⟩) (Box.mid ⟨(267/256), (539/512), (1013/512), (509/256), (267/256), (17/16)⟩ (Box.widthArg ⟨(267/256), (539/512), (1013/512), (509/256), (267/256), (17/16)⟩)) = ⟨(267/256), (539/512), (1013/512), (509/256), (539/512), (17/16)⟩ from by decide +kernel]; exact wk42)

theorem wk26 : walk4 table cQ pQ bits 53 2192 ⟨(267/256), (539/512), (63/32), (509/256), (267/256), (17/16)⟩ = some 4301 :=
  walk4_split table cQ pQ bits 52 2192 ⟨(267/256), (539/512), (63/32), (509/256), (267/256), (17/16)⟩ 2832 4301 (by decide +kernel)
    (by rw [show (⟨(267/256), (539/512), (63/32), (509/256), (267/256), (17/16)⟩ : Box).setHi (Box.widthArg ⟨(267/256), (539/512), (63/32), (509/256), (267/256), (17/16)⟩) (Box.mid ⟨(267/256), (539/512), (63/32), (509/256), (267/256), (17/16)⟩ (Box.widthArg ⟨(267/256), (539/512), (63/32), (509/256), (267/256), (17/16)⟩)) = ⟨(267/256), (539/512), (63/32), (1013/512), (267/256), (17/16)⟩ from by decide +kernel]; exact wk27)
    (by rw [show (⟨(267/256), (539/512), (63/32), (509/256), (267/256), (17/16)⟩ : Box).setLo (Box.widthArg ⟨(267/256), (539/512), (63/32), (509/256), (267/256), (17/16)⟩) (Box.mid ⟨(267/256), (539/512), (63/32), (509/256), (267/256), (17/16)⟩ (Box.widthArg ⟨(267/256), (539/512), (63/32), (509/256), (267/256), (17/16)⟩)) = ⟨(267/256), (539/512), (1013/512), (509/256), (267/256), (17/16)⟩ from by decide +kernel]; exact wk32)

theorem wk43 : walk4 table cQ pQ bits 53 4301 ⟨(539/512), (17/16), (63/32), (509/256), (267/256), (17/16)⟩ = some 4510 := by decide +kernel

theorem wk25 : walk4 table cQ pQ bits 54 2191 ⟨(267/256), (17/16), (63/32), (509/256), (267/256), (17/16)⟩ = some 4510 :=
  walk4_split table cQ pQ bits 53 2191 ⟨(267/256), (17/16), (63/32), (509/256), (267/256), (17/16)⟩ 4301 4510 (by decide +kernel)
    (by rw [show (⟨(267/256), (17/16), (63/32), (509/256), (267/256), (17/16)⟩ : Box).setHi (Box.widthArg ⟨(267/256), (17/16), (63/32), (509/256), (267/256), (17/16)⟩) (Box.mid ⟨(267/256), (17/16), (63/32), (509/256), (267/256), (17/16)⟩ (Box.widthArg ⟨(267/256), (17/16), (63/32), (509/256), (267/256), (17/16)⟩)) = ⟨(267/256), (539/512), (63/32), (509/256), (267/256), (17/16)⟩ from by decide +kernel]; exact wk26)
    (by rw [show (⟨(267/256), (17/16), (63/32), (509/256), (267/256), (17/16)⟩ : Box).setLo (Box.widthArg ⟨(267/256), (17/16), (63/32), (509/256), (267/256), (17/16)⟩) (Box.mid ⟨(267/256), (17/16), (63/32), (509/256), (267/256), (17/16)⟩ (Box.widthArg ⟨(267/256), (17/16), (63/32), (509/256), (267/256), (17/16)⟩)) = ⟨(539/512), (17/16), (63/32), (509/256), (267/256), (17/16)⟩ from by decide +kernel]; exact wk43)

theorem wk21 : walk4 table cQ pQ bits 55 1615 ⟨(267/256), (17/16), (63/32), (509/256), (131/128), (17/16)⟩ = some 4510 :=
  walk4_split table cQ pQ bits 54 1615 ⟨(267/256), (17/16), (63/32), (509/256), (131/128), (17/16)⟩ 2191 4510 (by decide +kernel)
    (by rw [show (⟨(267/256), (17/16), (63/32), (509/256), (131/128), (17/16)⟩ : Box).setHi (Box.widthArg ⟨(267/256), (17/16), (63/32), (509/256), (131/128), (17/16)⟩) (Box.mid ⟨(267/256), (17/16), (63/32), (509/256), (131/128), (17/16)⟩ (Box.widthArg ⟨(267/256), (17/16), (63/32), (509/256), (131/128), (17/16)⟩)) = ⟨(267/256), (17/16), (63/32), (509/256), (131/128), (267/256)⟩ from by decide +kernel]; exact wk22)
    (by rw [show (⟨(267/256), (17/16), (63/32), (509/256), (131/128), (17/16)⟩ : Box).setLo (Box.widthArg ⟨(267/256), (17/16), (63/32), (509/256), (131/128), (17/16)⟩) (Box.mid ⟨(267/256), (17/16), (63/32), (509/256), (131/128), (17/16)⟩ (Box.widthArg ⟨(267/256), (17/16), (63/32), (509/256), (131/128), (17/16)⟩)) = ⟨(267/256), (17/16), (63/32), (509/256), (267/256), (17/16)⟩ from by decide +kernel]; exact wk25)

theorem wk45 : walk4 table cQ pQ bits 54 4511 ⟨(267/256), (17/16), (509/256), (257/128), (131/128), (267/256)⟩ = some 4782 := by decide +kernel

theorem wk46 : walk4 table cQ pQ bits 54 4782 ⟨(267/256), (17/16), (509/256), (257/128), (267/256), (17/16)⟩ = some 5119 := by decide +kernel

theorem wk44 : walk4 table cQ pQ bits 55 4510 ⟨(267/256), (17/16), (509/256), (257/128), (131/128), (17/16)⟩ = some 5119 :=
  walk4_split table cQ pQ bits 54 4510 ⟨(267/256), (17/16), (509/256), (257/128), (131/128), (17/16)⟩ 4782 5119 (by decide +kernel)
    (by rw [show (⟨(267/256), (17/16), (509/256), (257/128), (131/128), (17/16)⟩ : Box).setHi (Box.widthArg ⟨(267/256), (17/16), (509/256), (257/128), (131/128), (17/16)⟩) (Box.mid ⟨(267/256), (17/16), (509/256), (257/128), (131/128), (17/16)⟩ (Box.widthArg ⟨(267/256), (17/16), (509/256), (257/128), (131/128), (17/16)⟩)) = ⟨(267/256), (17/16), (509/256), (257/128), (131/128), (267/256)⟩ from by decide +kernel]; exact wk45)
    (by rw [show (⟨(267/256), (17/16), (509/256), (257/128), (131/128), (17/16)⟩ : Box).setLo (Box.widthArg ⟨(267/256), (17/16), (509/256), (257/128), (131/128), (17/16)⟩) (Box.mid ⟨(267/256), (17/16), (509/256), (257/128), (131/128), (17/16)⟩ (Box.widthArg ⟨(267/256), (17/16), (509/256), (257/128), (131/128), (17/16)⟩)) = ⟨(267/256), (17/16), (509/256), (257/128), (267/256), (17/16)⟩ from by decide +kernel]; exact wk46)

theorem wk20 : walk4 table cQ pQ bits 56 1614 ⟨(267/256), (17/16), (63/32), (257/128), (131/128), (17/16)⟩ = some 5119 :=
  walk4_split table cQ pQ bits 55 1614 ⟨(267/256), (17/16), (63/32), (257/128), (131/128), (17/16)⟩ 4510 5119 (by decide +kernel)
    (by rw [show (⟨(267/256), (17/16), (63/32), (257/128), (131/128), (17/16)⟩ : Box).setHi (Box.widthArg ⟨(267/256), (17/16), (63/32), (257/128), (131/128), (17/16)⟩) (Box.mid ⟨(267/256), (17/16), (63/32), (257/128), (131/128), (17/16)⟩ (Box.widthArg ⟨(267/256), (17/16), (63/32), (257/128), (131/128), (17/16)⟩)) = ⟨(267/256), (17/16), (63/32), (509/256), (131/128), (17/16)⟩ from by decide +kernel]; exact wk21)
    (by rw [show (⟨(267/256), (17/16), (63/32), (257/128), (131/128), (17/16)⟩ : Box).setLo (Box.widthArg ⟨(267/256), (17/16), (63/32), (257/128), (131/128), (17/16)⟩) (Box.mid ⟨(267/256), (17/16), (63/32), (257/128), (131/128), (17/16)⟩ (Box.widthArg ⟨(267/256), (17/16), (63/32), (257/128), (131/128), (17/16)⟩)) = ⟨(267/256), (17/16), (509/256), (257/128), (131/128), (17/16)⟩ from by decide +kernel]; exact wk44)

theorem wk14 : walk4 table cQ pQ bits 57 606 ⟨(131/128), (17/16), (63/32), (257/128), (131/128), (17/16)⟩ = some 5119 :=
  walk4_split table cQ pQ bits 56 606 ⟨(131/128), (17/16), (63/32), (257/128), (131/128), (17/16)⟩ 1614 5119 (by decide +kernel)
    (by rw [show (⟨(131/128), (17/16), (63/32), (257/128), (131/128), (17/16)⟩ : Box).setHi (Box.widthArg ⟨(131/128), (17/16), (63/32), (257/128), (131/128), (17/16)⟩) (Box.mid ⟨(131/128), (17/16), (63/32), (257/128), (131/128), (17/16)⟩ (Box.widthArg ⟨(131/128), (17/16), (63/32), (257/128), (131/128), (17/16)⟩)) = ⟨(131/128), (267/256), (63/32), (257/128), (131/128), (17/16)⟩ from by decide +kernel]; exact wk15)
    (by rw [show (⟨(131/128), (17/16), (63/32), (257/128), (131/128), (17/16)⟩ : Box).setLo (Box.widthArg ⟨(131/128), (17/16), (63/32), (257/128), (131/128), (17/16)⟩) (Box.mid ⟨(131/128), (17/16), (63/32), (257/128), (131/128), (17/16)⟩ (Box.widthArg ⟨(131/128), (17/16), (63/32), (257/128), (131/128), (17/16)⟩)) = ⟨(267/256), (17/16), (63/32), (257/128), (131/128), (17/16)⟩ from by decide +kernel]; exact wk20)

theorem wk12 : walk4 table cQ pQ bits 58 598 ⟨(131/128), (17/16), (63/32), (257/128), (63/64), (17/16)⟩ = some 5119 :=
  walk4_split table cQ pQ bits 57 598 ⟨(131/128), (17/16), (63/32), (257/128), (63/64), (17/16)⟩ 606 5119 (by decide +kernel)
    (by rw [show (⟨(131/128), (17/16), (63/32), (257/128), (63/64), (17/16)⟩ : Box).setHi (Box.widthArg ⟨(131/128), (17/16), (63/32), (257/128), (63/64), (17/16)⟩) (Box.mid ⟨(131/128), (17/16), (63/32), (257/128), (63/64), (17/16)⟩ (Box.widthArg ⟨(131/128), (17/16), (63/32), (257/128), (63/64), (17/16)⟩)) = ⟨(131/128), (17/16), (63/32), (257/128), (63/64), (131/128)⟩ from by decide +kernel]; exact wk13)
    (by rw [show (⟨(131/128), (17/16), (63/32), (257/128), (63/64), (17/16)⟩ : Box).setLo (Box.widthArg ⟨(131/128), (17/16), (63/32), (257/128), (63/64), (17/16)⟩) (Box.mid ⟨(131/128), (17/16), (63/32), (257/128), (63/64), (17/16)⟩ (Box.widthArg ⟨(131/128), (17/16), (63/32), (257/128), (63/64), (17/16)⟩)) = ⟨(131/128), (17/16), (63/32), (257/128), (131/128), (17/16)⟩ from by decide +kernel]; exact wk14)

theorem wk47 : walk4 table cQ pQ bits 58 5119 ⟨(131/128), (17/16), (257/128), (131/64), (63/64), (17/16)⟩ = some 5200 := by decide +kernel

theorem wk11 : walk4 table cQ pQ bits 59 597 ⟨(131/128), (17/16), (63/32), (131/64), (63/64), (17/16)⟩ = some 5200 :=
  walk4_split table cQ pQ bits 58 597 ⟨(131/128), (17/16), (63/32), (131/64), (63/64), (17/16)⟩ 5119 5200 (by decide +kernel)
    (by rw [show (⟨(131/128), (17/16), (63/32), (131/64), (63/64), (17/16)⟩ : Box).setHi (Box.widthArg ⟨(131/128), (17/16), (63/32), (131/64), (63/64), (17/16)⟩) (Box.mid ⟨(131/128), (17/16), (63/32), (131/64), (63/64), (17/16)⟩ (Box.widthArg ⟨(131/128), (17/16), (63/32), (131/64), (63/64), (17/16)⟩)) = ⟨(131/128), (17/16), (63/32), (257/128), (63/64), (17/16)⟩ from by decide +kernel]; exact wk12)
    (by rw [show (⟨(131/128), (17/16), (63/32), (131/64), (63/64), (17/16)⟩ : Box).setLo (Box.widthArg ⟨(131/128), (17/16), (63/32), (131/64), (63/64), (17/16)⟩) (Box.mid ⟨(131/128), (17/16), (63/32), (131/64), (63/64), (17/16)⟩ (Box.widthArg ⟨(131/128), (17/16), (63/32), (131/64), (63/64), (17/16)⟩)) = ⟨(131/128), (17/16), (257/128), (131/64), (63/64), (17/16)⟩ from by decide +kernel]; exact wk47)

theorem wk9 : walk4 table cQ pQ bits 60 577 ⟨(63/64), (17/16), (63/32), (131/64), (63/64), (17/16)⟩ = some 5200 :=
  walk4_split table cQ pQ bits 59 577 ⟨(63/64), (17/16), (63/32), (131/64), (63/64), (17/16)⟩ 597 5200 (by decide +kernel)
    (by rw [show (⟨(63/64), (17/16), (63/32), (131/64), (63/64), (17/16)⟩ : Box).setHi (Box.widthArg ⟨(63/64), (17/16), (63/32), (131/64), (63/64), (17/16)⟩) (Box.mid ⟨(63/64), (17/16), (63/32), (131/64), (63/64), (17/16)⟩ (Box.widthArg ⟨(63/64), (17/16), (63/32), (131/64), (63/64), (17/16)⟩)) = ⟨(63/64), (131/128), (63/32), (131/64), (63/64), (17/16)⟩ from by decide +kernel]; exact wk10)
    (by rw [show (⟨(63/64), (17/16), (63/32), (131/64), (63/64), (17/16)⟩ : Box).setLo (Box.widthArg ⟨(63/64), (17/16), (63/32), (131/64), (63/64), (17/16)⟩) (Box.mid ⟨(63/64), (17/16), (63/32), (131/64), (63/64), (17/16)⟩ (Box.widthArg ⟨(63/64), (17/16), (63/32), (131/64), (63/64), (17/16)⟩)) = ⟨(131/128), (17/16), (63/32), (131/64), (63/64), (17/16)⟩ from by decide +kernel]; exact wk11)

theorem wk48 : walk4 table cQ pQ bits 60 5200 ⟨(63/64), (17/16), (63/32), (131/64), (17/16), (73/64)⟩ = some 5265 := by decide +kernel

theorem wk8 : walk4 table cQ pQ bits 61 576 ⟨(63/64), (17/16), (63/32), (131/64), (63/64), (73/64)⟩ = some 5265 :=
  walk4_split table cQ pQ bits 60 576 ⟨(63/64), (17/16), (63/32), (131/64), (63/64), (73/64)⟩ 5200 5265 (by decide +kernel)
    (by rw [show (⟨(63/64), (17/16), (63/32), (131/64), (63/64), (73/64)⟩ : Box).setHi (Box.widthArg ⟨(63/64), (17/16), (63/32), (131/64), (63/64), (73/64)⟩) (Box.mid ⟨(63/64), (17/16), (63/32), (131/64), (63/64), (73/64)⟩ (Box.widthArg ⟨(63/64), (17/16), (63/32), (131/64), (63/64), (73/64)⟩)) = ⟨(63/64), (17/16), (63/32), (131/64), (63/64), (17/16)⟩ from by decide +kernel]; exact wk9)
    (by rw [show (⟨(63/64), (17/16), (63/32), (131/64), (63/64), (73/64)⟩ : Box).setLo (Box.widthArg ⟨(63/64), (17/16), (63/32), (131/64), (63/64), (73/64)⟩) (Box.mid ⟨(63/64), (17/16), (63/32), (131/64), (63/64), (73/64)⟩ (Box.widthArg ⟨(63/64), (17/16), (63/32), (131/64), (63/64), (73/64)⟩)) = ⟨(63/64), (17/16), (63/32), (131/64), (17/16), (73/64)⟩ from by decide +kernel]; exact wk48)

theorem wk6 : walk4 table cQ pQ bits 62 378 ⟨(63/64), (17/16), (121/64), (131/64), (63/64), (73/64)⟩ = some 5265 :=
  walk4_split table cQ pQ bits 61 378 ⟨(63/64), (17/16), (121/64), (131/64), (63/64), (73/64)⟩ 576 5265 (by decide +kernel)
    (by rw [show (⟨(63/64), (17/16), (121/64), (131/64), (63/64), (73/64)⟩ : Box).setHi (Box.widthArg ⟨(63/64), (17/16), (121/64), (131/64), (63/64), (73/64)⟩) (Box.mid ⟨(63/64), (17/16), (121/64), (131/64), (63/64), (73/64)⟩ (Box.widthArg ⟨(63/64), (17/16), (121/64), (131/64), (63/64), (73/64)⟩)) = ⟨(63/64), (17/16), (121/64), (63/32), (63/64), (73/64)⟩ from by decide +kernel]; exact wk7)
    (by rw [show (⟨(63/64), (17/16), (121/64), (131/64), (63/64), (73/64)⟩ : Box).setLo (Box.widthArg ⟨(63/64), (17/16), (121/64), (131/64), (63/64), (73/64)⟩) (Box.mid ⟨(63/64), (17/16), (121/64), (131/64), (63/64), (73/64)⟩ (Box.widthArg ⟨(63/64), (17/16), (121/64), (131/64), (63/64), (73/64)⟩)) = ⟨(63/64), (17/16), (63/32), (131/64), (63/64), (73/64)⟩ from by decide +kernel]; exact wk8)

theorem wk49 : walk4 table cQ pQ bits 62 5265 ⟨(17/16), (73/64), (121/64), (131/64), (63/64), (73/64)⟩ = some 5388 := by decide +kernel

theorem wk5 : walk4 table cQ pQ bits 63 377 ⟨(63/64), (73/64), (121/64), (131/64), (63/64), (73/64)⟩ = some 5388 :=
  walk4_split table cQ pQ bits 62 377 ⟨(63/64), (73/64), (121/64), (131/64), (63/64), (73/64)⟩ 5265 5388 (by decide +kernel)
    (by rw [show (⟨(63/64), (73/64), (121/64), (131/64), (63/64), (73/64)⟩ : Box).setHi (Box.widthArg ⟨(63/64), (73/64), (121/64), (131/64), (63/64), (73/64)⟩) (Box.mid ⟨(63/64), (73/64), (121/64), (131/64), (63/64), (73/64)⟩ (Box.widthArg ⟨(63/64), (73/64), (121/64), (131/64), (63/64), (73/64)⟩)) = ⟨(63/64), (17/16), (121/64), (131/64), (63/64), (73/64)⟩ from by decide +kernel]; exact wk6)
    (by rw [show (⟨(63/64), (73/64), (121/64), (131/64), (63/64), (73/64)⟩ : Box).setLo (Box.widthArg ⟨(63/64), (73/64), (121/64), (131/64), (63/64), (73/64)⟩) (Box.mid ⟨(63/64), (73/64), (121/64), (131/64), (63/64), (73/64)⟩ (Box.widthArg ⟨(63/64), (73/64), (121/64), (131/64), (63/64), (73/64)⟩)) = ⟨(17/16), (73/64), (121/64), (131/64), (63/64), (73/64)⟩ from by decide +kernel]; exact wk49)

theorem wk50 : walk4 table cQ pQ bits 63 5388 ⟨(63/64), (73/64), (131/64), (141/64), (63/64), (73/64)⟩ = some 5405 := by decide +kernel

theorem wk4 : walk4 table cQ pQ bits 64 376 ⟨(63/64), (73/64), (121/64), (141/64), (63/64), (73/64)⟩ = some 5405 :=
  walk4_split table cQ pQ bits 63 376 ⟨(63/64), (73/64), (121/64), (141/64), (63/64), (73/64)⟩ 5388 5405 (by decide +kernel)
    (by rw [show (⟨(63/64), (73/64), (121/64), (141/64), (63/64), (73/64)⟩ : Box).setHi (Box.widthArg ⟨(63/64), (73/64), (121/64), (141/64), (63/64), (73/64)⟩) (Box.mid ⟨(63/64), (73/64), (121/64), (141/64), (63/64), (73/64)⟩ (Box.widthArg ⟨(63/64), (73/64), (121/64), (141/64), (63/64), (73/64)⟩)) = ⟨(63/64), (73/64), (121/64), (131/64), (63/64), (73/64)⟩ from by decide +kernel]; exact wk5)
    (by rw [show (⟨(63/64), (73/64), (121/64), (141/64), (63/64), (73/64)⟩ : Box).setLo (Box.widthArg ⟨(63/64), (73/64), (121/64), (141/64), (63/64), (73/64)⟩) (Box.mid ⟨(63/64), (73/64), (121/64), (141/64), (63/64), (73/64)⟩ (Box.widthArg ⟨(63/64), (73/64), (121/64), (141/64), (63/64), (73/64)⟩)) = ⟨(63/64), (73/64), (131/64), (141/64), (63/64), (73/64)⟩ from by decide +kernel]; exact wk50)

theorem wk52 : walk4 table cQ pQ bits 63 5406 ⟨(63/64), (73/64), (121/64), (131/64), (121/64), (141/64)⟩ = some 5893 := by decide +kernel

theorem wk53 : walk4 table cQ pQ bits 63 5893 ⟨(63/64), (73/64), (131/64), (141/64), (121/64), (141/64)⟩ = some 5910 := by decide +kernel

theorem wk51 : walk4 table cQ pQ bits 64 5405 ⟨(63/64), (73/64), (121/64), (141/64), (121/64), (141/64)⟩ = some 5910 :=
  walk4_split table cQ pQ bits 63 5405 ⟨(63/64), (73/64), (121/64), (141/64), (121/64), (141/64)⟩ 5893 5910 (by decide +kernel)
    (by rw [show (⟨(63/64), (73/64), (121/64), (141/64), (121/64), (141/64)⟩ : Box).setHi (Box.widthArg ⟨(63/64), (73/64), (121/64), (141/64), (121/64), (141/64)⟩) (Box.mid ⟨(63/64), (73/64), (121/64), (141/64), (121/64), (141/64)⟩ (Box.widthArg ⟨(63/64), (73/64), (121/64), (141/64), (121/64), (141/64)⟩)) = ⟨(63/64), (73/64), (121/64), (131/64), (121/64), (141/64)⟩ from by decide +kernel]; exact wk52)
    (by rw [show (⟨(63/64), (73/64), (121/64), (141/64), (121/64), (141/64)⟩ : Box).setLo (Box.widthArg ⟨(63/64), (73/64), (121/64), (141/64), (121/64), (141/64)⟩) (Box.mid ⟨(63/64), (73/64), (121/64), (141/64), (121/64), (141/64)⟩ (Box.widthArg ⟨(63/64), (73/64), (121/64), (141/64), (121/64), (141/64)⟩)) = ⟨(63/64), (73/64), (131/64), (141/64), (121/64), (141/64)⟩ from by decide +kernel]; exact wk53)

theorem wk54 : walk4 table cQ pQ bits 64 5910 ⟨(63/64), (73/64), (121/64), (141/64), (179/64), (105/32)⟩ = some 5917 := by decide +kernel

theorem wk55 : walk4 table cQ pQ bits 64 5917 ⟨(63/64), (73/64), (121/64), (141/64), (237/64), (231/40)⟩ = some 5918 := by decide +kernel

theorem wk56 : walk4 table cQ pQ bits 64 5918 ⟨(63/64), (73/64), (179/64), (105/32), (63/64), (73/64)⟩ = some 6293 := by decide +kernel

theorem wk57 : walk4 table cQ pQ bits 64 6293 ⟨(63/64), (73/64), (179/64), (105/32), (121/64), (141/64)⟩ = some 6300 := by decide +kernel

theorem wk58 : walk4 table cQ pQ bits 64 6300 ⟨(63/64), (73/64), (179/64), (105/32), (179/64), (105/32)⟩ = some 6301 := by decide +kernel

theorem wk59 : walk4 table cQ pQ bits 64 6301 ⟨(63/64), (73/64), (179/64), (105/32), (237/64), (231/40)⟩ = some 6302 := by decide +kernel

theorem wk60 : walk4 table cQ pQ bits 64 6302 ⟨(63/64), (73/64), (237/64), (231/40), (63/64), (73/64)⟩ = some 6309 := by decide +kernel

theorem wk61 : walk4 table cQ pQ bits 64 6309 ⟨(63/64), (73/64), (237/64), (231/40), (121/64), (141/64)⟩ = some 6310 := by decide +kernel

theorem wk62 : walk4 table cQ pQ bits 64 6310 ⟨(63/64), (73/64), (237/64), (231/40), (179/64), (105/32)⟩ = some 6311 := by decide +kernel

theorem wk63 : walk4 table cQ pQ bits 64 6311 ⟨(63/64), (73/64), (237/64), (231/40), (237/64), (231/40)⟩ = some 6312 := by decide +kernel

theorem wk64 : walk4 table cQ pQ bits 64 6312 ⟨(121/64), (141/64), (63/64), (73/64), (63/64), (73/64)⟩ = some 6543 := by decide +kernel

theorem wk65 : walk4 table cQ pQ bits 64 6543 ⟨(121/64), (141/64), (63/64), (73/64), (121/64), (141/64)⟩ = some 6836 := by decide +kernel

theorem wk66 : walk4 table cQ pQ bits 64 6836 ⟨(121/64), (141/64), (63/64), (73/64), (179/64), (105/32)⟩ = some 6843 := by decide +kernel

theorem wk67 : walk4 table cQ pQ bits 64 6843 ⟨(121/64), (141/64), (63/64), (73/64), (237/64), (231/40)⟩ = some 6844 := by decide +kernel

theorem wk71 : walk4 table cQ pQ bits 61 6847 ⟨(121/64), (63/32), (121/64), (131/64), (63/64), (73/64)⟩ = some 6848 := by decide +kernel

theorem wk73 : walk4 table cQ pQ bits 60 6849 ⟨(63/32), (131/64), (121/64), (63/32), (63/64), (73/64)⟩ = some 6850 := by decide +kernel

theorem wk76 : walk4 table cQ pQ bits 58 6852 ⟨(63/32), (257/128), (63/32), (131/64), (63/64), (17/16)⟩ = some 7051 := by decide +kernel

theorem wk77 : walk4 table cQ pQ bits 58 7051 ⟨(257/128), (131/64), (63/32), (131/64), (63/64), (17/16)⟩ = some 7382 := by decide +kernel

theorem wk75 : walk4 table cQ pQ bits 59 6851 ⟨(63/32), (131/64), (63/32), (131/64), (63/64), (17/16)⟩ = some 7382 :=
  walk4_split table cQ pQ bits 58 6851 ⟨(63/32), (131/64), (63/32), (131/64), (63/64), (17/16)⟩ 7051 7382 (by decide +kernel)
    (by rw [show (⟨(63/32), (131/64), (63/32), (131/64), (63/64), (17/16)⟩ : Box).setHi (Box.widthArg ⟨(63/32), (131/64), (63/32), (131/64), (63/64), (17/16)⟩) (Box.mid ⟨(63/32), (131/64), (63/32), (131/64), (63/64), (17/16)⟩ (Box.widthArg ⟨(63/32), (131/64), (63/32), (131/64), (63/64), (17/16)⟩)) = ⟨(63/32), (257/128), (63/32), (131/64), (63/64), (17/16)⟩ from by decide +kernel]; exact wk76)
    (by rw [show (⟨(63/32), (131/64), (63/32), (131/64), (63/64), (17/16)⟩ : Box).setLo (Box.widthArg ⟨(63/32), (131/64), (63/32), (131/64), (63/64), (17/16)⟩) (Box.mid ⟨(63/32), (131/64), (63/32), (131/64), (63/64), (17/16)⟩ (Box.widthArg ⟨(63/32), (131/64), (63/32), (131/64), (63/64), (17/16)⟩)) = ⟨(257/128), (131/64), (63/32), (131/64), (63/64), (17/16)⟩ from by decide +kernel]; exact wk77)

theorem wk78 : walk4 table cQ pQ bits 59 7382 ⟨(63/32), (131/64), (63/32), (131/64), (17/16), (73/64)⟩ = some 7427 := by decide +kernel

theorem wk74 : walk4 table cQ pQ bits 60 6850 ⟨(63/32), (131/64), (63/32), (131/64), (63/64), (73/64)⟩ = some 7427 :=
  walk4_split table cQ pQ bits 59 6850 ⟨(63/32), (131/64), (63/32), (131/64), (63/64), (73/64)⟩ 7382 7427 (by decide +kernel)
    (by rw [show (⟨(63/32), (131/64), (63/32), (131/64), (63/64), (73/64)⟩ : Box).setHi (Box.widthArg ⟨(63/32), (131/64), (63/32), (131/64), (63/64), (73/64)⟩) (Box.mid ⟨(63/32), (131/64), (63/32), (131/64), (63/64), (73/64)⟩ (Box.widthArg ⟨(63/32), (131/64), (63/32), (131/64), (63/64), (73/64)⟩)) = ⟨(63/32), (131/64), (63/32), (131/64), (63/64), (17/16)⟩ from by decide +kernel]; exact wk75)
    (by rw [show (⟨(63/32), (131/64), (63/32), (131/64), (63/64), (73/64)⟩ : Box).setLo (Box.widthArg ⟨(63/32), (131/64), (63/32), (131/64), (63/64), (73/64)⟩) (Box.mid ⟨(63/32), (131/64), (63/32), (131/64), (63/64), (73/64)⟩ (Box.widthArg ⟨(63/32), (131/64), (63/32), (131/64), (63/64), (73/64)⟩)) = ⟨(63/32), (131/64), (63/32), (131/64), (17/16), (73/64)⟩ from by decide +kernel]; exact wk78)

theorem wk72 : walk4 table cQ pQ bits 61 6848 ⟨(63/32), (131/64), (121/64), (131/64), (63/64), (73/64)⟩ = some 7427 :=
  walk4_split table cQ pQ bits 60 6848 ⟨(63/32), (131/64), (121/64), (131/64), (63/64), (73/64)⟩ 6850 7427 (by decide +kernel)
    (by rw [show (⟨(63/32), (131/64), (121/64), (131/64), (63/64), (73/64)⟩ : Box).setHi (Box.widthArg ⟨(63/32), (131/64), (121/64), (131/64), (63/64), (73/64)⟩) (Box.mid ⟨(63/32), (131/64), (121/64), (131/64), (63/64), (73/64)⟩ (Box.widthArg ⟨(63/32), (131/64), (121/64), (131/64), (63/64), (73/64)⟩)) = ⟨(63/32), (131/64), (121/64), (63/32), (63/64), (73/64)⟩ from by decide +kernel]; exact wk73)
    (by rw [show (⟨(63/32), (131/64), (121/64), (131/64), (63/64), (73/64)⟩ : Box).setLo (Box.widthArg ⟨(63/32), (131/64), (121/64), (131/64), (63/64), (73/64)⟩) (Box.mid ⟨(63/32), (131/64), (121/64), (131/64), (63/64), (73/64)⟩ (Box.widthArg ⟨(63/32), (131/64), (121/64), (131/64), (63/64), (73/64)⟩)) = ⟨(63/32), (131/64), (63/32), (131/64), (63/64), (73/64)⟩ from by decide +kernel]; exact wk74)

theorem wk70 : walk4 table cQ pQ bits 62 6846 ⟨(121/64), (131/64), (121/64), (131/64), (63/64), (73/64)⟩ = some 7427 :=
  walk4_split table cQ pQ bits 61 6846 ⟨(121/64), (131/64), (121/64), (131/64), (63/64), (73/64)⟩ 6848 7427 (by decide +kernel)
    (by rw [show (⟨(121/64), (131/64), (121/64), (131/64), (63/64), (73/64)⟩ : Box).setHi (Box.widthArg ⟨(121/64), (131/64), (121/64), (131/64), (63/64), (73/64)⟩) (Box.mid ⟨(121/64), (131/64), (121/64), (131/64), (63/64), (73/64)⟩ (Box.widthArg ⟨(121/64), (131/64), (121/64), (131/64), (63/64), (73/64)⟩)) = ⟨(121/64), (63/32), (121/64), (131/64), (63/64), (73/64)⟩ from by decide +kernel]; exact wk71)
    (by rw [show (⟨(121/64), (131/64), (121/64), (131/64), (63/64), (73/64)⟩ : Box).setLo (Box.widthArg ⟨(121/64), (131/64), (121/64), (131/64), (63/64), (73/64)⟩) (Box.mid ⟨(121/64), (131/64), (121/64), (131/64), (63/64), (73/64)⟩ (Box.widthArg ⟨(121/64), (131/64), (121/64), (131/64), (63/64), (73/64)⟩)) = ⟨(63/32), (131/64), (121/64), (131/64), (63/64), (73/64)⟩ from by decide +kernel]; exact wk72)

theorem wk79 : walk4 table cQ pQ bits 62 7427 ⟨(121/64), (131/64), (131/64), (141/64), (63/64), (73/64)⟩ = some 7446 := by decide +kernel

theorem wk69 : walk4 table cQ pQ bits 63 6845 ⟨(121/64), (131/64), (121/64), (141/64), (63/64), (73/64)⟩ = some 7446 :=
  walk4_split table cQ pQ bits 62 6845 ⟨(121/64), (131/64), (121/64), (141/64), (63/64), (73/64)⟩ 7427 7446 (by decide +kernel)
    (by rw [show (⟨(121/64), (131/64), (121/64), (141/64), (63/64), (73/64)⟩ : Box).setHi (Box.widthArg ⟨(121/64), (131/64), (121/64), (141/64), (63/64), (73/64)⟩) (Box.mid ⟨(121/64), (131/64), (121/64), (141/64), (63/64), (73/64)⟩ (Box.widthArg ⟨(121/64), (131/64), (121/64), (141/64), (63/64), (73/64)⟩)) = ⟨(121/64), (131/64), (121/64), (131/64), (63/64), (73/64)⟩ from by decide +kernel]; exact wk70)
    (by rw [show (⟨(121/64), (131/64), (121/64), (141/64), (63/64), (73/64)⟩ : Box).setLo (Box.widthArg ⟨(121/64), (131/64), (121/64), (141/64), (63/64), (73/64)⟩) (Box.mid ⟨(121/64), (131/64), (121/64), (141/64), (63/64), (73/64)⟩ (Box.widthArg ⟨(121/64), (131/64), (121/64), (141/64), (63/64), (73/64)⟩)) = ⟨(121/64), (131/64), (131/64), (141/64), (63/64), (73/64)⟩ from by decide +kernel]; exact wk79)

theorem wk80 : walk4 table cQ pQ bits 63 7446 ⟨(131/64), (141/64), (121/64), (141/64), (63/64), (73/64)⟩ = some 7475 := by decide +kernel

theorem wk68 : walk4 table cQ pQ bits 64 6844 ⟨(121/64), (141/64), (121/64), (141/64), (63/64), (73/64)⟩ = some 7475 :=
  walk4_split table cQ pQ bits 63 6844 ⟨(121/64), (141/64), (121/64), (141/64), (63/64), (73/64)⟩ 7446 7475 (by decide +kernel)
    (by rw [show (⟨(121/64), (141/64), (121/64), (141/64), (63/64), (73/64)⟩ : Box).setHi (Box.widthArg ⟨(121/64), (141/64), (121/64), (141/64), (63/64), (73/64)⟩) (Box.mid ⟨(121/64), (141/64), (121/64), (141/64), (63/64), (73/64)⟩ (Box.widthArg ⟨(121/64), (141/64), (121/64), (141/64), (63/64), (73/64)⟩)) = ⟨(121/64), (131/64), (121/64), (141/64), (63/64), (73/64)⟩ from by decide +kernel]; exact wk69)
    (by rw [show (⟨(121/64), (141/64), (121/64), (141/64), (63/64), (73/64)⟩ : Box).setLo (Box.widthArg ⟨(121/64), (141/64), (121/64), (141/64), (63/64), (73/64)⟩) (Box.mid ⟨(121/64), (141/64), (121/64), (141/64), (63/64), (73/64)⟩ (Box.widthArg ⟨(121/64), (141/64), (121/64), (141/64), (63/64), (73/64)⟩)) = ⟨(131/64), (141/64), (121/64), (141/64), (63/64), (73/64)⟩ from by decide +kernel]; exact wk80)

theorem wk81 : walk4 table cQ pQ bits 64 7475 ⟨(121/64), (141/64), (121/64), (141/64), (121/64), (141/64)⟩ = some 7486 := by decide +kernel

theorem wk82 : walk4 table cQ pQ bits 64 7486 ⟨(121/64), (141/64), (121/64), (141/64), (179/64), (105/32)⟩ = some 7487 := by decide +kernel

theorem wk83 : walk4 table cQ pQ bits 64 7487 ⟨(121/64), (141/64), (121/64), (141/64), (237/64), (231/40)⟩ = some 7488 := by decide +kernel

theorem wk84 : walk4 table cQ pQ bits 64 7488 ⟨(121/64), (141/64), (179/64), (105/32), (63/64), (73/64)⟩ = some 7495 := by decide +kernel

theorem wk85 : walk4 table cQ pQ bits 64 7495 ⟨(121/64), (141/64), (179/64), (105/32), (121/64), (141/64)⟩ = some 7496 := by decide +kernel

theorem wk86 : walk4 table cQ pQ bits 64 7496 ⟨(121/64), (141/64), (179/64), (105/32), (179/64), (105/32)⟩ = some 7497 := by decide +kernel

theorem wk87 : walk4 table cQ pQ bits 64 7497 ⟨(121/64), (141/64), (179/64), (105/32), (237/64), (231/40)⟩ = some 7498 := by decide +kernel

theorem wk88 : walk4 table cQ pQ bits 64 7498 ⟨(121/64), (141/64), (237/64), (231/40), (63/64), (73/64)⟩ = some 7499 := by decide +kernel

theorem wk89 : walk4 table cQ pQ bits 64 7499 ⟨(121/64), (141/64), (237/64), (231/40), (121/64), (141/64)⟩ = some 7500 := by decide +kernel

theorem wk90 : walk4 table cQ pQ bits 64 7500 ⟨(121/64), (141/64), (237/64), (231/40), (179/64), (105/32)⟩ = some 7501 := by decide +kernel

theorem wk91 : walk4 table cQ pQ bits 64 7501 ⟨(121/64), (141/64), (237/64), (231/40), (237/64), (231/40)⟩ = some 7502 := by decide +kernel

theorem wk92 : walk4 table cQ pQ bits 64 7502 ⟨(179/64), (105/32), (63/64), (73/64), (63/64), (73/64)⟩ = some 7575 := by decide +kernel

theorem wk93 : walk4 table cQ pQ bits 64 7575 ⟨(179/64), (105/32), (63/64), (73/64), (121/64), (141/64)⟩ = some 7582 := by decide +kernel

theorem wk94 : walk4 table cQ pQ bits 64 7582 ⟨(179/64), (105/32), (63/64), (73/64), (179/64), (105/32)⟩ = some 7583 := by decide +kernel

theorem wk95 : walk4 table cQ pQ bits 64 7583 ⟨(179/64), (105/32), (63/64), (73/64), (237/64), (231/40)⟩ = some 7584 := by decide +kernel

theorem wk96 : walk4 table cQ pQ bits 64 7584 ⟨(179/64), (105/32), (121/64), (141/64), (63/64), (73/64)⟩ = some 7591 := by decide +kernel

theorem wk97 : walk4 table cQ pQ bits 64 7591 ⟨(179/64), (105/32), (121/64), (141/64), (121/64), (141/64)⟩ = some 7592 := by decide +kernel

theorem wk98 : walk4 table cQ pQ bits 64 7592 ⟨(179/64), (105/32), (121/64), (141/64), (179/64), (105/32)⟩ = some 7593 := by decide +kernel

theorem wk99 : walk4 table cQ pQ bits 64 7593 ⟨(179/64), (105/32), (121/64), (141/64), (237/64), (231/40)⟩ = some 7594 := by decide +kernel

theorem wk100 : walk4 table cQ pQ bits 64 7594 ⟨(179/64), (105/32), (179/64), (105/32), (63/64), (73/64)⟩ = some 7595 := by decide +kernel

theorem wk101 : walk4 table cQ pQ bits 64 7595 ⟨(179/64), (105/32), (179/64), (105/32), (121/64), (141/64)⟩ = some 7596 := by decide +kernel

theorem wk102 : walk4 table cQ pQ bits 64 7596 ⟨(179/64), (105/32), (179/64), (105/32), (179/64), (105/32)⟩ = some 7597 := by decide +kernel

theorem wk103 : walk4 table cQ pQ bits 64 7597 ⟨(179/64), (105/32), (179/64), (105/32), (237/64), (231/40)⟩ = some 7598 := by decide +kernel

theorem wk104 : walk4 table cQ pQ bits 64 7598 ⟨(179/64), (105/32), (237/64), (231/40), (63/64), (73/64)⟩ = some 7599 := by decide +kernel

theorem wk105 : walk4 table cQ pQ bits 64 7599 ⟨(179/64), (105/32), (237/64), (231/40), (121/64), (141/64)⟩ = some 7600 := by decide +kernel

theorem wk106 : walk4 table cQ pQ bits 64 7600 ⟨(179/64), (105/32), (237/64), (231/40), (179/64), (105/32)⟩ = some 7601 := by decide +kernel

theorem wk107 : walk4 table cQ pQ bits 64 7601 ⟨(179/64), (105/32), (237/64), (231/40), (237/64), (231/40)⟩ = some 7602 := by decide +kernel

theorem wk108 : walk4 table cQ pQ bits 64 7602 ⟨(237/64), (231/40), (63/64), (73/64), (63/64), (73/64)⟩ = some 7609 := by decide +kernel

theorem wk109 : walk4 table cQ pQ bits 64 7609 ⟨(237/64), (231/40), (63/64), (73/64), (121/64), (141/64)⟩ = some 7610 := by decide +kernel

theorem wk110 : walk4 table cQ pQ bits 64 7610 ⟨(237/64), (231/40), (63/64), (73/64), (179/64), (105/32)⟩ = some 7611 := by decide +kernel

theorem wk111 : walk4 table cQ pQ bits 64 7611 ⟨(237/64), (231/40), (63/64), (73/64), (237/64), (231/40)⟩ = some 7612 := by decide +kernel

theorem wk112 : walk4 table cQ pQ bits 64 7612 ⟨(237/64), (231/40), (121/64), (141/64), (63/64), (73/64)⟩ = some 7613 := by decide +kernel

theorem wk113 : walk4 table cQ pQ bits 64 7613 ⟨(237/64), (231/40), (121/64), (141/64), (121/64), (141/64)⟩ = some 7614 := by decide +kernel

theorem wk114 : walk4 table cQ pQ bits 64 7614 ⟨(237/64), (231/40), (121/64), (141/64), (179/64), (105/32)⟩ = some 7615 := by decide +kernel

theorem wk115 : walk4 table cQ pQ bits 64 7615 ⟨(237/64), (231/40), (121/64), (141/64), (237/64), (231/40)⟩ = some 7616 := by decide +kernel

theorem wk116 : walk4 table cQ pQ bits 64 7616 ⟨(237/64), (231/40), (179/64), (105/32), (63/64), (73/64)⟩ = some 7617 := by decide +kernel

theorem wk117 : walk4 table cQ pQ bits 64 7617 ⟨(237/64), (231/40), (179/64), (105/32), (121/64), (141/64)⟩ = some 7618 := by decide +kernel

theorem wk118 : walk4 table cQ pQ bits 64 7618 ⟨(237/64), (231/40), (179/64), (105/32), (179/64), (105/32)⟩ = some 7619 := by decide +kernel

theorem wk119 : walk4 table cQ pQ bits 64 7619 ⟨(237/64), (231/40), (179/64), (105/32), (237/64), (231/40)⟩ = some 7620 := by decide +kernel

theorem wk120 : walk4 table cQ pQ bits 64 7620 ⟨(237/64), (231/40), (237/64), (231/40), (63/64), (73/64)⟩ = some 7621 := by decide +kernel

theorem wk121 : walk4 table cQ pQ bits 64 7621 ⟨(237/64), (231/40), (237/64), (231/40), (121/64), (141/64)⟩ = some 7622 := by decide +kernel

theorem wk122 : walk4 table cQ pQ bits 64 7622 ⟨(237/64), (231/40), (237/64), (231/40), (179/64), (105/32)⟩ = some 7623 := by decide +kernel

theorem wk123 : walk4 table cQ pQ bits 64 7623 ⟨(237/64), (231/40), (237/64), (231/40), (237/64), (231/40)⟩ = some 7624 := by decide +kernel

theorem nb_eq : (badOf5 cover).length = 4 := by decide +kernel

theorem root_000 : walk4 table cQ pQ bits 64 0 (boxOf4 (badOf5 cover) 0 0 0) = some 113 := by
  rw [show boxOf4 (badOf5 cover) 0 0 0 = ⟨(63/64), (73/64), (63/64), (73/64), (63/64), (73/64)⟩ from by decide +kernel]; exact wk0

theorem root_001 : walk4 table cQ pQ bits 64 113 (boxOf4 (badOf5 cover) 0 0 1) = some 296 := by
  rw [show boxOf4 (badOf5 cover) 0 0 1 = ⟨(63/64), (73/64), (63/64), (73/64), (121/64), (141/64)⟩ from by decide +kernel]; exact wk1

theorem root_002 : walk4 table cQ pQ bits 64 296 (boxOf4 (badOf5 cover) 0 0 2) = some 369 := by
  rw [show boxOf4 (badOf5 cover) 0 0 2 = ⟨(63/64), (73/64), (63/64), (73/64), (179/64), (105/32)⟩ from by decide +kernel]; exact wk2

theorem root_003 : walk4 table cQ pQ bits 64 369 (boxOf4 (badOf5 cover) 0 0 3) = some 376 := by
  rw [show boxOf4 (badOf5 cover) 0 0 3 = ⟨(63/64), (73/64), (63/64), (73/64), (237/64), (231/40)⟩ from by decide +kernel]; exact wk3

theorem root_010 : walk4 table cQ pQ bits 64 376 (boxOf4 (badOf5 cover) 0 1 0) = some 5405 := by
  rw [show boxOf4 (badOf5 cover) 0 1 0 = ⟨(63/64), (73/64), (121/64), (141/64), (63/64), (73/64)⟩ from by decide +kernel]; exact wk4

theorem root_011 : walk4 table cQ pQ bits 64 5405 (boxOf4 (badOf5 cover) 0 1 1) = some 5910 := by
  rw [show boxOf4 (badOf5 cover) 0 1 1 = ⟨(63/64), (73/64), (121/64), (141/64), (121/64), (141/64)⟩ from by decide +kernel]; exact wk51

theorem root_012 : walk4 table cQ pQ bits 64 5910 (boxOf4 (badOf5 cover) 0 1 2) = some 5917 := by
  rw [show boxOf4 (badOf5 cover) 0 1 2 = ⟨(63/64), (73/64), (121/64), (141/64), (179/64), (105/32)⟩ from by decide +kernel]; exact wk54

theorem root_013 : walk4 table cQ pQ bits 64 5917 (boxOf4 (badOf5 cover) 0 1 3) = some 5918 := by
  rw [show boxOf4 (badOf5 cover) 0 1 3 = ⟨(63/64), (73/64), (121/64), (141/64), (237/64), (231/40)⟩ from by decide +kernel]; exact wk55

theorem root_020 : walk4 table cQ pQ bits 64 5918 (boxOf4 (badOf5 cover) 0 2 0) = some 6293 := by
  rw [show boxOf4 (badOf5 cover) 0 2 0 = ⟨(63/64), (73/64), (179/64), (105/32), (63/64), (73/64)⟩ from by decide +kernel]; exact wk56

theorem root_021 : walk4 table cQ pQ bits 64 6293 (boxOf4 (badOf5 cover) 0 2 1) = some 6300 := by
  rw [show boxOf4 (badOf5 cover) 0 2 1 = ⟨(63/64), (73/64), (179/64), (105/32), (121/64), (141/64)⟩ from by decide +kernel]; exact wk57

theorem root_022 : walk4 table cQ pQ bits 64 6300 (boxOf4 (badOf5 cover) 0 2 2) = some 6301 := by
  rw [show boxOf4 (badOf5 cover) 0 2 2 = ⟨(63/64), (73/64), (179/64), (105/32), (179/64), (105/32)⟩ from by decide +kernel]; exact wk58

theorem root_023 : walk4 table cQ pQ bits 64 6301 (boxOf4 (badOf5 cover) 0 2 3) = some 6302 := by
  rw [show boxOf4 (badOf5 cover) 0 2 3 = ⟨(63/64), (73/64), (179/64), (105/32), (237/64), (231/40)⟩ from by decide +kernel]; exact wk59

theorem root_030 : walk4 table cQ pQ bits 64 6302 (boxOf4 (badOf5 cover) 0 3 0) = some 6309 := by
  rw [show boxOf4 (badOf5 cover) 0 3 0 = ⟨(63/64), (73/64), (237/64), (231/40), (63/64), (73/64)⟩ from by decide +kernel]; exact wk60

theorem root_031 : walk4 table cQ pQ bits 64 6309 (boxOf4 (badOf5 cover) 0 3 1) = some 6310 := by
  rw [show boxOf4 (badOf5 cover) 0 3 1 = ⟨(63/64), (73/64), (237/64), (231/40), (121/64), (141/64)⟩ from by decide +kernel]; exact wk61

theorem root_032 : walk4 table cQ pQ bits 64 6310 (boxOf4 (badOf5 cover) 0 3 2) = some 6311 := by
  rw [show boxOf4 (badOf5 cover) 0 3 2 = ⟨(63/64), (73/64), (237/64), (231/40), (179/64), (105/32)⟩ from by decide +kernel]; exact wk62

theorem root_033 : walk4 table cQ pQ bits 64 6311 (boxOf4 (badOf5 cover) 0 3 3) = some 6312 := by
  rw [show boxOf4 (badOf5 cover) 0 3 3 = ⟨(63/64), (73/64), (237/64), (231/40), (237/64), (231/40)⟩ from by decide +kernel]; exact wk63

theorem root_100 : walk4 table cQ pQ bits 64 6312 (boxOf4 (badOf5 cover) 1 0 0) = some 6543 := by
  rw [show boxOf4 (badOf5 cover) 1 0 0 = ⟨(121/64), (141/64), (63/64), (73/64), (63/64), (73/64)⟩ from by decide +kernel]; exact wk64

theorem root_101 : walk4 table cQ pQ bits 64 6543 (boxOf4 (badOf5 cover) 1 0 1) = some 6836 := by
  rw [show boxOf4 (badOf5 cover) 1 0 1 = ⟨(121/64), (141/64), (63/64), (73/64), (121/64), (141/64)⟩ from by decide +kernel]; exact wk65

theorem root_102 : walk4 table cQ pQ bits 64 6836 (boxOf4 (badOf5 cover) 1 0 2) = some 6843 := by
  rw [show boxOf4 (badOf5 cover) 1 0 2 = ⟨(121/64), (141/64), (63/64), (73/64), (179/64), (105/32)⟩ from by decide +kernel]; exact wk66

theorem root_103 : walk4 table cQ pQ bits 64 6843 (boxOf4 (badOf5 cover) 1 0 3) = some 6844 := by
  rw [show boxOf4 (badOf5 cover) 1 0 3 = ⟨(121/64), (141/64), (63/64), (73/64), (237/64), (231/40)⟩ from by decide +kernel]; exact wk67

theorem root_110 : walk4 table cQ pQ bits 64 6844 (boxOf4 (badOf5 cover) 1 1 0) = some 7475 := by
  rw [show boxOf4 (badOf5 cover) 1 1 0 = ⟨(121/64), (141/64), (121/64), (141/64), (63/64), (73/64)⟩ from by decide +kernel]; exact wk68

theorem root_111 : walk4 table cQ pQ bits 64 7475 (boxOf4 (badOf5 cover) 1 1 1) = some 7486 := by
  rw [show boxOf4 (badOf5 cover) 1 1 1 = ⟨(121/64), (141/64), (121/64), (141/64), (121/64), (141/64)⟩ from by decide +kernel]; exact wk81

theorem root_112 : walk4 table cQ pQ bits 64 7486 (boxOf4 (badOf5 cover) 1 1 2) = some 7487 := by
  rw [show boxOf4 (badOf5 cover) 1 1 2 = ⟨(121/64), (141/64), (121/64), (141/64), (179/64), (105/32)⟩ from by decide +kernel]; exact wk82

theorem root_113 : walk4 table cQ pQ bits 64 7487 (boxOf4 (badOf5 cover) 1 1 3) = some 7488 := by
  rw [show boxOf4 (badOf5 cover) 1 1 3 = ⟨(121/64), (141/64), (121/64), (141/64), (237/64), (231/40)⟩ from by decide +kernel]; exact wk83

theorem root_120 : walk4 table cQ pQ bits 64 7488 (boxOf4 (badOf5 cover) 1 2 0) = some 7495 := by
  rw [show boxOf4 (badOf5 cover) 1 2 0 = ⟨(121/64), (141/64), (179/64), (105/32), (63/64), (73/64)⟩ from by decide +kernel]; exact wk84

theorem root_121 : walk4 table cQ pQ bits 64 7495 (boxOf4 (badOf5 cover) 1 2 1) = some 7496 := by
  rw [show boxOf4 (badOf5 cover) 1 2 1 = ⟨(121/64), (141/64), (179/64), (105/32), (121/64), (141/64)⟩ from by decide +kernel]; exact wk85

theorem root_122 : walk4 table cQ pQ bits 64 7496 (boxOf4 (badOf5 cover) 1 2 2) = some 7497 := by
  rw [show boxOf4 (badOf5 cover) 1 2 2 = ⟨(121/64), (141/64), (179/64), (105/32), (179/64), (105/32)⟩ from by decide +kernel]; exact wk86

theorem root_123 : walk4 table cQ pQ bits 64 7497 (boxOf4 (badOf5 cover) 1 2 3) = some 7498 := by
  rw [show boxOf4 (badOf5 cover) 1 2 3 = ⟨(121/64), (141/64), (179/64), (105/32), (237/64), (231/40)⟩ from by decide +kernel]; exact wk87

theorem root_130 : walk4 table cQ pQ bits 64 7498 (boxOf4 (badOf5 cover) 1 3 0) = some 7499 := by
  rw [show boxOf4 (badOf5 cover) 1 3 0 = ⟨(121/64), (141/64), (237/64), (231/40), (63/64), (73/64)⟩ from by decide +kernel]; exact wk88

theorem root_131 : walk4 table cQ pQ bits 64 7499 (boxOf4 (badOf5 cover) 1 3 1) = some 7500 := by
  rw [show boxOf4 (badOf5 cover) 1 3 1 = ⟨(121/64), (141/64), (237/64), (231/40), (121/64), (141/64)⟩ from by decide +kernel]; exact wk89

theorem root_132 : walk4 table cQ pQ bits 64 7500 (boxOf4 (badOf5 cover) 1 3 2) = some 7501 := by
  rw [show boxOf4 (badOf5 cover) 1 3 2 = ⟨(121/64), (141/64), (237/64), (231/40), (179/64), (105/32)⟩ from by decide +kernel]; exact wk90

theorem root_133 : walk4 table cQ pQ bits 64 7501 (boxOf4 (badOf5 cover) 1 3 3) = some 7502 := by
  rw [show boxOf4 (badOf5 cover) 1 3 3 = ⟨(121/64), (141/64), (237/64), (231/40), (237/64), (231/40)⟩ from by decide +kernel]; exact wk91

theorem root_200 : walk4 table cQ pQ bits 64 7502 (boxOf4 (badOf5 cover) 2 0 0) = some 7575 := by
  rw [show boxOf4 (badOf5 cover) 2 0 0 = ⟨(179/64), (105/32), (63/64), (73/64), (63/64), (73/64)⟩ from by decide +kernel]; exact wk92

theorem root_201 : walk4 table cQ pQ bits 64 7575 (boxOf4 (badOf5 cover) 2 0 1) = some 7582 := by
  rw [show boxOf4 (badOf5 cover) 2 0 1 = ⟨(179/64), (105/32), (63/64), (73/64), (121/64), (141/64)⟩ from by decide +kernel]; exact wk93

theorem root_202 : walk4 table cQ pQ bits 64 7582 (boxOf4 (badOf5 cover) 2 0 2) = some 7583 := by
  rw [show boxOf4 (badOf5 cover) 2 0 2 = ⟨(179/64), (105/32), (63/64), (73/64), (179/64), (105/32)⟩ from by decide +kernel]; exact wk94

theorem root_203 : walk4 table cQ pQ bits 64 7583 (boxOf4 (badOf5 cover) 2 0 3) = some 7584 := by
  rw [show boxOf4 (badOf5 cover) 2 0 3 = ⟨(179/64), (105/32), (63/64), (73/64), (237/64), (231/40)⟩ from by decide +kernel]; exact wk95

theorem root_210 : walk4 table cQ pQ bits 64 7584 (boxOf4 (badOf5 cover) 2 1 0) = some 7591 := by
  rw [show boxOf4 (badOf5 cover) 2 1 0 = ⟨(179/64), (105/32), (121/64), (141/64), (63/64), (73/64)⟩ from by decide +kernel]; exact wk96

theorem root_211 : walk4 table cQ pQ bits 64 7591 (boxOf4 (badOf5 cover) 2 1 1) = some 7592 := by
  rw [show boxOf4 (badOf5 cover) 2 1 1 = ⟨(179/64), (105/32), (121/64), (141/64), (121/64), (141/64)⟩ from by decide +kernel]; exact wk97

theorem root_212 : walk4 table cQ pQ bits 64 7592 (boxOf4 (badOf5 cover) 2 1 2) = some 7593 := by
  rw [show boxOf4 (badOf5 cover) 2 1 2 = ⟨(179/64), (105/32), (121/64), (141/64), (179/64), (105/32)⟩ from by decide +kernel]; exact wk98

theorem root_213 : walk4 table cQ pQ bits 64 7593 (boxOf4 (badOf5 cover) 2 1 3) = some 7594 := by
  rw [show boxOf4 (badOf5 cover) 2 1 3 = ⟨(179/64), (105/32), (121/64), (141/64), (237/64), (231/40)⟩ from by decide +kernel]; exact wk99

theorem root_220 : walk4 table cQ pQ bits 64 7594 (boxOf4 (badOf5 cover) 2 2 0) = some 7595 := by
  rw [show boxOf4 (badOf5 cover) 2 2 0 = ⟨(179/64), (105/32), (179/64), (105/32), (63/64), (73/64)⟩ from by decide +kernel]; exact wk100

theorem root_221 : walk4 table cQ pQ bits 64 7595 (boxOf4 (badOf5 cover) 2 2 1) = some 7596 := by
  rw [show boxOf4 (badOf5 cover) 2 2 1 = ⟨(179/64), (105/32), (179/64), (105/32), (121/64), (141/64)⟩ from by decide +kernel]; exact wk101

theorem root_222 : walk4 table cQ pQ bits 64 7596 (boxOf4 (badOf5 cover) 2 2 2) = some 7597 := by
  rw [show boxOf4 (badOf5 cover) 2 2 2 = ⟨(179/64), (105/32), (179/64), (105/32), (179/64), (105/32)⟩ from by decide +kernel]; exact wk102

theorem root_223 : walk4 table cQ pQ bits 64 7597 (boxOf4 (badOf5 cover) 2 2 3) = some 7598 := by
  rw [show boxOf4 (badOf5 cover) 2 2 3 = ⟨(179/64), (105/32), (179/64), (105/32), (237/64), (231/40)⟩ from by decide +kernel]; exact wk103

theorem root_230 : walk4 table cQ pQ bits 64 7598 (boxOf4 (badOf5 cover) 2 3 0) = some 7599 := by
  rw [show boxOf4 (badOf5 cover) 2 3 0 = ⟨(179/64), (105/32), (237/64), (231/40), (63/64), (73/64)⟩ from by decide +kernel]; exact wk104

theorem root_231 : walk4 table cQ pQ bits 64 7599 (boxOf4 (badOf5 cover) 2 3 1) = some 7600 := by
  rw [show boxOf4 (badOf5 cover) 2 3 1 = ⟨(179/64), (105/32), (237/64), (231/40), (121/64), (141/64)⟩ from by decide +kernel]; exact wk105

theorem root_232 : walk4 table cQ pQ bits 64 7600 (boxOf4 (badOf5 cover) 2 3 2) = some 7601 := by
  rw [show boxOf4 (badOf5 cover) 2 3 2 = ⟨(179/64), (105/32), (237/64), (231/40), (179/64), (105/32)⟩ from by decide +kernel]; exact wk106

theorem root_233 : walk4 table cQ pQ bits 64 7601 (boxOf4 (badOf5 cover) 2 3 3) = some 7602 := by
  rw [show boxOf4 (badOf5 cover) 2 3 3 = ⟨(179/64), (105/32), (237/64), (231/40), (237/64), (231/40)⟩ from by decide +kernel]; exact wk107

theorem root_300 : walk4 table cQ pQ bits 64 7602 (boxOf4 (badOf5 cover) 3 0 0) = some 7609 := by
  rw [show boxOf4 (badOf5 cover) 3 0 0 = ⟨(237/64), (231/40), (63/64), (73/64), (63/64), (73/64)⟩ from by decide +kernel]; exact wk108

theorem root_301 : walk4 table cQ pQ bits 64 7609 (boxOf4 (badOf5 cover) 3 0 1) = some 7610 := by
  rw [show boxOf4 (badOf5 cover) 3 0 1 = ⟨(237/64), (231/40), (63/64), (73/64), (121/64), (141/64)⟩ from by decide +kernel]; exact wk109

theorem root_302 : walk4 table cQ pQ bits 64 7610 (boxOf4 (badOf5 cover) 3 0 2) = some 7611 := by
  rw [show boxOf4 (badOf5 cover) 3 0 2 = ⟨(237/64), (231/40), (63/64), (73/64), (179/64), (105/32)⟩ from by decide +kernel]; exact wk110

theorem root_303 : walk4 table cQ pQ bits 64 7611 (boxOf4 (badOf5 cover) 3 0 3) = some 7612 := by
  rw [show boxOf4 (badOf5 cover) 3 0 3 = ⟨(237/64), (231/40), (63/64), (73/64), (237/64), (231/40)⟩ from by decide +kernel]; exact wk111

theorem root_310 : walk4 table cQ pQ bits 64 7612 (boxOf4 (badOf5 cover) 3 1 0) = some 7613 := by
  rw [show boxOf4 (badOf5 cover) 3 1 0 = ⟨(237/64), (231/40), (121/64), (141/64), (63/64), (73/64)⟩ from by decide +kernel]; exact wk112

theorem root_311 : walk4 table cQ pQ bits 64 7613 (boxOf4 (badOf5 cover) 3 1 1) = some 7614 := by
  rw [show boxOf4 (badOf5 cover) 3 1 1 = ⟨(237/64), (231/40), (121/64), (141/64), (121/64), (141/64)⟩ from by decide +kernel]; exact wk113

theorem root_312 : walk4 table cQ pQ bits 64 7614 (boxOf4 (badOf5 cover) 3 1 2) = some 7615 := by
  rw [show boxOf4 (badOf5 cover) 3 1 2 = ⟨(237/64), (231/40), (121/64), (141/64), (179/64), (105/32)⟩ from by decide +kernel]; exact wk114

theorem root_313 : walk4 table cQ pQ bits 64 7615 (boxOf4 (badOf5 cover) 3 1 3) = some 7616 := by
  rw [show boxOf4 (badOf5 cover) 3 1 3 = ⟨(237/64), (231/40), (121/64), (141/64), (237/64), (231/40)⟩ from by decide +kernel]; exact wk115

theorem root_320 : walk4 table cQ pQ bits 64 7616 (boxOf4 (badOf5 cover) 3 2 0) = some 7617 := by
  rw [show boxOf4 (badOf5 cover) 3 2 0 = ⟨(237/64), (231/40), (179/64), (105/32), (63/64), (73/64)⟩ from by decide +kernel]; exact wk116

theorem root_321 : walk4 table cQ pQ bits 64 7617 (boxOf4 (badOf5 cover) 3 2 1) = some 7618 := by
  rw [show boxOf4 (badOf5 cover) 3 2 1 = ⟨(237/64), (231/40), (179/64), (105/32), (121/64), (141/64)⟩ from by decide +kernel]; exact wk117

theorem root_322 : walk4 table cQ pQ bits 64 7618 (boxOf4 (badOf5 cover) 3 2 2) = some 7619 := by
  rw [show boxOf4 (badOf5 cover) 3 2 2 = ⟨(237/64), (231/40), (179/64), (105/32), (179/64), (105/32)⟩ from by decide +kernel]; exact wk118

theorem root_323 : walk4 table cQ pQ bits 64 7619 (boxOf4 (badOf5 cover) 3 2 3) = some 7620 := by
  rw [show boxOf4 (badOf5 cover) 3 2 3 = ⟨(237/64), (231/40), (179/64), (105/32), (237/64), (231/40)⟩ from by decide +kernel]; exact wk119

theorem root_330 : walk4 table cQ pQ bits 64 7620 (boxOf4 (badOf5 cover) 3 3 0) = some 7621 := by
  rw [show boxOf4 (badOf5 cover) 3 3 0 = ⟨(237/64), (231/40), (237/64), (231/40), (63/64), (73/64)⟩ from by decide +kernel]; exact wk120

theorem root_331 : walk4 table cQ pQ bits 64 7621 (boxOf4 (badOf5 cover) 3 3 1) = some 7622 := by
  rw [show boxOf4 (badOf5 cover) 3 3 1 = ⟨(237/64), (231/40), (237/64), (231/40), (121/64), (141/64)⟩ from by decide +kernel]; exact wk121

theorem root_332 : walk4 table cQ pQ bits 64 7622 (boxOf4 (badOf5 cover) 3 3 2) = some 7623 := by
  rw [show boxOf4 (badOf5 cover) 3 3 2 = ⟨(237/64), (231/40), (237/64), (231/40), (179/64), (105/32)⟩ from by decide +kernel]; exact wk122

theorem root_333 : walk4 table cQ pQ bits 64 7623 (boxOf4 (badOf5 cover) 3 3 3) = some 7624 := by
  rw [show boxOf4 (badOf5 cover) 3 3 3 = ⟨(237/64), (231/40), (237/64), (231/40), (237/64), (231/40)⟩ from by decide +kernel]; exact wk123

theorem run_ok : ∀ i j k, i < (badOf5 cover).length → j < (badOf5 cover).length →
    k < (badOf5 cover).length →
    ∃ pos pos', walk4 table cQ pQ bits 64 pos (boxOf4 (badOf5 cover) i j k) = some pos' := by
  intro i j k hi hj hk
  rw [nb_eq] at hi hj hk
  match i, j, k, hi, hj, hk with
  | 0, 0, 0, _, _, _ => exact ⟨_, _, root_000⟩
  | 0, 0, 1, _, _, _ => exact ⟨_, _, root_001⟩
  | 0, 0, 2, _, _, _ => exact ⟨_, _, root_002⟩
  | 0, 0, 3, _, _, _ => exact ⟨_, _, root_003⟩
  | 0, 1, 0, _, _, _ => exact ⟨_, _, root_010⟩
  | 0, 1, 1, _, _, _ => exact ⟨_, _, root_011⟩
  | 0, 1, 2, _, _, _ => exact ⟨_, _, root_012⟩
  | 0, 1, 3, _, _, _ => exact ⟨_, _, root_013⟩
  | 0, 2, 0, _, _, _ => exact ⟨_, _, root_020⟩
  | 0, 2, 1, _, _, _ => exact ⟨_, _, root_021⟩
  | 0, 2, 2, _, _, _ => exact ⟨_, _, root_022⟩
  | 0, 2, 3, _, _, _ => exact ⟨_, _, root_023⟩
  | 0, 3, 0, _, _, _ => exact ⟨_, _, root_030⟩
  | 0, 3, 1, _, _, _ => exact ⟨_, _, root_031⟩
  | 0, 3, 2, _, _, _ => exact ⟨_, _, root_032⟩
  | 0, 3, 3, _, _, _ => exact ⟨_, _, root_033⟩
  | 1, 0, 0, _, _, _ => exact ⟨_, _, root_100⟩
  | 1, 0, 1, _, _, _ => exact ⟨_, _, root_101⟩
  | 1, 0, 2, _, _, _ => exact ⟨_, _, root_102⟩
  | 1, 0, 3, _, _, _ => exact ⟨_, _, root_103⟩
  | 1, 1, 0, _, _, _ => exact ⟨_, _, root_110⟩
  | 1, 1, 1, _, _, _ => exact ⟨_, _, root_111⟩
  | 1, 1, 2, _, _, _ => exact ⟨_, _, root_112⟩
  | 1, 1, 3, _, _, _ => exact ⟨_, _, root_113⟩
  | 1, 2, 0, _, _, _ => exact ⟨_, _, root_120⟩
  | 1, 2, 1, _, _, _ => exact ⟨_, _, root_121⟩
  | 1, 2, 2, _, _, _ => exact ⟨_, _, root_122⟩
  | 1, 2, 3, _, _, _ => exact ⟨_, _, root_123⟩
  | 1, 3, 0, _, _, _ => exact ⟨_, _, root_130⟩
  | 1, 3, 1, _, _, _ => exact ⟨_, _, root_131⟩
  | 1, 3, 2, _, _, _ => exact ⟨_, _, root_132⟩
  | 1, 3, 3, _, _, _ => exact ⟨_, _, root_133⟩
  | 2, 0, 0, _, _, _ => exact ⟨_, _, root_200⟩
  | 2, 0, 1, _, _, _ => exact ⟨_, _, root_201⟩
  | 2, 0, 2, _, _, _ => exact ⟨_, _, root_202⟩
  | 2, 0, 3, _, _, _ => exact ⟨_, _, root_203⟩
  | 2, 1, 0, _, _, _ => exact ⟨_, _, root_210⟩
  | 2, 1, 1, _, _, _ => exact ⟨_, _, root_211⟩
  | 2, 1, 2, _, _, _ => exact ⟨_, _, root_212⟩
  | 2, 1, 3, _, _, _ => exact ⟨_, _, root_213⟩
  | 2, 2, 0, _, _, _ => exact ⟨_, _, root_220⟩
  | 2, 2, 1, _, _, _ => exact ⟨_, _, root_221⟩
  | 2, 2, 2, _, _, _ => exact ⟨_, _, root_222⟩
  | 2, 2, 3, _, _, _ => exact ⟨_, _, root_223⟩
  | 2, 3, 0, _, _, _ => exact ⟨_, _, root_230⟩
  | 2, 3, 1, _, _, _ => exact ⟨_, _, root_231⟩
  | 2, 3, 2, _, _, _ => exact ⟨_, _, root_232⟩
  | 2, 3, 3, _, _, _ => exact ⟨_, _, root_233⟩
  | 3, 0, 0, _, _, _ => exact ⟨_, _, root_300⟩
  | 3, 0, 1, _, _, _ => exact ⟨_, _, root_301⟩
  | 3, 0, 2, _, _, _ => exact ⟨_, _, root_302⟩
  | 3, 0, 3, _, _, _ => exact ⟨_, _, root_303⟩
  | 3, 1, 0, _, _, _ => exact ⟨_, _, root_310⟩
  | 3, 1, 1, _, _, _ => exact ⟨_, _, root_311⟩
  | 3, 1, 2, _, _, _ => exact ⟨_, _, root_312⟩
  | 3, 1, 3, _, _, _ => exact ⟨_, _, root_313⟩
  | 3, 2, 0, _, _, _ => exact ⟨_, _, root_320⟩
  | 3, 2, 1, _, _, _ => exact ⟨_, _, root_321⟩
  | 3, 2, 2, _, _, _ => exact ⟨_, _, root_322⟩
  | 3, 2, 3, _, _, _ => exact ⟨_, _, root_323⟩
  | 3, 3, 0, _, _, _ => exact ⟨_, _, root_330⟩
  | 3, 3, 1, _, _, _ => exact ⟨_, _, root_331⟩
  | 3, 3, 2, _, _, _ => exact ⟨_, _, root_332⟩
  | 3, 3, 3, _, _, _ => exact ⟨_, _, root_333⟩
  | i + 4, _, _, hi, _, _ => exact absurd hi (by omega)
  | _, j + 4, _, _, hj, _ => exact absurd hj (by omega)
  | _, _, k + 4, _, _, hk => exact absurd hk (by omega)

theorem cover_ok : coverCheck5 table (3/2 * cQ) (1/2) SQ cover = true := by decide +kernel

theorem SQ_eq : SQ = cQ * pQ := by decide +kernel


end Zeta23Ext.Bridge.ThreePoint.FourDataB

/-! ###### the submission layer ###### -/

noncomputable section

namespace RiemannFail

open Filter
open Zeta23 Zeta23.ThmD Zeta23Ext.Bridge Zeta23Ext.BridgeW

/-- The four-point certificate from the checked table (bit-walk format). -/
theorem four_point_cert :
    ∀ g : Fin (4 - 1) → ℝ, (∀ i, 0 ≤ g i) → (2310 / 1000000 : ℝ) ≤ F 4 2500 g := by
  intro g hg
  rw [ThreePoint.F4_eq]
  have h := ThreePoint.four_point_of_check' ThreePoint.FourDataB.table ThreePoint.FourDataB.cover
    ThreePoint.FourDataB.bits 64 ThreePoint.FourDataB.cQ ThreePoint.FourDataB.pQ
    ThreePoint.FourDataB.SQ ThreePoint.FourDataB.SQ_eq (by norm_num [ThreePoint.FourDataB.pQ])
    (by norm_num [ThreePoint.FourDataB.cQ]) ThreePoint.FourDataB.table_ok ThreePoint.FourDataB.cover_ok
    ThreePoint.FourDataB.run_ok (g 0) (g 1) (g 2) (hg 0) (hg 1) (hg 2)
  unfold ThreePoint.G4 at h
  simp only [ThreePoint.FourDataB.cQ, ThreePoint.FourDataB.pQ] at h
  push_cast at h ⊢
  linarith

/-- `Phi_w' 4 (2310/10⁶) 435 (3/2500)` as an exact rational in `HD 1`. -/
theorem Phi_four_w' :
    Phi_w' 4 (2310 / 1000000 : ℝ) 435 (((4 : ℕ) - 1 : ℝ) / ((2500 : ℕ) : ℝ))
      = (906250 * HD 1 - 1080) / 904171 := by
  unfold Phi_w'
  push_cast
  rw [div_eq_div_iff (by norm_num) (by norm_num)]
  ring

/-- **The four-point bound, unconditional, with the window-count bookkeeping.** -/
theorem four_point_bound_w' :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      ((906250 * HD 1 - 1080) / 904171 - ε) * (Zeta23.Ncount T (2 * T) : ℝ)
        ≤ Zeta23.N0simple T (2 * T) := by
  rw [← Phi_four_w']
  exact n_point_bound_fixed' 4 (2310 / 1000000 : ℝ) 435 2500 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) four_point_cert (by norm_num)

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

/-- The pinned record is `HD 1`. -/
theorem currentRecordKappa_eq : currentRecordKappa = HD 1 := by
  unfold currentRecordKappa Zeta23.ThmD.HD
  rw [cStar_one_eq_cMT]

/-- The candidate rational sits below the proved constant. -/
theorem candidateKappa_le : candidateKappa ≤ (906250 * HD 1 - 1080) / 904171 := by
  unfold candidateKappa
  rw [le_div_iff₀ (by norm_num : (0:ℝ) < 904171)]
  linarith [HD_one_bounds.1]

/-- Simple on-line zeros are among the distinct on-line zeros. -/
theorem N0simple_le_N0star (T₁ T₂ : ℝ) : Zeta23.N0simple T₁ T₂ ≤ Zeta23.N0star T₁ T₂ := by
  refine Set.ncard_le_ncard Set.inter_subset_left ?_
  refine (Zeta23.zetaSeam.finite_window T₁ T₂).subset ?_
  rintro ρ ⟨⟨h1, h2, h3⟩, _⟩
  exact ⟨h1, h2, h3⟩

/-- The dyadic bound at the candidate rational, in the library's vocabulary. -/
theorem dyadic :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (candidateKappa - ε) * (Zeta23.Ncount T (2 * T) : ℝ) ≤ Zeta23.N0star T (2 * T) := by
  intro ε hε
  obtain ⟨T₀, hT₀⟩ := four_point_bound_w' ε hε
  refine ⟨T₀, fun T hT => ?_⟩
  have h1 := hT₀ T hT
  have hN : (0:ℝ) ≤ (Zeta23.Ncount T (2 * T) : ℝ) := Nat.cast_nonneg _
  have h2 : (Zeta23.N0simple T (2 * T) : ℝ) ≤ Zeta23.N0star T (2 * T) := by
    exact_mod_cast N0simple_le_N0star T (2 * T)
  have h0 : (candidateKappa - ε) * (Zeta23.Ncount T (2 * T) : ℝ)
      ≤ ((906250 * HD 1 - 1080) / 904171 - ε) * (Zeta23.Ncount T (2 * T) : ℝ) :=
    mul_le_mul_of_nonneg_right (by linarith [candidateKappa_le]) hN
  linarith

/-- The cumulative form, through the library's dyadic-to-cumulative wrapper. -/
theorem cumulative :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (candidateKappa - ε) * (Zeta23.Ncount 0 T : ℝ) ≤ Zeta23.N0star 0 T :=
  Zeta23.cumulative_of_dyadic Zeta23.zetaSeam Zeta23.paperInputs_zeta.RvM
    (fun _ _ _ => Zeta23.N0star_add' Zeta23.zetaSeam) dyadic

/-- Strict improvement over the record. -/
theorem strict : currentRecordKappa < candidateKappa := by
  rw [currentRecordKappa_eq]
  unfold candidateKappa
  linarith [HD_one_bounds.2]

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
