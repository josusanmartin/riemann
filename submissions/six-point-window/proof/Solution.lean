/-
Unconditional critical-line proportion via the weighted six-point refinement of the pinned Zeta23
Theorem D, with the window cos(3s/2) in place of cos(√2 s), at c within 10⁻⁴ of the
weighted functional's minimum.

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
import Zeta23.XiPrime.QuarticWindow.ZeroSide
import Zeta23.XiPrime.QuarticWindow.Moments
import Zeta23.XiPrime.Window
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
  ∫ t in (-(1 : ℝ) / 2)..(1 / 2), Real.cos ((3 / 2 : ℝ) * t) * Real.cos (2 * Real.pi * x * t)

def kfun (x : ℝ) : ℝ := Kfun x / Kfun 0

def wfun (x : ℝ) : ℝ := kfun x ^ 2

/-- the window profile `v(s) = cos(3s/2)` on `[-1/2, 1/2]`. -/
def vTheta (s : ℝ) : ℝ := Real.cos ((3 / 2 : ℝ) * s)

/-- the constant of the window `cos(3s/2)`: `2 − (b + J)/a²` with `a = (4/3) sin(3/4)`,
`b = 1/2 + sin(3/2)/3`, `J = (8/27) sin(3/2) − (4/9) cos(3/2)` (`= 2 − 1/c(vTheta)`, `Htheta_eq`). -/
def Htheta : ℝ :=
  2 - (1 / 2 + Real.sin (3 / 2) / 3 + (8 / 27 * Real.sin (3 / 2) - 4 / 9 * Real.cos (3 / 2)))
    / (4 / 3 * Real.sin (3 / 4)) ^ 2

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
  (Htheta - ((n : ℝ) - 1) * ((m : ℝ) - 1) / ((p : ℝ) * m))
    / (1 - c * ((m : ℝ) - ((n : ℝ) - 1)) / m)

def Phi (c : ℝ) (m p : ℕ) : ℝ :=
  (Htheta - 6 * ((m : ℝ) - 1) / ((p : ℝ) * m)) / (1 - c * ((m : ℝ) - 6) / m)

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

def mtParams (T : ℝ) : Params := (paramsOf stdProfile 1).atV vTheta T

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

lemma cos_three_halves_mul_nonneg {t : ℝ} (ht : t ∈ Set.Icc (-(1 : ℝ) / 2) (1 / 2)) :
    0 ≤ Real.cos ((3 / 2 : ℝ) * t) := by
  obtain ⟨h1, h2⟩ := ht
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
    rw [abs_mul, abs_of_nonneg (cos_three_halves_mul_nonneg ht)]
    calc Real.cos ((3 / 2 : ℝ) * t) * |Real.cos (2 * Real.pi * x * t)|
        ≤ Real.cos ((3 / 2 : ℝ) * t) * 1 :=
          mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (cos_three_halves_mul_nonneg ht)
      _ = Real.cos ((3 / 2 : ℝ) * t) := mul_one _

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

/-! ###### the window `cos(3s/2)`: admissibility, moments, zero side, prime side, ratio limit, constant ###### -/

noncomputable section
set_option linter.unusedSectionVars false

open Real Set MeasureTheory Filter Topology
open Zeta23

namespace Zeta23Ext.Bridge

lemma vTheta_even (s : ℝ) : vTheta (-s) = vTheta s := by
  simp only [vTheta, mul_neg, Real.cos_neg]

lemma vTheta_continuous : Continuous vTheta := by unfold vTheta; fun_prop

lemma vTheta_le_one (s : ℝ) : vTheta s ≤ 1 := Real.cos_le_one _

/-- on the window: `cos(3s/2) ≥ 23/32`. -/
lemma vTheta_ge {s : ℝ} (hs : |s| ≤ 1 / 2) : 23 / 32 ≤ vTheta s := by
  unfold vTheta
  have h := Real.one_sub_sq_div_two_le_cos (x := (3 / 2 : ℝ) * s)
  have hs2 : s ^ 2 ≤ 1 / 4 := by
    have := abs_le.mp hs; nlinarith
  nlinarith

lemma vTheta_pos_of_abs_lt {s : ℝ} (hs : |s| < 1) : 0 < vTheta s := by
  unfold vTheta
  apply Real.cos_pos_of_mem_Ioo
  have := abs_lt.mp hs
  have hπ := Real.pi_gt_three
  constructor <;> nlinarith

lemma vTheta_nonneg_on {s : ℝ} (hs : s ∈ Icc (-(1:ℝ)/2) (1/2)) : 0 ≤ vTheta s := by
  have : |s| ≤ 1 / 2 := abs_le.mpr ⟨by linarith [hs.1], hs.2⟩
  linarith [vTheta_ge this]

lemma vTheta_antitoneOn : AntitoneOn vTheta (Icc 0 (1 / 2)) := by
  intro s hs t ht hst
  unfold vTheta
  apply Real.cos_le_cos_of_nonneg_of_le_pi (by nlinarith [hs.1])
    (by nlinarith [ht.2, Real.pi_gt_three]) (by nlinarith)

namespace WinTheta

/-! ### the modulating factor `√cos(3u/(2L))` -/

/-- the modulating factor in the `u`-variable. -/
def fT (L : ℝ) (u : ℝ) : ℝ := Real.sqrt (max 0 (vTheta (u / L)))

/-- `h := cos(3u/(2L)) = fT²` near the core. -/
def hT (L : ℝ) (u : ℝ) : ℝ := vTheta (u / L)

lemma hT_eq (L u : ℝ) : hT L u = Real.cos (3 / (2 * L) * u) := by
  simp only [hT, vTheta]; congr 1; ring

variable {L : ℝ}

lemma fT_even (u : ℝ) : fT L (-u) = fT L u := by
  simp only [fT, neg_div, vTheta_even]

lemma fT_nonneg (u : ℝ) : 0 ≤ fT L u := Real.sqrt_nonneg _

lemma fT_le_one (u : ℝ) : fT L u ≤ 1 := by
  unfold fT
  rw [show (1:ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
  exact Real.sqrt_le_sqrt (max_le zero_le_one (vTheta_le_one _))

lemma core_abs (hL : 0 < L) {u : ℝ} (hu : |u| ≤ L / 2) : |u / L| ≤ 1 / 2 := by
  rw [abs_div, abs_of_pos hL, div_le_iff₀ hL]; linarith

lemma core_mem (hL : 0 < L) {u : ℝ} (hu : |u| ≤ L / 2) : u / L ∈ Icc (-(1/2 : ℝ)) (1/2) := by
  have := abs_le.mp (core_abs hL hu)
  exact ⟨this.1, this.2⟩

lemma hT_core_ge (hL : 0 < L) {u : ℝ} (hu : |u| ≤ L / 2) : 23 / 32 ≤ hT L u :=
  vTheta_ge (core_abs hL hu)

lemma fT_core_ge (hL : 0 < L) {u : ℝ} (hu : |u| ≤ L / 2) : 4 / 5 ≤ fT L u := by
  have h := hT_core_ge hL hu
  unfold fT
  rw [max_eq_right (by unfold hT at h; linarith)]
  refine Real.le_sqrt_of_sq_le ?_
  unfold hT at h; nlinarith

lemma hT_pos_of_mem (hL : 0 < L) {u : ℝ} (hu : u ∈ Ioo (-(L / 2 + L / 2)) (L / 2 + L / 2)) :
    0 < hT L u := by
  apply vTheta_pos_of_abs_lt
  rw [abs_div, abs_of_pos hL, div_lt_one hL, abs_lt]
  constructor <;> linarith [hu.1, hu.2]

lemma fT_eq_sqrt_of_mem (hL : 0 < L) {u : ℝ} (hu : u ∈ Ioo (-(L / 2 + L / 2)) (L / 2 + L / 2)) :
    fT L u = Real.sqrt (hT L u) := by
  show Real.sqrt (max 0 (hT L u)) = _
  rw [max_eq_right (hT_pos_of_mem hL hu).le]

lemma hT_contDiff : ContDiff ℝ 2 (hT L) := by
  have : hT L = fun u => Real.cos (3 / (2 * L) * u) := funext (hT_eq L)
  rw [this]; fun_prop

lemma fT_contDiffOn (hL : 0 < L) :
    ContDiffOn ℝ 2 (fT L) (Ioo (-(L / 2 + L / 2)) (L / 2 + L / 2)) := by
  have h1 : ContDiffOn ℝ 2 (fun u => Real.sqrt (hT L u)) (Ioo (-(L / 2 + L / 2)) (L / 2 + L / 2)) :=
    hT_contDiff.contDiffOn.sqrt fun u hu => (hT_pos_of_mem hL hu).ne'
  exact h1.congr fun u hu => fT_eq_sqrt_of_mem hL hu

lemma fT_mul_self_of_mem (hL : 0 < L) {u : ℝ} (hu : u ∈ Ioo (-(L / 2 + L / 2)) (L / 2 + L / 2)) :
    fT L u * fT L u = hT L u := by
  rw [fT_eq_sqrt_of_mem hL hu, ← sq, Real.sq_sqrt (hT_pos_of_mem hL hu).le]

/-! ### derivatives of `h` -/

lemma hasDerivAt_hT (u : ℝ) :
    HasDerivAt (hT L) (-(3 / (2 * L)) * Real.sin (3 / (2 * L) * u)) u := by
  have e : hT L = fun u => Real.cos (3 / (2 * L) * u) := funext (hT_eq L)
  rw [e]
  have h := ((hasDerivAt_id u).const_mul (3 / (2 * L))).cos
  simp only [id, mul_one] at h
  exact h.congr_deriv (by ring)

lemma deriv_hT (u : ℝ) : deriv (hT L) u = -(3 / (2 * L)) * Real.sin (3 / (2 * L) * u) :=
  (hasDerivAt_hT u).deriv

lemma hasDerivAt_deriv_hT (u : ℝ) :
    HasDerivAt (deriv (hT L)) (-(3 / (2 * L)) ^ 2 * Real.cos (3 / (2 * L) * u)) u := by
  have e : deriv (hT L) = fun u => -(3 / (2 * L)) * Real.sin (3 / (2 * L) * u) :=
    funext deriv_hT
  rw [e]
  have h := (((hasDerivAt_id u).const_mul (3 / (2 * L))).sin).const_mul (-(3 / (2 * L)))
  simp only [id, mul_one] at h
  exact h.congr_deriv (by ring)

lemma deriv2_hT (u : ℝ) :
    deriv (deriv (hT L)) u = -(3 / (2 * L)) ^ 2 * Real.cos (3 / (2 * L) * u) :=
  (hasDerivAt_deriv_hT u).deriv

lemma abs_deriv_hT_le (hL : 0 < L) (u : ℝ) : |deriv (hT L) u| ≤ 3 / 2 / L := by
  rw [deriv_hT, abs_mul, abs_neg, abs_of_pos (by positivity : (0:ℝ) < 3 / (2 * L))]
  calc 3 / (2 * L) * |Real.sin (3 / (2 * L) * u)| ≤ 3 / (2 * L) * 1 :=
        mul_le_mul_of_nonneg_left (Real.abs_sin_le_one _) (by positivity)
    _ = 3 / 2 / L := by field_simp

lemma abs_deriv2_hT_le (hL : 0 < L) (u : ℝ) : |deriv (deriv (hT L)) u| ≤ 9 / 4 / L ^ 2 := by
  rw [deriv2_hT, abs_mul, abs_neg, abs_pow, abs_of_pos (by positivity : (0:ℝ) < 3 / (2 * L))]
  calc (3 / (2 * L)) ^ 2 * |Real.cos (3 / (2 * L) * u)| ≤ (3 / (2 * L)) ^ 2 * 1 :=
        mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (by positivity)
    _ = 9 / 4 / L ^ 2 := by field_simp; ring

/-! ### derivatives of `fT` on the core, through `fT · fT = h` -/

lemma abs_deriv_fT_le (hL : 0 < L) {u : ℝ} (hu : |u| ≤ L / 2) : |deriv (fT L) u| ≤ 1 / L := by
  set U : Set ℝ := Ioo (-(L / 2 + L / 2)) (L / 2 + L / 2) with hUdef
  have hU : IsOpen U := isOpen_Ioo
  have huU : u ∈ U := by
    simp only [hUdef, mem_Ioo]; constructor <;> linarith [neg_abs_le u, le_abs_self u]
  have hsm := fT_contDiffOn hL
  have hev : (fun v => fT L v * fT L v) =ᶠ[nhds u] hT L := by
    filter_upwards [hU.mem_nhds huU] with v hv using fT_mul_self_of_mem hL hv
  have hd : deriv (hT L) u = deriv (fT L) u * fT L u + fT L u * deriv (fT L) u := by
    rw [← hev.deriv_eq]; exact XiPrime.deriv_mul_eq hU hsm hsm huU
  have hf := fT_core_ge hL hu
  have hh := abs_deriv_hT_le hL u
  have e : deriv (fT L) u = deriv (hT L) u / (2 * fT L u) := by
    rw [hd]; field_simp; ring
  rw [e, abs_div, abs_of_pos (by linarith : 0 < 2 * fT L u)]
  rw [div_le_div_iff₀ (by linarith) hL]
  calc |deriv (hT L) u| * L ≤ 3 / 2 / L * L := by gcongr
    _ = 3 / 2 := by field_simp
    _ ≤ 1 * (2 * (4 / 5)) := by norm_num
    _ ≤ 1 * (2 * fT L u) := by gcongr

lemma abs_deriv2_fT_le (hL : 0 < L) {u : ℝ} (hu : |u| ≤ L / 2) :
    |deriv (deriv (fT L)) u| ≤ 3 / L ^ 2 := by
  set U : Set ℝ := Ioo (-(L / 2 + L / 2)) (L / 2 + L / 2) with hUdef
  have hU : IsOpen U := isOpen_Ioo
  have huU : u ∈ U := by
    simp only [hUdef, mem_Ioo]; constructor <;> linarith [neg_abs_le u, le_abs_self u]
  have hsm := fT_contDiffOn hL
  have hd1 : ∀ v ∈ U, deriv (fun x => fT L x * fT L x) v = deriv (hT L) v := by
    intro v hv
    have hev : (fun x => fT L x * fT L x) =ᶠ[nhds v] hT L := by
      filter_upwards [hU.mem_nhds hv] with x hx using fT_mul_self_of_mem hL hx
    exact hev.deriv_eq
  have hev2 : deriv (fun x => fT L x * fT L x) =ᶠ[nhds u] deriv (hT L) := by
    filter_upwards [hU.mem_nhds huU] with v hv using hd1 v hv
  have hd2 : deriv (deriv (hT L)) u
      = deriv (deriv (fT L)) u * fT L u + 2 * (deriv (fT L) u * deriv (fT L) u)
        + fT L u * deriv (deriv (fT L)) u := by
    rw [← hev2.deriv_eq]; exact XiPrime.deriv2_mul_eq hU hsm hsm huU
  have hf := fT_core_ge hL hu
  have h1 := abs_deriv_fT_le hL hu
  have h2 := abs_deriv2_hT_le hL u
  have e : deriv (deriv (fT L)) u
      = (deriv (deriv (hT L)) u - 2 * (deriv (fT L) u * deriv (fT L) u)) / (2 * fT L u) := by
    rw [hd2]; field_simp; ring
  rw [e, abs_div, abs_of_pos (by linarith : 0 < 2 * fT L u),
    div_le_div_iff₀ (by linarith) (by positivity)]
  have hsq : |deriv (fT L) u| ^ 2 ≤ (1 / L) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h1 2
  calc |deriv (deriv (hT L)) u - 2 * (deriv (fT L) u * deriv (fT L) u)| * L ^ 2
      ≤ (|deriv (deriv (hT L)) u| + 2 * |deriv (fT L) u| ^ 2) * L ^ 2 := by
        gcongr
        calc |deriv (deriv (hT L)) u - 2 * (deriv (fT L) u * deriv (fT L) u)|
            ≤ |deriv (deriv (hT L)) u| + |2 * (deriv (fT L) u * deriv (fT L) u)| := abs_sub _ _
          _ = |deriv (deriv (hT L)) u| + 2 * |deriv (fT L) u| ^ 2 := by
              rw [abs_mul, abs_two, abs_mul, sq]
    _ ≤ (9 / 4 / L ^ 2 + 2 * (1 / L) ^ 2) * L ^ 2 := by gcongr
    _ = 9 / 4 + 2 := by field_simp
    _ ≤ 3 * (2 * (4 / 5)) := by norm_num
    _ ≤ 3 * (2 * fT L u) := by gcongr

/-! ### the `ModFactor` instance and the admissible window -/

theorem modFactor_fT (hL : 0 < L) : XiPrime.ModFactor (fT L) L 1 3 where
  A_nonneg := by norm_num
  B_nonneg := by norm_num
  even := fT_even
  nonneg := fT_nonneg
  le_one := fun u _ => fT_le_one u
  antitone := by
    intro x hx y hy hxy
    unfold fT
    apply Real.sqrt_le_sqrt
    apply max_le_max le_rfl
    refine vTheta_antitoneOn ⟨div_nonneg hx.1 hL.le, ?_⟩ ⟨div_nonneg hy.1 hL.le, ?_⟩
      (div_le_div_of_nonneg_right hxy hL.le)
    · rw [div_le_iff₀ hL]; linarith [hx.2]
    · rw [div_le_iff₀ hL]; linarith [hy.2]
  smooth := ⟨L / 2, by positivity, fT_contDiffOn hL⟩
  deriv_le := fun u hu => by simpa using abs_deriv_fT_le hL hu
  deriv2_le := fun u hu => abs_deriv2_fT_le hL hu

end WinTheta

open WinTheta

/-- the window constant of `cos(3s/2)` on the tree's taper. -/
def cTh (ϱ : ℝ → ℝ) : ℝ := XiPrime.cMod ϱ 1 3

theorem phiV_theta_eq (P : Params) (T : ℝ) :
    P.phiV vTheta T = XiPrime.phiM (fT (P.L T)) P.ϱ (P.L T) P.w := rfl

/-- **The window `√cos(3u/(2L)) · φ` is admissible.** -/
theorem admWindow_theta {P : Params} (hP : P.Valid) {T : ℝ} (hwL : 8 * P.w ≤ P.L T) :
    AdmWindow (P.phiV vTheta T) (P.L T) P.w (cTh P.ϱ) := by
  have hL : 0 < P.L T := by linarith [hP.one_le_w]
  rw [phiV_theta_eq]
  exact XiPrime.admWindow_phiM (modFactor_fT hL) hP.taper hP.one_le_w hwL

end Zeta23Ext.Bridge

end

/-! ###### moments of the `cos(3s/2)` window vs their scale-free limits ###### -/

noncomputable section
set_option linter.unusedSectionVars false

open Real Set MeasureTheory Filter Topology
open Zeta23

namespace Zeta23Ext.Bridge.WinTheta

variable {ϱ : ℝ → ℝ} {L w : ℝ}

/-- the squared modulating factor, globally: `max 0 (v(u/L)) = fT² ∈ [0,1]`. -/
def mT (L : ℝ) (u : ℝ) : ℝ := max 0 (vTheta (u / L))

lemma vTheta_div_nonneg (hL : 0 < L) {u : ℝ} (hu : u ∈ Icc (-(L/2)) (L/2)) : 0 ≤ vTheta (u / L) := by
  linarith [vTheta_ge (core_abs hL (abs_le.mpr ⟨hu.1, hu.2⟩))]

lemma mT_nonneg (u : ℝ) : 0 ≤ mT L u := le_max_left _ _
lemma mT_le_one (u : ℝ) : mT L u ≤ 1 := max_le zero_le_one (vTheta_le_one _)
lemma abs_mT_le_one (u : ℝ) : |mT L u| ≤ 1 := by rw [abs_of_nonneg (mT_nonneg u)]; exact mT_le_one u
lemma mT_continuous : Continuous (mT L) := by
  unfold mT; exact continuous_const.max (vTheta_continuous.comp (continuous_id.div_const L))
lemma fT_sq (u : ℝ) : fT L u ^ 2 = mT L u := Real.sq_sqrt (le_max_left _ _)
lemma mT_core (hL : 0 < L) {u : ℝ} (hu : u ∈ Icc (-(L/2)) (L/2)) : mT L u = vTheta (u / L) :=
  max_eq_right (vTheta_div_nonneg hL hu)

lemma phiMT_sq_eq (u : ℝ) :
    XiPrime.phiM (fT L) ϱ L w u ^ 2 = mT L u * Taper.phi ϱ L w u ^ 2 := by
  rw [XiPrime.phiM, mul_pow, fT_sq]

lemma phiMT_pow_four_eq (u : ℝ) :
    XiPrime.phiM (fT L) ϱ L w u ^ 4 = mT L u ^ 2 * Taper.phi ϱ L w u ^ 4 := by
  have : XiPrime.phiM (fT L) ϱ L w u ^ 4 = (XiPrime.phiM (fT L) ϱ L w u ^ 2) ^ 2 := by ring
  rw [this, phiMT_sq_eq]; ring

/-- `|L⁻¹∫φ_θ² − ∫v| ≤ 2w/L`. -/
theorem aT_close (hϱ : TaperProfile ϱ) (hw : 1 ≤ w) (hwL : 8 * w ≤ L) :
    |L⁻¹ * (∫ u, XiPrime.phiM (fT L) ϱ L w u ^ 2) - ∫ s in (-(1:ℝ)/2)..(1/2), vTheta s|
      ≤ 2 * w / L := by
  have hw0 : 0 < w := by linarith
  have hwL' : 2 * w ≤ L := by linarith
  have hL : 0 < L := by linarith
  have hsub : (∫ s in (-(1:ℝ)/2)..(1/2), vTheta s) = L⁻¹ * ∫ u in Set.Icc (-(L/2)) (L/2), mT L u := by
    rw [setIntegral_congr_fun measurableSet_Icc (fun u hu => mT_core hL hu),
      MeasureTheory.integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by linarith : -(L/2) ≤ L/2), XiPrime.integral_scale hL]
    field_simp
  have hwin : ∫ u, XiPrime.phiM (fT L) ϱ L w u ^ 2 = ∫ u, mT L u * Taper.phi ϱ L w u ^ 2 :=
    integral_congr_ae (ae_of_all _ fun u => phiMT_sq_eq u)
  rw [hwin, hsub]
  have hcore := XiPrime.edge_estimate (h := mT L) (p := fun u => Taper.phi ϱ L w u ^ 2) hL hw0 hwL'
    abs_mT_le_one (fun u => sq_nonneg _)
    (fun u => by
      calc Taper.phi ϱ L w u ^ 2 ≤ 1 ^ 2 :=
            pow_le_pow_left₀ (Taper.phi_nonneg hϱ u) (Taper.phi_le_one hϱ u) 2
        _ = 1 := one_pow 2)
    (fun u hu => by show Taper.phi ϱ L w u ^ 2 = 1; rw [Taper.phi_eq_one hϱ hw0 hu, one_pow])
    (fun u hu => by
      show Taper.phi ϱ L w u ^ 2 = 0; rw [Taper.phi_eq_zero hϱ hw0 hu, zero_pow two_ne_zero])
    ((Taper.phi_continuous hϱ hw0 hwL').pow 2) mT_continuous
  have e : L⁻¹ * (∫ u, mT L u * Taper.phi ϱ L w u ^ 2)
        - L⁻¹ * ∫ u in Set.Icc (-(L/2)) (L/2), mT L u
      = L⁻¹ * ((∫ u, mT L u * Taper.phi ϱ L w u ^ 2)
        - ∫ u in Set.Icc (-(L/2)) (L/2), mT L u) := by ring
  rw [e, abs_mul, abs_of_pos (by positivity : (0:ℝ) < L⁻¹)]
  calc L⁻¹ * |(∫ u, mT L u * Taper.phi ϱ L w u ^ 2) - ∫ u in Set.Icc (-(L/2)) (L/2), mT L u|
      ≤ L⁻¹ * (2 * w) := mul_le_mul_of_nonneg_left hcore (by positivity)
    _ = 2 * w / L := by rw [div_eq_inv_mul]

/-- `|L⁻¹∫φ_θ⁴ − ∫v²| ≤ 2w/L`. -/
theorem bT_close (hϱ : TaperProfile ϱ) (hw : 1 ≤ w) (hwL : 8 * w ≤ L) :
    |L⁻¹ * (∫ u, XiPrime.phiM (fT L) ϱ L w u ^ 4) - ∫ s in (-(1:ℝ)/2)..(1/2), vTheta s ^ 2|
      ≤ 2 * w / L := by
  have hw0 : 0 < w := by linarith
  have hwL' : 2 * w ≤ L := by linarith
  have hL : 0 < L := by linarith
  have hsub : (∫ s in (-(1:ℝ)/2)..(1/2), vTheta s ^ 2)
      = L⁻¹ * ∫ u in Set.Icc (-(L/2)) (L/2), mT L u ^ 2 := by
    rw [setIntegral_congr_fun measurableSet_Icc
        (fun u hu => by show mT L u ^ 2 = vTheta (u / L) ^ 2; rw [mT_core hL hu]),
      MeasureTheory.integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by linarith : -(L/2) ≤ L/2),
      XiPrime.integral_scale (g := fun s => vTheta s ^ 2) hL]
    field_simp
  have hwin : ∫ u, XiPrime.phiM (fT L) ϱ L w u ^ 4 = ∫ u, mT L u ^ 2 * Taper.phi ϱ L w u ^ 4 :=
    integral_congr_ae (ae_of_all _ fun u => phiMT_pow_four_eq u)
  rw [hwin, hsub]
  have hcore := XiPrime.edge_estimate (h := fun u => mT L u ^ 2)
    (p := fun u => Taper.phi ϱ L w u ^ 4) hL hw0 hwL'
    (fun u => by
      rw [abs_of_nonneg (sq_nonneg _)]
      calc mT L u ^ 2 ≤ 1 ^ 2 := pow_le_pow_left₀ (mT_nonneg u) (mT_le_one u) 2
        _ = 1 := one_pow 2)
    (fun u => by positivity)
    (fun u => by
      calc Taper.phi ϱ L w u ^ 4 ≤ 1 ^ 4 :=
            pow_le_pow_left₀ (Taper.phi_nonneg hϱ u) (Taper.phi_le_one hϱ u) 4
        _ = 1 := one_pow 4)
    (fun u hu => by show Taper.phi ϱ L w u ^ 4 = 1; rw [Taper.phi_eq_one hϱ hw0 hu, one_pow])
    (fun u hu => by show Taper.phi ϱ L w u ^ 4 = 0; rw [Taper.phi_eq_zero hϱ hw0 hu]; norm_num)
    ((Taper.phi_continuous hϱ hw0 hwL').pow 4) (mT_continuous.pow 2)
  have e : L⁻¹ * (∫ u, mT L u ^ 2 * Taper.phi ϱ L w u ^ 4)
        - L⁻¹ * ∫ u in Set.Icc (-(L/2)) (L/2), mT L u ^ 2
      = L⁻¹ * ((∫ u, mT L u ^ 2 * Taper.phi ϱ L w u ^ 4)
        - ∫ u in Set.Icc (-(L/2)) (L/2), mT L u ^ 2) := by ring
  rw [e, abs_mul, abs_of_pos (by positivity : (0:ℝ) < L⁻¹)]
  calc L⁻¹ * |(∫ u, mT L u ^ 2 * Taper.phi ϱ L w u ^ 4)
          - ∫ u in Set.Icc (-(L/2)) (L/2), mT L u ^ 2|
      ≤ L⁻¹ * (2 * w) := mul_le_mul_of_nonneg_left hcore (by positivity)
    _ = 2 * w / L := by rw [div_eq_inv_mul]

/-! ### the autocorrelation vs the sharp one -/

/-- the sharp window `1_{[−L/2,L/2]}·v(·/L)`. -/
def sharpT (L : ℝ) (u : ℝ) : ℝ := (Set.Icc (-(L/2)) (L/2)).indicator (fun u => vTheta (u / L)) u

lemma sharpT_nonneg (hL : 0 < L) (u : ℝ) : 0 ≤ sharpT L u := by
  unfold sharpT
  apply Set.indicator_nonneg
  intro x hx
  exact vTheta_div_nonneg hL hx

lemma sharpT_le_one (u : ℝ) : sharpT L u ≤ 1 := by
  unfold sharpT
  by_cases hm : u ∈ Set.Icc (-(L/2)) (L/2)
  · rw [Set.indicator_of_mem hm]; exact vTheta_le_one _
  · rw [Set.indicator_of_notMem hm]; exact zero_le_one

lemma sharpT_measurable : Measurable (sharpT L) := by
  unfold sharpT
  exact Measurable.indicator (vTheta_continuous.comp (continuous_id.div_const L)).measurable
    measurableSet_Icc

lemma sharpT_integrable : Integrable (sharpT L) := by
  unfold sharpT
  exact (MeasureTheory.integrable_indicator_iff measurableSet_Icc).mpr
    (((vTheta_continuous.comp (continuous_id.div_const L)).continuousOn).integrableOn_compact
      isCompact_Icc)

theorem sharpT_autocorr_eq (hL : 0 < L) {y : ℝ} (hy0 : 0 ≤ y) (hyL : y ≤ L) :
    ∫ u, sharpT L u * sharpT L (u + y) = L * XiPrime.vConv vTheta (y / L) := by
  have hind : ∀ u : ℝ, sharpT L u * sharpT L (u + y)
      = (Set.Icc (-(L/2)) (L/2 - y)).indicator
          (fun u => vTheta (u / L) * vTheta ((u + y) / L)) u := by
    intro u
    unfold sharpT
    by_cases hu : u ∈ Set.Icc (-(L/2)) (L/2 - y)
    · have hu1 : u ∈ Set.Icc (-(L/2)) (L/2) := ⟨hu.1, by linarith [hu.2]⟩
      have hu2 : u + y ∈ Set.Icc (-(L/2)) (L/2) := ⟨by linarith [hu.1], by linarith [hu.2]⟩
      rw [Set.indicator_of_mem hu, Set.indicator_of_mem hu1, Set.indicator_of_mem hu2]
    · rw [Set.indicator_of_notMem hu]
      rw [Set.mem_Icc, not_and_or, not_le, not_le] at hu
      rcases hu with hu | hu
      · rw [Set.indicator_of_notMem (s := Set.Icc (-(L/2)) (L/2)) (a := u)
          (by rw [Set.mem_Icc]; push Not; intro h; linarith), zero_mul]
      · rw [Set.indicator_of_notMem (s := Set.Icc (-(L/2)) (L/2)) (a := u + y)
          (by rw [Set.mem_Icc]; push Not; intro h; linarith), mul_zero]
  rw [MeasureTheory.integral_congr_ae (MeasureTheory.ae_of_all _ hind),
    MeasureTheory.integral_indicator measurableSet_Icc,
    MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith : -(L/2) ≤ L/2 - y)]
  have hsub := intervalIntegral.integral_comp_div (a := -(L/2)) (b := L/2 - y)
    (f := fun s => vTheta s * vTheta (s + y / L)) hL.ne'
  have e1 : -(L/2) / L = -(1:ℝ)/2 := by field_simp
  have e2 : (L/2 - y) / L = 1/2 - y / L := by field_simp
  rw [e1, e2, smul_eq_mul] at hsub
  unfold XiPrime.vConv
  rw [← hsub]
  refine intervalIntegral.integral_congr fun u _ => ?_
  simp only [add_div]

/-- `‖φ_θ² − sharp‖₁ ≤ 2w`. -/
theorem integral_abs_phiMTsq_sub_sharp (hϱ : TaperProfile ϱ) (hw : 0 < w) (hwL : 2 * w ≤ L) :
    ∫ u, |XiPrime.phiM (fT L) ϱ L w u ^ 2 - sharpT L u| ≤ 2 * w := by
  have hL : 0 < L := by linarith
  set maj : ℝ → ℝ := fun u => (Set.Icc (-(L/2)) (-(L/2) + w)).indicator (1 : ℝ → ℝ) u
      + (Set.Icc (L/2 - w) (L/2)).indicator (1 : ℝ → ℝ) u with hmaj
  have hImaj : Integrable maj := by
    apply Integrable.add <;>
      exact (MeasureTheory.integrable_indicator_iff measurableSet_Icc).mpr
        (MeasureTheory.integrableOn_const (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top))
  have hind0 : ∀ (s : Set ℝ) (u : ℝ), 0 ≤ s.indicator (1 : ℝ → ℝ) u := fun s u =>
    Set.indicator_nonneg (fun _ _ => zero_le_one) u
  have hpt : ∀ u : ℝ, |XiPrime.phiM (fT L) ϱ L w u ^ 2 - sharpT L u| ≤ maj u := by
    intro u
    have hmaj0 : 0 ≤ maj u := by
      rw [hmaj]
      exact add_nonneg (hind0 _ u) (hind0 _ u)
    have hval : XiPrime.phiM (fT L) ϱ L w u ^ 2 = mT L u * Taper.phi ϱ L w u ^ 2 := phiMT_sq_eq u
    rcases le_or_gt |u| (L/2 - w) with hpl | hedge
    · have huIcc : u ∈ Set.Icc (-(L/2)) (L/2) := by
        rw [abs_le] at hpl
        constructor <;> [linarith [hpl.1]; linarith [hpl.2]]
      rw [hval, Taper.phi_eq_one hϱ hw hpl, one_pow, mul_one, mT_core hL huIcc]
      unfold sharpT
      rw [Set.indicator_of_mem huIcc, sub_self, abs_zero]
      exact hmaj0
    · rcases le_or_gt |u| (L/2) with hin | hout
      · have hbound : |XiPrime.phiM (fT L) ϱ L w u ^ 2 - sharpT L u| ≤ 1 := by
          have h1' : 0 ≤ XiPrime.phiM (fT L) ϱ L w u ^ 2 := sq_nonneg _
          have h2' : XiPrime.phiM (fT L) ϱ L w u ^ 2 ≤ 1 := by
            rw [hval]
            calc mT L u * Taper.phi ϱ L w u ^ 2 ≤ 1 * 1 ^ 2 :=
                  mul_le_mul (mT_le_one u)
                    (pow_le_pow_left₀ (Taper.phi_nonneg hϱ u) (Taper.phi_le_one hϱ u) 2)
                    (sq_nonneg _) zero_le_one
              _ = 1 := by norm_num
          have h3' := sharpT_nonneg hL u
          have h4' : sharpT L u ≤ 1 := sharpT_le_one u
          rw [abs_le]
          constructor <;> linarith
        have hone : (1:ℝ) ≤ maj u := by
          rw [hmaj]
          show (1:ℝ) ≤ (Set.Icc (-(L/2)) (-(L/2) + w)).indicator (1 : ℝ → ℝ) u
            + (Set.Icc (L/2 - w) (L/2)).indicator (1 : ℝ → ℝ) u
          rcases le_or_gt u 0 with hneg | hpos
          · have hu1 : u ∈ Set.Icc (-(L/2)) (-(L/2) + w) := by
              refine ⟨?_, ?_⟩
              · have : |u| = -u := abs_of_nonpos hneg
                rw [this] at hin
                linarith
              · have : |u| = -u := abs_of_nonpos hneg
                rw [this] at hedge
                linarith
            have := hind0 (Set.Icc (L/2 - w) (L/2)) u
            rw [Set.indicator_of_mem hu1, Pi.one_apply]
            linarith
          · have hu1 : u ∈ Set.Icc (L/2 - w) (L/2) := by
              refine ⟨?_, ?_⟩
              · have : |u| = u := abs_of_pos hpos
                rw [this] at hedge
                linarith
              · have : |u| = u := abs_of_pos hpos
                rw [this] at hin
                linarith
            have := hind0 (Set.Icc (-(L/2)) (-(L/2) + w)) u
            rw [Set.indicator_of_mem hu1, Pi.one_apply]
            linarith
        linarith
      · have h1' : XiPrime.phiM (fT L) ϱ L w u = 0 := XiPrime.phiM_eq_zero hϱ hw (le_of_lt hout)
        have h2' : sharpT L u = 0 := by
          unfold sharpT
          apply Set.indicator_of_notMem
          intro hm
          have : |u| ≤ L / 2 := abs_le.mpr ⟨hm.1, hm.2⟩
          linarith
        rw [h1', h2']
        norm_num
        exact hmaj0
  calc ∫ u, |XiPrime.phiM (fT L) ϱ L w u ^ 2 - sharpT L u|
      ≤ ∫ u, maj u := by
        apply MeasureTheory.integral_mono_of_nonneg
          (MeasureTheory.ae_of_all _ fun u => abs_nonneg _) hImaj
          (MeasureTheory.ae_of_all _ hpt)
    _ = 2 * w := by
        rw [hmaj]
        rw [MeasureTheory.integral_add
          ((MeasureTheory.integrable_indicator_iff measurableSet_Icc).mpr
            (MeasureTheory.integrableOn_const (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)))
          ((MeasureTheory.integrable_indicator_iff measurableSet_Icc).mpr
            (MeasureTheory.integrableOn_const (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top))),
          MeasureTheory.integral_indicator_one measurableSet_Icc,
          MeasureTheory.integral_indicator_one measurableSet_Icc,
          MeasureTheory.measureReal_def, MeasureTheory.measureReal_def,
          Real.volume_Icc, Real.volume_Icc,
          ENNReal.toReal_ofReal (by linarith), ENNReal.toReal_ofReal (by linarith)]
        ring

/-- **`|g_θ(y) − L·(v⋆v)(y/L)| ≤ 4w` for `y ∈ [0, L]`** (`g = φ_θ² ⋆ φ_θ²`). -/
theorem autocorr_phiMTsq_close (hϱ : TaperProfile ϱ) (hw : 1 ≤ w) (hwL : 8 * w ≤ L) {y : ℝ}
    (hy0 : 0 ≤ y) (hyL : y ≤ L) :
    |Params.autocorr (fun u => XiPrime.phiM (fT L) ϱ L w u ^ 2) y
      - L * XiPrime.vConv vTheta (y / L)| ≤ 4 * w := by
  have hw0 : 0 < w := by linarith
  have hwL' : 2 * w ≤ L := by linarith
  have hL : 0 < L := by linarith
  have hf : XiPrime.ModFactor (fT L) L 1 3 := modFactor_fT hL
  set h : ℝ → ℝ := fun u => XiPrime.phiM (fT L) ϱ L w u ^ 2 with hhdef
  set k : ℝ → ℝ := sharpT L with hkdef
  have hh_cont : Continuous h := ((XiPrime.phiM_contDiff hf hϱ hw0 hwL').pow 2).continuous
  have hh1 : ∀ u, |h u| ≤ 1 := by
    intro u
    rw [hhdef]
    simp only
    rw [abs_of_nonneg (sq_nonneg _)]
    calc XiPrime.phiM (fT L) ϱ L w u ^ 2 ≤ 1 ^ 2 :=
          pow_le_pow_left₀ (XiPrime.phiM_nonneg hf hϱ u) (XiPrime.phiM_le_one hf hϱ hw0 u) 2
      _ = 1 := one_pow 2
  have hk_meas : Measurable k := sharpT_measurable
  have hk1 : ∀ u, |k u| ≤ 1 := by
    intro u
    rw [hkdef, abs_le]
    exact ⟨by linarith [sharpT_nonneg hL u], sharpT_le_one u⟩
  have hcs : HasCompactSupport h :=
    (XiPrime.phiM_hasCompactSupport (f := fT L) hϱ (L := L) hw0).comp_left
      (g := fun t => t ^ 2) (by norm_num)
  have hint_h : Integrable h := hh_cont.integrable_of_hasCompactSupport hcs
  have hint_k : Integrable k := sharpT_integrable
  have hint_d : Integrable (fun u => h u - k u) := hint_h.sub hint_k
  have hint_hy : Integrable (fun u => h (u + y)) := hint_h.comp_add_right y
  have hint_ky : Integrable (fun u => k (u + y)) := hint_k.comp_add_right y
  have hint_dy : Integrable (fun u => h (u + y) - k (u + y)) := hint_hy.sub hint_ky
  have hmeas_hy : MeasureTheory.AEStronglyMeasurable (fun u => h (u + y)) MeasureTheory.volume :=
    hint_hy.aestronglyMeasurable
  have hint_p1 : Integrable (fun u => (h u - k u) * h (u + y)) := by
    have := hint_d.bdd_mul (c := 1) hmeas_hy (MeasureTheory.ae_of_all _ fun u => by
      rw [Real.norm_eq_abs]
      exact hh1 (u + y))
    exact this.congr (MeasureTheory.ae_of_all _ fun u => by ring)
  have hint_p2 : Integrable (fun u => k u * (h (u + y) - k (u + y))) := by
    exact hint_dy.bdd_mul (c := 1) hk_meas.aestronglyMeasurable
      (MeasureTheory.ae_of_all _ fun u => by
        rw [Real.norm_eq_abs]
        exact hk1 u)
  have hint_hh : Integrable (fun u => h u * h (u + y)) := by
    have := hint_h.bdd_mul (c := 1) hmeas_hy (MeasureTheory.ae_of_all _ fun u => by
      rw [Real.norm_eq_abs]
      exact hh1 (u + y))
    exact this.congr (MeasureTheory.ae_of_all _ fun u => by ring)
  have hint_kk : Integrable (fun u => k u * k (u + y)) := by
    exact hint_ky.bdd_mul (c := 1) hk_meas.aestronglyMeasurable
      (MeasureTheory.ae_of_all _ fun u => by
        rw [Real.norm_eq_abs]
        exact hk1 u)
  have hCk : ∫ u, k u * k (u + y) = L * XiPrime.vConv vTheta (y / L) :=
    sharpT_autocorr_eq hL hy0 hyL
  have hdecomp : Params.autocorr h y - L * XiPrime.vConv vTheta (y / L)
      = (∫ u, (h u - k u) * h (u + y)) + ∫ u, k u * (h (u + y) - k (u + y)) := by
    have e1 : Params.autocorr h y - L * XiPrime.vConv vTheta (y / L)
        = ∫ u, (h u * h (u + y) - k u * k (u + y)) := by
      rw [show Params.autocorr h y = ∫ u, h u * h (u + y) from rfl, ← hCk,
        MeasureTheory.integral_sub hint_hh hint_kk]
    rw [e1, ← MeasureTheory.integral_add hint_p1 hint_p2]
    apply MeasureTheory.integral_congr_ae
    apply MeasureTheory.ae_of_all
    intro u
    ring
  have hd2w := integral_abs_phiMTsq_sub_sharp (L := L) hϱ hw0 hwL'
  have hint_dabs : Integrable (fun u => |h u - k u|) := hint_d.abs
  have hb1 : |∫ u, (h u - k u) * h (u + y)| ≤ 2 * w := by
    calc |∫ u, (h u - k u) * h (u + y)| ≤ ∫ u, |(h u - k u) * h (u + y)| :=
          MeasureTheory.abs_integral_le_integral_abs
      _ ≤ ∫ u, |h u - k u| := by
          apply MeasureTheory.integral_mono_of_nonneg
            (MeasureTheory.ae_of_all _ fun u => abs_nonneg _) hint_dabs
            (MeasureTheory.ae_of_all _ fun u => ?_)
          show |(h u - k u) * h (u + y)| ≤ |h u - k u|
          rw [abs_mul]
          calc |h u - k u| * |h (u + y)| ≤ |h u - k u| * 1 :=
                mul_le_mul_of_nonneg_left (hh1 (u + y)) (abs_nonneg _)
            _ = |h u - k u| := mul_one _
      _ ≤ 2 * w := hd2w
  have hb2 : |∫ u, k u * (h (u + y) - k (u + y))| ≤ 2 * w := by
    have htrans : ∫ u, |h (u + y) - k (u + y)| = ∫ u, |h u - k u| :=
      MeasureTheory.integral_add_right_eq_self (fun u => |h u - k u|) y
    calc |∫ u, k u * (h (u + y) - k (u + y))|
        ≤ ∫ u, |k u * (h (u + y) - k (u + y))| := MeasureTheory.abs_integral_le_integral_abs
      _ ≤ ∫ u, |h (u + y) - k (u + y)| := by
          apply MeasureTheory.integral_mono_of_nonneg
            (MeasureTheory.ae_of_all _ fun u => abs_nonneg _) (hint_dy.abs)
            (MeasureTheory.ae_of_all _ fun u => ?_)
          show |k u * (h (u + y) - k (u + y))| ≤ |h (u + y) - k (u + y)|
          rw [abs_mul]
          calc |k u| * |h (u + y) - k (u + y)| ≤ 1 * |h (u + y) - k (u + y)| :=
                mul_le_mul_of_nonneg_right (hk1 u) (abs_nonneg _)
            _ = _ := one_mul _
      _ = ∫ u, |h u - k u| := htrans
      _ ≤ 2 * w := hd2w
  calc |Params.autocorr h y - L * XiPrime.vConv vTheta (y / L)|
      = |(∫ u, (h u - k u) * h (u + y)) + ∫ u, k u * (h (u + y) - k (u + y))| := by rw [hdecomp]
    _ ≤ |∫ u, (h u - k u) * h (u + y)| + |∫ u, k u * (h (u + y) - k (u + y))| := abs_add_le _ _
    _ ≤ 4 * w := by linarith

end Zeta23Ext.Bridge.WinTheta

end

/-! ###### the scale-free moments of `cos(3s/2)` in closed form, and the constant `Htheta` ###### -/

noncomputable section
set_option linter.unusedSectionVars false

open Real Set MeasureTheory Filter Topology intervalIntegral
open Zeta23

namespace Zeta23Ext.Bridge

/-- `∫_{-1/2}^{1/2} cos(3s/2) ds = (4/3) sin(3/4)`. -/
theorem integral_vTheta : ∫ s in (-(1:ℝ)/2)..(1/2), vTheta s = 4 / 3 * Real.sin (3 / 4) := by
  have h : ∀ x ∈ Set.uIcc (-(1:ℝ)/2) (1/2),
      HasDerivAt (fun s => 2 / 3 * Real.sin (3 / 2 * s)) (vTheta x) x := by
    intro x _
    have h1 := (((hasDerivAt_id x).const_mul (3 / 2 : ℝ)).sin).const_mul (2 / 3 : ℝ)
    simp only [id, mul_one] at h1
    unfold vTheta
    exact h1.congr_deriv (by ring)
  rw [integral_eq_sub_of_hasDerivAt h (vTheta_continuous.intervalIntegrable _ _),
    show (3 / 2 : ℝ) * (1 / 2) = 3 / 4 by norm_num,
    show (3 / 2 : ℝ) * (-(1:ℝ) / 2) = -(3 / 4) by norm_num, Real.sin_neg]
  ring

/-- `∫_{-1/2}^{1/2} cos²(3s/2) ds = 1/2 + sin(3/2)/3`. -/
theorem integral_vTheta_sq :
    ∫ s in (-(1:ℝ)/2)..(1/2), vTheta s ^ 2 = 1 / 2 + Real.sin (3 / 2) / 3 := by
  have h : ∀ x ∈ Set.uIcc (-(1:ℝ)/2) (1/2),
      HasDerivAt (fun s => 1 / 2 * s + 1 / 6 * Real.sin (3 * s)) (vTheta x ^ 2) x := by
    intro x _
    have h1 := ((hasDerivAt_id x).const_mul (1 / 2 : ℝ)).add
      ((((hasDerivAt_id x).const_mul (3 : ℝ)).sin).const_mul (1 / 6 : ℝ))
    simp only [id, mul_one] at h1
    refine h1.congr_deriv ?_
    unfold vTheta
    rw [Real.cos_sq, show 2 * (3 / 2 * x) = 3 * x by ring]
    ring
  rw [integral_eq_sub_of_hasDerivAt h ((vTheta_continuous.pow 2).intervalIntegrable _ _),
    show (3 : ℝ) * (1 / 2) = 3 / 2 by norm_num,
    show (3 : ℝ) * (-(1:ℝ) / 2) = -(3 / 2) by norm_num, Real.sin_neg]
  ring

/-- the profile autocorrelation `(v⋆v)(r) = (1−r)cos(3r/2)/2 + sin(3(1−r)/2)/3`. -/
theorem vConv_vTheta (r : ℝ) :
    XiPrime.vConv vTheta r
      = (1 - r) * Real.cos (3 / 2 * r) / 2 + Real.sin (3 / 2 * (1 - r)) / 3 := by
  unfold XiPrime.vConv
  have h : ∀ x ∈ Set.uIcc (-(1:ℝ)/2) (1/2 - r),
      HasDerivAt (fun s => s * Real.cos (3 / 2 * r) / 2 + Real.sin (3 / 2 * (2 * s + r)) / 6)
        (vTheta x * vTheta (x + r)) x := by
    intro x _
    have h1 := ((hasDerivAt_id x).mul_const (Real.cos (3 / 2 * r))).div_const 2
    have h2 := (((((hasDerivAt_id x).const_mul (2 : ℝ)).add_const r).const_mul
      (3 / 2 : ℝ)).sin).div_const 6
    have h3 := h1.add h2
    simp only [id, mul_one, one_mul] at h3
    refine h3.congr_deriv ?_
    have key : vTheta x * vTheta (x + r)
        = (Real.cos (3 / 2 * r) + Real.cos (3 / 2 * (2 * x + r))) / 2 := by
      unfold vTheta
      have e1 : (3 / 2 : ℝ) * r = 3 / 2 * (x + r) - 3 / 2 * x := by ring
      have e2 : (3 / 2 : ℝ) * (2 * x + r) = 3 / 2 * x + 3 / 2 * (x + r) := by ring
      rw [e1, e2, Real.cos_sub, Real.cos_add]; ring
    rw [key]; ring
  rw [integral_eq_sub_of_hasDerivAt h ((vTheta_continuous.mul
    (vTheta_continuous.comp (continuous_id.add continuous_const))).intervalIntegrable _ _)]
  have e3 : Real.sin (3 / 2 * (2 * (1 / 2 - r) + r)) = Real.sin (3 / 2 * (1 - r)) := by
    congr 1; ring
  have e4 : Real.sin (3 / 2 * (2 * (-(1:ℝ) / 2) + r)) = -Real.sin (3 / 2 * (1 - r)) := by
    rw [← Real.sin_neg]; congr 1; ring
  simp only [e3, e4]
  ring

/-- `𝒥_id(1; v) = 2∫₀¹ r (v⋆v)(r) dr = (8/27) sin(3/2) − (4/9) cos(3/2)`. -/
theorem jWin_vTheta :
    XiPrime.jWin id 1 vTheta = 8 / 27 * Real.sin (3 / 2) - 4 / 9 * Real.cos (3 / 2) := by
  have hderiv : ∀ x ∈ Set.uIcc (0:ℝ) 1, HasDerivAt
      (fun r : ℝ => 4 / 27 * (-(9 / 4) * (r * (r - 1)) * Real.sin (3 / 2 * r)
        + 3 / 2 * r * Real.cos (3 / 2 * (1 - r)) - 3 / 2 * (2 * r - 1) * Real.cos (3 / 2 * r)
        + 2 * Real.sin (3 / 2 * r) + Real.sin (3 / 2 * (1 - r))))
      (x * ((1 - x) * Real.cos (3 / 2 * x) / 2 + Real.sin (3 / 2 * (1 - x)) / 3)) x := by
    intro x _
    have hid := hasDerivAt_id x
    have hs := (hid.const_mul (3 / 2 : ℝ)).sin
    have hc := (hid.const_mul (3 / 2 : ℝ)).cos
    have hs1 := ((hid.const_sub 1).const_mul (3 / 2 : ℝ)).sin
    have hc1 := ((hid.const_sub 1).const_mul (3 / 2 : ℝ)).cos
    have hp := hid.mul (hid.sub_const 1)
    have h := (((((hp.const_mul (-(9 / 4) : ℝ)).mul hs).add
      ((hid.const_mul (3 / 2 : ℝ)).mul hc1)).sub
      ((((hid.const_mul (2 : ℝ)).sub_const 1).const_mul (3 / 2 : ℝ)).mul hc)).add
      (hs.const_mul (2 : ℝ))).add hs1 |>.const_mul (4 / 27 : ℝ)
    simp only [id, Pi.mul_apply] at h
    exact h.congr_deriv (by ring)
  have hcongr : ∫ r in (0:ℝ)..1, (id (1 * r) * XiPrime.vConv vTheta r)
      = ∫ r in (0:ℝ)..1,
          r * ((1 - r) * Real.cos (3 / 2 * r) / 2 + Real.sin (3 / 2 * (1 - r)) / 3) := by
    refine intervalIntegral.integral_congr fun r _ => ?_
    simp only [id, one_mul, vConv_vTheta]
  unfold XiPrime.jWin
  rw [hcongr, integral_eq_sub_of_hasDerivAt hderiv (by
    apply Continuous.intervalIntegrable; fun_prop)]
  norm_num
  ring

/-- the scale-free window functional at `λ = 1`, in closed form. -/
theorem cWin_vTheta : XiPrime.cWin id 1 vTheta
    = (4 / 3 * Real.sin (3 / 4)) ^ 2
      / (1 / 2 + Real.sin (3 / 2) / 3 + (8 / 27 * Real.sin (3 / 2) - 4 / 9 * Real.cos (3 / 2))) := by
  unfold XiPrime.cWin
  rw [integral_vTheta, integral_vTheta_sq, jWin_vTheta, one_mul, one_mul]

/-- **`Htheta = 2 − 1/c(vTheta)`**, the constant the window `cos(3s/2)` delivers. -/
theorem Htheta_eq : Htheta = 2 - (XiPrime.cWin id 1 vTheta)⁻¹ := by
  rw [cWin_vTheta, inv_div]; rfl

lemma sin_three_quarters_pos : 0 < Real.sin (3 / 4) :=
  Real.sin_pos_of_pos_of_lt_pi (by norm_num) (by linarith [Real.pi_gt_three])

lemma integral_vTheta_pos : 0 < ∫ s in (-(1:ℝ)/2)..(1/2), vTheta s := by
  rw [integral_vTheta]; linarith [sin_three_quarters_pos]

lemma integral_vTheta_sq_pos : 0 < ∫ s in (-(1:ℝ)/2)..(1/2), vTheta s ^ 2 := by
  rw [integral_vTheta_sq]; linarith [Real.neg_one_le_sin (3 / 2)]

lemma jWin_vTheta_nonneg {lam : ℝ} (h0 : 0 ≤ lam) (h1 : lam ≤ 1) : 0 ≤ XiPrime.jWin id lam vTheta :=
  XiPrime.jWin_nonneg (fun x hx => hx.1) (fun s hs => vTheta_nonneg_on hs) h0 h1

lemma cWin_vTheta_pos {lam : ℝ} (h0 : 0 < lam) (h1 : lam ≤ 1) : 0 < XiPrime.cWin id lam vTheta :=
  XiPrime.cWin_pos integral_vTheta_pos.ne' integral_vTheta_sq_pos (jWin_vTheta_nonneg h0.le h1) h0

namespace WinTheta

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

theorem sin_three_quarters_bounds :
    (1408915287573 / 2066953011200 - 1 / 10 ^ 10 : ℝ) ≤ Real.sin (3 / 4)
      ∧ Real.sin (3 / 4) ≤ 1408915287573 / 2066953011200 + 1 / 10 ^ 10 := by
  have h := (cos_sin_taylor12 (3 / 4) (by rw [abs_of_pos (by norm_num)]; norm_num)).2
  rw [abs_of_pos (by norm_num : (0:ℝ) < 3 / 4)] at h
  have h' := abs_le.mp h
  constructor <;> norm_num at h' ⊢ <;> linarith [h'.1, h'.2]

theorem cos_three_quarters_bounds :
    (34371966151 / 46976204800 - 1 / 10 ^ 10 : ℝ) ≤ Real.cos (3 / 4)
      ∧ Real.cos (3 / 4) ≤ 34371966151 / 46976204800 + 1 / 10 ^ 10 := by
  have h := (cos_sin_taylor12 (3 / 4) (by rw [abs_of_pos (by norm_num)]; norm_num)).1
  rw [abs_of_pos (by norm_num : (0:ℝ) < 3 / 4)] at h
  have h' := abs_le.mp h
  constructor <;> norm_num at h' ⊢ <;> linarith [h'.1, h'.2]

end WinTheta

/-- `Htheta = 3/2 − 1/(32 sin²(3/4)) − (17/24) cot(3/4)`. -/
theorem Htheta_eq_cot : Htheta
    = 3 / 2 - 1 / (32 * Real.sin (3 / 4) ^ 2) - 17 / 24 * (Real.cos (3 / 4) / Real.sin (3 / 4)) := by
  have hs : Real.sin (3 / 4) ≠ 0 := sin_three_quarters_pos.ne'
  have h2 : Real.sin (3 / 2) = 2 * Real.sin (3 / 4) * Real.cos (3 / 4) := by
    rw [← Real.sin_two_mul]; norm_num
  have h3 : Real.cos (3 / 2) = 1 - 2 * Real.sin (3 / 4) ^ 2 := by
    rw [show (3 / 2 : ℝ) = 2 * (3 / 4) by norm_num, Real.cos_two_mul]
    linarith [Real.sin_sq_add_cos_sq (3 / 4 : ℝ)]
  unfold Htheta
  rw [h2, h3]
  field_simp
  ring

/-- **`Htheta` enclosed to `5·10⁻¹⁰`.** -/
theorem Htheta_bounds :
    (6723988624 / 10000000000 : ℝ) ≤ Htheta ∧ Htheta ≤ 6723988629 / 10000000000 := by
  obtain ⟨hs1, hs2⟩ := WinTheta.sin_three_quarters_bounds
  obtain ⟨hk1, hk2⟩ := WinTheta.cos_three_quarters_bounds
  set s := Real.sin (3 / 4) with hsdef
  set k := Real.cos (3 / 4) with hkdef
  set slo : ℝ := 1408915287573 / 2066953011200 - 1 / 10 ^ 10 with hslo
  set shi : ℝ := 1408915287573 / 2066953011200 + 1 / 10 ^ 10 with hshi
  set klo : ℝ := 34371966151 / 46976204800 - 1 / 10 ^ 10 with hklo
  set khi : ℝ := 34371966151 / 46976204800 + 1 / 10 ^ 10 with hkhi
  have hslo0 : 0 < slo := by rw [hslo]; norm_num
  have hklo0 : 0 < klo := by rw [hklo]; norm_num
  have hs0 : 0 < s := lt_of_lt_of_le hslo0 hs1
  have hk0 : 0 < k := lt_of_lt_of_le hklo0 hk1
  rw [Htheta_eq_cot]
  constructor
  · have e1 : 1 / (32 * s ^ 2) ≤ 1 / (32 * slo ^ 2) :=
      one_div_le_one_div_of_le (by positivity) (by nlinarith)
    have e2 : k / s ≤ khi / slo := by
      rw [div_le_div_iff₀ hs0 hslo0]; nlinarith
    have hnum : (6723988624 / 10000000000 : ℝ) ≤ 3 / 2 - 1 / (32 * slo ^ 2) - 17 / 24 * (khi / slo) := by
      rw [hslo, hkhi]; norm_num
    nlinarith
  · have e1 : 1 / (32 * shi ^ 2) ≤ 1 / (32 * s ^ 2) :=
      one_div_le_one_div_of_le (by positivity) (by nlinarith)
    have e2 : klo / shi ≤ k / s := by
      rw [div_le_div_iff₀ (by linarith) hs0]; nlinarith
    have hnum : 3 / 2 - 1 / (32 * shi ^ 2) - 17 / 24 * (klo / shi) ≤ (6723988629 / 10000000000 : ℝ) := by
      rw [hshi, hklo]; norm_num
    nlinarith

end Zeta23Ext.Bridge

end

/-! ###### the window `cos(3s/2)` at parameter level: ranges, zero side, local hypotheses ###### -/

noncomputable section
set_option linter.unusedSectionVars false

open Real Set MeasureTheory Filter Topology
open Zeta23

namespace Zeta23Ext.Bridge

open WinTheta

variable {P : Params}

lemma integral_vTheta_ge : 3 / 4 ≤ ∫ s in (-(1:ℝ)/2)..(1/2), vTheta s := by
  rw [integral_vTheta]
  have := WinTheta.sin_three_quarters_bounds.1
  norm_num at this ⊢; linarith

lemma integral_vTheta_sq_ge : 3 / 4 ≤ ∫ s in (-(1:ℝ)/2)..(1/2), vTheta s ^ 2 := by
  rw [integral_vTheta_sq, show (3 / 2 : ℝ) = 2 * (3 / 4) by norm_num, Real.sin_two_mul]
  have hs := WinTheta.sin_three_quarters_bounds.1
  have hk := WinTheta.cos_three_quarters_bounds.1
  norm_num at hs hk ⊢
  nlinarith

theorem aV_theta_close (hP : P.Valid) {T : ℝ} (hwL : 8 * P.w ≤ P.L T) :
    |AdmWindow.av (P.phiV vTheta T) (P.L T) - ∫ s in (-(1:ℝ)/2)..(1/2), vTheta s|
      ≤ 2 * P.w / P.L T := by
  rw [phiV_theta_eq]; exact aT_close hP.taper hP.one_le_w hwL

theorem bV_theta_close (hP : P.Valid) {T : ℝ} (hwL : 8 * P.w ≤ P.L T) :
    |AdmWindow.bv (P.phiV vTheta T) (P.L T) - ∫ s in (-(1:ℝ)/2)..(1/2), vTheta s ^ 2|
      ≤ 2 * P.w / P.L T := by
  rw [phiV_theta_eq]; exact bT_close hP.taper hP.one_le_w hwL

lemma two_w_div_le (hP : P.Valid) {T : ℝ} (hwL : 8 * P.w ≤ P.L T) : 2 * P.w / P.L T ≤ 1 / 4 := by
  have hL : 0 < P.L T := by linarith [hP.one_le_w]
  rw [div_le_iff₀ hL]; linarith

theorem bV_theta_ge_half (hP : P.Valid) {T : ℝ} (hwL : 8 * P.w ≤ P.L T) :
    1 / 2 ≤ AdmWindow.bv (P.phiV vTheta T) (P.L T) := by
  have h := bV_theta_close hP hwL
  linarith [(abs_le.mp h).1, two_w_div_le hP hwL, integral_vTheta_sq_ge]

theorem aV_theta_range (hP : P.Valid) {T : ℝ} (hwL : 8 * P.w ≤ P.L T) :
    1 / 2 ≤ (P.atV vTheta T).a T ∧ (P.atV vTheta T).a T ≤ 1 := by
  rw [Params.atV_a T hP vTheta_even]
  refine ⟨?_, (admWindow_theta hP hwL).av_le_one⟩
  have h := aV_theta_close hP hwL
  linarith [(abs_le.mp h).1, two_w_div_le hP hwL, integral_vTheta_ge]

theorem gV_theta_close_at (hP : P.Valid) {T : ℝ} (hwL : 8 * P.w ≤ P.L T) {y : ℝ}
    (hy : y ∈ Icc (0:ℝ) (P.L T)) :
    |AdmWindow.gv (P.phiV vTheta T) y - P.L T * XiPrime.vConv vTheta (y / P.L T)| ≤ 4 * P.w := by
  rw [phiV_theta_eq]; exact autocorr_phiMTsq_close hP.taper hP.one_le_w hwL hy.1 hy.2

/-- the §5 `LocalHypsCore` for the `cos(3s/2)` data, eventually. -/
theorem localHypsCoreT_eventually (hP : P.Valid) :
    ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T →
      PrimeSide.LocalHypsCore (cTh P.ϱ) (P.toSetting T)
        (AdmWindow.localFun (P.phiV vTheta T) (P.L T)) := by
  have hl : Tendsto l atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_id.atTop_div_const (by positivity))
  have hL : Tendsto P.L atTop atTop := hl.const_mul_atTop hP.lam_pos
  have hX : ∀ᶠ T in atTop, 1 ≤ P.X T := by
    filter_upwards [hL.eventually_ge_atTop 0] with T h
    simpa [Params.X] using Real.one_le_exp h
  obtain ⟨T₀, hT₀⟩ := eventually_atTop.mp ((hl.eventually_ge_atTop 1).and
    ((hL.eventually_ge_atTop (8 * P.w)).and hX))
  refine ⟨T₀, fun T hT => ?_⟩
  obtain ⟨h1, h8, hX1⟩ := hT₀ T hT
  exact AdmWindow.localHypsCore (P.toSetting T) (admWindow_theta hP h8) hP.lam_pos hP.lam_le_one
    h1 hX1 (bV_theta_ge_half hP h8)

/-! ### the zero side (instances of the profile-generic zero side of `XiPrime.QuarticWindow`) -/

theorem hW_theta (hP : P.Valid) :
    ∀ T : ℝ, 8 * P.w ≤ P.L T → AdmWindow (P.phiV vTheta T) (P.L T) P.w (cTh P.ϱ) :=
  fun _ h => admWindow_theta hP h

theorem poissonSqT (hP : P.Valid) {T : ℝ} (h8 : 8 * P.w ≤ P.L T) :
    ZeroSide.PoissonSq T (P.atV vTheta T) :=
  XiPrime.poissonSqV_of hP vTheta_even (hW_theta hP) h8

theorem eventually_GzGpT (Z : ZeroConfig) (H : PaperInputs Z) (hP : P.Valid) :
    ∀ᶠ T in atTop, Z.Gz (P.atV vTheta T) T = (P.atV vTheta T).Gp T := by
  filter_upwards [ThmD.eventually_w8 hP] with T h8
  exact XiPrime.GzGpV_of' hP vTheta_even (hW_theta hP) Z H.EF h8

theorem eventually_tailPackageT (Z : ZeroConfig) (H : PaperInputs Z) (hP : P.Valid) :
    ∃ θ₀ : ℝ → ℝ, (∀ᶠ T in atTop, Assembly.TailInputs Z (P.atV vTheta T) T (θ₀ T)) ∧
      ∃ C : ℝ, ∀ᶠ T in atTop, θ₀ T ≤ C * l T * T ^ (P.lam / 2 - 1) := by
  obtain ⟨A₀, hA₀, hloc⟩ := H.RvM.local_count
  exact XiPrime.eventually_tailPackageV_of hP vTheta_even (hW_theta hP)
    ((ThmD.eventually_w8 hP).mono fun T h8 => (aV_theta_range hP h8).1) Z hA₀ hloc

end Zeta23Ext.Bridge

end

/-! ###### the window `cos(3s/2)`: the prime side (`FactsD`) and the ratio limit ###### -/

noncomputable section
set_option linter.unusedSectionVars false

open Real Filter Topology MeasureTheory
open scoped BigOperators ArithmeticFunction
open Zeta23 Zeta23.ThmD Zeta23.PrimeSide Zeta23.PaperParams

namespace Zeta23Ext.Bridge.WinTheta

variable {P : Params}

/-- the abstract local data of the window `cos(3s/2)` at height `T`. -/
def FT (P : Params) (T : ℝ) : LocalFun := AdmWindow.localFun (P.phiV vTheta T) (P.L T)

/-- the concrete D-data of the window `cos(3s/2)` (`ThmD.concreteDataD` with `φ_D ↦ φ_θ`). -/
def dataT (P : Params) (Z : ZeroConfig) : DataD P where
  aT := fun T => (FT P T).a
  bT := fun T => (FT P T).b
  trG := fun T => trGtA (P.toSetting T) (FT P T)
  trG2 := fun T => trGt2A (P.toSetting T) (FT P T)
  Ncnt := fun T => (Z.N T (2 * T) : ℝ)
  Mtot := fun T => MtotalA (P.toSetting T) (FT P T)
  Mmumu := fun T => Mform (FT P T).Phi T Zeta23.mu Zeta23.mu
  MPP := fun T => Mform (FT P T).Phi T (Zeta23.PX (P.X T)) (Zeta23.PX (P.X T))
  MmuP := fun T => Mform (FT P T).Phi T Zeta23.mu (Zeta23.PX (P.X T))
  MmuPi := fun T => Mform (FT P T).Phi T Zeta23.mu (Zeta23.PiX (P.X T))
  MPPi := fun T => Mform (FT P T).Phi T (Zeta23.PX (P.X T)) (Zeta23.PiX (P.X T))
  MPiPi := fun T => Mform (FT P T).Phi T (Zeta23.PiX (P.X T)) (Zeta23.PiX (P.X T))
  intMu2 := fun T => ∫ τ in T..(2 * T), Zeta23.mu τ ^ 2
  sumL2g := fun T => sumA2g (P.X T) (FT P T).g
  JT := fun T => 2 / P.L T ^ 3 * ∫ y in (0:ℝ)..(P.L T), (FT P T).g y * y

/-- the taper hypotheses of §5 for the `cos(3s/2)` data, eventually. -/
def LocalHypsCoreTEventually (P : Params) : Prop :=
  ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T → LocalHypsCore (cTh P.ϱ) (P.toSetting T) (FT P T)

lemma localHypsCoreTEventually_of (hP : P.Valid) : LocalHypsCoreTEventually P :=
  localHypsCoreT_eventually hP

lemma evBound_of_eventuallyAtCoreT (hLoc : LocalHypsCoreTEventually P)
    {f g : Setting → LocalFun → ℝ}
    (h : ∃ C : ℝ, EventuallyAtCore (cTh P.ϱ) P.lam (fun p F => |f p F| ≤ C * g p F))
    (hg : ∀ᶠ T in atTop, 0 ≤ g (P.toSetting T) (FT P T)) :
    EvBound (fun T => f (P.toSetting T) (FT P T)) (fun T => g (P.toSetting T) (FT P T)) := by
  obtain ⟨T₀, hT₀⟩ := hLoc
  obtain ⟨C, T₁, hT₁⟩ := h
  obtain ⟨T₂, hT₂⟩ := eventually_atTop.mp hg
  refine ⟨max C 1, by positivity, max T₀ (max T₁ T₂), fun T hT => ?_⟩
  have h0 : T₀ ≤ T := (le_max_left _ _).trans hT
  have h1 : T₁ ≤ T := ((le_max_left _ _).trans (le_max_right _ _)).trans hT
  have h2 : T₂ ≤ T := ((le_max_right _ _).trans (le_max_right _ _)).trans hT
  have := hT₁ (P.toSetting T) (FT P T) rfl h1 (hT₀ T h0)
  calc |f (P.toSetting T) (FT P T)| ≤ C * g (P.toSetting T) (FT P T) := this
    _ ≤ max C 1 * g (P.toSetting T) (FT P T) :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) (hT₂ T h2)

/-- C¹ facts for `g = v² ⋆ v²` of an admissible window. -/
lemma gv_deriv_facts' {v : ℝ → ℝ} {L w c : ℝ} (hW : AdmWindow v L w c) :
    Differentiable ℝ (AdmWindow.gv v) ∧ Continuous (deriv (AdmWindow.gv v))
      ∧ ∀ y : ℝ, |deriv (AdmWindow.gv v) y| ≤ 2 := by
  apply ThmD.autocorr_deriv_facts
  · exact (hW.contDiff.pow 2).of_le (by norm_num)
  · exact hW.sq_hasCompactSupport
  · intro x; exact hW.sq_even x
  · intro u
    rw [abs_of_nonneg (sq_nonneg _)]
    calc v u ^ 2 ≤ 1 ^ 2 := pow_le_pow_left₀ (hW.nonneg u) (hW.le_one u) 2
      _ = 1 := one_pow 2
  · exact hW.l1_deriv_sq

/-- **FactsD for the `cos(3s/2)` data** (`ThmD.concreteFactsD` with `φ_D ↦ φ_θ`). -/
theorem concreteFactsT {Z : ZeroConfig} (hP : P.Valid) (inp : PaperInputs Z)
    (hLoc : LocalHypsCoreTEventually P) : FactsD (dataT P Z) := by
  have hlam : 0 < P.lam ∧ P.lam ≤ 1 := ⟨hP.lam_pos, hP.lam_le_one⟩
  have hΓ := inp.Gamma
  have hcheb := inp.cheb
  set cϱD := cTh P.ϱ with hcD
  have hreg : ∀ᶠ T in atTop, 0 ≤ T ∧ 0 ≤ l T ∧ 0 ≤ Real.log (l T) ∧ 0 ≤ P.L T ∧ 0 ≤ P.X T := by
    filter_upwards [eventually_ge_atTop 1, eventually_l_ge 1, eventually_log_l_ge 1,
      eventually_L_ge P hP.lam_pos 1, eventually_one_le_X P hP.lam_pos] with T h1 h2 h3 h4 h5
    exact ⟨by linarith, by linarith, by linarith, by linarith, by linarith⟩
  obtain ⟨T₀, hT₀⟩ := id hLoc
  have e_ends := evBound_of_eventuallyAtCoreT hLoc
    (PrimeSide.lem_ends cϱD P.lam hΓ hcheb hlam) (by
    filter_upwards [hreg] with T ⟨hT, hl, hlog, hL, hX⟩
    exact mul_nonneg (mul_nonneg (mul_nonneg hL hl) hlog) (add_nonneg (sq_nonneg _) hX))
  have e_mumu := evBound_of_eventuallyAtCoreT hLoc
    (PrimeSide.prop_mumu cϱD P.lam hΓ hcheb hlam) (by
    filter_upwards [hreg, eventually_L_ge P hP.lam_pos 1] with T ⟨hT, hl, hlog, hL, hX⟩ hL1
    exact mul_nonneg (sq_nonneg _) (Real.log_nonneg hL1))
  have e_PP := evBound_of_eventuallyAtCoreT hLoc
    (PrimeSide.prop_PP (cϱ := cϱD) (lam := P.lam) hcheb inp.MV hlam) (by
    filter_upwards [hreg] with T ⟨hT, hl, hlog, hL, hX⟩
    exact mul_nonneg (sq_nonneg _) hX)
  have e_muP := evBound_of_eventuallyAtCoreT hLoc
    (PrimeSide.prop_cross_muP cϱD P.lam hΓ hcheb hlam) (by
    filter_upwards [hreg] with T ⟨hT, hl, hlog, hL, hX⟩
    exact mul_nonneg hl (Real.sqrt_nonneg _))
  have e_muPi := evBound_of_eventuallyAtCoreT hLoc
    (PrimeSide.prop_cross_muPi cϱD P.lam hΓ hcheb hlam) (by
    filter_upwards [hreg] with T ⟨hT, hl, hlog, hL, hX⟩
    exact mul_nonneg (mul_nonneg hl hL) (Real.sqrt_nonneg _))
  have e_PPi := evBound_of_eventuallyAtCoreT hLoc
    (PrimeSide.prop_cross_PPi cϱD P.lam hΓ hcheb hlam) (by
    filter_upwards [hreg] with T ⟨hT, hl, hlog, hL, hX⟩
    exact mul_nonneg hL hX)
  have e_PiPi := evBound_of_eventuallyAtCoreT hLoc
    (PrimeSide.prop_cross_PiPi cϱD P.lam hΓ hcheb hlam) (by
    filter_upwards [hreg] with T ⟨hT, hl, hlog, hL, hX⟩
    exact div_nonneg (mul_nonneg hL hX) hT)
  refine ⟨hP.lam_pos, hP.lam_le_one, hP.one_le_w, ?ab_range, rvm_evBound inp.RvM, ?muints2,
    ?prop_trace, e_ends, ?Msplit, e_mumu, e_PP, ?sumJ, e_muP, e_muPi, e_PPi, e_PiPi⟩
  case ab_range =>
    filter_upwards [eventually_ge_atTop T₀, eventually_L_ge P hP.lam_pos 8,
      eventually_L_ge P hP.lam_pos (8 * P.w)] with T hT hL8 hLw
    have hF := hT₀ T hT
    have hL0 : 0 < P.L T := by linarith
    refine ⟨hF.b_ge_half, hF.b_le_a, hF.a_le_one, ?_, ?_⟩
    · apply mul_nonneg (by positivity)
      apply intervalIntegral.integral_nonneg (by linarith : (0:ℝ) ≤ P.L T)
      intro y hy
      exact mul_nonneg (hF.g_nonneg y) hy.1
    · have hgcont : Continuous (FT P T).g := (admWindow_theta hP hLw).gv_continuous
      have hgle : ∀ y ∈ Set.Icc (0:ℝ) (P.L T), (FT P T).g y * y ≤ P.L T * y := by
        intro y hy
        apply mul_le_mul_of_nonneg_right _ hy.1
        calc (FT P T).g y ≤ (FT P T).Aphi y := hF.g_le_Aphi y
          _ ≤ max ((P.toSetting T).L - |y|) 0 := hF.Aphi_le y
          _ ≤ P.L T := by
              apply max_le _ hL0.le
              have := abs_nonneg y
              show (P.toSetting T).L - |y| ≤ P.L T
              have e : (P.toSetting T).L = P.L T := rfl
              rw [e]
              linarith
      have hIle : ∫ y in (0:ℝ)..(P.L T), (FT P T).g y * y
          ≤ ∫ y in (0:ℝ)..(P.L T), P.L T * y := by
        apply intervalIntegral.integral_mono_on (by linarith : (0:ℝ) ≤ P.L T) ?_ ?_ hgle
        · exact (hgcont.mul continuous_id).intervalIntegrable 0 (P.L T)
        · exact (continuous_const.mul continuous_id).intervalIntegrable 0 (P.L T)
      have hIval : ∫ y in (0:ℝ)..(P.L T), P.L T * y = P.L T ^ 3 / 2 := by
        rw [intervalIntegral.integral_const_mul, integral_id]
        ring
      calc 2 / P.L T ^ 3 * ∫ y in (0:ℝ)..(P.L T), (FT P T).g y * y
          ≤ 2 / P.L T ^ 3 * (P.L T ^ 3 / 2) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            rw [← hIval]
            exact hIle
        _ = 1 := by field_simp
  case muints2 =>
    obtain ⟨C, T₁, hC⟩ := hΓ.int_mu_sq
    refine ⟨max C 1, by positivity, max T₁ 0, fun T hT =>
      (hC T ((le_max_left _ _).trans hT)).trans ?_⟩
    have hT0 : 0 ≤ T := (le_max_right _ _).trans hT
    rw [mul_div_assoc]
    refine mul_le_mul_of_nonneg_right (le_max_left _ _) ?_
    exact div_nonneg (div_nonneg (mul_nonneg hT0 (sq_nonneg _)) (by positivity)) (sq_nonneg _)
  case prop_trace =>
    obtain ⟨A, hA, T₁, hN⟩ := rvm_evBound inp.RvM
    obtain ⟨C, T₂, hC⟩ := PrimeSide.prop_trace cϱD P.lam hΓ hcheb hlam A
    refine ⟨max C 1, by positivity, max T₀ (max T₁ T₂), fun T hT => ?_⟩
    have h0 : T₀ ≤ T := (le_max_left _ _).trans hT
    have h1 : T₁ ≤ T := ((le_max_left _ _).trans (le_max_right _ _)).trans hT
    have h2 : T₂ ≤ T := ((le_max_right _ _).trans (le_max_right _ _)).trans hT
    have hF := hT₀ T h0
    have := hC (P.toSetting T) (FT P T) rfl h2 hF (Z.N T (2 * T) : ℝ) (hN T h1)
    refine this.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) ?_)
    exact mul_nonneg hF.L_pos.le (Real.sqrt_nonneg _)
  case Msplit =>
    filter_upwards [eventually_ge_atTop T₀] with T hT
    exact eq_Msplit cϱD hΓ (P.toSetting T) (FT P T) (hT₀ T hT)
  case sumJ =>
    obtain ⟨C, hC0, hC⟩ := ThmD.sumA2g_close hcheb
    refine ⟨C, hC0, ?_⟩
    obtain ⟨T₁, hT₁⟩ := eventually_atTop.mp (eventually_L_ge P hP.lam_pos 8)
    obtain ⟨T₂, hT₂⟩ := eventually_atTop.mp (eventually_L_ge P hP.lam_pos (8 * P.w))
    refine ⟨max T₀ (max T₁ T₂), fun T hT => ?_⟩
    have h1 : T₁ ≤ T := ((le_max_left _ _).trans (le_max_right _ _)).trans hT
    have h2 : T₂ ≤ T := ((le_max_right _ _).trans (le_max_right _ _)).trans hT
    have hL8 : 8 ≤ P.L T := hT₁ T h1
    have hLw : 8 * P.w ≤ P.L T := hT₂ T h2
    have hL0 : 0 < P.L T := by linarith
    have hW := admWindow_theta hP hLw
    have hg := gv_deriv_facts' hW
    have hgsupp : ∀ y : ℝ, P.L T ≤ y → (FT P T).g y = 0 := by
      intro y hy
      exact hW.gv_eq_zero (by rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ y)]; exact hy)
    have key := hC (P.L T) (P.X T) (FT P T).g hL8 (by
        show P.X T = Real.exp (P.L T)
        rfl) hg.1 hg.2.1 hg.2.2 hgsupp
    have e : P.L T ^ 3 / 2 * ((dataT P Z).JT T)
        = ∫ y in (0:ℝ)..(P.L T), (FT P T).g y * y := by
      show P.L T ^ 3 / 2 * (2 / P.L T ^ 3 * ∫ y in (0:ℝ)..(P.L T), (FT P T).g y * y) = _
      field_simp
    show |sumA2g (P.X T) (FT P T).g - P.L T ^ 3 / 2 * ((dataT P Z).JT T)| ≤ C * P.L T ^ 2
    rw [e]
    exact key

/-- **TracesBoundsD for the `cos(3s/2)` window.** -/
theorem tracesBoundsD_theta {Z : ZeroConfig} (hP : P.Valid) (inp : PaperInputs Z) :
    TracesBoundsD P (dataT P Z).aT (dataT P Z).bT (dataT P Z).JT
      (dataT P Z).trG (dataT P Z).trG2 (dataT P Z).Ncnt :=
  tracesBoundsD_of_factsD _ (concreteFactsT hP inp (localHypsCoreTEventually_of hP))

/-- **the `cos(3s/2)` window ratio converges**: `cRatio(λ₁; a_T, b_T, J_T) → c_λ(vTheta; id)`. -/
theorem tendsto_cRatio_theta (hP : P.Valid) (Z : ZeroConfig) :
    Tendsto (fun T => cRatio (P.lam1 T) ((dataT P Z).aT T) ((dataT P Z).bT T) ((dataT P Z).JT T))
      atTop (𝓝 (XiPrime.cWin id P.lam vTheta)) := by
  refine XiPrime.tendsto_cRatio_cWin hP.lam_pos (ThmD.tendsto_lam1 hP.lam_pos) ?_ ?_ ?_ ?_
  · apply ThmD.tendsto_of_close hP.lam_pos (C := 2)
    filter_upwards [ThmD.eventually_w8 hP] with T h8
    exact aV_theta_close hP h8
  · apply ThmD.tendsto_of_close hP.lam_pos (C := 2)
    filter_upwards [ThmD.eventually_w8 hP] with T h8
    exact bV_theta_close hP h8
  · have hJ := XiPrime.tendsto_JT_of_autocorr_close (D := id) (v := vTheta) hP continuousOn_id
      vTheta_continuous (g := fun T => AdmWindow.gv (P.phiV vTheta T)) (C := 4)
      ((ThmD.eventually_w8 hP).mono fun T h8 => (admWindow_theta hP h8).gv_continuous)
      ((ThmD.eventually_w8 hP).mono fun T h8 y hy => gV_theta_close_at hP h8 hy)
    refine hJ.congr' ?_
    filter_upwards [Assembly.eventually_l_pos] with T hl
    show 2 / P.L T ^ 3 * l T * ∫ y in (0:ℝ)..P.L T, (id (y / l T) * AdmWindow.gv (P.phiV vTheta T) y)
      = 2 / P.L T ^ 3 * ∫ y in (0:ℝ)..(P.L T), AdmWindow.gv (P.phiV vTheta T) y * y
    rw [mul_assoc, ← intervalIntegral.integral_const_mul]
    congr 1
    refine intervalIntegral.integral_congr fun y _ => ?_
    simp only [id]
    field_simp
  · have h1 := jWin_vTheta_nonneg hP.lam_pos.le hP.lam_le_one
    have h2 := integral_vTheta_sq_pos
    nlinarith [mul_nonneg hP.lam_pos.le h1]

end Zeta23Ext.Bridge.WinTheta

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

theorem endgame_defect (Z : ZeroConfig) (H : PaperInputs Z) (P : Params) (hP : P.Valid) (v : ℝ → ℝ)
    (aT bT JT trG trG2 : ℝ → ℝ)
    (hTr : TracesBoundsD P aT bT JT trG trG2 (fun T => (Z.N T (2 * T) : ℝ)))
    {c : ℝ} (hc0 : 0 < c)
    (hc : Tendsto (fun T => cRatio (P.lam1 T) (aT T) (bT T) (JT T)) atTop (𝓝 c))
    (ha : ∀ᶠ T in atTop, 1 / 2 ≤ aT T ∧ aT T ≤ 1)
    (θ₀ : ℝ → ℝ) (hTail : ∀ᶠ T in atTop, TailInputs Z (P.atV v T) T (θ₀ T))
    (hθ₀ : ∃ C : ℝ, ∀ᶠ T in atTop, θ₀ T ≤ C * l T * T ^ (P.lam / 2 - 1))
    (hNII : ∃ C : ℝ, ∀ᶠ T in atTop, (NII Z T : ℝ) ≤ C * Real.sqrt T * l T)
    (hGzGp : ∀ᶠ T in atTop, Z.Gz (P.atV v T) T = (P.atV v T).Gp T)
    (hId : ∀ᶠ T in atTop, (P.atV v T).trGtilde T = trG T ∧ (P.atV v T).trGtildeSq T = trG2 T ∧
      (P.atV v T).a T = aT T)
    (hcalE : Tendsto P.calE atTop (𝓝 0))
    (D : ℝ → ℝ)
    (hcore : ∀ᶠ T in atTop,
      4 * rtrace ((P.atV v T).hat T (Z.Az (P.atV v T) T))
        - frobSq ((P.atV v T).hat T (Z.Az (P.atV v T) T))
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
    have haposD : 0 < (P.atV v T).a T := by rw [hida]; exact hapos'
    have hLpos : 0 < P.L T := by simp only [Params.L]; positivity

    have hA := seamA_mult2_defect hT0 hTl haposD hLpos hcoreT

    have hrt : rtrace ((P.atV v T).hat T (Z.Gz (P.atV v T) T)) = (aT T * P.L T)⁻¹ * trG T := by
      rw [rtrace_hat, hGG, rtrace_tilde_Gp, hidtr, hida]; rfl
    have hfr : frobSq ((P.atV v T).hat T (Z.Gz (P.atV v T) T))
        = ((aT T * P.L T)⁻¹) ^ 2 * trG2 T := by
      rw [frobSq_hat, hGG, frobSq_tilde_Gp, hidfr, hida]; rfl
    have haL : (P.atV v T).a T * (P.atV v T).L T = aT T * P.L T := by rw [hida]; rfl
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

lemma atV_phiHatR_eq : (P.atV vTheta T).phiHatR T = AdmWindow.vHatR (P.phiV vTheta T) :=
  Params.atV_phiHatR T hP vTheta_even

lemma phiHatReal_atV : PhiHatReal T (P.atV vTheta T) := fun r => GzGp.phiHat_ofReal _ T r

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

lemma Kfun_zero_eq_aI : Kfun 0 = ∫ s in (-(1:ℝ)/2)..(1/2), vTheta s := by
  simp [Kfun, vTheta]

/-- `Kfun 0 = (4/3) sin(3/4)` (`= sinc(3/4)`). -/
lemma Kfun_zero_eq : Kfun 0 = 4 / 3 * Real.sin (3 / 4) := Kfun_zero_eq_aI.trans integral_vTheta

lemma cos_three_halves_mul_pos {t : ℝ} (ht : t ∈ Set.Ioo (-(1 : ℝ) / 2) (1 / 2)) :
    0 < Real.cos ((3 / 2 : ℝ) * t) := by
  apply Real.cos_pos_of_mem_Ioo
  have hπ := Real.pi_gt_three
  constructor <;> nlinarith [ht.1, ht.2]

lemma Kfun_zero_pos : 0 < Kfun 0 := by
  unfold Kfun
  apply intervalIntegral.intervalIntegral_pos_of_pos_on
  · exact (by fun_prop : Continuous fun t : ℝ =>
      Real.cos ((3 / 2 : ℝ) * t) * Real.cos (2 * Real.pi * 0 * t)).intervalIntegrable _ _
  · intro t ht
    simp only [mul_zero, zero_mul, Real.cos_zero, mul_one]
    exact cos_three_halves_mul_pos ht
  · norm_num

lemma abs_Kfun_le (x : ℝ) : |Kfun x| ≤ Kfun 0 := abs_Kfun_le_Kfun_zero x

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

lemma integral_sharpT_mul_cos {L : ℝ} (hL : 0 < L) (x : ℝ) :
    ∫ u, WinTheta.sharpT L u * Real.cos (2 * Real.pi * x / L * u) = L * Kfun x := by
  set f : ℝ → ℝ := fun t => Real.cos ((3 / 2 : ℝ) * t) * Real.cos (2 * Real.pi * x * t) with hf
  have hind : ∀ u, WinTheta.sharpT L u * Real.cos (2 * Real.pi * x / L * u)
      = (Set.Icc (-(L / 2)) (L / 2)).indicator (fun u => f (u / L)) u := by
    intro u
    unfold WinTheta.sharpT
    by_cases hu : u ∈ Set.Icc (-(L / 2)) (L / 2)
    · rw [Set.indicator_of_mem hu, Set.indicator_of_mem hu, hf]
      show vTheta (u / L) * Real.cos (2 * Real.pi * x / L * u)
        = Real.cos ((3 / 2 : ℝ) * (u / L)) * Real.cos (2 * Real.pi * x * (u / L))
      unfold vTheta
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

variable {P : Params} (hP : P.Valid) {T : ℝ} (h8 : 8 * P.w ≤ P.L T)
include hP h8

lemma abs_VPhiR_sub_L_mul_Kfun_le (x : ℝ) :
    |AdmWindow.VPhiR (P.phiV vTheta T) (2 * Real.pi * x / P.L T) - P.L T * Kfun x| ≤ 2 * P.w := by
  have hW := admWindow_theta hP h8
  have hL := hW.L_pos
  have hw : 0 < P.w := hW.w_pos
  set r := 2 * Real.pi * x / P.L T with hr
  have hV : AdmWindow.VPhiR (P.phiV vTheta T) r = ∫ u, P.phiV vTheta T u ^ 2 * Real.cos (r * u) :=
    re_paperFT_ofReal (hW.integrable_pow two_pos) r
  have hS : ∫ u, WinTheta.sharpT (P.L T) u * Real.cos (r * u) = P.L T * Kfun x :=
    integral_sharpT_mul_cos hL x
  have hL1 : ∫ u, |P.phiV vTheta T u ^ 2 - WinTheta.sharpT (P.L T) u| ≤ 2 * P.w := by
    rw [phiV_theta_eq]
    exact WinTheta.integral_abs_phiMTsq_sub_sharp hP.taper hw (by linarith)
  rw [hV, ← hS]
  exact (abs_integral_mul_cos_sub_le (hW.integrable_pow two_pos) WinTheta.sharpT_integrable r).trans
    hL1

lemma abs_aL_sub_L_mul_Kfun_zero_le :
    |(P.atV vTheta T).a T * P.L T - P.L T * Kfun 0| ≤ 2 * P.w := by
  have hL : 0 < P.L T := by linarith [hP.one_le_w]
  have h := aV_theta_close hP h8
  rw [← Kfun_zero_eq_aI] at h
  rw [Params.atV_a T hP vTheta_even]
  have e : AdmWindow.av (P.phiV vTheta T) (P.L T) * P.L T - P.L T * Kfun 0
      = (AdmWindow.av (P.phiV vTheta T) (P.L T) - Kfun 0) * P.L T := by ring
  rw [e, abs_mul, abs_of_pos hL]
  calc |AdmWindow.av (P.phiV vTheta T) (P.L T) - Kfun 0| * P.L T ≤ 2 * P.w / P.L T * P.L T :=
        mul_le_mul_of_nonneg_right h hL.le
    _ = 2 * P.w := by field_simp

lemma abs_VPhiR_div_sub_kfun_le (x : ℝ) :
    |AdmWindow.VPhiR (P.phiV vTheta T) (2 * Real.pi * x / P.L T) / ((P.atV vTheta T).a T * P.L T)
        - kfun x| ≤ 12 * P.w / P.L T := by
  have hW := admWindow_theta hP h8
  have hL := hW.L_pos
  have hw : 0 < P.w := hW.w_pos
  have ha : 1 / 2 ≤ (P.atV vTheta T).a T := (aV_theta_range hP h8).1
  have h1 := abs_VPhiR_sub_L_mul_Kfun_le hP h8 x
  have h2 := abs_aL_sub_L_mul_Kfun_zero_le hP h8
  have hK0 : 0 < Kfun 0 := Kfun_zero_pos
  have hK : |Kfun x| ≤ Kfun 0 := abs_Kfun_le x
  set V := AdmWindow.VPhiR (P.phiV vTheta T) (2 * Real.pi * x / P.L T) with hV
  set A := (P.atV vTheta T).a T * P.L T with hA
  set K := Kfun x with hK'
  set K0 := Kfun 0 with hK0'
  have hA2 : P.L T / 2 ≤ A := by rw [hA]; nlinarith
  have hApos : 0 < A := by linarith
  have e : V / A - K / K0 = (V - P.L T * K) / A + K * (P.L T * K0 - A) / (A * K0) := by
    field_simp
    ring
  unfold kfun
  rw [e]
  have h2' : |P.L T * K0 - A| ≤ 2 * P.w := by rw [abs_sub_comm]; exact h2
  calc |(V - P.L T * K) / A + K * (P.L T * K0 - A) / (A * K0)|
      ≤ |(V - P.L T * K) / A| + |K * (P.L T * K0 - A) / (A * K0)| := abs_add_le _ _
    _ = |V - P.L T * K| / A + |K| * |P.L T * K0 - A| / (A * K0) := by
        rw [abs_div, abs_of_pos hApos, abs_div, abs_mul, abs_of_pos (mul_pos hApos hK0)]
    _ ≤ 2 * P.w / A + K0 * (2 * P.w) / (A * K0) := by gcongr
    _ = 4 * P.w / A := by field_simp; ring
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
    PrimeSide.Kfun (P.toSetting T) (WinTheta.FT P T) γ γ'
      = ∑ k : Fin ((P.atV vTheta T).d T), (P.atV vTheta T).phiHatR T (γ - (P.atV vTheta T).tau T k)
          * (P.atV vTheta T).phiHatR T (γ' - (P.atV vTheta T).tau T k) := by
  rw [atV_phiHatR_eq hP T]; rfl

lemma Kinf_eq {P : Params} (T γ γ' : ℝ) :
    PrimeSide.Kinf (P.toSetting T) (WinTheta.FT P T) γ γ'
      = P.L T * AdmWindow.VPhiR (P.phiV vTheta T) (γ - γ') := rfl

theorem gram_close_of {P : Params} (hP : P.Valid) {T : ℝ} (hT : 0 < T)
    (h8 : 8 * P.w ≤ P.L T)
    (hF : PrimeSide.LocalHypsCoreW (cTh P.ϱ) (P.toSetting T) (WinTheta.FT P T))
    (Z : ZeroConfig) (z z' : retained Z (P.atV vTheta T) T) :
    ‖gram Z (P.atV vTheta T) T z z'
        - (kfun (xret Z (P.atV vTheta T) T z - xret Z (P.atV vTheta T) T z') : ℂ)‖
      ≤ 10 * (cTh P.ϱ / P.w) ^ 2 / P.L T ^ 4 + 12 * P.w / P.L T := by
  have hW := admWindow_theta hP h8
  have hL := hW.L_pos
  have ha : 1 / 2 ≤ (P.atV vTheta T).a T := (aV_theta_range hP h8).1
  have hc : 0 < aL2 (P.atV vTheta T) T := by
    unfold aL2; rw [Params.atV_L]; positivity
  set K : ℝ := (cTh P.ϱ / P.w) ^ 2 with hK
  have hK0 : 0 ≤ K := sq_nonneg _
  rw [gram_apply Z (P.atV vTheta T) T (phiHatReal_atV hP T) hc.le z z', ← Complex.ofReal_sub,
    Complex.norm_real, Real.norm_eq_abs, ← Kfun_eq_sum hP T (z.1 : ℂ).im (z'.1 : ℂ).im]
  set γ : ℝ := (z.1 : ℂ).im with hγ
  set γ' : ℝ := (z'.1 : ℂ).im with hγ'

  obtain ⟨g1, g2, g3⟩ := retained_far (Z := Z) (P := P.atV vTheta T) hL hT.le z.2
  obtain ⟨g1', g2', g3'⟩ := retained_far (Z := Z) (P := P.atV vTheta T) hL hT.le z'.2
  have htail : |PrimeSide.Kinf (P.toSetting T) (WinTheta.FT P T) γ γ'
      - PrimeSide.Kfun (P.toSetting T) (WinTheta.FT P T) γ γ'| ≤ 5 * K / P.L T ^ 2 :=
    abs_Kinf_sub_Kfun_le_of_far hF hT g1 g2 g3 g1' g2' g3'

  have hx : 2 * Real.pi * (xret Z (P.atV vTheta T) T z - xret Z (P.atV vTheta T) T z') / P.L T
      = γ - γ' := by
    unfold xret xnorm
    rw [Params.atV_L]
    field_simp
    ring
  have hlim := abs_VPhiR_div_sub_kfun_le hP h8
    (xret Z (P.atV vTheta T) T z - xret Z (P.atV vTheta T) T z')
  rw [hx] at hlim

  set A : ℝ := (P.atV vTheta T).a T with hA
  set V : ℝ := AdmWindow.VPhiR (P.phiV vTheta T) (γ - γ') with hV
  set Kf : ℝ := PrimeSide.Kfun (P.toSetting T) (WinTheta.FT P T) γ γ' with hKf
  have hKinf : PrimeSide.Kinf (P.toSetting T) (WinTheta.FT P T) γ γ' = P.L T * V := Kinf_eq T γ γ'
  rw [hKinf] at htail
  have haL2 : aL2 (P.atV vTheta T) T = A * P.L T ^ 2 := by unfold aL2; rw [Params.atV_L]
  rw [haL2]
  have hApos : 0 < A := by linarith
  have hsplit : (A * P.L T ^ 2)⁻¹ * Kf
        - kfun (xret Z (P.atV vTheta T) T z - xret Z (P.atV vTheta T) T z')
      = (A * P.L T ^ 2)⁻¹ * (Kf - P.L T * V)
        + (V / (A * P.L T) - kfun (xret Z (P.atV vTheta T) T z - xret Z (P.atV vTheta T) T z')) := by
    field_simp
    ring
  rw [hsplit]
  have hinv : (A * P.L T ^ 2)⁻¹ ≤ 2 / P.L T ^ 2 := by
    rw [inv_eq_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [pow_pos hL 2]
  calc |(A * P.L T ^ 2)⁻¹ * (Kf - P.L T * V)
        + (V / (A * P.L T) - kfun (xret Z (P.atV vTheta T) T z - xret Z (P.atV vTheta T) T z'))|
      ≤ |(A * P.L T ^ 2)⁻¹ * (Kf - P.L T * V)|
        + |V / (A * P.L T) - kfun (xret Z (P.atV vTheta T) T z - xret Z (P.atV vTheta T) T z')| :=
        abs_add_le _ _
    _ = (A * P.L T ^ 2)⁻¹ * |P.L T * V - Kf|
        + |V / (A * P.L T) - kfun (xret Z (P.atV vTheta T) T z - xret Z (P.atV vTheta T) T z')| := by
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
      (Htheta - ε) * (Z.N T (2 * T) : ℝ) + Dcirc Z (mtParams T) T ≤ (Z.N0s T (2 * T) : ℝ) := by

  set P : Params := paramsOf stdProfile 1 with hPdef
  have hP : P.Valid := paramsOf_valid taperProfile_stdProfile one_pos le_rfl

  have hTr := WinTheta.tracesBoundsD_theta (Z := Z) hP H
  have hc := WinTheta.tendsto_cRatio_theta hP Z
  have hc0 : 0 < XiPrime.cWin id P.lam vTheta := cWin_vTheta_pos hP.lam_pos hP.lam_le_one
  have ha : ∀ᶠ T in atTop, 1 / 2 ≤ (WinTheta.dataT P Z).aT T ∧ (WinTheta.dataT P Z).aT T ≤ 1 :=
    (WinTheta.concreteFactsT hP H (WinTheta.localHypsCoreTEventually_of hP)).ab_range.mono
      fun T h => ⟨h.1.trans h.2.1, h.2.2.1⟩
  obtain ⟨θ₀, hTail, hθ₀⟩ := eventually_tailPackageT Z H hP
  obtain ⟨A₀, hA₀, hloc⟩ := H.RvM.local_count
  have hNII := Tail.eventually_NII_le Z hA₀ hloc
  have hGzGp := eventually_GzGpT Z H hP
  have hId : ∀ᶠ T in atTop,
      (P.atV vTheta T).trGtilde T = (WinTheta.dataT P Z).trG T ∧
      (P.atV vTheta T).trGtildeSq T = (WinTheta.dataT P Z).trG2 T ∧
      (P.atV vTheta T).a T = (WinTheta.dataT P Z).aT T :=
    Eventually.of_forall fun T =>
      ⟨Params.atV_trGtilde T hP vTheta_even, Params.atV_trGtildeSq T hP vTheta_even,
        Params.atV_a T hP vTheta_even⟩
  have hcalE := Assembly.calE_tendsto_zero P hP.lam_pos hP.lam_le_one
    (zero_le_one.trans hP.one_le_w)

  have h := endgame_defect Z H P hP vTheta _ _ _ _ _ hTr hc0 hc ha θ₀ hTail hθ₀ hNII hGzGp hId
    hcalE (fun T => Dcirc Z (mtParams T) T) h7
  intro ε hε
  have h' := h ε hε
  rw [Htheta_eq]
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
  obtain ⟨T₀, hT₀⟩ := localHypsCoreT_eventually hP
  set K : ℝ := (cTh (paramsOf stdProfile 1).ϱ / (paramsOf stdProfile 1).w) ^ 2 with hK
  have hK0 : 0 ≤ K := sq_nonneg _
  have hw : 0 < (paramsOf stdProfile 1).w := by linarith [hP.one_le_w]
  filter_upwards [eventually_gt_atTop 0, eventually_w8 hP,
    eventually_ge_atTop T₀, (tendsto_L hP).eventually_ge_atTop 1,
    (tendsto_L hP).eventually_ge_atTop ((10 * K + 12 * (paramsOf stdProfile 1).w) / δ)]
    with T hT h8 hTT₀ hL1 hLδ
  intro z z' _
  have hF := (hT₀ T hTT₀).toCoreW
  have h := gram_close_of hP hT h8 hF Z z z'
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
      (Htheta - ((n : ℝ) - 1) * ((m : ℝ) - 1) / ((p : ℝ) * m) - ε) * N T
        ≤ (1 - c * ((m : ℝ) - ((n : ℝ) - 1)) / m) * N0 T) :
    ∀ ε > 0, ∀ᶠ T in atTop, (Phi_n n c m p - ε) * N T ≤ N0 T := by
  intro ε hε
  have hD := one_sub_div_pos hn hm hA0
  set Dn : ℝ := 1 - c * ((m : ℝ) - ((n : ℝ) - 1)) / m with hDn
  filter_upwards [h (ε * Dn) (mul_pos hε hD)] with T hT
  have hPhi : Phi_n n c m p
      = (Htheta - ((n : ℝ) - 1) * ((m : ℝ) - 1) / ((p : ℝ) * m)) / Dn := rfl
  rw [hPhi]
  have : (Htheta - ((n : ℝ) - 1) * ((m : ℝ) - 1) / ((p : ℝ) * m)) / Dn - ε
      = (Htheta - ((n : ℝ) - 1) * ((m : ℝ) - 1) / ((p : ℝ) * m) - ε * Dn) / Dn := by
    field_simp
  rw [this, div_mul_eq_mul_div, div_le_iff₀ hD]
  linarith

theorem Phi_paper : Phi (19 / 5000) 269 3000 = (1345000 * Htheta - 2680) / 1340003 := by
  unfold Phi
  norm_num
  field_simp
  ring

theorem Phi_lab : Phi (34697 / 10000000) 294 3400
    = (520625000 * Htheta - 915625) / 518855453 := by
  unfold Phi
  norm_num
  field_simp
  ring

theorem Phi_lab8 : Phi_n 8 (41763 / 10000000) 246 3200
    = (2460000000 * Htheta - 5359375) / 2450018643 := by
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
  filter_upwards [eventually_w8 P₀_valid] with T h8
  set P := mtParams T with hP
  have hconj : PhiHatConj T P := phiHatConj
  have hL : 0 < P.L T := by
    change 0 < P₀.L T; linarith [P₀_valid.one_le_w]
  have ha : 1 / 2 ≤ P.a T := (aV_theta_range P₀_valid h8).1
  have hc : 0 < aL2 P T := mul_pos (by linarith) (pow_pos hL 2)
  have hPois : PoissonSq T P := poissonSqT P₀_valid h8
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
      (Htheta - ((n : ℝ) - 1) * ((m : ℝ) - 1) / ((p : ℝ) * m) - ε) * (Z.N T (2 * T) : ℝ)
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
  have hmD : (m : ℝ) * D ≤ m * (n0 - (Htheta - η) * N) :=
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
  have key : ((m : ℝ) * Htheta - q * ((m : ℝ) - 1) - m * ε) * N ≤ ((m : ℝ) - A₀) * n0 := by
    linarith [h15, step1, step2, step3, hmD, hηN']
  have hL1 : (Htheta - ((n : ℝ) - 1) * ((m : ℝ) - 1) / ((p : ℝ) * m) - ε) * N
      = ((m : ℝ) * Htheta - q * ((m : ℝ) - 1) - m * ε) * N / m := by
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
      ((1345000 * Htheta - 2680) / 1340003 - ε) * (Zeta23.Ncount T (2 * T) : ℝ) ≤ Zeta23.N0simple T (2 * T) := by
  rw [← Phi_paper]
  exact seven_point_bound (19 / 5000) 269 3000 (by norm_num) (by norm_num) (by norm_num) hCert
    (by norm_num)

lemma eventually_Ncount_pos : ∀ᶠ T in atTop, 0 < (Zeta23.Ncount T (2 * T) : ℝ) := by
  have h := Zeta23.Assembly.tendsto_N_atTop zetaZeroConfig paperInputs_zeta.RvM
  simpa only [zetaZeroConfig_N] using h.eventually_gt_atTop 0

theorem seven_point_bound_lab
    (hCert : ∀ g : Fin 6 → ℝ, (∀ i, 0 ≤ g i) → 34697 / 10000000 ≤ F6 3400 g) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      ((520625000 * Htheta - 915625) / 518855453 - ε) * (Zeta23.Ncount T (2 * T) : ℝ)
        ≤ Zeta23.N0simple T (2 * T) := by
  rw [← Phi_lab]
  exact seven_point_bound (34697 / 10000000) 294 3400 (by norm_num) (by norm_num) (by norm_num)
    hCert (by norm_num)

theorem seven_point_bound_lab_ratio
    (hCert : ∀ g : Fin 6 → ℝ, (∀ i, 0 ≤ g i) → 34697 / 10000000 ≤ F6 3400 g) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (520625000 * Htheta - 915625) / 518855453 - ε
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
      ((2460000000 * Htheta - 5359375) / 2450018643 - ε) * (Zeta23.Ncount T (2 * T) : ℝ)
        ≤ Zeta23.N0simple T (2 * T) := by
  rw [← Phi_lab8]
  exact n_point_bound 8 (41763 / 10000000) 246 3200 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) hCert (by norm_num)

theorem eight_point_bound_ratio
    (hCert : ∀ g : Fin 7 → ℝ, (∀ i, 0 ≤ g i) → 41763 / 10000000 ≤ F 8 3200 g) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (2460000000 * Htheta - 5359375) / 2450018643 - ε
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
  (Htheta - B * ((m : ℝ) - 1) / m) / (1 - c * ((m : ℝ) - ((n : ℝ) - 1)) / m)

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
      (Htheta - W.B * ((m : ℝ) - 1) / m - ε) * (Z.N T (2 * T) : ℝ)
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
  have hmD : (m : ℝ) * D ≤ m * (n0 - (Htheta - η) * N) :=
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
  have key : ((m : ℝ) * Htheta - q * ((m : ℝ) - 1) - m * ε) * N ≤ ((m : ℝ) - A₀) * n0 := by
    linarith [h15, step1, step2, step3, hmD, hηN']
  have hL1 : (Htheta - q * ((m : ℝ) - 1) / m - ε) * N
      = ((m : ℝ) * Htheta - q * ((m : ℝ) - 1) - m * ε) * N / m := by
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
    (N0 := fun T => (Zeta23.N0simple T (2 * T) : ℝ)) (Htheta - W.B * ((m : ℝ) - 1) / m) hn hm hA0 (by
      have := pre_solve_w zetaZeroConfig paperInputs_zeta hn hm W hW hBpos hc hCert hA0
      simpa only [zetaZeroConfig_N, zetaZeroConfig_N0s] using this)
  intro ε hε
  exact eventually_atTop.mp (h ε hε)

def Phi_w' (n : ℕ) (c : ℝ) (m : ℕ) (B : ℝ) : ℝ :=
  (Htheta - B * ((m : ℝ) - ((n : ℝ) - 1)) / m) / (1 - c * ((m : ℝ) - ((n : ℝ) - 1)) / m)

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
      (Htheta - W.B * ((m : ℝ) - ((n : ℝ) - 1)) / m - ε) * (Z.N T (2 * T) : ℝ)
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
  have hmD : (m : ℝ) * D ≤ m * (n0 - (Htheta - η) * N) :=
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
  have key : ((m : ℝ) * Htheta - q * mq - m * ε) * N ≤ ((m : ℝ) - A₀) * n0 := by
    linarith [h15, step1, step2, step3, hmD, hηN']
  have hL1 : (Htheta - q * mq / m - ε) * N
      = ((m : ℝ) * Htheta - q * mq - m * ε) * N / m := by
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
    (N0 := fun T => (Zeta23.N0simple T (2 * T) : ℝ)) (Htheta - W.B * ((m : ℝ) - ((n : ℝ) - 1)) / m) hn hm hA0
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
      ((2460000000 * Htheta - 5228125) / 2450018643 - ε) * (Zeta23.Ncount T (2 * T) : ℝ)
        ≤ Zeta23.N0simple T (2 * T) := by
  have h := n_point_bound_fixed' 8 (41763 / 10000000) 246 3200 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hCert (by norm_num)
  have hPhi : Phi_w' 8 (41763 / 10000000) 246 (((8 : ℕ) - 1 : ℝ) / ((3200 : ℕ) : ℝ))
      = (2460000000 * Htheta - 5228125) / 2450018643 := by
    unfold Phi_w'
    norm_num
    field_simp
    ring
  rw [hPhi] at h
  exact h

theorem eight_point_bound_w'_ratio
    (hCert : ∀ g : Fin 7 → ℝ, (∀ i, 0 ≤ g i) → 41763 / 10000000 ≤ F 8 3200 g) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (2460000000 * Htheta - 5228125) / 2450018643 - ε
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
      (Real.sinc (((3 / 2 : ℝ) - 2 * Real.pi * x) / 2)
        + Real.sinc (((3 / 2 : ℝ) + 2 * Real.pi * x) / 2)) / 2 := by
  have key : ∀ t : ℝ, Real.cos ((3 / 2 : ℝ) * t) * Real.cos (2 * Real.pi * x * t)
      = (Real.cos (((3 / 2 : ℝ) - 2 * Real.pi * x) * t)
          + Real.cos (((3 / 2 : ℝ) + 2 * Real.pi * x) * t)) / 2 := by
    intro t
    rw [sub_mul, add_mul, Real.cos_sub, Real.cos_add]; ring
  unfold Kfun
  simp_rw [key]
  rw [intervalIntegral.integral_div,
    intervalIntegral.integral_add (cos_mul_intervalIntegrable _ _ _)
      (cos_mul_intervalIntegrable _ _ _),
    integral_cos_mul_eq_sinc, integral_cos_mul_eq_sinc]

def gam : ℝ := (3 / 4 : ℝ) * Real.cos (3 / 4) / Real.sin (3 / 4)

private lemma sin_three_quarters_pos : 0 < Real.sin (3 / 4 : ℝ) :=
  Real.sin_pos_of_pos_of_lt_pi (by norm_num) (by linarith [Real.pi_gt_three])

theorem cos_three_quarters_bounds :
    (7316888665/10^10 : ℝ) ≤ Real.cos (3 / 4) ∧ Real.cos (3 / 4) ≤ 7316888712/10^10 := by
  constructor
  · have := cos_lower (by norm_num : (0:ℝ) ≤ 3 / 4) le_rfl (by norm_num)
    have h : (7316888665/10^10 : ℝ) ≤ taylorCos (3 / 4) - taylorErr := by
      unfold taylorCos taylorErr; norm_num
    linarith
  · have := cos_upper (by norm_num : (0:ℝ) ≤ 3 / 4) le_rfl (by norm_num)
    have h : taylorCos (3 / 4 : ℝ) + taylorErr ≤ 7316888712/10^10 := by
      unfold taylorCos taylorErr; norm_num
    linarith

theorem sin_three_quarters_bounds :
    (6816387577/10^10 : ℝ) ≤ Real.sin (3 / 4) ∧ Real.sin (3 / 4) ≤ 6816387624/10^10 := by
  constructor
  · have := sin_lower (by norm_num : (0:ℝ) ≤ 3 / 4) le_rfl (by norm_num)
    have h : (6816387577/10^10 : ℝ) ≤ taylorSin (3 / 4) - taylorErr := by
      unfold taylorSin taylorErr; norm_num
    linarith
  · have := sin_upper (by norm_num : (0:ℝ) ≤ 3 / 4) le_rfl (by norm_num)
    have h : taylorSin (3 / 4 : ℝ) + taylorErr ≤ 6816387624/10^10 := by
      unfold taylorSin taylorErr; norm_num
    linarith

theorem gam_bounds : (8050696059/10^10 : ℝ) ≤ gam ∧ gam ≤ 8050696168/10^10 := by
  have hc := cos_three_quarters_bounds
  have hs := sin_three_quarters_bounds
  have hspos : (0:ℝ) < Real.sin (3 / 4) := by linarith [hs.1]
  constructor
  · rw [gam, le_div_iff₀ hspos]; nlinarith [hc.1, hs.2]
  · rw [gam, div_le_iff₀ hspos]; nlinarith [hc.2, hs.1]

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

theorem kfun_closed (x : ℝ) (h : 1 - 16/9*(Real.pi*x)^2 ≠ 0) :
    kfun x = (Real.cos (Real.pi*x) - 16/9*gam*(Real.pi*x)*Real.sin (Real.pi*x))
      / (1 - 16/9*(Real.pi*x)^2) := by
  set a : ℝ := 3 / 4 with ha_def
  set b : ℝ := Real.pi * x with hb_def
  have ha2 : a^2 = 9/16 := by rw [ha_def]; norm_num
  have ha : a ≠ 0 := by rw [ha_def]; norm_num
  have hsa : Real.sin a ≠ 0 := ne_of_gt sin_three_quarters_pos
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
    rw [Kfun_eq_sinc, show ((3 / 2 : ℝ) - 2*Real.pi*x)/2 = a - b by rw [ha_def, hb_def]; ring,
      show ((3 / 2 : ℝ) + 2*Real.pi*x)/2 = a + b by rw [ha_def, hb_def]; ring,
      Real.sinc_of_ne_zero h1, Real.sinc_of_ne_zero h2]
  have hK0 : Kfun 0 = Real.sin a / a := by
    rw [Kfun_eq_sinc, show ((3 / 2 : ℝ) - 2*Real.pi*0)/2 = a by rw [ha_def]; ring,
      show ((3 / 2 : ℝ) + 2*Real.pi*0)/2 = a by rw [ha_def]; ring,
      Real.sinc_of_ne_zero ha]
    ring
  have hgam : gam = a * (Real.cos a / Real.sin a) := by
    rw [gam, ← ha_def]; field_simp
  have hne1 : (9/16 : ℝ) - b^2 ≠ 0 := by
    intro hz; apply h; linarith
  rw [kfun, hK, hK0, kfun_aux a b ha hsa h1 h2, hgam, ha2,
    div_eq_div_iff hne1 h, ha_def]
  ring

theorem pi_lo : (3.14159265358979323846 : ℝ) ≤ Real.pi := le_of_lt Real.pi_gt_d20

theorem pi_hi : Real.pi ≤ 3.14159265358979323847 := le_of_lt Real.pi_lt_d20

lemma wfun_nonneg (x : ℝ) : 0 ≤ wfun x := sq_nonneg _

theorem wfun_ge (x nlo dhi : ℝ) (hnlo : 0 ≤ nlo) (hdhi : 0 < dhi)
    (hD0 : 1 < 16/9*(Real.pi*x)^2) (hD : 16/9*(Real.pi*x)^2 - 1 ≤ dhi)
    (hN : nlo ≤ |Real.cos (Real.pi*x) - 16/9*gam*(Real.pi*x)*Real.sin (Real.pi*x)|) :
    (nlo/dhi)^2 ≤ wfun x := by
  have hne : 1 - 16/9*(Real.pi*x)^2 ≠ 0 := by intro hz; nlinarith
  have hk : kfun x = (Real.cos (Real.pi*x) - 16/9*gam*(Real.pi*x)*Real.sin (Real.pi*x))
      / (1 - 16/9*(Real.pi*x)^2) := kfun_closed x hne
  have hw : wfun x = kfun x ^ 2 := rfl
  set N : ℝ := Real.cos (Real.pi*x) - 16/9*gam*(Real.pi*x)*Real.sin (Real.pi*x) with hN_def
  set Dd : ℝ := 1 - 16/9*(Real.pi*x)^2 with hD_def
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

theorem wfun_window (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1/2) : (19/100 : ℝ) ≤ wfun x := by
  have hpl := pi_lo
  have hph := pi_hi
  set A : ℝ := ((3 / 2 : ℝ) - 2*Real.pi*x)/2 with hA
  set B : ℝ := ((3 / 2 : ℝ) + 2*Real.pi*x)/2 with hB
  have hAlo : (-8209/10000 : ℝ) ≤ A := by rw [hA]; nlinarith
  have hAhi : A ≤ 7500/10000 := by rw [hA]; nlinarith
  have hAabs : |A| ≤ 1 := by rw [abs_le]; constructor <;> linarith
  have hA2 : A^2 ≤ 6739/10000 := by nlinarith
  have hsincA : (89000/100000 : ℝ) ≤ Real.sinc A := by
    have h := sinc_taylor A hAabs
    have hq : (89000/100000 : ℝ) ≤ taylorSinc A - taylorErr := by
      unfold taylorSinc taylorErr
      nlinarith [sq_nonneg A, sq_nonneg (A^2), sq_nonneg (A^3), sq_nonneg (A^4),
        sq_nonneg (A^5), hA2, sq_nonneg (A^2 - 6739/10000)]
    linarith
  have hBlo : (7500/10000 : ℝ) ≤ B := by rw [hB]; nlinarith
  have hBhi : B ≤ 23208/10000 := by rw [hB]; nlinarith
  have hsincB : (0:ℝ) ≤ Real.sinc B := by
    rw [Real.sinc_of_ne_zero (by positivity)]
    exact div_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith))
      (by linarith)
  have hK : (44500/100000 : ℝ) ≤ Kfun x := by
    rw [Kfun_eq_sinc, ← hA, ← hB]; linarith
  have hK0 : Kfun 0 = Real.sinc (3 / 4) := by
    rw [Kfun_eq_sinc, show ((3 / 2 : ℝ) - 2*Real.pi*0)/2 = 3 / 4 by ring,
      show ((3 / 2 : ℝ) + 2*Real.pi*0)/2 = 3 / 4 by ring]
    ring
  have hK0le : Kfun 0 ≤ 1 := by rw [hK0]; exact Real.sinc_le_one _
  have hK0pos : 0 < Kfun 0 := by
    rw [hK0, Real.sinc_of_ne_zero (by norm_num)]
    exact div_pos sin_three_quarters_pos (by norm_num)
  have hk : (44500/100000 : ℝ) ≤ kfun x := by
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
def gamLoQ : ℚ := 8050696059 / 10^10
def gamHiQ : ℚ := 8050696168 / 10^10

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
def P2L (c : Cell) : ℚ := floorD (16/9 * gamLoQ * c.BL)
def P2U (c : Cell) : ℚ := ceilD (16/9 * gamHiQ * c.BU)
def TLO (c : Cell) : ℚ := floorD (min (c.P2L * c.SX.1) (c.P2U * c.SX.1))
def THI (c : Cell) : ℚ := ceilD (max (c.P2L * c.SX.2) (c.P2U * c.SX.2))
def NLO (c : Cell) : ℚ := max 0 (max (c.CX.1 - c.THI) (c.TLO - c.CX.2))
def DHI (c : Cell) : ℚ := ceilD (16/9 * c.BU * c.BU - 1)
def Wc (c : Cell) : ℚ := (c.NLO / c.DHI)^2
def ok (c : Cell) : Bool :=
  decide (0 ≤ c.L) && decide (c.L ≤ c.U) && decide (0 ≤ c.rlo) && decide (c.TU ≤ 1)
    && decide (0 ≤ c.TL) && decide (0 ≤ c.BL) && decide (0 ≤ c.P2L)
    && decide (1 < 16/9 * c.BL * c.BL) && decide (0 < c.DHI) && decide (c.W ≤ c.Wc)
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
  have hB' : (1:ℝ) < 16/9 * c.BL * c.BL := by
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
  have hp1 : (c.P2L : ℝ) ≤ 16/9 * gam * (Real.pi * x) := by
    have h1 : (c.P2L : ℝ) ≤ ((16/9 * gamLoQ * c.BL : ℚ) : ℝ) := floorD_le' _
    push_cast at h1
    have := mul_le_mul gamLoQ_le hb1 hBL0 hgam0
    linarith
  have hp2 : 16/9 * gam * (Real.pi * x) ≤ c.P2U := by
    have h1 : ((16/9 * gamHiQ * c.BU : ℚ) : ℝ) ≤ (c.P2U : ℝ) := le_ceilD' _
    push_cast at h1
    have := mul_le_mul gamHiQ_ge hb2 hπx0 (gamLoQ_nonneg.trans (gamLoQ_le.trans gamHiQ_ge))
    linarith
  -- the product 2 γ π x · sin (π x)
  have hT1 : (c.TLO : ℝ) ≤ 16/9 * gam * (Real.pi * x) * Real.sin (Real.pi * x) := by
    have h1 : (c.TLO : ℝ) ≤ ((min (c.P2L * c.SX.1) (c.P2U * c.SX.1) : ℚ) : ℝ) := floorD_le' _
    rw [Rat.cast_min, Rat.cast_mul, Rat.cast_mul] at h1
    exact h1.trans (prod_lo hP2L0 hp1 hp2 hSX.1 (min_le_left _ _) (min_le_right _ _))
  have hT2 : 16/9 * gam * (Real.pi * x) * Real.sin (Real.pi * x) ≤ c.THI := by
    have h1 : ((max (c.P2L * c.SX.2) (c.P2U * c.SX.2) : ℚ) : ℝ) ≤ (c.THI : ℝ) := le_ceilD' _
    rw [Rat.cast_max, Rat.cast_mul, Rat.cast_mul] at h1
    exact (prod_hi hP2L0 hp1 hp2 hSX.2 (le_max_left _ _) (le_max_right _ _)).trans h1
  -- the numerator
  have eNLO : (c.NLO : ℝ) = max 0 (max (((c.CX).1 : ℝ) - c.THI) ((c.TLO : ℝ) - (c.CX).2)) := by
    rw [Cell.NLO, Rat.cast_max, Rat.cast_max]; push_cast; rfl
  have hN : (c.NLO : ℝ) ≤ |Real.cos (Real.pi * x) - 16/9 * gam * (Real.pi * x) * Real.sin (Real.pi * x)| := by
    rw [eNLO]
    refine max_le (abs_nonneg _) (max_le ?_ ?_)
    · exact le_trans (by linarith [hCX.1, hT2]) (le_abs_self _)
    · exact le_trans (by linarith [hCX.2, hT1]) (neg_le_abs _)
  have hNLO0 : (0:ℝ) ≤ c.NLO := by rw [eNLO]; exact le_max_left _ _
  -- the denominator
  have hD0 : (1:ℝ) < 16/9 * (Real.pi * x)^2 := by
    have := mul_le_mul hb1 hb1 hBL0 hπx0
    rw [pow_two]; nlinarith [this, hB']
  have hDD : 16/9 * (Real.pi * x)^2 - 1 ≤ c.DHI := by
    have h1 : ((16/9 * c.BU * c.BU - 1 : ℚ) : ℝ) ≤ (c.DHI : ℝ) := le_ceilD' _
    push_cast at h1
    have := mul_le_mul hb2 hb2 hπx0 (hπx0.trans hb2)
    rw [pow_two]; nlinarith [this, h1]
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
def GLN : ℕ := 14312348549
def GUN : ℕ := 14312348744
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
def P2LZ (c : CellN) : ℕ := ndiv (GLN * c.BLZ) 10000000000
def P2UZ (c : CellN) : ℕ := ndivc (GUN * c.BUZ) 10000000000
def TLOZ (c : CellN) : ℤ := zfdiv (min ((c.P2LZ : ℤ) * c.SXZ.1) ((c.P2UZ : ℤ) * c.SXZ.1))
def THIZ (c : CellN) : ℤ := zcdiv (max ((c.P2LZ : ℤ) * c.SXZ.2) ((c.P2UZ : ℤ) * c.SXZ.2))
def NLOZ (c : CellN) : ℤ := max 0 (max (c.CXZ.1 - c.THIZ) (c.TLOZ - c.CXZ.2))
def DHIZ (c : CellN) : ℤ := ((ndivc (16 * c.BUZ * c.BUZ) (9 * DZ) : ℕ) : ℤ) - DZ
/-- the conditions of the integer check that do not involve the claimed bound -/
def okC (c : CellN) : Bool :=
  decide (c.LN ≤ c.UN) && decide (c.TUZ ≤ DZ)
    && (if c.side then decide (c.k * SC ≤ 2 * c.LN) else decide (2 * c.UN ≤ c.k * SC))
    && decide (cosN c.TUZ ≤ cosP c.TUZ) && decide (cosN c.TLZ ≤ cosP c.TLZ)
    && decide (sinN c.TLZ ≤ sinP c.TLZ) && decide (sinN c.TUZ ≤ sinP c.TUZ)
    && decide (9 * (DZ * DZ) < 16 * (c.BLZ * c.BLZ)) && decide (0 < c.DHIZ)
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
theorem GLN_le : ((GLN : ℕ) : ℝ) / 10000000000 ≤ 16/9 * gam := by
  have h := gam_bounds.1; norm_num [GLN] at h ⊢; linarith
theorem GUN_ge : 16/9 * gam ≤ ((GUN : ℕ) : ℝ) / 10000000000 := by
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
  have hgam0 : (0:ℝ) ≤ 16/9 * gam := (nG0 GLN).trans GLN_le
  have hp1 : ((c.P2LZ : ℕ) : ℝ) / DZ ≤ 16/9 * gam * (Real.pi * x) := by
    unfold CellN.P2LZ
    exact ndiv_prod_le GLN c.BLZ 10000000000 (by norm_num) (A := 16/9 * gam) (B := Real.pi * x)
      (by push_cast; have := GLN_le; linarith) hb1 (nG0 _) hBL0
  have hp2 : 16/9 * gam * (Real.pi * x) ≤ ((c.P2UZ : ℕ) : ℝ) / DZ := by
    unfold CellN.P2UZ
    exact le_ndivc_prod GUN c.BUZ 10000000000 (by norm_num) (A := 16/9 * gam) (B := Real.pi * x)
      (by push_cast; have := GUN_ge; linarith) hb2 (by linarith) hπx0
  have hP2L0 : (0:ℝ) ≤ ((c.P2LZ : ℕ) : ℝ) / DZ := nd0 _
  -- the product 2 γ π x · sin (π x)
  have hT1 : ((c.TLOZ : ℤ) : ℝ) / DZ ≤ 16/9 * gam * (Real.pi * x) * Real.sin (Real.pi * x) := by
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
  have hT2 : 16/9 * gam * (Real.pi * x) * Real.sin (Real.pi * x) ≤ ((c.THIZ : ℤ) : ℝ) / DZ := by
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
  set N : ℝ := Real.cos (Real.pi * x) - 16/9 * gam * (Real.pi * x) * Real.sin (Real.pi * x) with hNdef
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
  have hD0' : (1:ℝ) < 16/9 * (Real.pi * x)^2 := by
    have h1 : ((9 * (DZ * DZ) : ℕ) : ℝ) < ((16 * (c.BLZ * c.BLZ) : ℕ) : ℝ) := by exact_mod_cast hB
    push_cast at h1
    have h2 : ((c.BLZ : ℕ) : ℝ) / DZ * (((c.BLZ : ℕ) : ℝ) / DZ) ≤ (Real.pi * x) * (Real.pi * x) :=
      mul_le_mul hb1 hb1 hBL0 hπx0
    have h3 : (1:ℝ) < 16/9 * (((c.BLZ : ℕ) : ℝ) / DZ * (((c.BLZ : ℕ) : ℝ) / DZ)) := by
      rw [div_mul_div_comm, ← mul_div_assoc, lt_div_iff₀ (mul_pos hD0 hD0)]
      linarith
    rw [pow_two]; linarith
  have hDD : 16/9 * (Real.pi * x)^2 - 1 ≤ ((c.DHIZ : ℤ) : ℝ) / DZ := by
    have h1 := le_ndivc (16 * c.BUZ * c.BUZ) (9 * DZ) (by norm_num [DZ])
    push_cast at h1
    have h2 : (Real.pi * x) * (Real.pi * x) ≤ ((c.BUZ : ℕ) : ℝ) / DZ * (((c.BUZ : ℕ) : ℝ) / DZ) :=
      mul_le_mul hb2 hb2 hπx0 (hπx0.trans hb2)
    have h3 : 16/9 * (((c.BUZ : ℕ) : ℝ) / DZ * (((c.BUZ : ℕ) : ℝ) / DZ))
        = 16 * (c.BUZ : ℝ) * (c.BUZ : ℝ) / (9 * DZ) / DZ := by ring
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

def Nf (θ : ℝ) : ℝ := Real.cos θ - 16/9 * gam * θ * Real.sin θ
def N1f (θ : ℝ) : ℝ := -(1 + 16/9 * gam) * Real.sin θ - 16/9 * gam * θ * Real.cos θ
def N2f (θ : ℝ) : ℝ := -(1 + 32/9 * gam) * Real.cos θ + 16/9 * gam * θ * Real.sin θ
def Df (θ : ℝ) : ℝ := 1 - 16/9 * θ ^ 2

/-- `d/dθ (N/D)` and `d²/dθ² (N/D)`. -/
def K1f (θ : ℝ) : ℝ := N1f θ / Df θ + 32/9 * θ * Nf θ / Df θ ^ 2
def K2f (θ : ℝ) : ℝ :=
  N2f θ / Df θ + 64/9 * θ * N1f θ / Df θ ^ 2 + 32/9 * Nf θ / Df θ ^ 2
    + 2048/81 * θ ^ 2 * Nf θ / Df θ ^ 3

lemma hasDerivAt_Nf (θ : ℝ) : HasDerivAt Nf (N1f θ) θ := by
  unfold Nf
  refine ((Real.hasDerivAt_cos θ).sub
    (((hasDerivAt_id' θ).const_mul (16/9 * gam)).mul (Real.hasDerivAt_sin θ))).congr_deriv ?_
  simp only [N1f]; ring

lemma hasDerivAt_N1f (θ : ℝ) : HasDerivAt N1f (N2f θ) θ := by
  unfold N1f
  refine (((Real.hasDerivAt_sin θ).const_mul (-(1 + 16/9 * gam))).sub
    (((hasDerivAt_id' θ).const_mul (16/9 * gam)).mul (Real.hasDerivAt_cos θ))).congr_deriv ?_
  simp only [N2f]; ring

lemma hasDerivAt_Df (θ : ℝ) : HasDerivAt Df (-(32/9) * θ) θ := by
  unfold Df
  refine (((hasDerivAt_pow 2 θ).const_mul (16/9)).const_sub 1).congr_deriv ?_
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
    ((((hasDerivAt_id' θ).const_mul (32/9)).mul (hasDerivAt_Nf θ)).div
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

/-- No poles from `1/2` on: `(16/9)(πx)² ≥ 4π²/9 > 1`. -/
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
  let G2T := iscale (16/9) (imul Gq T)
  let N := isub C (imul G2T S)
  let N1 := isub (imul (ineg (iadd (cst 1) (iscale (16/9) Gq))) S) (imul G2T C)
  let N2 := iadd (imul (ineg (iadd (cst 1) (iscale (32/9) Gq))) C) (imul G2T S)
  let T2 := imul T T
  let iD := iinvN (isub (cst 1) (iscale (16/9) T2))
  let iD2 := imul iD iD
  let K := imul N iD
  let K1 := iadd (imul N1 iD) (imul (iscale (32/9) (imul T N)) iD2)
  let K2 := iadd (iadd (iadd (imul N2 iD) (imul (iscale (64/9) (imul T N1)) iD2))
    (imul (iscale (32/9) N) iD2)) (imul (iscale (2048/81) (imul T2 N)) (imul iD2 iD))
  (K, iscale 2 (imul Pq (imul K K1)), iscale 2 (imul (imul Pq Pq) (iadd (imul K1 K1) (imul K K2))))

/-- The denominator enclosure is negative. -/
def negD (T : IQ) : Bool := decide ((isub (cst 1) (iscale (16/9) (imul T T))).2 < 0)

theorem enc_sound {C S T : IQ} {x : ℝ} (hC : Mem C (Real.cos (Real.pi * x)))
    (hS : Mem S (Real.sin (Real.pi * x))) (hT : Mem T (Real.pi * x)) (hneg : negD T = true) :
    Mem (enc C S T).1 (kfun x) ∧ Mem (enc C S T).2.1 (w1 x) ∧ Mem (enc C S T).2.2 (w2 x) := by
  simp only [negD, decide_eq_true_eq] at hneg
  set θ := Real.pi * x with hθ
  have hG : Mem Gq gam := ⟨gamLoQ_le, gamHiQ_ge⟩
  have hP : Mem Pq Real.pi := ⟨piLoQ_le, piHiQ_ge⟩
  have hG2T := mem_iscale (16/9) (mem_imul hG hT)
  have hN : Mem (isub C (imul (iscale (16/9) (imul Gq T)) S)) (Nf θ) := by
    have := mem_isub hC (mem_imul hG2T hS)
    refine mem_congr this ?_; unfold Nf; push_cast; ring
  have hN1 : Mem (isub (imul (ineg (iadd (cst 1) (iscale (16/9) Gq))) S) (imul (iscale (16/9) (imul Gq T)) C))
      (N1f θ) := by
    have := mem_isub (mem_imul (mem_ineg (mem_iadd (mem_cst 1) (mem_iscale (16/9) hG))) hS)
      (mem_imul hG2T hC)
    refine mem_congr this ?_; unfold N1f; push_cast; ring
  have hN2 : Mem (iadd (imul (ineg (iadd (cst 1) (iscale (32/9) Gq))) C) (imul (iscale (16/9) (imul Gq T)) S))
      (N2f θ) := by
    have := mem_iadd (mem_imul (mem_ineg (mem_iadd (mem_cst 1) (mem_iscale (32/9) hG))) hC)
      (mem_imul hG2T hS)
    refine mem_congr this ?_; unfold N2f; push_cast; ring
  have hT2 := mem_imul hT hT
  have hDm : Mem (isub (cst 1) (iscale (16/9) (imul T T))) (Df θ) := by
    have := mem_isub (mem_cst 1) (mem_iscale (16/9) hT2)
    refine mem_congr this ?_; unfold Df; push_cast; ring
  have hiD := mem_iinvN hDm hneg
  have hD0 : Df θ ≠ 0 := by
    have : Df θ < 0 := hDm.2.trans_lt (by exact_mod_cast hneg)
    exact this.ne
  have hiD2 := mem_imul hiD hiD
  have hK := mem_imul hN hiD
  have hK1 := mem_iadd (mem_imul hN1 hiD) (mem_imul (mem_iscale (32/9) (mem_imul hT hN)) hiD2)
  have hK2 := mem_iadd (mem_iadd (mem_iadd (mem_imul hN2 hiD)
    (mem_imul (mem_iscale (64/9) (mem_imul hT hN1)) hiD2)) (mem_imul (mem_iscale (32/9) hN) hiD2))
    (mem_imul (mem_iscale (2048/81) (mem_imul hT2 hN)) (mem_imul hiD2 hiD))
  have ek : kfun x = Nf θ * (1 / Df θ) := by
    rw [kfun_closed x (by simpa [Df, hθ] using hD0)]; simp [Nf, Df, hθ]; ring
  have ek1 : k1 x = Real.pi * (N1f θ * (1 / Df θ) + 32/9 * (θ * Nf θ) * (1 / Df θ * (1 / Df θ))) := by
    unfold k1 K1f; rw [← hθ]; field_simp
  have ek2 : k2 x = Real.pi ^ 2 * (N2f θ * (1 / Df θ) + 64/9 * (θ * N1f θ) * (1 / Df θ * (1 / Df θ))
      + 32/9 * Nf θ * (1 / Df θ * (1 / Df θ)) + 2048/81 * (θ * θ * Nf θ) * (1 / Df θ * (1 / Df θ) * (1 / Df θ))) := by
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
def cN : ℕ := 653514

/-- the weighted functional on the gaps, in real form -/
def G (g0 g1 g2 g3 g4 : ℝ) : ℝ :=
  (60390 / (SA:ℝ)) * g0 + (85125 / (SA:ℝ)) * g1 + (69521 / (SA:ℝ)) * g2 + (85125 / (SA:ℝ)) * g3 + (60390 / (SA:ℝ)) * g4
    + (26016264 / (SA:ℝ)) * wfun (g0) + (95829761 / (SA:ℝ)) * wfun (g0 + g1) + (52826981 / (SA:ℝ)) * wfun (g0 + g1 + g2) + (100000000 / (SA:ℝ)) * wfun (g0 + g1 + g2 + g3) + (200000000 / (SA:ℝ)) * wfun (g0 + g1 + g2 + g3 + g4) + (47404723 / (SA:ℝ)) * wfun (g1) + (4170238 / (SA:ℝ)) * wfun (g1 + g2) + (94346036 / (SA:ℝ)) * wfun (g1 + g2 + g3) + (100000000 / (SA:ℝ)) * wfun (g1 + g2 + g3 + g4) + (53158024 / (SA:ℝ)) * wfun (g2) + (4170238 / (SA:ℝ)) * wfun (g2 + g3) + (52826981 / (SA:ℝ)) * wfun (g2 + g3 + g4) + (47404723 / (SA:ℝ)) * wfun (g3) + (95829761 / (SA:ℝ)) * wfun (g3 + g4) + (26016264 / (SA:ℝ)) * wfun (g4)

/-- early exit: `true` once the running sum `s` reaches `C`, else the rest of the test -/
def ee (C s : ℕ) (rest : Bool) : Bool := Bool.rec (motive := fun _ => Bool) rest true (Nat.ble C s)

/-- the leaf test `cN·SC·U ≤ U·Σ b_r l_r + SC·Σ a_t lb_t` (U = 10¹⁰), the terms added in a fixed order and the
running sum tested after each -/
def leafOK (top : ℕ) (bk : ℕ → ℕ) (l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 : ℕ) : Bool :=
  let s0 := Nat.mul (Nat.add (Nat.add (Nat.add (Nat.add (Nat.mul 60390 l0) (Nat.mul 85125 l1)) (Nat.mul 69521 l2)) (Nat.mul 85125 l3)) (Nat.mul 60390 l4)) 10000000000
  ee 214143467520000000000 s0 (
  let s1 := Nat.add s0 (Nat.mul 1553357963264 (lb top bk l1 u1))
  ee 214143467520000000000 s1 (
  let s2 := Nat.add s1 (Nat.mul 1553357963264 (lb top bk l3 u3))
  ee 214143467520000000000 s2 (
  let s3 := Nat.add s2 (Nat.mul 1741882130432 (lb top bk l2 u2))
  ee 214143467520000000000 s3 (
  let s4 := Nat.add s3 (Nat.mul 852500938752 (lb top bk l0 u0))
  ee 214143467520000000000 s4 (
  let s5 := Nat.add s4 (Nat.mul 6553600000000 (lb top bk (Nat.add (Nat.add (Nat.add (Nat.add l0 l1) l2) l3) l4) (Nat.add (Nat.add (Nat.add (Nat.add u0 u1) u2) u3) u4)))
  ee 214143467520000000000 s5 (
  let s6 := Nat.add s5 (Nat.mul 852500938752 (lb top bk l4 u4))
  ee 214143467520000000000 s6 (
  let s7 := Nat.add s6 (Nat.mul 3276800000000 (lb top bk (Nat.add (Nat.add (Nat.add l0 l1) l2) l3) (Nat.add (Nat.add (Nat.add u0 u1) u2) u3)))
  ee 214143467520000000000 s7 (
  let s8 := Nat.add s7 (Nat.mul 3091530907648 (lb top bk (Nat.add (Nat.add l1 l2) l3) (Nat.add (Nat.add u1 u2) u3)))
  ee 214143467520000000000 s8 (
  let s9 := Nat.add s8 (Nat.mul 1731034513408 (lb top bk (Nat.add (Nat.add l0 l1) l2) (Nat.add (Nat.add u0 u1) u2)))
  ee 214143467520000000000 s9 (
  let s10 := Nat.add s9 (Nat.mul 3276800000000 (lb top bk (Nat.add (Nat.add (Nat.add l1 l2) l3) l4) (Nat.add (Nat.add (Nat.add u1 u2) u3) u4)))
  ee 214143467520000000000 s10 (
  let s11 := Nat.add s10 (Nat.mul 3140149608448 (lb top bk (Nat.add l0 l1) (Nat.add u0 u1)))
  ee 214143467520000000000 s11 (
  let s12 := Nat.add s11 (Nat.mul 1731034513408 (lb top bk (Nat.add (Nat.add l2 l3) l4) (Nat.add (Nat.add u2 u3) u4)))
  ee 214143467520000000000 s12 (
  let s13 := Nat.add s12 (Nat.mul 136650358784 (lb top bk (Nat.add l2 l3) (Nat.add u2 u3)))
  ee 214143467520000000000 s13 (
  let s14 := Nat.add s13 (Nat.mul 3140149608448 (lb top bk (Nat.add l3 l4) (Nat.add u3 u4)))
  ee 214143467520000000000 s14 (
  let s15 := Nat.add s14 (Nat.mul 136650358784 (lb top bk (Nat.add l1 l2) (Nat.add u1 u2)))
  Nat.ble 214143467520000000000 s15)))))))))))))))

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
    214143467520000000000 ≤ 10000000000 * (60390 * l0 + 85125 * l1 + 69521 * l2 + 85125 * l3 + 60390 * l4) + 32768 * (26016264 * lb top bk (l0) (u0) + 95829761 * lb top bk (l0 + l1) (u0 + u1) + 52826981 * lb top bk (l0 + l1 + l2) (u0 + u1 + u2) + 100000000 * lb top bk (l0 + l1 + l2 + l3) (u0 + u1 + u2 + u3) + 200000000 * lb top bk (l0 + l1 + l2 + l3 + l4) (u0 + u1 + u2 + u3 + u4) + 47404723 * lb top bk (l1) (u1) + 4170238 * lb top bk (l1 + l2) (u1 + u2) + 94346036 * lb top bk (l1 + l2 + l3) (u1 + u2 + u3) + 100000000 * lb top bk (l1 + l2 + l3 + l4) (u1 + u2 + u3 + u4) + 53158024 * lb top bk (l2) (u2) + 4170238 * lb top bk (l2 + l3) (u2 + u3) + 52826981 * lb top bk (l2 + l3 + l4) (u2 + u3 + u4) + 47404723 * lb top bk (l3) (u3) + 95829761 * lb top bk (l3 + l4) (u3 + u4) + 26016264 * lb top bk (l4) (u4)) := by
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
  set L : ℝ := 60390 * ((l0 : ℝ) / SC) + 85125 * ((l1 : ℝ) / SC) + 69521 * ((l2 : ℝ) / SC) + 85125 * ((l3 : ℝ) / SC) + 60390 * ((l4 : ℝ) / SC) with hL
  set Wt : ℝ := 26016264 * ((lb top bk (l0) (u0) : ℝ) / 10000000000) + 95829761 * ((lb top bk (l0 + l1) (u0 + u1) : ℝ) / 10000000000) + 52826981 * ((lb top bk (l0 + l1 + l2) (u0 + u1 + u2) : ℝ) / 10000000000) + 100000000 * ((lb top bk (l0 + l1 + l2 + l3) (u0 + u1 + u2 + u3) : ℝ) / 10000000000) + 200000000 * ((lb top bk (l0 + l1 + l2 + l3 + l4) (u0 + u1 + u2 + u3 + u4) : ℝ) / 10000000000) + 47404723 * ((lb top bk (l1) (u1) : ℝ) / 10000000000) + 4170238 * ((lb top bk (l1 + l2) (u1 + u2) : ℝ) / 10000000000) + 94346036 * ((lb top bk (l1 + l2 + l3) (u1 + u2 + u3) : ℝ) / 10000000000) + 100000000 * ((lb top bk (l1 + l2 + l3 + l4) (u1 + u2 + u3 + u4) : ℝ) / 10000000000) + 53158024 * ((lb top bk (l2) (u2) : ℝ) / 10000000000) + 4170238 * ((lb top bk (l2 + l3) (u2 + u3) : ℝ) / 10000000000) + 52826981 * ((lb top bk (l2 + l3 + l4) (u2 + u3 + u4) : ℝ) / 10000000000) + 47404723 * ((lb top bk (l3) (u3) : ℝ) / 10000000000) + 95829761 * ((lb top bk (l3 + l4) (u3 + u4) : ℝ) / 10000000000) + 26016264 * ((lb top bk (l4) (u4) : ℝ) / 10000000000) with hWt
  have e : (L + Wt) * (SC * 10000000000) = 10000000000 * (60390 * (l0 : ℝ) + 85125 * (l1 : ℝ) + 69521 * (l2 : ℝ) + 85125 * (l3 : ℝ) + 60390 * (l4 : ℝ)) + 32768 * (26016264 * (lb top bk (l0) (u0) : ℝ) + 95829761 * (lb top bk (l0 + l1) (u0 + u1) : ℝ) + 52826981 * (lb top bk (l0 + l1 + l2) (u0 + u1 + u2) : ℝ) + 100000000 * (lb top bk (l0 + l1 + l2 + l3) (u0 + u1 + u2 + u3) : ℝ) + 200000000 * (lb top bk (l0 + l1 + l2 + l3 + l4) (u0 + u1 + u2 + u3 + u4) : ℝ) + 47404723 * (lb top bk (l1) (u1) : ℝ) + 4170238 * (lb top bk (l1 + l2) (u1 + u2) : ℝ) + 94346036 * (lb top bk (l1 + l2 + l3) (u1 + u2 + u3) : ℝ) + 100000000 * (lb top bk (l1 + l2 + l3 + l4) (u1 + u2 + u3 + u4) : ℝ) + 53158024 * (lb top bk (l2) (u2) : ℝ) + 4170238 * (lb top bk (l2 + l3) (u2 + u3) : ℝ) + 52826981 * (lb top bk (l2 + l3 + l4) (u2 + u3 + u4) : ℝ) + 47404723 * (lb top bk (l3) (u3) : ℝ) + 95829761 * (lb top bk (l3 + l4) (u3 + u4) : ℝ) + 26016264 * (lb top bk (l4) (u4) : ℝ)) := by
    rw [hL, hWt]; field_simp; norm_num [SC]; try ring
  have hq' : (cN : ℝ) ≤ L + Wt := by
    refine le_of_mul_le_mul_right ?_ (by positivity : (0:ℝ) < SC * 10000000000)
    rw [e]
    calc (cN : ℝ) * (SC * 10000000000) = 214143467520000000000 := by norm_num [cN, SC]
      _ ≤ _ := hq
  unfold G
  rw [div_le_iff₀ hSA]
  have eG : ((60390 / (SA:ℝ)) * g0 + (85125 / (SA:ℝ)) * g1 + (69521 / (SA:ℝ)) * g2 + (85125 / (SA:ℝ)) * g3 + (60390 / (SA:ℝ)) * g4
      + (26016264 / (SA:ℝ)) * wfun (g0) + (95829761 / (SA:ℝ)) * wfun (g0 + g1) + (52826981 / (SA:ℝ)) * wfun (g0 + g1 + g2) + (100000000 / (SA:ℝ)) * wfun (g0 + g1 + g2 + g3) + (200000000 / (SA:ℝ)) * wfun (g0 + g1 + g2 + g3 + g4) + (47404723 / (SA:ℝ)) * wfun (g1) + (4170238 / (SA:ℝ)) * wfun (g1 + g2) + (94346036 / (SA:ℝ)) * wfun (g1 + g2 + g3) + (100000000 / (SA:ℝ)) * wfun (g1 + g2 + g3 + g4) + (53158024 / (SA:ℝ)) * wfun (g2) + (4170238 / (SA:ℝ)) * wfun (g2 + g3) + (52826981 / (SA:ℝ)) * wfun (g2 + g3 + g4) + (47404723 / (SA:ℝ)) * wfun (g3) + (95829761 / (SA:ℝ)) * wfun (g3 + g4) + (26016264 / (SA:ℝ)) * wfun (g4)) * SA
      = 60390 * g0 + 85125 * g1 + 69521 * g2 + 85125 * g3 + 60390 * g4 + 26016264 * wfun (g0) + 95829761 * wfun (g0 + g1) + 52826981 * wfun (g0 + g1 + g2) + 100000000 * wfun (g0 + g1 + g2 + g3) + 200000000 * wfun (g0 + g1 + g2 + g3 + g4) + 47404723 * wfun (g1) + 4170238 * wfun (g1 + g2) + 94346036 * wfun (g1 + g2 + g3) + 100000000 * wfun (g1 + g2 + g3 + g4) + 53158024 * wfun (g2) + 4170238 * wfun (g2 + g3) + 52826981 * wfun (g2 + g3 + g4) + 47404723 * wfun (g3) + 95829761 * wfun (g3 + g4) + 26016264 * wfun (g4) := by
    field_simp; try ring
  rw [eG]
  rw [hL, hWt] at hq'
  linarith [hq', mul_le_mul_of_nonneg_left h01 (by positivity : (0:ℝ) ≤ 60390), mul_le_mul_of_nonneg_left h11 (by positivity : (0:ℝ) ≤ 85125), mul_le_mul_of_nonneg_left h21 (by positivity : (0:ℝ) ≤ 69521), mul_le_mul_of_nonneg_left h31 (by positivity : (0:ℝ) ≤ 85125), mul_le_mul_of_nonneg_left h41 (by positivity : (0:ℝ) ≤ 60390), mul_le_mul_of_nonneg_left w0 (by positivity : (0:ℝ) ≤ 26016264), mul_le_mul_of_nonneg_left w1 (by positivity : (0:ℝ) ≤ 95829761), mul_le_mul_of_nonneg_left w2 (by positivity : (0:ℝ) ≤ 52826981), mul_le_mul_of_nonneg_left w3 (by positivity : (0:ℝ) ≤ 100000000), mul_le_mul_of_nonneg_left w4 (by positivity : (0:ℝ) ≤ 200000000), mul_le_mul_of_nonneg_left w5 (by positivity : (0:ℝ) ≤ 47404723), mul_le_mul_of_nonneg_left w6 (by positivity : (0:ℝ) ≤ 4170238), mul_le_mul_of_nonneg_left w7 (by positivity : (0:ℝ) ≤ 94346036), mul_le_mul_of_nonneg_left w8 (by positivity : (0:ℝ) ≤ 100000000), mul_le_mul_of_nonneg_left w9 (by positivity : (0:ℝ) ≤ 53158024), mul_le_mul_of_nonneg_left w10 (by positivity : (0:ℝ) ≤ 4170238), mul_le_mul_of_nonneg_left w11 (by positivity : (0:ℝ) ≤ 52826981), mul_le_mul_of_nonneg_left w12 (by positivity : (0:ℝ) ≤ 47404723), mul_le_mul_of_nonneg_left w13 (by positivity : (0:ℝ) ≤ 95829761), mul_le_mul_of_nonneg_left w14 (by positivity : (0:ℝ) ≤ 26016264)]


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
    (hS0 : cN * SC ≤ 60390 * S0) (hS1 : cN * SC ≤ 85125 * S1) (hS2 : cN * SC ≤ 69521 * S2) (hS3 : cN * SC ≤ 85125 * S3) (hS4 : cN * SC ≤ 60390 * S4)
    (hcov0 : coverCheck 26016264 (SC / 2) S0 cover0 = true) (hcov1 : coverCheck 47404723 (SC / 2) S1 cover1 = true) (hcov2 : coverCheck 53158024 (SC / 2) S2 cover2 = true) (hcov3 : coverCheck 47404723 (SC / 2) S3 cover3 = true) (hcov4 : coverCheck 26016264 (SC / 2) S4 cover4 = true)
    (hwin : cN * 100 ≤ 19 * 26016264)
    (hrun : ∀ i0 i1 i2 i3 i4, i0 < (badOf cover0).length → i1 < (badOf cover1).length → i2 < (badOf cover2).length → i3 < (badOf cover3).length → i4 < (badOf cover4).length →
      Covered ((badOf cover0).getD i0 (0, 0)).1 ((badOf cover0).getD i0 (0, 0)).2 ((badOf cover1).getD i1 (0, 0)).1 ((badOf cover1).getD i1 (0, 0)).2 ((badOf cover2).getD i2 (0, 0)).1 ((badOf cover2).getD i2 (0, 0)).2 ((badOf cover3).getD i3 (0, 0)).1 ((badOf cover3).getD i3 (0, 0)).2 ((badOf cover4).getD i4 (0, 0)).1 ((badOf cover4).getD i4 (0, 0)).2) :
    ∀ g0 g1 g2 g3 g4 : ℝ, 0 ≤ g0 → 0 ≤ g1 → 0 ≤ g2 → 0 ≤ g3 → 0 ≤ g4 → (cN : ℝ) / SA ≤ G g0 g1 g2 g3 g4 ∨ g4 < g0 := by
  intro g0 g1 g2 g3 g4 hg0 hg1 hg2 hg3 hg4
  have hw := fun v : ℝ => wfun_nonneg v
  have hSA : (0:ℝ) < SA := by norm_num [SA]
  have hSC : (0:ℝ) < SC := by norm_num [SC]
  have hhalf : ((SC / 2 : ℕ) : ℝ) / SC = 1/2 := by norm_num [SC]
  set Lin : ℝ := (60390 / (SA:ℝ)) * g0 + (85125 / (SA:ℝ)) * g1 + (69521 / (SA:ℝ)) * g2 + (85125 / (SA:ℝ)) * g3 + (60390 / (SA:ℝ)) * g4 with hLin
  set Wt : ℝ := (26016264 / (SA:ℝ)) * wfun (g0) + (95829761 / (SA:ℝ)) * wfun (g0 + g1) + (52826981 / (SA:ℝ)) * wfun (g0 + g1 + g2) + (100000000 / (SA:ℝ)) * wfun (g0 + g1 + g2 + g3) + (200000000 / (SA:ℝ)) * wfun (g0 + g1 + g2 + g3 + g4) + (47404723 / (SA:ℝ)) * wfun (g1) + (4170238 / (SA:ℝ)) * wfun (g1 + g2) + (94346036 / (SA:ℝ)) * wfun (g1 + g2 + g3) + (100000000 / (SA:ℝ)) * wfun (g1 + g2 + g3 + g4) + (53158024 / (SA:ℝ)) * wfun (g2) + (4170238 / (SA:ℝ)) * wfun (g2 + g3) + (52826981 / (SA:ℝ)) * wfun (g2 + g3 + g4) + (47404723 / (SA:ℝ)) * wfun (g3) + (95829761 / (SA:ℝ)) * wfun (g3 + g4) + (26016264 / (SA:ℝ)) * wfun (g4) with hWt
  have hG : G g0 g1 g2 g3 g4 = Lin + Wt := by unfold G; rw [hLin, hWt]; ring
  have hb00 : (0:ℝ) ≤ (60390 / (SA:ℝ)) * g0 := mul_nonneg (by positivity) hg0
  have hb10 : (0:ℝ) ≤ (85125 / (SA:ℝ)) * g1 := mul_nonneg (by positivity) hg1
  have hb20 : (0:ℝ) ≤ (69521 / (SA:ℝ)) * g2 := mul_nonneg (by positivity) hg2
  have hb30 : (0:ℝ) ≤ (85125 / (SA:ℝ)) * g3 := mul_nonneg (by positivity) hg3
  have hb40 : (0:ℝ) ≤ (60390 / (SA:ℝ)) * g4 := mul_nonneg (by positivity) hg4
  have ha00 : (0:ℝ) ≤ (26016264 / (SA:ℝ)) * wfun (g0) := mul_nonneg (by positivity) (hw _)
  have ha10 : (0:ℝ) ≤ (95829761 / (SA:ℝ)) * wfun (g0 + g1) := mul_nonneg (by positivity) (hw _)
  have ha20 : (0:ℝ) ≤ (52826981 / (SA:ℝ)) * wfun (g0 + g1 + g2) := mul_nonneg (by positivity) (hw _)
  have ha30 : (0:ℝ) ≤ (100000000 / (SA:ℝ)) * wfun (g0 + g1 + g2 + g3) := mul_nonneg (by positivity) (hw _)
  have ha40 : (0:ℝ) ≤ (200000000 / (SA:ℝ)) * wfun (g0 + g1 + g2 + g3 + g4) := mul_nonneg (by positivity) (hw _)
  have ha50 : (0:ℝ) ≤ (47404723 / (SA:ℝ)) * wfun (g1) := mul_nonneg (by positivity) (hw _)
  have ha60 : (0:ℝ) ≤ (4170238 / (SA:ℝ)) * wfun (g1 + g2) := mul_nonneg (by positivity) (hw _)
  have ha70 : (0:ℝ) ≤ (94346036 / (SA:ℝ)) * wfun (g1 + g2 + g3) := mul_nonneg (by positivity) (hw _)
  have ha80 : (0:ℝ) ≤ (100000000 / (SA:ℝ)) * wfun (g1 + g2 + g3 + g4) := mul_nonneg (by positivity) (hw _)
  have ha90 : (0:ℝ) ≤ (53158024 / (SA:ℝ)) * wfun (g2) := mul_nonneg (by positivity) (hw _)
  have ha100 : (0:ℝ) ≤ (4170238 / (SA:ℝ)) * wfun (g2 + g3) := mul_nonneg (by positivity) (hw _)
  have ha110 : (0:ℝ) ≤ (52826981 / (SA:ℝ)) * wfun (g2 + g3 + g4) := mul_nonneg (by positivity) (hw _)
  have ha120 : (0:ℝ) ≤ (47404723 / (SA:ℝ)) * wfun (g3) := mul_nonneg (by positivity) (hw _)
  have ha130 : (0:ℝ) ≤ (95829761 / (SA:ℝ)) * wfun (g3 + g4) := mul_nonneg (by positivity) (hw _)
  have ha140 : (0:ℝ) ≤ (26016264 / (SA:ℝ)) * wfun (g4) := mul_nonneg (by positivity) (hw _)
  have hLin0 : 0 ≤ Lin := by rw [hLin]; linarith [hb00, hb10, hb20, hb30, hb40]
  have hWt0 : 0 ≤ Wt := by rw [hWt]; linarith [ha00, ha10, ha20, ha30, ha40, ha50, ha60, ha70, ha80, ha90, ha100, ha110, ha120, ha130, ha140]
  have hbL0 : (60390 / (SA:ℝ)) * g0 ≤ Lin := by rw [hLin]; linarith [hb10, hb20, hb30, hb40]
  have hbL1 : (85125 / (SA:ℝ)) * g1 ≤ Lin := by rw [hLin]; linarith [hb00, hb20, hb30, hb40]
  have hbL2 : (69521 / (SA:ℝ)) * g2 ≤ Lin := by rw [hLin]; linarith [hb00, hb10, hb30, hb40]
  have hbL3 : (85125 / (SA:ℝ)) * g3 ≤ Lin := by rw [hLin]; linarith [hb00, hb10, hb20, hb40]
  have hbL4 : (60390 / (SA:ℝ)) * g4 ≤ Lin := by rw [hLin]; linarith [hb00, hb10, hb20, hb30]
  have haW0 : (26016264 / (SA:ℝ)) * wfun (g0) ≤ Wt := by rw [hWt]; linarith [ha10, ha20, ha30, ha40, ha50, ha60, ha70, ha80, ha90, ha100, ha110, ha120, ha130, ha140]
  have haW1 : (95829761 / (SA:ℝ)) * wfun (g0 + g1) ≤ Wt := by rw [hWt]; linarith [ha00, ha20, ha30, ha40, ha50, ha60, ha70, ha80, ha90, ha100, ha110, ha120, ha130, ha140]
  have haW2 : (52826981 / (SA:ℝ)) * wfun (g0 + g1 + g2) ≤ Wt := by rw [hWt]; linarith [ha00, ha10, ha30, ha40, ha50, ha60, ha70, ha80, ha90, ha100, ha110, ha120, ha130, ha140]
  have haW3 : (100000000 / (SA:ℝ)) * wfun (g0 + g1 + g2 + g3) ≤ Wt := by rw [hWt]; linarith [ha00, ha10, ha20, ha40, ha50, ha60, ha70, ha80, ha90, ha100, ha110, ha120, ha130, ha140]
  have haW4 : (200000000 / (SA:ℝ)) * wfun (g0 + g1 + g2 + g3 + g4) ≤ Wt := by rw [hWt]; linarith [ha00, ha10, ha20, ha30, ha50, ha60, ha70, ha80, ha90, ha100, ha110, ha120, ha130, ha140]
  have haW5 : (47404723 / (SA:ℝ)) * wfun (g1) ≤ Wt := by rw [hWt]; linarith [ha00, ha10, ha20, ha30, ha40, ha60, ha70, ha80, ha90, ha100, ha110, ha120, ha130, ha140]
  have haW6 : (4170238 / (SA:ℝ)) * wfun (g1 + g2) ≤ Wt := by rw [hWt]; linarith [ha00, ha10, ha20, ha30, ha40, ha50, ha70, ha80, ha90, ha100, ha110, ha120, ha130, ha140]
  have haW7 : (94346036 / (SA:ℝ)) * wfun (g1 + g2 + g3) ≤ Wt := by rw [hWt]; linarith [ha00, ha10, ha20, ha30, ha40, ha50, ha60, ha80, ha90, ha100, ha110, ha120, ha130, ha140]
  have haW8 : (100000000 / (SA:ℝ)) * wfun (g1 + g2 + g3 + g4) ≤ Wt := by rw [hWt]; linarith [ha00, ha10, ha20, ha30, ha40, ha50, ha60, ha70, ha90, ha100, ha110, ha120, ha130, ha140]
  have haW9 : (53158024 / (SA:ℝ)) * wfun (g2) ≤ Wt := by rw [hWt]; linarith [ha00, ha10, ha20, ha30, ha40, ha50, ha60, ha70, ha80, ha100, ha110, ha120, ha130, ha140]
  have haW10 : (4170238 / (SA:ℝ)) * wfun (g2 + g3) ≤ Wt := by rw [hWt]; linarith [ha00, ha10, ha20, ha30, ha40, ha50, ha60, ha70, ha80, ha90, ha110, ha120, ha130, ha140]
  have haW11 : (52826981 / (SA:ℝ)) * wfun (g2 + g3 + g4) ≤ Wt := by rw [hWt]; linarith [ha00, ha10, ha20, ha30, ha40, ha50, ha60, ha70, ha80, ha90, ha100, ha120, ha130, ha140]
  have haW12 : (47404723 / (SA:ℝ)) * wfun (g3) ≤ Wt := by rw [hWt]; linarith [ha00, ha10, ha20, ha30, ha40, ha50, ha60, ha70, ha80, ha90, ha100, ha110, ha130, ha140]
  have haW13 : (95829761 / (SA:ℝ)) * wfun (g3 + g4) ≤ Wt := by rw [hWt]; linarith [ha00, ha10, ha20, ha30, ha40, ha50, ha60, ha70, ha80, ha90, ha100, ha110, ha120, ha140]
  have haW14 : (26016264 / (SA:ℝ)) * wfun (g4) ≤ Wt := by rw [hWt]; linarith [ha00, ha10, ha20, ha30, ha40, ha50, ha60, ha70, ha80, ha90, ha100, ha110, ha120, ha130]
  -- gap 0: beyond the cutoff the pressure alone pays
  by_cases hcut0 : (S0 : ℝ) / SC ≤ g0
  · have h1 : (cN : ℝ) / SA ≤ (60390 / (SA:ℝ)) * g0 := by
      have hq := (Nat.cast_le (α := ℝ)).mpr hS0; push_cast at hq
      rw [div_le_iff₀ hSA]
      have e : (60390 / (SA:ℝ)) * g0 * SA = 60390 * g0 := by field_simp
      rw [e]
      calc (cN : ℝ) = (cN : ℝ) * SC / SC := by field_simp
        _ ≤ 60390 * S0 / SC := by apply div_le_div_of_nonneg_right _ hSC.le; linarith
        _ = 60390 * ((S0 : ℝ) / SC) := by ring
        _ ≤ 60390 * g0 := mul_le_mul_of_nonneg_left hcut0 (by norm_num)
    left; rw [hG]; linarith [h1, hbL0, hWt0]
  push_neg at hcut0
  rcases le_total g0 ((SC / 2 : ℕ) / (SC : ℝ)) with hwin0 | hwin0
  · have hw19 := wfun_window g0 hg0 (by rw [hhalf] at hwin0; exact hwin0)
    have hq := (Nat.cast_le (α := ℝ)).mpr hwin; push_cast at hq
    have h1 : (cN : ℝ) / SA ≤ (26016264 / (SA:ℝ)) * wfun g0 := by
      rw [div_le_iff₀ hSA]
      have e : (26016264 / (SA:ℝ)) * wfun g0 * SA = 26016264 * wfun g0 := by field_simp
      rw [e]
      have hm := mul_le_mul_of_nonneg_left hw19 (by norm_num : (0:ℝ) ≤ 26016264)
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
  · have h1 : (cN : ℝ) / SA ≤ (85125 / (SA:ℝ)) * g1 := by
      have hq := (Nat.cast_le (α := ℝ)).mpr hS1; push_cast at hq
      rw [div_le_iff₀ hSA]
      have e : (85125 / (SA:ℝ)) * g1 * SA = 85125 * g1 := by field_simp
      rw [e]
      calc (cN : ℝ) = (cN : ℝ) * SC / SC := by field_simp
        _ ≤ 85125 * S1 / SC := by apply div_le_div_of_nonneg_right _ hSC.le; linarith
        _ = 85125 * ((S1 : ℝ) / SC) := by ring
        _ ≤ 85125 * g1 := mul_le_mul_of_nonneg_left hcut1 (by norm_num)
    left; rw [hG]; linarith [h1, hbL1, hWt0]
  push_neg at hcut1
  rcases le_total g1 ((SC / 2 : ℕ) / (SC : ℝ)) with hwin1 | hwin1
  · have hw19 := wfun_window g1 hg1 (by rw [hhalf] at hwin1; exact hwin1)
    have hq := (Nat.cast_le (α := ℝ)).mpr hwin; push_cast at hq
    have h1 : (cN : ℝ) / SA ≤ (47404723 / (SA:ℝ)) * wfun g1 := by
      rw [div_le_iff₀ hSA]
      have e : (47404723 / (SA:ℝ)) * wfun g1 * SA = 47404723 * wfun g1 := by field_simp
      rw [e]
      have hm := mul_le_mul_of_nonneg_left hw19 (by norm_num : (0:ℝ) ≤ 47404723)
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
  · have h1 : (cN : ℝ) / SA ≤ (69521 / (SA:ℝ)) * g2 := by
      have hq := (Nat.cast_le (α := ℝ)).mpr hS2; push_cast at hq
      rw [div_le_iff₀ hSA]
      have e : (69521 / (SA:ℝ)) * g2 * SA = 69521 * g2 := by field_simp
      rw [e]
      calc (cN : ℝ) = (cN : ℝ) * SC / SC := by field_simp
        _ ≤ 69521 * S2 / SC := by apply div_le_div_of_nonneg_right _ hSC.le; linarith
        _ = 69521 * ((S2 : ℝ) / SC) := by ring
        _ ≤ 69521 * g2 := mul_le_mul_of_nonneg_left hcut2 (by norm_num)
    left; rw [hG]; linarith [h1, hbL2, hWt0]
  push_neg at hcut2
  rcases le_total g2 ((SC / 2 : ℕ) / (SC : ℝ)) with hwin2 | hwin2
  · have hw19 := wfun_window g2 hg2 (by rw [hhalf] at hwin2; exact hwin2)
    have hq := (Nat.cast_le (α := ℝ)).mpr hwin; push_cast at hq
    have h1 : (cN : ℝ) / SA ≤ (53158024 / (SA:ℝ)) * wfun g2 := by
      rw [div_le_iff₀ hSA]
      have e : (53158024 / (SA:ℝ)) * wfun g2 * SA = 53158024 * wfun g2 := by field_simp
      rw [e]
      have hm := mul_le_mul_of_nonneg_left hw19 (by norm_num : (0:ℝ) ≤ 53158024)
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
  · have h1 : (cN : ℝ) / SA ≤ (85125 / (SA:ℝ)) * g3 := by
      have hq := (Nat.cast_le (α := ℝ)).mpr hS3; push_cast at hq
      rw [div_le_iff₀ hSA]
      have e : (85125 / (SA:ℝ)) * g3 * SA = 85125 * g3 := by field_simp
      rw [e]
      calc (cN : ℝ) = (cN : ℝ) * SC / SC := by field_simp
        _ ≤ 85125 * S3 / SC := by apply div_le_div_of_nonneg_right _ hSC.le; linarith
        _ = 85125 * ((S3 : ℝ) / SC) := by ring
        _ ≤ 85125 * g3 := mul_le_mul_of_nonneg_left hcut3 (by norm_num)
    left; rw [hG]; linarith [h1, hbL3, hWt0]
  push_neg at hcut3
  rcases le_total g3 ((SC / 2 : ℕ) / (SC : ℝ)) with hwin3 | hwin3
  · have hw19 := wfun_window g3 hg3 (by rw [hhalf] at hwin3; exact hwin3)
    have hq := (Nat.cast_le (α := ℝ)).mpr hwin; push_cast at hq
    have h1 : (cN : ℝ) / SA ≤ (47404723 / (SA:ℝ)) * wfun g3 := by
      rw [div_le_iff₀ hSA]
      have e : (47404723 / (SA:ℝ)) * wfun g3 * SA = 47404723 * wfun g3 := by field_simp
      rw [e]
      have hm := mul_le_mul_of_nonneg_left hw19 (by norm_num : (0:ℝ) ≤ 47404723)
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
  · have h1 : (cN : ℝ) / SA ≤ (60390 / (SA:ℝ)) * g4 := by
      have hq := (Nat.cast_le (α := ℝ)).mpr hS4; push_cast at hq
      rw [div_le_iff₀ hSA]
      have e : (60390 / (SA:ℝ)) * g4 * SA = 60390 * g4 := by field_simp
      rw [e]
      calc (cN : ℝ) = (cN : ℝ) * SC / SC := by field_simp
        _ ≤ 60390 * S4 / SC := by apply div_le_div_of_nonneg_right _ hSC.le; linarith
        _ = 60390 * ((S4 : ℝ) / SC) := by ring
        _ ≤ 60390 * g4 := mul_le_mul_of_nonneg_left hcut4 (by norm_num)
    left; rw [hG]; linarith [h1, hbL4, hWt0]
  push_neg at hcut4
  rcases le_total g4 ((SC / 2 : ℕ) / (SC : ℝ)) with hwin4 | hwin4
  · have hw19 := wfun_window g4 hg4 (by rw [hhalf] at hwin4; exact hwin4)
    have hq := (Nat.cast_le (α := ℝ)).mpr hwin; push_cast at hq
    have h1 : (cN : ℝ) / SA ≤ (26016264 / (SA:ℝ)) * wfun g4 := by
      rw [div_le_iff₀ hSA]
      have e : (26016264 / (SA:ℝ)) * wfun g4 * SA = 26016264 * wfun g4 := by field_simp
      rw [e]
      have hm := mul_le_mul_of_nonneg_left hw19 (by norm_num : (0:ℝ) ≤ 26016264)
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

def TOP : ℕ := 137117952436064606828375394336669499952450716776597344774162284726500484978842349375544190737286239299823483844280201275331240391958260717013374889040929459075334405692188653374040297460656511408027447679018605267773263813228299222024251460681363959881886615568345548097596553949665605109747440027523063868400279753578324361518722580048484041249701223113689032366160515360400249554734461605891014386855704232654977835825015843656610056282137490223219600425428244862059740271549057107243727039766907581935823030069989224512725128725809023887945519963386268580715707787191890676703913774456941401222482870621051952051047541800822489726016164197062069401784999585940102819351328969721832474070573429636072402889213715355639141096483326700787312536179330858718099077606785815121760680434512069531855771490939758007001500765371414375213517460666313550998696297509862960549468164072142727072104031580420462522477908714236708796208355385789942822485594724586435081038005344097639635203798708767171262891236601393442569562673082845502219008773275712426554698557682987188930616848030528459146192100374262462632144134655141895718473572504190858411461618215534202342174143118322347847378774236977461045035703370826436857885496826543846087318806532083890010369007057671343950334060738209595747561338052254975986465915043319084945574474868283295531325694918253646100031423348294940524352962901594400884778878138207558386208942878577355103913408071738056589296872333511144992568678657594542309203726210057942322000300067220739761665959178556441330377619066166379577576692340128336448841502519346201377024426978737584285591262107739836139783062568064016040642519979552655399385070753270671865370545159732191560172702922750668665330011238842929616095463249170388650464044097866926609060521218991601072050448150413303860417326993556444260197496884657184175540538302698843166198262739995390176567400978134794421040570740779219077524553131094505954852928583626766421366518723693014890241315191128993054596764258119288840080390949389763114783747353847243485168989591722480365177766986027816546179362969769823355697053298238685309058907558224419319026968146046322589091424966973293323388614474242256777413482237837777377820812743247966356277945496322808593506505440927871798478022165908002406977651142658098935374678991514847110574652970361015345471152052526478293246083712670190582034515801520265067282737971656312523366671314508834847421196012001944079228599331234921105427821280004631053453697215329761462457121250703514154252224254207701120104465208138238912368338427192056135559131860877623228250572239258045898084968722464738295006866036791183832066209279375970154536858645876302610565831330027070239831090315052732543626347353659886905698622279415229057088577081362783839182988310531435714411448128502508840678779760359002254476841647768832139865468914759926495252399057542624049521448743129332113722989685033363609625401633545737805166759589871362804949184790393437658352211062948425771767459655977737760386013210426349648952974813618419774556051186092519139577856221332895760426413443299264426365499906986770961410741979627906005517288086681005322575679678394400519316144539776157628004335167928538399956021798670387134436516800696441670295978304141749651358458064196688490265755655844976898759867495533127786293880393138100726513404552329487344936771911730424490338043827878822074771771127538321328452530202074124780033996508377949473020883241003772880551912946311741373653269173094607010799565693973876706283425962233069990782534724869118330445900355845481303740420749202195153555505435323700639627944005303914204844789605197544333974928167951092635459425417489041393231704712179040025072484140987953980072042414662049967333646878623342546132680914978538623612766941716684984082885485977785579762373393625287854743241374782901469147052957038837590085077934980907357402753013941226159547660985583708548139542322490525877677624295184753494683811959491508707257605880192580161650477089333432997703533285803274768239986823461803445346287738258973546737027514434681017941525078390596939607824502900115192578442923434724985995849874083615208401035878265419354954730246646653043993166964068943194754728542828117705270058194997086663696858612281063005628924534552686936681289926791957671767541505419566676406451204780722409484677748655987889883566806826126718164134968253363689278122201038504126367512438074711735419822536089949576676120346643429674406967999844853696986593452671540847231057328998565878873419609414699927805270403306942811281361501101787986259115071500581290390063134395643110177919306535105885184520758865580156419189383176858149652437452114495240535719324619392570190464491130854112224633319268053144896135165704374690373552829897118310610441602442360228258960859924539788633444998410121095620375767080827570545187109715707493325577999270428799008867784259480683715109789703792525501030260984000066184624119634501767857700864
def BK_16 : ℕ := 89064631942218570252190274310107874004959319585440886850482335212758006955156898334711832622220271485541450038002297190474420022764303115643920967
def BK_17 : ℕ := 78626000629502454158891528269945918984126061901330951999517999471383358685826347204859604131999957587593299221642242965030942547957406610799732935
def BK_18 : ℕ := 68610896543633413466324015209939145240523805665390029577954262251471552418750921461872793152456120443475131846934073345215144591492619804651909639
def BK_19 : ℕ := 59122683966200870102589758252703224134102865559426396361973756532705876524513702923441830823995390712708605666416135575731992610308408750263760071
def BK_20 : ℕ := 679533492542705992104452503386076912191377676956019408853274887126841246317454241503777375983726684118825753773032813089098532089075736537349279061729287201692024209166747817044626775514027368520429370219477804562838494937298260285762643875531017250151108320127191783721530287314279563092811263770886
def BK_21 : ℕ := 568312768089105470794448388187213696046968896977999263256169869864912994335280246649445753256612156528233773070250630397916643726519496678088093775402213693903528352734415315207901941974127702164108762785253422873977209771818183363718904345648915328698574193481684138908341304617579536374917183270310
def BK_22 : ℕ := 467101981438118416879093773855561170512132968500325841359027446875074032197660278747879861448556804890101593187633100864018811352895317426824947162589676560892582175348833985584225399278902493190354528669332244140814650547063162164259294304375059715263117570108125129873204194363351382802097888557670
def BK_23 : ℕ := 376312309997113132394549865848587384731395770427768990523033051736519300706091056403431486031591284138760036405594641098562637542316346754490303050769111037195278869796975636096452771393497329924190674766168644035165139837803114980727411070909219762208872068834684710995330769184165183712860892394758
def BK_24 : ℕ := 296146104530722277016386370096852490001690305596304927068973025437630449672093770861403781224875565750551199897781914283464970290810241573754231731700291926545397670241583998962233185575517882674171701918355386965747021030303141974100241601230832308678134022968762349200693213003473066240534131815046
def BK_25 : ℕ := 226606415244272437937408580950682447101733865593351281941280937295552278538939865822177664809260161586081662147072224373977587387521400255523184875214243922138350004007330271416892869125619071875024228305022267292440173154833797962817826690730319318291112316241143290503851019689960452190802527549830
def BK_26 : ℕ := 30192962481190086408560645714490192173622710750872341954777888745589591262982348866224624091181657080732042700800170576647294209409558247532446395887877895000831875365880093891954079453260032454357166046559613225534682998786043580567591742957931278429569048130907484893892556468340691719390699177292538324161433155760005157937417078255972726163651473702015591583435172167813334523498007053552863022602512841135017564207089722127575643050877313531407068571489315858986431347061633587622117374899437503323971644741337384462689001770455190643682693849964037280366053901697696075129898188078013400781035176654341
def BK_27 : ℕ := 21353450157270835047648646182502571042070697708878075638235968849573710748890961497072118020530157402871967168990197484153795028115572418733012139144267585056370265997383343413205868798477838080263918462595748479280018686458107432269475522448235734005210744097489552944773024834591959634394753538714776905514713263211511961451826145350676404495929912189788304611933931970720427285092856889254082175184323613299796036602284058838088436454162260514457340762256981191658055948626355809821355762833642117542201470127248527380182355813572396798442098057751302588879198898357367432724762732884600281017982923079013
def BK_28 : ℕ := 14244549427994322042696947510352936858381797435427748744231055092127008619205554219847712539168717964029930241273868369593933485858917104148856586613106682479298097717365076670698017023895879007769813739480331772444805274069092266267897184243410254073229871196697228886865385885731933452005246805500050492922370780205740081797795572916144176796594446535961215113506535970053027437613969479974527545514344261621776623424181844653979527968719961409277990768595583476016080007610405467629288904618110358327813806749382396902228707803643392070793333133664177613673846769306563373052780867782954128989910621966597
def BK_29 : ℕ := 8750208554484379561667574195652221461520599295602138893672058058558810311134733111820856073443329720169564884731530865946677247887646610064278063539427268406882778767659309924430291921218968938815799383759474861500573683276172217581695209810605668537920387003706539916350232058875337641181393135866603165000120703290900571817491188076590224178824043885053077992143405111510898062715661623508317051317686351654260340218202759228883774538566734353395326782997598823714470973538024613749552746586393585488810181172540291129707787049152320009759440635129294348281409296792675367229673434529962252374593322133253
def BK_30 : ℕ := 153096671430533239744296157819230814263021547989314018915476688930353170080371625415682356218626063887370005161366337721134941763850609587826934800546065207781439012735127669982006122865680615975355979082073131736000589037372190282860106302716127699742527802657867088828764652539470374402461730427178971433437744469525609438709405277604325773207802102628666338808480769402953584859213379602038601762342660904603618750192732499682025111407489410600396824145286239498244246509215440709780191530789749338959570297856178529191595912838664626047093278718753812757222076036027666692987682377922998071745904667707605053868068270867227200348794123323047837691865214824347081081042171004559680062282313123327385161299318672598242237783465587923637737747593290589148765525707190019700527370324099366447067763620529585145737809079594407823362191281384003576429051952056629712924818645454360661493074332936615531874136787173646917290959539908090082481515237330541390961324330140106669433962148015551879038429020262368775972341749684511050510360426593385471543854966240210331119751156339954285053259238925466025792702332952182684454953321864349345309928505947700143234986777835413266101736025813048256666634716743121063871689891731297892
def BK_31 : ℕ := 66177040986014439810585227350764882548018197844601995661022381629328465846335951896343022047305968368533071618222911987502245637993255179406579474788316303153721497772551142869346750261961663699647665270274570528036504102151299067864329114555425312114857449520750691502384995182586659242495869138057485096947930415388638850843065425366093626141858675695575545052991284732615881039044844644954657326448747555371725120336603599517919303956700367974843154280958668918241979565982126163694046701427324475399232088272257894490800431528322610328917988006117596253647584428263045986235836005347646180116854780977460624474768828782475650355546328708216301197289569518576795833222125156878312405163184590101731424387711383803016207205128732233595010139223094275511024840851897094485242435153791152631430408002343195202257060836739931882626109983845489966528518569950496333856894761146114734911531506314693346085512669687606614629048818105880189582060079400687756148578404705466454573848354229526631751058597795442014956214780809905171267467337980446529488530530066670758337698940595883345925151172760042514958152344331437947965017093699885792250872391695703675729088822071634433321770299104251503277101182539973625964945875512556516
def BK_32 : ℕ := 16983412189976548766427700687174504789836505603457877060321500996172142560837409777599581959912464528316007008520162734807351056853697067398148192028695500939610880854023621777014379883875509472803123413391472610922531007600651659284362539469038766135762446786575853277459960104737291406183641289910918164568648736748802096052622357160861409265284954199736763688798540392424337311960252549715106663704673192117786176486252315316916070515799456772467517191042003869507507343907450780150710964760853691178977769920281536170257266809207361210735408181974409265327672372482664306169508013111532620379803178974241218536245123637740895221161736483907095192585213443061937852209243097634664029285926769508218813222352122343766299256760589757166871463295342084309615352369059384415188806490377347110050552767193367319152455557993442280008362616203648959262007275870929776454751304262826368567977330032438089032116220899358611949536447475439849110389447425820859740161302467348725098934385045814238529544633008595612322936919175192649215062888972621089247641286059430288122640783863236381004556117808136611813441458477167494398118854120220872700085500216671385986191955377264828869955530938241073868335497330605340582692461800929860
def BK_33 : ℕ := 121795086106833129521619882003808016483626815423914113867163451231957896414772144606347906577201498235805189834446508141669286169423393877700458649273311046622661375456106342854449070779752760617861159456873129078631593470229947057921886194853976890722264875660199911368499401947535722448565848421783198730377034239495356214959067958503785576316015756650031825866857677307826002032452602968559477644387395982334492938099718409225715810774393467185887885912261800571105280928317281997961982274277168434380684572228696538261803608543069745505157583921853143607943375167298010091532925567878876766697730857808738137462457526249896187847519576108994552751369302827157275435608719300937851716835631918938109472334450176121435105451422246680142671475358673266332994717913878369208309967556477750410124216892775332869458228473457626409495221029594723898211350545204064607550566320612367624157424402392639431170916562524905627732282115228302292189426160872235249303915399863127705121643906671056404314368193247480096153983168439832431186758727590895015840135090912884909976314345075310739333275393474832185159178744012745418815513929943818524357311320511042551329945977862992921409608233512249826102059627917274495946522697454404
def BK_34 : ℕ := 9691800585241985523840258155243454062611452090246809731360455007901263509146182704880517946304802535614355259329657392681698811956856917517123178785016667715625637998824040017318168138038630800438452794217050774487014981879981231620794433490182198754258433854171349610007100288545220894087927184655535621817203843921410675239640131732884442280588011060648239668041337737630603773172258932807562899004227993907194279902683141599566596772519609128176012486822599116338503216075590961057722148367148472787530745299483539372621529133336049265339717266099449419342707473728572437794555287566439859353204327233838184924477840976859852720987835021704780608902504846124478724024539136507514436000436491976254762260275673447613644079590801847456032604492135380479526482202732769659728690051852943242547628058283131268249252933767242039116522857004967458410746301020107392412161767561083111441148122242655396754755792010060962017930513896610114873730216629441296491936121541340254663745449135960085953398039210609351212869833984293253527864551619867465685890145144471880660261466778985156528726182260199740904615255019123322409350650064255015387736205303705504110903773289839795861971419646339500408401516112998745057007975654227972
def BK_35 : ℕ := 40551355595546407520033164994722986295525532521862536552723995842302756740835003702354499289803107905716304441698798865118717994900073297419213656559352405785760831940574387357465481550669406959648519116472439924082518939703636914041720624999236342607638205416367750371607767138599108421390962886131270067832062394958787716378995787775336404010826004670829309881631235036259879731807887346970695648164796868526811279946418093176573265196169549432216229935585647724183700489608581285487784393370547929298315416262580379613742574681285270585046109336419975271338257256847882352886468444652073748886314819936550744146916791544325131420742864834736902898447234688585291722514895974350900623161840198721623496294554173688509786359965548772693519937521393555879086760708918150510532108962096210544117571295347974259970126945854441017829489158611510393692031192684827518436343366788236688239211480141538266660360971743124858260429899729479438152812460310318846344011826820064606318542845411663405827538926002616276201603004886594241881324774472297492950555817211541258601322280633738744073586354677029878844924987359153436002099239055599856950472682036541426289168850765653383954520004651551096408552793533566606904317711014009060
def BK_36 : ℕ := 87426411851197455377752660413229895451874495298357687011265777638556601333669794321445447472258403975255299012496636284744848506608478321691807357332125237577508220255536299406938143974119430209083943974256608840121870252849010075951166003786942882159710460903659422722678032258615814057882718140262015201571125719844087200980279062295326273355215353791490866562949454719000760840963463320938317226270439916739890038088338749687701428016202740889918522044561009888591132095950500806174682496747837070437361281755663238418145775390572110217612597635899430953523754841722247304506591756244530223623755783485489866882030994410223579420161601400521874560345990292277028308245145134907474157058304991984724895993576476600156129353070213680270330306719911634028121952022159609166494981696867705399774582058863520171545640540681201666649873705931648427024785595693856365241414822371096964844771593960876139808280565836651405006709149895326184327448755965702968434312500060469561318805949265948976270463430551253020160851680271992358080078490853362066841721961798388858708138638714347235357072507557084110599173066621628726181970135240826664029389204337152990738113490326303550265775668642284762883243282954578661273969461347019140
def BK_37 : ℕ := 4457867850222079582806545880382290509926955019341227793580726226579907908850797361449288880753426873798595881195888175609683747897976795917447843075976417520720760827016090117395996319531686508874668476337536418884653571285378734186523876952768516346278495678398912526985666798379450874898438758627567821055989768245509759567355692259047566199886068765804368510969865290618916021086033876370247988883618933668243455404850794220236400394465847197859419295415710288200727954474418453169660054112668609697852690575065431741165751511319640019576310116950086257952268224418732028171486411746786525538636536009029
def BK_38 : ℕ := 6437917061248180748405524647393266928115618551091489613424218440543861040427269856194678259534075582218489883162926474480251013782582251085410163425099265837838250168119168988725021999773999255286492071299520204824198972899547373499030522650715626343906772599073460024456423885477780683775957708777711910011686342931566593580010819115541229456934094373784503699599179813576888423639421590826326484856563736335948732626811408237952412979138702673160659062753617827163377120945880694559935221234417940999084274777418160280281631555740047706868132834358544718626931957881486025292212943386315649466575352914341
def BK_39 : ℕ := 46689590187940817399377229703153533797928168610860912897843856525585215587880176493358040475374114711916857340651978098245490086518022614408365947121800970485394455891337130398243787643332710523045147547024783919348648304682343671642843920835713245693088213979524412370407997673346773910573672738502
def BK_40 : ℕ := 57790258462184745780898235909882038361922694545564262523654639187509918967676563735763165461467036709325156331229648338044111905970198898986425542541064141522943125404931978259026505201161665082483601202541659010330551574713749179812633596976553420529717730078270580190018605796862775963091181230278
def BK_41 : ℕ := 68097761398089307129373500099339023689820545355676025338316064640732065377479457366354732963170807033352473227179065195564140509337143653357715077222835867940484355266830873146718507656413248925546110939835359652169682483027112415399016078360428478544424058639045116410036334259086703173401838785446
def BK_42 : ℕ := 5682090708999071661468084801577821833022879263866337895422613325813419571838497157816141095309713291074875864340422843884465138805622145154323047
def BK_43 : ℕ := 6246055760451715113449976852312456406217601918125317693753043447830642775596498576445996247876538162608903164776199083702163404939923126255120935
def BK_44 : ℕ := 56604619401136750519546625194888862821054832070971738033761713804008
def BK_45 : ℕ := 59206613656531034677779741652051317771523236593910574451108226978760
def BK_46 : ℕ := 60531825532793489514322269015706418703248494126786829845678757046536
def BK_47 : ℕ := 60589530878916452464333677342096333694630523969926020686403914235304
def BK_48 : ℕ := 59189577100481298007012705053848919959206343144512367919633305035848
def BK_49 : ℕ := 56668353778228688437789021145932846131384753962499056669408779379496
def BK_50 : ℕ := 53204813148435065766402217970866158707641840364124588811087148072072
def BK_51 : ℕ := 5714265335780917233965727521329904835361580800815613170109110225252086010212634655257073195428114980634080201474637582351043897663819199467332935
def BK_52 : ℕ := 5149307434265428983330258669010062293415152955502243873991410992752615945317218532273149056571818623308726491325177669201167205861223107448358791
def BK_53 : ℕ := 4538139940967347154491973692006150476962171056707660049875556759714012923366868381545102366222041625534529052839353025991470375532634302033875335
def BK_54 : ℕ := 52519857612804124426869784904347997761388206606625897056263570066627197536142027655730515615192499722708944347971112468508930362959452224584055736162254297338052205557659242474423715958634161732184085193899157022170760253433124564191848184133647250561057775823379014468684812251166780781563095895910
def BK_55 : ℕ := 43951566409501895916643059671815000533599835676501047179442879414184579314343563035318010198938059948354808053698568931586249552200233659434841652145840826308656801331187537983524127856567385815355725610184110652453005896383327614090184028359130556867003573140413516746051126992882604126654021333958
def BK_56 : ℕ := 35639107318582367820007505922475428829800727488953858506758771851435406187041900453699470354542284401140389594058768009052306069413219080803062904967604558700656282451405255044662308198549318397665109038107699601287597789267175562487061425274604845596551123227930039572759798439712204689799720348230
def BK_57 : ℕ := 27830999256946633589118341877115971369240352656041458943681623165204908106478323638941946545681257180927386548572977436848080008039039706092350177549454790714359851627449236181666763300086114939763718011570112782478927644149897078553517873736664171141005567316767440105503848092164612922653902672294
def BK_58 : ℕ := 3734172425638496467099108273900577551292504744556841053921751526681030710361314381698584502994956279057064244625924669748544247297806196066506535328205010910239151950831916169466165144636341771776420522503170926647309612767204516190827138982745589086361043849679451280843773838772029249121605515113379869311796698039938992570533736083193520608290853019219846724475593903162604478821736586734489570154330200304164941381921913238310702110600112075983887564279576662807439697535758876536700336683168349716664455472101819112813995671857361295577109254444841430032624847301720828229948450578724609560068378848901
def BK_59 : ℕ := 2618356563678932497237533969791211076156055023786400842065831003291745361780368422611916545481845055380437671637668297125670081748492458391276057368178969866331978442757202631955766018463729703399267965052138816861019735426955966386395590487096653622135473526120971503405979592908281795169778216767247490025055714250507805179719742834891226749821154307048878342067741564947492589769777348596932065738905244055219714222857801037704415957168181521067562129413361606902508501737891361367547989000784057055023152694031739333835558635981579412937210767801027731795729899506841849361913052511821776565369333703493
def BK_60 : ℕ := 1687157202386715579047571370195695473542699221747938584110681366991778795248770941512312368593785025639339583721344141690417656820544057390981066867361176392283792076021609846061835101474559279785148803248102195046240289998349448904920822268042288385697908092585980473861124196998057415671628333477771165778281508857079640135410320058312954331330735826970500828294938437830392594947215106779089433464487965999708559887187627388118629587550599420358613454848517691487463943864314437364506883693341254622640325649923441324576734797343606721622041838209035425945880681385481708147493597770914420876141761319301
def BK_61 : ℕ := 30917689671480455132002717603483296808516737742070358695012810189433810920042620900689825415395759687518141986509387423632517089752423535102483027356026930166379493545018727566636506257489065646957450648639139497079545191691246089554504226754278626306613642563702485893794105009974008511408983018389451400722754562568042120015563117321349251619484994444602893429587611027050875280423245181153652419204284416372139301849046882283958011904426787355038754050042383341005585710440009342683357201918126690398109261134878321259524280640666783280239918221393381965613338272286723631478377884956160545431955941390737284040571164740937859244064730444957887231144740204111423575807869292219895553394522661989851473691169161142656714086434393202853880141391869035218246536736778468930030479916744680497540767685308044972252559478436183122452780611250365917062162450766408547429447919318417954020844452746391304562134455422041052959801248228909297552355662244774935443585007453758742294860008064191410555427135507894542045370954875344476304187045195211982192768531381551314303515586955487521143936200023810097367029601393157506449909087687220877545565574519780552206992973260442142404785734435304775717392725962580673829640555975191940
def BK_62 : ℕ := 13996785648980381994526850740092308768132622077808665355790842755832108159580202488499959776007395825223087327219386734199635982703710317653518769605954103394758713274033678091416161981984657650425539428360293099604444576316172798932647708016137421581244449586820345539902463762146333214166918428961956296572713073914298735226228818766562524935646488782249332441912053108303356022265473982212314085754672475444044476350962721634702661580492349133023565647371673907442139841095025674491282690303139743281530209963400433442995344101993606590089210680802678398779829552141323937152019901446500807002005818946953098895546970809507292483901632629370328411734106693940346814018705112382283578451814117434234763776823595657771010118618618618057071783818961585838083713227271749871550088963518375821488295655690826938344666971710172047636634912270611904235711743447453007944406981570095466098592538513991281334733420972521328756565190183440709601287975434818473749917327564166418073077763815728435921310448443046227403038258023446347790108478589835321628132120357289198968341966730096745447669002203641282918010317459239896371257818008094742442957664571500604676354634269386419358586292715037234122614470028300514246347779368307716
def BK_63 : ℕ := 3785139301074523613390782113792604863656466179495647270695415778913639064524807617971414183886239420092968610296549059940938740910359679105086510372209507250832297125053794676360207629835899846896677819609411709942889610634008758574196741804097452525387827570872657672289316026469107388972405363361087807960391044742468845217574162747502952453353061191315019007798707772927677283774213803349138531183898977114075798164556000640293422612066627934737821052838875843169475074165335234314882911053259657124963472105669049078653749168108377143752722357628235581870224017231807149581317729822922613440953107310564708010936017302045037239679927088001954894257520859143717607884332366629063557852783245918466616801260279480550910295417689384477212638846660011638308876504649265887067733074871984938867079534673075542841264738633382446064415836110962456740476946316808986194090029631215889403243920634022433164079987118394674746555247088922468803388427817142488248092613342561671859924759958691624546405254099721958300946086681721403358634329433259349887838426286053583025722564455907763170727004564628868541621240242994705473257798475296633991437254541910700827551223582044579211107494311942753491848191533885002737693458601616292
def BK_64 : ℕ := 35522509940668610546324424825020707960303769221072921765289090408340319483723890186142668069934185366663616697696919245109445521102763115020026169405099481617759967466155662768431314670047730179009839032986897340738431599562186503428663006385213796658798367790443002107295161420314069103231859236032714683182758963552500451688418133774308090631661074445346324533984426214365754040480262835440740460134069135988786337467987314846976604411446583053090196941671899296369817791365239154211192627914422795394356450724421868344502621260687987927477859075844141589033716916483538152279519048094505162676520850762344439235885635178294336972842922338242010244245959944280053534872246077537686334156260162509431254961008353001829288031315332484357727545637609567986921087489758929514821155580082264915885346391272573268619091636560937819266623645911374025985356154849446597662394265410360876979129866894920316585873597222968939063900660618460349180315605207632940259576527588420136171415633809729720566080207132211584019477268244773409016674471851025131608896031495209082805007874586913300578808306460231103221583850589402686214880004401375684874385511988994148362945039098347463990889451109307349294221321724397828325507827602148
def BK_65 : ℕ := 2212398154900562532432067003611115583005943557368129643541268944967088070780331086866994108332897176505130044779798708922729138880875213586987226966763755310687796706450842867283334430294685109573949854529386332136365689665779103803814796858396525857604422091063653085429170724391205467645261101321852960956298007510084179702061103638021353470469165107344587074420973188163180320696938542548520772025681320151897938497244782848022427954127248059896124623753968478439753221946919380058597954614919098428372249546720667448055037269495574170926484015155000485331012583068705059314104921243014361407782842325991202097124976422344561919158571638624426412198220061498764979186548992742824871460759738153124355780075663134804999718266487266157501117357254539170703257954723240107486413427211520871814837279953867479264488799213214258234520836575167213909320939864684069302763191719843971867473933453928009409879362215456026980447763699256473950250327923332816214657909626153856284251334264063786671908151220147098292726855585992512167521098243138365025226022768770988420143846846395904753896423233982883237741299434089554598777622302182152366611591816011910716079411607408278290468229040391662429454196866544528640021809768431620
def BK_66 : ℕ := 9747860820147878860129502825314317143024142549655565980109236382017148416934113044146007576173270710525492031543625829631831042471688354500149807812331184817054566505915307646800857746915868472550127917119159451362775830735298961199430128457740283271678551214946163906100042290762792597392069467765418904170813933005962856332981513040007390433499185125219296667799730450472851105530679076812328422160486020146243857836436171282336848306145002682820729489959071143765958271233885051365509831821949480585644473503356332192210780568366818177945271294018648375502462299685686472592424130416300290724122885995143655160013061681167032549237991195910205117685672875130108125450642177345043580949635174941839593377224382545026784852524429280592672665628099444897597035371040157934349167475679511868226975727160036444901454118470198824902904260360790721467485735806665918529704413782957568663711090984797901205902237661953833976076235384877477438965871032602902592836478912617472535208289370259459211846817097150872861603755364300027035589167701253483426385909720430313816664768439608721923070654922183476804240157895727378020597046677078282563627470515212203197190286396751084564708320343610633770297303365665109029405291899871428
def BK_67 : ℕ := 21862801330069624396063672214062900687864931928949600752897849764404831096234077247737650362549649233090185945264932494735977408237176183974820342030509350291477739271973806909850805007740823487970644002201441538256115839910693956099973356151729124339571761326845456538599176208022454786825552481022892212983135514859412417202044959841056028647865362728972929356411634754256328688917582430538492230267333967795906689058680078480882863306981127425380230612803671832829303202746968584944264533973327491202345847510170990612966566752028280336275191247136439232318629132604250720700701454284088195870897538931730408396062791676163010079881713373340411137755122500083653638774012058885821401701187989518380165852445854170420581219307477279665755580007124008884488421122426575347826707064697182092845880572414078689396386281816453812612307436400388336800719567720105701425713153614337328517234573326499638825784530030886409443252179752463396063678365569648566472103964251141451873188764293018245842925111717712953376322879203009864196697891688176630228580168254738269383528536002002435769711157405242080467296144365059933772830820544771771543225184179882762752765631282442018871957334461477800401475450869391606620290174962977188
def BK_68 : ℕ := 37654757338672007248828868171067804732250955681120157519260248391863395934395150799039496468892572807837549617688215960848841192221237638088885912174346332327614126814023091361525763874795266141088214303971277608469367878581167310175619447584042272846448212175800676282075795981127302461121351013043283435080224973939368128584354392507296181435094514960986761221795902514444043982893781541094316548442546533125813327072499393703420126740073837391717273065751983077170203646852594856360688782001715755706581775184367298461325776682286233491450057080874793901491339795847943854450522407788172398421936483481431961646887723364807264733543819416006609325478112478723940996234294208785364687746710649143459066399135758337288812967400279104942027563769215332808912259327436480743310029889433452198022487393466330308843492076791357485435224056705160015439999394717560845698086818207277289710765904315479971405337946551568863174712682882238225738301262746449831235382192554888593234628460950752402350337816480879483567362107872326809906386134679178027151766113651335958844825339415671604677482334239242083651708145264308156387565163686789805092870668746148776735840200365076313595391942048064981571488708724428906720644095199400772
def BK_69 : ℕ := 1726418114545418571186508916396453817148722750470809673433168239859878459624361423467403940481299895604228756064271397620901723722038134593740179637542648762478581908116190831132577342233251481898797092483770395890403410497762267541092584049141792703741192696955281388398239845611062478728273174234826724741154883659804734798590491016813476812762205739450238100871669463657609671748590045107136920052857776717127004348617390789063071978592606673259207823947570070170186506902955242231686965166698046043845997376114605018855654139220186726310877307656281114075007617258095868823415703933313131459393341358757
def BK_70 : ℕ := 2349857847415095138331959401154502433235243999340985008889201237447797117060550829143863241850994994762164273965131556210109592351012102305797508005979054865309873201008189133632123455295564584230052462576699937332624196185261715873081118104300578102739957243538847361805228258516651547006011934153869151189134710402190360935315304473085116142282596427399677224361766665898181377188846157155804463444113544704268653335887661979977798421998953822222128010695901148198635303959793623160930720237493670095092029125099700406282468830213106202252266673446292021918918959247044388672105055141748971256339908062661
def BK_71 : ℕ := 16518573261208058072570150609536901771256025041799770693032485103127564628817664870809120939989501556138284848918172717581905156803888691887072821865312861236656095760136540856989657626387946527922587568996218383304051674140593233941633047960075069622007647021403335365616310928627501487682330835398
def BK_72 : ℕ := 20058960395462418876833983895762279959185394787169464464844051486808292278226702141740612494187182475893358140240490806727119275745418206899723589732764625847368617657138956274231333823580878909497363895433981209714169850618563096941686979699431472161062934257212703835572978805657515410844027389158
def BK_73 : ℕ := 23404114118744731082533030755517205016877665599110689858314638107760621197011953537885931942889180002424845182886045224668229659257054018770135332448446818809477909874072312119093735551539541979460597121747432743935315106459212646295750199575820397468902587527213662146844645451306447669471433860134
def BK_74 : ℕ := 1950510978015739764466881950392916649803758637324251166526822203814308336661336593706786292199438713972337466811520927976532454966097785181401927
def BK_75 : ℕ := 2143444514345609850994595089354651143240098164239146059177381083905633318055573312073788651557260923802245589337412801816835866422571606572742727
def BK_76 : ℕ := 19559342150567766518844284009064693109062774472908412573408688852456
def BK_77 : ℕ := 20538345251080060463620597388195259373418353099354718426064891634792
def BK_78 : ℕ := 21107492375557786792633025438882693698382259702657356319725876873416
def BK_79 : ℕ := 21255337505175281329889984190295593897866788059716551087793482728040
def BK_80 : ℕ := 20899209502691380895677521585451390632749270473654390970968406436360
def BK_81 : ℕ := 20141778251039166899845068435137308357110949731802593924118858560360
def BK_82 : ℕ := 19034185959565134169458115446882026801927500465965077169088508037896
def BK_83 : ℕ := 2051044030898749228421331501494464684180914865242070340154882859430724069348510451518154877171244911679331242653376126391250283910454383444381639
def BK_84 : ℕ := 1858947231310260392512763378140964252308538449406286269462493403708831570123108797298456342505903955537742946852682873213065139390472272642936263
def BK_85 : ℕ := 1646423588797574724941835029930924308496080630044825808450051333035501302488259837520694325807956671337534413670321260660362441628744194126510023
def BK_86 : ℕ := 19103435007242771493040186008809413596175668194145750325736097206415656049700010707007264989475875154246474798470140185524966227160649176046875206228020198522938336799913887388580213567629157769170023769681097464237287735770131147688409768486534432370299006150569167269033866096855910590349265294342
def BK_87 : ℕ := 16023846548212687166661491339782355558197270703512314760795655191202416111097233252177241160173444914989432583529797202135415972464507959354361656682772936211808655714410633854769176513351029981550016080542045468770423702496509066011128479012854537972258471916220215011651356972422772662299678306630
def BK_88 : ℕ := 12995315426511443999747624416353166253570187603471955606793743650743003589895778285744832087522478608780887699786460813630867271966952153760074067566312990243063836082981993874963837536912297150806835648479195892673592361647160228683255817323662729267254481424057558738565011490103378650988594036742
def BK_89 : ℕ := 10118607877190449509406738640067448251369169922791233007789972627456074794648081991614545919188197778359958372634694057145679063125266808441383227850788800875057099640529586522540683048030946242929427349421310846541688781509683655458740762867415469926638207555097001400640379175124304297714035934918
def BK_90 : ℕ := 1346876547767542664629279440817069617281165503653101730183527779049038267405873146642306141701386088680236907755045620449732289951608629959952578685997582451070234901955227146183838149234432792454318074548350119832586734275718988501609230112496292732965424226578115313506821547426936480817220804272144978340610297582982429090356802372110462130767547558080295580232698567467259579748817280249150301436768013870445738663215823754273795585120939700419634130246796190093639679549379616676867682370842097123122699444447747190780564630064509872977457361238534107298178268180974842603474288310083520836329712847333
def BK_91 : ℕ := 930556060525474697505439950132836217108527714024126363474656463469563282530686087614120489535597981443420293610178100148373377676144043508464782601923208487549545682510059580092751717384075738538403900398395947357600171655659363131604852529994484768582225644694263646608034429199901004931726314130745975225876385355437709029474923783799528640609964925548123324375655812175031705343243727687284915423269783738368009847283652508653200180838721981999035628228520096973410213179102532957437691783374916767992619114927624488686928779072002593335455504112147040363549188970337871710791610972045007215357984307045
def BK_92 : ℕ := 583299110406445770599351279069899066749456326727390790992897328962963888635761083400511052060052853506829073415552865791639527716755183969869239322681813843787244204055632013828246028063999154308529837107925748530801905441235991592022401883777507431155894757440067272411088019941128419517968272328045041710180538954148605784275998710410376927863607456036199815054981957258574431198131491211584684949182772402365248463500974301813948256815941592534045348021360415746858384838587701850651259815346011752618394656776302629524165520855453192399376295912973172279802556941548520582656819003368543180475669703845
def BK_93 : ℕ := 10132252895034397392633527710545343078056830250214682508103178858893870410992147406444068846103928858040361149980111808351364247124586464775536497935029655803228625232099855737605766934770736953268462302802492851614397187815393515190788251436286191498270960960500527979773897474381570638715523064328449192684973500387449661076137966606357841239451064904532116844069712435187878387322773538400163811324947374652850959463738608909599840182123441871295804760639087784521046656626394701716531388580445008558678088497732691710886223157259602960560547589050162565616490178312726922881179668195570164350929306565986299445097772862131129159966531454033599882244874851015333756400660414691346839937364709244508056701175177160669436196576697802424758126932689009983388581156497152553919128317587778486098371610824238901097236228163042805227959663931444913871863881792620075554080038457110369766588375353143137220184078562800502605039946069295757619236446195265260213366887561921048777002000485152021025789473824484279694170017343242064476204331449897508826414147154199942986356499704697016649210148671408436724942193900946593844664381390593223132260339227168255006015985195432936357222316050550801210449284183986510944768763884126884
def BK_94 : ℕ := 4071401053643115517556334203481631790034206683622009573671398589700802786991105446338820157232522958486284659714772887923554495287805313446440504844307070347856263347600530141162761578026540701418479613442240137126647839457437306030626324466000635904621391925150308143413124929037172628027930154863426336073561336434102654932928074026731068888783363308532711752822223932740023052941638751598088944178366961534625305364274001029334577352266364485043802658961232466661662519260312355415473447470668716838812437099768027020310502935320819724202938300904236146025457669956468788650065446361690950837837113032819469462680770040952250190402916708533503562449401380783945242780454503111897275521928657962558763391097525540374811754499226811857234037176228149661260271741898274856045552434088924294127915308942921136942586707220593349915801125998101594656934256827534489816231922527752854192575559063435570632695401537823392181549036009842917839681995394838946809626563215239550802148724083515045180906743480780084421072340743481229339430789533224141649134431932188720802942290986411076068003929156053341662329088376881717896918495876882533606203108918138982274901286767387646751322162141773953981014268093436584575638880828082756
def BK_95 : ℕ := 735816173250437431936850772030042504624606862197774555220497478852679618651247927044545787771040296320979845562187541805531148139479522664258876934616811362482987777527618198358706861563452583008175891641483674099777829502000664693790932364118905245581954238532026726283025169254921087008350904010881325567230827915201015706031388511609630051049511071074873481499168647773129118180027977071679900214300180198404548962882474216426622052206816227294260351963793823985047286419202862244396678851305382433269913838614993490435705686489288462157203108907591016748706997487417664105504250632469102571090289165180161770991310833696946312326962478291694827282744271783459754397756303841752857152109651609754298634834352686335736234027793775954084557532455069131727395601027374914221501262268811219163785870348986334184477403519586475023636459441918000724895625037908734249082046693530873574696088737431379519960643618404019778358287191555019644717546846727621159924042679866898388811657976863860320255819769839377178505444883719361686438375426338979113466516826643706478435750302716784255663489498820622466075523386617401241134946846445454839674876760585042168190758171429315156970198809382919981404069649445473865729845020217252
def BK_96 : ℕ := 72077703643407036480330633287578836821627599115022631678995393367505405131688117736546534479882689763967131481622872921254673831758281962575244370765762888529196354195663391411539558861759653639327532497429673378855916748835257196840621441510651204055685086008726360790917810525902985958025394668636549057075153205827234006621211358360896836304257834723144898544108786598826221552387568066366545206047317808108922491519035789920578085910079206995984428496459951408022594301721256000038532029335751022083741406988314896597631768388608820112893578831693124617492168433735204568430724739090667198128727814076347496831884382296266291929748960729559225503988006049958455011468578038510191447621578165699374032527375454383854884345362185005221010713433600003375588685707938680984775909403580356669390555172656046467732416508055533346752321074361216891482336728381995562704203931445732582593124424283907440617419187854738840043798435818859513118114220947471572601044272456882657577562355859768246406733325813930646918938537312815790561298029093655207807197678209643921737323051443419308096608564727120354718466662287710143738209368574615456266731516868798916242221213266343693639229874325153269548473915523881081085946090225668
def BK_97 : ℕ := 1920907761351365362161200776520452691425755734337867280310218183046008068343314586154311406938785300567058690108003674939312098337722202820849766572512315369904048529801297285547929703685001110870562150800965997341350470068486211149329395157226841289870883345112604361819423095636100464291221537549208970089549196050109368441858754358426602899837210368367253660796798578316309255347969667672573096527574101678367424743662201339504412889902276033899238453089288703752072926203904494022031026034068019862811652538594732319030532528846380587290051287666203677613665130351446023746621566500990460822978987971355187928843816732529853352090918075562767554762735264644106410700539789173233865714920970145397171390531502152742952181132955987774706525564616836779788135418926924917120971025038612721142749460899970263390266954428168446925331294826358023612568711859023014032285313582808130004609568799730078995781205748071108400777950890077570476090517177068238815382539554228905165557437972932610212425395328599423069414152520642941272250791928753960015129093753218447188125719399157855182349786515803067848742008174679407547391415409725372994942000078772705199698419968115627805858918940993359304119287503467960430176725938606596
def BK_98 : ℕ := 6085717779491730157924651426398317721510096984921803336948046416822120185604718561122197078999970022599650564372041374955170641884357427640420763142786180972920785045314746884340680177036761687130674479682633537255146874715607069355519063030454432315928962878743166138192547272483747987704134702088689357733939805080056057626523935008005985938755906309631362965045821286339119523890328638117249243768553004267233455458752365370452871163914782593610872188246096382320813791928948934963745319416808704319797863956011328051190894206016105927068381602383733549342938725190378410903800392998849009387637119369345166173262515300551863454206775880106743448119510003964713186791758338160800998614950622865183218373686524499885529628380948450016950396832098956885418608039132274346934566408422123387798234820347813151691550396498376152546695849612335960600170718168870172068069470395931891576078515496592613006516041455598308847993674047976088695627556558878271527550914692000797143467136225100136529230461644564209941059903339381726367448658618838145493818436601001121004078026076028989182681192432002897886621278876370852550525489379971541504682794501106090712483756472696344229526107263903073066872472645855592851616019602645540
def BK_99 : ℕ := 12263183170857626332162174257792088632650215179853581278809486913873005656906226480920967533986602497570173705667387561277843820239441531808584882566904950567962756127399311266151934024225261252266896510325701654350122878757847877150377912301415371745574426971080204253916505089314203282192699215123939920887733864988095507180798292566998951425550501316485781779877850644192492446833178106147508363344272843742304111819479567344859250017062403457289191601750720831400730739069900302504628955043799838882493526241696286774150283699687474598061064980964294927471542342936999349428814635687191203050253761458079971436882487157318471528183255215557695938830518251365048168868563523377133769917614507362749789193991993577216384123562241421050268842667318942197354963491684022475537782392825351719664999793267556996180592536874870813762654440175506900028842192212811342094857955073950654957555741421282297340497542526696408648279661333980728554077316809294870759459321619714610708308428299517327527948032070876202288521964089852763616142602964097653169035002017996905234451716306513614735417585155172514382954792675571956908464964265953907212324864672724158459198908324632203494400552495179893061962445683578190367527527637729348
def BK_100 : ℕ := 617105616912649276399926586767885845870550882819861992446842355273247623723305253518480189155079959946632814165184896501322692704140004686446120449692922583729976736506736626074539746847917222832330900700297265210276072829190496028447604443176133562036215878901331166140935306737276326550437515342979673514420756063517382964410983870628884932001098548163302038328157893474547381278858890843750932439117103925720579512224596861813707240613867825793784246733210928103988540673806548792745761395924139596602593106882317646426773995573541640949416875842355204439208258434161672673100590077847121526818326497669
def BK_101 : ℕ := 896856630652180034409245795921637678856638454152952350818113844817244650291527318064575156258732503907533756959743404501286007914820222627672195020175107128974923579870126707057949575206050155608938334232402924443160968198741315760655916746804504121324954168786291004139964811294625821915686081649775070168609793762474128472301021720666882373386310263636916365147386880447911663193582685519920459714303812203685878028867490652709088533536687307844572673150027635124554713975189862489632852025713303712601397844062836798583454563266564501983184680031732243003518358222436673122834475682517990621398811708261
def BK_102 : ℕ := 1201498142408550146646783218677398941593671986460408403832754047049335625063765659616102447255694838389816776658347734310061555014403990191516644735303644118240633746221989474496945305245666856518480586176038775982531080645049360889229359202351081022093280724137520160163070839288119606937123816354566885208114370242533050064377675464652849653650545779593622619294229510624577603038185810400186759717457359221181527995620931253960472989069552620110249555141721349241836851474027191239197512461345544434958740782375823608307917051043790191762472888077296281780766177317867881027626351940006600162713741276965
def BK_103 : ℕ := 8374012053449011209141817496545333826509977645877753703504340323511377580913116366782028969649402918604000702126261998796725974301515772238251247664306614620287239763550493545213987404376989452393224955077350538099121210163025002696712550108000383349089341428855848718218905727149763791597620235366
def BK_104 : ℕ := 10113714638015106582764899580867571229374274948110687402848485056209777386848939934274824131976304469041944076546732486357778742801783878668578507339830228706164970416665615593968364367678877861322131716938855422479009555079074312314419751636411462180715797660728804879964099685745931133519776693190
def BK_105 : ℕ := 11767490995785926495371238054493246287953756234543492700353652184417608622421869702235788092944095383090345621760038623908376166202411365036106242144189769198014925384805254797526201897761912906082628378903342230432175243799835534246055476117357522941517171535503562785330021378052665572338639734886
def BK_106 : ℕ := 980745028602388957498774113949902814822685412722848628101754905392911044013940867973394375519645738819861067417416846418116588348489838308622055
def BK_107 : ℕ := 1077901549272682604018333520099862794476944139987774720693430401395182179164039769850112045566641572547288082409244609201444953240342872702550375
def BK_108 : ℕ := 9863643631477785788139181647430136332573634123088201669252369815880
def BK_109 : ℕ := 10373073121726004202797565862621603241068496207821789351216121823080
def BK_110 : ℕ := 10681376639370681203955223209088749189138706216461932013442856247336
def BK_111 : ℕ := 10780255956348845597823936169896265021150702111278609879568192447880
def BK_112 : ℕ := 10624910845182120419794726548142164182310465463444754447738503150152
def BK_113 : ℕ := 10264512806560713535834634230043670101565170407933572826085488829960
def BK_114 : ℕ := 9722716771973283273564910319519600717127983309853957306756696808840
def BK_115 : ℕ := 1048550406053618728809641660146066788631590136621132481234485521681980701944785809278422908587916193968447275034289060198872623752195998610135399
def BK_116 : ℕ := 952171474895775652509087796503378977824965178697478099212537880578590418089406540448107563199268682712068266359071069879800087059366372091185159
def BK_117 : ℕ := 844583550923449667579320331750289362001062933236631851441232746047078737493937227189770811805722305750047607893448511943823160992726026811516455
def BK_118 : ℕ := 729886865119665507241085897518644663367581817128736112539784651557961255944601291278554881021634846513461839686436541483724683287788617232730023
def BK_119 : ℕ := 8223657918544184723216247176623516357093777449411493429210448761697225438437098782290119702720960294300817278230147430370535830742662898824588239593518044428207635724916692508641352119293065385426817192077118076749838498225113660155436908134381937627187965242249225453775189524126749173965801668358
def BK_120 : ℕ := 6662500089610211166391312727905138707508421820622897105772028947066850296735967308400085509228779614854443844872393386355239503303668098782826118815162592004787677968103503877572388589150378720674588765322576537220737844831092077066917633412335423266718879763233133675134145585761852833889630804582
def BK_121 : ℕ := 5173557064542077914875996428484243408453328975845314860414916599269924923810973941569803041748111595846059913071367049217007828824547057437351496471259714683336424515296430436318327798574401002778960291436271513816827819370689455183468405232197868862340071348506786959503970566178334904996474423270
def BK_122 : ℕ := 684833667250826137474041341002898530146837738155065656976218572581912070567576301956269503014198901779890857847558476964587538608999873797574209366007785972742341371566006934010894969455288807481283701014594784344463407214077241203323095104744338985007852031595126717707725360536927341493938563688791884259866508925903932697007728219162631373446822050818455778041144232552983747950087033957791547688671199144479401211909018445913779609332020145684255721565018278990956302139608600565472748195265393512167528863429884439564647489386877212098380203962293964364289039417403475077285669728503658906883680159077
def BK_123 : ℕ := 468655177097007971392172571983158860999819784600629002387141579913518434061328175315268150239969464167923614479783626550835533665199084655145696141306436843412364056593318306077087685351164397627110232060021695298911905811036297698366581964920632815766020682094064745863332844198268885572363044702897159337472887369818372732519402141375220855107130946413482134355670359194367503142854290789466043141930822253551517252993668787074783986177800238014078671791265108996284363607546592965764899677038350025762995696534828871041134991802944994192757017988925496527101404302339266341779780852447570267263833597381
def BK_124 : ℕ := 288736369777065913222618824612339379103566031174593560847867168129633372989813235453042718031006039640526234503534315300535379432447643279556877649971776946548139311828493605556301817482738990690958698221203907356459106067675406976683145973847584438827771306227967822805091412777519923332005180064230194960605243507422562833252888525013315861934737448316564007979642435115924916665953386856775058826091465770825614689438113411341086155676514852389495065460022282565528420649824576506763453838441884686519566471550298320944937164140480979972157851438169534408395420096635228859200399954213731379424684857029
def BK_125 : ℕ := 4848963015325503114693722725319306783923409155376730272354141916605716418108930549944175372763511494574747210600310737505249641113622659586562553400445942384588864451196337035757198004163355341360982235618029002615421762947812716544723505763688663363486243507544659814391216495736292031029646047154917674263060074237874762196801709906627696139665371025282573855319581247054036262692349774585614805647003490411140126200028760283344029890579809287776469507906999645422799913002878892219673152680139450791430681151055389501751937625523578735141726628168922261908565689504532447579049858600311046161719983093535773456037143167645161223986956065426734967346196309787416421006011249964039055723336966126076950278554720285602739017126183140745244782674237102898513882963972934199779182499618882280851369124962789539736425940599833964860631679507121832023960704303157799220934867129574795309888145717091916243939111547494074487527247169955497586688833719052575995143693705918647911344965929596199349755341921399609269689674865448029891962538915246653035571231778965856330438019805830201244639652479620886258791932242580862053661095406299472056439528779718407461304524653761280576440809923585225356319350486256423308244121546316324
def BK_126 : ℕ := 1798936937860670046784052055205968271824264416108724135328510324313568757304240061779473617484979359384932654244428899363313192258481613990536343060949429340535648901372154376386479973932097364732952848953399156004274525965057659484515152735354278896921171419565210912456085357798069856392656233533722072346142229088899666967975101210874153011704053676446751397128691812490359919899434505025853573022585755619910936586283090843077321650467358470499727478619933887726770596025379833235411629959173798699825387900156783569686848119632310865587559749617390975061111124216154468603980500347252480174769014853184646251079977055714823283931375127345031625537516549484833670088068846637085275607038354258656822365542470324730468973345427800376643123777220951457250076834746233769742937463270823259764612798542979691522362967880439911114815474090829618719144519515383366651728720441035564529560128440511624444714382850326019589803981404393816889425270944295770994925393116849231102225912887137527050592830384270943264105855645674467473758904997284146210056881096620757193071011984974460125861204314872396858660323964627364278504649610071060584403668717125130673435354373435101165920271225390649611133261247450899698655568578532772
def BK_127 : ℕ := 231524077629014522928646696828823125304179369690030656698863165573000335190399284429333242968830084923813261808832124368820721082041079635253196098592892353823801779961075701559147328930906318602884892407432834421670628679432727773143481402232555178731716346678403519741939341485176385448515967991558818770102002570530731676844507283129157612189132562349354178910805144975755995274047645598011897614199667613641403940899923218377102935093964404302352267105363861211200859559753937452908789282023176506235102247763177207715787004868264376145903902000684238809279862074938234031879127273401557051579810634318829313751036867702286967034355392575332512249271287800270285147539613183243964024495230038777330956543633199980481252312960355737071926511987514200362858414662757563382570875974186437907698206328382845820330290019620533489232200478527403529454329779384244686612793834490604527079676359792174858934383757577357935455084839780231616837586767536475090982305751636130266963248267939213418646840285480847108259613740462049993920636736275601671228542221910940884877942937338951846331366316464810456453801486851628847338413027146516406651508884360222807631677870562096315343634960636111653916955086761946802742187045840388
def BK_128 : ℕ := 3653892301793918276197256377734170719890507594054910165968609219231034877464639744623294390276374572200698245102106667806465859103761066157259225963809527867257231996253798274077841569016068730333137665204224377212361090026438490451088420601224111953451436959221660032361101872421916252487751739651451261571951016247620829571161588141533750713375713784674052468733299985497658011944340667799002169218209006538591694720257969664643681010039599671085222305761143447354741901946672311091563730907534986106319416576104207181661667346279270953965080422639005280103220297900478045275199795864503779400511127557
def BK_129 : ℕ := 1419773504001082901415712411122237052976907463065142753223033681662807624721178219181988527753730292031151347151747964221994341360329998280516865149202876215183424738076511889615630755767937736737379521902500756691071644081786939264162461118072186509353476398009744932579875901984680735308502049609067978946079550007689533367846053037560074953030397136528321007587343274813565898335354723293505297305911344453127256302347717482457277901365209287512481095007700022306946794910188792233566993203859970081398395807606139127057220770600756612441205986690510328238964394581099049406963687786873547182728303106810212532678391336270252313494962908506184272452803704082461314615619685737428341323370308908101628167600086275127840041102689686105314521183373642361478609319975925863370029389500786056956367664399848763589177214867783114008918219122534210173179216820048735451900992739660489918721456642536767139520019348108122977612828222810529733177828108892339317098266301437537173576368212848001101710923225580502436719874720553181491498306562310542825308392839543785344006659228773246903562157696074421169981197455483587532833455847689646207584846534028383551106235646068828218595341453585531018069324161362582236423817114479236
def BK_130 : ℕ := 4007086595497725300859781000030520544611762309227511679909512993987773944329255651708426470748951410909896615242412993316612526016123937898994844537626768131713527171259900186417115886000882855996078586546335835948570437132162211233579905497567888117232309017026917609555026985887268755937716153072451434022760232014733088835438044955070214305127083980958422294288135236511996858957798615333209080956696878596343368231096417001646001178177523288434493049601820485135226392688787672899122699119880335384899333147410716355413542404792881356273431324395141334396895906176436695974650835862540896815282920175715694598271170567416696974655011595999881927702547389624844152334846399742906505289451070206768412391971627112092542758178384442833863118497393389248191732861541028020703165517883276670581571135148795144761177366691787985629934310377943470992944735967810025591861232181099067617074157809244943741132800605449184776702068629934858872976446435472578022783946100766351446307649679301033708732259117026958485345211567333465672292151858112778761155457333856991299013189888555776453717871166386145295396313366403000102652952894487945117828507351368081452459374829003688257129743779287103589013307682201572582618746765898852
def BK_131 : ℕ := 7729860855506726829292175228339239564923080805629293774874398010315897008161203427354600004852962873932986689259800307695413293169630178697915266422927934492165906837302295130985128007751147932127254582953219133990588742222041695810437559137539424983450976669357141998161911589850613953225487039775031863755643311395828361253968655199722847755241347775455922267668139023644332820908703234181726109585255310918486249609329824846249136565246945104884017389347421313301357714272059368812660508862537396013089248354737962943737835399479762369143706261882957400611677260323270291061731571175579378182293560898936871757561595620189794806137055956082132001997517108850788438178244293713871857581337456553208995900611359681453349073775432250281972416627208835794867238732744184885796962054806597134338981449684347486181794340670076373296023693587236274645761972430745331027524981013239230447811912402746277596796672209100042353630362675566174854452630123094088894765158093414322374976349253074804662856792849094548420953545189246919314981143740187015195144853573671062888163247347666996714242370904401838399133616560158670734961380232875674651688567293062562820385615877254563339375304506970396436499692396640513872841490741684228
def BK_132 : ℕ := 380801259007467219379262188984439920124537125291334733443668271234453376114228633851439603361292110305771420108311924868512391171825402779952703609430793586139143113987548312007854814588929315449345941209727247755431862104856628968784494339906644977406552939873860044457107680670579788825628275597107551739647181795027044900978524723708070724314863033839032564414208098474709196635673044987153754516737294285825521063242337579179124981454543619884494142090569557373981548272258027719784050718405946791608433489320110439846605308125302831987871548911873134123433418724684929574288257323717104092360043929509
def BK_133 : ℕ := 546717356726913409266665049851839860356604385233210073584913490892359398991293536628371413783470615666097701263228326609148371935394839842932854609208985911861653111682365861410201705223641355285639976575275831981666162514880716463326151900970717292087113219587307571052452078946191120836621272770165475590044709507217156466116061050489404396080640567969385647270263405105815892157785179926059625459945007221074899380674899460693297339409997783363024221712972172170287054620791486151998110048571989833945900871006800512778877176823653900542407107192400160095410791265445938551470468635260898804279071950693
def BK_134 : ℕ := 4009252122813141990454365935376520919402601450429792840275579506853077685329324855794226648658346554152913898536048740534129392247146583259145762294612717900000144006054479816543479703213477403013316835693461428373781212217550413008927366936372889680662810143705498532545931178159774972263377722630
def BK_135 : ℕ := 5048797086727871046597245360822923959140571760868096348566939426776499510163072056831825976841981998534712227710707171202072500300278925036810369809961110843201522920637050850380305304092869125173227113920490250447042766197728210754215366717571848055695045419864001951264732431354689260249164690214
def BK_136 : ℕ := 6082787377580465768436938098847389028267674775805283531687004568063314406709429785353983486874673942625552199989998670091596963928279818770425497222128193227923970699306643150837727572452484737107716934705097547598041726625042953850362191665608535978870779434903032605211053926580005012737079334278
def BK_137 : ℕ := 7068849122639265584050135495078394878807031836185090059694913469400298069012805356539703892373910034113243284041992644008019306386625093301908236948427145032950651524933839256077633544139663354586278318234392261651411661899492648678504008820748570139610936628654990849940123736125054569504625362566
def BK_138 : ℕ := 589247781780356665631516404279260401066746536750611963697676921336566274245471367048571424063464195988101207098278150886841978956568801185131111
def BK_139 : ℕ := 647735761284897697516101574822254392422838952166410675304266409584060989646015891397593785266261542048293347811009059274102676788580637637807783
def BK_140 : ℕ := 5936551994318840313806900503856879386867927736084106857837231538888
def BK_141 : ℕ := 6248454852310880291964068158403014579252423636711672888820076281480
def BK_142 : ℕ := 6440986317657862588503984636234400019087403470263317011323507055976
def BK_143 : ℕ := 6508367640283744744977680452403832259271606275649313637836170128552
def BK_144 : ℕ := 6422649547646973590488548473328895956630422032730956355908547680424
def BK_145 : ℕ := 6212592414264668298870403456610960842037676900005965969455711123912
def BK_146 : ℕ := 5891740920049368473913369449417838614341352099350258540522931095400
def BK_147 : ℕ := 635603834476026678876613469168255583213128735881207259527170543356044742372823194811136325248452279507791688436978525239037019889415983927883335
def BK_148 : ℕ := 577718444977568953994415499830810934851882077813159105539085669563504352099422763323371998959403276031951989118020567886737407932793302808543431
def BK_149 : ℕ := 512785138771008102388983814715849784887802613161222009686083974772572057493699278530555784447974915906878858836894954702828633986751073878873511
def BK_150 : ℕ := 443284261725640227890237664724666911812346066082356632722427059221562315056527038345763425625730689814456508171327909745258732300583870664410887
def BK_151 : ℕ := 4991802124504443634366765362740128665732578066039441582408404919525937650283311224053307166397367472686018957745076470581581611398717677257525092207927925976590241688983154409622303654763848923843071995236199488240183054091528609176016772023485923764668698697759942581552659885099742930741850796646
def BK_152 : ℕ := 4040455214988265342542813482513153120627777279664451693298402624616111123544706056037052053143135989570981134056806184382732593373904062573478670164977652580283352729131574690867082682966564954637447179580700189207575703349232861812515251565347924151198949098494161104202146305357049919960547483270
def BK_153 : ℕ := 3131239247015503792186011961654949081929871544381856411839790527315832863348068445256148672433877354889337700094051203635599211696011027373663103515068256085074915677709886189218420723851342323799024602963331201849679096325110909238689077891319957909735278271516406060651281373555867653333529838118
def BK_154 : ℕ := 412911749995974324235220166648389538274007360918307716114637542449879571511481733860482589260477300627151749358794638478896566541770759225953224014787408182805402026677190914602306984908670417162593373187869774971514868711717075690500606391184591206418891680481356333369593521099475775018845983143733578738111944793115740687490682753728024841408507358428912579248941506060950854800791827916350927586228025284162820429771521223135188041773768383825187081626885182079454633378161982911491414639681542514537482453591578216928509840565373172060416979097581053412315950934309894036276747510326044443958502515205
def BK_155 : ℕ := 280757814480945250085663787366039093271291571132949026349900433162791065883791899453095880355255418241466774475271880287632230954855995125969355015641227300034973488974607680950954582969775036845129261118241329906201858727389111870839161884633281206063891124180815720963555080241937315282670374891173281374248903062294110067130442606889097697104185678419448730693225062830342061341164742380981827931644168085211576287934058185704137787391787226560605013354305124713258944457455312796337346722833643345678203432811092222825963317353343976117015229622742181500141383859080400267210109639511892592789086361829
def BK_156 : ℕ := 170981271376195147483861843651637432394394899618502462289755173177152235572814793813109439537264462529975905852160349450301006102327072644493496660560124106285259128100229258967376063396165764782052547927455125993142843963833450216998189192859244160291522391334261831780101809606786724327223348066457790681475332391301154557363239068262802652749661244787878084550490625149031600117599497844198311922263923566885332186317992262774542528023221456255248662647351898198730309415996910115926831675533730110937097583026387466769732948428678623871695804196641586585915232827312827527568057171247393159289628604133
def BK_157 : ℕ := 2806269226490376038062850128668838599281949202191578971607090462020290888335361334856471956037380530508769625350208029493298166532248578773479013384642690437543860578276708246949750125387021475144256412714721794232618672163163478755929874715639346225486631038169977180991943323231819014989707933567825923209369993803606625146797981249002899041410084363681005468951044089215142525005370567321976305727325302249183583231297535134385863200256966604536836553532850654460350712371415328127786691440801902393498243808226931114304775991425946670501712447806456280385468463102544884182372395478262387591636257205525053905735017164927094343008911072907350274625188283273256834894428141237280319606124215494399009745441878321075812559724736789867477123400022348626247589566835451264501463465903690223917208631547497270330614669604857039008171293779561120520451010182963186514325688514131092402603409664509685984493671546008993705790149117787471680584142584164727155101396726257694842780785411806237272308612653136684209032803660049322777445069923208990841928344163862949293285660571150054660263202633970946553534738595663243117418853572360088781233250137183491775766145845194931392497832301198976241202127233782259166646863452721796
def BK_158 : ℕ := 983736370369181114490626449598446858051399437520412250535671317689597109910905794838108165332134163616540074495362172563101929352779537883297713539028360940663588750447107748002557493597033709283024753493559279529102200053150315956381892707377197566803487769714950355953269565799391629335425529222456160595402193732686990762037347261962462401212579698228460348360345826611093105346634713013829083824372088481125530078824177971265434866508555169309307522144454661910850337671352625595389908987062372302139142467899831332039369876887569200749044036507740714802946050961461584424049812280438340085766080900923695294587021754796002792003724029445814297638274433028265531787944848496355968013623079592726983261295744819722932144305694554228725182002427144376935506151654744243142818558283701502710120430090365235075401307729094779158575617678745219138248320626063721550237713215327643608255377172520284413631122024329241491881712095762142378916994245562149225684224032003981584139652281487854470098743196128365723702209811084946378752685171970537488505535951675556738271381434404032710965491270324064539655860585030161856729880447574059346400056681953959321549152820387708740043519644796909799054555284673423742402341745795300
def BK_159 : ℕ := 94588398092000893072543958817371517547003007028028932183753490617429878516002811650477036121211244111129903015267738283835086030794430894734621370678620148874177350077648078648700836411198516628726489671228932559982968774085751288603113197218422125088198659410210684798816117216186553973099983152517360523335525809384551063182596721898295487098731707811416687563419230514992380187574275338371114241213836692639950064368557381033655350984573691798726765174447912620969010532245099312273439149408132415377801628619318465805948425622685697246572380640207842368207876423660506924496623386291007823891488191908278793539325093147350317482309445534180240231034716939780537664112648603867253427378866499297054005086237752490400047064965570210893830547314793204617379730584313877647530141687100050984294269837497817146548500180519797338983125074282650379296848293870891334043162981719192204272989994107205474969425031925632360604186025141112345372757116310454039603390839899986956116433863299122921509820242422229097664270584595947774435935901475918188286127541816258750707141724788307335418991795073479558006828514347646798859448604119692981467083479460920248468512495361565655137831848291280758237327688051931107048128306052644
def BK_160 : ℕ := 18611834589801719774823354577856990494559117744252730979634161904027587260958281706823695695328588919605298397850886546571369797667139049228842865907316687072984806861113474199583454722624699487703497433946532018635055234978617664393972063152424279124045685918343145062488562324529573788639035398
def BK_161 : ℕ := 1055707182176104070524460931956830954272053633096160118057243080838865576893309203005110947630130257100075255465087258596156087129198582840861586201161447678616336307515169067153317865111460841339319671305217742835397922411734819704344757301280643237452565728737924468234866461929741794801774166299906792602570278285990090757171761716784178040804719632375009451039283567234668245603241588839328571578348266675306186338937918577778361102669684280571568948481482446226487241176984864934111652283238101530765634077139095096167738394466299874235653753665453071386417893660995399627221056414333254970251031188995077754639994823724989986394361251948644393194237513303670536163446920434774653934326040143604306920523474806333078806747889887958840728892772240218149843478784763586322657704698619051551962436030202481427793850080468213716114428081810917098777954592053525434265226722276595590501359301241936780613867709281318718560988924498514686443689693678462956189615409070916599636382074254453711571087606443953524441430045727689443101552477355561745400278509311002164120881398044837226276364510431496276783840924865456742302091111828022186194370178138650487829660507629431562922849058888827021181739239549139790635109366177828
def BK_162 : ℕ := 2809600990424734102799356402956701676684642496028235047377596471414425329900728093643876567130547563645801793624673961492076017718385068902581172975269027663342769958917246743473271344669105376148272291889549683778172454224966142714633844567571408628441543003120437705353251793154057899094244587683934305698885624264557417622963703516304524810401735459961744123092427375715028651499366937224261191883215370305366578561064242886847876066349125530490134886414146807881592959917665813053656780884939386993092067542866534359348018428467010799596194806797503623182449544001235581202113672699617370637506596777712366678152691604805330343046954653233093479566453942567313439558967251134158072445291736631449889094085795766001031978683964466542536434842188927421888361923567524516422664569934898601120612518952812804084557454459699985139508133877174051010015121570099778452527935884087110911544400295860582808802951535301483643789599732021557547138613419506381256774944701498184726392465911036110064784283094263557644773555471663216866939031308500073682385228334435162777103319039284721514773268853795557911760271734168996690471468470675406740075761506933427368885705233243824176232580473804567956398987921888657212042745814860004
def BK_163 : ℕ := 5293609470474829315237181382017082563161792797547765134714862930358828621719080482163846659164185655842668359556922499206395993765758086456215184429597412607386482279240924897799886246996946137501557975473149986530605806901814599626032078411095681561483099361063587544424390125802452402831848555352716559775347333718434113928071880444599989094296022318402300718183183980039487537075058063428855456697321064364835710001766770340438133069038659376960020835743040353105918632059366960292557012613209700284892904020167548207772514603902288094421098441381133237054756276748827813314099632874109619916325775699952583540771739495597555552544153475190527635992948873812943790677106776159371404033108334397688978032202236359779269214830270054935129291023974171248045317587955110387327700342818599777450116432426249199847876552395696552354600360193417404546360638779788121325311609722929477885537034951472477520611478851940864223257453542171469566809829679176383730470140177381305724805553068709633373884166978888707234018795636835913708986211288261918176041519666828746180008359801612922034373757186852922391419931784228684417381352114633814285129182276585603728588149495631393808340998148508305640675713919249581870355029409283812
def BK_164 : ℕ := 257731459132888879994431870745757238490925465373946882685603120328399779917289556134845179949985115908525449921543768478307656324831041234442092378273213432226136847356362564651561761236883846683621646524759610464669695083507195807626166618731354862577759449366233190422078062710047942341104978502597124912762479054709258193981141799577491191573260816142139225467736138019924229908741977497723740797550260995009201307132166734690540049907073213556634388118365948884918310332288592197470785888062071893054958042950090427359797309679013490749697042177427963297391346719788140049403215664082926714413108821541
def BK_165 : ℕ := 367500490054113473066580813408281004438196376804125016962722547976355893306961504793479352971392093081054065972991932335453171227360529803686020774588742232560766714673563895816131050277803145231031593823789802539393501825795994194606926507809090433262859574046881592943814722128563908471952185713504145055323394831661255887414728509144709913199978663126327558854632035330715575172545266522222761122344597012377614347040247118348669935378454010257234436885179828349462805585051276123309388058021425425116695711192265381328215492222549083263132713541612122442414632570238219580379458056118112100929935309509
def BK_166 : ℕ := 2684858335059709037594764089358631253304847924782061357587291832131919520182263348900141115765010913018600180938860105374357404269928846093247032178633229381352797098153924848394754195907799699092519942019705202198251878046034510872441167663888490296283795876623804644669881219651917836905959251590
def BK_167 : ℕ := 3372795176011773229277256910105065851938357044434550448293140687384703651019357549799214321536591259774906449045999233193407739424852359565839651058352802224792914063807885415513533751962633486699149601549490738277206347077181469644898973289987608653132525375569409511299321972758983264573607276518
def BK_168 : ℕ := 4057998963139744244965970360000373478124520166748897398120596504838318093685454994138506569963500657104826830275928923134964619302464958151375547221239285537156435744720110213753534659998382790094770568838122240801644484594121739429848558492055674887453605156515495764143487279413576261146000006566
def BK_169 : ℕ := 4712741549386791054806635295137386462264381547945380586321880138160636506227447408835036299026029026170495897072243122137900874172217676983520836793811080932292029148896677791890144961068344587730029448387076972756059112456357286007241774896447681394839327659168640040620919723664605289025256013606
def BK_170 : ℕ := 392914175305052358044112621661168888103949086404854966958930509941601753477128719717014641306260854690107206837125941149146921139693704767183239
def BK_171 : ℕ := 431981093868310054610833638414047046069622385071080922117169778776586651042464278151454510840757053475115973876818586584079075282589896717793863
def BK_172 : ℕ := 3963113362968592764129958721179464655989856816547969708110312796680
def BK_173 : ℕ := 4173621443350870763657722907833761036604665926729452432643534807464
def BK_174 : ℕ := 4305110755795741942723631568656336281135955925831747282838093034952
def BK_175 : ℕ := 4353401453581671416825420065820510822901799640060237575999320075464
def BK_176 : ℕ := 4299425208137535829156992802055292303412692131400910852283161596648
def BK_177 : ℕ := 4162034415733065004213091218841673394465080417991942646328126167144
def BK_178 : ℕ := 3949981063562152537621227118223187454605197551118076546582824738632
def BK_179 : ℕ := 426193550398833911665348771720084665458735366069594861820118394762131198214055104654285470010620513780976908651165913144904643139627932238167143
def BK_180 : ℕ := 387589645547545395928074123538431778348398407557400412683280730424876681440388784407784982369601376547031078064903015870291504988687968246484839
def BK_181 : ℕ := 344151995701868927347405418608144896841534054143335370961123957987256482555399515343662710962902390861058536470402721912375086026546751754266727
def BK_182 : ℕ := 297542003003472855559018767078761524484797009020178659228490852130097105178460708884365371138095858072107358262056510321808974742390712782186567
def BK_183 : ℕ := 3349075549497045206549676811036968215086464845177154119107440345923090484652782557309295805039476857114094963760346798183618585852468256468979856690270358197405166156716248333817990026698012801723290548609230466750615732401392793154708585464450348155496144431054133645033861147854224299664235812422
def BK_184 : ℕ := 2708830872002252704912055272333909015944860227208217840318047796315591170339189791027171071270824019863438733368370129418787473033631261460450523707870668334930954933173135098434083142288485631880793979403688496175413912175700114497153973512864444528360030537618746635949147266801785471160038809254
def BK_185 : ℕ := 2096179934193069240145022456199851049139306117741624724608051169176859119269984431104452812785254495866981427609170457688140941094801797358416441121626946994823027217589255876150128643933721119150216360396088232108875087377677606711431335872050225781648811394826702226648167591281267353642148699014
def BK_186 : ℕ := 275664778473502240994368286758260391189531381980583857038891417048220822009802402663500147408346053001750316759897613560135778176101317311099807334990880192691426871987452520990331338261133188101016264156338073328331954545936456602027233822043439637879018509976422396146063998885357663339498909863312173642922906637606411412196777305910374084563355679081946947057190443068848557406342302032933416311957356462006589541956264004597837165321820303320905961169573060067912156464634594828413761644601510716031135748769507286405805949700367227660289775293697936372612637052986111489261778686888515645848332336357
def BK_187 : ℕ := 186579366881125808763046063263093923489008271255672295457229836467283131364810618973628292982032320677053556471840431018199685195699867506836904468717315284267029753615216764103201341576776047734124251340419509710428141203671452550994797777254223169491406228107810329088605985586604186359752164187066778504880260550798939337582250059961907331916370985375306658398556640302735888899830065306530665576946995763179158329718351502244325835285034507602477172396915245651695657094539181314489450857804065366831753573560145486832063789188293750841517908426101857114187016455924824086607062437535503801380050113061
def BK_188 : ℕ := 112691550515994217889055429313267085077824943083797210466864670653250259910230385718999286594564852448825504750316153071966092708733444737048036802080208396303739277160840198173447034493230423265132807321947537377885663806349952423383128925062179886107961870990475297534164420378288383343624303988425761287946039518289843939283695608804031649564812539254408248935166143715036569963619672143233056536790731779097125609766066367785626404156298100314496605278286812007903050536584513978681837767444988681607665228886577432494550178027688747489770225200607436904010983339389006568276584418020512459786881959333
def BK_189 : ℕ := 1819224644609804252356736402835883093312023162002411619935021932994300420036253311688748153674850122436129489721923153742407417877274367492180294457243418454385223877865521681414837494574393914085547370695572320875216504680356425520585142596938331194725839057316565324108680592898331000457080647142974982227934140692845999940937931215337867571398414149291205187236533810067040525278681253203213794906194157363420296017813032164773877563311521017762382840840608266539323624029125426849508095709203876024595418675028193895107572871012372754683186018534020102669076348852413348365169451486260095320735603919659737605720489367271879951349447334573134221205419245395468484292389775301053205755919601152956099998764968902617587409248871749530382788054300904206603789940275240753694600107248338274822193806929040203147476270668464432587990783095243079738509970022296671129584479497433196202294336331344394753317508231535311837442050788902888436655951827404257007193539628459919064550261225244962540392743810391755475172585606426048747872178041528557492401022698319221391522058757666769536136076126020226663149043909019647804219340277559598249108980892454058310167612782328857306912148920842687119805502117129237415309860296871268
def BK_190 : ℕ := 611361473512169802182408288782572942897003448398132559315606761991810202976203126361792959670474012889965552655925888234833507082247994085458293230684107518714308891876417895646985595689600488660272156660277738027074011546239663942561339892385809308203220169312449475585018709277994779285745805231364348377544143469920912416732714031464104613913692600531882195399294509797572222884870669375747886026217955709497251385291283310384791280709043210618061815557939969536510327173648388559236143505119275133735440845457729645904114158306781344334274643150476623117010103099893384244240132080115214739417361406187910030564787472891564396750593609099037359361694231949009160145081706799198852414695210410835527881197008673329114797755884115808206716534213726003181682300333933738190169018146085370739634803954851324579173555849019526221442484807661249915176655105677749961851400222984809725884956474702498444384825086605125885915758490687706291886453874978146607589138937137712205480231837879278073828619656792917976468540084400188132733120652707903793636179357477404764478394982731821549863041381669081783865369536829892154743051635260691237163766323545203788565030018348439728921635622820274896306675631242618857216998029706468
def BK_191 : ℕ := 1409487399827619315885339306771067347156471103077928247979756924305679321723109229480218344760824017515423439485176124310923226653448426614104478060237009461645986812047237116812698140263560015695410589518208078922106536699652087268690785379373893907483890547663068988749567661683798118623019531715009711019693974934391914523741836885352076256246208343809422890041839143174734788140742554869599226463337319792141707373402782007179424984322106646266764638654981228794049270639270619998816167434231241259054277643328829126650900993760725933572293541437793772862705206882023391642154656696765608809986803397
def BK_192 : ℕ := 17183249518110424099220607715183822443458992392158876518149055822307067225981272806845846575308458454562669164311219277186377483419670354359005375579151420255995615814851630552394517660069190727235434805479237519443958717413806127974944043464125693001764285110061392433313472223996502422650355718
def BK_193 : ℕ := 24467349066816280431687236528533131674606061755679523754272579484326911359255443537299355092566600291366265122967460868638427204705915733391409525435212073772725876272343299948440593536981402983088711838043689947760126367441076897411807488287298587327288587503117454003349378627413409241375592352945638204602497931413883219693192052240231953921578561414341015691892656244898558111735375279904474165529793706811007283004530763375416425826647953423725523439701006902167420055041116575630037194488906473726980019773246170692314535912805741411445135157074085844383149814621295164412725530506459451939952343621
def BK_194 : ℕ := 2071021935169405996302793876396035545587310763819700365999872096814482727676282777908344602888251968633639869626734858785055112796713518496942451670840126294145061614603675091738233760502721372175539908817016104815335805595328536152151201148334185777730844009157381019193500279436284101585062324266602661833740285199450939493247998204063832462918610229285106896794491545803078233626254664858135081764689430608585475532686326291244231598022158210311709949941825682078846164688904735504583593949749415431183889942292305746044370126474217925153384746133703526450090875152637347489647877772289991670909380021988142323866098599308941730993274528151413282776408374508372719919789472797422042741399657545019266779360982945025824338617868363443952400984964584679668683625209458101915478864785253055472887105923999067682520647087498246186944089797969915449841821477598819823873627425143490280452385325833944824071181686914763772815647884129070370955960160804308881496179981260107503987176440998024183255559409213400227582696145590768262759371120897113674085767995282674232812693049852668615428319169360255708133982107868670228279388645147547890165628813672990603996145121248844489198950775283484876298361554497402764232280938216260
def BK_195 : ℕ := 3844996913417349821809407622839133616059922653052323066946031417341132169408749446683226031749836007476022149553536649565795153135809213403254397379101363540491956621367351078216315227408482245164979597178806747309387137093474605673430849962410381303489411620518818895047181427292867439491716674304509252402112311926517278993395547296826545506060765248613220286547910682911695821163504272915560027690815993987782166978421847773509939029867207795589581254176703433600062740639291609235977409276985922956508024209228146812181052707331241252102445774557579704041956970316970635896496654322348638630937962181627789146988165316208012161818091503555808716647798359046091542079907119820919963660090794692892463237454049282698042858448429060762670483067228927972880017229673895290058269405701970412465914616606975097312072742259924141453492548660060248120652744138915452059488449218264353394517139262319207406561243617999706248758766359167808858799434779163862879801660797533870114012564770993973802076929445888864244302563365036861241881700871162194988910165396594803013078891987765184899213916045368597396786443173430576846576110471433316518666527520076362680655519092286629228713928627762982790774431750731500613616448245637636
def BK_196 : ℕ := 185811778721627795128357788827050741699378440360111964537168034541961087510163135997182031472122607699946873967663300893019649750307511042699463684960019592328827430061546955624862020976461868985915114216227427324903867070795810598504447489282040057620822665907702618399137493465330764938060256599220288312928529756978573891471939841383728554276280668085402522917973554699233080573530913814247101044872264061096840656285910807378131376356206776184669696556020588404594135116050242709347971101978248928441585597923726646739654300152583788363037682530412777227045016389262580438517452625111363998700048507333
def BK_197 : ℕ := 263794463758181365206226345859712171295249990248711907365875882871610281944279083137257448928226536419885549746844155701585774692226763865450982520388247989929514005964966291616184668774829807341250288743141880045830820523790308858781611283040072520078943164889223090542682365522996268440332439966382365613681330836273245972916345373833283081482836974802664070890472640238134374013800521035450756419137014925379569215322080438256933822234129406430269691547119823985460492515860981425212198134272878612682070213605226960637573932256559979014697314567882925093010007010742469436641302869237973247996734106469
def BK_198 : ℕ := 1922582055863719804827809551805368784385816659949767471231225502615874817358890743077075695119171188287746373990563749081232187925767665225817512105740411077488325643787335951561390067140459804516420601925940194168186315046931906190254128392825848237234726487413150715479805042703238987179067602950
def BK_199 : ℕ := 2411458150197167685469986569566969297086589824362592848054186177286457387952165373168896694975066758900282742376674897868655827759280139914513012564285985931151189826006233081777277755870831303286498067924942962310207715741199479626245211869816249317529911456433154831647697247728068729710740348038
def BK_200 : ℕ := 2898858570101699892981326915732265561383257396150838450980785325129645748981018404702443388794977997042831050824879815098596664834936307089722519091968532855840779297823844138799021915785446435005539964331375073943950188942374740263912756184155551145867624766345444456953798986460325265992106104902
def BK_201 : ℕ := 3365226575339697702829228884921025951754619909682238854077110878556370791755796149425217440120831512601959941532108849064207545628109493512097887202735599077080871511450197928254658431855230752275046465828018613596424441509333963226600000601762968207949232927800090649276257406510877938115513274854
def BK_202 : ℕ := 280609312228840226621339061577172617717094592692409058810951157609224882209489520630883712637074998466734670575383937590067220914442728252271719
def BK_203 : ℕ := 308549085832758724701799517249429376042007029493319690582984278753454234945986438604949681269300046165335024316824572168384603598822245435273479
def BK_204 : ℕ := 2832695119157133773128422013538328896536302157939177261503283697256
def BK_205 : ℕ := 2984309321936851363995746885878166258461487378749458424369769231880
def BK_206 : ℕ := 3079762847862207126238992018624556430181523254582096026291358509032
def BK_207 : ℕ := 3115910718312465100401186034846375875192280609859390524754671838600
def BK_208 : ℕ := 3078923825343488991200787087624397996869026555769173729536313684744
def BK_209 : ℕ := 2982106410759409317043965495158199648424949195109766705723858819432
def BK_210 : ℕ := 2831571467750019207399583315924550035479158716990888433922024352584
def BK_211 : ℕ := 305547020943231100639800005505161762792538412334411399563623040829346188672568181022438609016395816330636519775829161420395547572622089337599399
def BK_212 : ℕ := 277969317689126530691419929901859375648437872807493254038687186286066610726464068390726652373992628400125152898031132803142330154890743211852487
def BK_213 : ℕ := 246872528807780836968971394836355284890277276344257765037573676721991192207135068959411063639143203506962791732330863761998667998336306678509383
def BK_214 : ℕ := 213447041688570800267373692429621401411300161218889941936485084246652409760150049819428386781483116024220121597190180991963702743623712974633127
def BK_215 : ℕ := 2401628948534381119110261707031506693372365736907444858534710463258955962270978185549829043675594762523041186843458614721941222033646597253025936059531254104347511539498954328921249261709639934304470751176586266392206393105519889142490593115776378384942830054868669078219862147109454502934852165062
def BK_216 : ℕ := 1941395345599474745031770136494482107472950335922640214488243487811881508083482696902817854135271958296463416318284116020889626113998763765917465445211396082833624329992241782735834300583424287388412553584463850169867900888131143051685986402657473226378296698516947178862450646654940421443259711654
def BK_217 : ℕ := 1500633971538810930703815427636977144931655397357548414315976914406740176957979071045376618026495766192401322344166027809869592599938434510446270137978621524135288984543317394435846577304413309089130774248576164706111997402468626339033058574318794479105853468035235394139177643151378245637957853350
def BK_218 : ℕ := 196941582774707878141922149388288102413252080338811667094478469462476597271361775367336999405786254370092958260013510997180207307730886592294981240865064487220125540250149581036951803078790516052042598586597911014972543828590711601101629014603985095266645849699462706960349405110565953094570476114988854934966334765586964854372986641025660426874936888814583199923450837734744007392213305263525962469184059659069033767146316193287089565339119936992840966334941689320320155432400794531271870407180554093171653198666934037497089661822964780063770941416568328665954138571095445344648865960040292844729128932069
def BK_219 : ℕ := 132841076039493109733741527459979921435846693413230551358489281578166530803644110742049742110650833302195288988765455585623082033101814568834693151331297184164490409964628855043112542915165685694042834674231168650593745992772232140456094380476045922678849462020729583826167011440310407015995505296947765038101708460020862924667421144340659500474895844933466466017796541922775430756699305402706836752569388779760024227989948481960456219328614360350319073427707498195138367616474356877640943108624222336156870888355947194278547766959850246210132578558141006078899259214279689142615492530390608284998988793157
def BK_220 : ℕ := 79740087431677827029994839244274001364815427127218917346303427007539482674496735079386744336456387466089237509624832729875304832827407161736124203599500215688877483874920742809542627739531575268876936509839482730566658001601400245008862285374000885353041094527837081125079492450438503711301114479332398720080253984450609948382601052980710879455412350460478650996088267193191356703486651419027072775424404259072372350706868453044599944800985951772709424509899460440596426803260578874443256169190955407926582036459039458303272601200224358645638538161175188546984715364713078471887100549222707919101000844645
def BK_221 : ℕ := 1271315247682296988584164417795069449061936628030702067231561914395437406146243106413469668075860414418375668314121069144129284368216964415939093456520495135877456664553758704952541275654096471787087644829281376448366806224072988584404286348059567282735518349193319957935784589484401904185317407552415719047784615466395012348039843370648874838184577258955562367161212557665491314420428659890564841501409541894952431542385945654634784009476196982181737051478086941446359621558132629950561742441509803513632423455114940831380718842266451217963959017211510249272284722872488260305274683201071277061644564477954544832756267113980949990709308516666620319151559345460959688759727319248983978845989384369695074698083881051113094489624495929779751684581213620066688701718971874512582197296250800827572476256712373551552527685313577003779867473824045342350776292351702373504727452192967501213925515031730721067497476375537061316991389610990516758381926868118262699127118495544857120099616888772368166489457209513334831929616961403615983963623971631644853560545524932406759147219455460131614886912289392951433914673920812745383360802442827891450962892423587351396216727329050171959314037900041647712069758091320339878906373460107876
def BK_222 : ℕ := 12793248095063225238956769903774026040986047137611435428760094998352989490068474247582292120323088455122791833052322657993086673166505989680530893812657154442750794933553735360450845304678356235091237265442076731365689906202828169708483529489062888248375882693485853126028757560809483818971848797997913392082383108689915180355510468949408022717752379155873539987577874407829064764559333896387500552175966434888501041184396515807336693120043011286892290415750863139065475464681602504033216748903768821591638444263051478375017949136427490304004339888428184082789015362398392670442089296690868702234431941957
def BK_223 : ℕ := 760188097279281379541955534758108935799535938498286393998145838308933193034453647551117549030046605876805406201621471036592418373888748090491619796087171205065031415482003691978614564112972891827279614742210055725053637577667582256989988090419295410908529684525770011415731483469937962060893417551054190541758265450102128864231860015149238277729521297351180325762665971643814813402402092684591518994644149332813818196739855707880697743301243530782900155452651554812714716778788401676740611819037962703867698074667024219597154932534039520565844012764068261217031435909742216255055101791484590415172509445
def BK_224 : ℕ := 910862659994753740348849792004852607090055927024367053564892691088119978030352269383819565153052829348339145573875336586101736824470924951559
def BK_225 : ℕ := 19211567775964336841129366872004626634231146190018476678082334742307028633078845442964758935111888998350594414429778916175375796755330016466777403139969266636468278912320679538619685060885178538843742218863997063704351278366821662018307057508036355137110855091436019495809995782251649941933908005411510156243281591704124731713196657900417971622780581814066611447612728498043044835910280218052132950233902853892749443976064669891376592909897490684366979628892189969841290612003383074205608484810843321636247959358643972518734699120918010941592705506039602642217651142235168957224818646647189978272520520741
def BK_226 : ℕ := 48536328176657711397080737756380488398491574062822576861319834480924690964504619640109059394503098797439692800837450275209300928493837540277571866826160411734772252673493693124738683961784735040093024670879957998325967764399344512579542879327934240409730327455879971451572122154809441072958759747200587799179001391297950781610369827309505480750289089031265812448830798680365671510710880810888742220312824441297619204018995346326860639406125721264023812525154056882217848643059503686808595383244997656297362733209454951029057552002258857429324903090278326768209521465652392868947993310620066567381563843397
def BK_227 : ℕ := 2916724720096108468479503636336189894272930656768781375362143488709796906056905499847987009064691227866861013436961150143865992454665028561442448599167347793703428036494327222054805470864772271510362666975374618236677687300513426772723052722083105180185902888650018461081137985105580296455310957381002656952429521621937763292867670400040898839060004100048437938845966918700797055257895827544531035945712756725577627078811805001317244705367432877387305987268054759120671569191848515818013233277336751959581970212316995970341291241002048741621915564387298016365187174802020693886351040102362851525640653135314986972199892229487574628076783814005219357462571791065976469275467182287520900030381623045611136848582212930184128298504537817826499016797572190800330519372838929829434532369181347157801079226022987994667058551851512395525517144649993780032986776215978981826444113229404793128676882517202181127288151982157616730346583628851290670625066519967001454187589628263237912845644121969960922196129705156699693478993551631445996875469498570412152509816945351603531317381054911238898372886851379546627373312359446394952082928950910895333327244867613313364430926979386109537008177275594636156375301519303826538103917564169700
def BK_228 : ℕ := 140229644643103243975022768669950899340534918756039780158949844295940383779327951413035040359444259423015507038492705921743848790710776329137445798370602733138583514802389038056573104351367838258362158390749725489445910736983062849517480774271793630063570187367538216737794156217420771550771865693954724192839486898601862806583172449701320381920825416318426895349503002071243698780958429340180469944185113926557517400070912079852383660524578832166803887972655668966815161451453683343283474616735555481461967265687975248391847253797422226742402255771963779120499958731627237220424720633855058307936631140741
def BK_229 : ℕ := 198480459121056394247720939062949026165320186093761388900774346058986280815225820570450251906358209188587691213138069443542763140998736449153635205457033725184994372520050955275296394492590522742523025683383109365181357838558970210641888996578602645543376015173162161686174482342356935960490004004601376222451287491790082235464713039101169903880664412577589334952942673855884786204915606346521518662616398743421013768007335364584384144677286506431828217516394947896694608534077222420821230605848035454345779085700263161573479846061696225671208243452587072985212645188323020243272442177818943002413930665957
def BK_230 : ℕ := 1444157927755342714406145965722029586158227137940070214382502026310351377165354483026039857851548657934782205424001166813814797216138723215834579939649641638581902809423694907113286105527477618673253460521543735335280556919559628921673750784086651163820064907584338880895213259574064823118572057958
def BK_231 : ℕ := 1809437244991429777460228314671037104141872338173035084487422951101057362162271548829956879492547554260223293336309829821853384938039889814070250787605656913819168624436018449786899973496975243107169228325238057543433335593374527253795158945082485552148427245686034110078209492898112921065548712838
def BK_232 : ℕ := 2173872072296563404688919017044561238968552350552116325389485494944641792307295648344977557486233588030801173529204466080487265163798156707959465267999395024426398146909628363853335262589597982648950572816057038672373237316837466317753540066891878980964332332272832025873495159189528391798201062566
def BK_233 : ℕ := 2522927702613164959565316486033368099350081160985067145462101950916045691219322818452533929954585216011618057999371214678448513478798604854077574117212618713599637267291638605222552019235292710789207617716732691935690794055492968550453012379613885101242647219419863958116131030765057280298384808294
def BK_234 : ℕ := 210399854647887283852799555212993030430041142170870050234094743198814068108603909999385201140990081785351594614115440398780065709701265481196807
def BK_235 : ℕ := 231373024445520833388505552604957208389726583333766880259806510213263005657617335386907234618760098501810334896664040193824438492590393903539143
def BK_236 : ℕ := 2125262740408161023170349961785956585952273650956334532975568919400
def BK_237 : ℕ := 2239654232055722885259579093589226267145855313345809137605229204488
def BK_238 : ℕ := 2312081139269661221232686187099581442775391026394032670064315608584
def BK_239 : ℕ := 2340098505814967428076274983910629463793848860468529944325795063080
def BK_240 : ℕ := 2313221261818208437224788748648698619643090692343585112100439531816
def BK_241 : ℕ := 2241338102270118835403407630108190321182452062699512413403948278824
def BK_242 : ℕ := 2128956689253714915573822064370787983731562032286603038557883282696
def BK_243 : ℕ := 229742370490362357271196189480445214604954192192487010533677308722827030656632739796004939367807753189109772771593813503617289648802270193062055
def BK_244 : ℕ := 209058377840480116468863177090302691978937781880203982212906420299888423178532396554270815667279095066814060744197393600542991534972987397953191
def BK_245 : ℕ := 185698665072136028592475265230437935739935182363514040284864942939846020982939139243209473089102509307841752159601849321895020950098129943425159
def BK_246 : ℕ := 160557976469853948659367032295167725833170993398892364156575875285439052930546782841263888254493312410059709751095849010903799863151790226319079
def BK_247 : ℕ := 1805997227117553291688424424335021387072732392081695971456133852235479591157700810467789694948779609532208659357213405047220902892644353142256348296824252933061319135453307700284018645679857051555556385331703293684130832404512922040130243116954537153398683210150697738212123263312425238876589375622
def BK_248 : ℕ := 1459238684257947747952804930526323994151496988238754816028283537613294222841160423515774389840354653832797442073684358139200316666855585977027802774983637780157874993385868795619634410435821281015912266645508243872789518918197350717129565700401524112504350504435400953849102427795060034885670195206
def BK_249 : ℕ := 1126955908796577752188561761205167775452721078911592892905758352288070484925270497855458238910738105459947288562841305459825720438398640076866206136038258897262338200681277732910109841822638687158739532447693772401561028663149502979302230434412239052323053556048196832738467370297609479007257266662
def BK_250 : ℕ := 147665696973862301837636944590690554247760212436664891791875055595226087705268578253056086759014233302392977565952953805562434916150617299478311847806685994277611064655924027783713219164340562543280348934187265404729968183790059321115586429069782958141969237847107682673630849392585965169011203467649030245393270066049911977155568464596819783156608875475846088598427731058762119900279002395357214333211459243807776600352623042213996616942008046005521247517127640821984658369237815532324821265536114703396247520342214797666831231745041762325138944862693836389868459172559221337867777632898807471983326274533
def BK_251 : ℕ := 99339822050363185324581353144859653727212099927575970163866502201298287053244213760219811705605317120848320068597606300264422736602247996989607407373711105736765935928831217689758141230900384623454205528888162651354766421545560005555617425797818892724370340614918350510924641594077477563199769814186942791727143104799649556161540940682803134655776936413986254227954457598166439660474907434315011408024329245409594584173418243249181172087265723234208929958957115601216782665553413955782525384154484305790199085127469397495443341354016846992840135088147967176318743581398373672663365195426746891159872813861
def BK_252 : ℕ := 59345518974929718122072965321300111089317421750862828540510362680605720161119951454346789458960659734253195449368438896437691746770072491763348369437969828938684921126656821696096816323514125572328695227290004728465262154748300682730971358468154361253604450932109497389855498491262813795508207671419523217392601868231604810896197418972751026579742755176415965966736191568600454189532298299083472563553122898927855786455896284909832045093764348571134258277513164374134394859024348283707077724967298818728239629571639535394728555322806398259064082491294188029523852094275535400990350525032111909651647619941
def BK_253 : ℕ := 28988450047328394573721275779672641031189569768778623289515160718139754963100712241766468455779150250717927611925396464147883354898103439178682969051639906949079004099529440445561771515074864410918876482823840605211909286757625309399662693232521011463725922851170533614825999662926860230263810545738038609326347824188193626035729606292360444457962661549940742913716310817059131586402276147203369823174667614223646863415282516772506715351027567294744001029732827477434031597577789107220235260913774765522181843449762559496356501197797945729593825007210122071275936049245509315873838771715175303037576838117
def BK_254 : ℕ := 9187344068271897187828916542224992914611560329228494119944964715229061539480788957785336790152103152292336783977000365818140066004486872508736472341276148393731389540643558222448116341508187409151124258323883638683558021364057874240543877104904557728430439117261480758217498526183338232218555616128109264498382974159092181609047048761406118958645048199291470771134608634561907514358389703575075335627931238501306915453677039934053478044409473021324011107029554231922447074536284930290456041514529157546767489200656714079973757396303028422420881938175146886636625301852913022551152663278233598642216764709
def BK_255 : ℕ := 2477336785070088266196475617319860111546831128995106561789606389688624808235621811100277748861442622871783284450689600967046232121169555843404065954081444454581247157079243621700073837970334119390472664985952881124468533138656365489754418307558949396632646111966099651920114623131742861281976582
def BK_256 : ℕ := 802569504773883136968568931415483020243021575461090153617539771404084729905491329518815164680161632914431820406622372111111099927515493302279
def BK_257 : ℕ := 15443423015217379650879425735444057431627033788305458597343529431438686999923245677790419308524140730292169063396064274991632299416842346002309294545916521385936915871694996261510252127616249154852488677650550171909009906434016222695754169698122397080016855917525147415399943855933145866923033558955433093696683531696725941183924586500288359165399034689328866558182403398069006180070905182844985802517982218277542849180247828117623182659661003414929754969436979549353422120043760365246021610544644032962106397854984180722852796197694936209149704647418381315096222617372179144269471357596815833340747232773
def BK_258 : ℕ := 38348069780510920625127200905372180217467937463663977837973164239144487770524453632400515818687460266375168725572730496134250259628279100676346365508266972391394250782126039350632598432272271831885231681518291517577164483493258031203766939589418433327317875195183861983671908793911444010248858620171705648735866542906605408894067741526033933247064016787128698734497280017707485060409235138574149901852066517751814311173530336479974950545341861415568446250093139089039684670006536375900916347811823434786109742456735096295408395127161752609018001368075838890588928485305668394046771165019465436698172421605
def BK_259 : ℕ := 70196699512937941457435011067062225625588470951573724829450049744496130139873317539889940611398837930686477842120685497785483007834886127628767819106597873786415047099976995146090753486402361100139734085433862130403462968065509166326181472136643596598845979949200034484741350402581441354512197764379141055109912594839927891529477287484679576674849238066387279117777002539033543956563795330430065732545723638680809633991542578484332908236894021052048640764075260775059056965859899017683259009062415318041592205294717673116646063784484749615882156225099337656734825913171956647018528609041050016712941210981
def BK_260 : ℕ := 109552915499553013329200539589603435637393897532666383241974873289510311727443918888023234467739004425498885614875548175277220259344097293092778781679013443357467806610303231029961189707579808286598102637960121877841310134406557726824617181504776452451061855235966054892249489761272856488929245532709658003807998114952044078007979085886978031012807302391051403912916533581628826688836437520667486263599666645468892711013651345639230872177389792423957670761188065526869809102361436302352308687311955835604593508761168728537954115477098023410786276738878359670202434780250085759455008607490065260909754659237
def BK_261 : ℕ := 154717226430038332773186725733675847105118554617805088431994091389200616556159477812080679439956974626639447330832687232473028359093933964104281575933365376955997040401476876510327249391436892654972944105350913855754862000850468673092067960618460855724387576687100787055701295601820314259800065774563905896474709501663669622406792204584013673630138545432081374072847741522352259255411007681020378540117618291920695718194436839115892492945738483959573015840562866826907801885324955510039860397333091786479157809044008481746984758276959132717336013711248975949691961276789138358008544115329820895879553731429
def BK_262 : ℕ := 1124363499335169300361259141427352677041060725242709587071289787220937730481201633453944424888519228638526121278518800694342804876569746576581980938280011779376072029693191978525861497422374677917402191413706738475973146629009883192446187041005717216317365750214492698645384715836701471359210870534
def BK_263 : ℕ := 1407650578136017321511564817852565268395008392385336781790782471357025144089188161590148506310791382432950039183898786964945741789601437853432549806806595351276104270016577413554991729293506917510059003928351596133933391119706288592186698765138088291130394462765314851935223883169688454319352570598
def BK_264 : ℕ := 1690436513909192337501006876289678339081385720255755910821518701225737893912704167249627841416289387063476946911431820938561199598679671405921107793315659047343962606419075918957789519800028379846302214623650971982579930430122664729762485774936636866822434806540099770952926688847788782036601793414
def BK_265 : ℕ := 1961494081210845114219233500684912777060594659773131313649064890125332925169429385992886700487601375468073741608981620496344501216100258386540799229959896567379367988582231258017120875440837063800693569793200465525611873248563185120146756302593209234555487202378423378070785027926129182512132525542
def BK_266 : ℕ := 163595604124713129977779953935774830499343404881434098005817736023230444234779972361593844516214576202874307197699620697995303483859542297925479
def BK_267 : ℕ := 179918610945652725087827779661501012885771500736304607568419346737834312801773778417362158636692540446814046127284501085428570842581872296868455
def BK_268 : ℕ := 1653287762117206556033436200482901371623284376263272507137209708968
def BK_269 : ℕ := 1742660835347355270388888379860176338664075065026996545538321565032
def BK_270 : ℕ := 1799488190625199392804115948477951284954699065851138968000176479688
def BK_271 : ℕ := 1821817599093688263552513968236860966366004893354007405525700697096
def BK_272 : ℕ := 1801427162247879699842580068541753591968081935978185308775772784360
def BK_273 : ℕ := 1745954054011037184831863933327354948837368298271578644011946356200
def BK_274 : ℕ := 1658858815462717232561671114782133037713705692543109876097237415528
def BK_275 : ℕ := 179019052082282286458891936847188383154445944600871757890552566209873651501377089083329200528526109906934784827493586311458234971914144582612551
def BK_276 : ℕ := 162931610784735125491672219715697783416288880379268690564530909965993972595944636528780672420477348345812242127281816311236006172466750624136071
def BK_277 : ℕ := 144741430872001745358360901760442313309068341976584798625151899805027597721185640113007742595097612367296415117983364640143298455533361274199047
def BK_278 : ℕ := 125145533236712799461571053103957142908741613704846852941367967903820099604639282249832976293386046390401759610762445488559730636801688035604935
def BK_279 : ℕ := 1407321576343034547037732299418873987890581209197230523434379319624862230842262963136775490702476285135974990662532258045879617079599949415789065933046335533316450611707536848994423834076563883950929251013293772519682232989443515528959193005637812868104676639340057197960692010429773980849539876326
def BK_280 : ℕ := 1136686877707221327059296234734412782110907791481637885465228037866658106204582076496557853703230517396088855495940137858023560298584060660515388583260896040385041656836201878030727031164583292667315823730977236142378181357989507922478549562796044078036048219554676612717091692717353345651228001894
def BK_281 : ℕ := 877236369208425366289913630611179925559414363287121965016509286926137817048479042629960315774594999101138385937713577537460422934683959957040937948577416662254774862399320668668930233629588718348905869357836006694017434700440093316711675952910720505711412467301003338696573781012080265711968946662
def BK_282 : ℕ := 114799390653588481909786829542835448103995595957856053750932161985507382437126776705612799676986537391796848434146131765278697825336407154795257552812212257713268718090511957984985827732378703133055742848106404800058908839158245461407873825772950049866777996289769134202789208616364660450375212261491361143797851532174169405725659471578850153084530215742995788423194483654403220934990964921142458559030904702656802531552669022426981768722121552979784759583713491226676617768653160571299775209805412675451382111637679816479144970069245611062180812857092540651892967513981704109869739335165821278158481514885
def BK_283 : ℕ := 77066703228545828734075513022181067566379034809547425578475605830531608136058248818098934327505362824552087416562076121874823158156382416131596977154268228006337897148105550163631927049467386545643519873921811907584583930229557002531144594238675103167985487030476921043224880411249753227375342226882001261562761905083621643026473483013929727509194170875871349815155144279590631090897172631123457672250971979268583674333774890191720549303701179021523499634850536866496154250703954749307444097466358451770056574614232156005410853594810316381331604149520346000664199707548581921449166287785525819495505935493
def BK_284 : ℕ := 45864065195456423309399619007488467538144670141096708017504371336677893656985083051347999491083883003811464411334556236184599707303854450149434843510657722614292342507049034450612913714837807530371970984458895799790463260432301160996677244525294918519010615501252855239026949090964156803993692927532448816326337978510644434402697508982910009992847690995761167344588740240606011111852091509277258963178660575555043532882299121850297742378299588187168005753698623290767062866393033696166386665213460008569946841562533704395122716705858844429969806951769225895083695615964650862991155335752048173074300762021
def BK_285 : ℕ := 22229335126908309511355198373090223394341476007158624276614943141986277191216730620880633554781879074263175956715783311567961824268961028711883719149714911222442452504470897612039633293661699571878671485026171213831511080297228163353056389810724109014191467755136017354884304087109079797466838597880711176118947651086349035447792900600400192911769364099334856558946782017354011492977920393637848770408858328247303503277852636242699836874463521406527148696681076446949594070024922744625074326102024808980745413727571364876062305041779682781797122362191934451070482668455757830504370845963765696841906232581
def BK_286 : ℕ := 6897697883320396360855664922069444050299614999116409769154717789555236065167473061884761296434781729897911630694784618726729238582056781364962747646695263593140693378477826672984520484464435699562783817302498203825641610003140465116537093805329869220775378363675375559157717254242149580713054231486260459104662615320214438406547949802586488130000598666214519023704557126037532072702926239181848409360170066157646264609521266958060428330298409795361259980901005824623834831553642866456759882838648146682297411622712411692314906942820141288363962466741290194268906580880872107834000132902988454858197832677
def BK_287 : ℕ := 1545840690305502599115793351566965247746799207082282537867269577595687553510210742843740761616120850418447773271161033992419671234509343872761945356145185379640452208410497249577614971762280151613359165770114780933403628305611468724657729937819348563884989966523660930355135892058949526826937254
def BK_288 : ℕ := 702951896565116407963519833689104425802420752546221068170804557961466778887584108194770093517145369256877411515537851206081288983684585619463
def BK_289 : ℕ := 67922811648823557869786655173462282462182195368148898522258839277128209354248280364421335198240231385685976787979804081995434201604203452629635824918625223797078299395635830544458703767959498534660475335137763190046108331190168545620291662027544523498085035826034924098935924759285691880125579590
def BK_290 : ℕ := 31044994306517483691706022881866242350650529504691508514584550827099153765754523445398292022062391905688785651321117072311887159577305061846837779192735000769363725387496095836533441880079088144746169224872830603290847170650223445319704170164178485550684949164024177756776891226906186174297587387202829069340998922639826705381533168439175958775942657024534121675950094341524215827657735545678801521931561179641752606353126602702005761901110838792582961593953882581638386754532534045876931269030162284458887310844644506610866859435498151552655201749590184735910990148042734852878810690962640845158919327077
def BK_291 : ℕ := 56510230403808503955654336761048918148462931640376944600830217391433525055639660716596630773491220958167022264499124900808866697087306919142019147715350006036637187031295725067941760153568682703139885650931030078635413177061312237008390356502309732874818703203219606659343592478277258871286907925902133672193683772484511258198519968912862415070427377070905578553509220596758522350061322807751760689988677651585449839507101275432070673303651899273907432919578197330629560877853004757188032023310181503669037572896266337636969160963965691114258466900885926434083296431979581524771558610621716145689469415493
def BK_292 : ℕ := 87933188438442232207153499037998768889235364551812549234122785946618355803325382628191899763859020977155031563475405250953709173498731129069524645943137120767766272290866902171311941977552963958104197402623660994236799844103252795357897464952769824459401220076744215898001166260732956323989747871143986876100456095259956594385867451785298692545243842488419390759654165056127580016257763216499235395998176411888401005406372328996554902394270720722516491621635003292371847911806812073959336175555167726177019729076949534459772431347353584968412024207856977549125375997847406529947808496814984020119522640997
def BK_293 : ℕ := 123974233102770553385587573904213090156221638635478454521846438719986950339973036304991804673992084873328731000071985971612409113388254279447105253892202878703969496487244671469343145563286283913696379058673431841088905406374068536051624418297222664230269767982589726218877920015853002874736909766719603099607442598016801200904921574047111924897106394081138593828045915468089106210938252596676036594161288140902793341248822824094943840273822374771549655080304100023161194902152924548954378307735221864944535264398821029594155341270310334083164183389554181160504629947296714184465701677097592018509312239013
def BK_294 : ℕ := 900110882104456355175400118114750508079986024738840514218533978192704101989748218430084418728251152830662125016698853251462209233140018333930295525193782784507330493847737295341903213015145763355249466660449719338604735716605735462756484021611723641516520239415264833879708617388978568667204789638
def BK_295 : ℕ := 1126223061174756763948058466686115845952476327089672210137535533265840201916542908947851560312487596842273856192430337648049386544818581191603861572587004752387259835657024083807921688835426363811516137708636793505033235694645616095486893145575156006092304787615592440287801309082232287378468715014
def BK_296 : ℕ := 1352032433848156305918461299511398671079495205780227014769813303859421972146466084154008843287907812663994932471650252536515327163612427095225491871622512536222212343283024977791252434668969239246060095345137210051867036801579060137368837296511620691223031000702486326491317657277021478894052157030
def BK_297 : ℕ := 1568606055487161211401566400483792092460656467061712532402528671522662139353332583308940366535536625184118882481334024145491965170635384677681355792571990259430339115933347820688075282209393243134593130622965298103465311008509950324348168956596158886018452573605276192581765964148563901496094799494
def BK_298 : ℕ := 130838436490635187725188869951708781317696078061306496175234765256630132881249409342628253182811398250689334813815325257976700401519367012639271
def BK_299 : ℕ := 143903321859982832570989363715220307510134788005548686965989962899643814451258736066546627886041178459061711010985465730191211236847076285309639
def BK_300 : ℕ := 1322756876585121647412635876868266989229424163447713838573700968392
def BK_301 : ℕ := 1394507865482950263695693074784632886898725501293493820618746931496
def BK_302 : ℕ := 1440281495685881593029128968791528795741271501680036592094959094568
def BK_303 : ℕ := 1458484287255344990304508975896178337717589959149383230445080973832
def BK_304 : ℕ := 1442496860651324764418670670002891095716498512805004605019345028104
def BK_305 : ℕ := 1398395249486944474293056616011290501841638530178056421637225926536
def BK_306 : ℕ := 1328917877057865882199169953758465788569300246386175073494446795688
def BK_307 : ℕ := 143416374803543430847236508835201951871750208882699720387451298552928684715424760610106409792607369555436504983451850741432229480321386364979911
def BK_308 : ℕ := 130546724130415471518567789170875141392435031216851842181062221591145103715679253249013735780100789008126030363699072908334809009756347028512103
def BK_309 : ℕ := 115981248233609537820692620101804914431532215666789282768255905230796935941634865624562995152212876076523765869199307732861984069750382921963047
def BK_310 : ℕ := 100278275547709104038267823852924929119451868892938283344756480560893973355587393624634786451098366325759648071651420161270940709955959283854759
def BK_311 : ℕ := 1127445513371127155810612417048281438337725269084416570758616104335849492207817885015479559816681101462242832065057577672651547833684119130051969158770879160475065804790839256687964562826120195483970746212817342435111845277363211376702956563980059926202961013613797671512756863199992383530741354022
def BK_312 : ℕ := 910352037701502630487939112157140473353066153044764047607643444244579888253961615123452172808357255920067028239259520245730770576308478767946250731576866434264407358724219092797759859010132279372737833016103138087346995267246076800396438383741468958476306738441864631902550082288594188098012799942
def BK_313 : ℕ := 702159386114264034710906982934887735842596009858258099430289349786704634526479350065579690117957081621739939162018506934649403813126900200173222810208222495998515342281202093857916387789919748614703505213247397408970022392069778057495408411585727412866802691276942538201118842001861311561575655718
def BK_314 : ℕ := 91793161230924562700122334417658005572072053613670847302067294397359602664437038212150987554688578756802826954275995054781327078832712884693582371435816561610746081830349012998400624810230398760315244858841117814900004565635133013774462870775039525222338645382305391919853129610204919828616009668400887196400879921055218586741317054761203046320674627866394740320814440855680481775224865764954112047323366437873174672306532108120592988903131032953426655136768969933148072564045173384776108574820518726621777518218730150655973840692036932212724865747487695967360216276965205298519882342607023996975112486981
def BK_315 : ℕ := 61516371754339901126292098769274778107075354667740565129010712198183012799283751188307006583024551637402959840284966602752514685421884183518230563426509390333254703651738666635631078994536441929258124636436508981636684393584014451182058908239888322984836567346710970632508690307407958763707868945222954321186124784064995631358761159149959074949942074264402906890529469274336240433903663787408896259047824969796512652381483202583076044540596525884685835495894007749767349645035528890393144746759808895572672035753390615460050123926141077335631966154023012936996273908140598336452164909603019428544265046981
def BK_316 : ℕ := 36495868118274514195835716258666200499880667950308666263374492159074984466580176796197772703800190992274204273448271980965859040087132528793081019899708659410166378061749517394872535808067225645035775563216988193876437068240671607271590931168429726298567073203178019044476385196009176767262441591992602818092240784565419947215392666037223215022973549649432918403305062135560366290834297727074562150413256365529504104021545182484274506380192647113860089840495689935032925492943653408186793991891223912971138317547579560879744169629816949532983360948343125227850466217942221558202047993409982283810758057797
def BK_317 : ℕ := 17576210328996398585605002949383416327549604129535347704911833945373725331752701512886917338271924239901775504833096727079039021052103683983860444268472499069946726812372162276651578315249469653434654060598348731471797485349142546507955960033047244707066649261801200567751012377909597313503932167654525932735617266484747481632672721437306737302680615929482137759244050945898596282010990365092324349249402760409629763854006684667998908560380771818916258639591761284087747499320660242010268022206382196876914438352102069283325404132860079472265142943008966293296785358775498750480504071858171493907087037925
def BK_318 : ℕ := 29801638029596818829127177760437973543373997250859434035453727815962487982135810185894639110963436836881269831654612239099125647853388189183134203387709549912318201829821500599361401113163473243103962983797683242348302527471976967731736060359335240100896085164951640225585659060618136185203501446
def BK_319 : ℕ := 75614486208350003894534592984116059708721654095695709253913087566243169781230072307089607004435663341771839786465931513555649468601691379303
def BK_320 : ℕ := 616126649904504728022555162609873589641362456491053292734672729172738505259436593828920474314435022533391024330376455067655308427206663864327
def BK_321 : ℕ := 56692779554745102766154327940451557458642003423925611551290258836896114451118816574727687905302532783512044030440465628996892583435873457582934223305600465859760531407151754477980334805981785381305728113037894230544264374464695667861449496615097359878233856601836518675456864652697720591106597798
def BK_322 : ℕ := 25637455701539201892315339888754717125124441377666340000071889953961500974246282141877488092223578514736302980511131720439051636867670501238689542810711473648224728327740940898201164106381792874319866673025162766838187518258483246933467749397586965611129613318407733865557657354008670757080771734700992421987616654566211468287386121443124374884834195494485914133625333727995022615488078565931607339479155408490603699127219857145429897185453282401815994676599154366487525635143817292751873854318098940013025090876546386648488816526897014672322120860787409704645130058053085235743173106662985769456557313445
def BK_323 : ℕ := 46462012558300335334620517517509702068157654098708361913996841383831008586853279759311432033549164335541100687443512867869082039165757102970916944644210852490644273472099693470398413541032329788720253848936075340987246882236216518080089075752541826909656962624184784540397382521871665919227665693121244866612987015544316742664196218120250526831007549467753464906317441138629770628691834289604998827240970594506481739944283810728656180976389690123664348957482124624943630250214664074554744675132763820338066448825401891570223236344489304495414775164549553614578656185031029488796185380271783612336245587557
def BK_324 : ℕ := 72129685176193587354917784470128232751063679437113799234541510932128723854878929370569481454972506221520570316106185608211184847157534382760009628170764819355951165724565577069028895313996603466577684194305711370487201004392637774429518866040756762646133785061765924132852689632912075744098908626749721786276491387915729610367432804687750501104083808129209442260999809552336030763608153424185062538101106203662583501049613927640795238482349697981866352883187249655256523351280479192323674254510334825824611680104986673569342664833581181245147897542340389502016563292974594068155736379663137392690479174021
def BK_325 : ℕ := 101557541883062994067726039498574247270752858805078801704290920076365737339068598137663108978813086576144317112012093282161186095240357402299733189853968583152887302476862588068362776686036767476999131348670350535793165378031960449412784587615977818155244102069862683880150999506688977794109200582763983222921906143699941808877547825516632499474757399582295862584708763367636277582649268910417554639924844668795559332746432680066319257692388701224542972295132427603929959906164980272781328053606085780645103547841560760986555784677850225297604865384666585246090022539622357381334068335338658357557954596197
def BK_326 : ℕ := 736815905691626147526358309345237467681822222473842698237929754138369891382321152676617391312595660769634716287201210053758159370938791019672906689598946353085757242941311999791200512502355131407965307707933218802882928871098911427446701009390974886241496771837480277614286438194043704190097465606
def BK_327 : ℕ := 921473545973104771349036956224304078026162844057524833885749449193420129180272921604570198840596231692982568648114362912734774147674954456924374431233478620769895624799723274948819045685457330532188284466657681599717413059969440458630851790769269922576344723624246713663735504290317635885905184966
def BK_328 : ℕ := 1105948753976354898962222421928671341038279141074506408113711238607836988376479767619888160473524611662980691552594289791171540218755085080891961831403289711501240847838668109180916900327487962290062544028931906683347390139777847149085680113686186397950521388840104561946649449676183017188595399686
def BK_329 : ℕ := 1282964508821086197009560127817354907299942315263972229283506299711130166536935372368310829994812957291387296479741810525313965576614447236756398432597808566225946682056196784848564869629248897497479323416878975273222774776399095252045117384483133360423367682529584679351467660371674950279210823014
def BK_330 : ℕ := 107020571108075155640234384629524936057383504476101947116825325293389221019980847999579164951699888790373796476503366605640642033706236580984231
def BK_331 : ℕ := 117714241081556596540637376335496030250435407129643562284199990850811830948058108084735596156592070553397824128724564421239396634038776210175239
def BK_332 : ℕ := 1082304309215398539530511511691391859106257364087481919073899305480
def BK_333 : ℕ := 1141176091419741511048637507742108614604305623314079063262320610120
def BK_334 : ℕ := 1178833479293457124347064676860394336058104220416016431474336197960
def BK_335 : ℕ := 1193950949816928767700555921251040474109428161842039935465007611176
def BK_336 : ℕ := 1181086004700517442039114955710428930029680361547860738435708293032
def BK_337 : ℕ := 1145186607050175642277333714985519521966396212029747538916068543336
def BK_338 : ℕ := 1088474348712895879740642152203397717315474991367578639595430342472
def BK_339 : ℕ := 117469883717668601123049332189517778487850204560316029134733272647905912418721367974387004734503230541420136683960411834956220867331347263395463
def BK_340 : ℕ := 106940490925432880803007618378803351706596909091168151405312205860023717479814998408809642779740648135899389972611361387590818203698753096190567
def BK_341 : ℕ := 95014590910966396130253685326583031621354119339721351362717211142317271946524951269588613933978740071304986375812883616057725711376600527449351
def BK_342 : ℕ := 1102116740586375978909117552762510451530817074796392630303472616506470115833866317657498600702885885024801533377284385063483600390792666056456402248710231555852639406422438866477429739613775475561735024647019958412565452343924937798006874467530451866796316950822193124905582894609228093490437399942
def BK_343 : ℕ := 923459718936917911049501437856073332483642436275700899233424571882935150304640265502980657925093647666580696606090323156077174434352253660724507203506262559727962596505989471661758021840584454043767805427836264788198148284048609453967390475436514520488797520904003434465498097335153171365076789702
def BK_344 : ℕ := 745451969088209014223495448950213197250855454843298852461126510532705636541615757716082732017718530491363972082042891956495784507940859255843809636330508914695632348419694752378729071922648955339217194543987571206200024667337542269058262258559732868322476943166923933279413407891336632650320261702
def BK_345 : ℕ := 574695668415720925187050314728857035367868546650981927663280713827154028193513633260712355006342645965972177502735751195794606591092574202339195219011776442610460438339540518485819604066541249306736179757037916478668096904817009939052266904830175976652782565711956709169354983716233804846752585062
def BK_346 : ℕ := 75065547305242910905348648624043947608180078639297736303937943477516549792113408129527356463658064897407595530785147859480595038021717291627531728216923535874673516605329577416396344717246562840411746442137811780121387424271202213445522637222935277175591006160014971634296039203771710718847378003579250284633624953059572920893180235436720169488497445394990474490338621904966834084053657374494762765322134155951457440733372634372445314112494300116631189696423634152457151249354208545926527102970532529277407549267352045258054424698723685767958157501976015654912580666528565478607143425386875500575429873285
def BK_347 : ℕ := 50234361899602967746726202127048292806246926624313086165634024338090716386463788037087125305472957820950790475783060132765142256786287654535321764565907732868782310364218055949840742248513586734551044253895037739006688722806401621105435322410459606970942053975402042672098764428332762922165668345445821916336490313731713989776864452039130666291577027587091963922977398113420907806805638819953472320819523423395854163325753195722274760365646507520528267483383268338496827115351905640620750712770070472454775586904302730812260680391018205596794185071080538100816110076521796363886941722737120876909940803621
def BK_348 : ℕ := 29725484922973619008811891889286781334841029562302769613120716199916427391050435775524797939423638748732445102523964439372840925102526013602010306236746110550914803347270662860465418633901059165224034858650580652945190516544236167743036009629514105363795984507613551128806469580578363792295098545767376102586329322906815201046774640711876251411840281278004563310978172548976761151951575006032419099942914512797214842057539788287636309109919599909713010147117591674178657398417671881734484103993874485748558768318269580878006848709720250282263392148382709843015590091010909879774426320312544233716942300997
def BK_349 : ℕ := 14239623678265115735054187727076101463894337986784811741376322652202348292827923542063243053555518661277560247449140528374163316431839422558829325781032695833881424122165704140335754310484849514477696258519948395034448155358237521682896160560809018647565543895191129980362774591503874142746343719517680879804868982126386478306511667509420372607619726835462289803854246997335275960207654606535751099285020636074311383425516082137772598234880881330942105778264243043175723335626224388998322251120400877872579812226828878814635450060979259729183057190340121110173540808058839173334810059080675415939950052933
def BK_350 : ℕ := 23789792795684322737028034093700611286146160857772582218988517896071444858543493523990384455123977795701282190442521320455648895411611303356855800904191661450957942235916417987973392703858493478047835607977602727737219757026715628444527938855923821381312966504465040956572597363081128871490568134
def BK_351 : ℕ := 51634623005027894055803401583907659718061585486210806343276075112994500473119109988682079014791550561762183085176973772200287563351395997063
def BK_352 : ℕ := 3094560938942767975530429267913544655841448092202211238209388552
def BK_353 : ℕ := 48005572755576263705610793867744319335582195476770111522914884061204000628715470633228932564482639316938390904893519568630062765076115811567609716698152345300918638418113939432320728298288651886555303752933200446020409608219894176084404698383940276605210278235318676210084913757052675913774269446
def BK_354 : ℕ := 117085036234774660296340019672149390632576677798476648492201157735226253402666830210343340979098456992823478885052996271952063233065675744962006156929180571089060664760207419673118591100405151190250204400253728664165786274376515256483125382341186208359646025640376972488019195681662504438928022086
def BK_355 : ℕ := 38869998334060128696550336893253451591272318338382467991922610140340594351092862552799332678267469790926668735335563011362678953259966742483845283739072768494980135897747453811196735550708623012979006121567640342433929714340469264648260710263464877225123321395592685486092466759502914590519969494425716510331897312126852815612684969740712253853380777327808199685793646686848863066702182570966847963013468997815485201915618423219205968086925856985982481388390297167048531647439982900961817013868358182845056361340649796747815588805390765091809525446556098888472559492922138796404752470620209392050163914981
def BK_356 : ℕ := 60230330828396951993407778378370321099901896380685814060626425917021993422963919687032908192385748848043910606199690849818112748490500007202486656737445958478670302027418124754963133163843025225837234359957941232106395476168394253902186097007846070825394913533018621475621884042502097906525006653126885542849966307767578804102394670571761775357552180012677235562441575672413123164216338456984025710045459888741591072367192364607213730634403008132319955758727094007143500088735671834176708580047586198728633690315233334730918024088703689486613109295673688741359494689949271899732640499252543989526776242021
def BK_357 : ℕ := 84711863345898770849525619946186706689861903672588565149938626461101961904014098275377289684815139441865845607018172771165107383232761737704176287525304121520505364716373683519052943598490011277376808611679264403656610203051142751471370396346376964742193477679013337807271432800524463617405897270402424592118793238540636905788581398130536992609656567879859342126216084391932229202442209968457352376321786623251164073472999401863910719725579820611411057571921333423860050658485395487329846145874918499534372559112067218443326043012237156876201052418135595128220788256411731546590049282320269019307543028709
def BK_358 : ℕ := 614234824202440125948367488344439509858672535677706674344561904064855955850930204359267020813648012839357274518070079298451034903756862680300446821149376431414645581057979569349383920400230311686750839151979701600796176139765367623888462835578088071684901970635720261722872110794979439938112098950
def BK_359 : ℕ := 767879600866924090289876526052182421135837044970262268079086652947742209350083464620337573219253235701834469796893231099440551270540537101835170273911488008226548036035551213149978182980705081062599286011360879085011779942074994885160806741094415344160147182956266295916158743397326066018891635174
def BK_360 : ℕ := 921417412964883041324043866117399376699135759251637554877899882442983893056049105284615297273466019640323648248140036722929599154097994509251716966789742367798810303439332625119435779734870475893444380896358255639590981733267726544193578146143648573438740813707075205996917092676029151774475645254
def BK_361 : ℕ := 1068805542107742706112368472414644127590628269086383033223949629003783910485583725840092415317938683059677184596568554119444348404572000280500280112829298219540711521069660049540855605495008767263807284817598743863527873893079092739378258497183014564006657508067499813432491021448623438044947645542
def BK_362 : ℕ := 89161643582988031132031593589929447722331888766052823129915237956802139033156294697163943171650218006798400640048200592338475326435531628623879
def BK_363 : ℕ := 98075896064775215246223530608073290730224765070359939622737881946426883868133796890612259756219956219053175103427136128752899287805976428202631
def BK_364 : ℕ := 901933950130748739501969893867518977430243632344009025417360786248
def BK_365 : ℕ := 951108062102790410907329635297248356226590264644107191880334322792
def BK_366 : ℕ := 982630763123650237815609830523167654683333448329911800088221406408
def BK_367 : ℕ := 995383222579710963701125105910801070844584660099512718527161220360
def BK_368 : ℕ := 984810976318203096095164562543437947650465929879950346675478458728
def BK_369 : ℕ := 955021558847856942650496068534011994857469246826849087937028654952
def BK_370 : ℕ := 907853307291972121582168807389781914166112738873410811831051542152
def BK_371 : ℕ := 97978255458358301210398539419932975598911202489164410895125210688722998059858721603183868942676991336824210214208076186789295538320717514335399
def BK_372 : ℕ := 89204067706211283892091343832133921783255215978831985991700624699294443707801143078888704610025042065784950808063091514117304802964824969490823
def BK_373 : ℕ := 79259890566637626389697926242306254746127681451820417126670572120267103689606122053053248914446697731742298976527916617702066925522251275038343
def BK_374 : ℕ := 919312736992329296410318366000505625017364959541073704847962348610557705078356527612349801444143867538173759828456475063257936542009351907485206436721277743789637170615239673795391427781822111706251786992660983070456434491627186920988992801484165979097632849250372575490285455642799298883451054982
def BK_375 : ℕ := 770214422184004722191415549456498951822790890414417401299639815895729977233419736155928959635511490531846363485582323744590268887149336588253450019029036317266417662186582848875475588291640799007823512386924859236914038409877572333529064922008928970108270875675398750961665314677721008485059393510
def BK_376 : ℕ := 621609766002275026119758634448614941383080718888322260690425035154276751583280492046841434699340410958383446228023382737989011708444296035406405750146910776934371021721283442274451773033086595025026029411371656302941154366148848321562935790775536512254777904712035461031564142647738123701116029478
def BK_377 : ℕ := 479027557955889559782217742021131751151553585418227932004525472085732794544526958421460417006564685899398584539612145107577548527510129970354445535243070519649228518790126383057705384955512525767914958032413957720590145678375793010193967227689147754281771724918759964205851232411065331802111347302
def BK_378 : ℕ := 62524349777045566454279520450129403969424867368232142367523853755119044707409499311370960053159986906049700059876187360957798500311647089102803534794490839537016695763757837778627885296022880142442781528060859404724704718965218243861324139014955454149040575397117309550801415114508401347112736007202101213670410901816064768457343453738924513668731898635938449370203672643773240414847196152574476075343037790851805078394853668811120213938952510792578036037106049155080226471622130150396376874730129477422942581095612669895277276828444215319201206867956539684255676634700431078018099830388469720212616287045
def BK_379 : ℕ := 41791340646091932610109888561832448537483924868432681889566050183085649721246534563568030830860069388255775174835090796476776947567281504300604762460095391213860988166161245246892511865772992820874899276811057768000672317551543773598449150039727036332026584246041033918748239192186999569666807274781123878731985285402709388987654626168906898463678022130385868257943757052389328576750352634554404460369522333057219882755844028259232100290492305880407876619518389277790214626652885345669358739092676451581789021130112730723847869159474673782973625710641186638164501489416478189844181047999287423390280580773
def BK_380 : ℕ := 24675447755711427938067389068522299814505970283654194434851406968725073763720702838506008037767958696278533902951049832235838911309107346160926094027635959346071769723155004800857726799974979159305566227127585226646924228758876505855029216739734165178358249819723262472651331164559699013969728465713885772970885226299389322779096574993096663570604594793470072567924320883120630009454075749277432119835587291386061518318610750311360811121160341519278437566510458486706128740035522767083377095518699372996333508241157144158451467672138346836887858007213535127294811780025653559006758818362624002913738353445
def BK_381 : ℕ := 65440797115318279555503714215530592641099536699232880984147833221156227980310207651731071611396813808649493866561110816796291694889421785951895449935156732213634246537660070657427684821460939096184974083660704702927753037974284383441017588953040549638912313531244823048761820704390187177719789286
def BK_382 : ℕ := 19412353665667135074655826342320902394571791041168739925202356308463254694373912166803665886533200067136510874584444581592523779999717942620090880933346581571292186154442394125724954118844263273204120035398535418891443210879403513439469606268502167313832966381641623975571013461181606910278657318
def BK_383 : ℕ := 36446601014538296920491449083271296144138217941863063305300408208523356152374633304152873670476251026364953216279476217106916991506902467559
def BK_384 : ℕ := 2766946445156979263115642521056070458983690588952020731570421768
def BK_385 : ℕ := 2855092286121651248102971598775544960081298784360410571216746912591693685492377638063897404579345653919011755026816425713526627820902095391015
def BK_386 : ℕ := 99695653833991456889907171097004178114374913927025952252163713933997333494062969643466854620375504997480379838148238289601269616953549204227192298053949320952510374054932368235954578802280731574028279128898527450619183295347115173511941694422969535083989437724024507416426396545569977828186066534
def BK_387 : ℕ := 180629473204551053569215431672158191939093829859303842022204545102488465713300089275095620096582290306848445841347062761336482652732933346810027693197038896296985618258168448658159324507021219174359011877719615613234426824561860670780460902024217167362166151977234295460028736918329018630308825830
def BK_388 : ℕ := 51048312561822715682058715717581473365387964643985450460248559196430197686593648760615619742462098023821828563504031074370739230455273488795494089456159892078469187779687792526549317229384855927390117145160805196702287199594419664704495663106994053320590914016117209252710378176182604923146193990726277658331541156537508498957961162233699432330716546527253419432820210328474888126793678084349690782737224412387307872388365714074100099027256446314959015329838256715462026602866502100719129697383248266698732521422312233424315131639352082721081064578590199045104913259897726673644579450805800850014278509061
def BK_389 : ℕ := 71733669783985851144373113758276407912180626436036621907668870539928046746020228704394817565437805411194525875868040344338631539315249921146291409569863665195223403322431109481663507789262354883456464145734997111205198749043822421746735816886145983643304060041978560785868947273179139418188726952905858404643205942142759805817761772279795441631003731225586274663158969166644155919246973271041595603066642045626704531940694784530284797633186090464623696148097961133154794250304778470862697293752165627744179811047178690784339800457268094359456262553517252927644480808803873915275876747427636238701127921893
def BK_390 : ℕ := 519878043197026778410778887771955193025257143251323517828185644808416186177900282709067429262904939529064064776357476082364653773233267215998494603325535607389135734118822173946145915696399714653942498124770140391396276322485128186894435631376522505451489329010318596527029491883275867458058486118
def BK_391 : ℕ := 649717122713951064176308355405320337841872788854892678198294061166239043345509779739417894487521127092934397920811249018741434183545280080668864452704078128083952027152023462359540046466306964280023578420043723351565220206369074771951174912712502931810036803727575760927471595153297501497851547366
def BK_392 : ℕ := 779497262571795756716555816480273855249264168604789278624033105746713234020392491975994642219579104783946327564419513914590125058822403192670097424393774834797827520634219485946546929933173300592875779732190510426652667884726593922249421822182534120118057365225247410699114306358155078144325195270
def BK_393 : ℕ := 904121273728849240459701103947753419705059723861843395621505508309061714059209996304523928541511188960881579194493417948047645429767019596218821264383085000753849007409402446067413587193022882715619057548968755337203003209325148688803527278563385026971583722174672648573654882941391757857545847878
def BK_394 : ℕ := 75427438598578908923603274891355195270845030878194719485183986388734545831096977533264861642644872964182520518820996053529236230858987778767559
def BK_395 : ℕ := 82972233888111180174008564683106005644912225990341462814866394304810015045015935233813591309019660048481359294325290720449020611505935706529447
def BK_396 : ℕ := 763172841304650059108952203310118258229338257856549893223713968936
def BK_397 : ℕ := 804862840200918125526666400655998613177489246113930370399797492040
def BK_398 : ℕ := 831636235830701034661050543059718094090194773251822634965954743432
def BK_399 : ℕ := 842536498322895743509616468843333295269004493360093764388232619336
def BK_400 : ℕ := 833696330406033693947936552009468906940065025182277550665229834888
def BK_401 : ℕ := 808580491371085008175173025611372174633345385944005318388600376552
def BK_402 : ℕ := 768734453882678109150998737388129791306976431084155544553114087592
def BK_403 : ℕ := 82964977130686210811673212941124760409776593648996883641652707264067478671161414018594129791262349279693850202884795104552656996206893293483719
def BK_404 : ℕ := 75540895216581526255749817431677553181732279337346074561162814280069798792828159246305170991924636305596090772632792699913783585922572633627527
def BK_405 : ℕ := 67122451409721692012212376850678791713947701848987731308474103013859770061308416209086249101550344064756173148919581548263032746181334797459527
def BK_406 : ℕ := 778490298769072603729566345415745351644998664239492425067052758838668506377268163016928323035966854607048358629665300804817606860277829566519134454074368306426377513619695153997712822561759489857121083151768980901754747209193472173665342390698964125830695494449930276638001204574418644929838509350
def BK_407 : ℕ := 652176372199676938770396176362947366809982001129859082717151743708157782802096121909842280734456342055303013316529145320248091049313746413377972198105165234008884768760624059726728946235945247308103753495972692210118965201140077529406846272097332247441779415573832683180225512320240358855991436870
def BK_408 : ℕ := 526246333039838527667788468933253088383831566768776944613763591718243558996740638443333328586901534253609320029264606748855291655044428842597902208637502165465641212762759845835917076353088173103183180914843706809198185626870886903909377445226870635950654122906278754891799157701783418543155968326
def BK_409 : ℕ := 405397890419220448241470073061601351307829623848459746618452061668356190845864867702371857402566458235563499586408820162281639410460244369656708480843165862436068669122441070843072642612910799295285280292215527891264789738872048871323557436013337384102115123189007139359736213085818483294296785190
def BK_410 : ℕ := 52881229216923049345608354546205052752662639454451614929724381619979737131317898884430297746155472141777771021305267902836561713497620391199357767202301821394148816255055859787411940002920712846788904311442806674300972676826670599804985942538935409964891975854756660041499655773591240819483159935964415469494948022320253376924649963842748359573733226076612153437520449254393707106165972061239908373784029054254079178759361806810963541654800669268316857073736933693353416600064287508145394959838965379647022930716726745917087884810493411001030129731530502936118224941982861562759702604261262672122086200805
def BK_411 : ℕ := 35309503773550598782811435719340876212891096217126337195868175936202519804903806583721317554067971412720896084903334731069553989001049658525393651181716272756581769428037105427462376816356153115335384723903696618429475557791967884990247152028429010717534943454881998923533078233560278798514109319372640296679444080698622697865310909614467434567364782450299892426332121373195496207811124449001826862938772842232479457253938533444606781815163276875837757163816985623338172986693262005415459549322913467664462328799047761578496869666376382149152029441552655022344920510221140077337954732252911825448303036933
def BK_412 : ℕ := 115727552976165860676526537977494449588070972383328024040483033513734065540177397734610676931556359298034093668972313886824164894990337433151762429517680432058862232556478171186857761729852196233836595657499516760115105910673204590130451634055008190097184240229767321530865357792613398970482635654
def BK_413 : ℕ := 54975421339672391041319927502886306592149584177010210446658860587834638260325891296284768843594110566182893195677698474883472393282477960251443566729504443347005272346463227351894313758660293737990925499570193435506239610371093258691146127832672553346746882039122577997259031526765272309706396678
def BK_414 : ℕ := 1202505244656459990543895642699986586678392203719314982953450883500708568295386064455249803692158318314346219223431506617095826821305522011815
def BK_415 : ℕ := 228386069855759506498452617354890597768744684769667189875707432
def BK_416 : ℕ := 2481313207776708382810923665066508268050833865451246678842540040
def BK_417 : ℕ := 2475694101383713684737758225505994322983037921679379722509676198830445551756267016053223366605563725365520144423669473194680217386987222230119
def BK_418 : ℕ := 85902526191749163992379089521998128457512184287945057458288569975833792333044528311962005410412703424874251414616912782369007295974112723211000480806602698932842760605880015812070971484825407555871209509910925503286294929465432912383237559311488680237504685391106341079579498082338945415815876326
def BK_419 : ℕ := 155250492562806752017834741985217177288335750810976861501940188250853567598975828325861451646106050632541958482610617375847532926500903446171881366899536524662982806632667449540750191798033936349328716960527231872226114426876842790525231512659205348802749064742501334869042251359046831642818409574
def BK_420 : ℕ := 240763829894761392596152675617669337233579485523457879486122311818267478053961586815719826421221986132565843227698001757740803735515168140873358399046003606449110156454498313711318535329218567324831951748753443228406171141269888932490861619793390476295032481704408781642995037859376264871988085702
def BK_421 : ℕ := 61523939998332784769423925224552438661865859168153708796653554673144255874445963393484635199109897527673879371462826805371244206102175027292607539080598095210469250676933766397599435296757155651211169043566855594766108993593133501369833500262057956811720202422326678003156385728844215760897865175688592884556478334491307123282475872175814350478117471688873356992148121617125883531850412209533508958948783659735392532509605522689008213327352835244487588197582383857189223324636899045316017255488573483407997550918896150499291489684519388045489654177437142619097639268357964551594928724475023450440342842853
def BK_422 : ℕ := 445702638076166533726272540969596139160160606985978311555507114430227521028419001590110093206032968794981604756897609550341029129833079625719094923404173141712116126909041410159038450952962908424192668815242016137190699627964610079465809827105938084659954135304703359511903850757317231958556460358
def BK_423 : ℕ := 556870319643003250261464878755131600479659706163204210303217891180276184587432527926160396801501624948904125895646388446593298319959277238087930747941274839078601095721089502585315970295456196894200259422435885333732587253554031555260168775998272475571801800427988301209212702246950301357341711494
def BK_424 : ℕ := 668011182105738390164213978385650667718535302312194387331873421635066523930212840819369332071127324558098715814164222144092976644472374345808352452282412189942122693544608779823374944782210764796525516356197284123659976134655024424277162243626015872114303928882431051303009115617264902504226938726
def BK_425 : ℕ := 774766497337360773997322833883961389251754487671749151407640380108580167518130367297646220087424664287246039862660781909131694551894258533441049767508288044940355999518736675069389783823536354175442660838922616388045725869800340426375291767980320642000876065339173069759832938060689464772373031206
def BK_426 : ℕ := 64638849302475682675723056461632419566001550306449269462005701499483108783144082709936511091268341853175660575959958246718441078459833866678855
def BK_427 : ℕ := 71107248773458655179099027481305321808865982855248796471207223181791324678444751221221771577807003991422689814135465119951792620942496546888775
def BK_428 : ℕ := 654139483702385155977897895505942919538350244220400062367610856776
def BK_429 : ℕ := 689932622576498593535275176636372071618545275496752359187957064072
def BK_430 : ℕ := 712954621340956931116642248985398951595355322759888390635535606408
def BK_431 : ℕ := 722377706035488593658801229706150392200427628930434212487760836904
def BK_432 : ℕ := 714877724447682914964659851762931786339647813625264016865494680968
def BK_433 : ℕ := 693416062526102160400584802505953295128079452796642176792939305448
def BK_434 : ℕ := 659310409467518963122712556914146832548822623518793033391385260520
def BK_435 : ℕ := 71156022559568099029508151195484627619326197188707097448483699530307929056626702030299287840181247767905804742947007684274231236583293206253031
def BK_436 : ℕ := 64792753041750406951526386817929574972361309926535338822481077923361905721231146061439491100060405079766055013939041671017791620960037110822855
def BK_437 : ℕ := 57573930383422234550656971925065880141136266446330441559954324965870524580977346171490814020712099971483880940790525123514885438891058815085479
def BK_438 : ℕ := 667713053462587782344872322750425567518158777830677169698328448671115151045274449612138597802794723087204640078323470649305908143751431588773398429881976867444712373818730126978895463477108150817229451692028111164118628524769819148079164875219459981788512854520019144299175427750276349239280105958
def BK_439 : ℕ := 559331752078532846104128420922605671352727623666776920880954609266950230760539351377986293264678107758847724705722340720123085454814834290401373673446762618015123186530088935575260329147316630171495273988426879210039244857285935161909016846685569416640841435287034953348806914853617882713549424390
def BK_440 : ℕ := 451255440041790156337694564399894189059022892247167137258328480848503483885498880827383898683103498469061403322151968000723706735240269098961368055467573364276305149140025431496805595223443001563801974695341897594210014581638383390131816291535855705074399548056691691573849804496042171001991237222
def BK_441 : ℕ := 347523511029771276900451510094911456030061412286185417688919649428269803672098473489159039297120631330107534930745867609570203665378733166339783422194836256751881393787008070842081545333672881664851438230187856158206752744188889916183020306028660108169887775999060858502627532837417805452016624422
def BK_442 : ℕ := 251973903588599238969335732557467657397605138295548419572752315965060694426997352138857878905851855566170381720201171682408891994112406942003796398104736503036139886015224394804188698140321096567798691405436111202545168171633738068483077704266936173853695319896178985920430948719814964504062232486
def BK_443 : ℕ := 168097155310440051822023955941754243667807443103466847951029140219480270613572156732775625140643234680476188026944363767338714143581646510371286547696761926506348951265513186905613180637484546423183370217163443921909544375482479332981205553522036394359396310018191791376227652794626542594576298758
def BK_444 : ℕ := 98906673213352087543987457794298305572867985814614639212023663001107508055677965187277184774083302987875895220637161477236489187344380152326921343626708935415588792689162046658940817700290143123346483410432408896877927945714649643836703844758598311446280356627404720386069052383168847435739618598
def BK_445 : ℕ := 46827403273993853686392641658239823666217871415481566470688442600851584150083376694675858373803508220920035896191193302930982144278497160713681656874161385581655644104677317410497272272116020081655238693115034819338015335059857020225262283557437918082357006635378094819413869737110128390027432454
def BK_446 : ℕ := 1014573824049620134084185062352733153053902927398189201841240788906079668118603568861696113603093655984580720710725599159107294218958656588967
def BK_447 : ℕ := 169732831181051239025779337834347967588677744603192168726686120
def BK_448 : ℕ := 2233041279925599330569608525975128021000590959763986806183297032
def BK_449 : ℕ := 2166723681688954102889508738296788809206952190857154667707910127537550963694659335285336984931548549403506073714506713804396660585217649214119
def BK_450 : ℕ := 74780082364296154816654190979968782480297380926549852164555342023780368324018905203040259196941558950890612456303176888158729599206332854085262372520310626920560639166043295036339675839379238758996110681826192716750653840444942810366453933304918537582446103046842193745712592200306077293352340134
def BK_451 : ℕ := 134862983796313632291470371344599352614555491859914749917257157871429358936304403930612854044403098165616929251152127886264701387900383094674145983434171139651568359769853024882011886359177731109260911526016819484880202603991850449684142681983706710012604015119545762348080426171965247447732207430
def BK_452 : ℕ := 208911465947544222614836430236583898417415186077338839700872605592178954503891013130523427272855956613409857555393583122143480529035903465290462621211681175187300228617633604217607477786921789828928656358180112991698175558419554812273026008928597463881673643123166190404833135335713141115995148390
def BK_453 : ℕ := 293881560495196991520671082127238020053907717171752934795148986428831389743389122232281020959981056352626560089435204569103609946492954178922901239291480628244840038431818455846033367457135910371728241289776569045834152489741607368548374728721619570262323574913851615318817332102746941652999272646
def BK_454 : ℕ := 386338551005787117039460254685529977232504221266896395183716410857851444459988219855234836302679706180330829525602799855848163923171924268064934096791127484722851400704831835892382118587291689700070405808483324865772594643099170117710620232078536485438612831747040433340299682775048927682260953318
def BK_455 : ℕ := 482592315856157434231910489872137253098044176517244756135202585357431169051205798872540825207154014827514348873146252392391222829538370729071485109903313817705088914312780954461550484645849210212117121434068611848007014508769584145100034848477858778874558120989275023691001937754534432691500496902
def BK_456 : ℕ := 578839531855566183769380016601687622712727582196725109200503468577833113515455793880644888873408771540976542386892478785276464592709770387096339091502966660054344124797548498335279085165914249392431317892141031738565438241253117441272619473068308149250975095972258779484804055454030776057640852070
def BK_457 : ℕ := 671312114868742419554958721619759044167423729671600885713589780779525667680233625318101869661466435298034077979733824851153580134373555110857297160872386193465700024805539738674005297842637829760794042732048269383934394393596738017207989468191670271693601485839968242946179222355035936019050633926
def BK_458 : ℕ := 56009936259852294319450177100065335923715141152224963410330460315355878025271712675549936859736609764743461631792252481866210874899585936081255
def BK_459 : ℕ := 61616944621693491564150944001296184339954333571733857586870375635398920476296623468875161121716138876232721006516216325975214809558390164392807
def BK_460 : ℕ := 566909664091386769430639059635078122189958406338599435493021676936
def BK_461 : ℕ := 597974387769073157595200495343904522779550414820382981518477711336
def BK_462 : ℕ := 617981569894441452704206679530746571486997598055508477243186502792
def BK_463 : ℕ := 626208088347380928180070239478799839858824479484004647835223324008
def BK_464 : ℕ := 619765873727320879624441333733960162397080965482326756971841229128
def BK_465 : ℕ := 601215180073490626525178531964907545404517641227372968481637366056
def BK_466 : ℕ := 571693116919874003341145665743585912914595355425327666748239754632
def BK_467 : ℕ := 61700327560461336545809572682281442584743311629654936180914213304866976523683664317394836736475946474028498222425348370387865849250865147235367
def BK_468 : ℕ := 56185656790227018796455329279152585233788021818260091461529014126488811342480598292606035456333871303178883242149195605155789448618653567911591
def BK_469 : ℕ := 49927098566400226100805518072779876911703146562323106335426795063226296770516888623436126759799612885578473474701725013734534534694261594006343
def BK_470 : ℕ := 579003876833827487543072623530610857850180524413726832289962435026625508111033891260601300479940033190726556965720037126296537350230504100734472258397616966059858757484197187671717274438094506668076566223219231732907398643749685046117703954928605340540355984199524275114645758604512239786478179398
def BK_471 : ℕ := 484989819031329117946007534958226540294014806217419349660449496950123100723005949839434152750908168286413058089771371865860420463588151449146937168573493556821555761029622634648424595658498919729565164315391990969510125991197446544954491135523966842145472017799114900430314236919829872441516580934
def BK_472 : ℕ := 391221499066947728952550655888066506193349210708577258672440608794538677847280223642030591348695259794862788677428106659552566344401628857269573685859504331647419007917380847794919356184771061049117605184069575488584571765128549667995459066074919048213559284263368278382104819146577092036150988486
def BK_473 : ℕ := 301210972186186791471337138011263823985959440602779281790762094788185525481521449698237702058929319083411061332237258382306288493650266220373524597378957541688971415529677830293631510524954389523371898734520001031845388136891937424671508848018106630661200983426882754847819601269965094610292678534
def BK_474 : ℕ := 218296281307523808264495611766644756863777056615500691087876192400427313277613905688629603210060496065795038719927204530573701720258411856351117031866780605154439000738253262655683575686616547726064064679342766791107778232511689725006809269029767784016784528550601419459822336448873345724624260230
def BK_475 : ℕ := 145517028853083425027399811511525514050346824781221132192384987474760887934819544431152637923224653321143669972845097020319128689642303436839275807831344437266446662432314454093985930106581596313887155535451207113744023173625788123924712326276934631745995979674971984919903743145704069562062067750
def BK_476 : ℕ := 85499927780860538531398367916884842176418605522653855874783191884721106657289980928826605432630046443511582076220189950228421399546227898962046796006439036014162008495560412937978278621220552415072896241543660728812673683681380560140886962739007434239922514156755788073525178691091862556047171398
def BK_477 : ℕ := 40361192519559460459805656581269627808896640586036889249983787612386025573660585576477971407872255585824406721584155175263240415073349211335045855317819296046672083639050869688193306146444409636441360402140940009007142013386339170856483073063371775601781798755248406854443608550630880464401805862
def BK_478 : ℕ := 867159301301243543212692089888305228729263515252732272351847396820841043530712161959898606630522008939062546290647489969591222201410871506023
def BK_479 : ℕ := 128755911007877033043187984551151089743699057429115251357405224
def BK_480 : ℕ := 2017510714726921957925843551557915102381002335172510601625731080
def BK_481 : ℕ := 1911853321931627997627967549874910262126305250092976482921139329042998421221814894521693389538856675631704524500414218635297159911374693455655
def BK_482 : ℕ := 4685516412134139799621896396878171538561666653065215698955894517315171833802958861712474500497108488942937185023167991898747271811353094788039
def BK_483 : ℕ := 118239505114431712540708856640428097803937540638157873488357948472639517349060592161683322055099207350818653129543798298766497213520348705278615679966661918190282593402404404303475393506300817464816509731758184687094537646239742365630200238099768902291603417909463165388786377231625274352326105990
def BK_484 : ℕ := 182983629220507098517117777381386534122892229200445199884206874482149711636084645431808290000147304694220672250144169872160638047367870046975122930359076394574693534577250809625196944578408667299452472018075620646854489766309594713637232862510887529723073187125920363579936673383898524802845963142
def BK_485 : ℕ := 257264751507936471494961976476332578509508251755463665342253740309682940384850147211765240486863610974366724724390076233578080747226423370939714342519784152720900889863956676711423459672074139352776117036250429045718961723236596866225079936003956673064234350488554131317513767046802154223902745286
def BK_486 : ℕ := 338090047061870236083755924812549140050024722841676545013303933708880092092349102167589031829740042195629257037606244831029502685275202058206334071971575905714174115070929382228074450029894886663677112722073924318222215762325979083344252143591502683366275948094191474459658373490777458246512441702
def BK_487 : ℕ := 422241847082533682969843401037461427848370634521153285815092750276704185467034947870767224562878320590712698534016078783994116661734767927647214715077022188274627906544124584881530638584411592851878452800292270066832863000169901973048571647978966800283510018703594917256102678849081357353004662982
def BK_488 : ℕ := 506401443354456494762477247032632339370720837155132678822824874336098268730653056723675940151444889457258364791059578970381053370433354438209395575682503928330818397157439281929716256427360203411454189806889242021879217512178826981040212609494331472928084334692768760446147976763923300379793386214
def BK_489 : ℕ := 587277882316477322979635801151959381860741859198203972265036494552481596940272050442675446668862968183003850856339316246796351022536308182529822535394382207971162952709566610593548576639282617364517695322190085370530998160632720905894238879710453517570090442132369827294525823151739855040155813126
def BK_490 : ℕ := 49000419895331456591835498278798932232032742975346726243430414314794844379030266507654385110922291514439156372456638348436192782935052729102567
def BK_491 : ℕ := 53907360456604056280073388266974486337243671812105353889204732694362897925123203771624846143544334628370251034109124394055803261228001436790151
def BK_492 : ℕ := 496034255562324377356063419571915640913290777487318227622143866024
def BK_493 : ℕ := 523249559154015765897722528730836967063865189151312645208270203464
def BK_494 : ℕ := 540797322601989801223058250755688403018783146531545837396480550056
def BK_495 : ℕ := 548041198440548985951408774534965821937760585776536627432491935048
def BK_496 : ℕ := 542448250576968485983739101565905424299488246829903912448360357480
def BK_497 : ℕ := 526254332432764963386810253446640893959740199385636583085298368744
def BK_498 : ℕ := 500449920445330771857620290255906958472998073343359509384359085768
def BK_499 : ℕ := 54011629832920984213164552927400648603947709003887468282885733310212626089732111281397243647121128376525105811911497730485543702143306279281351
def BK_500 : ℕ := 49186444091420698345404734232984138005514536379423619578656328879945381855901686734356408339180863121995133239017179505019267439119946750662343
def BK_501 : ℕ := 43708522287086441558204740128588478070447185338464627347099837012135323952638674823230294368771951590030318229254688451983715703481841757820615
def BK_502 : ℕ := 506867035479166640462007763038345379730789756276985793891220686317819311540475099359486348206708168346509458654514166346611345938095114191654172689709258710212590359188335996501661449306814929790487144811199573418682435871904938774938857099459429177585403652697361589218932252331976837829043528038
def BK_503 : ℕ := 424541429342147936564864023254259583203017788448205591410329198688641549310585681480942803894136029849094948774497368852218311562525398304831764742191360749046327073982374924003542699170690296845766158840598129593250190064688697648205112702778573914412019254817123370302589701201494241726747425414
def BK_504 : ℕ := 342416654636277688621955181604918860274705547495389638260228780665012582076655881117612661290505226391182107474527481255906133890593879078492756876796842150098528612529260287119471740642216192852805114583520095134845503236486175714529625351564430602052700113881296744639191255787372424926898693158
def BK_505 : ℕ := 263573789840118578951550098824666627898628712959351576859541837849043692279396007456960265135761190520417038522290683306845190253443288266018662141092121027821282251735696472145246250906485325293809382881158199959452959545399518403724252427529171040708252976784677956018802014271638240025477165382
def BK_506 : ℕ := 190943913558936784333460242587050591863713607074864313943123159709836740590204075938421900650236377127741028816762728571063718851276031486340384095837666613259182723210085519542212091245619870968499369675615485910923584850174986086782984756995268014849258692575575429891935578594433078316633880774
def BK_507 : ℕ := 127196774057409603450445223953897808268385892499005029038710454549720002521393559964148015053864221082630312906990974658614020170048462415606141141445757923378459417317340881933179399367691828732700140144397941310023629013751366987760118000616943560845508835278898055918857035537617641761071900870
def BK_508 : ℕ := 74642556494367019825292438590359146870101761331509704256017837955364214172833086664703595853282687956851283083835544586350032549233186257448493067522923961367011171729403371804168201741480802449524895786675286491728610484923981631107963029804739098853457615065076015189456421321146298629977595718
def BK_509 : ℕ := 2620178010540808164290312448846605897840831288851767965837006160005693570089785075321827001564006108923006746536302595200470402079942744932775
def BK_510 : ℕ := 749492833869160975612755389369877843857968587986222761228906124288858646297773338089042487244640198151519663757578491128940308492971834063879
def BK_511 : ℕ := 99429291665822710037884894138984568777400101333101757914430952
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
def BKs15_17 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_31 (Nat.beq j 31)) (Bool.rec (motive := fun _ => ℕ) 0 BK_32 (Nat.beq j 32)) (Nat.ble 32 j)
def BKs17_19 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_33 (Nat.beq j 33)) (Bool.rec (motive := fun _ => ℕ) 0 BK_34 (Nat.beq j 34)) (Nat.ble 34 j)
def BKs15_19 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs15_17 j) (BKs17_19 j) (Nat.ble 33 j)
def BKs19_21 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_35 (Nat.beq j 35)) (Bool.rec (motive := fun _ => ℕ) 0 BK_36 (Nat.beq j 36)) (Nat.ble 36 j)
def BKs21_23 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_37 (Nat.beq j 37)) (Bool.rec (motive := fun _ => ℕ) 0 BK_38 (Nat.beq j 38)) (Nat.ble 38 j)
def BKs19_23 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs19_21 j) (BKs21_23 j) (Nat.ble 37 j)
def BKs15_23 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs15_19 j) (BKs19_23 j) (Nat.ble 35 j)
def BKs23_25 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_39 (Nat.beq j 39)) (Bool.rec (motive := fun _ => ℕ) 0 BK_40 (Nat.beq j 40)) (Nat.ble 40 j)
def BKs25_27 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_41 (Nat.beq j 41)) (Bool.rec (motive := fun _ => ℕ) 0 BK_42 (Nat.beq j 42)) (Nat.ble 42 j)
def BKs23_27 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs23_25 j) (BKs25_27 j) (Nat.ble 41 j)
def BKs27_29 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_43 (Nat.beq j 43)) (Bool.rec (motive := fun _ => ℕ) 0 BK_44 (Nat.beq j 44)) (Nat.ble 44 j)
def BKs29_31 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_45 (Nat.beq j 45)) (Bool.rec (motive := fun _ => ℕ) 0 BK_46 (Nat.beq j 46)) (Nat.ble 46 j)
def BKs27_31 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs27_29 j) (BKs29_31 j) (Nat.ble 45 j)
def BKs23_31 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs23_27 j) (BKs27_31 j) (Nat.ble 43 j)
def BKs15_31 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs15_23 j) (BKs23_31 j) (Nat.ble 39 j)
def BKs0_31 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs0_15 j) (BKs15_31 j) (Nat.ble 31 j)
def BKs32_34 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_48 (Nat.beq j 48)) (Bool.rec (motive := fun _ => ℕ) 0 BK_49 (Nat.beq j 49)) (Nat.ble 49 j)
def BKs31_34 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_47 (Nat.beq j 47)) (BKs32_34 j) (Nat.ble 48 j)
def BKs34_36 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_50 (Nat.beq j 50)) (Bool.rec (motive := fun _ => ℕ) 0 BK_51 (Nat.beq j 51)) (Nat.ble 51 j)
def BKs36_38 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_52 (Nat.beq j 52)) (Bool.rec (motive := fun _ => ℕ) 0 BK_53 (Nat.beq j 53)) (Nat.ble 53 j)
def BKs34_38 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs34_36 j) (BKs36_38 j) (Nat.ble 52 j)
def BKs31_38 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs31_34 j) (BKs34_38 j) (Nat.ble 50 j)
def BKs38_40 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_54 (Nat.beq j 54)) (Bool.rec (motive := fun _ => ℕ) 0 BK_55 (Nat.beq j 55)) (Nat.ble 55 j)
def BKs40_42 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_56 (Nat.beq j 56)) (Bool.rec (motive := fun _ => ℕ) 0 BK_57 (Nat.beq j 57)) (Nat.ble 57 j)
def BKs38_42 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs38_40 j) (BKs40_42 j) (Nat.ble 56 j)
def BKs42_44 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_58 (Nat.beq j 58)) (Bool.rec (motive := fun _ => ℕ) 0 BK_59 (Nat.beq j 59)) (Nat.ble 59 j)
def BKs44_46 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_60 (Nat.beq j 60)) (Bool.rec (motive := fun _ => ℕ) 0 BK_61 (Nat.beq j 61)) (Nat.ble 61 j)
def BKs42_46 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs42_44 j) (BKs44_46 j) (Nat.ble 60 j)
def BKs38_46 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs38_42 j) (BKs42_46 j) (Nat.ble 58 j)
def BKs31_46 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs31_38 j) (BKs38_46 j) (Nat.ble 54 j)
def BKs46_48 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_62 (Nat.beq j 62)) (Bool.rec (motive := fun _ => ℕ) 0 BK_63 (Nat.beq j 63)) (Nat.ble 63 j)
def BKs48_50 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_64 (Nat.beq j 64)) (Bool.rec (motive := fun _ => ℕ) 0 BK_65 (Nat.beq j 65)) (Nat.ble 65 j)
def BKs46_50 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs46_48 j) (BKs48_50 j) (Nat.ble 64 j)
def BKs50_52 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_66 (Nat.beq j 66)) (Bool.rec (motive := fun _ => ℕ) 0 BK_67 (Nat.beq j 67)) (Nat.ble 67 j)
def BKs52_54 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_68 (Nat.beq j 68)) (Bool.rec (motive := fun _ => ℕ) 0 BK_69 (Nat.beq j 69)) (Nat.ble 69 j)
def BKs50_54 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs50_52 j) (BKs52_54 j) (Nat.ble 68 j)
def BKs46_54 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs46_50 j) (BKs50_54 j) (Nat.ble 66 j)
def BKs54_56 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_70 (Nat.beq j 70)) (Bool.rec (motive := fun _ => ℕ) 0 BK_71 (Nat.beq j 71)) (Nat.ble 71 j)
def BKs56_58 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_72 (Nat.beq j 72)) (Bool.rec (motive := fun _ => ℕ) 0 BK_73 (Nat.beq j 73)) (Nat.ble 73 j)
def BKs54_58 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs54_56 j) (BKs56_58 j) (Nat.ble 72 j)
def BKs58_60 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_74 (Nat.beq j 74)) (Bool.rec (motive := fun _ => ℕ) 0 BK_75 (Nat.beq j 75)) (Nat.ble 75 j)
def BKs60_62 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_76 (Nat.beq j 76)) (Bool.rec (motive := fun _ => ℕ) 0 BK_77 (Nat.beq j 77)) (Nat.ble 77 j)
def BKs58_62 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs58_60 j) (BKs60_62 j) (Nat.ble 76 j)
def BKs54_62 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs54_58 j) (BKs58_62 j) (Nat.ble 74 j)
def BKs46_62 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs46_54 j) (BKs54_62 j) (Nat.ble 70 j)
def BKs31_62 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs31_46 j) (BKs46_62 j) (Nat.ble 62 j)
def BKs0_62 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs0_31 j) (BKs31_62 j) (Nat.ble 47 j)
def BKs63_65 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_79 (Nat.beq j 79)) (Bool.rec (motive := fun _ => ℕ) 0 BK_80 (Nat.beq j 80)) (Nat.ble 80 j)
def BKs62_65 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_78 (Nat.beq j 78)) (BKs63_65 j) (Nat.ble 79 j)
def BKs65_67 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_81 (Nat.beq j 81)) (Bool.rec (motive := fun _ => ℕ) 0 BK_82 (Nat.beq j 82)) (Nat.ble 82 j)
def BKs67_69 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_83 (Nat.beq j 83)) (Bool.rec (motive := fun _ => ℕ) 0 BK_84 (Nat.beq j 84)) (Nat.ble 84 j)
def BKs65_69 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs65_67 j) (BKs67_69 j) (Nat.ble 83 j)
def BKs62_69 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs62_65 j) (BKs65_69 j) (Nat.ble 81 j)
def BKs69_71 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_85 (Nat.beq j 85)) (Bool.rec (motive := fun _ => ℕ) 0 BK_86 (Nat.beq j 86)) (Nat.ble 86 j)
def BKs71_73 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_87 (Nat.beq j 87)) (Bool.rec (motive := fun _ => ℕ) 0 BK_88 (Nat.beq j 88)) (Nat.ble 88 j)
def BKs69_73 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs69_71 j) (BKs71_73 j) (Nat.ble 87 j)
def BKs73_75 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_89 (Nat.beq j 89)) (Bool.rec (motive := fun _ => ℕ) 0 BK_90 (Nat.beq j 90)) (Nat.ble 90 j)
def BKs75_77 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_91 (Nat.beq j 91)) (Bool.rec (motive := fun _ => ℕ) 0 BK_92 (Nat.beq j 92)) (Nat.ble 92 j)
def BKs73_77 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs73_75 j) (BKs75_77 j) (Nat.ble 91 j)
def BKs69_77 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs69_73 j) (BKs73_77 j) (Nat.ble 89 j)
def BKs62_77 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs62_69 j) (BKs69_77 j) (Nat.ble 85 j)
def BKs77_79 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_93 (Nat.beq j 93)) (Bool.rec (motive := fun _ => ℕ) 0 BK_94 (Nat.beq j 94)) (Nat.ble 94 j)
def BKs79_81 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_95 (Nat.beq j 95)) (Bool.rec (motive := fun _ => ℕ) 0 BK_96 (Nat.beq j 96)) (Nat.ble 96 j)
def BKs77_81 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs77_79 j) (BKs79_81 j) (Nat.ble 95 j)
def BKs81_83 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_97 (Nat.beq j 97)) (Bool.rec (motive := fun _ => ℕ) 0 BK_98 (Nat.beq j 98)) (Nat.ble 98 j)
def BKs83_85 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_99 (Nat.beq j 99)) (Bool.rec (motive := fun _ => ℕ) 0 BK_100 (Nat.beq j 100)) (Nat.ble 100 j)
def BKs81_85 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs81_83 j) (BKs83_85 j) (Nat.ble 99 j)
def BKs77_85 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs77_81 j) (BKs81_85 j) (Nat.ble 97 j)
def BKs85_87 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_101 (Nat.beq j 101)) (Bool.rec (motive := fun _ => ℕ) 0 BK_102 (Nat.beq j 102)) (Nat.ble 102 j)
def BKs87_89 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_103 (Nat.beq j 103)) (Bool.rec (motive := fun _ => ℕ) 0 BK_104 (Nat.beq j 104)) (Nat.ble 104 j)
def BKs85_89 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs85_87 j) (BKs87_89 j) (Nat.ble 103 j)
def BKs89_91 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_105 (Nat.beq j 105)) (Bool.rec (motive := fun _ => ℕ) 0 BK_106 (Nat.beq j 106)) (Nat.ble 106 j)
def BKs91_93 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_107 (Nat.beq j 107)) (Bool.rec (motive := fun _ => ℕ) 0 BK_108 (Nat.beq j 108)) (Nat.ble 108 j)
def BKs89_93 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs89_91 j) (BKs91_93 j) (Nat.ble 107 j)
def BKs85_93 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs85_89 j) (BKs89_93 j) (Nat.ble 105 j)
def BKs77_93 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs77_85 j) (BKs85_93 j) (Nat.ble 101 j)
def BKs62_93 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs62_77 j) (BKs77_93 j) (Nat.ble 93 j)
def BKs94_96 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_110 (Nat.beq j 110)) (Bool.rec (motive := fun _ => ℕ) 0 BK_111 (Nat.beq j 111)) (Nat.ble 111 j)
def BKs93_96 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_109 (Nat.beq j 109)) (BKs94_96 j) (Nat.ble 110 j)
def BKs96_98 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_112 (Nat.beq j 112)) (Bool.rec (motive := fun _ => ℕ) 0 BK_113 (Nat.beq j 113)) (Nat.ble 113 j)
def BKs98_100 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_114 (Nat.beq j 114)) (Bool.rec (motive := fun _ => ℕ) 0 BK_115 (Nat.beq j 115)) (Nat.ble 115 j)
def BKs96_100 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs96_98 j) (BKs98_100 j) (Nat.ble 114 j)
def BKs93_100 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs93_96 j) (BKs96_100 j) (Nat.ble 112 j)
def BKs100_102 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_116 (Nat.beq j 116)) (Bool.rec (motive := fun _ => ℕ) 0 BK_117 (Nat.beq j 117)) (Nat.ble 117 j)
def BKs102_104 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_118 (Nat.beq j 118)) (Bool.rec (motive := fun _ => ℕ) 0 BK_119 (Nat.beq j 119)) (Nat.ble 119 j)
def BKs100_104 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs100_102 j) (BKs102_104 j) (Nat.ble 118 j)
def BKs104_106 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_120 (Nat.beq j 120)) (Bool.rec (motive := fun _ => ℕ) 0 BK_121 (Nat.beq j 121)) (Nat.ble 121 j)
def BKs106_108 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_122 (Nat.beq j 122)) (Bool.rec (motive := fun _ => ℕ) 0 BK_123 (Nat.beq j 123)) (Nat.ble 123 j)
def BKs104_108 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs104_106 j) (BKs106_108 j) (Nat.ble 122 j)
def BKs100_108 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs100_104 j) (BKs104_108 j) (Nat.ble 120 j)
def BKs93_108 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs93_100 j) (BKs100_108 j) (Nat.ble 116 j)
def BKs108_110 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_124 (Nat.beq j 124)) (Bool.rec (motive := fun _ => ℕ) 0 BK_125 (Nat.beq j 125)) (Nat.ble 125 j)
def BKs110_112 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_126 (Nat.beq j 126)) (Bool.rec (motive := fun _ => ℕ) 0 BK_127 (Nat.beq j 127)) (Nat.ble 127 j)
def BKs108_112 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs108_110 j) (BKs110_112 j) (Nat.ble 126 j)
def BKs112_114 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_128 (Nat.beq j 128)) (Bool.rec (motive := fun _ => ℕ) 0 BK_129 (Nat.beq j 129)) (Nat.ble 129 j)
def BKs114_116 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_130 (Nat.beq j 130)) (Bool.rec (motive := fun _ => ℕ) 0 BK_131 (Nat.beq j 131)) (Nat.ble 131 j)
def BKs112_116 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs112_114 j) (BKs114_116 j) (Nat.ble 130 j)
def BKs108_116 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs108_112 j) (BKs112_116 j) (Nat.ble 128 j)
def BKs116_118 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_132 (Nat.beq j 132)) (Bool.rec (motive := fun _ => ℕ) 0 BK_133 (Nat.beq j 133)) (Nat.ble 133 j)
def BKs118_120 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_134 (Nat.beq j 134)) (Bool.rec (motive := fun _ => ℕ) 0 BK_135 (Nat.beq j 135)) (Nat.ble 135 j)
def BKs116_120 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs116_118 j) (BKs118_120 j) (Nat.ble 134 j)
def BKs120_122 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_136 (Nat.beq j 136)) (Bool.rec (motive := fun _ => ℕ) 0 BK_137 (Nat.beq j 137)) (Nat.ble 137 j)
def BKs122_124 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_138 (Nat.beq j 138)) (Bool.rec (motive := fun _ => ℕ) 0 BK_139 (Nat.beq j 139)) (Nat.ble 139 j)
def BKs120_124 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs120_122 j) (BKs122_124 j) (Nat.ble 138 j)
def BKs116_124 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs116_120 j) (BKs120_124 j) (Nat.ble 136 j)
def BKs108_124 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs108_116 j) (BKs116_124 j) (Nat.ble 132 j)
def BKs93_124 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs93_108 j) (BKs108_124 j) (Nat.ble 124 j)
def BKs62_124 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs62_93 j) (BKs93_124 j) (Nat.ble 109 j)
def BKs0_124 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs0_62 j) (BKs62_124 j) (Nat.ble 78 j)
def BKs125_127 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_141 (Nat.beq j 141)) (Bool.rec (motive := fun _ => ℕ) 0 BK_142 (Nat.beq j 142)) (Nat.ble 142 j)
def BKs124_127 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_140 (Nat.beq j 140)) (BKs125_127 j) (Nat.ble 141 j)
def BKs127_129 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_143 (Nat.beq j 143)) (Bool.rec (motive := fun _ => ℕ) 0 BK_144 (Nat.beq j 144)) (Nat.ble 144 j)
def BKs129_131 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_145 (Nat.beq j 145)) (Bool.rec (motive := fun _ => ℕ) 0 BK_146 (Nat.beq j 146)) (Nat.ble 146 j)
def BKs127_131 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs127_129 j) (BKs129_131 j) (Nat.ble 145 j)
def BKs124_131 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs124_127 j) (BKs127_131 j) (Nat.ble 143 j)
def BKs131_133 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_147 (Nat.beq j 147)) (Bool.rec (motive := fun _ => ℕ) 0 BK_148 (Nat.beq j 148)) (Nat.ble 148 j)
def BKs133_135 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_149 (Nat.beq j 149)) (Bool.rec (motive := fun _ => ℕ) 0 BK_150 (Nat.beq j 150)) (Nat.ble 150 j)
def BKs131_135 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs131_133 j) (BKs133_135 j) (Nat.ble 149 j)
def BKs135_137 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_151 (Nat.beq j 151)) (Bool.rec (motive := fun _ => ℕ) 0 BK_152 (Nat.beq j 152)) (Nat.ble 152 j)
def BKs137_139 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_153 (Nat.beq j 153)) (Bool.rec (motive := fun _ => ℕ) 0 BK_154 (Nat.beq j 154)) (Nat.ble 154 j)
def BKs135_139 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs135_137 j) (BKs137_139 j) (Nat.ble 153 j)
def BKs131_139 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs131_135 j) (BKs135_139 j) (Nat.ble 151 j)
def BKs124_139 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs124_131 j) (BKs131_139 j) (Nat.ble 147 j)
def BKs139_141 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_155 (Nat.beq j 155)) (Bool.rec (motive := fun _ => ℕ) 0 BK_156 (Nat.beq j 156)) (Nat.ble 156 j)
def BKs141_143 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_157 (Nat.beq j 157)) (Bool.rec (motive := fun _ => ℕ) 0 BK_158 (Nat.beq j 158)) (Nat.ble 158 j)
def BKs139_143 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs139_141 j) (BKs141_143 j) (Nat.ble 157 j)
def BKs143_145 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_159 (Nat.beq j 159)) (Bool.rec (motive := fun _ => ℕ) 0 BK_160 (Nat.beq j 160)) (Nat.ble 160 j)
def BKs145_147 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_161 (Nat.beq j 161)) (Bool.rec (motive := fun _ => ℕ) 0 BK_162 (Nat.beq j 162)) (Nat.ble 162 j)
def BKs143_147 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs143_145 j) (BKs145_147 j) (Nat.ble 161 j)
def BKs139_147 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs139_143 j) (BKs143_147 j) (Nat.ble 159 j)
def BKs147_149 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_163 (Nat.beq j 163)) (Bool.rec (motive := fun _ => ℕ) 0 BK_164 (Nat.beq j 164)) (Nat.ble 164 j)
def BKs149_151 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_165 (Nat.beq j 165)) (Bool.rec (motive := fun _ => ℕ) 0 BK_166 (Nat.beq j 166)) (Nat.ble 166 j)
def BKs147_151 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs147_149 j) (BKs149_151 j) (Nat.ble 165 j)
def BKs151_153 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_167 (Nat.beq j 167)) (Bool.rec (motive := fun _ => ℕ) 0 BK_168 (Nat.beq j 168)) (Nat.ble 168 j)
def BKs153_155 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_169 (Nat.beq j 169)) (Bool.rec (motive := fun _ => ℕ) 0 BK_170 (Nat.beq j 170)) (Nat.ble 170 j)
def BKs151_155 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs151_153 j) (BKs153_155 j) (Nat.ble 169 j)
def BKs147_155 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs147_151 j) (BKs151_155 j) (Nat.ble 167 j)
def BKs139_155 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs139_147 j) (BKs147_155 j) (Nat.ble 163 j)
def BKs124_155 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs124_139 j) (BKs139_155 j) (Nat.ble 155 j)
def BKs156_158 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_172 (Nat.beq j 172)) (Bool.rec (motive := fun _ => ℕ) 0 BK_173 (Nat.beq j 173)) (Nat.ble 173 j)
def BKs155_158 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_171 (Nat.beq j 171)) (BKs156_158 j) (Nat.ble 172 j)
def BKs158_160 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_174 (Nat.beq j 174)) (Bool.rec (motive := fun _ => ℕ) 0 BK_175 (Nat.beq j 175)) (Nat.ble 175 j)
def BKs160_162 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_176 (Nat.beq j 176)) (Bool.rec (motive := fun _ => ℕ) 0 BK_177 (Nat.beq j 177)) (Nat.ble 177 j)
def BKs158_162 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs158_160 j) (BKs160_162 j) (Nat.ble 176 j)
def BKs155_162 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs155_158 j) (BKs158_162 j) (Nat.ble 174 j)
def BKs162_164 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_178 (Nat.beq j 178)) (Bool.rec (motive := fun _ => ℕ) 0 BK_179 (Nat.beq j 179)) (Nat.ble 179 j)
def BKs164_166 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_180 (Nat.beq j 180)) (Bool.rec (motive := fun _ => ℕ) 0 BK_181 (Nat.beq j 181)) (Nat.ble 181 j)
def BKs162_166 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs162_164 j) (BKs164_166 j) (Nat.ble 180 j)
def BKs166_168 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_182 (Nat.beq j 182)) (Bool.rec (motive := fun _ => ℕ) 0 BK_183 (Nat.beq j 183)) (Nat.ble 183 j)
def BKs168_170 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_184 (Nat.beq j 184)) (Bool.rec (motive := fun _ => ℕ) 0 BK_185 (Nat.beq j 185)) (Nat.ble 185 j)
def BKs166_170 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs166_168 j) (BKs168_170 j) (Nat.ble 184 j)
def BKs162_170 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs162_166 j) (BKs166_170 j) (Nat.ble 182 j)
def BKs155_170 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs155_162 j) (BKs162_170 j) (Nat.ble 178 j)
def BKs170_172 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_186 (Nat.beq j 186)) (Bool.rec (motive := fun _ => ℕ) 0 BK_187 (Nat.beq j 187)) (Nat.ble 187 j)
def BKs172_174 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_188 (Nat.beq j 188)) (Bool.rec (motive := fun _ => ℕ) 0 BK_189 (Nat.beq j 189)) (Nat.ble 189 j)
def BKs170_174 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs170_172 j) (BKs172_174 j) (Nat.ble 188 j)
def BKs174_176 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_190 (Nat.beq j 190)) (Bool.rec (motive := fun _ => ℕ) 0 BK_191 (Nat.beq j 191)) (Nat.ble 191 j)
def BKs176_178 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_192 (Nat.beq j 192)) (Bool.rec (motive := fun _ => ℕ) 0 BK_193 (Nat.beq j 193)) (Nat.ble 193 j)
def BKs174_178 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs174_176 j) (BKs176_178 j) (Nat.ble 192 j)
def BKs170_178 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs170_174 j) (BKs174_178 j) (Nat.ble 190 j)
def BKs178_180 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_194 (Nat.beq j 194)) (Bool.rec (motive := fun _ => ℕ) 0 BK_195 (Nat.beq j 195)) (Nat.ble 195 j)
def BKs180_182 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_196 (Nat.beq j 196)) (Bool.rec (motive := fun _ => ℕ) 0 BK_197 (Nat.beq j 197)) (Nat.ble 197 j)
def BKs178_182 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs178_180 j) (BKs180_182 j) (Nat.ble 196 j)
def BKs182_184 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_198 (Nat.beq j 198)) (Bool.rec (motive := fun _ => ℕ) 0 BK_199 (Nat.beq j 199)) (Nat.ble 199 j)
def BKs184_186 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_200 (Nat.beq j 200)) (Bool.rec (motive := fun _ => ℕ) 0 BK_201 (Nat.beq j 201)) (Nat.ble 201 j)
def BKs182_186 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs182_184 j) (BKs184_186 j) (Nat.ble 200 j)
def BKs178_186 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs178_182 j) (BKs182_186 j) (Nat.ble 198 j)
def BKs170_186 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs170_178 j) (BKs178_186 j) (Nat.ble 194 j)
def BKs155_186 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs155_170 j) (BKs170_186 j) (Nat.ble 186 j)
def BKs124_186 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs124_155 j) (BKs155_186 j) (Nat.ble 171 j)
def BKs187_189 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_203 (Nat.beq j 203)) (Bool.rec (motive := fun _ => ℕ) 0 BK_204 (Nat.beq j 204)) (Nat.ble 204 j)
def BKs186_189 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_202 (Nat.beq j 202)) (BKs187_189 j) (Nat.ble 203 j)
def BKs189_191 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_205 (Nat.beq j 205)) (Bool.rec (motive := fun _ => ℕ) 0 BK_206 (Nat.beq j 206)) (Nat.ble 206 j)
def BKs191_193 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_207 (Nat.beq j 207)) (Bool.rec (motive := fun _ => ℕ) 0 BK_208 (Nat.beq j 208)) (Nat.ble 208 j)
def BKs189_193 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs189_191 j) (BKs191_193 j) (Nat.ble 207 j)
def BKs186_193 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs186_189 j) (BKs189_193 j) (Nat.ble 205 j)
def BKs193_195 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_209 (Nat.beq j 209)) (Bool.rec (motive := fun _ => ℕ) 0 BK_210 (Nat.beq j 210)) (Nat.ble 210 j)
def BKs195_197 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_211 (Nat.beq j 211)) (Bool.rec (motive := fun _ => ℕ) 0 BK_212 (Nat.beq j 212)) (Nat.ble 212 j)
def BKs193_197 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs193_195 j) (BKs195_197 j) (Nat.ble 211 j)
def BKs197_199 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_213 (Nat.beq j 213)) (Bool.rec (motive := fun _ => ℕ) 0 BK_214 (Nat.beq j 214)) (Nat.ble 214 j)
def BKs199_201 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_215 (Nat.beq j 215)) (Bool.rec (motive := fun _ => ℕ) 0 BK_216 (Nat.beq j 216)) (Nat.ble 216 j)
def BKs197_201 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs197_199 j) (BKs199_201 j) (Nat.ble 215 j)
def BKs193_201 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs193_197 j) (BKs197_201 j) (Nat.ble 213 j)
def BKs186_201 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs186_193 j) (BKs193_201 j) (Nat.ble 209 j)
def BKs201_203 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_217 (Nat.beq j 217)) (Bool.rec (motive := fun _ => ℕ) 0 BK_218 (Nat.beq j 218)) (Nat.ble 218 j)
def BKs203_205 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_219 (Nat.beq j 219)) (Bool.rec (motive := fun _ => ℕ) 0 BK_220 (Nat.beq j 220)) (Nat.ble 220 j)
def BKs201_205 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs201_203 j) (BKs203_205 j) (Nat.ble 219 j)
def BKs205_207 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_221 (Nat.beq j 221)) (Bool.rec (motive := fun _ => ℕ) 0 BK_222 (Nat.beq j 222)) (Nat.ble 222 j)
def BKs207_209 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_223 (Nat.beq j 223)) (Bool.rec (motive := fun _ => ℕ) 0 BK_224 (Nat.beq j 224)) (Nat.ble 224 j)
def BKs205_209 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs205_207 j) (BKs207_209 j) (Nat.ble 223 j)
def BKs201_209 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs201_205 j) (BKs205_209 j) (Nat.ble 221 j)
def BKs209_211 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_225 (Nat.beq j 225)) (Bool.rec (motive := fun _ => ℕ) 0 BK_226 (Nat.beq j 226)) (Nat.ble 226 j)
def BKs211_213 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_227 (Nat.beq j 227)) (Bool.rec (motive := fun _ => ℕ) 0 BK_228 (Nat.beq j 228)) (Nat.ble 228 j)
def BKs209_213 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs209_211 j) (BKs211_213 j) (Nat.ble 227 j)
def BKs213_215 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_229 (Nat.beq j 229)) (Bool.rec (motive := fun _ => ℕ) 0 BK_230 (Nat.beq j 230)) (Nat.ble 230 j)
def BKs215_217 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_231 (Nat.beq j 231)) (Bool.rec (motive := fun _ => ℕ) 0 BK_232 (Nat.beq j 232)) (Nat.ble 232 j)
def BKs213_217 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs213_215 j) (BKs215_217 j) (Nat.ble 231 j)
def BKs209_217 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs209_213 j) (BKs213_217 j) (Nat.ble 229 j)
def BKs201_217 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs201_209 j) (BKs209_217 j) (Nat.ble 225 j)
def BKs186_217 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs186_201 j) (BKs201_217 j) (Nat.ble 217 j)
def BKs218_220 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_234 (Nat.beq j 234)) (Bool.rec (motive := fun _ => ℕ) 0 BK_235 (Nat.beq j 235)) (Nat.ble 235 j)
def BKs217_220 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_233 (Nat.beq j 233)) (BKs218_220 j) (Nat.ble 234 j)
def BKs220_222 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_236 (Nat.beq j 236)) (Bool.rec (motive := fun _ => ℕ) 0 BK_237 (Nat.beq j 237)) (Nat.ble 237 j)
def BKs222_224 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_238 (Nat.beq j 238)) (Bool.rec (motive := fun _ => ℕ) 0 BK_239 (Nat.beq j 239)) (Nat.ble 239 j)
def BKs220_224 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs220_222 j) (BKs222_224 j) (Nat.ble 238 j)
def BKs217_224 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs217_220 j) (BKs220_224 j) (Nat.ble 236 j)
def BKs224_226 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_240 (Nat.beq j 240)) (Bool.rec (motive := fun _ => ℕ) 0 BK_241 (Nat.beq j 241)) (Nat.ble 241 j)
def BKs226_228 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_242 (Nat.beq j 242)) (Bool.rec (motive := fun _ => ℕ) 0 BK_243 (Nat.beq j 243)) (Nat.ble 243 j)
def BKs224_228 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs224_226 j) (BKs226_228 j) (Nat.ble 242 j)
def BKs228_230 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_244 (Nat.beq j 244)) (Bool.rec (motive := fun _ => ℕ) 0 BK_245 (Nat.beq j 245)) (Nat.ble 245 j)
def BKs230_232 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_246 (Nat.beq j 246)) (Bool.rec (motive := fun _ => ℕ) 0 BK_247 (Nat.beq j 247)) (Nat.ble 247 j)
def BKs228_232 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs228_230 j) (BKs230_232 j) (Nat.ble 246 j)
def BKs224_232 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs224_228 j) (BKs228_232 j) (Nat.ble 244 j)
def BKs217_232 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs217_224 j) (BKs224_232 j) (Nat.ble 240 j)
def BKs232_234 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_248 (Nat.beq j 248)) (Bool.rec (motive := fun _ => ℕ) 0 BK_249 (Nat.beq j 249)) (Nat.ble 249 j)
def BKs234_236 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_250 (Nat.beq j 250)) (Bool.rec (motive := fun _ => ℕ) 0 BK_251 (Nat.beq j 251)) (Nat.ble 251 j)
def BKs232_236 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs232_234 j) (BKs234_236 j) (Nat.ble 250 j)
def BKs236_238 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_252 (Nat.beq j 252)) (Bool.rec (motive := fun _ => ℕ) 0 BK_253 (Nat.beq j 253)) (Nat.ble 253 j)
def BKs238_240 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_254 (Nat.beq j 254)) (Bool.rec (motive := fun _ => ℕ) 0 BK_255 (Nat.beq j 255)) (Nat.ble 255 j)
def BKs236_240 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs236_238 j) (BKs238_240 j) (Nat.ble 254 j)
def BKs232_240 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs232_236 j) (BKs236_240 j) (Nat.ble 252 j)
def BKs240_242 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_256 (Nat.beq j 256)) (Bool.rec (motive := fun _ => ℕ) 0 BK_257 (Nat.beq j 257)) (Nat.ble 257 j)
def BKs242_244 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_258 (Nat.beq j 258)) (Bool.rec (motive := fun _ => ℕ) 0 BK_259 (Nat.beq j 259)) (Nat.ble 259 j)
def BKs240_244 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs240_242 j) (BKs242_244 j) (Nat.ble 258 j)
def BKs244_246 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_260 (Nat.beq j 260)) (Bool.rec (motive := fun _ => ℕ) 0 BK_261 (Nat.beq j 261)) (Nat.ble 261 j)
def BKs246_248 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_262 (Nat.beq j 262)) (Bool.rec (motive := fun _ => ℕ) 0 BK_263 (Nat.beq j 263)) (Nat.ble 263 j)
def BKs244_248 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs244_246 j) (BKs246_248 j) (Nat.ble 262 j)
def BKs240_248 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs240_244 j) (BKs244_248 j) (Nat.ble 260 j)
def BKs232_248 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs232_240 j) (BKs240_248 j) (Nat.ble 256 j)
def BKs217_248 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs217_232 j) (BKs232_248 j) (Nat.ble 248 j)
def BKs186_248 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs186_217 j) (BKs217_248 j) (Nat.ble 233 j)
def BKs124_248 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs124_186 j) (BKs186_248 j) (Nat.ble 202 j)
def BKs0_248 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs0_124 j) (BKs124_248 j) (Nat.ble 140 j)
def BKs249_251 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_265 (Nat.beq j 265)) (Bool.rec (motive := fun _ => ℕ) 0 BK_266 (Nat.beq j 266)) (Nat.ble 266 j)
def BKs248_251 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_264 (Nat.beq j 264)) (BKs249_251 j) (Nat.ble 265 j)
def BKs251_253 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_267 (Nat.beq j 267)) (Bool.rec (motive := fun _ => ℕ) 0 BK_268 (Nat.beq j 268)) (Nat.ble 268 j)
def BKs253_255 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_269 (Nat.beq j 269)) (Bool.rec (motive := fun _ => ℕ) 0 BK_270 (Nat.beq j 270)) (Nat.ble 270 j)
def BKs251_255 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs251_253 j) (BKs253_255 j) (Nat.ble 269 j)
def BKs248_255 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs248_251 j) (BKs251_255 j) (Nat.ble 267 j)
def BKs255_257 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_271 (Nat.beq j 271)) (Bool.rec (motive := fun _ => ℕ) 0 BK_272 (Nat.beq j 272)) (Nat.ble 272 j)
def BKs257_259 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_273 (Nat.beq j 273)) (Bool.rec (motive := fun _ => ℕ) 0 BK_274 (Nat.beq j 274)) (Nat.ble 274 j)
def BKs255_259 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs255_257 j) (BKs257_259 j) (Nat.ble 273 j)
def BKs259_261 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_275 (Nat.beq j 275)) (Bool.rec (motive := fun _ => ℕ) 0 BK_276 (Nat.beq j 276)) (Nat.ble 276 j)
def BKs261_263 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_277 (Nat.beq j 277)) (Bool.rec (motive := fun _ => ℕ) 0 BK_278 (Nat.beq j 278)) (Nat.ble 278 j)
def BKs259_263 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs259_261 j) (BKs261_263 j) (Nat.ble 277 j)
def BKs255_263 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs255_259 j) (BKs259_263 j) (Nat.ble 275 j)
def BKs248_263 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs248_255 j) (BKs255_263 j) (Nat.ble 271 j)
def BKs263_265 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_279 (Nat.beq j 279)) (Bool.rec (motive := fun _ => ℕ) 0 BK_280 (Nat.beq j 280)) (Nat.ble 280 j)
def BKs265_267 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_281 (Nat.beq j 281)) (Bool.rec (motive := fun _ => ℕ) 0 BK_282 (Nat.beq j 282)) (Nat.ble 282 j)
def BKs263_267 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs263_265 j) (BKs265_267 j) (Nat.ble 281 j)
def BKs267_269 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_283 (Nat.beq j 283)) (Bool.rec (motive := fun _ => ℕ) 0 BK_284 (Nat.beq j 284)) (Nat.ble 284 j)
def BKs269_271 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_285 (Nat.beq j 285)) (Bool.rec (motive := fun _ => ℕ) 0 BK_286 (Nat.beq j 286)) (Nat.ble 286 j)
def BKs267_271 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs267_269 j) (BKs269_271 j) (Nat.ble 285 j)
def BKs263_271 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs263_267 j) (BKs267_271 j) (Nat.ble 283 j)
def BKs271_273 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_287 (Nat.beq j 287)) (Bool.rec (motive := fun _ => ℕ) 0 BK_288 (Nat.beq j 288)) (Nat.ble 288 j)
def BKs273_275 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_289 (Nat.beq j 289)) (Bool.rec (motive := fun _ => ℕ) 0 BK_290 (Nat.beq j 290)) (Nat.ble 290 j)
def BKs271_275 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs271_273 j) (BKs273_275 j) (Nat.ble 289 j)
def BKs275_277 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_291 (Nat.beq j 291)) (Bool.rec (motive := fun _ => ℕ) 0 BK_292 (Nat.beq j 292)) (Nat.ble 292 j)
def BKs277_279 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_293 (Nat.beq j 293)) (Bool.rec (motive := fun _ => ℕ) 0 BK_294 (Nat.beq j 294)) (Nat.ble 294 j)
def BKs275_279 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs275_277 j) (BKs277_279 j) (Nat.ble 293 j)
def BKs271_279 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs271_275 j) (BKs275_279 j) (Nat.ble 291 j)
def BKs263_279 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs263_271 j) (BKs271_279 j) (Nat.ble 287 j)
def BKs248_279 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs248_263 j) (BKs263_279 j) (Nat.ble 279 j)
def BKs280_282 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_296 (Nat.beq j 296)) (Bool.rec (motive := fun _ => ℕ) 0 BK_297 (Nat.beq j 297)) (Nat.ble 297 j)
def BKs279_282 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_295 (Nat.beq j 295)) (BKs280_282 j) (Nat.ble 296 j)
def BKs282_284 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_298 (Nat.beq j 298)) (Bool.rec (motive := fun _ => ℕ) 0 BK_299 (Nat.beq j 299)) (Nat.ble 299 j)
def BKs284_286 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_300 (Nat.beq j 300)) (Bool.rec (motive := fun _ => ℕ) 0 BK_301 (Nat.beq j 301)) (Nat.ble 301 j)
def BKs282_286 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs282_284 j) (BKs284_286 j) (Nat.ble 300 j)
def BKs279_286 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs279_282 j) (BKs282_286 j) (Nat.ble 298 j)
def BKs286_288 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_302 (Nat.beq j 302)) (Bool.rec (motive := fun _ => ℕ) 0 BK_303 (Nat.beq j 303)) (Nat.ble 303 j)
def BKs288_290 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_304 (Nat.beq j 304)) (Bool.rec (motive := fun _ => ℕ) 0 BK_305 (Nat.beq j 305)) (Nat.ble 305 j)
def BKs286_290 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs286_288 j) (BKs288_290 j) (Nat.ble 304 j)
def BKs290_292 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_306 (Nat.beq j 306)) (Bool.rec (motive := fun _ => ℕ) 0 BK_307 (Nat.beq j 307)) (Nat.ble 307 j)
def BKs292_294 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_308 (Nat.beq j 308)) (Bool.rec (motive := fun _ => ℕ) 0 BK_309 (Nat.beq j 309)) (Nat.ble 309 j)
def BKs290_294 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs290_292 j) (BKs292_294 j) (Nat.ble 308 j)
def BKs286_294 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs286_290 j) (BKs290_294 j) (Nat.ble 306 j)
def BKs279_294 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs279_286 j) (BKs286_294 j) (Nat.ble 302 j)
def BKs294_296 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_310 (Nat.beq j 310)) (Bool.rec (motive := fun _ => ℕ) 0 BK_311 (Nat.beq j 311)) (Nat.ble 311 j)
def BKs296_298 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_312 (Nat.beq j 312)) (Bool.rec (motive := fun _ => ℕ) 0 BK_313 (Nat.beq j 313)) (Nat.ble 313 j)
def BKs294_298 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs294_296 j) (BKs296_298 j) (Nat.ble 312 j)
def BKs298_300 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_314 (Nat.beq j 314)) (Bool.rec (motive := fun _ => ℕ) 0 BK_315 (Nat.beq j 315)) (Nat.ble 315 j)
def BKs300_302 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_316 (Nat.beq j 316)) (Bool.rec (motive := fun _ => ℕ) 0 BK_317 (Nat.beq j 317)) (Nat.ble 317 j)
def BKs298_302 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs298_300 j) (BKs300_302 j) (Nat.ble 316 j)
def BKs294_302 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs294_298 j) (BKs298_302 j) (Nat.ble 314 j)
def BKs302_304 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_318 (Nat.beq j 318)) (Bool.rec (motive := fun _ => ℕ) 0 BK_319 (Nat.beq j 319)) (Nat.ble 319 j)
def BKs304_306 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_320 (Nat.beq j 320)) (Bool.rec (motive := fun _ => ℕ) 0 BK_321 (Nat.beq j 321)) (Nat.ble 321 j)
def BKs302_306 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs302_304 j) (BKs304_306 j) (Nat.ble 320 j)
def BKs306_308 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_322 (Nat.beq j 322)) (Bool.rec (motive := fun _ => ℕ) 0 BK_323 (Nat.beq j 323)) (Nat.ble 323 j)
def BKs308_310 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_324 (Nat.beq j 324)) (Bool.rec (motive := fun _ => ℕ) 0 BK_325 (Nat.beq j 325)) (Nat.ble 325 j)
def BKs306_310 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs306_308 j) (BKs308_310 j) (Nat.ble 324 j)
def BKs302_310 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs302_306 j) (BKs306_310 j) (Nat.ble 322 j)
def BKs294_310 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs294_302 j) (BKs302_310 j) (Nat.ble 318 j)
def BKs279_310 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs279_294 j) (BKs294_310 j) (Nat.ble 310 j)
def BKs248_310 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs248_279 j) (BKs279_310 j) (Nat.ble 295 j)
def BKs311_313 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_327 (Nat.beq j 327)) (Bool.rec (motive := fun _ => ℕ) 0 BK_328 (Nat.beq j 328)) (Nat.ble 328 j)
def BKs310_313 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_326 (Nat.beq j 326)) (BKs311_313 j) (Nat.ble 327 j)
def BKs313_315 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_329 (Nat.beq j 329)) (Bool.rec (motive := fun _ => ℕ) 0 BK_330 (Nat.beq j 330)) (Nat.ble 330 j)
def BKs315_317 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_331 (Nat.beq j 331)) (Bool.rec (motive := fun _ => ℕ) 0 BK_332 (Nat.beq j 332)) (Nat.ble 332 j)
def BKs313_317 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs313_315 j) (BKs315_317 j) (Nat.ble 331 j)
def BKs310_317 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs310_313 j) (BKs313_317 j) (Nat.ble 329 j)
def BKs317_319 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_333 (Nat.beq j 333)) (Bool.rec (motive := fun _ => ℕ) 0 BK_334 (Nat.beq j 334)) (Nat.ble 334 j)
def BKs319_321 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_335 (Nat.beq j 335)) (Bool.rec (motive := fun _ => ℕ) 0 BK_336 (Nat.beq j 336)) (Nat.ble 336 j)
def BKs317_321 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs317_319 j) (BKs319_321 j) (Nat.ble 335 j)
def BKs321_323 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_337 (Nat.beq j 337)) (Bool.rec (motive := fun _ => ℕ) 0 BK_338 (Nat.beq j 338)) (Nat.ble 338 j)
def BKs323_325 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_339 (Nat.beq j 339)) (Bool.rec (motive := fun _ => ℕ) 0 BK_340 (Nat.beq j 340)) (Nat.ble 340 j)
def BKs321_325 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs321_323 j) (BKs323_325 j) (Nat.ble 339 j)
def BKs317_325 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs317_321 j) (BKs321_325 j) (Nat.ble 337 j)
def BKs310_325 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs310_317 j) (BKs317_325 j) (Nat.ble 333 j)
def BKs325_327 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_341 (Nat.beq j 341)) (Bool.rec (motive := fun _ => ℕ) 0 BK_342 (Nat.beq j 342)) (Nat.ble 342 j)
def BKs327_329 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_343 (Nat.beq j 343)) (Bool.rec (motive := fun _ => ℕ) 0 BK_344 (Nat.beq j 344)) (Nat.ble 344 j)
def BKs325_329 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs325_327 j) (BKs327_329 j) (Nat.ble 343 j)
def BKs329_331 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_345 (Nat.beq j 345)) (Bool.rec (motive := fun _ => ℕ) 0 BK_346 (Nat.beq j 346)) (Nat.ble 346 j)
def BKs331_333 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_347 (Nat.beq j 347)) (Bool.rec (motive := fun _ => ℕ) 0 BK_348 (Nat.beq j 348)) (Nat.ble 348 j)
def BKs329_333 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs329_331 j) (BKs331_333 j) (Nat.ble 347 j)
def BKs325_333 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs325_329 j) (BKs329_333 j) (Nat.ble 345 j)
def BKs333_335 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_349 (Nat.beq j 349)) (Bool.rec (motive := fun _ => ℕ) 0 BK_350 (Nat.beq j 350)) (Nat.ble 350 j)
def BKs335_337 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_351 (Nat.beq j 351)) (Bool.rec (motive := fun _ => ℕ) 0 BK_352 (Nat.beq j 352)) (Nat.ble 352 j)
def BKs333_337 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs333_335 j) (BKs335_337 j) (Nat.ble 351 j)
def BKs337_339 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_353 (Nat.beq j 353)) (Bool.rec (motive := fun _ => ℕ) 0 BK_354 (Nat.beq j 354)) (Nat.ble 354 j)
def BKs339_341 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_355 (Nat.beq j 355)) (Bool.rec (motive := fun _ => ℕ) 0 BK_356 (Nat.beq j 356)) (Nat.ble 356 j)
def BKs337_341 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs337_339 j) (BKs339_341 j) (Nat.ble 355 j)
def BKs333_341 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs333_337 j) (BKs337_341 j) (Nat.ble 353 j)
def BKs325_341 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs325_333 j) (BKs333_341 j) (Nat.ble 349 j)
def BKs310_341 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs310_325 j) (BKs325_341 j) (Nat.ble 341 j)
def BKs342_344 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_358 (Nat.beq j 358)) (Bool.rec (motive := fun _ => ℕ) 0 BK_359 (Nat.beq j 359)) (Nat.ble 359 j)
def BKs341_344 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_357 (Nat.beq j 357)) (BKs342_344 j) (Nat.ble 358 j)
def BKs344_346 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_360 (Nat.beq j 360)) (Bool.rec (motive := fun _ => ℕ) 0 BK_361 (Nat.beq j 361)) (Nat.ble 361 j)
def BKs346_348 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_362 (Nat.beq j 362)) (Bool.rec (motive := fun _ => ℕ) 0 BK_363 (Nat.beq j 363)) (Nat.ble 363 j)
def BKs344_348 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs344_346 j) (BKs346_348 j) (Nat.ble 362 j)
def BKs341_348 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs341_344 j) (BKs344_348 j) (Nat.ble 360 j)
def BKs348_350 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_364 (Nat.beq j 364)) (Bool.rec (motive := fun _ => ℕ) 0 BK_365 (Nat.beq j 365)) (Nat.ble 365 j)
def BKs350_352 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_366 (Nat.beq j 366)) (Bool.rec (motive := fun _ => ℕ) 0 BK_367 (Nat.beq j 367)) (Nat.ble 367 j)
def BKs348_352 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs348_350 j) (BKs350_352 j) (Nat.ble 366 j)
def BKs352_354 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_368 (Nat.beq j 368)) (Bool.rec (motive := fun _ => ℕ) 0 BK_369 (Nat.beq j 369)) (Nat.ble 369 j)
def BKs354_356 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_370 (Nat.beq j 370)) (Bool.rec (motive := fun _ => ℕ) 0 BK_371 (Nat.beq j 371)) (Nat.ble 371 j)
def BKs352_356 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs352_354 j) (BKs354_356 j) (Nat.ble 370 j)
def BKs348_356 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs348_352 j) (BKs352_356 j) (Nat.ble 368 j)
def BKs341_356 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs341_348 j) (BKs348_356 j) (Nat.ble 364 j)
def BKs356_358 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_372 (Nat.beq j 372)) (Bool.rec (motive := fun _ => ℕ) 0 BK_373 (Nat.beq j 373)) (Nat.ble 373 j)
def BKs358_360 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_374 (Nat.beq j 374)) (Bool.rec (motive := fun _ => ℕ) 0 BK_375 (Nat.beq j 375)) (Nat.ble 375 j)
def BKs356_360 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs356_358 j) (BKs358_360 j) (Nat.ble 374 j)
def BKs360_362 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_376 (Nat.beq j 376)) (Bool.rec (motive := fun _ => ℕ) 0 BK_377 (Nat.beq j 377)) (Nat.ble 377 j)
def BKs362_364 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_378 (Nat.beq j 378)) (Bool.rec (motive := fun _ => ℕ) 0 BK_379 (Nat.beq j 379)) (Nat.ble 379 j)
def BKs360_364 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs360_362 j) (BKs362_364 j) (Nat.ble 378 j)
def BKs356_364 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs356_360 j) (BKs360_364 j) (Nat.ble 376 j)
def BKs364_366 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_380 (Nat.beq j 380)) (Bool.rec (motive := fun _ => ℕ) 0 BK_381 (Nat.beq j 381)) (Nat.ble 381 j)
def BKs366_368 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_382 (Nat.beq j 382)) (Bool.rec (motive := fun _ => ℕ) 0 BK_383 (Nat.beq j 383)) (Nat.ble 383 j)
def BKs364_368 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs364_366 j) (BKs366_368 j) (Nat.ble 382 j)
def BKs368_370 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_384 (Nat.beq j 384)) (Bool.rec (motive := fun _ => ℕ) 0 BK_385 (Nat.beq j 385)) (Nat.ble 385 j)
def BKs370_372 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_386 (Nat.beq j 386)) (Bool.rec (motive := fun _ => ℕ) 0 BK_387 (Nat.beq j 387)) (Nat.ble 387 j)
def BKs368_372 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs368_370 j) (BKs370_372 j) (Nat.ble 386 j)
def BKs364_372 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs364_368 j) (BKs368_372 j) (Nat.ble 384 j)
def BKs356_372 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs356_364 j) (BKs364_372 j) (Nat.ble 380 j)
def BKs341_372 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs341_356 j) (BKs356_372 j) (Nat.ble 372 j)
def BKs310_372 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs310_341 j) (BKs341_372 j) (Nat.ble 357 j)
def BKs248_372 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs248_310 j) (BKs310_372 j) (Nat.ble 326 j)
def BKs373_375 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_389 (Nat.beq j 389)) (Bool.rec (motive := fun _ => ℕ) 0 BK_390 (Nat.beq j 390)) (Nat.ble 390 j)
def BKs372_375 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_388 (Nat.beq j 388)) (BKs373_375 j) (Nat.ble 389 j)
def BKs375_377 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_391 (Nat.beq j 391)) (Bool.rec (motive := fun _ => ℕ) 0 BK_392 (Nat.beq j 392)) (Nat.ble 392 j)
def BKs377_379 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_393 (Nat.beq j 393)) (Bool.rec (motive := fun _ => ℕ) 0 BK_394 (Nat.beq j 394)) (Nat.ble 394 j)
def BKs375_379 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs375_377 j) (BKs377_379 j) (Nat.ble 393 j)
def BKs372_379 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs372_375 j) (BKs375_379 j) (Nat.ble 391 j)
def BKs379_381 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_395 (Nat.beq j 395)) (Bool.rec (motive := fun _ => ℕ) 0 BK_396 (Nat.beq j 396)) (Nat.ble 396 j)
def BKs381_383 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_397 (Nat.beq j 397)) (Bool.rec (motive := fun _ => ℕ) 0 BK_398 (Nat.beq j 398)) (Nat.ble 398 j)
def BKs379_383 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs379_381 j) (BKs381_383 j) (Nat.ble 397 j)
def BKs383_385 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_399 (Nat.beq j 399)) (Bool.rec (motive := fun _ => ℕ) 0 BK_400 (Nat.beq j 400)) (Nat.ble 400 j)
def BKs385_387 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_401 (Nat.beq j 401)) (Bool.rec (motive := fun _ => ℕ) 0 BK_402 (Nat.beq j 402)) (Nat.ble 402 j)
def BKs383_387 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs383_385 j) (BKs385_387 j) (Nat.ble 401 j)
def BKs379_387 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs379_383 j) (BKs383_387 j) (Nat.ble 399 j)
def BKs372_387 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs372_379 j) (BKs379_387 j) (Nat.ble 395 j)
def BKs387_389 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_403 (Nat.beq j 403)) (Bool.rec (motive := fun _ => ℕ) 0 BK_404 (Nat.beq j 404)) (Nat.ble 404 j)
def BKs389_391 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_405 (Nat.beq j 405)) (Bool.rec (motive := fun _ => ℕ) 0 BK_406 (Nat.beq j 406)) (Nat.ble 406 j)
def BKs387_391 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs387_389 j) (BKs389_391 j) (Nat.ble 405 j)
def BKs391_393 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_407 (Nat.beq j 407)) (Bool.rec (motive := fun _ => ℕ) 0 BK_408 (Nat.beq j 408)) (Nat.ble 408 j)
def BKs393_395 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_409 (Nat.beq j 409)) (Bool.rec (motive := fun _ => ℕ) 0 BK_410 (Nat.beq j 410)) (Nat.ble 410 j)
def BKs391_395 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs391_393 j) (BKs393_395 j) (Nat.ble 409 j)
def BKs387_395 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs387_391 j) (BKs391_395 j) (Nat.ble 407 j)
def BKs395_397 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_411 (Nat.beq j 411)) (Bool.rec (motive := fun _ => ℕ) 0 BK_412 (Nat.beq j 412)) (Nat.ble 412 j)
def BKs397_399 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_413 (Nat.beq j 413)) (Bool.rec (motive := fun _ => ℕ) 0 BK_414 (Nat.beq j 414)) (Nat.ble 414 j)
def BKs395_399 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs395_397 j) (BKs397_399 j) (Nat.ble 413 j)
def BKs399_401 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_415 (Nat.beq j 415)) (Bool.rec (motive := fun _ => ℕ) 0 BK_416 (Nat.beq j 416)) (Nat.ble 416 j)
def BKs401_403 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_417 (Nat.beq j 417)) (Bool.rec (motive := fun _ => ℕ) 0 BK_418 (Nat.beq j 418)) (Nat.ble 418 j)
def BKs399_403 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs399_401 j) (BKs401_403 j) (Nat.ble 417 j)
def BKs395_403 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs395_399 j) (BKs399_403 j) (Nat.ble 415 j)
def BKs387_403 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs387_395 j) (BKs395_403 j) (Nat.ble 411 j)
def BKs372_403 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs372_387 j) (BKs387_403 j) (Nat.ble 403 j)
def BKs404_406 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_420 (Nat.beq j 420)) (Bool.rec (motive := fun _ => ℕ) 0 BK_421 (Nat.beq j 421)) (Nat.ble 421 j)
def BKs403_406 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_419 (Nat.beq j 419)) (BKs404_406 j) (Nat.ble 420 j)
def BKs406_408 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_422 (Nat.beq j 422)) (Bool.rec (motive := fun _ => ℕ) 0 BK_423 (Nat.beq j 423)) (Nat.ble 423 j)
def BKs408_410 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_424 (Nat.beq j 424)) (Bool.rec (motive := fun _ => ℕ) 0 BK_425 (Nat.beq j 425)) (Nat.ble 425 j)
def BKs406_410 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs406_408 j) (BKs408_410 j) (Nat.ble 424 j)
def BKs403_410 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs403_406 j) (BKs406_410 j) (Nat.ble 422 j)
def BKs410_412 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_426 (Nat.beq j 426)) (Bool.rec (motive := fun _ => ℕ) 0 BK_427 (Nat.beq j 427)) (Nat.ble 427 j)
def BKs412_414 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_428 (Nat.beq j 428)) (Bool.rec (motive := fun _ => ℕ) 0 BK_429 (Nat.beq j 429)) (Nat.ble 429 j)
def BKs410_414 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs410_412 j) (BKs412_414 j) (Nat.ble 428 j)
def BKs414_416 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_430 (Nat.beq j 430)) (Bool.rec (motive := fun _ => ℕ) 0 BK_431 (Nat.beq j 431)) (Nat.ble 431 j)
def BKs416_418 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_432 (Nat.beq j 432)) (Bool.rec (motive := fun _ => ℕ) 0 BK_433 (Nat.beq j 433)) (Nat.ble 433 j)
def BKs414_418 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs414_416 j) (BKs416_418 j) (Nat.ble 432 j)
def BKs410_418 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs410_414 j) (BKs414_418 j) (Nat.ble 430 j)
def BKs403_418 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs403_410 j) (BKs410_418 j) (Nat.ble 426 j)
def BKs418_420 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_434 (Nat.beq j 434)) (Bool.rec (motive := fun _ => ℕ) 0 BK_435 (Nat.beq j 435)) (Nat.ble 435 j)
def BKs420_422 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_436 (Nat.beq j 436)) (Bool.rec (motive := fun _ => ℕ) 0 BK_437 (Nat.beq j 437)) (Nat.ble 437 j)
def BKs418_422 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs418_420 j) (BKs420_422 j) (Nat.ble 436 j)
def BKs422_424 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_438 (Nat.beq j 438)) (Bool.rec (motive := fun _ => ℕ) 0 BK_439 (Nat.beq j 439)) (Nat.ble 439 j)
def BKs424_426 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_440 (Nat.beq j 440)) (Bool.rec (motive := fun _ => ℕ) 0 BK_441 (Nat.beq j 441)) (Nat.ble 441 j)
def BKs422_426 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs422_424 j) (BKs424_426 j) (Nat.ble 440 j)
def BKs418_426 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs418_422 j) (BKs422_426 j) (Nat.ble 438 j)
def BKs426_428 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_442 (Nat.beq j 442)) (Bool.rec (motive := fun _ => ℕ) 0 BK_443 (Nat.beq j 443)) (Nat.ble 443 j)
def BKs428_430 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_444 (Nat.beq j 444)) (Bool.rec (motive := fun _ => ℕ) 0 BK_445 (Nat.beq j 445)) (Nat.ble 445 j)
def BKs426_430 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs426_428 j) (BKs428_430 j) (Nat.ble 444 j)
def BKs430_432 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_446 (Nat.beq j 446)) (Bool.rec (motive := fun _ => ℕ) 0 BK_447 (Nat.beq j 447)) (Nat.ble 447 j)
def BKs432_434 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_448 (Nat.beq j 448)) (Bool.rec (motive := fun _ => ℕ) 0 BK_449 (Nat.beq j 449)) (Nat.ble 449 j)
def BKs430_434 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs430_432 j) (BKs432_434 j) (Nat.ble 448 j)
def BKs426_434 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs426_430 j) (BKs430_434 j) (Nat.ble 446 j)
def BKs418_434 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs418_426 j) (BKs426_434 j) (Nat.ble 442 j)
def BKs403_434 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs403_418 j) (BKs418_434 j) (Nat.ble 434 j)
def BKs372_434 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs372_403 j) (BKs403_434 j) (Nat.ble 419 j)
def BKs435_437 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_451 (Nat.beq j 451)) (Bool.rec (motive := fun _ => ℕ) 0 BK_452 (Nat.beq j 452)) (Nat.ble 452 j)
def BKs434_437 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_450 (Nat.beq j 450)) (BKs435_437 j) (Nat.ble 451 j)
def BKs437_439 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_453 (Nat.beq j 453)) (Bool.rec (motive := fun _ => ℕ) 0 BK_454 (Nat.beq j 454)) (Nat.ble 454 j)
def BKs439_441 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_455 (Nat.beq j 455)) (Bool.rec (motive := fun _ => ℕ) 0 BK_456 (Nat.beq j 456)) (Nat.ble 456 j)
def BKs437_441 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs437_439 j) (BKs439_441 j) (Nat.ble 455 j)
def BKs434_441 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs434_437 j) (BKs437_441 j) (Nat.ble 453 j)
def BKs441_443 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_457 (Nat.beq j 457)) (Bool.rec (motive := fun _ => ℕ) 0 BK_458 (Nat.beq j 458)) (Nat.ble 458 j)
def BKs443_445 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_459 (Nat.beq j 459)) (Bool.rec (motive := fun _ => ℕ) 0 BK_460 (Nat.beq j 460)) (Nat.ble 460 j)
def BKs441_445 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs441_443 j) (BKs443_445 j) (Nat.ble 459 j)
def BKs445_447 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_461 (Nat.beq j 461)) (Bool.rec (motive := fun _ => ℕ) 0 BK_462 (Nat.beq j 462)) (Nat.ble 462 j)
def BKs447_449 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_463 (Nat.beq j 463)) (Bool.rec (motive := fun _ => ℕ) 0 BK_464 (Nat.beq j 464)) (Nat.ble 464 j)
def BKs445_449 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs445_447 j) (BKs447_449 j) (Nat.ble 463 j)
def BKs441_449 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs441_445 j) (BKs445_449 j) (Nat.ble 461 j)
def BKs434_449 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs434_441 j) (BKs441_449 j) (Nat.ble 457 j)
def BKs449_451 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_465 (Nat.beq j 465)) (Bool.rec (motive := fun _ => ℕ) 0 BK_466 (Nat.beq j 466)) (Nat.ble 466 j)
def BKs451_453 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_467 (Nat.beq j 467)) (Bool.rec (motive := fun _ => ℕ) 0 BK_468 (Nat.beq j 468)) (Nat.ble 468 j)
def BKs449_453 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs449_451 j) (BKs451_453 j) (Nat.ble 467 j)
def BKs453_455 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_469 (Nat.beq j 469)) (Bool.rec (motive := fun _ => ℕ) 0 BK_470 (Nat.beq j 470)) (Nat.ble 470 j)
def BKs455_457 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_471 (Nat.beq j 471)) (Bool.rec (motive := fun _ => ℕ) 0 BK_472 (Nat.beq j 472)) (Nat.ble 472 j)
def BKs453_457 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs453_455 j) (BKs455_457 j) (Nat.ble 471 j)
def BKs449_457 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs449_453 j) (BKs453_457 j) (Nat.ble 469 j)
def BKs457_459 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_473 (Nat.beq j 473)) (Bool.rec (motive := fun _ => ℕ) 0 BK_474 (Nat.beq j 474)) (Nat.ble 474 j)
def BKs459_461 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_475 (Nat.beq j 475)) (Bool.rec (motive := fun _ => ℕ) 0 BK_476 (Nat.beq j 476)) (Nat.ble 476 j)
def BKs457_461 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs457_459 j) (BKs459_461 j) (Nat.ble 475 j)
def BKs461_463 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_477 (Nat.beq j 477)) (Bool.rec (motive := fun _ => ℕ) 0 BK_478 (Nat.beq j 478)) (Nat.ble 478 j)
def BKs463_465 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_479 (Nat.beq j 479)) (Bool.rec (motive := fun _ => ℕ) 0 BK_480 (Nat.beq j 480)) (Nat.ble 480 j)
def BKs461_465 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs461_463 j) (BKs463_465 j) (Nat.ble 479 j)
def BKs457_465 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs457_461 j) (BKs461_465 j) (Nat.ble 477 j)
def BKs449_465 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs449_457 j) (BKs457_465 j) (Nat.ble 473 j)
def BKs434_465 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs434_449 j) (BKs449_465 j) (Nat.ble 465 j)
def BKs466_468 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_482 (Nat.beq j 482)) (Bool.rec (motive := fun _ => ℕ) 0 BK_483 (Nat.beq j 483)) (Nat.ble 483 j)
def BKs465_468 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_481 (Nat.beq j 481)) (BKs466_468 j) (Nat.ble 482 j)
def BKs468_470 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_484 (Nat.beq j 484)) (Bool.rec (motive := fun _ => ℕ) 0 BK_485 (Nat.beq j 485)) (Nat.ble 485 j)
def BKs470_472 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_486 (Nat.beq j 486)) (Bool.rec (motive := fun _ => ℕ) 0 BK_487 (Nat.beq j 487)) (Nat.ble 487 j)
def BKs468_472 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs468_470 j) (BKs470_472 j) (Nat.ble 486 j)
def BKs465_472 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs465_468 j) (BKs468_472 j) (Nat.ble 484 j)
def BKs472_474 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_488 (Nat.beq j 488)) (Bool.rec (motive := fun _ => ℕ) 0 BK_489 (Nat.beq j 489)) (Nat.ble 489 j)
def BKs474_476 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_490 (Nat.beq j 490)) (Bool.rec (motive := fun _ => ℕ) 0 BK_491 (Nat.beq j 491)) (Nat.ble 491 j)
def BKs472_476 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs472_474 j) (BKs474_476 j) (Nat.ble 490 j)
def BKs476_478 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_492 (Nat.beq j 492)) (Bool.rec (motive := fun _ => ℕ) 0 BK_493 (Nat.beq j 493)) (Nat.ble 493 j)
def BKs478_480 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_494 (Nat.beq j 494)) (Bool.rec (motive := fun _ => ℕ) 0 BK_495 (Nat.beq j 495)) (Nat.ble 495 j)
def BKs476_480 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs476_478 j) (BKs478_480 j) (Nat.ble 494 j)
def BKs472_480 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs472_476 j) (BKs476_480 j) (Nat.ble 492 j)
def BKs465_480 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs465_472 j) (BKs472_480 j) (Nat.ble 488 j)
def BKs480_482 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_496 (Nat.beq j 496)) (Bool.rec (motive := fun _ => ℕ) 0 BK_497 (Nat.beq j 497)) (Nat.ble 497 j)
def BKs482_484 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_498 (Nat.beq j 498)) (Bool.rec (motive := fun _ => ℕ) 0 BK_499 (Nat.beq j 499)) (Nat.ble 499 j)
def BKs480_484 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs480_482 j) (BKs482_484 j) (Nat.ble 498 j)
def BKs484_486 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_500 (Nat.beq j 500)) (Bool.rec (motive := fun _ => ℕ) 0 BK_501 (Nat.beq j 501)) (Nat.ble 501 j)
def BKs486_488 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_502 (Nat.beq j 502)) (Bool.rec (motive := fun _ => ℕ) 0 BK_503 (Nat.beq j 503)) (Nat.ble 503 j)
def BKs484_488 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs484_486 j) (BKs486_488 j) (Nat.ble 502 j)
def BKs480_488 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs480_484 j) (BKs484_488 j) (Nat.ble 500 j)
def BKs488_490 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_504 (Nat.beq j 504)) (Bool.rec (motive := fun _ => ℕ) 0 BK_505 (Nat.beq j 505)) (Nat.ble 505 j)
def BKs490_492 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_506 (Nat.beq j 506)) (Bool.rec (motive := fun _ => ℕ) 0 BK_507 (Nat.beq j 507)) (Nat.ble 507 j)
def BKs488_492 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs488_490 j) (BKs490_492 j) (Nat.ble 506 j)
def BKs492_494 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_508 (Nat.beq j 508)) (Bool.rec (motive := fun _ => ℕ) 0 BK_509 (Nat.beq j 509)) (Nat.ble 509 j)
def BKs494_496 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 BK_510 (Nat.beq j 510)) (Bool.rec (motive := fun _ => ℕ) 0 BK_511 (Nat.beq j 511)) (Nat.ble 511 j)
def BKs492_496 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs492_494 j) (BKs494_496 j) (Nat.ble 510 j)
def BKs488_496 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs488_492 j) (BKs492_496 j) (Nat.ble 508 j)
def BKs480_496 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs480_488 j) (BKs488_496 j) (Nat.ble 504 j)
def BKs465_496 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs465_480 j) (BKs480_496 j) (Nat.ble 496 j)
def BKs434_496 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs434_465 j) (BKs465_496 j) (Nat.ble 481 j)
def BKs372_496 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs372_434 j) (BKs434_496 j) (Nat.ble 450 j)
def BKs248_496 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs248_372 j) (BKs372_496 j) (Nat.ble 388 j)
def BKs0_496 (j : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (BKs0_248 j) (BKs248_496 j) (Nat.ble 264 j)
def BK (j : ℕ) : ℕ := (BKs0_496 j)

theorem top_ok : Pyr.topOk TOP BK = true := by decide +kernel

theorem blk_0 : Pyr.allFrom 0 56 (fun j => Pyr.blockOk (BK j) j) = true := by decide +kernel
theorem blk_1 : Pyr.allFrom 56 40 (fun j => Pyr.blockOk (BK j) j) = true := by decide +kernel
theorem blk_2 : Pyr.allFrom 96 40 (fun j => Pyr.blockOk (BK j) j) = true := by decide +kernel
theorem blk_3 : Pyr.allFrom 136 40 (fun j => Pyr.blockOk (BK j) j) = true := by decide +kernel
theorem blk_4 : Pyr.allFrom 176 40 (fun j => Pyr.blockOk (BK j) j) = true := by decide +kernel
theorem blk_5 : Pyr.allFrom 216 40 (fun j => Pyr.blockOk (BK j) j) = true := by decide +kernel
theorem blk_6 : Pyr.allFrom 256 40 (fun j => Pyr.blockOk (BK j) j) = true := by decide +kernel
theorem blk_7 : Pyr.allFrom 296 40 (fun j => Pyr.blockOk (BK j) j) = true := by decide +kernel
theorem blk_8 : Pyr.allFrom 336 40 (fun j => Pyr.blockOk (BK j) j) = true := by decide +kernel
theorem blk_9 : Pyr.allFrom 376 40 (fun j => Pyr.blockOk (BK j) j) = true := by decide +kernel
theorem blk_10 : Pyr.allFrom 416 40 (fun j => Pyr.blockOk (BK j) j) = true := by decide +kernel
theorem blk_11 : Pyr.allFrom 456 40 (fun j => Pyr.blockOk (BK j) j) = true := by decide +kernel
theorem blk_12 : Pyr.allFrom 496 16 (fun j => Pyr.blockOk (BK j) j) = true := by decide +kernel
theorem blk_all : Pyr.allFrom 0 512 (fun j => Pyr.blockOk (BK j) j) = true := by
  have h := (Pyr.allFrom_add (Pyr.allFrom_add (Pyr.allFrom_add (Pyr.allFrom_add (Pyr.allFrom_add (Pyr.allFrom_add (Pyr.allFrom_add (Pyr.allFrom_add (Pyr.allFrom_add (Pyr.allFrom_add (Pyr.allFrom_add (Pyr.allFrom_add blk_0 blk_1) blk_2) blk_3) blk_4) blk_5) blk_6) blk_7) blk_8) blk_9) blk_10) blk_11) blk_12)
  exact h
theorem lbS : Pyr.LBSound TOP BK := Pyr.lb_sound (Pyr.blocks_of blk_all) top_ok


def V6 : Riemann.Basin6.Wts6 := ⟨60390, 85125, 69521, 85125, 60390, 26016264, 95829761, 52826981, 100000000, 200000000, 47404723, 4170238, 94346036, 100000000, 53158024, 4170238, 52826981, 47404723, 95829761, 26016264⟩

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

def bd0 : Riemann.Basin6.BasinD6 := ⟨⟨32770, 35720, 63332, 66282, 32965, 35915, 63332, 66282, 32770, 35720⟩, 4488607871, 8494384118, 4514172429, 8494384115, 4488607864,
    ⟨4295229440, 4681891840, [], (282918903051 / 500000000000 : ℚ)⟩,
    ⟨12596281344, 12884901888, [13369606144], (34832790963 / 500000000000 : ℚ)⟩,
    ⟨16917069824, 17179869184, [18077057024], (-1131131103 / 100000000000 : ℚ)⟩,
    ⟨25218121728, 25769803776, [26764771328], (-3037974163 / 500000000000 : ℚ)⟩,
    ⟨29513351168, 30064771072, [30755717120, 31101190144, 31446663168], (-165936661 / 12500000000 : ℚ)⟩,
    ⟨8301051904, 8589934592, [8687714304], (67201211027 / 250000000000 : ℚ)⟩,
    ⟨12621840384, 12884901888, [13395165184], (15910763189 / 250000000000 : ℚ)⟩,
    ⟨20922892288, 21474836480, [22082879488], (213703917 / 10000000000 : ℚ)⟩,
    ⟨25218121728, 25769803776, [26764771328], (-3037974163 / 500000000000 : ℚ)⟩,
    ⟨4320788480, 4707450880, [], (120976850041 / 250000000000 : ℚ)⟩,
    ⟨12621840384, 12884901888, [13395165184], (15910763189 / 250000000000 : ℚ)⟩,
    ⟨16917069824, 17179869184, [18077057024], (-1131131103 / 100000000000 : ℚ)⟩,
    ⟨8301051904, 8589934592, [8687714304], (67201211027 / 250000000000 : ℚ)⟩,
    ⟨12596281344, 12884901888, [13369606144], (34832790963 / 500000000000 : ℚ)⟩,
    ⟨4295229440, 4681891840, [], (282918903051 / 500000000000 : ℚ)⟩⟩

theorem bas0 : SixW25P.Covered bd0.box.l0 bd0.box.u0 bd0.box.l1 bd0.box.u1 bd0.box.l2 bd0.box.u2 bd0.box.l3 bd0.box.u3 bd0.box.l4 bd0.box.u4 :=
  basin_cov bd0 (by decide +kernel)

def bd1 : Riemann.Basin6.BasinD6 := ⟨⟨63467, 66417, 32929, 35879, 63443, 66393, 32929, 35879, 63467, 66417⟩, 8512040452, 4509340586, 8508966460, 4509340592, 8512040446,
    ⟨8318746624, 8589934592, [8705409024], (34635991079 / 125000000000 : ℚ)⟩,
    ⟨12634816512, 12884901888, [13408141312], (30266937591 / 500000000000 : ℚ)⟩,
    ⟨20950417408, 21474836480, [22110404608], (600498341 / 31250000000 : ℚ)⟩,
    ⟨25266487296, 25769803776, [26813136896], (-900859553 / 100000000000 : ℚ)⟩,
    ⟨33585233920, 34359738368, [34939142144, 35518545920], (-2552525787 / 500000000000 : ℚ)⟩,
    ⟨4316069888, 4702732288, [], (24942809413 / 50000000000 : ℚ)⟩,
    ⟨12631670784, 12884901888, [13404995584], (30645371317 / 500000000000 : ℚ)⟩,
    ⟨16947740672, 17179869184, [18107727872], (-198040259 / 12500000000 : ℚ)⟩,
    ⟨25266487296, 25769803776, [26813136896], (-900859553 / 100000000000 : ℚ)⟩,
    ⟨8315600896, 8589934592, [8702263296], (137818860647 / 500000000000 : ℚ)⟩,
    ⟨12631670784, 12884901888, [13404995584], (30645371317 / 500000000000 : ℚ)⟩,
    ⟨20950417408, 21474836480, [22110404608], (600498341 / 31250000000 : ℚ)⟩,
    ⟨4316069888, 4702732288, [], (24942809413 / 50000000000 : ℚ)⟩,
    ⟨12634816512, 12884901888, [13408141312], (30266937591 / 500000000000 : ℚ)⟩,
    ⟨8318746624, 8589934592, [8705409024], (34635991079 / 125000000000 : ℚ)⟩⟩

theorem bas1 : SixW25P.Covered bd1.box.l0 bd1.box.u0 bd1.box.l1 bd1.box.u1 bd1.box.l2 bd1.box.u2 bd1.box.l3 bd1.box.u3 bd1.box.l4 bd1.box.u4 :=
  basin_cov bd1 (by decide +kernel)

def bd2 : Riemann.Basin6.BasinD6 := ⟨⟨32796, 35746, 62929, 65879, 32808, 35758, 32822, 35772, 63148, 66098⟩, 4491936723, 8441537088, 4493555393, 4495318265, 8470260963,
    ⟨4298637312, 4685299712, [], (138694394393 / 250000000000 : ℚ)⟩,
    ⟨12546867200, 12884901888, [13320192000], (10113584671 / 125000000000 : ℚ)⟩,
    ⟨16847077376, 17179869184, [18007064576], (-539817421 / 500000000000 : ℚ)⟩,
    ⟨21149122560, 21474836480, [22085304320, 22695772160], (-5467937021 / 250000000000 : ℚ)⟩,
    ⟨29426057216, 30064771072, [30712070144, 31359369216], (-3085683559 / 250000000000 : ℚ)⟩,
    ⟨8248229888, 8589934592, [8634892288], (15140906537 / 62500000000 : ℚ)⟩,
    ⟨12548440064, 12884901888, [13321764864], (4027962143 / 50000000000 : ℚ)⟩,
    ⟨16850485248, 17179869184, [18010472448], (-196669147 / 125000000000 : ℚ)⟩,
    ⟨25127419904, 25769803776, [26674069504], (-151070373 / 250000000000 : ℚ)⟩,
    ⟨4300210176, 4686872576, [], (68710880289 / 125000000000 : ℚ)⟩,
    ⟨8602255360, 9375580160, [], (-48655194361 / 500000000000 : ℚ)⟩,
    ⟨16879190016, 17179869184, [18039177216], (-2875742837 / 500000000000 : ℚ)⟩,
    ⟨4302045184, 4688707584, [], (271879696897 / 500000000000 : ℚ)⟩,
    ⟨12578979840, 12884901888, [13352304640], (18415881851 / 250000000000 : ℚ)⟩,
    ⟨8276934656, 8589934592, [8663597056], (128511080259 / 500000000000 : ℚ)⟩⟩

theorem bas2 : SixW25P.Covered bd2.box.l0 bd2.box.u0 bd2.box.l1 bd2.box.u1 bd2.box.l2 bd2.box.u2 bd2.box.l3 bd2.box.u3 bd2.box.l4 bd2.box.u4 :=
  basin_cov bd2 (by decide +kernel)

def bd3 : Riemann.Basin6.BasinD6 := ⟨⟨32874, 35824, 63588, 66538, 63922, 66872, 33046, 35996, 63452, 66402⟩, 4502186582, 8527943986, 8571682540, 4524699942, 8510052829,
    ⟨4308860928, 4695523328, [], (260924421267 / 500000000000 : ℚ)⟩,
    ⟨12643467264, 12884901888, [13416792064], (29221148703 / 500000000000 : ℚ)⟩,
    ⟨21021851648, 21474836480, [22181838848], (671367831 / 50000000000 : ℚ)⟩,
    ⟨25353256960, 25769803776, [26334855168, 26899906560], (-2267870679 / 250000000000 : ℚ)⟩,
    ⟨33670037504, 34359738368, [34981543936, 35603349504], (-1901809879 / 250000000000 : ℚ)⟩,
    ⟨8334606336, 8589934592, [8721268736], (28425251187 / 100000000000 : ℚ)⟩,
    ⟨16712990720, 17179869184, [17486315520], (6571780607 / 125000000000 : ℚ)⟩,
    ⟨21044396032, 21474836480, [22204383232], (360857393 / 31250000000 : ℚ)⟩,
    ⟨29361176576, 30064771072, [30907826176], (1583986509 / 500000000000 : ℚ)⟩,
    ⟨8378384384, 8589934592, [8765046784], (147587666571 / 500000000000 : ℚ)⟩,
    ⟨12709789696, 12884901888, [13483114496], (20966645311 / 500000000000 : ℚ)⟩,
    ⟨21026570240, 21474836480, [22186557440], (6517918881 / 500000000000 : ℚ)⟩,
    ⟨4331405312, 4718067712, [], (225281733961 / 500000000000 : ℚ)⟩,
    ⟨12648185856, 12884901888, [13421510656], (1145903939 / 20000000000 : ℚ)⟩,
    ⟨8316780544, 8589934592, [8703442944], (69045670071 / 250000000000 : ℚ)⟩⟩

theorem bas3 : SixW25P.Covered bd3.box.l0 bd3.box.u0 bd3.box.l1 bd3.box.u1 bd3.box.l2 bd3.box.u2 bd3.box.l3 bd3.box.u3 bd3.box.l4 bd3.box.u4 :=
  basin_cov bd3 (by decide +kernel)

def bd4 : Riemann.Basin6.BasinD6 := ⟨⟨32165, 35115, 32530, 35480, 63190, 66140, 32908, 35858, 63415, 66365⟩, 4409269602, 4457094890, 8475822184, 4506703533, 8505215912,
    ⟨4215930880, 4294967296, [4602593280], (473919882109 / 500000000000 : ℚ)⟩,
    ⟨8479703040, 8589934592, [9253027840], (-56652647 / 7812500000 : ℚ)⟩,
    ⟨16762142720, 17179869184, [17922129920], (27578683 / 2500000000 : ℚ)⟩,
    ⟨21075460096, 21474836480, [22048473088, 22622109696], (-2022715943 / 125000000000 : ℚ)⟩,
    ⟨29387390976, 30064771072, [30692737024, 31320702976], (-5449137063 / 500000000000 : ℚ)⟩,
    ⟨4263772160, 4294967296, [4650434560], (360240412181 / 500000000000 : ℚ)⟩,
    ⟨12546211840, 12884901888, [13319536640], (8105410747 / 100000000000 : ℚ)⟩,
    ⟨16859529216, 17179869184, [18019516416], (-5636871 / 1953125000 : ℚ)⟩,
    ⟨25171460096, 25769803776, [26718109696], (-813217711 / 250000000000 : ℚ)⟩,
    ⟨8282439680, 8589934592, [8669102080], (129880937647 / 500000000000 : ℚ)⟩,
    ⟨12595757056, 12884901888, [13369081856], (17446919967 / 250000000000 : ℚ)⟩,
    ⟨20907687936, 21474836480, [22067675136], (2254063101 / 100000000000 : ℚ)⟩,
    ⟨4313317376, 4699979776, [], (50761316997 / 100000000000 : ℚ)⟩,
    ⟨12625248256, 12884901888, [13398573056], (31414905447 / 500000000000 : ℚ)⟩,
    ⟨8311930880, 8589934592, [8698593280], (136966804513 / 500000000000 : ℚ)⟩⟩

theorem bas4 : SixW25P.Covered bd4.box.l0 bd4.box.u0 bd4.box.l1 bd4.box.u1 bd4.box.l2 bd4.box.u2 bd4.box.l3 bd4.box.u3 bd4.box.l4 bd4.box.u4 :=
  basin_cov bd4 (by decide +kernel)

def bd5 : Riemann.Basin6.BasinD6 := ⟨⟨32166, 35116, 32626, 35576, 63677, 66627, 63553, 66503, 32843, 35793⟩, 4409448627, 4469716428, 8539549172, 8523385289, 4498108710,
    ⟨4216061952, 4294967296, [4602724352], (94723127711 / 100000000000 : ℚ)⟩,
    ⟨8492417024, 8589934592, [9265741824], (-835682773 / 50000000000 : ℚ)⟩,
    ⟨16838688768, 17179869184, [17998675968], (667083 / 5000000000 : ℚ)⟩,
    ⟨25168707584, 25769803776, [26715357184], (-96461829 / 31250000000 : ℚ)⟩,
    ⟨29473505280, 30064771072, [30735794176, 31406817280], (-439686391 / 31250000000 : ℚ)⟩,
    ⟨4276355072, 4294967296, [4663017472], (329481603203 / 500000000000 : ℚ)⟩,
    ⟨12622626816, 12884901888, [13395951616], (31727796127 / 500000000000 : ℚ)⟩,
    ⟨20952645632, 21474836480, [22112632832], (4759895711 / 250000000000 : ℚ)⟩,
    ⟨25257443328, 25769803776, [26804092928], (-4230139371 / 500000000000 : ℚ)⟩,
    ⟨8346271744, 8589934592, [8732934144], (144683067271 / 500000000000 : ℚ)⟩,
    ⟨16676290560, 17179869184, [17449615360], (24258750161 / 500000000000 : ℚ)⟩,
    ⟨20981088256, 21474836480, [22141075456], (1676376863 / 100000000000 : ℚ)⟩,
    ⟨8330018816, 8589934592, [8716681216], (141102645103 / 500000000000 : ℚ)⟩,
    ⟨12634816512, 12884901888, [13408141312], (30266937591 / 500000000000 : ℚ)⟩,
    ⟨4304797696, 4691460096, [], (16715335343 / 31250000000 : ℚ)⟩⟩

theorem bas5 : SixW25P.Covered bd5.box.l0 bd5.box.u0 bd5.box.l1 bd5.box.u1 bd5.box.l2 bd5.box.u2 bd5.box.l3 bd5.box.u3 bd5.box.l4 bd5.box.u4 :=
  basin_cov bd5 (by decide +kernel)

def bd6 : Riemann.Basin6.BasinD6 := ⟨⟨32843, 35793, 63553, 66503, 63677, 66627, 32626, 35576, 32166, 35116⟩, 4498108709, 8523385291, 8539549164, 4469716431, 4409448620,
    ⟨4304797696, 4691460096, [], (16715335343 / 31250000000 : ℚ)⟩,
    ⟨12634816512, 12884901888, [13408141312], (30266937591 / 500000000000 : ℚ)⟩,
    ⟨20981088256, 21474836480, [22141075456], (1676376863 / 100000000000 : ℚ)⟩,
    ⟨25257443328, 25769803776, [26804092928], (-4230139371 / 500000000000 : ℚ)⟩,
    ⟨29473505280, 30064771072, [30735794176, 31406817280], (-439686391 / 31250000000 : ℚ)⟩,
    ⟨8330018816, 8589934592, [8716681216], (141102645103 / 500000000000 : ℚ)⟩,
    ⟨16676290560, 17179869184, [17449615360], (24258750161 / 500000000000 : ℚ)⟩,
    ⟨20952645632, 21474836480, [22112632832], (4759895711 / 250000000000 : ℚ)⟩,
    ⟨25168707584, 25769803776, [26715357184], (-96461829 / 31250000000 : ℚ)⟩,
    ⟨8346271744, 8589934592, [8732934144], (144683067271 / 500000000000 : ℚ)⟩,
    ⟨12622626816, 12884901888, [13395951616], (31727796127 / 500000000000 : ℚ)⟩,
    ⟨16838688768, 17179869184, [17998675968], (667083 / 5000000000 : ℚ)⟩,
    ⟨4276355072, 4294967296, [4663017472], (329481603203 / 500000000000 : ℚ)⟩,
    ⟨8492417024, 8589934592, [9265741824], (-835682773 / 50000000000 : ℚ)⟩,
    ⟨4216061952, 4294967296, [4602724352], (94723127711 / 100000000000 : ℚ)⟩⟩

theorem bas6 : SixW25P.Covered bd6.box.l0 bd6.box.u0 bd6.box.l1 bd6.box.u1 bd6.box.l2 bd6.box.u2 bd6.box.l3 bd6.box.u3 bd6.box.l4 bd6.box.u4 :=
  basin_cov bd6 (by decide +kernel)

def bd7 : Riemann.Basin6.BasinD6 := ⟨⟨32130, 35080, 32511, 35461, 62929, 65879, 32511, 35461, 32130, 35080⟩, 4404714956, 4454548246, 8441606042, 4454548242, 4404714953,
    ⟨4211343360, 4294967296, [4446486528, 4598005760], (596856527441 / 500000000000 : ℚ)⟩,
    ⟨8472625152, 8589934592, [8917942272, 9245949952], (39321016847 / 500000000000 : ℚ)⟩,
    ⟨16720855040, 17179869184, [17530355712, 17880842240], (2677609667 / 100000000000 : ℚ)⟩,
    ⟨20982136832, 21474836480, [22001811456, 22528786432], (-274548069 / 31250000000 : ℚ)⟩,
    ⟨25193480192, 25769803776, [26448297984, 26787545088, 27126792192], (-4337847987 / 250000000000 : ℚ)⟩,
    ⟨4261281792, 4294967296, [4471455744, 4647944192], (510289257451 / 500000000000 : ℚ)⟩,
    ⟨12509511680, 12884901888, [13083869184, 13282836480], (25397779309 / 250000000000 : ℚ)⟩,
    ⟨16770793472, 17179869184, [17555324928, 17930780672], (2588945599 / 125000000000 : ℚ)⟩,
    ⟨20982136832, 21474836480, [22001811456, 22528786432], (-274548069 / 31250000000 : ℚ)⟩,
    ⟨8248229888, 8419082240, [8589934592, 8634892288], (591239821 / 1953125000 : ℚ)⟩,
    ⟨12509511680, 12884901888, [13083869184, 13282836480], (25397779309 / 250000000000 : ℚ)⟩,
    ⟨16720855040, 17179869184, [17530355712, 17880842240], (2677609667 / 100000000000 : ℚ)⟩,
    ⟨4261281792, 4294967296, [4471455744, 4647944192], (510289257451 / 500000000000 : ℚ)⟩,
    ⟨8472625152, 8589934592, [8917942272, 9245949952], (39321016847 / 500000000000 : ℚ)⟩,
    ⟨4211343360, 4294967296, [4446486528, 4598005760], (596856527441 / 500000000000 : ℚ)⟩⟩

theorem bas7 : SixW25P.Covered bd7.box.l0 bd7.box.u0 bd7.box.l1 bd7.box.u1 bd7.box.l2 bd7.box.u2 bd7.box.l3 bd7.box.u3 bd7.box.l4 bd7.box.u4 :=
  basin_cov bd7 (by decide +kernel)

def bd8 : Riemann.Basin6.BasinD6 := ⟨⟨32862, 35812, 63790, 66740, 64216, 67166, 63790, 66740, 32862, 35812⟩, 4500680638, 8554459600, 8610233801, 8554459593, 4500680644,
    ⟨4307288064, 4693950464, [], (6586128223 / 12500000000 : ℚ)⟩,
    ⟨12668370944, 12884901888, [13441695744], (5233943013 / 100000000000 : ℚ)⟩,
    ⟨21085290496, 21474836480, [22245277696], (808085603 / 100000000000 : ℚ)⟩,
    ⟨29446373376, 30064771072, [30993022976], (-58843719 / 125000000000 : ℚ)⟩,
    ⟨33753661440, 34359738368, [35023355904, 35686973440], (-4989713087 / 500000000000 : ℚ)⟩,
    ⟨8361082880, 8589934592, [8747745280], (29566843579 / 100000000000 : ℚ)⟩,
    ⟨16778002432, 17179869184, [17551327232], (28321801827 / 500000000000 : ℚ)⟩,
    ⟨25139085312, 25769803776, [26299072512], (133604933 / 7812500000 : ℚ)⟩,
    ⟨29446373376, 30064771072, [30993022976], (-58843719 / 125000000000 : ℚ)⟩,
    ⟨8416919552, 8589934592, [8803581952], (138187853661 / 500000000000 : ℚ)⟩,
    ⟨16778002432, 17179869184, [17551327232], (28321801827 / 500000000000 : ℚ)⟩,
    ⟨21085290496, 21474836480, [22245277696], (808085603 / 100000000000 : ℚ)⟩,
    ⟨8361082880, 8589934592, [8747745280], (29566843579 / 100000000000 : ℚ)⟩,
    ⟨12668370944, 12884901888, [13441695744], (5233943013 / 100000000000 : ℚ)⟩,
    ⟨4307288064, 4693950464, [], (6586128223 / 12500000000 : ℚ)⟩⟩

theorem bas8 : SixW25P.Covered bd8.box.l0 bd8.box.u0 bd8.box.l1 bd8.box.u1 bd8.box.l2 bd8.box.u2 bd8.box.l3 bd8.box.u3 bd8.box.l4 bd8.box.u4 :=
  basin_cov bd8 (by decide +kernel)

def bd9 : Riemann.Basin6.BasinD6 := ⟨⟨32803, 35753, 63371, 66321, 33030, 35980, 63955, 66905, 64092, 67042⟩, 4492845615, 8499455565, 4522636519, 8576104602, 8594014506,
    ⟨4299554816, 4686217216, [], (275903505407 / 500000000000 : ℚ)⟩,
    ⟨12605718528, 12884901888, [13379043328], (16864456741 / 250000000000 : ℚ)⟩,
    ⟨16935026688, 17179869184, [18095013888], (-1396185403 / 100000000000 : ℚ)⟩,
    ⟨25317736448, 25769803776, [26317094912, 26864386048], (-356970743 / 50000000000 : ℚ)⟩,
    ⟨33718403072, 34359738368, [35005726720, 35651715072], (-1124103427 / 125000000000 : ℚ)⟩,
    ⟨8306163712, 8589934592, [8692826112], (13561457409 / 50000000000 : ℚ)⟩,
    ⟨12635471872, 12884901888, [13408796672], (15093986129 / 250000000000 : ℚ)⟩,
    ⟨21018181632, 21474836480, [22178168832], (858196059 / 62500000000 : ℚ)⟩,
    ⟨29418848256, 30064771072, [30965497856], (7135571 / 10000000000 : ℚ)⟩,
    ⟨4329308160, 4715970560, [], (22855904153 / 50000000000 : ℚ)⟩,
    ⟨12712017920, 12884901888, [13485342720], (20682402827 / 500000000000 : ℚ)⟩,
    ⟨21112684544, 21474836480, [22272671744], (1430543483 / 250000000000 : ℚ)⟩,
    ⟨8382709760, 8589934592, [8769372160], (36639696513 / 125000000000 : ℚ)⟩,
    ⟨16783376384, 17179869184, [17556701184], (5609710453 / 100000000000 : ℚ)⟩,
    ⟨8400666624, 8589934592, [8787329024], (142216106711 / 500000000000 : ℚ)⟩⟩

theorem bas9 : SixW25P.Covered bd9.box.l0 bd9.box.u0 bd9.box.l1 bd9.box.u1 bd9.box.l2 bd9.box.u2 bd9.box.l3 bd9.box.u3 bd9.box.l4 bd9.box.u4 :=
  basin_cov bd9 (by decide +kernel)

def bd10 : Riemann.Basin6.BasinD6 := ⟨⟨63206, 66156, 32848, 35798, 32882, 35832, 63481, 66431, 64179, 67129⟩, 8477890536, 4498801467, 4503241646, 8513950447, 8605381172,
    ⟨8284536832, 8589934592, [8671199232], (130398880649 / 500000000000 : ℚ)⟩,
    ⟨12589989888, 12884901888, [13363314688], (17781717097 / 250000000000 : ℚ)⟩,
    ⟨16899899392, 17179869184, [18059886592], (-274541011 / 31250000000 : ℚ)⟩,
    ⟨25220481024, 25769803776, [26767130624], (-1554737419 / 250000000000 : ℚ)⟩,
    ⟨33632550912, 34359738368, [34962800640, 35565862912], (-3255538321 / 500000000000 : ℚ)⟩,
    ⟨4305453056, 4692115456, [], (266391587501 / 500000000000 : ℚ)⟩,
    ⟨8615362560, 9388687360, [], (-51948061509 / 500000000000 : ℚ)⟩,
    ⟨16935944192, 17179869184, [18095931392], (-281950011 / 20000000000 : ℚ)⟩,
    ⟨25348014080, 25769803776, [26332233728, 26894663680], (-878729407 / 100000000000 : ℚ)⟩,
    ⟨4309909504, 4696571904, [], (259246423607 / 500000000000 : ℚ)⟩,
    ⟨12630491136, 12884901888, [13403815936], (15393513611 / 250000000000 : ℚ)⟩,
    ⟨21042561024, 21474836480, [22202548224], (5850660391 / 500000000000 : ℚ)⟩,
    ⟨8320581632, 8589934592, [8707244032], (69482356467 / 250000000000 : ℚ)⟩,
    ⟨16732651520, 17179869184, [17505976320], (27328825557 / 500000000000 : ℚ)⟩,
    ⟨8412069888, 8589934592, [8798732288], (139399439369 / 500000000000 : ℚ)⟩⟩

theorem bas10 : SixW25P.Covered bd10.box.l0 bd10.box.u0 bd10.box.l1 bd10.box.u1 bd10.box.l2 bd10.box.u2 bd10.box.l3 bd10.box.u3 bd10.box.l4 bd10.box.u4 :=
  basin_cov bd10 (by decide +kernel)

def bd11 : Riemann.Basin6.BasinD6 := ⟨⟨64179, 67129, 63481, 66431, 32882, 35832, 32848, 35798, 63206, 66156⟩, 8605381181, 8513950445, 4503241645, 4498801468, 8477890542,
    ⟨8412069888, 8589934592, [8798732288], (139399439369 / 500000000000 : ℚ)⟩,
    ⟨16732651520, 17179869184, [17505976320], (27328825557 / 500000000000 : ℚ)⟩,
    ⟨21042561024, 21474836480, [22202548224], (5850660391 / 500000000000 : ℚ)⟩,
    ⟨25348014080, 25769803776, [26332233728, 26894663680], (-878729407 / 100000000000 : ℚ)⟩,
    ⟨33632550912, 34359738368, [34962800640, 35565862912], (-3255538321 / 500000000000 : ℚ)⟩,
    ⟨8320581632, 8589934592, [8707244032], (69482356467 / 250000000000 : ℚ)⟩,
    ⟨12630491136, 12884901888, [13403815936], (15393513611 / 250000000000 : ℚ)⟩,
    ⟨16935944192, 17179869184, [18095931392], (-281950011 / 20000000000 : ℚ)⟩,
    ⟨25220481024, 25769803776, [26767130624], (-1554737419 / 250000000000 : ℚ)⟩,
    ⟨4309909504, 4696571904, [], (259246423607 / 500000000000 : ℚ)⟩,
    ⟨8615362560, 9388687360, [], (-51948061509 / 500000000000 : ℚ)⟩,
    ⟨16899899392, 17179869184, [18059886592], (-274541011 / 31250000000 : ℚ)⟩,
    ⟨4305453056, 4692115456, [], (266391587501 / 500000000000 : ℚ)⟩,
    ⟨12589989888, 12884901888, [13363314688], (17781717097 / 250000000000 : ℚ)⟩,
    ⟨8284536832, 8589934592, [8671199232], (130398880649 / 500000000000 : ℚ)⟩⟩

theorem bas11 : SixW25P.Covered bd11.box.l0 bd11.box.u0 bd11.box.l1 bd11.box.u1 bd11.box.l2 bd11.box.u2 bd11.box.l3 bd11.box.u3 bd11.box.l4 bd11.box.u4 :=
  basin_cov bd11 (by decide +kernel)

def bd12 : Riemann.Basin6.BasinD6 := ⟨⟨31979, 34929, 32376, 35326, 32659, 35609, 62825, 65775, 32748, 35698⟩, 4384853898, 4436969805, 4474022042, 8427893831, 4485739181,
    ⟨4191551488, 4294967296, [4578213888], (105961091099 / 100000000000 : ℚ)⟩,
    ⟨8435138560, 8589934592, [9208463360], (12713368011 / 500000000000 : ℚ)⟩,
    ⟨12715819008, 12884901888, [13875806208], (-33752995229 / 500000000000 : ℚ)⟩,
    ⟨20950417408, 21474836480, [22497067008], (-7138571403 / 500000000000 : ℚ)⟩,
    ⟨25242763264, 25769803776, [26472939520, 26824507392, 27176075264], (-122049479 / 6250000000 : ℚ)⟩,
    ⟨4243587072, 4294967296, [4630249472], (10221041641 / 12500000000 : ℚ)⟩,
    ⟨8524267520, 8589934592, [9297592320], (-20335339659 / 500000000000 : ℚ)⟩,
    ⟨16758865920, 17179869184, [17918853120], (287255221 / 25000000000 : ℚ)⟩,
    ⟨21051211776, 21474836480, [22036348928, 22597861376], (-3568994849 / 250000000000 : ℚ)⟩,
    ⟨4280680448, 4294967296, [4667342848], (159413680963 / 250000000000 : ℚ)⟩,
    ⟨12515278848, 12884901888, [13288603648], (5487784991 / 62500000000 : ℚ)⟩,
    ⟨16807624704, 17179869184, [17967611904], (114886637 / 25000000000 : ℚ)⟩,
    ⟨8234598400, 8589934592, [8621260800], (117478917311 / 500000000000 : ℚ)⟩,
    ⟨12526944256, 12884901888, [13300269056], (2132131451 / 25000000000 : ℚ)⟩,
    ⟨4292345856, 4294967296, [4679008256], (289888924883 / 500000000000 : ℚ)⟩⟩

theorem bas12 : SixW25P.Covered bd12.box.l0 bd12.box.u0 bd12.box.l1 bd12.box.u1 bd12.box.l2 bd12.box.u2 bd12.box.l3 bd12.box.u3 bd12.box.l4 bd12.box.u4 :=
  basin_cov bd12 (by decide +kernel)

def bd13 : Riemann.Basin6.BasinD6 := ⟨⟨32748, 35698, 62825, 65775, 32659, 35609, 32376, 35326, 31979, 34929⟩, 4485739182, 8427893828, 4474022049, 4436969809, 4384853897,
    ⟨4292345856, 4294967296, [4679008256], (289888924883 / 500000000000 : ℚ)⟩,
    ⟨12526944256, 12884901888, [13300269056], (2132131451 / 25000000000 : ℚ)⟩,
    ⟨16807624704, 17179869184, [17967611904], (114886637 / 25000000000 : ℚ)⟩,
    ⟨21051211776, 21474836480, [22036348928, 22597861376], (-3568994849 / 250000000000 : ℚ)⟩,
    ⟨25242763264, 25769803776, [26472939520, 26824507392, 27176075264], (-122049479 / 6250000000 : ℚ)⟩,
    ⟨8234598400, 8589934592, [8621260800], (117478917311 / 500000000000 : ℚ)⟩,
    ⟨12515278848, 12884901888, [13288603648], (5487784991 / 62500000000 : ℚ)⟩,
    ⟨16758865920, 17179869184, [17918853120], (287255221 / 25000000000 : ℚ)⟩,
    ⟨20950417408, 21474836480, [22497067008], (-7138571403 / 500000000000 : ℚ)⟩,
    ⟨4280680448, 4294967296, [4667342848], (159413680963 / 250000000000 : ℚ)⟩,
    ⟨8524267520, 8589934592, [9297592320], (-20335339659 / 500000000000 : ℚ)⟩,
    ⟨12715819008, 12884901888, [13875806208], (-33752995229 / 500000000000 : ℚ)⟩,
    ⟨4243587072, 4294967296, [4630249472], (10221041641 / 12500000000 : ℚ)⟩,
    ⟨8435138560, 8589934592, [9208463360], (12713368011 / 500000000000 : ℚ)⟩,
    ⟨4191551488, 4294967296, [4578213888], (105961091099 / 100000000000 : ℚ)⟩⟩

theorem bas13 : SixW25P.Covered bd13.box.l0 bd13.box.u0 bd13.box.l1 bd13.box.u1 bd13.box.l2 bd13.box.u2 bd13.box.l3 bd13.box.u3 bd13.box.l4 bd13.box.u4 :=
  basin_cov bd13 (by decide +kernel)

def bd14 : Riemann.Basin6.BasinD6 := ⟨⟨32247, 35197, 32669, 35619, 95120, 98070, 33064, 36014, 63561, 66511⟩, 4420005976, 4475342283, 12660906605, 4527059296, 8524421322,
    ⟨4226678784, 4294967296, [4613341184], (448838897673 / 500000000000 : ℚ)⟩,
    ⟨8508669952, 8589934592, [9281994752], (-577890793 / 20000000000 : ℚ)⟩,
    ⟨20976238592, 21474836480, [22136225792], (8577482899 / 500000000000 : ℚ)⟩,
    ⟨25310003200, 25769803776, [26313228288, 26856652800], (-1679229243 / 250000000000 : ℚ)⟩,
    ⟨33641070592, 34359738368, [34967060480, 35574382592], (-3380864877 / 500000000000 : ℚ)⟩,
    ⟨4281991168, 4294967296, [4668653568], (315590684361 / 500000000000 : ℚ)⟩,
    ⟨16749559808, 17179869184, [17522884608], (28199144357 / 500000000000 : ℚ)⟩,
    ⟨21083324416, 21474836480, [22243311616], (164981377 / 20000000000 : ℚ)⟩,
    ⟨29414391808, 30064771072, [30961041408], (5653879 / 6250000000 : ℚ)⟩,
    ⟨12467568640, 12854231040, [], (50318095611 / 500000000000 : ℚ)⟩,
    ⟨16801333248, 17179869184, [17574658048], (27121066357 / 500000000000 : ℚ)⟩,
    ⟨25132400640, 25769803776, [26292387840], (1047030197 / 62500000000 : ℚ)⟩,
    ⟨4333764608, 4720427008, [], (11080205489 / 25000000000 : ℚ)⟩,
    ⟨12664832000, 12884901888, [13438156800], (5321393377 / 100000000000 : ℚ)⟩,
    ⟨8331067392, 8589934592, [8717729792], (70668758043 / 250000000000 : ℚ)⟩⟩

theorem bas14 : SixW25P.Covered bd14.box.l0 bd14.box.u0 bd14.box.l1 bd14.box.u1 bd14.box.l2 bd14.box.u2 bd14.box.l3 bd14.box.u3 bd14.box.l4 bd14.box.u4 :=
  basin_cov bd14 (by decide +kernel)

def bd15 : Riemann.Basin6.BasinD6 := ⟨⟨63595, 66545, 33071, 36021, 95398, 98348, 33071, 36021, 63595, 66545⟩, 8528839146, 4528009762, 12697399985, 4528009768, 8528839140,
    ⟨8335523840, 8589934592, [8722186240], (142329749629 / 500000000000 : ℚ)⟩,
    ⟨12670205952, 12884901888, [13443530752], (259425267 / 5000000000 : ℚ)⟩,
    ⟨25174212608, 25769803776, [26334199808], (9155295513 / 500000000000 : ℚ)⟩,
    ⟨29508894720, 30064771072, [31055544320], (-159027633 / 50000000000 : ℚ)⟩,
    ⟨37844418560, 38654705664, [39216218112, 39777730560], (-369724493 / 125000000000 : ℚ)⟩,
    ⟨4334682112, 4721344512, [], (27522074089 / 62500000000 : ℚ)⟩,
    ⟨16838688768, 17179869184, [17612013568], (12561081417 / 250000000000 : ℚ)⟩,
    ⟨21173370880, 21474836480, [22333358080], (205026473 / 500000000000 : ℚ)⟩,
    ⟨29508894720, 30064771072, [31055544320], (-159027633 / 50000000000 : ℚ)⟩,
    ⟨12504006656, 12884901888, [12890669056], (26271713829 / 250000000000 : ℚ)⟩,
    ⟨16838688768, 17179869184, [17612013568], (12561081417 / 250000000000 : ℚ)⟩,
    ⟨25174212608, 25769803776, [26334199808], (9155295513 / 500000000000 : ℚ)⟩,
    ⟨4334682112, 4721344512, [], (27522074089 / 62500000000 : ℚ)⟩,
    ⟨12670205952, 12884901888, [13443530752], (259425267 / 5000000000 : ℚ)⟩,
    ⟨8335523840, 8589934592, [8722186240], (142329749629 / 500000000000 : ℚ)⟩⟩

theorem bas15 : SixW25P.Covered bd15.box.l0 bd15.box.u0 bd15.box.l1 bd15.box.u1 bd15.box.l2 bd15.box.u2 bd15.box.l3 bd15.box.u3 bd15.box.l4 bd15.box.u4 :=
  basin_cov bd15 (by decide +kernel)

def bd16 : Riemann.Basin6.BasinD6 := ⟨⟨32225, 35175, 32662, 35612, 94835, 97785, 32662, 35612, 32225, 35175⟩, 4417129120, 4474414254, 12623528382, 4474414262, 4417129106,
    ⟨4223795200, 4294967296, [4610457600], (455594315557 / 500000000000 : ℚ)⟩,
    ⟨8504868864, 8589934592, [9278193664], (-6509353857 / 250000000000 : ℚ)⟩,
    ⟨20935081984, 21474836480, [22095069184], (5105468041 / 250000000000 : ℚ)⟩,
    ⟨25216155648, 25769803776, [26762805248], (-595679269 / 100000000000 : ℚ)⟩,
    ⟨29439950848, 30064771072, [30719016960, 31373262848], (-6426967961 / 500000000000 : ℚ)⟩,
    ⟨4281073664, 4294967296, [4667736064], (317856754523 / 500000000000 : ℚ)⟩,
    ⟨16711286784, 17179869184, [17484611584], (3274418977 / 62500000000 : ℚ)⟩,
    ⟨20992360448, 21474836480, [22152347648], (7924828729 / 500000000000 : ℚ)⟩,
    ⟨25216155648, 25769803776, [26762805248], (-595679269 / 100000000000 : ℚ)⟩,
    ⟨12430213120, 12816875520, [], (48075650677 / 500000000000 : ℚ)⟩,
    ⟨16711286784, 17179869184, [17484611584], (3274418977 / 62500000000 : ℚ)⟩,
    ⟨20935081984, 21474836480, [22095069184], (5105468041 / 250000000000 : ℚ)⟩,
    ⟨4281073664, 4294967296, [4667736064], (317856754523 / 500000000000 : ℚ)⟩,
    ⟨8504868864, 8589934592, [9278193664], (-6509353857 / 250000000000 : ℚ)⟩,
    ⟨4223795200, 4294967296, [4610457600], (455594315557 / 500000000000 : ℚ)⟩⟩

theorem bas16 : SixW25P.Covered bd16.box.l0 bd16.box.u0 bd16.box.l1 bd16.box.u1 bd16.box.l2 bd16.box.u2 bd16.box.l3 bd16.box.u3 bd16.box.l4 bd16.box.u4 :=
  basin_cov bd16 (by decide +kernel)

def bd17 : Riemann.Basin6.BasinD6 := ⟨⟨33068, 36018, 94812, 97762, 32994, 35944, 32958, 35908, 63213, 66163⟩, 4527564109, 12620544533, 4517961127, 4513163448, 8478746608,
    ⟨4334288896, 4720951296, [], (5519705069 / 12500000000 : ℚ)⟩,
    ⟨16761487360, 17179869184, [17534812160], (575974281 / 10000000000 : ℚ)⟩,
    ⟨21086076928, 21474836480, [22246064128], (80135293 / 10000000000 : ℚ)⟩,
    ⟨25405947904, 25769803776, [26361200640, 26952597504], (-5951665243 / 500000000000 : ℚ)⟩,
    ⟨33691402240, 34359738368, [34992226304, 35624714240], (-4111811549 / 500000000000 : ℚ)⟩,
    ⟨12427198464, 12813860864, [], (47885095293 / 500000000000 : ℚ)⟩,
    ⟨16751788032, 17179869184, [17525112832], (7078014811 / 125000000000 : ℚ)⟩,
    ⟨21071659008, 21474836480, [22231646208], (4622009259 / 500000000000 : ℚ)⟩,
    ⟨29357113344, 30064771072, [30903762944], (333922153 / 100000000000 : ℚ)⟩,
    ⟨4324589568, 4711251968, [], (117980810239 / 250000000000 : ℚ)⟩,
    ⟨8644460544, 9417785344, [], (-2368514233 / 20000000000 : ℚ)⟩,
    ⟨16929914880, 17179869184, [18089902080], (-6603239757 / 500000000000 : ℚ)⟩,
    ⟨4319870976, 4706533376, [], (60850983253 / 125000000000 : ℚ)⟩,
    ⟨12605325312, 12884901888, [13378650112], (1688754821 / 25000000000 : ℚ)⟩,
    ⟨8285454336, 8589934592, [8672116736], (130624803049 / 500000000000 : ℚ)⟩⟩

theorem bas17 : SixW25P.Covered bd17.box.l0 bd17.box.u0 bd17.box.l1 bd17.box.u1 bd17.box.l2 bd17.box.u2 bd17.box.l3 bd17.box.u3 bd17.box.l4 bd17.box.u4 :=
  basin_cov bd17 (by decide +kernel)

def basList : List Riemann.Basin6.Box6 := [⟨32770, 35720, 63332, 66282, 32965, 35915, 63332, 66282, 32770, 35720⟩, ⟨63467, 66417, 32929, 35879, 63443, 66393, 32929, 35879, 63467, 66417⟩, ⟨32796, 35746, 62929, 65879, 32808, 35758, 32822, 35772, 63148, 66098⟩, ⟨32874, 35824, 63588, 66538, 63922, 66872, 33046, 35996, 63452, 66402⟩, ⟨32165, 35115, 32530, 35480, 63190, 66140, 32908, 35858, 63415, 66365⟩, ⟨32166, 35116, 32626, 35576, 63677, 66627, 63553, 66503, 32843, 35793⟩, ⟨32843, 35793, 63553, 66503, 63677, 66627, 32626, 35576, 32166, 35116⟩, ⟨32130, 35080, 32511, 35461, 62929, 65879, 32511, 35461, 32130, 35080⟩, ⟨32862, 35812, 63790, 66740, 64216, 67166, 63790, 66740, 32862, 35812⟩, ⟨32803, 35753, 63371, 66321, 33030, 35980, 63955, 66905, 64092, 67042⟩, ⟨63206, 66156, 32848, 35798, 32882, 35832, 63481, 66431, 64179, 67129⟩, ⟨64179, 67129, 63481, 66431, 32882, 35832, 32848, 35798, 63206, 66156⟩, ⟨31979, 34929, 32376, 35326, 32659, 35609, 62825, 65775, 32748, 35698⟩, ⟨32748, 35698, 62825, 65775, 32659, 35609, 32376, 35326, 31979, 34929⟩, ⟨32247, 35197, 32669, 35619, 95120, 98070, 33064, 36014, 63561, 66511⟩, ⟨63595, 66545, 33071, 36021, 95398, 98348, 33071, 36021, 63595, 66545⟩, ⟨32225, 35175, 32662, 35612, 94835, 97785, 32662, 35612, 32225, 35175⟩, ⟨33068, 36018, 94812, 97762, 32994, 35944, 32958, 35908, 63213, 66163⟩]

theorem hbas : ∀ B ∈ basList, SixW25P.Covered B.l0 B.u0 B.l1 B.u1 B.l2 B.u2 B.l3 B.u3 B.l4 B.u4 := by
  intro B hB
  simp only [basList, List.mem_cons, List.not_mem_nil, or_false] at hB
  rcases hB with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [bas0, bas1, bas2, bas3, bas4, bas5, bas6, bas7, bas8, bas9, bas10, bas11, bas12, bas13, bas14, bas15, bas16, bas17]

def cover0 : List (ℕ × ℕ × Bool) := [
  (16384, 20480, true),
  (20480, 24576, true),
  (24576, 28672, true),
  (28672, 29184, true),
  (29184, 29440, true),
  (29440, 29568, true),
  (29568, 29696, true),
  (29696, 29712, true),
  (29712, 29720, true),
  (29720, 44064, false),
  (44064, 44072, true),
  (44072, 44080, true),
  (44080, 44096, true),
  (44096, 44128, true),
  (44128, 44160, true),
  (44160, 44224, true),
  (44224, 44288, true),
  (44288, 44416, true),
  (44416, 44544, true),
  (44544, 44800, true),
  (44800, 45056, true),
  (45056, 45568, true),
  (45568, 46080, true),
  (46080, 47104, true),
  (47104, 49152, true),
  (49152, 50176, true),
  (50176, 51200, true),
  (51200, 52224, true),
  (52224, 52480, true),
  (52480, 52736, true),
  (52736, 52864, true),
  (52864, 52992, true),
  (52992, 53024, true),
  (53024, 53056, true),
  (53056, 53072, true),
  (53072, 53080, true),
  (53080, 354601, false)]

theorem cover0_ok : SixW25P.coverCheck 26016264 (SC / 2) 354601 cover0 = true := by decide +kernel

def cover1 : List (ℕ × ℕ × Bool) := [
  (16384, 20480, true),
  (20480, 24576, true),
  (24576, 28672, true),
  (28672, 29696, true),
  (29696, 30720, true),
  (30720, 30848, true),
  (30848, 30912, true),
  (30912, 30944, true),
  (30944, 40544, false),
  (40544, 40560, true),
  (40560, 40576, true),
  (40576, 40640, true),
  (40640, 40704, true),
  (40704, 40960, true),
  (40960, 41984, true),
  (41984, 43008, true),
  (43008, 45056, true),
  (45056, 49152, true),
  (49152, 53248, true),
  (53248, 55296, true),
  (55296, 56320, true),
  (56320, 56832, true),
  (56832, 57088, true),
  (57088, 57344, true),
  (57344, 57408, true),
  (57408, 57440, true),
  (57440, 57456, true),
  (57456, 57472, true),
  (57472, 251564, false)]

theorem cover1_ok : SixW25P.coverCheck 47404723 (SC / 2) 251564 cover1 = true := by decide +kernel

def cover2 : List (ℕ × ℕ × Bool) := [
  (16384, 20480, true),
  (20480, 24576, true),
  (24576, 28672, true),
  (28672, 30720, true),
  (30720, 30976, true),
  (30976, 31104, true),
  (31104, 31136, true),
  (31136, 31144, true),
  (31144, 40128, false),
  (40128, 40144, true),
  (40144, 40160, true),
  (40160, 40192, true),
  (40192, 40320, true),
  (40320, 40448, true),
  (40448, 40960, true),
  (40960, 43008, true),
  (43008, 45056, true),
  (45056, 49152, true),
  (49152, 53248, true),
  (53248, 55296, true),
  (55296, 57344, true),
  (57344, 57856, true),
  (57856, 57984, true),
  (57984, 58016, true),
  (58016, 58032, true),
  (58032, 58040, true),
  (58040, 308028, false)]

theorem cover2_ok : SixW25P.coverCheck 53158024 (SC / 2) 308028 cover2 = true := by decide +kernel

def cover3 : List (ℕ × ℕ × Bool) := [
  (16384, 20480, true),
  (20480, 24576, true),
  (24576, 28672, true),
  (28672, 29696, true),
  (29696, 30720, true),
  (30720, 30848, true),
  (30848, 30912, true),
  (30912, 30944, true),
  (30944, 40544, false),
  (40544, 40560, true),
  (40560, 40576, true),
  (40576, 40640, true),
  (40640, 40704, true),
  (40704, 40960, true),
  (40960, 41984, true),
  (41984, 43008, true),
  (43008, 45056, true),
  (45056, 49152, true),
  (49152, 53248, true),
  (53248, 55296, true),
  (55296, 56320, true),
  (56320, 56832, true),
  (56832, 57088, true),
  (57088, 57344, true),
  (57344, 57408, true),
  (57408, 57440, true),
  (57440, 57456, true),
  (57456, 57472, true),
  (57472, 251564, false)]

theorem cover3_ok : SixW25P.coverCheck 47404723 (SC / 2) 251564 cover3 = true := by decide +kernel

def cover4 : List (ℕ × ℕ × Bool) := [
  (16384, 20480, true),
  (20480, 24576, true),
  (24576, 28672, true),
  (28672, 29184, true),
  (29184, 29440, true),
  (29440, 29568, true),
  (29568, 29696, true),
  (29696, 29712, true),
  (29712, 29720, true),
  (29720, 44064, false),
  (44064, 44072, true),
  (44072, 44080, true),
  (44080, 44096, true),
  (44096, 44128, true),
  (44128, 44160, true),
  (44160, 44224, true),
  (44224, 44288, true),
  (44288, 44416, true),
  (44416, 44544, true),
  (44544, 44800, true),
  (44800, 45056, true),
  (45056, 45568, true),
  (45568, 46080, true),
  (46080, 47104, true),
  (47104, 49152, true),
  (49152, 50176, true),
  (50176, 51200, true),
  (51200, 52224, true),
  (52224, 52480, true),
  (52480, 52736, true),
  (52736, 52864, true),
  (52864, 52992, true),
  (52992, 53024, true),
  (53024, 53056, true),
  (53056, 53072, true),
  (53072, 53080, true),
  (53080, 354601, false)]

theorem cover4_ok : SixW25P.coverCheck 26016264 (SC / 2) 354601 cover4 = true := by decide +kernel

theorem wk0llllll : SixW25P.Covered 29720 36892 30944 33344 31144 35636 30944 35744 29720 36892 :=
  SixW25P.covered_of_walk lbS hbas 154606084183250653671346211860149444322624991590567882002963711604442490251859485991499034977525006439818234374793470655649541999961030786455272419621806011187266522525458946654550377471750332522519545419857000731374196621510739196889704514945526899736676450138848383345383003120659653887445436618438728737726375668220006597862090463477785495641046959401963863179701866211749351549439824860625283470296265321910780942294265427691390744353596890942159090598126602292339558891702892477123307837337720592893354678512464098935317479000456594402446074277010475249687260871699266032963748735134017926316058884981326621575984432239126383244465837241509783514833169398908041563350469199020422622143565468140880414791290472366949084685986841802728529972757799589428003572634618073680930 200 29720 36892 30944 33344 31144 35636 30944 35744 29720 36892 2587
    (by decide +kernel) (by decide)
theorem wk0lllllr : SixW25P.Covered 29720 36892 33344 35744 31144 35636 30944 35744 29720 36892 :=
  SixW25P.covered_of_walk lbS hbas 82397792137551083768677949108510811444642478505131569316849176446139869973806531233181153288232836941753446781161286093889967977584801236701971982259335126034449738872448978844008435489621573064579530874829283221478906064702677017032138594025419834037819735601005499666292088137758966342155699767695161360242482874408183647315819564859602999251076243602170124290723381238573471467786369826775379912255675920920841983328816695464467044928164038374983892276407810899370660258238132106757400833052830152868302132781462145338606655042573910614557721525071622994346099024039107545714482897143418894212716895669591684607092196903257437174874819507211528004699946019042308422255098793372394917345195339899623215708621914317043662385110519424977685794902655470169435843548629692930214940407408437637796044704155232453666612007998031350438837619728882765081591342991215760503372119975360401338102737347231394513959138691068029843311891397415985319052775056144867210725256372183261856763883763469214090921925019881369347694053090189440218059086042737059566103831263054365391484824258888553487134593212520680878845808924356943248344903489144147144967292558413397069560878296670208873107595529560513282736112004848368797119619267052753920617874115906952277974440313630035402739452233018086711566604900192396839166383810895908637579978162776237981734345811413331153863642446130868244855699043332855213147851581253661101642707623227199329809970783831529914815736944600280359418288567228813648943753735175243812678079489642993332865932457547063677445651583622047561547810186969363873508723762862462288861522521705811773187575674740360745742432619418133923521724886027130425628535126798938442350883471255380415636676383679562270142422311569387993038621597295103264944166986036449941524672992373851487929311450158534981330733124215444368299255496537448301975288446188570323612890622901809808131865099829335528163931386957426754737695047767467391602711961782949121170716811021273534714867762529650494468822645520084214949532030672972757524874531554018 200 29720 36892 33344 35744 31144 35636 30944 35744 29720 36892 6762
    (by decide +kernel) (by decide)
theorem wk0lllll : SixW25P.Covered 29720 36892 30944 35744 31144 35636 30944 35744 29720 36892 :=
  SixW25P.covered_split1 33344 wk0llllll wk0lllllr
theorem wk0llllr : SixW25P.Covered 29720 36892 30944 35744 35636 40128 30944 35744 29720 36892 :=
  SixW25P.covered_of_walk lbS hbas 410195933779546155488767001982913786839603907292767630498948876760255520911467649825138807677546 200 29720 36892 30944 35744 35636 40128 30944 35744 29720 36892 322
    (by decide +kernel) (by decide)
theorem wk0llll : SixW25P.Covered 29720 36892 30944 35744 31144 40128 30944 35744 29720 36892 :=
  SixW25P.covered_split2 35636 wk0lllll wk0llllr
theorem wk0lllr : SixW25P.Covered 29720 36892 30944 35744 31144 40128 35744 40544 29720 36892 :=
  SixW25P.covered_of_walk lbS hbas 692188537057873404315589097410109262127949459495471319571808383578858 200 29720 36892 30944 35744 31144 40128 35744 40544 29720 36892 237
    (by decide +kernel) (by decide)
theorem wk0lll : SixW25P.Covered 29720 36892 30944 35744 31144 40128 30944 40544 29720 36892 :=
  SixW25P.covered_split3 35744 wk0llll wk0lllr
theorem wk0llr : SixW25P.Covered 29720 36892 35744 40544 31144 40128 30944 40544 29720 36892 :=
  SixW25P.covered_of_walk lbS hbas 2508236649946950122913459686829258668424484709647787491042084894378612339959038816691886 200 29720 36892 35744 40544 31144 40128 30944 40544 29720 36892 297
    (by decide +kernel) (by decide)
theorem wk0ll : SixW25P.Covered 29720 36892 30944 40544 31144 40128 30944 40544 29720 36892 :=
  SixW25P.covered_split1 35744 wk0lll wk0llr
theorem wk0lr : SixW25P.Covered 29720 36892 30944 40544 31144 40128 30944 40544 36892 44064 :=
  SixW25P.covered_of_walk lbS hbas 17591868281266228864814 200 29720 36892 30944 40544 31144 40128 30944 40544 36892 44064 82
    (by decide +kernel) (by decide)
theorem wk0l : SixW25P.Covered 29720 36892 30944 40544 31144 40128 30944 40544 29720 44064 :=
  SixW25P.covered_split4 36892 wk0ll wk0lr
theorem wk0r : SixW25P.Covered 36892 44064 30944 40544 31144 40128 30944 40544 29720 44064 :=
  SixW25P.covered_of_walk lbS hbas 307274286755812051785847544107627590242 200 36892 44064 30944 40544 31144 40128 30944 40544 29720 44064 137
    (by decide +kernel) (by decide)
theorem wk0 : SixW25P.Covered 29720 44064 30944 40544 31144 40128 30944 40544 29720 44064 :=
  SixW25P.covered_split0 36892 wk0l wk0r
theorem wk1lllllllll : SixW25P.Covered 29720 36892 30944 35744 31144 35636 30944 35744 53080 62502 :=
  SixW25P.covered_of_walk lbS hbas 6356214207014739362808962543878132863936074135579843263854128684727407775997992115683979464917163127204588111773502828044613443813953393508847186900374691098918102482 200 29720 36892 30944 35744 31144 35636 30944 35744 53080 62502 557
    (by decide +kernel) (by decide)
theorem wk1llllllllrl : SixW25P.Covered 29720 36892 30944 35744 31144 35636 30944 33344 62502 71925 :=
  SixW25P.covered_of_walk lbS hbas 125750377914816332179613779149435510832150996598004312198452951915586364691346334889180944679577457339080040748634641658306494607382881756691767362346345361966879586725978299456732605961427071001605909576136188436926839900405100150790078640981962337820571231407209199525485467099987112286554746711371299773117598146052199644062943369349868972459981820530535565052012564632272752125915376304498244025859803375074576581817556185701261268220582459118919030446602943621860558 200 29720 36892 30944 35744 31144 35636 30944 33344 62502 71925 1567
    (by decide +kernel) (by decide)
theorem wk1llllllllrrl : SixW25P.Covered 29720 36892 30944 35744 31144 33390 33344 35744 62502 71925 :=
  SixW25P.covered_of_walk lbS hbas 5156655229079060980977872000248780259239698585072166743708315326956034128404332203455636987653709218712999770121942229314450931207986703750385344845270763061522594648600904415113755217133517469547709320512979218325906888965293561097770246057263759041414963516089477497232963423085262922184935903632418296555213945139780686069645885455998305964999484066405742729179718395744844851590795703348345010332322078614236770792742936376307448071326112635336503148107822421235351811439899088367005267255361549675189454633965133936525937866 200 29720 36892 30944 35744 31144 33390 33344 35744 62502 71925 1762
    (by decide +kernel) (by decide)
theorem wk1llllllllrrrl : SixW25P.Covered 29720 36892 30944 33344 33390 35636 33344 35744 62502 71925 :=
  SixW25P.covered_of_walk lbS hbas 773071995070634333365587300407548475206115483450108548181748669843408172460126974967863811525985400853112448833735920774112448705565515803906286309605110685526214661358645375944949799746577596299521167291913795876576751745631051360170204722768176972925232890125371015873905981696461351594140925578682512713008724390044782293378172271441199458376754821335030688653516366234515250014767542789718660985722924323274344999460675469622281648725126157718397224908841805550500754122651044405943532516919134595386486780268121267834529667027377129985514206975432764063579729772516867712663877309944283613935799953289024944466080713691524690664992260160914068269373182423505030402636988429341708185008022268707910 200 29720 36892 30944 33344 33390 35636 33344 35744 62502 71925 2337
    (by decide +kernel) (by decide)
theorem wk1llllllllrrrrl : SixW25P.Covered 29720 33306 33344 35744 33390 35636 33344 35744 62502 71925 :=
  SixW25P.covered_of_walk lbS hbas 4792944821822817807276540236189250869641276036437410238669366136228870556939295413654254844568270615403121760223631061266250194196328086092436896962951863206307935027959400482633509567162475446076820001550415917634042190919222629255043430917794495953679290634006599501915770034234071798606794729525231926602769259901476436035867251546724854511712629911505684570839202082053701970002457736436319442696307025942070290383216797587949893766697316633074384577815623099901127906376215726525247541032403511999919501350364253742150985554174192623552063268807044367127202221051878418722590715434795420873046878424012169613170345632840989021162048612244702093822069059063324680290607828495910999930220453205819859034137819886645011425598424746016290523563471771687861875488384439287508774954829702545368028089665527108332946903755866424564800064505394608039775401275877816760661213565166799787854658835536809591048897392272985548071628190054532183357503124921859468005465464043679182848165403315090183261779037499690368413213553786773462029258720512803666425006841768598322405999726146 200 29720 33306 33344 35744 33390 35636 33344 35744 62502 71925 3577
    (by decide +kernel) (by decide)
theorem wk1llllllllrrrrr : SixW25P.Covered 33306 36892 33344 35744 33390 35636 33344 35744 62502 71925 :=
  SixW25P.covered_of_walk lbS hbas 158148360296428802419075578029769223894494119011220134500612819656148980206579964829026694143059427391334695519390956979228625306362636349880934497130816737111615137330590497929975483553815220809648141683554432034261585500210342719420274419128679446871992206038317197604929293429582750556580741323987057901925572705709342882042192935494753790351711901264608378915103794651022458828738481717960836608885040561874396444909377674677940225746512727545979540004565134083687971872004505582659435668481733792710676765375398270815968975835970742482179926386184575870940543051146389607360285588545298798166957591058258055249982519835500193107631282665799334129534226975524009869033525677665688724593081850993172840440284324044787864012512430152246186746112818499161984947701103378251906447538450149562122055585112276330899117884514231098929227084926350680839727427631311160620351304337653100797608698117614004089523991417130734846038371691518349153273877949019812302254142909358576071317037106548475221845727486544836053784931360521810800493185659965484766769281552765183637993047091063692239878894592000127093304607931385507387973256664701542002264571149009784270748682400133003186270336619386668660422433578518607827466989814269537515274821303311982560992244193363428624263954368282935438428324180071922171402553315243692385402515662985420825367931416614948275919516717983142477942262110438417587143371032973774574143730977897739144712617695150119394780256964168856436561410790210729479295652261631500377517315796984061110492826553896173448063743576356063391566939917525664490394031451134691411524513327968593458 200 33306 36892 33344 35744 33390 35636 33344 35744 62502 71925 5337
    (by decide +kernel) (by decide)
theorem wk1llllllllrrrr : SixW25P.Covered 29720 36892 33344 35744 33390 35636 33344 35744 62502 71925 :=
  SixW25P.covered_split0 33306 wk1llllllllrrrrl wk1llllllllrrrrr
theorem wk1llllllllrrr : SixW25P.Covered 29720 36892 30944 35744 33390 35636 33344 35744 62502 71925 :=
  SixW25P.covered_split1 33344 wk1llllllllrrrl wk1llllllllrrrr
theorem wk1llllllllrr : SixW25P.Covered 29720 36892 30944 35744 31144 35636 33344 35744 62502 71925 :=
  SixW25P.covered_split2 33390 wk1llllllllrrl wk1llllllllrrr
theorem wk1llllllllr : SixW25P.Covered 29720 36892 30944 35744 31144 35636 30944 35744 62502 71925 :=
  SixW25P.covered_split3 33344 wk1llllllllrl wk1llllllllrr
theorem wk1llllllll : SixW25P.Covered 29720 36892 30944 35744 31144 35636 30944 35744 53080 71925 :=
  SixW25P.covered_split4 62502 wk1lllllllll wk1llllllllr
theorem wk1lllllllr : SixW25P.Covered 29720 36892 30944 35744 31144 35636 35744 40544 53080 71925 :=
  SixW25P.covered_of_walk lbS hbas 1709112163617747283432308902456323685318285399822226713065180909669242953159773284712653356412485554990 200 29720 36892 30944 35744 31144 35636 35744 40544 53080 71925 347
    (by decide +kernel) (by decide)
theorem wk1lllllll : SixW25P.Covered 29720 36892 30944 35744 31144 35636 30944 40544 53080 71925 :=
  SixW25P.covered_split3 35744 wk1llllllll wk1lllllllr
theorem wk1llllllr : SixW25P.Covered 29720 36892 30944 35744 35636 40128 30944 40544 53080 71925 :=
  SixW25P.covered_of_walk lbS hbas 170682511160619677764271231752282501685600418789037576928014331377974076467557960623914480807804244677422 200 29720 36892 30944 35744 35636 40128 30944 40544 53080 71925 357
    (by decide +kernel) (by decide)
theorem wk1llllll : SixW25P.Covered 29720 36892 30944 35744 31144 40128 30944 40544 53080 71925 :=
  SixW25P.covered_split2 35636 wk1lllllll wk1llllllr
theorem wk1lllllr : SixW25P.Covered 29720 36892 35744 40544 31144 40128 30944 40544 53080 71925 :=
  SixW25P.covered_of_walk lbS hbas 7431335451021601773757810163104187002963692606697315996575936166 200 29720 36892 35744 40544 31144 40128 30944 40544 53080 71925 217
    (by decide +kernel) (by decide)
theorem wk1lllll : SixW25P.Covered 29720 36892 30944 40544 31144 40128 30944 40544 53080 71925 :=
  SixW25P.covered_split1 35744 wk1llllll wk1lllllr
theorem wk1llllr : SixW25P.Covered 36892 44064 30944 40544 31144 40128 30944 40544 53080 71925 :=
  SixW25P.covered_of_walk lbS hbas 14816879218907802906829350 200 36892 44064 30944 40544 31144 40128 30944 40544 53080 71925 92
    (by decide +kernel) (by decide)
theorem wk1llll : SixW25P.Covered 29720 44064 30944 40544 31144 40128 30944 40544 53080 71925 :=
  SixW25P.covered_split0 36892 wk1lllll wk1llllr
theorem wk1lllr : SixW25P.Covered 29720 44064 30944 40544 31144 40128 30944 40544 71925 90770 :=
  SixW25P.covered_of_walk lbS hbas 135602599462508523062085473710126050914 200 29720 44064 30944 40544 31144 40128 30944 40544 71925 90770 132
    (by decide +kernel) (by decide)
theorem wk1lll : SixW25P.Covered 29720 44064 30944 40544 31144 40128 30944 40544 53080 90770 :=
  SixW25P.covered_split4 71925 wk1llll wk1lllr
theorem wk1llr : SixW25P.Covered 29720 44064 30944 40544 31144 40128 30944 40544 90770 128460 :=
  SixW25P.covered_of_walk lbS hbas 38678256942982307204470048218782511067529132718313093443407672663998102304673909100904158818977500831383819164172009814955263930475225602718555671566772358872909078565813404058980543591395805246865974804286495406511483418238786313813970835117559362444296675130650140758435942664064161189933604985472594648929422099777891260647221489728019279843144645565833293047388539928491185946211793572667992102614559767099657941946956630431301784332892813637465284380873008428606341484214377319633030703206909409151062954693918099702229052065717440095695536676717669426815639393062826401348654457744606200494023838083981996343051741180508626455329410628593396604679967553901483016125192657203630197694994843556402310440869162906028786915611919931856025310272741820912279777239254228723766887405121789995853734158878931337052596528445061637730197011088785430120614480015070672766134415417772341207510164488609070695783694760239353571025095445794109163061267202418792168276189914296316423455347845259378811130014932027258568833165922 200 29720 44064 30944 40544 31144 40128 30944 40544 90770 128460 3392
    (by decide +kernel) (by decide)
theorem wk1ll : SixW25P.Covered 29720 44064 30944 40544 31144 40128 30944 40544 53080 128460 :=
  SixW25P.covered_split4 90770 wk1lll wk1llr
theorem wk1lr : SixW25P.Covered 29720 44064 30944 40544 31144 40128 30944 40544 128460 203840 :=
  SixW25P.covered_of_walk lbS hbas 264874001501201169816734351060226351480341268442043614610319120014820420101603612502428867922513833137903016403248086558005584040268127210540918506755683276578225672595657467385370078314298410287222915873826594 200 29720 44064 30944 40544 31144 40128 30944 40544 128460 203840 702
    (by decide +kernel) (by decide)
theorem wk1l : SixW25P.Covered 29720 44064 30944 40544 31144 40128 30944 40544 53080 203840 :=
  SixW25P.covered_split4 128460 wk1ll wk1lr
theorem wk1r : SixW25P.Covered 29720 44064 30944 40544 31144 40128 30944 40544 203840 354601 :=
  SixW25P.covered_of_walk lbS hbas 0 200 29720 44064 30944 40544 31144 40128 30944 40544 203840 354601 2
    (by decide +kernel) (by decide)
theorem wk1 : SixW25P.Covered 29720 44064 30944 40544 31144 40128 30944 40544 53080 354601 :=
  SixW25P.covered_split4 203840 wk1l wk1r
theorem wk2llllllll : SixW25P.Covered 29720 36892 30944 35744 31144 40128 57472 63537 29720 36892 :=
  SixW25P.covered_of_walk lbS hbas 12773312917966830908219261632127890623907484052447778942090783233835683226604956246794132513082841643486610652595533072951180031012020658182215830383421129689461983054654202160550583302013939205018208600248131133075147813062414761537816606023227195954561563720525344299084703863129952215369227707670820913814880276144450794571298905624502803299614573981905530109147398132948851939402155013228389614801095713085028997906589787915372608392514330549736171049906044934652937924964818982266847639667986660036150459188189508316382752949309092804014249952933028346507673210459345976187139966178101114412276398718932982541447836102100645424902661864069667929822328921013250510806573867207069364557423548306837363690626276320847493187767585958891954325352444430540117388836167206007868570697632372385568093107234992767612195728657180565431400862951715834618835915261385172900281112240005916039092844222222781919562053286482364445343232590008356804960924849396705113633597250435764637257501070422402246323441923209031812124451948019345466749273403492599712078100551521913752166654469864218639589804267614353551402041849244895352784792741198 200 29720 36892 30944 35744 31144 40128 57472 63537 29720 36892 3757
    (by decide +kernel) (by decide)
theorem wk2lllllllrll : SixW25P.Covered 29720 36892 30944 33344 31144 35636 63537 69602 29720 36892 :=
  SixW25P.covered_of_walk lbS hbas 6541789542290895245675234350164277728615967466014925631136342423451374371753005680916374144439406333179838677420627650610025816361662992839548221195368988881958623978016706972439240705093945058283797447621379615881166428239793717493424721202259598660508473988314559719656493475489287318502063869248381263613809354311453126930946727606287490430059992892698947654354494630558577321033866381466365996793382200882598062722657350526435832299064770496099524131156873675949270175103980852556621597255150144400468964877766756332424878946271279391546372475406025386304551671098961674899411699428122905775539797692047778909992009239878 200 29720 36892 30944 33344 31144 35636 63537 69602 29720 36892 2082
    (by decide +kernel) (by decide)
theorem wk2lllllllrlrl : SixW25P.Covered 29720 33306 33344 35744 31144 35636 63537 69602 29720 36892 :=
  SixW25P.covered_of_walk lbS hbas 85648790055816261161714524074166622256144908278719694500415841781760799008252833101784244543084354527546671320770023224635035497983514894766771701303567129693581646336143391157680124241084476235013092576622554541468365337427625041321051868591007649374230274855175472915158187746322744899298747022479170252649521445615530588098908207228559732568907284553195977981471758520660901856996234214802700377939702010554983881529490915354095507869434293361082417991801660613450357970237286076650232210179928627051311447550667295153044688064366247954646630204690520368881032395431155081975353755705141454185673776687137541879203241543756722049184295320385194193544218261059484151165043753981314214488327526495599520912280886806982503017076102672687074431141832725330997135667678304460430823427264802071768479331015981472823934151014151142137421790511720621038961486965790033061320242234312545572610947481033509288735766402259235338643210485721336504375001441492663675245561959125458439276738958675401658049321830386908439085392955602419822426679596711623143515827760897227205348943004644047697626638325702526990678653720977584032744137874722146083148974815983384964104306302382583621754225081469924725450692344793804565696344220279666227466651296235305484128345742256710565095565910837695433299023808967505541903774001858490837170118947507461904096748169707291970 200 29720 33306 33344 35744 31144 35636 63537 69602 29720 36892 4497
    (by decide +kernel) (by decide)
theorem wk2lllllllrlrr : SixW25P.Covered 33306 36892 33344 35744 31144 35636 63537 69602 29720 36892 :=
  SixW25P.covered_of_walk lbS hbas 73641410920644635143737206473476223015523780982090043823289751549100280492396061898778769688325115479509135140548227348963023395370450164278259219427251940186444585105845814307833396432685907453625379066564187079958334700473940448490365929871339169837000173944292109084865312283750197451840196249092611615661966756972814923498216572262407625563742728966913639524343019353159144992179001752047312157811763186773860250068082024777400292000339344410612410166907973932756028717799477093976989495986186370555393715369397314215425556436747508664923562009935540112133314378059947194105427737809679655124359305052380698985691988575406710628696960473457792086564876982989671640161309057496574298787643918449640921591810988084811132095513802079256297375708684788901683590032730310240355420206765710546247520760428847379391138287961275238438958879454686288613263390518269754640676576233809896271475313167542563812684930342527906358541335186624228320134874408551493514622353124572857546666257019320180837472541677672137635829102354014521075182546784229132300088499549778257365473737856151708003375834639541560743174289180984925859400090812738413802986257791094973704946672467509316791570021558822949722921872562015477182468475463368820586423898023603106994678573308853153038454874002124641537676863983275701234883526259802927860748529762008574759723896715242736010352209252202770112899676946840505793096696198077517698863530994273850660771364897248910660272585364094386096256530571750097001146581822407693239390791743092192762416144720113488631880814785565807970858840276144140358894362190599459321480398161785908385193111802546249733248446017049694669184677610603315020781113007057227685215210521751948954690124369878302850427665589344305553220163420972927448461783250788612350965713814678296731053279858758673578 200 33306 36892 33344 35744 31144 35636 63537 69602 29720 36892 5992
    (by decide +kernel) (by decide)
theorem wk2lllllllrlr : SixW25P.Covered 29720 36892 33344 35744 31144 35636 63537 69602 29720 36892 :=
  SixW25P.covered_split0 33306 wk2lllllllrlrl wk2lllllllrlrr
theorem wk2lllllllrl : SixW25P.Covered 29720 36892 30944 35744 31144 35636 63537 69602 29720 36892 :=
  SixW25P.covered_split1 33344 wk2lllllllrll wk2lllllllrlr
theorem wk2lllllllrr : SixW25P.Covered 29720 36892 30944 35744 35636 40128 63537 69602 29720 36892 :=
  SixW25P.covered_of_walk lbS hbas 13118363715276765342158267987042378242071524582308745771539827499685572338637980330617714594737599332519677308317423142596006126910298723701884395309548696055358643436647595996962183410281105002 200 29720 36892 30944 35744 35636 40128 63537 69602 29720 36892 652
    (by decide +kernel) (by decide)
theorem wk2lllllllr : SixW25P.Covered 29720 36892 30944 35744 31144 40128 63537 69602 29720 36892 :=
  SixW25P.covered_split2 35636 wk2lllllllrl wk2lllllllrr
theorem wk2lllllll : SixW25P.Covered 29720 36892 30944 35744 31144 40128 57472 69602 29720 36892 :=
  SixW25P.covered_split3 63537 wk2llllllll wk2lllllllr
theorem wk2llllllr : SixW25P.Covered 29720 36892 30944 35744 31144 40128 57472 69602 36892 44064 :=
  SixW25P.covered_of_walk lbS hbas 499134668848021762728347192734337211871629817688943727632108861095322177266 200 29720 36892 30944 35744 31144 40128 57472 69602 36892 44064 257
    (by decide +kernel) (by decide)
theorem wk2llllll : SixW25P.Covered 29720 36892 30944 35744 31144 40128 57472 69602 29720 44064 :=
  SixW25P.covered_split4 36892 wk2lllllll wk2llllllr
theorem wk2lllllr : SixW25P.Covered 29720 36892 35744 40544 31144 40128 57472 69602 29720 44064 :=
  SixW25P.covered_of_walk lbS hbas 373718560749953315187519265213427123349308302509446119342537051351032279303765916475878369733103619526774502 200 29720 36892 35744 40544 31144 40128 57472 69602 29720 44064 367
    (by decide +kernel) (by decide)
theorem wk2lllll : SixW25P.Covered 29720 36892 30944 40544 31144 40128 57472 69602 29720 44064 :=
  SixW25P.covered_split1 35744 wk2llllll wk2lllllr
theorem wk2llllr : SixW25P.Covered 36892 44064 30944 40544 31144 40128 57472 69602 29720 44064 :=
  SixW25P.covered_of_walk lbS hbas 207774246 200 36892 44064 30944 40544 31144 40128 57472 69602 29720 44064 37
    (by decide +kernel) (by decide)
theorem wk2llll : SixW25P.Covered 29720 44064 30944 40544 31144 40128 57472 69602 29720 44064 :=
  SixW25P.covered_split0 36892 wk2lllll wk2llllr
theorem wk2lllr : SixW25P.Covered 29720 44064 30944 40544 31144 40128 69602 81733 29720 44064 :=
  SixW25P.covered_of_walk lbS hbas 2726369041904176179065582 200 29720 44064 30944 40544 31144 40128 69602 81733 29720 44064 87
    (by decide +kernel) (by decide)
theorem wk2lll : SixW25P.Covered 29720 44064 30944 40544 31144 40128 57472 81733 29720 44064 :=
  SixW25P.covered_split3 69602 wk2llll wk2lllr
theorem wk2llr : SixW25P.Covered 29720 44064 30944 40544 31144 40128 81733 105995 29720 44064 :=
  SixW25P.covered_of_walk lbS hbas 19335848205797562855400409429444534239456378656010771996612787662577456485709433331322788017378008516768709049390980937065514810225888738039684690672124748261791611348659570775494946140748186340389198646749080948384354453680828636405054997948393099430892055560629449752329428709942449415897262419753466441323913375154376330565214480851516752253856571134938081658458019957435548549895658104759144757640212809374654163252937499921048599351125499944294841915631837469163831771872348413225433061592827426458349068873781972194694168773591234756784160236787783262788171243039664350600960604027441718712771125363690882919962080092629602484244698124827185095642398504330485193311811170230612548237390120528516931140636049142118791658415749536640212641444582539114063957719608426147676491305443444472486904917863367943413592574999174841418122178045950384694216435908074755341229669155440814767634636105225461513962276134869091703952132990219500885174251242816879253917801197026528716848936003939132186160714516174007283106792588474338056231520999608775784394130192127564968761063961989523541556543290054916198191216774600153610336787405482452178741281917459706305088665531615575782854313799370109776982713339980774787801387777173890830202116166448356879863494614799891651441388550515615593878221251573903145277274898782501154405709979230619998765759529026683824405386831725555019368184757794022421139905286403579365709231663394216881701154639512955891232411653439780418443943380903611296117419963241764314250889120656445973557727664899361508505896102972430428854557844786584312217872027242829115774332414560992146491996497169020957459874519244400452637014519911386526644987143005524150257729612572703520891288592367098872005236738076449802676605464278493525442654913431710535328836571020160591839481570 200 29720 44064 30944 40544 31144 40128 81733 105995 29720 44064 5962
    (by decide +kernel) (by decide)
theorem wk2ll : SixW25P.Covered 29720 44064 30944 40544 31144 40128 57472 105995 29720 44064 :=
  SixW25P.covered_split3 81733 wk2lll wk2llr
theorem wk2lr : SixW25P.Covered 29720 44064 30944 40544 31144 40128 105995 154518 29720 44064 :=
  SixW25P.covered_of_walk lbS hbas 14587332412889330122989517546071223520535176090901048281097560717378273461486 200 29720 44064 30944 40544 31144 40128 105995 154518 29720 44064 262
    (by decide +kernel) (by decide)
theorem wk2l : SixW25P.Covered 29720 44064 30944 40544 31144 40128 57472 154518 29720 44064 :=
  SixW25P.covered_split3 105995 wk2ll wk2lr
theorem wk2r : SixW25P.Covered 29720 44064 30944 40544 31144 40128 154518 251564 29720 44064 :=
  SixW25P.covered_of_walk lbS hbas 0 200 29720 44064 30944 40544 31144 40128 154518 251564 29720 44064 2
    (by decide +kernel) (by decide)
theorem wk2 : SixW25P.Covered 29720 44064 30944 40544 31144 40128 57472 251564 29720 44064 :=
  SixW25P.covered_split3 154518 wk2l wk2r
theorem wk3lllllllllll : SixW25P.Covered 29720 36892 30944 35744 31144 40128 57472 69602 53080 62502 :=
  SixW25P.covered_of_walk lbS hbas 3288265366302468645901240618746026357040340066986788324742317924265839182 200 29720 36892 30944 35744 31144 40128 57472 69602 53080 62502 247
    (by decide +kernel) (by decide)
theorem wk3llllllllllrl : SixW25P.Covered 29720 36892 30944 35744 31144 40128 57472 63537 62502 71925 :=
  SixW25P.covered_of_walk lbS hbas 4839428471836072565732906589873288397691490572976080785097967232231273262130792633493273800141178620599884577183880492112732686103931647521553578831419393660394596480179522894 200 29720 36892 30944 35744 31144 40128 57472 63537 62502 71925 592
    (by decide +kernel) (by decide)
theorem wk3llllllllllrrll : SixW25P.Covered 29720 36892 30944 33344 31144 35636 63537 69602 62502 71925 :=
  SixW25P.covered_of_walk lbS hbas 523597725298731322871690012279020376530866968711633806117489577266266327833848279145645287119760659765922080740329239523434944329142645661251804390237280190184953137411893673148589326311012787362118 200 29720 36892 30944 33344 31144 35636 63537 69602 62502 71925 662
    (by decide +kernel) (by decide)
theorem wk3llllllllllrrlrl : SixW25P.Covered 29720 33306 33344 35744 31144 35636 63537 69602 62502 71925 :=
  SixW25P.covered_of_walk lbS hbas 858955511584926435515629873519665633964590520386041985179971740044894022088809922163162561170917772764308919920298121941969181263469322555221083168904034256690108143085435225210635676899570585254152576336315779593490735593664019659997422285408311677144093122335616228396367907192804283597243525745095153847084246758406027001264518015865090846147100951917560020484984315848705205091719710507699017455204021521393357017932653637488582101693579862887820176922018034066787997391971882458028990084784664442470661264770729108091129561714525563942875041654860933808454793970468678789724395951873913384215909721628640538110760838928225350528347079570187417129380934581971615331642639403942530259118243745451413227712807477981600066560836641018030261047328455705125761367661014680540932545848420678639915205967473436642050640474318779042044644541580220465184358557815990116806874938912233540293437525248591589152195794303033004430960906867807168297982952685768926375030323207968477919900169431789061767696684196299633603713578430581435175241766919705546895519105101511123185424234887964204100018581510066581866228815205261923604307938759330502842581747707002508432683713663551864868183213787726326895062979390984201874734660314887257021567020176295792732309638667920512322 200 29720 33306 33344 35744 31144 35636 63537 69602 62502 71925 4202
    (by decide +kernel) (by decide)
theorem wk3llllllllllrrlrrl : SixW25P.Covered 33306 36892 33344 35744 31144 33390 63537 69602 62502 71925 :=
  SixW25P.covered_of_walk lbS hbas 3250130094372448472492336441549418981042286333927842962895182736958296770005322 200 33306 36892 33344 35744 31144 33390 63537 69602 62502 71925 267
    (by decide +kernel) (by decide)
theorem wk3llllllllllrrlrrrlllll : SixW25P.Covered 33306 35099 33344 34544 33390 35636 63537 65053 62502 67213 :=
  SixW25P.covered_of_walk lbS hbas 5606724409881170134713942326959256297880091528858941068810373028874868812064760472906064314505701813107089566782538531342070958038028564500308536928785190779101026025851874455918763960084990782525103562854106412295330405929671730439475997917928504628813114192430562204208366137433630222288114033719725942475565182075350656715611500431596115514388080357708299556500043992316501584706683233788396991628926533185991478373091713557058877096041721269718576439985433040187359577608871578195072782416365005179994765764354009570969925280025174804273265316994074873711498334694752626731287142003718188379718505424912449129201754736806648335210230524748777688519589369262853472158695063265718868534391412968880166758961437815208557019320683214648896484611644262042729819032680478895947311070837845823194306253198842012409872362490538352515934878093719687024972455014525017630427914275623224015700765675771540099117778147540303131484365338201387863289825667584857433297208102783879487301272929519861904239270002238717131185505328965688550832949790838139071216636491503681432246998792664512418942849944757294830353303451104505173296441480929052497583599244457770534282626960487372002664700362676335058917306928306771752735609890224844458998483216487299842821180242753012973741167440382498274754599592341074338649022531827067343975755982152060953202935456801312418128447010633084670780124489734966521303015311208628548205878637243015428515378 200 33306 35099 33344 34544 33390 35636 63537 65053 62502 67213 4752
    (by decide +kernel) (by decide)
theorem wk3llllllllllrrlrrrllllr : SixW25P.Covered 33306 35099 33344 34544 33390 35636 65053 66569 62502 67213 :=
  SixW25P.covered_of_walk lbS hbas 320957273923564519876496509621172831337972913932732882686216214812211985177755355147299725034711079536282210411208932937417287903792097880313898694273739628627717539502636546432525194491516725371124087499687740700481809058492481521289759297751023804136754280098829329481915065384100205595834052660988343662159698756261585472447589698227064399718444408753098086953084602186906423754253177179982900468573232447991271850582002053214968601202565552508709448269626259815262081922091831434889126917707127577740693523121306081685009757090678784196394854493720881187285893890799667294591730067517470147602169273464620040650032537236597480457116212140150732279096534403340353263243878326049029754110306982657493269363427534270149510535626496946124931814249763423397588490761638935626493142872360291520472346952990265605736538643840001199963229253559801614810472288016362857895348998201849522809294934330219606061236511567712171343230304503876413940435250029074036875969074365395627723947071192762112836017698361185364185520869044720369466630248911531835434198948014007023303766205142053501975104431622028693284846925602443178043578534422443063270600794875493045120909637739065952821580544937101406199523885917295498190288264396641804413154328567158380162537064844202972369823427974504274627302777742426428953057788202863541152540702025822766384969206588146027211631798870684699295406034690674 200 33306 35099 33344 34544 33390 35636 65053 66569 62502 67213 4597
    (by decide +kernel) (by decide)
theorem wk3llllllllllrrlrrrllll : SixW25P.Covered 33306 35099 33344 34544 33390 35636 63537 66569 62502 67213 :=
  SixW25P.covered_split3 65053 wk3llllllllllrrlrrrlllll wk3llllllllllrrlrrrllllr
theorem wk3llllllllllrrlrrrlllr : SixW25P.Covered 33306 35099 34544 35744 33390 35636 63537 66569 62502 67213 :=
  SixW25P.covered_of_walk lbS hbas 20532253320663598485107062710667052668671688807703408931775635533133410634603952809684170143260265773291644264774826110628320872389427425294010334664576850980137590372066094 200 33306 35099 34544 35744 33390 35636 63537 66569 62502 67213 577
    (by decide +kernel) (by decide)
theorem wk3llllllllllrrlrrrlll : SixW25P.Covered 33306 35099 33344 35744 33390 35636 63537 66569 62502 67213 :=
  SixW25P.covered_split1 34544 wk3llllllllllrrlrrrllll wk3llllllllllrrlrrrlllr
theorem wk3llllllllllrrlrrrllr : SixW25P.Covered 33306 35099 33344 35744 33390 35636 63537 66569 67213 71925 :=
  SixW25P.covered_of_walk lbS hbas 1488976947395266375899137519079228407922714337100043625441595726423492505052604683092056430157526412810846451337953638154573938644518966386665297799925421439083896448354593090331591326989693941323749379272418891195439716590350675324964836504585383819507576434 200 33306 35099 33344 35744 33390 35636 63537 66569 67213 71925 867
    (by decide +kernel) (by decide)
theorem wk3llllllllllrrlrrrll : SixW25P.Covered 33306 35099 33344 35744 33390 35636 63537 66569 62502 71925 :=
  SixW25P.covered_split4 67213 wk3llllllllllrrlrrrlll wk3llllllllllrrlrrrllr
theorem wk3llllllllllrrlrrrlr : SixW25P.Covered 35099 36892 33344 35744 33390 35636 63537 66569 62502 71925 :=
  SixW25P.covered_of_walk lbS hbas 15958738334770902446275490402 200 35099 36892 33344 35744 33390 35636 63537 66569 62502 71925 102
    (by decide +kernel) (by decide)
theorem wk3llllllllllrrlrrrl : SixW25P.Covered 33306 36892 33344 35744 33390 35636 63537 66569 62502 71925 :=
  SixW25P.covered_split0 35099 wk3llllllllllrrlrrrll wk3llllllllllrrlrrrlr
theorem wk3llllllllllrrlrrrr : SixW25P.Covered 33306 36892 33344 35744 33390 35636 66569 69602 62502 71925 :=
  SixW25P.covered_of_walk lbS hbas 730749206021600180336404985963001539661994108826185707572777562485416936249715320635346849176990565450844981793839783207766175423092917388523595534955164395058 200 33306 36892 33344 35744 33390 35636 66569 69602 62502 71925 537
    (by decide +kernel) (by decide)
theorem wk3llllllllllrrlrrr : SixW25P.Covered 33306 36892 33344 35744 33390 35636 63537 69602 62502 71925 :=
  SixW25P.covered_split3 66569 wk3llllllllllrrlrrrl wk3llllllllllrrlrrrr
theorem wk3llllllllllrrlrr : SixW25P.Covered 33306 36892 33344 35744 31144 35636 63537 69602 62502 71925 :=
  SixW25P.covered_split2 33390 wk3llllllllllrrlrrl wk3llllllllllrrlrrr
theorem wk3llllllllllrrlr : SixW25P.Covered 29720 36892 33344 35744 31144 35636 63537 69602 62502 71925 :=
  SixW25P.covered_split0 33306 wk3llllllllllrrlrl wk3llllllllllrrlrr
theorem wk3llllllllllrrl : SixW25P.Covered 29720 36892 30944 35744 31144 35636 63537 69602 62502 71925 :=
  SixW25P.covered_split1 33344 wk3llllllllllrrll wk3llllllllllrrlr
theorem wk3llllllllllrrr : SixW25P.Covered 29720 36892 30944 35744 35636 40128 63537 69602 62502 71925 :=
  SixW25P.covered_of_walk lbS hbas 500697084496065888706843239864252778652903498727741419531243008236482244632771453044330 200 29720 36892 30944 35744 35636 40128 63537 69602 62502 71925 297
    (by decide +kernel) (by decide)
theorem wk3llllllllllrr : SixW25P.Covered 29720 36892 30944 35744 31144 40128 63537 69602 62502 71925 :=
  SixW25P.covered_split2 35636 wk3llllllllllrrl wk3llllllllllrrr
theorem wk3llllllllllr : SixW25P.Covered 29720 36892 30944 35744 31144 40128 57472 69602 62502 71925 :=
  SixW25P.covered_split3 63537 wk3llllllllllrl wk3llllllllllrr
theorem wk3llllllllll : SixW25P.Covered 29720 36892 30944 35744 31144 40128 57472 69602 53080 71925 :=
  SixW25P.covered_split4 62502 wk3lllllllllll wk3llllllllllr
theorem wk3lllllllllr : SixW25P.Covered 29720 36892 35744 40544 31144 40128 57472 69602 53080 71925 :=
  SixW25P.covered_of_walk lbS hbas 759523280122558040902424501746198531247231718 200 29720 36892 35744 40544 31144 40128 57472 69602 53080 71925 157
    (by decide +kernel) (by decide)
theorem wk3lllllllll : SixW25P.Covered 29720 36892 30944 40544 31144 40128 57472 69602 53080 71925 :=
  SixW25P.covered_split1 35744 wk3llllllllll wk3lllllllllr
theorem wk3llllllllr : SixW25P.Covered 29720 36892 30944 40544 31144 40128 57472 69602 71925 90770 :=
  SixW25P.covered_of_walk lbS hbas 2749503879047910 200 29720 36892 30944 40544 31144 40128 57472 69602 71925 90770 57
    (by decide +kernel) (by decide)
theorem wk3llllllll : SixW25P.Covered 29720 36892 30944 40544 31144 40128 57472 69602 53080 90770 :=
  SixW25P.covered_split4 71925 wk3lllllllll wk3llllllllr
theorem wk3lllllllr : SixW25P.Covered 29720 36892 30944 40544 31144 40128 69602 81733 53080 90770 :=
  SixW25P.covered_of_walk lbS hbas 613948055353894443840238 200 29720 36892 30944 40544 31144 40128 69602 81733 53080 90770 87
    (by decide +kernel) (by decide)
theorem wk3lllllll : SixW25P.Covered 29720 36892 30944 40544 31144 40128 57472 81733 53080 90770 :=
  SixW25P.covered_split3 69602 wk3llllllll wk3lllllllr
theorem wk3llllllr : SixW25P.Covered 36892 44064 30944 40544 31144 40128 57472 81733 53080 90770 :=
  SixW25P.covered_of_walk lbS hbas 419362 200 36892 44064 30944 40544 31144 40128 57472 81733 53080 90770 27
    (by decide +kernel) (by decide)
theorem wk3llllll : SixW25P.Covered 29720 44064 30944 40544 31144 40128 57472 81733 53080 90770 :=
  SixW25P.covered_split0 36892 wk3lllllll wk3llllllr
theorem wk3lllllr : SixW25P.Covered 29720 44064 30944 40544 31144 40128 81733 105995 53080 90770 :=
  SixW25P.covered_of_walk lbS hbas 9482581405364726890260833154023460354475075916539729017847302436837322776867445629497153081488288174190274463665252877285735357433812284647177037711483249381434515530622605198845720138143046002238681368709534932604235647610658 200 29720 44064 30944 40544 31144 40128 81733 105995 53080 90770 757
    (by decide +kernel) (by decide)
theorem wk3lllll : SixW25P.Covered 29720 44064 30944 40544 31144 40128 57472 105995 53080 90770 :=
  SixW25P.covered_split3 81733 wk3llllll wk3lllllr
theorem wk3llllr : SixW25P.Covered 29720 44064 30944 40544 31144 40128 57472 105995 90770 128460 :=
  SixW25P.covered_of_walk lbS hbas 10610259644956629414633903200813834400579035049794248642637692935871433676283023592599614921713046066983371957167113886519031409172528475801293277739798882470586029952475215847689883351982099375502103635005528569702674515764604334519709155121619918161555209457835451532863864606658685601925248833104830267337405107380238413126596520351629729930546767754571585444369729082121444162088348968759277019889900799199816646990232424277134817266658862 200 29720 44064 30944 40544 31144 40128 57472 105995 90770 128460 1482
    (by decide +kernel) (by decide)
theorem wk3llll : SixW25P.Covered 29720 44064 30944 40544 31144 40128 57472 105995 53080 128460 :=
  SixW25P.covered_split4 90770 wk3lllll wk3llllr
theorem wk3lllr : SixW25P.Covered 29720 44064 30944 40544 31144 40128 57472 105995 128460 203840 :=
  SixW25P.covered_of_walk lbS hbas 638777808109697065374314327842 200 29720 44064 30944 40544 31144 40128 57472 105995 128460 203840 107
    (by decide +kernel) (by decide)
theorem wk3lll : SixW25P.Covered 29720 44064 30944 40544 31144 40128 57472 105995 53080 203840 :=
  SixW25P.covered_split4 128460 wk3llll wk3lllr
theorem wk3llr : SixW25P.Covered 29720 44064 30944 40544 31144 40128 105995 154518 53080 203840 :=
  SixW25P.covered_of_walk lbS hbas 68639477578265997874 200 29720 44064 30944 40544 31144 40128 105995 154518 53080 203840 72
    (by decide +kernel) (by decide)
theorem wk3ll : SixW25P.Covered 29720 44064 30944 40544 31144 40128 57472 154518 53080 203840 :=
  SixW25P.covered_split3 105995 wk3lll wk3llr
theorem wk3lr : SixW25P.Covered 29720 44064 30944 40544 31144 40128 57472 154518 203840 354601 :=
  SixW25P.covered_of_walk lbS hbas 0 200 29720 44064 30944 40544 31144 40128 57472 154518 203840 354601 2
    (by decide +kernel) (by decide)
theorem wk3l : SixW25P.Covered 29720 44064 30944 40544 31144 40128 57472 154518 53080 354601 :=
  SixW25P.covered_split4 203840 wk3ll wk3lr
theorem wk3r : SixW25P.Covered 29720 44064 30944 40544 31144 40128 154518 251564 53080 354601 :=
  SixW25P.covered_of_walk lbS hbas 0 200 29720 44064 30944 40544 31144 40128 154518 251564 53080 354601 2
    (by decide +kernel) (by decide)
theorem wk3 : SixW25P.Covered 29720 44064 30944 40544 31144 40128 57472 251564 53080 354601 :=
  SixW25P.covered_split3 154518 wk3l wk3r
theorem wk4llllllllll : SixW25P.Covered 29720 36892 30944 35744 58040 61946 30944 35744 29720 36892 :=
  SixW25P.covered_of_walk lbS hbas 129286860665102870854 200 29720 36892 30944 35744 58040 61946 30944 35744 29720 36892 72
    (by decide +kernel) (by decide)
theorem wk4lllllllllrl : SixW25P.Covered 29720 36892 30944 33344 61946 65852 30944 35744 29720 36892 :=
  SixW25P.covered_of_walk lbS hbas 3030756647696225028192949042388259278672026294718131239319594030205129996640679305450667115514186930506052257058854821804483016444046499505768948216016460665408364243126787589640142622148110921239316623173346916171177599602014847260294180161963041522172768336248596591502186133838827995336009105268460587178030156497613124875133940792315940397540231474042629821739038034750815833088839156703036819871173435914902341651910 200 29720 36892 30944 33344 61946 65852 30944 35744 29720 36892 1402
    (by decide +kernel) (by decide)
theorem wk4lllllllllrrl : SixW25P.Covered 29720 33306 33344 35744 61946 65852 30944 35744 29720 36892 :=
  SixW25P.covered_of_walk lbS hbas 60357250421911062576593982113045454798226131280041148648738664273201387822604083125260975699724031387224420303685333410962063624882923341508890058160918809608046299374929262079152339283724043524214443918750309655491065038113123005312092252150396007926044249484288608180303554292279828441874549295099214459905429470419048898022086178749797461909742628478630976436630503984529793420559574129835547203472182147321375995104795060631980486805789346892394688266960458043771596531864014570510679617370163764900254680948548045965145408826682944707831591156167111025818500321453456746521364936345819735231445931478983554017046185340279871246690660769459237183404558376626177401865385658382879652960581101412111567245683548001893117681642655226453421356113476181306180233685193274614118908695481193405821583467828880578968318855526073284580885069600544076490354986185095512104449668041069761773410605415364552264482131176883322542697908968491499353387194569760194 200 29720 33306 33344 35744 61946 65852 30944 35744 29720 36892 3172
    (by decide +kernel) (by decide)
theorem wk4lllllllllrrrl : SixW25P.Covered 33306 36892 33344 35744 61946 65852 30944 33344 29720 36892 :=
  SixW25P.covered_of_walk lbS hbas 29080196565990505061336356194356006663527487613164409988775907090029755316459005177761288395880224818870117522676762739984568422548077314328249342274499590334929650135522189880355812218560574899443091903773766633677511962950311382311022908992234275129084482567834623253194160788813202996122563977428436321989384432764686454700855596998131844731803478077503104572959208786929230 200 33306 36892 33344 35744 61946 65852 30944 33344 29720 36892 1257
    (by decide +kernel) (by decide)
theorem wk4lllllllllrrrr : SixW25P.Covered 33306 36892 33344 35744 61946 65852 33344 35744 29720 36892 :=
  SixW25P.covered_of_walk lbS hbas 467801879232237892760032288703996561843026933381043428798575288299678724260743029621317982048429552440606948876246729326370376757141538548153574583946438703962308678547744906955102915786860866283951449422284244209302251568652561737997568169956173294091614800246524272070929873672805025558583624220391837097190476697355255099582304635922265008164468679841439426727672771433490504979847076079251330287420183122377609228856699656046784525910140222938563366193896963075676865010204600971133767337780085038232373898564791514832856283007115992765207886580314997954449377506792254034548939547030745894736715350195321730762761045709045842297597064408935647230240273103035186513590176167216181890264157938532016506173529007555695253407335266634242927277152075418953485985764387443017121949604948733145687523658846302473989613030704593725457015101204207156153580071236264547944280634494447862100977722230471565641963086749344968162561261744217218026525741113281210166535162328134868032332167993334072398372195962152568035321337475302612148422804444195834898612499253907102391802961558462925886075776067097796325967908269262767047672712994598094329534632350406590470941795367027956406104281422210388218824564759428508998066742517914167243046774931171642075836280443768799383173750029855516894605315373628445514592251723586395302462945592905290229233169460411857540247041954016830644297202650357586083868217576109306203463795295525059968736751873121921940508557261309684104694538670744961649234368175396672348557119611301282346093349424353874858122948786592102560822744446635847828554074925971609257198651003296754625508031576972511739711172639560106671908552356554289525736713198266213780167660105982042203192834002431034262958480475770598228917799758466049972848308204681202138232284635640783745729949718877797787908417639200399648054930400110858544403057869687622800178813826960465872786212334219075126512707884163307986641603057611266304858338090182573433998697236870073119772429097667521127051419999595473534048181236183883656970448504582593435059371700622835493453720597937481638002580162710718608009607722724701259058 200 33306 36892 33344 35744 61946 65852 33344 35744 29720 36892 7022
    (by decide +kernel) (by decide)
theorem wk4lllllllllrrr : SixW25P.Covered 33306 36892 33344 35744 61946 65852 30944 35744 29720 36892 :=
  SixW25P.covered_split3 33344 wk4lllllllllrrrl wk4lllllllllrrrr
theorem wk4lllllllllrr : SixW25P.Covered 29720 36892 33344 35744 61946 65852 30944 35744 29720 36892 :=
  SixW25P.covered_split0 33306 wk4lllllllllrrl wk4lllllllllrrr
theorem wk4lllllllllr : SixW25P.Covered 29720 36892 30944 35744 61946 65852 30944 35744 29720 36892 :=
  SixW25P.covered_split1 33344 wk4lllllllllrl wk4lllllllllrr
theorem wk4lllllllll : SixW25P.Covered 29720 36892 30944 35744 58040 65852 30944 35744 29720 36892 :=
  SixW25P.covered_split2 61946 wk4llllllllll wk4lllllllllr
theorem wk4llllllllr : SixW25P.Covered 29720 36892 30944 35744 65852 73664 30944 35744 29720 36892 :=
  SixW25P.covered_of_walk lbS hbas 9990368738298813716060689739589743418932619978435113191639823143505717390580822399444090460757294709422109356315107170496421931630791048161062587839991192472958404835404612680025400631937887083896999350890506448601133716814498282526857924229170805776276271651101348103066073257293715178127400245978520882128206203324389421104440155880885467988292668762819495453870727869635421186812422195822441067417603008331926557249682561936573601426807175172922723848506252300687807792609810865186652286577069872141957529638648016431771601357939606412028041076524887955908860153748212462479737413789859614535925524809354835197573523104023053154366847733237477091467607107193917381633000409589229887884763853485608917962963075933419359857771880953430480699139191361255062941547113141434997039185948401485696012392108828225359335095827956810568687307699570505447513176404118534237944971072578266296822874317385426588773955616605882963168236324835380497694942887352814799131251269518576113725219505551279705444084836370639219260964317251616396003861301999284154116509338710467955192305154415310450740715713938836124541524290829979219443192936892465163669432028160673990475079880562218983111912080992195616682257999863666909198311857021652207208142832089433183371407658661098573548422105366707956822150798789126216287822597296819347280916054721272945928017741888981814327129841608320344782569608520845797922993622667990084207660939235504969656095273892570185143870510158649267210478341233996879571867062870540902458978201597946484966817615758215428787810220951749201873113944786211588714171241183933243193044842686720175567568787392819117506809714371051678965324834445965577727645129116794535418005185922042695620467144485857134777859096084933150327522114456102882515894569832094637272983838594220796388627275899058694352452296517748985824810902916140251860256905140300960102262691447181450323378564273722305235881120494611118650592807450883426971229829777513228994124312261439787060177065218552699362536113333603470062155193117073801801609235078021414627539701727198141569081167676878556113083056045156423286305480113091603648365119151703845098792329852845934264213490526713444041151280580373721825708076241092392890150129638801516160187085407782815338 200 29720 36892 30944 35744 65852 73664 30944 35744 29720 36892 7432
    (by decide +kernel) (by decide)
theorem wk4llllllll : SixW25P.Covered 29720 36892 30944 35744 58040 73664 30944 35744 29720 36892 :=
  SixW25P.covered_split2 65852 wk4lllllllll wk4llllllllr
theorem wk4lllllllr : SixW25P.Covered 29720 36892 30944 35744 58040 73664 35744 40544 29720 36892 :=
  SixW25P.covered_of_walk lbS hbas 409878522924387872054487971879796553542049997279484753960723786798538534669551939869644822413880511331920250747282820628367972472579146285101742 200 29720 36892 30944 35744 58040 73664 35744 40544 29720 36892 487
    (by decide +kernel) (by decide)
theorem wk4lllllll : SixW25P.Covered 29720 36892 30944 35744 58040 73664 30944 40544 29720 36892 :=
  SixW25P.covered_split3 35744 wk4llllllll wk4lllllllr
theorem wk4llllllr : SixW25P.Covered 29720 36892 35744 40544 58040 73664 30944 40544 29720 36892 :=
  SixW25P.covered_of_walk lbS hbas 315548023749583949404748968625633175572004269318809000378244527067189281114972250060382845480883034816348059639487215046148468953044891423980037686164515906245592801329312107297839788993254 200 29720 36892 35744 40544 58040 73664 30944 40544 29720 36892 632
    (by decide +kernel) (by decide)
theorem wk4llllll : SixW25P.Covered 29720 36892 30944 40544 58040 73664 30944 40544 29720 36892 :=
  SixW25P.covered_split1 35744 wk4lllllll wk4llllllr
theorem wk4lllllr : SixW25P.Covered 29720 36892 30944 40544 58040 73664 30944 40544 36892 44064 :=
  SixW25P.covered_of_walk lbS hbas 549672086326060151598 200 29720 36892 30944 40544 58040 73664 30944 40544 36892 44064 77
    (by decide +kernel) (by decide)
theorem wk4lllll : SixW25P.Covered 29720 36892 30944 40544 58040 73664 30944 40544 29720 44064 :=
  SixW25P.covered_split4 36892 wk4llllll wk4lllllr
theorem wk4llllr : SixW25P.Covered 36892 44064 30944 40544 58040 73664 30944 40544 29720 44064 :=
  SixW25P.covered_of_walk lbS hbas 66330768398768052134047327115748898 200 36892 44064 30944 40544 58040 73664 30944 40544 29720 44064 127
    (by decide +kernel) (by decide)
theorem wk4llll : SixW25P.Covered 29720 44064 30944 40544 58040 73664 30944 40544 29720 44064 :=
  SixW25P.covered_split0 36892 wk4lllll wk4llllr
theorem wk4lllr : SixW25P.Covered 29720 44064 30944 40544 73664 89288 30944 40544 29720 44064 :=
  SixW25P.covered_of_walk lbS hbas 0 200 29720 44064 30944 40544 73664 89288 30944 40544 29720 44064 2
    (by decide +kernel) (by decide)
theorem wk4lll : SixW25P.Covered 29720 44064 30944 40544 58040 89288 30944 40544 29720 44064 :=
  SixW25P.covered_split2 73664 wk4llll wk4lllr
theorem wk4llrllllll : SixW25P.Covered 29720 36892 30944 33344 89288 104912 30944 35744 29720 36892 :=
  SixW25P.covered_of_walk lbS hbas 12466958005859465683805271769737870291284592452471341342617278573382231614783962933856098333076326622571991387385520770778047763268744541628819009866597446 200 29720 36892 30944 33344 89288 104912 30944 35744 29720 36892 517
    (by decide +kernel) (by decide)
theorem wk4llrlllllrl : SixW25P.Covered 29720 33306 33344 35744 89288 104912 30944 35744 29720 36892 :=
  SixW25P.covered_of_walk lbS hbas 210364650368468479655099760248107269114563872979046396895306741423110514088338217506736913297065032058979971612795155963461705299663399101615971478791192324178671051685798244629811471706414912883830702692059318925462605199084433087374927591559082218887884822114617118679446869650365306696777442919291115947272324287691464790596594036171544576051311786911961962310809640059364897628200533672267019933951205069304196130647702519942125574470428290150644788499406067671084634357074148765057359410400778269951347079025334624340623638531820408410961939187046305829273723065566376610125910052668866 200 29720 33306 33344 35744 89288 104912 30944 35744 29720 36892 1967
    (by decide +kernel) (by decide)
theorem wk4llrlllllrr : SixW25P.Covered 33306 36892 33344 35744 89288 104912 30944 35744 29720 36892 :=
  SixW25P.covered_of_walk lbS hbas 10023473187682782431364983440577373879324678441002869425771836940986769648923064843816706055052759970801457711108992053424555593014577912487088486235916709448354727898396138219635509149403517527501864460166718593962772808356272736367277282851793624717250515376761907491178091812582971403488102596330128465287459831725954787449513609951024298139833490243578108063772433593596200322210150759165292042197588097115746421131835809877411627814085410262925028727772444938366356243313769103978583196908672809990590615023642607390542052920946875291849514699497104892128139613362385359044335036692674930518059689609333354083654982892919523265350231952618154673019358305388374161641840468695014992031922024671538711512061073808917195482409568809052817024977134367932142824676393247492127311765370473699662413292589796082437243717023859559575586971322643942220163624388249299456542484891174921698837317028912175394867411782711745210523083261364729712274943427371319101763101117470541425337690236900382415572018404483630753036224491901121282597181530843034911081345161182400858680671983620845995727219930036979719920196280681554385717091317372512516940366701696527847833531942114483531532939137309568422024974717293235184248943161467538966147106635645247431229214116394129188768258374108201022970746389130994416650437279972311020153801913703098248220234657734507413996360473027829439268929683213669209711495616490369762339602383608595390553223738763323076072604827760184436636771415552730274962033747951391482173386937380225530393789403800568253504466775933988405902336907877614446499526600923984306988299526543463584566122562697475933230007216112451829502428224567453485337715849599956512870744036425840527208726922489914454018795261167974296356758883886104913354101757901744400984255635081862900088999536820937749529759046479531690 200 33306 36892 33344 35744 89288 104912 30944 35744 29720 36892 6047
    (by decide +kernel) (by decide)
theorem wk4llrlllllr : SixW25P.Covered 29720 36892 33344 35744 89288 104912 30944 35744 29720 36892 :=
  SixW25P.covered_split0 33306 wk4llrlllllrl wk4llrlllllrr
theorem wk4llrlllll : SixW25P.Covered 29720 36892 30944 35744 89288 104912 30944 35744 29720 36892 :=
  SixW25P.covered_split1 33344 wk4llrllllll wk4llrlllllr
theorem wk4llrllllr : SixW25P.Covered 29720 36892 30944 35744 89288 104912 35744 40544 29720 36892 :=
  SixW25P.covered_of_walk lbS hbas 1771601959392213549205777650758959351693957623546325095214 200 29720 36892 30944 35744 89288 104912 35744 40544 29720 36892 197
    (by decide +kernel) (by decide)
theorem wk4llrllll : SixW25P.Covered 29720 36892 30944 35744 89288 104912 30944 40544 29720 36892 :=
  SixW25P.covered_split3 35744 wk4llrlllll wk4llrllllr
theorem wk4llrlllr : SixW25P.Covered 29720 36892 35744 40544 89288 104912 30944 40544 29720 36892 :=
  SixW25P.covered_of_walk lbS hbas 4006898648553569585478452270231966610724043532618529852494011158103859942 200 29720 36892 35744 40544 89288 104912 30944 40544 29720 36892 247
    (by decide +kernel) (by decide)
theorem wk4llrlll : SixW25P.Covered 29720 36892 30944 40544 89288 104912 30944 40544 29720 36892 :=
  SixW25P.covered_split1 35744 wk4llrllll wk4llrlllr
theorem wk4llrllr : SixW25P.Covered 29720 36892 30944 40544 104912 120537 30944 40544 29720 36892 :=
  SixW25P.covered_of_walk lbS hbas 1642 200 29720 36892 30944 40544 104912 120537 30944 40544 29720 36892 17
    (by decide +kernel) (by decide)
theorem wk4llrll : SixW25P.Covered 29720 36892 30944 40544 89288 120537 30944 40544 29720 36892 :=
  SixW25P.covered_split2 104912 wk4llrlll wk4llrllr
theorem wk4llrlr : SixW25P.Covered 29720 36892 30944 40544 89288 120537 30944 40544 36892 44064 :=
  SixW25P.covered_of_walk lbS hbas 61162 200 29720 36892 30944 40544 89288 120537 30944 40544 36892 44064 22
    (by decide +kernel) (by decide)
theorem wk4llrl : SixW25P.Covered 29720 36892 30944 40544 89288 120537 30944 40544 29720 44064 :=
  SixW25P.covered_split4 36892 wk4llrll wk4llrlr
theorem wk4llrr : SixW25P.Covered 36892 44064 30944 40544 89288 120537 30944 40544 29720 44064 :=
  SixW25P.covered_of_walk lbS hbas 419362 200 36892 44064 30944 40544 89288 120537 30944 40544 29720 44064 27
    (by decide +kernel) (by decide)
theorem wk4llr : SixW25P.Covered 29720 44064 30944 40544 89288 120537 30944 40544 29720 44064 :=
  SixW25P.covered_split0 36892 wk4llrl wk4llrr
theorem wk4ll : SixW25P.Covered 29720 44064 30944 40544 58040 120537 30944 40544 29720 44064 :=
  SixW25P.covered_split2 89288 wk4lll wk4llr
theorem wk4lr : SixW25P.Covered 29720 44064 30944 40544 120537 183034 30944 40544 29720 44064 :=
  SixW25P.covered_of_walk lbS hbas 3455385955958064331713199967939942884474721668844296365214947409249803625483280469965279748157931161576596548476295072224246337991111103819421760743212750061244082870637885927097135904547009017904322266204022067324511908243227522356897014813852533645204115369341020944729888693107433592147230311661145884370780518379453158051367069100716367348917132874405465600778320098501732255917917109264971303059243076599129574359867716730023432451630635880903020960348734105084785311263474531050999492555306 200 29720 44064 30944 40544 120537 183034 30944 40544 29720 44064 1657
    (by decide +kernel) (by decide)
theorem wk4l : SixW25P.Covered 29720 44064 30944 40544 58040 183034 30944 40544 29720 44064 :=
  SixW25P.covered_split2 120537 wk4ll wk4lr
theorem wk4r : SixW25P.Covered 29720 44064 30944 40544 183034 308028 30944 40544 29720 44064 :=
  SixW25P.covered_of_walk lbS hbas 0 200 29720 44064 30944 40544 183034 308028 30944 40544 29720 44064 2
    (by decide +kernel) (by decide)
theorem wk4 : SixW25P.Covered 29720 44064 30944 40544 58040 308028 30944 40544 29720 44064 :=
  SixW25P.covered_split2 183034 wk4l wk4r
theorem wk5llllllllllll : SixW25P.Covered 29720 36892 30944 35744 58040 73664 30944 35744 53080 62502 :=
  SixW25P.covered_of_walk lbS hbas 33499205036571986170247019820578913572106568092574915341475887609549927699373933801837053618225969846647819982681484957902813864336218481484760594638534019619851835768582626213259673370529258583334100611531334306258 200 29720 36892 30944 35744 58040 73664 30944 35744 53080 62502 717
    (by decide +kernel) (by decide)
theorem wk5lllllllllllrll : SixW25P.Covered 29720 36892 30944 35744 58040 61946 30944 35744 62502 71925 :=
  SixW25P.covered_of_walk lbS hbas 0 200 29720 36892 30944 35744 58040 61946 30944 35744 62502 71925 2
    (by decide +kernel) (by decide)
theorem wk5lllllllllllrlrl : SixW25P.Covered 29720 36892 30944 35744 61946 65852 30944 33344 62502 71925 :=
  SixW25P.covered_of_walk lbS hbas 1505883766004571847211517696445244742294349603056335801139058898687398409581674788251929656290114740089301858269100616788371870317413039271265288025383974783840703055054 200 29720 36892 30944 35744 61946 65852 30944 33344 62502 71925 567
    (by decide +kernel) (by decide)
theorem wk5lllllllllllrlrrl : SixW25P.Covered 29720 36892 30944 33344 61946 65852 33344 35744 62502 71925 :=
  SixW25P.covered_of_walk lbS hbas 603941922425316813204736861726892507431976756892521038123012187765784721975100128806019385386708952546439689621681110992105870932078080260537926249760959478142473809490204240342340343982628556252958532181764420250655812347074886796358 200 29720 36892 30944 33344 61946 65852 33344 35744 62502 71925 782
    (by decide +kernel) (by decide)
theorem wk5lllllllllllrlrrrl : SixW25P.Covered 29720 33306 33344 35744 61946 65852 33344 35744 62502 71925 :=
  SixW25P.covered_of_walk lbS hbas 615009061467164743178837802906015635489357031573467524240909043726074280766069458563726631260603661261647838540529201350150647782108635591946248610214090022639179419442394606805342265865283235500011725862154914594101390374257678980310105237879265035456858185200306166536949769837254062411188605979331438568862726928595673145807517828605916020131254725095906302908873345682412913619576514716820651650202991664357069422436000922239486275075789878016513761785524233895727395013864741480764187853559333092893050946300294015711071164051665928631086947723867080943012581945161884031421082465810840212792927778654709144266120414963065295057393750022296965602726029562989780304353219423820627770851715560100520651364371623061858053866933835524210260812835593886837850667381943698006008161867440736786636536004499011834418814867875397625630103824735767824681546507344910729299477674625748608533408348189047163861969635008328231993782491240894239130705963586487761094486374249223889837638573895657653703757522507210030289697464259797101745548262783018588710641420460099793400600301080977508393132466631741110122479031995581596711786545870430388460558181017548968792395446080809922226365106221393888664325142836432106304064552467222723099273776275745245095415996966859750097405977948016370509053030058337503663043222416788962925302156142221020333682686852845129328251261062001312962611792371438364487062343836603236928931273122627701463898013218689548297333220972005648029424717613530920375663767150891553399690834761408510254720650340974565234001739766061897305557604686527131573311042 200 29720 33306 33344 35744 61946 65852 33344 35744 62502 71925 5237
    (by decide +kernel) (by decide)
theorem wk5lllllllllllrlrrrrlll : SixW25P.Covered 33306 35099 33344 35744 61946 63899 33344 35744 62502 67213 :=
  SixW25P.covered_of_walk lbS hbas 145655031438377698522872599187667162453017329732544249636450231342092741446909985046767080431161403301909432760049064440063834217224018255889387469111626336643093061612764083169796547492425643650506376475030787465764409157771216726933507720607278714856532008274082678102139925413412811971482915727041134750812122074400318188275266234280242520273743109701833603449434960206021998754401495536351014361535907518497236722285760149829551816028955238564457228394827924470923910285636081950720234437300535987255623158847102636696635164959415928303551345252308102202302428193737176497980320748569542974136563626515195828370013709623659817835564469433951921237233390434299358462190485802560701658896528029990045998105591463130175964367784627866362688989906815874445587692385819102250300128023765721323148974734811393973374196830094180605194840264170225200428217290168065866676121945487205180370735331993444910573219806477003214632752532818693227573926 200 33306 35099 33344 35744 61946 63899 33344 35744 62502 67213 3132
    (by decide +kernel) (by decide)
theorem wk5lllllllllllrlrrrrllrllll : SixW25P.Covered 33306 35099 33344 33944 63899 65852 33344 35744 62502 63679 :=
  SixW25P.covered_of_walk lbS hbas 15756261606345366457714117990232329850936520111874514270915882844585502406648651698005598136481609562731138668436947674511395876009748134729120292037330861929872785834358979398522796667594112335246594642608227416980916768836067364595091335054839482590992252247148604421594439409598264488857087590127086018926621806711751265224512683144684131195705437522725079941431156534279833127996481303408419391594805408436148841328271869221649887726248648067774385747946643537692163052888782721589452803451247666402066637066012249419210385882557078668692851134518826552216930556185271518337145169980414405415384690039647272153682021389479387365047971853992869136877265021204398392934832772539740012300420647809115906290818062132182994857824920890524064454053518534539265077390096436767803318183768813813029888951180608636108707423087256291330608581286830185282014848518528016526034079297052972484583582594975001661319954174113155522831695271586460117144796606545570909731057548615205778934175088583405994113671601054318160210723593097791147819589603620834228792028875576099931142319418926 200 33306 35099 33344 33944 63899 65852 33344 35744 62502 63679 3577
    (by decide +kernel) (by decide)
theorem wk5lllllllllllrlrrrrllrlllr : SixW25P.Covered 33306 35099 33944 34544 63899 65852 33344 35744 62502 63679 :=
  SixW25P.covered_of_walk lbS hbas 175529722199863926960389554023364133856154340097065781466713346564502585841403982997284167071451260144848168485475293940104880311221190131106335746005383076763787517761319995642138956590424736702592832999712947345427551123642535497718957538674353340813370924479745982760929631212099569838564324584667338705466774319039895605505374066065933825998985123042084124902543199805132363514592400755502617381762352384511813815323288322731731688292957759866160846895831530787115039243379431723802082371483356499244432827020594015815921405630912340464127282261644418722457651814863472569970853534226375613823751232259498206376951584117882999389624865816661026516557461081936332627679563821661928417365099657262825537225746889171239494240656709596381643116616849188563587245418351155083940128880372804066533114499865143794560882092457931763009314161516237556124897623202490917984719960674798615036257222111670107247709893973714107113345178538354727004794571458177759573916191910310685682906113208467420480911584755906052104354734514835890254735728502033944110663365471059025869211878659442894602912632811863659233682824769212060682883831264381807769623940862939243676808653652549978013827069913073976791246450038258086250485555176854716883371358669748895367168150524996358273437336061507114898644105977525069558293031907910230361809556639324215427419460034667814657421672350152257150566346580147454500905220627656803082719040359943911675961103262097139265960255283029157932093858400083137966421616128305087736240217909081311146035124726738647556714676061591797668158581193727422417210409322345790398732893014029528367304759256276440720220026154844984932968495607460233059712568755677922 200 33306 35099 33944 34544 63899 65852 33344 35744 62502 63679 5567
    (by decide +kernel) (by decide)
theorem wk5lllllllllllrlrrrrllrlll : SixW25P.Covered 33306 35099 33344 34544 63899 65852 33344 35744 62502 63679 :=
  SixW25P.covered_split1 33944 wk5lllllllllllrlrrrrllrllll wk5lllllllllllrlrrrrllrlllr
theorem wk5lllllllllllrlrrrrllrllr : SixW25P.Covered 33306 35099 33344 34544 63899 65852 33344 35744 63679 64857 :=
  SixW25P.covered_of_walk lbS hbas 0 200 33306 35099 33344 34544 63899 65852 33344 35744 63679 64857 2
    (by decide +kernel) (by decide)
theorem wk5lllllllllllrlrrrrllrll : SixW25P.Covered 33306 35099 33344 34544 63899 65852 33344 35744 62502 64857 :=
  SixW25P.covered_split4 63679 wk5lllllllllllrlrrrrllrlll wk5lllllllllllrlrrrrllrllr
theorem wk5lllllllllllrlrrrrllrlrl : SixW25P.Covered 33306 35099 33344 34544 63899 65852 33344 35744 64857 66035 :=
  SixW25P.covered_of_walk lbS hbas 0 200 33306 35099 33344 34544 63899 65852 33344 35744 64857 66035 2
    (by decide +kernel) (by decide)
theorem wk5lllllllllllrlrrrrllrlrrll : SixW25P.Covered 33306 35099 33344 33944 63899 65852 33344 34544 66035 67213 :=
  SixW25P.covered_of_walk lbS hbas 632818739088626360513429991182710915534983400672260855933014964088103697013434052465077945257343361809335231345461078382869532675426087601190362991552024663681562093946102037326303910298200372752821724891750629898290305105378854145243937605851938238778938997722397970261259478729161837257961649235860439246804216608603364321050806381564072037833906712181019402589341177362160204232039452786425695886308354197367197137415286513768207743719844207746650662743556995218044307129487509278648676148692420816852159589718435653452632051300112815854117488766136341660291975643861968027587438172541695505386402467691839851767380718930149246517223080323335916463581457119843873144058385617272826184745076857851031642260870599654374096378071336767965003146977741041195810159085299390986090662963272979788667721242025711380386380450823032148825610723599181096007049374079769043135927799145918494827500947869011235992096096829709415720849483108136218200767489934125146802637299113530764968120607795972884083825741970456590222613533027008520087043689645447918058882462394375155257556720043471119934464915290880328869352396373175081226551601593053684294433797855141623783314179188935499922334481102652394335906 200 33306 35099 33344 33944 63899 65852 33344 34544 66035 67213 3972
    (by decide +kernel) (by decide)
theorem wk5lllllllllllrlrrrrllrlrrlr : SixW25P.Covered 33306 35099 33944 34544 63899 65852 33344 34544 66035 67213 :=
  SixW25P.covered_of_walk lbS hbas 14592267102436803446367434367239652595728977375456221682980027904548813022231345257544713336524019653717937528297533604563750785757081621920008770114710633420712895117787370095164848778091449261790674063795119458483373530353304640334491976586696905800746141274165482706740710882321834001690892146890758961218823880933151514356676314349823104685978398708868297164114798571557806169044401982021301005961346771301150783600127087991888992950803379802748392366011625168122059694874251342613068315867202480615073234040078338062245267988006624284257659012553038628394431635459869007328356299404513315981402379383770964573201297366767463055470873379059002594881553444441824636834472600956936728742938668393404408402272312347583803652949390440773394929530622800335599144065186570085704021509453565692297283370836940696005947678274136041174108787808476971108711476143081465269308372700664515881024633804838590118080468211335600248904050822434604784553187150059587683953709740972374476213894154275932146073379470277474697759509096118022985131848057908734245293293890213576889515667776321156556096475719374962894446739224468792227440023428148964204961134348830631828389521389634481296144781388525926081386873314830418973370267312386225365242942789884778226711395136168915974872213073244825750213488050437796314240965824882573400846386573412768198106104001774291331895695604078733455585510269687199057874838003179496086907658889748875607397140683226078648086178 200 33306 35099 33944 34544 63899 65852 33344 34544 66035 67213 4812
    (by decide +kernel) (by decide)
theorem wk5lllllllllllrlrrrrllrlrrl : SixW25P.Covered 33306 35099 33344 34544 63899 65852 33344 34544 66035 67213 :=
  SixW25P.covered_split1 33944 wk5lllllllllllrlrrrrllrlrrll wk5lllllllllllrlrrrrllrlrrlr
theorem wk5lllllllllllrlrrrrllrlrrr : SixW25P.Covered 33306 35099 33344 34544 63899 65852 34544 35744 66035 67213 :=
  SixW25P.covered_of_walk lbS hbas 942238818755450701285785425368595874305424987496221148415200974695299910096401085967485716844145736911204009485050067231749886481682087391531195956299785136288284381507911118387891211104495473685507939723765518660650503558979532518946868942389694193326352610490725842409526575131322132709271321759322026452753159519378163395935143502643674324117889668553916816220778 200 33306 35099 33344 34544 63899 65852 34544 35744 66035 67213 1222
    (by decide +kernel) (by decide)
theorem wk5lllllllllllrlrrrrllrlrr : SixW25P.Covered 33306 35099 33344 34544 63899 65852 33344 35744 66035 67213 :=
  SixW25P.covered_split3 34544 wk5lllllllllllrlrrrrllrlrrl wk5lllllllllllrlrrrrllrlrrr
theorem wk5lllllllllllrlrrrrllrlr : SixW25P.Covered 33306 35099 33344 34544 63899 65852 33344 35744 64857 67213 :=
  SixW25P.covered_split4 66035 wk5lllllllllllrlrrrrllrlrl wk5lllllllllllrlrrrrllrlrr
theorem wk5lllllllllllrlrrrrllrl : SixW25P.Covered 33306 35099 33344 34544 63899 65852 33344 35744 62502 67213 :=
  SixW25P.covered_split4 64857 wk5lllllllllllrlrrrrllrll wk5lllllllllllrlrrrrllrlr
theorem wk5lllllllllllrlrrrrllrr : SixW25P.Covered 33306 35099 34544 35744 63899 65852 33344 35744 62502 67213 :=
  SixW25P.covered_of_walk lbS hbas 258476074814960424368966653686702320424219173859120170897353347798718212676059821422881644256062955788608775598052755700154672935698823163750506747360072943689568986512925918080590543301498593193140672076985622183653662864739870025067591310041570443658674250575638059775316301552740094578803013966836458996702309846660397833576985464792712058052436416714353111050414726558596544389047926794251363492604481905404354252604903779998990116166756187025492827842424117494012922424934946642173298157346 200 33306 35099 34544 35744 63899 65852 33344 35744 62502 67213 1647
    (by decide +kernel) (by decide)
theorem wk5lllllllllllrlrrrrllr : SixW25P.Covered 33306 35099 33344 35744 63899 65852 33344 35744 62502 67213 :=
  SixW25P.covered_split1 34544 wk5lllllllllllrlrrrrllrl wk5lllllllllllrlrrrrllrr
theorem wk5lllllllllllrlrrrrll : SixW25P.Covered 33306 35099 33344 35744 61946 65852 33344 35744 62502 67213 :=
  SixW25P.covered_split2 63899 wk5lllllllllllrlrrrrlll wk5lllllllllllrlrrrrllr
theorem wk5lllllllllllrlrrrrlr : SixW25P.Covered 35099 36892 33344 35744 61946 65852 33344 35744 62502 67213 :=
  SixW25P.covered_of_walk lbS hbas 33836478672387249251688406099143628111336882233928889440013524697298509458465207324410043350282554099020582022730512905513497658697663810102609132821193322 200 35099 36892 33344 35744 61946 65852 33344 35744 62502 67213 517
    (by decide +kernel) (by decide)
theorem wk5lllllllllllrlrrrrl : SixW25P.Covered 33306 36892 33344 35744 61946 65852 33344 35744 62502 67213 :=
  SixW25P.covered_split0 35099 wk5lllllllllllrlrrrrll wk5lllllllllllrlrrrrlr
theorem wk5lllllllllllrlrrrrr : SixW25P.Covered 33306 36892 33344 35744 61946 65852 33344 35744 67213 71925 :=
  SixW25P.covered_of_walk lbS hbas 5386089646812126649692345515229791357339542644699741917395711592079150558966438368939790196139368236001833975219315659899687690514307453253543818099839842990262530837662984046423657071167180657621685183442766569435283566006985376588399439097378052708991912519452617970349361506135670066235462131092309245773144344988376921529470455350275854551950228793999649330 200 33306 36892 33344 35744 61946 65852 33344 35744 67213 71925 1202
    (by decide +kernel) (by decide)
theorem wk5lllllllllllrlrrrr : SixW25P.Covered 33306 36892 33344 35744 61946 65852 33344 35744 62502 71925 :=
  SixW25P.covered_split4 67213 wk5lllllllllllrlrrrrl wk5lllllllllllrlrrrrr
theorem wk5lllllllllllrlrrr : SixW25P.Covered 29720 36892 33344 35744 61946 65852 33344 35744 62502 71925 :=
  SixW25P.covered_split0 33306 wk5lllllllllllrlrrrl wk5lllllllllllrlrrrr
theorem wk5lllllllllllrlrr : SixW25P.Covered 29720 36892 30944 35744 61946 65852 33344 35744 62502 71925 :=
  SixW25P.covered_split1 33344 wk5lllllllllllrlrrl wk5lllllllllllrlrrr
theorem wk5lllllllllllrlr : SixW25P.Covered 29720 36892 30944 35744 61946 65852 30944 35744 62502 71925 :=
  SixW25P.covered_split3 33344 wk5lllllllllllrlrl wk5lllllllllllrlrr
theorem wk5lllllllllllrl : SixW25P.Covered 29720 36892 30944 35744 58040 65852 30944 35744 62502 71925 :=
  SixW25P.covered_split2 61946 wk5lllllllllllrll wk5lllllllllllrlr
theorem wk5lllllllllllrrll : SixW25P.Covered 29720 36892 30944 35744 65852 69758 30944 33344 62502 71925 :=
  SixW25P.covered_of_walk lbS hbas 6311702229566889253871714984039828910941666117303235518161774914357000241978444721744317646 200 29720 36892 30944 35744 65852 69758 30944 33344 62502 71925 312
    (by decide +kernel) (by decide)
theorem wk5lllllllllllrrlrl : SixW25P.Covered 29720 36892 30944 33344 65852 69758 33344 35744 62502 71925 :=
  SixW25P.covered_of_walk lbS hbas 145844936739125919710442164248619999864612915481808355186475971523856720778978992056189935191309095789562216482623450253295107282175047719927515441010682623784660214645824768601803140351269858231377232966 200 29720 36892 30944 33344 65852 69758 33344 35744 62502 71925 682
    (by decide +kernel) (by decide)
theorem wk5lllllllllllrrlrrl : SixW25P.Covered 29720 33306 33344 35744 65852 69758 33344 35744 62502 71925 :=
  SixW25P.covered_of_walk lbS hbas 32117682961175953966598393959907083524290532665905598350460394098090902421935745067590851070108140012073418282848814836634745575674127792893500693643853937618578115941820413267062408998179260041111039939634529162621609843389344185434063976418034833105958249901523845891254276847229635064467927451636240106362606661221660871695369610255764030884743789503703714978202158105429102082799801885773816031907934382375906945886326121981846274495944612965182578029667146686977735895388011279094119268297735710988371584770933678634335787622400441733746134507822582848674498834522721366076941569965812961639114964871783260053205442109027338601848086823111752859938175810704760935731598782668323170400988321346 200 29720 33306 33344 35744 65852 69758 33344 35744 62502 71925 2327
    (by decide +kernel) (by decide)
theorem wk5lllllllllllrrlrrr : SixW25P.Covered 33306 36892 33344 35744 65852 69758 33344 35744 62502 71925 :=
  SixW25P.covered_of_walk lbS hbas 24859988756606925693941127807740367599245327574272114662720430037333998993361164356412183990124059972417701891640278879717935321784320409078944970345756132865696921884073942762309789614844981816527212908468139359053495793557160863880004860323658597686465262028739188677066551761025194598928150306468260344616183968548155604453785738385957801846682062062069500765753256686766966591572071225675879207226647673294847698808463929450275258019862152149333374470441498177711336616521980107044249583217892549020813166133927051961797959741857032367369890826708290146085842715218007093835283550851494882766716875483355110805185883957203279560910762072864587519016720587081889121856321008749254969302909280284169952764957153346349226911114176185912451687558604275421174551879099343976221319953155725905516100307913703411965950767173669918022401517078479896394816350548273178108960023559437075134978783992801994116080523119014923828753358622781873739926084922787612576323297347487813459666642426671625742172296705295095268524745946643487606393756976517667655077932954032939548269015630538696810681288496331165494087671077271246612346294203987630786370341273528167036488457123534653838384968935839342916372473506424105374037397384918484240167575638819273122455812389315104181784194424493650384638887157264168098713987581321608601311039803259315663229376280838588547394922015935370180522174471846453748964953997925673870671848133088249904029094894896836359659994880167521280825333279835371954307698426371946973536005813619421649860585721274413421687491767684352663279705946596798901747034246246717054584787455819981847172783939115702913119723498453780652358620384148715664737697346835692042633889993235513033441233686491861753753220997210492106596319702047038722213745680923667650402386711308023783581441126255470781205845068353510128161574886315293627534358423688451645772531391046914947823595103435127925643241722727458455043627207466273833647462312498 200 33306 36892 33344 35744 65852 69758 33344 35744 62502 71925 6452
    (by decide +kernel) (by decide)
theorem wk5lllllllllllrrlrr : SixW25P.Covered 29720 36892 33344 35744 65852 69758 33344 35744 62502 71925 :=
  SixW25P.covered_split0 33306 wk5lllllllllllrrlrrl wk5lllllllllllrrlrrr
theorem wk5lllllllllllrrlr : SixW25P.Covered 29720 36892 30944 35744 65852 69758 33344 35744 62502 71925 :=
  SixW25P.covered_split1 33344 wk5lllllllllllrrlrl wk5lllllllllllrrlrr
theorem wk5lllllllllllrrl : SixW25P.Covered 29720 36892 30944 35744 65852 69758 30944 35744 62502 71925 :=
  SixW25P.covered_split3 33344 wk5lllllllllllrrll wk5lllllllllllrrlr
theorem wk5lllllllllllrrr : SixW25P.Covered 29720 36892 30944 35744 69758 73664 30944 35744 62502 71925 :=
  SixW25P.covered_of_walk lbS hbas 1148650 200 29720 36892 30944 35744 69758 73664 30944 35744 62502 71925 27
    (by decide +kernel) (by decide)
theorem wk5lllllllllllrr : SixW25P.Covered 29720 36892 30944 35744 65852 73664 30944 35744 62502 71925 :=
  SixW25P.covered_split2 69758 wk5lllllllllllrrl wk5lllllllllllrrr
theorem wk5lllllllllllr : SixW25P.Covered 29720 36892 30944 35744 58040 73664 30944 35744 62502 71925 :=
  SixW25P.covered_split2 65852 wk5lllllllllllrl wk5lllllllllllrr
theorem wk5lllllllllll : SixW25P.Covered 29720 36892 30944 35744 58040 73664 30944 35744 53080 71925 :=
  SixW25P.covered_split4 62502 wk5llllllllllll wk5lllllllllllr
theorem wk5llllllllllr : SixW25P.Covered 29720 36892 30944 35744 58040 73664 35744 40544 53080 71925 :=
  SixW25P.covered_of_walk lbS hbas 1267211060244099754378958160581952583600381444377722304910112745583782933790759277391453767752769974952831063953051721155143252080816337612324796217515203433432561189356207628681667546423005033434035339416839382722696063519131781622253207741018678439548860033836460016839963685260212133275097351726579518272048213180392458597406488341895870988760128319954051206446432059916632492229845622946710814334443507727628389038 200 29720 36892 30944 35744 58040 73664 35744 40544 53080 71925 1392
    (by decide +kernel) (by decide)
theorem wk5llllllllll : SixW25P.Covered 29720 36892 30944 35744 58040 73664 30944 40544 53080 71925 :=
  SixW25P.covered_split3 35744 wk5lllllllllll wk5llllllllllr
theorem wk5lllllllllr : SixW25P.Covered 29720 36892 35744 40544 58040 73664 30944 40544 53080 71925 :=
  SixW25P.covered_of_walk lbS hbas 42692353792159381238337306308604305130840023593776592640357917720429376839362393813818915996617721913376030182054 200 29720 36892 35744 40544 58040 73664 30944 40544 53080 71925 382
    (by decide +kernel) (by decide)
theorem wk5lllllllll : SixW25P.Covered 29720 36892 30944 40544 58040 73664 30944 40544 53080 71925 :=
  SixW25P.covered_split1 35744 wk5llllllllll wk5lllllllllr
theorem wk5llllllllr : SixW25P.Covered 36892 44064 30944 40544 58040 73664 30944 40544 53080 71925 :=
  SixW25P.covered_of_walk lbS hbas 418342 200 36892 44064 30944 40544 58040 73664 30944 40544 53080 71925 27
    (by decide +kernel) (by decide)
theorem wk5llllllll : SixW25P.Covered 29720 44064 30944 40544 58040 73664 30944 40544 53080 71925 :=
  SixW25P.covered_split0 36892 wk5lllllllll wk5llllllllr
theorem wk5lllllllr : SixW25P.Covered 29720 44064 30944 40544 58040 73664 30944 40544 71925 90770 :=
  SixW25P.covered_of_walk lbS hbas 16593533499536885689954 200 29720 44064 30944 40544 58040 73664 30944 40544 71925 90770 77
    (by decide +kernel) (by decide)
theorem wk5lllllll : SixW25P.Covered 29720 44064 30944 40544 58040 73664 30944 40544 53080 90770 :=
  SixW25P.covered_split4 71925 wk5llllllll wk5lllllllr
theorem wk5llllllr : SixW25P.Covered 29720 44064 30944 40544 58040 73664 30944 40544 90770 128460 :=
  SixW25P.covered_of_walk lbS hbas 116148167093275109518187769441063387090044737418451729866828718487354492696773687757391515835747037554632033705626887603631334721198462017259386693873093512218687338486251956173529604639543203135475741172028892261457989117387988007248217456488517134910551723494204491444785297198711840097024220682858753455628627013523535198490116002610186588584073123208104935895910751197007171757871086273027861981800250408867775092876987476139190685912369630260638305542965696393596869570625605418929140751997812265816620996723926122521585948482762503700589774247858442834601244611040194594300818636675263471737357371198443541170019901807946752226782989772370217291107390170864798341048217739195983060467413961804790529886817567317711554728514865308885509650370810808724565468250020876161929744626778158568348681627678148927442435667939388961201972512938333346856651265420823440824666868472250448023853809152327687945752923990252600055893333889564807981504869392207489123086564232333031948493833790435337296648312356736308544333614910914008638194677290391437281610044380326888991202403901653947318642974874829489909996742027829911976585428537344862266981704915065675240767765935082386543073084928751717661338038526863365459890345247490593962918784705922165357356786246571645480396775984747916971747207445379926885044448849749326670908991387265432894595513942675081677116199304594609460797044842967498282551173065797894370377097913807148640181424514787125049119315125264814877478946485280258205276393758654092252155329772201954553902148953892085698762645504767876487660992504395993834064836591593259967648857909482234771681663550615749111625505681756760758818375666115059865675008749028643333680330250028088635641624569839359714149924027661841593831794831627845806604851962132695326862946 200 29720 44064 30944 40544 58040 73664 30944 40544 90770 128460 5892
    (by decide +kernel) (by decide)
theorem wk5llllll : SixW25P.Covered 29720 44064 30944 40544 58040 73664 30944 40544 53080 128460 :=
  SixW25P.covered_split4 90770 wk5lllllll wk5llllllr
theorem wk5lllllr : SixW25P.Covered 29720 44064 30944 40544 58040 73664 30944 40544 128460 203840 :=
  SixW25P.covered_of_walk lbS hbas 1772256303398186716938621472999153418597691374770215588752624456378361230306600738 200 29720 44064 30944 40544 58040 73664 30944 40544 128460 203840 277
    (by decide +kernel) (by decide)
theorem wk5lllll : SixW25P.Covered 29720 44064 30944 40544 58040 73664 30944 40544 53080 203840 :=
  SixW25P.covered_split4 128460 wk5llllll wk5lllllr
theorem wk5llllr : SixW25P.Covered 29720 44064 30944 40544 73664 89288 30944 40544 53080 203840 :=
  SixW25P.covered_of_walk lbS hbas 0 200 29720 44064 30944 40544 73664 89288 30944 40544 53080 203840 2
    (by decide +kernel) (by decide)
theorem wk5llll : SixW25P.Covered 29720 44064 30944 40544 58040 89288 30944 40544 53080 203840 :=
  SixW25P.covered_split2 73664 wk5lllll wk5llllr
theorem wk5lllr : SixW25P.Covered 29720 44064 30944 40544 89288 120537 30944 40544 53080 203840 :=
  SixW25P.covered_of_walk lbS hbas 53532073492928160930147840828629417319689511063602494072800052659603041158068597238585273913884740150703052260065419573942802994385593187095329599384980356495063869252061973986169633879291717803100454665583780635036547102634946968754723012589041840406223609732663205213205754781525804668150555590300883511814716883252013990677629742177184246446630237090739885014883127143769230852746708672478903131210321093679888081988595497751161013409362129022637247273203114826568474629612382886876386757540430879092491520047072118116079429821334501274830430074361997549961410665157275170982702536676231414705377570907524942829407271661612357647704950017837451721591835067552654293544518201035712056545677652997097813867517191588464988151562159787846251690071074379322901167978653780037444020283842932975490671652064896485325767521182620930253507000164762472453412001539239255745609547598143667908635357719326660120655159003583277334853577628429452764134501073490065202508553374480502127251610912274492308563256935285016454816147811796818434152877828087614836764837201430912938463363901694283737820934449682471166955526116130597194096534972440351012846950590749229354357186849482109721375762677773312390727672981200742759151383428125454807366916688017888779071709068835917208782500236540479912894952351316992300720063217589456033652743369179555278733270413868564012458197584893469089552032870074558631720577418259854660242311024680895253281645828458330946772915691091655297840224804304196547937702661651695701305312238285219491981171426729689843333909366812127414710734881269806755679813188075338720041821485029898815444973579915736390741104430821415622500529848606084976874327266470490892168659635229392778034 200 29720 44064 30944 40544 89288 120537 30944 40544 53080 203840 5642
    (by decide +kernel) (by decide)
theorem wk5lll : SixW25P.Covered 29720 44064 30944 40544 58040 120537 30944 40544 53080 203840 :=
  SixW25P.covered_split2 89288 wk5llll wk5lllr
theorem wk5llr : SixW25P.Covered 29720 44064 30944 40544 120537 183034 30944 40544 53080 203840 :=
  SixW25P.covered_of_walk lbS hbas 40462462217037586959443247127393650142077903666246180237142566589592826681058079282 200 29720 44064 30944 40544 120537 183034 30944 40544 53080 203840 282
    (by decide +kernel) (by decide)
theorem wk5ll : SixW25P.Covered 29720 44064 30944 40544 58040 183034 30944 40544 53080 203840 :=
  SixW25P.covered_split2 120537 wk5lll wk5llr
theorem wk5lr : SixW25P.Covered 29720 44064 30944 40544 58040 183034 30944 40544 203840 354601 :=
  SixW25P.covered_of_walk lbS hbas 0 200 29720 44064 30944 40544 58040 183034 30944 40544 203840 354601 2
    (by decide +kernel) (by decide)
theorem wk5l : SixW25P.Covered 29720 44064 30944 40544 58040 183034 30944 40544 53080 354601 :=
  SixW25P.covered_split4 203840 wk5ll wk5lr
theorem wk5r : SixW25P.Covered 29720 44064 30944 40544 183034 308028 30944 40544 53080 354601 :=
  SixW25P.covered_of_walk lbS hbas 0 200 29720 44064 30944 40544 183034 308028 30944 40544 53080 354601 2
    (by decide +kernel) (by decide)
theorem wk5 : SixW25P.Covered 29720 44064 30944 40544 58040 308028 30944 40544 53080 354601 :=
  SixW25P.covered_split2 183034 wk5l wk5r
theorem wk6llllllllllll : SixW25P.Covered 29720 36892 30944 35744 58040 73664 57472 63537 29720 36892 :=
  SixW25P.covered_of_walk lbS hbas 521196575278677878447418996804745906671589379255644784368049846731173364860666196183986373083207752975781231444000821567882548095647460091972220341847258815863580723667182185840217058285686511758388419444886897593453276225182459204146261525487698844360972312458435585202188976051870159488377132366 200 29720 36892 30944 35744 58040 73664 57472 63537 29720 36892 992
    (by decide +kernel) (by decide)
theorem wk6lllllllllllrll : SixW25P.Covered 29720 36892 30944 35744 58040 61946 63537 69602 29720 36892 :=
  SixW25P.covered_of_walk lbS hbas 0 200 29720 36892 30944 35744 58040 61946 63537 69602 29720 36892 2
    (by decide +kernel) (by decide)
theorem wk6lllllllllllrlrl : SixW25P.Covered 29720 36892 30944 33344 61946 65852 63537 69602 29720 36892 :=
  SixW25P.covered_of_walk lbS hbas 3450486662015808910261414726734381674090576157165938303335081605840462200829012293299650014067894196160710 200 29720 36892 30944 33344 61946 65852 63537 69602 29720 36892 357
    (by decide +kernel) (by decide)
theorem wk6lllllllllllrlrrl : SixW25P.Covered 29720 33306 33344 35744 61946 65852 63537 69602 29720 36892 :=
  SixW25P.covered_of_walk lbS hbas 1211880290020260848101165857120258983969393363227406834347841331474686916379070850714763213779638152503148712633762458207010428348567217471002633567853529886124700679343698291830041211915246217620250721397369673172781929871733319172776320468845790425854047255106994323917638280694264717133023139656713874598179743765250353116310449727043665429440020384307554091564698631876004497926149448469918905022402796745122077402909324332762974754719363000452043718761173081639366293070874158162077613539149596790445547911667183109305093434751807519216571373117230038273415695183941395900521846351778934434691090844466969221079547332288529338250295639059542222359899091565436778715739482508928578 200 29720 33306 33344 35744 61946 65852 63537 69602 29720 36892 2277
    (by decide +kernel) (by decide)
theorem wk6lllllllllllrlrrrl : SixW25P.Covered 33306 36892 33344 35744 61946 65852 63537 69602 29720 33306 :=
  SixW25P.covered_of_walk lbS hbas 37869088158309879105753520458841850586099710538564690 200 33306 36892 33344 35744 61946 65852 63537 69602 29720 33306 192
    (by decide +kernel) (by decide)
theorem wk6lllllllllllrlrrrrl : SixW25P.Covered 33306 36892 33344 35744 61946 65852 63537 66569 33306 36892 :=
  SixW25P.covered_of_walk lbS hbas 3338383608272970672480038966084864174742079687103183614280663897436457330873060130590476736478345097990155485387316107800486632719449355442522338254982975087237643342657891844877823947089401990352819618569240827730529801675322555563950004105347623878265201933491643878420532982111849862654802351340617948745222786034658149528694613625999528777424894150900577855405183038160396284885653787385399775594076353719828035156843137494705816269626362435580062768940599892151580314601563903237174859614889282362555521746590812139922418942304964171374845842759288082136065214163091947526177969650160296551639617454737225524860384083565549417770197593201662337000757406698989155631779941969547372744492327052761749321113375972220639420221228019646327877496257579534343567939291581678883131199927096376464840963535638644033382432901801426827496830369724976101136729774614525128330762636024685212397661497126038486503308696755246904837389636514137491970346122068562439379664100650066613153313796103705802425622135171970522264609034486345748970129516402691732302176265312021024948333464974366219396562849259528887826181685682391342800260123769789762956791822233010476971820118623446777246078652359345250849442689162459504944929222683969914743928496713985998665703822655552276593309903274541780008264518456764222632169271977368573991596963336103539744218760962779465337638478535749960111294607543241795343784775159501830138890733318242998488818646236736069853989465748220347076810405104325678125029764839095757007084098538262658568957323292755436138891933501300349222246638273021762573194212137484334098041041726889426240265425256103483612207255516827014694561508144338409090382574661624295041661356548096906538838359484698604635627450946393932379144009816827601304482391829672934144160179382745615281982668177847322560088100802730138814037851249778639459681955523696064875625528378446132078183590229807532017092328189611318268397012475980833122366455785019375174926367926913774562228203809520655531803212447133239307492649229775967201476385005281884259204244620109474 200 33306 36892 33344 35744 61946 65852 63537 66569 33306 36892 6822
    (by decide +kernel) (by decide)
theorem wk6lllllllllllrlrrrrr : SixW25P.Covered 33306 36892 33344 35744 61946 65852 66569 69602 33306 36892 :=
  SixW25P.covered_of_walk lbS hbas 243357411890108154303970274474517536518182494144760168349407551868643685520267082508352812163578664798287808598845819266745556448287331033383525940324384249672367284876091392103727044710839045347959889630002650317377283516353922879817582879852332636942872412347082591003390198269922901087867475751348868341970867630447988090066554287506635779508496939517670791310616105126523111590818251567493704284251468952126194189980056049402520977359496740426813686523995423082355299248657353679415494413865976852955911011654633891247703258100675149689624590579264907737889021011335795187246287641528056399314117550432098150503636086003577677047029499483320653337790306273284885307681094427422478310168061401028143358635059910852161186 200 33306 36892 33344 35744 61946 65852 66569 69602 33306 36892 2417
    (by decide +kernel) (by decide)
theorem wk6lllllllllllrlrrrr : SixW25P.Covered 33306 36892 33344 35744 61946 65852 63537 69602 33306 36892 :=
  SixW25P.covered_split3 66569 wk6lllllllllllrlrrrrl wk6lllllllllllrlrrrrr
theorem wk6lllllllllllrlrrr : SixW25P.Covered 33306 36892 33344 35744 61946 65852 63537 69602 29720 36892 :=
  SixW25P.covered_split4 33306 wk6lllllllllllrlrrrl wk6lllllllllllrlrrrr
theorem wk6lllllllllllrlrr : SixW25P.Covered 29720 36892 33344 35744 61946 65852 63537 69602 29720 36892 :=
  SixW25P.covered_split0 33306 wk6lllllllllllrlrrl wk6lllllllllllrlrrr
theorem wk6lllllllllllrlr : SixW25P.Covered 29720 36892 30944 35744 61946 65852 63537 69602 29720 36892 :=
  SixW25P.covered_split1 33344 wk6lllllllllllrlrl wk6lllllllllllrlrr
theorem wk6lllllllllllrl : SixW25P.Covered 29720 36892 30944 35744 58040 65852 63537 69602 29720 36892 :=
  SixW25P.covered_split2 61946 wk6lllllllllllrll wk6lllllllllllrlr
theorem wk6lllllllllllrrll : SixW25P.Covered 29720 36892 30944 33344 65852 69758 63537 69602 29720 36892 :=
  SixW25P.covered_of_walk lbS hbas 12975063830758421331010414313464752576245380069095646457170854739654375609580097798973858039288495027764010967369629899827497158 200 29720 36892 30944 33344 65852 69758 63537 69602 29720 36892 432
    (by decide +kernel) (by decide)
theorem wk6lllllllllllrrlrl : SixW25P.Covered 29720 33306 33344 35744 65852 69758 63537 69602 29720 36892 :=
  SixW25P.covered_of_walk lbS hbas 38118380165511558049266313852565724307192901389486781088728789470219266897468058536359092651586343482500541366901514417527916943748106431123976501921548454507506189937005140056986938762286059574002775132194290584294603722597936312150614457168654380394609993171738230265865321321952213103374863690705451321266331839982214497235550408935418503228322959051206325579070818908933615476960434612127822475321790744221634260212468697336840732045658447612912651129751263732163929010610140587560415685085944240224014535016265780332593387556331718885952960119943257264896917319913881438592532160668109362378613085528798754345932113820473402946 200 29720 33306 33344 35744 65852 69758 63537 69602 29720 36892 2107
    (by decide +kernel) (by decide)
theorem wk6lllllllllllrrlrr : SixW25P.Covered 33306 36892 33344 35744 65852 69758 63537 69602 29720 36892 :=
  SixW25P.covered_of_walk lbS hbas 39110053176714225384133841446613109102717096310255305282060116118823190085564651425192636472178911363221284841235723727873235656376846133498595099689076555030677697242676493137518931645960234300060234369543579385785551603515314974234481407808680702798469052486418173853246625674747897616525197618777707025779345260422262493492168873329286983958978436012394917373391121566866631560861453324814585952753032303162215154480795133792702967517796384939634141473994369812649396565823058120167640741993644262659439755614675093029195417052912936203303123322777074401718205951564948611188901229453397346154854567368237178185635825416832139933045067255740279636202875610611852257825224263901476260527606653620849592559518309085963301695228609656076087597421130151997717150225793713310183116258357694481850982717989221516102485959165493821059688572045346302586472097653082710146789483020213257492137809933027810333005466913605693025798651179217426954419517982795689168371052373626073670472625938554889502020622736742456358748401762777603932972674061046742218733991176427797983930498643774516230638488684819956545300095434546240981076398741858049467164560785146715322122821737262008832873727320848402790905190497302461276083898295680693718312298436918688221163827640613107464243004198943422795976930044267835848324527526429457502334843131432414437333362746241975223135780546297217874420378444794839205345151769138740568020798474920743928745579722227651305432250458094538421349895441180503887351989467146328265567104878300079885438309755191353792012314248051140570446904530288369732375172109209982019401754708170983220075778340215912385824542814990190463362952957434191336280580831285163035868165781146436904720250293566515247701000050546231579212847170718728570036450672379571759804428567137765280449868440453536253399983485895986 200 33306 36892 33344 35744 65852 69758 63537 69602 29720 36892 6042
    (by decide +kernel) (by decide)
theorem wk6lllllllllllrrlr : SixW25P.Covered 29720 36892 33344 35744 65852 69758 63537 69602 29720 36892 :=
  SixW25P.covered_split0 33306 wk6lllllllllllrrlrl wk6lllllllllllrrlrr
theorem wk6lllllllllllrrl : SixW25P.Covered 29720 36892 30944 35744 65852 69758 63537 69602 29720 36892 :=
  SixW25P.covered_split1 33344 wk6lllllllllllrrll wk6lllllllllllrrlr
theorem wk6lllllllllllrrr : SixW25P.Covered 29720 36892 30944 35744 69758 73664 63537 69602 29720 36892 :=
  SixW25P.covered_of_walk lbS hbas 78529593962 200 29720 36892 30944 35744 69758 73664 63537 69602 29720 36892 42
    (by decide +kernel) (by decide)
theorem wk6lllllllllllrr : SixW25P.Covered 29720 36892 30944 35744 65852 73664 63537 69602 29720 36892 :=
  SixW25P.covered_split2 69758 wk6lllllllllllrrl wk6lllllllllllrrr
theorem wk6lllllllllllr : SixW25P.Covered 29720 36892 30944 35744 58040 73664 63537 69602 29720 36892 :=
  SixW25P.covered_split2 65852 wk6lllllllllllrl wk6lllllllllllrr
theorem wk6lllllllllll : SixW25P.Covered 29720 36892 30944 35744 58040 73664 57472 69602 29720 36892 :=
  SixW25P.covered_split3 63537 wk6llllllllllll wk6lllllllllllr
theorem wk6llllllllllr : SixW25P.Covered 29720 36892 30944 35744 58040 73664 57472 69602 36892 44064 :=
  SixW25P.covered_of_walk lbS hbas 21087151222834052008223649923293595976578359326175026 200 29720 36892 30944 35744 58040 73664 57472 69602 36892 44064 182
    (by decide +kernel) (by decide)
theorem wk6llllllllll : SixW25P.Covered 29720 36892 30944 35744 58040 73664 57472 69602 29720 44064 :=
  SixW25P.covered_split4 36892 wk6lllllllllll wk6llllllllllr
theorem wk6lllllllllr : SixW25P.Covered 29720 36892 35744 40544 58040 73664 57472 69602 29720 44064 :=
  SixW25P.covered_of_walk lbS hbas 65518437122931772549321685388919373210200937679450696779513680409217888038 200 29720 36892 35744 40544 58040 73664 57472 69602 29720 44064 257
    (by decide +kernel) (by decide)
theorem wk6lllllllll : SixW25P.Covered 29720 36892 30944 40544 58040 73664 57472 69602 29720 44064 :=
  SixW25P.covered_split1 35744 wk6llllllllll wk6lllllllllr
theorem wk6llllllllr : SixW25P.Covered 36892 44064 30944 40544 58040 73664 57472 69602 29720 44064 :=
  SixW25P.covered_of_walk lbS hbas 418342 200 36892 44064 30944 40544 58040 73664 57472 69602 29720 44064 27
    (by decide +kernel) (by decide)
theorem wk6llllllll : SixW25P.Covered 29720 44064 30944 40544 58040 73664 57472 69602 29720 44064 :=
  SixW25P.covered_split0 36892 wk6lllllllll wk6llllllllr
theorem wk6lllllllr : SixW25P.Covered 29720 44064 30944 40544 58040 73664 69602 81733 29720 44064 :=
  SixW25P.covered_of_walk lbS hbas 89307369094887629501688591086 200 29720 44064 30944 40544 58040 73664 69602 81733 29720 44064 102
    (by decide +kernel) (by decide)
theorem wk6lllllll : SixW25P.Covered 29720 44064 30944 40544 58040 73664 57472 81733 29720 44064 :=
  SixW25P.covered_split3 69602 wk6llllllll wk6lllllllr
theorem wk6llllllr : SixW25P.Covered 29720 44064 30944 40544 58040 73664 81733 105995 29720 44064 :=
  SixW25P.covered_of_walk lbS hbas 27590745724858064770857666844363619163021496392394715422099485412468398669547443430942817617030216255274657155755872045079686569562709620453118342400717547807742952220236420191881248896224127519483511149436864458389558574523978468142935195575944419924691455872346597746340578 200 29720 44064 30944 40544 58040 73664 81733 105995 29720 44064 917
    (by decide +kernel) (by decide)
theorem wk6llllll : SixW25P.Covered 29720 44064 30944 40544 58040 73664 57472 105995 29720 44064 :=
  SixW25P.covered_split3 81733 wk6lllllll wk6llllllr
theorem wk6lllllr : SixW25P.Covered 29720 44064 30944 40544 73664 89288 57472 105995 29720 44064 :=
  SixW25P.covered_of_walk lbS hbas 0 200 29720 44064 30944 40544 73664 89288 57472 105995 29720 44064 2
    (by decide +kernel) (by decide)
theorem wk6lllll : SixW25P.Covered 29720 44064 30944 40544 58040 89288 57472 105995 29720 44064 :=
  SixW25P.covered_split2 73664 wk6llllll wk6lllllr
theorem wk6llllr : SixW25P.Covered 29720 44064 30944 40544 89288 120537 57472 105995 29720 44064 :=
  SixW25P.covered_of_walk lbS hbas 46380395548913269109404421125574763690568328007490859789847466432932172009068902285466811328288412355896359838269106138559641761005160277267614234678024382817025315245285457335153624413066257174432029637160000864243847545881519477708817071338435205152857557442994270585123221553097013608660212592487319195288389982651836589962070103183641021334373810977452478436605432935854788088672286858651101728143750061715609305648974907455918986718177177529518224095436790011634217134696943824972967417442842836023058659591178027084116527719512697859977477846297278181682872398300850376154136140216821754911660799146673247645265104025508166027267591601099359100570947981396378638392073481776409977200673180761847270421930541533152635240489710 200 29720 44064 30944 40544 89288 120537 57472 105995 29720 44064 2437
    (by decide +kernel) (by decide)
theorem wk6llll : SixW25P.Covered 29720 44064 30944 40544 58040 120537 57472 105995 29720 44064 :=
  SixW25P.covered_split2 89288 wk6lllll wk6llllr
theorem wk6lllr : SixW25P.Covered 29720 44064 30944 40544 120537 183034 57472 105995 29720 44064 :=
  SixW25P.covered_of_walk lbS hbas 9989707007175305966 200 29720 44064 30944 40544 120537 183034 57472 105995 29720 44064 77
    (by decide +kernel) (by decide)
theorem wk6lll : SixW25P.Covered 29720 44064 30944 40544 58040 183034 57472 105995 29720 44064 :=
  SixW25P.covered_split2 120537 wk6llll wk6lllr
theorem wk6llr : SixW25P.Covered 29720 44064 30944 40544 58040 183034 105995 154518 29720 44064 :=
  SixW25P.covered_of_walk lbS hbas 74929073057573546 200 29720 44064 30944 40544 58040 183034 105995 154518 29720 44064 67
    (by decide +kernel) (by decide)
theorem wk6ll : SixW25P.Covered 29720 44064 30944 40544 58040 183034 57472 154518 29720 44064 :=
  SixW25P.covered_split3 105995 wk6lll wk6llr
theorem wk6lr : SixW25P.Covered 29720 44064 30944 40544 183034 308028 57472 154518 29720 44064 :=
  SixW25P.covered_of_walk lbS hbas 0 200 29720 44064 30944 40544 183034 308028 57472 154518 29720 44064 2
    (by decide +kernel) (by decide)
theorem wk6l : SixW25P.Covered 29720 44064 30944 40544 58040 308028 57472 154518 29720 44064 :=
  SixW25P.covered_split2 183034 wk6ll wk6lr
theorem wk6r : SixW25P.Covered 29720 44064 30944 40544 58040 308028 154518 251564 29720 44064 :=
  SixW25P.covered_of_walk lbS hbas 0 200 29720 44064 30944 40544 58040 308028 154518 251564 29720 44064 2
    (by decide +kernel) (by decide)
theorem wk6 : SixW25P.Covered 29720 44064 30944 40544 58040 308028 57472 251564 29720 44064 :=
  SixW25P.covered_split3 154518 wk6l wk6r
theorem wk7 : SixW25P.Covered 29720 44064 30944 40544 58040 308028 57472 251564 53080 354601 :=
  SixW25P.covered_of_walk lbS hbas 21444169521605076251238097783562726610303566575874579147358631772152651989366617471673827051877047060922358056953532489822692294693807901702486779164807848471734761410347187600918396106580982698876558469630389563162559795200048470026264021260738882553397191774333915416157236809182623743987989577965684322104256143052374114248713603670946697988109274043529321936796109542826173688738708515836254043368627805712046369696584473698984469686158100308644619549184197500266525507657134184664872103080148280793264899780834300467060755021799862596588981514289162429605804360665710447859374849681435893620736256368651642579677674394930441908180110754967247422266920914276039199213254425446734399328961592567750553012063819167737077084164104771034049415093686101923815568487051045934771408640756663049279739190992549043381874433262761625687364765740708161589170033350889275729860800704841297455515863426509399116015735159136232069799452592244142551355605623334667876394636746375170017814997411454121284469885866320696373372278141163748634624139553234457580326407176977863876938729754040333846267279302195625675981965926672630203186696083706965821707163579124751728953909094017146236367574562658033502083245872809128489449565596634010603703448222799420830324567720792001445793007843977264599369662423574546333541211490593613593062081344348355466993563277376603905866466895858119560373863339586612882185010962576666714083653460276952083313521407999162240344785583293545759651601726094196651145562314577526036317198874006142551355285412564462316202985507623283510206313128801234782094549298382179970222871305442349917434740044689865522737142544961633048356623274239966322734659544755343511696106 200 29720 44064 30944 40544 58040 308028 57472 251564 53080 354601 5597
    (by decide +kernel) (by decide)
theorem wk8llllllll : SixW25P.Covered 29720 36892 57472 63537 31144 40128 30944 35744 29720 36892 :=
  SixW25P.covered_of_walk lbS hbas 66247027339611681776089983609846834985823273994511244435196337862685875490425657886562548866246233516289198183834346033740525049634785821741788396616419916750291436988178231350734926030942261860567758383913959296872442238091267916958970064834776261025144003202523974538140032447434924264903838384793111346518372816743505610936327564082020543685004430444844852669338207045047339305011042814855189019352937604384064264289883183589294089228536654411682637340315127677499004173118806270644571816274875284606533109661168920958247138997436278272900105673721986800960838 200 29720 36892 57472 63537 31144 40128 30944 35744 29720 36892 1877
    (by decide +kernel) (by decide)
theorem wk8lllllllrll : SixW25P.Covered 29720 36892 63537 69602 31144 35636 30944 33344 29720 36892 :=
  SixW25P.covered_of_walk lbS hbas 9930129421059928734697031609690826900128125733324894818502515449510409757357350192870100117368596647949829213163429302748868229564696409182351439622827062669693631231550356107651143917410009977576764614778635759607153624939022325762406183936180616127605614027784472811957026817038587067875728159174142000240093416147561897203225196549297098811302577189013229449907320447314055815446571928357449646741538011208811760361451554288492698383190191839817558613212350656209600851758270370408143088052615285838136197330148609117754941875657108778870958911753947290680481711035726 200 29720 36892 63537 69602 31144 35636 30944 33344 29720 36892 1902
    (by decide +kernel) (by decide)
theorem wk8lllllllrlrl : SixW25P.Covered 29720 36892 63537 69602 31144 35636 33344 35744 29720 33306 :=
  SixW25P.covered_of_walk lbS hbas 893273595952738309377764274893510208015761388881635988115281457167089805010126895925314596448585293235449820473216085751584162355379398649666509187566382297891712232209307007860380724430484217564804667097722581187900556189401060846299473402983962031311271977053816210969801951006026404816842653912508629933649915087573346423965800002869305828010373226490227902809611395585610555928816833367890944114340548647833121212522081342727558482 200 29720 36892 63537 69602 31144 35636 33344 35744 29720 33306 1462
    (by decide +kernel) (by decide)
theorem wk8lllllllrlrr : SixW25P.Covered 29720 36892 63537 69602 31144 35636 33344 35744 33306 36892 :=
  SixW25P.covered_of_walk lbS hbas 618293214984612151835696252885579028808456330296599250637667663372768317082459447610180984162448934977234723833360628150738182550055904312022011394736766074861496944849580058697966576329760788451297110342050058272836025408432546420926679858373203715023537101025846279479130278523124706409060227273343408333442291096513060184034876271906710157603394506030865184963485364691727344431787375147259604833525650270535279114378616745316162897230121628605187301857833749583034053386020446354447922507424301789325941706487063699804575380644404030091765390385525820192615045227798760462594360743680512543096879008114699607225808969764210226708022885751386811492815865278479823729625763092469959418167423465791617064967036432503778700282397185903054727873040650119037497969980352898091264522965386596169694893142675200111156549271309255910312367822547169477557705338929081804496697400805904655636090792155572763103207775321682555455662710467890136658804146246923531388820851351417064769459492461552771091474617804214408874998972910955085368309150284171473061654715222679194738923123578229866268518563732274983230780656265886735761675785866382760609781419544391215029897194552300550165096366497791929583014975962490673608517908978549100821313613863133502287135037206771169696968917168933802369697324045599936628416415594829142174318630176247266476891140556463308388901107308619560275085386417840432577200138235880825441038589980321754339401476642254864865899978725337104417625012368110644338557720193086506573852736445129813483581757765606933197672394330176436404771942092623548053787405473859485134400627489129617613515047959180543890206578181801455757596334114368701030328542989493317238308968358786253396213032516690993270563240501880674091208996235754485374432040592088103265610524506525553753442515963213897564016338454264763842272268288300388364510288928300367208947070350468827327580683437966549117271412923553507063547546679308353288310051752703837220535643397645943978 200 29720 36892 63537 69602 31144 35636 33344 35744 33306 36892 6532
    (by decide +kernel) (by decide)
theorem wk8lllllllrlr : SixW25P.Covered 29720 36892 63537 69602 31144 35636 33344 35744 29720 36892 :=
  SixW25P.covered_split4 33306 wk8lllllllrlrl wk8lllllllrlrr
theorem wk8lllllllrl : SixW25P.Covered 29720 36892 63537 69602 31144 35636 30944 35744 29720 36892 :=
  SixW25P.covered_split3 33344 wk8lllllllrll wk8lllllllrlr
theorem wk8lllllllrr : SixW25P.Covered 29720 36892 63537 69602 35636 40128 30944 35744 29720 36892 :=
  SixW25P.covered_of_walk lbS hbas 788651186948275496301950743490559417403101928147549151340355433731368024524951020034829982769211145176090732875321297231088347183595730523500702022172770650016256979454283498 200 29720 36892 63537 69602 35636 40128 30944 35744 29720 36892 587
    (by decide +kernel) (by decide)
theorem wk8lllllllr : SixW25P.Covered 29720 36892 63537 69602 31144 40128 30944 35744 29720 36892 :=
  SixW25P.covered_split2 35636 wk8lllllllrl wk8lllllllrr
theorem wk8lllllll : SixW25P.Covered 29720 36892 57472 69602 31144 40128 30944 35744 29720 36892 :=
  SixW25P.covered_split1 63537 wk8llllllll wk8lllllllr
theorem wk8llllllr : SixW25P.Covered 36892 44064 57472 69602 31144 40128 30944 35744 29720 36892 :=
  SixW25P.covered_of_walk lbS hbas 70416577509786252354082 200 36892 44064 57472 69602 31144 40128 30944 35744 29720 36892 92
    (by decide +kernel) (by decide)
theorem wk8llllll : SixW25P.Covered 29720 44064 57472 69602 31144 40128 30944 35744 29720 36892 :=
  SixW25P.covered_split0 36892 wk8lllllll wk8llllllr
theorem wk8lllllr : SixW25P.Covered 29720 44064 57472 69602 31144 40128 35744 40544 29720 36892 :=
  SixW25P.covered_of_walk lbS hbas 185164789162350192800806871860206488148147850203711059049993639366080112761346058695148261091747055214 200 29720 44064 57472 69602 31144 40128 35744 40544 29720 36892 342
    (by decide +kernel) (by decide)
theorem wk8lllll : SixW25P.Covered 29720 44064 57472 69602 31144 40128 30944 40544 29720 36892 :=
  SixW25P.covered_split3 35744 wk8llllll wk8lllllr
theorem wk8llllr : SixW25P.Covered 29720 44064 57472 69602 31144 40128 30944 40544 36892 44064 :=
  SixW25P.covered_of_walk lbS hbas 30061294 200 29720 44064 57472 69602 31144 40128 30944 40544 36892 44064 32
    (by decide +kernel) (by decide)
theorem wk8llll : SixW25P.Covered 29720 44064 57472 69602 31144 40128 30944 40544 29720 44064 :=
  SixW25P.covered_split4 36892 wk8lllll wk8llllr
theorem wk8lllr : SixW25P.Covered 29720 44064 69602 81733 31144 40128 30944 40544 29720 44064 :=
  SixW25P.covered_of_walk lbS hbas 35971847820786722432558690 200 29720 44064 69602 81733 31144 40128 30944 40544 29720 44064 92
    (by decide +kernel) (by decide)
theorem wk8lll : SixW25P.Covered 29720 44064 57472 81733 31144 40128 30944 40544 29720 44064 :=
  SixW25P.covered_split1 69602 wk8llll wk8lllr
theorem wk8llr : SixW25P.Covered 29720 44064 81733 105995 31144 40128 30944 40544 29720 44064 :=
  SixW25P.covered_of_walk lbS hbas 16385950280858608176086296696997605390848305852664576816745926160582976093934096445556131479103401159334145081183314662405552759059012628273739532674286511555658607318022404898816750767397411941698262404276526721966366333388480963575691895511662713104608319110680996118447596029667438895719272181640577366284716117868340755721833554474807581523400369165582764022482998533563508993951648528904703618503867694051458252086005369044144822445203530279870211918671576244315075943453356490319766043466944787927491924594747236414545845111722409488905556452216663134787853456117988192036419374923595788217663056488363521931196119170340474659593693076437935098440219100610075569361272732633753646623157652254139364521013555204841730368750732094296105395048386276404229718326373731003727968657648998848931966699918799201434733098412569396954893212613295291553827176412512312203291980406142030077990827593920411236520112444907580951565894977719430549121613485391855857528117120338240479367535863189538645046091019935947435750627525457633876694890654287035245398988884797693230570713678869730744293352840739643504753560682753868147671636018236792164530680739526745387332847218 200 29720 44064 81733 105995 31144 40128 30944 40544 29720 44064 3867
    (by decide +kernel) (by decide)
theorem wk8ll : SixW25P.Covered 29720 44064 57472 105995 31144 40128 30944 40544 29720 44064 :=
  SixW25P.covered_split1 81733 wk8lll wk8llr
theorem wk8lr : SixW25P.Covered 29720 44064 105995 154518 31144 40128 30944 40544 29720 44064 :=
  SixW25P.covered_of_walk lbS hbas 133508492827172704159477310586825341120332754527218990545851989960909283838518374 200 29720 44064 105995 154518 31144 40128 30944 40544 29720 44064 272
    (by decide +kernel) (by decide)
theorem wk8l : SixW25P.Covered 29720 44064 57472 154518 31144 40128 30944 40544 29720 44064 :=
  SixW25P.covered_split1 105995 wk8ll wk8lr
theorem wk8r : SixW25P.Covered 29720 44064 154518 251564 31144 40128 30944 40544 29720 44064 :=
  SixW25P.covered_of_walk lbS hbas 0 200 29720 44064 154518 251564 31144 40128 30944 40544 29720 44064 2
    (by decide +kernel) (by decide)
theorem wk8 : SixW25P.Covered 29720 44064 57472 251564 31144 40128 30944 40544 29720 44064 :=
  SixW25P.covered_split1 154518 wk8l wk8r
theorem wk9llllllllll : SixW25P.Covered 29720 36892 57472 63537 31144 40128 30944 40544 53080 71925 :=
  SixW25P.covered_of_walk lbS hbas 2975204315428694505235987545518665523786852342372118953327677481347071567999784787689883495441708467238099155368091951100410801240195672564953303079752741483198419777053305197958126150280710014515707147515343137512886415326014915641409190411198636315847927517624419054155190484374668086022018823225394942765517576505682055047153829898320638328055182527604571034924191320943552022912083483842576717916074747697830313540974120798182678097471335999079424929025875018326231772671225362540775684703323503007972737911595064031191278717968752311611990561083991943813802122426778209238843135551924600583524627733051214359998546542588623752123854578988602560724466608885666399995788047580312746488405396092808634050240359661815907098938581986489997501721878154385009203858597707100792575638133070332637860933514998680351353203854522784318919531351996073100109250186585413375780562282773990007003776582 200 29720 36892 57472 63537 31144 40128 30944 40544 53080 71925 2972
    (by decide +kernel) (by decide)
theorem wk9lllllllllrll : SixW25P.Covered 29720 36892 63537 69602 31144 40128 30944 35744 53080 62502 :=
  SixW25P.covered_of_walk lbS hbas 54173094961496999217576076242723745853704737547287843313014480109988200590047653245966110644709781157907675191929556874302841232224715474860344461647662969168024694204336911127554391624146 200 29720 36892 63537 69602 31144 40128 30944 35744 53080 62502 632
    (by decide +kernel) (by decide)
theorem wk9lllllllllrlrll : SixW25P.Covered 29720 36892 63537 69602 31144 35636 30944 33344 62502 71925 :=
  SixW25P.covered_of_walk lbS hbas 854321740125871553045686125154138961639763459385408600748768736040694568062800553315253719432867284865129275799734141633584566453513339275123712133780359093458668425435727224826393720857510459213852583497217161674 200 29720 36892 63537 69602 31144 35636 30944 33344 62502 71925 717
    (by decide +kernel) (by decide)
theorem wk9lllllllllrlrlrl : SixW25P.Covered 29720 36892 63537 69602 31144 33390 33344 35744 62502 71925 :=
  SixW25P.covered_of_walk lbS hbas 3274999191526147524461681674169852404289186790023229048866036223160779518318855481527859338738312516253493448169626047215209245183163140130496899818401780268100309663625444378954 200 29720 36892 63537 69602 31144 33390 33344 35744 62502 71925 597
    (by decide +kernel) (by decide)
theorem wk9lllllllllrlrlrrll : SixW25P.Covered 29720 33306 63537 69602 33390 35636 33344 35744 62502 67213 :=
  SixW25P.covered_of_walk lbS hbas 11171937577193706108710082141106078218208171676783605922641073321820439248953562303011762780660676238986193437158204688142882824307240134195288827028389502229029817235862364139189728549822776904500508319650598966306986628126057883617566550166877856165841402313616140652532552395265222583699199276502517395504530381814406617406166207234313868201918325711006856401328678122020553283170617876629259814018168925795725133485263355599787208802922988566727565741903898153561132412944230630867715914989194578060542665639602999678636890247723951338299296340609417772017443507584453823661887455720364721832875029228473026355484578667491272007694107000815088568458072569964548306399914762424942070758015999709787161592085130168403882405036978881037960473070948405007431295191300995781738920289866371046220662765254518290233445570 200 29720 33306 63537 69602 33390 35636 33344 35744 62502 67213 2717
    (by decide +kernel) (by decide)
theorem wk9lllllllllrlrlrrlrlll : SixW25P.Covered 33306 36892 63537 65053 33390 35636 33344 35744 62502 64857 :=
  SixW25P.covered_of_walk lbS hbas 1241797031044329888147375477923438851725377701660489888017845570665178069376123751422217034619594288785002807616647340466192983825466334582722839493657895124712840205094529469502278003576366698239002591441156448164792380185176281562538867317020631941244528117233625849148456378017562437377304350977903634545146578689647547056304822365221700842278522924970162403303021549066749334271826144120253367482014357450169932331146257664612423328182648555039574652062960767517174400687932973714097431399550642711776572944213751568873735979764705373075637125521874013480223276077510953508457325932479973475403864400860000185586225320395604693253515290343528610552195133859707544879471421464053170421905015653388523687384860087492454605123928676494690204306267583677970795287196499207935907888358635118317496315093681386250630079802427836063976147112697585952133782358717410465618882691048914078274033321828072818398161943758224125831803650671783819876233245877300719835808001240499658449912336174339004020028361877487258961478411701786686787752549963458079857405101919819201942725194851758872478333197681309558394487019191556281072323260236718969485277743255891848526634843168933147251464001162577504793356274335934768167439808526489665072825278511051219029646310472611070861179351976190796041968717107836987087442784074730820912579453832092963268262450269061265826950381159583476482510640520657473537448037303486408588381861520002221843420669424130252524607314415902954810715856724324466285637876351433856671982835400212803462568149831980105697798881086970425603516585382587908596644695998952322045921211027078118220682169945279460323917980989733754235163251101016726456230243607657359431865927072271217403856242994621903004487725247996252854126309103281475800935992244235435876696717669030088830687070263631987097353248835647893127175945900905272326340078734519629396555548626991941908394293576800121876570493139739059732784153731099440139325228882168840413883834294790586298146 200 33306 36892 63537 65053 33390 35636 33344 35744 62502 64857 6542
    (by decide +kernel) (by decide)
theorem wk9lllllllllrlrlrrlrllrll : SixW25P.Covered 33306 35099 63537 65053 33390 35636 33344 35744 64857 66035 :=
  SixW25P.covered_of_walk lbS hbas 0 200 33306 35099 63537 65053 33390 35636 33344 35744 64857 66035 2
    (by decide +kernel) (by decide)
theorem wk9lllllllllrlrlrrlrllrlrlll : SixW25P.Covered 33306 35099 63537 65053 33390 34513 33344 33944 66035 67213 :=
  SixW25P.covered_of_walk lbS hbas 77553093264034149078573360505185659397266098088387437133131899075898239237622208787090896263480528450207105509346506896224616115580252729890074252181936730233043084491482404032715482554171535966398024393599147981285988180552091464778439988395964064199748770159111539210417710946982689376442023766791535917336415761446866027263129222260348863773056419601557635823493963275804687743129481236106580800688045076408747012548178207983985219240679875739116541390827418459264278246802879021059602141680379122988339271833607673998309521196507300221563529396515379861444633695813466587678083136911941010663640193609338592276432373210776180550519143912101909410821519753969469222887632423602872962290843589598908408493094599073142170419215779580877647913329342578505701030360719952712716738946520478496008857123442482295171039731738830693406746665638 200 33306 35099 63537 65053 33390 34513 33344 33944 66035 67213 2792
    (by decide +kernel) (by decide)
theorem wk9lllllllllrlrlrrlrllrlrllr : SixW25P.Covered 33306 35099 63537 65053 33390 34513 33944 34544 66035 67213 :=
  SixW25P.covered_of_walk lbS hbas 635609619737868739953093024337947174127610648192861575526668385879208111317027997395269929391809938788544973852924945085409228724825382399589208120184768411558821337811176436640099546495141892923782785311441014064223930813892753346427932590870955109246198856588289230472523136480981539694309698170647811517232740214652358859334729710576345359599894054747699431119086027812526017471131228908235454319275955501074882951092012617231053404011717658170644558142508104370935045404392720381866505383831845400270404990839219224999343138197989050223503642626237083912237886633311218029071514047258350570005879629073189604195121085876780116289344976470525271030504073154279395949014783536184230875440923501896217472782990473577459893828605072304138541599337756482867667897368183351355475581620394349678240729442665763160913581831188085233465905308473496649192694914910800948548530409974123056716958491422532855229349185042957765702957003915672677389333189444348357902449659356032734934854847644636033110007992746587678456430948597598079456535645410572918153402556504665326202305124077884833556212503888988190057279180232367477995977606630634015612422776168783954108218767604576304374100880723943453163104929673312405860754884808641187086175136821251281317379194987193552108739343898905822947855032986627381886435486254044534808360587413241209834524781455600118955728074721086348079304450802492561842398435718400462210636100138755556473488447853575770754998923571951641154480346078637000086748553894 200 33306 35099 63537 65053 33390 34513 33944 34544 66035 67213 4947
    (by decide +kernel) (by decide)
theorem wk9lllllllllrlrlrrlrllrlrll : SixW25P.Covered 33306 35099 63537 65053 33390 34513 33344 34544 66035 67213 :=
  SixW25P.covered_split3 33944 wk9lllllllllrlrlrrlrllrlrlll wk9lllllllllrlrlrrlrllrlrllr
theorem wk9lllllllllrlrlrrlrllrlrlr : SixW25P.Covered 33306 35099 63537 65053 34513 35636 33344 34544 66035 67213 :=
  SixW25P.covered_of_walk lbS hbas 261213377883823240597654790487701303634167580752305893331718857691058205546111684728653016588015042402957917096636652097877543657989599752936652802801653682258860713157347786246111506428473658667265832291076109900934925079066087441257079023336383145505054747104155174921191616805682572986865258807652966861155744012039921827340995578227812105055401052323813800771282450188216083484597018613702952586987237894055658767456219772675524488070421111351623320387565723113582378624131694 200 33306 35099 63537 65053 34513 35636 33344 34544 66035 67213 1597
    (by decide +kernel) (by decide)
theorem wk9lllllllllrlrlrrlrllrlrl : SixW25P.Covered 33306 35099 63537 65053 33390 35636 33344 34544 66035 67213 :=
  SixW25P.covered_split2 34513 wk9lllllllllrlrlrrlrllrlrll wk9lllllllllrlrlrrlrllrlrlr
theorem wk9lllllllllrlrlrrlrllrlrr : SixW25P.Covered 33306 35099 63537 65053 33390 35636 34544 35744 66035 67213 :=
  SixW25P.covered_of_walk lbS hbas 879419509265619060184898820620753366949899568430109380715636528980610548735699013300256639769392751773321483106933823666864310346756426587660048366115401890169223848262394004121777230329262810858 200 33306 35099 63537 65053 33390 35636 34544 35744 66035 67213 652
    (by decide +kernel) (by decide)
theorem wk9lllllllllrlrlrrlrllrlr : SixW25P.Covered 33306 35099 63537 65053 33390 35636 33344 35744 66035 67213 :=
  SixW25P.covered_split3 34544 wk9lllllllllrlrlrrlrllrlrl wk9lllllllllrlrlrrlrllrlrr
theorem wk9lllllllllrlrlrrlrllrl : SixW25P.Covered 33306 35099 63537 65053 33390 35636 33344 35744 64857 67213 :=
  SixW25P.covered_split4 66035 wk9lllllllllrlrlrrlrllrll wk9lllllllllrlrlrrlrllrlr
theorem wk9lllllllllrlrlrrlrllrr : SixW25P.Covered 35099 36892 63537 65053 33390 35636 33344 35744 64857 67213 :=
  SixW25P.covered_of_walk lbS hbas 677207220803236268902037937742138739990706058808141336739384164674231877910987580016320818794059760934301707278264217769338659338833882826182638871353366119678452924453437476236744322243460747262839276043987645230766807718940700975325853894857289281396508235722168553841669769601787148365754724639279089822313459725584883273580089416066347676881465352853341377003900146492802928447794096866918954160822402388060661506734 200 35099 36892 63537 65053 33390 35636 33344 35744 64857 67213 1402
    (by decide +kernel) (by decide)
theorem wk9lllllllllrlrlrrlrllr : SixW25P.Covered 33306 36892 63537 65053 33390 35636 33344 35744 64857 67213 :=
  SixW25P.covered_split0 35099 wk9lllllllllrlrlrrlrllrl wk9lllllllllrlrlrrlrllrr
theorem wk9lllllllllrlrlrrlrll : SixW25P.Covered 33306 36892 63537 65053 33390 35636 33344 35744 62502 67213 :=
  SixW25P.covered_split4 64857 wk9lllllllllrlrlrrlrlll wk9lllllllllrlrlrrlrllr
theorem wk9lllllllllrlrlrrlrlrll : SixW25P.Covered 33306 35099 65053 66569 33390 35636 33344 35744 62502 64857 :=
  SixW25P.covered_of_walk lbS hbas 151029024995340055379058172907734494393441806587881134470867125012714686539922585251647730423648283002821501190854971592613176731562935322481325220270368408881575794820916169492816076690087738415138956963141557743122767330369268632364361318230785324564597661086295996660349798345312178765982151829626193989581498005041588608255582696856321289471403141441542701244292681916264118614878652534459062864045192568397964908517612056988312114901068875725510584203623339692196532928310850260069208368272836754864464528098737291001397255483264940712466197462997062678377789793896154510723669711420105322552131788097205912004586112217266288933522655192421394549892291934826935728099331970212211405762586757244595118840488485704855609422362148886398956401332356735611226263429897656599025605283903875368540964559182358122703851659865044174580735242244041394383435686880817865049744566967866349667109011777448944069955353700816496702666344589217391796123214944924546814152533837105190104561875809744604549660338650853386150768757636776790198325100308573312511691811367668903421306571119509006766385268529089329076362717612292337943259030337316753036540573899674221150179275255020372884936595749474422432854411952169032648066353384182363448963824239765648926344545436783962245093897277761176941601053236394256384446737599376929618312763124610390884367046757786669335020912298431068491707474188241888485627000412691698768302487690248196658164410684074242187365309917813504004356693509115596835441182645630870781566224300983646163017771861249936881419722967617683910161428963434420455641892544211267246 200 33306 35099 65053 66569 33390 35636 33344 35744 62502 64857 5272
    (by decide +kernel) (by decide)
theorem wk9lllllllllrlrlrrlrlrlr : SixW25P.Covered 33306 35099 65053 66569 33390 35636 33344 35744 64857 67213 :=
  SixW25P.covered_of_walk lbS hbas 111719897142176220059698387610590255251100063289913889049046584118174778298751362232381580909968275030843990590792443384294085106378621504735208216168468243083284001931539470507734464027521129185328463616509892203689187595720059767698493392977581258978461560746501713604829948805645244765352375007991390074850343570644645374436113477348678551045252968672587687407168624760646092925667811116469978098925573301440096543205183599400007111883615297764456071157633082053145753123365899335840284521583978323082571458568547067864806601213560725597246588720728707200928337276734812532041225952210027841495573601451205842560523227294241952556273472440362127740315979363690914017409607830063094832839399961606298153882025036551662901125583779845360170992833527138283174313573479228567216983476898360711826087507805035872620640118263989363956480536605378097471800700919629537699583970319284847216074747020566893184751844342185425538196046526409111055808655447040585031183162737845156365455085658904896768573109644031114526971404329819105199767271280445933050929924903019541564926859741904219910815986158462742190 200 33306 35099 65053 66569 33390 35636 33344 35744 64857 67213 3662
    (by decide +kernel) (by decide)
theorem wk9lllllllllrlrlrrlrlrl : SixW25P.Covered 33306 35099 65053 66569 33390 35636 33344 35744 62502 67213 :=
  SixW25P.covered_split4 64857 wk9lllllllllrlrlrrlrlrll wk9lllllllllrlrlrrlrlrlr
theorem wk9lllllllllrlrlrrlrlrr : SixW25P.Covered 35099 36892 65053 66569 33390 35636 33344 35744 62502 67213 :=
  SixW25P.covered_of_walk lbS hbas 10291442344759640598474579013477325846420393621992544289342690175341784301200924820517767229700477778414553597915015358564302732272924111949110309391943229150196569159388293950002 200 35099 36892 65053 66569 33390 35636 33344 35744 62502 67213 597
    (by decide +kernel) (by decide)
theorem wk9lllllllllrlrlrrlrlr : SixW25P.Covered 33306 36892 65053 66569 33390 35636 33344 35744 62502 67213 :=
  SixW25P.covered_split0 35099 wk9lllllllllrlrlrrlrlrl wk9lllllllllrlrlrrlrlrr
theorem wk9lllllllllrlrlrrlrl : SixW25P.Covered 33306 36892 63537 66569 33390 35636 33344 35744 62502 67213 :=
  SixW25P.covered_split1 65053 wk9lllllllllrlrlrrlrll wk9lllllllllrlrlrrlrlr
theorem wk9lllllllllrlrlrrlrr : SixW25P.Covered 33306 36892 66569 69602 33390 35636 33344 35744 62502 67213 :=
  SixW25P.covered_of_walk lbS hbas 10017130568989665018305442369741783809062329091925458143916030458174847983690829246015667255044082652538797594611010849443187801172873761218725776930121119773405734 200 33306 36892 66569 69602 33390 35636 33344 35744 62502 67213 547
    (by decide +kernel) (by decide)
theorem wk9lllllllllrlrlrrlr : SixW25P.Covered 33306 36892 63537 69602 33390 35636 33344 35744 62502 67213 :=
  SixW25P.covered_split1 66569 wk9lllllllllrlrlrrlrl wk9lllllllllrlrlrrlrr
theorem wk9lllllllllrlrlrrl : SixW25P.Covered 29720 36892 63537 69602 33390 35636 33344 35744 62502 67213 :=
  SixW25P.covered_split0 33306 wk9lllllllllrlrlrrll wk9lllllllllrlrlrrlr
theorem wk9lllllllllrlrlrrr : SixW25P.Covered 29720 36892 63537 69602 33390 35636 33344 35744 67213 71925 :=
  SixW25P.covered_of_walk lbS hbas 57527972838731647247798866576891863176458308192184343614020040347625192257237647138232105981151319669639856558172185548510704864573612479248364954708509204353949091303304509675187864915875201951526500486254203257394 200 29720 36892 63537 69602 33390 35636 33344 35744 67213 71925 722
    (by decide +kernel) (by decide)
theorem wk9lllllllllrlrlrr : SixW25P.Covered 29720 36892 63537 69602 33390 35636 33344 35744 62502 71925 :=
  SixW25P.covered_split4 67213 wk9lllllllllrlrlrrl wk9lllllllllrlrlrrr
theorem wk9lllllllllrlrlr : SixW25P.Covered 29720 36892 63537 69602 31144 35636 33344 35744 62502 71925 :=
  SixW25P.covered_split2 33390 wk9lllllllllrlrlrl wk9lllllllllrlrlrr
theorem wk9lllllllllrlrl : SixW25P.Covered 29720 36892 63537 69602 31144 35636 30944 35744 62502 71925 :=
  SixW25P.covered_split3 33344 wk9lllllllllrlrll wk9lllllllllrlrlr
theorem wk9lllllllllrlrr : SixW25P.Covered 29720 36892 63537 69602 35636 40128 30944 35744 62502 71925 :=
  SixW25P.covered_of_walk lbS hbas 1616900629703263190771585197731814691610159772709708262187006204518378877716990058484113994547244610562539500438887947705254378459083871435474978564479517331811103801765571748239944382008094799876820544764946190838923632267469896574182317402146564601215675424107242 200 29720 36892 63537 69602 35636 40128 30944 35744 62502 71925 887
    (by decide +kernel) (by decide)
theorem wk9lllllllllrlr : SixW25P.Covered 29720 36892 63537 69602 31144 40128 30944 35744 62502 71925 :=
  SixW25P.covered_split2 35636 wk9lllllllllrlrl wk9lllllllllrlrr
theorem wk9lllllllllrl : SixW25P.Covered 29720 36892 63537 69602 31144 40128 30944 35744 53080 71925 :=
  SixW25P.covered_split4 62502 wk9lllllllllrll wk9lllllllllrlr
theorem wk9lllllllllrr : SixW25P.Covered 29720 36892 63537 69602 31144 40128 35744 40544 53080 71925 :=
  SixW25P.covered_of_walk lbS hbas 136323367438657041791012134841104316197674898803718666705040777491484943665348322961229391173054133167171495423306090582833620106208073951078812316130622491447705037989934647243113530214127031280072066171377032330454839086 200 29720 36892 63537 69602 31144 40128 35744 40544 53080 71925 747
    (by decide +kernel) (by decide)
theorem wk9lllllllllr : SixW25P.Covered 29720 36892 63537 69602 31144 40128 30944 40544 53080 71925 :=
  SixW25P.covered_split3 35744 wk9lllllllllrl wk9lllllllllrr
theorem wk9lllllllll : SixW25P.Covered 29720 36892 57472 69602 31144 40128 30944 40544 53080 71925 :=
  SixW25P.covered_split1 63537 wk9llllllllll wk9lllllllllr
theorem wk9llllllllr : SixW25P.Covered 36892 44064 57472 69602 31144 40128 30944 40544 53080 71925 :=
  SixW25P.covered_of_walk lbS hbas 31074062388327950335164521641971714221595198513762 200 36892 44064 57472 69602 31144 40128 30944 40544 53080 71925 172
    (by decide +kernel) (by decide)
theorem wk9llllllll : SixW25P.Covered 29720 44064 57472 69602 31144 40128 30944 40544 53080 71925 :=
  SixW25P.covered_split0 36892 wk9lllllllll wk9llllllllr
theorem wk9lllllllr : SixW25P.Covered 29720 44064 69602 81733 31144 40128 30944 40544 53080 71925 :=
  SixW25P.covered_of_walk lbS hbas 65073886152822302306 200 29720 44064 69602 81733 31144 40128 30944 40544 53080 71925 72
    (by decide +kernel) (by decide)
theorem wk9lllllll : SixW25P.Covered 29720 44064 57472 81733 31144 40128 30944 40544 53080 71925 :=
  SixW25P.covered_split1 69602 wk9llllllll wk9lllllllr
theorem wk9llllllr : SixW25P.Covered 29720 44064 57472 81733 31144 40128 30944 40544 71925 90770 :=
  SixW25P.covered_of_walk lbS hbas 495901818283558 200 29720 44064 57472 81733 31144 40128 30944 40544 71925 90770 52
    (by decide +kernel) (by decide)
theorem wk9llllll : SixW25P.Covered 29720 44064 57472 81733 31144 40128 30944 40544 53080 90770 :=
  SixW25P.covered_split4 71925 wk9lllllll wk9llllllr
theorem wk9lllllr : SixW25P.Covered 29720 44064 57472 81733 31144 40128 30944 40544 90770 128460 :=
  SixW25P.covered_of_walk lbS hbas 139095706595578113263131388591405432212323486777519631023703355410372652876482034428022701434270836199466775700698677746265882479151138174690709278054994779231777649861209656449109736287772649807207544197333549265484266291960388701118857423861772034579672110779726233051766015452218230916504098193249134809967462288109476816785315300796549755963255349751481641074492526285239445625831833919151547228023671480320512612810188121190099263102638319105406637494924447007575992973356916364595845708965811720892192501739835530962219979361309969145030270840300200714519115337344524491724402993422517676186764218479462732188073484014443147946759799940757377130431053250169706257585713414202161413351774301804834220270162961043339705704121700294040231441240884922060573528225597208414435646571555250204459634123062210499356008090369328785871849018147143819875160929937594021123689857740158973988155499420698332112173077309291610541130922405206995656631142726785566408363503706633996779753605212118830221545098196827293101396371918035945551541722033342963677348604220253944269969739698107987839022406244010445954645831781578132924700841546628385708155152060385052101102599272569491609163144088590078351648407722041721019526749821695049543144739447954589308207348006851132432610835251128629606076979974477284862245634221617969826562599032072420376493622058983007198986353144435205571777886603595364031033535927661753248766743566014473697323228201522429055785234637604058974472693900131154380394422665298139701895205679258959207882164880717451293541636382358577253512005789467366740090436460687428941948798410323974008958684184743820710137353428691472895708376139222806648708537954029905661592922361160677503562240233898738222698894503581859297133912120778344709814863676394853336576148062642458593560988527076160472818294838586088824138064137855451244286669367524984286671571232792844790547502013849547850912515031838827563998539357861696091926411558887629334627501445672225107917906772624547722524178268560658134367539615981818373670 200 29720 44064 57472 81733 31144 40128 30944 40544 90770 128460 6722
    (by decide +kernel) (by decide)
theorem wk9lllll : SixW25P.Covered 29720 44064 57472 81733 31144 40128 30944 40544 53080 128460 :=
  SixW25P.covered_split4 90770 wk9llllll wk9lllllr
theorem wk9llllr : SixW25P.Covered 29720 44064 57472 81733 31144 40128 30944 40544 128460 203840 :=
  SixW25P.covered_of_walk lbS hbas 3448990864292612609450494818743902637776738843395121958 200 29720 44064 57472 81733 31144 40128 30944 40544 128460 203840 187
    (by decide +kernel) (by decide)
theorem wk9llll : SixW25P.Covered 29720 44064 57472 81733 31144 40128 30944 40544 53080 203840 :=
  SixW25P.covered_split4 128460 wk9lllll wk9llllr
theorem wk9lllr : SixW25P.Covered 29720 44064 81733 105995 31144 40128 30944 40544 53080 203840 :=
  SixW25P.covered_of_walk lbS hbas 855743482030286237886648287312153616060236322559141071630072045603529876835087817421610848573576802775369303990735307406695416148882782340622902642000607051499851183929148028328540200840484989568823474290484947802069675156889437074786183345484653370898725705209115581475273588831337621083505885346611764100667556431582942050938890091716022089202944010524402330298390610665628872114998544118541118692810665867372334203778902852658039211641579059773389576454511245023011764008418934207474943161653237735546688658408435765839828024232664158062231302227520615025078249046919358699871093339227543406284011215098302317535557414411203378 200 29720 44064 81733 105995 31144 40128 30944 40544 53080 203840 2097
    (by decide +kernel) (by decide)
theorem wk9lll : SixW25P.Covered 29720 44064 57472 105995 31144 40128 30944 40544 53080 203840 :=
  SixW25P.covered_split1 81733 wk9llll wk9lllr
theorem wk9llr : SixW25P.Covered 29720 44064 105995 154518 31144 40128 30944 40544 53080 203840 :=
  SixW25P.covered_of_walk lbS hbas 1884165968311322309426 200 29720 44064 105995 154518 31144 40128 30944 40544 53080 203840 77
    (by decide +kernel) (by decide)
theorem wk9ll : SixW25P.Covered 29720 44064 57472 154518 31144 40128 30944 40544 53080 203840 :=
  SixW25P.covered_split1 105995 wk9lll wk9llr
theorem wk9lr : SixW25P.Covered 29720 44064 57472 154518 31144 40128 30944 40544 203840 354601 :=
  SixW25P.covered_of_walk lbS hbas 0 200 29720 44064 57472 154518 31144 40128 30944 40544 203840 354601 2
    (by decide +kernel) (by decide)
theorem wk9l : SixW25P.Covered 29720 44064 57472 154518 31144 40128 30944 40544 53080 354601 :=
  SixW25P.covered_split4 203840 wk9ll wk9lr
theorem wk9r : SixW25P.Covered 29720 44064 154518 251564 31144 40128 30944 40544 53080 354601 :=
  SixW25P.covered_of_walk lbS hbas 0 200 29720 44064 154518 251564 31144 40128 30944 40544 53080 354601 2
    (by decide +kernel) (by decide)
theorem wk9 : SixW25P.Covered 29720 44064 57472 251564 31144 40128 30944 40544 53080 354601 :=
  SixW25P.covered_split1 154518 wk9l wk9r
theorem wk10lllllllllll : SixW25P.Covered 29720 36892 57472 63537 31144 40128 57472 69602 29720 36892 :=
  SixW25P.covered_of_walk lbS hbas 179344951982844581565181258316674771952688986644472088098008362026659640792553117971414082854749601202437185510192595028926898179117736524663658937359748822389732608917843145067371543997454709871463673314809134474965811217740725958326024786376403203052636614544979550759091221659801182077631023220067712119283848891766180587532082114097415580998978945495273727174931016775132421574 200 29720 36892 57472 63537 31144 40128 57472 69602 29720 36892 1272
    (by decide +kernel) (by decide)
theorem wk10llllllllllrl : SixW25P.Covered 29720 36892 63537 69602 31144 40128 57472 63537 29720 36892 :=
  SixW25P.covered_of_walk lbS hbas 1848144353421875245900890498801912829224129441174712885383461239561160246244588882808244352115630399784208339614495015820220400777176697497956484074912962537880014406430651291162256493361990696747307222181826750313376800507290193535916880433734681430379566688754329141382400552335735784399165094672491698382462996886178323674948044527096331050455896869875425475587566844503649228486050637786719374266360878274538654164057121318384596874503024247768958406192090752421526515633293011406 200 29720 36892 63537 69602 31144 40128 57472 63537 29720 36892 1617
    (by decide +kernel) (by decide)
theorem wk10llllllllllrrll : SixW25P.Covered 29720 36892 63537 69602 31144 33390 63537 69602 29720 36892 :=
  SixW25P.covered_of_walk lbS hbas 8628231013236683981694420991705200101547436656326420727740667386979715402 200 29720 36892 63537 69602 31144 33390 63537 69602 29720 36892 252
    (by decide +kernel) (by decide)
theorem wk10llllllllllrrlrl : SixW25P.Covered 29720 33306 63537 69602 33390 35636 63537 69602 29720 36892 :=
  SixW25P.covered_of_walk lbS hbas 3188471181233186457992651267536659692219401959574747758511938193394710159557913327552941127221957591927735543584403049203347326216888977971989022915426652379651346502566592164144557232678534737237095330221505407616485569385523224657632749936510259408575363397880286964287657641019969589730178625343028356796613983428351989564063515214040755636432444105725180559397779613173830017903153103821666974510887387791214899466753645212554646880048045273909202807387967175746882234827530989990602152205991891773421511594664857628476082662168594456231506236608244268459549491306613494330926913731490556253906340030369198622716353835910221819586114 200 29720 33306 63537 69602 33390 35636 63537 69602 29720 36892 2122
    (by decide +kernel) (by decide)
theorem wk10llllllllllrrlrrl : SixW25P.Covered 33306 36892 63537 69602 33390 35636 63537 69602 29720 33306 :=
  SixW25P.covered_of_walk lbS hbas 178164012269735539577788658053730904566801657307087954 200 33306 36892 63537 69602 33390 35636 63537 69602 29720 33306 192
    (by decide +kernel) (by decide)
theorem wk10llllllllllrrlrrrlll : SixW25P.Covered 33306 36892 63537 65053 33390 35636 63537 66569 33306 36892 :=
  SixW25P.covered_of_walk lbS hbas 1472972689955996559491257919232993086951547532120284714078616513314873129057524638527790862649296586142636436288401698212022022878692547666948608842483232463305755374641482889759587383570006313467062201861664664745132642924925655053476399566952410945375803767778722563887317294423066502210334200300044818379257645102052518944463062989159475662092639870327851597594904837010557994356676407262111240137167223414559979170200715338666310134736621392940204502484598360509839709504076119521982585389762288246051934873064469597365558429197601487054671673641757020629753994533012473857852323828868635076519544132721323921479951530567123180525358405232244304827689230668647054561241124421203594833084327791021928741879222017671607333235084457265651258605472319013760119419223870399346910200792770122330888120662128982735663491747235812143503856244030820696194317796529410992811350507349647792417869589907112164914051967169517837781839638796271160912995397487315617255441298231850536405722659149078982828705941591304981753936339061286487786612106639176570467518341464116251146849386693167465833645875378979705346253955818438909867389236001443828270 200 33306 36892 63537 65053 33390 35636 63537 66569 33306 36892 3782
    (by decide +kernel) (by decide)
theorem wk10llllllllllrrlrrrllr : SixW25P.Covered 33306 36892 65053 66569 33390 35636 63537 66569 33306 36892 :=
  SixW25P.covered_of_walk lbS hbas 204547589160469017876428786400151219579238850310585749801514358648286492767005498738182287527339565003666930966201090174348661737426564030309814524096036096276797152634052976133879760935545798908850783495937839777411618908678480798860817827045328365438113553626725098303872891809967692954023809648553496724152783874916022448332917108904231135468806353717063440560427358742671734272227359952516760580489310906838783762694402567314334093033809642512936575395097567890737569224278523808417447766874132426472690318043388932757151914159242824009845323346644038382894860404360982648713715117916600119117700063181511131433198152998915691960893041883409777584747213575424472861490995372114287867524389630974278117950081958618283559752912524782208264189510617729878886337556984185412274362391315429334807528886368061304458940411558003315328257083219954195319178610641108427496723857976035741359454930917990711344822675199578708418496660416195074889841823537519130282809652796649991988111242023609618288078413426575601881656934491877741803687543960558763834480707820080669470776012167441672201185844155974051022784159047011984082215422190559293185443881721439503632925320502808906339015497706400711805107979211046166608051406156778634286633572272471371339340178039922393553804723845794098745722448127012928783766896758246190805929020959886022874704308094653721745687897727370051682046377656566769269288951583888752489694537329139953631135733473888856170007178532085150594632317171672603411844248305504924403644974711143061482866222092115084909439397962049590522735564263610811778200811246133603461692467600309302864898111947738438793646754674474955851670324635725774573485326063666558946143272925128920980888328562877126771664664437087548337386947479904792746911920448633224615436258906837001155294565554333168367204159402891999683747856329991653891022482566239435244963779547209340177231336844687405778049729028902802177779331810 200 33306 36892 65053 66569 33390 35636 63537 66569 33306 36892 6382
    (by decide +kernel) (by decide)
theorem wk10llllllllllrrlrrrll : SixW25P.Covered 33306 36892 63537 66569 33390 35636 63537 66569 33306 36892 :=
  SixW25P.covered_split1 65053 wk10llllllllllrrlrrrlll wk10llllllllllrrlrrrllr
theorem wk10llllllllllrrlrrrlr : SixW25P.Covered 33306 36892 63537 66569 33390 35636 66569 69602 33306 36892 :=
  SixW25P.covered_of_walk lbS hbas 220800784051095636823611605481329700159794222205767862174403845988928744715919302240427218775669301443988528852690911116729019984910041441749521975899525248766320603696542554739539242963353147078438722818655101022504131963254081352753240772237735961093182700037401564126387442758847477516397767192029231034531054210370577369017737602727012484629809211182 200 33306 36892 63537 66569 33390 35636 66569 69602 33306 36892 1182
    (by decide +kernel) (by decide)
theorem wk10llllllllllrrlrrrl : SixW25P.Covered 33306 36892 63537 66569 33390 35636 63537 69602 33306 36892 :=
  SixW25P.covered_split3 66569 wk10llllllllllrrlrrrll wk10llllllllllrrlrrrlr
theorem wk10llllllllllrrlrrrr : SixW25P.Covered 33306 36892 66569 69602 33390 35636 63537 69602 33306 36892 :=
  SixW25P.covered_of_walk lbS hbas 2356440767596953674236483813205597846144156740776080527152424455152251735962012583108610337349627231378901356654798594153268740281415140102120990449953342121204264995347265560700365858192196364237294078313307533213045533421318121715108112375152441033894253607102563380279154015213121546672956713776903723959052047003097227463077331034977466088898459191890684567007927637580915081958372473633583382621538911027738442916462 200 33306 36892 66569 69602 33390 35636 63537 69602 33306 36892 1407
    (by decide +kernel) (by decide)
theorem wk10llllllllllrrlrrr : SixW25P.Covered 33306 36892 63537 69602 33390 35636 63537 69602 33306 36892 :=
  SixW25P.covered_split1 66569 wk10llllllllllrrlrrrl wk10llllllllllrrlrrrr
theorem wk10llllllllllrrlrr : SixW25P.Covered 33306 36892 63537 69602 33390 35636 63537 69602 29720 36892 :=
  SixW25P.covered_split4 33306 wk10llllllllllrrlrrl wk10llllllllllrrlrrr
theorem wk10llllllllllrrlr : SixW25P.Covered 29720 36892 63537 69602 33390 35636 63537 69602 29720 36892 :=
  SixW25P.covered_split0 33306 wk10llllllllllrrlrl wk10llllllllllrrlrr
theorem wk10llllllllllrrl : SixW25P.Covered 29720 36892 63537 69602 31144 35636 63537 69602 29720 36892 :=
  SixW25P.covered_split2 33390 wk10llllllllllrrll wk10llllllllllrrlr
theorem wk10llllllllllrrr : SixW25P.Covered 29720 36892 63537 69602 35636 40128 63537 69602 29720 36892 :=
  SixW25P.covered_of_walk lbS hbas 3910636611829895942633667862973245677861707887908632255673013004060039640696036132088874766730762537578858258456207549816927889590071442159440851094187604289721795890157297413249987565641232404129802706354814707651316956657356060896914944360535754590056285875049371157673953435015866584536953487998738099944677064100480531888297589600481050469184555027284522 200 29720 36892 63537 69602 35636 40128 63537 69602 29720 36892 1197
    (by decide +kernel) (by decide)
theorem wk10llllllllllrr : SixW25P.Covered 29720 36892 63537 69602 31144 40128 63537 69602 29720 36892 :=
  SixW25P.covered_split2 35636 wk10llllllllllrrl wk10llllllllllrrr
theorem wk10llllllllllr : SixW25P.Covered 29720 36892 63537 69602 31144 40128 57472 69602 29720 36892 :=
  SixW25P.covered_split3 63537 wk10llllllllllrl wk10llllllllllrr
theorem wk10llllllllll : SixW25P.Covered 29720 36892 57472 69602 31144 40128 57472 69602 29720 36892 :=
  SixW25P.covered_split1 63537 wk10lllllllllll wk10llllllllllr
theorem wk10lllllllllr : SixW25P.Covered 29720 36892 57472 69602 31144 40128 57472 69602 36892 44064 :=
  SixW25P.covered_of_walk lbS hbas 24444678347096298676842290 200 29720 36892 57472 69602 31144 40128 57472 69602 36892 44064 92
    (by decide +kernel) (by decide)
theorem wk10lllllllll : SixW25P.Covered 29720 36892 57472 69602 31144 40128 57472 69602 29720 44064 :=
  SixW25P.covered_split4 36892 wk10llllllllll wk10lllllllllr
theorem wk10llllllllr : SixW25P.Covered 36892 44064 57472 69602 31144 40128 57472 69602 29720 44064 :=
  SixW25P.covered_of_walk lbS hbas 65284095101109226886804197749282 200 36892 44064 57472 69602 31144 40128 57472 69602 29720 44064 112
    (by decide +kernel) (by decide)
theorem wk10llllllll : SixW25P.Covered 29720 44064 57472 69602 31144 40128 57472 69602 29720 44064 :=
  SixW25P.covered_split0 36892 wk10lllllllll wk10llllllllr
theorem wk10lllllllr : SixW25P.Covered 29720 44064 57472 69602 31144 40128 69602 81733 29720 44064 :=
  SixW25P.covered_of_walk lbS hbas 854512351194926 200 29720 44064 57472 69602 31144 40128 69602 81733 29720 44064 57
    (by decide +kernel) (by decide)
theorem wk10lllllll : SixW25P.Covered 29720 44064 57472 69602 31144 40128 57472 81733 29720 44064 :=
  SixW25P.covered_split3 69602 wk10llllllll wk10lllllllr
theorem wk10llllllr : SixW25P.Covered 29720 44064 69602 81733 31144 40128 57472 81733 29720 44064 :=
  SixW25P.covered_of_walk lbS hbas 319775959655048802 200 29720 44064 69602 81733 31144 40128 57472 81733 29720 44064 67
    (by decide +kernel) (by decide)
theorem wk10llllll : SixW25P.Covered 29720 44064 57472 81733 31144 40128 57472 81733 29720 44064 :=
  SixW25P.covered_split1 69602 wk10lllllll wk10llllllr
theorem wk10lllllr : SixW25P.Covered 29720 44064 57472 81733 31144 40128 81733 105995 29720 44064 :=
  SixW25P.covered_of_walk lbS hbas 6471010441926385966884229568142013118906867935230086614334214224576819834636920990604741859456916667833077491304450988687547984398810994944863877710420402567954586879068952074049774791003726786940148413894449663708498499721225247415535944474208318738671452751087040148762891513813638310357390990156124001470837478 200 29720 44064 57472 81733 31144 40128 81733 105995 29720 44064 1047
    (by decide +kernel) (by decide)
theorem wk10lllll : SixW25P.Covered 29720 44064 57472 81733 31144 40128 57472 105995 29720 44064 :=
  SixW25P.covered_split3 81733 wk10llllll wk10lllllr
theorem wk10llllr : SixW25P.Covered 29720 44064 81733 105995 31144 40128 57472 105995 29720 44064 :=
  SixW25P.covered_of_walk lbS hbas 6781447444595080338157134230311579007842870618425217447696703180791347336108521921129197624459913715601994600639318574446197815684027739346972793298772414922655562846007688101305252308132590529818736136766124135618129950174873752014715144729638445808519014215663948448723502162325987785415558359567185545751098950255735666085688494775046995584750 200 29720 44064 81733 105995 31144 40128 57472 105995 29720 44064 1152
    (by decide +kernel) (by decide)
theorem wk10llll : SixW25P.Covered 29720 44064 57472 105995 31144 40128 57472 105995 29720 44064 :=
  SixW25P.covered_split1 81733 wk10lllll wk10llllr
theorem wk10lllr : SixW25P.Covered 29720 44064 57472 105995 31144 40128 105995 154518 29720 44064 :=
  SixW25P.covered_of_walk lbS hbas 147123814 200 29720 44064 57472 105995 31144 40128 105995 154518 29720 44064 37
    (by decide +kernel) (by decide)
theorem wk10lll : SixW25P.Covered 29720 44064 57472 105995 31144 40128 57472 154518 29720 44064 :=
  SixW25P.covered_split3 105995 wk10llll wk10lllr
theorem wk10llr : SixW25P.Covered 29720 44064 105995 154518 31144 40128 57472 154518 29720 44064 :=
  SixW25P.covered_of_walk lbS hbas 6950383342 200 29720 44064 105995 154518 31144 40128 57472 154518 29720 44064 42
    (by decide +kernel) (by decide)
theorem wk10ll : SixW25P.Covered 29720 44064 57472 154518 31144 40128 57472 154518 29720 44064 :=
  SixW25P.covered_split1 105995 wk10lll wk10llr
theorem wk10lr : SixW25P.Covered 29720 44064 57472 154518 31144 40128 154518 251564 29720 44064 :=
  SixW25P.covered_of_walk lbS hbas 0 200 29720 44064 57472 154518 31144 40128 154518 251564 29720 44064 2
    (by decide +kernel) (by decide)
theorem wk10l : SixW25P.Covered 29720 44064 57472 154518 31144 40128 57472 251564 29720 44064 :=
  SixW25P.covered_split3 154518 wk10ll wk10lr
theorem wk10r : SixW25P.Covered 29720 44064 154518 251564 31144 40128 57472 251564 29720 44064 :=
  SixW25P.covered_of_walk lbS hbas 0 200 29720 44064 154518 251564 31144 40128 57472 251564 29720 44064 2
    (by decide +kernel) (by decide)
theorem wk10 : SixW25P.Covered 29720 44064 57472 251564 31144 40128 57472 251564 29720 44064 :=
  SixW25P.covered_split1 154518 wk10l wk10r
theorem wk11 : SixW25P.Covered 29720 44064 57472 251564 31144 40128 57472 251564 53080 354601 :=
  SixW25P.covered_of_walk lbS hbas 11365383317922177935784740721643202759564188184389565603439705833521100281890304599067996759211890006639392959516708445678675301085385719115195308901379617362405701972931427219918779877575994193011195548333673865688630787671002159385995006981853937179595420966445900530290953341504799499717301825846355935746262736006121958238232549496362649757654697887860446694938794110071956714244792257466086868969511753100221262886203864951004150990719024506524607472946144661301362431756332472747305664075185241882382179171040861629173368885839159604133299102663285531407165517528330380748633973945330273785858962543897693491431518417194210482287649987056979315131704907166675831537782523707135123562355880828232995149779404898434614502853936525237023892284837529764247449165148648952669260401990664578478030211448189980544026324144734200056961478778725090198510311406804567861859483646718403841373540984045199944186870851353620426488545850521552198486705047981461614086184668859122659718608022570698458403269377613107409587378540296700063325663422740559102002224934467281132989781794808955168600336390954815228945532386860090388236383476636886325904301389063981688769710862782517225943792060219633590935753537721857440085879858999297854344964054690447800402622402365145968845814951112347375166752167244975964422168747822741952489031444077634560234102252212864467561524303693682647881547242235159512765404486395827272587277413956569346187074746075224980627113121227111612022552751381162659621055901237597907453376317790565094 200 29720 44064 57472 251564 31144 40128 57472 251564 53080 354601 5037
    (by decide +kernel) (by decide)
theorem wk12llllllllllll : SixW25P.Covered 29720 36892 57472 63537 58040 73664 30944 35744 29720 36892 :=
  SixW25P.covered_of_walk lbS hbas 626141297426456641621368812752045408103196501179835664919206981216890109419087175962139878041710936648469062364518535341713520085656703268247648028686074783593643102009136923579367540105673974100715228337001305414 200 29720 36892 57472 63537 58040 73664 30944 35744 29720 36892 712
    (by decide +kernel) (by decide)
theorem wk12lllllllllllrll : SixW25P.Covered 29720 36892 63537 69602 58040 61946 30944 35744 29720 36892 :=
  SixW25P.covered_of_walk lbS hbas 0 200 29720 36892 63537 69602 58040 61946 30944 35744 29720 36892 2
    (by decide +kernel) (by decide)
theorem wk12lllllllllllrlrl : SixW25P.Covered 29720 36892 63537 69602 61946 65852 30944 33344 29720 36892 :=
  SixW25P.covered_of_walk lbS hbas 1382068628751889026713195464186009748350426446413664227589455172019200505415266325869353362960948579234179147355403618766 200 29720 36892 63537 69602 61946 65852 30944 33344 29720 36892 407
    (by decide +kernel) (by decide)
theorem wk12lllllllllllrlrrl : SixW25P.Covered 29720 36892 63537 69602 61946 65852 33344 35744 29720 33306 :=
  SixW25P.covered_of_walk lbS hbas 134717997833056969335600844757847314986451636485969281291353881369058926335016312800657070086087469562177160274 200 29720 36892 63537 69602 61946 65852 33344 35744 29720 33306 382
    (by decide +kernel) (by decide)
theorem wk12lllllllllllrlrrr : SixW25P.Covered 29720 36892 63537 69602 61946 65852 33344 35744 33306 36892 :=
  SixW25P.covered_of_walk lbS hbas 781559634833206368536913092450708053133119235863511829925208833893816278707248320946368148576302530020463495720838112955679828643729234224595294382082993402873749172048522276272930624676059293910548863992270998447468928043078622145922886327011202241495437982835749698845719215470624389029171861032433161296091007834807584921340724569773145615039547583413959746975853867996883386568801853656225247046528584495966358207276002162981247225810708302313903260955932240031540163552224023664273834178240071064504764201102686675642621365108913528236989335967348164166033265093100671458162510507948700114830494645802951454308777316739230605630135167701301602588229029869618215272931490577199527690151012208840265138399337607649413375164787732222127912212870105718523760777843313662289981505473071777483884215543939629813072346470029451770254200433455019590416842573352478532178509574548791615809019090192332858757652104820902485001142439965228204881148554856869673257653549371792254353655816854042554072730623472919082635283356212603706116409725593639820947838018366535589024174801074817867529187312583670148654434124878062035939918579512175600639126246262805673174690366604056620852010874229822693198103459272348183764951253348515721898083133142985574593495168760749588088740145523935325941483392973435864651709738504430353788747039040608425172826307823027920519752691309501225031226269876876086983532974049556209831754060452806353101633462555891891314228736451930381683554921123304902333635848603254230247037295653016699209954217226059188454612477619559038772163067505558224285516712773748922585696357486452834005157004726393961227277135656944169305986990968456917543204083858341054824444040462810958005684824200175151210293723367923168552225381785942440811852078326982255729442263044358210421944485499774506890348757272442512078576392068281202780576282528831399208854405096753751566262868679718945269028257126950844500145348484202886347650478150355750957430525848693627400786912679817652879772435688236732988344554112416596584547998250660085581376301149434398039115390871853021438193374771519793453398183971774594825241669755067131295254698195516254846248784569701921180213553472055479578555618396899387858114501528165252686882 200 29720 36892 63537 69602 61946 65852 33344 35744 33306 36892 7382
    (by decide +kernel) (by decide)
theorem wk12lllllllllllrlrr : SixW25P.Covered 29720 36892 63537 69602 61946 65852 33344 35744 29720 36892 :=
  SixW25P.covered_split4 33306 wk12lllllllllllrlrrl wk12lllllllllllrlrrr
theorem wk12lllllllllllrlr : SixW25P.Covered 29720 36892 63537 69602 61946 65852 30944 35744 29720 36892 :=
  SixW25P.covered_split3 33344 wk12lllllllllllrlrl wk12lllllllllllrlrr
theorem wk12lllllllllllrl : SixW25P.Covered 29720 36892 63537 69602 58040 65852 30944 35744 29720 36892 :=
  SixW25P.covered_split2 61946 wk12lllllllllllrll wk12lllllllllllrlr
theorem wk12lllllllllllrr : SixW25P.Covered 29720 36892 63537 69602 65852 73664 30944 35744 29720 36892 :=
  SixW25P.covered_of_walk lbS hbas 190337899489304183004278027957835626169742255504776837958424380565470538506749164275136128309336792005831300691313203107964077690826873866230446407306283984541902364907403076729044575026405717675027631719709048220643813064845885538492938744857825534149838281414845580482438262411547088223345501229096198799609563052029688338744357544543286160158762782681674956506625061608668232539280858137606726119278141512841116453725596696599329032971358835908973580757212058240710096010830132518951813467568064930211962720460457184157373563917667962111908712292061177338955597994668698393500208490527352668690852712722601417475342571008071545152141341564985267126171652097172906694800515673567781218861911228136387991408510483752836398032464671428069300126241803172086602024040931601301297545300269285947807761146676634958142788673346789906865701066119860443531586290537924491525777709717632213757428444075417034951061396614413067392328285818788467428288033754595168406902735012816670391875635987183592524165425880693576643378153353010206645061860076541223428517119970456549523942581524075350939210830604250378438760557817604315753019616683382204807570935707289883971676913606110687703074353611726802831271249749349189880681231042876878902350153467025259635389580728735612355772928976483910334686692643281164739401006600645327210415913844566957167019101846360735638870876476341718990235604644751042465900116349813485030988694487326062941302148771785266920873394453805871974728645110320747492264791767181502425371495466631278961345829712186647690138001378908045750027679940983682054672581456744358924100905116209670383598691137541785399466344111498606078464151524430267973612487384197257382752225195382508469402476347890493673194 200 29720 36892 63537 69602 65852 73664 30944 35744 29720 36892 5707
    (by decide +kernel) (by decide)
theorem wk12lllllllllllr : SixW25P.Covered 29720 36892 63537 69602 58040 73664 30944 35744 29720 36892 :=
  SixW25P.covered_split2 65852 wk12lllllllllllrl wk12lllllllllllrr
theorem wk12lllllllllll : SixW25P.Covered 29720 36892 57472 69602 58040 73664 30944 35744 29720 36892 :=
  SixW25P.covered_split1 63537 wk12llllllllllll wk12lllllllllllr
theorem wk12llllllllllr : SixW25P.Covered 36892 44064 57472 69602 58040 73664 30944 35744 29720 36892 :=
  SixW25P.covered_of_walk lbS hbas 1019926304490919174690 200 36892 44064 57472 69602 58040 73664 30944 35744 29720 36892 87
    (by decide +kernel) (by decide)
theorem wk12llllllllll : SixW25P.Covered 29720 44064 57472 69602 58040 73664 30944 35744 29720 36892 :=
  SixW25P.covered_split0 36892 wk12lllllllllll wk12llllllllllr
theorem wk12lllllllllr : SixW25P.Covered 29720 44064 57472 69602 58040 73664 35744 40544 29720 36892 :=
  SixW25P.covered_of_walk lbS hbas 25004668674043935070005403245787439408724804639210011122290885508858248396475754030 200 29720 44064 57472 69602 58040 73664 35744 40544 29720 36892 292
    (by decide +kernel) (by decide)
theorem wk12lllllllll : SixW25P.Covered 29720 44064 57472 69602 58040 73664 30944 40544 29720 36892 :=
  SixW25P.covered_split3 35744 wk12llllllllll wk12lllllllllr
theorem wk12llllllllr : SixW25P.Covered 29720 44064 57472 69602 58040 73664 30944 40544 36892 44064 :=
  SixW25P.covered_of_walk lbS hbas 61230 200 29720 44064 57472 69602 58040 73664 30944 40544 36892 44064 22
    (by decide +kernel) (by decide)
theorem wk12llllllll : SixW25P.Covered 29720 44064 57472 69602 58040 73664 30944 40544 29720 44064 :=
  SixW25P.covered_split4 36892 wk12lllllllll wk12llllllllr
theorem wk12lllllllr : SixW25P.Covered 29720 44064 69602 81733 58040 73664 30944 40544 29720 44064 :=
  SixW25P.covered_of_walk lbS hbas 9934154436308215536412468834 200 29720 44064 69602 81733 58040 73664 30944 40544 29720 44064 102
    (by decide +kernel) (by decide)
theorem wk12lllllll : SixW25P.Covered 29720 44064 57472 81733 58040 73664 30944 40544 29720 44064 :=
  SixW25P.covered_split1 69602 wk12llllllll wk12lllllllr
theorem wk12llllllr : SixW25P.Covered 29720 44064 81733 105995 58040 73664 30944 40544 29720 44064 :=
  SixW25P.covered_of_walk lbS hbas 69124559249630406105697471847774756583701008965766693357029465820788068273770728181654741955974487943376951063655539481710808617917902817009932908815030669404805408472326439547957142768471895070940788075834774716246331184774866190683628200873593201805540540574725089365449726268039794 200 29720 44064 81733 105995 58040 73664 30944 40544 29720 44064 947
    (by decide +kernel) (by decide)
theorem wk12llllll : SixW25P.Covered 29720 44064 57472 105995 58040 73664 30944 40544 29720 44064 :=
  SixW25P.covered_split1 81733 wk12lllllll wk12llllllr
theorem wk12lllllr : SixW25P.Covered 29720 44064 57472 105995 73664 89288 30944 40544 29720 44064 :=
  SixW25P.covered_of_walk lbS hbas 0 200 29720 44064 57472 105995 73664 89288 30944 40544 29720 44064 2
    (by decide +kernel) (by decide)
theorem wk12lllll : SixW25P.Covered 29720 44064 57472 105995 58040 89288 30944 40544 29720 44064 :=
  SixW25P.covered_split2 73664 wk12llllll wk12lllllr
theorem wk12llllr : SixW25P.Covered 29720 44064 57472 105995 89288 120537 30944 40544 29720 44064 :=
  SixW25P.covered_of_walk lbS hbas 1774746691508988928195083877247174425259124773764182139746718369981987735001536082179107102805642565803221916244191187880453679808533300386370666696586962915329672469570834928141784401162915639426411829454832583704694681255566871397514105874034711517941696384846268649799704214281693847932411380925049596460923566969066441366164767974657490179141678924096324797679646257017468354548828631424000423346091304856504105862141505639059702774726248877927227537332449277844866692152988637936863178786639761541611755422141202297526499889528900473777274446027554202512457464558250365324279853283935131603393736024718562328745908716895414105962665207646957515366 200 29720 44064 57472 105995 89288 120537 30944 40544 29720 44064 2172
    (by decide +kernel) (by decide)
theorem wk12llll : SixW25P.Covered 29720 44064 57472 105995 58040 120537 30944 40544 29720 44064 :=
  SixW25P.covered_split2 89288 wk12lllll wk12llllr
theorem wk12lllr : SixW25P.Covered 29720 44064 57472 105995 120537 183034 30944 40544 29720 44064 :=
  SixW25P.covered_of_walk lbS hbas 83781157970225343078 200 29720 44064 57472 105995 120537 183034 30944 40544 29720 44064 77
    (by decide +kernel) (by decide)
theorem wk12lll : SixW25P.Covered 29720 44064 57472 105995 58040 183034 30944 40544 29720 44064 :=
  SixW25P.covered_split2 120537 wk12llll wk12lllr
theorem wk12llr : SixW25P.Covered 29720 44064 105995 154518 58040 183034 30944 40544 29720 44064 :=
  SixW25P.covered_of_walk lbS hbas 77249179887545002 200 29720 44064 105995 154518 58040 183034 30944 40544 29720 44064 67
    (by decide +kernel) (by decide)
theorem wk12ll : SixW25P.Covered 29720 44064 57472 154518 58040 183034 30944 40544 29720 44064 :=
  SixW25P.covered_split1 105995 wk12lll wk12llr
theorem wk12lr : SixW25P.Covered 29720 44064 57472 154518 183034 308028 30944 40544 29720 44064 :=
  SixW25P.covered_of_walk lbS hbas 0 200 29720 44064 57472 154518 183034 308028 30944 40544 29720 44064 2
    (by decide +kernel) (by decide)
theorem wk12l : SixW25P.Covered 29720 44064 57472 154518 58040 308028 30944 40544 29720 44064 :=
  SixW25P.covered_split2 183034 wk12ll wk12lr
theorem wk12r : SixW25P.Covered 29720 44064 154518 251564 58040 308028 30944 40544 29720 44064 :=
  SixW25P.covered_of_walk lbS hbas 0 200 29720 44064 154518 251564 58040 308028 30944 40544 29720 44064 2
    (by decide +kernel) (by decide)
theorem wk12 : SixW25P.Covered 29720 44064 57472 251564 58040 308028 30944 40544 29720 44064 :=
  SixW25P.covered_split1 154518 wk12l wk12r
theorem wk13llllllllllllll : SixW25P.Covered 29720 36892 57472 63537 58040 73664 30944 40544 53080 71925 :=
  SixW25P.covered_of_walk lbS hbas 220606346908200915776455919749190 200 29720 36892 57472 63537 58040 73664 30944 40544 53080 71925 112
    (by decide +kernel) (by decide)
theorem wk13lllllllllllllrll : SixW25P.Covered 29720 36892 63537 69602 58040 73664 30944 35744 53080 62502 :=
  SixW25P.covered_of_walk lbS hbas 16197870423879780818 200 29720 36892 63537 69602 58040 73664 30944 35744 53080 62502 67
    (by decide +kernel) (by decide)
theorem wk13lllllllllllllrlrll : SixW25P.Covered 29720 36892 63537 69602 58040 61946 30944 35744 62502 71925 :=
  SixW25P.covered_of_walk lbS hbas 0 200 29720 36892 63537 69602 58040 61946 30944 35744 62502 71925 2
    (by decide +kernel) (by decide)
theorem wk13lllllllllllllrlrlrl : SixW25P.Covered 29720 36892 63537 69602 61946 65852 30944 33344 62502 71925 :=
  SixW25P.covered_of_walk lbS hbas 10318 200 29720 36892 63537 69602 61946 65852 30944 33344 62502 71925 17
    (by decide +kernel) (by decide)
theorem wk13lllllllllllllrlrlrrl : SixW25P.Covered 29720 33306 63537 69602 61946 65852 33344 35744 62502 71925 :=
  SixW25P.covered_of_walk lbS hbas 1851156759058923731286074882788985167067860895965259600628325896722395002410980840908866 200 29720 33306 63537 69602 61946 65852 33344 35744 62502 71925 297
    (by decide +kernel) (by decide)
theorem wk13lllllllllllllrlrlrrrll : SixW25P.Covered 33306 36892 63537 66569 61946 65852 33344 35744 62502 67213 :=
  SixW25P.covered_of_walk lbS hbas 510609711985656100950798096709828149209893803549152926120311429279179992918640808819441643841785224857228565768157068397998226185618730668675594040464364451935297812533852760078616088024455933231892968702448820728640384362416863027368193773894452538878804814570009530785683087386817280145927572836183137027588662647913991748873492052707257491121387033123175980664572996737500020984648392776772820429011488113083858598368462179194171969989845649894721743426128551058096354568550319248948984398040568561933334978280910641597823707351995391885632453233321923536801473341027121476210852349246155257860098765615825119750256583120434766179476681553348581106527453878153033154127058610526140772489653171146859396770319935559521213130553924692222144529111337988160232144343999669807128678623511570320728594626483301889009393021373191910758522221273780565776297733249855220936369836934429698069704080898416706326571338467380936306256478772466798822966537380134809036643828988558759172566813956271289780216341654654048816112158411988156888216142837605079772663317151354056180956262217333548972968652516377711375762456099279975311978756507950813292139659289390982936478125571078911191711869319565591634933118022151344282194901531134526501817217110333255598941683226862226483420478060779258389625523787113769834050223311539515740887192533646112137345046937244259186384703486472033300750078706494092092057862675590024428493336929376484569165992807562521957735476382138398638986090088567132812203477328592861920640851700650104919185885235961985646860554560599680610067782744559256556938757469451449260912363983895804540107727798539735073940152586894182970959806701518959532491405263302449225294211654851805673486097345029033348049584004408768921920503175203908706842286067383578326798303707552022451011064787803282676532002425491162791665632502582047904686305162450914368463034516947936091425010170714930460837407215023132941965799320829646136950863919753161861392854047313072376272324470977231833438558765908902388003082438772721172160536416429637217371546031274 200 33306 36892 63537 66569 61946 65852 33344 35744 62502 67213 6812
    (by decide +kernel) (by decide)
theorem wk13lllllllllllllrlrlrrrlr : SixW25P.Covered 33306 36892 66569 69602 61946 65852 33344 35744 62502 67213 :=
  SixW25P.covered_of_walk lbS hbas 7073259159927566702912205189195628095807242323817861651786093682112857770600231164304905447251039442737990450846207720611946230391138789544291428280575553231632233321187676940817184944084561582441021363071665763599543220901719353617089530879858271750063757857641612904637885800675605632041182270386605870757522719758972933678634 200 33306 36892 66569 69602 61946 65852 33344 35744 62502 67213 1097
    (by decide +kernel) (by decide)
theorem wk13lllllllllllllrlrlrrrl : SixW25P.Covered 33306 36892 63537 69602 61946 65852 33344 35744 62502 67213 :=
  SixW25P.covered_split1 66569 wk13lllllllllllllrlrlrrrll wk13lllllllllllllrlrlrrrlr
theorem wk13lllllllllllllrlrlrrrr : SixW25P.Covered 33306 36892 63537 69602 61946 65852 33344 35744 67213 71925 :=
  SixW25P.covered_of_walk lbS hbas 905823316404871188976807503426389170927320075648716592859988849568922000143008658586102386 200 33306 36892 63537 69602 61946 65852 33344 35744 67213 71925 307
    (by decide +kernel) (by decide)
theorem wk13lllllllllllllrlrlrrr : SixW25P.Covered 33306 36892 63537 69602 61946 65852 33344 35744 62502 71925 :=
  SixW25P.covered_split4 67213 wk13lllllllllllllrlrlrrrl wk13lllllllllllllrlrlrrrr
theorem wk13lllllllllllllrlrlrr : SixW25P.Covered 29720 36892 63537 69602 61946 65852 33344 35744 62502 71925 :=
  SixW25P.covered_split0 33306 wk13lllllllllllllrlrlrrl wk13lllllllllllllrlrlrrr
theorem wk13lllllllllllllrlrlr : SixW25P.Covered 29720 36892 63537 69602 61946 65852 30944 35744 62502 71925 :=
  SixW25P.covered_split3 33344 wk13lllllllllllllrlrlrl wk13lllllllllllllrlrlrr
theorem wk13lllllllllllllrlrl : SixW25P.Covered 29720 36892 63537 69602 58040 65852 30944 35744 62502 71925 :=
  SixW25P.covered_split2 61946 wk13lllllllllllllrlrll wk13lllllllllllllrlrlr
theorem wk13lllllllllllllrlrr : SixW25P.Covered 29720 36892 63537 69602 65852 73664 30944 35744 62502 71925 :=
  SixW25P.covered_of_walk lbS hbas 2596499257052463350485919837083104358260932812341038698605118547660921663321041933730963621431663117355407145727021882016626469909740490247311616900337167584010985196600878635462575865062555581192296847079551101532721794171337946540907880795991935807654891881499706442893383794738820129557661293854075738539478870103597481418862386954369695285109615559640077100798020524910261987535863122244793850551506346972184642472284109248339731842587451841702023888103910023591641126749151438777528432196161918667602274486942580226758816416181914908757426423221974583852719824734405646842669798819122356206498264438216730205882436654301069111957448504816486381442251395480687720003294794052791930686382782191133731262306294215878453570174764152054341485770262367701566521334862383087075642717717893410767684127857270990736530672091303159431457177179076769218826450723888014611373072181262280806996335773082875069704906143793459393005206188371349005047584823889256047474110839503260682721820311521181144323687534462327682852470484971623712547901809563464851843799396903997994798469805716051076116097508307439068540127412191621454022860896384550804478753957253989735138440920356928073385718206806969491437402202178241836164298714828393233761240371359149238951804567469090888982852124825629165148083590286720676130594180166085163376296682 200 29720 36892 63537 69602 65852 73664 30944 35744 62502 71925 4402
    (by decide +kernel) (by decide)
theorem wk13lllllllllllllrlr : SixW25P.Covered 29720 36892 63537 69602 58040 73664 30944 35744 62502 71925 :=
  SixW25P.covered_split2 65852 wk13lllllllllllllrlrl wk13lllllllllllllrlrr
theorem wk13lllllllllllllrl : SixW25P.Covered 29720 36892 63537 69602 58040 73664 30944 35744 53080 71925 :=
  SixW25P.covered_split4 62502 wk13lllllllllllllrll wk13lllllllllllllrlr
theorem wk13lllllllllllllrr : SixW25P.Covered 29720 36892 63537 69602 58040 73664 35744 40544 53080 71925 :=
  SixW25P.covered_of_walk lbS hbas 1527287598092923769758605142359044070879823791924177508292848985898604404880126910692157274297948777200974933173200507130893102 200 29720 36892 63537 69602 58040 73664 35744 40544 53080 71925 427
    (by decide +kernel) (by decide)
theorem wk13lllllllllllllr : SixW25P.Covered 29720 36892 63537 69602 58040 73664 30944 40544 53080 71925 :=
  SixW25P.covered_split3 35744 wk13lllllllllllllrl wk13lllllllllllllrr
theorem wk13lllllllllllll : SixW25P.Covered 29720 36892 57472 69602 58040 73664 30944 40544 53080 71925 :=
  SixW25P.covered_split1 63537 wk13llllllllllllll wk13lllllllllllllr
theorem wk13llllllllllllr : SixW25P.Covered 36892 44064 57472 69602 58040 73664 30944 40544 53080 71925 :=
  SixW25P.covered_of_walk lbS hbas 3517868221986 200 36892 44064 57472 69602 58040 73664 30944 40544 53080 71925 52
    (by decide +kernel) (by decide)
theorem wk13llllllllllll : SixW25P.Covered 29720 44064 57472 69602 58040 73664 30944 40544 53080 71925 :=
  SixW25P.covered_split0 36892 wk13lllllllllllll wk13llllllllllllr
theorem wk13lllllllllllr : SixW25P.Covered 29720 44064 69602 81733 58040 73664 30944 40544 53080 71925 :=
  SixW25P.covered_of_walk lbS hbas 8802 200 29720 44064 69602 81733 58040 73664 30944 40544 53080 71925 22
    (by decide +kernel) (by decide)
theorem wk13lllllllllll : SixW25P.Covered 29720 44064 57472 81733 58040 73664 30944 40544 53080 71925 :=
  SixW25P.covered_split1 69602 wk13llllllllllll wk13lllllllllllr
theorem wk13llllllllllr : SixW25P.Covered 29720 44064 57472 81733 58040 73664 30944 40544 71925 90770 :=
  SixW25P.covered_of_walk lbS hbas 18 200 29720 44064 57472 81733 58040 73664 30944 40544 71925 90770 7
    (by decide +kernel) (by decide)
theorem wk13llllllllll : SixW25P.Covered 29720 44064 57472 81733 58040 73664 30944 40544 53080 90770 :=
  SixW25P.covered_split4 71925 wk13lllllllllll wk13llllllllllr
theorem wk13lllllllllr : SixW25P.Covered 29720 44064 57472 81733 58040 73664 30944 40544 90770 128460 :=
  SixW25P.covered_of_walk lbS hbas 17305129285697249836393815319961064226251396877250610324422176569976186028931323797039448410467947376920869314116647270504269995209254 200 29720 44064 57472 81733 58040 73664 30944 40544 90770 128460 447
    (by decide +kernel) (by decide)
theorem wk13lllllllll : SixW25P.Covered 29720 44064 57472 81733 58040 73664 30944 40544 53080 128460 :=
  SixW25P.covered_split4 90770 wk13llllllllll wk13lllllllllr
theorem wk13llllllllr : SixW25P.Covered 29720 44064 57472 81733 58040 73664 30944 40544 128460 203840 :=
  SixW25P.covered_of_walk lbS hbas 102 200 29720 44064 57472 81733 58040 73664 30944 40544 128460 203840 12
    (by decide +kernel) (by decide)
theorem wk13llllllll : SixW25P.Covered 29720 44064 57472 81733 58040 73664 30944 40544 53080 203840 :=
  SixW25P.covered_split4 128460 wk13lllllllll wk13llllllllr
theorem wk13lllllllr : SixW25P.Covered 29720 44064 81733 105995 58040 73664 30944 40544 53080 203840 :=
  SixW25P.covered_of_walk lbS hbas 3747784314445590765198799666 200 29720 44064 81733 105995 58040 73664 30944 40544 53080 203840 97
    (by decide +kernel) (by decide)
theorem wk13lllllll : SixW25P.Covered 29720 44064 57472 105995 58040 73664 30944 40544 53080 203840 :=
  SixW25P.covered_split1 81733 wk13llllllll wk13lllllllr
theorem wk13llllllr : SixW25P.Covered 29720 44064 57472 105995 73664 89288 30944 40544 53080 203840 :=
  SixW25P.covered_of_walk lbS hbas 0 200 29720 44064 57472 105995 73664 89288 30944 40544 53080 203840 2
    (by decide +kernel) (by decide)
theorem wk13llllll : SixW25P.Covered 29720 44064 57472 105995 58040 89288 30944 40544 53080 203840 :=
  SixW25P.covered_split2 73664 wk13lllllll wk13llllllr
theorem wk13lllllr : SixW25P.Covered 29720 44064 57472 105995 89288 120537 30944 40544 53080 203840 :=
  SixW25P.covered_of_walk lbS hbas 740910205469215744749460514363445000055218640877175488973263972149387063669426 200 29720 44064 57472 105995 89288 120537 30944 40544 53080 203840 267
    (by decide +kernel) (by decide)
theorem wk13lllll : SixW25P.Covered 29720 44064 57472 105995 58040 120537 30944 40544 53080 203840 :=
  SixW25P.covered_split2 89288 wk13llllll wk13lllllr
theorem wk13llllr : SixW25P.Covered 29720 44064 57472 105995 120537 183034 30944 40544 53080 203840 :=
  SixW25P.covered_of_walk lbS hbas 1258278 200 29720 44064 57472 105995 120537 183034 30944 40544 53080 203840 27
    (by decide +kernel) (by decide)
theorem wk13llll : SixW25P.Covered 29720 44064 57472 105995 58040 183034 30944 40544 53080 203840 :=
  SixW25P.covered_split2 120537 wk13lllll wk13llllr
theorem wk13lllr : SixW25P.Covered 29720 44064 105995 154518 58040 183034 30944 40544 53080 203840 :=
  SixW25P.covered_of_walk lbS hbas 1723019946 200 29720 44064 105995 154518 58040 183034 30944 40544 53080 203840 42
    (by decide +kernel) (by decide)
theorem wk13lll : SixW25P.Covered 29720 44064 57472 154518 58040 183034 30944 40544 53080 203840 :=
  SixW25P.covered_split1 105995 wk13llll wk13lllr
theorem wk13llr : SixW25P.Covered 29720 44064 57472 154518 183034 308028 30944 40544 53080 203840 :=
  SixW25P.covered_of_walk lbS hbas 0 200 29720 44064 57472 154518 183034 308028 30944 40544 53080 203840 2
    (by decide +kernel) (by decide)
theorem wk13ll : SixW25P.Covered 29720 44064 57472 154518 58040 308028 30944 40544 53080 203840 :=
  SixW25P.covered_split2 183034 wk13lll wk13llr
theorem wk13lr : SixW25P.Covered 29720 44064 57472 154518 58040 308028 30944 40544 203840 354601 :=
  SixW25P.covered_of_walk lbS hbas 0 200 29720 44064 57472 154518 58040 308028 30944 40544 203840 354601 2
    (by decide +kernel) (by decide)
theorem wk13l : SixW25P.Covered 29720 44064 57472 154518 58040 308028 30944 40544 53080 354601 :=
  SixW25P.covered_split4 203840 wk13ll wk13lr
theorem wk13r : SixW25P.Covered 29720 44064 154518 251564 58040 308028 30944 40544 53080 354601 :=
  SixW25P.covered_of_walk lbS hbas 0 200 29720 44064 154518 251564 58040 308028 30944 40544 53080 354601 2
    (by decide +kernel) (by decide)
theorem wk13 : SixW25P.Covered 29720 44064 57472 251564 58040 308028 30944 40544 53080 354601 :=
  SixW25P.covered_split1 154518 wk13l wk13r
theorem wk14 : SixW25P.Covered 29720 44064 57472 251564 58040 308028 57472 251564 29720 44064 :=
  SixW25P.covered_of_walk lbS hbas 87601600229466671275623648267900605158631301603207412346401749326595833125274056587201978789189545718657010573173686289456970936396101364588293737151593276946142435380759744720395638288177311487047858458574468218639541320353802330755041248968868186837417091025428638920949597003254013163797455733405818972871959010373562481623773056786705927694807629884859277846475926619701025700118321988487065481581201379703068676003712524981397388177777961753352421755102249579448367234277279160664402086667251694120067689203518953790869420260060668327911131888848918839706012904225529360040168559556387386470907734158644897283170051538027139735609229191265609366578050264646985384748847976964590727796226209792373367697143594340324953596554208872916675044338641877328116676914312684043771631845687607314249479564843848721985554873330699338108219848296773981549346738002588073336659615379999367224793852681927140057209835736723719092194870264606735871782311686429557377013898340394726 200 29720 44064 57472 251564 58040 308028 57472 251564 29720 44064 3242
    (by decide +kernel) (by decide)
theorem wk15 : SixW25P.Covered 29720 44064 57472 251564 58040 308028 57472 251564 53080 354601 :=
  SixW25P.covered_of_walk lbS hbas 86695467053712304383365945046027404154199155463234277892747281739366 200 29720 44064 57472 251564 58040 308028 57472 251564 53080 354601 242
    (by decide +kernel) (by decide)
theorem wk16 : SixW25P.Covered 53080 354601 30944 40544 31144 40128 30944 40544 29720 44064 :=
  SixW25P.covered_of_walk lbS hbas 0 200 53080 354601 30944 40544 31144 40128 30944 40544 29720 44064 2
    (by decide +kernel) (by decide)
theorem wk17llllllllll : SixW25P.Covered 53080 62502 30944 35744 31144 40128 30944 40544 53080 71925 :=
  SixW25P.covered_of_walk lbS hbas 2242255080457448531637729530710126474836919438568063850269055872234437627598629500331141994171582418030109077181074997242442070562882 200 53080 62502 30944 35744 31144 40128 30944 40544 53080 71925 447
    (by decide +kernel) (by decide)
theorem wk17lllllllllrll : SixW25P.Covered 62502 71925 30944 35744 31144 40128 30944 35744 53080 62502 :=
  SixW25P.covered_of_walk lbS hbas 35235117515727064552195154 200 62502 71925 30944 35744 31144 40128 30944 35744 53080 62502 102
    (by decide +kernel) (by decide)
theorem wk17lllllllllrlrll : SixW25P.Covered 62502 71925 30944 33344 31144 35636 30944 35744 62502 71925 :=
  SixW25P.covered_of_walk lbS hbas 146084196418668336165548700101678977688325193612536899358134845873262662401848325391864031039231200928434087871565450781214233192814567210849755701715413882477225505917558686767802646506736500266665790950098168862484920071616367924767099712534206808845342090801578349700245430037382922830583238 200 62502 71925 30944 33344 31144 35636 30944 35744 62502 71925 982
    (by decide +kernel) (by decide)
theorem wk17lllllllllrlrlrl : SixW25P.Covered 62502 71925 33344 35744 31144 35636 30944 33344 62502 71925 :=
  SixW25P.covered_of_walk lbS hbas 71388279275841817848854560327258872370933735656837624555602276828610075541986548782276913083662656245534842341834346035373484075131632270809929688378221829578322617124888891556548159790934333273675051462679929490221696667622657395412548066225418213664790303490564755821072976878028183103714692359079246 200 62502 71925 33344 35744 31144 35636 30944 33344 62502 71925 1012
    (by decide +kernel) (by decide)
theorem wk17lllllllllrlrlrrl : SixW25P.Covered 62502 71925 33344 35744 31144 33390 33344 35744 62502 71925 :=
  SixW25P.covered_of_walk lbS hbas 4310336807484020183314533178149886616354359376598982919956031829182019992731085701425265835378213063948670009712742233036432621976431548333353321004694322516587959753721484022258360525891335122795529902067198078160640794478539074004688199501314592391032794080344182668151965309883867235912010 200 62502 71925 33344 35744 31144 33390 33344 35744 62502 71925 977
    (by decide +kernel) (by decide)
theorem wk17lllllllllrlrlrrrllll : SixW25P.Covered 62502 64857 33344 35744 33390 35636 33344 35744 62502 64857 :=
  SixW25P.covered_of_walk lbS hbas 10807880325085826611920594738020245379100310798794094818582353905817518525430388879338069452835659011892000831061926784869186106178491279940468026387008265877287708805680829682675959545434137569459017875832476506703309282606588974577790595135735673285347738810376732178309951382492500214463513579942735511056289768390436602751712144837388784240300825196778340789811056173882459097445159517777803500616888824118251333717549308475949722835751836500166887742255038802893575699026783675455307613770742403943657762570835390186420583776598212308182674880664251825907182185128930366384654326174492436794613115572847144414180886273435098581502516516275899665102894796671810709861978632373230186119312136251129811694071303091222167714762759955234591434278947555099272982441582122850765856386050108119449591446885759831450747552407322587866814346218763298834673270717485869521234702036348356133964872347766638018532134897851174236217828438253393493628737166927045532384845718140437744601303210942460432913717783591891796137836464968089641409500349476652194758192682640894217843219615426562349960808632825156325737963520022373890574594045560243363210196980922750586540035863254230537491209255561095679808087914775079659410510704212720335160133895306611155228504809896722782952985142555454377720201188835123033779204813502869804319764815763391321239350275627422989941454970922894733665568391240965807384881173185018263733123261101364388385740212415376649133196053380501360561985180349077428887821441346985903048614748918358628527710674474204231229579182094798228961217398900344936266302193380687908044186542074988519419859450672032066878609468574441950945609024756018965228524084731845417803824718795426206915951866502553586129998430903356538240795117904380109924229752283775903415404333988521543255272089636785862376449622018372562071969553661087676582879840090732334530090189464751920678356853472357710116235491304938258719021362484707365955009150173560245085386885449455397606 200 62502 64857 33344 35744 33390 35636 33344 35744 62502 64857 6537
    (by decide +kernel) (by decide)
theorem wk17lllllllllrlrlrrrlllr : SixW25P.Covered 62502 64857 33344 35744 33390 35636 33344 35744 64857 67213 :=
  SixW25P.covered_of_walk lbS hbas 565543427113454086526362397961763235858736982410556016785570612701726982855921551408590324708047952420901016386353972503675059221025956083617753380714156306469525676301047233808437298775844503043737380918742484622771309160803735451837253461195481715956976663257970582424838411763907879089769733094905926903723096762803429827515478712468750542932185097070477019581465928447434756466895771305729312124581026682274320985965532101066440425679936989585233874866991438011775709600267457700286718874057570767009197335627640544572998731293780333745588288451156669682340573367225066451204998763497682230558192419616610368041113561394031621648706301363599631579183304177046187591465874009136415437825454694096474561467787521635496153638123203373230005743023356138084276193045485772059344232318001659037014320035642146169933673235154845785899818852593656708702870297559674397659921226215206070115521205420712900979181231602064513638078338562939091688060913901587932233855417940846676561025158510263407278758167047008285647950259451431076108508969461507564781991489764224059415063132666833880220731938006231372851525774646320057912639723316059160798944042825698227479533717543972649959580653966152821471719419792699656665788898101796717384147684393118553544328604626377672122511004215700002808583276620758979201640805199760456054209278343118170861138693174398582678241305521936713286307391589443167699595127096555221348431179606865304509300452436450222483081027339535763881040153945369897124732695382472220461160519727129172866879594880190280815847336558 200 62502 64857 33344 35744 33390 35636 33344 35744 64857 67213 5127
    (by decide +kernel) (by decide)
theorem wk17lllllllllrlrlrrrlll : SixW25P.Covered 62502 64857 33344 35744 33390 35636 33344 35744 62502 67213 :=
  SixW25P.covered_split4 64857 wk17lllllllllrlrlrrrllll wk17lllllllllrlrlrrrlllr
theorem wk17lllllllllrlrlrrrllr : SixW25P.Covered 64857 67213 33344 35744 33390 35636 33344 35744 62502 67213 :=
  SixW25P.covered_of_walk lbS hbas 164315101106607170023834390069554440758912130556319270035131132734441631573416886210727211525849798554466683400089050108941496394940706899847246095353093380165790941992169229674780242221851200495589203726814064372910868138464601598712872423285428051623230124521385370479807395646373383080957005946180081968043816920875863242668505640174508353720470501830309922328572619816816121732082997128318834430041016468126933354029957439175923008914944351569848703353305160427043616523803775489880120888601941165643668587791762780629241142546677986774266150667449975900308250914220672200225714632164215316797630038106761487204249103463895040605740667834958197521713623071710498689290912392632750546186510943134155491618122626317390827894069919481849115887170297006527982721926014804844279181234725086872441832861841967090803965440088865262443652847954682545815130243592947250740957217473474667843063371039002928334335182419467926889866927195451922471310504085953283284488179068155292031059839598308923705322115133627614131618582484936001464846721727757498779901232234479641842546856157937458917022204822994599702626186918831407459309490054798183251826571756790453526917918424769726780577502370664889365220133078353038892212147167797022733384711506924869605579969550176767338877360167079504534728362152155843320601286124701111486198074247587206803954698718871846207496998 200 64857 67213 33344 35744 33390 35636 33344 35744 62502 67213 4517
    (by decide +kernel) (by decide)
theorem wk17lllllllllrlrlrrrll : SixW25P.Covered 62502 67213 33344 35744 33390 35636 33344 35744 62502 67213 :=
  SixW25P.covered_split0 64857 wk17lllllllllrlrlrrrlll wk17lllllllllrlrlrrrllr
theorem wk17lllllllllrlrlrrrlr : SixW25P.Covered 62502 67213 33344 35744 33390 35636 33344 35744 67213 71925 :=
  SixW25P.covered_of_walk lbS hbas 44270471593037172816405430272397160363806997115182814553693790186939122 200 62502 67213 33344 35744 33390 35636 33344 35744 67213 71925 242
    (by decide +kernel) (by decide)
theorem wk17lllllllllrlrlrrrl : SixW25P.Covered 62502 67213 33344 35744 33390 35636 33344 35744 62502 71925 :=
  SixW25P.covered_split4 67213 wk17lllllllllrlrlrrrll wk17lllllllllrlrlrrrlr
theorem wk17lllllllllrlrlrrrr : SixW25P.Covered 67213 71925 33344 35744 33390 35636 33344 35744 62502 71925 :=
  SixW25P.covered_of_walk lbS hbas 33465975985404605121692005189165858 200 67213 71925 33344 35744 33390 35636 33344 35744 62502 71925 122
    (by decide +kernel) (by decide)
theorem wk17lllllllllrlrlrrr : SixW25P.Covered 62502 71925 33344 35744 33390 35636 33344 35744 62502 71925 :=
  SixW25P.covered_split0 67213 wk17lllllllllrlrlrrrl wk17lllllllllrlrlrrrr
theorem wk17lllllllllrlrlrr : SixW25P.Covered 62502 71925 33344 35744 31144 35636 33344 35744 62502 71925 :=
  SixW25P.covered_split2 33390 wk17lllllllllrlrlrrl wk17lllllllllrlrlrrr
theorem wk17lllllllllrlrlr : SixW25P.Covered 62502 71925 33344 35744 31144 35636 30944 35744 62502 71925 :=
  SixW25P.covered_split3 33344 wk17lllllllllrlrlrl wk17lllllllllrlrlrr
theorem wk17lllllllllrlrl : SixW25P.Covered 62502 71925 30944 35744 31144 35636 30944 35744 62502 71925 :=
  SixW25P.covered_split1 33344 wk17lllllllllrlrll wk17lllllllllrlrlr
theorem wk17lllllllllrlrr : SixW25P.Covered 62502 71925 30944 35744 35636 40128 30944 35744 62502 71925 :=
  SixW25P.covered_of_walk lbS hbas 2455755638822251305364884558674934310773058549519713579943530 200 62502 71925 30944 35744 35636 40128 30944 35744 62502 71925 212
    (by decide +kernel) (by decide)
theorem wk17lllllllllrlr : SixW25P.Covered 62502 71925 30944 35744 31144 40128 30944 35744 62502 71925 :=
  SixW25P.covered_split2 35636 wk17lllllllllrlrl wk17lllllllllrlrr
theorem wk17lllllllllrl : SixW25P.Covered 62502 71925 30944 35744 31144 40128 30944 35744 53080 71925 :=
  SixW25P.covered_split4 62502 wk17lllllllllrll wk17lllllllllrlr
theorem wk17lllllllllrr : SixW25P.Covered 62502 71925 30944 35744 31144 40128 35744 40544 53080 71925 :=
  SixW25P.covered_of_walk lbS hbas 247698794151743912495005812294186222612011450670747149070080095367854 200 62502 71925 30944 35744 31144 40128 35744 40544 53080 71925 232
    (by decide +kernel) (by decide)
theorem wk17lllllllllr : SixW25P.Covered 62502 71925 30944 35744 31144 40128 30944 40544 53080 71925 :=
  SixW25P.covered_split3 35744 wk17lllllllllrl wk17lllllllllrr
theorem wk17lllllllll : SixW25P.Covered 53080 71925 30944 35744 31144 40128 30944 40544 53080 71925 :=
  SixW25P.covered_split0 62502 wk17llllllllll wk17lllllllllr
theorem wk17llllllllr : SixW25P.Covered 53080 71925 35744 40544 31144 40128 30944 40544 53080 71925 :=
  SixW25P.covered_of_walk lbS hbas 1338988964561844545861482634866154676447394367174959013381313377745156967079161718406541174743757701853926 200 53080 71925 35744 40544 31144 40128 30944 40544 53080 71925 357
    (by decide +kernel) (by decide)
theorem wk17llllllll : SixW25P.Covered 53080 71925 30944 40544 31144 40128 30944 40544 53080 71925 :=
  SixW25P.covered_split1 35744 wk17lllllllll wk17llllllllr
theorem wk17lllllllr : SixW25P.Covered 53080 71925 30944 40544 31144 40128 30944 40544 71925 90770 :=
  SixW25P.covered_of_walk lbS hbas 155397168174 200 53080 71925 30944 40544 31144 40128 30944 40544 71925 90770 42
    (by decide +kernel) (by decide)
theorem wk17lllllll : SixW25P.Covered 53080 71925 30944 40544 31144 40128 30944 40544 53080 90770 :=
  SixW25P.covered_split4 71925 wk17llllllll wk17lllllllr
theorem wk17llllllr : SixW25P.Covered 71925 90770 30944 40544 31144 40128 30944 40544 53080 90770 :=
  SixW25P.covered_of_walk lbS hbas 26162 200 71925 90770 30944 40544 31144 40128 30944 40544 53080 90770 22
    (by decide +kernel) (by decide)
theorem wk17llllll : SixW25P.Covered 53080 90770 30944 40544 31144 40128 30944 40544 53080 90770 :=
  SixW25P.covered_split0 71925 wk17lllllll wk17llllllr
theorem wk17lllllr : SixW25P.Covered 53080 90770 30944 40544 31144 40128 30944 40544 90770 128460 :=
  SixW25P.covered_of_walk lbS hbas 21765787249705658292151399791416383082067369078204490930321838527294312362951949125631663046355490009242735976112879756372131183611132844282519038550057760083958982704011246686490104615628428387262853091615170777149188508674640797332518796055524957313642500183810623281021734468998292407923403662727060625788232145358712903360083712238772228479652830536981838432602751261240161662261233017807221265879421814220227039966730512539613532989416556157684259785767287889039727383248849722783908475139290816676748345324956690511895385254081714093526058309813105733328772213331503699396793739630592080692952313822821631914678832645930868403856193022301797039937465725786703001795129995444620078558230564688721651547659077526208713259754082 200 53080 90770 30944 40544 31144 40128 30944 40544 90770 128460 2432
    (by decide +kernel) (by decide)
theorem wk17lllll : SixW25P.Covered 53080 90770 30944 40544 31144 40128 30944 40544 53080 128460 :=
  SixW25P.covered_split4 90770 wk17llllll wk17lllllr
theorem wk17llllr : SixW25P.Covered 53080 90770 30944 40544 31144 40128 30944 40544 128460 203840 :=
  SixW25P.covered_of_walk lbS hbas 49507540495048521855293257004618898512927062972357031632053761025784950355864989807331649314 200 53080 90770 30944 40544 31144 40128 30944 40544 128460 203840 312
    (by decide +kernel) (by decide)
theorem wk17llll : SixW25P.Covered 53080 90770 30944 40544 31144 40128 30944 40544 53080 203840 :=
  SixW25P.covered_split4 128460 wk17lllll wk17llllr
theorem wk17lllr : SixW25P.Covered 90770 128460 30944 40544 31144 40128 30944 40544 53080 203840 :=
  SixW25P.covered_of_walk lbS hbas 874497910510679594522034030116169727685859200492054070860103924907950871355014455452433226828052246574996238152408906678444051691287991090 200 90770 128460 30944 40544 31144 40128 30944 40544 53080 203840 472
    (by decide +kernel) (by decide)
theorem wk17lll : SixW25P.Covered 53080 128460 30944 40544 31144 40128 30944 40544 53080 203840 :=
  SixW25P.covered_split0 90770 wk17llll wk17lllr
theorem wk17llr : SixW25P.Covered 128460 203840 30944 40544 31144 40128 30944 40544 53080 203840 :=
  SixW25P.covered_of_walk lbS hbas 9522 200 128460 203840 30944 40544 31144 40128 30944 40544 53080 203840 17
    (by decide +kernel) (by decide)
theorem wk17ll : SixW25P.Covered 53080 203840 30944 40544 31144 40128 30944 40544 53080 203840 :=
  SixW25P.covered_split0 128460 wk17lll wk17llr
theorem wk17lr : SixW25P.Covered 53080 203840 30944 40544 31144 40128 30944 40544 203840 354601 :=
  SixW25P.covered_of_walk lbS hbas 0 200 53080 203840 30944 40544 31144 40128 30944 40544 203840 354601 2
    (by decide +kernel) (by decide)
theorem wk17l : SixW25P.Covered 53080 203840 30944 40544 31144 40128 30944 40544 53080 354601 :=
  SixW25P.covered_split4 203840 wk17ll wk17lr
theorem wk17r : SixW25P.Covered 203840 354601 30944 40544 31144 40128 30944 40544 53080 354601 :=
  SixW25P.covered_of_walk lbS hbas 0 200 203840 354601 30944 40544 31144 40128 30944 40544 53080 354601 2
    (by decide +kernel) (by decide)
theorem wk17 : SixW25P.Covered 53080 354601 30944 40544 31144 40128 30944 40544 53080 354601 :=
  SixW25P.covered_split0 203840 wk17l wk17r
theorem wk18 : SixW25P.Covered 53080 354601 30944 40544 31144 40128 57472 251564 29720 44064 :=
  SixW25P.covered_of_walk lbS hbas 0 200 53080 354601 30944 40544 31144 40128 57472 251564 29720 44064 2
    (by decide +kernel) (by decide)
theorem wk19lllllllll : SixW25P.Covered 53080 90770 30944 40544 31144 40128 57472 81733 53080 90770 :=
  SixW25P.covered_of_walk lbS hbas 31002573441902972671950796156062991718614476816031556882144350412037120546980438222562586458295561703915895577192092421680450015837478714272926596020258456871801490997373011541787564647460382353085090580462131320921438608793853635687290226857626768402881771510188849437639686557991087323546679402034092009718266678860619180419703148960237120658826455596321751628458823693037859204532305210326680315052589535500802868555462379150680892043141337764476254740366080458668897569312330165187701348275563110366675617020278108080745375298902752867787141247075013914774279057944750177524505326065106674285220941810657790596893053162229563227459940445960596420171683866925731505317796088099989104229255868993390478507942849925604416838507666868370710789594397932627303192410988319577233844791291832905116171483454823280414956195575426916286399880387852085300475826690344772460412663886439992650474742261900181377844918446451778578122511398090260234915486409782163697058731042475624834660517017748689296250366087779717436748286882493078630754956509491612039754384390482973608556642856673527245322424572384965812663389333167260095030188342663535385829685800682225021790238240856530337252201512062522803258050917231627888987215964402516615671133690828063771864326387729370375952066517989884369556229709741077318311702012993711575032167385579127276944523002041115878444365682933840375805120095523049515905351143703180801025041602776493009966513044606064529863025691598360135014038434547455075278396013973121455606712839959159788814260629701420858396911086262706022852640058725872620080018100674361295333940931440283719184129210515925410518221339913093742033567476528735342867861031045983848089567428924073854903546259833130027660588213199266237805796182006347619101690045136510629720437502498400670505844347102262000299785880941189235374948602823911267280958935603612032914366292698256832474706771573555507964541023408833189356014244569903392099842056711909571237741847198046150301648873919388516557952343672184989835313104295245873920884371479493454085250298105239693803512025571124927331730244646215988948054331902848354624918568200856179872897682085104293352864172162785195591765361133737527733965483575795533525011861538622878434 200 53080 90770 30944 40544 31144 40128 57472 81733 53080 90770 7377
    (by decide +kernel) (by decide)
theorem wk19llllllllr : SixW25P.Covered 53080 90770 30944 40544 31144 40128 81733 105995 53080 90770 :=
  SixW25P.covered_of_walk lbS hbas 905870229990213676728608628141135032098 200 53080 90770 30944 40544 31144 40128 81733 105995 53080 90770 137
    (by decide +kernel) (by decide)
theorem wk19llllllll : SixW25P.Covered 53080 90770 30944 40544 31144 40128 57472 105995 53080 90770 :=
  SixW25P.covered_split3 81733 wk19lllllllll wk19llllllllr
theorem wk19lllllllr : SixW25P.Covered 90770 128460 30944 40544 31144 40128 57472 105995 53080 90770 :=
  SixW25P.covered_of_walk lbS hbas 18 200 90770 128460 30944 40544 31144 40128 57472 105995 53080 90770 7
    (by decide +kernel) (by decide)
theorem wk19lllllll : SixW25P.Covered 53080 128460 30944 40544 31144 40128 57472 105995 53080 90770 :=
  SixW25P.covered_split0 90770 wk19llllllll wk19lllllllr
theorem wk19llllllr : SixW25P.Covered 128460 203840 30944 40544 31144 40128 57472 105995 53080 90770 :=
  SixW25P.covered_of_walk lbS hbas 0 200 128460 203840 30944 40544 31144 40128 57472 105995 53080 90770 2
    (by decide +kernel) (by decide)
theorem wk19llllll : SixW25P.Covered 53080 203840 30944 40544 31144 40128 57472 105995 53080 90770 :=
  SixW25P.covered_split0 128460 wk19lllllll wk19llllllr
theorem wk19lllllr : SixW25P.Covered 53080 203840 30944 40544 31144 40128 57472 105995 90770 128460 :=
  SixW25P.covered_of_walk lbS hbas 974370326446907300329268909488590881306043955329865930021652449956955593192658570826457772441269001089644513994731427017611002806111429841354638571381028744520226 200 53080 203840 30944 40544 31144 40128 57472 105995 90770 128460 552
    (by decide +kernel) (by decide)
theorem wk19lllll : SixW25P.Covered 53080 203840 30944 40544 31144 40128 57472 105995 53080 128460 :=
  SixW25P.covered_split4 90770 wk19llllll wk19lllllr
theorem wk19llllr : SixW25P.Covered 53080 203840 30944 40544 31144 40128 57472 105995 128460 203840 :=
  SixW25P.covered_of_walk lbS hbas 120916468258 200 53080 203840 30944 40544 31144 40128 57472 105995 128460 203840 47
    (by decide +kernel) (by decide)
theorem wk19llll : SixW25P.Covered 53080 203840 30944 40544 31144 40128 57472 105995 53080 203840 :=
  SixW25P.covered_split4 128460 wk19lllll wk19llllr
theorem wk19lllr : SixW25P.Covered 53080 203840 30944 40544 31144 40128 105995 154518 53080 203840 :=
  SixW25P.covered_of_walk lbS hbas 158693729074 200 53080 203840 30944 40544 31144 40128 105995 154518 53080 203840 47
    (by decide +kernel) (by decide)
theorem wk19lll : SixW25P.Covered 53080 203840 30944 40544 31144 40128 57472 154518 53080 203840 :=
  SixW25P.covered_split3 105995 wk19llll wk19lllr
theorem wk19llr : SixW25P.Covered 53080 203840 30944 40544 31144 40128 57472 154518 203840 354601 :=
  SixW25P.covered_of_walk lbS hbas 0 200 53080 203840 30944 40544 31144 40128 57472 154518 203840 354601 2
    (by decide +kernel) (by decide)
theorem wk19ll : SixW25P.Covered 53080 203840 30944 40544 31144 40128 57472 154518 53080 354601 :=
  SixW25P.covered_split4 203840 wk19lll wk19llr
theorem wk19lr : SixW25P.Covered 53080 203840 30944 40544 31144 40128 154518 251564 53080 354601 :=
  SixW25P.covered_of_walk lbS hbas 0 200 53080 203840 30944 40544 31144 40128 154518 251564 53080 354601 2
    (by decide +kernel) (by decide)
theorem wk19l : SixW25P.Covered 53080 203840 30944 40544 31144 40128 57472 251564 53080 354601 :=
  SixW25P.covered_split3 154518 wk19ll wk19lr
theorem wk19r : SixW25P.Covered 203840 354601 30944 40544 31144 40128 57472 251564 53080 354601 :=
  SixW25P.covered_of_walk lbS hbas 0 200 203840 354601 30944 40544 31144 40128 57472 251564 53080 354601 2
    (by decide +kernel) (by decide)
theorem wk19 : SixW25P.Covered 53080 354601 30944 40544 31144 40128 57472 251564 53080 354601 :=
  SixW25P.covered_split0 203840 wk19l wk19r
theorem wk20 : SixW25P.Covered 53080 354601 30944 40544 58040 308028 30944 40544 29720 44064 :=
  SixW25P.covered_of_walk lbS hbas 0 200 53080 354601 30944 40544 58040 308028 30944 40544 29720 44064 2
    (by decide +kernel) (by decide)
theorem wk21llllllllllllll : SixW25P.Covered 53080 62502 30944 35744 58040 73664 30944 40544 53080 71925 :=
  SixW25P.covered_of_walk lbS hbas 126781100486504280581269230386244569799080653702609573954 200 53080 62502 30944 35744 58040 73664 30944 40544 53080 71925 192
    (by decide +kernel) (by decide)
theorem wk21lllllllllllllrll : SixW25P.Covered 62502 71925 30944 35744 58040 73664 30944 35744 53080 62502 :=
  SixW25P.covered_of_walk lbS hbas 11417459794 200 62502 71925 30944 35744 58040 73664 30944 35744 53080 62502 42
    (by decide +kernel) (by decide)
theorem wk21lllllllllllllrlrll : SixW25P.Covered 62502 71925 30944 35744 58040 61946 30944 35744 62502 71925 :=
  SixW25P.covered_of_walk lbS hbas 0 200 62502 71925 30944 35744 58040 61946 30944 35744 62502 71925 2
    (by decide +kernel) (by decide)
theorem wk21lllllllllllllrlrlrl : SixW25P.Covered 62502 71925 30944 33344 61946 65852 30944 35744 62502 71925 :=
  SixW25P.covered_of_walk lbS hbas 2198207278890002618574 200 62502 71925 30944 33344 61946 65852 30944 35744 62502 71925 77
    (by decide +kernel) (by decide)
theorem wk21lllllllllllllrlrlrrl : SixW25P.Covered 62502 71925 33344 35744 61946 65852 30944 33344 62502 71925 :=
  SixW25P.covered_of_walk lbS hbas 29490217552775035214 200 62502 71925 33344 35744 61946 65852 30944 33344 62502 71925 72
    (by decide +kernel) (by decide)
theorem wk21lllllllllllllrlrlrrrlll : SixW25P.Covered 62502 67213 33344 35744 61946 63899 33344 35744 62502 67213 :=
  SixW25P.covered_of_walk lbS hbas 620161545630155150965519152419053729512541463165194356406267242746852298054378713489641004857733845195891828120136092607675717541896490169782200320938374191057867649246772355593353901283410192597720172553625591863619236122771483021169485146752251703594148426447967352284234 200 62502 67213 33344 35744 61946 63899 33344 35744 62502 67213 912
    (by decide +kernel) (by decide)
theorem wk21lllllllllllllrlrlrrrllrl : SixW25P.Covered 62502 64857 33344 35744 63899 65852 33344 35744 62502 67213 :=
  SixW25P.covered_of_walk lbS hbas 1415357175613778935511432176182006132502400514266262323881177842118814508666000520403851611217114002540254030195633520786798125026494989900284057171260522427444922746887374278806450723291183317478396969551859489445283307368665721502338320232123982082029395968934350760328533129511124303623909406423193937554022415754026990454513456270269622691475629935120055247244025561151670668576033042465275139596332733160254928641779860902664183021396346570869581061507828348267793402350916071655733838401731724215724848052711861950091282664427738919507866504240690876876835116308403812721398974659539868515936431218700835852481940723961562828900450368495074806711940036951416953715815025228591839184089061983885694899396159239854259560324943505623642828191743811066806081435883837496265914744369545624570511743426825614214269185988706788504948502281002390391101960949735247115350123210703996928262905952352191534780208166208804368163099718033406105845557027624416633726938741844900177771101833029102250508527245527202142676145785334344048885700010453571407461953939071208032676664111448646972985462462241581079216529286097502124510705043986319293653993289381967209265512537275614760364257348684387254220743695149028242056883775134797790441489823075805188105428420000151950917525880267767492944684760069405254888595301993706060147399804866564329187567787314243462151786716926822270094818780974405908968622294936752950562784573105718216985042733723501108557022959623025909509325949590448793926364543507347430417410904075518371326504076555514654782279195836910393451270980981407208456371004566853624063441038687629259473141408718437502411682574991290278777690960788500501057204976299081493097199355158717792127969976027964892930214579037365952307614264495978589628533627800601151309799542094350030651871459182079084452642439694950193823190325704193846228494765861239895762016197150280494840388685048628538594989462910573954441199982787328053695093848308050619605149220983988062029132556862815277844811360830974461171438434892433681744814770 200 62502 64857 33344 35744 63899 65852 33344 35744 62502 67213 6737
    (by decide +kernel) (by decide)
theorem wk21lllllllllllllrlrlrrrllrr : SixW25P.Covered 64857 67213 33344 35744 63899 65852 33344 35744 62502 67213 :=
  SixW25P.covered_of_walk lbS hbas 178242061272969028722343579195584755947132758529845641660877102812287153556482831759342806064678656963455121824671617102547755853489803964790099870123054639584263709405615495629663213729832139842040744695211518983992136016764959945635737530873449894019402894890697530978034263964169964228875212037882381084771870600861083768913400761161196359953604281357948485534168807803624514229400462899758119602607778004835450179138778068073073541088413758294198441025040140685056083825175533318221230534755468631632018024764313175463066055377482602243089689403861846289154053352358448151079418468582868320900821213451961284854000465293220414731768760867631089850080215811022889445361427624889374118871885527880161534384141345040838088872984209984560589481758081975996992288070616536888879787823306796499401302074115971799984215156961986325500387057340152456073519194749599560954256080170715150791979049889720462810800803257779132647946510807090728278236587127375442362300609856963622689993667865511161763203176499276745626277379128689312491176524530796704431115823922477658789279944335108168347536218518203606885257465547598596218930210078029228603355790358258892500888821621613428735966295010362667843663331025825285802755324515463999883590551459404727670620252667589046286392355944462922942745658620785373588006476548985541526358520748543459105217644770759498546844675339645023388243551274165397354119494664304806348564523976727720396143294305525668331038905838533225520565609735783589081738831860665086365184424068578589159997047556193593945895995695563538574483304838210771373605529054415886176552911404756306277830607745551504797078053047001169635750428983755693996602417493686269999880367224799826482 200 64857 67213 33344 35744 63899 65852 33344 35744 62502 67213 5632
    (by decide +kernel) (by decide)
theorem wk21lllllllllllllrlrlrrrllr : SixW25P.Covered 62502 67213 33344 35744 63899 65852 33344 35744 62502 67213 :=
  SixW25P.covered_split0 64857 wk21lllllllllllllrlrlrrrllrl wk21lllllllllllllrlrlrrrllrr
theorem wk21lllllllllllllrlrlrrrll : SixW25P.Covered 62502 67213 33344 35744 61946 65852 33344 35744 62502 67213 :=
  SixW25P.covered_split2 63899 wk21lllllllllllllrlrlrrrlll wk21lllllllllllllrlrlrrrllr
theorem wk21lllllllllllllrlrlrrrlr : SixW25P.Covered 62502 67213 33344 35744 61946 65852 33344 35744 67213 71925 :=
  SixW25P.covered_of_walk lbS hbas 9235746955266040586644168108460548560124558545778622712260873725456075294200707114413247266462657431938248862870808290552744772367325867882385164103626819239833619122 200 62502 67213 33344 35744 61946 65852 33344 35744 67213 71925 557
    (by decide +kernel) (by decide)
theorem wk21lllllllllllllrlrlrrrl : SixW25P.Covered 62502 67213 33344 35744 61946 65852 33344 35744 62502 71925 :=
  SixW25P.covered_split4 67213 wk21lllllllllllllrlrlrrrll wk21lllllllllllllrlrlrrrlr
theorem wk21lllllllllllllrlrlrrrr : SixW25P.Covered 67213 71925 33344 35744 61946 65852 33344 35744 62502 71925 :=
  SixW25P.covered_of_walk lbS hbas 5022606894014274272883579583957072307049388330573277584129401634 200 67213 71925 33344 35744 61946 65852 33344 35744 62502 71925 222
    (by decide +kernel) (by decide)
theorem wk21lllllllllllllrlrlrrr : SixW25P.Covered 62502 71925 33344 35744 61946 65852 33344 35744 62502 71925 :=
  SixW25P.covered_split0 67213 wk21lllllllllllllrlrlrrrl wk21lllllllllllllrlrlrrrr
theorem wk21lllllllllllllrlrlrr : SixW25P.Covered 62502 71925 33344 35744 61946 65852 30944 35744 62502 71925 :=
  SixW25P.covered_split3 33344 wk21lllllllllllllrlrlrrl wk21lllllllllllllrlrlrrr
theorem wk21lllllllllllllrlrlr : SixW25P.Covered 62502 71925 30944 35744 61946 65852 30944 35744 62502 71925 :=
  SixW25P.covered_split1 33344 wk21lllllllllllllrlrlrl wk21lllllllllllllrlrlrr
theorem wk21lllllllllllllrlrl : SixW25P.Covered 62502 71925 30944 35744 58040 65852 30944 35744 62502 71925 :=
  SixW25P.covered_split2 61946 wk21lllllllllllllrlrll wk21lllllllllllllrlrlr
theorem wk21lllllllllllllrlrr : SixW25P.Covered 62502 71925 30944 35744 65852 73664 30944 35744 62502 71925 :=
  SixW25P.covered_of_walk lbS hbas 983802484365772597108114787515646158383413782251385999580050574116450166133043939117204673982176022713725965647530148669159277658893062990404362636522431758998915936400251414729790824898092454500745741499579163395824271289816915611371173798866428671126829713091389183193667771743138038280188548506739380360744599038930142922967058374514189695934117138378975830604883217155906147069690149011839334394192064106030092348089727306720794911583186627798145604241775688352839074290072701858596638213524967686981571812227610306630174668259798451577722323054964552613474740750395773580594653114940908265911758889507206388117642480248403248414777282608328384716667111264491853392384357325284236245883370661746256545515580672572770448580049607981363946617329361675969367533996519733094289930024219741934338585082769530373137961631306116284340470869812128083338570254240970425600615691714898107661925899939529739588020683720766596335765615385769697126974307441132034446375717424887415324705674497217099338566732041298222080077843970511764548924920122220648981900269141186187842679357682041887756055792928783472957382630570326201834780168624785644081167221013442954255314101181938354944014975683415076659488429802111341192373580147275243391482678775371784241962676246848370362616739563706684215645642758820190260814590569164528922792554163737905234665258389585255365178551845052735589505092719106738233822749326910866339308031594 200 62502 71925 30944 35744 65852 73664 30944 35744 62502 71925 4707
    (by decide +kernel) (by decide)
theorem wk21lllllllllllllrlr : SixW25P.Covered 62502 71925 30944 35744 58040 73664 30944 35744 62502 71925 :=
  SixW25P.covered_split2 65852 wk21lllllllllllllrlrl wk21lllllllllllllrlrr
theorem wk21lllllllllllllrl : SixW25P.Covered 62502 71925 30944 35744 58040 73664 30944 35744 53080 71925 :=
  SixW25P.covered_split4 62502 wk21lllllllllllllrll wk21lllllllllllllrlr
theorem wk21lllllllllllllrr : SixW25P.Covered 62502 71925 30944 35744 58040 73664 35744 40544 53080 71925 :=
  SixW25P.covered_of_walk lbS hbas 58081320727663527150218079544579330802606529592769996207230984604863657987695091193003667092798827768958779945597379307142687426873084123254949081701343758081477294 200 62502 71925 30944 35744 58040 73664 35744 40544 53080 71925 557
    (by decide +kernel) (by decide)
theorem wk21lllllllllllllr : SixW25P.Covered 62502 71925 30944 35744 58040 73664 30944 40544 53080 71925 :=
  SixW25P.covered_split3 35744 wk21lllllllllllllrl wk21lllllllllllllrr
theorem wk21lllllllllllll : SixW25P.Covered 53080 71925 30944 35744 58040 73664 30944 40544 53080 71925 :=
  SixW25P.covered_split0 62502 wk21llllllllllllll wk21lllllllllllllr
theorem wk21llllllllllllr : SixW25P.Covered 53080 71925 35744 40544 58040 73664 30944 40544 53080 71925 :=
  SixW25P.covered_of_walk lbS hbas 12977874174775619858609389625347348130874907545771007854714487886715885667109073861861590626269935719508944536625262963817028732475383739670772549629260485535684722240010138650512824592840845469243908371174 200 53080 71925 35744 40544 58040 73664 30944 40544 53080 71925 692
    (by decide +kernel) (by decide)
theorem wk21llllllllllll : SixW25P.Covered 53080 71925 30944 40544 58040 73664 30944 40544 53080 71925 :=
  SixW25P.covered_split1 35744 wk21lllllllllllll wk21llllllllllllr
theorem wk21lllllllllllr : SixW25P.Covered 53080 71925 30944 40544 58040 73664 30944 40544 71925 90770 :=
  SixW25P.covered_of_walk lbS hbas 590 200 53080 71925 30944 40544 58040 73664 30944 40544 71925 90770 12
    (by decide +kernel) (by decide)
theorem wk21lllllllllll : SixW25P.Covered 53080 71925 30944 40544 58040 73664 30944 40544 53080 90770 :=
  SixW25P.covered_split4 71925 wk21llllllllllll wk21lllllllllllr
theorem wk21llllllllllr : SixW25P.Covered 53080 71925 30944 40544 58040 73664 30944 40544 90770 128460 :=
  SixW25P.covered_of_walk lbS hbas 523576735590133706170781634194334953540158380985783242245214110739293584100437819541859673175302344926213408839704655239422571021826623865138678915557394352284225884818734272221963943109639166610115707028406577335717087962379308347459577164037885571229571239371578433432404663117028988951398387812117663190391486812978781698519039494854108662735806346491035413476274420704459857479331477150214301471859681010 200 53080 71925 30944 40544 58040 73664 30944 40544 90770 128460 1362
    (by decide +kernel) (by decide)
theorem wk21llllllllll : SixW25P.Covered 53080 71925 30944 40544 58040 73664 30944 40544 53080 128460 :=
  SixW25P.covered_split4 90770 wk21lllllllllll wk21llllllllllr
theorem wk21lllllllllr : SixW25P.Covered 53080 71925 30944 40544 58040 73664 30944 40544 128460 203840 :=
  SixW25P.covered_of_walk lbS hbas 713935922 200 53080 71925 30944 40544 58040 73664 30944 40544 128460 203840 37
    (by decide +kernel) (by decide)
theorem wk21lllllllll : SixW25P.Covered 53080 71925 30944 40544 58040 73664 30944 40544 53080 203840 :=
  SixW25P.covered_split4 128460 wk21llllllllll wk21lllllllllr
theorem wk21llllllllr : SixW25P.Covered 71925 90770 30944 40544 58040 73664 30944 40544 53080 203840 :=
  SixW25P.covered_of_walk lbS hbas 13106 200 71925 90770 30944 40544 58040 73664 30944 40544 53080 203840 22
    (by decide +kernel) (by decide)
theorem wk21llllllll : SixW25P.Covered 53080 90770 30944 40544 58040 73664 30944 40544 53080 203840 :=
  SixW25P.covered_split0 71925 wk21lllllllll wk21llllllllr
theorem wk21lllllllr : SixW25P.Covered 90770 128460 30944 40544 58040 73664 30944 40544 53080 203840 :=
  SixW25P.covered_of_walk lbS hbas 8075985227670181011559218 200 90770 128460 30944 40544 58040 73664 30944 40544 53080 203840 92
    (by decide +kernel) (by decide)
theorem wk21lllllll : SixW25P.Covered 53080 128460 30944 40544 58040 73664 30944 40544 53080 203840 :=
  SixW25P.covered_split0 90770 wk21llllllll wk21lllllllr
theorem wk21llllllr : SixW25P.Covered 128460 203840 30944 40544 58040 73664 30944 40544 53080 203840 :=
  SixW25P.covered_of_walk lbS hbas 306 200 128460 203840 30944 40544 58040 73664 30944 40544 53080 203840 12
    (by decide +kernel) (by decide)
theorem wk21llllll : SixW25P.Covered 53080 203840 30944 40544 58040 73664 30944 40544 53080 203840 :=
  SixW25P.covered_split0 128460 wk21lllllll wk21llllllr
theorem wk21lllllr : SixW25P.Covered 53080 203840 30944 40544 73664 89288 30944 40544 53080 203840 :=
  SixW25P.covered_of_walk lbS hbas 0 200 53080 203840 30944 40544 73664 89288 30944 40544 53080 203840 2
    (by decide +kernel) (by decide)
theorem wk21lllll : SixW25P.Covered 53080 203840 30944 40544 58040 89288 30944 40544 53080 203840 :=
  SixW25P.covered_split2 73664 wk21llllll wk21lllllr
theorem wk21llllr : SixW25P.Covered 53080 203840 30944 40544 89288 120537 30944 40544 53080 203840 :=
  SixW25P.covered_of_walk lbS hbas 13430345425430175468247491620184503918560165027169961336094049424495305737116670949245740253860609250515666697079269058568588141936859442835740261538682493155306542459403209316510164327358363473962832694154292486222772725991518061289977282801950587969700206710726028085569169032085039732167561525986548920994 200 53080 203840 30944 40544 89288 120537 30944 40544 53080 203840 1027
    (by decide +kernel) (by decide)
theorem wk21llll : SixW25P.Covered 53080 203840 30944 40544 58040 120537 30944 40544 53080 203840 :=
  SixW25P.covered_split2 89288 wk21lllll wk21llllr
theorem wk21lllr : SixW25P.Covered 53080 203840 30944 40544 120537 183034 30944 40544 53080 203840 :=
  SixW25P.covered_of_walk lbS hbas 744106090471970 200 53080 203840 30944 40544 120537 183034 30944 40544 53080 203840 62
    (by decide +kernel) (by decide)
theorem wk21lll : SixW25P.Covered 53080 203840 30944 40544 58040 183034 30944 40544 53080 203840 :=
  SixW25P.covered_split2 120537 wk21llll wk21lllr
theorem wk21llr : SixW25P.Covered 53080 203840 30944 40544 58040 183034 30944 40544 203840 354601 :=
  SixW25P.covered_of_walk lbS hbas 0 200 53080 203840 30944 40544 58040 183034 30944 40544 203840 354601 2
    (by decide +kernel) (by decide)
theorem wk21ll : SixW25P.Covered 53080 203840 30944 40544 58040 183034 30944 40544 53080 354601 :=
  SixW25P.covered_split4 203840 wk21lll wk21llr
theorem wk21lr : SixW25P.Covered 203840 354601 30944 40544 58040 183034 30944 40544 53080 354601 :=
  SixW25P.covered_of_walk lbS hbas 0 200 203840 354601 30944 40544 58040 183034 30944 40544 53080 354601 2
    (by decide +kernel) (by decide)
theorem wk21l : SixW25P.Covered 53080 354601 30944 40544 58040 183034 30944 40544 53080 354601 :=
  SixW25P.covered_split0 203840 wk21ll wk21lr
theorem wk21r : SixW25P.Covered 53080 354601 30944 40544 183034 308028 30944 40544 53080 354601 :=
  SixW25P.covered_of_walk lbS hbas 0 200 53080 354601 30944 40544 183034 308028 30944 40544 53080 354601 2
    (by decide +kernel) (by decide)
theorem wk21 : SixW25P.Covered 53080 354601 30944 40544 58040 308028 30944 40544 53080 354601 :=
  SixW25P.covered_split2 183034 wk21l wk21r
theorem wk22 : SixW25P.Covered 53080 354601 30944 40544 58040 308028 57472 251564 29720 44064 :=
  SixW25P.covered_of_walk lbS hbas 0 200 53080 354601 30944 40544 58040 308028 57472 251564 29720 44064 2
    (by decide +kernel) (by decide)
theorem wk23 : SixW25P.Covered 53080 354601 30944 40544 58040 308028 57472 251564 53080 354601 :=
  SixW25P.covered_of_walk lbS hbas 4390704159669058085309103560307482325831699905390955349052602729556474561432782070915800293549762048689529143662080023745384937734582894940811111650377625694512272380051781570835733261216626872689888080641880969454851407513477614784612288959079628581602 200 53080 354601 30944 40544 58040 308028 57472 251564 53080 354601 852
    (by decide +kernel) (by decide)
theorem wk24 : SixW25P.Covered 53080 354601 57472 251564 31144 40128 30944 40544 29720 44064 :=
  SixW25P.covered_of_walk lbS hbas 0 200 53080 354601 57472 251564 31144 40128 30944 40544 29720 44064 2
    (by decide +kernel) (by decide)
theorem wk25 : SixW25P.Covered 53080 354601 57472 251564 31144 40128 30944 40544 53080 354601 :=
  SixW25P.covered_of_walk lbS hbas 192096704848371103648703084985351346264456002872099232743534940161114024964889765308086152134339718379642319330706299827954503656061146049317649862986564005546014829911515141506556402473602251605322582667929194771573665003058203713243448059528800300880758046302620147789600287570493007295708318957112363730129202664832978322944300496301821760815670715096922795233209004453455165323544875675616084593766816686550972421511513233611171664138332786445219938303007997594093021677740860997100951222417960517089981249454767019694360293922110853532190071575100869543072520138390341749525664808494374257675204972854990845508053529948940971664532807474508266418856117297601810540440544191494444132478684054222600311495460027103776640824892345555352318594363652636920485185059156927483859469243658595828369697172023894788520324247498754588040123596756523401685792902296760892741357743677618931411875035370718615422241985562930597469197718706145783934314164231433227388972399192633592256875654424718840742968217153591622072385948372309871724452744201827809323180436140478578594937660312469946803137773399476813364672463526548414056218818143899700705586669845597854485769794656131610727030390157088735095670645944525441613883829092719739295851473980340620703253917919299256393163145786236987497395474573239831072835243971955610359834847608658384598286906414109300751884529426291601170180464934126139305184586536037048694766708059783667568981188858839294931504728981724792108179332740128590249146609420728328045005582308176806514865367492144029300277033743934501094005021781405302993156691073429374125747499407888724260973983732355350869702793782900268158952445499526536346149661960181335904687568459596821931123375016404094186299488506017785537247549091608457462812793191369540803952127822291884683222353151368754359925261543814451630755932265884008344999194611941166719118008879254716957377847922 200 53080 354601 57472 251564 31144 40128 30944 40544 53080 354601 6272
    (by decide +kernel) (by decide)
theorem wk26 : SixW25P.Covered 53080 354601 57472 251564 31144 40128 57472 251564 29720 44064 :=
  SixW25P.covered_of_walk lbS hbas 0 200 53080 354601 57472 251564 31144 40128 57472 251564 29720 44064 2
    (by decide +kernel) (by decide)
theorem wk27 : SixW25P.Covered 53080 354601 57472 251564 31144 40128 57472 251564 53080 354601 :=
  SixW25P.covered_of_walk lbS hbas 2874630110313405358074598712433146413809669995747644134575109467927961906703018038768030485812189666249962039014 200 53080 354601 57472 251564 31144 40128 57472 251564 53080 354601 382
    (by decide +kernel) (by decide)
theorem wk28 : SixW25P.Covered 53080 354601 57472 251564 58040 308028 30944 40544 29720 44064 :=
  SixW25P.covered_of_walk lbS hbas 0 200 53080 354601 57472 251564 58040 308028 30944 40544 29720 44064 2
    (by decide +kernel) (by decide)
theorem wk29 : SixW25P.Covered 53080 354601 57472 251564 58040 308028 30944 40544 53080 354601 :=
  SixW25P.covered_of_walk lbS hbas 1483684206618929051092311873227596624186534805271351731191715528969291152963476238491706737430402868964855590449593684438376906803231635758550752792804140769331681503776793218601107359786302632399320916117144247510919449008485614734005828050415478552408473029342935978353114881370738 200 53080 354601 57472 251564 58040 308028 30944 40544 53080 354601 957
    (by decide +kernel) (by decide)
theorem wk30 : SixW25P.Covered 53080 354601 57472 251564 58040 308028 57472 251564 29720 44064 :=
  SixW25P.covered_of_walk lbS hbas 0 200 53080 354601 57472 251564 58040 308028 57472 251564 29720 44064 2
    (by decide +kernel) (by decide)
theorem wk31 : SixW25P.Covered 53080 354601 57472 251564 58040 308028 57472 251564 53080 354601 :=
  SixW25P.covered_of_walk lbS hbas 8158016242811812781172108006 200 53080 354601 57472 251564 58040 308028 57472 251564 53080 354601 117
    (by decide +kernel) (by decide)
theorem bd0_0 : (SixW25P.badOf cover0).getD 0 (0, 0) = (29720, 44064) := by decide +kernel
theorem bd0_1 : (SixW25P.badOf cover0).getD 1 (0, 0) = (53080, 354601) := by decide +kernel
theorem nb0_eq : (SixW25P.badOf cover0).length = 2 := by decide +kernel
theorem bd1_0 : (SixW25P.badOf cover1).getD 0 (0, 0) = (30944, 40544) := by decide +kernel
theorem bd1_1 : (SixW25P.badOf cover1).getD 1 (0, 0) = (57472, 251564) := by decide +kernel
theorem nb1_eq : (SixW25P.badOf cover1).length = 2 := by decide +kernel
theorem bd2_0 : (SixW25P.badOf cover2).getD 0 (0, 0) = (31144, 40128) := by decide +kernel
theorem bd2_1 : (SixW25P.badOf cover2).getD 1 (0, 0) = (58040, 308028) := by decide +kernel
theorem nb2_eq : (SixW25P.badOf cover2).length = 2 := by decide +kernel
theorem bd3_0 : (SixW25P.badOf cover3).getD 0 (0, 0) = (30944, 40544) := by decide +kernel
theorem bd3_1 : (SixW25P.badOf cover3).getD 1 (0, 0) = (57472, 251564) := by decide +kernel
theorem nb3_eq : (SixW25P.badOf cover3).length = 2 := by decide +kernel
theorem bd4_0 : (SixW25P.badOf cover4).getD 0 (0, 0) = (29720, 44064) := by decide +kernel
theorem bd4_1 : (SixW25P.badOf cover4).getD 1 (0, 0) = (53080, 354601) := by decide +kernel
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
  | 0, 0, 1, 0, 0, _, _, _, _, _ => rw [bd0_0, bd1_0, bd2_1, bd3_0, bd4_0]; exact wk4
  | 0, 0, 1, 0, 1, _, _, _, _, _ => rw [bd0_0, bd1_0, bd2_1, bd3_0, bd4_1]; exact wk5
  | 0, 0, 1, 1, 0, _, _, _, _, _ => rw [bd0_0, bd1_0, bd2_1, bd3_1, bd4_0]; exact wk6
  | 0, 0, 1, 1, 1, _, _, _, _, _ => rw [bd0_0, bd1_0, bd2_1, bd3_1, bd4_1]; exact wk7
  | 0, 1, 0, 0, 0, _, _, _, _, _ => rw [bd0_0, bd1_1, bd2_0, bd3_0, bd4_0]; exact wk8
  | 0, 1, 0, 0, 1, _, _, _, _, _ => rw [bd0_0, bd1_1, bd2_0, bd3_0, bd4_1]; exact wk9
  | 0, 1, 0, 1, 0, _, _, _, _, _ => rw [bd0_0, bd1_1, bd2_0, bd3_1, bd4_0]; exact wk10
  | 0, 1, 0, 1, 1, _, _, _, _, _ => rw [bd0_0, bd1_1, bd2_0, bd3_1, bd4_1]; exact wk11
  | 0, 1, 1, 0, 0, _, _, _, _, _ => rw [bd0_0, bd1_1, bd2_1, bd3_0, bd4_0]; exact wk12
  | 0, 1, 1, 0, 1, _, _, _, _, _ => rw [bd0_0, bd1_1, bd2_1, bd3_0, bd4_1]; exact wk13
  | 0, 1, 1, 1, 0, _, _, _, _, _ => rw [bd0_0, bd1_1, bd2_1, bd3_1, bd4_0]; exact wk14
  | 0, 1, 1, 1, 1, _, _, _, _, _ => rw [bd0_0, bd1_1, bd2_1, bd3_1, bd4_1]; exact wk15
  | 1, 0, 0, 0, 0, _, _, _, _, _ => rw [bd0_1, bd1_0, bd2_0, bd3_0, bd4_0]; exact wk16
  | 1, 0, 0, 0, 1, _, _, _, _, _ => rw [bd0_1, bd1_0, bd2_0, bd3_0, bd4_1]; exact wk17
  | 1, 0, 0, 1, 0, _, _, _, _, _ => rw [bd0_1, bd1_0, bd2_0, bd3_1, bd4_0]; exact wk18
  | 1, 0, 0, 1, 1, _, _, _, _, _ => rw [bd0_1, bd1_0, bd2_0, bd3_1, bd4_1]; exact wk19
  | 1, 0, 1, 0, 0, _, _, _, _, _ => rw [bd0_1, bd1_0, bd2_1, bd3_0, bd4_0]; exact wk20
  | 1, 0, 1, 0, 1, _, _, _, _, _ => rw [bd0_1, bd1_0, bd2_1, bd3_0, bd4_1]; exact wk21
  | 1, 0, 1, 1, 0, _, _, _, _, _ => rw [bd0_1, bd1_0, bd2_1, bd3_1, bd4_0]; exact wk22
  | 1, 0, 1, 1, 1, _, _, _, _, _ => rw [bd0_1, bd1_0, bd2_1, bd3_1, bd4_1]; exact wk23
  | 1, 1, 0, 0, 0, _, _, _, _, _ => rw [bd0_1, bd1_1, bd2_0, bd3_0, bd4_0]; exact wk24
  | 1, 1, 0, 0, 1, _, _, _, _, _ => rw [bd0_1, bd1_1, bd2_0, bd3_0, bd4_1]; exact wk25
  | 1, 1, 0, 1, 0, _, _, _, _, _ => rw [bd0_1, bd1_1, bd2_0, bd3_1, bd4_0]; exact wk26
  | 1, 1, 0, 1, 1, _, _, _, _, _ => rw [bd0_1, bd1_1, bd2_0, bd3_1, bd4_1]; exact wk27
  | 1, 1, 1, 0, 0, _, _, _, _, _ => rw [bd0_1, bd1_1, bd2_1, bd3_0, bd4_0]; exact wk28
  | 1, 1, 1, 0, 1, _, _, _, _, _ => rw [bd0_1, bd1_1, bd2_1, bd3_0, bd4_1]; exact wk29
  | 1, 1, 1, 1, 0, _, _, _, _, _ => rw [bd0_1, bd1_1, bd2_1, bd3_1, bd4_0]; exact wk30
  | 1, 1, 1, 1, 1, _, _, _, _, _ => rw [bd0_1, bd1_1, bd2_1, bd3_1, bd4_1]; exact wk31
  | i + 2, _, _, _, _, hi, _, _, _, _ => exact absurd hi (by omega)
  | _, i + 2, _, _, _, _, hi, _, _, _ => exact absurd hi (by omega)
  | _, _, i + 2, _, _, _, _, hi, _, _ => exact absurd hi (by omega)
  | _, _, _, i + 2, _, _, _, _, hi, _ => exact absurd hi (by omega)
  | _, _, _, _, i + 2, _, _, _, _, hi => exact absurd hi (by omega)

theorem cert : ∀ g0 g1 g2 g3 g4 : ℝ, 0 ≤ g0 → 0 ≤ g1 → 0 ≤ g2 → 0 ≤ g3 → 0 ≤ g4 → (SixW25P.cN : ℝ) / SixW25P.SA ≤ SixW25P.G g0 g1 g2 g3 g4 ∨ g4 < g0 :=
  SixW25P.of_check cover0 cover1 cover2 cover3 cover4 354601 251564 308028 251564 354601
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
  | 0, 1 => (26016264 : ℝ) / 100000000
  | 0, 2 => (95829761 : ℝ) / 100000000
  | 0, 3 => (52826981 : ℝ) / 100000000
  | 0, 4 => (100000000 : ℝ) / 100000000
  | 0, 5 => (200000000 : ℝ) / 100000000
  | 1, 2 => (47404723 : ℝ) / 100000000
  | 1, 3 => (4170238 : ℝ) / 100000000
  | 1, 4 => (94346036 : ℝ) / 100000000
  | 1, 5 => (100000000 : ℝ) / 100000000
  | 2, 3 => (53158024 : ℝ) / 100000000
  | 2, 4 => (4170238 : ℝ) / 100000000
  | 2, 5 => (52826981 : ℝ) / 100000000
  | 3, 4 => (47404723 : ℝ) / 100000000
  | 3, 5 => (95829761 : ℝ) / 100000000
  | 4, 5 => (26016264 : ℝ) / 100000000
  | _, _ => 0

/-- the per-gap pressures, over `100000000` -/
def bW : Fin 5 → ℝ
  | 0 => (60390 : ℝ) / 100000000
  | 1 => (85125 : ℝ) / 100000000
  | 2 => (69521 : ℝ) / 100000000
  | 3 => (85125 : ℝ) / 100000000
  | 4 => (60390 : ℝ) / 100000000

def WW : WCert 6 := ⟨aW, bW⟩

theorem aW_0_0 : aW 0 0 = 0 := rfl
theorem aW_0_1 : aW 0 1 = (26016264 : ℝ) / 100000000 := rfl
theorem aW_0_2 : aW 0 2 = (95829761 : ℝ) / 100000000 := rfl
theorem aW_0_3 : aW 0 3 = (52826981 : ℝ) / 100000000 := rfl
theorem aW_0_4 : aW 0 4 = (100000000 : ℝ) / 100000000 := rfl
theorem aW_0_5 : aW 0 5 = (200000000 : ℝ) / 100000000 := rfl
theorem aW_1_0 : aW 1 0 = 0 := rfl
theorem aW_1_1 : aW 1 1 = 0 := rfl
theorem aW_1_2 : aW 1 2 = (47404723 : ℝ) / 100000000 := rfl
theorem aW_1_3 : aW 1 3 = (4170238 : ℝ) / 100000000 := rfl
theorem aW_1_4 : aW 1 4 = (94346036 : ℝ) / 100000000 := rfl
theorem aW_1_5 : aW 1 5 = (100000000 : ℝ) / 100000000 := rfl
theorem aW_2_0 : aW 2 0 = 0 := rfl
theorem aW_2_1 : aW 2 1 = 0 := rfl
theorem aW_2_2 : aW 2 2 = 0 := rfl
theorem aW_2_3 : aW 2 3 = (53158024 : ℝ) / 100000000 := rfl
theorem aW_2_4 : aW 2 4 = (4170238 : ℝ) / 100000000 := rfl
theorem aW_2_5 : aW 2 5 = (52826981 : ℝ) / 100000000 := rfl
theorem aW_3_0 : aW 3 0 = 0 := rfl
theorem aW_3_1 : aW 3 1 = 0 := rfl
theorem aW_3_2 : aW 3 2 = 0 := rfl
theorem aW_3_3 : aW 3 3 = 0 := rfl
theorem aW_3_4 : aW 3 4 = (47404723 : ℝ) / 100000000 := rfl
theorem aW_3_5 : aW 3 5 = (95829761 : ℝ) / 100000000 := rfl
theorem aW_4_0 : aW 4 0 = 0 := rfl
theorem aW_4_1 : aW 4 1 = 0 := rfl
theorem aW_4_2 : aW 4 2 = 0 := rfl
theorem aW_4_3 : aW 4 3 = 0 := rfl
theorem aW_4_4 : aW 4 4 = 0 := rfl
theorem aW_4_5 : aW 4 5 = (26016264 : ℝ) / 100000000 := rfl
theorem aW_5_0 : aW 5 0 = 0 := rfl
theorem aW_5_1 : aW 5 1 = 0 := rfl
theorem aW_5_2 : aW 5 2 = 0 := rfl
theorem aW_5_3 : aW 5 3 = 0 := rfl
theorem aW_5_4 : aW 5 4 = 0 := rfl
theorem aW_5_5 : aW 5 5 = 0 := rfl
theorem bW_0 : bW 0 = (60390 : ℝ) / 100000000 := rfl
theorem bW_1 : bW 1 = (85125 : ℝ) / 100000000 := rfl
theorem bW_2 : bW 2 = (69521 : ℝ) / 100000000 := rfl
theorem bW_3 : bW 3 = (85125 : ℝ) / 100000000 := rfl
theorem bW_4 : bW 4 = (60390 : ℝ) / 100000000 := rfl

theorem WW_B : WW.B = (360551 : ℝ) / 100000000 := by
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

theorem WW_bmin : ∀ r, ((60390 : ℝ) / 100000000) ≤ WW.b r := by
  intro r
  unfold WW
  match r with
  | 0 => show ((60390 : ℝ) / 100000000) ≤ bW 0; norm_num [bW_0]
  | 1 => show ((60390 : ℝ) / 100000000) ≤ bW 1; norm_num [bW_1]
  | 2 => show ((60390 : ℝ) / 100000000) ≤ bW 2; norm_num [bW_2]
  | 3 => show ((60390 : ℝ) / 100000000) ≤ bW 3; norm_num [bW_3]
  | 4 => show ((60390 : ℝ) / 100000000) ≤ bW 4; norm_num [bW_4]

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
theorem cert_WW : ∀ g : Fin (6 - 1) → ℝ, (∀ i, 0 ≤ g i) → (653514 : ℝ) / 100000000 ≤ Fw WW g := by
  intro g hg
  rw [Fw_WW]
  have h := cert_full (g 0) (g 1) (g 2) (g 3) (g 4) (hg 0) (hg 1) (hg 2) (hg 3) (hg 4)
  simp only [SixW25P.cN, SixW25P.SA] at h
  push_cast at h
  exact h

/-- `Phi_w' 6 c 158 B` as an exact rational in `Htheta` -/
theorem Phi_WW : Phi_w' 6 ((653514 : ℝ) / 100000000) 158 ((360551 : ℝ) / 100000000)
    = (15800000000 * Htheta - 55164303) / 15700012358 := by
  unfold Phi_w'
  push_cast
  rw [div_eq_div_iff (by norm_num) (by norm_num)]
  ring

/-- **The 6-point weighted bound, unconditional.** -/
theorem bound_WW :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      ((15800000000 * Htheta - 55164303) / 15700012358 - ε) * (Zeta23.Ncount T (2 * T) : ℝ) ≤ Zeta23.N0simple T (2 * T) := by
  rw [← Phi_WW, ← WW_B]
  exact n_point_bound_w' 6 ((653514 : ℝ) / 100000000) 158 WW (by norm_num) (by norm_num) WW_adm
    (by norm_num : (0 : ℝ) < (60390 : ℝ) / 100000000) WW_bmin (by norm_num) cert_WW (by norm_num)

/-- The candidate rational sits below the proved constant. -/
theorem candidateKappa_le : candidateKappa ≤ (15800000000 * Htheta - 55164303) / 15700012358 := by
  unfold candidateKappa
  rw [le_div_iff₀ (by norm_num : (0:ℝ) < 15700012358)]
  linarith [Htheta_bounds.1]

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
      ≤ ((15800000000 * Htheta - 55164303) / 15700012358 - ε) * (Zeta23.Ncount T (2 * T) : ℝ) :=
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
the original closed form `2 - 1/cMT = Htheta`, through `cStar_one_eq_cMT` and the enclosure of `Htheta`. -/
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


