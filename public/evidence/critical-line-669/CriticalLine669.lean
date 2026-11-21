import DistinctBound
import Main

/-!
Exact asymptotic critical-line bounds obtained by applying Alpöge's published
RH theorem to the distinct-zero results of Alpöge and Furman. We use the
counting functions defined in Zeta23. The denominator counts multiplicities.
-/
noncomputable section
namespace CriticalLine669

theorem onLineCount (a b : ℝ) :
    Zeta23.N0star a b = Zeta23.Ndist a b :=
  (Zeta23.RH_implies_all_on_line _root_.riemannHypothesis a b).2

/-- In every window the exact loss from discarding distinct off-line zeros is zero. -/
theorem offLineLoss (a b : ℝ) : Zeta23.Ndist a b - Zeta23.N0star a b = 0 := by
  rw [onLineCount, Nat.sub_self]

/-- A bound for distinct zeros anywhere transfers to the critical line. -/
private theorem transfer {a b k : ℝ} {ε : ℝ}
    (h : (k - ε) * (Zeta23.Ncount a b : ℝ) ≤ Zeta23.Ndist a b) :
    (k - ε) * (Zeta23.Ncount a b : ℝ) ≤ Zeta23.N0star a b := by
  rw [onLineCount]
  exact h

theorem dyadic {k : ℝ} (hk : k ≤ Zeta23.ThmD.GD 1) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (k - ε) * (Zeta23.Ncount T (2 * T) : ℝ) ≤ Zeta23.N0star T (2 * T) := by
  intro ε hε
  obtain ⟨T₀, h⟩ := Zeta23.ThmD.thmD₀_dist_mult ε hε
  refine ⟨T₀, fun T hT => transfer ?_⟩
  exact (mul_le_mul_of_nonneg_right (sub_le_sub_right hk ε) (Nat.cast_nonneg _)).trans (h T hT)

theorem cumulative {k : ℝ} (hk : k ≤ Zeta23.ThmD.GD 1) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (k - ε) * (Zeta23.Ncount 0 T : ℝ) ≤ Zeta23.N0star 0 T := by
  intro ε hε
  obtain ⟨T₀, h⟩ := Zeta23.ThmD.thmD₀_dist_mult_cumulative ε hε
  refine ⟨T₀, fun T hT => transfer ?_⟩
  exact (mul_le_mul_of_nonneg_right (sub_le_sub_right hk ε) (Nat.cast_nonneg _)).trans (h T hT)

theorem dyadic_669 :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      ((669 / 800 : ℝ) - ε) * (Zeta23.Ncount T (2 * T) : ℝ) ≤ Zeta23.N0star T (2 * T) :=
  dyadic RiemannRHBridge.rational_le_GD_one

theorem cumulative_669 :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      ((669 / 800 : ℝ) - ε) * (Zeta23.Ncount 0 T : ℝ) ≤ Zeta23.N0star 0 T :=
  cumulative RiemannRHBridge.rational_le_GD_one

end CriticalLine669
end

#print axioms CriticalLine669.offLineLoss
#print axioms CriticalLine669.dyadic_669
#print axioms CriticalLine669.cumulative_669
