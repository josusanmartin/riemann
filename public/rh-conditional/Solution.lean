import ChallengeDeps.CandidateSpec

noncomputable section

theorem candidate_strict_improvement :
    currentRecordKappa < candidateKappa := by
  sorry

theorem candidate_critical_line_bound_of_RH (hRH : RiemannHypothesis) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (candidateKappa - ε) * (Ncount T (2 * T) : ℝ) ≤ N0star T (2 * T) := by
  sorry

theorem candidate_critical_line_bound_cumulative_of_RH (hRH : RiemannHypothesis) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (candidateKappa - ε) * (Ncount 0 T : ℝ) ≤ N0star 0 T := by
  sorry

end
