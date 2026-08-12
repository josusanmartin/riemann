export const SUBMISSION_STARTER_PATH = "/templates/Solution.lean";

export const submissionStarterSource = `/-
Riemann.fail one-file submission starter

The submission form supplies the exact numerator and denominator. The verifier
then generates currentRecordKappa and candidateKappa for this file.

Before submitting:
1. Keep all three theorem names and statements exactly as written.
2. Replace every sorry with a complete proof. Any remaining sorry is rejected.
3. Put any helper declarations and additional imports in this same file.
4. Do not assume the Riemann hypothesis or add new axioms.

Rate limit: three admitted uploads per GitHub account per UTC calendar day,
resetting at 00:00 UTC. Once an upload enters the verification queue, it uses
one slot even if it later ends in a compilation error, comparison or kernel
rejection, timeout, or infrastructure failure. Validate locally first whenever
possible.
-/

/- Trusted statement generated for one Riemann.fail candidate. -/
import ChallengeDeps.CandidateSpec

noncomputable section

/-- The submitted bound is strictly larger than the current formal record. -/
theorem candidate_strict_improvement :
    currentRecordKappa < candidateKappa := by
  sorry

/-- The candidate proves a larger unconditional critical-line proportion on dyadic windows. -/
theorem candidate_critical_line_bound :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (candidateKappa - ε) * (Ncount T (2 * T) : ℝ) ≤ N0star T (2 * T) := by
  sorry

/-- The same unconditional bound in cumulative windows. -/
theorem candidate_critical_line_bound_cumulative :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (candidateKappa - ε) * (Ncount 0 T : ℝ) ≤ N0star 0 T := by
  sorry

end
`;
