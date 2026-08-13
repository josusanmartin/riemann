/-
Copyright (c) 2026.
SPDX-License-Identifier: Apache-2.0

Height-dependent Montgomery--Taylor seam for the one-band finite-state bonus.
-/
import Zeta23.GapMatching.DNormalizedMoments
import Zeta23.GapMatching.ScalarBonusCertificate
import Zeta23.GapMatching.GapMatchingZetaSeam
import Zeta23.GapMatching.OneBandPotentialSafeNumerics
import Zeta23.ThmD.Final
import Zeta23.ThmD.Mult

open Filter Asymptotics Topology Real RHLinalg

noncomputable section

namespace Zeta23.GapMatching.OneBandGapMatchingD

open Zeta23
open Zeta23.Assembly
open Zeta23.ThmD
open Zeta23.GapMatching.DNormalizedMoments
open Zeta23.GapMatching.GapMatchingZetaSeam
open Zeta23.GapMatching.ScalarBonusCertificate
open Zeta23.GapMatching.OneBandPotentialSafeNumerics

private abbrev Acoef : ℝ := A
private abbrev Bcoef : ℝ := B

/-- Matching core for the actual height-dependent D-window. -/
def MatchingCoreDAt
    (Z : ZeroConfig) (P : Params) (T energy : ℝ) : Prop :=
  MatchingCoreAt Z (P.atD T) T energy

/-- Minimal eventual one-band bonus. -/
structure EventualOneBandBonusD
    (Z : ZeroConfig) (P : Params)
    (energy error : ℝ → ℝ) : Prop where
  core : ∀ᶠ T in atTop, MatchingCoreDAt Z P T (energy T)
  gain : ∀ᶠ T in atTop,
    Acoef * (Z.N0s T (2 * T) : ℝ)
      - Bcoef * (Z.N T (2 * T) : ℝ) - error T ≤ 2 * energy T
  error_small : error =o[atTop]
    (fun T => (Z.N T (2 * T) : ℝ))

/-- The existing fixed-parameter matching seam, specialized correctly to
`P.atD T`. -/
theorem seamA_mult2D_with_matching
    {Z : ZeroConfig} {P : Params} {T energy theta0 : ℝ}
    (hT : 0 ≤ T)
    (hcore : MatchingCoreDAt Z P T energy)
    (hTail : TailInputs Z (P.atD T) T theta0)
    (ha : 0 < (P.atD T).a T)
    (hL : 0 < (P.atD T).L T) :
    4 * rtrace ((P.atD T).hat T (Z.Gz (P.atD T) T))
        - frobSq ((P.atD T).hat T (Z.Gz (P.atD T) T))
        - 2 * (Z.N T (2 * T) : ℝ)
        - 3 * (NII Z T : ℝ)
        - theta0 / ((P.atD T).a T * (P.atD T).L T)
            * (4
              + 2 * Real.sqrt
                  (frobSq ((P.atD T).hat T (Z.Gz (P.atD T) T)))
              + theta0 / ((P.atD T).a T * (P.atD T).L T))
        + 2 * energy
      ≤ (Z.N0s T (2 * T) : ℝ) := by
  exact seamA_mult2_with_matching hT hcore hTail ha hL

/-- Multiplicity-aware Theorem D with an additive gap-matching bonus. -/
theorem thmD_mult2_gap_abstract
    (Z : ZeroConfig) (H : PaperInputs Z)
    (P : Params) (hP : P.Valid) (hlam : P.lam < 1)
    (aT bT JT trG trG2 : ℝ → ℝ)
    (hTr : TracesBoundsD P aT bT JT trG trG2
      (fun T => (Z.N T (2 * T) : ℝ)))
    {c : ℝ} (hc0 : 0 < c)
    (hc : Tendsto
      (fun T => cRatio (P.lam1 T) (aT T) (bT T) (JT T))
      atTop (𝓝 c))
    (ha : ∀ᶠ T in atTop, 1 / 2 ≤ aT T ∧ aT T ≤ 1)
    (energy error theta0 : ℝ → ℝ)
    (hgap : EventualOneBandBonusD Z P energy error)
    (hTail : ∀ᶠ T in atTop,
      TailInputs Z (P.atD T) T (theta0 T))
    (hθ0 : ∃ C : ℝ, ∀ᶠ T in atTop,
      theta0 T ≤ C * l T * T ^ (P.lam / 2 - 1))
    (hNII : ∃ C : ℝ, ∀ᶠ T in atTop,
      (NII Z T : ℝ) ≤ C * Real.sqrt T * l T)
    (hGzGp : ∀ᶠ T in atTop,
      Z.Gz (P.atD T) T = (P.atD T).Gp T)
    (hId : ∀ᶠ T in atTop,
      (P.atD T).trGtilde T = trG T ∧
      (P.atD T).trGtildeSq T = trG2 T ∧
      (P.atD T).a T = aT T)
    (hcalE : Tendsto P.calE atTop (𝓝 0)) :
    ∀ epsilon > 0, ∃ T0 : ℝ, ∀ T ≥ T0,
      (((2 - c⁻¹) - Bcoef) / (1 - Acoef) - epsilon)
          * (Z.N T (2 * T) : ℝ)
        ≤ (Z.N0s T (2 * T) : ℝ) := by
  have hlam0 := hP.lam_pos
  obtain ⟨Ctheta, htheta⟩ := hθ0
  obtain ⟨CII, hII⟩ := hNII

  set N : ℝ → ℝ := fun T => (Z.N T (2 * T) : ℝ) with hNdef
  set trHat : ℝ → ℝ :=
    fun T => (aT T * P.L T)⁻¹ * trG T
    with htrHat
  set frHat : ℝ → ℝ :=
    fun T => ((aT T * P.L T)⁻¹) ^ 2 * trG2 T
    with hfrHat
  set Btail : ℝ → ℝ :=
    fun T => theta0 T / (aT T * P.L T)
    with hBtaildef

  have hNtop : Tendsto N atTop atTop := tendsto_N_atTop Z H.RvM
  have hN0 : ∀ᶠ T in atTop, 0 ≤ N T :=
    Eventually.of_forall fun _ => Nat.cast_nonneg _

  have hseam : ∀ᶠ T in atTop,
      4 * trHat T - frHat T - 2 * N T
          - 3 * (NII Z T : ℝ)
          - Btail T * (4 + 2 * Real.sqrt (frHat T) + Btail T)
          + 2 * energy T
        ≤ (Z.N0s T (2 * T) : ℝ) := by
    filter_upwards [hgap.core, hTail, hGzGp, hId, ha,
      eventually_ge_atTop (0 : ℝ), eventually_l_pos]
      with T hcore hTl hGG hid haT hT0 hlT
    obtain ⟨hidtr, hidfr, hida⟩ := hid
    have hapos : 0 < aT T := by linarith [haT.1]
    have haposD : 0 < (P.atD T).a T := by
      rw [hida]
      exact hapos
    have hLpos : 0 < P.L T := by
      simp only [Params.L]
      positivity
    have hLD : 0 < (P.atD T).L T := by simpa using hLpos

    have hA := seamA_mult2D_with_matching
      hT0 hcore hTl haposD hLD

    have hrt :
        rtrace ((P.atD T).hat T (Z.Gz (P.atD T) T))
          = (aT T * P.L T)⁻¹ * trG T := by
      rw [rtrace_hat, hGG, rtrace_tilde_Gp, hidtr, hida]
      rfl
    have hfr :
        frobSq ((P.atD T).hat T (Z.Gz (P.atD T) T))
          = ((aT T * P.L T)⁻¹) ^ 2 * trG2 T := by
      rw [frobSq_hat, hGG, frobSq_tilde_Gp, hidfr, hida]
      rfl
    have haL :
        (P.atD T).a T * (P.atD T).L T = aT T * P.L T := by
      rw [hida]
      rfl

    rw [hrt, hfr, haL] at hA
    simpa only [hNdef, htrHat, hfrHat, hBtaildef] using hA

  have hB0 : ∀ᶠ T in atTop, 0 ≤ Btail T := by
    filter_upwards [hTail, ha, eventually_l_pos]
      with T hTl haT hlT
    have hapos : 0 < aT T := by linarith [haT.1]
    have hLpos : 0 < P.L T := by
      simp only [Params.L]
      positivity
    simp only [hBtaildef]
    exact div_nonneg hTl.theta_nonneg (mul_pos hapos hLpos).le

  have hBto : Tendsto Btail atTop (𝓝 0) := by
    have hup : Tendsto
        (fun T =>
          2 * |Ctheta|
            * (l T * T ^ (P.lam / 2 - 1) / P.L T))
        atTop (𝓝 0) := by
      simpa using
        (tendsto_theta_over_L P hP.lam_pos hlam.le).const_mul
          (2 * |Ctheta|)

    refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
      tendsto_const_nhds hup ?_ ?_
    · filter_upwards [hTail, ha, eventually_l_pos]
        with T hTl haT hlT
      have hLpos : 0 < P.L T := by
        simp only [Params.L]
        positivity
      have hapos : 0 < aT T := by linarith [haT.1]
      simp only [hBtaildef]
      exact div_nonneg hTl.theta_nonneg (mul_pos hapos hLpos).le
    · filter_upwards [hTail, ha, eventually_l_pos, htheta,
        eventually_gt_atTop (0 : ℝ)]
        with T hTl haT hlT hthetaT hTpos
      have hLpos : 0 < P.L T := by
        simp only [Params.L]
        positivity
      have hapos : 0 < aT T := by linarith [haT.1]
      have hq :
          0 ≤ l T * T ^ (P.lam / 2 - 1) / P.L T := by
        positivity
      simp only [hBtaildef]
      rw [div_le_iff₀ (mul_pos hapos hLpos)]
      calc
        theta0 T
            ≤ Ctheta * l T * T ^ (P.lam / 2 - 1) := hthetaT
        _ ≤ |Ctheta| * l T * T ^ (P.lam / 2 - 1) := by
              gcongr
              exact le_abs_self _
        _ = |Ctheta|
              * (l T * T ^ (P.lam / 2 - 1) / P.L T)
              * P.L T := by field_simp
        _ ≤ (2 * |Ctheta|
              * (l T * T ^ (P.lam / 2 - 1) / P.L T))
              * (aT T * P.L T) := by
              have heq :
                  |Ctheta|
                      * (l T * T ^ (P.lam / 2 - 1) / P.L T)
                      * P.L T
                    = (2 * |Ctheta|
                        * (l T * T ^ (P.lam / 2 - 1) / P.L T))
                        * (1 / 2 * P.L T) := by ring
              rw [heq]
              gcongr
              exact haT.1

  have hNII_o :
      (fun T => (NII Z T : ℝ)) =o[atTop] N := by
    have hO :
        (fun T => (NII Z T : ℝ))
          =O[atTop] (fun T => Real.sqrt T * l T) := by
      refine IsBigO.of_bound CII ?_
      filter_upwards [hII, eventually_l_pos]
        with T hT hlT
      rw [Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg (Nat.cast_nonneg _),
        abs_of_nonneg (by positivity)]
      simpa [mul_assoc] using hT
    exact hO.trans_isLittleO
      (isLittleO_N_of_isLittleO_Tl Z H.RvM
        isLittleO_sqrt_mul_l_Tl)

  obtain ⟨htrace, hfrob⟩ := normalized_moment_bounds
    Z H P hP hlam aT bT JT trG trG2 hTr hc0 hc ha hcalE

  have hcert := ScalarBonusCertificate.count_certificate_with_bonus
    N trHat frHat (fun T => (NII Z T : ℝ)) Btail
    (fun T => (Z.N0s T (2 * T) : ℝ))
    (fun T => 2 * energy T)
    c⁻¹ (inv_nonneg.mpr hc0.le)
    hseam hB0 hBto hNII_o hNtop hN0
    (by simpa only [hNdef, htrHat] using htrace)
    (by simpa only [hNdef, hfrHat] using hfrob)

  have hden : Acoef < 1 := parameter_ranges.2.1
  have hden' : Acoef * 1 < 1 := by simpa using hden
  have hAne : Acoef ≠ 0 := ne_of_gt parameter_ranges.1
  have hgain : ∀ᶠ T in atTop,
      Acoef * (1 * (Z.N0s T (2 * T) : ℝ)
        - 2 * (Bcoef / (2 * Acoef)) * N T)
        - error T ≤ 2 * energy T := by
    filter_upwards [hgap.gain] with T hT
    have hid :
        Acoef * (1 * (Z.N0s T (2 * T) : ℝ)
          - 2 * (Bcoef / (2 * Acoef)) * N T)
          = Acoef * (Z.N0s T (2 * T) : ℝ) - Bcoef * N T := by
      field_simp [hAne]
    rw [hid]
    simpa only [hNdef] using hT

  exact fixed_point_certificate
    (N := N)
    (lower := fun T => (Z.N0s T (2 * T) : ℝ))
    (bonus := fun T => 2 * energy T)
    (error := error)
    (delta := 2 - c⁻¹)
    (beta := Acoef)
    (span := 1)
    (lam := Bcoef / (2 * Acoef))
    hN0 hcert hgain hgap.error_small hden'

/-- Concrete D-window specialization for an abstract zero configuration. -/
theorem thmD_gap_lam_abstract
    (Z : ZeroConfig) (H : PaperInputs Z)
    (P : Params) (hP : P.Valid) (hlam : P.lam < 1)
    (energy error : ℝ → ℝ)
    (hgap : EventualOneBandBonusD Z P energy error) :
    ∀ epsilon > 0, ∃ T0 : ℝ, ∀ T ≥ T0,
      ((HD P.lam - Bcoef) / (1 - Acoef) - epsilon)
          * (Z.N T (2 * T) : ℝ)
        ≤ (Z.N0s T (2 * T) : ℝ) := by
  have hLoc : LocalHypsCoreDEventually P :=
    localHypsCoreD_eventually hP
  have hTr := tracesBoundsD_concrete (Z := Z) hP H hLoc
  have hc := tendsto_cRatio_concrete hP Z
  have hc0 := cStar_pos hP.lam_pos hP.lam_le_one
  have ha : ∀ᶠ T in atTop,
      1 / 2 ≤ (concreteDataD P Z).aT T ∧
      (concreteDataD P Z).aT T ≤ 1 :=
    (concreteFactsD hP H hLoc).ab_range.mono fun T h =>
      ⟨h.1.trans h.2.1, h.2.2.1⟩
  obtain ⟨theta0, hTail, htheta0⟩ :=
    eventually_tailPackageD Z H hP
  obtain ⟨A0, hA0, hlocal⟩ := H.RvM.local_count
  have hNII := Tail.eventually_NII_le Z hA0 hlocal
  have hGzGp := eventually_GzGpD Z H hP
  have hId : ∀ᶠ T in atTop,
      (P.atD T).trGtilde T = (concreteDataD P Z).trG T ∧
      (P.atD T).trGtildeSq T = (concreteDataD P Z).trG2 T ∧
      (P.atD T).a T = (concreteDataD P Z).aT T :=
    Eventually.of_forall fun T =>
      ⟨Params.atD_trGtilde T hP,
        Params.atD_trGtildeSq T hP,
        Params.atD_a T hP⟩
  have hcalE := calE_tendsto_zero P hP.lam_pos
    hP.lam_le_one (zero_le_one.trans hP.one_le_w)

  have h := thmD_mult2_gap_abstract
    Z H P hP hlam
    (concreteDataD P Z).aT
    (concreteDataD P Z).bT
    (concreteDataD P Z).JT
    (concreteDataD P Z).trG
    (concreteDataD P Z).trG2
    hTr hc0 hc ha energy error theta0 hgap
    hTail htheta0 hNII hGzGp hId hcalE
  simpa only [HD, one_div] using h

/-- Zeta specialization at any fixed `0 < lam < 1`. -/
theorem thmD_gap_lam_eventual
    {lam0 : ℝ} (h0 : 0 < lam0) (h1 : lam0 < 1)
    (energy error : ℝ → ℝ)
    (hgap : EventualOneBandBonusD zetaZeroConfig
      (paramsOf stdProfile lam0) energy error) :
    ∀ epsilon > 0, ∃ T0 : ℝ, ∀ T ≥ T0,
      ((HD lam0 - Bcoef) / (1 - Acoef) - epsilon)
          * (Ncount T (2 * T) : ℝ)
        ≤ N0simple T (2 * T) := by
  have hP := paramsOf_valid taperProfile_stdProfile h0 h1.le
  exact thmD_gap_lam_abstract
    zetaZeroConfig paperInputs_zeta
    (paramsOf stdProfile lam0) hP h1
    energy error hgap

end Zeta23.GapMatching.TwoBandGapMatchingD
