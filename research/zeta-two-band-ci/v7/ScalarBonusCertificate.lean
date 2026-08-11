/-
Copyright (c) 2026.
SPDX-License-Identifier: Apache-2.0

Seam-independent scalar moment certificate with an additive matrix bonus.

This is the family-generic replacement for applying `Assembly.count_certificate`
to the height-dependent Montgomery--Taylor parameters `P.atD T`.
-/
import Zeta23.Assembly.Certificate

open Filter Asymptotics Topology Real

noncomputable section

namespace Zeta23.GapMatching.ScalarBonusCertificate

open Zeta23
open Zeta23.Assembly

/-- If a scalar trace/Frobenius certificate carries an additive bonus on the
left, the same bonus survives the asymptotic moment argument. -/
theorem count_certificate_with_bonus
    (N tr fr NII B lower bonus : ℝ → ℝ)
    (κ : ℝ)
    (hκ : 0 ≤ κ)
    (h0 : ∀ᶠ T in atTop,
      4 * tr T - fr T - 2 * N T - 3 * NII T
        - B T * (4 + 2 * Real.sqrt (fr T) + B T)
        + bonus T ≤ lower T)
    (hB0 : ∀ᶠ T in atTop, 0 ≤ B T)
    (hBto : Tendsto B atTop (𝓝 0))
    (hNII_o : NII =o[atTop] N)
    (hNtop : Tendsto N atTop atTop)
    (hN0 : ∀ᶠ T in atTop, 0 ≤ N T)
    (htrace : ∀ δ > (0 : ℝ), ∀ᶠ T in atTop,
      (1 - δ) * N T ≤ tr T)
    (hfrob : ∀ δ > (0 : ℝ), ∀ᶠ T in atTop,
      fr T ≤ (κ + δ) * N T) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (2 - κ - ε) * N T + bonus T ≤ lower T := by
  intro ε hε
  set δ : ℝ := ε / 6 with hδdef
  have hδ : 0 < δ := by
    simp only [hδdef]
    linarith
  have hκδ0 : 0 ≤ κ + δ := by linarith

  have hot := err_isLittleO
    (N := N)
    (R₁ := fun _ => 0)
    (R₂ := fun _ => 0)
    (NII := NII)
    (B := B)
    (cl := fun _ => κ + δ)
    (K := κ + δ)
    hNtop
    (isLittleO_zero _ _)
    (isLittleO_zero _ _)
    hNII_o
    hBto
    (Eventually.of_forall fun _ => ⟨hκδ0, le_rfl⟩)

  have hsmall : ∀ᶠ T in atTop,
      3 * NII T
          + B T * (4 + 2 * Real.sqrt ((κ + δ) * N T) + B T)
        ≤ δ * N T := by
    filter_upwards [hot.def hδ, hN0] with T h1 hNT
    simp only [Real.norm_eq_abs, mul_zero, zero_add, add_zero,
      abs_of_nonneg hNT] at h1
    exact (le_abs_self _).trans h1

  have hmain : ∀ᶠ T in atTop,
      (2 - κ - ε) * N T + bonus T ≤ lower T := by
    filter_upwards [h0, hB0, htrace δ hδ, hfrob δ hδ,
      hsmall, hN0]
      with T hA hB htr hfr hsm hNT

    have hA' :
        4 * tr T - fr T - 2 * N T - 3 * NII T
            - B T * (4 + 2 * Real.sqrt (fr T) + B T)
          ≤ lower T - bonus T := by
      linarith

    have hlow := N0star_lower_moment
      (κ := κ)
      (R₁ := δ * N T)
      (R₂ := δ * N T)
      hB hA'
      (by linarith)
      (by linarith)

    rw [show κ * N T + δ * N T = (κ + δ) * N T by ring]
      at hlow

    have hfin :
        (2 - κ - ε) * N T
          = (2 - κ) * N T
              - (4 * (δ * N T) + δ * N T + δ * N T) := by
      simp only [hδdef]
      ring

    rw [hfin]
    linarith [hsm, hlow]

  obtain ⟨T₀, hT₀⟩ := eventually_atTop.mp hmain
  exact ⟨T₀, fun T hT => hT₀ T hT⟩

end Zeta23.GapMatching.ScalarBonusCertificate
