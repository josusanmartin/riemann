/-
Instantiate the exported D-window ramp theorem in the normalized overlap shape
used by the one-band path.
-/
import Zeta23.GapMatching.DWindowRampAPI
import Zeta23.GapMatching.DWindowFiniteGridApprox
import Zeta23.GapMatching.OneBandSharpProfileAPI

noncomputable section

namespace Zeta23.GapMatching.DWindowRampProfileBridge

open Zeta23
open Zeta23.AdmWindow
open Zeta23.GapMatching.DWindowRampAPI
open Zeta23.GapMatching.DWindowFiniteGridApprox
open Zeta23.GapMatching.OneBandSharpProfileAPI

/-- Exported ramp comparison in normalized-separation coordinates. -/
theorem abs_normalizedFullOverlap_sub_sharpProfile_le
    {v : ℝ → ℝ} {L w c tau tau' : ℝ}
    (hW : AdmWindow v L w c)
    (hL : 0 < L) :
    |normalizedFullOverlap v L tau tau'
        - sharpProfile (L * (tau' - tau) / (2 * Real.pi))|
      ≤ 12 * w / L := by
  have h := rampComparison
  exact?

end Zeta23.GapMatching.DWindowRampProfileBridge
