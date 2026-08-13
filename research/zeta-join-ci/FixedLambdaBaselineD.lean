/-
Stable rational lower bound for the fixed-lambda Montgomery--Taylor density
used by the one-band path.
-/
import Zeta23.GapMatching.OneBandSharpProfileExtraAPI
import Zeta23.GapMatching.OneBandLiveFixedSimpleNumerics

noncomputable section

namespace Zeta23.GapMatching.FixedLambdaBaselineD

open Zeta23.GapMatching.OneBandSharpProfileExtraAPI
open Zeta23.GapMatching.OneBandLiveFixedSimpleNumerics

/-- The generated fixed-window certificate proves the rational baseline. -/
theorem distinctLower_le_HD_lambda :
    distinctLower ≤ Zeta23.ThmD.HD lambda := by
  have h := baselineCertificate
  exact?

end Zeta23.GapMatching.FixedLambdaBaselineD
