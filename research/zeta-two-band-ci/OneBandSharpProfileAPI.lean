/-
Stable API surface for the mechanically generated one-band sharp-profile proof.
The source generator appends `exportedSharpProfile` and
`exportedProfileStepCertificate` to `OneBandSharpProfile.lean` before this
module is compiled.
-/
import Zeta23.GapMatching.OneBandSharpProfile

noncomputable section

namespace Zeta23.GapMatching.OneBandSharpProfileAPI

open Zeta23.GapMatching.OneBandSharpProfile

/-- The exact sharp profile used by the one-band certificate. -/
abbrev sharpProfile := exportedSharpProfile

/-- The assembled local profile-step theorem, with its full inferred type. -/
abbrev profileStepCertificate := exportedProfileStepCertificate

end Zeta23.GapMatching.OneBandSharpProfileAPI
