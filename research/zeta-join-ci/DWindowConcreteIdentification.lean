/-
Concrete D-window parameter package for the generic finite Poisson comparison.
The exact raw-window arity and theorem argument order are inferred by pinned
Lean from the stable ParamsD API.
-/
import Zeta23.GapMatching.ParamsDStableAPI
import Zeta23.GapMatching.GramToFinitePoisson

noncomputable section

namespace Zeta23.GapMatching.DWindowConcreteIdentification

open Zeta23
open Zeta23.AdmWindow
open Zeta23.GapMatching.ParamsDStableAPI
open Zeta23.GapMatching.GramToFinitePoisson

variable {Z : ZeroConfig} {P : Params} {T : ℝ}

/-- All concrete ingredients required by the generic finite/full theorem. -/
structure Package (Z : ZeroConfig) (P : Params) (T : ℝ) where
  v : ℝ → ℝ
  L w c : ℝ
  L_eq : L = P.L T
  identification : Identification (Z := Z) (P := P) (T := T) v L
  admissible : AdmWindow v L w c
  average_pos : 0 < av v L
  scale_pos : 0 < dScale P T
  L_pos : 0 < L

/-- The fixed D-window parameter construction supplies the package. -/
theorem exists_package
    (Z : ZeroConfig) (P : Params) (T : ℝ)
    (hT : 2 * Real.pi < T) :
    Nonempty (Package Z P T) := by
  have hv := vD
  have hadm := admWindowD
  have hsample := sampleD
  have hgrid := gridD
  have hscale := scaleD
  have hscalePos := scalePosD
  have hLPos := LPosD
  exact?

end Zeta23.GapMatching.DWindowConcreteIdentification
