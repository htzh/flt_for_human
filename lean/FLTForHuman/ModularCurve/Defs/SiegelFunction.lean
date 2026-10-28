/-
The Siegel unit `siegelFun`, the definition layer of the `SiegelUnit` rows of the
`ModularCurve` ready shelf (MC-5 / story M4): the `SL(2, ℤ)`-slash invariance
`ModularCurve.siegelFun_specialLinearGroup_smul` and the differentiability pair
`ModularCurve.SiegelUnit.differentiableOn_siegelFun`.

Transcribed verbatim from FLT's `Definitions/Def_ModularCurve_SiegelFunction.lean`
(pinned `aa2d8b3`, 32 lines), whole: the two declarations the pin has. The pin's
file imports only mathlib, so this module is the whole definition layer: the
q-product *engine* (`jtp_term`, `theta_eq`) that the two rows' proofs need is the
rows' own prelude and does not live here.

FLT provenance, pinned `aa2d8b3`:
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularCurve_SiegelFunction.lean

spec-pin: Definitions/Def_ModularCurve_SiegelFunction.lean
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic

set_option autoImplicit false

noncomputable section

namespace ModularCurve

/-- The Siegel unit at level `N` and index `(r, s)`, as the pin's infinite product. -/
def siegelFun (N : ℕ) (r s : ℤ) (z : ℂ) : ℂ :=
  -Complex.exp (Real.pi * Complex.I * (s : ℂ) * ((r : ℂ) - (N : ℂ)) / (N : ℂ) ^ 2) *
    Complex.exp (Real.pi * Complex.I * (((r : ℂ) / (N : ℂ)) ^ 2 - (r : ℂ) / (N : ℂ) + 1 / 6) * z) *
    (1 - Complex.exp (2 * Real.pi * Complex.I * ((r : ℂ) * z + (s : ℂ)) / (N : ℂ))) *
    ∏' n : ℕ, ((1 - Complex.exp (2 * Real.pi * Complex.I * z) ^ (n + 1) *
        Complex.exp (2 * Real.pi * Complex.I * ((r : ℂ) * z + (s : ℂ)) / (N : ℂ))) *
      (1 - Complex.exp (2 * Real.pi * Complex.I * z) ^ (n + 1) *
        (Complex.exp (2 * Real.pi * Complex.I * ((r : ℂ) * z + (s : ℂ)) / (N : ℂ)))⁻¹))

/-- The defining equation of `siegelFun`. -/
theorem siegelFun_def (N : ℕ) (r s : ℤ) (z : ℂ) :
    siegelFun N r s z =
      -Complex.exp (Real.pi * Complex.I * (s : ℂ) * ((r : ℂ) - (N : ℂ)) / (N : ℂ) ^ 2) *
        Complex.exp (Real.pi * Complex.I * (((r : ℂ) / (N : ℂ)) ^ 2 - (r : ℂ) / (N : ℂ) + 1 / 6) * z) *
        (1 - Complex.exp (2 * Real.pi * Complex.I * ((r : ℂ) * z + (s : ℂ)) / (N : ℂ))) *
        ∏' n : ℕ, ((1 - Complex.exp (2 * Real.pi * Complex.I * z) ^ (n + 1) *
            Complex.exp (2 * Real.pi * Complex.I * ((r : ℂ) * z + (s : ℂ)) / (N : ℂ))) *
          (1 - Complex.exp (2 * Real.pi * Complex.I * z) ^ (n + 1) *
            (Complex.exp (2 * Real.pi * Complex.I * ((r : ℂ) * z + (s : ℂ)) / (N : ℂ)))⁻¹)) :=
  rfl

end ModularCurve

end
