/-
  The Weierstrass `ζ`-function and the lattice sum `eisensteinG1` used in the
  construction of the Eisenstein series of weight `1`.

  Transcribed verbatim from `Definitions/Def_EisensteinSeries_WeierstrassZeta.lean`
  (pinned `aa2d8b3`, 14 lines). The mathematics is math/018 §3.
-/
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.E2.Defs
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

namespace EisensteinSeries

noncomputable def weierstrassZeta (τ : UpperHalfPlane) (z : ℂ) : ℂ :=
  1 / z + ∑' v : Fin 2 → ℤ, if v = 0 then 0 else
    (1 / (z - ((v 0 : ℂ) * τ + v 1)) + 1 / ((v 0 : ℂ) * τ + v 1) + z / ((v 0 : ℂ) * τ + v 1) ^ 2)

noncomputable def eisensteinG1 (N : ℕ) (v : Fin 2 → ℤ) (τ : UpperHalfPlane) : ℂ :=
  1 / (N : ℂ) *
    (weierstrassZeta τ (((v 0 : ℂ) * τ + v 1) / N) -
      ((v 0 : ℂ) * ((τ : ℂ) * G2 τ - 2 * Real.pi * Complex.I) + (v 1 : ℂ) * G2 τ) / N)

end EisensteinSeries
