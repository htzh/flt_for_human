/-
  The Kähler differential `omegaOf` attached to a `q`-expansion.

  For a function `f : ℍ → ℂ` and a place `σ : AlgebraicClosure ℚ →+* ℂ`, the
  witness `x` of the equation

      `coeffMap σ (x · thetaL jq) = qExpansion 1 f`

  is unique (the `θ`-multiple of `jq` has nonzero `(-1)`-coefficient), and
  `omegaOf f σ` is the corresponding multiple of the Kähler differential
  `D jq` of `jq` in the function field `modularFunctionFieldBar N`; it is `0` when
  no such witness exists.

  The port's home of the pin's `Definitions/Def_ModularCurve_OmegaOf.lean`
  (pinned `aa2d8b3`, 94 lines), transcribed verbatim and whole, including the two
  `private` helper lemmas `theta_coeffEmb_jq_coeff_neg_one` and
  `thetaL_coeffEmb_jq_ne_zero` that the pin states beside the definition.  The
  pin's four `Definitions/` imports and its two `Theorems/` imports are the port's
  `Defs`/`Period` modules named below (`thetaL`, `theta_coeff`,
  `coeffMap`/`coeffMap_injective`/`coeffEmb` and `jq`/`coeff_jq_neg_one` are all
  already homed; nothing is re-proved); the pin's `import Mathlib` becomes the two
  named mathlib modules.  This is a new definition leaf with no dependents: nothing
  is promoted and nothing is registered.

  References (public mirror, pinned):
  <https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularCurve_OmegaOf.lean>

  spec-pin: Definitions/Def_ModularCurve_OmegaOf.lean
-/

import FLTForHuman.ModularCurve.Defs.ArithmeticGalois
import FLTForHuman.ModularCurve.Defs.QAdicPlace
import FLTForHuman.ModularCurve.Defs.Laurent
import FLTForHuman.ModularCurve.Defs.Jq
import FLTForHuman.ModularCurve.Period.QExpansionDerivative
import Mathlib.RingTheory.Kaehler.Basic
import Mathlib.NumberTheory.ModularForms.QExpansion

set_option autoImplicit false

noncomputable section

open UpperHalfPlane

namespace ModularCurve

variable (N : ℕ) [NeZero N]

open scoped Classical in

def omegaOf (f : ℍ → ℂ) (σ : AlgebraicClosure ℚ →+* ℂ) :
    Ω[modularFunctionFieldBar N⁄AlgebraicClosure ℚ] :=
  if h : ∃ x : modularFunctionFieldBar N,
      coeffMap σ ((x : LaurentSeries (AlgebraicClosure ℚ)) *
          thetaL (AlgebraicClosure ℚ) (coeffEmb (AlgebraicClosure ℚ) jq)) =
        ((qExpansion 1 f : PowerSeries ℂ) : LaurentSeries ℂ)
  then
    h.choose •
      KaehlerDifferential.D (AlgebraicClosure ℚ) (modularFunctionFieldBar N)
        (⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩ :
          modularFunctionFieldBar N)
  else 0

private theorem theta_coeffEmb_jq_coeff_neg_one :
    (thetaL (AlgebraicClosure ℚ) (coeffEmb (AlgebraicClosure ℚ) jq)).coeff (-1 : ℤ) = -1 := by
  rw [thetaL_apply, theta_coeff, coeffEmb_coeff, coeff_jq_neg_one, map_one]
  norm_num

private theorem thetaL_coeffEmb_jq_ne_zero :
    thetaL (AlgebraicClosure ℚ) (coeffEmb (AlgebraicClosure ℚ) jq) ≠ 0 := by
  intro h0
  have h := theta_coeffEmb_jq_coeff_neg_one
  rw [h0] at h
  simp at h

omit [NeZero N] in

theorem omegaOf_witness_unique (f : ℍ → ℂ)
    (σ : AlgebraicClosure ℚ →+* ℂ) {x y : modularFunctionFieldBar N}
    (hx : coeffMap σ ((x : LaurentSeries (AlgebraicClosure ℚ)) *
        thetaL (AlgebraicClosure ℚ) (coeffEmb (AlgebraicClosure ℚ) jq)) =
      ((qExpansion 1 f : PowerSeries ℂ) : LaurentSeries ℂ))
    (hy : coeffMap σ ((y : LaurentSeries (AlgebraicClosure ℚ)) *
        thetaL (AlgebraicClosure ℚ) (coeffEmb (AlgebraicClosure ℚ) jq)) =
      ((qExpansion 1 f : PowerSeries ℂ) : LaurentSeries ℂ)) : x = y := by
  have h1 : (x : LaurentSeries (AlgebraicClosure ℚ)) *
        thetaL (AlgebraicClosure ℚ) (coeffEmb (AlgebraicClosure ℚ) jq)
      = (y : LaurentSeries (AlgebraicClosure ℚ)) *
        thetaL (AlgebraicClosure ℚ) (coeffEmb (AlgebraicClosure ℚ) jq) :=
    coeffMap_injective σ.injective (hx.trans hy.symm)
  have h2 : (x : LaurentSeries (AlgebraicClosure ℚ)) = y :=
    mul_right_cancel₀ thetaL_coeffEmb_jq_ne_zero h1
  exact_mod_cast h2

theorem omegaOf_eq_smul_D_of_coeffMap_eq (f : ℍ → ℂ)
    (σ : AlgebraicClosure ℚ →+* ℂ) {x : modularFunctionFieldBar N}
    (hx : coeffMap σ ((x : LaurentSeries (AlgebraicClosure ℚ)) *
        thetaL (AlgebraicClosure ℚ) (coeffEmb (AlgebraicClosure ℚ) jq)) =
      ((qExpansion 1 f : PowerSeries ℂ) : LaurentSeries ℂ)) :
    omegaOf N f σ =
      x • KaehlerDifferential.D (AlgebraicClosure ℚ) (modularFunctionFieldBar N)
        (⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩ :
          modularFunctionFieldBar N) := by
  have h : ∃ z : modularFunctionFieldBar N,
      coeffMap σ ((z : LaurentSeries (AlgebraicClosure ℚ)) *
          thetaL (AlgebraicClosure ℚ) (coeffEmb (AlgebraicClosure ℚ) jq)) =
        ((qExpansion 1 f : PowerSeries ℂ) : LaurentSeries ℂ) := ⟨x, hx⟩
  unfold omegaOf
  rw [dite_eq_left h, omegaOf_witness_unique N f σ h.choose_spec hx]

theorem omegaOf_eq_zero_of_not_exists (f : ℍ → ℂ)
    (σ : AlgebraicClosure ℚ →+* ℂ)
    (h : ¬ ∃ x : modularFunctionFieldBar N,
        coeffMap σ ((x : LaurentSeries (AlgebraicClosure ℚ)) *
            thetaL (AlgebraicClosure ℚ) (coeffEmb (AlgebraicClosure ℚ) jq)) =
          ((qExpansion 1 f : PowerSeries ℂ) : LaurentSeries ℂ)) :
    omegaOf N f σ = 0 := by
  unfold omegaOf
  rw [dite_eq_right h]

end ModularCurve

end
