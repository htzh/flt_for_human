/-
The pin's `Integral` block of `Definitions/Def_ModularCurve_X1.lean` (lines 37–63).

The `IsIntegralQExp` `def` itself is already public at
`FLTForHuman/ModularForms/WeightOne/Gamma0Integral.lean:98` and is imported, not
restated. This module lands the five lemmas the pin proves beside it, which the
`P4`/`P6` integral-`q`-expansion witnesses of `X1/FunctionField.lean` consume.

FLT provenance, pinned `aa2d8b3`:
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularCurve_X1.lean
-/
import FLTForHuman.ModularForms.WeightOne.Gamma0Integral

set_option autoImplicit false

noncomputable section

open UpperHalfPlane ModularForm
open scoped MatrixGroups ModularForm

namespace ModularCurve

section Integral

theorem IsIntegralQExp.coeff {f : ℍ → ℂ} {p : PowerSeries ℤ} (h : IsIntegralQExp f p) (n : ℕ) :
    ((PowerSeries.coeff n p : ℤ) : ℂ) = PowerSeries.coeff n (qExpansion 1 f) := by
  rw [← h, PowerSeries.coeff_map, eq_intCast]

theorem isIntegralQExp_iff {f : ℍ → ℂ} {p : PowerSeries ℤ} :
    IsIntegralQExp f p ↔ ∀ n : ℕ, ((PowerSeries.coeff n p : ℤ) : ℂ) =
      PowerSeries.coeff n (qExpansion 1 f) := by
  refine ⟨fun h n => h.coeff n, fun h => ?_⟩
  ext n
  rw [PowerSeries.coeff_map, eq_intCast]
  exact h n

theorem IsIntegralQExp.unique {f : ℍ → ℂ} {p p' : PowerSeries ℤ} (h : IsIntegralQExp f p)
    (h' : IsIntegralQExp f p') : p = p' := by
  ext n
  have := (h.coeff n).trans (h'.coeff n).symm
  exact_mod_cast this

theorem isIntegralQExp_one : IsIntegralQExp (1 : ℍ → ℂ) 1 := by
  rw [IsIntegralQExp, map_one, qExpansion_one]

theorem isIntegralQExp_zero : IsIntegralQExp (0 : ℍ → ℂ) 0 := by
  rw [IsIntegralQExp, map_zero, qExpansion_zero]

end Integral

end ModularCurve

end
