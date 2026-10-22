/-
The pin's `Integral` block of `Definitions/Def_ModularCurve_X1.lean` (lines 37–63):
the predicate `IsIntegralQExp`, together with the five lemmas the pin proves beside
it.

This is a **definition-layer** module and imports mathlib alone.  `IsIntegralQExp`
names only `UpperHalfPlane.qExpansion` and `PowerSeries ℤ`/`ℂ`, so nothing of the
port stands below it — which is what the whole `q`-expansion function-field layer
(`X1/Defs.lean`, `JqIntegralRatios.lean`, and the 23 `ModularCurve` modules above
them) needs.

The predicate used to be stated inside
`FLTForHuman/ModularForms/WeightOne/Gamma0Integral.lean` — the home of its *first*
consumer, whose third headline's statement names it — so every consumer of
`intFormRatiosC`/`qExpFunctionFieldC` reached a 2,245-line analytic weight-one
module to read three lines.  It moved here on 2026-10-21, at the pin's own
statement, so that the pin's `Integral` block is homed whole; `Gamma0Integral`
imports this module rather than declaring the predicate.

FLT provenance, pinned `aa2d8b3`:
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularCurve_X1.lean

spec-pin: Definitions/Def_ModularCurve_X1.lean
-/
import Mathlib.NumberTheory.ModularForms.QExpansion
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Data.Int.Cast.Lemmas

set_option autoImplicit false

noncomputable section

open UpperHalfPlane ModularForm
open scoped MatrixGroups ModularForm

namespace ModularCurve

section Integral

/-- The pin's `Def_ModularCurve_X1.IsIntegralQExp`: integrality of a `q`-expansion
against an integral power series. -/
def IsIntegralQExp (f : ℍ → ℂ) (p : PowerSeries ℤ) : Prop :=
  p.map (Int.castRingHom ℂ) = qExpansion 1 f

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
