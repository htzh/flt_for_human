/-
  Layer 0b — the polynomial datum attached to `N`.

  `ModularPolynomialData N` bundles the modular polynomial `Φ` with the four
  facts the splitting input needs about it: monic, of degree `ψ(N)`, and
  vanishing at `j(q ^ N)` under evaluation at `jq`. It is small and kept apart
  from the function fields because it is the *type* of the `Φ_p` input rather
  than a field.

  FLT provenance, pinned `aa2d8b3`:
  `Definitions/Def_ModularCurve_X0.lean` lines 215–232.
  https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularCurve_X0.lean

  `Polynomial` is mathlib's; `ModularPolynomialData` is FLT's name, verbatim.
  Assumes `dedekindPsi`, `evalAtJ` and `jqN` from `FLTForHuman.ModularCurve.Defs.Jq`.
-/
import FLTForHuman.ModularCurve.Defs.Jq

set_option autoImplicit false

noncomputable section

open PowerSeries HahnSeries IntermediateField

namespace ModularCurve

/-- The modular polynomial datum at `N`: a monic `Φ ∈ ℤ[X][Y]` of degree
`ψ(N)`, vanishing at `j(q ^ N)` when `Y` is evaluated at `jq`. The splitting
input is the assertion that such a `Φ` exists, is symmetric, and is
irreducible. -/
structure ModularPolynomialData (N : ℕ) [NeZero N] : Type where

  Φ : Polynomial (Polynomial ℤ)

  monic : Φ.Monic

  natDegree_eq : Φ.natDegree = dedekindPsi N

  eval_eq_zero : Φ.eval₂ evalAtJ (jqN N) = 0

/-- The `N = 1` datum: `Φ = X - Y`, which vanishes at `jq` and `jqN 1 = jq`. -/
def modularPolynomialDataOne : ModularPolynomialData 1 where
  Φ := Polynomial.X - Polynomial.C Polynomial.X
  monic := Polynomial.monic_X_sub_C _
  natDegree_eq := by simp
  eval_eq_zero := by
    simp only [Polynomial.eval₂_sub, Polynomial.eval₂_X, Polynomial.eval₂_C, jqN_one,
      evalAtJ_X, sub_self]

end ModularCurve

end
