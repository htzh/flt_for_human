/-
The EDS level of the multiplication-formula bridge.

Ported from `Definitions/Def_WeierstrassCurve_EDSEngine.lean`, pinned at
`aa2d8b3` (the generic elliptic-sequence sections). See `logs/card-torsion-port.md` for why this
material is needed and what mathlib v4.34.0 does and does not supply.

mathlib's `IsEllipticNet.atom` / `atomRel` / `rel` are *definitionally* FLT's
`addMulSub` / `rel₄` / `net`, and mathlib's `normEDS`, `preNormEDS`, `complEDS`,
`complEDS₂` cover the corresponding FLT names, so those are referenced rather
than redefined. The `map_*` lemmas and the universal (`ℤ[B, C, D]`) EDS are
ported because mathlib has no analogue.
-/
import FLTForHuman.Elliptic.DivisionPolynomial

open scoped Polynomial Polynomial.Bivariate
open Polynomial
open WeierstrassCurve

namespace FLTForHuman.Elliptic

variable {R S : Type*} [CommRing R] [CommRing S]

section Map

variable (f : R →+* S)

lemma map_invarNum (u : ℤ → R) (s m : ℤ) :
    f (invarNum u s m) = invarNum (f ∘ u) s m := by
  simp only [invarNum, map_add, map_mul, map_pow, Function.comp]

lemma map_invarDenom (u : ℤ → R) (s m : ℤ) :
    f (invarDenom u s m) = invarDenom (f ∘ u) s m := by
  simp only [invarDenom, map_mul, Function.comp_apply]

end Map

/-- The three parameters of a normalised EDS, as indeterminates. -/
inductive Param : Type
  | B : Param
  | C : Param
  | D : Param

open MvPolynomial

/-- The universal normalised EDS over `ℤ[B, C, D]`. -/
noncomputable def universalNormEDS : ℤ → MvPolynomial Param ℤ :=
  normEDS (X Param.B) (X Param.C) (X Param.D)

/-- Specialising the universal EDS recovers `normEDS b c d`. -/
lemma normEDS_eq_aeval (b c d : R) :
    normEDS b c d = (aeval (Param.rec b c d) <| universalNormEDS ·) := by
  simp_rw [universalNormEDS, map_normEDS, MvPolynomial.aeval_X]

end FLTForHuman.Elliptic
