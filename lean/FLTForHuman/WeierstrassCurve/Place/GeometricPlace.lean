/-
The geometric place map of an affine Weierstrass curve: the map
`geomPlaceOfPoint` sending a rational point to the place of its equation (or the
infinite place at the origin), its degree, injectivity, and — over an
algebraically closed field in characteristic-free generality — surjectivity, the
resulting bijection `geomPointEquivPlace` between rational points and places of
the function field, the induced geometric divisor sum `geomDivisorSum`, and the
`GeomAbelTheorem` carrier asserting that principal divisors are exactly those
with zero geometric sum.

Statements are transcribed verbatim from the pinned FLT `aa2d8b3`,
`P2M/Sol/S_WeierstrassCurve_Affine_exists_genusOnePlaceGate_isCentred_and_abelTheorem.lean`
lines 924–1035 (only proof bodies are adapted to mathlib `v4.34.0`).  The
preceding `InfinitePlace` class (pin line 913) and `isElliptic_Δ_ne_zero` (pin
line 1005) are already ported in `WeierstrassCurve/Place/Dictionary.lean` and
imported here; the RR-space, class-group/unit-ideal/Abel blocks and the headline
are out of scope.

Imports `FLTForHuman.WeierstrassCurve.Place.Dictionary` (which supplies
`InfinitePlace`, `isElliptic_Δ_ne_zero`, `placeOfEquation` and its degree and
injectivity, `isFinitePlace_placeOfEquation`, and
`isFinitePlace_iff_exists_placeOfEquation`) and, transitively, the divisor API
(`AlgebraicCurve.Divisor`, `Divisor.degree`, `Divisor.IsPrincipal`).

Reference (public mirror, pinned):
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_WeierstrassCurve_Affine_exists_genusOnePlaceGate_isCentred_and_abelTheorem.lean#L924-L1035>
-/
import FLTForHuman.WeierstrassCurve.Place.Dictionary

set_option autoImplicit false
set_option linter.style.haveILetI false

noncomputable section

open AlgebraicCurve WeierstrassCurve WeierstrassCurve.Affine

open scoped WeierstrassCurve.Affine

namespace WeierstrassCurve.Affine

universe u

section GeomPlaceOfPoint

variable {F : Type u} [Field F] {W : Affine F}
variable [IsDedekindDomain W.CoordinateRing]

def geomPlaceOfPoint [InfinitePlace W] : W.Point → AlgebraicCurve.Place F W.FunctionField
  | .zero => InfinitePlace.place
  | .some x y h => placeOfEquation (W := W) (x := x) (y := y) h.left

@[scoped simp]
theorem geomPlaceOfPoint_zero [InfinitePlace W] :
    geomPlaceOfPoint (.zero : W.Point) = InfinitePlace.place := rfl

@[scoped simp]
theorem geomPlaceOfPoint_some [InfinitePlace W] {x y : F} (h : W.Nonsingular x y) :
    geomPlaceOfPoint (.some x y h) = placeOfEquation h.left := rfl

theorem deg_geomPlaceOfPoint [InfinitePlace W] (P : W.Point) : (geomPlaceOfPoint P).deg = 1 := by
  cases P with
  | zero => exact InfinitePlace.deg_eq_one
  | some x y h => exact deg_placeOfEquation h.left

theorem geomPlaceOfPoint_injective [InfinitePlace W] :
    Function.Injective (geomPlaceOfPoint (W := W)) := by
  intro P Q h
  cases P with
  | zero => cases Q with
    | zero => rfl
    | some xQ yQ hQ =>
        rw [geomPlaceOfPoint_zero, geomPlaceOfPoint_some] at h
        exact absurd (h ▸ InfinitePlace.not_isFinitePlace) (not_not.mpr
          (isFinitePlace_placeOfEquation hQ.left))
  | some xP yP hP => cases Q with
    | zero =>
        rw [geomPlaceOfPoint_some, geomPlaceOfPoint_zero] at h
        exact absurd (h ▸ isFinitePlace_placeOfEquation hP.left)
          InfinitePlace.not_isFinitePlace
    | some xQ yQ hQ =>
        rw [geomPlaceOfPoint_some, geomPlaceOfPoint_some] at h
        obtain ⟨hx, hy⟩ := placeOfEquation_injective hP.left hQ.left h
        subst hx
        subst hy
        rfl

theorem geomPlaceOfPoint_surjective [InfinitePlace W] [IsAlgClosed F] (hΔ : W.Δ ≠ 0) :
    Function.Surjective (geomPlaceOfPoint (W := W)) := by
  intro v
  by_cases hv : IsFinitePlace v
  · obtain ⟨x, y, h, rfl⟩ := (isFinitePlace_iff_exists_placeOfEquation v).mp hv
    exact ⟨.some x y ((W.equation_iff_nonsingular_of_Δ_ne_zero hΔ).mp h), rfl⟩
  · exact ⟨.zero, (InfinitePlace.eq_of_not_isFinitePlace v hv).symm⟩

end GeomPlaceOfPoint

section GeomPointEquivPlace

variable {F : Type u} [Field F] [DecidableEq F] {W : Affine F}
variable [IsAlgClosed F] [W.IsElliptic] [InfinitePlace W]

-- `geomPlaceOfPoint` needs the Dedekind instance on the coordinate ring, which
-- the pin supplies through its `scoped instance`; the port's copy of that
-- instance lives in `WeierstrassCurve.Affine.CoordinateRing`, so it is supplied
-- explicitly here (the checker diffs statement text, where section variables do
-- not appear, so this matches the pin's public surface).
variable [IsDedekindDomain W.CoordinateRing]

def geomPointEquivPlace : W.Point ≃ AlgebraicCurve.Place F W.FunctionField :=
  Equiv.ofBijective geomPlaceOfPoint
    ⟨geomPlaceOfPoint_injective, geomPlaceOfPoint_surjective isElliptic_Δ_ne_zero⟩

omit [DecidableEq F] in
@[scoped simp]
theorem geomPointEquivPlace_apply (P : W.Point) : geomPointEquivPlace P = geomPlaceOfPoint P := rfl

omit [DecidableEq F] in
@[scoped simp]
theorem geomPointEquivPlace_symm_geomPlaceOfPoint (P : W.Point) :
    geomPointEquivPlace.symm (geomPlaceOfPoint (W := W) P) = P :=
  geomPointEquivPlace.symm_apply_apply P

def geomDivisorSum : AlgebraicCurve.Divisor F W.FunctionField →+ W.Point :=
  Finsupp.liftAddHom fun v => zmultiplesHom W.Point (geomPointEquivPlace.symm v)

@[scoped simp]
theorem geomDivisorSum_single (v : AlgebraicCurve.Place F W.FunctionField) (n : ℤ) :
    geomDivisorSum (Finsupp.single v n) = n • (geomPointEquivPlace (W := W)).symm v :=
  Finsupp.liftAddHom_apply_single _ v n

variable (W) in

class GeomAbelTheorem : Prop where

  isPrincipal_iff_geomDivisorSum_eq_zero :
    ∀ D : AlgebraicCurve.Divisor F W.FunctionField, Divisor.degree D = 0 →
      (Divisor.IsPrincipal D ↔ geomDivisorSum D = 0)

end GeomPointEquivPlace

end WeierstrassCurve.Affine
