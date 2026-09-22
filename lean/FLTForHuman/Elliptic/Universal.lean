/-
The universal Weierstrass curve, used to prove coefficient-identities generically.

Ported from the FLT project, pinned at `aa2d8b3`:

  Definitions/Def_WeierstrassCurve_EDSEngine.lean, section `PortEllSequenceUniversal`
  https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_WeierstrassCurve_EDSEngine.lean

The trick: the coefficients `a₁ … a₆` become indeterminates `A₁ … A₆`, so an
identity proved for the universal curve transfers to any curve by specialising
the indeterminates to its coefficients. mathlib has no analogue of this layer,
so it is ported; the statements carry over verbatim, relocated from
`WeierstrassCurve`/`Univ` to `FLTForHuman.Elliptic`/`Univ` so they cannot clash
with a future mathlib addition.

Adaptations:
* `Affine.CoordinateRing.algebraMap_injective'` is not in mathlib v4.34.0, so it
  is kept (as `algebraMap_injective'`).
* the redundant `instance : CommRing Poly` re-declaration is dropped.
-/
import Mathlib.AlgebraicGeometry.EllipticCurve.Jacobian.Point
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.Polynomial.Bivariate
import Mathlib.RingTheory.Localization.FractionRing
import FLTForHuman.Elliptic.Basic

noncomputable section

open scoped Polynomial Polynomial.Bivariate
open scoped FLTForHuman.Elliptic
open WeierstrassCurve

namespace FLTForHuman.Elliptic

/-- The five coefficients of the universal Weierstrass curve. -/
inductive Coeff : Type
  | A₁ : Coeff
  | A₂ : Coeff
  | A₃ : Coeff
  | A₄ : Coeff
  | A₆ : Coeff

/-- `algebraMap R W.CoordinateRing` is injective. Not in mathlib v4.34.0. -/
lemma algebraMap_injective' {R : Type*} [CommRing R] (W : Affine R) :
    Function.Injective (algebraMap R W.CoordinateRing) := by
  have h : Function.Injective (algebraMap (Polynomial R) W.CoordinateRing) :=
    (injective_iff_map_eq_zero _).mpr fun p hp ↦ And.left <|
      WeierstrassCurve.Affine.CoordinateRing.smul_basis_eq_zero (W' := W) (q := 0) <| by
        rw [WeierstrassCurve.Affine.CoordinateRing.smul,
          WeierstrassCurve.Affine.CoordinateRing.smul, mul_one, Polynomial.C_0, map_zero, zero_mul,
          add_zero]
        exact hp
  exact h.comp Polynomial.C_injective

namespace Univ

open Coeff
open MvPolynomial (X)

/-- The universal Weierstrass curve over `ℤ`. -/
def curve : Affine (MvPolynomial Coeff ℤ) :=
  { a₁ := X A₁, a₂ := X A₂, a₃ := X A₃, a₄ := X A₄, a₆ := X A₆ }

lemma Δ_curve_ne_zero : curve.Δ ≠ 0 := fun h ↦ by
  simp_rw [Δ, b₂, b₄, b₆, b₈, curve] at h
  apply_fun MvPolynomial.eval (Coeff.rec 0 0 0 0 1) at h
  simp at h

/-- Bivariate polynomials in the universal coefficients. -/
abbrev Poly : Type := (MvPolynomial Coeff ℤ)[X][Y]

protected abbrev Ring : Type := curve.CoordinateRing

protected abbrev Field : Type := FractionRing Univ.Ring

lemma Poly.two_ne_zero : (2 : Poly) ≠ 0 :=
  Polynomial.C_ne_zero.mpr <| Polynomial.C_ne_zero.mpr fun h ↦ two_ne_zero' (α := ℤ) <|
    MvPolynomial.C_injective _ _ <| by rwa [← MvPolynomial.C_0] at h

/-- Evaluation of a polynomial in the universal coefficients at the universal
point; the map to the fraction field of the coordinate ring. -/
def polyToField : Poly →+* Univ.Field :=
  (algebraMap Univ.Ring _).comp <| AdjoinRoot.mk _

lemma polyToField_apply (p : Poly) :
    polyToField p = algebraMap Univ.Ring _ (AdjoinRoot.mk _ p) := rfl

lemma algebraMap_field_eq_comp :
    algebraMap (MvPolynomial Coeff ℤ) Univ.Field = polyToField.comp (algebraMap _ _) := rfl

lemma algebraMap_ring_eq_comp :
    algebraMap (MvPolynomial Coeff ℤ) Univ.Ring = (AdjoinRoot.mk _).comp (algebraMap _ _) :=
  rfl

@[simp] lemma polyToField_polynomial : polyToField curve.polynomial = 0 := by
  rw [polyToField_apply, AdjoinRoot.mk_self, map_zero]

lemma algebraMap_field_injective :
    Function.Injective (algebraMap (MvPolynomial Coeff ℤ) Univ.Field) :=
  (IsFractionRing.injective Univ.Ring Univ.Field).comp (algebraMap_injective' _)

/-- The universal curve over the fraction field of its coordinate ring, with a
distinguished point. -/
abbrev pointedCurve : WeierstrassCurve Univ.Field :=
  WeierstrassCurve.baseChange curve Univ.Field

instance : pointedCurve.IsElliptic where
  isUnit := isUnit_iff_ne_zero.mpr <| by
    simpa only [pointedCurve, WeierstrassCurve.baseChange, map_Δ, map_ne_zero_iff _ algebraMap_field_injective]
      using Δ_curve_ne_zero

open Polynomial in
lemma equation_point : pointedCurve.toAffine.Equation (polyToField (C X)) (polyToField Y) := by
  -- Route: `evalEval` of a coefficient-mapped polynomial is `eval₂`, whose
  -- coefficient map is `eval₂RingHom (algebraMap …) (polyToField (C X)) = algebraMap _ _`
  -- because `polyToField (C X)` *is* the image of the coefficient variable `X`.
  -- That turns the goal into `aeval (polyToField Y) curve.polynomial = 0`, and
  -- `polyToField Y` is `algebraMap _ _ (root curve.polynomial)`, so the
  -- `AdjoinRoot` identity `aeval (root f) f = 0` (`aeval_eq` + `mk_self`) finishes.
  rw [Affine.Equation, pointedCurve, WeierstrassCurve.baseChange, Affine.map_polynomial]
  rw [← Polynomial.eval₂_eval₂RingHom_apply (algebraMap (MvPolynomial Coeff ℤ) Univ.Field)
        (polyToField (C X)) (polyToField Y) curve.polynomial]
  have hx : polyToField (C X) = algebraMap (MvPolynomial Coeff ℤ)[X] Univ.Field X := by
    rw [polyToField_apply, AdjoinRoot.mk_C, ← AdjoinRoot.algebraMap_eq,
      IsScalarTower.algebraMap_apply (MvPolynomial Coeff ℤ)[X] Univ.Ring Univ.Field]
  have hmap : Polynomial.eval₂RingHom (algebraMap (MvPolynomial Coeff ℤ) Univ.Field)
        (polyToField (C X)) = algebraMap (MvPolynomial Coeff ℤ)[X] Univ.Field := by
    rw [hx]
    refine Polynomial.ringHom_ext (fun a => ?_) ?_
    · simp only [Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C, ← Polynomial.C_eq_algebraMap,
        IsScalarTower.algebraMap_apply (MvPolynomial Coeff ℤ) (MvPolynomial Coeff ℤ)[X] Univ.Field]
    · simp only [Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]
  rw [hmap]
  rw [← Polynomial.aeval_def]
  have hy : polyToField (Y : Poly) =
      algebraMap Univ.Ring Univ.Field (AdjoinRoot.root curve.polynomial) := by
    rw [polyToField_apply, AdjoinRoot.mk_X]
  rw [hy, Polynomial.aeval_algebraMap_apply Univ.Field (AdjoinRoot.root curve.polynomial)
        curve.polynomial,
      AdjoinRoot.aeval_eq, AdjoinRoot.mk_self, map_zero]

open Polynomial Affine in

/-- The universal point `(x, y)` on the universal curve. -/
def affinePoint : curve⟮Univ.Field⟯ :=
  .some (polyToField (C X)) (polyToField Y)
    ((pointedCurve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero
      (by simpa only [pointedCurve, WeierstrassCurve.baseChange, map_Δ, map_ne_zero_iff _ algebraMap_field_injective]
        using Δ_curve_ne_zero)).mp equation_point)

/-- The universal point, as a Jacobian point. -/
def jacobianPoint : Jacobian.Point (WeierstrassCurve.baseChange curve Univ.Field) :=
  Jacobian.Point.fromAffine affinePoint

open Polynomial (CC)

@[simp] lemma pointedCurve_a₁ : pointedCurve.a₁ = polyToField (CC curve.a₁) := rfl
@[simp] lemma pointedCurve_a₂ : pointedCurve.a₂ = polyToField (CC curve.a₂) := rfl
@[simp] lemma pointedCurve_a₃ : pointedCurve.a₃ = polyToField (CC curve.a₃) := rfl
@[simp] lemma pointedCurve_a₄ : pointedCurve.a₄ = polyToField (CC curve.a₄) := rfl
@[simp] lemma pointedCurve_a₆ : pointedCurve.a₆ = polyToField (CC curve.a₆) := rfl

abbrev curvePoly : WeierstrassCurve Poly := WeierstrassCurve.baseChange curve Poly

abbrev curveRing : WeierstrassCurve Univ.Ring :=
  WeierstrassCurve.baseChange curve Univ.Ring

abbrev curveField : WeierstrassCurve Univ.Field :=
  WeierstrassCurve.baseChange curve Univ.Field

lemma curveField_eq : curveField = pointedCurve := rfl

end Univ

/-- The cuspidal cubic `y² = x³`, used to detect the zero ring: evaluating the
universal coefficient expressions there must not collapse to `0 = 1`. -/
def cusp : Affine ℤ := { a₁ := 0, a₂ := 0, a₃ := 0, a₄ := 0, a₆ := 0 }

lemma cusp_equation_one_one : cusp.Equation 1 1 := by
  simp [Affine.Equation, Affine.polynomial, cusp, Polynomial.evalEval]

open Univ

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

/-- Specialise the universal coefficients to those of `W`. -/
def specialize : MvPolynomial Coeff ℤ →+* R :=
  (MvPolynomial.aeval <| Coeff.rec W.a₁ W.a₂ W.a₃ W.a₄ W.a₆).toRingHom

lemma map_specialize : WeierstrassCurve.map Univ.curve (specialize W) = W := by
  simp [specialize, curve, map]

namespace Univ

variable (x y : R)

open Polynomial (eval₂RingHom) in

def polyEval : Poly →+* R := eval₂RingHom (eval₂RingHom (specialize W) x) y

open Polynomial in
lemma polyEval_apply (p : Poly) :
    polyEval W x y p = (p.map <| mapRingHom (specialize W)).evalEval x y :=
  eval₂_eval₂RingHom_apply _ _ _ _

variable {W x y} (eqn : Affine.Equation W x y)

open Polynomial in

def ringEval : Univ.Ring →+* R :=
  AdjoinRoot.lift (eval₂RingHom (specialize W) x) y <| by
    simp_rw [← coe_eval₂RingHom, eval₂RingHom_eval₂RingHom, RingHom.comp_apply, coe_mapRingHom]
    rw [← Affine.map_polynomial]
    simpa only [Affine.map, map_specialize, Affine.Equation, evalEval, coe_evalRingHom] using eqn

lemma ringEval_mk (p : Poly) : ringEval eqn (AdjoinRoot.mk _ p) = polyEval W x y p :=
  AdjoinRoot.lift_mk _ p

lemma ringEval_comp_mk : (ringEval eqn).comp (AdjoinRoot.mk _) = polyEval W x y :=
  RingHom.ext (ringEval_mk eqn)

lemma polyEval_comp_eq_specialize : (polyEval W x y).comp (algebraMap _ _) = specialize W := by
  ext <;> simp [polyEval]

lemma ringEval_comp_eq_specialize : (ringEval eqn).comp (algebraMap _ _) = specialize W := by
  rw [algebraMap_ring_eq_comp, ← RingHom.comp_assoc, ringEval_comp_mk, polyEval_comp_eq_specialize]

protected lemma Field.two_ne_zero : (2 : Univ.Field) ≠ 0 := by
  rw [← map_ofNat (algebraMap Univ.Ring _), map_ne_zero_iff _ (IsFractionRing.injective _ _)]
  intro h
  replace h := congr(ringEval cusp_equation_one_one $h)
  rw [map_ofNat, map_zero] at h
  cases h

lemma curveRing_map_ringEval : curveRing.map (ringEval eqn) = W := by
  rw [curveRing, WeierstrassCurve.baseChange, WeierstrassCurve.map_map, ringEval_comp_eq_specialize, map_specialize]

end Univ

end FLTForHuman.Elliptic
