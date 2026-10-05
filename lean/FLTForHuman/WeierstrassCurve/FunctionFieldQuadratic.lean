/-
  The quadratic equation of the Weierstrass function field.

  For a Weierstrass curve `W` over a field `F`, the function field `W.FunctionField`
  is generated over `RatFunc F` by the image `yCoord` of `CoordinateRing.mk W Y`,
  which satisfies the Weierstrass quadratic
  `Y² + (a₁X + a₃)Y = X³ + a₂X² + a₄X + a₆`. This module carries that vocabulary:
  the `F[X]`-algebra map `polyToFunctionField`, the induced `RatFunc F`-algebra
  structure, `yCoord`, the quadratic `weierstrassQuadratic`, and the integrality of
  `yCoord` over `RatFunc F`.

  Transcribed verbatim from `Definitions/Def_WeierstrassCurve_FunctionFieldQuadratic.lean`
  (pinned `aa2d8b3`, 150 lines); mathlib-only, exactly as the pin. The lemmas it
  rests on (`smul_basis_eq_zero`, `smul_basis_mul_Y`, `YClass_ne_zero`) are
  mathlib's `Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point`, so the pin's
  `Def_EllipticCurve_ValuationInfty` basis re-development is not needed here.

  This module is also the shared home of the pin's *generic-point bridge*
  (`yGen`, `polyToFunctionField_eq_aeval`,
  `equation_map_polyToFunctionField_yGen`, `transcendental_polyToFunctionField_X`).
  The pin inlines that four-declaration block into every `S_` file that needs it
  (ten files in the Vélu cluster); writing it once here is the H0 home of the
  Vélu port plan.

  The `placeOfEquation`/`IsFinitePlace`/`ord` dictionary and the class-group block
  that the pin's `S_WeierstrassCurve_Affine_hasPrincipalDivisors_functionField.lean`
  also carries are **not** ported: they are a shallow, wide API surface whose
  consumers (`IsogenyEndDatum`, `velu*`, `genusOnePlaceGate`, …) will pull in what
  they need when they are taken. This module is the capstone's whole prerequisite.
-/
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.RingTheory.Localization.FractionRing

set_option autoImplicit false

noncomputable section

open Polynomial

open scoped Polynomial.Bivariate

namespace WeierstrassCurve.Affine

open CoordinateRing

variable {F : Type*} [Field F] {W : Affine F}

def polyToFunctionField (W : Affine F) : F[X] →+* W.FunctionField :=
  (algebraMap W.CoordinateRing W.FunctionField).comp (algebraMap F[X] W.CoordinateRing)

theorem polyToFunctionField_apply (p : F[X]) :
    polyToFunctionField W p
      = algebraMap W.CoordinateRing W.FunctionField (algebraMap F[X] W.CoordinateRing p) := rfl

theorem algebraMap_smul_one (p : F[X]) :
    algebraMap W.CoordinateRing W.FunctionField (p • (1 : W.CoordinateRing))
      = polyToFunctionField W p := by
  rw [polyToFunctionField_apply, smul, mul_one]
  rfl

theorem polyToFunctionField_injective : Function.Injective (polyToFunctionField W) := by
  intro p q h
  rw [polyToFunctionField_apply, polyToFunctionField_apply] at h
  have h2 := IsFractionRing.injective W.CoordinateRing W.FunctionField h
  have h0 : (p - q) • (1 : W.CoordinateRing) + (0 : F[X]) • CoordinateRing.mk W Y = 0 := by
    rw [zero_smul, add_zero, sub_smul, ← Algebra.algebraMap_eq_smul_one,
      ← Algebra.algebraMap_eq_smul_one, h2, sub_self]
  exact sub_eq_zero.mp (smul_basis_eq_zero h0).1

theorem polyToFunctionField_C (c : F) :
    polyToFunctionField W (C c) = algebraMap F W.FunctionField c := by
  rw [polyToFunctionField_apply,
    show algebraMap F[X] W.CoordinateRing (C c) = algebraMap F W.CoordinateRing c from
      (IsScalarTower.algebraMap_apply F F[X] W.CoordinateRing c).symm]
  exact (IsScalarTower.algebraMap_apply F W.CoordinateRing W.FunctionField c).symm

theorem polyToFunctionField_ne_zero {p : F[X]} (hp : p ≠ 0) :
    polyToFunctionField W p ≠ 0 := by
  intro h
  exact hp (polyToFunctionField_injective (by simpa using h))

theorem algebraMap_smul_basis (p q : F[X]) :
    algebraMap W.CoordinateRing W.FunctionField
        (p • (1 : W.CoordinateRing) + q • CoordinateRing.mk W Y)
      = polyToFunctionField W p + polyToFunctionField W q
          * algebraMap W.CoordinateRing W.FunctionField (CoordinateRing.mk W Y) := by
  rw [map_add, algebraMap_smul_one, smul, map_mul, polyToFunctionField_apply]
  rfl

theorem Y_image_ne_zero :
    algebraMap W.CoordinateRing W.FunctionField (CoordinateRing.mk W Y) ≠ 0 := by
  have h1 : (CoordinateRing.mk W Y) ≠ 0 := by
    have h2 := YClass_ne_zero (W' := W) 0
    simpa [YClass] using h2
  exact (map_ne_zero_iff _ (IsFractionRing.injective W.CoordinateRing W.FunctionField)).mpr h1

theorem algebraMap_polynomial_eq_polyToFunctionField :
    algebraMap F[X] W.FunctionField = polyToFunctionField W :=
  IsScalarTower.algebraMap_eq F[X] W.CoordinateRing W.FunctionField

theorem algebraMap_polynomial_injective :
    Function.Injective (algebraMap F[X] W.FunctionField) := by
  rw [algebraMap_polynomial_eq_polyToFunctionField]
  exact polyToFunctionField_injective

variable (W) in

def ratFuncToFunctionField : RatFunc F →+* W.FunctionField :=
  IsFractionRing.lift algebraMap_polynomial_injective

@[simp]
theorem ratFuncToFunctionField_algebraMap (p : F[X]) :
    ratFuncToFunctionField W (algebraMap F[X] (RatFunc F) p)
      = algebraMap F[X] W.FunctionField p :=
  IsFractionRing.lift_algebraMap algebraMap_polynomial_injective p

instance : Algebra (RatFunc F) W.FunctionField :=
  (ratFuncToFunctionField W).toAlgebra

instance : IsScalarTower F[X] (RatFunc F) W.FunctionField :=
  IsScalarTower.of_algebraMap_eq fun p => (ratFuncToFunctionField_algebraMap p).symm

instance : IsScalarTower F (RatFunc F) W.FunctionField := by
  refine IsScalarTower.of_algebraMap_eq fun c => ?_
  rw [IsScalarTower.algebraMap_apply F F[X] (RatFunc F) c,
    ← IsScalarTower.algebraMap_apply F[X] (RatFunc F) W.FunctionField,
    Polynomial.algebraMap_eq, algebraMap_polynomial_eq_polyToFunctionField]
  exact (polyToFunctionField_C c).symm

variable (W) in

def yCoord : W.FunctionField :=
  algebraMap W.CoordinateRing W.FunctionField (CoordinateRing.mk W Y)

variable (W) in

def weierstrassQuadratic : Polynomial (RatFunc F) :=
  X ^ 2 + (C (algebraMap F[X] (RatFunc F) (C W.a₁ * X + C W.a₃)) * X
    - C (algebraMap F[X] (RatFunc F) (X ^ 3 + C W.a₂ * X ^ 2 + C W.a₄ * X + C W.a₆)))

theorem weierstrassQuadratic_sub_degree_lt :
    (C (algebraMap F[X] (RatFunc F) (C W.a₁ * X + C W.a₃)) * X
      - C (algebraMap F[X] (RatFunc F)
        (X ^ 3 + C W.a₂ * X ^ 2 + C W.a₄ * X + C W.a₆))).degree < ((2 : ℕ) : WithBot ℕ) := by
  rw [sub_eq_add_neg, ← Polynomial.C_neg]
  exact lt_of_le_of_lt Polynomial.degree_linear_le (by exact_mod_cast Nat.one_lt_two)

theorem weierstrassQuadratic_monic : (weierstrassQuadratic W).Monic :=
  monic_X_pow_add weierstrassQuadratic_sub_degree_lt

theorem yCoord_relation :
    yCoord W * yCoord W
      = polyToFunctionField W (X ^ 3 + C W.a₂ * X ^ 2 + C W.a₄ * X + C W.a₆)
        - polyToFunctionField W (C W.a₁ * X + C W.a₃) * yCoord W := by
  have h1 := smul_basis_mul_Y (W' := W) 0 1
  rw [zero_smul, zero_add, one_smul, one_mul, one_mul, zero_sub] at h1
  have h2 := congrArg (algebraMap W.CoordinateRing W.FunctionField) h1
  rw [map_mul, algebraMap_smul_basis, _root_.map_neg, neg_mul, ← sub_eq_add_neg] at h2
  exact h2

theorem aeval_yCoord_weierstrassQuadratic :
    Polynomial.aeval (yCoord W) (weierstrassQuadratic W) = 0 := by
  have hc : ∀ p : F[X],
      algebraMap (RatFunc F) W.FunctionField (algebraMap F[X] (RatFunc F) p)
        = polyToFunctionField W p := fun p => by
    rw [← IsScalarTower.algebraMap_apply F[X] (RatFunc F) W.FunctionField,
      algebraMap_polynomial_eq_polyToFunctionField]
  simp only [weierstrassQuadratic, map_add, map_sub, map_mul, map_pow, Polynomial.aeval_X,
    Polynomial.aeval_C, hc]
  rw [sq]
  have hrel := yCoord_relation (W := W)
  simp only [map_add, map_mul, map_pow] at hrel ⊢
  linear_combination hrel

theorem isIntegral_yCoord : _root_.IsIntegral (RatFunc F) (yCoord W) :=
  ⟨weierstrassQuadratic W, weierstrassQuadratic_monic, by
    rw [← Polynomial.aeval_def]; exact aeval_yCoord_weierstrassQuadratic⟩

/-! ### The generic point of the function field

The bridge between the `F[X]`-algebra structure of `W.FunctionField` and its
`RatFunc F`-algebra structure. The pin's `S_` proof modules each inline a copy of
this four-declaration block (ten files in the Vélu slice); it is written once
here. `transcendental_polyToFunctionField_X` is the statement every
`RatFunc F`-algebra computation in the cluster starts from, and
`equation_map_polyToFunctionField_yGen` says the generic point `(X, yGen)` lies on
the base-changed curve `W.map (algebraMap F W.FunctionField)`. -/

section GenericPoint

theorem polyToFunctionField_eq_aeval (p : F[X]) :
    polyToFunctionField W p = Polynomial.aeval (polyToFunctionField W X) p := by
  have h1 : (polyToFunctionField W : F[X] →+* W.FunctionField)
      = algebraMap F[X] W.FunctionField :=
    (IsScalarTower.algebraMap_eq F[X] W.CoordinateRing W.FunctionField).symm
  have h2 : (IsScalarTower.toAlgHom F F[X] W.FunctionField : F[X] →ₐ[F] W.FunctionField)
      = Polynomial.aeval (polyToFunctionField W X) := by
    refine Polynomial.algHom_ext ?_
    rw [Polynomial.aeval_X, IsScalarTower.coe_toAlgHom', ← h1]
  calc polyToFunctionField W p = algebraMap F[X] W.FunctionField p := by rw [h1]
    _ = (IsScalarTower.toAlgHom F F[X] W.FunctionField : F[X] →ₐ[F] W.FunctionField) p := rfl
    _ = Polynomial.aeval (polyToFunctionField W X) p := by rw [h2]

/-- The pin's `S_`-local name for `yCoord`: the `Y`-coordinate of the generic
point of `W.FunctionField`, as an element of the function field. Kept under the
pin's name (definitionally `yCoord`) so the consumers transcribe unchanged. -/
def yGen (W : Affine F) : W.FunctionField := yCoord W

theorem equation_map_polyToFunctionField_yGen :
    (W.map (algebraMap F W.FunctionField)).toAffine.Equation
      (polyToFunctionField W X) (yGen W) := by
  rw [equation_iff]
  have hrel := smul_basis_mul_Y (W' := W) 0 1
  rw [zero_smul, zero_add, one_smul, one_mul, one_mul, zero_sub] at hrel
  have h2 := congrArg (algebraMap W.CoordinateRing W.FunctionField) hrel
  rw [map_mul, algebraMap_smul_basis, _root_.map_neg, neg_mul, ← sub_eq_add_neg] at h2
  simp only [map_a₁, map_a₂, map_a₃, map_a₄, map_a₆]
  simp only [map_add, map_mul, map_pow, polyToFunctionField_C] at h2
  rw [show yGen W = algebraMap W.CoordinateRing W.FunctionField (CoordinateRing.mk W Y)
    from rfl]
  simp only [polyToFunctionField_apply] at h2 ⊢
  linear_combination h2

theorem transcendental_polyToFunctionField_X :
    Transcendental F (polyToFunctionField W X) := by
  rw [transcendental_iff]
  intro p hp
  rw [← polyToFunctionField_eq_aeval] at hp
  exact polyToFunctionField_injective (by simpa using hp)

end GenericPoint

end WeierstrassCurve.Affine

end
