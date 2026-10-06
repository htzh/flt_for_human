/-
The shared base-change prelude of the D column: the function-field `pointPullback`
maps, the `TreeIsogenyEndDatum` datum with its `degree`, and the tensor-product
base change of a Weierstrass curve's function field — in both the `General`
spelling (algebraically closed `F`, `F'`) and the `NoAC` spelling (no algebraic
closure hypothesis, over an arbitrary base field `R₀`) — together with the
`IsogenyEndDatum` base-change block built on them.

This is set **D-1** of `topics/velu/WORKORDER-P2-basechange.md`. It has no headline
of its own: it exists so that D-2 (`interm`), D-3 (`bcff`, `varCh`), D-4 (`conj`)
and D-5 (the two silos) import one home instead of each re-proving the same
prelude. Statements are transcribed verbatim from the pinned FLT `aa2d8b3`:

* `P2M/Sol/S_WeierstrassCurve_Affine_exists_algHom_functionField_baseChange_finrankAlong_eq.lean`
  (the `General` spelling; also carries `ofHeightOneSpectrum_injective`,
  already ported in `AlgebraicCurve/Defs/RatFuncPlaces.lean`);
* `P2M/Sol/S_WeierstrassCurve_exists_intermediateField_countable_map_eq_and_finrankAlong_eq.lean`
  (the `NoAC` spelling, with `TreeIsogenyEndDatum` in place of `IsogenyEndDatum`);
* `P2M/Sol/S_WeierstrassCurve_Affine_isAddCyclic_ker_pointMapOfPushforward_of_baseChange_algHom.lean`
  (the `pointPullback*To` column and the `kw_functionField_algHom_ext` /
  `kw_coordinateRingBasis` vocabulary).

The `NoAC` declarations are strictly more general than their `General` twins
(`…NoAC` drops `[IsAlgClosed F] [IsAlgClosed F']`); the `General` names are kept —
the checker diffs the text, and D-3/D-5 consume them — but their proofs are
one-line invocations of the `NoAC` general lemmas.

Already public in the port and **imported, not re-proved**: `yGen`,
`polyToFunctionField_eq_aeval`, `equation_map_polyToFunctionField_yGen`,
`transcendental_polyToFunctionField_X` (`WeierstrassCurve/FunctionFieldQuadratic.lean`);
`algebraMap_polynomial_eq_mk_C`, `CoordinateRing.algebraMap_eq_mk_C_C`
(`WeierstrassCurve/Place/Dictionary.lean`); `AlgebraicCurve.Place.ofHeightOneSpectrum_injective`
(`AlgebraicCurve/Defs/RatFuncPlaces.lean`; pinned copy at `bcff:149`, and the
already-present port declaration has a binder spelling difference —
`ofHeightOneSpectrum (K := K) (F := F) (R := R)` against the pin's
`(K := K) (R := R) (F := F)` — which is *not* a specialisation, so the pin copy is
not re-declared here); `IsogenyEndDatum` and `degree`
(`WeierstrassCurve/Isogeny/ConditionalCurrency.lean`,
`WeierstrassCurve/IsogenyEndDatum/DualEndData.lean`).

Only proof bodies are adapted to mathlib `v4.34.0`. `Algebra.TensorProduct.rightAlgebra`
is mathlib's `Mathlib.RingTheory/TensorProduct/Basic.lean` abbreviation, activated
as a local instance exactly where the pin does.

Import note. This module imports `GenusOnePlaceGate.lean` (the gate *classes*), **not**
`GenusOnePlaceGateCentred.lean` (the *producer* `exists_genusOnePlaceGate_isCentred_and_abelTheorem`).
The producer module pulls `Place/RRSpace.lean`, whose `scoped instance instInfinitePlace`
collides with `IsogenyEndDatum/Engine.lean`'s `WeierstrassCurve.Affine.instInfinitePlace`
(two declarations of one name: no environment can import both). The D column supplies the
gate classes as *arguments* everywhere, so the producer is not needed and the D-4/D-5
consumers of this module can import `Engine.lean` freely. See `CARRY-FORWARD.md`.

Reference (public mirror, pinned):
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_WeierstrassCurve_Affine_exists_algHom_functionField_baseChange_finrankAlong_eq.lean>
-/
import FLTForHuman.WeierstrassCurve.FunctionFieldQuadratic
import FLTForHuman.WeierstrassCurve.Isogeny.ConditionalCurrency
import FLTForHuman.WeierstrassCurve.GenusOnePlaceGate
import FLTForHuman.WeierstrassCurve.Place.Dictionary
import Mathlib.Algebra.Polynomial.Basis
import Mathlib.RingTheory.PolynomialAlgebra
import Mathlib.RingTheory.TensorProduct.Free
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.RingTheory.Flat.Basic

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

noncomputable section

open Polynomial
open scoped Polynomial.Bivariate WeierstrassCurve TensorProduct

universe u

namespace WeierstrassCurve

namespace Affine

/-! ### The `TreeIsogenyEndDatum` datum

The pin's `interm` spelling of `IsogenyEndDatum`: the same three fields under the
name the `S_` file uses, so the countable-descent module can transcribe unchanged. -/

section TreeDatum

variable {F : Type u} [Field F]
variable (W : Affine F)
variable [W.IsElliptic]

structure TreeIsogenyEndDatum where
  ι : W.FunctionField →ₐ[F] W.FunctionField
  hι : ι.toRingHom.IsIntegral
  hfin : AlgebraicCurve.FiniteAlong F ι

end TreeDatum

namespace TreeIsogenyEndDatum

variable {F : Type u} [Field F] {W : Affine F}

def degree (D : TreeIsogenyEndDatum W) : ℕ := AlgebraicCurve.finrankAlong F D.ι

end TreeIsogenyEndDatum

/-! ### The function-field `pointPullback` maps

The pin's `…To` column: `pointPullbackCoordHomTo h` is the `F`-algebra map
`W.CoordinateRing →ₐ[F] L` sending `X ↦ xP`, `Y ↦ yP` for a point `(xP, yP)` of the
base-changed curve `W.map (algebraMap F L)`, and `pointPullbackHomTo` is its
extension to the function field. The port's `WeierstrassCurve.Affine.pointPullback*`
(`IsogenyEndDatum/Engine.lean`) is the `L = W.FunctionField` special case; the
general-`L` statements are re-proved here because they cannot be derived from it
without a map `W.FunctionField → L`. -/

section PointPullbackTo

variable {F : Type u} [Field F] {W : Affine F} {L : Type u} [Field L] [Algebra F L]

theorem eval₂_polynomial_of_equation_map_target {xP yP : L}
    (h : (W.map (algebraMap F L)).toAffine.Equation xP yP) :
    W.polynomial.eval₂
      (Polynomial.aeval xP : F[X] →ₐ[F] L).toRingHom yP = 0 := by
  rw [equation_iff'] at h
  simp only [map_a₁, map_a₂, map_a₃, map_a₄, map_a₆] at h
  simp only [WeierstrassCurve.Affine.polynomial, eval₂_add, eval₂_sub, eval₂_mul, eval₂_pow,
    eval₂_X, eval₂_C, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_add, map_mul, map_pow,
    Polynomial.aeval_C, Polynomial.aeval_X]
  linear_combination h

def pointPullbackCoordHomTo {xP yP : L}
    (h : (W.map (algebraMap F L)).toAffine.Equation xP yP) :
    W.CoordinateRing →ₐ[F] L where
  __ := AdjoinRoot.lift
    (Polynomial.aeval xP : F[X] →ₐ[F] L).toRingHom
    yP (eval₂_polynomial_of_equation_map_target h)
  commutes' c := by
    show AdjoinRoot.lift _ _ (eval₂_polynomial_of_equation_map_target h) (algebraMap F _ c)
      = algebraMap F L c
    rw [CoordinateRing.algebraMap_eq_mk_C_C, AdjoinRoot.lift_mk, eval₂_C]
    exact Polynomial.aeval_C _ c

theorem pointPullbackCoordHomTo_mk {xP yP : L}
    (h : (W.map (algebraMap F L)).toAffine.Equation xP yP) (g : F[X][Y]) :
    pointPullbackCoordHomTo h (CoordinateRing.mk W g)
      = g.eval₂ (Polynomial.aeval xP : F[X] →ₐ[F] L).toRingHom yP :=
  AdjoinRoot.lift_mk (eval₂_polynomial_of_equation_map_target h) g

theorem pointPullbackCoordHomTo_comp_algebraMap {xP yP : L}
    (h : (W.map (algebraMap F L)).toAffine.Equation xP yP) :
    (pointPullbackCoordHomTo h).toRingHom.comp (algebraMap F[X] W.CoordinateRing)
      = (Polynomial.aeval xP : F[X] →ₐ[F] L).toRingHom := by
  refine RingHom.ext fun p => ?_
  show pointPullbackCoordHomTo h (algebraMap F[X] _ p) = _
  rw [algebraMap_polynomial_eq_mk_C, pointPullbackCoordHomTo_mk, eval₂_C]

theorem pointPullbackCoordHomTo_injective {xP yP : L}
    (h : (W.map (algebraMap F L)).toAffine.Equation xP yP)
    (hx : Function.Injective (Polynomial.aeval (R := F) xP)) :
    Function.Injective (pointPullbackCoordHomTo h) := by
  have hker : RingHom.ker (pointPullbackCoordHomTo h).toRingHom = ⊥ := by
    haveI : Module.Finite F[X] W.CoordinateRing :=
      Module.Finite.of_basis (CoordinateRing.basis W)
    refine Ideal.eq_bot_of_under_eq_bot (R := F[X]) ?_
    rw [Ideal.under_def, RingHom.comap_ker, pointPullbackCoordHomTo_comp_algebraMap,
      ← RingHom.injective_iff_ker_eq_bot]
    exact hx
  exact (RingHom.injective_iff_ker_eq_bot (pointPullbackCoordHomTo h).toRingHom).mpr hker

def pointPullbackHomTo {xP yP : L}
    (h : (W.map (algebraMap F L)).toAffine.Equation xP yP)
    (hx : Function.Injective (Polynomial.aeval (R := F) xP)) :
    W.FunctionField →ₐ[F] L :=
  IsFractionRing.liftAlgHom (pointPullbackCoordHomTo_injective h hx)

theorem pointPullbackHomTo_algebraMap {xP yP : L}
    (h : (W.map (algebraMap F L)).toAffine.Equation xP yP)
    (hx : Function.Injective (Polynomial.aeval (R := F) xP)) (r : W.CoordinateRing) :
    pointPullbackHomTo h hx (algebraMap W.CoordinateRing W.FunctionField r)
      = pointPullbackCoordHomTo h r :=
  IsFractionRing.lift_algebraMap (pointPullbackCoordHomTo_injective h hx) r

theorem pointPullbackHomTo_polyToFunctionField_X {xP yP : L}
    (h : (W.map (algebraMap F L)).toAffine.Equation xP yP)
    (hx : Function.Injective (Polynomial.aeval (R := F) xP)) :
    pointPullbackHomTo h hx (polyToFunctionField W X) = xP := by
  rw [polyToFunctionField_apply, pointPullbackHomTo_algebraMap,
    algebraMap_polynomial_eq_mk_C, pointPullbackCoordHomTo_mk, eval₂_C]
  exact Polynomial.aeval_X _

theorem pointPullbackHomTo_yGen {xP yP : L}
    (h : (W.map (algebraMap F L)).toAffine.Equation xP yP)
    (hx : Function.Injective (Polynomial.aeval (R := F) xP)) :
    pointPullbackHomTo h hx (yGen W) = yP := by
  show pointPullbackHomTo h hx (algebraMap _ _ (CoordinateRing.mk W Y)) = _
  rw [pointPullbackHomTo_algebraMap, pointPullbackCoordHomTo_mk]
  exact eval₂_X _ _

end PointPullbackTo

/-! ### Function-field extension

An `F`-algebra map out of `W.FunctionField` is determined by the images of
`polyToFunctionField W X` and `yGen W`. The port's `es1a8_functionField_algHom_ext_cmp`
(`IsogenyEndDatum/Engine.lean`) is the `L = W.FunctionField` case with a different
proof; the general-`L` statement is the pin's `kw_functionField_algHom_ext`. -/

section AlgHomExt

variable {F : Type u} [Field F] {W : Affine F}

theorem kw_functionField_algHom_ext {L : Type*} [Field L] [Algebra F L]
    {f g : W.FunctionField →ₐ[F] L}
    (hX : f (polyToFunctionField W X) = g (polyToFunctionField W X))
    (hy : f (yGen W) = g (yGen W)) : f = g := by
  have hCR : ∀ r : W.CoordinateRing,
      f (algebraMap W.CoordinateRing W.FunctionField r)
        = g (algebraMap W.CoordinateRing W.FunctionField r) := by
    intro r
    obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective r
    have hFX : ∀ c : F[X], f (algebraMap W.CoordinateRing W.FunctionField
          (algebraMap F[X] W.CoordinateRing c))
        = g (algebraMap W.CoordinateRing W.FunctionField
          (algebraMap F[X] W.CoordinateRing c)) :=
      fun c => DFunLike.congr_fun
        (Polynomial.algHom_ext (f := (f.comp (IsScalarTower.toAlgHom F W.CoordinateRing
            W.FunctionField)).comp (IsScalarTower.toAlgHom F F[X] W.CoordinateRing))
          (g := (g.comp (IsScalarTower.toAlgHom F W.CoordinateRing W.FunctionField)).comp
            (IsScalarTower.toAlgHom F F[X] W.CoordinateRing)) hX) c
    have hFX' : ∀ c : F[X], f (algebraMap W.CoordinateRing W.FunctionField
          (AdjoinRoot.mk W.polynomial (C c)))
        = g (algebraMap W.CoordinateRing W.FunctionField
          (AdjoinRoot.mk W.polynomial (C c))) := fun c => by
      rw [show AdjoinRoot.mk W.polynomial (C c) = algebraMap F[X] W.CoordinateRing c from rfl]
      exact hFX c
    have hy' : f (algebraMap W.CoordinateRing W.FunctionField (AdjoinRoot.mk W.polynomial Y))
        = g (algebraMap W.CoordinateRing W.FunctionField (AdjoinRoot.mk W.polynomial Y)) := hy
    induction p using Polynomial.induction_on with
    | C c => exact hFX' c
    | monomial n c _ => simp only [map_mul, map_pow, hy', hFX' c]
    | add p q hp hq => simp only [map_add, hp, hq]
  refine AlgHom.ext fun a => ?_
  obtain ⟨p, q, hq, rfl⟩ := IsFractionRing.div_surjective (A := W.CoordinateRing) a
  simp only [map_div₀, hCR p, hCR q]

end AlgHomExt

end Affine

end WeierstrassCurve

namespace ModularCurve

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.CoordinateRing

/-! ### The coordinate-ring basis

`kw_coordinateRingBasis V` is the `R`-basis `Xⁿ`, `XⁿY` of `V.CoordinateRing`, read
off the `R[X]`-basis of `Polynomial` and the `Fin 2`-basis of the coordinate ring. -/

def kw_coordinateRingBasis {R : Type*} [CommRing R] (V : Affine R) :
    Module.Basis (ℕ × Fin 2) R V.CoordinateRing :=
  (Polynomial.basisMonomials R).smulTower (CoordinateRing.basis V)

/-! ### The `NoAC` spelling

Over an arbitrary base field `R₀`, with **no** algebraic-closure hypothesis on `F`
or `F'`: the base change `W⁄F → W⁄F'` of the function field, the tensor-product
description of `(W⁄F').FunctionField`, and the `IsogenyEndDatum` base change built
on it. Everything here is stated for `TreeIsogenyEndDatum`, the pin's `interm`
spelling of the endomorphism datum. -/

section NoAC

variable {R₀ : Type u} [Field R₀]
variable (W : WeierstrassCurve R₀) [W.IsElliptic]
variable (F : Type u) [Field F] [Algebra R₀ F] [DecidableEq F] [CharZero F]
variable (F' : Type u) [Field F'] [Algebra R₀ F'] [DecidableEq F'] [CharZero F']
variable [Algebra F F'] [IsScalarTower R₀ F F']

theorem kw_transcendental_polyToFunctionField_X_over_baseGeneralNoAC :
    Transcendental F (polyToFunctionField (W⁄F') X) :=
  Transcendental.of_tower_top F (L := F')
    (transcendental_polyToFunctionField_X (W := (W⁄F')))

theorem kw_equation_map_polyToFunctionField_yGen_over_baseGeneralNoAC :
    ((W⁄F).map (algebraMap F (W⁄F').FunctionField)).toAffine.Equation
      (polyToFunctionField (W⁄F') X) (yGen (W⁄F')) := by
  have hcurve : (W⁄F).map (algebraMap F (W⁄F').FunctionField)
      = (W⁄F').map (algebraMap F' (W⁄F').FunctionField) := by
    show (W.map _).map _ = (W.map _).map _
    rw [WeierstrassCurve.map_map, WeierstrassCurve.map_map]
    congr 1
    exact ((IsScalarTower.algebraMap_eq R₀ F (W⁄F').FunctionField).symm).trans
      (IsScalarTower.algebraMap_eq R₀ F' (W⁄F').FunctionField)
  exact hcurve ▸ equation_map_polyToFunctionField_yGen (W := (W⁄F'))

def kw_functionFieldMapAlongGeneralNoAC : (W⁄F).FunctionField →ₐ[F] (W⁄F').FunctionField :=
  pointPullbackHomTo (kw_equation_map_polyToFunctionField_yGen_over_baseGeneralNoAC W F F')
    ((injective_iff_map_eq_zero _).mpr fun p hp =>
      transcendental_iff.mp (kw_transcendental_polyToFunctionField_X_over_baseGeneralNoAC W F F') p
        hp)

theorem kw_functionFieldMapAlongGeneralNoAC_polyToFunctionField_X :
    kw_functionFieldMapAlongGeneralNoAC W F F' (polyToFunctionField (W⁄F) X)
      = polyToFunctionField (W⁄F') X :=
  pointPullbackHomTo_polyToFunctionField_X _ _

theorem kw_functionFieldMapAlongGeneralNoAC_yGen :
    kw_functionFieldMapAlongGeneralNoAC W F F' (yGen (W⁄F)) = yGen (W⁄F') :=
  pointPullbackHomTo_yGen _ _

def KwFunctionFieldTensorIsDomainGeneralNoAC : Prop :=
  IsDomain ((W⁄F).FunctionField ⊗[F] F')

attribute [local instance] Algebra.TensorProduct.rightAlgebra

scoped instance kw_isScalarTower_base_right_tensorGeneralNoAC :
    IsScalarTower R₀ F' ((W⁄F).FunctionField ⊗[F] F') := by
  refine IsScalarTower.of_algebraMap_eq' (RingHom.ext fun r => ?_)
  rw [RingHom.comp_apply, Algebra.TensorProduct.right_algebraMap_apply,
    IsScalarTower.algebraMap_apply R₀ F F',
    show algebraMap R₀ ((W⁄F).FunctionField ⊗[F] F') r
      = (algebraMap F ((W⁄F).FunctionField ⊗[F] F')) (algebraMap R₀ F r) from
        IsScalarTower.algebraMap_apply R₀ F ((W⁄F).FunctionField ⊗[F] F') r,
    Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_eq_smul_one,
    Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul, Algebra.algebraMap_eq_smul_one]

section FracHom

variable [IsDomain ((W⁄F).FunctionField ⊗[F] F')]

scoped instance kw_isScalarTower_base_right_fracTensorGeneralNoAC :
    IsScalarTower R₀ F' (FractionRing ((W⁄F).FunctionField ⊗[F] F')) :=
  IsScalarTower.of_algebraMap_eq fun r =>
    (IsScalarTower.algebraMap_apply R₀ ((W⁄F).FunctionField ⊗[F] F')
        (FractionRing ((W⁄F).FunctionField ⊗[F] F')) r).trans <|
      (congrArg (algebraMap ((W⁄F).FunctionField ⊗[F] F')
          (FractionRing ((W⁄F).FunctionField ⊗[F] F')))
        (IsScalarTower.algebraMap_apply R₀ F' ((W⁄F).FunctionField ⊗[F] F') r)).trans
      (IsScalarTower.algebraMap_apply F' ((W⁄F).FunctionField ⊗[F] F')
        (FractionRing ((W⁄F).FunctionField ⊗[F] F')) (algebraMap R₀ F' r)).symm

theorem kw_equation_tensorFracXYGeneralNoAC :
    ((W⁄F').map (algebraMap F' (FractionRing ((W⁄F).FunctionField ⊗[F] F')))).toAffine.Equation
      (algebraMap ((W⁄F).FunctionField ⊗[F] F')
        (FractionRing ((W⁄F).FunctionField ⊗[F] F'))
        ((polyToFunctionField (W⁄F) X) ⊗ₜ[F] (1 : F')))
      (algebraMap ((W⁄F).FunctionField ⊗[F] F')
        (FractionRing ((W⁄F).FunctionField ⊗[F] F'))
        ((yGen (W⁄F)) ⊗ₜ[F] (1 : F'))) := by
  have hcurve : (W⁄F').map (algebraMap F' (FractionRing ((W⁄F).FunctionField ⊗[F] F')))
      = W⁄(FractionRing ((W⁄F).FunctionField ⊗[F] F')) := by
    show (W.map _).map _ = W.map _
    rw [WeierstrassCurve.map_map]; congr 1
    exact (IsScalarTower.algebraMap_eq R₀ F'
      (FractionRing ((W⁄F).FunctionField ⊗[F] F'))).symm
  rw [hcurve]
  exact Equation.baseChange (W := W) (S := R₀)
    (f := (IsScalarTower.toAlgHom R₀ ((W⁄F).FunctionField ⊗[F] F')
            (FractionRing ((W⁄F).FunctionField ⊗[F] F'))).comp
          (Algebra.TensorProduct.includeLeft (R := F) (S := R₀)))
    (equation_map_polyToFunctionField_yGen (W := (W⁄F)))

theorem kw_transcendental_tensorFracXGeneralNoAC :
    Function.Injective (Polynomial.aeval (R := F')
      (algebraMap ((W⁄F).FunctionField ⊗[F] F')
        (FractionRing ((W⁄F).FunctionField ⊗[F] F'))
        ((polyToFunctionField (W⁄F) X) ⊗ₜ[F] (1 : F')))) := by
  rw [show algebraMap ((W⁄F).FunctionField ⊗[F] F')
        (FractionRing ((W⁄F).FunctionField ⊗[F] F'))
        ((polyToFunctionField (W⁄F) X) ⊗ₜ[F] (1 : F'))
      = IsScalarTower.toAlgHom F' ((W⁄F).FunctionField ⊗[F] F')
          (FractionRing ((W⁄F).FunctionField ⊗[F] F'))
          ((polyToFunctionField (W⁄F) X) ⊗ₜ[F] (1 : F')) from rfl,
    Polynomial.aeval_algHom]
  refine (IsFractionRing.injective ((W⁄F).FunctionField ⊗[F] F')
    (FractionRing ((W⁄F).FunctionField ⊗[F] F'))).comp ?_
  have heq : (Polynomial.aeval (R := F')
        ((polyToFunctionField (W⁄F) X) ⊗ₜ[F] (1 : F')
          : (W⁄F).FunctionField ⊗[F] F')).toRingHom
      = ((Algebra.TensorProduct.map
            (Polynomial.aeval (R := F) (polyToFunctionField (W⁄F) X))
            (AlgHom.id F F')).toRingHom.comp
          (Algebra.TensorProduct.comm F F' F[X]).toAlgHom.toRingHom).comp
          (polyEquivTensor' F F').toAlgHom.toRingHom := by
    refine Polynomial.ringHom_ext (fun c => ?_) ?_
    · show aeval _ (C c) = Algebra.TensorProduct.map _ _
          (Algebra.TensorProduct.comm F F' F[X] (polyEquivTensor' F F' (C c)))
      rw [show (polyEquivTensor' F F') (C c) = c ⊗ₜ[F] (1 : F[X]) from by
            rw [coe_polyEquivTensor', polyEquivTensor_apply, eval₂_C]; rfl,
        Algebra.TensorProduct.comm_tmul, Algebra.TensorProduct.map_tmul, Polynomial.aeval_C,
        Algebra.TensorProduct.right_algebraMap_apply, AlgHom.coe_id, id_eq, map_one]
    · show aeval _ (X : F'[X]) = Algebra.TensorProduct.map _ _
          (Algebra.TensorProduct.comm F F' F[X] (polyEquivTensor' F F' X))
      rw [show (polyEquivTensor' F F') X = (1:F') ⊗ₜ[F] (X : F[X]) from by
            rw [coe_polyEquivTensor', polyEquivTensor_apply, eval₂_X],
        Algebra.TensorProduct.comm_tmul, Algebra.TensorProduct.map_tmul, Polynomial.aeval_X,
        AlgHom.coe_id, id_eq, Polynomial.aeval_X]
  have hinj : Function.Injective
      (((Algebra.TensorProduct.map
          (Polynomial.aeval (R := F) (polyToFunctionField (W⁄F) X))
          (AlgHom.id F F')).toRingHom.comp
        (Algebra.TensorProduct.comm F F' F[X]).toAlgHom.toRingHom).comp
        (polyEquivTensor' F F').toAlgHom.toRingHom) :=
    ((Module.Flat.rTensor_preserves_injective_linearMap (M := F')
        (Polynomial.aeval (R := F) (polyToFunctionField (W⁄F) X)).toLinearMap
        ((injective_iff_map_eq_zero _).mpr fun p hp =>
          transcendental_iff.mp (transcendental_polyToFunctionField_X (W := (W⁄F))) p hp)).comp
      (Algebra.TensorProduct.comm F F' F[X]).injective).comp (polyEquivTensor' F F').injective
  intro p q hpq
  refine hinj ?_
  have := DFunLike.congr_fun heq
  exact (this p).symm.trans (hpq.trans (this q))

def kw_functionFieldTensorFracHomGeneralNoAC :
    (W⁄F').FunctionField →ₐ[F'] FractionRing ((W⁄F).FunctionField ⊗[F] F') :=
  pointPullbackHomTo (kw_equation_tensorFracXYGeneralNoAC W F F')
    (kw_transcendental_tensorFracXGeneralNoAC W F F')

theorem kw_functionFieldTensorFracHomGeneralNoAC_X :
    kw_functionFieldTensorFracHomGeneralNoAC W F F' (polyToFunctionField (W⁄F') X)
      = algebraMap ((W⁄F).FunctionField ⊗[F] F') _
          ((polyToFunctionField (W⁄F) X) ⊗ₜ[F] (1 : F')) :=
  pointPullbackHomTo_polyToFunctionField_X _ _

theorem kw_functionFieldTensorFracHomGeneralNoAC_yGen :
    kw_functionFieldTensorFracHomGeneralNoAC W F F' (yGen (W⁄F'))
      = algebraMap ((W⁄F).FunctionField ⊗[F] F') _ ((yGen (W⁄F)) ⊗ₜ[F] (1 : F')) :=
  pointPullbackHomTo_yGen _ _

theorem kw_functionFieldTensorFracHomGeneralNoAC_bijective :
    Function.Bijective (kw_functionFieldTensorFracHomGeneralNoAC W F F') := by
  refine ⟨(kw_functionFieldTensorFracHomGeneralNoAC W F F').injective, ?_⟩
  set ψ := kw_functionFieldTensorFracHomGeneralNoAC W F F'
  have hκ : (ψ.restrictScalars F).comp (kw_functionFieldMapAlongGeneralNoAC W F F')
      = (IsScalarTower.toAlgHom F ((W⁄F).FunctionField ⊗[F] F')
          (FractionRing ((W⁄F).FunctionField ⊗[F] F'))).comp
          (Algebra.TensorProduct.includeLeft (R := F)) := by
    refine kw_functionField_algHom_ext ?_ ?_
    · show ψ (kw_functionFieldMapAlongGeneralNoAC W F F' (polyToFunctionField (W⁄F) X)) = _
      rw [kw_functionFieldMapAlongGeneralNoAC_polyToFunctionField_X,
        kw_functionFieldTensorFracHomGeneralNoAC_X]
      rfl
    · show ψ (kw_functionFieldMapAlongGeneralNoAC W F F' (yGen (W⁄F))) = _
      rw [kw_functionFieldMapAlongGeneralNoAC_yGen, kw_functionFieldTensorFracHomGeneralNoAC_yGen]
      rfl
  have hT_sub : ∀ t : (W⁄F).FunctionField ⊗[F] F',
      algebraMap ((W⁄F).FunctionField ⊗[F] F') (FractionRing _) t ∈ ψ.toRingHom.fieldRange := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp only [_root_.map_zero]; exact zero_mem _
    | add _ _ hx hy => simp only [map_add]; exact add_mem hx hy
    | tmul a c =>
      rw [show (a ⊗ₜ[F] c : (W⁄F).FunctionField ⊗[F] F') = (a ⊗ₜ[F] 1) * (1 ⊗ₜ[F] c) from
            by rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul],
        map_mul]
      refine mul_mem ?_ ⟨algebraMap F' _ c, ?_⟩
      · exact ⟨kw_functionFieldMapAlongGeneralNoAC W F F' a, DFunLike.congr_fun hκ a⟩
      · simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, ψ.commutes,
          IsScalarTower.algebraMap_apply F' ((W⁄F).FunctionField ⊗[F] F')
            (FractionRing ((W⁄F).FunctionField ⊗[F] F')),
          Algebra.TensorProduct.right_algebraMap_apply]
  intro z
  obtain ⟨t, s, _, rfl⟩ := IsFractionRing.div_surjective
    (A := (W⁄F).FunctionField ⊗[F] F') (K := FractionRing _) z
  exact div_mem (hT_sub t) (hT_sub s)

def kw_functionFieldTensorFracEquivGeneralNoAC :
    (W⁄F').FunctionField ≃ₐ[F'] FractionRing ((W⁄F).FunctionField ⊗[F] F') :=
  AlgEquiv.ofBijective _ (kw_functionFieldTensorFracHomGeneralNoAC_bijective W F F')

end FracHom

/-! ### The tensor-product `IsogenyEndDatum` base change

The `F'`-linear base change of the endomorphism ring hom `D.ι` to
`(W⁄F).FunctionField ⊗[F] F'`, its fraction-field extension, and the `_seam`
proposition asserting finiteness and the degree match. The `Along` block turns
the seam into the datum-level base-change statement. -/

section FracTensorNoAC

variable [IsDomain ((W⁄F).FunctionField ⊗[F] F')]

def kw_tensorIotaRingHomGeneralNoAC (D : TreeIsogenyEndDatum (W⁄F)) :
    (W⁄F).FunctionField ⊗[F] F' →+* (W⁄F).FunctionField ⊗[F] F' :=
  (Algebra.TensorProduct.map D.ι (AlgHom.id F F')).toRingHom

theorem kw_tensorIotaRingHomGeneralNoAC_tmul (D : TreeIsogenyEndDatum (W⁄F))
    (a : (W⁄F).FunctionField)
    (c : F') : kw_tensorIotaRingHomGeneralNoAC W F F' D (a ⊗ₜ[F] c) = (D.ι a) ⊗ₜ[F] c := by
  simp [kw_tensorIotaRingHomGeneralNoAC, Algebra.TensorProduct.map_tmul]

theorem kw_tensorIotaRingHomGeneralNoAC_injective (D : TreeIsogenyEndDatum (W⁄F)) :
    Function.Injective (kw_tensorIotaRingHomGeneralNoAC W F F' D) :=
  Module.Flat.rTensor_preserves_injective_linearMap (M := F') D.ι.toLinearMap D.ι.injective

def kw_tensorFracIotaRingHomGeneralNoAC (D : TreeIsogenyEndDatum (W⁄F)) :
    FractionRing ((W⁄F).FunctionField ⊗[F] F')
      →+* FractionRing ((W⁄F).FunctionField ⊗[F] F') :=
  IsFractionRing.map (K := FractionRing ((W⁄F).FunctionField ⊗[F] F'))
    (L := FractionRing ((W⁄F).FunctionField ⊗[F] F'))
    (kw_tensorIotaRingHomGeneralNoAC_injective W F F' D)

theorem kw_tensorFracIotaRingHomGeneralNoAC_algebraMap (D : TreeIsogenyEndDatum (W⁄F))
    (t : (W⁄F).FunctionField ⊗[F] F') :
    kw_tensorFracIotaRingHomGeneralNoAC W F F' D
        (algebraMap ((W⁄F).FunctionField ⊗[F] F')
          (FractionRing ((W⁄F).FunctionField ⊗[F] F')) t)
      = algebraMap ((W⁄F).FunctionField ⊗[F] F') (FractionRing ((W⁄F).FunctionField ⊗[F] F'))
          (kw_tensorIotaRingHomGeneralNoAC W F F' D t) := by
  unfold kw_tensorFracIotaRingHomGeneralNoAC IsFractionRing.map
  exact IsLocalization.map_eq (T := nonZeroDivisors ((W⁄F).FunctionField ⊗[F] F')) _ t

def KwTensorFracIotaFinrankSeamGeneralNoAC : Prop :=
  ∀ D : TreeIsogenyEndDatum (W⁄F),
    (kw_tensorFracIotaRingHomGeneralNoAC W F F' D).Finite ∧
    (letI := (kw_tensorFracIotaRingHomGeneralNoAC W F F' D).toAlgebra
     @Module.finrank (FractionRing ((W⁄F).FunctionField ⊗[F] F'))
       (FractionRing ((W⁄F).FunctionField ⊗[F] F')) _ _ Algebra.toModule) = D.degree

def kw_isogenyEndDatumBaseChangeIotaGeneralNoAC (D : TreeIsogenyEndDatum (W⁄F)) :
    (W⁄F').FunctionField →ₐ[F'] (W⁄F').FunctionField :=
  let ψ := kw_functionFieldTensorFracEquivGeneralNoAC W F F'
  { ψ.symm.toRingEquiv.toRingHom.comp
      ((kw_tensorFracIotaRingHomGeneralNoAC W F F' D).comp ψ.toRingEquiv.toRingHom) with
    commutes' := fun c => by
      have hc : ψ (algebraMap F' (W⁄F').FunctionField c)
          = algebraMap ((W⁄F).FunctionField ⊗[F] F')
              (FractionRing ((W⁄F).FunctionField ⊗[F] F'))
              ((1 : (W⁄F).FunctionField) ⊗ₜ[F] c) := by
        rw [AlgEquiv.commutes, IsScalarTower.algebraMap_apply F' ((W⁄F).FunctionField ⊗[F] F')
          (FractionRing ((W⁄F).FunctionField ⊗[F] F')),
          Algebra.TensorProduct.right_algebraMap_apply]
      show ψ.symm (kw_tensorFracIotaRingHomGeneralNoAC W F F' D (ψ (algebraMap F' _ c)))
          = algebraMap F' _ c
      rw [hc, kw_tensorFracIotaRingHomGeneralNoAC_algebraMap, kw_tensorIotaRingHomGeneralNoAC_tmul,
        map_one, ← hc]
      exact ψ.symm_apply_apply _ }

def KwIsogenyEndDatumBaseChangeAlongGeneralNoAC (_σ : F →ₐ[R₀] F') (N : ℕ) : Prop :=
  (∃ D : TreeIsogenyEndDatum (W⁄F), D.degree = N) →
    ∃ D' : TreeIsogenyEndDatum (W⁄F'), D'.degree = N

theorem kw_isogenyEndDatumBaseChangeAlong_of_isDomain_tensorGeneralNoAC
    (hseam : KwTensorFracIotaFinrankSeamGeneralNoAC W F F')
    (σ : F →ₐ[R₀] F') (N : ℕ) : KwIsogenyEndDatumBaseChangeAlongGeneralNoAC W F F' σ N := by
  intro ⟨D, hD⟩
  let ψ := kw_functionFieldTensorFracEquivGeneralNoAC W F F'
  let ιFr := kw_tensorFracIotaRingHomGeneralNoAC W F F' D
  obtain ⟨hfin_Fr, hdeg_Fr⟩ := hseam D
  have hcomm : ∀ x, ιFr (ψ x) = ψ (kw_isogenyEndDatumBaseChangeIotaGeneralNoAC W F F' D x) :=
    fun x => (ψ.apply_symm_apply _).symm
  have hfin : (kw_isogenyEndDatumBaseChangeIotaGeneralNoAC W F F' D).toRingHom.Finite := by
    have h₁ : (kw_isogenyEndDatumBaseChangeIotaGeneralNoAC W F F' D).toRingHom
        = ψ.symm.toRingEquiv.toRingHom.comp (ιFr.comp ψ.toRingEquiv.toRingHom) := rfl
    rw [h₁]
    exact (RingHom.Finite.of_surjective _ ψ.symm.surjective).comp
      (hfin_Fr.comp (RingHom.Finite.of_surjective _ ψ.surjective))
  refine ⟨⟨kw_isogenyEndDatumBaseChangeIotaGeneralNoAC W F F' D, hfin.to_isIntegral, hfin⟩, ?_⟩
  refine hD ▸ ?_
  exact (@Algebra.finrank_eq_of_equiv_equiv
      (W⁄F').FunctionField (W⁄F').FunctionField _ _
      (AlgebraicCurve.algebraAlong (kw_isogenyEndDatumBaseChangeIotaGeneralNoAC W F F' D))
      (FractionRing ((W⁄F).FunctionField ⊗[F] F'))
      (FractionRing ((W⁄F).FunctionField ⊗[F] F')) _ _
      (ιFr.toAlgebra) ψ.toRingEquiv ψ.toRingEquiv
      (RingHom.ext hcomm)).trans hdeg_Fr

end FracTensorNoAC

theorem kw_isogenyEndDatumBaseChangeAlong_of_tensorIsDomainGeneralNoAC
    (htens : KwFunctionFieldTensorIsDomainGeneralNoAC W F F')
    (hseam : haveI : IsDomain ((W⁄F).FunctionField ⊗[F] F') := htens
             KwTensorFracIotaFinrankSeamGeneralNoAC W F F')
    (σ : F →ₐ[R₀] F') (N : ℕ) :
    KwIsogenyEndDatumBaseChangeAlongGeneralNoAC W F F' σ N :=
  haveI : IsDomain ((W⁄F).FunctionField ⊗[F] F') := htens
  kw_isogenyEndDatumBaseChangeAlong_of_isDomain_tensorGeneralNoAC W F F' hseam σ N

/-! ### `CoordinateRing ⊗ F'` is a domain

The pin's route: the tensor product of the coordinate ring with `F'` is a domain
(via the explicit basis `kw_coordinateRingBasis`), and the function-field tensor
product is a localization of it. -/

section FFDomainNoAC

attribute [local instance] Algebra.TensorProduct.rightAlgebra

local notation3 "CR" => (W⁄F).toAffine.CoordinateRing
local notation3 "FFₗ" => (W⁄F).FunctionField

theorem kw_coordinateRingMap_basisGeneralNoAC (i : ℕ × Fin 2) :
    CoordinateRing.map (W⁄F).toAffine (algebraMap F F')
        (kw_coordinateRingBasis (W⁄F).toAffine i)
      = kw_coordinateRingBasis ((W⁄F).toAffine.map (algebraMap F F')) i := by
  obtain ⟨n, j⟩ := i
  simp only [kw_coordinateRingBasis, Module.Basis.smulTower_apply,
    Polynomial.coe_basisMonomials, CoordinateRing.map_smul]
  congr 1
  · simp [Polynomial.map_monomial]
  · rcases j with ⟨j, hj⟩
    interval_cases j <;>
      simp [CoordinateRing.basis_apply, CoordinateRing.map,
        AdjoinRoot.lift_root, AdjoinRoot.powerBasis'_gen]

def kw_coordinateRingMapAlongGeneralNoAC :
    CR →ₐ[F] ((W⁄F).toAffine.map (algebraMap F F')).CoordinateRing where
  __ := CoordinateRing.map (W⁄F).toAffine (algebraMap F F')
  commutes' r := by
    simp only [RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe,
      MonoidHom.coe_coe]
    show CoordinateRing.map (W⁄F).toAffine (algebraMap F F') (algebraMap F CR r) = algebraMap F _ r
    rw [IsScalarTower.algebraMap_apply F F[X] CR,
      show (algebraMap F F[X] r) = Polynomial.C r from rfl,
      show (algebraMap F[X] CR) (C r) = (C r : F[X]) • (1 : CR) by
        rw [Algebra.smul_def, mul_one],
      CoordinateRing.map_smul, map_one, Polynomial.map_C,
      IsScalarTower.algebraMap_apply F F' ((W⁄F).toAffine.map (algebraMap F F')).CoordinateRing,
      IsScalarTower.algebraMap_apply F' F'[X]
        ((W⁄F).toAffine.map (algebraMap F F')).CoordinateRing,
      show (algebraMap F' F'[X]) ((algebraMap F F') r) = Polynomial.C ((algebraMap F F') r)
        from rfl,
      Algebra.smul_def, mul_one]

theorem kw_coordinateRingTensor_isDomainGeneralNoAC : IsDomain (CR ⊗[F] F') := by
  suffices h : IsDomain (F' ⊗[F] CR) by
    haveI := h
    exact Function.Injective.isDomain (Algebra.TensorProduct.comm F CR F').toRingHom
      (Algebra.TensorProduct.comm F CR F').injective
  set W'' := (W⁄F).toAffine.map (algebraMap F F') with hW''
  let θ : F' ⊗[F] CR →ₐ[F'] W''.CoordinateRing :=
    AlgHom.liftEquiv F F' CR W''.CoordinateRing (kw_coordinateRingMapAlongGeneralNoAC W F F')
  have hθ : Function.Injective θ := by
    let bT : Module.Basis (ℕ × Fin 2) F' (F' ⊗[F] CR) :=
      Algebra.TensorProduct.basis F' (kw_coordinateRingBasis (W⁄F).toAffine)
    let bD : Module.Basis (ℕ × Fin 2) F' W''.CoordinateRing := kw_coordinateRingBasis W''
    have key : ∀ i, θ.toLinearMap (bT i) = (bT.equiv bD (Equiv.refl _)) (bT i) := fun i => by
      rw [Module.Basis.equiv_apply, Equiv.refl_apply, AlgHom.toLinearMap_apply]
      simp only [bT, Algebra.TensorProduct.basis_apply, θ, AlgHom.liftEquiv_tmul, one_smul]
      exact kw_coordinateRingMap_basisGeneralNoAC W F F' i
    have heq : (θ : F' ⊗[F] CR → W''.CoordinateRing) = bT.equiv bD (Equiv.refl _) :=
      funext fun x => DFunLike.congr_fun (bT.ext key : θ.toLinearMap = _) x
    exact heq ▸ (bT.equiv bD (Equiv.refl _)).injective
  exact Function.Injective.isDomain θ.toRingHom hθ

theorem kw_functionFieldTensorIsDomain_dischargeGeneralNoAC :
    KwFunctionFieldTensorIsDomainGeneralNoAC W F F' := by
  show IsDomain (FFₗ ⊗[F] F')
  haveI hCR : IsDomain (CR ⊗[F] F') := kw_coordinateRingTensor_isDomainGeneralNoAC W F F'
  letI : Algebra (CR ⊗[F] F') (FFₗ ⊗[F] F') :=
    (Algebra.TensorProduct.map (IsScalarTower.toAlgHom F CR FFₗ)
      (AlgHom.id F F')).toRingHom.toAlgebra
  haveI hst : IsScalarTower CR (CR ⊗[F] F') (FFₗ ⊗[F] F') :=
    IsScalarTower.of_algebraMap_eq (R := CR) (S := CR ⊗[F] F') (A := FFₗ ⊗[F] F') fun c => by
      show Algebra.TensorProduct.map (IsScalarTower.toAlgHom F CR FFₗ) (AlgHom.id F F')
          (algebraMap CR (CR ⊗[F] F') c) = algebraMap CR (FFₗ ⊗[F] F') c
      rfl
  haveI hloc : IsLocalization
      (Algebra.algebraMapSubmonoid (CR ⊗[F] F') (nonZeroDivisors CR)) (FFₗ ⊗[F] F') :=
    IsLocalization.tensorProduct_tensorProduct F F' (nonZeroDivisors CR) FFₗ (by
      ext x; simp [RingHom.algebraMap_toAlgebra, Algebra.TensorProduct.map_tmul])
  have hle : Algebra.algebraMapSubmonoid (CR ⊗[F] F') (nonZeroDivisors CR)
      ≤ nonZeroDivisors (CR ⊗[F] F') := by
    rintro _ ⟨c, hc, rfl⟩
    refine mem_nonZeroDivisors_of_ne_zero ?_
    have hinj : Function.Injective (algebraMap CR (CR ⊗[F] F')) :=
      Algebra.TensorProduct.includeLeft_injective (S := F) (algebraMap F F').injective
    exact fun h => (nonZeroDivisors.ne_zero hc) (hinj (by simp only [map_zero] at h ⊢; exact h))
  exact IsLocalization.isDomain_of_le_nonZeroDivisors
    (M := Algebra.algebraMapSubmonoid (CR ⊗[F] F') (nonZeroDivisors CR)) _ hle

end FFDomainNoAC

/-! ### The seam discharge

The finiteness and degree parts of the seam are the pin's flat/`IsIntegral`
argument: a basis of the `F`-module `(W⁄F).FunctionField` pushes forward along
`ι` and then along `⊗[F] F'`. The proof is written once, for a raw endomorphism
`ι`, and invoked by both the `NoAC` and the `General` seam. -/

section SeamAux

variable [IsDomain ((W⁄F).FunctionField ⊗[F] F')]

private def tensorIotaRingHomAux (ι : (W⁄F).FunctionField →ₐ[F] (W⁄F).FunctionField) :
    (W⁄F).FunctionField ⊗[F] F' →+* (W⁄F).FunctionField ⊗[F] F' :=
  (Algebra.TensorProduct.map ι (AlgHom.id F F')).toRingHom

private theorem tensorIotaRingHomAux_injective
    (ι : (W⁄F).FunctionField →ₐ[F] (W⁄F).FunctionField) :
    Function.Injective (tensorIotaRingHomAux W F F' ι) :=
  Module.Flat.rTensor_preserves_injective_linearMap (M := F') ι.toLinearMap ι.injective

private def tensorFracIotaRingHomAux (ι : (W⁄F).FunctionField →ₐ[F] (W⁄F).FunctionField) :
    FractionRing ((W⁄F).FunctionField ⊗[F] F')
      →+* FractionRing ((W⁄F).FunctionField ⊗[F] F') :=
  IsFractionRing.map (K := FractionRing ((W⁄F).FunctionField ⊗[F] F'))
    (L := FractionRing ((W⁄F).FunctionField ⊗[F] F'))
    (tensorIotaRingHomAux_injective W F F' ι)

private theorem tensorIotaRingHomAux_finite
    (ι : (W⁄F).FunctionField →ₐ[F] (W⁄F).FunctionField)
    (hι : ι.toRingHom.IsIntegral) (hfin : AlgebraicCurve.FiniteAlong F ι) :
    (tensorIotaRingHomAux W F F' ι).Finite :=
  RingHom.Finite.tensorProductMap (f := ι) hfin (g := AlgHom.id F F') (RingHom.Finite.id F')

private theorem tensorFracIotaFinrankSeam_aux
    (ι : (W⁄F).FunctionField →ₐ[F] (W⁄F).FunctionField)
    (hι : ι.toRingHom.IsIntegral) (hfin : AlgebraicCurve.FiniteAlong F ι) :
    (tensorFracIotaRingHomAux W F F' ι).Finite ∧
      (letI := (tensorFracIotaRingHomAux W F F' ι).toAlgebra
       @Module.finrank (FractionRing ((W⁄F).FunctionField ⊗[F] F'))
         (FractionRing ((W⁄F).FunctionField ⊗[F] F')) _ _ Algebra.toModule)
        = AlgebraicCurve.finrankAlong F ι := by
  classical
  let FF := (W⁄F).FunctionField
  let T := (W⁄F).FunctionField ⊗[F] F'
  let FrT := FractionRing ((W⁄F).FunctionField ⊗[F] F')
  let ιT : T →+* T := tensorIotaRingHomAux W F F' ι
  let ιFr : FrT →+* FrT := tensorFracIotaRingHomAux W F F' ι
  have hιT_inj : Function.Injective ιT := tensorIotaRingHomAux_injective W F F' ι
  have hιT_fin : ιT.Finite := tensorIotaRingHomAux_finite W F F' ι hι hfin
  have hιFr_am : ∀ t : T, ιFr (algebraMap T FrT t) = algebraMap T FrT (ιT t) := by
    intro t
    change tensorFracIotaRingHomAux W F F' ι (algebraMap T FrT t)
      = algebraMap T FrT (tensorIotaRingHomAux W F F' ι t)
    unfold tensorFracIotaRingHomAux IsFractionRing.map
    exact IsLocalization.map_eq (T := nonZeroDivisors T) _ t
  letI algDι : Algebra FF FF := ι.toRingHom.toAlgebra
  letI smulDι : SMul FF FF := algDι.toSMul
  letI modDι : Module FF FF := Algebra.toModule
  have hsmul_Dι : ∀ (c x : FF), c • x = ι c * x := fun c x => rfl
  haveI hfinFF : Module.Finite FF FF := hfin
  haveI hfreeFF : Module.Free FF FF := Module.Free.of_divisionRing FF FF
  let b : Module.Basis (Fin (AlgebraicCurve.finrankAlong F ι)) FF FF :=
    Module.finBasisOfFinrankEq FF FF (n := AlgebraicCurve.finrankAlong F ι) rfl
  have hrepr_mul : ∀ (c x : FF) (j : Fin (AlgebraicCurve.finrankAlong F ι)),
      b.repr (ι c * x) j = c * b.repr x j := fun c x j => by
    rw [← hsmul_Dι, map_smul, Finsupp.smul_apply, smul_eq_mul]
  let e : Fin (AlgebraicCurve.finrankAlong F ι) → T := fun i => (b i) ⊗ₜ[F] (1 : F')
  let bFr : Fin (AlgebraicCurve.finrankAlong F ι) → FrT := fun i => algebraMap T FrT (e i)
  have hspanT : ∀ t : T, ∃ c : Fin (AlgebraicCurve.finrankAlong F ι) → T,
      t = ∑ i, ιT (c i) * e i := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp⟩
    | add x y hx hy =>
      obtain ⟨cx, hx⟩ := hx; obtain ⟨cy, hy⟩ := hy
      exact ⟨cx + cy, by simp only [Pi.add_apply, map_add, add_mul,
        Finset.sum_add_distrib, ← hx, ← hy]⟩
    | tmul a c =>
      refine ⟨fun i => (b.repr a i) ⊗ₜ[F] c, ?_⟩
      have hb_sum : a = ∑ i, ι (b.repr a i) * b i := by
        conv_lhs => rw [← b.linearCombination_repr a, Finsupp.linearCombination_apply,
          Finsupp.sum_fintype _ _ (fun i => by rw [hsmul_Dι, _root_.map_zero, zero_mul])]
        exact Finset.sum_congr rfl fun i _ => hsmul_Dι _ _
      calc (a ⊗ₜ[F] c : T)
          = (∑ i, ι (b.repr a i) * b i) ⊗ₜ[F] c := by rw [← hb_sum]
        _ = ∑ i, ιT ((b.repr a i) ⊗ₜ[F] c) * e i := by
            rw [TensorProduct.sum_tmul]
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [show ιT ((b.repr a i) ⊗ₜ[F] c) = (ι (b.repr a i)) ⊗ₜ[F] c from rfl,
              Algebra.TensorProduct.tmul_mul_tmul, mul_one]
  have hliT : ∀ c : Fin (AlgebraicCurve.finrankAlong F ι) → T,
      ∑ i, ιT (c i) * e i = 0 → ∀ j, c j = 0 := by
    intro c hc j
    let pj : FF →ₗ[F] FF :=
      { toFun := fun x => b.repr x j
        map_add' := fun x y => by simp only [map_add, Finsupp.add_apply]
        map_smul' := fun f x => by
          simp only [RingHom.id_apply, Algebra.smul_def]
          have h := hrepr_mul (algebraMap F FF f) x j
          rwa [ι.commutes] at h }
    let Ej : T →ₗ[F] T := LinearMap.rTensor F' pj
    have hEj_key : ∀ (a : T) (i : Fin (AlgebraicCurve.finrankAlong F ι)),
        Ej (ιT a * e i) = if i = j then a else 0 := by
      intro a i
      induction a using TensorProduct.induction_on with
      | zero => simp
      | add x y hx hy =>
        simp only [map_add, add_mul, hx, hy]; split_ifs <;> simp
      | tmul x c' =>
        rw [show ιT ((x : FF) ⊗ₜ[F] c') = (ι x) ⊗ₜ[F] c' from rfl,
            Algebra.TensorProduct.tmul_mul_tmul, mul_one]
        show (pj (ι x * b i)) ⊗ₜ[F] c' = if i = j then (x : FF) ⊗ₜ[F] c' else 0
        rw [show pj (ι x * b i) = if i = j then x else 0 from ?_]
        · split_ifs with h
          · rfl
          · exact TensorProduct.zero_tmul _ c'
        · show b.repr (ι x * b i) j = if i = j then x else 0
          rw [hrepr_mul, b.repr_self, Finsupp.single_apply]
          split_ifs with h <;> simp [h]
    have hc' : Ej (∑ i, ιT (c i) * e i) = 0 := by rw [hc, _root_.map_zero]
    simpa only [map_sum, hEj_key, Finset.sum_ite_eq', Finset.mem_univ, if_true] using hc'
  have hint : ∀ s : T, s ≠ 0 → ∃ (u s₀ : T), s₀ ≠ 0 ∧ s * u = ιT s₀ := by
    intro s hs
    obtain ⟨p, hp_monic, hp_eval⟩ : ιT.IsIntegralElem s := hιT_fin.to_isIntegral s
    obtain ⟨q, hq_eq, hq_ndvd⟩ := Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd p
      hp_monic.ne_zero 0
    simp only [Polynomial.C_0, sub_zero] at hq_eq hq_ndvd
    have hq0 : q.coeff 0 ≠ 0 := fun h => hq_ndvd (Polynomial.X_dvd_iff.mpr h)
    have hqs : q.eval₂ ιT s = 0 := by
      have h := hp_eval
      rw [hq_eq, Polynomial.eval₂_mul, Polynomial.eval₂_pow, Polynomial.eval₂_X,
        mul_eq_zero] at h
      exact h.resolve_left (pow_ne_zero _ hs)
    have h3 : ιT (q.coeff 0) + s * (q.divX).eval₂ ιT s = 0 := by
      have h := hqs
      conv at h => lhs; rw [← Polynomial.divX_mul_X_add q]
      simpa [Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_X,
        Polynomial.eval₂_C, add_comm, mul_comm] using h
    exact ⟨(q.divX).eval₂ ιT s, -q.coeff 0, neg_ne_zero.mpr hq0,
      by rw [_root_.map_neg]; exact eq_neg_of_add_eq_zero_right h3⟩
  have hspanFr : ∀ z : FrT, ∃ d : Fin (AlgebraicCurve.finrankAlong F ι) → FrT,
      z = ∑ i, ιFr (d i) * bFr i := by
    intro z
    obtain ⟨t, s, hs, rfl⟩ := IsFractionRing.div_surjective (A := T) (K := FrT) z
    rcases eq_or_ne s 0 with rfl | hs'
    · exact ⟨0, by simp⟩
    obtain ⟨u, s₀, hs₀, hsu⟩ := hint s hs'
    have hιTs₀ : ιT s₀ ≠ 0 := fun h => hs₀ (hιT_inj (h.trans (_root_.map_zero ιT).symm))
    have hu_ne : u ≠ 0 := fun h => hιTs₀ (by rw [← hsu, h, mul_zero])
    obtain ⟨c, hc⟩ := hspanT (t * u)
    refine ⟨fun i => (algebraMap T FrT s₀)⁻¹ * algebraMap T FrT (c i), ?_⟩
    have hum := (map_ne_zero_iff _ (IsFractionRing.injective T FrT)).mpr hu_ne
    have hz : (algebraMap T FrT t) / (algebraMap T FrT s)
        = (algebraMap T FrT (ιT s₀))⁻¹ * algebraMap T FrT (t * u) := by
      rw [← div_eq_inv_mul, ← hsu, map_mul, map_mul,
        ← div_mul_div_comm, div_self hum, mul_one]
    rw [hz, hc, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, map_mul, ← hιFr_am s₀, ← hιFr_am (c i), ← map_inv₀ ιFr, mul_assoc]
  have hliFr : ∀ d : Fin (AlgebraicCurve.finrankAlong F ι) → FrT,
      ∑ i, ιFr (d i) * bFr i = 0 → ∀ j, d j = 0 := by
    intro d hd j
    obtain ⟨q, hq⟩ := IsLocalization.exist_integer_multiples_of_finset
      (nonZeroDivisors T) (Finset.univ.image d)
    choose p hp using fun i => hq (d i) (Finset.mem_image_of_mem d (Finset.mem_univ i))
    have hq0 : (algebraMap T FrT (q : T)) ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective T FrT)).mpr (nonZeroDivisors.ne_zero q.2)
    have hp' : ∀ i, algebraMap T FrT (p i) = algebraMap T FrT (q : T) * d i := fun i => by
      rw [hp i, Algebra.smul_def]
    have hd' : algebraMap T FrT (∑ i, ιT (p i) * e i) = 0 := by
      have h1 : ∑ i, ιFr (algebraMap T FrT (q : T)) * (ιFr (d i) * bFr i) = 0 := by
        rw [← Finset.mul_sum, hd, mul_zero]
      rw [map_sum, ← h1]; refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_mul, ← hιFr_am (p i), ← mul_assoc, ← map_mul, ← hp' i]
    have hpj : p j = 0 :=
      hliT p ((IsFractionRing.injective T FrT) (by simpa using hd')) j
    have hthis : algebraMap T FrT (q : T) * d j = 0 := by
      rw [← hp' j, hpj, _root_.map_zero]
    exact (mul_eq_zero.mp hthis).resolve_left hq0
  letI algFr : Algebra FrT FrT := ιFr.toAlgebra
  letI smulFr : SMul FrT FrT := algFr.toSMul
  letI modFr : Module FrT FrT := Algebra.toModule
  have hsmul_Fr : ∀ (c x : FrT), c • x = ιFr c * x := fun c x => rfl
  have hli_modFr : LinearIndependent FrT bFr := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    refine hliFr g ?_ i
    simpa only [hsmul_Fr] using hg
  have hsp_modFr : ⊤ ≤ Submodule.span FrT (Set.range bFr) := by
    intro z _
    obtain ⟨d, hd⟩ := hspanFr z
    rw [hd]
    exact Submodule.sum_mem _ fun i _ => (hsmul_Fr (d i) (bFr i)) ▸
      Submodule.smul_mem _ (d i) (Submodule.subset_span ⟨i, rfl⟩)
  let bFr' : Module.Basis (Fin (AlgebraicCurve.finrankAlong F ι)) FrT FrT :=
    .mk hli_modFr hsp_modFr
  refine ⟨Module.Finite.of_basis bFr', ?_⟩
  show Module.finrank FrT FrT = AlgebraicCurve.finrankAlong F ι
  rw [Module.finrank_eq_card_basis bFr', Fintype.card_fin]

end SeamAux

section SeamNoAC

variable [IsDomain ((W⁄F).FunctionField ⊗[F] F')]

theorem kw_tensorIotaRingHom_finiteGeneralNoAC (D : TreeIsogenyEndDatum (W⁄F)) :
    (kw_tensorIotaRingHomGeneralNoAC W F F' D).Finite :=
  RingHom.Finite.tensorProductMap (f := D.ι) D.hfin (g := AlgHom.id F F') (RingHom.Finite.id F')

theorem kw_tensorFracIotaFinrankSeam_dischargeGeneralNoAC :
    KwTensorFracIotaFinrankSeamGeneralNoAC W F F' := by
  intro D
  exact tensorFracIotaFinrankSeam_aux W F F' D.ι D.hι D.hfin

end SeamNoAC

theorem kw_isogenyEndDatumBaseChangeAlong_dischargeGeneralNoAC (σ : F →ₐ[R₀] F') (N : ℕ) :
    KwIsogenyEndDatumBaseChangeAlongGeneralNoAC W F F' σ N :=
  haveI : IsDomain ((W⁄F).FunctionField ⊗[F] F') :=
    kw_functionFieldTensorIsDomain_dischargeGeneralNoAC W F F'
  kw_isogenyEndDatumBaseChangeAlong_of_tensorIsDomainGeneralNoAC W F F'
    (kw_functionFieldTensorIsDomain_dischargeGeneralNoAC W F F')
    (kw_tensorFracIotaFinrankSeam_dischargeGeneralNoAC W F F') σ N

end NoAC

/-! ### The `General` spelling

The same block with `[IsAlgClosed F] [IsAlgClosed F']` added — the spelling the
`bcff` node and the two silos use. The `NoAC` lemmas above are strictly more
general, so every declaration whose type does not mention the datum is a one-line
invocation of its `NoAC` twin; the datum-indexed declarations (`IsogenyEndDatum`
here against `TreeIsogenyEndDatum` above) are distinct types and are proved
directly. -/

section General

variable {R₀ : Type u} [Field R₀]
variable (W : WeierstrassCurve R₀) [W.IsElliptic]
variable (F : Type u) [Field F] [Algebra R₀ F] [DecidableEq F] [IsAlgClosed F] [CharZero F]
variable (F' : Type u) [Field F'] [Algebra R₀ F'] [DecidableEq F'] [IsAlgClosed F'] [CharZero F']
variable [Algebra F F'] [IsScalarTower R₀ F F']

theorem kw_transcendental_polyToFunctionField_X_over_baseGeneral :
    Transcendental F (polyToFunctionField (W⁄F') X) :=
  kw_transcendental_polyToFunctionField_X_over_baseGeneralNoAC W F F'

theorem kw_equation_map_polyToFunctionField_yGen_over_baseGeneral :
    ((W⁄F).map (algebraMap F (W⁄F').FunctionField)).toAffine.Equation
      (polyToFunctionField (W⁄F') X) (yGen (W⁄F')) :=
  kw_equation_map_polyToFunctionField_yGen_over_baseGeneralNoAC W F F'

def kw_functionFieldMapAlongGeneral : (W⁄F).FunctionField →ₐ[F] (W⁄F').FunctionField :=
  kw_functionFieldMapAlongGeneralNoAC W F F'

theorem kw_functionFieldMapAlongGeneral_polyToFunctionField_X :
    kw_functionFieldMapAlongGeneral W F F' (polyToFunctionField (W⁄F) X)
      = polyToFunctionField (W⁄F') X :=
  kw_functionFieldMapAlongGeneralNoAC_polyToFunctionField_X W F F'

theorem kw_functionFieldMapAlongGeneral_yGen :
    kw_functionFieldMapAlongGeneral W F F' (yGen (W⁄F)) = yGen (W⁄F') :=
  kw_functionFieldMapAlongGeneralNoAC_yGen W F F'

def KwFunctionFieldTensorIsDomainGeneral : Prop :=
  IsDomain ((W⁄F).FunctionField ⊗[F] F')

attribute [local instance] Algebra.TensorProduct.rightAlgebra

scoped instance kw_isScalarTower_base_right_tensorGeneral :
    IsScalarTower R₀ F' ((W⁄F).FunctionField ⊗[F] F') :=
  kw_isScalarTower_base_right_tensorGeneralNoAC (R₀ := R₀) W F F'

section FracHomGeneral

variable [IsDomain ((W⁄F).FunctionField ⊗[F] F')]

scoped instance kw_isScalarTower_base_right_fracTensorGeneral :
    IsScalarTower R₀ F' (FractionRing ((W⁄F).FunctionField ⊗[F] F')) :=
  kw_isScalarTower_base_right_fracTensorGeneralNoAC (R₀ := R₀) W F F'

theorem kw_equation_tensorFracXYGeneral :
    ((W⁄F').map (algebraMap F' (FractionRing ((W⁄F).FunctionField ⊗[F] F')))).toAffine.Equation
      (algebraMap ((W⁄F).FunctionField ⊗[F] F')
        (FractionRing ((W⁄F).FunctionField ⊗[F] F'))
        ((polyToFunctionField (W⁄F) X) ⊗ₜ[F] (1 : F')))
      (algebraMap ((W⁄F).FunctionField ⊗[F] F')
        (FractionRing ((W⁄F).FunctionField ⊗[F] F'))
        ((yGen (W⁄F)) ⊗ₜ[F] (1 : F'))) :=
  kw_equation_tensorFracXYGeneralNoAC W F F'

theorem kw_transcendental_tensorFracXGeneral :
    Function.Injective (Polynomial.aeval (R := F')
      (algebraMap ((W⁄F).FunctionField ⊗[F] F')
        (FractionRing ((W⁄F).FunctionField ⊗[F] F'))
        ((polyToFunctionField (W⁄F) X) ⊗ₜ[F] (1 : F')))) :=
  kw_transcendental_tensorFracXGeneralNoAC W F F'

def kw_functionFieldTensorFracHomGeneral :
    (W⁄F').FunctionField →ₐ[F'] FractionRing ((W⁄F).FunctionField ⊗[F] F') :=
  kw_functionFieldTensorFracHomGeneralNoAC W F F'

theorem kw_functionFieldTensorFracHomGeneral_X :
    kw_functionFieldTensorFracHomGeneral W F F' (polyToFunctionField (W⁄F') X)
      = algebraMap ((W⁄F).FunctionField ⊗[F] F') _
          ((polyToFunctionField (W⁄F) X) ⊗ₜ[F] (1 : F')) :=
  kw_functionFieldTensorFracHomGeneralNoAC_X W F F'

theorem kw_functionFieldTensorFracHomGeneral_yGen :
    kw_functionFieldTensorFracHomGeneral W F F' (yGen (W⁄F'))
      = algebraMap ((W⁄F).FunctionField ⊗[F] F') _ ((yGen (W⁄F)) ⊗ₜ[F] (1 : F')) :=
  kw_functionFieldTensorFracHomGeneralNoAC_yGen W F F'

theorem kw_functionFieldTensorFracHomGeneral_bijective :
    Function.Bijective (kw_functionFieldTensorFracHomGeneral W F F') :=
  kw_functionFieldTensorFracHomGeneralNoAC_bijective W F F'

def kw_functionFieldTensorFracEquivGeneral :
    (W⁄F').FunctionField ≃ₐ[F'] FractionRing ((W⁄F).FunctionField ⊗[F] F') :=
  kw_functionFieldTensorFracEquivGeneralNoAC W F F'

def kw_tensorIotaRingHomGeneral (D : IsogenyEndDatum (W⁄F)) :
    (W⁄F).FunctionField ⊗[F] F' →+* (W⁄F).FunctionField ⊗[F] F' :=
  (Algebra.TensorProduct.map D.ι (AlgHom.id F F')).toRingHom

theorem kw_tensorIotaRingHomGeneral_tmul (D : IsogenyEndDatum (W⁄F)) (a : (W⁄F).FunctionField)
    (c : F') : kw_tensorIotaRingHomGeneral W F F' D (a ⊗ₜ[F] c) = (D.ι a) ⊗ₜ[F] c := by
  simp [kw_tensorIotaRingHomGeneral, Algebra.TensorProduct.map_tmul]

theorem kw_tensorIotaRingHomGeneral_injective (D : IsogenyEndDatum (W⁄F)) :
    Function.Injective (kw_tensorIotaRingHomGeneral W F F' D) :=
  Module.Flat.rTensor_preserves_injective_linearMap (M := F') D.ι.toLinearMap D.ι.injective

def kw_tensorFracIotaRingHomGeneral (D : IsogenyEndDatum (W⁄F)) :
    FractionRing ((W⁄F).FunctionField ⊗[F] F')
      →+* FractionRing ((W⁄F).FunctionField ⊗[F] F') :=
  IsFractionRing.map (K := FractionRing ((W⁄F).FunctionField ⊗[F] F'))
    (L := FractionRing ((W⁄F).FunctionField ⊗[F] F'))
    (kw_tensorIotaRingHomGeneral_injective W F F' D)

theorem kw_tensorFracIotaRingHomGeneral_algebraMap (D : IsogenyEndDatum (W⁄F))
    (t : (W⁄F).FunctionField ⊗[F] F') :
    kw_tensorFracIotaRingHomGeneral W F F' D
        (algebraMap ((W⁄F).FunctionField ⊗[F] F')
          (FractionRing ((W⁄F).FunctionField ⊗[F] F')) t)
      = algebraMap ((W⁄F).FunctionField ⊗[F] F') (FractionRing ((W⁄F).FunctionField ⊗[F] F'))
          (kw_tensorIotaRingHomGeneral W F F' D t) := by
  unfold kw_tensorFracIotaRingHomGeneral IsFractionRing.map
  exact IsLocalization.map_eq (T := nonZeroDivisors ((W⁄F).FunctionField ⊗[F] F')) _ t

def KwTensorFracIotaFinrankSeamGeneral : Prop :=
  ∀ D : IsogenyEndDatum (W⁄F),
    (kw_tensorFracIotaRingHomGeneral W F F' D).Finite ∧
    (letI := (kw_tensorFracIotaRingHomGeneral W F F' D).toAlgebra
     @Module.finrank (FractionRing ((W⁄F).FunctionField ⊗[F] F'))
       (FractionRing ((W⁄F).FunctionField ⊗[F] F')) _ _ Algebra.toModule)
      = AlgebraicCurve.finrankAlong F D.ι

def kw_isogenyEndDatumBaseChangeIotaGeneral (D : IsogenyEndDatum (W⁄F)) :
    (W⁄F').FunctionField →ₐ[F'] (W⁄F').FunctionField :=
  let ψ := kw_functionFieldTensorFracEquivGeneral W F F'
  { ψ.symm.toRingEquiv.toRingHom.comp
      ((kw_tensorFracIotaRingHomGeneral W F F' D).comp ψ.toRingEquiv.toRingHom) with
    commutes' := fun c => by
      have hc : ψ (algebraMap F' (W⁄F').FunctionField c)
          = algebraMap ((W⁄F).FunctionField ⊗[F] F')
              (FractionRing ((W⁄F).FunctionField ⊗[F] F'))
              ((1 : (W⁄F).FunctionField) ⊗ₜ[F] c) := by
        rw [AlgEquiv.commutes, IsScalarTower.algebraMap_apply F' ((W⁄F).FunctionField ⊗[F] F')
          (FractionRing ((W⁄F).FunctionField ⊗[F] F')),
          Algebra.TensorProduct.right_algebraMap_apply]
      show ψ.symm (kw_tensorFracIotaRingHomGeneral W F F' D (ψ (algebraMap F' _ c)))
          = algebraMap F' _ c
      rw [hc, kw_tensorFracIotaRingHomGeneral_algebraMap, kw_tensorIotaRingHomGeneral_tmul,
        map_one, ← hc]
      exact ψ.symm_apply_apply _ }

def KwIsogenyEndDatumBaseChangeAlongGeneral (_σ : F →ₐ[R₀] F') (N : ℕ) : Prop :=
  (∃ D : IsogenyEndDatum (W⁄F), AlgebraicCurve.finrankAlong F D.ι = N) →
    ∃ D' : IsogenyEndDatum (W⁄F'), AlgebraicCurve.finrankAlong F' D'.ι = N

theorem kw_isogenyEndDatumBaseChangeAlong_of_isDomain_tensorGeneral
    (hseam : KwTensorFracIotaFinrankSeamGeneral W F F')
    (σ : F →ₐ[R₀] F') (N : ℕ) : KwIsogenyEndDatumBaseChangeAlongGeneral W F F' σ N := by
  intro ⟨D, hD⟩
  let ψ := kw_functionFieldTensorFracEquivGeneral W F F'
  let ιFr := kw_tensorFracIotaRingHomGeneral W F F' D
  obtain ⟨hfin_Fr, hdeg_Fr⟩ := hseam D
  have hcomm : ∀ x, ιFr (ψ x) = ψ (kw_isogenyEndDatumBaseChangeIotaGeneral W F F' D x) :=
    fun x => (ψ.apply_symm_apply _).symm
  have hfin : (kw_isogenyEndDatumBaseChangeIotaGeneral W F F' D).toRingHom.Finite := by
    have h₁ : (kw_isogenyEndDatumBaseChangeIotaGeneral W F F' D).toRingHom
        = ψ.symm.toRingEquiv.toRingHom.comp (ιFr.comp ψ.toRingEquiv.toRingHom) := rfl
    rw [h₁]
    exact (RingHom.Finite.of_surjective _ ψ.symm.surjective).comp
      (hfin_Fr.comp (RingHom.Finite.of_surjective _ ψ.surjective))
  refine ⟨⟨kw_isogenyEndDatumBaseChangeIotaGeneral W F F' D, hfin.to_isIntegral, hfin⟩, ?_⟩
  refine hD ▸ ?_
  exact (@Algebra.finrank_eq_of_equiv_equiv
      (W⁄F').FunctionField (W⁄F').FunctionField _ _
      (AlgebraicCurve.algebraAlong (kw_isogenyEndDatumBaseChangeIotaGeneral W F F' D))
      (FractionRing ((W⁄F).FunctionField ⊗[F] F'))
      (FractionRing ((W⁄F).FunctionField ⊗[F] F')) _ _
      (ιFr.toAlgebra) ψ.toRingEquiv ψ.toRingEquiv
      (RingHom.ext hcomm)).trans hdeg_Fr

end FracHomGeneral

theorem kw_isogenyEndDatumBaseChangeAlong_of_tensorIsDomainGeneral
    (htens : KwFunctionFieldTensorIsDomainGeneral W F F')
    (hseam : haveI : IsDomain ((W⁄F).FunctionField ⊗[F] F') := htens
             KwTensorFracIotaFinrankSeamGeneral W F F')
    (σ : F →ₐ[R₀] F') (N : ℕ) :
    KwIsogenyEndDatumBaseChangeAlongGeneral W F F' σ N :=
  haveI : IsDomain ((W⁄F).FunctionField ⊗[F] F') := htens
  kw_isogenyEndDatumBaseChangeAlong_of_isDomain_tensorGeneral W F F' hseam σ N

section FFDomainGeneral

attribute [local instance] Algebra.TensorProduct.rightAlgebra

local notation3 "CR" => (W⁄F).toAffine.CoordinateRing
local notation3 "FFₗ" => (W⁄F).FunctionField

theorem kw_coordinateRingMap_basisGeneral (i : ℕ × Fin 2) :
    CoordinateRing.map (W⁄F).toAffine (algebraMap F F')
        (kw_coordinateRingBasis (W⁄F).toAffine i)
      = kw_coordinateRingBasis ((W⁄F).toAffine.map (algebraMap F F')) i :=
  kw_coordinateRingMap_basisGeneralNoAC W F F' i

def kw_coordinateRingMapAlongGeneral :
    CR →ₐ[F] ((W⁄F).toAffine.map (algebraMap F F')).CoordinateRing :=
  kw_coordinateRingMapAlongGeneralNoAC W F F'

theorem kw_coordinateRingTensor_isDomainGeneral : IsDomain (CR ⊗[F] F') :=
  kw_coordinateRingTensor_isDomainGeneralNoAC W F F'

theorem kw_functionFieldTensorIsDomain_dischargeGeneral :
    KwFunctionFieldTensorIsDomainGeneral W F F' :=
  kw_functionFieldTensorIsDomain_dischargeGeneralNoAC W F F'

end FFDomainGeneral

section SeamGeneral

variable [IsDomain ((W⁄F).FunctionField ⊗[F] F')]

theorem kw_tensorIotaRingHom_finiteGeneral (D : IsogenyEndDatum (W⁄F)) :
    (kw_tensorIotaRingHomGeneral W F F' D).Finite :=
  RingHom.Finite.tensorProductMap (f := D.ι) D.hfin (g := AlgHom.id F F') (RingHom.Finite.id F')

theorem kw_tensorFracIotaFinrankSeam_dischargeGeneral :
    KwTensorFracIotaFinrankSeamGeneral W F F' := by
  intro D
  exact tensorFracIotaFinrankSeam_aux W F F' D.ι D.hι D.hfin

end SeamGeneral

theorem kw_isogenyEndDatumBaseChangeAlong_dischargeGeneral (σ : F →ₐ[R₀] F') (N : ℕ) :
    KwIsogenyEndDatumBaseChangeAlongGeneral W F F' σ N :=
  haveI : IsDomain ((W⁄F).FunctionField ⊗[F] F') :=
    kw_functionFieldTensorIsDomain_dischargeGeneral W F F'
  kw_isogenyEndDatumBaseChangeAlong_of_tensorIsDomainGeneral W F F'
    (kw_functionFieldTensorIsDomain_dischargeGeneral W F F')
    (kw_tensorFracIotaFinrankSeam_dischargeGeneral W F F') σ N

end General

end ModularCurve
