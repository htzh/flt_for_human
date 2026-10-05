/-
The unit ideal of a point (and of a divisor), its class in the Weil class group,
and Abel's theorem in genus one: a degree-zero divisor is principal iff its
geometric divisor sum is zero.

Transcribed verbatim from the pinned FLT `aa2d8b3`:
`P2M/Sol/S_WeierstrassCurve_Affine_exists_genusOnePlaceGate_isCentred_and_abelTheorem.lean`
(lines 1907–2076).  This is the block `CARRY-FORWARD.md` registered as deferred
from the A1 file ("Port it when a `genusOnePlaceGate`/RR consumer is taken"); the
genus-one headline is that consumer.

It builds on the geometric point↔place bijection
(`WeierstrassCurve/Place/GeometricPlace.lean`), the generic Dedekind count
lemmas (`AlgebraicCurve/PrincipalDivisors/Count.lean`) and mathlib's
`Affine.Point.toClass` class-group homomorphism.  Only proof bodies are adapted;
declaration names, namespaces and kinds are kept.

Reference (public mirror, pinned):
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_WeierstrassCurve_Affine_exists_genusOnePlaceGate_isCentred_and_abelTheorem.lean>
-/
import FLTForHuman.WeierstrassCurve.Place.GeometricPlace
import FLTForHuman.AlgebraicCurve.PrincipalDivisors.Count

set_option autoImplicit false
set_option linter.unusedSectionVars false
-- The pin's `haveI` instance walls are transcribed literally.
set_option linter.style.haveILetI false

noncomputable section

open AlgebraicCurve WeierstrassCurve WeierstrassCurve.Affine
open IsDedekindDomain FractionalIdeal
open scoped nonZeroDivisors

namespace WeierstrassCurve.Affine

universe u

variable {F : Type u} [Field F] [DecidableEq F] {W : Affine F}
variable [IsAlgClosed F] [W.IsElliptic] [InfinitePlace W]
-- The pin supplies the Dedekind instance through its `scoped instance` in the
-- `CoordinateRing` namespace; the port's copy needs to be supplied explicitly
-- (the checker diffs statement text, where section variables do not appear).
variable [IsDedekindDomain W.CoordinateRing]

omit [DecidableEq F] [InfinitePlace W] in

theorem isFinitePlace_ofHeightOneSpectrum (w : HeightOneSpectrum W.CoordinateRing) :
    IsFinitePlace (W := W)
      (AlgebraicCurve.Place.ofHeightOneSpectrum (K := F) (F := W.FunctionField) w) := fun r =>
  w.valuation_le_one r

omit [DecidableEq F] in

theorem infinitePlace_ne_ofHeightOneSpectrum (w : HeightOneSpectrum W.CoordinateRing) :
    (InfinitePlace.place : AlgebraicCurve.Place F W.FunctionField)
      ≠ AlgebraicCurve.Place.ofHeightOneSpectrum (K := F) w := fun h =>
  InfinitePlace.not_isFinitePlace (W := W) (h ▸ isFinitePlace_ofHeightOneSpectrum w)

def unitIdealOfPoint : W.Point → (FractionalIdeal W.CoordinateRing⁰ W.FunctionField)ˣ
  | .zero => 1
  | .some _ _ h => CoordinateRing.XYIdeal' h

omit [DecidableEq F] [InfinitePlace W] in
@[scoped simp]
theorem unitIdealOfPoint_zero : unitIdealOfPoint (.zero : W.Point) = 1 := rfl

omit [DecidableEq F] [InfinitePlace W] in
@[scoped simp]
theorem unitIdealOfPoint_some {x y : F} (h : W.Nonsingular x y) :
    unitIdealOfPoint (.some x y h) = CoordinateRing.XYIdeal' h := rfl

omit [InfinitePlace W] in

theorem classGroup_mk_unitIdealOfPoint (P : W.Point) :
    ClassGroup.mk (K := W.FunctionField) (unitIdealOfPoint P) = Additive.toMul (Point.toClass P) := by
  cases P with
  | zero => exact map_one _
  | some x y h => rfl

def unitIdealOfDivisor (D : AlgebraicCurve.Divisor F W.FunctionField) :
    (FractionalIdeal W.CoordinateRing⁰ W.FunctionField)ˣ :=
  D.prod fun v n => unitIdealOfPoint (geomPointEquivPlace.symm v) ^ n

omit [DecidableEq F] in
@[scoped simp]
theorem unitIdealOfDivisor_zero :
    unitIdealOfDivisor (0 : AlgebraicCurve.Divisor F W.FunctionField) = 1 :=
  Finsupp.prod_zero_index

omit [DecidableEq F] in
theorem unitIdealOfDivisor_add (D E : AlgebraicCurve.Divisor F W.FunctionField) :
    unitIdealOfDivisor (D + E) = unitIdealOfDivisor D * unitIdealOfDivisor E :=
  Finsupp.prod_add_index' (fun _ => zpow_zero _) fun _ m n => _root_.zpow_add _ m n

omit [DecidableEq F] in
theorem unitIdealOfDivisor_single (v : AlgebraicCurve.Place F W.FunctionField) (n : ℤ) :
    unitIdealOfDivisor (Finsupp.single v n) = unitIdealOfPoint (geomPointEquivPlace.symm v) ^ n :=
  Finsupp.prod_single_index (zpow_zero _)

theorem classGroup_mk_unitIdealOfDivisor (D : AlgebraicCurve.Divisor F W.FunctionField) :
    ClassGroup.mk (K := W.FunctionField) (unitIdealOfDivisor D)
      = Additive.toMul (Point.toClass (geomDivisorSum D)) := by
  induction D using Finsupp.induction with
  | zero =>
      rw [unitIdealOfDivisor_zero, map_one, _root_.map_zero, _root_.map_zero]
      rfl
  | single_add v n E _ _ ih =>
      rw [unitIdealOfDivisor_add, map_mul, ih, unitIdealOfDivisor_single, map_zpow,
        classGroup_mk_unitIdealOfPoint, map_add, geomDivisorSum_single, map_add, toMul_add,
        map_zsmul, toMul_zsmul]

omit [DecidableEq F] in

theorem count_unitIdealOfDivisor (D : AlgebraicCurve.Divisor F W.FunctionField)
    (w : HeightOneSpectrum W.CoordinateRing) :
    FractionalIdeal.count W.FunctionField w (unitIdealOfDivisor D : _) =
      D (AlgebraicCurve.Place.ofHeightOneSpectrum (K := F) w) := by
  classical
  induction D using Finsupp.induction with
  | zero =>
      rw [unitIdealOfDivisor_zero, Units.val_one, FractionalIdeal.count_one]
      rfl
  | single_add v n E _ _ ih =>
      rw [unitIdealOfDivisor_add, Units.val_mul,
        FractionalIdeal.count_mul _ _ (Units.ne_zero _) (Units.ne_zero _), ih,
        Finsupp.add_apply, unitIdealOfDivisor_single, Units.val_zpow_eq_zpow_val,
        FractionalIdeal.count_zpow, Finsupp.single_apply]
      congr 1
      obtain ⟨P, rfl⟩ := geomPointEquivPlace.surjective v
      rw [Equiv.symm_apply_apply]
      cases P with
      | zero =>
          rw [unitIdealOfPoint_zero, Units.val_one, FractionalIdeal.count_one, mul_zero,
            if_neg]
          exact infinitePlace_ne_ofHeightOneSpectrum w
      | some x y h =>
          rw [unitIdealOfPoint_some, CoordinateRing.XYIdeal'_eq,
            show (CoordinateRing.XYIdeal W x (Polynomial.C y) :
                FractionalIdeal W.CoordinateRing⁰ W.FunctionField)
              = ((CoordinateRing.heightOneSpectrumOfEquation h.left).asIdeal :
                FractionalIdeal W.CoordinateRing⁰ W.FunctionField) from rfl,
            FractionalIdeal.count_maximal]
          simp only [geomPointEquivPlace_apply, geomPlaceOfPoint_some, placeOfEquation,
            (AlgebraicCurve.Place.ofHeightOneSpectrum_injective
              (K := F) (R := W.CoordinateRing) (F := W.FunctionField)).eq_iff]
          split_ifs <;> ring

theorem geomDivisorSum_eq_zero_of_isPrincipal' {D : AlgebraicCurve.Divisor F W.FunctionField}
    (hD : Divisor.IsPrincipal D) : geomDivisorSum D = 0 := by
  obtain ⟨f, hf, hDf⟩ := hD

  have key : (unitIdealOfDivisor D : FractionalIdeal W.CoordinateRing⁰ W.FunctionField)
      = FractionalIdeal.spanSingleton W.CoordinateRing⁰ f :=
    FractionalIdeal.eq_of_count_eq (Units.ne_zero _)
      (FractionalIdeal.spanSingleton_ne_zero_iff.mpr hf) fun w => by
        rw [count_unitIdealOfDivisor, hDf,
          AlgebraicCurve.Place.ord_ofHeightOneSpectrum_eq_count w hf]

  have hcls : ClassGroup.mk (K := W.FunctionField) (unitIdealOfDivisor D) = 1 :=
    ClassGroup.mk_eq_one_iff.mpr ((FractionalIdeal.isPrincipal_iff _).mpr ⟨f, key⟩)

  apply Point.toClass_injective
  rw [_root_.map_zero]
  rw [classGroup_mk_unitIdealOfDivisor] at hcls
  exact Additive.toMul.injective hcls

theorem isPrincipal_of_geomDivisorSum_eq_zero' [HasPrincipalDivisors F W.FunctionField]
    {D : AlgebraicCurve.Divisor F W.FunctionField} (h0 : Divisor.degree D = 0)
    (hD : geomDivisorSum D = 0) : Divisor.IsPrincipal D := by
  classical

  have hcls : ClassGroup.mk (K := W.FunctionField) (unitIdealOfDivisor D) = 1 := by
    rw [classGroup_mk_unitIdealOfDivisor, hD, _root_.map_zero]
    rfl

  obtain ⟨f, hf⟩ := (FractionalIdeal.isPrincipal_iff _).mp (ClassGroup.mk_eq_one_iff.mp hcls)
  have hf0 : f ≠ 0 := by
    rintro rfl
    rw [FractionalIdeal.spanSingleton_zero] at hf
    exact Units.ne_zero (unitIdealOfDivisor D) hf

  have hfin : ∀ w : HeightOneSpectrum W.CoordinateRing,
      D (AlgebraicCurve.Place.ofHeightOneSpectrum (K := F) w)
        = (AlgebraicCurve.Place.ofHeightOneSpectrum (K := F) w).ord f := by
    intro w
    rw [← count_unitIdealOfDivisor, hf,
      AlgebraicCurve.Place.ord_ofHeightOneSpectrum_eq_count w hf0]

  obtain ⟨Df, hDf, hDf0⟩ := HasPrincipalDivisors.exists_divisor (K := F) f hf0

  have hsub : D - Df = Finsupp.single (InfinitePlace.place :
      AlgebraicCurve.Place F W.FunctionField) ((D - Df) InfinitePlace.place) := by
    ext v
    obtain ⟨P, rfl⟩ := geomPlaceOfPoint_surjective isElliptic_Δ_ne_zero v
    cases P with
    | zero =>
        rw [geomPlaceOfPoint_zero, Finsupp.single_eq_same]
    | some x y h =>
        rw [Finsupp.sub_apply, geomPlaceOfPoint_some, placeOfEquation, hfin, hDf, sub_self,
          Finsupp.single_apply, if_neg]
        exact infinitePlace_ne_ofHeightOneSpectrum _

  have hdeg : Divisor.degree (D - Df) = 0 := by rw [map_sub, h0, hDf0, sub_zero]
  rw [hsub, Divisor.degree_single, InfinitePlace.deg_eq_one, Nat.cast_one, mul_one,
    Finsupp.sub_apply, sub_eq_zero] at hdeg

  refine ⟨f, hf0, fun v => ?_⟩
  obtain ⟨P, rfl⟩ := geomPlaceOfPoint_surjective isElliptic_Δ_ne_zero v
  cases P with
  | zero => rw [geomPlaceOfPoint_zero, hdeg, hDf]
  | some x y h => rw [geomPlaceOfPoint_some, placeOfEquation, hfin]

scoped instance instAbelTheorem [HasPrincipalDivisors F W.FunctionField] : GeomAbelTheorem W where
  isPrincipal_iff_geomDivisorSum_eq_zero _D h0 :=
    ⟨geomDivisorSum_eq_zero_of_isPrincipal', isPrincipal_of_geomDivisorSum_eq_zero' h0⟩

end WeierstrassCurve.Affine

end
