/-
The Weierstrass genus-one place gate: the bundled bijection between the rational
points of an affine Weierstrass curve and the degree-one places of its function
field, the divisor/`Pic0` dictionary that it induces, the `AbelTheorem` carrier,
and the `IsCentred` refinement.

Transcribed verbatim from the pinned FLT `aa2d8b3`:

* `Definitions/Def_WeierstrassCurve_GenusOnePic0.lean` (171 lines / 29 declarations);
* `Definitions/Def_WeierstrassCurve_GenusOnePlaceGateCentred.lean` (40 / 3);

and the three statement wrappers

* `Theorems/Thm_WeierstrassCurve_Affine_placeOfPoint_some_eq_ofHeightOneSpectrum.lean`;
* `Theorems/Thm_WeierstrassCurve_Affine_algebraMap_mk_C_X_notMem_toValuationSubring_placeOfPoint_zero.lean`;
* `Theorems/Thm_WeierstrassCurve_Affine_GenusOnePlaceGate_ext_of_isCentred.lean`

(statements from the wrappers, proofs adapted to mathlib `v4.34.0`).  Only proof
bodies are adapted; declaration names, namespaces and kinds are kept.

The pin proves the three wrapper statements through
`WeierstrassCurve.Affine.FunctionField.exists_eq_valuationSubring_of_X_mem` and
`AlgebraicCurve.Place.eq_ofHeightOneSpectrum_of_XClass_mem_nonunits_of_YClass_mem_nonunits`,
neither of which the port carries.  This module needs neither: the port's existing
`AlgebraicCurve.Place.toValuationSubring_eq_of_forall_mem` and
`WeierstrassCurve.Affine.isFinitePlace_of_mem` (both in
`WeierstrassCurve/Place/Dictionary.lean` / `AlgebraicCurve/Defs/PlacesOverDVR.lean`)
already give the Dedekind "a valuation ring is determined by its centre" step, and
the private lemma below recombines them.  The helper is `private`, so the checker
still diffs exactly the pin's public surface.

Reference (public mirror, pinned):
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_WeierstrassCurve_GenusOnePic0.lean>
-/
import FLTForHuman.WeierstrassCurve.Place.Dictionary

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

noncomputable section

open AlgebraicCurve WeierstrassCurve WeierstrassCurve.Affine

namespace WeierstrassCurve.Affine

universe u

variable {F : Type u} [Field F] [DecidableEq F]

variable (W : Affine F) in

class GenusOnePlaceGate : Type u where

  pointEquivPlace : W.Point ≃ AlgebraicCurve.Place F W.FunctionField

  deg_eq_one : ∀ v : AlgebraicCurve.Place F W.FunctionField, v.deg = 1

variable {W : Affine F} [GenusOnePlaceGate W]

abbrev pointEquivPlace : W.Point ≃ AlgebraicCurve.Place F W.FunctionField :=
  GenusOnePlaceGate.pointEquivPlace (W := W)

def placeOfPoint : W.Point → AlgebraicCurve.Place F W.FunctionField :=
  pointEquivPlace (W := W)

@[simp]
theorem pointEquivPlace_apply (P : W.Point) :
    (pointEquivPlace (W := W)) P = placeOfPoint P := rfl

@[simp]
theorem pointEquivPlace_symm_placeOfPoint (P : W.Point) :
    (pointEquivPlace (W := W)).symm (placeOfPoint P) = P :=
  (pointEquivPlace (W := W)).symm_apply_apply P

theorem deg_eq_one (v : AlgebraicCurve.Place F W.FunctionField) : v.deg = 1 :=
  GenusOnePlaceGate.deg_eq_one v

@[simp]
theorem deg_placeOfPoint (P : W.Point) : (placeOfPoint (W := W) P).deg = 1 :=
  deg_eq_one _

theorem degree_eq_sum (D : AlgebraicCurve.Divisor F W.FunctionField) :
    Divisor.degree D = D.sum fun _ n => n := by
  rw [Divisor.degree, Finsupp.liftAddHom_apply]
  exact Finsupp.sum_congr fun v _ => by
    rw [AddMonoidHom.mulRight_apply, deg_eq_one v, Nat.cast_one, mul_one]

def divisorSum : AlgebraicCurve.Divisor F W.FunctionField →+ W.Point :=
  Finsupp.liftAddHom fun v => zmultiplesHom W.Point ((pointEquivPlace (W := W)).symm v)

@[simp]
theorem divisorSum_single (v : AlgebraicCurve.Place F W.FunctionField) (n : ℤ) :
    divisorSum (Finsupp.single v n) = n • (pointEquivPlace (W := W)).symm v :=
  Finsupp.liftAddHom_apply_single _ v n

theorem divisorSum_single_placeOfPoint (P : W.Point) (n : ℤ) :
    divisorSum (Finsupp.single (placeOfPoint P) n) = n • P := by
  rw [divisorSum_single, pointEquivPlace_symm_placeOfPoint]

def pointDivisor (P : W.Point) : Divisor.degZero (K := F) (F := W.FunctionField) :=
  ⟨Finsupp.single (placeOfPoint P) 1 - Finsupp.single (placeOfPoint (0 : W.Point)) 1, by
    rw [Divisor.mem_degZero, map_sub, Divisor.degree_single, Divisor.degree_single,
      deg_placeOfPoint, deg_placeOfPoint, sub_self]⟩

@[simp]
theorem coe_pointDivisor (P : W.Point) :
    (pointDivisor P : AlgebraicCurve.Divisor F W.FunctionField)
      = Finsupp.single (placeOfPoint P) 1 - Finsupp.single (placeOfPoint (0 : W.Point)) 1 :=
  rfl

@[simp]
theorem pointDivisor_zero : pointDivisor (0 : W.Point) = 0 :=
  Subtype.ext (sub_self _)

theorem divisorSum_pointDivisor (P : W.Point) :
    divisorSum (pointDivisor P : AlgebraicCurve.Divisor F W.FunctionField) = P := by
  rw [coe_pointDivisor, map_sub, divisorSum_single_placeOfPoint, divisorSum_single_placeOfPoint,
    one_smul, one_smul, sub_zero]

def pointClass (P : W.Point) : AlgebraicCurve.Pic0 F W.FunctionField :=
  Pic0.mk (pointDivisor P)

@[simp]
theorem pointClass_zero : pointClass (0 : W.Point) = 0 := by
  rw [pointClass, pointDivisor_zero, Pic0.mk_zero]

variable (W) in

class AbelTheorem : Prop where

  isPrincipal_iff_divisorSum_eq_zero :
    ∀ D : AlgebraicCurve.Divisor F W.FunctionField, Divisor.degree D = 0 →
      (Divisor.IsPrincipal D ↔ divisorSum D = 0)

section AbelTheorem

variable [AbelTheorem W]

theorem divisorSum_eq_zero_of_isPrincipal {D : AlgebraicCurve.Divisor F W.FunctionField}
    (h0 : Divisor.degree D = 0) (hD : Divisor.IsPrincipal D) : divisorSum D = 0 :=
  (AbelTheorem.isPrincipal_iff_divisorSum_eq_zero D h0).mp hD

theorem isPrincipal_of_divisorSum_eq_zero {D : AlgebraicCurve.Divisor F W.FunctionField}
    (h0 : Divisor.degree D = 0) (hD : divisorSum D = 0) : Divisor.IsPrincipal D :=
  (AbelTheorem.isPrincipal_iff_divisorSum_eq_zero D h0).mpr hD

def pic0ToPoint : AlgebraicCurve.Pic0 F W.FunctionField →+ W.Point :=
  QuotientAddGroup.lift _
    (divisorSum.comp (Divisor.degZero (K := F) (F := W.FunctionField)).subtype)
    (by
      rintro ⟨D, hD0⟩ hD
      rw [AddSubgroup.mem_addSubgroupOf] at hD
      rw [AddMonoidHom.mem_ker, AddMonoidHom.comp_apply, AddSubgroup.coe_subtype]
      exact divisorSum_eq_zero_of_isPrincipal (Divisor.mem_degZero.mp hD0)
        (Divisor.mem_principal.mp hD))

@[simp]
theorem pic0ToPoint_mk (D : Divisor.degZero (K := F) (F := W.FunctionField)) :
    pic0ToPoint (Pic0.mk D) = divisorSum (D : AlgebraicCurve.Divisor F W.FunctionField) :=
  rfl

@[simp]
theorem pic0ToPoint_pointClass (P : W.Point) : pic0ToPoint (pointClass P) = P := by
  rw [pointClass, pic0ToPoint_mk, divisorSum_pointDivisor]

theorem pic0ToPoint_surjective : Function.Surjective (pic0ToPoint (W := W)) := fun P =>
  ⟨pointClass P, pic0ToPoint_pointClass P⟩

theorem pic0ToPoint_injective : Function.Injective (pic0ToPoint (W := W)) := by
  rw [injective_iff_map_eq_zero]
  intro c
  induction c using QuotientAddGroup.induction_on with
  | H D =>
    intro hD
    obtain ⟨D, hD0⟩ := D
    replace hD : divisorSum D = 0 := hD
    rw [QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]
    exact Divisor.mem_principal.mpr
      (isPrincipal_of_divisorSum_eq_zero (Divisor.mem_degZero.mp hD0) hD)

variable (W) in

def genusOnePic0Equiv : AlgebraicCurve.Pic0 F W.FunctionField ≃+ W.Point :=
  AddEquiv.ofBijective pic0ToPoint ⟨pic0ToPoint_injective, pic0ToPoint_surjective⟩

@[simp]
theorem genusOnePic0Equiv_apply (c : AlgebraicCurve.Pic0 F W.FunctionField) :
    genusOnePic0Equiv W c = pic0ToPoint c := rfl

@[simp]
theorem genusOnePic0Equiv_symm_apply (P : W.Point) :
    (genusOnePic0Equiv W).symm P = pointClass P :=
  (genusOnePic0Equiv W).injective (by
    rw [AddEquiv.apply_symm_apply, genusOnePic0Equiv_apply, pic0ToPoint_pointClass])

theorem pointClass_add (P Q : W.Point) :
    pointClass (P + Q) = pointClass P + pointClass Q := by
  rw [← genusOnePic0Equiv_symm_apply, ← genusOnePic0Equiv_symm_apply,
    ← genusOnePic0Equiv_symm_apply, ← map_add]

end AbelTheorem

end WeierstrassCurve.Affine

namespace WeierstrassCurve.Affine

universe u

variable {F : Type u} [Field F]

variable (W : Affine F) in

class GenusOnePlaceGate.IsCentred [GenusOnePlaceGate W] : Prop where

  XClass_mem_nonunits : ∀ (x y : F) (h : W.Nonsingular x y),
    algebraMap W.CoordinateRing W.FunctionField (CoordinateRing.XClass W x)
      ∈ (placeOfPoint (Point.some x y h)).toValuationSubring.nonunits

  YClass_mem_nonunits : ∀ (x y : F) (h : W.Nonsingular x y),
    algebraMap W.CoordinateRing W.FunctionField (CoordinateRing.YClass W (Polynomial.C y))
      ∈ (placeOfPoint (Point.some x y h)).toValuationSubring.nonunits

namespace GenusOnePlaceGate.IsCentred

variable {W : Affine F} [GenusOnePlaceGate W] [GenusOnePlaceGate.IsCentred W]

theorem algebraMap_XClass_mem_nonunits {x y : F} (h : W.Nonsingular x y) :
    algebraMap W.CoordinateRing W.FunctionField (CoordinateRing.XClass W x)
      ∈ (placeOfPoint (Point.some x y h)).toValuationSubring.nonunits :=
  XClass_mem_nonunits x y h

theorem algebraMap_YClass_mem_nonunits {x y : F} (h : W.Nonsingular x y) :
    algebraMap W.CoordinateRing W.FunctionField (CoordinateRing.YClass W (Polynomial.C y))
      ∈ (placeOfPoint (Point.some x y h)).toValuationSubring.nonunits :=
  YClass_mem_nonunits x y h

end GenusOnePlaceGate.IsCentred

end WeierstrassCurve.Affine

/-! ### The three `Theorems/`-wrapper statements

The pin's proofs route through
`WeierstrassCurve.Affine.FunctionField.exists_eq_valuationSubring_of_X_mem`, which
the port does not carry.  The private recombination below replaces it with the
port's `Place.toValuationSubring_eq_of_forall_mem`: the `IsCentred` non-units put
`X` and `Y` (hence all of `W.CoordinateRing`) inside the place's valuation ring,
`isFinitePlace_of_mem` turns that into `IsFinitePlace`, and the centre is then the
`XYIdeal`, which pins the place. -/

namespace WeierstrassCurve.Affine

universe u

variable {F : Type u} [Field F] [DecidableEq F]

private theorem eq_ofHeightOneSpectrum_of_mem_nonunits {W : Affine F}
    [IsDedekindDomain W.CoordinateRing] {x y : F} (h : W.Equation x y)
    (v : AlgebraicCurve.Place F W.FunctionField)
    (hX : algebraMap W.CoordinateRing W.FunctionField (CoordinateRing.XClass W x)
      ∈ v.toValuationSubring.nonunits)
    (hY : algebraMap W.CoordinateRing W.FunctionField (CoordinateRing.YClass W (Polynomial.C y))
      ∈ v.toValuationSubring.nonunits)
    (w : IsDedekindDomain.HeightOneSpectrum W.CoordinateRing)
    (hw : w.asIdeal = CoordinateRing.XYIdeal W x (Polynomial.C y)) :
    v = Place.ofHeightOneSpectrum (K := F) w := by
  have hXmem : algebraMap W.CoordinateRing W.FunctionField (CoordinateRing.XClass W x)
      ∈ v.toValuationSubring := ValuationSubring.nonunits_subset hX
  have hYmem : algebraMap W.CoordinateRing W.FunctionField (CoordinateRing.YClass W (Polynomial.C y))
      ∈ v.toValuationSubring := ValuationSubring.nonunits_subset hY
  have hmkX : algebraMap W.CoordinateRing W.FunctionField
      (CoordinateRing.mk W (Polynomial.C Polynomial.X)) ∈ v.toValuationSubring := by
    have hsub : CoordinateRing.mk W (Polynomial.C Polynomial.X)
        = CoordinateRing.XClass W x + algebraMap F W.CoordinateRing x := by
      rw [CoordinateRing.XClass, CoordinateRing.algebraMap_eq_mk_C_C, ← map_add, map_sub,
        sub_add_cancel]
    rw [hsub, map_add]
    exact add_mem hXmem (v.algebraMap_mem' x)
  have hpolyX : polyToFunctionField W Polynomial.X ∈ v.toValuationSubring := by
    rw [polyToFunctionField_apply]
    exact hmkX
  have hv : IsFinitePlace v := isFinitePlace_of_mem v hpolyX
  have hXc : CoordinateRing.XClass W x ∈ Place.center W.CoordinateRing v hv := by
    obtain ⟨ha, hmax⟩ :=
      (ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal (A := v.toValuationSubring)).mp hX
    exact hmax
  have hYc : CoordinateRing.YClass W (Polynomial.C y) ∈ Place.center W.CoordinateRing v hv := by
    obtain ⟨ha, hmax⟩ :=
      (ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal (A := v.toValuationSubring)).mp hY
    exact hmax
  have hle : CoordinateRing.XYIdeal W x (Polynomial.C y) ≤ Place.center W.CoordinateRing v hv := by
    rw [CoordinateRing.XYIdeal, Ideal.span_le]
    rintro _ (rfl | rfl)
    · exact hXc
    · exact hYc
  haveI hcenterPrime : (Place.center W.CoordinateRing v hv).IsPrime := Ideal.comap_isPrime _ _
  have hcenter : CoordinateRing.XYIdeal W x (Polynomial.C y) = Place.center W.CoordinateRing v hv :=
    (CoordinateRing.XYIdeal_isMaximal h).eq_of_le hcenterPrime.ne_top hle
  have hspec : Place.centerHeightOneSpectrum W.CoordinateRing v hv = w := by
    apply IsDedekindDomain.HeightOneSpectrum.ext
    show Place.center W.CoordinateRing v hv = w.asIdeal
    rw [← hcenter, ← hw]
  have hval : v.toValuationSubring = (w.valuation W.FunctionField).valuationSubring := by
    rw [Place.toValuationSubring_eq_of_forall_mem (R := W.CoordinateRing) v hv, hspec,
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring]
  exact Place.ext (by
    rw [Place.ofHeightOneSpectrum_toValuationSubring]
    exact hval)

end WeierstrassCurve.Affine

universe u

theorem WeierstrassCurve.Affine.placeOfPoint_some_eq_ofHeightOneSpectrum
    {F : Type u} [Field F] [DecidableEq F] {W : WeierstrassCurve.Affine F}
    [GenusOnePlaceGate W] [GenusOnePlaceGate.IsCentred W] [IsDedekindDomain W.CoordinateRing]
    {x y : F} (h : W.Nonsingular x y)
    (w : IsDedekindDomain.HeightOneSpectrum W.CoordinateRing)
    (hw : w.asIdeal = CoordinateRing.XYIdeal W x (Polynomial.C y)) :
    placeOfPoint (Point.some x y h) = Place.ofHeightOneSpectrum (K := F) w :=
  eq_ofHeightOneSpectrum_of_mem_nonunits h.1 _
    (GenusOnePlaceGate.IsCentred.algebraMap_XClass_mem_nonunits h)
    (GenusOnePlaceGate.IsCentred.algebraMap_YClass_mem_nonunits h) w hw

theorem WeierstrassCurve.Affine.algebraMap_mk_C_X_notMem_toValuationSubring_placeOfPoint_zero
    {F : Type u} [Field F] [DecidableEq F] [IsAlgClosed F] {W : WeierstrassCurve.Affine F} [W.IsElliptic]
    [GenusOnePlaceGate W] [GenusOnePlaceGate.IsCentred W] :
    algebraMap W.CoordinateRing W.FunctionField (CoordinateRing.mk W (Polynomial.C Polynomial.X))
      ∉ (placeOfPoint (0 : W.Point)).toValuationSubring := by
  intro hXO
  haveI : IsDedekindDomain W.CoordinateRing :=
    CoordinateRing.isDedekindDomain_of_Δ_ne_zero (W.coe_Δ' ▸ W.Δ'.ne_zero)
  have hv0 : IsFinitePlace (placeOfPoint (0 : W.Point)) := by
    refine isFinitePlace_of_mem _ ?_
    rw [polyToFunctionField_apply]
    exact hXO
  let w : IsDedekindDomain.HeightOneSpectrum W.CoordinateRing :=
    Place.centerHeightOneSpectrum W.CoordinateRing (placeOfPoint (0 : W.Point)) hv0
  have hw : (placeOfPoint (0 : W.Point)).toValuationSubring
      = (w.valuation W.FunctionField).valuationSubring := by
    have h := Place.toValuationSubring_eq_of_forall_mem (R := W.CoordinateRing)
      (placeOfPoint (0 : W.Point)) hv0
    rw [IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring] at h
    exact h
  have hmax : w.asIdeal.IsMaximal := w.isPrime.isMaximal w.ne_bot
  obtain ⟨a, b, hab, hwI⟩ := CoordinateRing.exists_eq_XYIdeal_of_isMaximal w.asIdeal hmax
  have hns : W.Nonsingular a b := (equation_iff_nonsingular (W := W)).mp hab
  have h1 : placeOfPoint (Point.some a b hns) = Place.ofHeightOneSpectrum (K := F) w :=
    WeierstrassCurve.Affine.placeOfPoint_some_eq_ofHeightOneSpectrum hns w hwI.symm
  have h2 : placeOfPoint (0 : W.Point) = Place.ofHeightOneSpectrum (K := F) w :=
    Place.ext (by
      rw [Place.ofHeightOneSpectrum_toValuationSubring]
      exact hw)
  have h3 : (Point.some a b hns : W.Point) = 0 :=
    (pointEquivPlace (W := W)).injective (by
      rw [pointEquivPlace_apply, pointEquivPlace_apply, h1, h2])
  exact (Point.some_ne_zero hns) h3

theorem WeierstrassCurve.Affine.GenusOnePlaceGate.ext_of_isCentred
    {F : Type u} [Field F] [DecidableEq F] {W : WeierstrassCurve.Affine F}
    [IsDedekindDomain W.CoordinateRing]
    (g₁ g₂ : WeierstrassCurve.Affine.GenusOnePlaceGate W)
    (h₁ : @WeierstrassCurve.Affine.GenusOnePlaceGate.IsCentred F _ W g₁)
    (h₂ : @WeierstrassCurve.Affine.GenusOnePlaceGate.IsCentred F _ W g₂) :
    g₁ = g₂ := by
  have hw : ∀ {x y : F} (h : W.Nonsingular x y),
      ∃ w : IsDedekindDomain.HeightOneSpectrum W.CoordinateRing,
        w.asIdeal = CoordinateRing.XYIdeal W x (Polynomial.C y) := fun {x y} h =>
    ⟨⟨CoordinateRing.XYIdeal W x (Polynomial.C y),
        (CoordinateRing.XYIdeal_isMaximal h.1).isPrime,
        CoordinateRing.XYIdeal_ne_bot x (Polynomial.C y)⟩, rfl⟩
  have hsome : ∀ {x y : F} (h : W.Nonsingular x y),
      g₁.pointEquivPlace (Point.some x y h) = g₂.pointEquivPlace (Point.some x y h) := by
    intro x y h
    obtain ⟨w, hw⟩ := hw h
    have e1 := @WeierstrassCurve.Affine.placeOfPoint_some_eq_ofHeightOneSpectrum F _ _ W g₁ h₁ _ x y h w hw
    have e2 := @WeierstrassCurve.Affine.placeOfPoint_some_eq_ofHeightOneSpectrum F _ _ W g₂ h₂ _ x y h w hw
    exact e1.trans e2.symm
  have hall : ∀ P : W.Point, g₁.pointEquivPlace P = g₂.pointEquivPlace P := by
    intro P
    cases P with
    | some x y h => exact hsome h
    | zero =>
      have key : g₁.pointEquivPlace.symm (g₂.pointEquivPlace 0) = 0 := by
        rcases hP : g₁.pointEquivPlace.symm (g₂.pointEquivPlace 0) with _ | ⟨x, y, h⟩
        · rfl
        · exfalso
          have h3 : g₂.pointEquivPlace 0 = g₁.pointEquivPlace (Point.some x y h) := by
            rw [← hP, Equiv.apply_symm_apply]
          have h5 : (Point.some x y h : W.Point) = 0 :=
            g₂.pointEquivPlace.injective ((h3.trans (hsome h)).symm)
          exact Point.some_ne_zero h h5
      have := congrArg g₁.pointEquivPlace key
      rw [Equiv.apply_symm_apply] at this
      exact this.symm
  cases g₁ with
  | mk e₁ d₁ =>
    cases g₂ with
    | mk e₂ d₂ =>
      congr
      exact Equiv.ext hall
