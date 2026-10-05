/-
The H5 vocabulary tail (`IsogenyEndDatum` / `IsogenyHomDatum`).

Canonical sources: the pinned FLT `aa2d8b3` `S_` files

* `P2M/Sol/S_WeierstrassCurve_Affine_IsogenyEndDatum_pointEnd_apply_eq_sub.lean`,
* `P2M/Sol/S_WeierstrassCurve_Affine_IsogenyHomDatum_pointHom_apply_eq_sub.lean`,
* `P2M/Sol/S_WeierstrassCurve_Affine_IsogenyEndDatum_exists_pointEnd_eq_add.lean`,
* `P2M/Sol/S_WeierstrassCurve_Affine_natCard_ker_pointMapOfPushforward_eq_finrankAlong.lean`;

the statements are taken from the corresponding `Theorems/` wrappers.  The two
remaining H5 vocabulary nodes — `IsogenyHomDatum.exists_pointHom_comp_eq_of_ker_le_of_isCentred`
and `IsogenyEndDatum.aeval_j_diag_eq_zero_of_finrankAlong_eq` — are **not**
here: they are blocked on unported `Theorems/` nodes outside SET-3 (see the
module report and `Engine`/`NatCard`).  Statements are transcribed verbatim; only
proof bodies are adapted to mathlib `v4.34.0`.

Reference (public mirror, pinned):
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_WeierstrassCurve_Affine_natCard_ker_pointMapOfPushforward_eq_finrankAlong.lean>
-/
import FLTForHuman.WeierstrassCurve.IsogenyEndDatum.DualEndData
import FLTForHuman.WeierstrassCurve.Isogeny.NatCard
import FLTForHuman.WeierstrassCurve.Isogeny.ConditionalCurrency
import Mathlib.Tactic

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

noncomputable section

open Polynomial Finset
open scoped Polynomial.Bivariate Classical
open WeierstrassCurve
open WeierstrassCurve.Affine
open WeierstrassCurve.Affine.CoordinateRing
open AlgebraicCurve
open IsDedekindDomain

universe u

namespace WeierstrassCurve

namespace Affine

namespace IsogenyEndDatum

theorem pointEnd_apply_eq_sub
    {F : Type u} [Field F] [DecidableEq F] [IsAlgClosed F] [CharZero F]
    {W : WeierstrassCurve.Affine F} [W.IsElliptic] [GenusOnePlaceGate W] [AbelTheorem W]
    (D : IsogenyEndDatum W) (hN : NormFormulaAlong F D.ι D.hfin) (P : W.Point) :
    D.pointEnd hN P
      = (pointEquivPlace (W := W)).symm ((placeOfPoint P).restrictAlong D.ι D.hι)
        - (pointEquivPlace (W := W)).symm ((placeOfPoint (0 : W.Point)).restrictAlong D.ι D.hι) := by
  set Q : W.Point := (pointEquivPlace (W := W)).symm ((placeOfPoint P).restrictAlong D.ι D.hι) with hQ
  set Q₀ : W.Point :=
    (pointEquivPlace (W := W)).symm ((placeOfPoint (0 : W.Point)).restrictAlong D.ι D.hι) with hQ₀
  have hP : (placeOfPoint P).restrictAlong D.ι D.hι = placeOfPoint Q :=
    ((pointEquivPlace (W := W)).apply_symm_apply _).symm
  have h0 : (placeOfPoint (0 : W.Point)).restrictAlong D.ι D.hι = placeOfPoint Q₀ :=
    ((pointEquivPlace (W := W)).apply_symm_apply _).symm
  have hdiv : (Pic0.pushforwardAlongDegZero D.ι D.hι (pointDivisor P) :
      AlgebraicCurve.Divisor F W.FunctionField)
        = Finsupp.single (placeOfPoint Q) 1 - Finsupp.single (placeOfPoint Q₀) 1 := by
    rw [Pic0.coe_pushforwardAlongDegZero, coe_pointDivisor, map_sub,
      pushforwardAlong_single_eq D.ι D.hι, pushforwardAlong_single_eq D.ι D.hι, hP, h0]
  rw [IsogenyEndDatum.pointEnd_apply, pointClass, Pic0.pushforwardAlongHom_mk,
    genusOnePic0Equiv_apply, pic0ToPoint_mk, hdiv, map_sub, divisorSum_single_placeOfPoint,
    divisorSum_single_placeOfPoint, one_smul, one_smul]

end IsogenyEndDatum

namespace IsogenyHomDatum

theorem pointHom_apply_eq_sub
    {F : Type u} [Field F] [DecidableEq F] [IsAlgClosed F] [CharZero F]
    {V₀ V₁ : WeierstrassCurve.Affine F} [V₀.IsElliptic] [GenusOnePlaceGate V₀] [AbelTheorem V₀]
    [V₁.IsElliptic] [GenusOnePlaceGate V₁] [AbelTheorem V₁]
    (φ : IsogenyHomDatum V₀ V₁) (hN : NormFormulaAlong F φ.ι φ.hfin) (P : V₀.Point) :
    φ.pointHom hN P
      = (pointEquivPlace (W := V₁)).symm ((placeOfPoint P).restrictAlong φ.ι φ.hι)
        - (pointEquivPlace (W := V₁)).symm ((placeOfPoint (0 : V₀.Point)).restrictAlong φ.ι φ.hι) := by
  set Q : V₁.Point := (pointEquivPlace (W := V₁)).symm ((placeOfPoint P).restrictAlong φ.ι φ.hι) with hQ
  set Q₀ : V₁.Point :=
    (pointEquivPlace (W := V₁)).symm ((placeOfPoint (0 : V₀.Point)).restrictAlong φ.ι φ.hι) with hQ₀
  have hP : (placeOfPoint P).restrictAlong φ.ι φ.hι = placeOfPoint Q :=
    ((pointEquivPlace (W := V₁)).apply_symm_apply _).symm
  have h0 : (placeOfPoint (0 : V₀.Point)).restrictAlong φ.ι φ.hι = placeOfPoint Q₀ :=
    ((pointEquivPlace (W := V₁)).apply_symm_apply _).symm
  have hdiv : (Pic0.pushforwardAlongDegZero φ.ι φ.hι (pointDivisor P) :
      AlgebraicCurve.Divisor F V₁.FunctionField)
        = Finsupp.single (placeOfPoint Q) 1 - Finsupp.single (placeOfPoint Q₀) 1 := by
    rw [Pic0.coe_pushforwardAlongDegZero, coe_pointDivisor, map_sub,
      pushforwardAlong_single_eq φ.ι φ.hι, pushforwardAlong_single_eq φ.ι φ.hι, hP, h0]
  rw [IsogenyHomDatum.pointHom_apply, pointClass, Pic0.pushforwardAlongHom_mk,
    genusOnePic0Equiv_apply, pic0ToPoint_mk, hdiv, map_sub, divisorSum_single_placeOfPoint,
    divisorSum_single_placeOfPoint, one_smul, one_smul]

end IsogenyHomDatum

namespace IsogenyEndDatum

/-- The pin's local `normFormulaAlong_of_finiteAlong_aux` helper (from the
`exists_pointEnd_eq_add` `S_` file), kept local to this module. -/
private theorem normFormulaAlong_of_finiteAlong_aux
    {F : Type u} [Field F] [CharZero F] {V W : WeierstrassCurve.Affine F}
    [HasPrincipalDivisors F W.FunctionField]
    (ι : V.FunctionField →ₐ[F] W.FunctionField) (hfin : FiniteAlong F ι) :
    NormFormulaAlong F ι hfin := by
  haveI : CharZero V.FunctionField :=
    charZero_of_injective_algebraMap (algebraMap F V.FunctionField).injective
  have hsep : SeparableAlong F ι := by
    letI := algebraAlong ι
    haveI := isScalarTower_along ι
    haveI : Module.Finite V.FunctionField W.FunctionField := hfin
    show Algebra.IsSeparable V.FunctionField W.FunctionField
    infer_instance
  exact AlgebraicCurve.normFormulaAlong ι hfin hsep

theorem exists_pointEnd_eq_add
    {F : Type u} [Field F] [DecidableEq F] [IsAlgClosed F] [CharZero F]
    {W : WeierstrassCurve.Affine F} [W.IsElliptic]
    [GenusOnePlaceGate W] [GenusOnePlaceGate.IsCentred W] [AbelTheorem W]
    (D₁ : IsogenyEndDatum W) (hN₁ : NormFormulaAlong F D₁.ι D₁.hfin)
    (D₂ : IsogenyEndDatum W) (hN₂ : NormFormulaAlong F D₂.ι D₂.hfin)
    (h : D₁.pointEnd hN₁ + D₂.pointEnd hN₂ ≠ 0) :
    ∃ (D₃ : IsogenyEndDatum W) (hN₃ : NormFormulaAlong F D₃.ι D₃.hfin),
      D₃.pointEnd hN₃ = D₁.pointEnd hN₁ + D₂.pointEnd hN₂ := by
  obtain ⟨D₃, hD₃⟩ :=
    IsogenyEndDatum.exists_restrictAlong_placeOfPoint_eq_add D₁ hN₁ D₂ hN₂ h
  haveI : HasPrincipalDivisors F W.FunctionField := hasPrincipalDivisors_functionField W
  have hN₃ : NormFormulaAlong F D₃.ι D₃.hfin := normFormulaAlong_of_finiteAlong_aux D₃.ι D₃.hfin
  refine ⟨D₃, hN₃, ?_⟩
  refine AddMonoidHom.ext fun P => ?_
  show D₃.pointEnd hN₃ P = D₁.pointEnd hN₁ P + D₂.pointEnd hN₂ P
  rw [IsogenyEndDatum.pointEnd_apply_eq_sub D₃ hN₃, IsogenyEndDatum.pointEnd_apply_eq_sub D₁ hN₁,
    IsogenyEndDatum.pointEnd_apply_eq_sub D₂ hN₂, hD₃ P, hD₃ 0,
    pointEquivPlace_symm_placeOfPoint, pointEquivPlace_symm_placeOfPoint]
  abel

end IsogenyEndDatum

end Affine

end WeierstrassCurve

namespace WeierstrassCurve

namespace Affine

/-- The plain (no `SeparableAlong`/`HasPrincipalDivisors` binder) sibling of the
landed `_of_separableAlong` headline; the pin `S_` file derives both from
`[IsAlgClosed F] [CharZero F]`. -/
theorem natCard_ker_pointMapOfPushforward_eq_finrankAlong
    {F : Type u} [Field F] [DecidableEq F] [IsAlgClosed F] [CharZero F]
    (E E' : WeierstrassCurve.Affine F) [E.IsElliptic] [GenusOnePlaceGate E] [AbelTheorem E]
    [E'.IsElliptic] [GenusOnePlaceGate E'] [AbelTheorem E']
    (ι : E'.FunctionField →ₐ[F] E.FunctionField) (hι : ι.toRingHom.IsIntegral)
    (hfin : FiniteAlong F ι) (hN : NormFormulaAlong F ι hfin) :
    Nat.card (pointMapOfPushforward ι hι hfin hN).ker = finrankAlong F ι := by
  haveI : HasPrincipalDivisors F E.FunctionField := hasPrincipalDivisors_functionField E
  haveI : HasPrincipalDivisors F E'.FunctionField := hasPrincipalDivisors_functionField E'
  have hsep : SeparableAlong F ι := by
    letI := algebraAlong ι
    haveI := isScalarTower_along ι
    haveI : Module.Finite E'.FunctionField E.FunctionField := hfin
    haveI : CharZero E'.FunctionField :=
      charZero_of_injective_algebraMap (algebraMap F E'.FunctionField).injective
    show Algebra.IsSeparable E'.FunctionField E.FunctionField
    infer_instance
  exact WeierstrassCurve.Affine.natCard_ker_pointMapOfPushforward_eq_finrankAlong_of_separableAlong
    E E' ι hι hfin hsep hN

end Affine

end WeierstrassCurve
