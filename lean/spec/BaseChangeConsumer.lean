/-
  Cross-module wire test for **D-1**, the shared base-change prelude
  (`FLTForHuman/WeierstrassCurve/Isogeny/BaseChange.lean`).

  A `spec/` probe, not a library module. It exists separately from
  `spec/WeierstrassCurveConsumer.lean` so that D-1's prelude has a wire test that does
  not pull the `IsogenyEndDatum/Engine.lean` cone (its consumers' home). D-1 itself
  imports `GenusOnePlaceGate.lean` — the gate *classes* — and **not**
  `GenusOnePlaceGateCentred.lean`, whose `Place/RRSpace.lean` dependency would collide
  with `Engine.lean`'s `WeierstrassCurve.Affine.instInfinitePlace`; that pairing is
  therefore importable, and D-4/D-5 rely on it (see `CARRY-FORWARD.md`).

  Executed zones (each a real composition, no `#check`, no `sorry`; deleting
  `BaseChange.lean` makes every one of them fail):

  * zone 1 — function-field rigidity: an `F`-algebra map out of `(W⁄F).FunctionField`
    that sends the generic point to the generic point of `(W⁄F').FunctionField` is
    `functionFieldMapAlongGeneralNoAC`, by `functionField_algHom_ext` together
    with the two `…_polyToFunctionField_X`/`…_yGen` computation lemmas;
  * zone 2 — the `General`/`NoAC` bridge is definitional: the two `Prop`s and the two
    map-along maps agree by `rfl`, so a consumer may pass between spellings;
  * zone 3 — the `NoAC` datum-level discharge at `ℚ → AlgebraicClosure ℚ` (this runs
    the coordinate-ring basis, the tensor-domain, the flat/`IsIntegral` finrank
    argument and the `Along` packaging in full);
  * zone 4 — the `General` datum-level discharge at
    `AlgebraicClosure ℚ → AlgebraicClosure ℚ`;
  * zone 5 — **D-3a**: the `bcff` headline (`Isogeny/BaseChangeAlgHom.lean`) at
    `ℚ → AlgebraicClosure ℚ`, an integral finite function-field endomorphism over `ℚ`
    descending to the algebraic closure with the same `finrankAlong`;
  * zone 6 — **D-3b**: the variable-change `AlgEquiv` (`Isogeny/VariableChangeAlgEquiv.lean`)
    at `ℚ`: the headline, `mrtw60aVCPlaceSeamAlgEquiv` with its two coordinate identities and
    its round trip, the coordinate-ring rigidity `mrtw60a_coordHom_ext`, and the composition
    identifying any `AlgEquiv` with the two prescribed generic-point coordinates with
    `mrtw60aVCFunHom`'s inverse through the module's `mrtw60a_funHom_ext` (which is D-1's
    `functionField_algHom_ext`).

  Deleting `BaseChangeAlgHom.lean` kills zone 5, deleting `VariableChangeAlgEquiv.lean` kills
  zone 6, and deleting `BaseChange.lean` kills all six.
-/
import FLTForHuman.WeierstrassCurve.Isogeny.BaseChange
import FLTForHuman.WeierstrassCurve.Isogeny.BaseChangeAlgHom
import FLTForHuman.WeierstrassCurve.Isogeny.VariableChangeAlgEquiv
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

universe u

noncomputable section

open Polynomial
open scoped Polynomial.Bivariate WeierstrassCurve TensorProduct

open WeierstrassCurve WeierstrassCurve.Affine ModularCurve

attribute [local instance] Classical.decEq

/-! ### Zone 1 — function-field rigidity at the generic point -/

example {R₀ : Type u} [Field R₀] (W : WeierstrassCurve R₀) [W.IsElliptic]
    (F : Type u) [Field F] [Algebra R₀ F] [DecidableEq F] [CharZero F]
    (F' : Type u) [Field F'] [Algebra R₀ F'] [DecidableEq F'] [CharZero F']
    [Algebra F F'] [IsScalarTower R₀ F F']
    {φ : (W⁄F).FunctionField →ₐ[F] (W⁄F').FunctionField}
    (hX : φ (polyToFunctionField (W⁄F) X) = polyToFunctionField (W⁄F') X)
    (hy : φ (yGen (W⁄F)) = yGen (W⁄F')) :
    φ = functionFieldMapAlongGeneralNoAC W F F' := by
  symm
  refine functionField_algHom_ext ?_ ?_
  · rw [functionFieldMapAlongGeneralNoAC_polyToFunctionField_X]
    exact hX.symm
  · rw [functionFieldMapAlongGeneralNoAC_yGen]
    exact hy.symm

/-! ### Zone 2 — the `General`/`NoAC` bridge is definitional -/

example (W : WeierstrassCurve ℚ) [W.IsElliptic] :
    functionFieldMapAlongGeneral W (AlgebraicClosure ℚ) (AlgebraicClosure ℚ)
      = functionFieldMapAlongGeneralNoAC W (AlgebraicClosure ℚ) (AlgebraicClosure ℚ) :=
  rfl

example (W : WeierstrassCurve ℚ) [W.IsElliptic] :
    KwFunctionFieldTensorIsDomainGeneral W (AlgebraicClosure ℚ) (AlgebraicClosure ℚ)
      ↔ KwFunctionFieldTensorIsDomainGeneralNoAC W (AlgebraicClosure ℚ) (AlgebraicClosure ℚ) :=
  Iff.rfl

/-! ### Zone 3 — the `NoAC` datum-level discharge, executed -/

example (W : WeierstrassCurve ℚ) [W.IsElliptic] (N : ℕ) :
    KwIsogenyEndDatumBaseChangeAlongGeneralNoAC W ℚ (AlgebraicClosure ℚ)
      (IsScalarTower.toAlgHom ℚ ℚ (AlgebraicClosure ℚ)) N :=
  isogenyEndDatumBaseChangeAlong_dischargeGeneralNoAC W ℚ (AlgebraicClosure ℚ) _ N

/-! ### Zone 4 — the `General` datum-level discharge, executed -/

example (W : WeierstrassCurve ℚ) [W.IsElliptic] (N : ℕ) :
    KwIsogenyEndDatumBaseChangeAlongGeneral W (AlgebraicClosure ℚ) (AlgebraicClosure ℚ)
      (IsScalarTower.toAlgHom ℚ (AlgebraicClosure ℚ) (AlgebraicClosure ℚ)) N :=
  isogenyEndDatumBaseChangeAlong_dischargeGeneral W (AlgebraicClosure ℚ)
    (AlgebraicClosure ℚ) _ N

/-! ### Zone 5 — D-3a (`BaseChangeAlgHom.lean`), executed

An integral finite endomorphism of `(W⁄ℚ̄).FunctionField` over an algebraically closed
`ℚ̄` descends to a second algebraically closed field `k` with the same `finrankAlong`. The
headline is the pin wrapper's statement verbatim; its `F`/`F'` are *independent* universe
parameters, so the call only elaborates because D-1's `General`/`NoAC` block was
universe-generalised (the module states `F : Type v`, `F' : Type w`). -/

example (W : WeierstrassCurve ℚ) [W.IsElliptic]
    (ι : (W.baseChange (AlgebraicClosure ℚ)).toAffine.FunctionField →ₐ[AlgebraicClosure ℚ]
        (W.baseChange (AlgebraicClosure ℚ)).toAffine.FunctionField)
    (hι : ι.toRingHom.IsIntegral)
    (hfin : AlgebraicCurve.FiniteAlong (AlgebraicClosure ℚ) ι) :
    ∃ ι' : (W.baseChange (AlgebraicClosure ℚ)).toAffine.FunctionField →ₐ[AlgebraicClosure ℚ]
        (W.baseChange (AlgebraicClosure ℚ)).toAffine.FunctionField,
      ι'.toRingHom.IsIntegral ∧
        ∃ hfin' : AlgebraicCurve.FiniteAlong (AlgebraicClosure ℚ) ι',
          AlgebraicCurve.finrankAlong (AlgebraicClosure ℚ) ι'
            = AlgebraicCurve.finrankAlong (AlgebraicClosure ℚ) ι :=
  exists_algHom_functionField_baseChange_finrankAlong_eq W (AlgebraicClosure ℚ)
    (AlgebraicClosure ℚ) ι hι hfin

/-! ### Zone 6 — D-3b (`VariableChangeAlgEquiv.lean`), executed

The variable-change `AlgEquiv` of function fields at `ℚ`, and the composition with D-1's
rigidity that pins it down by its two generic-point coordinates. -/

example (W : WeierstrassCurve ℚ) (C : WeierstrassCurve.VariableChange ℚ) :
    Nonempty (W.toAffine.FunctionField ≃ₐ[ℚ] (C • W).toAffine.FunctionField) :=
  nonempty_functionField_algEquiv_of_variableChange W C

example (W : WeierstrassCurve ℚ) (C : WeierstrassCurve.VariableChange ℚ) :
    (mrtw60aVCFunHom (C := C) (W := W.toAffine) (V := (C • W).toAffine) rfl).comp
        (mrtw60aVCFunHomInv (C := C) (W := W.toAffine) (V := (C • W).toAffine) rfl)
      = AlgHom.id ℚ (C • W).toAffine.FunctionField :=
  mrtw60a_funHom_comp_funHomInv rfl

example (W : WeierstrassCurve ℚ) (C : WeierstrassCurve.VariableChange ℚ)
    (x : (C • W).toAffine.FunctionField) :
    (mrtw60aVCPlaceSeamAlgEquiv (C := C) (W := W.toAffine) (V := (C • W).toAffine) rfl).symm
        ((mrtw60aVCPlaceSeamAlgEquiv (C := C) (W := W.toAffine) (V := (C • W).toAffine) rfl) x)
      = x :=
  AlgEquiv.symm_apply_apply _ x

example (W : WeierstrassCurve ℚ) (C : WeierstrassCurve.VariableChange ℚ)
    {S : Type} [CommRing S] [Algebra ℚ S]
    {φ ψ : ((C • W).toAffine).CoordinateRing →ₐ[ℚ] S}
    (hX : φ (CoordinateRing.mk (C • W).toAffine (Polynomial.C X))
        = ψ (CoordinateRing.mk (C • W).toAffine (Polynomial.C X)))
    (hY : φ (CoordinateRing.mk (C • W).toAffine Y)
        = ψ (CoordinateRing.mk (C • W).toAffine Y)) : φ = ψ :=
  mrtw60a_coordHom_ext hX hY

/-- An `AlgEquiv` out of `W.FunctionField` whose two generic-point coordinates are the
`mrtw60a` forward coordinates of the variable change *is* `mrtw60aVCFunHom`: the composition
of D-3b's coordinate block with D-1's `functionField_algHom_ext`, through D-3b's own
`mrtw60a_funHom_ext`. -/
example (W : WeierstrassCurve ℚ) (C : WeierstrassCurve.VariableChange ℚ)
    {e : W.toAffine.FunctionField ≃ₐ[ℚ] (C • W).toAffine.FunctionField}
    (hX : e (polyToFunctionField W.toAffine X) = mrtw60a_xFwd C ((C • W).toAffine))
    (hy : e (yGen W.toAffine) = mrtw60a_yFwd C ((C • W).toAffine)) :
    e.toAlgHom = mrtw60aVCFunHom (C := C) (W := W.toAffine) (V := (C • W).toAffine) rfl := by
  refine mrtw60a_funHom_ext ?_ ?_
  · rw [mrtw60aVCFunHom_X]
    exact hX
  · rw [mrtw60aVCFunHom_yGen]
    exact hy
