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
    `kw_functionFieldMapAlongGeneralNoAC`, by `kw_functionField_algHom_ext` together
    with the two `…_polyToFunctionField_X`/`…_yGen` computation lemmas;
  * zone 2 — the `General`/`NoAC` bridge is definitional: the two `Prop`s and the two
    map-along maps agree by `rfl`, so a consumer may pass between spellings;
  * zone 3 — the `NoAC` datum-level discharge at `ℚ → AlgebraicClosure ℚ` (this runs
    the coordinate-ring basis, the tensor-domain, the flat/`IsIntegral` finrank
    argument and the `Along` packaging in full);
  * zone 4 — the `General` datum-level discharge at
    `AlgebraicClosure ℚ → AlgebraicClosure ℚ`.
-/
import FLTForHuman.WeierstrassCurve.Isogeny.BaseChange
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

set_option autoImplicit false
set_option maxHeartbeats 4000000

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
    φ = kw_functionFieldMapAlongGeneralNoAC W F F' := by
  symm
  refine kw_functionField_algHom_ext ?_ ?_
  · rw [kw_functionFieldMapAlongGeneralNoAC_polyToFunctionField_X]
    exact hX.symm
  · rw [kw_functionFieldMapAlongGeneralNoAC_yGen]
    exact hy.symm

/-! ### Zone 2 — the `General`/`NoAC` bridge is definitional -/

example (W : WeierstrassCurve ℚ) [W.IsElliptic] :
    kw_functionFieldMapAlongGeneral W (AlgebraicClosure ℚ) (AlgebraicClosure ℚ)
      = kw_functionFieldMapAlongGeneralNoAC W (AlgebraicClosure ℚ) (AlgebraicClosure ℚ) :=
  rfl

example (W : WeierstrassCurve ℚ) [W.IsElliptic] :
    KwFunctionFieldTensorIsDomainGeneral W (AlgebraicClosure ℚ) (AlgebraicClosure ℚ)
      ↔ KwFunctionFieldTensorIsDomainGeneralNoAC W (AlgebraicClosure ℚ) (AlgebraicClosure ℚ) :=
  Iff.rfl

/-! ### Zone 3 — the `NoAC` datum-level discharge, executed -/

example (W : WeierstrassCurve ℚ) [W.IsElliptic] (N : ℕ) :
    KwIsogenyEndDatumBaseChangeAlongGeneralNoAC W ℚ (AlgebraicClosure ℚ)
      (IsScalarTower.toAlgHom ℚ ℚ (AlgebraicClosure ℚ)) N :=
  kw_isogenyEndDatumBaseChangeAlong_dischargeGeneralNoAC W ℚ (AlgebraicClosure ℚ) _ N

/-! ### Zone 4 — the `General` datum-level discharge, executed -/

example (W : WeierstrassCurve ℚ) [W.IsElliptic] (N : ℕ) :
    KwIsogenyEndDatumBaseChangeAlongGeneral W (AlgebraicClosure ℚ) (AlgebraicClosure ℚ)
      (IsScalarTower.toAlgHom ℚ (AlgebraicClosure ℚ) (AlgebraicClosure ℚ)) N :=
  kw_isogenyEndDatumBaseChangeAlong_dischargeGeneral W (AlgebraicClosure ℚ)
    (AlgebraicClosure ℚ) _ N
