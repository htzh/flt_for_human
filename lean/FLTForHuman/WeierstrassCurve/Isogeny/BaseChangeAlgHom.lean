/-
The base change of an isogeny endomorphism datum to a larger field: an integral
function-field endomorphism `ι` of `(W⁄F).FunctionField` whose `finrankAlong` is `n`
descends along any `Algebra R₀ F →ₐ[R₀] F'` to an endomorphism `ι'` of
`(W⁄F').FunctionField` with the same `finrankAlong`. This is set **D-3** of
`topics/velu/WORKORDER-P2-basechange.md`.

Statement transcribed verbatim from the pinned FLT `aa2d8b3` wrapper
`Theorems/Thm_WeierstrassCurve_Affine_exists_algHom_functionField_baseChange_finrankAlong_eq.lean`;
the pin's solution file
`P2M/Sol/S_WeierstrassCurve_Affine_exists_algHom_functionField_baseChange_finrankAlong_eq.lean`
(1,336 lines) is otherwise the source of D-1's prelude and is **not** re-proved here.

Assumes from D-1 (`Isogeny/BaseChange.lean`): the whole `General` base-change prelude at
its prefix-stripped names — `KwIsogenyEndDatumBaseChangeAlongGeneral`,
`isogenyEndDatumBaseChangeAlong_of_tensorIsDomainGeneral`,
`isogenyEndDatumBaseChangeAlong_dischargeGeneral`, the tensor-product base change of the
function field, its domain discharge and the flat/`IsIntegral` seam. The node-unique
declarations the work order listed for this file (`kw_tensorFracIotaRingHomGeneral*`,
`kw_tensorIotaRingHomGeneral*`, `kw_isogenyEndDatumBaseChangeIotaGeneral`,
`KwIsogenyEndDatumBaseChangeAlongGeneral`, `kw_tensorFracIotaFinrankSeam_dischargeGeneral`,
`kw_tensorIotaRingHom_finiteGeneral`, `ofHeightOneSpectrum_injective`,
`kw_equation_map_polyToFunctionField_yGen_over_baseGeneral`) were all landed by D-1, so the
only new declaration is the headline itself.

Only the proof body is adapted to mathlib `v4.34.0`.

Reference (public mirror, pinned):
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_WeierstrassCurve_Affine_exists_algHom_functionField_baseChange_finrankAlong_eq.lean>
-/
import FLTForHuman.WeierstrassCurve.Isogeny.BaseChange

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

universe u v w

noncomputable section

open Polynomial
open scoped Polynomial.Bivariate WeierstrassCurve
open AlgebraicCurve

namespace WeierstrassCurve
namespace Affine

/-- An integral `F`-endomorphism of `(W⁄F).FunctionField` of finite degree descends to
`F'` with the same degree: there is an integral `F'`-endomorphism `ι'` of
`(W⁄F').FunctionField` with `finrankAlong F' ι' = finrankAlong F ι`. -/
theorem exists_algHom_functionField_baseChange_finrankAlong_eq
    {R₀ : Type u} [Field R₀] (W : WeierstrassCurve R₀) [W.IsElliptic]
    (F : Type v) [Field F] [Algebra R₀ F] [DecidableEq F] [IsAlgClosed F] [CharZero F]
    (F' : Type w) [Field F'] [Algebra R₀ F'] [DecidableEq F'] [IsAlgClosed F'] [CharZero F']
    [Algebra F F'] [IsScalarTower R₀ F F']
    (ι : (W.baseChange F).toAffine.FunctionField →ₐ[F] (W.baseChange F).toAffine.FunctionField)
    (hι : ι.toRingHom.IsIntegral) (hfin : FiniteAlong F ι) :
    ∃ ι' : (W.baseChange F').toAffine.FunctionField →ₐ[F'] (W.baseChange F').toAffine.FunctionField,
      ι'.toRingHom.IsIntegral ∧ ∃ hfin' : FiniteAlong F' ι', finrankAlong F' ι' = finrankAlong F ι := by
  obtain ⟨D', hD'⟩ := ModularCurve.isogenyEndDatumBaseChangeAlong_dischargeGeneral W F F'
    (IsScalarTower.toAlgHom R₀ F F') (finrankAlong F ι) ⟨⟨ι, hι, hfin⟩, rfl⟩
  exact ⟨D'.ι, D'.hι, D'.hfin, hD'⟩

end Affine
end WeierstrassCurve

end
