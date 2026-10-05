/-
The `restrictAlong` place calculus and the identity `AlgHom` facts, extracted
from the Vélu H4 module `FLTForHuman/WeierstrassCurve/Velu/RestrictAlong.lean`
(where they were transcribed from the pin's `S_…exists_restrictAlong_placeOfPoint_eq_add.lean`
lines 3269–3301) so that the H5 `IsogenyEndDatum` column can consume them
without importing Vélu.

This is a leaf: it imports only `AlgebraicCurve/Defs/Correspondence.lean`.
Declaration names, namespaces and kinds are unchanged.

Reference (public mirror, pinned):
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_WeierstrassCurve_Affine_IsogenyEndDatum_exists_restrictAlong_placeOfPoint_eq_add.lean#L3269-L3301>
-/
import FLTForHuman.AlgebraicCurve.Defs.Correspondence
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

noncomputable section

namespace AlgebraicCurve.Place

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']

theorem mem_restrictAlong_iff (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral)
    (w : Place K F') (f : F) :
    f ∈ (w.restrictAlong φ hφ).toValuationSubring ↔ φ f ∈ w.toValuationSubring :=
  Iff.rfl

theorem ramificationIndexAlong_pos (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral)
    (w : Place K F') : 0 < Place.ramificationIndexAlong φ w := by
  letI := algebraAlong φ
  haveI := isScalarTower_along φ
  haveI := isIntegral_along φ hφ
  exact w.ramificationIndex_pos

theorem ord_restrictAlong_ne_zero_iff (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral)
    (w : Place K F') (f : F) :
    (w.restrictAlong φ hφ).ord f ≠ 0 ↔ w.ord (φ f) ≠ 0 := by
  rw [w.ord_restrictAlong φ hφ f]
  have hpos := Place.ramificationIndexAlong_pos φ hφ w
  constructor
  · intro h hcon
    rcases mul_eq_zero.mp hcon with h1 | h1
    · omega
    · exact h h1
  · intro h hcon
    exact h (by rw [hcon, mul_zero])

end AlgebraicCurve.Place

namespace WeierstrassCurve

namespace Affine

namespace IsogenyEndDatum

variable {F : Type*} [Field F] (W : Affine F)

theorem isIntegral_algHomId :
    (AlgHom.id F W.FunctionField).toRingHom.IsIntegral :=
  RingHom.isIntegral_of_surjective _ Function.surjective_id

theorem finiteAlong_algHomId : AlgebraicCurve.FiniteAlong F (AlgHom.id F W.FunctionField) := by
  unfold AlgebraicCurve.FiniteAlong AlgebraicCurve.algebraAlong
  exact Module.Finite.self _

theorem restrictAlong_algHomId (w : AlgebraicCurve.Place F W.FunctionField) :
    w.restrictAlong (AlgHom.id F W.FunctionField) (isIntegral_algHomId W) = w :=
  AlgebraicCurve.Place.ext (SetLike.ext fun _ => Iff.rfl)

end IsogenyEndDatum

end Affine

end WeierstrassCurve
