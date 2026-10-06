/-
Surjectivity of the point map of a finite integral function-field homomorphism.

Canonical source: the pinned FLT `aa2d8b3` wrapper

* `Theorems/Thm_WeierstrassCurve_Affine_pointMapOfPushforward_surjective.lean`,

with its `S_` file `P2M/Sol/S_WeierstrassCurve_Affine_pointMapOfPushforward_surjective.lean`
(58 lines).  The statement is the wrapper's verbatim text; the proof is the `S_`
file's body adapted to mathlib `v4.34.0`.

The whole new content beyond the already-ported char-free
`WeierstrassCurve.Affine.pointMapOfPushforward_surjective_of_separableAlong'`
(`Isogeny/NatCard.lean`) is the derivation of `SeparableAlong F ι`: the extension is
finite (`hfin`) and integral (`hι`), and in characteristic zero every algebraic
extension is separable.  The pin's `charZero_of_injective_algebraMap` at the field
`E'.FunctionField` supplies the `[CharZero]` instance that
`Algebra.IsSeparable.of_integral` consumes.

Assumes from lower modules: `Isogeny/NatCard.lean` — the char-free surjectivity
lemma and the `pointMapOfPushforward` API.

Reference (public mirror, pinned):
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_WeierstrassCurve_Affine_pointMapOfPushforward_surjective.lean>
-/
import FLTForHuman.WeierstrassCurve.Isogeny.NatCard

set_option autoImplicit false
set_option linter.style.haveILetI false

noncomputable section

open WeierstrassCurve WeierstrassCurve.Affine AlgebraicCurve

universe u

/-- **The point map is surjective.**  Verbatim from
`Theorems/Thm_WeierstrassCurve_Affine_pointMapOfPushforward_surjective.lean`. -/
theorem WeierstrassCurve.Affine.pointMapOfPushforward_surjective
    {F : Type u} [Field F] [DecidableEq F] [IsAlgClosed F] [CharZero F]
    (E E' : WeierstrassCurve.Affine F) [E.IsElliptic] [GenusOnePlaceGate E] [AbelTheorem E]
    [E'.IsElliptic] [GenusOnePlaceGate E'] [AbelTheorem E']
    (ι : E'.FunctionField →ₐ[F] E.FunctionField) (hι : ι.toRingHom.IsIntegral)
    (hfin : FiniteAlong F ι) (hN : NormFormulaAlong F ι hfin) :
    Function.Surjective (pointMapOfPushforward ι hι hfin hN) := by
  have hsep : SeparableAlong F ι := by
    letI := algebraAlong ι
    haveI : Module.Finite E'.FunctionField E.FunctionField := hfin
    haveI : Algebra.IsIntegral E'.FunctionField E.FunctionField := isIntegral_along ι hι
    haveI : CharZero E'.FunctionField :=
      charZero_of_injective_algebraMap (algebraMap F E'.FunctionField).injective
    show Algebra.IsSeparable E'.FunctionField E.FunctionField
    exact Algebra.IsSeparable.of_integral E'.FunctionField E.FunctionField
  exact pointMapOfPushforward_surjective_of_separableAlong' ι hι hfin hN hsep

end
