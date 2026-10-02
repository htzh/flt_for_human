/-
  A finite extension of `K(x)` is essentially of finite type over `K`.

  If `x : F` is transcendental over `K` and `F` is finite-dimensional over the
  rational function field `K⟮x⟯ = IntermediateField.adjoin K {x}`, then `F` is
  essentially of finite type over `K`. The proof chains the three
  `Algebra.EssFiniteType` transports: `K[X] → RatFunc K` is a localization, the
  `K`-algebra isomorphism `RatFunc K ≃ₐ[K] K⟮x⟯` (`RatFunc.algEquivOfTranscendental`)
  transports it to `K⟮x⟯`, and finite type over `K⟮x⟯` composes with `K → K⟮x⟯`.
  Its pin consumers are the `essFiniteType`-flavoured targets
  (`ModularCurve.essFiniteType_x1FunctionFieldBar`,
  `ModularCurve.isCurveOver_and_essFiniteType_laurentBaseChange_xHFunctionField`,
  `ModularCurve.essFiniteType_modularFunctionFieldFullC`, …), none of them ported
  yet; the pin's `isCurveOver_of_transcendental` route does **not** use it.

  Transcribed from
  `P2M/Sol/S_AlgebraicCurve_essFiniteType_of_transcendental_of_finiteDimensional.lean`
  (pinned `aa2d8b3`); the statement is the `Theorems/` wrapper's. FLT imports
  only `Mathlib` and `P2M.Util` here, so there is no `Definitions/` cone behind
  it; every ingredient is mathlib, and the recorded negative is that the
  `EssFiniteType` API has no `of_finiteDimensional` shortcut for this shape, so
  the localization/`AlgEquiv` transports are the route.
-/
import Mathlib.RingTheory.EssentialFiniteness
import Mathlib.FieldTheory.RatFunc.IntermediateField

set_option autoImplicit false

-- The pin's `haveI` instance walls are transcribed literally.
set_option linter.style.haveILetI false

noncomputable section

open IntermediateField Polynomial

namespace AlgebraicCurve

/-- **Finite extensions of `K(x)` are essentially of finite type.**  The pin's
`AlgebraicCurve.essFiniteType_of_transcendental_of_finiteDimensional`, verbatim
from its `Theorems/` wrapper. -/
theorem essFiniteType_of_transcendental_of_finiteDimensional
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    {x : F} (htr : Transcendental K x)
    (hfd : FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F) :
    Algebra.EssFiniteType K F := by
  haveI := hfd
  let e : RatFunc K ≃ₐ[K] K⟮x⟯ := RatFunc.algEquivOfTranscendental x htr
  haveI : Algebra.EssFiniteType K[X] (RatFunc K) :=
    Algebra.EssFiniteType.of_isLocalization (RatFunc K) (nonZeroDivisors K[X])
  haveI : Algebra.EssFiniteType K (RatFunc K) := Algebra.EssFiniteType.comp K K[X] (RatFunc K)
  haveI : Algebra.EssFiniteType K ↥K⟮x⟯ := Algebra.EssFiniteType.of_surjective e.toAlgHom e.surjective
  haveI : Algebra.EssFiniteType ↥K⟮x⟯ F := Algebra.EssFiniteType.of_finiteType _ _
  exact Algebra.EssFiniteType.comp K ↥K⟮x⟯ F

end AlgebraicCurve

end
