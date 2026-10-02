/-
  Principal divisors on a Weierstrass curve have degree zero.

  For a Weierstrass curve `W` over a characteristic-zero field `F`, the function
  field `W.FunctionField` has principal divisors. This is the pin node
  `WeierstrassCurve.Affine.hasPrincipalDivisors_functionField`, and its proof is a
  single application of the already-ported generic transfer
  `AlgebraicCurve.hasPrincipalDivisors_of_finiteDimensional_ratFunc`: the two
  hypotheses it needs are `Algebra (RatFunc F) W.FunctionField` with its scalar
  tower (`FunctionFieldQuadratic.lean`) and `FiniteDimensional (RatFunc F) W.FunctionField`
  (`FunctionFieldFinite.lean`).

  Transcribed from
  `P2M/Sol/S_WeierstrassCurve_Affine_hasPrincipalDivisors_functionField.lean`
  (pinned `aa2d8b3`); the statement is the `Theorems/` wrapper's. The pin's `S_`
  file is 2,248 lines, but ~2,000 of them are a self-contained Weierstrass
  place/Riemann–Roch/class-group development that this proof does not reach (see
  the frontier scoping registered in `CARRY-FORWARD.md`); that API is deferred
  until its consumers (`IsogenyEndDatum`, `velu*`, `genusOnePlaceGate`, …) need it.
-/
import FLTForHuman.WeierstrassCurve.FunctionFieldFinite
import FLTForHuman.AlgebraicCurve.PrincipalDivisors.Transcendence

set_option autoImplicit false

-- The pin's `haveI` instance walls are transcribed literally.
set_option linter.style.haveILetI false

noncomputable section

namespace WeierstrassCurve.Affine

theorem hasPrincipalDivisors_functionField {F : Type*} [Field F] [CharZero F]
    (W : WeierstrassCurve.Affine F) :
    AlgebraicCurve.HasPrincipalDivisors F W.FunctionField := by
  haveI : FiniteDimensional (RatFunc F) W.FunctionField :=
    finiteDimensional_ratFunc_functionField W
  exact AlgebraicCurve.hasPrincipalDivisors_of_finiteDimensional_ratFunc F W.FunctionField

end WeierstrassCurve.Affine

end
