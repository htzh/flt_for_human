/-
  Cross-module wire test for the Weierstrass principal-divisor capstone.

  A `spec/` probe, not a library module. Two executed zones: the function-field
  prerequisites (`adjoin_yCoord_eq_top`, `finiteDimensional_ratFunc_functionField`)
  and the headline `hasPrincipalDivisors_functionField`, applied both at a
  variable curve over `ℚ` (discharging `[CharZero ℚ]`) and at a concrete curve.
-/
import FLTForHuman.WeierstrassCurve.PrincipalDivisors

set_option autoImplicit false

noncomputable section

open Polynomial WeierstrassCurve.Affine

namespace WeierstrassCurveConsumer

-- Zone 1: the function-field prerequisites. `yCoord` generates the function
-- field over `RatFunc F`, and it is a finite extension.
#check @WeierstrassCurve.Affine.adjoin_yCoord_eq_top
#check @WeierstrassCurve.Affine.finiteDimensional_ratFunc_functionField

example (F : Type*) [Field F] (W : WeierstrassCurve.Affine F) :
    IntermediateField.adjoin (RatFunc F) {WeierstrassCurve.Affine.yCoord W} = ⊤ :=
  WeierstrassCurve.Affine.adjoin_yCoord_eq_top

example (F : Type*) [Field F] (W : WeierstrassCurve.Affine F) :
    FiniteDimensional (RatFunc F) W.FunctionField :=
  WeierstrassCurve.Affine.finiteDimensional_ratFunc_functionField W

-- Zone 2: the headline, at a variable curve over `ℚ` ...
#check @WeierstrassCurve.Affine.hasPrincipalDivisors_functionField

example (W : WeierstrassCurve.Affine ℚ) :
    AlgebraicCurve.HasPrincipalDivisors ℚ W.FunctionField :=
  WeierstrassCurve.Affine.hasPrincipalDivisors_functionField W

-- ... and at a concrete curve `y² = x³ + 1`.
example : AlgebraicCurve.HasPrincipalDivisors ℚ
    (WeierstrassCurve.mk (0 : ℚ) 0 0 0 1).toAffine.FunctionField :=
  WeierstrassCurve.Affine.hasPrincipalDivisors_functionField _

end WeierstrassCurveConsumer

end
