/-
Principal divisors for a finite separable extension of `RatFunc K`, at the pin
node's name.

Canonical source: the pinned FLT `aa2d8b3` wrapper

* `Theorems/Thm_AlgebraicCurve_hasPrincipalDivisors_of_finiteDimensional_ratFunc_of_isSeparable.lean`,

whose `S_` file
`P2M/Sol/S_AlgebraicCurve_hasPrincipalDivisors_of_finiteDimensional_ratFunc_of_isSeparable.lean`
(911 lines) is the same mathematics as the already-ported
`AlgebraicCurve.hasPrincipalDivisors_of_finiteDimensional_of_isSeparable`
(`AlgebraicCurve/PrincipalDivisors/IsSeparable.lean`), whose statement is the pin
node's up to binder spelling (`E` explicit vs the wrapper's `(K) (F')` pair).  The
pin's 911-line proof (the `SeparableRelNorm`/ideal-norm route) is not transcribed:
the port's landed theorem is the same statement and its own character-free proof,
so this is a one-line alias.  The pin's wrapper is the statement authority; the
binders below are its verbatim text.

This module assumes `AlgebraicCurve/PrincipalDivisors/IsSeparable.lean` — the
separability transfer and its split-field/Galois proof.

Reference (public mirror, pinned):
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_AlgebraicCurve_hasPrincipalDivisors_of_finiteDimensional_ratFunc_of_isSeparable.lean>
-/
import FLTForHuman.AlgebraicCurve.PrincipalDivisors.IsSeparable
import Mathlib.FieldTheory.RatFunc.Basic

set_option autoImplicit false

open AlgebraicCurve

namespace AlgebraicCurve

/-- **Principal divisors for a finite separable `RatFunc K`-extension.**  Verbatim
from
`Theorems/Thm_AlgebraicCurve_hasPrincipalDivisors_of_finiteDimensional_ratFunc_of_isSeparable.lean`;
one line over the ported `hasPrincipalDivisors_of_finiteDimensional_of_isSeparable`. -/
theorem hasPrincipalDivisors_of_finiteDimensional_ratFunc_of_isSeparable (K : Type*) [Field K]
    (F' : Type*) [Field F'] [Algebra K F'] [Algebra (RatFunc K) F']
    [IsScalarTower K (RatFunc K) F'] [FiniteDimensional (RatFunc K) F']
    [Algebra.IsSeparable (RatFunc K) F'] :
    HasPrincipalDivisors K F' :=
  hasPrincipalDivisors_of_finiteDimensional_of_isSeparable (K := K) F'

end AlgebraicCurve
