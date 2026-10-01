/-
The `RatFunc` K ending — row 6's first public headline.

`AlgebraicCurve.residueTheoremK_ratFunc_of_isAlgClosed`: the residue theorem for
`K(T)` over an algebraically closed field.  The mathematics is the ℙ¹ chain's
`p0n22_cpf_residueTheoremK_ratFunc_of_isAlgClosed_main` (`P1/Core.lean:753`), so this
module is a statement-only wrapper: the public binders are the pin's `Thm_` wrapper
verbatim (the pin's own `S_` file proves the same statement from the same call), and
the wrapper's four extra hypotheses are unused.

Source: `Theorems/Thm_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.lean`
(<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.lean>),
body `P2M/Sol/S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.lean`
(pin 13,170 ln, `solution` at the tail).
-/
import FLTForHuman.AlgebraicCurve.P1.Core

set_option autoImplicit false

namespace AlgebraicCurve

/-- Row 6's `RatFunc` headline: the residue theorem for `K(T)`, `K` algebraically
closed.  This is the pin's `solution`, whose proof is the port's ℙ¹ main theorem. -/
theorem residueTheoremK_ratFunc_of_isAlgClosed
    (K : Type*) [Field K] [IsAlgClosed K] [DecidableEq (RatFunc K)]
    [AlgebraicCurve.HasCanonicalLocalResidueKStar K (RatFunc K)]
    [AlgebraicCurve.HasCanonicalDivisor (K := K) (F := RatFunc K)]
    [∀ v : AlgebraicCurve.Place K (RatFunc K), v.DCoordGenerates] :
    AlgebraicCurve.ResidueTheoremK K (RatFunc K) :=
  AlgebraicCurve.p0n22_cpf_residueTheoremK_ratFunc_of_isAlgClosed_main K

end AlgebraicCurve
