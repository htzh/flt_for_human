/-
The public uniformizer of a place, after FLT's
`Definitions/Def_ModularCurve_CanonicalDivisorUniformizer.lean` (35 ln)
(<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularCurve_CanonicalDivisorUniformizer.lean>).

The pin keeps `uniformizer` (and its two order lemmas) `private` in
`Definitions/Def_ModularCurve_CanonicalDivisor.lean` and re-exposes them here.  The
refactor round promoted the pin's re-exposed copies once, in
`Defs/CanonicalDivisor.lean`, so this module no longer restates `uniformizer` /
`ord_uniformizer` / `uniformizer_ne_zero`; it keeps only the pin's definitional
identity `dCoord_eq`, which needs the single public `Place.uniformizer`.  `dCoord_eq`
is `rfl` because the port's `dCoord` and the public `uniformizer` share their body.
-/
import FLTForHuman.AlgebraicCurve.Defs.CanonicalDivisor

set_option autoImplicit false

noncomputable section

open KaehlerDifferential

namespace AlgebraicCurve

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

namespace Place

variable (v : Place K F)

theorem dCoord_eq : v.dCoord = KaehlerDifferential.D K F v.uniformizer := rfl

end Place

end AlgebraicCurve

end
