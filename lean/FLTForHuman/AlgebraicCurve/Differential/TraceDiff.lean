/-
The trace differential of a tower of field extensions.  This is the `TraceDiff` half of
the pin's `Definitions/Def_ModularCurve_QExpansionDiff.lean` (pinned `aa2d8b3`); its
`Theta` half is homed in `ModularCurve/Period/QExpansionDerivative.lean` and its
`QExpansionDiff` half in `ModularCurve/Period/QExpansionDiff.lean`.  Statements are
transcribed verbatim.

References (public mirror, pinned):
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularCurve_QExpansionDiff.lean>
-/
import Mathlib.RingTheory.Kaehler.Basic
import Mathlib.RingTheory.Trace.Defs

set_option autoImplicit false

noncomputable section

namespace AlgebraicCurve

section TraceDiff

variable (K F F' : Type*) [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
  [Algebra F F'] [IsScalarTower K F F']

def IsTraceDiff (t : Ω[F'⁄K] →ₗ[F] Ω[F⁄K]) : Prop :=
  ∀ (y : F') (ω : Ω[F⁄K]),
    t (y • KaehlerDifferential.map K K F F' ω) = Algebra.trace F F' y • ω

open scoped Classical in

def traceDiff : Ω[F'⁄K] →ₗ[F] Ω[F⁄K] :=
  if h : ∃ t : Ω[F'⁄K] →ₗ[F] Ω[F⁄K], IsTraceDiff K F F' t then h.choose else 0

end TraceDiff

end AlgebraicCurve
