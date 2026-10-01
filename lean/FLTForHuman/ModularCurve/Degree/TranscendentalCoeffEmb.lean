/-
  The bar-embedded `j(q)` is transcendental: the pin's
  `ModularCurve.transcendental_coeffEmb_jq`.

  The pin proves this inside the `DivUSol` modular-unit/cuspidal-divisor/Fricke
  development (`P2M/Sol/S_ModularCurve_transcendental_coeffEmb_jq.lean`, 265 lines)
  and only then concludes transcendence.  The port already carries the two pieces
  the statement needs -- `transcendental_jqModC` (`Degree/PhiDegree.lean`) and the
  definitional bridge `coeffEmb L jq = jqModC L` (`Degree/LaurentGlue.lean`) -- and
  mathlib's `Subalgebra.transcendental_iff_transcendental_val` moves transcendence
  across the `laurentBaseChange` subtype, so the node is the four lines below.  It
  is a leaf module so that bringing in `PhiDegree`/`QAdicPlace` does not widen any
  existing module's cone.

  FLT provenance, pinned `aa2d8b3`:
  https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularCurve_transcendental_coeffEmb_jq.lean
  https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_transcendental_coeffEmb_jq.lean
-/
import FLTForHuman.ModularCurve.Degree.LaurentGlue
import FLTForHuman.ModularCurve.Degree.PhiDegree
import FLTForHuman.ModularCurve.Defs.QAdicPlace

set_option autoImplicit false

noncomputable section

namespace ModularCurve

/-- `j(q)`, embedded in the bar field `laurentBaseChange L (modularFunctionFieldFull N)`
by `coeffEmb`, is transcendental over `L`. Verbatim from
`Theorems/Thm_ModularCurve_transcendental_coeffEmb_jq.lean`. -/
theorem transcendental_coeffEmb_jq (L : Type*) [Field L] [Algebra ℚ L] (N : ℕ) [NeZero N] :
    Transcendental L (⟨coeffEmb L jq, coeffEmb_mem_laurentBaseChange L (jq_mem_full N)⟩ :
      laurentBaseChange L (modularFunctionFieldFull N)) := by
  rw [Subalgebra.transcendental_iff_transcendental_val]
  show Transcendental L (coeffEmb L jq)
  rw [coeffEmb_jq]
  exact transcendental_jqModC L

end ModularCurve

end
