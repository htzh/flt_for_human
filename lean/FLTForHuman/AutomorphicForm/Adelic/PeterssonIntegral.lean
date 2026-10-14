/-
  The adelic Petersson integral.

  `peterssonIntegral s S x y` is the pairing `∫ g in S, x g * conj (y g) * ‖det g‖ ^ (-s)`
  against the adelic `GL₂` Haar measure, weighted by the idèle norm of the determinant to the
  power `-s` so as to compensate a central character of modulus `‖·‖ ^ s`. It is the pairing the
  weighted-Petersson covariance, non-vanishing and sesquilinearity results
  (`AutomorphicForm.exists_sesqForm_eq_peterssonIntegral_…`) are stated over.

  Transcribed verbatim from `Definitions/Def_AutomorphicForm_PeterssonIntegral.lean` (pinned
  `aa2d8b3`, 22 lines / 1 declaration). The pin's stub import `Def_NumberField_TateGlobalZeta`
  is replaced by the port's `NumberField/TateGlobal/Defs.lean` (and `NumberField/AdelicHaar/
  GeneralLinear.lean` for `glBorel`/`adelicGLHaar`); the pin namespace `AutomorphicForm` is kept.
  mathlib `v4.34.0` has no counterpart, so the declaration is residue.

  Pin: `anthropics/fermats-last-theorem` at `aa2d8b3`.
-/
import FLTForHuman.AutomorphicForm.Adelic.Basic
import FLTForHuman.NumberTheory.AdelicHaar.GeneralLinear
import FLTForHuman.NumberTheory.NumberField.TateGlobal.Defs

set_option autoImplicit false

noncomputable section

open NumberField NumberField.AdelicHaar MeasureTheory

namespace AutomorphicForm

variable (F : Type) [Field F] [NumberField F]

def peterssonIntegral (s : ℝ) (S : Set (AdelicGL2 (𝓞 F) F)) (x y : AdelicGL2 (𝓞 F) F → ℂ) : ℂ :=
  letI := glBorel (Fin 2) (𝓞 F) F
  ∫ g in S,
    x g * (starRingEnd ℂ) (y g) *
      ((NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ^ (-s) : ℝ) : ℂ)
    ∂(adelicGLHaar (Fin 2) (𝓞 F) F)

end AutomorphicForm

end
