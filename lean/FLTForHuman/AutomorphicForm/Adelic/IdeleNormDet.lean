/-
  The idèle norm of the determinant of a global point is one.

  `AutomorphicForm.ideleNorm_det_globalPoints`: for a global point `γ : GL₂(F)`, the idèle norm
  of the determinant of its image in `GL₂(𝔸_F)` is `1`. It is the idèle-norm form of the
  principal-idèle fact `distribHaarChar (algebraMap a) = 1`, through
  `det (globalPoints γ) = Units.map (algebraMap F 𝔸_F) (det γ)`.

  Transcribed from the pin `P2M/Sol/S_AutomorphicForm_ideleNorm_det_globalPoints.lean` (pinned
  `aa2d8b3`, 27 lines / 1 declaration) and its `Theorems/Thm_AutomorphicForm_ideleNorm_det_globalPoints.lean`
  wrapper (the statement authority). The pin namespace `AutomorphicForm` is kept. The same
  statement was previously carried `private` in the slab-covering engine
  (`AutomorphicForm/Adelic/Siegel/SlabCovering.lean`); it is homed here as the public node it is
  (a premise of `exists_sesqForm_eq_peterssonIntegral_…`, and a graph node with 170 pin
  consumers), and the engine now imports it. mathlib `v4.34.0` has no counterpart.

  Pin: `anthropics/fermats-last-theorem` at `aa2d8b3`.
-/
import FLTForHuman.AutomorphicForm.Adelic.Basic
import FLTForHuman.NumberTheory.AdelicHaar.Adele
import FLTForHuman.NumberTheory.AdelicModulus
import FLTForHuman.NumberTheory.NumberField.TateGlobal.Defs

set_option autoImplicit false

noncomputable section

open IsDedekindDomain NumberField NumberField.TateGlobal NumberField.AdelicHaar
open scoped NumberField

namespace AutomorphicForm

theorem ideleNorm_det_globalPoints {F : Type} [Field F] [NumberField F]
    (γ : Matrix.GeneralLinearGroup (Fin 2) F) :
    NumberField.TateGlobal.ideleNorm F
        (Matrix.GeneralLinearGroup.det (AutomorphicForm.globalPoints (𝓞 F) F γ)) = 1 := by
  have hdet : Matrix.GeneralLinearGroup.det (globalPoints (𝓞 F) F γ)
      = Units.map (algebraMap F (AdeleRing (𝓞 F) F)).toMonoidHom (Matrix.GeneralLinearGroup.det γ) := by
    refine Units.ext ?_
    rw [Units.coe_map, Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.val_det_apply,
      RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, RingHom.map_det]
    rfl
  let := adeleBorel (𝓞 F) F
  have := borelSpace_adeleBorel (𝓞 F) F
  unfold ideleNorm
  rw [hdet, NumberField.AdeleRing.distribHaarChar_algebraMap F (Matrix.GeneralLinearGroup.det γ)]
  rfl

end AutomorphicForm

end
