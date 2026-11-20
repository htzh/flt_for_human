/-
  SET-AF91B consumer: the finite window points as an explicit finset.

  **The row.** `FLTForHuman/AutomorphicForm/Adelic/Siegel/AmpleFiniteness.lean` carries
  `finite_setOf_exists_globalPoints_mul_mem_image_centreCutSiegelSetAmple`: for an ample centre-cut
  Siegel window and `x` with all archimedean components row isometries, only finitely many rational
  `γ` have a translate in the window over `x`.

  **The reading.** The `Set.Finite` is turned into an explicit `Finset` (through `Finite.toFinset`),
  which is the form the partition-of-unity and counting arguments use when they index by the
  rational points.

  `spec/` is outside every Lake library, so this file is checked by
  `lake env lean spec/AutomorphicFormSetAF91BConsumer.lean` and never enters the build.
-/
import FLTForHuman.AutomorphicForm.Adelic.Siegel.AmpleFiniteness

set_option autoImplicit false

noncomputable section

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open IsDedekindDomain AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open scoped ENNReal BigOperators

namespace AutomorphicFormSetAF91BConsumer

/-- **The reading.** The finite set of window points is an explicit `Finset` of rational matrices. -/
theorem exists_finset_forall_globalPoints_mul_mem_image_centreCutSiegelSetAmple
    (F : Type) [Field F] [NumberField F]
    (c u d₁ d₂ κ : ℝ) (hc : 0 < c) (hd₁ : 0 < d₁) (x : AdelicGL2 (𝓞 F) F)
    (hx : ∀ w : InfinitePlace F,
      archComponent F w (glArch (𝓞 F) F x) ∈ rowIsometrySubgroup (w.Completion)) :
    ∃ T : Finset (Matrix.GeneralLinearGroup (Fin 2) F), ∀ γ : Matrix.GeneralLinearGroup (Fin 2) F,
      (∃ s ∈ centreCutSiegelSetAmple F c u d₁ d₂ κ,
        globalPoints (𝓞 F) F γ * s ∈ (· * x) '' centreCutSiegelSetAmple F c u d₁ d₂ κ) → γ ∈ T := by
  have h := finite_setOf_exists_globalPoints_mul_mem_image_centreCutSiegelSetAmple F c u d₁ d₂ κ hc hd₁ x hx
  exact ⟨h.toFinset, fun γ hγ => h.mem_toFinset.mpr hγ⟩

end AutomorphicFormSetAF91BConsumer
