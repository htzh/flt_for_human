/-
  The (central) slab-covering headlines.

  The three public statements the pin ready nodes
  `AutomorphicForm.exists_finset_{central_,}slab_covering_of_coversModCentre[_centreCutSiegelSetAmple]`
  carry, each taken verbatim from its `Theorems/` wrapper and proved by the tier-3
  `AutomorphicForm.SiegelCovering.Engine` kernels of `Siegel/SlabCovering.lean`. This thin
  façade is the checker's wire; the engine stays tier 3 and is recorded in
  `spec/UNWIRED-PUBLIC.md`.

  Pin: `anthropics/fermats-last-theorem` at `aa2d8b3`; the wrappers are
  https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/Theorems/Thm_AutomorphicForm_exists_finset_central_slab_covering_of_coversModCentre.lean
  https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/Theorems/Thm_AutomorphicForm_exists_finset_central_slab_covering_of_coversModCentre_centreCutSiegelSetAmple.lean
  https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/Theorems/Thm_AutomorphicForm_exists_finset_slab_covering_of_coversModCentre.lean
-/
import FLTForHuman.AutomorphicForm.Adelic.Siegel.SlabCovering

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory Matrix
open Set
open AutomorphicForm.WindowedSiegel
open AutomorphicForm.SiegelCovering

noncomputable section

namespace AutomorphicForm

theorem exists_finset_central_slab_covering_of_coversModCentre
    (F : Type) [Field F] [NumberField F] (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (hd : d₁ < d₂)
    (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
    (α β : ℝ) (hα : 0 < α) :
    ∃ N : Finset (AdeleRing (𝓞 F) F)ˣ, ∀ g : AdelicGL2 (𝓞 F) F,
      NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β →
        ∃ γ : GL (Fin 2) F, ∃ n ∈ N, ∃ x ∈ T,
          globalPoints (𝓞 F) F γ * g ∈
            (· * (centralScalar (𝓞 F) F n * x)) '' centreCutSiegelSet F c u d₁ d₂ :=
  Engine.exists_finset_central_slab_covering_of_coversModCentre F c u d₁ d₂ T hd hcov α β hα

theorem exists_finset_central_slab_covering_of_coversModCentre_centreCutSiegelSetAmple
    (F : Type) [Field F] [NumberField F] (c u d₁ d₂ κ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (hd : d₁ < d₂)
    (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSetAmple F c u d₁ d₂ κ)) :
    ∀ a b : ℝ, 0 < a → ∃ N : Finset (AdeleRing (𝓞 F) F)ˣ, ∀ g : AdelicGL2 (𝓞 F) F,
      NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc a b →
        ∃ γ : GL (Fin 2) F, ∃ n ∈ N,
          globalPoints (𝓞 F) F γ * g ∈
            (· * centralScalar (𝓞 F) F n) ''
              (⋃ x ∈ T, (· * x) '' centreCutSiegelSetAmple F c u d₁ d₂ κ) :=
  Engine.exists_finset_central_slab_covering_of_coversModCentre_centreCutSiegelSetAmple
    F c u d₁ d₂ κ T hd hcov

theorem exists_finset_slab_covering_of_coversModCentre
    (F : Type) [Field F] [NumberField F] (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (hd : d₁ < d₂)
    (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
    (α β : ℝ) (hα : 0 < α) :
    ∃ T' : Finset (AdelicGL2 (𝓞 F) F), ∀ g : AdelicGL2 (𝓞 F) F,
      NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β →
        ∃ γ : GL (Fin 2) F,
          globalPoints (𝓞 F) F γ * g ∈ ⋃ x ∈ T', (· * x) '' centreCutSiegelSet F c u d₁ d₂ :=
  Engine.exists_finset_slab_covering_of_coversModCentre F c u d₁ d₂ T hd hcov α β hα

end AutomorphicForm

end
