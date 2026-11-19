/-
  SET-AF88D consumer: the Siegel windows at a concrete window, and the cover/vanishing composition.

  **The rows.** `FLTForHuman/AutomorphicForm/Adelic/Siegel/WindowCriterion.lean` carries the compactness of
  a capped centre-cut Siegel set, the monotonicity of a covering property in the band's lower edge, the
  windows' union being a neighbourhood of every point, and the vanishing criterion for an `L`-function that
  dies on a covering set.

  **The readings.** Zone 1 instantiates the compactness row at `ℚ` and the pin's own ample thresholds
  (`c = 1/2`, `u = 1`, `d₁ = 1/2`, `d₂ = 2`, cap `C = 3`). Zone 2 reads the neighbourhood row as the
  statement about a *point* it is: for every `g` there are thresholds and a finite set whose translates
  are a neighbourhood of `g`. Zone 3 composes the two cover rows: vanishing on the *wider* window set
  suffices, because a cover at the narrow band lifts to the wider one.

  `spec/` is outside every Lake library, so this file is checked by
  `lake env lean spec/AutomorphicFormSetAF88DConsumer.lean` and never enters the build.
-/
import FLTForHuman.AutomorphicForm.Adelic.Siegel.WindowCriterion

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology NumberField NumberField.AdelicHaar NumberField.AdelicLevel
open IsDedekindDomain AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open scoped Classical ENNReal NNReal BigOperators

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

namespace AutomorphicFormSetAF88DConsumer

/-- **Zone 1.** The compactness row at `ℚ` and the ample thresholds: the centre-cut Siegel set with
`c = 1/2`, `u = 1`, the band `[1/2, 2]` and the height cap `3` is compact. -/
theorem isCompact_centreCutSiegelSet_rat_inter_heightCap :
    IsCompact (centreCutSiegelSet ℚ (1 / 2) 1 (1 / 2) 2 ∩
      {g | ∀ w : InfinitePlace ℚ,
        localHeight (archComponent ℚ w (glArch (𝓞 ℚ) ℚ g)) ≤ 3}) :=
  isCompact_centreCutSiegelSet_inter_heightCap ℚ (by norm_num) (by norm_num)

/-- **Zone 2.** The neighbourhood row at a point: for every `g` there are thresholds and a finite set whose
translates of the centre-cut Siegel set form a neighbourhood of `g`. -/
theorem exists_window_mem_nhds (g : AdelicGL2 (𝓞 ℚ) ℚ) :
    ∃ (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 ℚ) ℚ)), 0 < c ∧ 0 < d₁ ∧
      (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂) ∈ 𝓝 g :=
  exists_iUnion_centreCutSiegelSet_mem_nhds ℚ g

/-- **Zone 3.** Vanishing on the *wider* window set suffices: a cover at the narrow band lifts to the wider
one (the monotonicity row), so the vanishing criterion applies to the wider set. -/
theorem eq_zero_of_vanishing_on_wider_window (F : Type) [Field F] [NumberField F]
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ) (φ : AdelicGL2 (𝓞 F) F → ℂ)
    (hφ : IsLsXiFunction (𝓞 F) F ⊤ ξ φ)
    (c u d₁ d₂ d₁' : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (hle : d₁ ≤ d₁') (hlt : d₁' < d₂)
    (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
    (hvan : ∀ g ∈ ⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁' d₂, φ g = 0) :
    φ = 0 :=
  eq_zero_of_isLsXiFunction_of_coversModCentre_of_forall_mem_eq_zero F ξ φ hφ
    (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁' d₂)
    (coversModCentre_of_le_of_lt_of_coversModCentre F c u d₁ d₂ d₁' T hle hlt hcov) hvan

end AutomorphicFormSetAF88DConsumer
