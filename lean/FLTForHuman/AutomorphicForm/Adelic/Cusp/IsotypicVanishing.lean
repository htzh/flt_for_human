/-
Isotypic and cover vanishing in the cusp space, with constant-term linearity.

Three small automorphic-function facts: the isotypic cusp submodule is trivial when the archimedean
parameter is nonpositive; an `L`-function that vanishes on a covering set vanishes identically; and
the constant term is additive and homogeneous. They are the API tail the cusp-form arguments call
without opening the constituent or the Siegel machinery.

  spec-pin: P2M/Sol/S_AutomorphicForm_isotypicCuspSubmodule_eq_bot_of_nonpos.lean
  spec-pin: P2M/Sol/S_AutomorphicForm_eq_zero_of_isCuspAutomorphicFnAt_productionPinsOf_of_coversModCentre_of_forall_mem_eq_zero.lean
  spec-pin: P2M/Sol/S_AutomorphicForm_constantTerm_add.lean
  spec-pin: P2M/Sol/S_AutomorphicForm_constantTerm_smul.lean

  ## Port deltas

  - `import FLTForHuman.AutomorphicForm.Adelic.RationalCentreHaar`: the nonpos row's premise
    `isotypicCuspSubmodule_bot_eq_bot_of_productionPinsOf` (the `N = ⊥` branch) lives there and is
    in no other module of the scaffold's closure (FR-0229).
  - `import FLTForHuman.AutomorphicForm.Adelic.Cusp.SpectrumConstituentClosure`: the same row's
    `IsIsotypicCuspFormAt.exists_smoothCuspRealizationAt_toFun_eq_of_ne_bot` (the `N ≠ ⊥` branch).
  - FR-0223: the cover row's `letI := (productionPinsOf F D U gen B).mS` is written as the typed
    `let mS : MeasurableSpace (AdelicGL2 (𝓞 F) F) := …` (the `haveILetI` linter's own suggestion).
    The row's goal is a proposition, so nothing about the frozen statement changes (FR-0235 does
    not apply); the module is silent.
  - heartbeat probe (`lake env lean -DautoImplicit=false -DmaxHeartbeats=N`, never installed):
    silent at **1000**, fails at **800** (`whnf`) and at **500** (`elaborator`); the measured
    pair for the probe is 1000 / 500.
-/
import FLTForHuman.AutomorphicForm.Adelic.Cusp.Constituent
import FLTForHuman.AutomorphicForm.Adelic.ProductionPinsGeneral
import FLTForHuman.AutomorphicForm.Adelic.RationalCentreHaar
import FLTForHuman.AutomorphicForm.Adelic.Cusp.SpectrumConstituentClosure
import FLTForHuman.AutomorphicForm.Adelic.Cusp.CuspUnrealizable
import FLTForHuman.AutomorphicForm.Adelic.Siegel.WindowCriterion

set_option autoImplicit false

noncomputable section

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open IsDedekindDomain AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open AutomorphicForm.CuspidalConstituent Matrix
open scoped ENNReal BigOperators

namespace AutomorphicForm

theorem isotypicCuspSubmodule_eq_bot_of_nonpos
    (F : Type) [Field F] [NumberField F] (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (hc : c ≤ 0) (hd : d₁ < d₂)
    (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
    (ξ : (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)).Z →* ℂˣ)
    (N : Ideal (𝓞 F)) (S : Finset (HeightOneSpectrum (𝓞 F))) (Ψ : HeckeEigensystem F ℂ) :
    isotypicCuspSubmodule F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ξ N S Ψ = ⊥
  := by
  rw [isotypicCuspSubmodule_eq_bot_iff]
  intro φ hφ
  by_cases hN : N = ⊥
  · subst hN
    exact (isotypicCuspSubmodule_eq_bot_iff F _ ξ ⊥ S Ψ).mp
      (AutomorphicForm.isotypicCuspSubmodule_bot_eq_bot_of_productionPinsOf F _ (adelicBox F) ξ S Ψ) φ hφ
  · by_contra h0
    obtain ⟨Ψ', R, -, -, -, hR, -, -⟩ :=
      AutomorphicForm.IsIsotypicCuspFormAt.exists_smoothCuspRealizationAt_toFun_eq_of_ne_bot F _ ξ N hN S Ψ φ hφ h0
    exact AutomorphicForm.not_isArithGenuineCuspRealizable_of_nonpos_of_lt_of_coversModCentre F c u d₁ d₂ T hc hd hcov Ψ'
      ⟨R, show Continuous R.toFun by rw [hR]; exact hφ.continuous⟩

theorem eq_zero_of_isCuspAutomorphicFnAt_productionPinsOf_of_coversModCentre_of_forall_mem_eq_zero
    (F : Type) [Field F] [NumberField F]
    (D : Set (AdelicGL2 (𝓞 F) F)) (U : Ideal (𝓞 F) → Subgroup (AdelicGL2 (𝓞 F) F))
    (gen : HeightOneSpectrum (𝓞 F) → AdelicGL2 (𝓞 F) F) (B : Set (AdeleRing (𝓞 F) F))
    (ξ : (productionPinsOf F D U gen B).Z →* ℂˣ) (φ : AdelicGL2 (𝓞 F) F → ℂ)
    (hφ : IsCuspAutomorphicFnAt F (productionPinsOf F D U gen B) ξ φ)
    (W : Set (AdelicGL2 (𝓞 F) F)) (hcov : CoversModCentre F W)
    (h0 : ∀ x ∈ W, φ x = 0) : φ = 0
  := by
  let mS : MeasurableSpace (AdelicGL2 (𝓞 F) F) := (productionPinsOf F D U gen B).mS
  have h : IsLsXiFunction (𝓞 F) F (productionPinsOf F D U gen B).Z ξ φ :=
    ((lsXiMemberAt_iff (𝓞 F) F (productionPinsOf F D U gen B).μ (productionPinsOf F D U gen B).Z ξ
      (productionPinsOf F D U gen B).D φ).mp hφ.1).1
  exact AutomorphicForm.eq_zero_of_isLsXiFunction_of_coversModCentre_of_forall_mem_eq_zero F ξ φ h W hcov h0

theorem constantTerm_add
    {Q : Type*} [MeasurableSpace Q] {G : Type*} [Group G]
    (μ : Measure Q) (u : Q → G) {f₁ f₂ : G → ℂ} (g : G)
    (h₁ : Integrable (constantTermIntegrand u f₁ g) μ)
    (h₂ : Integrable (constantTermIntegrand u f₂ g) μ) :
    constantTerm μ u (fun x => f₁ x + f₂ x) g
      = constantTerm μ u f₁ g + constantTerm μ u f₂ g
  := by
  simpa [constantTerm, constantTermIntegrand] using integral_add h₁ h₂

theorem constantTerm_smul
    {Q : Type*} [MeasurableSpace Q] {G : Type*} [Group G]
    (μ : Measure Q) (u : Q → G) (c : ℂ) (f : G → ℂ) (g : G) :
    constantTerm μ u (fun x => c * f x) g = c * constantTerm μ u f g
  := by
  simpa [constantTerm, constantTermIntegrand, smul_eq_mul] using
    integral_smul (μ := μ) c (fun q => f (u q * g))

end AutomorphicForm

end
