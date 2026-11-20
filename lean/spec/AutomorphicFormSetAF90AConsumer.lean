/-
  SET-AF90A consumer: an isotypic cusp form in an orthogonal complement is a realization.

  **The rows.** `FLTForHuman/AutomorphicForm/Adelic/Cusp/SpectrumConstituentClosure.lean` carries
  both halves of the isotypic picture: `isIsotypicCuspFormAt_of_mem_of_sub_mem_orthogonal` (a
  cuspidal `K`-finite form in the right membership classes and orthogonal to a closed cusp subrep
  is isotypic) and `IsIsotypicCuspFormAt.exists_smoothCuspRealizationAt_toFun_eq_of_ne_bot` (a
  nonzero isotypic form is the underlying function of a smooth cusp realization).

  **The reading.** The orthogonal-complement hypothesis is the one the pin's decomposition proof
  actually produces; feeding its conclusion to the realization row gives the smooth-cusp interface
  for the *second* form `ψ` — the direction a consumer that starts from the orthogonal-complement
  membership (rather than from an isotypic hypothesis) needs.

  `spec/` is outside every Lake library, so this file is checked by
  `lake env lean spec/AutomorphicFormSetAF90AConsumer.lean` and never enters the build.
-/
import FLTForHuman.AutomorphicForm.Adelic.Cusp.SpectrumConstituentClosure

set_option autoImplicit false

noncomputable section

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open IsDedekindDomain AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open AutomorphicForm.CuspidalConstituent AutomorphicForm.CuspidalSpectrum
open scoped ComplexConjugate ENNReal InnerProductSpace BigOperators Matrix

namespace AutomorphicFormSetAF90AConsumer

/-- **The reading.** The orthogonal-complement membership row, then the realization row at the
nonzero form `ψ`: a cuspidal `K`-finite form in the orthogonal complement of a closed cusp subrep
is the underlying function of a smooth cusp realization with the prescribed level, central
character and exceptional set. -/
theorem exists_smoothCuspRealizationAt_of_mem_of_sub_mem_orthogonal
    (F : Type) [Field F] [NumberField F] (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (hc : 0 < c) (hd₁ : 0 < d₁) (hd : d₁ < d₂)
    (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ) (σ : ℝ) (hσ : HasModulus F ξ σ)
    {α β : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)} (hΦ₀ : IsSlabFundamentalDomain F α β Φ₀)
    (N : Ideal (𝓞 F)) (hN : N ≠ ⊥) (S : Finset (HeightOneSpectrum (𝓞 F))) (Ψ : HeckeEigensystem F ℂ)
    (M : Submodule ℂ ↥(cuspSubcarrier F hΦ₀ σ ξ)) (hM : IsClosedCuspSubrep F hΦ₀ σ ξ M)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφI : IsIsotypicCuspFormAt F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ξ N S Ψ φ)
    (hφm : φ ∈ cuspMemberSubmodule F Φ₀ ξ)
    (ψ : AdelicGL2 (𝓞 F) F → ℂ) (hψK : ψ ∈ cuspKFiniteSubmodule F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ξ)
    (hψm : ψ ∈ cuspMemberSubmodule F Φ₀ ξ)
    (hψM : toCuspSubcarrier F hΦ₀ σ ξ ⟨ψ, hψm⟩ ∈ M)
    (hperp : toCuspSubcarrier F hΦ₀ σ ξ ⟨φ, hφm⟩ - toCuspSubcarrier F hΦ₀ σ ξ ⟨ψ, hψm⟩ ∈ Mᗮ)
    (hψne : ψ ≠ 0) :
    ∃ (Ψ' : HeckeEigensystem F ℂ) (R : SmoothCuspRealizationAt F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) Ψ'.toRawCentral),
      Ψ'.level = N ∧ (∀ v, Ψ'.a v = Ψ.a v) ∧ (∀ v, Ψ'.b v = Ψ.b v) ∧
        R.toFun = ψ ∧ R.centralChar = ξ ∧ R.exceptionalSet = S := by
  have hI := isIsotypicCuspFormAt_of_mem_of_sub_mem_orthogonal F c u d₁ d₂ T hc hd₁ hd hcov
    ξ σ hσ hΦ₀ N S Ψ M hM φ hφI hφm ψ hψK hψm hψM hperp
  exact IsIsotypicCuspFormAt.exists_smoothCuspRealizationAt_toFun_eq_of_ne_bot F
    (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
      (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
      (fun v => heckeGen (𝓞 F) F v) (adelicBox F)) ξ N hN S Ψ ψ hI hψne

end AutomorphicFormSetAF90AConsumer
