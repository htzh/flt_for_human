/-
  Cross-module wire test for SET-AF23 (the archimedean cut projector and the archimedean
  approximation).

  A `spec/` probe, not a library module. **One zone**, over `ℚ` with the trivial archimedean type
  family `tysQ` (`ofChar` at the trivial character): it reads the two headlines of
  `Adelic/ArchApproximation.lean` against each other and against the engine of
  `Adelic/ArchCutProjector.lean`.

  * `rightConv_zero_mem` / `rightConv_zero_mem_iff` read
    `rightConv_mem_archCutSubmodule_of_isArchBiFinite` at `g = 0` and at the concrete vanishing
    test function `α = 0` (`isFactorizableTestFn_zero`, `isArchBiFinite_zero`), then compose the
    conclusion with `mem_archCutSubmodule_iff` — i.e. with `archCutSubmodule`'s definition as the
    infimum over the places of the type suprema;
  * `projector_yields_factor` reads `exists_rightConv_eq_of_archCutProjector` as an implication
    in its data `Q`, `hQ` (they are hypotheses of the theorem, not existentials);
  * `exists_projector_and_factor` is the composition the work order asks for: the port's
    `exists_linearMap_archCutProjector_comm_rightTranslate` supplies `Q` together with exactly the
    three conjuncts `exists_rightConv_eq_of_archCutProjector` consumes, so the two headlines
    compose into one existential — the projector and the factorizable, bi-finite `f'` in one
    statement. The wire dies if either the engine's three properties or the approximation's
    hypothesis bundle changes shape.

  It imports only the modules it composes.
-/
import FLTForHuman.AutomorphicForm.Adelic.ArchApproximation
import FLTForHuman.AutomorphicForm.Adelic.ArchCutProjector

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel
open AutomorphicForm AutomorphicForm.CuspidalConstituent
open scoped ENNReal

noncomputable section

namespace SetAF23ArchApproximationConsumer

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

/-- The trivial archimedean type family over `ℚ`: one archimedean type per place, the trivial
character. -/
def tysQ : ArchTypeFamily ℚ := ArchTypeFamily.ofChar ℚ fun _ => 1

/-- **The membership headline at `g = 0`.** Right convolution of the zero function by a
factorizable, archimedean-bi-finite test function stays in the archimedean cut. -/
theorem rightConv_zero_mem {α : AdelicGL2 (𝓞 ℚ) ℚ → ℂ} (hα : IsFactorizableTestFn ℚ α)
    (hαt : IsArchBiFinite ℚ tysQ α) :
    rightConv ℚ (fun _ => 0) α ∈ archCutSubmodule ℚ tysQ :=
  rightConv_mem_archCutSubmodule_of_isArchBiFinite ℚ tysQ (fun _ => 0) continuous_const α hα hαt

/-- **The same vector read through `archCutSubmodule`'s definition.** The conclusion of the
membership headline, unfolded at every place: membership in the supremum of the archimedean type
submodules of that place. -/
theorem rightConv_zero_mem_unfolded {α : AdelicGL2 (𝓞 ℚ) ℚ → ℂ} (hα : IsFactorizableTestFn ℚ α)
    (hαt : IsArchBiFinite ℚ tysQ α) :
    ∀ w : InfinitePlace ℚ,
      rightConv ℚ (fun _ => 0) α ∈ ⨆ i : Fin (tysQ.card w), archTypeSubmoduleAt ℚ w (tysQ.rep w i) :=
  (mem_archCutSubmodule_iff ℚ tysQ _).mp (rightConv_zero_mem hα hαt)

/-- **The membership headline at the concrete vanishing test function.** `α = 0` is factorizable
and archimedean-bi-finite, so the composition above applies with no hypothesis left open. -/
theorem rightConv_zero_zero_mem :
    rightConv ℚ (fun _ => 0) (fun _ => 0) ∈ archCutSubmodule ℚ tysQ :=
  rightConv_zero_mem (isFactorizableTestFn_zero ℚ) (isArchBiFinite_zero ℚ tysQ)

/-- **The approximation headline as an implication in its data.** `Q` and its three properties are
hypotheses, so the statement is read here at the shape "given a projector with those three
properties, every right convolution by a bi-finite test function is the right convolution by a
factorizable, bi-finite one". -/
theorem projector_yields_factor
    (Q : (AdelicGL2 (𝓞 ℚ) ℚ → ℂ) →ₗ[ℂ] (AdelicGL2 (𝓞 ℚ) ℚ → ℂ))
    (hQ :
      (∀ φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ, Continuous φ → φ ∈ archCutSubmodule ℚ tysQ → Q φ = φ) ∧
      (∀ φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ, Continuous φ →
        FiniteDimensional ℂ (Submodule.span ℂ
          {ψ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ |
            ∃ k ∈ (⨆ w : InfinitePlace ℚ, (rowIsometryInclAt₀ ℚ w).range),
              ψ = rightTranslate ℚ k φ}) →
        Q φ ∈ archCutSubmodule ℚ tysQ ⊓ Submodule.span ℂ
          {ψ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ |
            ∃ k ∈ (⨆ w : InfinitePlace ℚ, (rowIsometryInclAt₀ ℚ w).range),
              ψ = rightTranslate ℚ k φ}) ∧
      (∀ φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ, Continuous φ →
        FiniteDimensional ℂ (Submodule.span ℂ
          {ψ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ |
            ∃ k ∈ (⨆ w : InfinitePlace ℚ, (rowIsometryInclAt₀ ℚ w).range),
              ψ = rightTranslate ℚ k φ}) →
        ∀ k ∈ (⨆ w : InfinitePlace ℚ, (rowIsometryInclAt₀ ℚ w).range),
          Q (rightTranslate ℚ k φ) = rightTranslate ℚ k (Q φ)))
    {y : AdelicGL2 (𝓞 ℚ) ℚ → ℂ} (hyc : Continuous y) (hy : y ∈ archCutSubmodule ℚ tysQ)
    {f : AdelicGL2 (𝓞 ℚ) ℚ → ℂ} (tys' : ArchTypeFamily ℚ) (hf : IsFactorizableTestFn ℚ f)
    (hbf : IsArchBiFinite ℚ tys' f) :
    ∃ f' : AdelicGL2 (𝓞 ℚ) ℚ → ℂ,
      IsFactorizableTestFn ℚ f' ∧ IsArchBiFinite ℚ tysQ f' ∧ Q (rightConv ℚ y f) = rightConv ℚ y f' :=
  exists_rightConv_eq_of_archCutProjector ℚ tysQ Q hQ hyc hy tys' hf hbf

/-- **The zone.** The engine's projector — `exists_linearMap_archCutProjector_comm_rightTranslate`,
whose three conjuncts are literally the `hQ` bundle consumed above — composed with the
approximation headline: one existential carrying the projector *and* the bi-finite factorizable
`f'`. -/
theorem exists_projector_and_factor {y : AdelicGL2 (𝓞 ℚ) ℚ → ℂ} (hyc : Continuous y)
    (hy : y ∈ archCutSubmodule ℚ tysQ) {f : AdelicGL2 (𝓞 ℚ) ℚ → ℂ} (tys' : ArchTypeFamily ℚ)
    (hf : IsFactorizableTestFn ℚ f) (hbf : IsArchBiFinite ℚ tys' f) :
    ∃ Q : (AdelicGL2 (𝓞 ℚ) ℚ → ℂ) →ₗ[ℂ] (AdelicGL2 (𝓞 ℚ) ℚ → ℂ),
      (∀ φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ, Continuous φ → φ ∈ archCutSubmodule ℚ tysQ → Q φ = φ) ∧
      (∀ φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ, Continuous φ →
        FiniteDimensional ℂ (Submodule.span ℂ
          {ψ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ |
            ∃ k ∈ (⨆ w : InfinitePlace ℚ, (rowIsometryInclAt₀ ℚ w).range),
              ψ = rightTranslate ℚ k φ}) →
        Q φ ∈ archCutSubmodule ℚ tysQ ⊓ Submodule.span ℂ
          {ψ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ |
            ∃ k ∈ (⨆ w : InfinitePlace ℚ, (rowIsometryInclAt₀ ℚ w).range),
              ψ = rightTranslate ℚ k φ}) ∧
      (∀ φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ, Continuous φ →
        FiniteDimensional ℂ (Submodule.span ℂ
          {ψ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ |
            ∃ k ∈ (⨆ w : InfinitePlace ℚ, (rowIsometryInclAt₀ ℚ w).range),
              ψ = rightTranslate ℚ k φ}) →
        ∀ k ∈ (⨆ w : InfinitePlace ℚ, (rowIsometryInclAt₀ ℚ w).range),
          Q (rightTranslate ℚ k φ) = rightTranslate ℚ k (Q φ)) ∧
      ∃ f' : AdelicGL2 (𝓞 ℚ) ℚ → ℂ,
        IsFactorizableTestFn ℚ f' ∧ IsArchBiFinite ℚ tysQ f' ∧
          Q (rightConv ℚ y f) = rightConv ℚ y f' := by
  obtain ⟨Q, h1, h2, h3⟩ := exists_linearMap_archCutProjector_comm_rightTranslate ℚ tysQ
  exact ⟨Q, h1, h2, h3, projector_yields_factor Q ⟨h1, h2, h3⟩ hyc hy tys' hf hbf⟩

end SetAF23ArchApproximationConsumer

end
