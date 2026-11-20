import FLTForHuman.AutomorphicForm.Adelic.ProductionPinsTail

/-!
  SET-AF92E consumer: the cuspidal functions are closed under an affine combination.

  **The rows.** `FLTForHuman/AutomorphicForm/Adelic/ProductionPinsTail.lean` carries
  `AutomorphicForm.IsCuspidalFn.add` and `IsCuspidalFn.smul`: a sum of cuspidal functions is
  cuspidal, and a scalar multiple is cuspidal (given the integrabilities of the constant-term
  integrands).

  **The reading.** The two rows composed on `c·f₁ + f₂`: the cuspidal class is a `ℂ`-submodule of the
  functions, the form the cusp-space arguments use when they take linear combinations of cusp forms.
  The scalar integrability is transported through `constantTermIntegrand`'s definition.

  `spec/` is outside every Lake library, so this file is checked by
  `lake env lean spec/AutomorphicFormSetAF92EConsumer.lean` and never enters the build.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open IsDedekindDomain AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open scoped ENNReal NNReal BigOperators

namespace AutomorphicFormSetAF92EConsumer

theorem IsCuspidalFn.add_smul
    {Q : Type*} [MeasurableSpace Q] {G : Type*} [Group G]
    {μ : Measure Q} {u : Q → G} {f₁ f₂ : G → ℂ}
    (hf₁ : IsCuspidalFn μ u f₁) (hf₂ : IsCuspidalFn μ u f₂) (c : ℂ)
    (h₁ : ∀ g, Integrable (constantTermIntegrand u f₁ g) μ)
    (h₂ : ∀ g, Integrable (constantTermIntegrand u f₂ g) μ) :
    IsCuspidalFn μ u (fun x => c * f₁ x + f₂ x) := by
  have hc : IsCuspidalFn μ u (fun x => c * f₁ x) := IsCuspidalFn.smul hf₁ c
  refine IsCuspidalFn.add hc hf₂ ?_ h₂
  intro g
  unfold constantTermIntegrand
  exact (h₁ g).const_mul c

end AutomorphicFormSetAF92EConsumer
