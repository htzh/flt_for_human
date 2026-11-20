/-
  SET-AF91E consumer: the constant term is linear over a binary combination.

  **The rows.** `FLTForHuman/AutomorphicForm/Adelic/Cusp/IsotypicVanishing.lean` carries the
  constant term's additivity (`constantTerm_add`) and homogeneity (`constantTerm_smul`), both at
  the pin's general `(Q, G)` with an arbitrary measure on the unipotent parameter space.

  **The reading.** The two rows are composed into the mixed formula
  `constantTerm (c · f₁ + f₂) = c · constantTerm f₁ + constantTerm f₂`, which is how the constant
  term is used when it is fed a linear combination (the cusp-form and Eisenstein arguments). The
  integrability of the scalar multiple's integrand is transported from `h₁` by the definitional
  unfolding of `constantTermIntegrand`.

  `spec/` is outside every Lake library, so this file is checked by
  `lake env lean spec/AutomorphicFormSetAF91EConsumer.lean` and never enters the build.
-/
import FLTForHuman.AutomorphicForm.Adelic.Cusp.IsotypicVanishing

set_option autoImplicit false

noncomputable section

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open IsDedekindDomain AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open AutomorphicForm.CuspidalConstituent Matrix
open scoped ENNReal BigOperators

namespace AutomorphicFormSetAF91EConsumer

/-- **The reading.** Additivity and homogeneity of the constant term combined on `c · f₁ + f₂`. -/
theorem constantTerm_add_smul
    {Q : Type*} [MeasurableSpace Q] {G : Type*} [Group G]
    (μ : Measure Q) (u : Q → G) (c : ℂ) {f₁ f₂ : G → ℂ} (g : G)
    (h₁ : Integrable (constantTermIntegrand u f₁ g) μ)
    (h₂ : Integrable (constantTermIntegrand u f₂ g) μ) :
    constantTerm μ u (fun x => c * f₁ x + f₂ x) g
      = c * constantTerm μ u f₁ g + constantTerm μ u f₂ g := by
  have hc : Integrable (constantTermIntegrand u (fun x => c * f₁ x) g) μ := by
    unfold constantTermIntegrand
    exact h₁.const_mul c
  rw [constantTerm_add μ u g hc h₂, constantTerm_smul]

end AutomorphicFormSetAF91EConsumer
