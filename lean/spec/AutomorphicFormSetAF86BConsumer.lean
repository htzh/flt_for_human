/-
  SET-AF86B consumer: the archimedean derivative and the Casimir on the diagonal `x' = x`.

  **The rows.** `FLTForHuman/AutomorphicForm/Adelic/PeterssonSkewAdjunction.lean` carries the formal
  adjointness of the archimedean differential operators for the Petersson pairing:
  `setIntegral_archDerivAt{,Complex}_mul_conj_add_eq_zero_of_isFundamentalDomain` (the derivative is
  skew-adjoint) and `setIntegral_archCasimirAt{,Complex}_mul_conj_eq_and_…_adjoint_…` (the Casimir is
  self-adjoint, the raised/lowered combinations adjoint up to a sign).

  **The readings.** Both rows are stated for a *pair* `x x'`; the form they are used in downstream is the
  diagonal `x' = x`, where the derivative statement says the pairing `∫ X x · conj x` is purely imaginary
  (its two halves cancel) and the Casimir statement says `∫ C x · conj x` is real. The two zones below are
  exactly that specialisation, `x' := x`, with the hypotheses the row then needs only once.

  `spec/` is outside every Lake library, so this file is checked by
  `lake env lean spec/AutomorphicFormSetAF86BConsumer.lean` and never enters the build.
-/
import FLTForHuman.AutomorphicForm.Adelic.PeterssonSkewAdjunction

set_option autoImplicit false

noncomputable section

open MeasureTheory Set NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.TateGlobal
open IsDedekindDomain AutomorphicForm
open scoped Classical ENNReal NNReal Pointwise ComplexConjugate

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

namespace AutomorphicFormSetAF86BConsumer

/-- **Zone 1.** The derivative row on the diagonal: the two halves of the pairing cancel, so
`∫ X x · conj x + x · conj (X x) = 0` holds for a single function. -/
theorem setIntegral_archDerivAt_mul_conj_add_eq_zero_self
    (K : Type) [Field K] [NumberField K]
    (w : InfinitePlace K) (hw : w.IsReal) (X : ArchDir)
    (e₁ e₂ : ℝ) (he₁ : 0 < e₁) (he : e₁ < e₂)
    (𝓕 : Set (AdelicGL2 (𝓞 K) K)) (h𝓕m : MeasurableSet 𝓕)
    (h𝓕s : 𝓕 ⊆ {g | ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc e₁ e₂})
    (h𝓕 : IsFundamentalDomain (globalPoints (𝓞 K) K).range 𝓕
      ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict
        {g | ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc e₁ e₂}))
    (x : AdelicGL2 (𝓞 K) K → ℂ)
    (hx : ∀ (γ : GL (Fin 2) K) (g : AdelicGL2 (𝓞 K) K), x (globalPoints (𝓞 K) K γ * g) = x g)
    (hxc : Continuous x) (hxs : IsArchSmoothAt hw x)
    (hDx : Continuous (archDerivAt hw X x))
    (B : ℝ) (hB : ∀ g : AdelicGL2 (𝓞 K) K, ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc e₁ e₂ →
      ‖x g‖ ≤ B ∧ ‖archDerivAt hw X x g‖ ≤ B) :
    ∫ g in 𝓕, (archDerivAt hw X x g * conj (x g) + x g * conj (archDerivAt hw X x g))
      ∂(adelicGLHaar (Fin 2) (𝓞 K) K) = 0 :=
  setIntegral_archDerivAt_mul_conj_add_eq_zero_of_isFundamentalDomain K w hw X e₁ e₂ he₁ he
    𝓕 h𝓕m h𝓕s h𝓕 x x hx hx hxc hxc hxs hxs hDx hDx B
    (fun g hg => ⟨(hB g hg).1, (hB g hg).1, (hB g hg).2, (hB g hg).2⟩)

/-- **Zone 2.** The Casimir row on the diagonal, first conjunct: the Casimir is self-adjoint, so
`∫ C x · conj x = ∫ x · conj (C x)` for a single function. -/
theorem setIntegral_archCasimirAt_mul_conj_eq_self
    (K : Type) [Field K] [NumberField K]
    (w : InfinitePlace K) (hw : w.IsReal)
    (e₁ e₂ : ℝ) (he₁ : 0 < e₁) (he : e₁ < e₂)
    (𝓕 : Set (AdelicGL2 (𝓞 K) K)) (h𝓕m : MeasurableSet 𝓕)
    (h𝓕s : 𝓕 ⊆ {g | ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc e₁ e₂})
    (h𝓕 : IsFundamentalDomain (globalPoints (𝓞 K) K).range 𝓕
      ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict
        {g | ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc e₁ e₂}))
    (x : AdelicGL2 (𝓞 K) K → ℂ)
    (hx : ∀ (γ : GL (Fin 2) K) (g : AdelicGL2 (𝓞 K) K), x (globalPoints (𝓞 K) K γ * g) = x g)
    (hxc : Continuous x) (hxs : IsArchSmoothAt hw x)
    (hD1 : ∀ d : ArchDir, Continuous (archDerivAt hw d x))
    (hD2 : ∀ d d' : ArchDir, Continuous (archDerivAt hw d (archDerivAt hw d' x)))
    (B : ℝ) (hB : ∀ g : AdelicGL2 (𝓞 K) K, ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc e₁ e₂ →
      ‖x g‖ ≤ B ∧ (∀ d : ArchDir, ‖archDerivAt hw d x g‖ ≤ B) ∧
      (∀ d d' : ArchDir, ‖archDerivAt hw d (archDerivAt hw d' x) g‖ ≤ B)) :
    ∫ g in 𝓕, archCasimirAt hw x g * conj (x g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) =
      ∫ g in 𝓕, x g * conj (archCasimirAt hw x g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) :=
  (setIntegral_archCasimirAt_mul_conj_eq_and_lower_adjoint_of_isFundamentalDomain K w hw
    e₁ e₂ he₁ he 𝓕 h𝓕m h𝓕s h𝓕 x x hx hx hxc hxc hxs hxs hD1 hD1 hD2 hD2 B
    (fun g hg => ⟨(hB g hg).1, (hB g hg).1,
      ⟨fun d => ⟨(hB g hg).2.1 d, (hB g hg).2.1 d⟩,
        fun d d' => ⟨(hB g hg).2.2 d d', (hB g hg).2.2 d d'⟩⟩⟩)).1

end AutomorphicFormSetAF86BConsumer
