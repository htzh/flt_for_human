import FLTForHuman.AutomorphicForm.Adelic.WhittakerPositivity

/-!
  SET-AF92D consumer: the `L²` norm of a cusp section is the sum of the squared coefficients.

  **The row.** `FLTForHuman/AutomorphicForm/Adelic/WhittakerPositivity.lean` carries
  `integral_mul_conj_eq_tsum_whittakerCoefficient_mul_conj`: the integral of `φ₁ · conj φ₂` along the
  unipotent orbit is the `tsum` of the coefficient-product series.

  **The reading.** At `φ₁ = φ₂` the identity becomes the `L²`-norm expansion
  `∫ ‖φ‖² = ∑' ‖wc‖²`, which is how the Bessel/Petersson arguments read the energy of a section.
  The passage is the pointwise `z · conj z = ‖z‖²` (`Complex.mul_conj`, `Complex.normSq_eq_norm_sq`)
  pushed through the integral and the `tsum`.

  `spec/` is outside every Lake library, so this file is checked by
  `lake env lean spec/AutomorphicFormSetAF92DConsumer.lean` and never enters the build.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open IsDedekindDomain AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open scoped ENNReal NNReal BigOperators ComplexConjugate

namespace AutomorphicFormSetAF92DConsumer

theorem integral_normSq_eq_tsum_normSq_whittakerCoefficient
    (F : Type) [Field F] [NumberField F]
    (D : Set (AdelicGL2 (𝓞 F) F)) (U : Ideal (𝓞 F) → Subgroup (AdelicGL2 (𝓞 F) F))
    (gen : HeightOneSpectrum (𝓞 F) → AdelicGL2 (𝓞 F) F)
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (hψ : IsGlobalAddChar F ψ)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (g : AdelicGL2 (𝓞 F) F)
    (hper : ∀ (β : F) (u : AdeleRing (𝓞 F) F),
      φ (unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) β + u) * g) = φ (unipotentGL2 u * g))
    (hcont : Continuous fun x : AdeleRing (𝓞 F) F => φ (unipotentGL2 x * g))
    (hbdd : ∃ C : ℝ, ∀ x : AdeleRing (𝓞 F) F, ‖φ (unipotentGL2 x * g)‖ ≤ C)
    (hsum : Summable fun α : F =>
      ‖whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ φ α g‖) :
    ∫ x, (‖φ (unipotentGL2 x * g)‖ : ℂ) ^ 2
        ∂(productionPinsOf F D U gen (adelicBox F)).ν =
      ∑' α : F, (‖whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ φ α g‖ : ℂ) ^ 2 := by
  have h := integral_mul_conj_eq_tsum_whittakerCoefficient_mul_conj F D U gen ψ hψ φ φ g
    hper hcont hcont hbdd hsum
  simpa only [Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_pow] using h

end AutomorphicFormSetAF92DConsumer
