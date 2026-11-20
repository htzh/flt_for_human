/-
  SET-AF91A consumer: the Whittaker sum in `tsum` form.

  **The row.** `FLTForHuman/AutomorphicForm/Adelic/WhittakerSum.lean` carries
  `hasSum_whittakerCoefficient`: for a continuous `x ↦ φ (unipotentGL2 x * g)` whose Whittaker
  coefficients are summable, the series of the coefficients has sum `φ g`.

  **The reading.** The `HasSum` is turned into the unconditional `∑'` identity, which is the form
  the Fourier-expansion arguments use when they substitute the expansion into an integral
  (`tsum` rewriting, summability side conditions discharged once).

  `spec/` is outside every Lake library, so this file is checked by
  `lake env lean spec/AutomorphicFormSetAF91AConsumer.lean` and never enters the build.
-/
import FLTForHuman.AutomorphicForm.Adelic.WhittakerSum

set_option autoImplicit false

noncomputable section

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open IsDedekindDomain AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open scoped ENNReal BigOperators

namespace AutomorphicFormSetAF91AConsumer

/-- **The reading.** The Whittaker expansion as a `tsum` identity. -/
theorem tsum_whittakerCoefficient
    (F : Type) [Field F] [NumberField F]
    (D : Set (AdelicGL2 (𝓞 F) F))
    (U : Ideal (𝓞 F) → Subgroup (AdelicGL2 (𝓞 F) F))
    (gen : HeightOneSpectrum (𝓞 F) → AdelicGL2 (𝓞 F) F)
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (hψ : IsGlobalAddChar F ψ)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (g : AdelicGL2 (𝓞 F) F)
    (hcont : Continuous (fun x => φ (unipotentGL2 x * g)))
    (hsum : Summable (fun α : F =>
      whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ φ α g)) :
    ∑' α : F, whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ φ α g = φ g :=
  (hasSum_whittakerCoefficient F D U gen ψ hψ φ g hcont hsum).tsum_eq

end AutomorphicFormSetAF91AConsumer
