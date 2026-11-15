/-
  Cross-module wire test for the Whittaker unfolding of an induced section (`AF76A`).

  A `spec/` probe, not a library module. Both zones run at `F = ℚ`:

  * **Zone 1 — the headline, evaluated.** `whittakerCoefficient_bruhatSeries_eq_of_isInducedSection`
    read at the trivial character pair (`χ₁ = χ₂ = 1`, so `φ = chiDet 1` is an induced section by
    `isInducedSection_chiDet`) with the Bruhat series' `∑'` at `ξ = 1` (`one_ne_zero` supplies
    `hξ`), so the unfolded coefficient is the `adelicBox`-average of the Jacquet integrand.
  * **Zone 2 — the production pins' coefficient, rebuilt from the public surface.** The content of
    the pin's private `whittakerCoefficient_productionPins_eq` at the concrete pins
    `productionPins ℚ` — whose `D`, `U`, `gen` are read out in `productionPins_concrete` — by
    rewriting the coefficient's measure (`productionPins_ν`) and `ProbabilityTheory.cond`.

  Deleting the module (or leaving a hole in it) breaks this file: every zone is a real
  composition, no `#check`.
-/
import FLTForHuman.EisensteinGeneral.Unfolding

set_option autoImplicit false

noncomputable section

open MeasureTheory NumberField NumberField.AdelicBox NumberField.AdelicHaar IsDedekindDomain
open AutomorphicForm AutomorphicForm.WindowedSiegel NumberField.AdelicLevel
open ProbabilityTheory Filter Topology Matrix
open scoped ENNReal NNReal

namespace EisensteinGeneralSetAF76AConsumer

attribute [local instance] NumberField.AdelicHaar.adeleBorel
  NumberField.AdelicHaar.borelSpace_adeleBorel

/-! ### Zone 1 — the unfolding identity at the trivial induced section, `ξ = 1` -/

/-- The headline at `F = ℚ`, the trivial character pair and `ξ = 1`: the Whittaker coefficient of
the Bruhat-series summand of `chiDet 1` is the invariant integral of the Jacquet integrand. -/
theorem unfolding_trivial_section
    {ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ} (hψ : IsGlobalAddChar ℚ ψ)
    (g : AdelicGL2 (𝓞 ℚ) ℚ)
    (hint : Integrable
      (fun y => chiDet (𝓞 ℚ) ℚ (1 : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ)
        (adelicWeyl (𝓞 ℚ) ℚ * unipotentGL2 y * g)) (adelicAddHaar (𝓞 ℚ) ℚ)) :
    whittakerCoefficient ℚ (productionPins ℚ) ψ
        (fun g' : AdelicGL2 (𝓞 ℚ) ℚ =>
          chiDet (𝓞 ℚ) ℚ (1 : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) g'
            + ∑' ξ' : ℚ, chiDet (𝓞 ℚ) ℚ (1 : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ)
                (adelicWeyl (𝓞 ℚ) ℚ * unipotentGL2 (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) ξ') * g'))
        1 g
      = ((adelicAddHaar (𝓞 ℚ) ℚ) (adelicBox ℚ))⁻¹.toReal •
          ∫ y, chiDet (𝓞 ℚ) ℚ (1 : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ)
                (adelicWeyl (𝓞 ℚ) ℚ * unipotentGL2 y * g)
              * ψ (-(algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) 1 * y)) ∂(adelicAddHaar (𝓞 ℚ) ℚ) :=
  EisensteinGeneral.Unfolding.whittakerCoefficient_bruhatSeries_eq_of_isInducedSection hψ
    (isInducedSection_chiDet (1 : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ)) one_ne_zero g hint

/-! ### Zone 2 — the production pins at their concrete `D`, `U`, `gen` -/

/-- The concrete windowed-Siegel data the production pins carry at `F = ℚ`. -/
theorem productionPins_concrete :
    (productionPins ℚ).D = centreCutSiegelSet ℚ (1 / 2 : ℝ) 1 (1 / 2) 2
      ∧ (∀ N : Ideal (𝓞 ℚ), (productionPins ℚ).U N = levelOne (𝓞 ℚ) ℚ N)
      ∧ (∀ v : HeightOneSpectrum (𝓞 ℚ), (productionPins ℚ).gen v = heckeGen (𝓞 ℚ) ℚ v) :=
  ⟨productionPins_D ℚ, fun N => productionPins_U ℚ N, fun v => productionPins_gen ℚ v⟩

/-- The coefficient of the production pins, unfolded to the `adelicBox` integral against the
additive Haar measure — the pin's private `whittakerCoefficient_productionPins_eq`, rebuilt from
`productionPins_ν` and `ProbabilityTheory.cond` at `F = ℚ`. -/
theorem whittakerCoefficient_productionPins_eq_at_rat
    (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (α : ℚ)
    (g : AdelicGL2 (𝓞 ℚ) ℚ) :
    whittakerCoefficient ℚ (productionPins ℚ) ψ φ α g
      = ((adelicAddHaar (𝓞 ℚ) ℚ) (adelicBox ℚ))⁻¹.toReal •
          ∫ x in adelicBox ℚ,
            φ (unipotentGL2 x * g) * ψ (-(algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) α * x))
              ∂(adelicAddHaar (𝓞 ℚ) ℚ) := by
  show (∫ x, φ (unipotentGL2 x * g) * ψ (-(algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) α * x))
      ∂((adelicAddHaar (𝓞 ℚ) ℚ)[|adelicBox ℚ])) = _
  unfold ProbabilityTheory.cond
  rw [integral_smul_measure]

end EisensteinGeneralSetAF76AConsumer
