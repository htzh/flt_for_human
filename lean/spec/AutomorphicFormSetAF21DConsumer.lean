/-
  Cross-module wire test for SET-AF21D (the two rational quotient integrals agree after summing
  over the units).

  A `spec/` probe, not a library module. **One zone**, and it reads all four conjuncts of
  `AutomorphicForm.integral_rationalTorusUnipotentQuotient_tsum_units_eq_integral_rationalCentreUnipotentQuotient`
  at the one concrete weight for which the hypotheses are free: `k ≡ 0`.

  Why `k ≡ 0` and not `k ≡ 1`: `hfin` bounds `∫⁻ g in 𝓕B, ∑' a : Fˣ, ‖k (diagOne a · g)‖ₑ`, and for
  `k ≡ 1` the inner sum is `∑' a : Fˣ, 1`, which is `⊤` because `Fˣ` is infinite. The zero weight
  is the only constant one that satisfies the hypothesis; the conclusion below is stated in the
  *headline's* own three conjuncts (the two `Integrable` statements and the composed identity
  `h3.trans h4`, the torus-quotient integral equals the centre-quotient one, with the integral over
  `𝓕B` cancelled), so it is proved by reading the headline and dies if either identity, either
  integrability claim, or the order of the conjuncts changes.

  It imports only the module it composes.
-/
import FLTForHuman.AutomorphicForm.Adelic.RationalUnipotentQuotientIntegral

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicBox NumberField.AdelicLevel
open AutomorphicForm
open scoped ENNReal

noncomputable section

namespace SetAF21DQuotientIntegralConsumer

variable (F : Type) [Field F] [NumberField F]

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel

/-- **Zone A — the headline at `k ≡ 0`.** With the zero weight every hypothesis of the headline is
discharged (`hfin` is `∫⁻ g in 𝓕B, ∑' a, ‖0‖ₑ = 0 < ⊤`), and the conclusion is the headline's own
first three conjuncts at that weight: the two integrability statements and the composed identity
between the two quotient measures. -/
theorem quotient_integrals_agree_at_zero
    (𝓕B : Set (AdelicGL2 (𝓞 F) F))
    (h𝓕B : IsFundamentalDomain ((borelSubgroup F).map (globalPoints (𝓞 F) F)) 𝓕B
      (adelicGLHaar (Fin 2) (𝓞 F) F)) :
    Integrable (fun _ : RationalCentreUnipotentQuotient F => (0 : ℂ))
        (rationalCentreUnipotentQuotientMeasure F) ∧
      Integrable (fun _ : RationalTorusUnipotentQuotient F => ∑' _ : Fˣ, (0 : ℂ))
        (rationalTorusUnipotentQuotientMeasure F) ∧
      (∫ _ : RationalTorusUnipotentQuotient F, ∑' _ : Fˣ, (0 : ℂ)
          ∂(rationalTorusUnipotentQuotientMeasure F)) =
        ∫ _ : RationalCentreUnipotentQuotient F, (0 : ℂ)
          ∂(rationalCentreUnipotentQuotientMeasure F) := by
  have hfin : ∫⁻ g in 𝓕B, ∑' a : Fˣ, ‖(fun _ : AdelicGL2 (𝓞 F) F => (0 : ℂ))
      (globalPoints (𝓞 F) F (diagOne a) * g)‖ₑ ∂(adelicGLHaar (Fin 2) (𝓞 F) F) < ∞ := by
    simp
  obtain ⟨h1, h2, h3, h4⟩ :=
    integral_rationalTorusUnipotentQuotient_tsum_units_eq_integral_rationalCentreUnipotentQuotient F
      𝓕B h𝓕B (fun _ => (0 : ℂ)) measurable_const (fun _ _ _ => rfl) hfin
  exact ⟨h1, h2, h3.trans h4⟩

end SetAF21DQuotientIntegralConsumer

end
