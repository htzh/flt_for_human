/-
  SET-AF62A consumer: the adelic box's periodic `lintegral` and its conditional integral.

  **The zone.** Two rows, hence two compositions, read off the one module of the set,
  `FLTForHuman/NumberTheory/AdelicBoxPeriodicIntegral.lean`:

  * `NumberField.AdelicBox.setLIntegral_adelicBox_comp_mul_add_eq_of_periodic`;
  * `NumberField.AdelicBox.integral_cond_adelicBox_comp_mul_algebraMap`.

  **The readings.**

  * Zone A. The periodic headline produces, for a function `h` periodic along the rational adeles
    (`hper`) and any principal scaling `a : Fˣ`, any additive shift `u₀`, the identity of the
    `lintegral` over the box of `u ↦ h (algebraMap F a * u + u₀)` with the `lintegral` of `h`
    itself. The consumer *executes* the equality at two independent data `(a, u₀)` and `(b, v₀)`
    and chains the two, which is the shape the production-pin integrals use: the box average of a
    periodic function does not see the scaling or the shift at all.
  * Zone B. The conditional headline produces the same statement for the *conditional* integral
    against `adelicBox F` of a function invariant under the principal translations — the measure
    `ProbabilityTheory.cond (adelicAddHaar …) (adelicBox F)` that every `productionPins*`
    construction integrates against. The consumer *executes* it at two nonzero scalings `a`, `b`
    and chains, so the conditional integral of `f` under `x ↦ a * x` is the same whichever
    `a ≠ 0` is used.

  The periodicity/invariance hypotheses (`hper`, `hf`) are properties of an arbitrary periodic
  function and cannot be instantiated concretely, so they enter in hypothesis form, which is the
  legitimate reading for these rows.

  This module is outside every library: it is a spec-side composition check, not part of the
  port's import graph.
-/
import FLTForHuman.NumberTheory.AdelicBoxPeriodicIntegral

set_option autoImplicit false

noncomputable section

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicBox
open scoped ENNReal

attribute [local instance] NumberField.AdelicHaar.adeleBorel
  NumberField.AdelicHaar.borelSpace_adeleBorel

namespace SetAF62AConsumer

/-! ### Zone A: the periodic `lintegral` over the box, at two data -/

section zoneA

variable (F : Type) [Field F] [NumberField F]

/-- **Zone A.** Two executions of the periodic headline, chained: the `lintegral` over the box of
`h` composed with the principal scaling `a` and the shift `u₀` equals the same `lintegral` for
`b`, `v₀` — the box is a fundamental domain for the rational adeles' action, so both are the
`lintegral` of `h` over the box. -/
theorem consumer_zoneA_two_scalings
    (h : AdeleRing (𝓞 F) F → ℝ≥0∞) (hh : Measurable h)
    (hper : ∀ (β : F) (u : AdeleRing (𝓞 F) F),
      h (algebraMap F (AdeleRing (𝓞 F) F) β + u) = h u)
    (a b : Fˣ) (u₀ v₀ : AdeleRing (𝓞 F) F) :
    ∫⁻ u in adelicBox F, h (algebraMap F (AdeleRing (𝓞 F) F) a * u + u₀)
        ∂(adelicAddHaar (𝓞 F) F)
      = ∫⁻ u in adelicBox F, h (algebraMap F (AdeleRing (𝓞 F) F) b * u + v₀)
        ∂(adelicAddHaar (𝓞 F) F) := by
  rw [NumberField.AdelicBox.setLIntegral_adelicBox_comp_mul_add_eq_of_periodic F h hh hper a u₀,
    NumberField.AdelicBox.setLIntegral_adelicBox_comp_mul_add_eq_of_periodic F h hh hper b v₀]

/-- **Zone A'.** The periodic headline read against the trivial data: scaling by `1 : Fˣ` and
shifting by `0` leaves the box `lintegral` of `h` unchanged. -/
theorem consumer_zoneA_identity_data
    (h : AdeleRing (𝓞 F) F → ℝ≥0∞) (hh : Measurable h)
    (hper : ∀ (β : F) (u : AdeleRing (𝓞 F) F),
      h (algebraMap F (AdeleRing (𝓞 F) F) β + u) = h u) :
    ∫⁻ u in adelicBox F, h (algebraMap F (AdeleRing (𝓞 F) F) (1 : Fˣ) * u + 0)
        ∂(adelicAddHaar (𝓞 F) F)
      = ∫⁻ u in adelicBox F, h u ∂(adelicAddHaar (𝓞 F) F) :=
  NumberField.AdelicBox.setLIntegral_adelicBox_comp_mul_add_eq_of_periodic F h hh hper 1 0

end zoneA

/-! ### Zone B: the conditional integral along `K → 𝔸`, at two scalings -/

section zoneB

variable (F : Type) [Field F] [NumberField F]
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Zone B.** Two executions of the conditional headline, chained: for a function invariant
under the principal translations, the conditional integral against `adelicBox F` of
`x ↦ f (algebraMap F a * x)` is independent of the nonzero scaling `a`. -/
theorem consumer_zoneB_two_scalings
    {f : AdeleRing (𝓞 F) F → E}
    (hf : ∀ (k : F) (x : AdeleRing (𝓞 F) F),
      f (algebraMap F (AdeleRing (𝓞 F) F) k + x) = f x)
    (a b : F) (ha : a ≠ 0) (hb : b ≠ 0) :
    ∫ x, f (algebraMap F (AdeleRing (𝓞 F) F) a * x)
        ∂(ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (adelicBox F))
      = ∫ x, f (algebraMap F (AdeleRing (𝓞 F) F) b * x)
        ∂(ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (adelicBox F)) := by
  rw [NumberField.AdelicBox.integral_cond_adelicBox_comp_mul_algebraMap F hf a ha,
    NumberField.AdelicBox.integral_cond_adelicBox_comp_mul_algebraMap F hf b hb]

/-- **Zone B'.** The conditional headline at `a = 1`, read back against the unconditioned data:
scaling by the identity is the conditional integral of `f` itself. -/
theorem consumer_zoneB_identity_scaling
    {f : AdeleRing (𝓞 F) F → E}
    (hf : ∀ (k : F) (x : AdeleRing (𝓞 F) F),
      f (algebraMap F (AdeleRing (𝓞 F) F) k + x) = f x) :
    ∫ x, f (algebraMap F (AdeleRing (𝓞 F) F) (1 : F) * x)
        ∂(ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (adelicBox F))
      = ∫ x, f x ∂(ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (adelicBox F)) :=
  NumberField.AdelicBox.integral_cond_adelicBox_comp_mul_algebraMap F hf 1 one_ne_zero

end zoneB

end SetAF62AConsumer
