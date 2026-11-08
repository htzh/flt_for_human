/-
  Consumer zone for `FLTForHuman/AutomorphicForm/Adelic/BorelHaarDisintegration.lean` (order AF40B).

  A `spec/` probe, not a library module: it *consumes* the headline in composition, never by
  `#check`.

  The headline is an existential: some `c ∈ (0, ∞)` such that for **every** measurable
  `F : GL₂(𝔸_K) → ℝ≥0∞` the `μB`-integral of `F` over the Borel equals `c` times the iterated
  coordinate integral `∫⁻ x ∫⁻ u ∫⁻ t, F (n(x) · z(u) · diag(t)) · ‖t‖⁻¹` of the pulled-back `F`.
  Because the statement is uniform in `F`, it can be *read at an indicator*, and that is what the
  zones below do:

  * **Zone 1** is the headline at its own hypotheses, written through the abbreviation
    `coordIntegral` for the iterated integral of the statement — the shape every later zone uses.

  * **Zone 2** instantiates `F = Set.indicator U 1` for a measurable set `U` of matrices. The left
    side collapses (`lintegral_indicator_one`) to the `μB`-mass of the Borel points whose underlying
    matrix lies in `U`, so the headline becomes a statement about measures of *sets*: the Borel mass
    of `U` is `c` times the integral of `‖t‖⁻¹` over the coordinate triple whose Borel point lands in
    `U`.

  * **Zone 3** takes `U = Set.univ`: with `Set.indicator_univ` the same statement is the total mass
    `μB univ = c · ∫⁻ x ∫⁻ u ∫⁻ t, ‖t‖⁻¹`, i.e. the measure of the whole Borel in terms of the
    additive Haar on `𝔸_K`, the idèle Haar twice, and the Jacobian `‖t‖⁻¹`.

  * **Zone 4** is the vanishing criterion: a measurable set of matrices whose coordinate integral of
    `‖t‖⁻¹` vanishes carries no `μB`-mass at all. This is where the headline's `c ≠ 0` is used — the
    constant is *not* allowed to absorb a null set, so the `‖t‖⁻¹`-integral is a faithful density
    for every left-invariant `μB`.

  `spec/` is outside every Lake library, so this file is checked by
  `lake env lean spec/AutomorphicFormSetAF40BConsumer.lean` and never enters the build.
-/
import FLTForHuman.AutomorphicForm.Adelic.BorelHaarDisintegration

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicHaar IsDedekindDomain
open AutomorphicForm
open scoped ENNReal NNReal

noncomputable section

namespace AutomorphicFormSetAF40BConsumer

-- The pin's local instance wall, as in the module and in its `S_` file: the statements' iterated
-- integrals are taken against `adelicAddHaar` and `idelicHaar`, so the ambient instances must be the
-- measurable spaces those measures are pinned to.
attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel
  NumberField.Idele.ideleBorel NumberField.Idele.borelSpace_ideleBorel

variable (K : Type) [Field K] [NumberField K]

/-- The underlying matrix of a point of the Borel — the map the headline integrates `F` along. -/
abbrev borelVal : adelicBorel (𝓞 K) K → AdelicGL2 (𝓞 K) K := Subtype.val

/-- The iterated coordinate integral of the headline: additive Haar on `𝔸_K`, the idèle Haar twice,
and the Jacobian `‖t‖⁻¹`. This is the statement's right-hand factor, written once. -/
abbrev coordIntegral (F : AdelicGL2 (𝓞 K) K → ℝ≥0∞) : ℝ≥0∞ :=
  ∫⁻ x, ∫⁻ u, ∫⁻ t,
      F (unipotentGL2 x * centralScalar (𝓞 K) K u * diagOne t) *
        ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm K t)⁻¹)
    ∂(NumberField.Idele.idelicHaar K) ∂(NumberField.Idele.idelicHaar K) ∂(adelicAddHaar (𝓞 K) K)

/-- **Zone 1.** The headline at its own hypotheses, with the coordinate integral abbreviated. -/
theorem exists_borel_eq_mul_coordIntegral
    (μB : Measure (adelicBorel (𝓞 K) K)) [μB.IsMulLeftInvariant] [IsFiniteMeasureOnCompacts μB]
    [μB.IsOpenPosMeasure] :
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ∞ ∧
      ∀ F : AdelicGL2 (𝓞 K) K → ℝ≥0∞, Measurable F →
        ∫⁻ b, F (borelVal K b) ∂μB = c * coordIntegral K F :=
  exists_lintegral_adelicBorel_eq_mul_lintegral_coord_of_isMulLeftInvariant K μB

/-- **Zone 2.** The headline read at the indicator of a measurable set of matrices: the `μB`-mass of
the Borel points over `U` is `c` times the coordinate integral of `U`'s indicator. -/
theorem exists_borelMeasure_preimage_eq_mul_coordIntegral_indicator
    (μB : Measure (adelicBorel (𝓞 K) K)) [μB.IsMulLeftInvariant] [IsFiniteMeasureOnCompacts μB]
    [μB.IsOpenPosMeasure] (U : Set (AdelicGL2 (𝓞 K) K)) (hU : MeasurableSet U) :
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ∞ ∧
      μB ((borelVal K) ⁻¹' U) = c * coordIntegral K (Set.indicator U 1) := by
  obtain ⟨c, hc0, hctop, hF⟩ := exists_borel_eq_mul_coordIntegral K μB
  refine ⟨c, hc0, hctop, ?_⟩
  rw [← hF (Set.indicator U 1) (measurable_one.indicator hU)]
  rw [show (fun b : adelicBorel (𝓞 K) K => Set.indicator U 1 (borelVal K b))
      = Set.indicator ((borelVal K) ⁻¹' U) 1 from rfl,
    lintegral_indicator_one (hU.preimage measurable_subtype_coe)]

/-- **Zone 3.** At `U = Set.univ`: the total mass of the Borel is `c` times the iterated integral of
the Jacobian `‖t‖⁻¹` alone. -/
theorem exists_borelMeasure_univ_eq_mul_coordIntegral_one
    (μB : Measure (adelicBorel (𝓞 K) K)) [μB.IsMulLeftInvariant] [IsFiniteMeasureOnCompacts μB]
    [μB.IsOpenPosMeasure] :
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ∞ ∧
      μB Set.univ = c * coordIntegral K (fun _ => 1) := by
  obtain ⟨c, hc0, hctop, hU⟩ :=
    exists_borelMeasure_preimage_eq_mul_coordIntegral_indicator K μB Set.univ MeasurableSet.univ
  rw [Set.preimage_univ] at hU
  refine ⟨c, hc0, hctop, ?_⟩
  rw [hU, Set.indicator_univ]
  rfl

/-- **Zone 4.** The vanishing criterion: a measurable set of matrices whose coordinate integral of
`‖t‖⁻¹` vanishes carries no `μB`-mass — the headline's `c ≠ 0` forbids a null set from absorbing the
constant. -/
theorem borelMeasure_preimage_eq_zero_of_coordIntegral_indicator_eq_zero
    (μB : Measure (adelicBorel (𝓞 K) K)) [μB.IsMulLeftInvariant] [IsFiniteMeasureOnCompacts μB]
    [μB.IsOpenPosMeasure] (U : Set (AdelicGL2 (𝓞 K) K)) (hU : MeasurableSet U)
    (hzero : coordIntegral K (Set.indicator U 1) = 0) :
    μB ((borelVal K) ⁻¹' U) = 0 := by
  obtain ⟨c, -, -, h⟩ :=
    exists_borelMeasure_preimage_eq_mul_coordIntegral_indicator K μB U hU
  rw [h, hzero, mul_zero]

end AutomorphicFormSetAF40BConsumer
