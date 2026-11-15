/-
  Cross-module wire test for the box normalization (`AF76B`).

  A `spec/` probe, not a library module. The whole zone is at the base field `F = ℚ`, where the
  pin's abstract objects have concrete shapes:

  * `𝓞 ℚ = ℤ`, so `adelicBox ℚ` is the unit interval's fundamental domain times the integral
    finite adèles and `disc ℚ = 1`, `nrComplexPlaces ℚ = 0`;
  * `𝓞̂ = integralFiniteAdeles (𝓞 ℚ) ℚ` is the compact open unit ball of the finite adèles, and the
    ball `{y | s * y ∈ 𝓞̂}` of the normalization module at `s = 1` is `𝓞̂` itself
    (`isCompact_setOf_mul_mem_integralFiniteAdeles_rat_one`);
  * the adèles carry the port's `adelicAddHaar` and the finite adèles the `M4aS4` place measure
    `finMeasure` — both additive Haar measures (`instances` supplied locally below), the pair the
    identity is stated for;
  * at `f = g = 1` the pure tensor is the constant `1`, so both integrals are computed by
    `integral_const` to `μ.real univ` (the identity's two sides are then values of the total masses,
    not of an integrand).

  Every zone is a real composition — no `#check` — so deleting the module (or leaving a hole in it)
  breaks this file.
-/
import FLTForHuman.NumberTheory.AdelicBox.Normalization

set_option autoImplicit false

noncomputable section

open MeasureTheory NumberField NumberField.InfinitePlace NumberField.InfiniteAdeleRing
open NumberField.AdelicBox
open IsDedekindDomain
open scoped ENNReal NNReal Classical M4aS4

namespace NumberTheorySetAF76BConsumer

-- the adèles' and the finite adèles' Borel structures (the port spells them as named instances)
attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel
attribute [local instance] M4aS4.finBorel
attribute [local instance] NumberField.AdelicHaar.isAddHaarMeasure_adelicAddHaar

/-! ### `isCompact_setOf_mul_mem_integralFiniteAdeles` at `F = ℚ`, `s = 1` -/

/-- `isCompact_setOf_mul_mem_integralFiniteAdeles` at `F = ℚ` and `s = 1`: the ball of the
normalization module is compact at the unit of `𝓞 ℚ` — it is the integral finite adèles themselves,
whose compactness `AdelicBox` already carries. -/
theorem isCompact_setOf_mul_mem_integralFiniteAdeles_rat_one :
    IsCompact {y : FiniteAdeleRing (𝓞 ℚ) ℚ |
      algebraMap (𝓞 ℚ) (FiniteAdeleRing (𝓞 ℚ) ℚ) 1 * y ∈ integralFiniteAdeles (𝓞 ℚ) ℚ} :=
  isCompact_setOf_mul_mem_integralFiniteAdeles ℚ 1 one_ne_zero

/-! ### The three countability/compactness rows at `F = ℚ` -/

/-- `sigmaCompactSpace_finiteAdeleRing` at `F = ℚ`: the finite adèles of `ℚ` are `σ`-compact. -/
theorem sigmaCompactSpace_finiteAdeleRing_rat :
    SigmaCompactSpace (FiniteAdeleRing (𝓞 ℚ) ℚ) := sigmaCompactSpace_finiteAdeleRing ℚ

/-- `secondCountableTopology_infiniteAdeleRing` at `F = ℚ`: the infinite adèles of `ℚ` are second
countable. -/
theorem secondCountableTopology_infiniteAdeleRing_rat :
    SecondCountableTopology (InfiniteAdeleRing ℚ) := secondCountableTopology_infiniteAdeleRing ℚ

/-- `continuous_ringEquiv_mixedSpace_symm` at `F = ℚ`: the mixed-space transport is continuous in
the inverse direction. -/
theorem continuous_ringEquiv_mixedSpace_symm_rat :
    Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace ℚ).symm :=
  continuous_ringEquiv_mixedSpace_symm ℚ

/-! ### The normalization identity at `F = ℚ`, `f = g = 1`, both integrals computed -/

/-- The headline of the normalization module at `F = ℚ`, `μ = adelicAddHaar`, `ν = finMeasure` and
`f = g = 1`: the pure tensor is the constant `1`, so `integral_const` computes both integrals of the
identity — the archimedean one to `volume.real univ` on the mixed space and the finite one to
`(finMeasure ℚ).real univ` — and the identity reads the corresponding equality of total masses. -/
theorem inv_measure_adelicBox_mul_integral_pureTensor_eq_rat_one :
    ((NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ (adelicBox ℚ)).toReal : ℂ)⁻¹ *
        (((NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ).real Set.univ : ℝ) : ℂ)
      = (((2 : ℝ) ^ nrComplexPlaces ℚ / Real.sqrt |(discr ℚ : ℝ)| : ℝ) : ℂ) *
        ((((volume : Measure (mixedEmbedding.mixedSpace ℚ)).real Set.univ : ℝ) : ℂ) *
          (((M4aS4.finMeasure ℚ (integralFiniteAdeles (𝓞 ℚ) ℚ)).toReal : ℂ)⁻¹ *
            (((M4aS4.finMeasure ℚ).real Set.univ : ℝ) : ℂ))) := by
  have h := NumberField.AdelicBox.inv_measure_adelicBox_mul_integral_pureTensor_eq (F := ℚ)
    (NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ) (M4aS4.finMeasure ℚ)
    (fun _ => 1) (fun _ => 1)
  simpa [integral_const, Measure.real, one_smul, smul_eq_mul, mul_one, MeasureTheory.Measure.real_def]
    using h

end NumberTheorySetAF76BConsumer
