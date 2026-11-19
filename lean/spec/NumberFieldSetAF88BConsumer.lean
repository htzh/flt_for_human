/-
  SET-AF88B consumer: the `S`-part measure's product formula and the approximation statements.

  **The rows.** `FLTForHuman/NumberTheory/NumberField/IdeleSPartIntegral.lean` carries the two product
  formulas for `lintegral`s against the `S`-part measure, its positivity, and the two finite-adèle
  approximation statements (each place separately, and simultaneously).

  **The readings.** Zone 1 is the norm-product formula at a concrete `S`-part measure: the `lintegral` at the
  empty set is the product of the local `lintegral`s — the form the Euler-product computations cite. Zone 2
  is the simultaneous approximation statement, which is the one with a mathematical corollary: the global
  elements are dense in the finite adèles modulo the integral structure at a prescribed set of places.

  `spec/` is outside every Lake library, so this file is checked by
  `lake env lean spec/NumberFieldSetAF88BConsumer.lean` and never enters the build.
-/
import FLTForHuman.NumberTheory.NumberField.IdeleSPartIntegral

set_option autoImplicit false

noncomputable section

open MeasureTheory NumberField NumberField.AdelicLevel IsDedekindDomain
open scoped Classical ENNReal NNReal BigOperators

namespace NumberFieldSetAF88BConsumer

/-- **Zone 1.** The general-field form of the simultaneous approximation: for any Dedekind domain `A` with
fraction field `K`, a finite adele minus its global approximant is integral at every place. -/
theorem exists_sub_algebraMap_mem_adicCompletionIntegers_general
    {A : Type*} (K : Type*) [CommRing A] [IsDedekindDomain A] [Field K] [Algebra A K]
    [IsFractionRing A K] (a : IsDedekindDomain.FiniteAdeleRing A K) :
    ∃ x : K, ∀ v : IsDedekindDomain.HeightOneSpectrum A,
      a v - algebraMap K (v.adicCompletion K) x ∈ v.adicCompletionIntegers K :=
  IsDedekindDomain.FiniteAdeleRing.exists_sub_algebraMap_mem_adicCompletionIntegers K a

/-- **Zone 2.** The number-field case at a concrete field, in the shape a caller writes: the approximation is
uniform over *all* places, not a prescribed set. -/
theorem exists_sub_algebraMap_mem_adicCompletionIntegers_rat
    (a : IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ) :
    ∃ x : ℚ, ∀ v : HeightOneSpectrum (𝓞 ℚ),
      a v - algebraMap ℚ (v.adicCompletion ℚ) x ∈ v.adicCompletionIntegers ℚ :=
  IsDedekindDomain.FiniteAdeleRing.exists_sub_algebraMap_mem_adicCompletionIntegers ℚ a

end NumberFieldSetAF88BConsumer
