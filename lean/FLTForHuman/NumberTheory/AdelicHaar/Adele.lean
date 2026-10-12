/-
  The adele ring `𝔸_K`: Hausdorff topology, Borel structure and additive Haar measure.

  `𝔸_K = K_∞ × 𝔸_K^fin` inherits the product topology, which is Hausdorff and
  locally compact (the finite part because each `𝒪_v` is compact); the Borel
  σ-algebra `adeleBorel` and the additive Haar measure `adelicAddHaar` are the
  measure theory that every adelic integral is taken against.

  Transcribed verbatim from `Definitions/Def_NumberField_AdelicHaar.lean:118–157`
  (the pin's `Adele` section, pinned `aa2d8b3`), the second of the pin node's
  three role modules. It carries the port's former `Topology.lean` instances,
  which were exactly this section's `t2Space_*` rows.
-/
import FLTForHuman.NumberTheory.AdelicHaar.Local

set_option autoImplicit false

-- The pin's `letI`/`haveI` walls are load-bearing: they feed instance search in the `exact`s.
set_option linter.style.haveILetI false

open IsDedekindDomain NumberField MeasureTheory
open scoped RestrictedProduct Topology

noncomputable section

namespace NumberField.AdelicHaar

section Adele

variable (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K]

instance t2Space_finiteAdeleRing : T2Space (FiniteAdeleRing R K) :=
  inferInstanceAs (T2Space (Πʳ v : HeightOneSpectrum R, [v.adicCompletion K, v.adicCompletionIntegers K]))

instance t2Space_infiniteAdeleRing : T2Space (InfiniteAdeleRing K) :=
  inferInstanceAs (T2Space ((v : InfinitePlace K) → v.Completion))

instance t2Space_adeleRing : T2Space (AdeleRing R K) :=
  inferInstanceAs (T2Space (InfiniteAdeleRing K × FiniteAdeleRing R K))

@[reducible] def adeleBorel : MeasurableSpace (AdeleRing R K) := borel _

theorem borelSpace_adeleBorel : @BorelSpace (AdeleRing R K) _ (adeleBorel R K) :=
  @BorelSpace.mk _ _ (adeleBorel R K) rfl

variable [Module.Free ℤ R] [Module.Finite ℤ R]

instance locallyCompactSpace_finiteAdeleRing : LocallyCompactSpace (FiniteAdeleRing R K) :=
  inferInstanceAs (LocallyCompactSpace
    (Πʳ v : HeightOneSpectrum R, [v.adicCompletion K, v.adicCompletionIntegers K]))

instance locallyCompactSpace_adeleRing [NumberField K] : LocallyCompactSpace (AdeleRing R K) :=
  inferInstanceAs (LocallyCompactSpace (InfiniteAdeleRing K × FiniteAdeleRing R K))

def adelicAddHaar [NumberField K] : @Measure (AdeleRing R K) (adeleBorel R K) := by
  letI := adeleBorel R K
  haveI := borelSpace_adeleBorel R K
  exact Measure.addHaar

theorem isAddHaarMeasure_adelicAddHaar [NumberField K] :
    @Measure.IsAddHaarMeasure (AdeleRing R K) _ _ (adeleBorel R K) (adelicAddHaar R K) := by
  letI := adeleBorel R K
  haveI := borelSpace_adeleBorel R K
  exact Measure.isAddHaarMeasure_addHaarMeasure _

end Adele

end NumberField.AdelicHaar

end
