/-
  Uniqueness of the additive Haar measure on the adèle ring.

  Two additive Haar measures on `𝔸_F` differ by a positive scalar
  (`exists_smul_eq_of_isAddHaarMeasure_adeleRing`).  Mathlib's `isAddLeftInvariant_eq_smul` proves
  this for a second-countable locally compact additive group; the content here is that the adèle
  ring is second countable, which `NumberField/AdelicLevel/Countability.lean` already establishes
  for the infinite, the finite and the product.  The row is the uniqueness input of the Fourier
  inversion, whose constant is a ratio of Haar measures.

  Transcribed from the pin's proof file (pinned `aa2d8b3`)
  `P2M/Sol/S_NumberField_AdelicFourier_exists_smul_eq_of_isAddHaarMeasure_adeleRing.lean` (the
  countability prelude of that file is the port's own module and is imported, not re-proved).

  spec-pin: P2M/Sol/S_NumberField_AdelicFourier_exists_smul_eq_of_isAddHaarMeasure_adeleRing.lean
-/
import FLTForHuman.NumberTheory.AdelicHaar.Adele
import FLTForHuman.NumberTheory.AdelicLevel.Countability
import Mathlib.MeasureTheory.Measure.Haar.Unique

set_option autoImplicit false

noncomputable section

open NumberField NumberField.AdelicHaar IsDedekindDomain MeasureTheory MeasureTheory.Measure
open scoped NNReal ENNReal NumberField.AdelicCountability

namespace NumberField.AdelicHaar

theorem exists_smul_eq_of_isAddHaarMeasure_adeleRing (F : Type) [Field F] [NumberField F]
    [MeasurableSpace (AdeleRing (𝓞 F) F)] [BorelSpace (AdeleRing (𝓞 F) F)]
    (μ ν : MeasureTheory.Measure (AdeleRing (𝓞 F) F)) [μ.IsAddHaarMeasure] [ν.IsAddHaarMeasure] :
    ∃ c : NNReal, 0 < c ∧ μ = c • ν := by
  have : Countable (𝓞 F) := NumberField.AdelicCountability.instCountableRingOfIntegers F
  have : SecondCountableTopology (AdeleRing (𝓞 F) F) :=
    NumberField.AdelicCountability.instSecondCountableAdeleRing (𝓞 F) F
  exact ⟨addHaarScalarFactor μ ν, addHaarScalarFactor_pos_of_isAddHaarMeasure μ ν,
    isAddLeftInvariant_eq_smul μ ν⟩

end NumberField.AdelicHaar

end
