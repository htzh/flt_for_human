/-
  Consumer zone for `FLTForHuman/NumberTheory/NumberField/DenseRange.lean`.

  The row under test is the general-field strong approximation at one finite place, and it is
  exercised in composition with its `ℚ` twin
  `FLTForHuman/NumberTheory/RatAdele/DenseRange.lean`, never by `#check`:

  * `NumberField.denseRange_algebraMap_add_adeleSingleAt` is instantiated at `K = ℚ`, where its
    image function `qy ↦ algebraMap ℚ 𝔸_ℚ qy.1 + adeleSingleAt ℚ v qy.2` is *the same function* as
    the one in `RatAdele.denseRange_algebraMap_add_adeleSingleAt` — `same_map` is the `funext` +
    `rfl` comparison (`NumberField.RingOfIntegers ℚ` and `RingOfIntegers ℚ` are one constant);
  * the transport along `same_map` is run in both directions: `ratAdele_of_numberField` derives the
    `ℚ` twin's statement from the general headline, `numberField_of_ratAdele` derives the general
    headline's `ℚ` instance from the twin's theorem. Each is thus the other's hypothesis, and the
    zone breaks if either module's image function is respelled;
  * the pair is cashed out in the form the Hecke layer consumes: every neighbourhood of a target
    adele meets the image on the nose (`exists_witness_of_mem_nhds`). The witness is extracted from
    the *twin's* density through `DenseRange.mem_nhds` and read back at the general function's
    spelling, so neither headline alone closes the zone.

  `spec/` is outside every Lake library, so this file is checked by
  `lake env lean spec/NumberFieldSetAF34AConsumer.lean` and never enters the build.
-/
import FLTForHuman.NumberTheory.NumberField.DenseRange
import FLTForHuman.NumberTheory.RatAdele.DenseRange

set_option autoImplicit false

noncomputable section

open IsDedekindDomain NumberField

open scoped Topology

namespace NumberFieldSetAF34AConsumer

variable (v : HeightOneSpectrum (RingOfIntegers ℚ))

/-- The general headline at `K = ℚ`: the image function spelled as in the general statement. -/
theorem general_headline_at_rat :
    DenseRange fun qy : ℚ × v.adicCompletion ℚ =>
      algebraMap ℚ (NumberField.AdeleRing (NumberField.RingOfIntegers ℚ) ℚ) qy.1 +
        NumberField.StandardAddChar.adeleSingleAt ℚ v qy.2 :=
  NumberField.denseRange_algebraMap_add_adeleSingleAt ℚ v

/-- The two headlines are about the same function: the general statement's image at `K = ℚ` and the
`ℚ` twin's image are equal by `funext` and `rfl`. -/
theorem same_map :
    (fun qy : ℚ × v.adicCompletion ℚ =>
        algebraMap ℚ (NumberField.AdeleRing (NumberField.RingOfIntegers ℚ) ℚ) qy.1 +
          NumberField.StandardAddChar.adeleSingleAt ℚ v qy.2) =
      fun qy : ℚ × v.adicCompletion ℚ =>
        algebraMap ℚ (AdeleRing (RingOfIntegers ℚ) ℚ) qy.1 +
          NumberField.StandardAddChar.adeleSingleAt ℚ v qy.2 := by
  funext qy
  rfl

/-- The `ℚ` twin's statement, derived from the general headline through `same_map`. -/
theorem ratAdele_of_numberField :
    DenseRange fun qy : ℚ × v.adicCompletion ℚ =>
      algebraMap ℚ (AdeleRing (RingOfIntegers ℚ) ℚ) qy.1 +
        NumberField.StandardAddChar.adeleSingleAt ℚ v qy.2 :=
  (congrArg DenseRange (same_map v)).mp (general_headline_at_rat v)

/-- Conversely, the general headline's `ℚ` instance follows from the ported `ℚ` twin. -/
theorem numberField_of_ratAdele :
    DenseRange fun qy : ℚ × v.adicCompletion ℚ =>
      algebraMap ℚ (NumberField.AdeleRing (NumberField.RingOfIntegers ℚ) ℚ) qy.1 +
        NumberField.StandardAddChar.adeleSingleAt ℚ v qy.2 :=
  (congrArg DenseRange (same_map v)).mpr (RatAdele.denseRange_algebraMap_add_adeleSingleAt v)

/-- The two dense ranges have the same image. -/
theorem range_eq :
    Set.range (fun qy : ℚ × v.adicCompletion ℚ =>
        algebraMap ℚ (NumberField.AdeleRing (NumberField.RingOfIntegers ℚ) ℚ) qy.1 +
          NumberField.StandardAddChar.adeleSingleAt ℚ v qy.2) =
      Set.range fun qy : ℚ × v.adicCompletion ℚ =>
        algebraMap ℚ (AdeleRing (RingOfIntegers ℚ) ℚ) qy.1 +
          NumberField.StandardAddChar.adeleSingleAt ℚ v qy.2 :=
  congrArg Set.range (same_map v)

/-- Every neighbourhood of a target adele is met on the nose by the image of the general statement:
the witness comes from the `ℚ` twin's density (`DenseRange.mem_nhds`) and is read back at the
general spelling through `same_map`. -/
theorem exists_witness_of_mem_nhds (x : AdeleRing (RingOfIntegers ℚ) ℚ)
    (W : Set (AdeleRing (RingOfIntegers ℚ) ℚ)) (hW : W ∈ 𝓝 x) :
    ∃ qy : ℚ × v.adicCompletion ℚ,
      algebraMap ℚ (NumberField.AdeleRing (NumberField.RingOfIntegers ℚ) ℚ) qy.1 +
        NumberField.StandardAddChar.adeleSingleAt ℚ v qy.2 ∈ W := by
  obtain ⟨qy, hqy⟩ := (RatAdele.denseRange_algebraMap_add_adeleSingleAt v).mem_nhds hW
  exact ⟨qy, (congrFun (same_map v) qy) ▸ hqy⟩

end NumberFieldSetAF34AConsumer
