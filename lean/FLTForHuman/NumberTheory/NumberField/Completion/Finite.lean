/-
  Finiteness and compactness of the completed integers at a finite place.

  For a number field `K` and a height-one prime `v`: the residue field of the
  completed integers `𝒪_v` is finite, `𝒪_v` is compact and open in `K_v`, and
  (for `K = ℚ`) `K_v` is locally compact. These are the local inputs to the adelic
  topology and to the compactness of `GL₂(𝔸_K)`'s level subgroups.

  Transcribed whole from `Definitions/Def_NumberField_Completion_Finite.lean`
  (pinned `aa2d8b3`). This is its natural home, at the mathlib path
  `Mathlib/NumberTheory/NumberField/Completion/Finite.lean` under `FLTForHuman/`;
  the instances themselves are the port's `NumberField.AdelicHaar` ones (which build
  `ProperSpace` from mathlib's normed-field structure rather than the pin's
  `Valued.WithZeroMulInt` shim), and the pin's public names are exposed here so a
  consumer written against the pin's `attribute [-instance]` lines finds them.
-/
import FLTForHuman.NumberTheory.AdelicHaar.Local
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace

set_option autoImplicit false

noncomputable section

open IsDedekindDomain IsLocalRing NumberField MeasureTheory
open scoped Valued

namespace NumberField

variable (K : Type*) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

-- pin: instFiniteResidueFieldAdicCompletionIntegers (Def_NumberField_Completion_Finite.lean:16)
instance instFiniteResidueFieldAdicCompletionIntegers :
    Finite (ResidueField (v.adicCompletionIntegers K)) :=
  AdelicHaar.finite_residueField_adicCompletionIntegers (𝓞 K) K v

-- pin: instCompactSpaceAdicCompletionIntegers (Def_NumberField_Completion_Finite.lean:26)
instance instCompactSpaceAdicCompletionIntegers : CompactSpace (v.adicCompletionIntegers K) :=
  AdelicHaar.compactSpace_adicCompletionIntegers (𝓞 K) K v

-- pin: isCompactAdicCompletionIntegers (Def_NumberField_Completion_Finite.lean:30)
lemma isCompactAdicCompletionIntegers :
    IsCompact (v.adicCompletionIntegers K : Set (v.adicCompletion K)) := by
  rw [isCompact_iff_compactSpace]
  exact instCompactSpaceAdicCompletionIntegers K v

-- pin: isOpenAdicCompletionIntegers (Def_NumberField_Completion_Finite.lean:35)
lemma isOpenAdicCompletionIntegers :
    IsOpen (v.adicCompletionIntegers K : Set (v.adicCompletion K)) :=
  Valued.isOpen_valuationSubring _

end NumberField

namespace Rat.adicCompletion

-- pin: locallyCompactSpace (Def_NumberField_Completion_Finite.lean:39)
instance locallyCompactSpace (v : HeightOneSpectrum (𝓞 ℚ)) :
    LocallyCompactSpace (v.adicCompletion ℚ) :=
  inferInstance

end Rat.adicCompletion

end
