/-
  The degree-one asymptotic theorem `FrobeniusDensity.degOneAsymptotic`, the
  S7-II headline: `DegOneAsymptotic L` for a Galois number field `L` follows from
  the summability of the degree-one terms and the log-pole asymptotic, applied to
  the fixed field of each subgroup.

  This module is deliberately separate from the D1 definition module
  `FrobeniusDensity/DegOneAsymptotic.lean`: it imports that definition and the
  analytic chain in `DegOneSumAsymptotic.lean`.

  Transcribed from the pinned FLT solution file (`aa2d8b3`,
  `P2M/Sol/S_FrobeniusDensity_degOneAsymptotic.lean`).
-/
import FLTForHuman.NumberTheory.FrobeniusDensity.DegOneAsymptotic
import FLTForHuman.NumberTheory.FrobeniusDensity.DegOneSumAsymptotic

set_option autoImplicit false

open NumberField

namespace FrobeniusDensity

theorem degOneAsymptotic (L : Type*) [Field L] [NumberField L] [IsGalois ℚ L] :
    FrobeniusDensity.DegOneAsymptotic L := fun H S₀ =>
  ⟨fun _ hs => FrobeniusDensity.summable_degOne_term
      (FixedPoints.intermediateField H : IntermediateField ℚ L) S₀ hs,
    FrobeniusDensity.degOneSum_add_log_isBigO
      (FixedPoints.intermediateField H : IntermediateField ℚ L) S₀⟩

end FrobeniusDensity
