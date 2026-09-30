/-
  The Frobenius-density statement `FrobeniusDensity.statement`: every conjugacy
  condition on `Gal(L/ℚ)` is realised by a prime outside any finite set `S`.

  This is the unconditional form, obtained from
  `statement_of_degOneAsymptotic` applied to the S7-II headline
  `FrobeniusDensity.degOneAsymptotic`.

  Transcribed from the pinned FLT solution file (`aa2d8b3`,
  `P2M/Sol/S_FrobeniusDensity_statement.lean`, 12 lines). The mathematics is
  math/019 §4.
-/
import FLTForHuman.NumberTheory.FrobeniusDensity.StatementOfDegOneAsymptotic
import FLTForHuman.NumberTheory.FrobeniusDensity.DegOneAsymptoticProof

set_option autoImplicit false

open NumberField

namespace FrobeniusDensity

theorem statement (L : Type*) [Field L] [NumberField L] [IsGalois ℚ L] :
    FrobeniusDensity.Statement L :=
  FrobeniusDensity.statement_of_degOneAsymptotic L (FrobeniusDensity.degOneAsymptotic L)

end FrobeniusDensity
