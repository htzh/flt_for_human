/-
  The absolute Galois group of `ℚ` acts on the algebraic closure `AlgebraicClosure ℚ`:
  the extension `ℚ ⊆ AlgebraicClosure ℚ` is Galois.

  Transcribed verbatim from `Definitions/Def_FieldTheory_RatAlgClosureGalois.lean`
  (pinned `aa2d8b3`, 7 lines).
-/
import Mathlib.Algebra.Algebra.Rat
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.Galois.Basic

instance AlgebraicClosure.Rat.isGalois :
    @IsGalois ℚ _ (AlgebraicClosure ℚ) _ DivisionRing.toRatAlgebra :=
  @IsAlgClosure.isGalois ℚ (AlgebraicClosure ℚ) _ _ (AlgebraicClosure.instAlgebra ℚ) _ _
