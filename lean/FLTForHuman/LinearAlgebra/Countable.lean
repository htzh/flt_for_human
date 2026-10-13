/-
  Mathlib supplement: countability of finite modules and of a number field.

  Backported from the pin's `Definitions/Def_Mathlib_LinearAlgebra_Countable.lean`
  (pinned `aa2d8b3`), which mirrors the mathlib path `Mathlib/LinearAlgebra/Countable.lean`;
  it therefore lives at that path under `FLTForHuman/`. In `v4.34.0` the lemma body is
  mathlib's `Finsupp.Countable.of_moduleFinite` (the pin's `_of_module_finite`
  spelling predates the rename), so this file keeps the pin's public name as a thin
  wrapper and adds the number-field instance the pin supplies.
-/
import Mathlib.LinearAlgebra.Countable
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.Data.Rat.Denumerable

set_option autoImplicit false

-- pin: Countable.of_module_finite (Def_Mathlib_LinearAlgebra_Countable.lean:5)
theorem Countable.of_module_finite (R M : Type*) [Semiring R] [Countable R]
    [AddCommMonoid M] [Module R M] [Module.Finite R M] : Countable M :=
  Finsupp.Countable.of_moduleFinite (R := R) (M := M)

-- pin: instCountableOfNumberField (Def_Mathlib_LinearAlgebra_Countable.lean:12)
instance (K : Type*) [Field K] [NumberField K] : Countable K :=
  Countable.of_module_finite ℚ K
