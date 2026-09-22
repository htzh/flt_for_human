/-
Ported from the FLT project, pinned at `aa2d8b3`:

  Definitions/Def_Mathlib_LinearAlgebra_Countable.lean
  https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_Mathlib_LinearAlgebra_Countable.lean

A finitely generated module over a countable ring is countable; in particular
every number field is countable. The FLT development needs this to build
restricted products (adeles) over countable index sets.

Adaptations for this project:

* Declarations live under `FLTForHuman` rather than the root namespace, so an
  adapted lemma cannot collide with a later mathlib addition of the same name.
  The original FLT names are `Countable.of_module_finite` and the anonymous
  `Countable` instance for `NumberField K`.
* The proof of `exists_fin`-based countability is unchanged; the number-field
  instance is restated with an explicit `Module.Finite` argument so the step
  "a number field is a finite-dimensional `ℚ`-vector space" is visible.
-/
import Mathlib

namespace FLTForHuman

/-- A finitely generated module over a countable ring is countable. -/
theorem countable_of_module_finite (R M : Type*) [Semiring R] [Countable R]
    [AddCommMonoid M] [Module R M] [Module.Finite R M] : Countable M := by
  obtain ⟨n, s, h⟩ := Module.Finite.exists_fin (R := R) (M := M)
  rw [← Set.countable_univ_iff]
  have : Countable (Submodule.span R (Set.range s)) := inferInstance
  rwa [h] at this

/-- A number field is a finite-dimensional `ℚ`-vector space, hence countable. -/
instance (K : Type*) [Field K] [NumberField K] : Countable K :=
  countable_of_module_finite ℚ K

end FLTForHuman
