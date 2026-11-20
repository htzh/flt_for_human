/-
  SET-AF90B consumer: rational strong approximation, one level down.

  **The rows.** `FLTForHuman/NumberTheory/AdelicLevel/ArchLevelLattice.lean` carries
  `exists_glFin_globalPoints_mul_mem_finiteLevelOne_rat` (every finite adèle is left-multiplied
  into `finiteLevelOne N` by a rational point), and the port's `AdelicLevel/Level.lean` carries
  `finiteLevelOne_le_finiteLevelZero`.

  **The reading.** The level-one approximation is pushed one level down: the same rational point
  puts `g` into `finiteLevelZero N`, the congruence subgroup the coset/Hecke arguments use (it is
  the level-zero side of the `finiteLevelOne ⊂ finiteLevelZero ⊂ finiteIntegralGL2` chain). This is
  the form in which the level lattice is consumed by the double-coset computations.

  `spec/` is outside every Lake library, so this file is checked by
  `lake env lean spec/NumberFieldSetAF90BConsumer.lean` and never enters the build.
-/
import FLTForHuman.NumberTheory.AdelicLevel.ArchLevelLattice

set_option autoImplicit false

noncomputable section

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm IsDedekindDomain Matrix

namespace NumberFieldSetAF90BConsumer

/-- **The reading.** Rational strong approximation into `finiteLevelOne N`, then the inclusion
into `finiteLevelZero N`: the same rational point serves the level-zero congruence. -/
theorem exists_glFin_globalPoints_mul_mem_finiteLevelZero_rat
    {N : Ideal (𝓞 ℚ)} (hN : N ≠ ⊥)
    (g : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) :
    ∃ γ : GL (Fin 2) ℚ,
      glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ γ) * g ∈ finiteLevelZero (𝓞 ℚ) ℚ N := by
  obtain ⟨γ, hγ⟩ := exists_glFin_globalPoints_mul_mem_finiteLevelOne_rat hN g
  exact ⟨γ, finiteLevelOne_le_finiteLevelZero (𝓞 ℚ) ℚ N hγ⟩

end NumberFieldSetAF90BConsumer
