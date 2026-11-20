/-
  SET-AF90E consumer: the height comparison survives rational left multiplication.

  **The rows.** `FLTForHuman/NumberTheory/AdelicHeight/Compactness.lean` carries
  `exists_forall_mul_adelicHeight_le_adelicHeight_mul_of_isCompact` (the two-sided height
  comparison under right multiplication by a compact set) and
  `adelicHeight_globalPoints_mul_of_apply_one_zero_eq_zero` (invariance of the height under the
  rational points whose lower-left entry vanishes).

  **The reading.** The comparison at `C` is pushed through a rational left factor with vanishing
  lower-left entry: for every `x ∈ C` the height of `γ g x` is the height of `g x`, so the compact-set
  comparison of `g` is the comparison of `γ g`. That is the form the cusp-form estimates use when
  they first move the argument by a rational point.

  `spec/` is outside every Lake library, so this file is checked by
  `lake env lean spec/NumberFieldSetAF90EConsumer.lean` and never enters the build.
-/
import FLTForHuman.NumberTheory.AdelicHeight.Compactness

set_option autoImplicit false

noncomputable section

open MeasureTheory NumberField NumberField.AdelicBox IsDedekindDomain
open AutomorphicForm AutomorphicForm.WindowedSiegel Matrix NumberField.AdelicHeight
open scoped ENNReal BigOperators

namespace NumberFieldSetAF90EConsumer

/-- **The reading.** The height comparison on the compact set `C` is unaffected by a rational left
factor whose lower-left entry is zero. -/
theorem exists_forall_mul_globalPoints_le_of_isCompact
    (F : Type) [Field F] [NumberField F]
    (C : Set (AdelicGL2 (𝓞 F) F)) (hC : IsCompact C)
    (γ : GL (Fin 2) F) (hγ : (γ : Matrix (Fin 2) (Fin 2) F) 1 0 = 0) :
    ∃ κ K : ℝ, 0 < κ ∧ ∀ (g : AdelicGL2 (𝓞 F) F), ∀ x ∈ C,
      κ * adelicHeight F g ≤ adelicHeight F (globalPoints (𝓞 F) F γ * (g * x)) ∧
      adelicHeight F (globalPoints (𝓞 F) F γ * (g * x)) ≤ K * adelicHeight F g := by
  obtain ⟨κ, K, hκ, hcomp⟩ :=
    AdelicHeight.exists_forall_mul_adelicHeight_le_adelicHeight_mul_of_isCompact F C hC
  refine ⟨κ, K, hκ, fun g x hx => ?_⟩
  rw [AdelicHeight.adelicHeight_globalPoints_mul_of_apply_one_zero_eq_zero F γ hγ]
  exact hcomp g x hx

end NumberFieldSetAF90EConsumer
