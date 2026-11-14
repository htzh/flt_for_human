/-
Copyright (c) 2026 FLT-for-human contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FLT-for-human contributors
-/
import Mathlib.Analysis.Complex.UpperHalfPlane.MoebiusAction
import Mathlib.NumberTheory.ModularForms.Discriminant
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Basic
import Mathlib.NumberTheory.ModularForms.LevelOne.Basic
import Mathlib.NumberTheory.ModularForms.SlashInvariantForms

/-!
# The level-one `j`-invariant

`j τ = E₄ τ ^ 3 / Δ τ` is the Hauptmodul of the modular group: it is invariant under the
action of `SL(2, ℤ)` on `ℍ` and generates the field of level-one modular functions.

## Main definitions

* `ModularForm.j`: the level-one `j`-invariant `ℍ → ℂ`.

## Main results

* `ModularForm.j_smul`: `j` is invariant under `SL(2, ℤ)`.
* `ModularForm.j_mul_discriminant`: the division-free form `j τ * Δ τ = E₄ τ ^ 3`.
-/

noncomputable section

open Matrix.SpecialLinearGroup UpperHalfPlane

open scoped MatrixGroups

namespace ModularForm

/-- The level-one `j`-invariant `j τ = E₄ τ ^ 3 / Δ τ`. -/
def j : ℍ → ℂ := fun τ => E₄ τ ^ 3 / discriminant τ

/-- The level-one `j`-invariant is invariant under `SL(2, ℤ)`. -/
theorem j_smul (γ : SL(2, ℤ)) (τ : ℍ) : j (γ • τ) = j τ := by
  have hγ : (mapGL ℝ γ : GL (Fin 2) ℝ) ∈ 𝒮ℒ := ⟨γ, rfl⟩
  have hE : E₄ (γ • τ) = denom (mapGL ℝ γ) τ ^ (4 : ℤ) * E₄ τ :=
    SlashInvariantForm.slash_action_eqn'' E₄ hγ τ
  have hΔ : discriminant (γ • τ) = denom (mapGL ℝ γ) τ ^ (12 : ℤ) * discriminant τ := by
    have h := SlashInvariantForm.slash_action_eqn'' CuspForm.discriminant hγ τ
    simp only [CuspForm.coe_discriminant] at h
    exact h
  have hd : denom (mapGL ℝ γ : GL (Fin 2) ℝ) τ ≠ 0 := denom_ne_zero _ _
  rw [j, j, hE, hΔ, mul_pow, ← zpow_natCast, ← zpow_mul]
  norm_num
  first
  | rw [mul_div_mul_left _ _ (zpow_ne_zero 12 hd)]
  | rw [mul_div_mul_left _ _ (pow_ne_zero 12 hd)]

/-- The division-free form of the definition: `j τ * Δ τ = E₄ τ ^ 3`. -/
theorem j_mul_discriminant (τ : ℍ) : j τ * discriminant τ = E₄ τ ^ 3 := by
  rw [j]
  exact div_mul_cancel₀ _ (discriminant_ne_zero τ)

end ModularForm
