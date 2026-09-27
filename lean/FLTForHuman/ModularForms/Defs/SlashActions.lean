/-
  A generic evaluation of the `T`-slash action.

  `slash_T_zpow_apply` computes `(h ∣[k] T ^ b) τ = h (b +ᵥ τ)` for an arbitrary
  `h : ℍ → ℂ`. It is the elementary modular-group computation behind the
  periodicity of a `Γ(N)`-invariant function; mathlib has
  `UpperHalfPlane.modular_T_zpow_smul` but no slash form of it.

  The pin writes it `private` in the `CardC` namespace of
  `P2M/Sol/S_EisensteinSeries_qExpansion_eisensteinG_coeff.lean` (pinned
  `aa2d8b3`); the port promotes it here as shared slash-action vocabulary.
-/
import Mathlib.NumberTheory.ModularForms.SlashActions
import Mathlib.Analysis.Complex.UpperHalfPlane.MoebiusAction
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup

set_option autoImplicit false
set_option linter.style.haveILetI false

open UpperHalfPlane
open scoped MatrixGroups ModularForm UpperHalfPlane

namespace SlashAction

variable {k : ℤ}

/-- The `T ^ b` slash action is translation by `b` on the upper half plane. -/
lemma slash_T_zpow_apply (h : ℍ → ℂ) (b : ℤ) (τ : ℍ) :
    (h ∣[k] (ModularGroup.T ^ b)) τ = h (((b : ℝ)) +ᵥ τ) := by
  rw [ModularForm.SL_slash_apply, ModularGroup.denom_apply, UpperHalfPlane.modular_T_zpow_smul]
  simp [ModularGroup.coe_T_zpow]

end SlashAction
