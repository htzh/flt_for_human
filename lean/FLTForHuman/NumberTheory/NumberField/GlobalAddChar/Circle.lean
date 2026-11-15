/-
  A global additive character takes values on the unit circle.

  `AutomorphicForm.IsGlobalAddChar` is the pin's predicate on a continuous nontrivial additive
  character of `𝔸_F` that is trivial on the principal adèles.  This module proves that such a
  character is bounded (the fundamental box `adelicBox F` plus principal invariance bounds it on a
  compact set, `exists_norm_apply_le_of_isGlobalAddChar`) and hence — by the power argument that
  forbids a value of modulus `> 1` — takes values in the unit circle
  (`norm_apply_eq_one_of_isGlobalAddChar`).  Consequently it is the composition of a character with
  values in `Circle` with the inclusion `Circle → ℂ` (`toCircleAddChar`,
  `exists_compAddChar_eq_of_isGlobalAddChar`), which is what lets the Fourier theory of
  `NumberField/AdelicFourier` use the compact-group results on `Circle`.

  Transcribed from the pin's proof file (pinned `aa2d8b3`)
  `P2M/Sol/S_NumberField_AdelicFourier_norm_apply_eq_one_of_isGlobalAddChar.lean`, whose namespace
  `NumberField.AdelicFourier` is renamed to `AutomorphicForm` — the subject is the character
  predicate `AutomorphicForm.IsGlobalAddChar`, not the Fourier transform.

  spec-pin: P2M/Sol/S_NumberField_AdelicFourier_norm_apply_eq_one_of_isGlobalAddChar.lean
-/
import FLTForHuman.NumberTheory.NumberField.GlobalAddChar
import FLTForHuman.NumberTheory.AdelicBox
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Complex.Circle

set_option autoImplicit false

noncomputable section

open NumberField NumberField.AdelicBox IsDedekindDomain MeasureTheory Filter
open scoped Classical NNReal ENNReal

namespace AutomorphicForm

variable (F : Type) [Field F] [NumberField F]

local notation "𝔸" => AdeleRing (𝓞 F) F

local notation "ι" => algebraMap F (AdeleRing (𝓞 F) F)

theorem exists_norm_apply_le_of_isGlobalAddChar {ψ : AddChar 𝔸 ℂ} (hψ : IsGlobalAddChar F ψ) :
    ∃ M : ℝ, ∀ x : 𝔸, ‖ψ x‖ ≤ M := by
  obtain ⟨C, hC, hsub⟩ := AdelicBox.exists_isCompact_adelicBox_subset F
  obtain ⟨M, hM⟩ := hC.exists_bound_of_continuousOn hψ.continuous.continuousOn
  refine ⟨M, fun x => ?_⟩
  obtain ⟨k, hk⟩ := (AdelicBox.existsUnique_algebraMap_add_mem_adelicBox F x).exists
  have hkx : ψ (ι k + x) = ψ x := by
    rw [AddChar.map_add_eq_mul, hψ.principalInvariant k, one_mul]
  rw [← hkx]
  exact hM _ (hsub hk)

theorem norm_apply_le_one_of_bounded {ψ : AddChar 𝔸 ℂ} {M : ℝ} (hM : ∀ x : 𝔸, ‖ψ x‖ ≤ M)
    (x : 𝔸) : ‖ψ x‖ ≤ 1 := by
  by_contra h
  have h1 : 1 < ‖ψ x‖ := lt_of_not_ge h
  have hpow : ∀ n : ℕ, ‖ψ x‖ ^ n ≤ M := fun n => by
    rw [← norm_pow, ← AddChar.map_nsmul_eq_pow]
    exact hM _
  obtain ⟨n, hn⟩ := ((tendsto_pow_atTop_atTop_of_one_lt h1).eventually (eventually_gt_atTop M)).exists
  exact absurd (hpow n) (not_le.mpr hn)

theorem norm_apply_eq_one_of_isGlobalAddChar {ψ : AddChar 𝔸 ℂ} (hψ : IsGlobalAddChar F ψ) (x : 𝔸) :
    ‖ψ x‖ = 1 := by
  obtain ⟨M, hM⟩ := exists_norm_apply_le_of_isGlobalAddChar F hψ
  refine le_antisymm (norm_apply_le_one_of_bounded F hM x) ?_
  have hneg : ‖ψ (-x)‖ ≤ 1 := norm_apply_le_one_of_bounded F hM (-x)
  have hprod : ‖ψ (-x)‖ * ‖ψ x‖ = 1 := by
    rw [← norm_mul, ← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one, norm_one]
  calc (1 : ℝ) = ‖ψ (-x)‖ * ‖ψ x‖ := hprod.symm
    _ ≤ 1 * ‖ψ x‖ := mul_le_mul_of_nonneg_right hneg (norm_nonneg _)
    _ = ‖ψ x‖ := one_mul _

def toCircleAddChar {ψ : AddChar 𝔸 ℂ} (hψ : IsGlobalAddChar F ψ) : AddChar 𝔸 Circle where
  toFun x := ⟨ψ x, mem_sphere_zero_iff_norm.2 (norm_apply_eq_one_of_isGlobalAddChar F hψ x)⟩
  map_zero_eq_one' := by
    ext
    simp only [AddChar.map_zero_eq_one]
    rfl
  map_add_eq_mul' a b := by
    ext
    simp only [AddChar.map_add_eq_mul]
    rfl

theorem coe_toCircleAddChar_apply {ψ : AddChar 𝔸 ℂ} (hψ : IsGlobalAddChar F ψ) (x : 𝔸) :
    ((toCircleAddChar F hψ x : Circle) : ℂ) = ψ x := rfl

theorem exists_compAddChar_eq_of_isGlobalAddChar {ψ : AddChar 𝔸 ℂ} (hψ : IsGlobalAddChar F ψ) :
    ∃ e : AddChar 𝔸 Circle, Circle.coeHom.compAddChar e = ψ :=
  ⟨toCircleAddChar F hψ, by ext x; rfl⟩

end AutomorphicForm

end
