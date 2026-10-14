/-
  The `GL₂` idele-norm headlines: determinant-norm slabs and compact subgroups.

  Two successors of the landed `continuous_ideleNorm_det`
  (`FLTForHuman/NumberTheory/NumberField/TateGlobalContinuousIdeleNorm.lean`):

  * `NumberField.TateGlobal.measurableSet_setOf_ideleNorm_det_mem_Icc` — the
    determinant-norm slab `{g | |det g| ∈ [d₁, d₂]}` is Borel for `glBorel`;
  * `NumberField.TateGlobal.ideleNorm_det_eq_one_of_isCompact_of_mem` — every element of a
    compact subgroup of `GL₂(𝔸_F)` has determinant of idelic norm `1`, because a compact
    subgroup's height is bounded above and below along powers.

  Each statement is the pin's `Theorems/` wrapper verbatim:
  https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/Theorems/Thm_NumberField_TateGlobal_measurableSet_setOf_ideleNorm_det_mem_Icc.lean
  https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/Theorems/Thm_NumberField_TateGlobal_ideleNorm_det_eq_one_of_isCompact_of_mem.lean
  and each proof is the pin's `P2M/Sol/S_NumberField_TateGlobal_{measurableSet_setOf_ideleNorm_det_mem_Icc,
  ideleNorm_det_eq_one_of_isCompact_of_mem}.lean` of the same pin.
-/
import FLTForHuman.NumberTheory.NumberField.TateGlobalContinuousIdeleNorm
import FLTForHuman.NumberTheory.NumberField.TateGlobal.Defs
import FLTForHuman.NumberTheory.AdelicHaar.GeneralLinear

set_option autoImplicit false

open NumberField AutomorphicForm

namespace NumberField
namespace TateGlobal

-- pin: measurableSet_setOf_ideleNorm_det_mem_Icc (S_NumberField_TateGlobal_measurableSet_setOf_ideleNorm_det_mem_Icc.lean:18)
-- The two local instances are load-bearing: the statement's `glBorel` measurable space
-- needs its `BorelSpace` companion for `IsClosed.preimage`. Narrow suppression of the
-- `haveI`/`letI` style linter on this one declaration (house style, playbook §7.4).
set_option linter.style.haveILetI false in
theorem measurableSet_setOf_ideleNorm_det_mem_Icc (F : Type) [Field F] [NumberField F]
    (d₁ d₂ : ℝ) :
    @MeasurableSet (AdelicGL2 (𝓞 F) F) (NumberField.AdelicHaar.glBorel (Fin 2) (𝓞 F) F)
      {g : AdelicGL2 (𝓞 F) F | ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc d₁ d₂} := by
  letI := NumberField.AdelicHaar.glBorel (Fin 2) (𝓞 F) F
  haveI := NumberField.AdelicHaar.borelSpace_glBorel (Fin 2) (𝓞 F) F
  exact (isClosed_Icc.preimage (NumberField.TateGlobal.continuous_ideleNorm_det F)).measurableSet

-- pin: ideleNorm_det_eq_one_of_isCompact_of_mem (S_NumberField_TateGlobal_ideleNorm_det_eq_one_of_isCompact_of_mem.lean:19)
theorem ideleNorm_det_eq_one_of_isCompact_of_mem
    (F : Type) [Field F] [NumberField F]
    (U : Subgroup (AdelicGL2 (𝓞 F) F)) (hU : IsCompact (U : Set (AdelicGL2 (𝓞 F) F)))
    (u : AdelicGL2 (𝓞 F) F) (hu : u ∈ U) :
    ideleNorm F (Matrix.GeneralLinearGroup.det u) = 1 := by
  have hcont : Continuous fun g : AdelicGL2 (𝓞 F) F => ideleNorm F (Matrix.GeneralLinearGroup.det g) :=
    NumberField.TateGlobal.continuous_ideleNorm_det F
  have hmul : ∀ a b : AdelicGL2 (𝓞 F) F, ideleNorm F (Matrix.GeneralLinearGroup.det (a * b)) =
      ideleNorm F (Matrix.GeneralLinearGroup.det a) * ideleNorm F (Matrix.GeneralLinearGroup.det b) := by
    intro a b; rw [map_mul, ideleNorm_mul]
  have hpow : ∀ (n : ℕ), ideleNorm F (Matrix.GeneralLinearGroup.det (u ^ n)) =
      ideleNorm F (Matrix.GeneralLinearGroup.det u) ^ n := by
    intro n
    induction n with
    | zero => simp [NumberField.TateGlobal.ideleNorm]
    | succ n ih => rw [pow_succ u n, hmul, ih, ← pow_succ]
  obtain ⟨M, hM⟩ := (hU.image hcont).isBounded.bddAbove
  have hbd : ∀ g ∈ U, ideleNorm F (Matrix.GeneralLinearGroup.det g) ≤ M := fun g hg => hM ⟨g, hg, rfl⟩
  set x := ideleNorm F (Matrix.GeneralLinearGroup.det u) with hx
  have hxpos : 0 < x := ideleNorm_pos _
  have hup : ∀ n : ℕ, x ^ n ≤ M := fun n => by rw [← hpow]; exact hbd _ (U.pow_mem hu n)
  have hinv : ideleNorm F (Matrix.GeneralLinearGroup.det u⁻¹) = x⁻¹ := by
    have h1 : ideleNorm F (Matrix.GeneralLinearGroup.det (u * u⁻¹)) = 1 := by
      rw [mul_inv_cancel]; simp [NumberField.TateGlobal.ideleNorm]
    rw [hmul] at h1
    exact (eq_inv_of_mul_eq_one_right h1)
  have hpow' : ∀ n : ℕ, ideleNorm F (Matrix.GeneralLinearGroup.det (u⁻¹ ^ n)) = x⁻¹ ^ n := by
    intro n
    induction n with
    | zero => simp [NumberField.TateGlobal.ideleNorm]
    | succ n ih => rw [pow_succ u⁻¹ n, hmul, ih, hinv, ← pow_succ]
  have hdown : ∀ n : ℕ, x⁻¹ ^ n ≤ M := fun n => by
    rw [← hpow']; exact hbd _ (U.pow_mem (U.inv_mem hu) n)
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  ·
    have h1 : 1 < x⁻¹ := (one_lt_inv₀ hxpos).mpr hlt
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt M h1
    exact absurd (hdown n) (not_le.mpr hn)
  · obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt M hgt
    exact absurd (hup n) (not_le.mpr hn)

end TateGlobal
end NumberField
