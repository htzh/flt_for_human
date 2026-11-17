/-
  The `q`-coefficient layer over a `ModularFormClass`: an element of any bundled
  class of modular forms is presented by its own `q`-expansion, hence determined by
  its coefficients, and `qCoeff` is additive and `ℂ`-homogeneous on it.

  This is the instance-level facade on `ModularForms/QCoeff`: the function-level
  facts live there, and every statement below is a single application of one of
  them to the regularity that the class provides.

  The pin statements are port-owned (`topics/TOPIC-interface-changes.md`); their
  `spec-pin:` lines are parked in `Reserve/ModularForms/PortOwnedSpecPins.lean`.
-/
import FLTForHuman.ModularForms.QCoeff

set_option autoImplicit false

noncomputable section

open Complex Function Filter
open UpperHalfPlane hiding I
open scoped Real MatrixGroups ModularForm Manifold Topology

open ModularForm ModularFormClass

/-- An element of any `ModularFormClass` is presented by its own `q`-expansion. -/
theorem ModularFormClass.hasSum_qCoeff {F : Type*} [FunLike F UpperHalfPlane ℂ]
    {Γ : Subgroup (Matrix.GeneralLinearGroup (Fin 2) ℝ)} {k : ℤ} [ModularFormClass F Γ k]
    (f : F) (hΓ : (1 : ℝ) ∈ Γ.strictPeriods) (τ : ℍ) :
    HasSum (fun m ↦ ModularFormClass.qCoeff f m • Periodic.qParam 1 τ ^ m) (f τ) := by
  have : Fact (IsCusp OnePoint.infty Γ) := ⟨Γ.isCusp_of_mem_strictPeriods one_pos hΓ⟩
  exact UpperHalfPlane.hasSum_qExpansion one_pos
    (SlashInvariantFormClass.periodic_comp_ofComplex f hΓ) (holo f) (bdd_at_infty f) τ

/-- The bundled form of `UpperHalfPlane.eq_of_forall_qCoeff_eq`. -/
theorem ModularFormClass.eq_of_forall_qCoeff_eq {F : Type*} [FunLike F UpperHalfPlane ℂ]
    {Γ : Subgroup (Matrix.GeneralLinearGroup (Fin 2) ℝ)} {k : ℤ} [ModularFormClass F Γ k]
    {f g : F} (hΓ : (1 : ℝ) ∈ Γ.strictPeriods)
    (h : ∀ n : ℕ, ModularFormClass.qCoeff f n = ModularFormClass.qCoeff g n) : f = g := by
  refine DFunLike.ext f g fun τ => ?_
  have hf := ModularFormClass.hasSum_qCoeff f hΓ τ
  have hg := ModularFormClass.hasSum_qCoeff g hΓ τ
  simp only [h] at hf
  exact hf.unique hg

/-- `qCoeff` is additive, for any `ModularFormClass`. -/
theorem ModularFormClass.qCoeff_add' {F : Type*} [FunLike F UpperHalfPlane ℂ]
    {Γ : Subgroup (Matrix.GeneralLinearGroup (Fin 2) ℝ)} {k : ℤ} [ModularFormClass F Γ k]
    (hΓ : (1 : ℝ) ∈ Γ.strictPeriods) (f g : F) (n : ℕ) :
    qCoeff (⇑f + ⇑g) n = qCoeff ⇑f n + qCoeff ⇑g n := by
  simp only [qCoeff]
  rw [ModularForm.qExpansion_add one_pos hΓ f g]
  simp

/-- `qCoeff` is subtractive, for any `ModularFormClass`. -/
theorem ModularFormClass.qCoeff_sub' {F : Type*} [FunLike F UpperHalfPlane ℂ]
    {Γ : Subgroup (Matrix.GeneralLinearGroup (Fin 2) ℝ)} {k : ℤ} [ModularFormClass F Γ k]
    (hΓ : (1 : ℝ) ∈ Γ.strictPeriods) (f g : F) (n : ℕ) :
    qCoeff (⇑f - ⇑g) n = qCoeff ⇑f n - qCoeff ⇑g n := by
  simp only [qCoeff]
  rw [ModularForm.qExpansion_sub one_pos hΓ f g]
  simp

/-- `qCoeff` is `ℂ`-linear, for any `ModularFormClass`. -/
theorem ModularFormClass.qCoeff_const_smul' {F : Type*} [FunLike F UpperHalfPlane ℂ]
    {Γ : Subgroup (Matrix.GeneralLinearGroup (Fin 2) ℝ)} {k : ℤ} [ModularFormClass F Γ k]
    (hΓ : (1 : ℝ) ∈ Γ.strictPeriods) (f : F) (c : ℂ) (n : ℕ) :
    qCoeff (c • ⇑f) n = c * qCoeff ⇑f n := by
  simp only [qCoeff]
  rw [ModularForm.qExpansion_smul one_pos hΓ c f]
  simp

end
