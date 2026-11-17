/-
  `q`-coefficients of modular forms: `qCoeff`, its `HasSum` presentation, that equal
  coefficients force equal functions, and the coefficient algebra.

  spec-pin: Definitions/Def_FLTPrelim_Modularity.lean
  spec-pin: Theorems/Thm_UpperHalfPlane_eq_of_forall_qCoeff_eq.lean
  spec-pin: P2M/Sol/S_UpperHalfPlane_eq_of_forall_qCoeff_eq.lean
  spec-pin: Theorems/Thm_ModularFormClass_eq_of_forall_qCoeff_eq.lean
  spec-pin: P2M/Sol/S_CuspForm_IsEigenformWith_heckeU_add_smul_slash_heckeDiagMatrix_degeneracy_eq_qCoeff_smul.lean
-/
import Mathlib.NumberTheory.ModularForms.QExpansion
import Mathlib.NumberTheory.ModularForms.BoundedAtCusp

set_option autoImplicit false

noncomputable section

open Complex Function Filter
open UpperHalfPlane hiding I
open scoped Real MatrixGroups ModularForm Manifold Topology

namespace ModularFormClass

/-- The `n`-th `q`-coefficient of `f`. -/
def qCoeff (f : ℍ → ℂ) (n : ℕ) : ℂ :=
  (qExpansion 1 f).coeff n

end ModularFormClass

open ModularForm ModularFormClass

/-! ## The `q`-expansion presentation -/

/-- A function with a `q`-expansion has `qCoeff` as its `HasSum` coefficients. -/
theorem hasSum_qCoeff {f : ℍ → ℂ} (hper : Periodic (f ∘ ofComplex) 1) (hhol : MDiff f)
    (hbdd : IsBoundedAtImInfty f) (τ : ℍ) :
    HasSum (fun m ↦ qCoeff f m • Periodic.qParam 1 τ ^ m) (f τ) :=
  hasSum_qExpansion one_pos hper hhol hbdd τ

/-! ## Equal coefficients force equality -/

/-- Two periodic, holomorphic, bounded functions with equal `q`-coefficients are
equal. -/
theorem UpperHalfPlane.eq_of_forall_qCoeff_eq {f g : UpperHalfPlane → ℂ} (hfper : Function.Periodic (f ∘ UpperHalfPlane.ofComplex) 1) (hfhol : MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) f) (hfbdd : UpperHalfPlane.IsBoundedAtImInfty f) (hgper : Function.Periodic (g ∘ UpperHalfPlane.ofComplex) 1) (hghol : MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) g) (hgbdd : UpperHalfPlane.IsBoundedAtImInfty g) (h : ∀ n : ℕ, ModularFormClass.qCoeff f n = ModularFormClass.qCoeff g n) : f = g := by
  funext τ
  have hf := hasSum_qCoeff hfper hfhol hfbdd τ
  have hg := hasSum_qCoeff hgper hghol hgbdd τ
  simp only [h] at hf
  exact hf.unique hg

/-- The bundled form of `UpperHalfPlane.eq_of_forall_qCoeff_eq`. -/
theorem ModularFormClass.eq_of_forall_qCoeff_eq {F : Type*} [FunLike F UpperHalfPlane ℂ]
    {Γ : Subgroup (Matrix.GeneralLinearGroup (Fin 2) ℝ)} {k : ℤ} [ModularFormClass F Γ k]
    {f g : F} (hΓ : (1 : ℝ) ∈ Γ.strictPeriods)
    (h : ∀ n : ℕ, ModularFormClass.qCoeff f n = ModularFormClass.qCoeff g n) : f = g := by
  have hcusp : Fact (IsCusp OnePoint.infty Γ) := ⟨Γ.isCusp_of_mem_strictPeriods one_pos hΓ⟩
  exact DFunLike.coe_injective
    (UpperHalfPlane.eq_of_forall_qCoeff_eq
      (SlashInvariantFormClass.periodic_comp_ofComplex f hΓ) (holo f) (bdd_at_infty f)
      (SlashInvariantFormClass.periodic_comp_ofComplex g hΓ) (holo g) (bdd_at_infty g) h)

/-! ## The `q`-coefficient algebra -/

/-- `qCoeff` is additive. -/
theorem ModularFormClass.qCoeff_add {f g : ℍ → ℂ} (hfper : Periodic (f ∘ ofComplex) 1)
    (hfhol : MDiff f) (hfbdd : IsBoundedAtImInfty f) (hgper : Periodic (g ∘ ofComplex) 1)
    (hghol : MDiff g) (hgbdd : IsBoundedAtImInfty g) (n : ℕ) :
    qCoeff (f + g) n = qCoeff f n + qCoeff g n := by
  simp only [qCoeff]
  rw [qExpansion_add (analyticAt_cuspFunction_zero one_pos hfper hfhol hfbdd)
    (analyticAt_cuspFunction_zero one_pos hgper hghol hgbdd)]
  simp

/-- `qCoeff` is subtractive. -/
theorem ModularFormClass.qCoeff_sub {f g : ℍ → ℂ} (hfper : Periodic (f ∘ ofComplex) 1)
    (hfhol : MDiff f) (hfbdd : IsBoundedAtImInfty f) (hgper : Periodic (g ∘ ofComplex) 1)
    (hghol : MDiff g) (hgbdd : IsBoundedAtImInfty g) (n : ℕ) :
    qCoeff (f - g) n = qCoeff f n - qCoeff g n := by
  simp only [qCoeff]
  rw [qExpansion_sub (analyticAt_cuspFunction_zero one_pos hfper hfhol hfbdd)
    (analyticAt_cuspFunction_zero one_pos hgper hghol hgbdd)]
  simp

/-- `qCoeff` is `ℂ`-linear. -/
theorem ModularFormClass.qCoeff_const_smul {f : ℍ → ℂ} (hper : Periodic (f ∘ ofComplex) 1)
    (hhol : MDiff f) (hbdd : IsBoundedAtImInfty f) (c : ℂ) (n : ℕ) :
    qCoeff (c • f) n = c * qCoeff f n := by
  simp only [qCoeff]
  rw [qExpansion_smul (analyticAt_cuspFunction_zero one_pos hper hhol hbdd)]
  simp

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
