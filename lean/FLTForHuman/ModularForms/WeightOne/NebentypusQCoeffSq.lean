/-
  The nebentypus coefficient-square disjunction: `U_p`/`T` eigen-hypotheses.

  ## What the module is

  The twin of `WeightOne/PrimitiveQCoeffNorm.lean`: same Fricke-twisted computation
  (`h = trForm W p f` is again a nebentypus form, `T_p` on it computed two ways), but the
  hypotheses are `U_p`- and `T`-eigen instead of primitivity, and the conclusion is the
  disjunction

    `a_p(f)² = ε'(p) · p^(k-2)  ∨  ∃ g at level M / p` eigen for `ε'`,

    `CuspForm.qCoeff_sq_eq_mul_zpow_or_exists_hasNebentypus_qCoeff_hecke_eigen_of_dvd_of_not_sq_dvd`

  The pin's file is 1,312 lines; 1,189 of them are the *shared* block, ported once in
  `PrimitiveQCoeffNorm.lean` (in A's `ℓ` spelling — byte-identical after the rename). This module
  imports that block and adds **only its own head**: the private assembly `main_of_nebentypus`
  and the public headline. Nothing of the shared block is re-declared.

  FLT provenance, pinned `aa2d8b3`:
  https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_CuspForm_qCoeff_sq_eq_mul_zpow_or_exists_hasNebentypus_qCoeff_hecke_eigen_of_dvd_of_not_sq_dvd.lean

  spec-pin: P2M/Sol/S_CuspForm_qCoeff_sq_eq_mul_zpow_or_exists_hasNebentypus_qCoeff_hecke_eigen_of_dvd_of_not_sq_dvd.lean
  spec-pin: Theorems/Thm_CuspForm_qCoeff_sq_eq_mul_zpow_or_exists_hasNebentypus_qCoeff_hecke_eigen_of_dvd_of_not_sq_dvd.lean
-/
import FLTForHuman.ModularForms.WeightOne.PrimitiveQCoeffNorm

set_option autoImplicit false
set_option maxHeartbeats 3200000

-- The pin's `haveI` walls are kept literal (as in the rest of the port).
set_option linter.style.haveILetI false

open CongruenceSubgroup ModularForm ModularFormClass UpperHalfPlane Filter Function
open scoped ModularForm MatrixGroups

open CuspForm.PrimitiveQCoeffNorm

noncomputable section

namespace CuspForm

namespace NebentypusQCoeffSq

local notation "Γ₁ℝ" M => ((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))
local notation "Γ₀ℝ" M => ((Gamma0 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

private theorem main_of_nebentypus (M : ℕ) [NeZero M] (k : ℤ) {p : ℕ} (hp : p.Prime) (hpM : p ∣ M) (hp2 : ¬ p ^ 2 ∣ M)
    (ε' : DirichletCharacter ℂ (M / p)) (f : CuspForm (Γ₁ℝ M) k) (hf0 : f ≠ 0)
    (hε : CuspForm.HasNebentypus (DirichletCharacter.changeLevel (Nat.div_dvd_of_dvd hpM) ε') f)
    (hU : ∀ n : ℕ, qCoeff (⇑f) (p * n) = qCoeff (⇑f) p * qCoeff (⇑f) n)
    (hT : ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ M → ∀ n : ℕ,
        qCoeff (⇑f) (ℓ * n) +
            ε' (ℓ : ZMod (M / p)) * (ℓ : ℂ) ^ (k - 1) *
              (if ℓ ∣ n then qCoeff (⇑f) (n / ℓ) else 0) =
          qCoeff (⇑f) ℓ * qCoeff (⇑f) n) :
    qCoeff (⇑f) p ^ 2 = ε' (p : ZMod (M / p)) * (p : ℂ) ^ (k - 2) ∨
    ∃ g : CuspForm (Γ₁ℝ (M / p)) k, g ≠ 0 ∧ CuspForm.HasNebentypus ε' g ∧
      ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ M → ∀ n : ℕ,
        qCoeff (⇑g) (ℓ * n) +
            ε' (ℓ : ZMod (M / p)) * (ℓ : ℂ) ^ (k - 1) *
              (if ℓ ∣ n then qCoeff (⇑g) (n / ℓ) else 0) =
          qCoeff (⇑f) ℓ * qCoeff (⇑g) n := by
  set W : AtkinLehnerDatum M p := datum hp hpM hp2 with hW
  have hp0 : p ≠ 0 := hp.ne_zero

  have hF : IsOfType M k ε' (⇑f) := isOfType_of_hasNebentypus (Nat.div_dvd_of_dvd hpM) ε' hε
  have hFW : IsOfType M k (show DirichletCharacter ℂ W.R from ε') (⇑f) := hF

  set ap : ℂ := qCoeff (⇑f) p with hap
  have hUf : heckeU k p ⇑f = ap • (⇑f : ℍ → ℂ) := heckeU_eq_smul_of_qCoeff f hp0 ap hU

  set g : CuspForm (Γ₁ℝ (M / p)) k := trForm W hp ε' f hFW with hg
  have hcoe : (⇑g : ℍ → ℂ) = alSlash W k ⇑f + heckeU k p ⇑f := rfl
  have hneb : CuspForm.HasNebentypus ε' g := hasNebentypus_trForm W hp ε' f hFW

  have hTg : ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ M →
      phi k ℓ (ε' (ℓ : ZMod (M / p))) ⇑g = qCoeff (⇑f) ℓ • (⇑g : ℍ → ℂ) := by
    intro ℓ hℓ hℓM
    have hΦf : phi k ℓ (ε' (ℓ : ZMod (M / p))) ⇑f = qCoeff (⇑f) ℓ • (⇑f : ℍ → ℂ) :=
      phi_eq_smul_of_qCoeff f hℓ.ne_zero _ _ (hT ℓ hℓ hℓM)
    have hΦW : alSlash W k (phi k ℓ (ε' (ℓ : ZMod (M / p))) ⇑f)
        = phi k ℓ (ε' (ℓ : ZMod (M / p))) (alSlash W k ⇑f) := alSlash_phi W hℓ hℓM ε' hFW
    rw [hcoe, phi_add, ← hΦW, hΦf, alSlash_smul, hUf, phi_smul, hΦf, smul_add, smul_comm]
  by_cases hg0 : g = 0
  ·
    left
    have hh0 : (⇑g : ℍ → ℂ) = 0 := by rw [hg0]; rfl
    have hWf : alSlash W k ⇑f = (-ap) • (⇑f : ℍ → ℂ) := by
      have := hh0
      rw [hcoe, hUf] at this
      exact (eq_neg_of_add_eq_zero_left this).trans (neg_smul ap _).symm
    have hsq : (ap * ap) • (⇑f : ℍ → ℂ) = (ε' (p : ZMod (M / p)) * (p : ℂ) ^ (k - 2)) • (⇑f : ℍ → ℂ) := by
      have h2 : alSlash W k (alSlash W k ⇑f) = (ap * ap) • (⇑f : ℍ → ℂ) := by
        rw [hWf, alSlash_smul, hWf, smul_smul, neg_mul_neg]
      rw [← h2]
      exact alSlash_alSlash W ε' hFW
    have hf0' : (⇑f : ℍ → ℂ) ≠ 0 := fun h0 => hf0 (DFunLike.ext' (by rw [h0]; rfl))
    obtain ⟨τ, hτ⟩ : ∃ τ, f τ ≠ 0 := by
      by_contra hall
      push Not at hall
      exact hf0' (funext hall)
    have := congrFun hsq τ
    simp only [Pi.smul_apply, smul_eq_mul] at this
    rw [sq]
    exact mul_right_cancel₀ hτ this
  ·
    right
    refine ⟨g, hg0, hneb, fun ℓ hℓ hℓM n => ?_⟩
    exact qCoeff_of_phi_eq_smul g hℓ.ne_zero _ _ (hTg ℓ hℓ hℓM) n


end NebentypusQCoeffSq

/-- For a non-zero level-`M` form with nebentypus `ε'`, eigen for `U_p` and for all `T_ℓ`
(`ℓ ∤ M`, `p ∣ M`, `p² ∤ M`), either `a_p(f)² = ε'(p) · p^(k-2)`, or there is a non-zero
level-`M/p` form `g` with nebentypus `ε'` whose Hecke eigenvalues agree with `f`. -/
theorem qCoeff_sq_eq_mul_zpow_or_exists_hasNebentypus_qCoeff_hecke_eigen_of_dvd_of_not_sq_dvd
    (M : ℕ) [NeZero M] (k : ℤ) {p : ℕ} (hp : p.Prime) (hpM : p ∣ M) (hp2 : ¬ p ^ 2 ∣ M)
    (ε' : DirichletCharacter ℂ (M / p)) (f : CuspForm (Gamma1 M) k) (hf0 : f ≠ 0)
    (hε : CuspForm.HasNebentypus (DirichletCharacter.changeLevel (Nat.div_dvd_of_dvd hpM) ε') f)
    (hU : ∀ n : ℕ, ModularFormClass.qCoeff f (p * n) =
      ModularFormClass.qCoeff f p * ModularFormClass.qCoeff f n)
    (hT : ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ M → ∀ n : ℕ,
        ModularFormClass.qCoeff f (ℓ * n) +
            ε' (ℓ : ZMod (M / p)) * (ℓ : ℂ) ^ (k - 1) *
              (if ℓ ∣ n then ModularFormClass.qCoeff f (n / ℓ) else 0) =
          ModularFormClass.qCoeff f ℓ * ModularFormClass.qCoeff f n) :
    ModularFormClass.qCoeff f p ^ 2 = ε' (p : ZMod (M / p)) * (p : ℂ) ^ (k - 2) ∨
    ∃ g : CuspForm (Gamma1 (M / p)) k, g ≠ 0 ∧ CuspForm.HasNebentypus ε' g ∧
      ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ M → ∀ n : ℕ,
        ModularFormClass.qCoeff g (ℓ * n) +
            ε' (ℓ : ZMod (M / p)) * (ℓ : ℂ) ^ (k - 1) *
              (if ℓ ∣ n then ModularFormClass.qCoeff g (n / ℓ) else 0) =
          ModularFormClass.qCoeff f ℓ * ModularFormClass.qCoeff g n :=
  NebentypusQCoeffSq.main_of_nebentypus M k hp hpM hp2 ε' f hf0 hε hU hT

end CuspForm
