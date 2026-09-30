/-
  H1 prelude: the `T`-slash periodicity and Hecke-matrix/analytic blocks that the
  phase-H1 consumers share.

  FLT spreads these blocks over three `S_` files, which repeat the proofs with
  different binders (and, in one case, a weight-`1` instead of a general-weight
  copy). This module ports the union once, at the pin's names and statements,
  taking the most general copy of each:

  * `P2M/Sol/S_CuspForm_qCoeff_heckeTLinOne.lean` (the general-weight copy);
  * `P2M/Sol/S_CuspForm_slash_eq_dirichlet_smul_of_qCoeff_hecke_eigen.lean`;
  * `P2M/Sol/S_DeligneSerre_exists_subalgebra_qCoeff_mem_forall_ringHom_exists_qCoeff_eq_of_weightOne_hecke_eigen.lean`
    (weight-`1` copies of the `cusp_*` block).

  `T_pow_mem_Gamma1`/`T_mem_Gamma1`/`mapGL_apply` are H2 clash or live-in-port
  names, so no copy is added here: `mapGL_apply` comes from
  `Defs/HeckeRepresentatives.lean`, and the `Γ₁`-membership witness for the
  periodicity proof is a `private` local helper (`T_pow_mem_Gamma1_aux`), as is
  `cusp_slash_T_pow` (the pin's unlisted general-weight witness helper).

  `Definitions.Def_CuspForm_Gamma1HeckeOperators` is the definition source for
  the two pin files; the port's home for its repeated vocabulary is
  `FLTForHuman.ModularForms.Level.Diamond`, imported below.
-/
import FLTForHuman.ModularForms.Level.Diamond
import FLTForHuman.ModularForms.Defs.HeckeRepresentatives
import FLTForHuman.ModularForms.HeckeAnalytic
import FLTForHuman.ModularForms.HeckeQCoeff
import FLTForHuman.ModularForms.Eisenstein.WeierstrassZeta

set_option autoImplicit false

-- The pin's `haveI` walls are kept literal (as in `Level/Diamond.lean`).
set_option linter.style.haveILetI false

noncomputable section

open CongruenceSubgroup UpperHalfPlane Filter Function
open ModularForm
open ModularForm.HeckeRepresentatives
open scoped MatrixGroups ModularForm OnePoint Manifold

namespace ModularForm

section SlashT

variable {k : ℤ} {p : ℕ}

theorem heckeDiagMatrix_mul_T (hp : p ≠ 0) :
    heckeDiagMatrix p * (Matrix.SpecialLinearGroup.mapGL ℝ ModularGroup.T)
      = Matrix.SpecialLinearGroup.mapGL ℝ (ModularGroup.T ^ p) * heckeDiagMatrix p := by
  have hTp : ((ModularGroup.T ^ p : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) =
      !![1, (p : ℤ); 0, 1] := by
    rw [show ModularGroup.T ^ p = ModularGroup.T ^ (p : ℤ) from (zpow_natCast _ p).symm]
    exact ModularGroup.coe_T_zpow (p : ℤ)
  ext i j
  rw [Units.val_mul, Units.val_mul, Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_two,
    Fin.sum_univ_two, mapGL_apply, mapGL_apply, mapGL_apply, mapGL_apply, hTp, ModularGroup.coe_T,
    val_heckeDiagMatrix hp]
  fin_cases i <;> fin_cases j <;> simp

theorem periodic_of_slash_T {F : ℍ → ℂ}
    (h : F ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ ModularGroup.T) = F) :
    Periodic (F ∘ ofComplex) 1 := by
  have hT : ∀ τ : ℍ, F ((1 : ℝ) +ᵥ τ) = F τ := by
    intro τ
    have hden : denom (Matrix.SpecialLinearGroup.mapGL ℝ ModularGroup.T) (τ : ℂ) = 1 := by
      rw [denom, mapGL_apply, mapGL_apply, ModularGroup.coe_T]
      norm_num
    have hden' : denom (Matrix.SpecialLinearGroup.toGL
        (Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) ModularGroup.T)) (τ : ℂ) = 1 := hden
    have := congrFun h τ
    change (F ∣[k] ModularGroup.T) τ = F τ at this
    rw [SL_slash_apply, hden'] at this
    simp at this
    rw [← modular_T_smul]
    exact this
  intro w
  by_cases hw : 0 < w.im
  · have : 0 < (w + 1).im := by simp [hw]
    simp only [comp_apply, ofComplex_apply_of_im_pos this, ofComplex_apply_of_im_pos hw]
    convert hT ⟨w, hw⟩ using 2
    ext
    simp [add_comm]
  · have hw : w.im ≤ 0 := le_of_not_gt hw
    have : (w + 1).im ≤ 0 := by simpa using hw
    simp [ofComplex_apply_of_im_nonpos this, ofComplex_apply_of_im_nonpos hw]

theorem slash_heckeDiagMatrix_slash_T (hp : p ≠ 0) {F : ℍ → ℂ}
    (h : F ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ (ModularGroup.T ^ p)) = F) :
    (F ∣[k] heckeDiagMatrix p) ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ ModularGroup.T)
      = F ∣[k] heckeDiagMatrix p := by
  rw [← SlashAction.slash_mul, heckeDiagMatrix_mul_T hp, SlashAction.slash_mul, h]

theorem isBoundedAtImInfty_slash_heckeMatrix (hp : p ≠ 0) (j : ℕ) {F : ℍ → ℂ}
    (hF : IsBoundedAtImInfty F) : IsBoundedAtImInfty (F ∣[k] heckeMatrix p j) :=
  hF.slash k (by simp [val_heckeMatrix hp])

theorem isBoundedAtImInfty_slash_heckeDiagMatrix (hp : p ≠ 0) {F : ℍ → ℂ}
    (hF : IsBoundedAtImInfty F) : IsBoundedAtImInfty (F ∣[k] heckeDiagMatrix p) :=
  hF.slash k (by simp [val_heckeDiagMatrix hp])

end SlashT

end ModularForm

local notation "Γ₁ℝ" M => ((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

namespace CuspForm

section Cusp

variable {M : ℕ} {k : ℤ}

/-- `T ^ n ∈ Γ₁(M)`; the pin states this as the public `T_pow_mem_Gamma1`, which
is an H2 clash name, so the witness stays `private` here. -/
private theorem T_pow_mem_Gamma1_aux (M n : ℕ) : ModularGroup.T ^ n ∈ Gamma1 M := by
  rw [show ModularGroup.T ^ n = ModularGroup.T ^ (n : ℤ) from (zpow_natCast _ n).symm]
  rw [Gamma1_mem, ModularGroup.coe_T_zpow]
  simp

/-- The pin's unlisted general-weight witness helper (`cusp_slash_T_pow` in
`S_CuspForm_qCoeff_heckeTLinOne.lean`). -/
private theorem cusp_slash_T_pow (F : CuspForm (Γ₁ℝ M) k) (n : ℕ) :
    (⇑F : ℍ → ℂ) ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ (ModularGroup.T ^ n)) = ⇑F :=
  SlashInvariantFormClass.slash_action_eq F _ (Subgroup.mem_map_of_mem _ (T_pow_mem_Gamma1_aux M n))

variable (F : CuspForm (Γ₁ℝ M) k)

theorem cusp_periodic : Periodic (⇑F ∘ ofComplex) 1 :=
  periodic_of_slash_T (k := k) (by simpa using cusp_slash_T_pow F 1)

theorem cusp_holo :
    MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) (⇑F) :=
  F.holo'

theorem cusp_bdd : IsBoundedAtImInfty (⇑F : ℍ → ℂ) := by
  have h1 : (1 : ℝ) ∈ (Γ₁ℝ M).strictPeriods := by
    rw [CongruenceSubgroup.strictPeriods_Gamma1]; exact AddSubgroup.mem_zmultiples _
  haveI : Fact (IsCusp OnePoint.infty (Γ₁ℝ M)) :=
    ⟨(Γ₁ℝ M).isCusp_of_mem_strictPeriods one_pos h1⟩
  exact ModularFormClass.bdd_at_infty F

end Cusp

end CuspForm

end
