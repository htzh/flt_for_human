/-
  The degeneracy (level-raising) map `f(τ) ↦ f(dτ)` on `Γ₀`-cusp forms.

  If `d * M ∣ N`, every weight-`k` cusp form for `Γ₀(M)` pulls back along
  `τ ↦ dτ` to a cusp form for `Γ₀(N)`. The construction restricts the translate
  `f ∣[k] heckeDiagMatrix d` — which lives at the conjugate level
  `toConjAct (heckeDiagMatrix d)⁻¹ • Γ₀(M)` — along
  `Γ₀(N) ≤ toConjAct (heckeDiagMatrix d)⁻¹ • Γ₀(M)`, then normalises by the
  automorphy factor `d ^ (k - 1)`.

  The statement is the pin's `Theorems/` wrapper verbatim; the proof is
  transcribed from
  https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_CuspForm_exists_degeneracy_Gamma0.lean
  with `DegeneracyPort` kept `private`. The pin's block is shared with the
  *ModularForm* degeneracy node `ModularForm.exists_degeneracy_Gamma0`, whose
  helpers `restrictMF`, `coe_restrictMF` and `exists_modularForm` were dropped by
  the original CuspForm-only pass (playbook §7.1, "no self-consumed lemmas").
  Row S's `E₄³/Δ` modular-polynomial tail consumes the `ModularForm` twin, so it
  is ported here at its pin name (the helpers stay `private`); the same
  `Gamma0_le_conj_Gamma0` serves both.
-/
import FLTForHuman.ModularForms.Defs.HeckeOperator
import Mathlib.NumberTheory.ModularForms.Basic
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.Data.ZMod.Basic

set_option autoImplicit false

-- The pin's `haveI` walls are load-bearing; keep them literal (port convention).
set_option linter.style.haveILetI false

noncomputable section

open UpperHalfPlane
open scoped Matrix MatrixGroups ModularForm Pointwise

namespace ModularForm

namespace DegeneracyPort

variable {k : ℤ}

/-- Restrict a modular form along an inclusion of level subgroups. -/
private def restrictMF {Γ Γ' : Subgroup (GL (Fin 2) ℝ)} (h : Γ' ≤ Γ) (F : ModularForm Γ k) :
    ModularForm Γ' k where
  toFun := F
  slash_action_eq' γ hγ := SlashInvariantForm.slash_action_eqn F γ (h hγ)
  holo' := F.holo'
  bdd_at_cusps' hc := F.bdd_at_cusps' (hc.mono h)

@[scoped simp] private theorem coe_restrictMF {Γ Γ' : Subgroup (GL (Fin 2) ℝ)} (h : Γ' ≤ Γ)
    (F : ModularForm Γ k) : ⇑(restrictMF h F) = ⇑F := rfl

/-- Restrict a cusp form along an inclusion of level subgroups. -/
private def restrictCF {Γ Γ' : Subgroup (GL (Fin 2) ℝ)} (h : Γ' ≤ Γ) (F : CuspForm Γ k) :
    CuspForm Γ' k where
  toFun := F
  slash_action_eq' γ hγ := SlashInvariantForm.slash_action_eqn F γ (h hγ)
  holo' := F.holo'
  zero_at_cusps' hc := F.zero_at_cusps' (hc.mono h)

@[scoped simp] private theorem coe_restrictCF {Γ Γ' : Subgroup (GL (Fin 2) ℝ)} (h : Γ' ≤ Γ)
    (F : CuspForm Γ k) : ⇑(restrictCF h F) = ⇑F := rfl

/-- `Γ₀(N)` is contained in the conjugate of `Γ₀(M)` by `heckeDiagMatrix d` when
`d * M ∣ N`. -/
private theorem Gamma0_le_conj_Gamma0 {M N d : ℕ} (hd : d ≠ 0) (hdiv : d * M ∣ N) :
    ((CongruenceSubgroup.Gamma0 N : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) ≤
      ConjAct.toConjAct (heckeDiagMatrix d)⁻¹ •
        ((CongruenceSubgroup.Gamma0 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) := by
  rintro _ ⟨A, hA, rfl⟩
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ConjAct.toConjAct_inv, inv_inv,
    ConjAct.toConjAct_smul]

  have hN : (N : ℤ) ∣ (A : Matrix (Fin 2) (Fin 2) ℤ) 1 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ N).mp (CongruenceSubgroup.Gamma0_mem.mp hA)
  obtain ⟨c', hc'⟩ : (d : ℤ) ∣ (A : Matrix (Fin 2) (Fin 2) ℤ) 1 0 :=
    (Int.natCast_dvd_natCast.mpr (Dvd.intro _ rfl : d ∣ d * M)).trans
      ((Int.natCast_dvd_natCast.mpr hdiv).trans hN)
  have hMc' : (M : ℤ) ∣ c' := by
    have h1 : (d : ℤ) * M ∣ (d : ℤ) * c' := by
      rw [← hc']; exact_mod_cast (Int.natCast_dvd_natCast.mpr hdiv).trans hN
    exact (mul_dvd_mul_iff_left (by exact_mod_cast hd)).mp h1
  have hdet : (A : Matrix (Fin 2) (Fin 2) ℤ) 0 0 * (A : Matrix (Fin 2) (Fin 2) ℤ) 1 1 -
      (A : Matrix (Fin 2) (Fin 2) ℤ) 0 1 * (A : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = 1 := by
    rw [← Matrix.det_fin_two, A.det_coe]

  let B : SL(2, ℤ) := ⟨!![(A : Matrix (Fin 2) (Fin 2) ℤ) 0 0, d * (A : Matrix (Fin 2) (Fin 2) ℤ) 0 1;
      c', (A : Matrix (Fin 2) (Fin 2) ℤ) 1 1], by
    rw [Matrix.det_fin_two_of]
    linear_combination hdet + (A : Matrix (Fin 2) (Fin 2) ℤ) 0 1 * hc'⟩
  refine ⟨B, ?_, ?_⟩
  ·
    rw [SetLike.mem_coe, CongruenceSubgroup.Gamma0_mem]
    show ((c' : ℤ) : ZMod M) = 0
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ M).mpr hMc'
  ·
    rw [eq_mul_inv_iff_mul_eq]
    apply Units.ext
    simp only [Units.val_mul, Matrix.SpecialLinearGroup.mapGL_coe_matrix, val_heckeDiagMatrix hd]
    ext i j
    rw [Matrix.SpecialLinearGroup.map_apply_coe]
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, B, hc', mul_comm]

/-- The modular-form degeneracy map. -/
private theorem exists_modularForm {M N d : ℕ} [NeZero N] (hdiv : d * M ∣ N)
    (f : ModularForm (CongruenceSubgroup.Gamma0 M) k) :
    ∃ g : ModularForm (CongruenceSubgroup.Gamma0 N) k,
      ⇑g = fun τ ↦ f (heckeDiagMatrix d • τ) := by
  have hd : d ≠ 0 := by
    rintro rfl
    rw [zero_mul, zero_dvd_iff] at hdiv
    exact NeZero.ne N hdiv
  have hdk : ((d : ℂ) ^ (k - 1)) ≠ 0 := zpow_ne_zero _ (Nat.cast_ne_zero.mpr hd)
  refine ⟨((d : ℂ) ^ (k - 1))⁻¹ •
    restrictMF (Gamma0_le_conj_Gamma0 hd hdiv) (ModularForm.translate f (heckeDiagMatrix d)), ?_⟩
  funext τ
  rw [FunLike.coe_smul, Pi.smul_apply, coe_restrictMF, ModularForm.coe_translate,
    slash_heckeDiagMatrix_apply k hd, smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hdk, one_mul]

/-- The cusp-form degeneracy map. -/
private theorem exists_cuspForm {M N d : ℕ} [NeZero N] (hdiv : d * M ∣ N)
    (f : CuspForm (CongruenceSubgroup.Gamma0 M) k) :
    ∃ g : CuspForm (CongruenceSubgroup.Gamma0 N) k,
      ⇑g = fun τ ↦ f (heckeDiagMatrix d • τ) := by
  have hd : d ≠ 0 := by
    rintro rfl
    rw [zero_mul, zero_dvd_iff] at hdiv
    exact NeZero.ne N hdiv
  have hdk : ((d : ℂ) ^ (k - 1)) ≠ 0 := zpow_ne_zero _ (Nat.cast_ne_zero.mpr hd)
  refine ⟨((d : ℂ) ^ (k - 1))⁻¹ •
    restrictCF (Gamma0_le_conj_Gamma0 hd hdiv) (CuspForm.translate f (heckeDiagMatrix d)), ?_⟩
  funext τ
  rw [FunLike.coe_smul, Pi.smul_apply, coe_restrictCF]
  show ((d : ℂ) ^ (k - 1))⁻¹ • (⇑f ∣[k] heckeDiagMatrix d) τ = _
  rw [slash_heckeDiagMatrix_apply k hd, smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hdk, one_mul]

end DegeneracyPort

end ModularForm

/-- **The degeneracy map `f(τ) ↦ f(dτ)`.** Stated verbatim from
`Theorems/Thm_CuspForm_exists_degeneracy_Gamma0.lean`. -/
theorem CuspForm.exists_degeneracy_Gamma0 {k : ℤ} {M N d : ℕ} [NeZero N]
    (hd : d * M ∣ N) (f : CuspForm (CongruenceSubgroup.Gamma0 M) k) :
    ∃ g : CuspForm (CongruenceSubgroup.Gamma0 N) k,
      ⇑g = fun τ ↦ f (ModularForm.heckeDiagMatrix d • τ) :=
  ModularForm.DegeneracyPort.exists_cuspForm hd f

/-- **The degeneracy map `f(τ) ↦ f(dτ)` on modular forms.** Stated verbatim from
`Theorems/Thm_ModularForm_exists_degeneracy_Gamma0.lean`; the pin's twin of
`CuspForm.exists_degeneracy_Gamma0`. -/
theorem ModularForm.exists_degeneracy_Gamma0 {k : ℤ} {M N d : ℕ} [NeZero N]
    (hd : d * M ∣ N) (f : ModularForm (CongruenceSubgroup.Gamma0 M) k) :
    ∃ g : ModularForm (CongruenceSubgroup.Gamma0 N) k,
      ⇑g = fun τ ↦ f (ModularForm.heckeDiagMatrix d • τ) :=
  ModularForm.DegeneracyPort.exists_modularForm hd f

end
