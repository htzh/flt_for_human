/-
  The `U_ℓ` operator on `Γ₁`-cusp forms, and its level lowering.

  `ModularForm.heckeU k ℓ f` is the `ℓ`-th Hecke operator `U_ℓ` (the sum over the mod-`ℓ` cosets). On
  `Γ₁`-cusp forms it is again a `Γ₁`-cusp form and its `q`-expansion is the `ℓ`-subsequence of `f`'s:
  `qCoeff (U_ℓ f) n = qCoeff f (ℓ n)`; moreover `U_ℓ` preserves the nebentypus at the level `N`
  (`exists_gamma1_coe_eq_heckeU_of_dvd`). When `ℓ² ∣ N` the same form descends to level `N/ℓ` — the
  level-lowering property that makes `U_ℓ` the standard tool for raising and lowering the level of an
  eigenform — and the nebentypus descends along the level change
  (`exists_gamma1_div_coe_eq_heckeU_of_dvd_div`).

  Transcribed whole from the pin's proof files
  `P2M/Sol/S_CuspForm_exists_gamma1_coe_eq_heckeU_of_dvd.lean` (pinned `aa2d8b3`, 241 lines / 20
  declarations) and `…_exists_gamma1_div_coe_eq_heckeU_of_dvd_div.lean` (348 lines / 32 declarations),
  with the statements from their `Theorems/` wrappers. The two files share three premises
  (`CuspFormClass.isZeroAt_heckeU`, `ModularForm.mdifferentiable_heckeU`,
  `ModularFormClass.qCoeff_heckeU`), all already ported.

  spec-pin: Theorems/Thm_CuspForm_exists_gamma1_coe_eq_heckeU_of_dvd.lean
  spec-pin: P2M/Sol/S_CuspForm_exists_gamma1_coe_eq_heckeU_of_dvd.lean
  spec-pin: Theorems/Thm_CuspForm_exists_gamma1_div_coe_eq_heckeU_of_dvd_div.lean
  spec-pin: P2M/Sol/S_CuspForm_exists_gamma1_div_coe_eq_heckeU_of_dvd_div.lean
-/
import FLTForHuman.ModularForms.Defs.HeckeOperator
import FLTForHuman.ModularForms.HeckeCusps
import FLTForHuman.ModularForms.HeckeNebentypus
import FLTForHuman.ModularForms.HeckeQCoeff
import FLTForHuman.ModularForms.HeckePrelude

set_option autoImplicit false

open CongruenceSubgroup
open ModularForm
open UpperHalfPlane Matrix.SpecialLinearGroup
open ModularForm.HeckeRepresentatives
open scoped MatrixGroups

noncomputable section

namespace CuspForm

local notation "Γ₁(" M ")" => ((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

/-! ## Row A — `U_ℓ` on `Γ₁(N)`-cusp forms

Transcribed from `P2M/Sol/S_CuspForm_exists_gamma1_coe_eq_heckeU_of_dvd.lean`. The pin's private
coset permutation `perm` is the port's `affinePerm` (`Defs/HeckeRepresentatives.lean`), and the
pin's `det_eq`, `heckeMatrix_mul_of_eq`, `sum_range_eq_sum_zmod`, `heckeU_eq_sum_zmod` are that
module's declarations, so they are not re-stated here. -/

section HeckeUGamma1

theorem mem_Gamma1_of {N : ℕ} {γ : SL(2, ℤ)} (hc : (N : ℤ) ∣ γ 1 0)
    (hd : ((γ 1 1 : ℤ) : ZMod N) = 1) : γ ∈ Gamma1 N :=
  ModularForm.Level.mem_Gamma1_of_d_eq_one
    (Gamma0_mem.mpr ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hc)) hd

/-- The pin's `exists_cocycle`, with its private `perm` replaced by the port's `affinePerm`. -/
private theorem exists_cocycle {N ℓ : ℕ} (hℓ : ℓ ≠ 0) (g : SL(2, ℤ))
    (hg : g ∈ Gamma0 N) {hc : ((g 1 0 : ℤ) : ZMod ℓ) = 0} (x : ZMod ℓ) :
    ∃ g' : SL(2, ℤ), (N : ℤ) ∣ g' 1 0 ∧ ((g' 1 1 : ℤ) : ZMod N) = ((g 1 1 : ℤ) : ZMod N) ∧
      heckeMatrix ℓ x.val * mapGL ℝ g =
        mapGL ℝ g' * heckeMatrix ℓ (affinePerm g hc x).val := by
  have hNℓ : NeZero ℓ := ⟨hℓ⟩
  have hcN : ((g 1 0 : ℤ) : ZMod N) = 0 := by simpa using Gamma0_mem.mp hg
  have hNc : (N : ℤ) ∣ g 1 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hcN
  have had : ((g 0 0 : ℤ) : ZMod ℓ) * ((g 1 1 : ℤ) : ZMod ℓ) = 1 := by
    have := congrArg (Int.cast : ℤ → ZMod ℓ) (det_eq g)
    push_cast at this
    rw [hc] at this
    linear_combination this
  set y : ZMod ℓ := affinePerm g hc x with hy
  obtain ⟨e, he⟩ : (ℓ : ℤ) ∣ g 0 1 + x.val * g 1 1 - y.val * (g 0 0 + x.val * g 1 0) := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val, hc, hy, affinePerm_apply]
    linear_combination (-(((g 0 1 : ℤ) : ZMod ℓ)) - x * ((g 1 1 : ℤ) : ZMod ℓ)) * had
  obtain ⟨g', hc', hd', hmul⟩ := heckeMatrix_mul_of_eq hℓ g x.val y.val e (by linear_combination he)
  refine ⟨g', ?_, ?_, hmul⟩
  · rw [hc']
    exact dvd_mul_of_dvd_right hNc _
  · rw [hd']
    push_cast
    rw [hcN, zero_mul, sub_zero]

/-- A `Γ₀(N)`-slash-eigenvector for the eigenvalue `C` is one for `U_ℓ` when `ℓ ∣ N`, provided the
eigenvalue depends on `γ` only through its `1 1` entry mod `N` (the Nebentypus case). -/
theorem heckeU_slash_eq_smul {N ℓ : ℕ} (hℓN : ℓ ∣ N) (k : ℤ) (f : ℍ → ℂ) (g : SL(2, ℤ))
    (hg : g ∈ Gamma0 N) (C : ℂ)
    (hf : ∀ g' : SL(2, ℤ), (N : ℤ) ∣ g' 1 0 → ((g' 1 1 : ℤ) : ZMod N) = ((g 1 1 : ℤ) : ZMod N) →
      f ∣[k] mapGL ℝ g' = C • f) :
    (heckeU k ℓ f) ∣[k] mapGL ℝ g = C • heckeU k ℓ f := by
  rcases eq_or_ne ℓ 0 with rfl | hℓ
  · simp
  have hNℓ : NeZero ℓ := ⟨hℓ⟩
  have hcℓ : ((g 1 0 : ℤ) : ZMod ℓ) = 0 := by
    have hc : ((g 1 0 : ℤ) : ZMod N) = 0 := by simpa using Gamma0_mem.mp hg
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hc ⊢
    exact dvd_trans (Int.natCast_dvd_natCast.mpr hℓN) hc
  rw [heckeU_eq_sum_zmod, SlashAction.sum_slash, Finset.smul_sum]
  calc ∑ x : ZMod ℓ, (f ∣[k] heckeMatrix ℓ x.val) ∣[k] mapGL ℝ g
      = ∑ x : ZMod ℓ, C • f ∣[k] heckeMatrix ℓ (affinePerm g hcℓ x).val := by
        refine Finset.sum_congr rfl fun x _ => ?_
        obtain ⟨g', hc', hd', hmul⟩ := exists_cocycle hℓ g hg (hc := hcℓ) x
        rw [← SlashAction.slash_mul, hmul, SlashAction.slash_mul, hf g' hc' hd', smul_slash,
          σ_heckeMatrix]
        rfl
    _ = ∑ x : ZMod ℓ, C • f ∣[k] heckeMatrix ℓ x.val :=
        Equiv.sum_comp (affinePerm g hcℓ) (fun x ↦ C • f ∣[k] heckeMatrix ℓ x.val)

variable {N : ℕ} {k : ℤ}

/-- The same-level `U_ℓ` of a `Γ₁(N)`-cusp form, as a bundled cusp form. -/
def heckeUForm [NeZero N] {ℓ : ℕ} (hℓN : ℓ ∣ N) (f : CuspForm Γ₁(N) k) :
    CuspForm Γ₁(N) k where
  toFun := heckeU k ℓ ⇑f
  slash_action_eq' := by
    intro A hA
    obtain ⟨γ, hγ, rfl⟩ := hA
    have h1 := heckeU_slash_eq_smul hℓN k (⇑f) γ (Gamma1_in_Gamma0 N hγ) 1 (fun g' hc' hd' => by
      rw [one_smul]
      have hdγ : ((γ 1 1 : ℤ) : ZMod N) = 1 := by simpa using ((Gamma1_mem N γ).mp hγ).2.1
      exact SlashInvariantFormClass.slash_action_eq f _
        (Subgroup.mem_map_of_mem _ (mem_Gamma1_of hc' (hd'.trans hdγ))))
    rwa [one_smul] at h1
  holo' := ModularForm.mdifferentiable_heckeU f.holo' k ℓ
  zero_at_cusps' := fun hc => CuspFormClass.isZeroAt_heckeU f ℓ hc

theorem coe_heckeUForm [NeZero N] {ℓ : ℕ} (hℓN : ℓ ∣ N) (f : CuspForm Γ₁(N) k) :
    (⇑(heckeUForm hℓN f) : ℍ → ℂ) = heckeU k ℓ ⇑f := rfl

theorem one_mem_strictPeriods (L : ℕ) : (1 : ℝ) ∈ (Γ₁(L)).strictPeriods := by
  rw [strictPeriods_Gamma1]
  exact AddSubgroup.mem_zmultiples 1

theorem qCoeff_heckeUForm [NeZero N] {ℓ : ℕ} (hℓN : ℓ ∣ N) (f : CuspForm Γ₁(N) k)
    (n : ℕ) :
    ModularFormClass.qCoeff (⇑(heckeUForm hℓN f)) n = ModularFormClass.qCoeff (⇑f) (ℓ * n) := by
  have hℓ : ℓ ≠ 0 := fun h0 => (NeZero.ne N) (Nat.eq_zero_of_zero_dvd (h0 ▸ hℓN))
  rw [coe_heckeUForm, ModularFormClass.qCoeff_heckeU f (one_mem_strictPeriods N) hℓ n,
    coeffHeckeU_apply, mul_comm]

theorem denom_mapGL (γ : SL(2, ℤ)) (τ : ℍ) :
    denom (mapGL ℝ γ : GL (Fin 2) ℝ) τ = ((γ 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((γ 1 1 : ℤ) : ℂ) := by
  simp [denom]

theorem slash_mapGL_apply (F : ℍ → ℂ) (γ : SL(2, ℤ)) (τ : ℍ) :
    (F ∣[k] (mapGL ℝ γ : GL (Fin 2) ℝ)) τ
      = F (γ • τ) * (((γ 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((γ 1 1 : ℤ) : ℂ)) ^ (-k) := by
  have := ModularForm.SL_slash_apply (f := F) (k := k) γ τ
  rw [ModularForm.SL_slash] at this
  convert this using 2
  rfl
  rfl

theorem J_ne_zero (γ : SL(2, ℤ)) (τ : ℍ) :
    ((γ 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((γ 1 1 : ℤ) : ℂ) ≠ 0 := by
  rw [← denom_mapGL]
  exact denom_ne_zero _ τ

theorem slash_eq_smul_of_hasNebentypus {ε : DirichletCharacter ℂ N} {f : CuspForm Γ₁(N) k}
    (hf : CuspForm.HasNebentypus ε f) (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 N) :
    (⇑f : ℍ → ℂ) ∣[k] (mapGL ℝ γ : GL (Fin 2) ℝ) = ε ((γ 1 1 : ℤ) : ZMod N) • (⇑f : ℍ → ℂ) := by
  funext τ
  rw [slash_mapGL_apply, hf γ hγ τ, Pi.smul_apply, smul_eq_mul]
  have hJ := zpow_ne_zero k (J_ne_zero γ τ)
  rw [zpow_neg]
  field_simp

theorem hasNebentypus_of_slash_eq_smul {ε : DirichletCharacter ℂ N} {F : CuspForm Γ₁(N) k}
    (hF : ∀ γ : SL(2, ℤ), γ ∈ Gamma0 N →
      (⇑F : ℍ → ℂ) ∣[k] (mapGL ℝ γ : GL (Fin 2) ℝ) = ε ((γ 1 1 : ℤ) : ZMod N) • (⇑F : ℍ → ℂ)) :
    CuspForm.HasNebentypus ε F := by
  intro γ hγ τ
  have hpt := congrFun (hF γ hγ) τ
  rw [slash_mapGL_apply, Pi.smul_apply, smul_eq_mul] at hpt
  have hJ := J_ne_zero γ τ
  have hzk : (((γ 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((γ 1 1 : ℤ) : ℂ)) ^ (-k) ≠ 0 := zpow_ne_zero _ hJ
  have key : F (γ • τ) = ε ((γ 1 1 : ℤ) : ZMod N) * F τ *
      ((((γ 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((γ 1 1 : ℤ) : ℂ)) ^ (-k))⁻¹ := by
    rw [eq_mul_inv_iff_mul_eq₀ hzk]
    exact hpt
  rw [key, ← zpow_neg, neg_neg]
  ring

theorem hasNebentypus_heckeUForm [NeZero N] {ℓ : ℕ} (hℓN : ℓ ∣ N)
    {ε : DirichletCharacter ℂ N} {f : CuspForm Γ₁(N) k} (hf : CuspForm.HasNebentypus ε f) :
    CuspForm.HasNebentypus ε (heckeUForm hℓN f) := by
  refine hasNebentypus_of_slash_eq_smul fun γ hγ => ?_
  rw [coe_heckeUForm]
  refine heckeU_slash_eq_smul hℓN k (⇑f) γ hγ _ fun g' hc' hd' => ?_
  have hg'0 : g' ∈ Gamma0 N := Gamma0_mem.mpr ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hc')
  rw [slash_eq_smul_of_hasNebentypus hf g' hg'0, hd']

end HeckeUGamma1

/-! ## Row B — level lowering

Transcribed from `P2M/Sol/S_CuspForm_exists_gamma1_div_coe_eq_heckeU_of_dvd_div.lean`. The pin's
`mapGL_apply`, `det_entries`, `denom_SL`, `SL_slash_apply'`, `denom_SL_ne_zero`, `isUnit_entry` are
the port's `mapGL_apply`, `det_eq`, `denom_mapGL`, `slash_mapGL_apply`, `J_ne_zero` (row A) and
`ModularForm.Level.isUnit_d`, so they are not re-stated; the pin's `sum_slash` is mathlib's
`SlashAction.sum_slash`, and the two `neb` lemmas are row A's. -/

section ULowerGamma1

theorem val_mapGL_eq (g : SL(2, ℤ)) :
    ((Matrix.SpecialLinearGroup.mapGL ℝ g : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)
      = !![((g 0 0 : ℤ) : ℝ), ((g 0 1 : ℤ) : ℝ); ((g 1 0 : ℤ) : ℝ), ((g 1 1 : ℤ) : ℝ)] := by
  ext i j
  rw [mapGL_apply]
  fin_cases i <;> fin_cases j <;> rfl

section Cocycle

variable {ℓ : ℕ}

def cocycleMat (ℓ : ℕ) (γ : SL(2, ℤ)) (j j' b' : ℤ) : Matrix (Fin 2) (Fin 2) ℤ :=
  !![γ 0 0 + j * γ 1 0, b'; ℓ * γ 1 0, γ 1 1 - γ 1 0 * j']

theorem det_cocycleMat (γ : SL(2, ℤ)) {j j' b' : ℤ}
    (hb' : (ℓ : ℤ) * b' = γ 0 1 + j * γ 1 1 - (γ 0 0 + j * γ 1 0) * j') :
    (cocycleMat ℓ γ j j' b').det = 1 := by
  rw [cocycleMat, Matrix.det_fin_two_of]
  linear_combination (-(γ 1 0)) * hb' + det_eq γ

def cocycleSL (ℓ : ℕ) (γ : SL(2, ℤ)) (j j' b' : ℤ)
    (hb' : (ℓ : ℤ) * b' = γ 0 1 + j * γ 1 1 - (γ 0 0 + j * γ 1 0) * j') : SL(2, ℤ) :=
  ⟨cocycleMat ℓ γ j j' b', det_cocycleMat γ hb'⟩

theorem cocycleSL_apply (γ : SL(2, ℤ)) (j j' b' : ℤ)
    (hb' : (ℓ : ℤ) * b' = γ 0 1 + j * γ 1 1 - (γ 0 0 + j * γ 1 0) * j') (i i' : Fin 2) :
    (cocycleSL ℓ γ j j' b' hb') i i' = cocycleMat ℓ γ j j' b' i i' := rfl

theorem cocycleSL_00 (γ : SL(2, ℤ)) (j j' b' : ℤ) (hb') :
    (cocycleSL ℓ γ j j' b' hb') 0 0 = γ 0 0 + j * γ 1 0 := by
  rw [cocycleSL_apply]
  rfl

theorem cocycleSL_01 (γ : SL(2, ℤ)) (j j' b' : ℤ) (hb') :
    (cocycleSL ℓ γ j j' b' hb') 0 1 = b' := by
  rw [cocycleSL_apply]
  rfl

theorem cocycleSL_10 (γ : SL(2, ℤ)) (j j' b' : ℤ) (hb') :
    (cocycleSL ℓ γ j j' b' hb') 1 0 = ℓ * γ 1 0 := by
  rw [cocycleSL_apply]
  rfl

theorem cocycleSL_11 (γ : SL(2, ℤ)) (j j' b' : ℤ) (hb') :
    (cocycleSL ℓ γ j j' b' hb') 1 1 = γ 1 1 - γ 1 0 * j' := by
  rw [cocycleSL_apply]
  rfl

theorem heckeMatrix_mul_eq (hℓ : ℓ ≠ 0) (γ : SL(2, ℤ)) (j j' : ℕ) (b' : ℤ)
    (hb' : (ℓ : ℤ) * b' = γ 0 1 + j * γ 1 1 - (γ 0 0 + j * γ 1 0) * j') :
    heckeMatrix ℓ j * (Matrix.SpecialLinearGroup.mapGL ℝ γ : GL (Fin 2) ℝ)
      = (Matrix.SpecialLinearGroup.mapGL ℝ (cocycleSL ℓ γ j j' b' hb') : GL (Fin 2) ℝ)
          * heckeMatrix ℓ j' := by
  have hb'R : (ℓ : ℝ) * (b' : ℝ) = γ 0 1 + j * γ 1 1 - (γ 0 0 + j * γ 1 0) * j' := by
    exact_mod_cast hb'
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, val_heckeMatrix hℓ, val_heckeMatrix hℓ, val_mapGL_eq,
    val_mapGL_eq, cocycleSL_00, cocycleSL_01, cocycleSL_10, cocycleSL_11]
  push_cast
  simp only [Matrix.mul_fin_two]
  ext i i'
  fin_cases i <;> fin_cases i'
  · simp
  · simp; linear_combination -hb'R
  · simp
  · simp; ring

end Cocycle

section Residues

variable {ℓ : ℕ}

def perm (ℓ : ℕ) (γ : SL(2, ℤ)) (r : ZMod ℓ) : ZMod ℓ :=
  (γ 1 1 : ZMod ℓ) * ((γ 0 1 : ZMod ℓ) + r * (γ 1 1 : ZMod ℓ))

def permInv (ℓ : ℕ) (γ : SL(2, ℤ)) (r : ZMod ℓ) : ZMod ℓ :=
  (γ 0 0 : ZMod ℓ) * ((γ 0 0 : ZMod ℓ) * r - (γ 0 1 : ZMod ℓ))

theorem ad_eq_one {γ : SL(2, ℤ)} (hc : (ℓ : ℤ) ∣ γ 1 0) :
    (γ 0 0 : ZMod ℓ) * (γ 1 1 : ZMod ℓ) = 1 := by
  have hc0 : ((γ 1 0 : ℤ) : ZMod ℓ) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hc
  have := congrArg (Int.cast : ℤ → ZMod ℓ) (det_eq γ)
  push_cast at this
  rwa [hc0, mul_zero, sub_zero] at this

theorem permInv_perm {γ : SL(2, ℤ)} (hc : (ℓ : ℤ) ∣ γ 1 0) (r : ZMod ℓ) :
    permInv ℓ γ (perm ℓ γ r) = r := by
  have h := ad_eq_one hc
  unfold perm permInv
  linear_combination ((γ 0 0 : ZMod ℓ) * (γ 0 1 : ZMod ℓ)
    + r * ((γ 0 0 : ZMod ℓ) * (γ 1 1 : ZMod ℓ) + 1)) * h

theorem perm_permInv {γ : SL(2, ℤ)} (hc : (ℓ : ℤ) ∣ γ 1 0) (r : ZMod ℓ) :
    perm ℓ γ (permInv ℓ γ r) = r := by
  have h := ad_eq_one hc
  unfold perm permInv
  linear_combination (r * ((γ 0 0 : ZMod ℓ) * (γ 1 1 : ZMod ℓ) + 1)
    - (γ 1 1 : ZMod ℓ) * (γ 0 1 : ZMod ℓ)) * h

theorem dvd_numerator [NeZero ℓ] {γ : SL(2, ℤ)} (hc : (ℓ : ℤ) ∣ γ 1 0) (j : ℕ) :
    (ℓ : ℤ) ∣ γ 0 1 + j * γ 1 1 - (γ 0 0 + j * γ 1 0) * ((perm ℓ γ (j : ZMod ℓ)).val : ℤ) := by
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  have hc0 : ((γ 1 0 : ℤ) : ZMod ℓ) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hc
  have h := ad_eq_one hc
  push_cast
  rw [ZMod.natCast_zmod_val, hc0, perm]
  linear_combination (-((γ 0 1 : ZMod ℓ) + (j : ZMod ℓ) * (γ 1 1 : ZMod ℓ))) * h

end Residues

section Main

variable {N : ℕ} {k : ℤ} {ℓ : ℕ}

theorem heckeU_slash_of_mem_Gamma0_div (hℓN : ℓ ∣ N) (hℓ : ℓ ∣ N / ℓ) (hℓ0 : ℓ ≠ 0)
    (ε' : DirichletCharacter ℂ (N / ℓ)) (F : ℍ → ℂ)
    (hF : ∀ γ' : SL(2, ℤ), γ' ∈ Gamma0 N →
      F ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ γ' : GL (Fin 2) ℝ)
        = ε' ((γ' 1 1 : ℤ) : ZMod (N / ℓ)) • F)
    {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 (N / ℓ)) :
    heckeU k ℓ F ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ γ : GL (Fin 2) ℝ)
      = ε' ((γ 1 1 : ℤ) : ZMod (N / ℓ)) • heckeU k ℓ F := by
  have hNℓ : NeZero ℓ := ⟨hℓ0⟩
  have hLc : ((N / ℓ : ℕ) : ℤ) ∣ γ 1 0 := by
    have := Gamma0_mem.mp hγ
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp this
  have hc : (ℓ : ℤ) ∣ γ 1 0 := (Int.natCast_dvd_natCast.mpr hℓ).trans hLc

  have hdata : ∀ j : ℕ, ∃ b' : ℤ,
      (ℓ : ℤ) * b' = γ 0 1 + j * γ 1 1 - (γ 0 0 + j * γ 1 0) * ((perm ℓ γ (j : ZMod ℓ)).val : ℤ) :=
    fun j => ⟨_, Int.mul_ediv_cancel' (dvd_numerator hc j)⟩
  choose b' hb' using hdata

  have hterm : ∀ j : ℕ, (F ∣[k] heckeMatrix ℓ j) ∣[k] (mapGL ℝ γ : GL (Fin 2) ℝ)
      = ε' ((γ 1 1 : ℤ) : ZMod (N / ℓ)) • (F ∣[k] heckeMatrix ℓ (perm ℓ γ (j : ZMod ℓ)).val) := by
    intro j
    set γ' := cocycleSL ℓ γ j ((perm ℓ γ (j : ZMod ℓ)).val) (b' j) (hb' j) with hγ'
    have hγ'0 : γ' ∈ Gamma0 N := by
      rw [Gamma0_mem, hγ', cocycleSL_10, ZMod.intCast_zmod_eq_zero_iff_dvd]
      obtain ⟨t, ht⟩ := hLc
      rw [ht, ← mul_assoc, ← Nat.cast_mul, Nat.mul_div_cancel' hℓN]
      exact dvd_mul_right _ _
    rw [← SlashAction.slash_mul, heckeMatrix_mul_eq hℓ0 γ j _ (b' j) (hb' j), SlashAction.slash_mul,
      ← hγ', hF γ' hγ'0, smul_slash, σ_heckeMatrix]
    simp only [ContinuousAlgEquiv.refl_apply]
    congr 1
    congr 1
    rw [hγ', cocycleSL_11]
    push_cast
    have : ((γ 1 0 : ℤ) : ZMod (N / ℓ)) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hLc
    rw [this, zero_mul, sub_zero]

  rw [ModularForm.heckeU_def, SlashAction.sum_slash]
  simp_rw [hterm]
  rw [← Finset.smul_sum]
  congr 1
  symm
  refine Finset.sum_nbij' (fun j => (permInv ℓ γ (j : ZMod ℓ)).val)
    (fun j => (perm ℓ γ (j : ZMod ℓ)).val) ?_ ?_ ?_ ?_ ?_
  · intro j _; exact Finset.mem_range.mpr (ZMod.val_lt _)
  · intro j _; exact Finset.mem_range.mpr (ZMod.val_lt _)
  · intro j hj
    simp only [ZMod.natCast_val, ZMod.cast_id', id_eq, perm_permInv hc]
    exact ZMod.val_cast_of_lt (Finset.mem_range.mp hj)
  · intro j hj
    simp only [ZMod.natCast_val, ZMod.cast_id', id_eq, permInv_perm hc]
    exact ZMod.val_cast_of_lt (Finset.mem_range.mp hj)
  · intro j hj
    simp only [ZMod.natCast_val, ZMod.cast_id', id_eq, perm_permInv hc]
    rw [ZMod.val_cast_of_lt (Finset.mem_range.mp hj)]

/-- The pin's local `hF` in `lowerForm`/`main`: at level `N` the Nebentypus
`changeLevel ε'` of `f` is the level-`N/ℓ` character `ε'` evaluated at the `1 1` entry. -/
private theorem slash_eq_smul_changeLevel (hℓN : ℓ ∣ N) (ε' : DirichletCharacter ℂ (N / ℓ))
    {f : CuspForm Γ₁(N) k}
    (hf : CuspForm.HasNebentypus
      (DirichletCharacter.changeLevel (Nat.div_dvd_of_dvd hℓN) ε') f)
    {γ' : SL(2, ℤ)} (hγ' : γ' ∈ Gamma0 N) :
    (⇑f : ℍ → ℂ) ∣[k] (mapGL ℝ γ' : GL (Fin 2) ℝ)
      = ε' ((γ' 1 1 : ℤ) : ZMod (N / ℓ)) • (⇑f : ℍ → ℂ) := by
  rw [slash_eq_smul_of_hasNebentypus hf γ' hγ']
  congr 1
  have hu := ModularForm.Level.isUnit_d hγ'
  rw [← hu.unit_spec, DirichletCharacter.changeLevel_eq_cast_of_dvd ε' (Nat.div_dvd_of_dvd hℓN),
    hu.unit_spec, ZMod.cast_intCast (Nat.div_dvd_of_dvd hℓN)]

variable [NeZero N]

theorem neZero_div (hℓN : ℓ ∣ N) : NeZero (N / ℓ) := by
  refine ⟨fun h => ?_⟩
  rcases Nat.eq_zero_or_pos ℓ with rfl | hpos
  · exact NeZero.ne N (zero_dvd_iff.mp hℓN)
  · exact NeZero.ne N (Nat.eq_zero_of_dvd_of_div_eq_zero hℓN h)

def lowerForm (hℓN : ℓ ∣ N) (hℓ : ℓ ∣ N / ℓ) (ε' : DirichletCharacter ℂ (N / ℓ))
    (f : CuspForm Γ₁(N) k)
    (hf : CuspForm.HasNebentypus (DirichletCharacter.changeLevel (Nat.div_dvd_of_dvd hℓN) ε') f) :
    CuspForm Γ₁(N / ℓ) k :=
  haveI : NeZero (N / ℓ) := neZero_div hℓN
  have hℓ0 : ℓ ≠ 0 := fun h => NeZero.ne N (zero_dvd_iff.mp (h ▸ hℓN))
  { toFun := heckeU k ℓ ⇑f
    slash_action_eq' := by
      intro A hA
      obtain ⟨γ, hγ, rfl⟩ := hA
      have hγ0 : γ ∈ Gamma0 (N / ℓ) := Gamma1_in_Gamma0 (N / ℓ) hγ
      have hd : ((γ 1 1 : ℤ) : ZMod (N / ℓ)) = 1 := (Gamma1_mem (N / ℓ) γ |>.mp hγ).2.1
      rw [heckeU_slash_of_mem_Gamma0_div hℓN hℓ hℓ0 ε' ⇑f
        (fun γ' hγ' => slash_eq_smul_changeLevel hℓN ε' hf hγ') hγ0, hd, map_one, one_smul]
    holo' := ModularForm.mdifferentiable_heckeU f.holo' k ℓ
    zero_at_cusps' := by
      intro c hc
      refine CuspFormClass.isZeroAt_heckeU f ℓ ?_
      rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc ⊢
      exact hc }

theorem coe_lowerForm (hℓN : ℓ ∣ N) (hℓ : ℓ ∣ N / ℓ)
    (ε' : DirichletCharacter ℂ (N / ℓ)) (f : CuspForm Γ₁(N) k)
    (hf : CuspForm.HasNebentypus (DirichletCharacter.changeLevel (Nat.div_dvd_of_dvd hℓN) ε') f) :
    (⇑(lowerForm hℓN hℓ ε' f hf) : ℍ → ℂ) = heckeU k ℓ ⇑f := rfl

end Main

end ULowerGamma1

theorem exists_gamma1_coe_eq_heckeU_of_dvd
    {N : ℕ} [NeZero N] (k : ℤ) {ℓ : ℕ} (hℓ : ℓ ∣ N) (f : CuspForm (Gamma1 N) k) :
    ∃ U : CuspForm (Gamma1 N) k,
      (⇑U : UpperHalfPlane → ℂ) = ModularForm.heckeU k ℓ ⇑f ∧
      (∀ n : ℕ, ModularFormClass.qCoeff U n = ModularFormClass.qCoeff f (ℓ * n)) ∧
      ∀ ε : DirichletCharacter ℂ N, CuspForm.HasNebentypus ε f → CuspForm.HasNebentypus ε U :=
  ⟨heckeUForm hℓ f, coe_heckeUForm hℓ f, qCoeff_heckeUForm hℓ f,
    fun _ hf => hasNebentypus_heckeUForm hℓ hf⟩

theorem exists_gamma1_div_coe_eq_heckeU_of_dvd_div
    {N : ℕ} [NeZero N] (k : ℤ) {ℓ : ℕ} (hℓN : ℓ ∣ N) (hℓ : ℓ ∣ N / ℓ)
    (ε' : DirichletCharacter ℂ (N / ℓ)) (f : CuspForm (Gamma1 N) k)
    (hf : CuspForm.HasNebentypus
      (DirichletCharacter.changeLevel (Nat.div_dvd_of_dvd hℓN) ε') f) :
    ∃ h : CuspForm (Gamma1 (N / ℓ)) k,
      (⇑h : UpperHalfPlane → ℂ) = ModularForm.heckeU k ℓ ⇑f ∧
      (∀ n : ℕ, ModularFormClass.qCoeff h n = ModularFormClass.qCoeff f (ℓ * n)) ∧
      CuspForm.HasNebentypus ε' h := by
  have hℓ0 : ℓ ≠ 0 := fun h => NeZero.ne N (zero_dvd_iff.mp (h ▸ hℓN))
  refine ⟨lowerForm hℓN hℓ ε' f hf, coe_lowerForm hℓN hℓ ε' f hf, fun n => ?_, ?_⟩
  · rw [coe_lowerForm, ModularFormClass.qCoeff_heckeU f (one_mem_strictPeriods N) hℓ0 n,
      coeffHeckeU_apply, mul_comm]
  · refine hasNebentypus_of_slash_eq_smul fun γ hγ => ?_
    rw [coe_lowerForm]
    exact heckeU_slash_of_mem_Gamma0_div hℓN hℓ hℓ0 ε' ⇑f
      (fun γ' hγ' => slash_eq_smul_changeLevel hℓN ε' hf hγ') hγ

end CuspForm
