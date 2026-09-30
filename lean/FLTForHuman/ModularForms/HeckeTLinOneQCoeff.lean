/-
  The `q`-coefficient law of the diamond-twisted `Γ₁` Hecke operator `T_ℓ`, and
  the `Γ₀`-slash compatibility of `T_ℓ`.

  FLT states the coefficient law in `P2M/Sol/S_CuspForm_qCoeff_heckeTLinOne.lean`
  (178 lines; pinned `aa2d8b3`) as the `QExpHeckeTOne` block plus a final
  `solution`, and the slash law in the 22-line
  `P2M/Sol/S_CuspForm_heckeTLinOne_slashOfMemGamma0.lean`. The public targets are
  the `Theorems/` wrappers `Thm_CuspForm_qCoeff_heckeTLinOne.lean` and
  `Thm_CuspForm_heckeTLinOne_slashOfMemGamma0.lean`; the statements below are
  transcribed verbatim from those wrappers.

  All block helpers are `private`: the pin's `T_pow_mem_Gamma1` (the port's public
  copy lives in the heavy `WeightOne` cone, which this module must not import),
  its witness `cusp_slash_T_pow`, the `periodic_smul` used for the dilation, and
  the coefficient identity `qCoeff_heckeU_add_slash`. The remaining vocabulary is
  the shared prelude (`ModularForm.periodic_of_slash_T`,
  `ModularForm.heckeDiagMatrix_mul_T`, `ModularForm.slash_heckeDiagMatrix_slash_T`,
  the two `IsBoundedAtImInfty` slashes, `CuspForm.cusp_periodic`/`cusp_holo`/
  `cusp_bdd`, `ModularForm.HeckeGamma1.mdifferentiable_heckeU`,
  `ModularForm.periodic_heckeU_comp_ofComplex`,
  `ModularForm.isBoundedAtImInfty_heckeU`, `UpperHalfPlane.qCoeff_heckeU`,
  `UpperHalfPlane.qCoeff_comp_heckeDiagMatrix_smul`,
  `ModularForm.coeffHeckeU_apply`, `ModularForm.slash_heckeDiagMatrix_apply` and
  the mathlib `UpperHalfPlane.analyticAt_cuspFunction_zero`/`qExpansion_smul`/
  `qExpansion_add`).
-/
import FLTForHuman.ModularForms.HeckePrelude
import FLTForHuman.ModularForms.HeckeAnalytic
import FLTForHuman.ModularForms.HeckeQCoeff
import FLTForHuman.ModularForms.Level.Diamond
import FLTForHuman.ModularForms.Defs.Gamma1HeckeOperators

set_option autoImplicit false

noncomputable section

open CongruenceSubgroup ModularForm ModularFormClass UpperHalfPlane Filter Function
open scoped MatrixGroups ModularForm

namespace CuspForm

section QExpHeckeTOne

variable {M : ℕ} {k : ℤ} {p : ℕ}

/-- `T ^ n ∈ Γ₁(N)`. Private local copy: the public `WeightOne`-cone copy is not
imported here. -/
private theorem T_pow_mem_Gamma1 (N n : ℕ) : ModularGroup.T ^ n ∈ Gamma1 N := by
  rw [show ModularGroup.T ^ n = ModularGroup.T ^ (n : ℤ) from (zpow_natCast _ n).symm]
  rw [Gamma1_mem, ModularGroup.coe_T_zpow]
  simp

/-- The pin's witness that a `Γ₁(M)`-cusp form is fixed by `T ^ n`. -/
private theorem cusp_slash_T_pow (F : CuspForm (CongruenceSubgroup.Gamma1 M) k) (n : ℕ) :
    (⇑F : ℍ → ℂ) ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ (ModularGroup.T ^ n)) = ⇑F :=
  SlashInvariantFormClass.slash_action_eq F _ (Subgroup.mem_map_of_mem _ (T_pow_mem_Gamma1 M n))

/-- A scalar multiple of a `1`-periodic function is `1`-periodic. -/
private theorem periodic_smul {G : ℍ → ℂ} (hG : Periodic (G ∘ ofComplex) 1) (c : ℂ) :
    Periodic ((c • G) ∘ ofComplex) 1 := by
  intro w
  have h2 := hG w
  simp only [comp_apply, Pi.smul_apply, smul_eq_mul] at h2 ⊢
  rw [h2]

variable (F : CuspForm (CongruenceSubgroup.Gamma1 M) k)

/-- The pin's `qCoeff_heckeU_add_slash`: the coefficient identity behind the
`T_ℓ` law. -/
private theorem qCoeff_heckeU_add_slash (hp : p ≠ 0)
    (G : CuspForm (CongruenceSubgroup.Gamma1 M) k) (n : ℕ) :
    qCoeff (heckeU k p ⇑F + (⇑G) ∣[k] heckeDiagMatrix p) n =
      qCoeff (⇑F) (p * n) +
        (p : ℂ) ^ (k - 1) * (if p ∣ n then qCoeff (⇑G) (n / p) else 0) := by
  have hFper := cusp_periodic F
  have hFhol := cusp_holo F
  have hFbdd := cusp_bdd F
  have hGper := cusp_periodic G
  have hGhol := cusp_holo G
  have hGbdd := cusp_bdd G
  set U : ℍ → ℂ := heckeU k p (⇑F) with hU
  set D : ℍ → ℂ := (⇑G : ℍ → ℂ) ∣[k] heckeDiagMatrix p with hD
  have hUper : Periodic (U ∘ ofComplex) 1 := periodic_heckeU_comp_ofComplex hFper k p
  have hDT : D ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ ModularGroup.T) = D :=
    slash_heckeDiagMatrix_slash_T hp (cusp_slash_T_pow G p)
  have hDper : Periodic (D ∘ ofComplex) 1 := periodic_of_slash_T hDT
  have hUhol : MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) U :=
    ModularForm.HeckeGamma1.mdifferentiable_heckeU hFhol
  have hDhol : MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) D :=
    hGhol.slash k _
  have hUbdd : IsBoundedAtImInfty U := isBoundedAtImInfty_heckeU hFbdd k p
  have hDbdd : IsBoundedAtImInfty D := isBoundedAtImInfty_slash_heckeDiagMatrix hp hGbdd
  have hanU := analyticAt_cuspFunction_zero one_pos hUper hUhol hUbdd
  have hanD := analyticAt_cuspFunction_zero one_pos hDper hDhol hDbdd
  set G' : ℍ → ℂ := fun τ => G (heckeDiagMatrix p • τ) with hG'
  have hDG : D = ((p : ℂ) ^ (k - 1)) • G' := by
    funext τ
    rw [hD, slash_heckeDiagMatrix_apply k hp, Pi.smul_apply, smul_eq_mul]
  have hpk : ((p : ℂ) ^ (k - 1)) ≠ 0 := zpow_ne_zero _ (Nat.cast_ne_zero.mpr hp)
  have hGD : G' = ((p : ℂ) ^ (k - 1))⁻¹ • D := by
    rw [hDG, smul_smul, inv_mul_cancel₀ hpk, one_smul]
  have hanG : AnalyticAt ℂ (cuspFunction 1 G') 0 := by
    rw [hGD]
    exact analyticAt_cuspFunction_zero one_pos (periodic_smul hDper _)
      (MDifferentiable.const_smul _ hDhol) (BoundedAtFilter.smul _ hDbdd)
  have hqD : qCoeff D n = (p : ℂ) ^ (k - 1) * (if p ∣ n then qCoeff (⇑G) (n / p) else 0) := by
    rw [qCoeff, hDG, qExpansion_smul hanG, map_smul, smul_eq_mul]
    congr 1
    exact UpperHalfPlane.qCoeff_comp_heckeDiagMatrix_smul hGper hGhol hGbdd hp n
  have hqU : qCoeff U n = qCoeff (⇑F) (p * n) := by
    rw [hU, UpperHalfPlane.qCoeff_heckeU hFper hFhol hFbdd k hp n, coeffHeckeU_apply, mul_comm]
  rw [qCoeff, qExpansion_add hanU hanD, map_add]
  have h1 := hqU
  have h2 := hqD
  simp only [qCoeff] at h1 h2 ⊢
  rw [h1, h2]

end QExpHeckeTOne

/-- The `q`-coefficient law of `T_ℓ` on `Γ₁(M)`, `ℓ ∤ M`. Stated verbatim from
`Theorems/Thm_CuspForm_qCoeff_heckeTLinOne.lean`. -/
theorem qCoeff_heckeTLinOne {M : ℕ} (k : ℤ) {p : ℕ} (hp : p.Prime) (hpM : ¬ p ∣ M)
    (f : CuspForm (CongruenceSubgroup.Gamma1 M) k) (n : ℕ) :
    ModularFormClass.qCoeff (CuspForm.heckeTLinOne k hp hpM f) n =
      ModularFormClass.qCoeff f (p * n) +
        (p : ℂ) ^ (k - 1) *
          (if p ∣ n then ModularFormClass.qCoeff (CuspForm.diamondLinOne M k p f) (n / p) else 0) := by
  rw [CuspForm.coe_heckeTLinOne_apply]
  exact qCoeff_heckeU_add_slash f hp.ne_zero (CuspForm.diamondLinOne M k p f) n

/-- `T_ℓ` commutes with the `Γ₀(M)`-slash. Stated verbatim from
`Theorems/Thm_CuspForm_heckeTLinOne_slashOfMemGamma0.lean`. -/
theorem heckeTLinOne_slashOfMemGamma0
    {M : ℕ} (k : ℤ) {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M)
    {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 M) (f : CuspForm (Gamma1 M) k) :
    CuspForm.heckeTLinOne k hℓ hℓM (CuspForm.slashOfMemGamma0 M k hγ f) =
      CuspForm.slashOfMemGamma0 M k hγ (CuspForm.heckeTLinOne k hℓ hℓM f) := by
  obtain ⟨σ, hσ⟩ := ModularForm.Level.exists_isDiamondLift_of_coprime (M := M)
    ((Nat.Prime.coprime_iff_not_dvd hℓ).2 hℓM)
  refine DFunLike.ext' ?_
  rw [CuspForm.coe_heckeTLinOne_apply_of_isDiamondLift k hℓ hℓM hσ,
    ModularForm.Level.coe_slashOfMemGamma0, ModularForm.Level.coe_slashOfMemGamma0,
    CuspForm.coe_heckeTLinOne_apply_of_isDiamondLift k hℓ hℓM hσ]
  exact (CuspForm.Gamma1Hecke.heckeU_add_slash_heckeDiagMatrix_slash_of_mem_Gamma0 k hℓ hℓM
    (fun g hg => SlashInvariantFormClass.slash_action_eq f g hg) σ hσ.1 hσ.2 hγ).symm

end CuspForm

end
