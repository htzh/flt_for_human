/-
  The `Γ_H` dictionary: a `Γ_H(M)`-form is a `Γ₁(M)`-form, a nebentypus form is a `Γ_H(M)`-form, the
  `⟨d⟩`/`T_ℓ`/`U_q` action on a nebentypus form, and the `Γ_H`-nebentypus decomposition of the cusp
  space.

  * `CuspForm.exists_gamma1_coe_eq_of_gammaH`: every `Γ_H(M)`-cusp form is a `Γ₁(M)`-cusp form with the
    same underlying function, since `Γ₁(M) ≤ Γ_H(M)`.
  * `CuspForm.exists_gammaH_coe_eq_of_hasNebentypus`: conversely a `Γ₁(M)`-form with a nebentypus `ε`
    that is trivial on `H` is a `Γ_H(M)`-form.
  * `CuspForm.coe_diamondLinH_and_coe_heckeTLinH_and_coe_heckeULinH_of_hasNebentypus`: the underlying
    functions of `diamondLinH d`, `heckeTLinH ℓ` and `heckeULinH q` applied to a nebentypus form, read
    as `ℍ → ℂ` (the `Γ_H` Hecke operators of `ModularForms/Defs/GammaH.lean`).
  * `CuspForm.exists_finset_dirichlet_sum_eq_and_independent_of_gammaH`: the `Γ_H`-nebentypus
    decomposition — a `Γ_H(M)`-form splits as a finite `ε`-indexed sum of its nebentypus components, and
    the components are linearly independent.

  Transcribed from the pin's proof files (pinned `aa2d8b3`)
  `S_CuspForm_exists_gamma1_coe_eq_of_gammaH.lean` (51 lines),
  `S_CuspForm_exists_gammaH_coe_eq_of_hasNebentypus.lean` (68),
  `S_CuspForm_coe_diamondLinH_and_coe_heckeTLinH_and_coe_heckeULinH_of_hasNebentypus.lean` (51) and
  `S_CuspForm_exists_finset_dirichlet_sum_eq_and_independent_of_gammaH.lean` (340), with the statements
  from the wrappers of the same names.  The pin's two private `Γ₁ ≤ Γ_H` lemmas are copied into the
  first two files and are written **once** here; the pin label namespace
  `CuspForm.GammaHNebentypusDecomp` is a word name and is kept.

  Assumes from earlier modules: `ModularForms/Gamma1CuspStructure.lean` (`CohCarrier.GammaH`,
  `CohCarrier.mem_GammaH_iff`, `CohCarrier.gamma0Units`), `ModularForms/Defs/GammaH.lean` (the `Γ_H`
  Hecke operators) and `ModularForms/Defs/PrimitiveFormGamma1.lean`.

  spec-pin: Theorems/Thm_CuspForm_exists_gamma1_coe_eq_of_gammaH.lean
  spec-pin: P2M/Sol/S_CuspForm_exists_gamma1_coe_eq_of_gammaH.lean
  spec-pin: Theorems/Thm_CuspForm_exists_gammaH_coe_eq_of_hasNebentypus.lean
  spec-pin: P2M/Sol/S_CuspForm_exists_gammaH_coe_eq_of_hasNebentypus.lean
  spec-pin: Theorems/Thm_CuspForm_coe_diamondLinH_and_coe_heckeTLinH_and_coe_heckeULinH_of_hasNebentypus.lean
  spec-pin: P2M/Sol/S_CuspForm_coe_diamondLinH_and_coe_heckeTLinH_and_coe_heckeULinH_of_hasNebentypus.lean
  spec-pin: Theorems/Thm_CuspForm_exists_finset_dirichlet_sum_eq_and_independent_of_gammaH.lean
  spec-pin: P2M/Sol/S_CuspForm_exists_finset_dirichlet_sum_eq_and_independent_of_gammaH.lean
-/
import FLTForHuman.ModularForms.Gamma1CuspStructure
import FLTForHuman.ModularForms.Defs.GammaH
import FLTForHuman.ModularForms.Defs.PrimitiveFormGamma1
import FLTForHuman.ModularCurve.Period.HeckeStability
import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
import Mathlib.NumberTheory.ModularForms.QExpansion
import Mathlib.Tactic

set_option autoImplicit false

noncomputable section


open scoped MatrixGroups

private theorem Gamma1_le_GammaH (M : ℕ) (H : Subgroup (ZMod M)ˣ) :
    CongruenceSubgroup.Gamma1 M ≤ CohCarrier.GammaH M H := by
  intro A hA
  rw [CongruenceSubgroup.Gamma1_mem] at hA
  rw [CohCarrier.mem_GammaH_iff]
  have h0 : A ∈ CongruenceSubgroup.Gamma0 M := by rw [CongruenceSubgroup.Gamma0_mem]; exact hA.2.2
  refine ⟨h0, ?_⟩
  have : CohCarrier.gamma0Units M ⟨A, h0⟩ = 1 := by
    ext
    rw [CohCarrier.val_gamma0Units]
    show ((A 1 1 : ℤ) : ZMod M) = ((1 : (ZMod M)ˣ) : ZMod M)
    rw [hA.2.1, Units.val_one]
  rw [this]; exact one_mem H

private theorem Gamma_le_GammaH' (M : ℕ) (H : Subgroup (ZMod M)ˣ) :
    CongruenceSubgroup.Gamma M ≤ CohCarrier.GammaH M H := by
  intro A hA
  rw [CohCarrier.mem_GammaH_iff]
  have hA' := CongruenceSubgroup.Gamma_mem.mp hA
  have h0 : A ∈ CongruenceSubgroup.Gamma0 M := by rw [CongruenceSubgroup.Gamma0_mem]; exact hA'.2.2.1
  refine ⟨h0, ?_⟩
  have : CohCarrier.gamma0Units M ⟨A, h0⟩ = 1 := by
    ext
    rw [CohCarrier.val_gamma0Units]
    show ((A 1 1 : ℤ) : ZMod M) = ((1 : (ZMod M)ˣ) : ZMod M)
    rw [hA'.2.2.2, Units.val_one]
  rw [this]
  exact one_mem H


open scoped MatrixGroups

theorem CuspForm.exists_gamma1_coe_eq_of_gammaH
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (k : ℤ) (f : CuspForm (CohCarrier.GammaH M H) k) :
    ∃ g : CuspForm (CongruenceSubgroup.Gamma1 M) k, (⇑g : UpperHalfPlane → ℂ) = ⇑f := by
  have hle : ((CongruenceSubgroup.Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) ≤
      ((CohCarrier.GammaH M H : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) :=
    Subgroup.map_mono (Gamma1_le_GammaH M H)
  refine ⟨{ toFun := ⇑f
            slash_action_eq' := fun γ hγ => SlashInvariantFormClass.slash_action_eq f γ (hle hγ)
            holo' := CuspFormClass.holo f
            zero_at_cusps' := fun hc => CuspFormClass.zero_at_cusps f
              ((Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z _).mpr
                ((Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z _).mp hc)) }, rfl⟩

open scoped MatrixGroups ModularForm


open scoped MatrixGroups

theorem CuspForm.exists_gammaH_coe_eq_of_hasNebentypus
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (k : ℤ) (ε : DirichletCharacter ℂ M)
    (hε : ∀ d : (ZMod M)ˣ, d ∈ H → ε (d : ZMod M) = 1)
    (g : CuspForm (CongruenceSubgroup.Gamma1 M) k) (hg : CuspForm.HasNebentypus ε g) :
    ∃ f : CuspForm (CohCarrier.GammaH M H) k, (⇑f : UpperHalfPlane → ℂ) = ⇑g := by
  have hinv : ∀ γ ∈ ((CohCarrier.GammaH M H : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)),
      (⇑g) ∣[k] γ = ⇑g := by
    intro γ hγ
    obtain ⟨A, hA, rfl⟩ := Subgroup.mem_map.mp hγ
    obtain ⟨hA0, hAH⟩ := CohCarrier.mem_GammaH_iff.mp hA
    have hεA : ε ((A 1 1 : ℤ) : ZMod M) = 1 := by
      have := hε _ hAH
      rwa [CohCarrier.val_gamma0Units] at this
    funext τ
    show ((⇑g) ∣[k] A) τ = g τ
    rw [ModularForm.SL_slash_apply, hg A hA0 τ, hεA, one_mul]
    have hden : UpperHalfPlane.denom (A : GL (Fin 2) ℝ) τ =
        ((A 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((A 1 1 : ℤ) : ℂ) := by
      simp [UpperHalfPlane.denom]
    rw [hden, mul_comm, ← mul_assoc, ← zpow_add₀ (by
      rw [← hden]; exact UpperHalfPlane.denom_ne_zero _ _), neg_add_cancel, zpow_zero, one_mul]
  refine ⟨{ toFun := ⇑g
            slash_action_eq' := hinv
            holo' := CuspFormClass.holo g
            zero_at_cusps' := fun hc => CuspFormClass.zero_at_cusps g
              ((Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z _).mpr
                ((Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z _).mp hc)) }, rfl⟩

open scoped MatrixGroups ModularForm

private theorem slash_eq_smul_of_hasNebentypus {M : ℕ} {k : ℤ} {ε : DirichletCharacter ℂ M}
    {g : CuspForm (CongruenceSubgroup.Gamma1 M) k} (hg : CuspForm.HasNebentypus ε g)
    (A : SL(2, ℤ)) (hA0 : A ∈ CongruenceSubgroup.Gamma0 M) :
    (⇑g) ∣[k] ((Matrix.SpecialLinearGroup.mapGL ℝ A : GL (Fin 2) ℝ)) = ε ((A 1 1 : ℤ) : ZMod M) • ⇑g := by
  funext τ
  show ((⇑g) ∣[k] A) τ = _
  rw [ModularForm.SL_slash_apply, hg A hA0 τ, Pi.smul_apply, smul_eq_mul]
  have hden : UpperHalfPlane.denom (A : GL (Fin 2) ℝ) τ =
      ((A 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((A 1 1 : ℤ) : ℂ) := by
    simp [UpperHalfPlane.denom]
  have hne : ((A 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((A 1 1 : ℤ) : ℂ) ≠ 0 := by
    rw [← hden]; exact UpperHalfPlane.denom_ne_zero _ _
  rw [hden, mul_assoc, mul_assoc, mul_comm (_ ^ k), mul_assoc, ← zpow_add₀ hne, neg_add_cancel, zpow_zero,
    mul_one]


open scoped MatrixGroups ModularForm

theorem CuspForm.coe_diamondLinH_and_coe_heckeTLinH_and_coe_heckeULinH_of_hasNebentypus
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (k : ℤ) (ε : DirichletCharacter ℂ M)
    (f : CuspForm (CohCarrier.GammaH M H) k) (g : CuspForm (CongruenceSubgroup.Gamma1 M) k)
    (hfg : (⇑f : UpperHalfPlane → ℂ) = ⇑g) (hg : CuspForm.HasNebentypus ε g) :
    (∀ d : (ZMod M)ˣ, (⇑(CuspForm.diamondLinH k d f) : UpperHalfPlane → ℂ) = ε (d : ZMod M) • ⇑g) ∧
    (∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M),
      haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
      (⇑(CuspForm.heckeTLinH k hℓ hℓM f) : UpperHalfPlane → ℂ) =
        ModularForm.heckeU k ℓ ⇑g + ε (ℓ : ZMod M) • ((⇑g) ∣[k] ModularForm.heckeDiagMatrix ℓ)) ∧
    (∀ (q : ℕ), q.Prime → q ∣ M →
      (⇑(CuspForm.heckeULinH k q f) : UpperHalfPlane → ℂ) = ModularForm.heckeU k q ⇑g) := by
  refine ⟨fun d => ?_, fun ℓ hℓ hℓM => ?_, fun q hq hqM => ?_⟩
  · rw [CuspForm.coe_diamondLinH_apply k (CuspForm.stableD M H k) d f, hfg,
      slash_eq_smul_of_hasNebentypus hg _ (CohCarrier.gammaLift M d).2]
    congr 2
    have := congrArg (fun u : (ZMod M)ˣ => (u : ZMod M)) (CohCarrier.gamma0Units_gammaLift (M := M) d)
    simp only [CohCarrier.val_gamma0Units] at this
    exact this
  · have : NeZero ℓ := ⟨hℓ.ne_zero⟩
    rw [CuspForm.coe_heckeTLinH_apply k hℓ hℓM (CuspForm.stableT M H k hℓ hℓM) f, hfg, SlashAction.slash_mul,
      slash_eq_smul_of_hasNebentypus hg _ (CohCarrier.gammaLift M _).2, CohCarrier.gammaLift_apply_11 hℓ hℓM]
    congr 1
    simp only [ModularForm.smul_slash, ModularForm.σ_heckeDiagMatrix, ContinuousAlgEquiv.refl_apply]
  · rw [CuspForm.coe_heckeULinH_apply k (CuspForm.stableU M H k hq hqM) f, hfg]

namespace CuspForm
namespace GammaHNebentypusDecomp
open CuspForm
open CongruenceSubgroup ModularForm
open scoped MatrixGroups ModularForm

variable {M : ℕ} {H : Subgroup (ZMod M)ˣ}

private abbrev dd (γ : SL(2, ℤ)) : ZMod M := ((γ 1 1 : ℤ) : ZMod M)

private theorem det_mod (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M) :
    ((γ 0 0 : ℤ) : ZMod M) * ((γ 1 1 : ℤ) : ZMod M) = 1 := by
  have hc : ((γ 1 0 : ℤ) : ZMod M) = 0 := by simpa using Gamma0_mem.mp hγ
  have h := γ.det_coe
  rw [Matrix.det_fin_two] at h
  have := congrArg (Int.cast : ℤ → ZMod M) h
  push_cast at this
  rw [hc] at this
  linear_combination this

private theorem dd_mul {γ₁ γ₂ : SL(2, ℤ)} (h₁ : γ₁ ∈ Gamma0 M) (h₂ : γ₂ ∈ Gamma0 M) :
    dd (M := M) (γ₁ * γ₂) = dd (M := M) γ₁ * dd γ₂ := by
  have := map_mul (Gamma0Map M) ⟨γ₁, h₁⟩ ⟨γ₂, h₂⟩
  exact this

private theorem isUnit_dd {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 M) : IsUnit (dd (M := M) γ) := IsUnit.of_mul_eq_one _ (by rw [mul_comm]; exact det_mod γ hγ)

private theorem val_gamma0Units_eq_dd {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 M) :
    ((CohCarrier.gamma0Units M ⟨γ, hγ⟩ : (ZMod M)ˣ) : ZMod M) = dd γ := rfl

private theorem mem_GammaH_of_dd_eq {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 M) {u : (ZMod M)ˣ} (hu : u ∈ H)
    (h : dd (M := M) γ = (u : ZMod M)) : γ ∈ CohCarrier.GammaH M H := by
  rw [CohCarrier.mem_GammaH_iff]
  refine ⟨hγ, ?_⟩
  have : CohCarrier.gamma0Units M ⟨γ, hγ⟩ = u := Units.ext (by rw [val_gamma0Units_eq_dd, h])
  rw [this]
  exact hu

private theorem mul_inv_mem_GammaH {γ₁ γ₂ : SL(2, ℤ)} (h₁ : γ₁ ∈ Gamma0 M) (h₂ : γ₂ ∈ Gamma0 M)
    (h : dd (M := M) γ₁ = dd γ₂) : γ₂ * γ₁⁻¹ ∈ CohCarrier.GammaH M H := by
  have hmem : γ₂ * γ₁⁻¹ ∈ Gamma0 M := mul_mem h₂ (inv_mem h₁)
  refine mem_GammaH_of_dd_eq hmem (one_mem H) ?_
  have hprod : dd (M := M) (γ₂ * γ₁⁻¹) * dd (M := M) γ₁ = dd γ₂ := by
    rw [← dd_mul hmem h₁, inv_mul_cancel_right]
  rw [h] at hprod
  rw [Units.val_one]
  exact (isUnit_dd h₂).mul_left_injective (hprod.trans (one_mul _).symm)

private theorem exists_lift (u : (ZMod M)ˣ) [NeZero M] :
    ∃ σ : SL(2, ℤ), σ ∈ Gamma0 M ∧ dd (M := M) σ = (u : ZMod M) := by
  have hn : (u : ZMod M).val.Coprime M := ZMod.val_coe_unit_coprime u
  obtain ⟨a, b, hab⟩ : IsCoprime ((u : ZMod M).val : ℤ) (M : ℤ) := Nat.isCoprime_iff_coprime.mpr hn
  let σ : SL(2, ℤ) := ⟨!![a, -b; (M : ℤ), ((u : ZMod M).val : ℤ)], by
    rw [Matrix.det_fin_two_of]; linear_combination hab⟩
  refine ⟨σ, ?_, ?_⟩
  · rw [CongruenceSubgroup.Gamma0_mem]
    dsimp only [σ]
    simp
  · dsimp only [σ]
    simp [dd]

private theorem finiteIndex_GammaH [NeZero M] : (CohCarrier.GammaH M H).FiniteIndex := Subgroup.finiteIndex_of_le (_root_.Gamma_le_GammaH' M H)

section Slash

variable {k : ℤ}

private theorem sl_slash (f : UpperHalfPlane → ℂ) (γ : SL(2, ℤ)) :
    f ∣[k] γ = f ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ γ : GL (Fin 2) ℝ) := rfl

private theorem slash_mem (g : CuspForm (CohCarrier.GammaH M H) k) {γ : SL(2, ℤ)}
    (hγ : γ ∈ CohCarrier.GammaH M H) :
    (⇑g : UpperHalfPlane → ℂ) ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ γ : GL (Fin 2) ℝ) = ⇑g := SlashInvariantFormClass.slash_action_eq g _ (Subgroup.mem_map_of_mem _ hγ)

private theorem slash_eq_of_dd_eq (g : CuspForm (CohCarrier.GammaH M H) k) {σ σ' : SL(2, ℤ)}
    (hσ : σ ∈ Gamma0 M) (hσ' : σ' ∈ Gamma0 M) (h : dd (M := M) σ = dd σ') :
    (⇑g : UpperHalfPlane → ℂ) ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ σ : GL (Fin 2) ℝ)
      = (⇑g : UpperHalfPlane → ℂ) ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ σ' : GL (Fin 2) ℝ) := by
  have hmem : σ' * σ⁻¹ ∈ CohCarrier.GammaH M H := mul_inv_mem_GammaH hσ hσ' h
  conv_rhs => rw [show σ' = (σ' * σ⁻¹) * σ by rw [inv_mul_cancel_right], map_mul,
    SlashAction.slash_mul, slash_mem g hmem]

end Slash

section Diamond

variable [NeZero M] {k : ℤ}

private def diamond (σ : SL(2, ℤ)) (hσ : σ ∈ Gamma0 M) :
    CuspForm (CohCarrier.GammaH M H) k →ₗ[ℂ] CuspForm (CohCarrier.GammaH M H) k where
  toFun g :=
    { toFun := (⇑g : UpperHalfPlane → ℂ) ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ σ : GL (Fin 2) ℝ)
      slash_action_eq' := by
        intro A hA
        obtain ⟨γ, hγ, rfl⟩ := hA
        change ((⇑g : UpperHalfPlane → ℂ) ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ σ : GL (Fin 2) ℝ)) ∣[k]
          (Matrix.SpecialLinearGroup.mapGL ℝ γ : GL (Fin 2) ℝ) = _
        have hconj : σ * γ * σ⁻¹ ∈ CohCarrier.GammaH M H :=
          CohCarrier.conj_mem_GammaH M H ⟨σ, hσ⟩ ⟨γ, hγ⟩
        rw [← SlashAction.slash_mul, ← map_mul,
          show σ * γ = (σ * γ * σ⁻¹) * σ by rw [inv_mul_cancel_right], map_mul,
          SlashAction.slash_mul, slash_mem g hconj]
      holo' := (CuspFormClass.holo g).slash k _
      zero_at_cusps' := by
        have : (CohCarrier.GammaH M H).FiniteIndex := finiteIndex_GammaH
        intro c hc A hA
        have hσSL : (Matrix.SpecialLinearGroup.mapGL ℝ σ : GL (Fin 2) ℝ) ∈
            (Matrix.SpecialLinearGroup.mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ).range := ⟨σ, rfl⟩
        have hc' : IsCusp ((Matrix.SpecialLinearGroup.mapGL ℝ σ : GL (Fin 2) ℝ) • c)
            ((CohCarrier.GammaH M H : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) := by
          rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc ⊢
          exact hc.smul_of_mem hσSL
        have := (OnePoint.IsZeroAt.smul_iff (g := (Matrix.SpecialLinearGroup.mapGL ℝ σ : GL (Fin 2) ℝ))
          (c := c) (f := (⇑g : UpperHalfPlane → ℂ)) (k := k)).mp (CuspFormClass.zero_at_cusps g hc')
        exact this A hA }
  map_add' g h := by
    apply DFunLike.coe_injective
    change ((⇑(g + h) : UpperHalfPlane → ℂ)) ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ σ : GL (Fin 2) ℝ)
      = (⇑g : UpperHalfPlane → ℂ) ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ σ : GL (Fin 2) ℝ)
        + (⇑h : UpperHalfPlane → ℂ) ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ σ : GL (Fin 2) ℝ)
    rw [FunLike.coe_add, SlashAction.add_slash]
  map_smul' c g := by
    apply DFunLike.coe_injective
    change ((⇑(c • g) : UpperHalfPlane → ℂ)) ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ σ : GL (Fin 2) ℝ)
      = c • ((⇑g : UpperHalfPlane → ℂ) ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ σ : GL (Fin 2) ℝ))
    rw [FunLike.coe_smul, ← sl_slash, ModularForm.SL_smul_slash, sl_slash]

private def lift (u : (ZMod M)ˣ) : SL(2, ℤ) := (exists_lift (M := M) u).choose

private theorem lift_mem (u : (ZMod M)ˣ) : lift (M := M) u ∈ Gamma0 M := (exists_lift (M := M) u).choose_spec.1

private theorem dd_lift (u : (ZMod M)ˣ) : dd (M := M) (lift u) = (u : ZMod M) := (exists_lift (M := M) u).choose_spec.2

private theorem lift_mem_GammaH {u : (ZMod M)ˣ} (hu : u ∈ H) : lift (M := M) u ∈ CohCarrier.GammaH M H := mem_GammaH_of_dd_eq (lift_mem u) hu (dd_lift u)

private def proj (ε : DirichletCharacter ℂ M) (g : CuspForm (CohCarrier.GammaH M H) k) :
    CuspForm (CohCarrier.GammaH M H) k :=
  ((M.totient : ℂ))⁻¹ •
    ∑ u : (ZMod M)ˣ, ε ((u⁻¹ : (ZMod M)ˣ) : ZMod M) • diamond (lift u) (lift_mem u) g

omit [NeZero M] in
private theorem coe_sum {ι : Type*} (s : Finset ι) (F : ι → CuspForm (CohCarrier.GammaH M H) k) :
    (⇑(∑ i ∈ s, F i) : UpperHalfPlane → ℂ) = ∑ i ∈ s, (⇑(F i) : UpperHalfPlane → ℂ) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, FunLike.coe_add, ih]

private theorem coe_proj (ε : DirichletCharacter ℂ M) (g : CuspForm (CohCarrier.GammaH M H) k) :
    (⇑(proj ε g) : UpperHalfPlane → ℂ) = ((M.totient : ℂ))⁻¹ •
      ∑ u : (ZMod M)ˣ, ε ((u⁻¹ : (ZMod M)ˣ) : ZMod M) •
        ((⇑g : UpperHalfPlane → ℂ) ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ (lift u) : GL (Fin 2) ℝ)) := by
  rw [proj, FunLike.coe_smul, coe_sum]
  rfl

private theorem sigma_mapGL (γ : SL(2, ℤ)) (c : ℂ) :
    UpperHalfPlane.σ (Matrix.SpecialLinearGroup.mapGL ℝ γ : GL (Fin 2) ℝ) c = c := by
  rw [UpperHalfPlane.σ, ite_eq_left (by simp)]
  rfl

private theorem proj_slash (ε : DirichletCharacter ℂ M) (g : CuspForm (CohCarrier.GammaH M H) k)
    (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M) :
    (⇑(proj ε g) : UpperHalfPlane → ℂ) ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ γ : GL (Fin 2) ℝ)
      = ε (dd γ) • ⇑(proj ε g) := by
  set d₀ : (ZMod M)ˣ := (isUnit_dd hγ).unit with hd₀
  have hd₀' : (d₀ : ZMod M) = dd γ := (isUnit_dd hγ).unit_spec
  rw [coe_proj, ModularForm.smul_slash, SlashAction.sum_slash]
  simp_rw [sigma_mapGL, ModularForm.smul_slash, sigma_mapGL, ← SlashAction.slash_mul, ← map_mul]
  have hstep : ∀ u : (ZMod M)ˣ,
      (⇑g : UpperHalfPlane → ℂ) ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ (lift u * γ) : GL (Fin 2) ℝ)
        = (⇑g : UpperHalfPlane → ℂ) ∣[k]
            (Matrix.SpecialLinearGroup.mapGL ℝ (lift (u * d₀)) : GL (Fin 2) ℝ) := by
    intro u
    apply slash_eq_of_dd_eq g (mul_mem (lift_mem u) hγ) (lift_mem _)
    rw [dd_mul (lift_mem u) hγ, dd_lift, dd_lift, ← hd₀', Units.val_mul]
  simp_rw [hstep]
  rw [smul_comm]
  congr 1
  rw [Finset.smul_sum]
  refine (Fintype.sum_equiv (Equiv.mulRight d₀) _ _ fun u => ?_)
  simp only [Equiv.coe_mulRight]
  rw [smul_smul]
  congr 1
  rw [show (u⁻¹ : (ZMod M)ˣ) = d₀ * (u * d₀)⁻¹ by group, Units.val_mul, map_mul, hd₀']

private theorem sum_proj (g : CuspForm (CohCarrier.GammaH M H) k) :
    ∑ ε : DirichletCharacter ℂ M, proj ε g = g := by
  apply DFunLike.coe_injective
  rw [coe_sum]
  simp_rw [coe_proj]
  rw [← Finset.smul_sum, Finset.sum_comm]
  have hφ : ((M.totient : ℂ)) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (NeZero.pos M)).ne'
  have horth : ∀ u : (ZMod M)ˣ,
      ∑ ε : DirichletCharacter ℂ M, ε ((u⁻¹ : (ZMod M)ˣ) : ZMod M)
        = if u = 1 then (M.totient : ℂ) else 0 := by
    intro u
    have := DirichletCharacter.sum_char_inv_mul_char_eq ℂ (Units.isUnit u) 1
    simp only [map_one, mul_one, ZMod.inv_coe_unit, Units.val_eq_one] at this
    exact this
  simp_rw [← Finset.sum_smul, horth, ite_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ,
    ite_true, smul_smul, inv_mul_cancel₀ hφ, one_smul]
  exact slash_mem g (lift_mem_GammaH (one_mem H))

private theorem proj_eq_zero_of_apply_ne_one (ε : DirichletCharacter ℂ M)
    (g : CuspForm (CohCarrier.GammaH M H) k) {d : (ZMod M)ˣ} (hd : d ∈ H)
    (hε : ε (d : ZMod M) ≠ 1) : proj ε g = 0 := by
  have h1 := proj_slash ε g (lift d) (lift_mem d)
  rw [slash_mem (proj ε g) (lift_mem_GammaH hd), dd_lift] at h1
  have h2 : (ε (d : ZMod M) - 1) • (⇑(proj ε g) : UpperHalfPlane → ℂ) = 0 := by
    rw [sub_smul, one_smul, ← h1, sub_self]
  rw [smul_eq_zero, sub_eq_zero] at h2
  exact DFunLike.coe_injective ((h2.resolve_left hε).trans FunLike.coe_zero.symm)

open Classical in
private theorem sum_inv_mul_eq (ε₀ ε : DirichletCharacter ℂ M) :
    ∑ u : (ZMod M)ˣ, ε₀ ((u⁻¹ : (ZMod M)ˣ) : ZMod M) * ε (u : ZMod M)
      = if ε₀ = ε then (M.totient : ℂ) else 0 := by
  split_ifs with h
  · subst h
    have h1 : ∀ u : (ZMod M)ˣ, ε₀ ((u⁻¹ : (ZMod M)ˣ) : ZMod M) * ε₀ (u : ZMod M) = 1 := by
      intro u
      rw [← map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, map_one]
    simp_rw [h1]
    rw [Finset.sum_const, Finset.card_univ, ZMod.card_units_eq_totient, nsmul_eq_mul, mul_one]
  · obtain ⟨u₀, hu₀⟩ : ∃ u₀ : (ZMod M)ˣ, ε₀ (u₀ : ZMod M) ≠ ε (u₀ : ZMod M) := by
      by_contra hall
      push Not at hall
      exact h (MulChar.ext hall)
    set c : ℂ := ε₀ ((u₀⁻¹ : (ZMod M)ˣ) : ZMod M) * ε (u₀ : ZMod M) with hc
    have hc1 : c ≠ 1 := by
      intro h1
      apply hu₀
      have e : ε₀ (u₀ : ZMod M) * c = ε (u₀ : ZMod M) := by
        rw [hc, ← mul_assoc, ← map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, map_one,
          one_mul]
      rw [h1, mul_one] at e
      exact e
    set S : ℂ := ∑ u : (ZMod M)ˣ, ε₀ ((u⁻¹ : (ZMod M)ˣ) : ZMod M) * ε (u : ZMod M) with hS
    have hreindex : S = c * S := by
      rw [hS, Finset.mul_sum]
      refine (Fintype.sum_equiv (Equiv.mulLeft u₀) _ _ fun u => ?_).symm
      simp only [Equiv.coe_mulLeft]
      rw [hc, mul_inv_rev, Units.val_mul, Units.val_mul, map_mul, map_mul]
      ring
    have : (1 - c) * S = 0 := by rw [sub_mul, one_mul, ← hreindex, sub_self]
    rcases mul_eq_zero.mp this with h0 | h0
    · exact absurd (sub_eq_zero.mp h0).symm hc1
    · exact h0

private theorem indep (s : Finset (DirichletCharacter ℂ M))
    (g : DirichletCharacter ℂ M → CuspForm (CohCarrier.GammaH M H) k)
    (hg : ∀ ε ∈ s, ∀ σ : Gamma0 M,
      ⇑(g ε) ∣[k] ((Matrix.SpecialLinearGroup.mapGL ℝ (σ : SL(2, ℤ)) : GL (Fin 2) ℝ)) =
        ε (((σ : SL(2, ℤ)) 1 1 : ℤ) : ZMod M) • ⇑(g ε))
    (hsum : (∑ ε ∈ s, ⇑(g ε)) = 0) : ∀ ε ∈ s, g ε = 0 := by
  classical
  intro ε₀ hε₀
  let Q : (UpperHalfPlane → ℂ) → (UpperHalfPlane → ℂ) := fun F =>
    ∑ u : (ZMod M)ˣ, ε₀ ((u⁻¹ : (ZMod M)ˣ) : ZMod M) •
      (F ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ (lift (M := M) u) : GL (Fin 2) ℝ))
  have hQ := congrArg Q hsum
  have hQ0 : Q 0 = 0 := by
    simp only [Q, SlashAction.zero_slash, smul_zero, Finset.sum_const_zero]
  have hQs : Q (∑ ε ∈ s, ⇑(g ε)) = (M.totient : ℂ) • ⇑(g ε₀) := by
    simp only [Q, SlashAction.sum_slash, Finset.smul_sum]
    rw [Finset.sum_comm]
    have hterm : ∀ ε ∈ s, ∀ u : (ZMod M)ˣ,
        ε₀ ((u⁻¹ : (ZMod M)ˣ) : ZMod M) •
            ((⇑(g ε) : UpperHalfPlane → ℂ) ∣[k]
              (Matrix.SpecialLinearGroup.mapGL ℝ (lift (M := M) u) : GL (Fin 2) ℝ))
          = (ε₀ ((u⁻¹ : (ZMod M)ˣ) : ZMod M) * ε (u : ZMod M)) • ⇑(g ε) := by
      intro ε hε u
      rw [hg ε hε ⟨lift u, lift_mem u⟩, smul_smul]
      congr 2
      exact congrArg ε (dd_lift u)
    rw [Finset.sum_congr rfl fun ε hε => (Finset.sum_congr rfl fun u _ => hterm ε hε u)]
    simp_rw [← Finset.sum_smul, sum_inv_mul_eq, ite_smul, zero_smul, Finset.sum_ite_eq s ε₀,
      ite_eq_left hε₀]
  rw [hQs, hQ0, smul_eq_zero] at hQ
  have hφ : ((M.totient : ℂ)) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (NeZero.pos M)).ne'
  exact DFunLike.coe_injective ((hQ.resolve_left hφ).trans FunLike.coe_zero.symm)

end Diamond

end CuspForm.GammaHNebentypusDecomp

end

open scoped MatrixGroups ModularForm

open scoped MatrixGroups ModularForm in
open CuspForm.GammaHNebentypusDecomp in

theorem CuspForm.exists_finset_dirichlet_sum_eq_and_independent_of_gammaH
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (k : ℤ) :
    (∀ f : CuspForm (CohCarrier.GammaH M H) k,
      ∃ (s : Finset (DirichletCharacter ℂ M)) (fε : DirichletCharacter ℂ M → CuspForm (CohCarrier.GammaH M H) k),
        (∀ ε ∈ s, ∀ d : (ZMod M)ˣ, d ∈ H → ε (d : ZMod M) = 1) ∧
        (∀ ε ∈ s, ∀ σ : CongruenceSubgroup.Gamma0 M,
          ⇑(fε ε) ∣[k] ((Matrix.SpecialLinearGroup.mapGL ℝ (σ : SL(2, ℤ)) : GL (Fin 2) ℝ)) =
            ε (((σ : SL(2, ℤ)) 1 1 : ℤ) : ZMod M) • ⇑(fε ε)) ∧
        ⇑f = ∑ ε ∈ s, ⇑(fε ε)) ∧
    (∀ (s : Finset (DirichletCharacter ℂ M)) (g : DirichletCharacter ℂ M → CuspForm (CohCarrier.GammaH M H) k),
      (∀ ε ∈ s, ∀ σ : CongruenceSubgroup.Gamma0 M,
          ⇑(g ε) ∣[k] ((Matrix.SpecialLinearGroup.mapGL ℝ (σ : SL(2, ℤ)) : GL (Fin 2) ℝ)) =
            ε (((σ : SL(2, ℤ)) 1 1 : ℤ) : ZMod M) • ⇑(g ε)) →
      (∑ ε ∈ s, ⇑(g ε)) = 0 → ∀ ε ∈ s, g ε = 0) := by
  classical
  refine ⟨fun f => ?_, fun s g hg hsum => indep s g hg hsum⟩
  refine ⟨Finset.univ.filter (fun ε : DirichletCharacter ℂ M => ∀ d : (ZMod M)ˣ, d ∈ H → ε (d : ZMod M) = 1),
    fun ε => proj ε f, ?_, ?_, ?_⟩
  · intro ε hε
    exact (Finset.mem_filter.mp hε).2
  · intro ε _ σ
    exact proj_slash ε f (σ : SL(2, ℤ)) σ.2
  · rw [Finset.sum_filter_of_ne, ← coe_sum, sum_proj]
    intro ε _ hne d hd
    by_contra hεd
    apply hne
    show (⇑(proj ε f) : UpperHalfPlane → ℂ) = 0
    rw [proj_eq_zero_of_apply_ne_one ε f hd hεd, FunLike.coe_zero]

