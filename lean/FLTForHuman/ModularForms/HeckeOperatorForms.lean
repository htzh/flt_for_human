/-
  The bundled Hecke operators `T_p`/`U_p` as linear endomorphisms of
  `ModularForm (Γ₀(N)) k` and `CuspForm (Γ₀(N)) k`.

  This is the payoff of SET 1–2: every structure field of the bundled form is one
  theorem already proved. The pin calls its file a *definition* module
  (`Definitions/Def_ModularForm_HeckeOperatorForms.lean`); the port's `Defs/`
  layer is the operator block and its representatives, while the bundling
  *consumes* the invariance/analytic/cusp layers, so this module lives at the top
  level (like `HeckeInvariance.lean`). Only the placement diverges; the twelve
  bundled declarations are verbatim from the pin's `Definitions/` file (no
  `Theorems/` wrapper), and the checker verifies them by name.

  The level split is in the hypotheses, as in the pin: `T_p` for `p` prime with
  `p ∤ N`, `U_p` for `p ∣ N` (with the `NeZero N` asymmetry kept literal —
  `heckeTLin` derives `NeZero N` from `hpN`, `heckeULin` takes it).

  | field | source |
  |---|---|
  | `slash_action_eq'` | `ModularForm.hecke{T,U}_slash_eq_self_of_mem_Gamma0` (T1) |
  | `holo'` | `ModularForm.mdifferentiable_hecke{T,U}` (T3) |
  | `bdd_at_cusps'` | `ModularFormClass.isBoundedAt_hecke{T,U}` (T4) |
  | `zero_at_cusps'` | `CuspFormClass.isZeroAt_hecke{T,U}` (T4) |
  | `map_add'`, `map_smul'` | `hecke{T,U}_add`/`hecke{T,U}_smul` (T0, `Defs/HeckeOperator.lean`) |

  FLT provenance, pinned `aa2d8b3`:
  `Definitions/Def_ModularForm_HeckeOperatorForms.lean` (112 lines) and the three
  thin wrappers `S_CuspForm_qExpansion_heckeTLin.lean` (19),
  `S_CuspForm_exists_coe_eq_heckeT.lean` (7), `S_CuspForm_exists_coe_eq_heckeU.lean`
  (7). Commutation and the algebra are T7.
-/
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import FLTForHuman.ModularForms.Defs.HeckeOperator
import FLTForHuman.ModularForms.HeckeInvariance
import FLTForHuman.ModularForms.HeckeAnalytic
import FLTForHuman.ModularForms.HeckeCusps
import FLTForHuman.ModularForms.HeckeQCoeff

set_option autoImplicit false

noncomputable section

open UpperHalfPlane
open scoped MatrixGroups ModularForm

namespace ModularForm

variable {N : ℕ} {p : ℕ}

/-- `T_p` as a `ℂ`-linear endomorphism of `ModularForm (Γ₀(N)) k`, for `p` prime
and `p ∤ N`. Verbatim from `Definitions/Def_ModularForm_HeckeOperatorForms.lean`. -/
def heckeTLin (k : ℤ) (hp : p.Prime) (hpN : ¬ p ∣ N) :
    ModularForm (CongruenceSubgroup.Gamma0 N) k →ₗ[ℂ] ModularForm (CongruenceSubgroup.Gamma0 N) k :=
  have hN : NeZero N := ⟨fun h => hpN (h ▸ dvd_zero p)⟩
  { toFun := fun f =>
      { toFun := heckeT k p ⇑f
        slash_action_eq' := fun γ hγ => heckeT_slash_eq_self_of_mem_Gamma0 k hp hpN
          (fun γ hγ => SlashInvariantFormClass.slash_action_eq f γ hγ) γ hγ
        holo' := mdifferentiable_heckeT (ModularFormClass.holo f) k p
        bdd_at_cusps' := fun hc => ModularFormClass.isBoundedAt_heckeT f p hc }
    map_add' := fun f g => DFunLike.coe_injective <|
      show heckeT k p ⇑(f + g) = heckeT k p ⇑f + heckeT k p ⇑g by rw [FunLike.coe_add, heckeT_add]
    map_smul' := fun c f => DFunLike.coe_injective <|
      show heckeT k p ⇑(c • f) = c • heckeT k p ⇑f by rw [FunLike.coe_smul, heckeT_smul] }

/-- `U_p` as a `ℂ`-linear endomorphism of `ModularForm (Γ₀(N)) k`, for `p ∣ N`.
Verbatim from `Definitions/Def_ModularForm_HeckeOperatorForms.lean`. -/
def heckeULin (k : ℤ) [NeZero N] (hpN : p ∣ N) :
    ModularForm (CongruenceSubgroup.Gamma0 N) k →ₗ[ℂ] ModularForm (CongruenceSubgroup.Gamma0 N) k where
  toFun f :=
    { toFun := heckeU k p ⇑f
      slash_action_eq' := fun γ hγ => heckeU_slash_eq_self_of_mem_Gamma0 k hpN
        (fun γ hγ => SlashInvariantFormClass.slash_action_eq f γ hγ) γ hγ
      holo' := mdifferentiable_heckeU (ModularFormClass.holo f) k p
      bdd_at_cusps' := fun hc => ModularFormClass.isBoundedAt_heckeU f p hc }
  map_add' f g := DFunLike.coe_injective <|
    show heckeU k p ⇑(f + g) = heckeU k p ⇑f + heckeU k p ⇑g by rw [FunLike.coe_add, heckeU_add]
  map_smul' c f := DFunLike.coe_injective <|
    show heckeU k p ⇑(c • f) = c • heckeU k p ⇑f by rw [FunLike.coe_smul, heckeU_smul]

@[simp] theorem coe_heckeTLin_apply (k : ℤ) (hp : p.Prime) (hpN : ¬ p ∣ N)
    (f : ModularForm (CongruenceSubgroup.Gamma0 N) k) : ⇑(heckeTLin k hp hpN f) = heckeT k p ⇑f := rfl

@[simp] theorem coe_heckeULin_apply (k : ℤ) [NeZero N] (hpN : p ∣ N)
    (f : ModularForm (CongruenceSubgroup.Gamma0 N) k) : ⇑(heckeULin k hpN f) = heckeU k p ⇑f := rfl

theorem heckeTLin_apply_apply (k : ℤ) (hp : p.Prime) (hpN : ¬ p ∣ N)
    (f : ModularForm (CongruenceSubgroup.Gamma0 N) k) (τ : UpperHalfPlane) :
    heckeTLin k hp hpN f τ = heckeT k p ⇑f τ := rfl

theorem heckeULin_apply_apply (k : ℤ) [NeZero N] (hpN : p ∣ N)
    (f : ModularForm (CongruenceSubgroup.Gamma0 N) k) (τ : UpperHalfPlane) :
    heckeULin k hpN f τ = heckeU k p ⇑f τ := rfl

end ModularForm

namespace CuspForm

open ModularForm

variable {N : ℕ} {p : ℕ}

/-- `T_p` as a `ℂ`-linear endomorphism of `CuspForm (Γ₀(N)) k`, for `p` prime and
`p ∤ N`. Verbatim from `Definitions/Def_ModularForm_HeckeOperatorForms.lean`. -/
def heckeTLin (k : ℤ) (hp : p.Prime) (hpN : ¬ p ∣ N) :
    CuspForm (CongruenceSubgroup.Gamma0 N) k →ₗ[ℂ] CuspForm (CongruenceSubgroup.Gamma0 N) k :=
  have hN : NeZero N := ⟨fun h => hpN (h ▸ dvd_zero p)⟩
  { toFun := fun f =>
      { toFun := heckeT k p ⇑f
        slash_action_eq' := fun γ hγ => heckeT_slash_eq_self_of_mem_Gamma0 k hp hpN
          (fun γ hγ => SlashInvariantFormClass.slash_action_eq f γ hγ) γ hγ
        holo' := mdifferentiable_heckeT (CuspFormClass.holo f) k p
        zero_at_cusps' := fun hc => CuspFormClass.isZeroAt_heckeT f p hc }
    map_add' := fun f g => DFunLike.coe_injective <|
      show heckeT k p ⇑(f + g) = heckeT k p ⇑f + heckeT k p ⇑g by rw [FunLike.coe_add, heckeT_add]
    map_smul' := fun c f => DFunLike.coe_injective <|
      show heckeT k p ⇑(c • f) = c • heckeT k p ⇑f by rw [FunLike.coe_smul, heckeT_smul] }

/-- `U_p` as a `ℂ`-linear endomorphism of `CuspForm (Γ₀(N)) k`, for `p ∣ N`.
Verbatim from `Definitions/Def_ModularForm_HeckeOperatorForms.lean`. -/
def heckeULin (k : ℤ) [NeZero N] (hpN : p ∣ N) :
    CuspForm (CongruenceSubgroup.Gamma0 N) k →ₗ[ℂ] CuspForm (CongruenceSubgroup.Gamma0 N) k where
  toFun f :=
    { toFun := heckeU k p ⇑f
      slash_action_eq' := fun γ hγ => heckeU_slash_eq_self_of_mem_Gamma0 k hpN
        (fun γ hγ => SlashInvariantFormClass.slash_action_eq f γ hγ) γ hγ
      holo' := mdifferentiable_heckeU (CuspFormClass.holo f) k p
      zero_at_cusps' := fun hc => CuspFormClass.isZeroAt_heckeU f p hc }
  map_add' f g := DFunLike.coe_injective <|
    show heckeU k p ⇑(f + g) = heckeU k p ⇑f + heckeU k p ⇑g by rw [FunLike.coe_add, heckeU_add]
  map_smul' c f := DFunLike.coe_injective <|
    show heckeU k p ⇑(c • f) = c • heckeU k p ⇑f by rw [FunLike.coe_smul, heckeU_smul]

@[simp] theorem coe_heckeTLin_apply (k : ℤ) (hp : p.Prime) (hpN : ¬ p ∣ N)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N) k) : ⇑(heckeTLin k hp hpN f) = heckeT k p ⇑f := rfl

@[simp] theorem coe_heckeULin_apply (k : ℤ) [NeZero N] (hpN : p ∣ N)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N) k) : ⇑(heckeULin k hpN f) = heckeU k p ⇑f := rfl

theorem heckeTLin_apply_apply (k : ℤ) (hp : p.Prime) (hpN : ¬ p ∣ N)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N) k) (τ : UpperHalfPlane) :
    heckeTLin k hp hpN f τ = heckeT k p ⇑f τ := rfl

theorem heckeULin_apply_apply (k : ℤ) [NeZero N] (hpN : p ∣ N)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N) k) (τ : UpperHalfPlane) :
    heckeULin k hpN f τ = heckeU k p ⇑f τ := rfl

/-! ## The thin downstream wrappers -/

/-- `qExpansion` of `T_p f` through the bundled `T_p`. Stated verbatim from
`Theorems/Thm_CuspForm_qExpansion_heckeTLin.lean`. -/
theorem qExpansion_heckeTLin {N p : ℕ} (hp : p.Prime) (hpN : ¬ p ∣ N)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N) 2) :
    UpperHalfPlane.qExpansion 1 ⇑(CuspForm.heckeTLin 2 hp hpN f)
      = PowerSeries.heckeT p 2 (UpperHalfPlane.qExpansion 1 ⇑f) := by
  have hΓ : (1 : ℝ) ∈ ((CongruenceSubgroup.Gamma0 N : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) :
      Subgroup (Matrix.GeneralLinearGroup (Fin 2) ℝ)).strictPeriods := by
    rw [CongruenceSubgroup.strictPeriods_Gamma0]
    exact AddSubgroup.mem_zmultiples 1
  rw [CuspForm.coe_heckeTLin_apply]
  exact ModularFormClass.qExpansion_heckeT_eq_heckeT (k := 2) f hΓ hp.ne_zero (by norm_num)

/-- A cusp form with prescribed coercion `heckeT k p ⇑f`. Stated verbatim from
`Theorems/Thm_CuspForm_exists_coe_eq_heckeT.lean`. -/
theorem exists_coe_eq_heckeT {N : ℕ} {k : ℤ} (f : CuspForm (CongruenceSubgroup.Gamma0 N) k) {p : ℕ} (hp : p.Prime) (hpN : ¬ p ∣ N) : ∃ g : CuspForm (CongruenceSubgroup.Gamma0 N) k, ⇑g = ModularForm.heckeT k p ⇑f := by
  have hN : NeZero N := ⟨fun h => hpN (h ▸ dvd_zero p)⟩
  exact ⟨{ toFun := ModularForm.heckeT k p ⇑f
           slash_action_eq' := fun γ hγ => ModularForm.heckeT_slash_eq_self_of_mem_Gamma0 k hp hpN
             (fun γ hγ => SlashInvariantFormClass.slash_action_eq f γ hγ) γ hγ
           holo' := ModularForm.mdifferentiable_heckeT (CuspFormClass.holo f) k p
           zero_at_cusps' := fun hc => CuspFormClass.isZeroAt_heckeT f p hc }, rfl⟩

/-- A cusp form with prescribed coercion `heckeU k p ⇑f`. Stated verbatim from
`Theorems/Thm_CuspForm_exists_coe_eq_heckeU.lean`. -/
theorem exists_coe_eq_heckeU {N : ℕ} [NeZero N] {k : ℤ} (f : CuspForm (CongruenceSubgroup.Gamma0 N) k) {p : ℕ} (hpN : p ∣ N) : ∃ g : CuspForm (CongruenceSubgroup.Gamma0 N) k, ⇑g = ModularForm.heckeU k p ⇑f :=
  ⟨{ toFun := ModularForm.heckeU k p ⇑f
     slash_action_eq' := fun γ hγ => ModularForm.heckeU_slash_eq_self_of_mem_Gamma0 k hpN
       (fun γ hγ => SlashInvariantFormClass.slash_action_eq f γ hγ) γ hγ
     holo' := ModularForm.mdifferentiable_heckeU (CuspFormClass.holo f) k p
     zero_at_cusps' := fun hc => CuspFormClass.isZeroAt_heckeU f p hc }, rfl⟩

end CuspForm

end
