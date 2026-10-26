/-
  The three `CuspForm.Stable*` theorems: the hypotheses of the Hecke-equivariance
  layer, discharged.

  `StableD`, `StableU`, `StableT`
  (`ModularForms/Defs/GammaH.lean`, transcribed from the tail of
  `Definitions/Def_CuspForm_HeckeOperatorFormsGammaH.lean`) are the statements
  that the diamond action, `U_q`, and the `T_ℓ` combination
  `U_ℓ f + f ∣ (ρ · diag ℓ)` again land in `Γ_H(M)`-cusp forms. This module proves
  all three. Each is a three-component conjunction (invariance, holomorphic,
  cuspidal), and each component is one already-ported lemma:

  | component | lemma |
  |---|---|
  | `Γ_H`-invariance of `U_q` | `ModularForm.heckeU_slash_eq_self_of_mem_GammaH` (W3b, node 8) |
  | `Γ_H`-invariance of `U_ℓ + f ∣ (ρ · diag ℓ)` | `ModularForm.heckeU_add_slash_slash_eq_self_of_mem_GammaH` (W3b, node 9) |
  | holomorphy | `ModularForm.mdifferentiable_heckeU` |
  | vanishing at cusps under `U_p` | `CuspFormClass.isZeroAt_heckeU` |
  | vanishing at cusps under `∣[k] σ` | `CuspFormClass.isZeroAt_slash_of_mem_Gamma0` |
  | vanishing at cusps under `∣[k] σ ∣[k] diag ℓ` | `CuspFormClass.isZeroAt_slash_slash_heckeDiagMatrix_of_mem_Gamma0` |

  Keeping these out of `ModularForms/HeckeInvariance.lean` leaves that module's
  "statements about `U_p`/`T_p` themselves" scope intact.

  FLT provenance, pinned `aa2d8b3`:

  spec-pin: Theorems/Thm_CuspForm_stableD.lean
  spec-pin: P2M/Sol/S_CuspForm_stableD.lean   -- comparable copy
  spec-pin: Theorems/Thm_CuspForm_stableU.lean
  spec-pin: P2M/Sol/S_CuspForm_stableU.lean   -- comparable copy
  spec-pin: Theorems/Thm_CuspForm_stableT.lean
  spec-pin: P2M/Sol/S_CuspForm_stableT.lean   -- comparable copy
-/
import FLTForHuman.ModularForms.Defs.GammaH
import FLTForHuman.ModularForms.HeckeInvariance
import FLTForHuman.ModularForms.CuspFormSlashHecke
import FLTForHuman.ModularForms.HeckeAnalytic
import FLTForHuman.ModularForms.HeckeCusps

set_option autoImplicit false

-- The pin's `haveI : NeZero ℓ` before the conclusion is part of its proof text
-- (`stableT`); kept literal, as in `HeckeInvariance.lean` and `Corestriction.lean`.
set_option linter.style.haveILetI false

noncomputable section

open UpperHalfPlane CongruenceSubgroup

open scoped MatrixGroups ModularForm

open CohCarrier

namespace CuspForm

/-- Slashing by a `Γ₀(M)`-matrix preserves cuspidality for `Γ_H(M)`-cusp forms. -/
theorem stableD (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (k : ℤ) :
    CuspForm.StableD M H k := by
  intro σ f c hc
  exact CuspFormClass.isZeroAt_slash_of_mem_Gamma0 M H k σ f hc

/-- `U_q f` is again `Γ_H(M)`-invariant, holomorphic and cuspidal, for `q ∣ M`. -/
theorem stableU (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (k : ℤ) {q : ℕ}
    (hq : q.Prime) (hqM : q ∣ M) :
    CuspForm.StableU M H k q := by
  intro f
  exact ⟨fun γ hγ => ModularForm.heckeU_slash_eq_self_of_mem_GammaH M H k hq hqM
      (fun γ hγ => SlashInvariantFormClass.slash_action_eq f γ hγ) γ hγ,
    ModularForm.mdifferentiable_heckeU (CuspFormClass.holo f) k q,
    fun c hc => CuspFormClass.isZeroAt_heckeU f q hc⟩

/-- The `T_ℓ` combination `U_ℓ f + f ∣ (ρ · diag ℓ)` is again
`Γ_H(M)`-invariant, holomorphic and cuspidal, for `ℓ` prime and `ℓ ∤ M`. -/
theorem stableT (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (k : ℤ) {ℓ : ℕ}
    (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M) :
    CuspForm.StableT M H k ℓ := by
  haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
  intro ρ hρ f
  refine ⟨fun γ hγ => ModularForm.heckeU_add_slash_slash_eq_self_of_mem_GammaH M H k hℓ hℓM ρ hρ
      (fun γ hγ => SlashInvariantFormClass.slash_action_eq f γ hγ) γ hγ,
    (ModularForm.mdifferentiable_heckeU (CuspFormClass.holo f) k ℓ).add
      ((CuspFormClass.holo f).slash k _),
    fun c hc => ?_⟩
  rw [SlashAction.slash_mul]
  exact (CuspFormClass.isZeroAt_heckeU f ℓ hc).add
    (CuspFormClass.isZeroAt_slash_slash_heckeDiagMatrix_of_mem_Gamma0 M H k ℓ ρ f hc)

end CuspForm

end
