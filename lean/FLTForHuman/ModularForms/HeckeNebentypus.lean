/-
  The Nebentypus twist law of the diamond operator: on a `Γ₁(M)`-cusp form with
  Nebentypus `ε`, the diamond `⟨d⟩` (for `(d, M) = 1`) acts by the scalar
  `ε (d : ZMod M)`.

  FLT states this in `P2M/Sol/S_CuspForm_HasNebentypus_diamondLinOne_apply_eq_smul.lean`
  (29 lines; pinned `aa2d8b3`); the public statement is the `Theorems/` wrapper
  `Thm_CuspForm_HasNebentypus_diamondLinOne_apply_eq_smul.lean`, transcribed
  verbatim below.

  The only helper is invisible: `CuspForm.ext` reduces the cusp-form equality to
  a pointwise one, `ModularForm.Level.diamondLinOne_apply_apply` presents the
  diamond as the slash by a `Γ₀`-lift, and the pin's `HasNebentypus` twist law
  plus `ModularForm.SL_slash_apply` and `ModularGroup.denom_apply` cancel the
  automorphy factor.
-/
import FLTForHuman.ModularForms.Defs.PrimitiveFormGamma1
import FLTForHuman.ModularForms.Level.Diamond

set_option autoImplicit false

noncomputable section

open CongruenceSubgroup ModularForm UpperHalfPlane
open scoped MatrixGroups ModularForm

namespace CuspForm

/-- On a `Γ₁(M)`-cusp form with Nebentypus `ε`, the diamond `⟨d⟩` acts as the
scalar `ε (d : ZMod M)`. Stated verbatim from
`Theorems/Thm_CuspForm_HasNebentypus_diamondLinOne_apply_eq_smul.lean`. -/
theorem HasNebentypus.diamondLinOne_apply_eq_smul {M : ℕ} {k : ℤ}
    {ε : DirichletCharacter ℂ M} {g : CuspForm (CongruenceSubgroup.Gamma1 M) k}
    (hg : CuspForm.HasNebentypus ε g) {d : ℕ} (hd : Nat.Coprime d M) :
    CuspForm.diamondLinOne M k d g = ε (d : ZMod M) • g := by
  obtain ⟨γ, hγ⟩ := ModularForm.Level.exists_isDiamondLift_of_coprime hd
  refine CuspForm.ext fun τ => ?_
  rw [ModularForm.Level.diamondLinOne_apply_apply hγ, smul_apply, smul_eq_mul]
  have hs : ((⇑g : ℍ → ℂ) ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ γ)) τ
      = g (γ • τ) * denom (γ : GL (Fin 2) ℝ) τ ^ (-k) :=
    ModularForm.SL_slash_apply (f := ⇑g) (k := k) γ τ
  rw [hs, hg γ hγ.1 τ, hγ.2]
  have hden : denom (γ : GL (Fin 2) ℝ) τ = ((γ 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((γ 1 1 : ℤ) : ℂ) := by
    rw [ModularGroup.denom_apply]
  have hne : ((γ 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((γ 1 1 : ℤ) : ℂ) ≠ 0 := by
    rw [← hden]; exact denom_ne_zero _ τ
  rw [hden, zpow_neg, mul_assoc, mul_comm (_ ^ k * g τ), ← mul_assoc ((_) ^ k)⁻¹, inv_mul_cancel₀
    (zpow_ne_zero k hne), one_mul]

end CuspForm

end
