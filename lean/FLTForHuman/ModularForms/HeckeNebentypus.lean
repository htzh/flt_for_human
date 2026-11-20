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
  ext τ
  rw [ModularForm.Level.diamondLinOne_apply_apply hγ,
    (CuspForm.hasNebentypus_iff ε g).mp hg γ hγ.1,
    show ModularForm.Level.dd γ = (d : ZMod M) from hγ.2]
  rfl

end CuspForm

end
