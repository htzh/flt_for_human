/-
  The cusp-form-vanishing layer (`base/003`) — the definition of done for the
  `ModularForm.S2_Gamma0_{2,1}_eq_zero` port.

  Four zones, each a real instantiation rather than a `#check` alone:

  * **A `[norm]`** — the generic cusp-form norm API;
  * **B `[index]`** — `[SL(2, ℤ) : Γ₀(2)] = 3`;
  * **C `[vanishing]`** — the two wrapper theorems, unconditional;
  * **D `[compose]`** — the norm into the level-one vanishing, the composition
    the FLT modularity/level-lowering route consumes.
-/
import FLTForHuman.ModularForms.LevelTwoCuspVanishing

set_option autoImplicit false

noncomputable section

open UpperHalfPlane SlashInvariantForm CongruenceSubgroup
open scoped MatrixGroups ModularForm Topology Filter Manifold

/-! ## Zone A — `[norm]` the generic cusp-form norm -/

#check @CuspForm.norm
#check @CuspForm.norm_eq_zero_iff
#check @CuspForm.coe_norm_eq_coe_modularFormNorm

/-! ## Zone B — `[index]` `Γ₀(2)` has index three -/

#check @ModularForm.Gamma0_two_index_eq_three
example : (CongruenceSubgroup.Gamma0 2).index = 3 := ModularForm.Gamma0_two_index_eq_three

/-! ## Zone C — `[vanishing]` the two wrapper theorems -/

#check @ModularForm.S2_Gamma0_2_eq_zero
#check @ModularForm.S2_Gamma0_one_eq_zero
example (f : CuspForm (CongruenceSubgroup.Gamma0 2) 2) : f = 0 :=
  ModularForm.S2_Gamma0_2_eq_zero f
example (f : CuspForm (CongruenceSubgroup.Gamma0 1) 2) : f = 0 :=
  ModularForm.S2_Gamma0_one_eq_zero f

/-! ## Zone D — `[compose]` the norm into the level-one vanishing -/

/-- The route's use of the API: the norm of a form on `Γ₀(2)` is a level-one
cusp form of weight `6`; the vanishing theorem makes it zero, and
`CuspForm.norm_eq_zero_iff` reads that back as the form being zero. -/
example (f : CuspForm (CongruenceSubgroup.Gamma0 2) 2) :
    CuspForm.norm (↑(CongruenceSubgroup.Gamma 1) : Subgroup (GL (Fin 2) ℝ)) f = 0 := by
  rw [CuspForm.norm_eq_zero_iff]
  simpa using congrArg (fun g : CuspForm (CongruenceSubgroup.Gamma0 2) 2 => (g : ℍ → ℂ))
    (ModularForm.S2_Gamma0_2_eq_zero f)

end
