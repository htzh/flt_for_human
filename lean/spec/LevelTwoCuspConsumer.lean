/-
  Consumer for the weight-2 cusp-form vanishing (`base/003`).

  Both theorems are now corollaries of the Sturm bound: the weight-`2` bound is
  `⌊2 · [SL(2, ℤ) : Γ] / 12⌋ = 0` at `Γ(1)` and `Γ₀(2)`, and a cusp form has
  vanishing constant term. This file applies them and exercises the route's
  ingredients.

  * **A `[vanishing]`** — the two wrapper theorems;
  * **B `[index]`** — the weight-`2` bound is `0` because `(Γ₀ 2).index = 3`;
  * **C `[sturm]`** — the two Sturm headlines, applied;
  * **D `[bridge]`** — `Γ(1) = 𝒮ℒ` and the subgroup-equality transport.
-/
import Reserve.ModularForms.LevelTwoCuspVanishing
import FLTForHuman.ModularForms.Gamma0TwoIndex

set_option autoImplicit false

noncomputable section

open UpperHalfPlane ModularForm SlashInvariantForm Subgroup Matrix Matrix.SpecialLinearGroup
open scoped MatrixGroups ModularForm Topology Filter Manifold CongruenceSubgroup

/-! ## Zone A — `[vanishing]` the two wrapper theorems -/

#check @ModularForm.S2_Gamma0_2_eq_zero
#check @ModularForm.S2_Gamma0_one_eq_zero
example (f : CuspForm (CongruenceSubgroup.Gamma0 2) 2) : f = 0 :=
  ModularForm.S2_Gamma0_2_eq_zero f
example (f : CuspForm (CongruenceSubgroup.Gamma0 1) 2) : f = 0 :=
  ModularForm.S2_Gamma0_one_eq_zero f

/-! ## Zone B — `[index]` the weight-2 Sturm bound vanishes at `Γ₀(2)` -/

#check @ModularForm.Gamma0_two_index_eq_three
example : (((2 : ℤ) * (CongruenceSubgroup.Gamma0 2).index).toNat / 12) = 0 := by
  rw [ModularForm.Gamma0_two_index_eq_three]; norm_num

/-! ## Zone C — `[sturm]` the Sturm headlines, applied -/

example (F : ModularForm (CongruenceSubgroup.Gamma0 2) 2)
    (h : ∀ n : ℕ, n ≤ (((2 : ℤ) * (CongruenceSubgroup.Gamma0 2).index).toNat / 12) →
      (qExpansion 1 F).coeff n = 0) : F = 0 :=
  ModularForm.sturm_bound_Gamma0 2 F h

example (F : ModularForm 𝒮ℒ 2)
    (h : (↑((2 : ℤ).toNat / 12) : ℕ∞) < (qExpansion 1 F).order) : F = 0 :=
  ModularForm.sturm_bound_levelOne (k := 2) (f := F) h

/-! ## Zone D — `[bridge]` `Γ(1) = 𝒮ℒ` and subgroup transport -/

#check @ModularForm.coe_Gamma_one_eq_SL
#check @ModularForm.cuspForm_eq_zero_of_subgroup_eq

end
