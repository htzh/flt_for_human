/-
  The endgame: **there are no weight-2 cusp forms on `Γ₀(2)`** (and the level-one
  analogue), assembled from the norm and the index.

  A hypothetical nonzero `f : CuspForm (Γ₀ 2) 2` has a nonzero norm of weight
  `2 * 3 = 6` at level one (`CuspForm.norm`, `CuspForm.norm_eq_zero_iff`,
  `Gamma0_two_index_eq_three`), and every level-one cusp form of weight `< 12`
  is zero (mathlib's `CuspForm.rank_eq_zero_of_weight_lt_twelve`). The bridge
  `Γ(1) ≃ 𝒮ℒ` transports the level-one vanishing, whose weight-`6` form is read
  at the quotient card `Nat.card (Γ(1) ⧸ Γ₀(2)) = 3`.

  The level-one statement `S2_Gamma0_one_eq_zero` is the same argument with the
  norm skipped: its weight `2` is already `< 12`, so it needs only the bridge.

  FLT provenance, pinned `aa2d8b3`:
  `P2M/Sol/S_ModularForm_S2_Gamma0_2_eq_zero.lean` lines 77–92 and 176–206, and
  `P2M/Sol/S_ModularForm_S2_Gamma0_one_eq_zero.lean`.
  https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularForm_S2_Gamma0_2_eq_zero.lean
  https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularForm_S2_Gamma0_one_eq_zero.lean

  The two public theorems keep their names, binders and types verbatim from their
  `Theorems/` wrappers; the pin's `private` bridges and quotient-card lemma are
  reproduced `private`, except `cuspForm_eq_zero_of_subgroup_eq`, which both files
  carry (the level-one copy is `private` in the pin) and the port writes once.
-/
import FLTForHuman.ModularForms.CuspFormNorm
import FLTForHuman.ModularForms.Gamma0TwoIndex
import Mathlib.NumberTheory.ModularForms.LevelOne.DimensionFormula
import Mathlib.NumberTheory.ModularForms.ArithmeticSubgroups

set_option autoImplicit false

noncomputable section

open UpperHalfPlane SlashInvariantForm Subgroup Matrix Matrix.SpecialLinearGroup
open scoped MatrixGroups ModularForm Topology Filter Manifold CongruenceSubgroup

namespace ModularForm

section LevelOneBridge

/-- `Γ(1)` is `𝒮ℒ`, the image of `SL(2, ℤ)` in `GL(2, ℝ)`; the bridge between
mathlib's level-one statements and FLT's congruence-subgroup spelling. -/
lemma coe_Gamma_one_eq_SL : (↑Γ(1) : Subgroup (GL (Fin 2) ℝ)) = 𝒮ℒ := by
  rw [CongruenceSubgroup.Gamma_one_top]
  ext x
  simp [Subgroup.mem_map, MonoidHom.mem_range]

/-- Transport a vanishing statement across an equality of level subgroups. -/
lemma cuspForm_eq_zero_of_subgroup_eq {Γ₁ Γ₂ : Subgroup (GL (Fin 2) ℝ)} (h : Γ₂ = Γ₁)
    {k : ℤ} (H : ∀ g : CuspForm Γ₂ k, g = 0) (f : CuspForm Γ₁ k) : f = 0 := by
  subst h; exact H f

/-- Every level-one cusp form of weight `6` is zero. -/
theorem S6_levelOne_eq_zero (f : CuspForm Γ(1) 6) : f = 0 :=
  cuspForm_eq_zero_of_subgroup_eq coe_Gamma_one_eq_SL.symm
    (fun g => rank_zero_iff_forall_zero.mp
      (CuspForm.rank_eq_zero_of_weight_lt_twelve (by norm_num)) g) f

/-- The same at a variable weight equal to `6`, the form the norm produces. -/
theorem S6_levelOne_eq_zero' {k : ℤ} (hk : k = 6) (f : CuspForm Γ(1) k) : f = 0 := by
  subst hk; exact S6_levelOne_eq_zero f

end LevelOneBridge

section Assembly

/-- The quotient card `Nat.card (Γ(1) ⧸ Γ₀(2)) = 3`, transported from the index. -/
private lemma card_quotient_eq_three :
    Nat.card ((↑(CongruenceSubgroup.Gamma 1) : Subgroup (GL (Fin 2) ℝ)) ⧸
      (↑(CongruenceSubgroup.Gamma0 2) : Subgroup (GL (Fin 2) ℝ)).subgroupOf
        (↑(CongruenceSubgroup.Gamma 1))) = 3 := by
  show Subgroup.relIndex (↑(CongruenceSubgroup.Gamma0 2) : Subgroup (GL (Fin 2) ℝ))
    (↑(CongruenceSubgroup.Gamma 1) : Subgroup (GL (Fin 2) ℝ)) = 3
  show Subgroup.relIndex ((CongruenceSubgroup.Gamma0 2).map (mapGL ℝ))
    ((CongruenceSubgroup.Gamma 1).map (mapGL ℝ)) = 3
  rw [Subgroup.relIndex_map_map_of_injective _ _ mapGL_injective,
      CongruenceSubgroup.Gamma_one_top, Subgroup.relIndex_top_right,
      Gamma0_two_index_eq_three]

/-- The finite-index instance the norm needs, from the card computation. Public
(anonymous, so the checker never reads it) so that consumers can apply
`CuspForm.norm` at `Γ(1) ⧸ Γ₀(2)` directly. -/
instance : Subgroup.IsFiniteRelIndex
    (↑(CongruenceSubgroup.Gamma0 2) : Subgroup (GL (Fin 2) ℝ))
    (↑(CongruenceSubgroup.Gamma 1)) :=
  ⟨by show Nat.card _ ≠ 0; rw [card_quotient_eq_three]; decide⟩

/-- **The endgame.** Every weight-2 cusp form on `Γ₀(2)` is zero: its norm is a
nonzero level-one cusp form of weight `6`, and there are none. -/
theorem S2_Gamma0_2_eq_zero (f : CuspForm (CongruenceSubgroup.Gamma0 2) 2) : f = 0 := by
  have hweight : (2 : ℤ) * Nat.card ((↑(CongruenceSubgroup.Gamma 1) : Subgroup (GL (Fin 2) ℝ)) ⧸
      (↑(CongruenceSubgroup.Gamma0 2) : Subgroup (GL (Fin 2) ℝ)).subgroupOf
        (↑(CongruenceSubgroup.Gamma 1))) = 6 := by
    rw [card_quotient_eq_three]; norm_num
  have hf0 : (f : ℍ → ℂ) = 0 :=
    (CuspForm.norm_eq_zero_iff (↑(CongruenceSubgroup.Gamma 1) : Subgroup (GL (Fin 2) ℝ)) f).1
      (S6_levelOne_eq_zero' hweight
        (CuspForm.norm (↑(CongruenceSubgroup.Gamma 1) : Subgroup (GL (Fin 2) ℝ)) f))
  exact DFunLike.coe_injective (by simpa using hf0)

end Assembly

section LevelOne

private lemma Gamma0_one_eq_top :
    (CongruenceSubgroup.Gamma0 1 : Subgroup SL(2, ℤ)) = ⊤ := by
  ext A
  simp [CongruenceSubgroup.Gamma0_mem, eq_iff_true_of_subsingleton]

private lemma coe_Gamma0_one_eq_SL :
    ((CongruenceSubgroup.Gamma0 1 : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) = 𝒮ℒ := by
  rw [Gamma0_one_eq_top]
  ext x
  simp [Subgroup.mem_map, MonoidHom.mem_range]

/-- The level-one analogue: weight `2 < 12`, so no norm is needed. -/
theorem S2_Gamma0_one_eq_zero (f : CuspForm (CongruenceSubgroup.Gamma0 1) 2) : f = 0 :=
  cuspForm_eq_zero_of_subgroup_eq coe_Gamma0_one_eq_SL.symm
    (fun g => rank_zero_iff_forall_zero.mp
      (CuspForm.rank_eq_zero_of_weight_lt_twelve (by norm_num)) g) f

end LevelOne

end ModularForm

end
