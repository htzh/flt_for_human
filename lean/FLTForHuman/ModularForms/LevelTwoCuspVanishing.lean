/-
  The endgame: **there are no weight-2 cusp forms on `Γ₀(2)`** (and the level-one
  analogue), as corollaries of the Sturm bound.

  For weight `2` the Sturm bound is
  `⌊2 · [SL(2, ℤ) : Γ] / 12⌋ = ⌊[SL(2, ℤ) : Γ] / 6⌋`, which is `0` for both
  `Γ(1)` (index 1) and `Γ₀(2)` (index 3). A cusp form has vanishing constant
  term, hence `q`-order `≥ 1 > 0`, so the bound applies with no other input: the
  only coefficient to check below the bound is the constant term.

  This replaces the earlier norm-based route (the cusp-form norm to a level-one
  weight-`6` form, then `CuspForm.rank_eq_zero_of_weight_lt_twelve`). The norm is
  the content of the general Sturm bound itself
  (`ModularForm.sturm_bound_of_isArithmetic`), so the two proofs are the same
  mathematics packaged at different levels; the only extra input here is the
  numerical index value `(Γ₀ 2).index = 3` (`Gamma0_two_index_eq_three`).

  FLT provenance, pinned `aa2d8b3`:
  `P2M/Sol/S_ModularForm_S2_Gamma0_2_eq_zero.lean` and
  `P2M/Sol/S_ModularForm_S2_Gamma0_one_eq_zero.lean`.
  https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularForm_S2_Gamma0_2_eq_zero.lean
  https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularForm_S2_Gamma0_one_eq_zero.lean

  The two public theorems keep their names, binders and types verbatim from their
  `Theorems/` wrappers.
-/
import FLTForHuman.ModularForms.Gamma0TwoIndex
import FLTForHuman.ModularForms.SturmBound
import Mathlib.NumberTheory.ModularForms.LevelOne.DimensionFormula

set_option autoImplicit false

noncomputable section

open UpperHalfPlane SlashInvariantForm Subgroup Matrix Matrix.SpecialLinearGroup
open scoped MatrixGroups ModularForm Topology Filter Manifold CongruenceSubgroup

namespace ModularForm

section Bridge

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

end Bridge

section LevelOne

private lemma Gamma0_one_eq_top :
    (CongruenceSubgroup.Gamma0 1 : Subgroup SL(2, ℤ)) = ⊤ := by
  ext A
  simp [CongruenceSubgroup.Gamma0_mem, eq_iff_true_of_subsingleton]

private lemma coe_Gamma0_one_eq_SL :
    ((CongruenceSubgroup.Gamma0 1 : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) = 𝒮ℒ := by
  rw [Gamma0_one_eq_top, ← CongruenceSubgroup.Gamma_one_top]
  exact coe_Gamma_one_eq_SL

/-- **Level one.** `S₂(SL(2, ℤ)) = 0`: the weight-`2` Sturm bound is
`⌊2 / 12⌋ = 0`, and a cusp form has vanishing constant term. -/
theorem S2_Gamma0_one_eq_zero (f : CuspForm (CongruenceSubgroup.Gamma0 1) 2) : f = 0 :=
  cuspForm_eq_zero_of_subgroup_eq coe_Gamma0_one_eq_SL.symm
    (fun g => CuspForm.toModularFormₗ_injective (by
      simpa using sturm_bound_levelOne (f := CuspForm.toModularFormₗ g) (by
        have h1 : (1 : ℕ∞) ≤ (qExpansion 1 ⇑g).order :=
          PowerSeries.one_le_order_iff_constCoeff_eq_zero.mpr (by
            simpa [PowerSeries.coeff_zero_eq_constantCoeff] using
              CuspFormClass.qExpansion_coeff_zero g one_pos one_mem_strictPeriods_SL)
        change (↑((2 : ℤ).toNat / 12) : ℕ∞) < (qExpansion 1 ⇑g).order
        norm_num
        exact lt_of_lt_of_le (by norm_num : (0 : ℕ∞) < 1) h1))) f

end LevelOne

section LevelTwo

/-- **Level two.** `S₂(Γ₀(2)) = 0`: the weight-`2` Sturm bound is
`⌊2 · 3 / 12⌋ = 0`, and a cusp form has vanishing constant term. -/
theorem S2_Gamma0_2_eq_zero (f : CuspForm (CongruenceSubgroup.Gamma0 2) 2) : f = 0 := by
  have hB : (((2 : ℤ) * (CongruenceSubgroup.Gamma0 2).index).toNat / 12) = 0 := by
    rw [Gamma0_two_index_eq_three]; norm_num
  have hM : CuspForm.toModularFormₗ (Γ := CongruenceSubgroup.Gamma0 2) (k := 2) f = 0 := by
    refine sturm_bound_Gamma0 2 _ (fun n hn => ?_)
    rw [hB] at hn
    have hn0 : n = 0 := by omega
    subst hn0
    change (qExpansion 1 ⇑f).coeff 0 = 0
    exact CuspFormClass.qExpansion_coeff_zero f one_pos
      (CongruenceSubgroup.one_mem_strictPeriods_Gamma0 2)
  exact CuspForm.toModularFormₗ_injective (by simpa using hM)

end LevelTwo

end ModularForm

end
