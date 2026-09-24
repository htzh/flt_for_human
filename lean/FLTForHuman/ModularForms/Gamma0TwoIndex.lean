/-
  The index `[SL(2, ℤ) : Γ₀(2)] = 3`, counted through the **first column modulo 2**.

  The map `g ↦ (g 0 0, g 1 0) mod 2` sends `SL(2, ℤ)` to the three nonzero vectors
  of `(ZMod 2)²`, is constant on left cosets of `Γ₀(2)` (a matrix of `Γ₀(2)` has
  first column `(1, 0)` mod 2), and is injective (the lower-left entry of
  `g₁⁻¹ g₂` is `-c₁a₂ + a₁c₂ ≡ 0`) and surjective (witnesses `S`, `1`,
  `[[1,0],[1,1]]`). Hence `SL(2, ℤ) ⧸ Γ₀(2) ≃ {p ≠ 0}` and the index is `3`.

  FLT provenance, pinned `aa2d8b3`:
  `P2M/Sol/S_ModularForm_S2_Gamma0_2_eq_zero.lean` lines 94–174.
  https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularForm_S2_Gamma0_2_eq_zero.lean

  The pin defines the coset/projection helpers `private`; they are reproduced
  `private` here, and only the headline `Gamma0_two_index_eq_three` is public.
  v4.34 adaptation (proof only): the two nonzero witnesses other than `1` are
  packaged as the `private def`s `matS`/`matC`, since `by decide` does not reduce
  an inline `!![⋯]` matrix's determinant in the quotient argument.
-/
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.GroupTheory.Index
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.FinCases

set_option autoImplicit false

noncomputable section

open Subgroup Matrix Matrix.SpecialLinearGroup
open scoped MatrixGroups CongruenceSubgroup

namespace ModularForm

section Gamma0TwoIndex

/-- The first column of `g`, read modulo `2`. -/
private def firstColMod2 (g : SL(2, ℤ)) : ZMod 2 × ZMod 2 :=
  ((g.1 0 0 : ZMod 2), (g.1 1 0 : ZMod 2))

/-- The determinant identity `ad - bc = 1`, read in `ZMod 2`. -/
private lemma det_eq_one_mod2 (g : SL(2, ℤ)) :
    (g.1 0 0 : ZMod 2) * g.1 1 1 - g.1 0 1 * g.1 1 0 = 1 := by
  have h := g.2
  rw [Matrix.det_fin_two] at h
  have := congrArg (fun n : ℤ => (n : ZMod 2)) h
  push_cast at this; exact this

/-- The first column is never zero: `a ≡ c ≡ 0` would force `0 = 1` in `ZMod 2`. -/
private lemma firstColMod2_ne_zero (g : SL(2, ℤ)) : firstColMod2 g ≠ 0 := by
  intro h
  rw [firstColMod2, Prod.ext_iff] at h
  obtain ⟨h00, h10⟩ := h
  simp only [Prod.fst_zero, Prod.snd_zero] at h00 h10
  have hdet := det_eq_one_mod2 g
  rw [h00, h10, zero_mul, mul_zero, sub_zero] at hdet
  exact one_ne_zero hdet.symm

/-- A matrix of `Γ₀(2)` has `a ≡ 1` in `ZMod 2`. -/
private lemma Gamma0_two_diag_eq_one {h : SL(2, ℤ)}
    (hh : h ∈ CongruenceSubgroup.Gamma0 2) : (h.1 0 0 : ZMod 2) = 1 := by
  have hh10 : (h.1 1 0 : ZMod 2) = 0 := CongruenceSubgroup.Gamma0_mem.1 hh
  have hdet := det_eq_one_mod2 h
  rw [hh10, mul_zero, sub_zero] at hdet
  exact (show ∀ a b : ZMod 2, a * b = 1 → a = 1 by decide) _ _ hdet

/-- The first column is constant on left cosets of `Γ₀(2)`, so it descends. -/
private lemma firstColMod2_mul_mem (g : SL(2, ℤ)) {h : SL(2, ℤ)}
    (hh : h ∈ CongruenceSubgroup.Gamma0 2) : firstColMod2 (g * h) = firstColMod2 g := by
  have hh10 : (h.1 1 0 : ZMod 2) = 0 := CongruenceSubgroup.Gamma0_mem.1 hh
  have hh00 : (h.1 0 0 : ZMod 2) = 1 := Gamma0_two_diag_eq_one hh
  have hmul : ∀ i : Fin 2, (g * h).1 i 0 = g.1 i 0 * h.1 0 0 + g.1 i 1 * h.1 1 0 := fun i => by
    simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
  unfold firstColMod2
  refine Prod.ext ?_ ?_ <;> simp only [hmul] <;> push_cast <;> rw [hh10, hh00] <;> ring

/-- The first-column map on the coset space `SL(2, ℤ) ⧸ Γ₀(2)`. -/
private def cosetToProj : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 2 →
    {p : ZMod 2 × ZMod 2 // p ≠ 0} :=
  Quotient.lift (fun g => ⟨firstColMod2 g, firstColMod2_ne_zero g⟩) fun g₁ g₂ hg => by
    have hg' : g₁⁻¹ * g₂ ∈ CongruenceSubgroup.Gamma0 2 := QuotientGroup.leftRel_apply.mp hg
    refine Subtype.ext ?_
    show firstColMod2 g₁ = firstColMod2 g₂
    conv_rhs => rw [show g₂ = g₁ * (g₁⁻¹ * g₂) by group]
    exact (firstColMod2_mul_mem g₁ hg').symm

@[simp] private lemma cosetToProj_mk (g : SL(2, ℤ)) :
    cosetToProj (QuotientGroup.mk g) = ⟨firstColMod2 g, firstColMod2_ne_zero g⟩ := rfl

/-- `cosetToProj` is injective: equal first columns force `g₁⁻¹ g₂ ∈ Γ₀(2)`. -/
private lemma cosetToProj_injective : Function.Injective cosetToProj := by
  rintro ⟨g₁⟩ ⟨g₂⟩ heq
  have heq' : firstColMod2 g₁ = firstColMod2 g₂ := congrArg Subtype.val heq
  rw [firstColMod2, firstColMod2, Prod.mk.injEq] at heq'
  obtain ⟨h00, h10⟩ := heq'
  refine Quotient.sound (QuotientGroup.leftRel_apply.mpr ?_)
  rw [CongruenceSubgroup.Gamma0_mem]
  have hinv10 : (g₁⁻¹).1 1 0 = -g₁.1 1 0 := by
    rw [Matrix.SpecialLinearGroup.SL2_inv_expl]; simp
  have hinv11 : (g₁⁻¹).1 1 1 = g₁.1 0 0 := by
    rw [Matrix.SpecialLinearGroup.SL2_inv_expl]; simp
  have hmul : (g₁⁻¹ * g₂).1 1 0 = (g₁⁻¹).1 1 0 * g₂.1 0 0 + (g₁⁻¹).1 1 1 * g₂.1 1 0 := by
    simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
  rw [hmul, hinv10, hinv11]
  push_cast
  rw [h00, h10]; ring

/-- The two nonzero witnesses other than `1`; the pin writes them inline, but here
`by decide` needs the matrix type to be known from the subtype. -/
private def matS : SL(2, ℤ) := ⟨!![(0:ℤ), -1; 1, 0], by decide⟩

private def matC : SL(2, ℤ) := ⟨!![(1:ℤ), 0; 1, 1], by decide⟩

/-- `cosetToProj` is surjective onto the three nonzero vectors. -/
private lemma cosetToProj_surjective : Function.Surjective cosetToProj := by
  rintro ⟨p, hp⟩
  have key : p = (0, 1) ∨ p = (1, 0) ∨ p = (1, 1) :=
    (show ∀ q : ZMod 2 × ZMod 2, q ≠ 0 → q = (0,1) ∨ q = (1,0) ∨ q = (1,1) by decide) p hp
  rcases key with rfl | rfl | rfl
  · refine ⟨QuotientGroup.mk matS, ?_⟩
    rw [cosetToProj_mk, Subtype.mk.injEq]; decide
  · refine ⟨QuotientGroup.mk 1, ?_⟩
    rw [cosetToProj_mk, Subtype.mk.injEq]; decide
  · refine ⟨QuotientGroup.mk matC, ?_⟩
    rw [cosetToProj_mk, Subtype.mk.injEq]; decide

/-- **The index is three.** `SL(2, ℤ) ⧸ Γ₀(2) ≃ {p : (ZMod 2)² // p ≠ 0}`. -/
theorem Gamma0_two_index_eq_three : (CongruenceSubgroup.Gamma0 2).index = 3 := by
  rw [Subgroup.index,
    Nat.card_congr (Equiv.ofBijective _ ⟨cosetToProj_injective, cosetToProj_surjective⟩),
    Nat.card_eq_fintype_card]
  decide

end Gamma0TwoIndex

end ModularForm

end
