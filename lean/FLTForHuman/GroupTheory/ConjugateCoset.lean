/-
  Conjugation is a bijection of coset spaces.  If an element `g` preserves a subgroup `G`
  and conjugates `H ≤ G` onto `K ≤ G`, then `a H ↦ g a g⁻¹ K` matches the cosets, so `H`
  and `K` have the same index in `G`.  The subgroup isomorphism `c : H ≃ K` records the
  conjugation on `H`; no normality of `H` or `K` is used.

  The ambient-group form is mathlib's `Subgroup.relIndex_pointwise_smul`; the
  isomorphism form is mathlib's `Subgroup.index_map_equiv`.
-/
import Mathlib.GroupTheory.Index
import Mathlib.Algebra.Group.Subgroup.Pointwise

set_option autoImplicit false

open scoped Pointwise

namespace Subgroup

/-- Conjugation by an element `g` that preserves `G` and carries `H` onto `K` preserves the
relative index.  This is the index form of the coset bijection `a H ↦ g a g⁻¹ K`. -/
theorem relIndex_eq_of_smul {A : Type*} [Group A] {G H K : Subgroup A}
    (g : A) (hG : MulAut.conj g • G = G) (hH : MulAut.conj g • H = K) :
    H.relIndex G = K.relIndex G := by
  rw [← Subgroup.relIndex_pointwise_smul (MulAut.conj g) H G, hH, hG]

/-- An isomorphism `e : G ≃* G'` matches the cosets of `Λ ≤ G` with those of
`Λ.map e ≤ G'`; in particular the two quotients have the same cardinality. -/
theorem card_quotient_eq_of_map {G G' : Type*} [Group G] [Group G'] {Λ : Subgroup G}
    (e : G ≃* G') [Fintype (G ⧸ Λ)] [Fintype (G' ⧸ Λ.map (e : G →* G'))] :
    Fintype.card (G ⧸ Λ) = Fintype.card (G' ⧸ Λ.map (e : G →* G')) := by
  rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card,
    ← Subgroup.index_eq_card, ← Subgroup.index_eq_card, Subgroup.index_map_equiv]

/-- Conjugation by an element `g` that preserves `G` and carries `H` onto `K` gives
`Fintype.card (G ⧸ H) = Fintype.card (G ⧸ K)`. -/
theorem card_quotient_eq_of_smul {A : Type*} [Group A] {G H K : Subgroup A}
    (g : A) (hG : MulAut.conj g • G = G) (hH : MulAut.conj g • H = K)
    [Fintype (G ⧸ H.subgroupOf G)] [Fintype (G ⧸ K.subgroupOf G)] :
    Fintype.card (G ⧸ H.subgroupOf G) = Fintype.card (G ⧸ K.subgroupOf G) := by
  have hrel : H.relIndex G = K.relIndex G := by
    rw [← Subgroup.relIndex_pointwise_smul (MulAut.conj g) H G, hH, hG]
  simpa only [Subgroup.relIndex, Subgroup.index_eq_card, Nat.card_eq_fintype_card] using hrel

/-- The same with the conjugation recorded by a subgroup isomorphism `c : H ≃ K`. -/
theorem card_quotient_eq_of_conj {A : Type*} [Group A] {G H K : Subgroup A}
    (g : A) (c : H ≃ K)
    (hc : ∀ h : H, g * (h : A) = (c h : A) * g)
    (hG : MulAut.conj g • G = G)
    [Fintype (G ⧸ H.subgroupOf G)] [Fintype (G ⧸ K.subgroupOf G)] :
    Fintype.card (G ⧸ H.subgroupOf G) = Fintype.card (G ⧸ K.subgroupOf G) := by
  have hH : MulAut.conj g • H = K := by
    ext x
    constructor
    · rintro ⟨h, hh, rfl⟩
      show MulAut.conj g (h : A) ∈ K
      rw [MulAut.conj_apply]
      have h' : g * (h : A) = (c ⟨h, hh⟩ : A) * g := hc ⟨h, hh⟩
      rw [h', mul_assoc, mul_inv_cancel, mul_one]
      exact (c ⟨h, hh⟩).2
    · intro hx
      refine ⟨c.symm ⟨x, hx⟩, (c.symm ⟨x, hx⟩).2, ?_⟩
      show MulAut.conj g (c.symm ⟨x, hx⟩ : A) = x
      rw [MulAut.conj_apply]
      have h := hc (c.symm ⟨x, hx⟩)
      rw [h, Equiv.apply_symm_apply, mul_assoc, mul_inv_cancel, mul_one]
  exact Subgroup.card_quotient_eq_of_smul g hG hH

end Subgroup
