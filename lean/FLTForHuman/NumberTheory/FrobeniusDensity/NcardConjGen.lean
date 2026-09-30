/-
  The group-theoretic criterion behind the Frobenius-density statement: the set
  of conjugators `g` of a power `σ ^ k` (with `k` coprime to `orderOf σ`) to `τ`
  is nonempty exactly when `τ` is conjugate to some such power.

  This is the `FrobeniusDensity.ncard_conj_gen_ne_zero_iff` node of S7-III, used
  by `FrobeniusDensity.statement_of_degOneAsymptotic`. It is generic group
  theory, so it has no Frobenius-specific import.

  Transcribed from the pinned FLT solution file (`aa2d8b3`,
  `P2M/Sol/S_FrobeniusDensity_ncard_conj_gen_ne_zero_iff.lean`). The mathematics
  is math/018 §6.
-/
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Data.Set.Card

set_option autoImplicit false

namespace FrobeniusDensity

theorem ncard_conj_gen_ne_zero_iff {G : Type*} [Group G] [Finite G] (σ τ : G) :
    {g : G | ∃ k : ℕ, k.Coprime (orderOf σ) ∧ g * σ ^ k * g⁻¹ = τ}.ncard ≠ 0
      ↔ ∃ k : ℕ, k.Coprime (orderOf σ) ∧ IsConj (σ ^ k) τ := by
  constructor
  · intro hne
    obtain ⟨g, k, hk, hgk⟩ := Set.nonempty_of_ncard_ne_zero hne
    exact ⟨k, hk, isConj_iff.mpr ⟨g, hgk⟩⟩
  · rintro ⟨k, hk, hconj⟩
    obtain ⟨g, hg⟩ := isConj_iff.mp hconj
    exact Set.ncard_ne_zero_of_mem (a := g) ⟨k, hk, hg⟩ (Set.toFinite _)

end FrobeniusDensity
