/-
  The **norm of a cusp form** — the generic construction FLT adds on top of
  mathlib.

  Mathlib has `ModularForm.norm` (`Mathlib/NumberTheory/ModularForms/NormTrace.lean:108`),
  the product of the translates `f ∣[k] g_q⁻¹` over `ℋ ⧸ (𝒢 ⊓ ℋ)`, but it is a
  *modular* form: it carries the bounded-at-cusps condition of its factors. The
  `S_ModularForm_S2_Gamma0_2_eq_zero` file needs the analogous **cusp** form, so it
  supplies the one missing field `zero_at_cusps'`: each factor is a translate of a
  cusp form, and a product of functions tending to `0` tends to `0`. That is the
  only statement in the level-2 vanishing proof not already in mathlib.

  This module is that construction, once:
  `CuspForm.norm`, the coercion bridge
  `CuspForm.coe_norm_eq_coe_modularFormNorm`, and the zero-set statement
  `CuspForm.norm_eq_zero_iff` (the useful direction: the norm vanishes only on
  zero forms; it is *not* linear — it is homogeneous of degree the index).

  FLT provenance, pinned `aa2d8b3`:
  `P2M/Sol/S_ModularForm_S2_Gamma0_2_eq_zero.lean` lines 18–70.
  https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularForm_S2_Gamma0_2_eq_zero.lean

  v4.34 adaptations (proofs only; the statements are verbatim):
  `CuspForm` no longer extends `ModularForm`, but the `__ := ModularForm.norm ℋ f`
  inheritance still fills `toFun`/`slash_action_eq'`/`holo'` and leaves
  `zero_at_cusps'` to us; the deprecated `tendsto_finset_prod` is spelled
  `tendsto_finsetProd`; and the `coe_zero` lemmas are now `map_zero`/`simp`.
-/
import Mathlib.NumberTheory.ModularForms.NormTrace

set_option autoImplicit false

noncomputable section

open UpperHalfPlane SlashInvariantForm
open scoped ModularForm Topology Filter Manifold

variable {𝒢 ℋ : Subgroup (GL (Fin 2) ℝ)} {F : Type*} (f : F) [FunLike F ℍ ℂ] {k : ℤ}

local notation "𝒬" => ℋ ⧸ (𝒢.subgroupOf ℋ)

variable (ℋ) [𝒢.IsFiniteRelIndex ℋ]

/-- The norm of a cusp form: the product of its translates over the cosets
`ℋ ⧸ 𝒢`, as a cusp form of weight `k` times the index. Mathlib's
`ModularForm.norm` gives every field but `zero_at_cusps'`, which the product
inherits from its factors. -/
@[simps! -fullyApplied]
noncomputable def CuspForm.norm [ℋ.HasDetPlusMinusOne] [CuspFormClass F 𝒢 k] :
    CuspForm ℋ (k * Nat.card 𝒬) where
  __ := ModularForm.norm ℋ f
  zero_at_cusps' h γ := by
    rintro rfl
    simp_rw [ModularForm.toFun_eq_coe, ModularForm.coe_norm, IsZeroAtImInfty, Filter.ZeroAtFilter]
    let := Fintype.ofFinite 𝒬
    rw [Nat.card_eq_fintype_card, ← Finset.card_univ, ModularForm.prod_slash]
    refine Filter.ZeroAtFilter.smul _ ?_
    show Filter.Tendsto _ _ (nhds 0)
    rw [show (0 : ℂ) = ∏ _q : 𝒬, (0 : ℂ) by
        rw [Finset.prod_const, Finset.card_univ, zero_pow Fintype.card_ne_zero],
      Finset.prod_fn]
    refine tendsto_finsetProd _ (Quotient.forall.mpr fun ⟨r, hr⟩ _ ↦ ?_)
    refine (CuspForm.translate f _).zero_at_cusps' ?_ γ rfl
    simpa using h.of_isFiniteRelIndex_conj hr

/-- The coefficient of the cusp-form norm is the modular-form norm — the
`zero_at_cusps'` field is invisible to the function. -/
@[simp]
lemma CuspForm.coe_norm_eq_coe_modularFormNorm [ℋ.HasDetPlusMinusOne] [CuspFormClass F 𝒢 k] :
    (CuspForm.norm ℋ f : ℍ → ℂ) = (ModularForm.norm ℋ f : ℍ → ℂ) := rfl

/-- The norm vanishes only on zero forms; the transport of
`ModularForm.norm_eq_zero_iff` to cusp forms. -/
lemma CuspForm.norm_eq_zero_iff [ℋ.HasDetPlusMinusOne] [CuspFormClass F 𝒢 k] :
    CuspForm.norm ℋ f = 0 ↔ (f : ℍ → ℂ) = 0 := by
  rw [← ModularForm.norm_eq_zero_iff ℋ f, ← DFunLike.coe_injective.eq_iff,
    ← @DFunLike.coe_injective.eq_iff (ModularForm ℋ (k * Nat.card 𝒬)),
    CuspForm.coe_norm_eq_coe_modularFormNorm]
  simp

end
