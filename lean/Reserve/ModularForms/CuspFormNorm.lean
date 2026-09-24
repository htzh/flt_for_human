/-
  **Reserve.** The norm of a cusp form — a generic construction FLT adds on top
  of mathlib (FLT's, not the port's; see the provenance below). Kept out of the
  critical-path port: the `base/003` cusp-form vanishing is now a corollary of
  the Sturm bound (`FLTForHuman/ModularForms/SturmBound.lean`), whose general
  proof (`ModularForm.sturm_bound_of_isArithmetic`) internalises this norm.

  **It is not base/003-only.** FLT defines the same three declarations `private`
  and `p2m_export`s them a second time in
  `P2M/Sol/S_CuspForm_finiteDimensional_cuspForm.lean` lines 23–59, where they
  feed `CuspForm.finiteDimensional_cuspForm` and the wider cusp-form
  finite-dimensionality family — all inside `FLT.fermatLastTheorem`'s closure.
  This port writes the construction once for both sites, which is why it is kept
  rather than deleted. (It is a `def`, so the theorem-node graph does not show
  it; the second site was found by source grep.)

  **Caveat: it may turn out unnecessary at both sites.** Both FLT uses of the
  norm are proofs of the Sturm bound. The second file's section is literally
  `section SturmBound`, its
  `eq_zero_of_qExpansion_coeff_eq_zero`/`Gamma0_eq_zero_of_qExpansion_coeff_eq_zero`
  are the arithmetic-level and `Γ₀` Sturm bounds in coefficient form, and its
  ~300-line `normCofactor` prelude serves only that proof — the
  finite-dimensionality argument itself (`qCoeffTrunc` +
  `FiniteDimensional.of_injective`) uses only the vanishing lemma. When
  `CuspForm.finiteDimensional_*` is ported, the ported
  `sturm_bound_of_isArithmetic`/`sturm_bound_Gamma0` should replace the whole
  norm block, and this module may then stay unused; investigate before promoting
  it back into `FLTForHuman`. (See
  `studies/hecke-finiteness-coverage.md` §9.)

  Mathlib has `ModularForm.norm` (`Mathlib/NumberTheory/ModularForms/NormTrace.lean:108`),
  the product of the translates `f ∣[k] g_q⁻¹` over `ℋ ⧸ (𝒢 ⊓ ℋ)`, but it is a
  *modular* form: it carries the bounded-at-cusps condition of its factors. Both
  FLT sites need the analogous **cusp** form, so they supply the one missing field
  `zero_at_cusps'`: each factor is a translate of a cusp form, and a product of
  functions tending to `0` tends to `0`.

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
