# The level-2/level-1 cusp-form vanishing port — measured record

**Scope.** FLT's `ModularForm.S2_Gamma0_2_eq_zero` and
`ModularForm.S2_Gamma0_one_eq_zero` (the `base/003` endgame), ported into
`FLTForHuman/ModularForms/`. Both are leaves of FLT's dependency graph
(`cites: []`). They are consumed by
`FreyPackage.level_lowering_to_two_of_conductorLevel` and
`FreyPackage.no_frey_package` (level 2) and by
`CuspForm.heckeULin_eq_neg_atkinLehnerLin_of_prime_level` (level 1).

> **Restructured (2026-09-23, after the Sturm-bound port).** The two theorems are
> now proved as **corollaries of the Sturm bound**: for weight `2` the bound is
> `⌊2 · [SL(2,ℤ) : Γ] / 12⌋ = ⌊[SL(2,ℤ) : Γ] / 6⌋`, which is `0` at `Γ(1)`
> (index 1) and `Γ₀(2)` (index 3); a cusp form has vanishing constant term
> (`CuspFormClass.qExpansion_coeff_zero`), so
> `sturm_bound_levelOne`/`sturm_bound_Gamma0` applied to
> `CuspForm.toModularFormₗ f` (then injectivity of the inclusion) gives `f = 0`.
> The only numerical input is `(Γ₀ 2).index = 3` from `Gamma0TwoIndex.lean`.
>
> This supersedes the norm route: the norm is the content of the general Sturm
> bound (`ModularForm.sturm_bound_of_isArithmetic`), so the old proof (norm to a
> level-one weight-`6` form, then the weight-`< 12` cusp vanishing) and the new
> one are the same mathematics packaged at different levels. The norm-only
> declarations `S6_levelOne_eq_zero`/`'`, the quotient-card lemma and the
> `IsFiniteRelIndex` instance were dropped; the checker moved
> **1,258 → 1,256**. `CuspFormNorm.lean` is retired (see the table).

The original norm route is still the mathematics of
[../../base/003-no-level-2-weight-2-cusp-forms.md](../../base/003-no-level-2-weight-2-cusp-forms.md)
§3; the Sturm bound is `../../math/012-sturm-bound.md`.

## Deliverables

| module | role | lines |
|---|---|---|
| `ModularForms/LevelTwoCuspVanishing.lean` | the two wrapper theorems, as Sturm corollaries | 105 |
| `ModularForms/Gamma0TwoIndex.lean` | `[SL(2,ℤ) : Γ₀(2)] = 3` by the first column mod 2 | 137 |
| `spec/LevelTwoCuspConsumer.lean` | Zones A–D wire test (vanishing, index, Sturm headlines, bridge) | 55 |
| *(`Reserve`)* `Reserve/ModularForms/CuspFormNorm.lean` | the norm of a cusp form; kept off the critical path | 81 |

The pin is `S_ModularForm_S2_Gamma0_2_eq_zero.lean` (215 raw / 140 content) and
`S_ModularForm_S2_Gamma0_one_eq_zero.lean` (30 raw / 18 content). All `p2m_*`
scaffolding, the `local notation` (except `𝒬`, kept for the checker) and the
pin's `solution` glue are dropped.

## Checker

- `SOURCES` gains the two `Theorems/Thm_ModularForm_S2_Gamma0_{2,1}_eq_zero`
  wrappers and the two `S_` files; `PORT_FILES` gains the modules.
- After the restructure: **1,256 identical (69 promoted), 0 mismatched, 0
  missing**, 14 own-proof exemptions, 1,270 port declarations. The two
  declarations dropped from the count are `S6_levelOne_eq_zero` and
  `S6_levelOne_eq_zero'` (public port twins of pin declarations, no longer
  needed). The promoted declarations `CuspForm.norm`/`CuspForm.norm_eq_zero_iff`
  are kept in the reserve module `Reserve/ModularForms/CuspFormNorm.lean`, which
  is still listed in `PORT_FILES` and built (the `Reserve` library is a
  `@[default_target]`), so the count is unchanged by the move.

## The `Reserve` library

Superseded-but-verified modules live in the `Reserve/` library (module prefix
`Reserve.*`), added to `lakefile.lean` as a second `@[default_target] lean_lib`.
`Reserve` may import `FLTForHuman`; `FLTForHuman` must never import `Reserve`.
The cusp-form norm moved there because the Sturm route superseded it, and it is a
genuine mathlib gap (mathlib has `ModularForm.norm` but not `CuspForm.norm`) worth
keeping for reserve work.

## Verification

- `timeout 180 lake build`: **4,112 jobs, 0 warnings, no `sorry`**.
- `#print axioms` on `ModularForm.S2_Gamma0_2_eq_zero`,
  `ModularForm.S2_Gamma0_one_eq_zero`, `ModularForm.coe_Gamma_one_eq_SL` and
  `ModularForm.cuspForm_eq_zero_of_subgroup_eq`:
  `[propext, Classical.choice, Quot.sound]`.
- `spec/LevelTwoCuspConsumer.lean`: exit 0, **0 errors, 0 warnings**.

## The type bridge the Sturm route needs

The target is `CuspForm (Γ₀ N) k`; the Sturm bound is about
`ModularForm (Γ₀ N) k`. In v4.34 `CuspForm` does not extend `ModularForm`
(`Basic.lean:82`), so the application goes through the inclusion
`CuspForm.toModularFormₗ [Γ.HasDetOne] : CuspForm Γ k →ₗ[ℂ] ModularForm Γ k`
and `CuspForm.toModularFormₗ_injective` to return. The old norm route avoided
this by defining `CuspForm.norm` directly on cusp forms (the pin's
`__ := ModularForm.norm ℋ f` inheritance fills `toFun`/`slash_action_eq'`/`holo'`
and leaves only `zero_at_cusps'`).

## Other v4.33 (note) → v4.34 (project) notes

- `CuspFormClass.qExpansion_coeff_zero` is the constant-term vanishing used for
  both theorems; `PowerSeries.one_le_order_iff_constCoeff_eq_zero` turns it into
  the order condition of `sturm_bound_levelOne`.
- `tendsto_finset_prod` → `tendsto_finsetProd`; `CuspForm.coe_zero`/
  `ModularForm.coe_zero` are deprecated (the coercion is `simpa`); the pin's
  `import …DimensionFormulas.LevelOne` is deprecated in favour of
  `…LevelOne.DimensionFormula`.
- In `Gamma0TwoIndex.lean` the pin's inline witnesses `⟨!![⋯], by decide⟩` do not
  elaborate inside a quotient argument (the determinant does not reduce under
  `decide` there); they are the `private def`s `matS`/`matC`.

## Pointers

- [../../base/003-no-level-2-weight-2-cusp-forms.md](../../base/003-no-level-2-weight-2-cusp-forms.md)
  — the norm proof as mathematics.
- [../../math/012-sturm-bound.md](../../math/012-sturm-bound.md) — the Sturm
  bound, whose general proof is that norm.
- [../../studies/hecke-finiteness-coverage.md](../../studies/hecke-finiteness-coverage.md)
  §4 — where the Sturm bound sits in the finiteness routes.
