# The level-1/2 weight-2 cusp-form vanishing — measured record

**Scope.** FLT's `ModularForm.S2_Gamma0_2_eq_zero` and
`ModularForm.S2_Gamma0_one_eq_zero` (the `base/003` endgame). Both are leaves of
FLT's dependency graph (`cites: []`). They are consumed by
`FreyPackage.level_lowering_to_two_of_conductorLevel` and
`FreyPackage.no_frey_package` (level 2) and by
`CuspForm.heckeULin_eq_neg_atkinLehnerLin_of_prime_level` (level 1).

## Final layout (2026-09-23)

| module | role | lines |
|---|---|---|
| `FLTForHuman/ModularForms/SturmBound.lean` | the Sturm bound and its inputs, **plus the two cusp-form vanishing corollaries** at the end | 285 |
| `FLTForHuman/ModularForms/Gamma0TwoIndex.lean` | `[SL(2,ℤ) : Γ₀(2)] = 3` by the first column mod 2 | 137 |
| `Reserve/ModularForms/LevelTwoCuspVanishing.lean` | the **reserve norm route**: the two theorems by `CuspForm.norm` + weight-6 level-one vanishing, verbatim from commit `4c4f588` | 140 |
| `Reserve/ModularForms/CuspFormNorm.lean` | the cusp-form norm, the reserve route's input | 85 |
| `spec/LevelTwoCuspConsumer.lean` | Zones A–D wire test (vanishing, index, Sturm headlines, bridge) | 55 |

The two theorems are declared in **both** routes (the wrapper statements are
fixed), so `FLTForHuman/ModularForms/SturmBound.lean` and
`Reserve/ModularForms/LevelTwoCuspVanishing.lean` must never be imported
together. Each route alone is consistent: the reserve copy imports
`Reserve.ModularForms.CuspFormNorm` and `FLTForHuman.ModularForms.Gamma0TwoIndex`,
never `SturmBound`.

## Why the Sturm route, and how trivial it is

For weight `2` the Sturm bound is
`⌊2 · [SL(2,ℤ) : Γ] / 12⌋ = ⌊[SL(2,ℤ) : Γ] / 6⌋`, which is `0` at `Γ(1)`
(index 1) and `Γ₀(2)` (index 3). A cusp form has vanishing constant term
(`CuspFormClass.qExpansion_coeff_zero`), so the bound's only hypothesis below
`0` — the constant term — is discharged, and
`sturm_bound_levelOne`/`sturm_bound_Gamma0` applied to
`CuspForm.toModularFormₗ f` (then `toModularFormₗ_injective`) gives `f = 0`.
The only numerical input is `(Γ₀ 2).index = 3` from `Gamma0TwoIndex.lean`.

The norm is not a separate phenomenon: the general Sturm bound
(`ModularForm.sturm_bound_of_isArithmetic`) is proved *by* the norm, so the
reserve route and the Sturm route are the same mathematics packaged at
different levels. The reserve copy exists because the norm route is the one
`base/003` narrates, and because a from-scratch norm construction
(`CuspForm.norm`) is a genuine mathlib gap.

## Route history

1. `4c4f588` — the original port: `CuspFormNorm.lean`,
   `Gamma0TwoIndex.lean` and the norm-assembled `LevelTwoCuspVanishing.lean`
   under `FLTForHuman/ModularForms/`.
2. `8b02acf` — the Sturm bound port (`FLTForHuman/ModularForms/SturmBound.lean`).
3. `61ffe8a` — the two theorems re-proved as Sturm corollaries in a standalone
   `LevelTwoCuspVanishing.lean`; `CuspFormNorm.lean` moved to `Reserve/`.
4. **Final** — the Sturm corollaries merged into `SturmBound.lean`; the
   standalone module removed; the norm route restored verbatim from `4c4f588`
   into `Reserve/ModularForms/LevelTwoCuspVanishing.lean`.

## Checker

- `SOURCES` carries the two `Theorems/Thm_ModularForm_S2_Gamma0_{2,1}_eq_zero`
  wrappers and the two `S_` files; `PORT_FILES` the modules above.
- Final: **1,262 identical (69 promoted), 0 mismatched, 0 missing**, 14
  own-proof exemptions, 1,276 port declarations. The six declarations of the
  reserve norm route (`coe_Gamma_one_eq_SL`,
  `cuspForm_eq_zero_of_subgroup_eq`, `S6_levelOne_eq_zero`,
  `S6_levelOne_eq_zero'`, `S2_Gamma0_2_eq_zero`, `S2_Gamma0_one_eq_zero`) are the
  increase over the 1,256 of the pre-merge state, where the norm-route module had
  already been dropped.

## Verification

- `timeout 180 lake build`: **4,113 jobs, 0 warnings, no `sorry`** across
  `FLTForHuman` and `Reserve`.
- `#print axioms` on `ModularForm.S2_Gamma0_2_eq_zero`,
  `ModularForm.S2_Gamma0_one_eq_zero`, `ModularForm.coe_Gamma_one_eq_SL` and
  `ModularForm.cuspForm_eq_zero_of_subgroup_eq`:
  `[propext, Classical.choice, Quot.sound]`.
- `spec/LevelTwoCuspConsumer.lean`: exit 0, **0 errors, 0 warnings**.

## The type bridge the Sturm route needs

The target is `CuspForm (Γ₀ N) k`; the Sturm bound is about
`ModularForm (Γ₀ N) k`. In v4.34 `CuspForm` does not extend `ModularForm`
(`Basic.lean:82`), so the application goes through
`CuspForm.toModularFormₗ [Γ.HasDetOne] : CuspForm Γ k →ₗ[ℂ] ModularForm Γ k`
and `CuspForm.toModularFormₗ_injective` to return. The norm route avoided this
by defining `CuspForm.norm` directly on cusp forms (the pin's
`__ := ModularForm.norm ℋ f` inheritance fills `toFun`/`slash_action_eq'`/`holo'`
and leaves only `zero_at_cusps'`).

## v4.33 (note) → v4.34 (project) notes

- `CuspFormClass.qExpansion_coeff_zero` is the constant-term vanishing used for
  both Sturm corollaries; `PowerSeries.one_le_order_iff_constCoeff_eq_zero` turns
  it into the order condition of `sturm_bound_levelOne`.
- `tendsto_finset_prod` → `tendsto_finsetProd`; `CuspForm.coe_zero`/
  `ModularForm.coe_zero` are deprecated (the coercion is `simpa`); the pin's
  `import …DimensionFormulas.LevelOne` is deprecated in favour of
  `…LevelOne.DimensionFormula`.
- In `Gamma0TwoIndex.lean` the pin's inline witnesses `⟨!![⋯], by decide⟩` do not
  elaborate inside a quotient argument (the determinant does not reduce under
  `decide` there); they are the `private def`s `matS`/`matC`.
- The `Γ(1)` notation in the merged corollaries needs
  `open scoped CongruenceSubgroup` in `SturmBound.lean`.

## Pointers

- [../../base/003-no-level-2-weight-2-cusp-forms.md](../../base/003-no-level-2-weight-2-cusp-forms.md)
  — the norm proof as mathematics.
- [../../math/012-sturm-bound.md](../../math/012-sturm-bound.md) — the Sturm
  bound, whose general proof is that norm.
- [../../studies/hecke-finiteness-coverage.md](../../studies/hecke-finiteness-coverage.md)
  §4 — where the Sturm bound sits in the finiteness routes.
