# The level-2/level-1 cusp-form vanishing port — measured record

**Scope.** FLT's `ModularForm.S2_Gamma0_2_eq_zero` and
`ModularForm.S2_Gamma0_one_eq_zero` (the `base/003` endgame), ported into
`FLTForHuman/ModularForms/`. Both are leaves of FLT's dependency graph
(`cites: []`): mathlib's level-one dimension formula and the norm/trace
machinery are the only inputs. They are consumed by
`FreyPackage.level_lowering_to_two_of_conductorLevel` and
`FreyPackage.no_frey_package` (level 2) and by
`CuspForm.heckeULin_eq_neg_atkinLehnerLin_of_prime_level` (level 1).

## Deliverables

| module | role | lines |
|---|---|---|
| `ModularForms/CuspFormNorm.lean` | the norm of a cusp form | 81 |
| `ModularForms/Gamma0TwoIndex.lean` | `[SL(2,ℤ) : Γ₀(2)] = 3` by the first column mod 2 | 137 |
| `ModularForms/LevelTwoCuspVanishing.lean` | the two wrapper theorems and the assembly | 127 |
| `spec/LevelTwoCuspConsumer.lean` | Zones A–D wire test | 53 |

The pin is `S_ModularForm_S2_Gamma0_2_eq_zero.lean` (215 raw / 140 content) and
`S_ModularForm_S2_Gamma0_one_eq_zero.lean` (30 raw / 18 content). All `p2m_*`
scaffolding, the `local notation` (except `𝒬`, kept for the checker) and the
pin's `solution` glue are dropped.

## Checker

- `SOURCES` gains the two `Theorems/Thm_ModularForm_S2_Gamma0_{2,1}_eq_zero`
  wrappers and the two `S_` files; `PORT_FILES` gains the three modules.
- **1,240 → 1,250 identical (69 promoted), 0 mismatched, 0 missing**, 14
  own-proof exemptions, 1,264 port declarations. The two promoted declarations
  are `CuspForm.norm` and `CuspForm.norm_eq_zero_iff` (private in the pin, public
  here).

## Verification

- `timeout 180 lake build`: **4,110 jobs, 0 warnings, no `sorry`**.
- `#print axioms` on `ModularForm.S2_Gamma0_2_eq_zero`,
  `ModularForm.S2_Gamma0_one_eq_zero`, `ModularForm.Gamma0_two_index_eq_three`,
  `CuspForm.norm` and `CuspForm.norm_eq_zero_iff`:
  `[propext, Classical.choice, Quot.sound]`.
- `spec/LevelTwoCuspConsumer.lean`: exit 0, **0 errors, 0 warnings**; Zone D
  composes `CuspForm.norm_eq_zero_iff` with the vanishing theorem, the way the
  modularity route consumes it.

## v4.33 (note) → v4.34 (project) drift — proofs only

The statements are verbatim; the following proof-level adaptations were needed:

- **`CuspForm` no longer extends `ModularForm`** (v4.34 `Basic.lean:82`), so the
  pin's `__ := ModularForm.norm ℋ f` is not a parent assignment. Lean's
  `__ :=` inheritance still fills `toFun`/`slash_action_eq'`/`holo'` and leaves
  only `zero_at_cusps'`; the pin's proof of that field ports unchanged.
- `tendsto_finset_prod` → `tendsto_finsetProd` (the alias is deprecated).
- `CuspForm.coe_zero`/`ModularForm.coe_zero` are deprecated; the final coercion
  step is `simpa`.
- the pin's `import Mathlib.NumberTheory.ModularForms.DimensionFormulas.LevelOne`
  is deprecated; the project uses `Mathlib.NumberTheory.ModularForms.LevelOne.DimensionFormula`
  (as `HeckeFricke.lean` already does).
- the pin's inline witnesses `⟨!![⋯], by decide⟩` do not elaborate inside a
  quotient argument (the determinant does not reduce under `decide` there); they
  are the `private def`s `matS`/`matC`.
- the pin's `private scoped instance` of `IsFiniteRelIndex` is made a public
  anonymous instance, so a consumer can apply `CuspForm.norm` at
  `Γ(1) ⧸ Γ₀(2)` directly. Anonymous instances are invisible to the statement
  checker.

## Friction

- The `!![⋯]`/`decide` incompatibility cost the most iterations: `⟨!![...], by decide⟩`
  elaborates as an `SL(2,ℤ)` element in isolation but not when the expected type
  is reached through `QuotientGroup.mk`; naming the elements fixes it.
- The `𝒬` local notation is load-bearing for the checker: the port's
  `CuspForm.norm` statement must spell `Nat.card 𝒬` exactly as the pin does,
  since `norm` in `spec/check_flt_statements.py` only normalizes whitespace and
  the `ModularCurve.`/`AlgebraicCurve.` prefixes. Likewise `Γ(1)` and `𝒮ℒ` must
  be written as the pin writes them.
