# Topic 6: the bundled linear maps

**Status: planned (not started).** Second topic of [SET-3](SET-3.md). This is the
payoff of SET 1–2: the pin's `Definitions/Def_ModularForm_HeckeOperatorForms.lean`
turns `heckeU`/`heckeT` into linear endomorphisms of `ModularForm (Γ₀(N)) k` and
`CuspForm (Γ₀(N)) k`, with the level split in the hypotheses (`p ∤ N` for `T_p`,
`p ∣ N` for `U_p`). Every `toFun` obligation is a theorem SET 1–2 already proved,
so this topic is assembly.

**Audience.** A fresh session taking the second SET-3 topic. Read
[SET-3.md](SET-3.md) §0–§3; the pin's
`Definitions/Def_ModularForm_HeckeOperatorForms.lean` (112 lines); and the four
modules it builds on — `HeckeInvariance.lean`, `HeckeAnalytic.lean`,
`HeckeCusps.lean`, `Defs/HeckeOperator.lean`.

**Goal.** One new module `FLTForHuman/ModularForms/HeckeOperatorForms.lean` with
the pin's twelve declarations verbatim:

```lean
def ModularForm.heckeTLin (k : ℤ) (hp : p.Prime) (hpN : ¬ p ∣ N) :
    ModularForm (CongruenceSubgroup.Gamma0 N) k →ₗ[ℂ] ModularForm (CongruenceSubgroup.Gamma0 N) k
def ModularForm.heckeULin (k : ℤ) [NeZero N] (hpN : p ∣ N) :
    ModularForm (CongruenceSubgroup.Gamma0 N) k →ₗ[ℂ] ModularForm (CongruenceSubgroup.Gamma0 N) k
-- and the same two in namespace CuspForm, plus for each:
-- coe_heckeTLin_apply, coe_heckeULin_apply, heckeTLin_apply_apply, heckeULin_apply_apply
```

and the downstream thin wrappers:

- `CuspForm.qExpansion_heckeTLin` (pin file 19 lines):
  `qExpansion 1 ⇑(heckeTLin 2 hp hpN f) = PowerSeries.heckeT p 2 (qExpansion 1 ⇑f)`;
- `CuspForm.exists_coe_eq_heckeT` and `CuspForm.exists_coe_eq_heckeU` (7 lines
  each): a cusp form with a prescribed coercion.

## 1. Why this topic, and what is settled

- **The bundling is assembly.** Each `toFun` field is exactly one SET 1–2 export:

  | field | source |
  |---|---|
  | `slash_action_eq'` | `ModularForm.heckeT_slash_eq_self_of_mem_Gamma0` / `…heckeU…` (T1) |
  | `holo'` | `ModularForm.mdifferentiable_heckeT` / `…heckeU` (T3) |
  | `bdd_at_cusps'` | `ModularFormClass.isBoundedAt_heckeT` / `…heckeU` (T4) |
  | `zero_at_cusps'` | `CuspFormClass.isZeroAt_heckeT` / `…heckeU` (T4) |
  | `map_add'`, `map_smul'` | `heckeT_add`/`heckeT_smul`, `heckeU_add`/`heckeU_smul` (T0, `Defs/HeckeOperator.lean`) |

  `heckeTLin` must `haveI : NeZero N := ⟨fun h => hpN (h ▸ dvd_zero p)⟩` as the pin
  does; `heckeULin` takes `[NeZero N]` explicitly.
- **The level split is the hypotheses.** Do not add a `p ≠ 0`/`p.Prime` hypothesis
  or a hypothesis-free variant: the checker diffs the binders against the
  `Definitions/` declaration.
- **Two thin downstream wrappers belong here.** `CuspForm.qExpansion_heckeTLin`
  needs T5's `PowerSeries.heckeT` and the bundled map; the two `exists_coe_eq_*`
  wrappers produce a `CuspForm` from a coercion equality and consume
  `heckeTLin`/`heckeULin` (or T1's invariance directly) — check the pin's proof
  and import what it uses.

**Settled: module placement.** The pin calls the file a *definition* module, but
the port's `Defs/` layer is the operator block and its representatives; the
bundling is the result that consumes the invariance/analytic/cusp layers. Put it
at `FLTForHuman/ModularForms/HeckeOperatorForms.lean` (top level, like
`HeckeInvariance.lean`), and record the placement divergence in the header.

**Settled: no `ModularForm.heckeTLin_comm` here.** Commutation and the algebra
are T7.

## 2. The scouted inventory

| pin declaration | pin line | target | note |
|---|---|---|---|
| `ModularForm.heckeTLin` | 20 | public def | `toFun` from the five fields above |
| `ModularForm.heckeULin` | 34 | public def | |
| `coe_heckeTLin_apply`, `coe_heckeULin_apply` | 47, 50 | public `@[simp]` `rfl`s | |
| `heckeTLin_apply_apply`, `heckeULin_apply_apply` | 53, 57 | public `rfl`s | |
| `CuspForm.heckeTLin` | 69 | public def | same shape, `zero_at_cusps'` instead of `bdd_at_cusps'` |
| `CuspForm.heckeULin` | 83 | public def | |
| `coe_*`/`_apply_apply` ×4 | 96–108 | public `rfl`s | |
| `CuspForm.qExpansion_heckeTLin` | 19-line file | public target | uses T5's `PowerSeries.heckeT` |
| `CuspForm.exists_coe_eq_heckeT`, `…heckeU` | 7-line files | public targets | |

Route notes:

- The `map_add'`/`map_smul'` fields go through `DFunLike.coe_injective` and the
  T0 linearity lemmas (`heckeT_add`, `heckeT_smul`), exactly as the pin; the
  coercion in the `show` is `ModularForm.coe_add`/`IsGLPos.coe_smul` for the
  bundled form and `CuspForm.coe_add`/`IsGLPos.coe_smul` for the cusp form.
- `slash_action_eq'` receives `f`'s own invariance as
  `fun γ hγ => SlashInvariantFormClass.slash_action_eq f γ hγ` and passes it to
  T1's theorem; do not reprove the invariance.
- `holo'`/`bdd_at_cusps'`/`zero_at_cusps'` are the pin's `ModularFormClass.holo f`
  / `ModularFormClass.bdd_at_cusps f hc` / `CuspFormClass.isZeroAt…` calls into
  T3/T4.
- `CuspForm.qExpansion_heckeTLin` is a two-line rewrite of the bundled `qExpansion`
  through T5's `PowerSeries.heckeT`; import `HeckeQCoeff` for the formal operator
  (or just `Defs/FormalHeckeOperators`).

## 3. What is different about this topic

- **It is the first topic with no new mathematics.** If any field needs a proof
  the layers do not already have, that is a finding: the layering was wrong, and
  the fix belongs in T1/T3/T4, not here.
- **The checker is the whole test.** These twelve declarations have no `Thm_`
  wrappers; the checker verifies them by name against
  `Definitions/Def_ModularForm_HeckeOperatorForms.lean`, so a binder drift shows
  up immediately.
- **The `heckeULin` `NeZero` asymmetry** (`heckeTLin` derives it, `heckeULin`
  takes it) is the pin's and must be kept; it is easy to "fix" and wrong to.
- **No commutation.** Resist adding `heckeTLin_comm` when it is in reach; T7 owns
  it.

## 4. Budget

**1–2 goal rounds.** The module is ~150–200 lines of assembly; one round should
land it, the second is the downstream wrappers and bookkeeping.

**Stop early on**: a `toFun` field needing a lemma not among the SET 1–2 exports
(report which, and whether it belongs in T1/T3/T4); a binder that will not match
the pin's `Definitions/` text; or `CuspForm.qExpansion_heckeTLin` pulling in a
`PowerSeries` declaration T5 did not port.

## 5. Definition of done

**Reviewed and ticked (2026-09-23), independently re-verified by the reviewer.**
Checker **772 identical, 0 mismatched, 0 missing**; full `lake build` exit 0
(4048 jobs), 0 warnings, no `sorry`; `#print axioms` clean on the bundled maps and
the three wrappers. The reviewer spot-checked `ModularForm.heckeTLin`'s fields
against the assembly table: `slash_action_eq'` ← T1, `holo'` ← T3,
`bdd_at_cusps'` ← T4, `map_add'`/`map_smul'` ← T0 — no new lemma was needed.

- [x] `FLTForHuman/ModularForms/HeckeOperatorForms.lean` created; the twelve
      bundled declarations verbatim from
      `Definitions/Def_ModularForm_HeckeOperatorForms.lean`.
- [x] the three thin wrappers (`CuspForm.qExpansion_heckeTLin`,
      `exists_coe_eq_heckeT/U`) verbatim from their `Theorems/` wrappers.
- [x] every `toFun` field resolves to a named SET 1–2 export (list them in the
      log).
- [x] `timeout 600 lake build` green, 0 warnings, no `sorry`.
- [x] checker: `HeckeOperatorForms.lean` in `PORT_FILES`; the three wrappers in
      `SOURCES`; **0 mismatched, 0 missing**.
- [x] `#print axioms` on the wrappers clean.
- [x] `logs/hecke-port.md` §T6: the assembly table (field → source lemma), the
      build/checker result.
- [x] `README.md` row.

## 6. Reporting back

1. The assembly table, re-derived (which SET 1–2 lemma discharged each field) —
   this is the evidence the layering was right.
2. Any field that needed a new lemma, and where it should live.
3. The `CuspForm.qExpansion_heckeTLin` / `exists_coe_eq_*` dependencies.
4. The SET-4 hand-off: the exact `heckeTLin`/`heckeULin` API T7 (and later the
   eigenform interface) will use, with names and binder order.
