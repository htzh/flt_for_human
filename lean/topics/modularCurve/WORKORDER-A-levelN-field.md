# WORKORDER-A — the level-`N` function field of `X(N)`: the field, its Galois action and its places

**Status: blocked on the manager's definition wave (§1).** Do not start until
`FLTForHuman/ModularCurve/LevelN/FunctionField.lean` is in the tree, `lake build`-green, and the
manager has said so. Subject **A** of the `ModularCurve` ready shelf (scoping:
[TOPIC-levelN-and-modular-polynomial.md](TOPIC-levelN-and-modular-polynomial.md) §1); 8 rows,
3,996 raw / **2,814 net new math lines** (`port_plan`), 243 declaration groups, of which 976 raw
lines are duplicate copies removable by writing the shared prelude once.

**New files only; no existing Lean module is edited; no promotion is needed.** `port_advise`
reports **3** trusted substitutions for the whole set (5 lines in the port) and **0** private
helpers to re-derive — the pin files declare their prelude publicly, so what this set writes is
almost all new.

Pin `anthropics/fermats-last-theorem@aa2d8b3` (Lean `v4.33.1` / mathlib `db584cd6`); port mathlib
`v4.34.0`. Target: `+8` headlines, plus whatever public prelude this set homes, with `0 mismatched
/ 0 missing`. The manager will give you the exact checker baseline after set B1 has landed — record
the before/after delta you actually measure rather than assuming a figure.

## 1. The prerequisite — the definition layer (manager's, already landed when you start)

The pin's `Definitions/Def_ModularCurve_LevelNFunctionField.lean` (53 lines, 11 declarations) is the
whole new definition layer, and it is the manager's work, not yours. It declares, in namespace
`ModularCurve.LevelN`:

`wp`, `fricke`, `jAnalytic`, `generators`, `ring`, `jAnalytic_mem_generators`,
`fricke_mem_generators`, `jAnalytic_mem`, `fricke_mem`, `jGen`, `coe_jGen`.

Its only imports are `Mathlib` and `Def_PeriodPair_Uniformization`, and the latter is ported
(`FLTForHuman/Elliptic/PeriodPair/{Basic,Lattice,Discriminant,Uniformization,JLine}.lean`, with
`PeriodPair.ofTau` at `Elliptic/PeriodPair/Basic.lean:139`), so the transcription is verbatim. The
other definition modules the eight rows import — `Def_ModularCurve_JqCoeff`,
`Def_AlgebraicCurve_BaseChangeGalois`, `Def_AlgebraicCurve_DivisorClassGroup`,
`Def_PeriodPair_Uniformization` — are all registered in the checker's `SOURCES` and verified.
`Def_ModularCurve_QAdicPlaceMod` is imported by *non-ready* `LevelN` nodes only and is out of
scope.

Use the manager's names; do not redeclare or shadow them, and do not edit the module.

The pin's own `Theorems/` premises for these eight rows are four —
`Thm_ModularCurve_jqModC_eq_qExpansion_E4_cube_div_discriminant`,
`Thm_WLight_frickeFunction_modularity_package`, `Thm_WLight_frickeFunction_orbit_package`,
`Thm_WLight_levelN_structure_package` — and all four are registered in the checker's `SOURCES`
(3,567 raw `S_` lines behind them), so this set's readiness is trustworthy: unlike subject B2,
whose unregistered premise a last-name frontier view hides (`CARRY-FORWARD.md`, scoping
cautions), nothing here needs a wave beyond §1.

## 2. The eight rows

Write the prelude once (§3), then the rows in the order of the phases. Phase A1 first
(the field and its Galois action), then A2 (the places and valuations); both phases are one set
and one report.

| phase | head (`ModularCurve.LevelN.` prefix) | `S_` lines | content |
|---|---|---:|---|
| A1 | `isDomain_ring` | 27 | `IsDomain (ring M)` |
| A1 | `slash_eq_self_of_mem_Gamma_of_mul_eq` | 258 | a `MDifferentiable` `F` with a divisibility identity against `ring N`-members is slash-invariant under `Γ(N)` |
| A1 | `exists_monoidHom_algEquiv_fixedField_eq_adjoin` | 472 | the `SL(2, ℤ)`-action on `K`: the homomorphism `σ`, its kernel `Γ(N) ⊔ ±1`, the fixed field `ℂ(jGen)`, `IsGalois`, transcendence and `finrank = index` |
| A1 | `exists_algHom_laurentSeries_qExpansion` | 602 | the q-expansion at `i∞`: a `ℂ`-place `K →ₐ[ℂ] LaurentSeries ℂ` sending `jGen` to `qExpand ℂ N (jqModC ℂ)`, commuting with q-expansions of bounded quotients |
| A2 | `exists_place_ord_neg_forall_smul_eq` | 891 | a cusp place `W` with `ord jGen < 0`, fixed by every automorphism fixing the `T`-cusp |
| A2 | `exists_place_ord_sub_pos_forall_smul_eq` | 521 | for each `τ₀`: `W` with `0 < ord (jGen - jAnalytic τ₀)`, fixed by the stabilizer of `τ₀` |
| A2 | `exists_place_analyticOrderAt_eq_mul_ord` | 405 | for each `τ₀`: `W` and `e > 0` with `analyticOrderAt F τ₀ = e * W.ord F` for every nonzero `F ∈ ring N` |
| A2 | `valuation_apply_smul_le_one_of_tendsto_div_smul` | 820 | the valuation bound `Valued.v (E (σ γ z)) ≤ 1` for a modular-form quotient bounded at `i∞` |

**Statements: verbatim from the pinned wrappers; do not paraphrase, rename a binder or relax a
hypothesis.** Pinned sources (statement = `Theorems/`, proof = `P2M/Sol/`; replace `refs/heads/main`
with `aa2d8b3`):

* <https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularCurve_LevelN_isDomain_ring.lean>
* <https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularCurve_LevelN_slash_eq_self_of_mem_Gamma_of_mul_eq.lean>
* <https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularCurve_LevelN_exists_monoidHom_algEquiv_fixedField_eq_adjoin.lean>
* <https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularCurve_LevelN_exists_algHom_laurentSeries_qExpansion.lean>
* <https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularCurve_LevelN_exists_place_ord_neg_forall_smul_eq.lean>
* <https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularCurve_LevelN_exists_place_ord_sub_pos_forall_smul_eq.lean>
* <https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularCurve_LevelN_exists_place_analyticOrderAt_eq_mul_ord.lean>
* <https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularCurve_LevelN_valuation_apply_smul_le_one_of_tendsto_div_smul.lean>

and the matching `P2M/Sol/S_ModularCurve_LevelN_<stem>.lean` for each proof. The local pin clone is
`~/proj/fermats-last-theorem`.

## 3. The shared prelude — write it once

`port_advise` prices **≈911 removable lines** in 65 names proved in two or more of the eight
files. The four blocks that matter, with their copy counts and sizes (once-cost in one home):

| block | files | once | top declarations |
|---|---:|---:|---|
| A1-1 | 3 | 187 | `exists_isBoundedAtImInfty_mul_pow` (40), `const` (20), `smul_eq_self_of_mem` (16), `periodic_of_mem` (15), `good_of_PB` (15), `mul_discriminant_pow_eq_zero_iff` (14) |
| A1-2 | 2 | 146 | `Q_natCast_eq_qExpand` (68), `Q_eq_zero_iff` (15), `Q_discriminant_ne_zero` (13), `qParam_pow_mul` (12) |
| A2-1 | 2 | 137 | `analyticPlace` (29), `jSub_ne_zero` (14), `min_ordAt_le_ordAt_add` (14), `ordAt_jSub_pos` (13), `ordAt_one` (11) |
| A2-2 | 3 | 126 | `ordValuation` (53), `analyticOrderAt_ne_top` (16), `nonZeroDivisors_le_supp_primeCompl` (15), `nontrivial_valueGroup` (13) |

Also named in the topic note and to be reused rather than re-derived: `jAnalytic_smul` (5 copies),
`some_congr` and `T_pow_mem_Gamma` (the latter already in the port at
`ModularForms/WeightOne/RationalityDvd.lean`, a binder variant).

These pin declarations are **public in the pin**; the port may home them publicly in one module
(they then verify against the pin's `S_` files and count toward `identical`), or keep a copy
`private`. Prefer public in one home over `private` copies in several: the set spans modules and a
`private` prelude cannot be shared.

**Drift to resolve at the pin.** The `ordValuation` family is `port_advise`'s generalise row (same
conclusion, different binders across the three big files): take the wrapper's binders and write the
valuation **once**, then derive the variants. `port_plan` reports **0** suspect type-only `def`
matches for this set.

## 4. Deliverable modules

Suggested homes (re-home freely under `ModularCurve/LevelN/`, recording the choice):

| module | content |
|---|---|
| `FLTForHuman/ModularCurve/LevelN/FunctionField.lean` | the manager's definition layer (§1) — **do not edit** |
| `FLTForHuman/ModularCurve/LevelN/Prelude.lean` | the shared blocks of §3, public, written once |
| `FLTForHuman/ModularCurve/LevelN/FieldGalois.lean` | phase A1's four headlines |
| `FLTForHuman/ModularCurve/LevelN/Places.lean` | phase A2's four headlines |

If a single module is more natural, use one — but keep the prelude in exactly one place.

## 5. Build discipline

* edit loop `timeout 300 lake env lean -DmaxHeartbeats=4000000 -DautoImplicit=false <file>`;
* `flock .lake/flt_build.lock timeout 300 lake build <module>` when a file is done;
* **no whole-tree `lake build`** — the manager runs the milestone build;
* every `lake build` serialized and bounded; never raise the heartbeat cap. On a timeout
  quarantine and bisect, and tell real CPU work from another agent's lock by CPU time.

## 6. Stop and report

Stop and report, with the quotation and the pin line, if: a statement cannot be matched without
moving the pin's text; a proof needs an unported `Definitions/` module beyond §1 (report the import
verbatim — in particular say so immediately if anything needs `Def_ModularCurve_QAdicPlaceMod`);
a helper is genuinely needed publicly and is `private` in an existing hub (a promotion is the
manager's); or a build exceeds its bound and bisecting does not settle it. Do not open another set,
and do not touch subject B's rows or `ModularCurve/Degree/PhiData.lean`.

## 7. Wiring

Append to `SOURCES`, last, each target's `Theorems/Thm_ModularCurve_LevelN_<stem>.lean` and
`P2M/Sol/S_ModularCurve_LevelN_<stem>.lean`; append each new module to `PORT_FILES`, last. Run the
checker as soon as each module is written and reconcile the `identical` delta to that module's new
public surface before building. The manager owns the final wiring state.

## 8. Completion report

Module paths and line counts; public/`private` counts; tier-0 wall/CPU and warnings (target **0**);
tier-1 result per module; the checker before → after with the `identical` delta reconciled; one
token mutation on each of the eight headlines, caught and reverted; `#print axioms` on all eight
(`[propext, Classical.choice, Quot.sound]`); `git status --porcelain` showing only this set's files
(the tree is dirty before you start — the manager's notes, the C1/C2/D1/D2 modules and the checker
wiring are pre-existing; report only your delta); anything you could not match, quoted.

Reproduce the scoping (from `tools/deps/`):

```bash
python3 port_advise.py \
  --target ModularCurve.LevelN.exists_monoidHom_algEquiv_fixedField_eq_adjoin \
  --target ModularCurve.LevelN.exists_algHom_laurentSeries_qExpansion \
  --target ModularCurve.LevelN.exists_place_ord_neg_forall_smul_eq \
  --target ModularCurve.LevelN.exists_place_ord_sub_pos_forall_smul_eq \
  --target ModularCurve.LevelN.exists_place_analyticOrderAt_eq_mul_ord \
  --target ModularCurve.LevelN.valuation_apply_smul_le_one_of_tendsto_div_smul \
  --target ModularCurve.LevelN.slash_eq_self_of_mem_Gamma_of_mul_eq \
  --target ModularCurve.LevelN.isDomain_ring \
  --json build/mc_a_advise.json
python3 port_plan.py --json build/mc_a_advise.json
```
