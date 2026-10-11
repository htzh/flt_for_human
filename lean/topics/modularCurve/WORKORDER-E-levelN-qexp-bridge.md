# WORKORDER-E — the level-`N` `q`-expansion bridge: the two twin nodes written once

**Status: landed 2026-10-11 (the manager's own set, not dispatched).** This is the successor
subject the A/B wave's step-6 re-read put on the shelf
([TOPIC-levelN-and-modular-polynomial.md](TOPIC-levelN-and-modular-polynomial.md) §2 outcome): the
two ready `ModularCurve` rows at the head of the column frontier,

* `ModularCurve.exists_ringHom_laurentBaseChange_qExpFunctionFieldC_levelN_qExpansion` (982 silo
  lines), and
* `ModularCurve.exists_ringHom_laurentBaseChange_qExpFunctionFieldC_levelN` (955).

They are the same development transcribed twice, so they are one set and one module.

Pin `anthropics/fermats-last-theorem@aa2d8b3` (Lean `v4.33.1` / mathlib `db584cd6`); port mathlib
`v4.34.0`.

## 1. The cut — the twin relation

The two pin `S_` files differ by 54 diff lines. 98 of their 101 declaration groups are
statement-identical; only three declarations live alone:

| declaration | file | content |
|---|---|---|
| `main2` (33 ln) | `_qExpansion` only | the strong engine: `∃ Φ, ∃ E : K →ₐ[ℂ] LaurentSeries ℂ`, with `E (jGen) = qExpand (jqModC)` and `E (Φ u) = qExpand (coeffMap ι u)` |
| `solution` (31 ln) | `_qExpansion` | the wrapper above, proved by `main2` |
| `solution` (27 ln) | `_levelN` | literally the `_qExpansion` headline with the two `E` conjuncts deleted; proved by `main`, whose conclusion is a prefix of `main2`'s |

So the `_levelN` node is the projection of the `_qExpansion` node. The port writes the
`_qExpansion` development once, `private`, and derives the `_levelN` headline from `main2`.

## 2. The scoping numbers, and what the tools under-report

```bash
cd tools/deps
python3 port_advise.py \
  --nodes ModularCurve.exists_ringHom_laurentBaseChange_qExpFunctionFieldC_levelN_qExpansion \
  --nodes ModularCurve.exists_ringHom_laurentBaseChange_qExpFunctionFieldC_levelN \
  --json build/levelN_advise.json
python3 port_plan.py --json build/levelN_advise.json
```

`port_plan` reports **1,937 raw / 1,871 declaration lines / 885 duplicate copies / 986 once-cost /
373 already in the port (vetted) / 613 NET NEW**, with 84 trusted and 4 suspect substitutions.

The 4 suspect rows are the parser's type-only `def` matches and **both are false**: `famS` (4 ln)
against `FrickeTransport.genSet` (the finite generating set `insert jf {g | ∃ v ≠ 0, g = fricke v}`)
and `goodSeries` (2 ln) against `X1DiamondPullback.ratioField` (the ratio field of modular-form
`q`-expansions). Both stay new.

**The hand-check corrects the tool twice more, and this is the lesson of the set.** The
authoritative match is the checker's own parser, run declaration by declaration against the whole
port corpus (public and private, exact and modulo the pin's `M` / port's `N` section variable):

* **six declarations are already in the port but `port_advise` misses them**: `Q` (2 ln), `one`
  (2 ln), `precomp_apply` (3 ln) and `PB` (2 ln) are byte-identical to `ModularCurve.LevelN.*` in
  `LevelN/Prelude.lean`, but the substitution table omits them; `good_of_PB` (9 ln) matches the
  port's copy after `M`↔`N` (the tool's own near-duplicate row, ratio 0.976); and
  `coeffMap_ofPowerSeries` (9 ln) matches the port's **private** copy in `PhiGenIntegrality.lean`
  under renamed binders.
* hence the reusable set is **48 declarations**, and the genuinely new mathematics is
  **≈586 lines**, not 613 — 27 lines of the tool's "new" already exist.
* `PB`/`good_of_PB`/`Q`/`one`/`precomp_apply` are imported from `LevelN/Prelude.lean`; nothing is
  re-proved.

`port_plan`'s "47-node slice" label is a stale hard-coded print string, not the node count; the
slice is the two `S_` files.

## 3. The promotion decision — none is made

The only port-`private` substitution is `algebraMap_laurentSeries` (6 ln, `private` in
`LevelN/FieldGalois.lean`'s `QExpEmbedding`). Two further port copies are unusable without a heavy
import or a promotion: `one_mem_strictPeriods` lives in `ModularCurve/X1/FunctionField.lean` (a
large module imported only for it) and `coeffMap_ofPowerSeries` is `private` in
`PhiGenIntegrality.lean`.

All three are **few-line adaptors** — `HahnSeries`/`PowerSeries` glue and a
`Subgroup.strictPeriods` restatement, not mathematics another theory states — so per playbook
§4(b) ("few line adaptors can stay private") they are **re-derived `private` in the new module**
(6 + 5 + 9 lines). No declaration is promoted and no existing Lean module is edited, so there is
no hub wave: the whole set is one new file plus the checker wiring.

## 4. The definition layer

Hand-checked, declaration by declaration, per the column's §4(a). Both pin `S_` files import the
same eight pin modules, and **all eight are already wired** in `spec/check_flt_statements.py`:

* `Def_ModularCurve_LevelNFunctionField` (L2694) — subject A's layer, whole, at
  `ModularCurve/LevelN/FunctionField.lean`;
* `Def_ModularCurve_X1` (L966), `Def_ModularCurve_JqCoeff` (L633);
* `Thm_WLight_frickeFunction_modularity_package` / `_orbit_package` (L917–918),
  `Thm_WLight_exists_levelFraction_of_stable_family` (L932),
  `Thm_WLight_levelN_structure_package` (L942),
  `Thm_ModularCurve_LevelN_exists_algHom_laurentSeries_qExpansion` (L2716).

No definition needs a new home; the port's A1 headline
`ModularCurve.LevelN.exists_algHom_laurentSeries_qExpansion` supplies the `E` the bridge builds on.

## 5. Deliverable

| module | content |
|---|---|
| `FLTForHuman/ModularCurve/LevelN/QExpBridge.lean` | the `_qExpansion` development once: `den`/`FF`/`famS` blocks, `E`, `E_div_eq`, `exists_kappa`, `fixedSub`/`goodSeries`/`iotaM`/`Phi`, `laurentBaseChange_le`, `main` and `main2`; then the two public wrapper headlines |

668 lines: **54 `private`** declarations, **2 public** (`ModularCurve.exists_ringHom_laurentBaseChange_
qExpFunctionFieldC_levelN` and `…_qExpansion`, the pin's `Theorems/` wrappers verbatim), the pin's
own section order (`Forms`, `Quotients`, `Family`, `Expansion`, `Bridge`) preserved. The prelude is
imported, not re-declared: `LevelN/Prelude.lean` is the single home. Six narrow
`set_option linter.unusedSectionVars false in` suppressions (the same `NeZero`-in-value/not-in-type
pattern as subject A, §9 of the topic note); no file-wide linter option, no `omit` failure, no
heartbeat override (the pin's 6,400,000-heartbeat `E_div_eq` bump is **not** transcribed and the
project's 4,000,000 cap suffices).

## 6. Verification

| check | result |
|---|---|
| tier-0 `lake env lean -DmaxHeartbeats=4000000` | exit 0, **0 warnings** |
| tier-1 `lake build FLTForHuman.ModularCurve.LevelN.QExpBridge` | green |
| checker before (module line absent) | 7630 identical, 0 mismatched, 0 missing, 38 own (7668) |
| checker after | **7632 identical, 0 mismatched, 0 missing, 38 own (7670)** — delta **+2**, exactly the two headlines |
| one-token mutation | `+ (hMut : True)` on a headline → exactly 1 mismatched; reverted |
| `#print axioms` (both headlines) | `[propext, Classical.choice, Quot.sound]` |
| forbidden-token sweep | no `sorry`/`admit`/`axiom`/`native_decide`/bare `import Mathlib`/heartbeat override |
| milestone whole-tree build | green, **9,394 jobs** |

The checker's `before` is the *measured current* tree (7630 / 38 own), not the column note's stale
7592 / 36: other `WeierstrassCurve` shelf rows have landed since the note was written. Record the
delta you measure, not the note's figure.

## 7. Wiring

Appended last to `SOURCES`, both `Theorems/Thm_ModularCurve_exists_ringHom_laurentBaseChange_
qExpFunctionFieldC_levelN[_qExpansion].lean` wrappers and both matching `P2M/Sol/S_…` files (the
`S_` files carry the pin's public prelude rows; every port helper is `private`, so only the two
headlines are diffed); appended last to `PORT_FILES`,
`FLTForHuman/ModularCurve/LevelN/QExpBridge.lean`.

## 8. Reproduce

```bash
cd tools/deps
python3 port_advise.py \
  --nodes ModularCurve.exists_ringHom_laurentBaseChange_qExpFunctionFieldC_levelN_qExpansion \
  --nodes ModularCurve.exists_ringHom_laurentBaseChange_qExpFunctionFieldC_levelN \
  --json build/levelN_advise.json
python3 port_plan.py --json build/levelN_advise.json
cd ../lean
timeout 300 python3 spec/check_flt_statements.py
flock .lake/flt_build.lock timeout 900 lake build
```

FLT provenance, pinned `aa2d8b3`:
* <https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularCurve_exists_ringHom_laurentBaseChange_qExpFunctionFieldC_levelN.lean>
* <https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularCurve_exists_ringHom_laurentBaseChange_qExpFunctionFieldC_levelN_qExpansion.lean>
* <https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_exists_ringHom_laurentBaseChange_qExpFunctionFieldC_levelN_qExpansion.lean>
