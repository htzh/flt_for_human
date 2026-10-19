# WORKORDER-R1 — the radial rectangle: six arcs and refinement (engine/façade)

**Status (written 2026-10-14): ready to dispatch.** The first sub-set of Set R of
[TOPIC-cell-dissection.md](TOPIC-cell-dissection.md) (§5). One story: a rectangle is a
radial region with six arcs, and a radial region refines to any finite break set.

**Audience.** A coding session. Method: [porting-playbook.md](../../porting-playbook.md)
§3–§5; visibility rule: [TOPIC-cell-dissection.md](TOPIC-cell-dissection.md) §1a
(**tier-3 engine + tier-1 façade**); house style: `ModularCurve/TateCurve/*` and
`AlgebraicCurve/Place/FiniteResidue.lean`.

## 1. Scope

Port two self-contained pin nodes whole, each as an **engine/façade pair**:

| node | pin `S_` lines | headline |
|---|---:|---|
| `AlgebraicCurve.RadialRegion.exists_rect_sixArcs` | 1,839 | a rectangle is a `RadialRegion` with `N = 6`, the stated `K`/`Kint`, six arc/loop/radius/subset conjuncts |
| `AlgebraicCurve.RadialRegion.exists_refine_exact` | 259 | `∃ R', R'.q = R.q ∧ … ∧ Set.range R'.φs = Set.range R.φs ∪ T ∧ …` |

`exists_rect_sixArcs` is the node the DeligneSerre column deferred
([WORKORDER-P1](WORKORDER-P1-isPrimeOverValuationSubring.md) §2) for the missing
definition layer, now homed.

**Not this set:** the other seven `RadialRegion` nodes (`exists_window_perimeter`,
the reparam twin, `exists_grid_geometry`, `exists_isOpen_starConvex_subset`,
`exists_recip`, `exists_pow_pullback_laps`) and the `CellDissection` cluster.

## 2. Pre-round (landed)

`AlgebraicCurve/Defs/ComplexLineIntegral.lean` and
`AlgebraicCurve/Defs/CellDissection.lean` are homed and green (checker `9780
identical`). Import `FLTForHuman.AlgebraicCurve.Defs.CellDissection`; do not touch
the definition modules.

## 3. Source

Pinned `aa2d8b3`; statements from the `Theorems/` wrappers, proofs from the `S_`
files:

* `Theorems/Thm_AlgebraicCurve_RadialRegion_exists_rect_sixArcs.lean` /
  `P2M/Sol/S_AlgebraicCurve_RadialRegion_exists_rect_sixArcs.lean`
* `Theorems/Thm_AlgebraicCurve_RadialRegion_exists_refine_exact.lean` /
  `P2M/Sol/S_AlgebraicCurve_RadialRegion_exists_refine_exact.lean`

Both `S_` files have the same shape: an internal development namespace
(`RectRadial`/`RectSixArcs`, `RadialRefine`) and a top-level `solution` wrapper. Both
`import Mathlib`, `Definitions.Def_AlgebraicCurve_CellDissection`, `P2M.Util`;
replace by the specific Mathlib modules and the port's `Defs/CellDissection` (no bare
`import Mathlib`). Drop the pin's `P2MW.S_…` wrapper namespace; root the internal
namespaces at `AlgebraicCurve.RadialRegion` (e.g.
`AlgebraicCurve.RadialRegion.RectSixArcs.*`, `…RadialRefine.*`).

## 4. Deliverables — four modules

For each node, an **engine** (the `S_` file's development, minus the top-level
`solution`) and a **façade** (the headline).

1. `FLTForHuman/AlgebraicCurve/RadialRegion/Engine/RectSixArcs.lean` — tier 3.
   Every declaration of the pin `S_` file **except** `solution`, at the pin's
   visibility: pin-public stays public, pin-private stays private. Add a
   `-- pin: <name> (S_AlgebraicCurve_RadialRegion_exists_rect_sixArcs.lean:<line>)`
   comment above every **public** declaration (the register reads it). Module
   docstring: the `RectSixArcs` development, public but unwired, pointing at the
   topic.
2. `FLTForHuman/AlgebraicCurve/RadialRegion/RectSixArcs.lean` — tier 1. Only the
   public headline `AlgebraicCurve.RadialRegion.exists_rect_sixArcs`, stated verbatim
   from the wrapper (with its `-- pin:` comment), proven from the engine's general
   theorem exactly as the pin's `solution` does. Imports the engine.
3. `FLTForHuman/AlgebraicCurve/RadialRegion/Engine/RefineExact.lean` — tier 3, same
   rule, from the `refine_exact` `S_` file (its `RadialRefine` helpers are already
   `private`; keep them so; the public `refineExact*`/`exists_refine_exact` surface
   is exposed with `-- pin:` comments).
4. `FLTForHuman/AlgebraicCurve/RadialRegion/RefineExact.lean` — tier 1, only the
   public headline `AlgebraicCurve.RadialRegion.exists_refine_exact`, imports the
   engine.

Transcribe statements and proofs verbatim; adapt only what v4.34.0 forces and list
every adaptation. Do not edit anything else.

## 5. Wiring

Append last, with one-line comments, to `lean/spec/old_check_stmts.py`:
`SOURCES` += the two `Theorems/Thm_…` wrappers and the two `P2M/Sol/S_…` files;
`PORT_FILES` += the **two façades only** (the engines stay unlisted). Then, from the
repo root, run `python3 tools/deps/unwired_register.py` to register the engines and
confirm `--check` exits 0. Expected checker delta **+2** (the two headlines),
0 mismatched / 0 missing; the register should gain the two engine modules.

## 6. Build discipline (copy, do not paraphrase)

> Edit loop `timeout 120 lake env lean -DautoImplicit=false -DmaxHeartbeats=200000 <file>`
> (from `lean/`) — the cap is **low on purpose**; never raise `maxHeartbeats`, never add
> a module `set_option maxHeartbeats`. `lake build <module>` per finished file,
> serialized with `flock` and bounded with `timeout`. Never a bare whole-tree
> `lake build`.

Build order: engines first, then façades.

## 7. Verification

* tier-0 green on all four, 0 warnings; tier-1 `lake build` green on all four;
* checker `0 mismatched / 0 missing`, `identical` delta exactly **+2**;
* a scratch `#check` of the two headlines from the two façades, 0 errors;
* `unwired_register.py --check` exits 0 and lists
  `AlgebraicCurve/RadialRegion/Engine/{RectSixArcs,RefineExact}.lean`;
* `#print axioms` on both headlines = `[propext, Classical.choice, Quot.sound]`;
* grep sweep for `sorry`/`admit`/`axiom`/`native_decide`/bare `import Mathlib`/
  `maxHeartbeats` — 0 in all four;
* `git status` shows the four modules, the checker appends and the regenerated
  `UNWIRED-PUBLIC.md` only.

## 8. Hub prohibition and report

Only the four new modules, the four checker-list appends, and the register rewrite
(through the tool). A promotion or host edit is a stop-and-report. Report: the four
paths and sizes; per-module public/private counts; the namespace mapping chosen; the
builds; the checker before/after with the delta; the register check; the `#check` and
axioms lines; the grep sweep; `git status`; every adaptation.
