# WORKORDER-R3a — the reparametrisation twin (port once)

**Status (written 2026-10-14): ready to dispatch.** The third sub-set of Set R of
[TOPIC-cell-dissection.md](TOPIC-cell-dissection.md) (§5). One story: transporting a
radial arc across a shared side of two cells, in the "across edge" and "same side"
variants.

**Audience.** A coding session. Method: [porting-playbook.md](../../porting-playbook.md)
§3–§5; visibility rule: [TOPIC-cell-dissection.md](TOPIC-cell-dissection.md) §1a
(**tier-3 engine + tier-1 façade**); template and house style:
[WORKORDER-R1-radial-rectangle.md](WORKORDER-R1-radial-rectangle.md).

## 1. Scope and the twin

Two pin nodes whose `S_` files are **byte-identical through line 704** (the whole
`SegmentTransport`/`SegmentReparam` development, including both theorems
`exists_reparam_across_edge` and `exists_reparam_same_side`); they differ **only** in
the final `solution` statement (line 705 onward):

| node | pin `S_` | public headline |
|---|---:|---|
| `AlgebraicCurve.RadialRegion.exists_reparam_across_edge` | 726 | the "across edge" transport (`.re` difference, `(-cos/b)⁻¹`, `StrictAntiOn`) |
| `AlgebraicCurve.RadialRegion.exists_reparam_same_side` | 744 | the "same side" transport (`.re` sum, `(cos/a')⁻¹`, `StrictMonoOn`) |

Port the shared development **once** and give each node a thin façade. This is the
`port_advise` block `once 614 / decls 37 / files 2` of
`tools/deps/build/radial_plan.txt`.

**Not this set:** `exists_grid_geometry` (R3b, which consumes both headlines),
`exists_isOpen_starConvex_subset` / `exists_recip` / `exists_pow_pullback_laps` (R4),
the `CellDissection` cluster.

## 2. Pre-round (landed)

`Defs/{ComplexLineIntegral,CellDissection}.lean` and the R1/R2 engines+façades are in
place and green (checker `9783`). Nothing else is imported by these two nodes.

## 3. Source

Pinned `aa2d8b3`:
`Theorems/Thm_AlgebraicCurve_RadialRegion_exists_reparam_{across_edge,same_side}.lean`
(statements) and `P2M/Sol/S_AlgebraicCurve_RadialRegion_exists_reparam_{across_edge,same_side}.lean`
(proofs). Both pin files `import Mathlib`, `Definitions.Def_AlgebraicCurve_CellDissection`,
`P2M.Util`; replace with the specific Mathlib modules + the port's
`FLTForHuman.AlgebraicCurve.Defs.CellDissection` (no bare `import Mathlib`). Drop the
pin's `P2MW.S_…` wrapper namespace and root the internal namespaces at
`AlgebraicCurve.RadialRegion`.

## 4. Deliverables — three modules

1. `FLTForHuman/AlgebraicCurve/RadialRegion/Engine/Reparam.lean` — **tier 3**. The
   shared development, taken from the pin `S_` lines 1–704 of **either** file (they are
   identical there), at the pin's visibility (40 public / 0 private), every public
   declaration carrying a `-- pin: <name> (S_AlgebraicCurve_RadialRegion_exists_reparam_across_edge.lean:<line>)`
   comment (the two pin files agree byte-for-byte on these lines, so one pin source
   suffices — say so in the module docstring). Module docstring: public but unwired.
2. `FLTForHuman/AlgebraicCurve/RadialRegion/ReparamAcrossEdge.lean` — **tier 1**. Only
   `AlgebraicCurve.RadialRegion.exists_reparam_across_edge`, stated verbatim from its
   wrapper (with `-- pin:`), proven from the engine exactly as the pin's `solution`
   does.
3. `FLTForHuman/AlgebraicCurve/RadialRegion/ReparamSameSide.lean` — **tier 1**. The
   same for `AlgebraicCurve.RadialRegion.exists_reparam_same_side`.

## 5. Wiring

`SOURCES` += the two `Theorems/Thm_…` wrappers and the two `P2M/Sol/S_…` files;
`PORT_FILES` += the **two façades only**; appended last with one-line comments. From
the repo root run `python3 tools/deps/unwired_register.py` and confirm `--check` exits
0. Expected checker delta **+2**, 0 mismatched / 0 missing; the register gains the
engine (~40 rows).

## 6. Build discipline (copy, do not paraphrase)

> Edit loop `timeout 120 lake env lean -DautoImplicit=false -DmaxHeartbeats=200000 <file>`
> (from `lean/`) — the cap is **low on purpose**; never raise `maxHeartbeats`, never add a
> module `set_option maxHeartbeats`. `lake build <module>` per finished file, serialized
> with `flock` and bounded with `timeout`. Never a bare whole-tree `lake build`.

Build the engine first, then the façades.

## 7. Verification

* tier-0 green on all three, 0 warnings; tier-1 `lake build` green on all three;
* checker `0 mismatched / 0 missing`, `identical` delta exactly **+2**;
* `unwired_register.py --check` exits 0 and lists
  `AlgebraicCurve/RadialRegion/Engine/Reparam.lean`;
* a scratch `#check` of both headlines from the façades, 0 errors; `#print axioms` on
  both = `[propext, Classical.choice, Quot.sound]`;
* grep sweep for `sorry`/`admit`/`axiom`/`native_decide`/bare `import Mathlib`/
  `maxHeartbeats` — 0 in all three;
* the shared block is written **once**: the engine must not contain a second copy of
  any declaration, and the two façade files must each declare exactly one theorem;
* `git status` shows the three modules, the four checker appends and the regenerated
  `UNWIRED-PUBLIC.md` only.

## 8. Hub prohibition and report

Only the three new modules, the four checker-list appends and the register rewrite
(through the tool). A promotion or host edit is a stop-and-report. Report per R1 §8:
paths and sizes; public/private counts (engine = pin's 40, no demotion); the namespace
mapping; builds; checker before/after with the delta; the register check; the
`#check`/axioms lines; the grep sweep; the confirm that the twin is written once;
`git status`; every adaptation.
