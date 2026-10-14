# WORKORDER-R3b — the grid geometry

**Status (written 2026-10-14): ready to dispatch.** The fourth sub-set of Set R of
[TOPIC-cell-dissection.md](TOPIC-cell-dissection.md) (§5). One story: a rectangular
grid, with per-cell control points inside their squares, is a radial region whose arcs
are the cell sides and whose geometry is the stated grid data.

**Audience.** A coding session. Method: [porting-playbook.md](../../porting-playbook.md)
§3–§5; visibility rule: [TOPIC-cell-dissection.md](TOPIC-cell-dissection.md) §1a
(**tier-3 engine + tier-1 façade**); template and house style:
[WORKORDER-R1-radial-rectangle.md](WORKORDER-R1-radial-rectangle.md).

## 1. Scope

Port the one pin node `AlgebraicCurve.RadialRegion.exists_grid_geometry`
(`S_AlgebraicCurve_RadialRegion_exists_grid_geometry.lean`, 2,819 lines, 194
pin-public / 2 pin-private) whole, as an engine/façade pair. It consumes the two R3a
headlines (`exists_reparam_across_edge`, `exists_reparam_same_side`).

**Not this set:** `exists_isOpen_starConvex_subset` / `exists_recip` /
`exists_pow_pullback_laps` (R4) and the `CellDissection` cluster.

## 2. Pre-round (landed)

The definition layer (`Defs/{ComplexLineIntegral,CellDissection}.lean`) and the R1/R2
engines+façades plus the R3a façades `RadialRegion/{ReparamAcrossEdge,ReparamSameSide}.lean`
are in place and green (checker `9785`). The pin `S_` file imports the two reparam
`Theorems/` wrappers; import the port's two R3a **façades** in their place.

## 3. Source

Pinned `aa2d8b3`: statement from
`Theorems/Thm_AlgebraicCurve_RadialRegion_exists_grid_geometry.lean`, proof from
`P2M/Sol/S_AlgebraicCurve_RadialRegion_exists_grid_geometry.lean`. The pin imports
`Mathlib`, `Definitions.Def_AlgebraicCurve_CellDissection`, the two reparam
`Theorems/` wrappers and `P2M.Util`; replace by specific Mathlib modules, the port's
`Defs.CellDissection` and the two R3a façades (no bare `import Mathlib`).

**Scaffolding to drop.** The pin wraps its development in the `P2MW.S_…` namespace and
uses three `p2m_export` calls (lines 470, 602, 925) to move `ArcData`/`arcSet_injective`/
`yL` into `SideIdentity`/`GridVertices`. The port drops the wrapper namespace and the
`p2m_export` calls and keeps each declaration in the namespace the port's own section
structure gives it (`PlanarRegions`/`GridData`, `SideIdentity`/`ArcData`, `GridVertices`,
`ArcReversal`, `StarProperty`/`Window`, `GridGeometry`, all rooted at
`AlgebraicCurve.RadialRegion`); record the mapping in the module docstring and in the
report. No consumer outside this node uses those internals.

## 4. Deliverables — two modules

1. `FLTForHuman/AlgebraicCurve/RadialRegion/Engine/GridGeometry.lean` — **tier 3**.
   Every declaration of the pin `S_` file **except** the top-level `solution`, at the
   pin's visibility (the 194 pin-public stay public; the 2 pin-private stay private),
   a `-- pin: <name> (S_AlgebraicCurve_RadialRegion_exists_grid_geometry.lean:<line>)`
   comment above every **public** declaration. Module docstring: public but unwired,
   the `p2m_export` mapping noted.
2. `FLTForHuman/AlgebraicCurve/RadialRegion/GridGeometry.lean` — **tier 1**. Only the
   public headline `AlgebraicCurve.RadialRegion.exists_grid_geometry`, stated verbatim
   from the wrapper (with `-- pin:`), proven from the engine's general
   `GridGeometry.exists_grid_geometry` exactly as the pin's `solution` does. Imports
   the engine.

Statements and proofs are transcribed verbatim; list every v4.34.0-forced adaptation.

## 5. Wiring

`SOURCES` += the `Theorems/Thm_…exists_grid_geometry` wrapper and the
`P2M/Sol/S_…exists_grid_geometry` file; `PORT_FILES` += the **façade only**; appended
last with one-line comments. From the repo root run
`python3 tools/deps/unwired_register.py` and confirm `--check` exits 0. Expected
checker delta **+1**, 0 mismatched / 0 missing; the register gains the engine
(~194 public rows).

## 6. Build discipline (copy, do not paraphrase)

> Edit loop `timeout 120 lake env lean -DautoImplicit=false -DmaxHeartbeats=200000 <file>`
> (from `lean/`) — the cap is **low on purpose**; never raise `maxHeartbeats`, never add a
> module `set_option maxHeartbeats`. `lake build <module>` per finished file, serialized
> with `flock` and bounded with `timeout`. Never a bare whole-tree `lake build`.

Build the engine first, then the façade.

## 7. Verification

* tier-0 green on both, 0 warnings; tier-1 `lake build` green on both;
* checker `0 mismatched / 0 missing`, `identical` delta exactly **+1**;
* `unwired_register.py --check` exits 0 and lists
  `AlgebraicCurve/RadialRegion/Engine/GridGeometry.lean`;
* a scratch `#check` of `AlgebraicCurve.RadialRegion.exists_grid_geometry` from the
  façade, 0 errors; `#print axioms` on it = `[propext, Classical.choice, Quot.sound]`;
* grep sweep for `sorry`/`admit`/`axiom`/`native_decide`/bare `import Mathlib`/
  `maxHeartbeats` — 0 in both;
* the engine public count equals the pin's **194** (the `solution` wrapper is all that
  is not carried over) — no demotion;
* `git status` shows the two modules, the two checker appends and the regenerated
  `UNWIRED-PUBLIC.md` only.

## 8. Hub prohibition and report

Only the two new modules, the two checker-list appends and the register rewrite
(through the tool). A promotion or host edit is a stop-and-report. Report per R1 §8:
paths and sizes; public/private counts with the no-demotion reconciliation; the
namespace/`p2m_export` mapping; builds; checker before/after with the delta; the
register check; the `#check` and axioms lines; the grep sweep; `git status`; every
adaptation.
