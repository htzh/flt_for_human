# WORKORDER-R2 — the grid window perimeter

**Status (written 2026-10-14): ready to dispatch.** The second sub-set of Set R of
[TOPIC-cell-dissection.md](TOPIC-cell-dissection.md) (§5). One story: the boundary of a
grid window is a radial region whose `N` counts the sides, with pairwise-distinct arcs
and the stated perimeter data.

**Audience.** A coding session. Method: [porting-playbook.md](../../porting-playbook.md)
§3–§5; visibility rule: [TOPIC-cell-dissection.md](TOPIC-cell-dissection.md) §1a
(**tier-3 engine + tier-1 façade**); template and house style:
[WORKORDER-R1-radial-rectangle.md](WORKORDER-R1-radial-rectangle.md).

## 1. Scope

Port the one pin node `AlgebraicCurve.RadialRegion.exists_window_perimeter`
(`S_AlgebraicCurve_RadialRegion_exists_window_perimeter.lean`, 1,834 lines, 136
pin-public / 22 pin-private) whole, as an engine/façade pair. It consumes the two R1
headlines (`exists_rect_sixArcs`, `exists_refine_exact`) and nothing else outside the
definition layer.

**Not this set:** the reparametrisation twin + `exists_grid_geometry` (R3),
`exists_isOpen_starConvex_subset` / `exists_recip` / `exists_pow_pullback_laps` (R4),
and the `CellDissection` cluster.

## 2. Pre-round (landed)

`AlgebraicCurve/Defs/{ComplexLineIntegral,CellDissection}.lean` (definition layer) and
the R1 façades `AlgebraicCurve/RadialRegion/{RectSixArcs,RefineExact}.lean` are in
place and green. The pin `S_` file imports the two `Theorems/Thm_…{rect_sixArcs,
refine_exact}` wrappers; import the port's two R1 **façades** in their place. Do not
touch any of them.

## 3. Source

Pinned `aa2d8b3`; statement from
`Theorems/Thm_AlgebraicCurve_RadialRegion_exists_window_perimeter.lean`, proof from
`P2M/Sol/S_AlgebraicCurve_RadialRegion_exists_window_perimeter.lean`. The pin imports
`Mathlib`, `Definitions.Def_AlgebraicCurve_CellDissection`, the two `Theorems/`
wrappers and `P2M.Util`; replace by the specific Mathlib modules, the port's
`Defs.CellDissection` and the two R1 façades (no bare `import Mathlib`). The pin's
internal namespaces are `GridWindow` (with `WinData`/`Base`/`Win` nested) and
`WindowPerimeter`; drop the `P2MW.S_…` wrapper and root them at
`AlgebraicCurve.RadialRegion`.

## 4. Deliverables — two modules

1. `FLTForHuman/AlgebraicCurve/RadialRegion/Engine/WindowPerimeter.lean` — **tier 3**.
   Every declaration of the pin `S_` file **except** the top-level `solution`, at the
   pin's visibility (pin-public stays public; the 22 pin-private helpers stay private).
   A `-- pin: <name> (S_AlgebraicCurve_RadialRegion_exists_window_perimeter.lean:<line>)`
   comment above every **public** declaration (the register reads it). Module docstring:
   public but unwired, pointing at the topic.
2. `FLTForHuman/AlgebraicCurve/RadialRegion/WindowPerimeter.lean` — **tier 1**. Only
   the public headline `AlgebraicCurve.RadialRegion.exists_window_perimeter`, stated
   verbatim from the wrapper (with its `-- pin:` comment), proven from the engine's
   general `WindowPerimeter.exists_window_perimeter` exactly as the pin's `solution`
   does. Imports the engine.

## 5. Wiring

`SOURCES` += the `Theorems/Thm_…exists_window_perimeter` wrapper and the
`P2M/Sol/S_…exists_window_perimeter` file; `PORT_FILES` += the **façade only** (the
engine stays unlisted); both appended last with one-line comments. Then from the repo
root run `python3 tools/deps/unwired_register.py` and confirm `--check` exits 0.
Expected checker delta **+1** (the headline), 0 mismatched / 0 missing; the register
gains the engine with ~135 public rows.

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
  `AlgebraicCurve/RadialRegion/Engine/WindowPerimeter.lean`;
* a scratch `#check` of `AlgebraicCurve.RadialRegion.exists_window_perimeter` from the
  façade, 0 errors; `#print axioms` on it = `[propext, Classical.choice, Quot.sound]`;
* grep sweep for `sorry`/`admit`/`axiom`/`native_decide`/bare `import Mathlib`/
  `maxHeartbeats` — 0 in both;
* a pin-comment/namespace-stripped diff of the engine body against the pin `S_` body
  shows only the header and any v4.34.0-forced renames; **no pin-public declaration is
  demoted** (engine public count = pin public count − 1, the `solution` wrapper);
* `git status` shows the two modules, the two checker appends and the regenerated
  `UNWIRED-PUBLIC.md` only.

## 8. Hub prohibition and report

Only the two new modules, the two checker-list appends and the register rewrite
(through the tool). A promotion or host edit is a stop-and-report. Report per R1 §8:
paths and sizes; public/private counts with the "no demotion" reconciliation; the
namespace mapping; builds; checker before/after with the delta; the register check; the
`#check` and axioms lines; the grep sweep; `git status`; every adaptation.
