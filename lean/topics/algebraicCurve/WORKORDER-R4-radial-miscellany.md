# WORKORDER-R4 — radial miscellany: star-convexity, reciprocals and power pullbacks

**Status (written 2026-10-14): ready to dispatch.** The last sub-set of Set R of
[TOPIC-cell-dissection.md](TOPIC-cell-dissection.md) (§5). Three independent radial-region
constructions, ~1,431 pin lines, 56 pin-public declarations. After this, Set R is done
and the column pauses (the `CellDissection` sets C1/C2 and the `exists_pairedCellFamily`
consumer stay unwritten).

**Audience.** A coding session. Method: [porting-playbook.md](../../porting-playbook.md)
§3–§5; visibility rule: [TOPIC-cell-dissection.md](TOPIC-cell-dissection.md) §1a
(**tier-3 engine + tier-1 façade**); template and house style:
[WORKORDER-R1-radial-rectangle.md](WORKORDER-R1-radial-rectangle.md).

## 1. Scope — three nodes

| node | pin `S_` lines | pin public / private | internal namespace |
|---|---:|---|---|
| `AlgebraicCurve.RadialRegion.exists_isOpen_starConvex_subset` | 389 | 17 / 1 | `CellPeriods` (after `AlgebraicCurve.Cell`) |
| `AlgebraicCurve.RadialRegion.exists_recip` | 281 | 18 / 5 | `RadialRecip` |
| `AlgebraicCurve.RadialRegion.exists_pow_pullback_laps` | 761 | 21 / 35 | `PowPullback` |

They are mutually independent (no in-cluster premises). `exists_isOpen_starConvex_subset`
additionally imports `Definitions.Def_AlgebraicCurve_IsCurveOver` (ported as
`FLTForHuman.AlgebraicCurve.Defs.IsCurveOver`); the other two import only the dissection
definition module.

## 2. Pre-round (landed)

`Defs/{ComplexLineIntegral,CellDissection}.lean` and the R1/R2/R3a/R3b engines+façades are
in place and green (checker `9786`). Nothing else is imported.

## 3. Source

Pinned `aa2d8b3`: for each node the `Theorems/Thm_AlgebraicCurve_RadialRegion_<node>.lean`
wrapper (statement) and the `P2M/Sol/S_AlgebraicCurve_RadialRegion_<node>.lean` (proof).
All three `import Mathlib` + `Definitions.Def_AlgebraicCurve_CellDissection` + `P2M.Util`
(the first also `Def_AlgebraicCurve_IsCurveOver`); replace with the specific Mathlib
modules, the port's `Defs.CellDissection` (and `Defs.IsCurveOver`), and no bare
`import Mathlib`. Drop the `P2MW.S_…` wrapper namespace and root the internal namespaces
at `AlgebraicCurve.RadialRegion`.

**`noncomputable section` is now safe to keep.** `unwired_register.py`'s `NS_EVENT` did
not admit a modifier before `section` (it was fixed 2026-10-14, see
[CARRY-FORWARD.md](../../CARRY-FORWARD.md) "Tool hazards"), so mirror the pin's
`noncomputable section` verbatim — do **not** work around it with explicit
`noncomputable` markers.

## 4. Deliverables — six modules

For each node, an engine (`S_` file whole minus the top-level `solution`, at the pin's
visibility, a `-- pin: <name> (S_…:line)` comment on every public declaration) and a
façade (the wrapper headline verbatim, proven from the engine exactly as the pin's
`solution` does):

* `FLTForHuman/AlgebraicCurve/RadialRegion/Engine/IsOpenStarConvex.lean` (tier 3) +
  `…/RadialRegion/IsOpenStarConvex.lean` (tier 1)
* `FLTForHuman/AlgebraicCurve/RadialRegion/Engine/Recip.lean` + `…/RadialRegion/Recip.lean`
* `FLTForHuman/AlgebraicCurve/RadialRegion/Engine/PowPullbackLaps.lean` +
  `…/RadialRegion/PowPullbackLaps.lean`

Statements and proofs transcribed verbatim; list every v4.34.0-forced adaptation.

## 5. Wiring

`SOURCES` += the three `Theorems/Thm_…` wrappers and the three `P2M/Sol/S_…` files;
`PORT_FILES` += the **three façades only**; appended last with one-line comments. From
the repo root run `python3 tools/deps/unwired_register.py` and confirm `--check` exits 0.
Expected checker delta **+3**, 0 mismatched / 0 missing; the register gains the three
engines (**53** public rows: 16 + 17 + 20; the 56 figure counts the pins' three
`solution`s).

## 6. Build discipline (copy, do not paraphrase)

> Edit loop `timeout 120 lake env lean -DautoImplicit=false -DmaxHeartbeats=200000 <file>`
> (from `lean/`) — the cap is **low on purpose**; never raise `maxHeartbeats`, never add a
> module `set_option maxHeartbeats`. `lake build <module>` per finished file, serialized
> with `flock` and bounded with `timeout`. Never a bare whole-tree `lake build`.

Build each engine before its façade.

## 7. Verification

* tier-0 green on all six, 0 warnings; tier-1 `lake build` green on all six;
* checker `0 mismatched / 0 missing`, `identical` delta exactly **+3**;
* `unwired_register.py --check` exits 0 and lists the three engines, with every row's
  importable name correct (no doubled `AlgebraicCurve.RadialRegion.AlgebraicCurve.…`);
* a scratch `#check` of the three headlines, 0 errors; `#print axioms` on each =
  `[propext, Classical.choice, Quot.sound]`;
* grep sweep for `sorry`/`admit`/`axiom`/`native_decide`/bare `import Mathlib`/
  `maxHeartbeats` — 0 in all six;
* each engine's public count equals its pin's **minus the `solution`** (17→16, 18→17,
  21→20): no demotion;
* `git status` shows the six modules, the six checker appends and the regenerated
  `UNWIRED-PUBLIC.md` only.

## 8. Hub prohibition and report

Only the six new modules, the six checker-list appends and the register rewrite (through
the tool). A promotion or host edit is a stop-and-report; if a tool defect blocks a
correct register, record it rather than editing the tool. Report per R1 §8: paths and
sizes; public/private counts with the no-demotion reconciliation; the namespace mapping;
builds; checker before/after with the delta; the register check; the `#check`/axioms
lines; the grep sweep; `git status`; every adaptation.
