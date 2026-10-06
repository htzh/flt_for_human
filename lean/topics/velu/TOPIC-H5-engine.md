# H5 — the `IsogenyEndDatum` column: scope, sets, and work orders

**Status: scoped (2026-10-04); SET-1 dispatched.** Work orders for home H5 of
[TOPIC-port-plan.md](TOPIC-port-plan.md) §5, after the H5r dictionary extraction.
Pin `anthropics/fermats-last-theorem@aa2d8b3`; mathlib `v4.34.0`. Method:
[../../porting-playbook.md](../../porting-playbook.md) §2 (plan), §3.4 (sets,
review gates), §3.5 (build ladder), §3.7 (order), §4 (faithfulness); the measured
record is [../../logs/velu-port.md](../../logs/velu-port.md). The mathematics is
[../../../studies/velu-cluster-structure.md](../../../studies/velu-cluster-structure.md)
§2.3 (Spine E).

## 1. What H5 is, measured

H5 is the classification half of Spine E — the two big theorems

* `WeierstrassCurve.Affine.IsogenyEndDatum.exists_dualEndData_dual_mem_and_norm_eq_finrankAlong`,
* `WeierstrassCurve.Affine.IsogenyEndDatum.exists_restrictAlong_placeOfPoint_eq_add`,

together with the engine they share, the `DualEndData` algebra they are stated
in, and the small `IsogenyEndDatum`/`IsogenyHomDatum` vocabulary nodes the plan
§5 folds into this home. Both headlines carry the full gate binders
`[DecidableEq F] [IsAlgClosed F] [CharZero F] {W} [W.IsElliptic]
[GenusOnePlaceGate W] [GenusOnePlaceGate.IsCentred W] [AbelTheorem W]`; the
statements come from the `Theorems/` wrappers, the proofs from the `S_` files.

The two pin files are near-copies of each other, like the map/`restrictAlong`
pair. Splitting their declarations by **name occurrence**:

| group | decls | max-span lines | what it is |
|---|---:|---:|---|
| shared by both `S_` files | 196 | 5,106 | the common engine and the already-ported dictionary/H0 names (many of the 196 are in the port) |
| dual-only | 183 | 5,398 | the `kw_dcao_*` (41), `cmm*`, `idDatum`/`compDatum`, `endst20` tail and the `dualEndData` proof's private helpers |
| res-only | 105 | 2,396 | the non-collinear cases `es1a9_*` (32) and `es1a10_*` (61) |

The plan's block table prices the genuinely-new shared engine at **82 decls /
2,363 once-lines** (`mmr73_cs_*`, `es1a8_*`, `endst20_ps_*`, `kw_hk5f_*`), the
seam at **35 decls / 631 once-lines** (`restrictAlong_comp`,
`pointPullbackHom_yGen`, `es1a4_*`), and the two headline proofs at ≈ 6.3 k
unique (§1.1: 4,008 + 2,316). Net new ≈ **9.3 k lines**. §1.4's 26,674-line
remaining budget is dominated by this home.

### 1.1 The definition module the plan did not count

Both `S_` files and the `Thm_` wrappers import
`Definitions/Def_DualIsogenyAPI.lean` (**316 lines, ~50 declarations**,
mathlib-only: `AddMonoidHom.IsDualPair`, `AddMonoid.End.DualEndData`,
`DualEndData.ofCharPoly`/`intLinComb`/`symm`/`dualEndData_intCast`,
`DualIsogenyExistence`). **None of it is in the port.** It is a clean leaf module
and comes first (§3, SET-1).

### 1.2 Prerequisite: names H5 needs that live only in Vélu (H5r-2)

H5 must not import Vélu. Comparing every declaration name in the H5 `S_` files
against the port, exactly eight pin names are currently declared **only** in Vélu
modules, and all eight are used by the H5 proofs:

| name | now in | home it needs |
|---|---|---|
| `ord_X_eq_neg_two_of_not_isFinitePlace` | `Velu/Engine.lean` | `WeierstrassCurve/Place/Dictionary.lean` |
| `Place.mem_restrictAlong_iff`, `Place.ramificationIndexAlong_pos`, `Place.ord_restrictAlong_ne_zero_iff` | `Velu/RestrictAlong.lean` | new `AlgebraicCurve/Defs/RestrictAlongAPI.lean` |
| `isIntegral_algHomId`, `finiteAlong_algHomId`, `restrictAlong_algHomId` | `Velu/RestrictAlong.lean` | new `AlgebraicCurve/Defs/RestrictAlongAPI.lean` |
| `normFormulaAlong_of_elliptic` | `Velu/RestrictAlong.lean` | the H5 engine (see §5.4) |

The three `Place.*` lemmas already sit in a delimited
`/-! ### Prerequisites: the restrictAlong place calculus -/` block at the top of
`Velu/RestrictAlong.lean`, and `ord_X_eq_neg_two…` is Engine-side dictionary
material — the same class H5r relocated. **Moving them edits existing modules;
that is the one cascade in H5 and it is paid once, in SET-1.**

### 1.3 The `addX_addY_specialize_at_place` node: a second unbudgeted prerequisite

SET-1's shared engine ends with three producers
(`kw_hk5f_addSumCoordSeamDataNCAt_proved`, `kw_hk5f_addGeomMorphSupply_proved`,
`kw_hk5f_addDatumSupply_proved`). They need
`WeierstrassCurve.Affine.FunctionField.addX_addY_specialize_at_place`, whose
canonical home is the separate pin node

* `P2M/Sol/S_WeierstrassCurve_Affine_FunctionField_addX_addY_specialize_at_place.lean`
  — **3,061 lines / 115 declarations**.

It is **not in the port and not in the 42-node slice**: the scout's classifier
missed it, as it missed `Def_DualIsogenyAPI` (the same class of finding as
[TOPIC-H2-engine.md](TOPIC-H2-engine.md) §2). Its 115 declarations are exactly the
`restrictAlong`-column engine (`es1a9_*`, `es1a10_*`, `es1a11_*`,
`kw_hk5f_addSumCoordSeamDataNCAt_proved`), and **all 115 also occur in
`S_…exists_restrictAlong_placeOfPoint_eq_add.lean`** (which inlines the node), so
porting the node once covers the res engine. Consequences:

* SET-1 leaves the three `kw_hk5f_*_proved` unported and reports them rather than
  pulling the node in;
* the `restrictAlong`-add headline's engine *is* this node, so it belongs to SET-2;
* the dual column consumes `kw_hk5f_addDatumSupply_proved`, so SET-3 waits on SET-2.

**Budget effect: re-attribution, not 3,061 new lines.** The node file is not in
the 42-node slice, but **every one of its 115 declarations is also *declared* in
`S_…exists_restrictAlong_placeOfPoint_eq_add.lean`**, which is in the slice (the
res file inlines the node). So the res engine's lines were already inside the res
node's budget and the plan's 26,674 net-new figure did not miss them. What the
budget missed is the node's *existence* (its declarations have a canonical home
and a scheduling role) and its own headline `solution`
(`WeierstrassCurve.Affine.FunctionField.addX_addY_specialize_at_place`, pin
L3001, ~60 lines, absent from the res file and from every slice target). So the
overall figure moves by roughly that one theorem, not by the node's file; H5's
*internal* budget is what is re-cut (the res engine is now priced under the
specialize node, and the dual column acquires a dependency on it). The same
caveat as the file-granular frontier shadowing in
[CARRY-FORWARD.md](../../CARRY-FORWARD.md) applies: a node-level re-measure would
surface the node, while the content-level total stays put.

## 2. Sets: three, sequential, no two in flight

Each set is one coherent story and all of its files are **new** except SET-1's
three moves. The manager reviews SET-1's tree (build, checker, consumer, and the
code) before writing SET-2's order against the modules that actually exist.

| set | story | new modules | edits | net new (est.) |
|---|---|---|---|---|
| **SET-1** | the substrate: extraction + `IsDualPair`/`DualEndData` + the shared engine | `AlgebraicCurve/Defs/RestrictAlongAPI.lean`, `WeierstrassCurve/Isogeny/DualAPI.lean`, `WeierstrassCurve/IsogenyEndDatum/Engine.lean` | `Place/Dictionary.lean`, `Velu/Engine.lean`, `Velu/RestrictAlong.lean` | **landed** — 130/136; the 3 `kw_hk5f_*_proved` move to SET-2 |
| **SET-2** | the `restrictAlong` column: the `addX_addY_specialize_at_place` node, the res-only engine, the 3 shared-engine producers, and the additivity headline | `WeierstrassCurve/IsogenyEndDatum/RestrictAlongAdd.lean` | — | ≈ 4.5 k |
| **SET-3** | the dual-end-data column | `WeierstrassCurve/IsogenyEndDatum/DualEndData.lean` | — | ≈ 3.5 k |

### Module DAG (SET-1 establishes the leaves)

```
AlgebraicCurve/Defs/RestrictAlongAPI.lean   (leaf; imports Correspondence)
WeierstrassCurve/Isogeny/DualAPI.lean       (leaf; mathlib-only)
WeierstrassCurve/Place/Dictionary.lean      (+ ord_X_eq_neg_two; edited)
     └─ WeierstrassCurve/IsogenyEndDatum/Engine.lean   (shared engine)   SET-1
          ├─ WeierstrassCurve/IsogenyEndDatum/RestrictAlongAdd.lean     SET-2
          │    (= the pin `FunctionField.addX_addY_specialize_at_place` node)
          └─ WeierstrassCurve/IsogenyEndDatum/DualEndData.lean          SET-3
Velu/RestrictAlong.lean  imports RestrictAlongAPI (the six move out)     edited once
Velu/Engine.lean         loses ord_X_eq_neg_two (Dictionary supplies it) edited once
```

SET-3 imports SET-1's engine and SET-2 (it consumes
`kw_hk5f_addDatumSupply_proved`, which SET-2's node supplies); SET-2 does not
import SET-3. They are run sequentially by decision.

### Why this minimizes the cascade

All of SET-2/3 are new files: `lake build <module>` re-elaborates one file and
cascades nowhere. SET-1 is the only set in H5 that edits existing modules, and it
did all three moves in one wave, so the `Dictionary`/`Engine`/`RestrictAlong`
dependent cascade was paid once (the whole tree was re-verified green after
SET-1). The move of the six `Place.*`/`algHomId` names went into a **new** file
rather than into `Correspondence.lean` deliberately: adding to that hub would
cascade every WeilExchange/ModularCurve importer.

## 3. Build discipline (copy into every work order)

1. **Do not edit an existing module except the three SET-1 moves.** Anything else
   that looks like a missing prerequisite is a stop-and-report, not a local patch.
2. **Edit loop** (per declaration, no `.olean`, no cascade):
   `timeout 120 lake env lean -DmaxHeartbeats=4000000 -DautoImplicit=false <file>`.
   The two `-D` options are mandatory (`lake env lean` does not inherit the
   lakefile's `leanOptions`).
3. **Module done** (writes the `.olean`, builds dependencies, never dependents):
   `timeout 180 flock .lake/flt_build.lock bash -c 'time lake build <module>'`.
   The lock must live in the workspace (`lean/.lake/flt_build.lock`), not `/tmp`.
4. **Checker at every module close**: `python3 spec/check_flt_statements.py`;
   target `0 mismatched / 0 missing`, and record the `identical` delta.
5. **Never run a bare `lake build`** except the one milestone gate after SET-3.
6. **Iterate on a hard declaration in the gitignored `Scratch*.lean`**, not by
   rebuilding the module.
7. **Import specifically** — the one or two modules the file needs; never
   `import Mathlib` in a library module.
8. **Run one set at a time**; never build concurrently.

## 4. SET-1 work order — the substrate

### 4.1 Scope

The H5r-style extraction (§1.2), the `Def_DualIsogenyAPI` definition module, and
the engine the two headlines share (the pin declarations whose names occur in
**both** big `S_` files), plus the H5 copy of `normFormulaAlong_of_elliptic`.
Not this set: the two headline theorems, the dual-only and res-only engines.

### 4.2 Source

* `P2M/Sol/S_WeierstrassCurve_Affine_IsogenyEndDatum_exists_dualEndData_dual_mem_and_norm_eq_finrankAlong.lean`
  — the primary source and the declaration order for the shared engine. Port the
  intersection of this file's and the res file's declaration sets **once**, in
  **this file's line order** (the pin's definition-before-use order is the
  topological order).
* `P2M/Sol/S_WeierstrassCurve_Affine_IsogenyEndDatum_exists_restrictAlong_placeOfPoint_eq_add.lean`
  — the second copy; use it only to confirm a shared statement/proof, never to
  duplicate a declaration.
* `Definitions/Def_DualIsogenyAPI.lean` — verbatim, names/kinds/namespaces kept.
* The extraction sources: `Velu/Engine.lean` (one declaration) and
  `Velu/RestrictAlong.lean` (the six; the `Place.*` three are pin lines
  3269–3301).

The manager's by-name inventories are `tmp/h5/set1_common.txt`,
`set2_dual_only.txt`, `set3_res_only.txt` (line, kind, private?, span, in-port
location). They are a starting point, not the authority: **regenerate the list
with `tools/deps/port_advise.py`** and reconcile it against the pin before
writing.

### 4.3 Deliverables

1. **New `AlgebraicCurve/Defs/RestrictAlongAPI.lean`** — the six extracted
   declarations, verbatim, in `namespace AlgebraicCurve.Place` /
   `WeierstrassCurve.Affine` as in `Velu/RestrictAlong.lean`. Imports:
   `AlgebraicCurve/Defs/Correspondence.lean`. Then **delete** them from
   `Velu/RestrictAlong.lean` and add the import of `RestrictAlongAPI` there.
2. **Edited `WeierstrassCurve/Place/Dictionary.lean`** — add
   `ord_X_eq_neg_two_of_not_isFinitePlace`; **delete** it from `Velu/Engine.lean`
   (Engine imports Dictionary, so its three uses resolve unchanged).
3. **New `WeierstrassCurve/Isogeny/DualAPI.lean`** — the whole
   `Def_DualIsogenyAPI.lean` (namespaces `AddMonoidHom` and `AddMonoid.End`),
   mathlib-only, statement-verbatim. Add it to the checker `PORT_FILES` and its
   source to `SOURCES`.
4. **New `WeierstrassCurve/IsogenyEndDatum/Engine.lean`** — the shared engine,
   plus `normFormulaAlong_of_elliptic`. Imports: `Place/Dictionary.lean`,
   `Isogeny/ConditionalCurrency.lean`, `Isogeny/DualAPI.lean`,
   `AlgebraicCurve/Defs/Correspondence.lean`,
   `AlgebraicCurve/WeilExchange/Transport.lean` (for
   `AlgebraicCurve.normFormulaAlong`), `WeierstrassCurve/PrincipalDivisors.lean`
   (for `hasPrincipalDivisors_functionField`), `WeierstrassCurve/GenusOnePlaceGate.lean`,
   and the specific mathlib modules the declarations use. Register it in
   `PORT_FILES`.

### 4.4 Fidelity rules that bite here

* **Section variables are invisible to the checker.** Take each declaration's
  binders from the pin's own section, not from the port's H2 modules. Verify with
  a `Scratch*.lean` `#check @<name>` probe and compare with the pin.
* **`normFormulaAlong_of_elliptic` is a same-name/different-statement pair.** The
  pin's H5 section is `[Field F] [DecidableEq F] [IsAlgClosed F] [CharZero F]
  {V W} [V.IsElliptic] [W.IsElliptic]` with **no `hsep`**; the port's
  `Velu/RestrictAlong.lean` copy is the H4 (char-free) version **with `hsep`**.
  Write the H5 copy with the pin's H5 binders and proof (it goes through
  `AlgebraicCurve.normFormulaAlong` + the separability instance). The two live in
  disjoint import branches; do not import `Velu/RestrictAlong.lean` from any H5
  module.
* **Promote pin-private helpers public** (the checker's dotted fallback verifies
  them as promotions), and keep purely local proof helpers `private`.
* **A shape the checker cannot see** (a `def : Prop` bundle, a `class`) still
  needs the pin's kind; `port_advise` is the per-declaration authority.

### 4.5 Verification

* Every edited/new module `lake env lean` clean, then `lake build <module>`.
* `python3 spec/check_flt_statements.py` — `0 mismatched / 0 missing`; record the
  `identical` before → after. A move plus a promotion is a net-zero or small
  positive delta; anything else is a bug.
* `#print axioms` on the SET-1 public surface is
  `[propext, Classical.choice, Quot.sound]`; no `sorry`.
* Do **not** run a bare `lake build` (the milestone is after SET-3).

## 5. SET-2 work order — the `restrictAlong` column (dispatched)

### 5.1 Scope

Port the `restrictAlong`-add column of H5: the canonical
`addX_addY_specialize_at_place` node, the res-only declarations of the
`exists_restrictAlong_placeOfPoint_eq_add` `S_` file that are not already in
Engine, the three shared-engine producers SET-1 left behind, and the additivity
headline. Not this set: the dual-end-data column (SET-3).

### 5.2 Source

* `P2M/Sol/S_WeierstrassCurve_Affine_FunctionField_addX_addY_specialize_at_place.lean`
  — **canonical** for its 115 declarations (`es1a9_*`, `es1a10_*`, `es1a11_*`,
  `kw_hk5f_addSumCoordSeamDataNCAt_proved`, its `solution`); declaration order is
  the topological order.
* `P2M/Sol/S_WeierstrassCurve_Affine_IsogenyEndDatum_exists_restrictAlong_placeOfPoint_eq_add.lean`
  — second copy of those 115 plus the res-only declarations not in Engine.
* `Theorems/Thm_WeierstrassCurve_Affine_FunctionField_addX_addY_specialize_at_place.lean`
  and `Theorems/Thm_…_exists_restrictAlong_placeOfPoint_eq_add.lean` — the
  statement authority (the binders are the wrapper's, not the `S_` file's).
* The three producers are in the two H5 `S_` files at `kw_hk5f_addSumCoordSeamDataNCAt_proved`,
  `kw_hk5f_addGeomMorphSupply_proved`, `kw_hk5f_addDatumSupply_proved`.

### 5.3 Deliverables

1. **New `WeierstrassCurve/IsogenyEndDatum/RestrictAlongAdd.lean`** — the
   `addX_addY_specialize_at_place` node's 115 declarations (statement-verbatim,
   pin order), the res-only declarations of the additivity `S_` file not already
   ported, and the headline
   `WeierstrassCurve.Affine.IsogenyEndDatum.exists_restrictAlong_placeOfPoint_eq_add`.
   Imports: `FLTForHuman.WeierstrassCurve.IsogenyEndDatum.Engine`, the H5 gate
   modules (`GenusOnePlaceGate`, `Isogeny/ConditionalCurrency`), and
   `AlgebraicCurve/Defs/Correspondence.lean`/`RestrictAlongAPI.lean` as needed.
   Do **not** import `Velu/RestrictAlong.lean`.
2. **The three producers live in `RestrictAlongAdd.lean`, not Engine.** Their
   proofs go through the specialize node's `es1a9`/`es1a10` engine, and
   `RestrictAlongAdd` imports Engine, so Engine cannot host them. This is the
   set's first ordering correction: `kw_hk5f_addSumCoordSeamDataNCAt_proved`
   (canonical in the specialize `S_` file) is followed by
   `kw_hk5f_addGeomMorphSupply_proved` and `kw_hk5f_addDatumSupply_proved` (the
   res-only extras), all in `RestrictAlongAdd.lean`.
3. **Checker** — add `RestrictAlongAdd.lean` to `PORT_FILES` (append last) and
   the specialize `S_` file to `SOURCES`.

### 5.4 Fidelity rules that bite here

* The `addX_addY_specialize_at_place` node's `es1a9`/`es1a10` declarations use
  the pin's `attribute [local instance] ModularCurve.Es1a1.instDecEqFunctionFieldEs1a6Add`
  around `es1a6_addSumX`/`endst20_ps_dupX`; without it `rw`/`ring` see distinct
  atoms (SET-1 hit this in `mmr62_cd_collision_addSumX_eq_map_dupX`).
* The headline's section is the wrapper's:
  `[DecidableEq F] [IsAlgClosed F] [CharZero F] {W} [W.IsElliptic]
  [GenusOnePlaceGate W] [GenusOnePlaceGate.IsCentred W] [AbelTheorem W]`.
* `Affine.map_equation` is mathlib's implicit-`W` form; `yGen` needs
  `unfold yGen yCoord` where the pin had the `algebraMap` directly.
* Section variables stay invisible to the checker — `#check @` probe each
  headline against the wrapper.

### 5.5 Verification

`lake env lean` per file; `lake build <module>` per file; checker
`0 mismatched / 0 missing` with the delta recorded; `#print axioms` clean; no
`sorry`. The wave's cascade is checked with one whole-tree `lake build` (the
manager's gate); no bare `lake build` inside the set.

## 6. SET-3 work order — the dual-end-data column and the vocabulary tail

### 6.1 Scope

The dual-end-data column — the dual-only declarations of
`S_…exists_dualEndData_dual_mem_and_norm_eq_finrankAlong.lean` and the headline
`WeierstrassCurve.Affine.IsogenyEndDatum.exists_dualEndData_dual_mem_and_norm_eq_finrankAlong`
— plus the H5 home's vocabulary tail:
`pointEnd_apply_eq_sub`, `pointHom_apply_eq_sub`, `exists_pointEnd_eq_add`,
`exists_pointHom_comp_eq_of_ker_le_of_isCentred`,
`aeval_j_diag_eq_zero_of_finrankAlong_eq`, and the plain
`natCard_ker_pointMapOfPushforward_eq_finrankAlong` (the H5b sibling). Not this
set: the Phase D consumers (`exists_pointEnd_eq_of_mem_isogenyEndSubring`,
`exists_sq_lt_four_mul…`, `exists_forall_pointEnd_eq_zsmul…`).

### 6.2 Source

* `P2M/Sol/S_WeierstrassCurve_Affine_IsogenyEndDatum_exists_dualEndData_dual_mem_and_norm_eq_finrankAlong.lean`
  — the dual-only declarations (`kw_dcao_*` (41), `cmm*`, `idDatum`/`compDatum`,
  `endst20` tail); pin order is the topological order.
* `Theorems/Thm_…_exists_dualEndData_dual_mem_and_norm_eq_finrankAlong.lean` —
  the headline statement (`[DecidableEq F] [IsAlgClosed F] [CharZero F] {W}
  [W.IsElliptic] [GenusOnePlaceGate W] [GenusOnePlaceGate.IsCentred W]
  [AbelTheorem W]`, `(hNs : ∀ D, NormFormulaAlong F D.ι D.hfin) (D)`).
* The vocabulary `S_` files and their `Theorems/` wrappers, all under
  `P2M/Sol/S_WeierstrassCurve_Affine_IsogenyEndDatum_aeval_j_diag_eq_zero_of_finrankAlong_eq.lean`,
  `…_IsogenyEndDatum_exists_pointEnd_eq_add.lean`,
  `…_IsogenyEndDatum_pointEnd_apply_eq_sub.lean`,
  `…_IsogenyHomDatum_pointHom_apply_eq_sub.lean`,
  `…_IsogenyHomDatum_exists_pointHom_comp_eq_of_ker_le_of_isCentred.lean`,
  `…_natCard_ker_pointMapOfPushforward_eq_finrankAlong.lean` (the plain sibling of
  the landed `_of_separableAlong`).

### 6.3 Deliverables

1. **New `WeierstrassCurve/IsogenyEndDatum/DualEndData.lean`** — the dual-only
   engine and the headline. Imports `IsogenyEndDatum/RestrictAlongAdd.lean`
   (transitively Engine + DualAPI) for `kw_hk5f_addDatumSupply_proved` /
   `kw_hk5f_addGeomMorphSupply_proved`, and the gate modules.
2. **New `WeierstrassCurve/IsogenyEndDatum/Vocabulary.lean`** — the six
   vocabulary-tail declarations, statements from their wrappers; it imports
   `DualEndData.lean` (for `aeval_j_diag…`) and the H5b `Isogeny/NatCard.lean`
   (for the plain `natCard` sibling). Split from `DualEndData.lean` only to keep
   two coherent stories; both are new files.
3. **Checker** — append both modules to `PORT_FILES` and every new `S_`/wrapper
   source to `SOURCES` (append last).

### 6.4 Fidelity rules that bite here

* **`solution` must stay `private`.** The dual `S_` file's public `solution` is
  its headline; exposing it as `solution` would diff against an earlier same-last
  name in `SOURCES` (SET-2 hit this with the specialize node). Keep
  `private theorem solution` and expose the wrapper name.
* The gate binders on the headline and on the two producers are the wrapper's.
* `es1a6`/`endst20` proofs need
  `attribute [local instance] ModularCurve.Es1a1.instDecEqFunctionFieldEs1a6Add`
  active at file scope (Engine's instance is reachable cross-module by name);
  `pin W.isUnit_Δ.ne_zero` is the port's `isElliptic_Δ_ne_zero (W := W)`.
* Section variables stay invisible to the checker — `#check @` probe each
  headline against its wrapper.

### 6.5 Verification

`lake env lean` per file; `lake build <module>` per file; checker
`0 mismatched / 0 missing` with the delta recorded; `#print axioms` clean; no
`sorry`. Manager re-verifies with one whole-tree `lake build` at review.

### 6.6 Outcome (landed)

`DualEndData.lean` (3,959 lines, 138 of the 183 dual-only declarations) carries
the dual engine and the headline; `Vocabulary.lean` (177 lines) carries four of
the six vocabulary declarations. Checker `5412 → 5555 identical (313 promoted),
0 mismatched, 0 missing, 36 own` (+143); whole tree green; no `sorry`; axioms
clean. **The H5 home's two big theorems are both landed** (this set's
`exists_dualEndData_dual_mem_and_norm_eq_finrankAlong` and SET-2's
`exists_restrictAlong_placeOfPoint_eq_add`), over SET-1's engine + `DualAPI`.

**Two vocabulary nodes are deferred, deliberately** (stopped, not weakened or
back-filled), because they are Phase D consumers with large unported
prerequisites:

* `IsogenyHomDatum.exists_pointHom_comp_eq_of_ker_le_of_isCentred` needs
  `WeierstrassCurve.Affine.exists_algEquiv_restrictAlong_placeOfPoint_eq_add`
  (pin `S_` 4,271 lines) and `…algHom_ext_of_forall_restrictAlong_placeOfPoint_eq`
  (988 lines);
  **both landed 2026-10-06** — the first as V3
  ([TOPIC-V3-translation-place-action.md](TOPIC-V3-translation-place-action.md),
  `TranslationAlgEquiv.lean`), the second together with this node as V4
  ([TOPIC-V4-isogeny-kernel-rigidity.md](TOPIC-V4-isogeny-kernel-rigidity.md),
  `Vocabulary.lean`). Only `aeval_j_diag_eq_zero_of_finrankAlong_eq` remains here —
  it still needs the `PeriodPair` uniformization ladder plus
  `exists_intermediateField_countable…`,
  `Affine.exists_algHom_functionField_baseChange…`,
  `eval_jLattice_eq_zero_of_isAddCyclic`, `IsAddCyclic.of_squarefree_natCard`,
  `exists_genusOnePlaceGate_isCentred_and_abelTheorem`.

They move to Phase D (see [TOPIC-port-plan.md](TOPIC-port-plan.md) §5 Phase D),
each with its prerequisite set, rather than being priced into H5.

**Friction the record should carry.** Three by-name "in port" labels were false
(`degree` collides with `AlgebraicCurve.Divisor.degree`; `finiteAlong_comp` is
the dual specialization vs the general form; `ord_ofHeightOneSpectrum_eq_neg_log`
is the general `AlgebraicCurve.Place` form vs the port's `RationalFunctionField`
form) and had to be ported. Three unported pin `Theorems/` imports were re-proved
locally rather than pulled in: `finite_torsionBy_of_natCast_ne_zero` and
`Point.exists_zsmul_eq_of_isAlgClosed` from
`FLTForHuman.Elliptic.{card_torsion_of_isAlgClosed,smul_surjective}`, and
`nonempty_torsionBy_addEquiv_zmod_prod_of_isAlgClosed` was avoided by re-proving
its sole consumer `cmm5_dp_natCard_ker_natCast` directly (so the pin-private
`nonempty_pointTorsionBy_zmod`, whose generic `AddCommGroup` lemma is 378 lines,
is omitted). The pin's `S13_instIsDedekindDomainCoordinateRing` referenced a
nonexistent `CoordinateRing.isDedekindDomain` and was rewritten to
`CoordinateRing.isDedekindDomain_of_Δ_ne_zero`.

## 7. Risk register

| risk | mitigation | status |
|---|---|---|
| the prerequisite extraction edits three hubs | one wave in SET-1; the six `Place.*`/`algHomId` names went to a **new** leaf, not `Correspondence` | **resolved** (SET-1) |
| an unbudgeted 3,061-line node (`addX_addY_specialize_at_place`) is on the res route | it is SET-2's subject; all 115 declarations also occur in the additivity `S_` file, so one port covers both | **open** (SET-2) |
| the checker cannot see section variables | `#check @` probe per moved/ported declaration against the pin's section | usual |
| `normFormulaAlong_of_elliptic` same name, different statement from H4 | H5 copy uses the pin's H5 binders; no H5 module imports `Velu/RestrictAlong` | resolved (SET-1) |
| the shared engine's by-name intersection over-counts already-ported names | regenerate with `port_advise`; import the port's copy rather than re-declaring | resolved (SET-1) |
| `InfinitePlace` is a namespace in the pin, a `class` in the port | Engine defines the recovering instance; registered as one `OWN_PROOFS` exemption | resolved (SET-1) |
| a set's turn is cut short by the harness | work in bounded batches with a `tmp/h5/setN-progress.md` line per batch; the manager resumes | working (SET-1) |

## 8. Reproduce

The by-name split of §1 is regenerated by reading the pin `S_` files' declaration
names with `spec/check_flt_statements.py`'s `DECL_RE` and intersecting; the
line/span/in-port inventory is `tmp/h5/set{1,2,3}_*.txt`. The per-declaration
authority remains `tools/deps/port_advise.py` (rerun §TOPIC-port-plan §6); the
remaining-work budget is `tools/deps/build/velu_plan.txt`.
