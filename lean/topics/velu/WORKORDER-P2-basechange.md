# P-2 work order — the base-change / descent column (the D row)

**Status: landed 2026-10-06 (D-1…D-5).** The subject's D row, chosen over the S row: every node is
already premised (frontier `--ready`), it does not depend on S, and it is the gate's
largest remaining prerequisite. Pin `anthropics/fermats-last-theorem@aa2d8b3`; port
mathlib `v4.34.0`. Method: [../../porting-playbook.md](../../porting-playbook.md) §2.4
(dedup), §3.1–§3.2 (role, layout), §3.5 (build ladder), §3.7 (order), §4 (faithfulness).

## 1. Scope

Port the six unported nodes that carry `WeierstrassCurve`/`PeriodPair` base change,
function-field descent and the cyclicity of the isogeny kernel. All are **fully
premised** today: `frontier.py --ready` lists them with no unported prerequisite, and
none of them cites the S row (`S-dep = 0`, `D-dep = 0` for every one).

| node | pin raw | role |
|---|---:|---|
| `WeierstrassCurve.exists_intermediateField_countable_map_eq_and_finrankAlong_eq` | 2,684 | D — countable descent |
| `WeierstrassCurve.Affine.exists_algHom_functionField_baseChange_finrankAlong_eq` | 1,336 | D — base change to ℂ |
| `WeierstrassCurve.nonempty_functionField_algEquiv_of_variableChange` | 744 | D — variable change |
| `WeierstrassCurve.Affine.isAddCyclic_ker_pointMapOfPushforward_of_algEquiv_conj` | 1,821 | D — kernel cyclicity under conjugation |
| `WeierstrassCurve.Affine.isAddCyclic_ker_pointMapOfPushforward_of_baseChange_algHom` | 5,357 | D — kernel cyclicity under base change |
| `WeierstrassCurve.Affine.exists_algHom_baseChange_of_isAddCyclic_ker_pointMapOfPushforward` | 5,338 | D — existence of the base-changed datum |

**Not this set:** the S row (the `PeriodPair` seam/index arithmetic:
`exists_differentiable_toPoint_comp_…`, the two `exists_scale_lattice_…`,
`exists_mem_primCosetReps…`, `eval_jLattice_eq_zero_of_isAddCyclic`,
`IsAddCyclic.of_squarefree_natCard`), the `rationalHomSet`/torsion columns, and
`eval_modularPolynomial_map_j_eq_zero_of_isAddCyclic_ker_pointMapOfPushforward` (the
consumer; it is the S/D capstone). A worker that reaches an unported prerequisite
**stops at the boundary and reports**.

## 2. The dedup, measured

The six `S_` files are **17,280 raw lines / 696 declarations**; the two
`…isAddCyclic_ker_pointMapOfPushforward_of_baseChange_algHom` /
`…exists_algHom_baseChange_…` files (5,357 / 5,338) are near-identical — 163 of their
176 declarations coincide (4,926 removable lines). After statement-anchored dedup
(`port_advise` statements, private included):

```
distinct declarations                     350
  already public in the port            95   (3,220 lines — import, do not re-prove)
  private in the port (promote)         15   (  121 lines)
  NEW to write                          240   (5,470 lines)
      of which shared by ≥2 files       88   (2,393 lines)
      node-unique                      152   (3,077 lines)
```

`port_plan`'s coarser figure is 6,748 net-new (it scores 12 `def … : Prop` matches as
type-only suspects); treat **5,470 / 240 declarations** as the working figure.

**Already in the port** (import; the pin copies are re-proofs): the place dictionary
(`Place/Dictionary.lean`: `isFinitePlace_*`, `evalAt_*`, `ord_*`, `eq_placeOfEquation_*`,
`algebraMap_coordinateRing_ne_zero`, `placeOfPoint_*`), `FunctionFieldQuadratic.lean`
(`yGen`, `transcendental_polyToFunctionField_X`), `IsogenyEndDatum/Engine.lean`
(`restrictAlong_eq_infinitePlace`, `normFormulaAlong_of_elliptic`, `pointEnd'_eq_of_seam`),
`Isogeny/NatCard.lean`, `GenusOnePlaceGateCentred.lean`, and the whole `Elliptic/PeriodPair/`
lattice/uniformization prelude (the `kw_isUniformization`/`kw_toPoint*`/`kw_ker_toPointHom`
chain — `private` in the port, so those copies are dropped).

**Promotions needed** (15, all `private` in the port; verify through the checker's
`stripped_source`/dotted fallback): `apply_eq_apply_of_differentiable_of_forall_periodic`,
`toPoint_neg`, `toPoint_add_mem`, `sub_fract_mem_lattice`, `kw_countable_lattice`,
`kw_toPoint_add` (→ `Elliptic/PeriodPair/Uniformization.lean`), `discriminantNeZero_scale_iff`
(→ `Discriminant.lean`), `scaleLatticeEquiv_apply`, `latticeEquivOfEq`, `mulLeftR*`,
`mulLeftZ*` (→ `Lattice.lean`), `kw_iCa_genSet` (→ `WeightOne/Basic.lean`).

## 3. The shared prelude — the reason for the order

`port_advise`'s `blocks` section (declarations shared by an *identical* set of target
files) is the schedule:

| block | once | files | contents |
|---|---:|---|---|
| A | 946 | all 5 | the `pointPullback*` column + `kw_functionField_algHom_ext` + `kw_coordinateRingBasis` + `degree` (`transcendental_…_X`, `equation_map_…_yGen` are already ported) |
| B | 400 | siloBC, siloEx, bcff | the function-field **tensor** block (General) |
| C | (in A/B split) | interm, siloBC, siloEx | the same tensor block, **NoAC** spelling |
| D | 1,719 | conj, siloBC, siloEx (+ the S row) | the **seam**: `KwD5BetweenCurvesHoloLift` (11 lines — the 748 was a `p2m_*` span artefact; all five pin copies are byte-identical), `pointEnd'_eq_of_seam` (264), `KwD5BetweenCurves*`, `kw_surge_hgf4_*` |
| E | 1,513 | siloBC, siloEx | the two silos' own `kw_surge_hgf4_*` / `KwD5*` tail |

Blocks A/B/C/D are written **once**, in `WeierstrassCurve/Isogeny/BaseChange.lean`; the
node modules import it. Block D is shared with the *S* row's
`exists_differentiable_toPoint_comp_…` and `exists_scale_lattice_…_isAddCyclic_sublatticeQuotient`,
so its home is chosen here and the S row will import it later (that is the S row's
problem, not this set's — do not port the S nodes).

### 3.1 Import rule (binding for every set)

**Do not import `WeierstrassCurve/GenusOnePlaceGateCentred.lean` or
`WeierstrassCurve/Place/RRSpace.lean` in any module of this column.** The gate *classes*
(`GenusOnePlaceGate`, `GenusOnePlaceGate.IsCentred`, `AbelTheorem`) live in the lighter
`WeierstrassCurve/GenusOnePlaceGate.lean`, and the column's pin hypotheses supply them as
arguments — the *producer* `exists_genusOnePlaceGate_isCentred_and_abelTheorem` is never
needed. The producer's module pulls `Place/RRSpace.lean`, whose `scoped instance
instInfinitePlace` collides at the *name* level with `IsogenyEndDatum/Engine.lean`'s
`WeierstrassCurve.Affine.instInfinitePlace`, so no environment can import both
(verified: `import GenusOnePlaceGateCentred` + `import IsogenyEndDatum.Engine` fails with
`environment already contains 'WeierstrassCurve.Affine.instInfinitePlace._proof_4'`).
D-4 and D-5 **need** `Engine.lean` (`restrictAlong_eq_infinitePlace`,
`pointEnd'_eq_of_seam`, `normFormulaAlong_of_elliptic`); D-1 was corrected to import
`GenusOnePlaceGate.lean`, which removes RRSpace from the column and makes that possible.
Registered in [../../CARRY-FORWARD.md](../../CARRY-FORWARD.md).

### 3.2 Naming: strip `kw_` when promoting

**Strip the `kw_` prefix whenever the port promotes a helper** — whenever it gives a pin
helper a public home as the port's own reusable API. Declare it at the prefix-stripped pin
name (`kw_g₂_ofTau` → `g₂_ofTau`); the checker verifies it through `stripped_source`,
prints `RENAMED`, and counts it in `renamed`. The criterion is *promotion*, not the pin's
`private` marker: all five existing `renamed` rows (`G_ofTau_eq`, `riemannZeta_six`,
`g₂_ofTau`, `g₃_ofTau`, `jLattice_ofTau_eq`) come from pin-**public** `kw_` declarations
that P-SET-1/P-SET-2 re-homed into `Elliptic/PeriodPair/`.

A helper that stays local to its module is `private` with a content name and never carries
`kw_` — that is how D-2's descent block is landed, and it is why the checker surface of a
single-node set is usually one declaration. **Do not leave a declaration both public and
stripped**: it is either a promotion (strip, public) or transcription (keep the pin name)
or local (private).

A pin declaration **transcribed at its pin name and namespace keeps the pin's name**,
including a `kw_` prefix: that is the mechanical-faithfulness default (267 `kw_` public
declarations in the older modules) and it keeps `renamed` a small, meaningful signal.

**Applied to D-1 (2026-10-06), before D-3 was written.** `BaseChange.lean` was a new shared
home for 56 pin-public `kw_` helpers (and 4 `scoped instance`s), i.e. a promotion; the
prefix was stripped in place so that D-3–D-5 import the stripped names and are written
once rather than re-done. Checker: `5942 identical (313 promoted, 5 → 61 renamed), 0
mismatched, 0 missing, 36 own, 5978 checked`.

That required one checker change, recorded in
[../../porting-playbook.md](../../porting-playbook.md) §4: `norm` now erases the `kw_`
prefix **inside statements** on both sides, not only on the declaration name. Twenty of
the 56 have statements that mention a promoted map —
`functionFieldMapAlongGeneralNoAC_polyToFunctionField_X` states
`functionFieldMapAlongGeneralNoAC W F F' (polyToFunctionField (W⁄F) X) = polyToFunctionField (W⁄F') X`
— so renaming the map changed the statement text and the diff failed (measured: 20
`missing`). Erasing the prefix on both sides keeps `kw_foo` and `foo` comparable without
weakening the diff, and it moved nothing else: `identical` is unchanged at 5942 and
`mismatched`/`missing` stay 0.

Sets D-3–D-5 import D-1's **stripped** names; a new public helper any of them introduces
follows the rule above.

## 4. Module DAG and the sets

New files only; no library module is edited except the 15 promotions. Every module is a
leaf, so no set cascades.

```
WeierstrassCurve/Isogeny/BaseChange.lean          D-1  the shared prelude (blocks A/B/C part)
  ├─ WeierstrassCurve/Isogeny/IntermediateField.lean   D-2  interm    (2,684)
  ├─ WeierstrassCurve/Isogeny/BaseChangeAlgHom.lean    D-3a bcff      (1,336)
  ├─ WeierstrassCurve/Isogeny/VariableChangeAlgEquiv.lean D-3b varCh  (744)
  └─ WeierstrassCurve/Isogeny/KernelCyclicTransfer.lean D-4  conj (1,821) + seam (block D)
       └─ WeierstrassCurve/Isogeny/KernelBaseChange.lean  D-5 the two silos, ONE home (5,357+5,338 → block E once)
```

| set | deliverable | priced | **landed** | dispatch |
|---|---|---:|---:|---|
| **D-1** | `BaseChange.lean` — the shared prelude | ~1,700 | **1,168** | first |
| **D-2** | `IntermediateField.lean` — the countable descent | ~1,900 | **1,124** | after D-1 review |
| **D-3** | `BaseChangeAlgHom.lean` + `VariableChangeAlgEquiv.lean` | ~1,650 | **382** | after D-2 review |
| **D-4** | `KernelCyclicTransfer.lean` — `algEquiv_conj` + the seam | ~2,000 | **472** | after D-3 review |
| **D-5** | `KernelBaseChange.lean` — both silos, one home | ~2,400 | **1,377** | after D-4 review |

Every set landed 2026-10-06; 4,523 written lines against the row's 5,470 new-declaration
lines, the difference being the shared homes (D-1 and D-5) that turned the pin's repeated
preludes into imports. The priced column was an upper bound taken from pin `S_`-line counts;
three of the five came in well under because `port_advise`'s own-file figures count inlined
preludes and `p2m_*` scaffolding. The column's checker closed at
`6037 identical (313 promoted, 67 renamed), 0 mismatched, 0 missing, 36 own, 6073 checked`
(entry state: `5869 identical (313, 5), 0/0, 36 own, 5905`); the per-set record is
[../../logs/velu-port.md](../../logs/velu-port.md) §P-2.

One set per subagent, reviewed before the next (playbook §0.2, §3.4). The sets are
independent after D-1, so D-2/D-3 could be reordered if a review changes the picture;
D-4 and D-5 must follow D-1, and D-5 reuses D-4's seam home.

## 5. Order inside the column

1. **Definitions and the shared prelude first** (D-1): nothing can be stated before the
   tensor/point-pullback vocabulary, and D-1 is a leaf.
2. **`interm` second** (D-2): the largest single item and the one the gate names first.
3. **`bcff` and `varCh` third** (D-3): the two mid-size generic nodes.
4. **The kernel column last** (D-4, D-5): it is the largest, it reuses the seam, and its
   two 5.3 k files must be ported as **one** home — porting them as two would repeat the
   package-by-package mistake the WeightOne rectification paid for.

## 6. Risks (stop and report, do not push)

- **The `NoAC` vs `General` split.** `interm`'s S_ file carries `…NoAC` spellings of the
  tensor block while `bcff`/the silos carry the `General` ones. **Resolved as landed**: the
  two `def … : Prop` bodies are identical and the `NoAC` block is strictly more general
  (it drops `[IsAlgClosed F] [IsAlgClosed F']`), so 24 of the 30 `General` declarations are
  one-line invocations of their `NoAC` twin and both names are kept — the checker diffs the
  text. The six datum-indexed ones could not delegate: the pin indexes `General` by
  `IsogenyEndDatum` and `NoAC` by `TreeIsogenyEndDatum`, different structures, so they were
  proved directly.
- **A promotion that changes a statement.** The promotions are `private` in the port; the
  column needed **21** — the plan's 15, plus D-5 `§1.5`'s six
  (`PeriodPair.{toPointHom, toPointHom_apply, ker_toPointHom, toPointAddEquiv,
  toPointAddEquiv_mk, discriminantNeZero}`, the last because `toPointHom_apply`'s statement
  mentions `L.kw_discriminantNeZero`). If the pin statement does not match the port's
  private statement, report the two.
- **A `def … : Prop` whose body is load-bearing.** The tool's substitution test matches
  `def … : Prop` by type only (it is why `KwD5BetweenCurvesHoloLift` scored as a
  substitution). Do not drop such a `def` on the tool's word; `grep -c` its body first.
- **Binder spellings.** A public declaration must spell its binders exactly as the copy
  the checker will match — in practice the `Theorems/` wrapper for a headline and the
  `S_` file for a stripped promotion (`norm` strips only `ModularCurve.`/`AlgebraicCurve.`,
  so `PeriodPair.`/`ModularForm.` qualification is part of the diff).
- **Any pull toward the S row or `eval_modularPolynomial_…`** — that is the boundary (§1).
- **Universe polymorphism is part of a shared declaration's statement (found 2026-10-06,
  D-3 on D-1).** D-1 monomorphised the prelude's section variables to `universe u`
  (`F : Type u`, `F' : Type u`), but the pin's `bcff` file is `universe u v w` with
  `F : Type v`, `F' : Type w` (`R₀ : Type u`) and the wrapper spells `(F : Type v)` /
  `(F' : Type w)` — so the D-3 headline could not instantiate the prelude
  (`Type v` against `Type u`). The port must carry the pin's universe *spelling*, not just
  its hypothesis set: section-variable universes do not enter the checker's statement diff
  (it reads the text after the declaration name), so the mechanical check is blind to it
  and only the consumer's elaboration catches it. D-1 was generalised in place; the two
  sections moved together because every `General` declaration invokes its `NoAC` twin.
  When a set ports a shared block another set will consume, check the *consumers'* pin
  universe declarations too, not only the block's own file. The same collapse appeared one
  section later: D-1's `section PointPullbackTo` pinned `{L : Type u}` where the pin writes
  `{L : Type*}` (bcff:404), so `pointPullbackHomTo` could not take
  `L := (W⁄F').FunctionField : Type w`. The symptom is diagnostic: **a `whnf` heartbeat
  timeout in a shared block usually means a universe was pinned too tight, not that the
  proof is heavy** — the unifier spins instead of failing, and the two `def`s it hit are
  exactly the ones the pin guards with a 51.2M-heartbeat bump. Naming the implicits at the
  application sites inside the bodies removed the search, so the port's 4M cap suffices;
  the pin's `set_option` bumps are not transcribed and the statements do not move.

## 7. Build discipline (binding, copy into every set order)

> `lake env lean <opts> <file>` is the edit loop, `<opts>` =
> `-DmaxHeartbeats=4000000 -DautoImplicit=false`; `lake build <module>` when a file is
> done; **one** `lake build` per wave; the full build at the milestone. Bound every build
> (`timeout 60`/`90`/`300`), serialize every `lake build` with
> `flock .lake/flt_build.lock`. Never raise `maxHeartbeats`. Import specifically — never
> `import Mathlib` in a library module. Iterate in bounded blocks, not per declaration.
> Keep heavy modules at the leaves.

New files cost no cascade, but they import the **16 MB** `LevelField`/`WeightOne` oleans
through `Elliptic/PeriodPair/Discriminant.lean`; the seam and silo modules will also
import `IsogenyEndDatum/Engine.lean`. Measure the first `lake env lean` time of each new
module before writing the whole file, and report a blow-up rather than bisecting inline.

## 8. Verification (every set)

- `lake env lean` clean per module; `lake build <module>`; then one wave `lake build`
  over the set, bounded and `flock`ed, timed (wall + user/sys).
- `python3 spec/check_flt_statements.py` → **0 mismatched / 0 missing**. Baseline
  **`5869 identical (313 promoted, 5 renamed), 0 mismatched, 0 missing, 36 own, 5905
  checked`** (2026-10-06, after P-SET-2). Reconcile every delta; a mismatch is a bug.
- The `SOURCES` entries for a set are the `Theorems/` wrapper plus the `S_` file of each
  node it lands (wrapper before `S_`); `PORT_FILES` gets the new module, appended last.
- Extend `spec/` — do not add `#check`s. A new zone per set, a real executed
  cross-module composition; add a `spec/…Consumer.lean` or extend
  `spec/WeierstrassCurveConsumer.lean`; deleting any one new module must make it fail.
- `#print axioms` on every headline: `[propext, Classical.choice, Quot.sound]`; no `sorry`.
- `grep -c` of every declaration dropped as already-present or duplicate, with the
  reason, in the friction log; the full table goes in
  [../../logs/velu-port.md](../../logs/velu-port.md) §P-2.

## 9. Close-out (fill per set, in the log)

Written lines per module; checker before → after and the reconciliation; the promoted
count; the consumer exit and time; whole-tree build jobs and seconds; `#print axioms`;
friction findings; any statement whose binder spelling had to follow the wrapper rather
than the `S_` file; and — for the silo set — the measured proof that the two pin files
became one home (duplicate lines shipped, before and after).
