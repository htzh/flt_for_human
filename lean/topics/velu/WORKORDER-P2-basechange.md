# P-2 work order — the base-change / descent column (the D row)

**Status: open, 2026-10-06.** The subject's D row, chosen over the S row: every node is
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
| D | 1,719 | conj, siloBC, siloEx (+ the S row) | the **seam**: `KwD5BetweenCurvesHoloLift` (748), `pointEnd'_eq_of_seam` (264), `KwD5BetweenCurves*`, `kw_surge_hgf4_*` |
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

| set | deliverable | ≈ new lines | dispatch |
|---|---|---:|---|
| **D-1** | `BaseChange.lean` — the shared prelude | ~1,700 | first |
| **D-2** | `IntermediateField.lean` — the countable descent | ~1,900 | after D-1 review |
| **D-3** | `BaseChangeAlgHom.lean` + `VariableChangeAlgEquiv.lean` | ~1,650 | after D-2 review |
| **D-4** | `KernelCyclicTransfer.lean` — `algEquiv_conj` + the seam | ~2,000 | after D-3 review |
| **D-5** | `KernelBaseChange.lean` — both silos, one home | ~2,400 | after D-4 review |

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
  tensor block while `bcff`/the silos carry the `General` ones. If they are not
  specialisations of one general lemma, the two spellings are **different statements**:
  report the pair rather than merging, and keep both names (the checker diffs the text).
- **A promotion that changes a statement.** The 15 promotions are `private` in the port;
  if the pin statement does not match the port's private statement, report the two.
- **A `def … : Prop` whose body is load-bearing.** The tool's substitution test matches
  `def … : Prop` by type only (it is why `KwD5BetweenCurvesHoloLift` scored as a
  substitution). Do not drop such a `def` on the tool's word; `grep -c` its body first.
- **Binder spellings.** A public declaration must spell its binders exactly as the copy
  the checker will match — in practice the `Theorems/` wrapper for a headline and the
  `S_` file for a stripped promotion (`norm` strips only `ModularCurve.`/`AlgebraicCurve.`,
  so `PeriodPair.`/`ModularForm.` qualification is part of the diff).
- **Any pull toward the S row or `eval_modularPolynomial_…`** — that is the boundary (§1).

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
