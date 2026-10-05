# Vélu port plan — factoring the 91 k-line cluster

**Status: the explicit-Vélu column, the H5r dictionary extraction, H5 and the
torsion-API promotion are landed; the base-change column and the cheap-node
phases remain.** H0, the H1w place dictionary, the H2 engine (SET-1/2/3) and both
explicit-Vélu headline pairs (H3/H4) are in the port, together with the H5a/H5b
prerequisites the wire test pulled forward. The plan's **Phase C capstone** — its
four headline theorems — therefore landed early, during what the plan had
scheduled as Phase A; Phase C's two `IsogenyEndDatum` theorems did not, and are
the deliverable of home **H5**, whose three sets have now landed (the shared
engine + `Isogeny/DualAPI.lean`, the `restrictAlong`-add column, and the dual
column), with two vocabulary nodes deferred to Phase D; see
[TOPIC-H5-engine.md](TOPIC-H5-engine.md). The H5r refactor round has since
moved the place dictionary out of the Vélu modules into
`WeierstrassCurve/Place/Dictionary.lean`, so H5 can import it without importing
Vélu. Re-measured against the port, the remaining slice is **42 nodes / 26,674
net new lines** (pre-port: 47 / 39,986). Dated record:
[../../logs/velu-port.md](../../logs/velu-port.md).

The operative plan for the Vélu block
of the elliptic-curve subject (scout §4 items 4–5). Pin
`anthropics/fermats-last-theorem@aa2d8b3`; port mathlib `v4.34.0`. The subject
scout is [../../../studies/elliptic-weierstrass-tate-scout.md](../../../studies/elliptic-weierstrass-tate-scout.md)
(§2 measures the block, §4 orders the subject); the method is
[../../porting-playbook.md](../../porting-playbook.md) §2 (plan), §3.4 (sets/review),
§3.7 (order), §4 (faithfulness). The worked precedent for the reuse-first method is
[../../logs/card-torsion-port.md](../../logs/card-torsion-port.md). The theory
structure of the cluster (the two proof spines) and the derivation of this plan as
a reusable method are in
[../../../studies/velu-cluster-structure.md](../../../studies/velu-cluster-structure.md).

Everything below is measured with `tools/deps` on the scout §6 `--nodes` slice
(47 nodes / 91,442 raw `S_` lines pre-port — the scout's unit classifier spells
the same block as 49 nodes / 91,772 lines; two nodes differ between the two
spellings). The numbers are the tools' numbers, not estimates; §6 reproduces
them. §1–§3 are the pre-port planning measurement that derived the factoring;
§1.4 re-runs the same instrument against the port to price what is left. The text
report of the naive instrument is ~105 kB over 4,607 declarations — too large to
read as a plan — so §4 describes the compact companion that regroups it.

## 0. Decision in one paragraph

The slice is **91,442 raw `S_` lines but 42,970 lines once each declaration
statement is counted once, and 39,986 after subtracting what the port already
has**. The mass is not mathematics; it is four 10 k-line files that are near-copies
of each other plus a ~370-declaration prelude repeated in all four. So: (1) port
the shared prelude **once** into homes; (2) port only the **general** member of
each `X` / `X_of_Y` pair and derive the plain one; (3) then the four big theorems
are thin layers over the homes. The naive arithmetic
`91k − 50k removable − 10k already ported ≈ 31k` is **wrong by ~9 k**: it
subtracts per-occurrence substitutions that sit inside the removable duplicates
(§1.3). The port has since realized the deduction: §1.4 re-measures what remains
at **26,674** net new lines.

## 1. Budget: what is actually new

On the 47 `S_` files:

| quantity | lines |
|---|---:|
| raw `S_` lines | 91,442 |
| declaration lines | 90,139 |
| — duplicate copies (removable by porting once) | 47,169 |
| boilerplate (imports, `attribute`, `p2m_*`, sections) | 1,303 |
| **distinct declaration groups** | **1,930** |
| once-cost after dedup | 42,970 |
| — already in the port (vetted substitutions) | 2,984 |
| **net new mathematics** | **39,986** |

So the honest reduction is **56 %**, not the ~66 % a first pass suggests. Of the
~40 k, about **21 k is shared engine** and **19 k is genuine per-theorem work**.

### 1.1 Where the 19 k sits

| node | raw | unique-to-node (approx) |
|---|---:|---:|
| `Affine.IsogenyEndDatum.exists_dualEndData_dual_mem_and_norm_eq_finrankAlong` | 9,956 | 4,008 |
| `veluQuotient_oddOrderSummingSet_discriminant_prod_veluU_pow` | 3,566 | 3,546 |
| `Affine.exists_intermediateField_countable_map_eq_of_…` | 3,729 | 2,035 |
| `Affine.IsogenyEndDatum.exists_restrictAlong_placeOfPoint_eq_add` | 7,298 | 2,316 |
| `exists_addMonoidHom_coe_eq_veluPointMap2` | 1,438 | 1,292 |
| `bijOn_cyclicQuotientJ_isRoot_modularPolynomial_of_transcendental_j` | 1,133 | 1,082 |
| `Affine.IsogenyEndDatum.exists_pointEnd_eq_of_mem_isogenyEndSubring` | 2,745 | 521 |

The rest of the 47 nodes are ≤ 500 unique lines each, and **23 of the 47 have no
shared helpers at all**. `veluQuotient_oddOrderSummingSet_discriminant_prod_veluU_pow`
is self-contained (203 private helpers, shared with nothing) and is best ported as
one package.

### 1.2 The four big files are one proof in four copies

`exists_dualEndData…` (9,956) and `exists_restrictAlong_placeOfPoint_eq_add`
(7,298) are the `IsogenyEndDatum` endomorphism-data column. `velu_map_equation…`
(11,992 / 12,012) and `exists_veluFunctionFieldHom_restrictAlong_placeOfPoint_eq…`
(9,542 / 9,786) are the explicit-Vélu column. The tools measure:

* the four explicit-Vélu files share **373 declarations / 7,265 once-lines** —
  66 % of the whole "port once" figure;
* the two `IsogenyEndDatum` files share **82 declarations / 2,363 once-lines**;
* the strongest factoring unit is the 11,614-line pair
  `velu_map_equation…` ↔ `…_of_isAlgClosed` (641 proofs); the strongest
  cross-column unit is 8,596 lines between a `velu_map` and a `restrictAlong`
  file.

### 1.3 Why 30 k is too optimistic

The advice tool reports substitutions **per occurrence**: a lemma present in ten
target files and already in the port contributes ten rows. It reports removable
duplicates **per statement group** (occurrence-sum minus one copy). Subtracting
both double-counts every in-port declaration that is also duplicated, which is
most of them. At *group* granularity the in-port saving collapses from 9,676
per-occurrence lines to **2,984**: "keep one copy" already zeroes the other
copies, and the only extra saving is that the kept copy is free.

### 1.4 Re-measured against the port

The landed explicit-Vélu column removes its four `S_` files and the H1w /
place-gate nodes from the slice. Re-running §6 against the present port — the
node filter is "nodes the port does not yet provide", so it shrinks as homes
land — gives the remaining work:

| quantity | pre-port | remaining |
|---|---:|---:|
| nodes | 47 | 42 |
| raw `S_` lines | 91,442 | 47,509 |
| distinct declaration groups | 1,930 | 1,282 |
| once-cost after dedup | 42,970 | 30,647 |
| — already in the port | 2,984 | 3,973 |
| **net new mathematics** | **39,986** | **26,674** |

So the engine and its four headlines consumed ≈ 13.3 k of the original 40 k. All
seven nodes of §1.1 are still ahead, so that table still says where the mass is:
the two `IsogenyEndDatum` headlines H5 owns are ≈ 6.3 k unique, the two large
self-contained consumers (`veluQuotient_oddOrderSummingSet_discriminant_prod_veluU_pow`,
`exists_intermediateField_countable_map_eq_of_…`) ≈ 5.6 k, and the rest is §5's
cheap-node phases.

## 2. The factoring units (homes)

Regrouping the shared declarations by **identical target-file set** gives the
homes: write each once, import it everywhere the row lists. The load-bearing
rows (the full 39 rows ≥ 40 lines are in the tool's `blocks` section):

| once | in port | decls | files | what it is |
|---:|---:|---:|---:|---|
| 7,265 | 65 | 373 | 4 | the explicit-Vélu engine (`veluY_*`, `veluDeficit*`, `evalAt_velu*`, `addXFun_*`, `map_veluQuotient`…) |
| 3,660 | 2,741 | 173 | 2 | the `velu_map_equation`-only engine (`isPrincipalIdealRing_comap`, `deg_placeInfty`, `ord_placeInfty_X`, `wqDiscPoly_ne_zero`…) — mostly **already ported**, in `AlgebraicCurve/P1/` |
| 2,363 | 0 | 82 | 2 | the `IsogenyEndDatum` engine (`mmr73_cs_*`, `es1a8_*`, `endst20_ps_*`, `kw_hk5f_*`) |
| 1,496 | 0 | 41 | 2 | the base-change/tensor engine (`kw_surge_hgf4_*`, `kw_functionFieldTensor*`) |
| 1,331 | 0 | 68 | 2 | the `restrictAlong`-only engine (`s2c_key`, `veluXClearedPoly_monic`, `kw_restrictAlong*`) |
| 972 | 0 | 4 | 10 | the function-field bridge — `transcendental_polyToFunctionField_X`, `yGen`, `equation_map_polyToFunctionField_yGen`, `polyToFunctionField_eq_aeval` |
| 748 | 0 | 1 | 3 | `KwD5BetweenCurvesHoloLift` (a `def : Prop` bundle) |
| 725 | 556 | 21 | 3 | the place/ramification dictionary — mostly **already ported** |
| 631 | 0 | 35 | 3 | the `IsogenyEndDatum` seam (`restrictAlong_comp`, `pointPullbackHom_yGen`, `es1a4_*`) |
| 577 | 279 | 11 | 6 | `ord_add_eq_min`, `ord_sub_evalAt_pos`, `evalAt_*` — partly ported |
| 528 | 0 | 22 | 3 | `kw_functionField_algHom_ext`, coordinate-ring tensor basis |
| 316 | 0 | 8 | 2 | `pushforwardAlong_pushforwardAlong`, `inertiaDegAlong_comp` |
| 280 | 0 | 5 | 8 | `pointEnd'_eq_of_seam` |
| 248 | 18 | 15 | 11 | `isFinitePlace_of_mem`, `isFinitePlace_iff_exists_placeOfEquation` |

**Reuse first (playbook §2.4).** The vetted substitutions come from
`FLTForHuman/AlgebraicCurve/P1/Dictionary.lean` (39 decls),
`…/Defs/PlaceDictionary.lean` (33), `…/Defs/PlacesOverDVR.lean` (58),
`…/Defs/PlaceEvaluationAlgebra.lean` (31), `…/Defs/PushPull.lean` (32),
`FLTForHuman/WeierstrassCurve/FunctionFieldQuadratic.lean` (63), and the rest of
`AlgebraicCurve/`. That is exactly the "shallow, wide API surface" the header of
[`FunctionFieldQuadratic.lean`](../../FLTForHuman/WeierstrassCurve/FunctionFieldQuadratic.lean)
says it deliberately left to the consumer. This cluster **is** that consumer: it
should import that surface, not re-derive it.

**Correction (2026-10-04, after H2's measurement).** That surface is the
*general* `AlgebraicCurve.Place`/`P¹` layer. The **Weierstrass** `CoordinateRing`
dictionary — `placeOfEquation`, `IsFinitePlace`, `heightOneSpectrumOfEquation`,
`exists_eq_XYIdeal_of_isMaximal`, `isDedekindDomain_of_Δ_ne_zero` — was never
ported: it is the deferred [CARRY-FORWARD.md](../../CARRY-FORWARD.md) entry #1,
whose registered trigger is this very cluster. H2 cannot import it; it must be
written first, as home **H1w**. Measured: `IsFinitePlace` occurs 713 / 405 / 525
times in the `IsogenyEndDatum` and base-change files and zero `velu*` names do,
so H1w is the slice's true prerequisite and H5/H6 run parallel with each other
after it. H1w and the explicit-Vélu rows of the table above are now landed; the
`IsogenyEndDatum` and base-change rows are H5/H6. See
[TOPIC-H2-engine.md](TOPIC-H2-engine.md).

## 3. The sibling rule: port the general, derive the special

The `X` / `X_of_Y` target pairs whose declaration sets nest, with the public
binders compared:

| pair | plain / general | overlap | verdict |
|---|---|---:|---|
| `velu_map_equation_of_oddOrderSummingSet` | 11,992 / 12,012 | 99.2 % | **implication** — general drops `(h2 : (2:L) ≠ 0)` |
| `exists_veluFunctionFieldHom_restrictAlong_placeOfPoint_eq` | 9,542 / 9,786 | 98.4 % | **implication** — general drops `[CharZero F]` |
| `natCard_ker_pointMapOfPushforward_eq_finrankAlong` | 547 / 601 | 96.3 % | **variant** — plain has `[CharZero F]`; `…_of_separableAlong` has `[HasPrincipalDivisors …]` + `hsep`; neither implies the other for free |

For the two implications the conclusion is syntactically identical; the general
statement is the plain one with one hypothesis/instance removed — compare the
public wrappers
[`Thm_…_velu_map_equation….lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_WeierstrassCurve_velu_map_equation_of_oddOrderSummingSet.lean#L8-L14)
and
[`Thm_…_of_isAlgClosed.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_WeierstrassCurve_velu_map_equation_of_oddOrderSummingSet_of_isAlgClosed.lean#L8-L13).
The plain `S_` file's own unique content is 5 decls / 98 lines (`velu_map`) and
9 decls / 308 lines (`restrictAlong`); everything else is the shared engine. So:

> **Port `…_of_isAlgClosed`; make the plain theorem a corollary.** The ~12 k-line
> and ~9.5 k-line plain proof bodies are not transcribed at all.

Both public statements are genuinely needed downstream — the plain
`restrictAlong` feeds `…_pointMapOfPushforward_ker_eq_zmultiples` and
`…_of_oddOrder`; the general one feeds the `fullKernelHom` chain — so the pair
must be *provided*, not dropped. The `natCard` row is the warning: the `_of_`
suffix does not imply generality. Always compare binders (the tool does) before
collapsing.

## 4. Handling the output: vet the substitutions

Two instrument limits decide how the advice must be read.

**`def : Prop` false positives.** The statement checker reads a `def`'s **type**
as its statement, and for `def foo : Prop := …` that type is just `Prop`; any two
`Prop`-valued defs then "match". On this slice that produces 70 rows / 2,420
per-occurrence lines of false positive, all of the shape
`KwD5BetweenCurvesHoloLift -> EisensteinWeightOne.E1Chi3IsModular`,
`KwD5… -> CohCarrier.H1`, `addXFun -> WeierstrassCurve.Affine.yCoord`,
`inertiaDeg -> AlgebraicCurve.Place.deg`. Split the 495 substitutions into
**425 trusted** (theorems, structures, and defs whose last name matches the
port's) and **70 suspect**, and count only the trusted against the budget; verify
each renamed `def` by name or body before treating it as done.

**Pairwise factoring figures.** The "strongest factoring units (target module
pairs)" line is pairwise, so a declaration shared by four files is counted in six
pairs; the block view in §2 counts it once. Use the block row, not a single
declaration span, for planning — a `def`'s span can be inflated where its
`p2m`-generated proof is not matched by the declaration regex
(`KwD5BetweenCurvesHoloLift` reads as 748 lines but is a `def : Prop` bundle).

The compact companion used here (`tools/deps/port_plan.py`, private toolchain)
consumes the advice JSON and emits budget / blocks / siblings / layers in ~275
lines. It is a planning aid, not a second instrument: `port_advise` remains the
per-declaration authority.

## 5. Homes, status, and what remains

Homes follow the scout §4/§5 discipline (one home per piece) and the existing
tree. The status column is the plan's status; the dated record is
[../../logs/velu-port.md](../../logs/velu-port.md).

| id | home | status | contents |
|---|---|---|---|
| H0 | `FLTForHuman/WeierstrassCurve/FunctionFieldQuadratic.lean` (extend) | landed | the 4-decl generic-point bridge, the slice's highest fan-in (10 files). 36 written lines, not 972 — the tool's span counted the pin's empty section skeleton |
| H1 | `FLTForHuman/AlgebraicCurve/{P1,Defs}/…` (import) | landed | the **general** place/`ord`/`evalAt` layer, imported not re-derived. It is *not* the Weierstrass dictionary — that is H1w |
| H1w | `WeierstrassCurve/Place/Dictionary.lean` + `AlgebraicCurve/Defs/PlaceCalculus.lean` (new) | landed | the deferred Weierstrass `CoordinateRing` place dictionary ([CARRY-FORWARD.md](../../CARRY-FORWARD.md) entry #1) plus the general `evalAt`/`ord` additions; the prerequisite of every later home |
| H2 | `WeierstrassCurve/Velu/{Defs,Formula,Engine,Discharge,OddOrder}.lean` (new) | landed | the explicit-Vélu engine, ported as three sequential sets (SET-1 A–D + vocabulary, SET-2 E+F, SET-3 G+H). Work orders: [TOPIC-H2-engine.md](TOPIC-H2-engine.md) |
| H3 | `WeierstrassCurve/Velu/MapEquation.lean` (new) | landed | the map-column engine + both `velu_map_equation_of_oddOrderSummingSet{,_of_isAlgClosed}` headlines |
| H4 | `WeierstrassCurve/Velu/RestrictAlong.lean` (new) | landed | the `restrictAlong`-only engine + both `exists_veluFunctionFieldHom_restrictAlong_placeOfPoint_eq{,_of_isAlgClosed}` headlines |
| H5a | `WeierstrassCurve/GenusOnePlaceGate.lean` + `Isogeny/ConditionalCurrency.lean` (new) | landed | the wire test's finding: `GenusOnePlaceGate`/`IsCentred`/`AbelTheorem`/`placeOfPoint` and `pointMapOfPushforward`/`IsogenyEndDatum`/`IsogenyHomDatum` |
| H5b | `WeierstrassCurve/Isogeny/NatCard.lean` (new) | landed | `natCard_…_of_separableAlong` + its three helpers, the H4 headline's route closure |
| H5r | `Velu/{Discharge,Engine,RestrictAlong,Formula,OddOrder}.lean` → `Place/Dictionary.lean` (move) | landed | the dictionary extraction: the A1 `placeOfEquation` ord/centre group, `algebraMap_coordinateRing_ne_zero`/`IsFinitePlace.mem_centre_iff_ord_ne_zero`, `algebraMap_polynomial_eq_mk_C`, `eq_placeOfEquation_of_le_centre` and `ord_polyToFunctionField_*` moved to the dictionary (H5 must not import Vélu), and `exists_some_of_ne_zero` folded to one public copy in `Velu/Formula.lean` |
| **H5** | `WeierstrassCurve/IsogenyEndDatum/{Engine,RestrictAlongAdd,DualEndData,Vocabulary}.lean` + `Isogeny/DualAPI.lean` (new) | **landed** (two vocabulary nodes deferred) | the 82-decl `IsogenyEndDatum` engine + the 35-decl seam, **and the two `IsogenyEndDatum` big theorems of the plan's Phase C** (`exists_dualEndData_dual_mem_and_norm_eq_finrankAlong` and `exists_restrictAlong_placeOfPoint_eq_add`), plus the small layer 0–1 `pointEnd`/`pointHom`/`aeval_j_diag` nodes and the plain `natCard_…` sibling of H5b. Builds on H1w + H5a. **Three sequential sets, all landed** (SET-1 substrate + `DualAPI`; SET-2 the `restrictAlong` column incl. the unbudgeted 3,061-line `addX_addY_specialize_at_place` node; SET-3 the dual column + the vocabulary tail), with `pointHom_apply_eq_sub`/`pointEnd_apply_eq_sub`/`exists_pointEnd_eq_add`/plain `natCard` landed and **`exists_pointHom_comp_eq_of_ker_le_of_isCentred` + `aeval_j_diag_eq_zero_of_finrankAlong_eq` deferred to Phase D** on large unported prerequisites. Detail in [TOPIC-H5-engine.md](TOPIC-H5-engine.md) |
| **H6** | `WeierstrassCurve/Isogeny/BaseChange.lean` (new, or extend `ModularityLifting.lean`) | **remaining** | the tensor/base-change blocks (≈ 1.5 k once-lines), reusing the already-ported WeightOne lattice material (`latticeEquivOfEq`). Independent of H5 |

### What remains, in order

The tool's `layers` section (§6) is the authoritative remaining inventory — the
plan's own name lists have under-counted before, so take the 42-node list from
the tool and read it through the groups below. Homes land before consumers; the
landed run already validated the `H5a → H5b → H4 headlines` order, and H5r has
landed, so the dictionary is importable without Vélu.

1. **H5 — the `IsogenyEndDatum` column.** Engine and seam, then its two big
   theorems (the plan's Phase C remainder) and the small vocabulary nodes
   (`pointEnd_apply_eq_sub`, `pointHom_apply_eq_sub`, `exists_pointEnd_eq_add`,
   `exists_pointHom_comp_eq_of_ker_le_of_isCentred`, `aeval_j_diag_eq_zero…`, and
   the plain `natCard_ker_pointMapOfPushforward_eq_finrankAlong`).
2. **H6 — the base-change column.** Tensor engine and its three consumer nodes
   (`exists_algHom_baseChange…`,
   `isAddCyclic_ker_pointMapOfPushforward_of_baseChange_algHom`,
   `…_of_algEquiv_conj`). Parallel to H5 in principle, sequential by decision.
3. **Phase B — the cheap, self-contained formula nodes** (layer 0, mostly ≤ 200
   lines each; they exercise the landed engine): `veluQuotient2_{Delta_eq,cFour,j}`,
   `Delta_eq_veluGx_sq_mul_velu2QuadDisc`, the `velu2_*_cleared_identity` trio,
   `veluGx_ne_zero_of_two_torsion`, `velu2QuadDisc_ne_zero_of_two_torsion`,
   `veluQuotient2_Delta_ne_zero`, `isElliptic_veluQuotient2_of_isElliptic`,
   `isOddVeluSet_oddOrderSummingSet`,
   `veluQuotient_oddOrderSummingSet_discriminant_ne_zero_of_addOrderOf_eq`,
   `exists_map_eq_veluQuotient_and_map_residue…`,
   `cyclicQuotientJ_{variableChange_eq,baseChange_map_eq_of_isAlgClosed}`,
   `exists_addMonoidHom_coe_eq_veluPointMap2` (1,292 unique).
4. **Phase D — the remaining consumers**, in `layers` order: layer 2
   (`exists_pointEnd_eq_of_mem_isogenyEndSubring`, `exists_intermediateField…`,
   `exists_enum_cyclicKernels…`, `exists_veluFunctionFieldHom_pointMap…`,
   `exists_veluPointHom_oddOrderSummingSet_of_isAlgClosed`), then layers 3–6
   (`exists_sq_lt_four_mul…`, `eval_modularPolynomial…`,
   `isElliptic_veluQuotient2…`, `zmultiples_eq_…_forall_isogenyEndDatum_exists_int`,
   `exists_forall_pointEnd_eq_zsmul_of_transcendental_j`, `exists_enum_twoTorsion…`,
   `veluQuotient2_j`, `bijOn_cyclicQuotientJ…`,
   `zmultiples_eq_…_of_transcendental`, `exists_equiv_addSubgroup…`). The
   `IsogenyEndDatum`-dependent nodes here wait on the H5 home (now landed).
   Two H5 vocabulary nodes join this phase, each bringing its own prerequisite
   set: `exists_pointHom_comp_eq_of_ker_le_of_isCentred` (needs
   `exists_algEquiv_restrictAlong_placeOfPoint_eq_add`, 4,271 pin lines, and
   `algHom_ext_of_forall_restrictAlong_placeOfPoint_eq`, 988) and
   `aeval_j_diag_eq_zero_of_finrankAlong_eq` (needs the `PeriodPair`
   uniformization ladder plus `exists_intermediateField_countable…`,
   `Affine.exists_algHom_functionField_baseChange…`,
   `eval_jLattice_eq_zero_of_isAddCyclic`, `IsAddCyclic.of_squarefree_natCard` and
   `exists_genusOnePlaceGate_isCentred_and_abelTheorem`). They are the only
   unfinished business of H5.
5. **Torsion-API promotion (H5 follow-up) — landed 2026-10-05.** The glue case
   (`finite_torsionBy_of_natCast_ne_zero` / the `private` `finite_torsionBy_aux`)
   stays private; the other two are promoted:
   * `WeierstrassCurve.Affine.Point.exists_zsmul_eq_of_isAlgClosed` — now **char-free
     as the pin states it** (the old public `surjective_zsmul_of_ne_zero` added
     `[CharZero K]` and has been deleted); the already-ported `Elliptic/` EDS
     material served its proof, so nothing was weakened or pulled in.
   * `WeierstrassCurve.nonempty_torsionBy_addEquiv_zmod_prod_of_isAlgClosed` plus
     its generic prerequisite
     `AddCommGroup.nonempty_zmod_prod_addEquiv_torsionBy_of_card_torsionBy_eq_sq`
     — the structural "`E[n]` is `(ZMod n)²`" statement, which **7 other pin `S_`
     nodes import, including both of H6's base-change nodes**, so it is now
     available before H6.
   New modules `FLTForHuman/Algebra/ZModTorsion.lean` (392 lines, `Mathlib`-only)
   and `FLTForHuman/Elliptic/TorsionZMod.lean` (192 lines); `DualEndData.lean`
   imports the promoted statement and its local copy is gone. Checker
   `5555 → 5572 identical, 0 mismatched, 0 missing, 36 own`; whole tree green; no
   `sorry`; axioms clean at `[propext, Classical.choice, Quot.sound]`. The mathlib
   audit (the generic lemma and the divisibility instance are both absent from
   mathlib `v4.34.0`) and the detail are in
   [TOPIC-torsion-promotion.md](TOPIC-torsion-promotion.md).

**Cheap-node first.** Phases B and D are the bulk of the remaining node count but
little of the remaining mass. Land them between the home phases where the layer
graph allows; the only large self-contained items are
`veluQuotient_oddOrderSummingSet_discriminant_prod_veluU_pow` (3,546 unique) and
`exists_intermediateField_countable_map_eq_of_…` (2,035 unique), both unchanged
from §1.1.

### Revisions the port forced

- **The capstone was scheduled twice.** Phase A item 5 ("write the capstone") and
  Phase C items 1–2 are the same four theorems; they landed with the H2/H4 work
  once the wire test pulled H5a/H5b forward. The remaining work is now stated
  once, as H5 and H6.
- **A set's list is the route closure of its deliverable, not the cluster
  intersection of its files.** H3/H4 needed off-list names and H4b a char-free
  norm and separability chain; the rule and its evidence are in
  [TOPIC-H2-engine.md](TOPIC-H2-engine.md) §5. Apply it when scoping H5/H6.
- **A relocation needs its dependency closure, not its name list.** H5r's plan
  row named the A1 group, but `centre_placeOfEquation` forced
  `IsFinitePlace.mem_centre_iff_ord_ne_zero` and
  `algebraMap_coordinateRing_ne_zero` out of `Velu/Engine.lean`, and the
  `ord_polyToFunctionField_*` bridge pulled `algebraMap_polynomial_eq_mk_C` and
  the `RestrictAlong` `Affine` prerequisites with it. The move is recorded in the
  log.

## 6. Reproduce

```bash
cd tools/deps
python3 frontier.py --selfcheck | tail -1          # graph sanity

# the slice: nodes the port does not yet provide. This shrinks as homes land
# (47 nodes pre-port, 42 after the explicit-Vélu column)
python3 - <<'PY' > build/velu_nodes.txt
import frontier, re
fr = frontier.Frontier(); pay = fr.pay; front = fr.frontier('union')
ds = fr.closure(pay.pid('DeligneSerre.exists_galoisRep_of_weightOne_qCoeff_hecke_eigen'))
rx = re.compile(r'[Vv]elu|cyclicQuotient|cyclicKernels|isAddCyclic|IsogenyEnd|IsogenyHom|OddOrderSummingSet|ker_pointMap|veluFunctionFieldHom|veluQuotient|velu_map_equation')
print(','.join(pay.qual(i) for i in ds
               if i not in front and pay.qual(i).startswith('WeierstrassCurve.')
               and rx.search(pay.qual(i).split('.', 1)[1])))
PY
python3 port_advise.py --nodes "$(cat build/velu_nodes.txt)" --json build/velu_advise.json

# the plan (budget, blocks, siblings, layers) — ~275 lines, not ~105 kB
python3 port_plan.py --json build/velu_advise.json --json-out build/velu_plan.json
python3 port_plan.py --selftest
```

`port_plan.py` is a private companion in `tools/deps` (untracked, like the rest of
the toolchain); its artifacts are `tools/deps/build/velu_plan.{txt,json}`. These
hold the **current (post-port) run** of the block above, which is where §1.4 and
§5's remaining list come from; §1's budget is the pre-port measurement of the same
report, recorded in this file. The per-node raw lines and the `X` / `X_of_Y`
overlap ratios are recomputed from the pin at `aa2d8b3`, so re-pin before
re-measuring.
