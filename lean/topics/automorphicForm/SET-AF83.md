# SET-AF83 — four heavy orders off the D–S leaves shelf

**Status: SCAFFOLDED, DISPATCHED (2026-11-14).** The first set of the wave cut from the *leaves* block rather
than the ready shelf, and the largest single dispatch of the column: **13 rows / 4,968 silo** in **seven new
modules** (plus one manager `Def_` module), four orders.

| # | order | rows | silo | module(s) | public decls | engine decls |
|---|---|---|---:|---|---:|---:|
| A | the archimedean type submodules | 3 | 1,102 | `AutomorphicForm/Adelic/Cusp/ArchTypeSubmodule` | 3 | 61 |
| B | the finite-place integrality calculus | 4 | 1,179 | `AutomorphicForm/Adelic/FiniteIntegralConjugation` | 6 | 66 |
| C | the Siegel window at height, and the archimedean–Petersson dictionary | 4 | 1,131 | `AutomorphicForm/Adelic/WindowedSiegel/WindowVanishing`, `AutomorphicForm/Adelic/ArchPeterssonPairing` | 4 | 50 |
| D | the Eisenstein piece | 2 | 1,556 | `EisensteinGeneral/PieceFactorizationDatum`, `EisensteinGeneral/PieceLatticeMajorant` | 2 | 40 |
| | | **13** | **4,968** | 7 modules | **15** | **217** |

(Public and engine counts are **pin-side**, i.e. the number of declarations the pin's `S_` files carry — that is
what sizes the order. The port transcribes 179 of the 217 engine declarations; §5 accounts for the difference
declaration by declaration: dead-in-the-pin helpers, merges, and the ones already public in the port's closure.)

Silo per order is the pin's own figure for the rows (`S_` lines), so each worker transcribes **1,100–1,560
lines of pin** and 40–60 engine declarations: this is the column's heaviest wave by construction, and the
reason the cut is four orders of one subject each rather than ten small ones.

## 0. The read

```bash
cd tools/deps
python3 frontier.py --ds --ready --include-leaves --rank-by silo --top 0 --json > build/shelf_after_af81_82.json
python3 frontier.py --selfcheck
```

| figure | value |
|---|---:|
| `needed [F terminal]` | **576 / 261,442** |
| ready rows, all namespaces | **15 / 3,585** |
| leaves, all namespaces | **140 / 36,013** |
| withheld by the FR-0044 guard | 4 / 831 |

These are exactly SET-AF81/AF82 §5's post-landing figures (the pair landed to the line), so this set opens on
their re-read. `--selfcheck` still FAILS on the fifteen MD-005 `ModularCurve.PhiGen` markers; no row cut here
cites one. SET-AF81 §1.1's ready-block table is one row shorter now (its 890 row is this set's) — the block
below is the whole of it.

**The read is what opens on the leaves.** The ready block is now fifteen rows, four of them behind missing
definition layers and several needing their own topic; SET-AF82's landing note says the cheap ready shelf is
exhausted. The leaves block — 140 rows, 36,013 silo — is where the column's own subject matter (`AutomorphicForm`
37 rows / 7,210, plus its neighbours `LanglandsTunnell` 9 / 1,845, `EisensteinGeneral` 5 / 1,378,
`UnramifiedWhittaker` 3 / 792, `LocalNewvector` 2 / 647) is concentrated.

**Leaves are self-contained**: `leaf_nodes` is "no outgoing citation edges", so a leaf's pin proof imports no
other unported `Theorems/` node. That is why this wave can be cut large and dispatched in parallel without a
chain: no order waits on another order's landing. Every row below has `premises = 0`,
`premises_unported = 0`, `premises_pruned = 0`.

## 1. The rows, and why each one

A leaf's `silo` is its whole `S_` file, and the files here are **one public statement over a private engine** —
the best load shape the column has (the worker transcribes engine, the manager's scaffold is one statement).
The public-surface count per row was the selection criterion, after silo:

| # | row | silo | lev | pub | priv |
|---|---|---:|---:|---:|---:|
| A1 | `AutomorphicForm.CuspidalConstituent.exists_forall_le_archTypeSubmoduleAt_of_isSimple_of_le_iSup` | 646 | 2/4 | 1 | 32 |
| A2 | `AutomorphicForm.CuspidalSpectrum.exists_isArchBiFinite_flat` | 304 | 1/1 | 1 | 17 |
| A3 | `AutomorphicForm.typeSubmodule_inf_typeSubmodule_eq_bot` | 152 | 1/2 | 1 | 10 |
| B1 | `AutomorphicForm.exists_upperTriangular_globalPoints_mul_mul_scalar_mul_finIdeleDiag_inv_mem_finiteIntegralGL2` | 587 | 1/1 | 1 | 21 |
| B2 | `AutomorphicForm.exists_forall_adelicGLHaar_image2_unipotentGL2_mul_mul_le_of_isCompact` | 317 | 1/1 | 1 | 24 |
| B3 | `AutomorphicForm.exists_borel_mul_gl2Weyl_mul_unipotentGL2_eq_of_integral` | 156 | 1/1 | 1 | 6 |
| B4 | `AutomorphicForm.mem_rationalCentreUnipotent_iff_heckeGen_mul_centralScalar_conj_mem` | 119 | 1/1 | 4 | 15 |
| C1 | `AutomorphicForm.WindowedSiegel.exists_forall_apply_one_zero_eq_zero_of_inv_mul_globalPoints_mul_mul_centralScalar_mem` | 386 | 3/4 | 1 | 23 |
| C2 | `AutomorphicForm.exists_norm_a_le_absNorm_rpow_and_norm_b_le_of_smoothCuspRealizationAt_of_peterssonPairing` | 384 | 1/2 | 1 | 11 |
| C3 | `AutomorphicForm.integral_prod_conj_eq_and_eq_conj_mul_of_conj_invariant_of_flat` | 196 | 4/5 | 1 | 4 |
| C4 | `AutomorphicForm.isArchTestFactor_of_contDiff_of_hasCompactSupport_of_tsupport_subset_isUnit_det` | 165 | 1/5 | 1 | 12 |
| D1 | `EisensteinGeneral.Piece.exists_forall_nonempty_factorizationDatum` | 890 | 3/5 | 1 | 25 |
| D2 | `EisensteinGeneral.Piece.exists_summable_majorant_of_lattice_vanishing` | 666 | 1/1 | 1 | 15 |

A1–A3 are one subject: the archimedean `ArchTypeFamily` decomposition of the cuspidal space (the flatness of
arch-bi-finiteness, the irreducible constituent inside a supremum of arch type submodules, and the purely
algebraic disjointness of inequivalent type submodules). B1–B4 are one subject: moving an element of `GL₂` into
a fixed integral subgroup, the Borel, or the rational-centre unipotent set — and B4 is the closure lemma that
SET-AF82's consumer had to prove privately (`RationalCentreHaar`'s header calls it the wave's first promotion
candidate; here it lands at the name the mathematics gives it). C1–C4 are the archimedean side of the smooth
cusp realisation. D1–D2 are the `EisensteinGeneral.Piece` pair.

**D1 was a ready row, not a leaf, and it is the one row whose definition layer the port did not have.** Its
statement is `Nonempty (FactorizationDatum …)`, and `Definitions/Def_EisensteinGeneral_FactorizationDatum` (75
lines, one structure) was ported nowhere. The manager paid it (§2) rather than deferring the row: it is 75 lines
and it unlocks 890.

## 1.1 The shelf, quoted whole — every row cut or deferred

**The ready block: 15 rows / 3,585 silo — 1 cut (D1), 14 deferred.**

| row | silo | lev | cut |
|---|---:|---:|---|
| `EisensteinGeneral.Piece.exists_forall_nonempty_factorizationDatum` | 890 | 3/5 | **D1** |
| `WeierstrassCurve.natCard_torsionOrbit_and_exists_surjective_doubleCoset_of_char_two` | 697 | 1/1 | deferred (char-two torsion orbit; not this column's subject) |
| `WeierstrassCurve.exists_isGalois_goodModel_inertia_faithful_of_two_ne_zero` | 599 | 1/4 | deferred |
| `GaloisRep.exists_isSemisimpleRepresentation_charpoly_map_eq_of_trace_det_frobenius_mem_range` | 495 | 1/1 | deferred (needs its own topic) |
| `MeasureTheory.exists_integral_conj_apply_smul_ne_zero_of_forall_norm_apply_eq_of_continuous` | 200 | 1/1 | deferred (needs its own topic) |
| `ValuationSubring.exists_aeval_div_eq_aeval_div_add_inv_pow_mul_add_aeval_inv` | 138 | 1/1 | deferred (needs its own topic) |
| `NumberField.TateGlobal.exists_isCompact_forall_eq_principal_mul_balanced_mul` | 120 | 1/2 | deferred (needs its own topic) |
| `AutomorphicForm.SmoothCuspRealizationAt.centralChar_eq_of_agreesAwayFromFinite` | 113 | 1/16 | deferred (a candidate for the next AF wave) |
| `NumberField.AdelicHaar.isMulRightInvariant_of_isHaarMeasure_generalLinearGroup_infiniteAdeleRing` | 84 | 4/5 | deferred |
| `ModularForm.exists_gamma0_qExpansion_div_eq_E4_cube_div_discriminant` | 66 | 1/3 | deferred |
| `AlgebraicCurve.exists_placeMap_mapDomain_eq_ord_of_good_constantReduction` | 59 | 2/5 | deferred (the AC column's) |
| `ModularCurve.exists_sum_smul_eq_of_isIntegralQExp_gamma1` | 36 | 1/3 | deferred (MD-001 wire; the MC column's) |
| `ModularCurve.exists_coeffMap_diffQExp_x1FunctionFieldBar_eq_qExpansion` | 34 | 1/1 | deferred |
| `AutomorphicForm.SiegelCovering.centreCutSiegelSet_coversModCentre_rat` | 30 | 1/6 | deferred (still ready after this set; the companion of the 1,781 row it readies — see §4) |
| `ModularCurve.rep_tateModule_jOne_comm` | 24 | 1/6 | deferred |

**The leaves block: 140 rows / 36,013 silo — 12 cut (A1–A3, B1–B4, C1–C4, D2), 128 deferred.** Quoted whole by
namespace, with the largest deferred rows named (the full table is SET-AF81 §1.1's, one edit old — 12 of its
140 rows are this set's):

| namespace | rows | silo | of which cut here |
|---|---:|---:|---|
| `M4aTorus` | 1 | 12,126 | 0 — `completedRayL_fe`, a 12,126-line single headline (762 private declarations, the completed ray-class L-function functional equation). **Not dispatchable as one order**; it needs its own multi-wave topic, and its two `Def_` modules are unported |
| `AutomorphicForm` | 37 | 7,210 | 11 |
| `NumberField` | 30 | 5,243 | 0 — the `AdelicBox`/`Idele` measure families are the next AF-adjacent cut |
| `WeierstrassCurve` | 16 | 2,301 | 0 |
| `LanglandsTunnell` | 9 | 1,845 | 0 — `isBoundedOnSiegelWindows_weightOneLift` (501, 1 public) is the next single-row order |
| `EisensteinGeneral` | 5 | 1,378 | 1 (D2) |
| `TateCurve` | 9 | 1,038 | 0 |
| `MeasureTheory` | 10 | 1,021 | 0 |
| `ValuationSubring` | 7 | 960 | 0 |
| `UnramifiedWhittaker` | 3 | 792 | 0 |
| `IsDedekindDomain` | 5 | 753 | 0 |
| `LocalNewvector` | 2 | 647 | 0 |
| `ModularForm` | 5 | 529 | 0 |
| `HaarQuotient` | 1 | 170 | 0 |

The `NumberField` block (30 rows / 5,243) is the natural successor on this column's own ground: the `AdelicBox`
family (`exists_eq_sum_indicator_image_integralFiniteAdeles` 483, `absNorm_mul_measure_image_integralFiniteAdeles`
229, `exists_ne_zero_forall_addChar_mul_eq_one` 201, `integralFiniteAdeles_subset_closure_range_…` 109,
`exists_denom_of_hasCompactSupport` 70) and the idele-product-measure pair (381 + 370) are two coherent stories
whose `Def_` layers are long since ported. They are deferred only because their public surfaces are 34 / 17 / 15
statements each — a *scaffolding* cost, not a risk, and the natural next set.

## 2. The manager's ground work (done before dispatch)

Each order below arrives with its module already written: header, imports, the pin's public declarations
**verbatim**, `sorry` bodies, and a green checker line. That line is the dispatch criterion — a `MISSING` here
would have meant an unportable statement, found in minutes instead of after a worker's hour.

| module | rows | scaffold checker line | `scaffold_audit` |
|---|---|---:|---|
| `EisensteinGeneral/FactorizationDatum.lean` (new, `Def_`) | — | **1 ok / 0 / 0** | (the wire) |
| `AutomorphicForm/Adelic/Cusp/ArchTypeSubmodule.lean` | A1–A3 | **3 ok / 0 / 0** | complete |
| `AutomorphicForm/Adelic/FiniteIntegralConjugation.lean` | B1–B4 | **6 ok / 0 / 0** | complete (1 by import: `centralScalar_mul_comm`) |
| `AutomorphicForm/Adelic/WindowedSiegel/WindowVanishing.lean` | C1 | **1 ok / 0 / 0** | complete |
| `AutomorphicForm/Adelic/ArchPeterssonPairing.lean` | C2–C4 | **3 ok / 0 / 0** | complete |
| `EisensteinGeneral/PieceFactorizationDatum.lean` | D1 | **1 ok / 0 / 0** | complete |
| `EisensteinGeneral/PieceLatticeMajorant.lean` | D2 | **1 ok / 0 / 0** | complete |

**The `Def_` work: `Def_EisensteinGeneral_FactorizationDatum`, 75 lines, one structure.** Transcribed whole as
`EisensteinGeneral/FactorizationDatum.lean` (its three pin imports replaced by the port modules carrying
`adelicWeyl`/`unipotentGL2`, `NumberField.TateGlobal.localChar` and
`LanglandsTunnell.TateLocal.higherUnitsAt`/`charExt`/`modulus`), own `spec-pin:` wire, silent build,
`1 ok / 0 / 0`. Building it took 5.3 s.

**Two scaffold traps, both now in [../../logs/frictions.md](../../logs/frictions.md) as FR-0224.** (i) The
checker hashes the *statement text*: writing the row as `Nonempty (EisensteinGeneral.Piece.FactorizationDatum …)`
where the pin writes `FactorizationDatum` gives `MISSING (no match)` with no diagnostic. The cure is the pin's
own `open EisensteinGeneral.Piece in`. (ii) The same module's `∏ i : {w : InfinitePlace F // w.IsReal}` needs
`open scoped Classical` — the pin's `open … in` lines are load-bearing, not decoration. Both are statement-level
facts that `lake env lean` alone does not catch, which is why the gate is *both* commands.

## 3. The price and the homes

No `port_advise`/`port_plan` pass was run this time, and the figure it would have produced is already known
from the shape: **every row is 1 public statement over a private engine**, so "substitute" and "port once" have
nothing to bite on, and the net-new figure is the pin's own 4,968 minus whatever the engine turns out to
duplicate. The one substitution found by reading is B4's `centralScalar_mul_comm` — the port holds it publicly
and more generally at the pin's name (`Adelic/Basic.lean`), so it is imported, not restated. The one *promotion*
this set makes is B4 itself (AF82's named candidate), which is a landing, not a cost.

Homes, and the import-direction check (recipe §4). Every row is a leaf, so the proof's premises are not graph
nodes; the constraint is that the home must *import* the declaration layer the statements are written in:

| module | imports the statement's vocabulary from |
|---|---|
| `Cusp/ArchTypeSubmodule` | `Cusp/Constituent`, `Cusp/SpectrumCarrier` (+ `Mathlib.RepresentationTheory.Irreducible`) |
| `Adelic/FiniteIntegralConjugation` | `ProductionPinsGeneral`, `Basic`, `UnipotentQuotient`, `WeylIntertwining`, `WindowedSiegel/CentreCutSet`, `AdelicLevel/HeckeGen`, `AdelicHaar/GeneralLinear`, `AdelicBox` |
| `WindowedSiegel/WindowVanishing` | `WindowedSiegel/CentreCutSet`, `WindowedSiegel/Set`, `ProductionPinsGeneral`, `AdelicHeight`, `AdelicLevel/Projections` |
| `Adelic/ArchPeterssonPairing` | `PeterssonIntegral`, `HeckeEigensystem`, `Cusp/SmoothRealization`, `CarrierPins`, `FactorizableTestFn`, `ArchType`, `IsotypicCuspSpace`, `WindowedSiegel/CentreCutSet`, `TateGlobal/Defs` |
| `EisensteinGeneral/PieceFactorizationDatum` | `EisensteinGeneral/FactorizationDatum`, `Adelic/BigCellExpansion`, `Adelic/AdelicIwasawa`, `EtaFamily`, `InducedSection`, `ArchKFinite`, `SmoothAutomorphicFn`, `WindowedSiegel/RowIsometry`, `NumberField/GlobalAddChar` |
| `EisensteinGeneral/PieceLatticeMajorant` | mathlib only (`CanonicalEmbedding/Basic`, `FractionalIdeal`, `Pow`, `ZLattice`, `Log.Summable`) |

Every one of those is an *existing* module; no legacy home was touched, so no migration is due this set. Each
module is new, so no hub is edited and the four orders touch disjoint files — they can run concurrently, and
only the build lock is shared.

## 4. The forecast, measured with `--port`

Thirteen rows `--port`ed on this read (the recipe's §0 warning: `--also` would put them in the pruned set R and
withhold their own consumers):

| figure | §0 | forecast (AF83) |
|---|---:|---:|
| `needed [F terminal]` | 576 / 261,442 | **563 / 256,474** |
| ready rows | 15 / 3,585 | **18 / 5,347** |
| leaves | 140 / 36,013 | **128 / 31,935** |

**Four rows become ready, and they are the next wave's head:**

| row readied by the set | silo | lev |
|---|---:|---:|
| `AutomorphicForm.SiegelCovering.exists_finset_coversModCentre_iUnion_mul_centreCutSiegelSet` | 1,781 | 1/2 |
| `AutomorphicForm.CuspidalConstituent.exists_inf_invariants_le_iSup_isIrreducible_of_isCuspSubrep` | 320 | 2/4 |
| `AutomorphicForm.CuspidalConstituent.exists_inf_archCutSubmodule_le_iSup_isIrreducible_of_isCuspSubrep` | 317 | 2/4 |
| `AutomorphicForm.CuspidalSpectrum.isClosedCuspSubrep_orthogonal` | 234 | 2/3 |

The readied rows name their own premise, checked against the pin `S_` files' `import Theorems.` lines: the two
`CuspidalConstituent` rows cite **A1**, `isClosedCuspSubrep_orthogonal` cites **A2**, and the 1,781-line
`SiegelCovering` row cites **B1** (`exists_upperTriangular_globalPoints_mul_mul_scalar_mul_finIdeleDiag_inv_mem_finiteIntegralGL2`)
— so three of the four are order A's return and the big one is order B's. The next scoping pass therefore opens
on a ready block of **18 / 5,347** whose head is that 1,781-line Siegel-covering row, and the four new rows plus
`centreCutSiegelSet_coversModCentre_rat` (30, still ready, and the natural companion of the 1,781 row) are about
2,680 silo — one order, and a coherent one (the Siegel covering of the centre).

The 563 figure is the literal accounting of 13 rows and 4,968 lines; it is exact (§5 records it). It is *not* a
claim that the column is near the frontier: the D–S cone's remaining 256 k lines are dominated by the leaves
that are not on any cheap shelf (`M4aTorus` alone is 12,126).

## 5. The landing

All thirteen rows in, no `sorry`, **seven new modules** plus the manager's `Def_` module, four consumers. The
measured shelf re-read is the forecast to the line.

| file | rows | lines | decls | checker | axioms |
|---|---|---:|---:|---|---|
| `EisensteinGeneral/FactorizationDatum.lean` (`Def_`) | — | **96** | 1 | **1 ok / 0 / 0** | — |
| `AutomorphicForm/Adelic/Cusp/ArchTypeSubmodule.lean` | A1–A3 | **1,223** | 59 (3 + 56) | **3 ok / 0 / 0** | clean |
| `AutomorphicForm/Adelic/FiniteIntegralConjugation.lean` | B1–B4 | **1,173** | 49 (6 + 43) | **6 ok / 0 / 0** | clean |
| `AutomorphicForm/Adelic/WindowedSiegel/WindowVanishing.lean` | C1 | **376** | 19 (1 + 18) | **1 ok / 0 / 0** | clean |
| `AutomorphicForm/Adelic/ArchPeterssonPairing.lean` | C2–C4 | **861** | 29 (3 + 26) | **3 ok / 0 / 0** | clean |
| `EisensteinGeneral/PieceFactorizationDatum.lean` | D1 | **902** | 22 (1 + 21) | **1 ok / 0 / 0** | clean |
| `EisensteinGeneral/PieceLatticeMajorant.lean` | D2 | **689** | 16 (1 + 15) | **1 ok / 0 / 0** | clean |
| | **13** | **5,320** | **194 (15 + 179)** | **15 ok / 0 / 0** | |

Consumers, each `0 errors, 0 warnings`: `spec/AutomorphicFormSetAF83AConsumer.lean` (4 zones),
`…B…` (6 zones), `…C…` (3 zones), `spec/EisensteinGeneralSetAF83DConsumer.lean` (2 zones). `scaffold_audit` reads
**complete** on all seven modules; `move_dead` reads `0 declarations, 0 lines` on all seven; `dedup --within`
reads **0 clusters** on five, and **1** on each of `FiniteIntegralConjugation` and `PieceLatticeMajorant` — in
both cases the pin's own private-engine/public-row pair (FR-0221 requires the row at the row's name and the pin
declares the same pair), with the reason recorded in the modules' headers.

**Builds**: each module's own `lake build` under `flock`/`timeout`, serialized: A 7.6 s, B 8.7 s, C1 8.0 s,
C2 12 s, D1 10 s, D2 17 s, `Def_` 5.3 s. All silent; no `sorry`, no `admit`, no `set_option` other than
`autoImplicit false`, no `linter.*`.

### The heartbeat question, settled against the playbook

This order's gate 6 asked for a `set_option maxHeartbeats` floor, and **two workers pushed back on it** —
correctly. Playbook §3.5 is explicit that *no* module carries a `set_option maxHeartbeats` (an in-file cap is a
defect marker, not a budget), while the gate's "4–8× the natural cost" and "fails at n/2" cannot both hold at any
margin above 2×. Four of the seven modules arrived carrying an in-file floor.

The manager's ruling: **the playbook wins, the measurement is kept, the `set_option` is not.** I removed the four
floors (`ArchTypeSubmodule` 80000, `WindowVanishing` 12000, `ArchPeterssonPairing` 60000,
`PieceFactorizationDatum` 100000, `PieceLatticeMajorant` 800000 — five sites across four modules), replaced each
with the probe that produced it as a header comment, and re-elaborated every module at the playbook's own cap
(`lake env lean -DautoImplicit=false -DmaxHeartbeats=200000`): all seven silent, no proof changed. The probes:

| module | silent at | fails at | natural cost |
|---|---:|---:|---|
| `ArchTypeSubmodule` | 20,000 | 19,000 | ≈20 k |
| `FiniteIntegralConjugation` | 200,000 | 50,000 | ≈62 k |
| `WindowVanishing` | 7,000 | 6,000 | ≈7 k |
| `ArchPeterssonPairing` | 45,000 | 40,000 | ≈45 k |
| `PieceFactorizationDatum` | 25,000 | 12,500 | <25 k |
| `PieceLatticeMajorant` | 200,000 | 175,000 | **≈190 k** |

`PieceLatticeMajorant` is the one to watch: it sits within 5 % of the edit loop's cap (`lake build`'s project cap
is 4,000,000, so it is not a build risk — it is an edit-loop one). Recorded as **FR-0225**, and the gate text is
retired in favour of: *probe with `-DmaxHeartbeats=`, record the number in the module header, never install it.*

### What the workers' diagnoses overrode in this brief

Five, all mine, all now in the modules' headers or here:

1. **A's engine count.** The 304-line pin has 19 private declarations, not 17; the wire has **3** public
   declarations, not 5. Port-side accounting: 61 pin privates → 56, the difference being 2 unused (`conjRep_apply`,
   `intertwiningOfEquivariant_apply`), 1 dead in the pin too (`IsSubquotient.of_equiv`) and 2 merged (the 304-pin's
   `transportRep`/`transportRep_apply` are the same mathematics as `conjRep`/`conjRep_apply`, written once).
2. **B dropped two pin privates as dead** (`CritSol.glFin_globalPoints_eq_map:137`, `CritSol.det_diagOne:147`) —
   gate 5 (0 dead) and "transcribe the pin whole" pull apart exactly where the pin has dead helpers. Gate 5 wins;
   the drops are named in the module header.
3. **C imported six pin privates rather than restating them** — 5 of C1's 23 and 1 of the test-factor pin's 12 are
   already public in the port's import closure (`rowMaxNorm_mul_le`, `finLocalHeight_mul_eq`, `finHeight_mul_of_mem`,
   `continuous_finHeight`, `mul_centralScalar_eq`, `continuous_ringEquiv_mixedSpace`). The AF81B precedent.
4. **D1's `attribute` walls.** My first correction (`lean/tmp/af83/WO.md` as dispatched) said to reinstate the
   pin's two `attribute [-instance]`/`[-simp]` walls narrowly; the port's recorded practice is to **drop** them,
   and dropping them cost nothing — the engine compiles against the port's default simp set with zero compensating
   `simp only`, and only deprecation renames were forced. D1 dropped 4 further helpers dead in the pin.
5. **The gate-5 command lines did not parse** as written in this brief (`dedup.py` wants `--within --module <stem>`,
   `move_dead.py` wants `--source/--target/--dry-run`, `scaffold_audit.py` must run from `tools/deps/` with
   `../../lean/…`). Three workers reported the same three corrections independently: the brief, not the tools.

Two scaffold facts also earned their keep: **no worker had to touch a statement** (all fifteen were byte-green at
scaffold and at the end — the point of FR-0224's two traps), and A's report confirms the second one from the other
side: its only tension between "zero warnings" and "no `set_option`" was the flat row's unused `hf` hypothesis,
resolved by naming it once in the proof rather than by renaming the binder (which would have rewritten the checked
statement).

### The set's numbers

| figure | before | **after** (measured) | forecast |
|---|---:|---:|---:|
| `needed [F terminal]` | 576 / 261,442 | **563 / 256,474** | 563 / 256,474 ✓ exact |
| ready rows | 15 / 3,585 | **18 / 5,347** | 18 / 5,347 ✓ exact |
| leaves | 140 / 36,013 | **128 / 31,935** | 128 / 31,935 ✓ exact |
| withheld | 4 / 831 | **4 / 831** | unchanged |

The four rows that became ready are the forecast's four, and their premise citations confirm the attribution:
`SiegelCovering.exists_finset_coversModCentre_iUnion_mul_centreCutSiegelSet` (1,781) cites B1, the two
`CuspidalConstituent` rows (320, 317) cite A1, and `CuspidalSpectrum.isClosedCuspSubrep_orthogonal` (234) cites A2.
The next cut is therefore the Siegel-covering order: that 1,781-line row plus
`centreCutSiegelSet_coversModCentre_rat` (30, still ready and its `_rat` companion) and the three
CuspidalConstituent/Spectrum rows — ≈2,680 silo, one subject, four rows, and every one of them is a leaf or a
ready row whose premises have just landed.
