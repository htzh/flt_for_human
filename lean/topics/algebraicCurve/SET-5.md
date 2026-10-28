# SET 5 — the `AlgebraicCurve` shelf after SET 4: the 24 leaves it left, and the five rows its landing made ready

**Status (2026-10-27): landed and green.** All six orders are in: 29 rows consumed, 21 modules
created or edited, every module `0 mismatch / 0 missing` and silent at the 200k cap, every headline
axiom-clean, the consumer zones at 0 errors, and the shelf re-read (§1.3 and §8 carry the numbers).
This note began as the run brief for the set — cut from the D–S ready shelf following the recipe in
[../deligneSerre/TOPIC-scoping-a-ds-set.md](../deligneSerre/TOPIC-scoping-a-ds-set.md) — and now
records the landing as well: §1.1 the manager's ground prep, §1.2 the per-order record, §1.3 the
set's numbers and the new shelf, §7 the six decided calls, §8 the three measured figures.

| figure (this read) | value |
|---|---:|
| ready candidates, all namespaces | 87 |
| `AlgebraicCurve` rows | **29** — 5 in the ready block, 24 in the leaves block |
| their silo lines | **3,623** (1,132 ready + 2,491 leaves) |
| declarations in those 29 pin files | 225 (19 `private`) → **216** distinct groups |
| net new math lines (`port_plan`) | **2,369** (in-port 812, dedup 59) → **≈2,200** after §7 call 3 |
| `needed [F terminal]` | 1,070 nodes / 414,126 lines |

## 0. The read, and what moved since SET 4

Canonical, as the recipe requires:

```bash
cd tools/deps
python3 frontier.py --ds --ready --include-leaves --rank-by silo --top 0 --json > build/frontier-set5.json
```

4.5 s on the cached graph. Cone 2,103 / 982,173; avoided 140 / 74,620; literal `needed` 1,083 /
417,601; frontier 1,336 / 712,028 (1,020 / 564,572 in the cone).

**The delta against the SET 4 read** (2026-10-27: `needed 1,084 / 418,536`, ready 96,
`AlgebraicCurve` rows 38 = 14 + 24):

- `needed [F terminal]` −14 nodes / −4,410 lines. SET 4 consumed fourteen rows / 4,410 silo, which
  is exactly that difference.
- ready candidates 96 → 87: 14 rows left, 5 entered.
- `AlgebraicCurve` rows 38 → 29: the same 24 leaves, 14 rows consumed, **5 new arrivals**.

**The five new arrivals, and which SET 4 order each owes its readiness to.** Each one's last
unported premise is a declaration SET 4 landed; every one is `premises == 1`:

| new row | silo | owes its readiness to |
|---|---:|---|
| `genus_eq_of_constantFieldExtension_of_isAlgClosed` | 539 | BC8's `Place.ordDifferential_D_eq_zero_of_constantFieldExtension_of_forall_mem` (`Differential/RegularDiffs`), with BC7's `Place.exists_comap_algebraMap_eq_of_constantFieldExtension` |
| `Place.exists_chartedSpace_meromorphicOrderAt_evalAt_eq_ord_complex` | 482 | BC9's `Place.connectedSpace_of_chartedSpace_of_meromorphicOrderAt_eq_ord_complex` (`Place/ComplexDictionary`), over the `localParam` family |
| `regularDiffs_eq_regularDifferentials` | 68 | BC8's `Place.ordDiff_eq_ordDifferential` (`Differential/RegularDiffs`) |
| `Pic0.torsion.move_of_forall_isRational` | 26 | BC6's `Pic0.exists_mk_eq_forall_notMem_support` (`Place/OrderArithmetic`) |
| `SemilinearAut.pushforwardAlong_smul` | 17 | BC6's `SemilinearAut.pushforward_smul` (`WeilExchange/GaloisRamification`) |

**The 24 leaves are the rest of the shelf, and they are the reason this set exists.** They total
**2,491 silo lines** and they were on SET 4's shelf — its own read put them in the `leaves_rank`
block — but SET-4.md's §0 table priced `AlgebraicCurve` at 14 rows / 4,410 and did not name them.
That is the same failure the recipe's §0 records for SET 3 ("`--ready` alone … missed them"), moved
one step later: the read was right, the *reporting* took the ready block only. FR-0040 records it.

The good news: they are unusually cheap. Nineteen of the 24 are one-to-eight-declaration tails whose
engines the port already holds — the five exceptions are the 646-, 340-, 260-, 209- and 151-line
rows — and the set's net-new-to-silo ratio is **2,369 / 3,623 = 65 %**, against 82 % in SET 3 —
because SET 4's landings and the earlier private engines now supply the preludes.

### 0.1 The definition layer — two gates, not fifteen

`port_advise --with-defs` puts 15 pin `Definitions/Def_*.lean` modules in the closure of these 29
rows. Thirteen are already ported — eight of them wired by `spec-pin:`, five present and
registered-unwired — so the SET 3 finding repeats: no definition *work* for the bulk of the set.
Two are **absent from the port**:

| pin module | decls | needed by | port home to create |
|---|---:|---|---|
| `Definitions/Def_AlgebraicCurve_WeilDatum.lean` | 4 (structure `WeilDatum`, `pairing`, `symm`, `addLeft`) | `WeilDatum.symm_pairing` | `Defs/WeilDatum.lean` |
| `Definitions/Def_HahnSeries_RamificationBound.lean` | 7 (`ramScale`, `ramScale_apply`, `ramScale_injective`, `ramScale_le_iff`, `puiseuxRamEmb`, `HasRamBound`, `puiseuxRamSubfield`) | `Place.exists_ord_mul_eq_order_of_hasRamBound` | `Defs/HahnSeriesRamificationBound.lean` |

Both are small (81 and 42 pin lines) and each is consumed by exactly one row. They are the
manager's ground prep (§4): the `WeilDatum` headline's proof is `rfl`-level once the structure
exists, and the ramification-bound row is unprovable without `HasRamBound` in scope.

### 0.2 What the instruments said, and the two places they are blind

The whole-set `port_advise` reads **422 substitutions (≈3,551 lines) already in the port**, 407
importable and 15 held `private`; **14 names proved twice or more inside the set (≈142 removable
lines)**; and no same-name/different-statement pair among the 29 *headlines*. The six such pairs the
tool reports (`pointwise_smul_top`, `smul_toValuationSubring`, `deg_smul`, `valuationSubring`,
`ord_smul`, `coe_degZeroSMulHom`) are all helper declarations inside pin prelude files — five are
copies between the `Def_DivisorClassGroup` and `Def_BaseChangeGalois` layers, which the port already
holds once in `Defs/SemilinearAut.lean`, and the sixth is RB1's local `valuationSubring` matching a
`NumberField` definition of the same short name. So this set needs **no namespace split**, only
imports.

The largest single reusable block is `Defs/SemilinearAut.lean`'s seven-lemma `smul` algebra
(`degree_smul` 26, `deg_smul` 13, `pointwise_smul_top` 7, `smul_def` 4, `smul_single` 4,
`smul_toValuationSubring` 3, plus `ord_smul`). Two rows spend it without writing any of it: PIC1's
14-line `ofAlgAut_smul_place` (its pin `Def_AlgebraicCurve_BaseChangeGalois` import carries all
seven) and RB1's prelude (its `Def_AlgebraicCurve_DivisorClassGroup` import carries the same seven
again).

Two name-anchored blind spots, both found by hand, both priced wrongly by the tool:

- **Four headline statements already exist in the port under another name.** The three
  `Divisor.evalFun_*` laws are in `Defs/PlaceEvaluationAlgebra.lean` as
  `evalFun_add_of_forall_ne_zero` / `evalFun_zsmul_divisor` / `evalFun_ne_zero_of_forall_ne_zero`
  — statement-identical, different name (they are the pin's *definitions* layer; the rows are the
  pin's *wrapper* names). `hasCanonicalLocalResidueK` is `inferInstance` against
  `LocalResidue/Instance.lean`'s unconditional `instHasCanonicalLocalResidueK`. All four are
  one-line public declarations at the pin's names, which is what the surface rule asks for
  (SET 4's BC9b precedent), not re-proofs.
- **The ramification-bound row's engine is `Place.exists_of_orderMap`.** The port's
  `Place/ValueDictionary.lean` already realises a `WithTop ℤ`-valued order map as `e` times a
  place's order; the pin's `φ.order` takes values in `ℚ` with a common denominator `d` (its
  `ramScale`/`HasRamBound`), so `exists_of_orderMap` is the `d = 1` case. `port_advise` calls all
  318 lines of that row new. They are not — the reviewer has taken the generalising route (§4.4,
  §7 call 3).

## 1. The cut — six orders, one story each

| order | work order | story | rows | silo | net new | homes | gate |
|---|---|---|---:|---:|---:|---|---|
| **RP2** | [WORKORDER-RP2](WORKORDER-RP2-regular-prolongation-residue.md) | the residue field of a regular prolongation: transcendence, monic bounds, the integers | 4 | 1,104 | 665 | insert `RegularProlongationFinrank.lean` | — |
| **PC1** | [WORKORDER-PC1](WORKORDER-PC1-charted-space.md) | the charted space on the places over `ℂ` | 2 | 505 | 337 | **new** `Place/ChartedSpace.lean`; insert `Defs/PlaceEvaluation.lean` | — |
| **RB1** | [WORKORDER-RB1](WORKORDER-RB1-ramification-bound.md) | a place from a ramified Hahn-series embedding, derived from the order-map engine | 1 | 340 | 318 → **≈150** | **new** `Defs/HahnSeriesRamificationBound.lean`; insert `Place/ValueDictionary.lean` | def + 1 `own:` |
| **CFE2** | [WORKORDER-CFE2](WORKORDER-CFE2-genus-separability.md) | genus, separability and the different under a constant field extension | 3 | 816 | 382 | 3 insertions (`Genus/ConstantFieldExtension` +2 imports, `Place/FromValuationSubring`, `Differential/RegularDiffs`) | 11 promotions |
| **PIC1** | [WORKORDER-PIC1](WORKORDER-PIC1-torsion-and-semilinear.md) | the torsion of `Pic0`, the Weil datum, and the semilinear action on the correspondence | 8 | 398 | 299 | **new** `Defs/WeilDatum.lean`; 4 insertions | def + 1 wire |
| **TL1** | [WORKORDER-TL1](WORKORDER-TL1-tails.md) | the tails: five fragments, each the last public declaration of an engine already in the port | 11 | 460 | 368 | 5 insertions (3 unwired) + **new** `FunctionField.lean` | 3 wires |

Totals: 29 rows, 3,623 silo, **≈2,200** net new, 225 declarations (216 groups), 3 new mathematics
modules + 2 definition modules, 4 wires, 11 promotions, 2 generalisations (§4). `port_plan` read
2,369 for the same rows; call 3 re-scopes RB1's 318 to a ≈150 budget, which is the whole of the
difference.

The six orders touch **disjoint files**, so all six are safe concurrently; only the build lock is
shared. Two reassignments made the disjointness hold: `Place.pairwiseDisjoint_fiber` moved from
PC1 to TL1 (it is a `fiber`/support lemma and belongs with the other two), and the
`evalAt`-algebra law stayed in PC1's `Defs/PlaceEvaluation.lean` while the `evalFun` laws went to
TL1's `Defs/PlaceEvaluationAlgebra.lean`.

### 1.1 The ground prep, as landed (manager)

| item | module | state |
|---|---|---|
| definition gate 1 | **new** `Defs/WeilDatum.lean` (pin `Def_AlgebraicCurve_WeilDatum`, 4 decls) | **4 ok** / 0 / 0, builds |
| definition gate 2 | **new** `Defs/HahnSeriesRamificationBound.lean` (pin `Def_HahnSeries_RamificationBound`, 7 decls) | **7 ok** / 0 / 0, builds |
| wire | `Defs/Correspondence.lean` | **42 ok**, plus three `pin:` rows for `finrankAlong_comp` / `_id` / `_eq_relfinrank_fieldRange`, whose pin copies live in the standalone node wrappers rather than in the `Def_` file |
| wire | `Defs/AdelicIndex.lean` | **68 ok** |
| wire | `Differential/PushPull.lean` | **8 ok** |
| wire | `Defs/PlaceEvaluationAlgebra.lean` | **14 ok** (the `Def_` layer plus the six `Divisor.evalFun_*` wrappers) |
| promotions | `Differential/ConstantFieldExtension.lean`, `Differential/RegularDiffs.lean` | **13 ok** and **16 ok**: the eleven declarations are public, and every one matched a pin copy already on its module's wire, so no marker row was needed — the promotion was a `private` deletion plus the proof-order fix that `D_ne_zero_of_transcendental` keeps K as a file-level `variable` (the checker extracts the statement without the prefix; spelling K inline reports MISMATCH — the drift-table row again) |
| RB1's `own:` | `spec/decl_markers.tsv` | `AlgebraicCurve.Place.exists_of_orderMap_rat` |

Two findings from the definition gate, worth carrying: mathlib's `Field R⟦Γ⟧` instance lives in
`HahnSeries/Summable.lean`, not beside `Multiplication.lean` (a `Subfield` of Hahn series does not
elaborate without it), and the pin's `HasRamBound`/`ramScale` block is otherwise `import`-free.

### 1.2 Landing record

| order | modules | added | checker before → after | build | axioms |
|---|---|---:|---|---|---|
| RP2 | `RegularProlongationFinrank.lean` (+664, purely additive) | 20 public (21, less the `ord` lemma the review moved to `Defs/PushPull`) | 29 → **49 ok** / 0 / 0 | 10 s, 0 warnings | four headlines clean |
| PC1 | **new** `Place/ChartedSpace.lean` (447) and `Defs/PlaceEvaluation.lean` (+1) | 34 (33 + 1) | 0 → **33 ok**; 11 → **24 ok** | 0 warnings each | capstone clean |
| RB1 | `Place/ValueDictionary.lean` (+294/−2) | 2 public (engine + headline) | 69 → **70 ok** / 0 / 0 / **1 own** | 0 warnings | engine and headline clean |
| CFE2 | `Place/FromValuationSubring.lean` (generalised), `Genus/ConstantFieldExtension.lean` (+241), `Differential/RegularDiffs.lean` (+74/−?) | 14 public in the genus module (the pin's 12-declaration prelude + headline), the engine `S12R.regularDiffs_eq`, one separable headline | 4 → **17 ok**; 16 → **18 ok**; **3 ok** in the generalised dictionary | 0 warnings each | five headlines clean |
| PIC1 | **new** `Pic0/Torsion.lean` and 5 insertions (`WeilDatum` +1, `OrderArithmetic` +1, `Correspondence` +10, `GaloisRamification` +1, `SemilinearAut` +1) | 17 public (10 of them the pin's prelude block in `Correspondence`) | 4 → **5 ok**; 8 → **10 ok**; 0 → **3 ok**; 42 → **52 ok**; 9 → **10 ok**; 51 → **53 ok** | 0 warnings each | eight headlines clean |
| TL1 | **new** `FunctionField.lean` (219 lines) and five insertions (+274, append-only) | 9 in the new module (2 headlines + 7 pin helpers) + 15 insertions | 9 ok; `PlaceEvaluationAlgebra` 17, `PushPull` 66 → **67** (the review's move added one), `AdelicIndex` 69, `Differential/PushPull` 15, `LocalResidue/Instance` 121 — all / 0 / 0 | 0 warnings each | eleven headlines clean |

**One PIC1 deviation is a homing confirmation, not a workaround.** The pin's `mk_eq_zero_iff_aux`
has a port twin (`Pic0.mk_eq_zero_iff`) but it lives in `WeilExchange/Transport.lean`, which imports
`GaloisRamification ⊃ Correspondence ⊃ PushPull` — importing it would make the torsion-finiteness
module depend on the WeilExchange layer, i.e. invert the homing the order asks for. The worker
inlined the three-step quotient rewrite at its single use and flagged it; the review keeps the
inlining, because the import would have been a cycle in the other direction (the SET 4 rule: the
home is above the proof's premises, not below them).

**The consumer zone** is [../../spec/AlgebraicCurveSet5Consumer.lean](../../spec/AlgebraicCurveSet5Consumer.lean)
— three zones, 0 errors, each a composition of two modules that were written a wave apart:
the charted-space capstone's order clause *is* `ConnectedOfCharted.OrderHypothesis` (PC1 + SET 4's
`ComplexDictionary`), evaluated at the chart's centre by `reading_center`; RB1's rational order map
yields membership in the realised place's valuation ring (`Place/ValueDictionary` + `Defs/PushPull`);
and RP2's `eq_integers` transfers the prolongation's integrality along the valuation-subring
equality. The first zone needed the capstone's `∃ topology, ∃ charted` to be consumed *inside* an
existential (a `Prop` target cannot mention the instances it produces), which is the honest shape of
the capstone's interface and is recorded in the file's header.

**Two RP2 deviations held for review.** (i) The pin states `exists_unit_mul_mem_span` twice, with
different statements (the finrank node's, already ported, and the `eq_integers` node's, which adds
the membership conjunct); the second is declared as `exists_unit_mul_mem_span_adjoin` with the pin's
statement verbatim and checks `ok` by content hash — the port's precedent for a same-last-name pair
with two statements is a split, so the suffix stands until a review says otherwise. (ii)
`Place.ord_neg_of_not_mem` is the case the review reversed, and the reversal is the rule: homing is
decided by substance, not by cascade cost. The lemma is the negative side of the `ord`/membership
dictionary whose positive sides — `Place.ord_nonneg_of_mem` and `Place.mem_of_ord_nonneg` — carry
**108 and 107** pin consumers and are already public in `Defs/PushPull.lean`; the pin itself states
`ord_neg_of_not_mem` in **34** `S_` files. It has mathematics and it will have users, so it was moved
to `Defs/PushPull.lean` beside its siblings and wired by a `pin:` row to the pin copy that spells its
binders (`S_AlgebraicCurve_Place_analyticAt_evalAt_extChartAt_symm_of_mem.lean:51`); the checker named
that file when the declaration arrived unwired. The move cost the hub cascade — ~10 upstream modules
re-elaborated, `Tate/Agreement.lean` at 100 s — and the review pays it: the alternative is every
future wave re-stating a 5-line lemma the pin writes 34 times. The module now checks **67 ok** and
RP2's **49** (the declaration is diffed once, where it lives). The drift-table lesson recurred on the
way: the pin's copies write `v` as a section variable, so the port's first spelling with the full
`{K F : Type*} …` prefix reported MISMATCH, and the section-variable form matched.

### 1.3 The set's numbers, and what the landing moved

**Consumed.** 29 rows, 3,623 silo; the tree carries **+1,880 lines over 16 edited modules and
1,059 lines in 5 new ones** (2,941 total, of which the declarations are ≈2,400 after the headers,
docstrings and wires). 21 modules carry the set's edits; every one builds, checks `0 mismatch /
0 missing`, and is silent at `-DmaxHeartbeats=200000`; every headline is
`[propext, Classical.choice, Quot.sound]`.

**The new shelf** (re-read with the canonical command after the landing):

| figure | before | after |
|---|---:|---:|
| `needed [F terminal]` | 1,070 / 414,126 | **1,040 / 410,470** |
| ready candidates | 87 | **96** |
| leaves block | 320 | **296** |
| `AlgebraicCurve` rows | 29 (3,623 silo) | **14 (4,000 silo)** |
| `AlgebraicCurve` demand | 105 / 29,700 | **75 / 26,044** |

**Fourteen rows became ready because of the set**, and they are the successors of the six stories
— which is the recipe's third number and the check that the set was cut along real seams:

| new ready row | silo | unblocked by |
|---|---:|---|
| `RationalFunctionField.weilReciprocity` | 1,273 | TL1's `FunctionField` pair (the family's bottom) |
| `Differential.sum_ord_smul_pullbackAlong_eq_zero` | 629 | PIC1's semilinear/along insertions |
| `Place.exists_comap_algebraMap_eq_of_constantFieldExtension_of_isAlgClosed` | 620 | CFE2's separable generalisation |
| `WeilDatum.pairing_eq_of_isPrincipal_sub` | 439 | the new `Defs/WeilDatum.lean` |
| `Differential.map_correspondence_regularDifferentials_of_constantFieldExtension` | 309 | CFE2's `regularDiffs_eq_regularDifferentials` |
| `Place.exists_ord_mul_eq_order_of_algHom_laurentSeries` | 146 | RB1's realised place |
| `Place.exists_natCast_dvd_ord_sub_single_sub_single_complex` | 126 | TL1's `evalFun` laws |
| `Pic0.finite_torsion_of_isAlgClosed_of_charZero` | 95 | PIC1's torsion finiteness |
| `lSpace_nsmul_succ_poleDivisor_le_sup_map_mulLeft_of_ell_eq` | 95 | TL1's `LSpace` row |
| `WeilDatum.addLeft_pairing` | 80 | the new `Defs/WeilDatum.lean` |
| `WeilDatum.pairing_ne_zero` | 65 | idem |
| `Divisor.evalFun_algebraMap_pushforward` | 59 | TL1's `evalFun` laws |
| `constantsAreBase_of_isAlgClosed_of_transcendental` | 48 | CFE2's separable generalisation |
| `SemilinearAut.correspondence_smul` | 16 | PIC1's `Correspondence` insertion |

The largest is the one the brief's call 5 was argued over: cutting the `FunctionField` pair put
`weilReciprocity` — 1,273 silo lines, the head of the unported Weil-reciprocity family — on the
ready shelf, together with four of its `WeilDatum` neighbours.

**Dedup, read at review.** Three clusters, all kept with the reason: `Genus/ConstantFieldExtension`
reports its two pair-of-engine-and-wrapper clusters (`isPrincipal_of_constantFieldExtension` 38 L
and `exists_torsion_descent_of_constantFieldExtension` 33 L over the private engines SET 4 left),
which is the pin's own shape; `Place/ChartedSpace` reports `isManifold` / `orderClause` over the
shared 11-line `letI` statement preamble — two different statements, a false positive of the shape
tier, the same class as SET 4's `conductorIdeal_ne_top`/`_ne_bot` note. `Pic0/Torsion`,
`FunctionField`, `Defs/WeilDatum` and `Place/ValueDictionary` report nothing.

## 2. The rows

`silo` is the pin `S_` file's line count (the rank key); `prem` the pin's `import Theorems.Thm_*`
premise count; `lev` cone / project consumers. All 29 carry `premises_unported = 0`.

| order | node (`AlgebraicCurve.` dropped) | silo | prem | lev | block |
|---|---|---:|---:|---:|---|
| RP2 | `RegularProlongation.eq_integers_of_forall_mem_adjoin_iff` | 646 | 0 | 3 / 31 | leaf |
| RP2 | `RegularProlongation.mul_min_ord_residue_le_of_monic` | 260 | 0 | 1 / 6 | leaf |
| RP2 | `RegularProlongation.transcendental_of_residue_transcendental` | 110 | 0 | 2 / 4 | leaf |
| RP2 | `RegularProlongation.isIntegral_adjoin_residue_of_exists_monic_bivariate_eval_eq_zero` | 88 | 0 | 3 / 4 | leaf |
| PC1 | `Place.exists_chartedSpace_meromorphicOrderAt_evalAt_eq_ord_complex` | 482 | 6 | 1 / 6 | ready |
| PC1 | `Place.evalAt_algebraMap_eq_evalAt_restrict` | 23 | 0 | 1 / 25 | leaf |
| RB1 | `Place.exists_ord_mul_eq_order_of_hasRamBound` | 340 | 0 | 1 / 9 | leaf |
| CFE2 | `genus_eq_of_constantFieldExtension_of_isAlgClosed` | 539 | 6 | 2 / 3 | ready |
| CFE2 | `Place.exists_toValuationSubring_eq_comap_ringHom_of_isSeparable` | 209 | 0 | 5 / 14 | leaf |
| CFE2 | `regularDiffs_eq_regularDifferentials` | 68 | 2 | 2 / 6 | ready |
| PIC1 | `SemilinearAut.pic0_correspondence_swap_smul` | 151 | 0 | 1 / 4 | leaf |
| PIC1 | `Pic0.exists_ord_eq_mul_and_forall_pow_ne_of_ne_zero` | 79 | 0 | 1 / 2 | leaf |
| PIC1 | `Pic0.finite_torsion_of_forall_primePow` | 67 | 0 | 1 / 8 | leaf |
| PIC1 | `Pic0.torsion.exists_forall_ord_eq_mul` | 35 | 0 | 2 / 3 | leaf |
| PIC1 | `Pic0.torsion.move_of_forall_isRational` | 26 | 1 | 1 / 4 | ready |
| PIC1 | `SemilinearAut.pushforwardAlong_smul` | 17 | 1 | 1 / 4 | ready |
| PIC1 | `SemilinearAut.ofAlgAut_smul_place` | 14 | 0 | 1 / 5 | leaf |
| PIC1 | `WeilDatum.symm_pairing` | 9 | 0 | 2 / 2 | leaf |
| TL1 | `FunctionField.finite_of_ratFuncAlgHom` | 162 | 0 | 1 / 2 | leaf |
| TL1 | `Differential.pullbackAlong_traceAlong_eq_sum_lifts` | 127 | 0 | 1 / 1 | leaf |
| TL1 | `mul_mem_lSpace_nsmul_succ_and_reflects_of_poleDivisor` | 65 | 0 | 1 / 3 | leaf |
| TL1 | `FunctionField.exists_ratFuncAlgHom_apply_X_eq` | 25 | 0 | 1 / 6 | leaf |
| TL1 | `Divisor.support_pushforward_subset` | 14 | 0 | 1 / 1 | leaf |
| TL1 | `Divisor.evalFun_add` | 13 | 0 | 3 / 11 | leaf |
| TL1 | `Divisor.evalFun_zsmul` | 12 | 0 | 2 / 8 | leaf |
| TL1 | `hasCanonicalLocalResidueK` | 12 | 0 | 1 / 3 | leaf |
| TL1 | `Divisor.support_pullback_subset` | 11 | 0 | 1 / 2 | leaf |
| TL1 | `Place.pairwiseDisjoint_fiber` | 10 | 0 | 1 / 2 | leaf |
| TL1 | `Divisor.evalFun_ne_zero` | 9 | 0 | 4 / 10 | leaf |

Demand is again inverted relative to size: the 646-line `eq_integers` carries 31 project consumers
and the 23-line `evalAt_algebraMap_eq_evalAt_restrict` carries 25, while the 340-line
ramification-bound row carries 9 and four rows carry 1–2. The tail is also where the leverage is:
`Support`/`evalFun`/`fiber` rows that cost 9–14 lines each have 2–11 project consumers.

## 3. Homes — checked against the import direction, per node

Method as in the recipe §4: pin `S_` premise nodes → statement-identical port module
(`twin_scan`'s `PortIndex` over a rebuilt index) → the modules above all of them in the port's
import closure; then each home confirmed by reading the pin proof's first lines. The machine table
is a first cut (FR-0038). In this pass it was wrong once: its nearest home for the charted-space
capstone was `Place/ComplexDictionary.lean`, which the import direction refuses (it is above one of
the six premises, not six). Every other home below was confirmed by reading the pin proof.

| order | node | premises → port modules | home | why |
|---|---|---|---|---|
| RP2 | all four | none (leaves; the pin files import `Def_AlgebraicCurve_RegularProlongation` only) | **insert** `RegularProlongationFinrank.lean` | it already declares the engine these four consume: `constHom` (80), `residue_constHom` (91), `residue_eq_zero_iff` (96), `mem_of_sum_smul_mem`, `linearIndependent_{co,adjoin,residue_frame}`, `exists_{normalizer,normalize_aeval,repr_adjoinField}` — 18 of the four proofs' substitution targets; it is wired (2), 904 lines, 1 importer |
| PC1 | `chartedSpace` | `LocalParamDatum`, `BranchUniqueness`, `FiniteCover`, `ComplexDictionary`, `OrdCalculus`, `Approximation` | **new** `Place/ChartedSpace.lean` | no existing module is above all six: `ComplexDictionary` (the nearest) misses four of them, and every LP-family module misses the other four. This is the assembly the column's §2 already named as the capstone's remainder |
| PC1 | `evalAt_algebraMap_eq_evalAt_restrict` | none | **insert** `Defs/PlaceEvaluation.lean` | it is an `evalAt` law at a `restrict`, and that module is the eval-at algebra; it is above `Defs/PushPull` where `restrict`/`restrictInclusion` live |
| RB1 | `hasRamBound` | none (the new `Def_` module only) | **insert** `Place/ValueDictionary.lean` | the module of `exists_of_orderMap` (1013), the general order-map→place realisation this row refines to the ramified case; wired (4), 1,178 lines, 1 importer |
| CFE2 | `genus_eq…` | `Differential/Coefficient`, `Canonical/DCoordGenerates`, `IsCurveOver/EssFiniteType`, `Place/ConstantFieldExtension`, `Place/FromValuationSubring`, `Differential/RegularDiffs` | **insert** `Genus/ConstantFieldExtension.lean` | it is the module of the CFE invariants (8 wires, 1,635 lines, 1 importer) and it is already above four of the six. It needs **two added imports** (`Differential.Coefficient`, `Differential.RegularDiffs`); neither is above `Genus/ConstantFieldExtension`, so both are safe |
| CFE2 | `…_of_isSeparable` | none (its 11 helpers are the pin's own prelude, `private`, 169 lines) | **insert** `Place/FromValuationSubring.lean` | the same subject — the valuation-subring↔place dictionary — and the pin's own separable file is the same ten-helper block the port carries there under `[CharZero K]`. See §4.3: this is a *generalisation*, not a second copy |
| CFE2 | `regularDiffs_eq…` | `Differential/RegularDiffs`, `Canonical/DCoordGenerates` | **insert** `Differential/RegularDiffs.lean` | above both premises; the row's engine is `regularDiffs_eq` (the pin's own local 25-line theorem), and `regularDiffs_eq_span` + `mem_regularDiffs_of_isRegularDiff` + `mem_regularDifferentials_iff` are already public in `Differential/Coefficient` / the Def layer |
| PIC1 | `pic0_correspondence_swap_smul` | none | **insert** `Defs/Correspondence.lean` (+wire) | it is `algebraAlong`/`Divisor.pullbackAlong`/`Pic0.correspondence`/`IntertwinesAlong` algebra — this module's own subject; unwired today, so the order adds the wire |
| PIC1 | `Pic0.exists_ord_eq_mul…`, `finite_torsion…`, `torsion.exists_forall_ord_eq_mul` | none | **new** `Pic0/Torsion.lean` | the torsion of `Pic0` has no module of its own: `Pic0`/`Pic0.torsion`/`Pic0.mk` sit in `Defs/Divisor.lean`, a hub with 15 importers. Three rows about torsion's finiteness and its divisor representatives are a subject; a cascade-free module above `Defs/Divisor` hosts all three |
| PIC1 | `torsion.move_of_forall_isRational` | `Place/OrderArithmetic` | **insert** `Place/OrderArithmetic.lean` | it *is* the moving lemma's rationality clause; its premise `Pic0.exists_mk_eq_forall_notMem_support` was homed there by SET 4 (FR-0038), so anything above must import it — this module is where the pair belongs |
| PIC1 | `pushforwardAlong_smul` | `WeilExchange/GaloisRamification` | **insert** `WeilExchange/GaloisRamification.lean` | it is the along-version of the `pushforward_smul` SET 4 landed there (11 wires) |
| PIC1 | `ofAlgAut_smul_place` | none | **insert** `Defs/SemilinearAut.lean` | `SemilinearAut.ofAlgAut` and `smul_toValuationSubring` (198) are that module's own |
| PIC1 | `WeilDatum.symm_pairing` | none | **new** `Defs/WeilDatum.lean` (with the Def) | 3 lines (`rfl` after `inv_div`) on a structure the port lacks; the def module and its one law ship together, as `RegularProlongation.lean` does |
| TL1 | `FunctionField.*` (2) | none (both pin files import `Mathlib` only) | **new** `AlgebraicCurve/FunctionField.lean`, `namespace AlgebraicCurve.FunctionField` | `RatFunc K →ₐ[K] F` existence and finiteness; the port has no home for the algHom layer (`Defs/RatFuncPlaces.lean` is the ℙ¹ *place* vocabulary; `PrincipalDivisors/RatFuncDegree.lean` the place/degree theory). Their consumers are the unported Weil-reciprocity family — see §7, call 5 |
| TL1 | `Differential.pullbackAlong_traceAlong_eq_sum_lifts` | none | **insert** `Differential/PushPull.lean` (+wire) | `pullbackAlong`/`traceAlong` are defined there and it imports `Defs/Correspondence` (`FiniteAlong`/`SeparableAlong`); unwired, so the order adds the wire |
| TL1 | `mul_mem_lSpace…` | none | **insert** `Defs/AdelicIndex.lean` (+wire) | `LSpace` (abbrev) and `mem_lSpace_iff_ord` are there; unwired, so the order adds the wire |
| TL1 | `support_pushforward_subset`, `support_pullback_subset`, `pairwiseDisjoint_fiber` | none | **insert** `Defs/PushPull.lean` | `pushforward`/`pullback`/`fiber` are defined there (546); a hub (29 importers), so the insertion's price is a re-elaboration, not a cycle |
| TL1 | `evalFun_add`, `evalFun_zsmul`, `evalFun_ne_zero` | none | **insert** `Defs/PlaceEvaluationAlgebra.lean` (+wire) | the three statements already exist there under the pin's *definition-layer* names (§0.2); the module's header already carries one wrapper statement for exactly this reason. Unwired, so the order adds the six `Theorems/Thm_AlgebraicCurve_Divisor_evalFun_*` wrappers |
| TL1 | `hasCanonicalLocalResidueK` | none | **insert** `LocalResidue/Instance.lean` | the unconditional `instHasCanonicalLocalResidueK` (453) is the whole proof |

**None of the 29 rows cites another row of this set.** The five non-leaf rows cite only SET 4's
declarations and earlier landings; the rest are leaves. So the orders are independent as far as
the mathematics goes, and the only scheduling constraint is the shared-file one (§1). One derived
edge appears *inside* CFE2 once the generalisation of §4.3 is made: the genus node's premise
`Place.exists_toValuationSubring_eq_comap_ringHom` is the `[CharZero K]` headline, which then
derives from the new separable one — same module, so it is a proof-order item for one worker, not
a scheduling one.

## 4. Ground prep — the manager's share, before any order dispatches

### 4.1 Two definition modules (new)

`Defs/WeilDatum.lean` and `Defs/HahnSeriesRamificationBound.lean`, each wired by its pin `Def_`
file, each transcribed verbatim (both are `import Mathlib`-only in the pin, both have zero drift
surface). The `WeilDatum` structure needs `Divisor.evalFun` from `Defs/PlaceEvaluation.lean`; the
HahnSeries block needs nothing.

### 4.2 Four wires

`Defs/Correspondence.lean`, `Defs/PlaceEvaluationAlgebra.lean`,
`Defs/AdelicIndex.lean`, `Differential/PushPull.lean` are registered-unwired. Each gets a
`spec-pin:` block over the pin sources it transcribes — one line for the `Def_` file, plus the
`Theorems/`/`S_` pair of any node the order adds there (the `PlaceEvaluationAlgebra` case is six
wrappers). A module is not an insertion target until its wire is green (the SET 4 rule).

### 4.3 Eleven promotions, and two generalisations

**Promotions (CFE2).** The pin's `genus_eq…` file states 36 declarations, none private; the port
holds eleven of them `private`, split across two modules. Promote them public at the pin's names,
each on its own wire:

| module | declarations | lines |
|---|---|---:|
| `Differential/ConstantFieldExtension.lean` | `finiteDimensional_adjoin_of_transcendental` 49, `exists_basis_D` 29, `ratFuncBasis_zero` 10, `towerBasis_zero` 8, `ratFuncBasis` 6, `towerBasis` 6, `polyBasis` 3, `polyBasis_zero` 3 | 114 |
| `Differential/RegularDiffs.lean` | `coeffLin` 10, `coeffDer` 5, `D_ne_zero_of_transcendental` 16 | 31 |

This is the CFE2 order's unblocking act as much as a surface correction: without the promotion the
genus node cannot import its own engine and the worker re-proves 145 lines.

**Generalisations (2).** Both are the "same name, the port's hypothesis is a special case" case
the recipe's §2 treats as a split/generalisation, not a rename:

1. `Place/FromValuationSubring.lean` carries a nine-theorem private block and two public headlines
   under `[CharZero K]`; the pin's `_of_isSeparable` file is the *same block* under
   `[Algebra.IsSeparable (adjoin K {x}) F]`, a strictly weaker hypothesis (in char 0 separability is
   automatic, so the separable statement covers the port's case). CFE2 should generalise the block
   in place (all nine helpers are `private`, so nothing public breaks) and state the pin's two
   public headlines at its names; the existing `[CharZero K]` headlines stay, unchanged in
   statement, as corollaries. That turns the 209-line row (the pin's 169 new private lines) into two
   public statements over an edited private block.
2. **RB1's engine, decided** (call 3): generalise the realisation to the pin's ramified case. It is
   not a second generalisation but the same development's general statement — see §4.4.

### 4.4 RB1's route, as decided — generalise the engine, paid now

The reviewer's call is route (b), and not as deferred debt. It changes the order's content, so the
plan in full:

- **What the node states.** `φ : F →ₐ[K] HahnSeries ℚ L` with `HasRamBound d`, and the conclusion is
  a place `w` and a rational `g > 0` with `(w.ord x : ℚ) * g = (φ x).order` for every `x`
  (`Place.ord : F → ℤ` with the junk value `ord 0 = 0`, `HahnSeries.order : ℚ` with the junk value
  `order 0 = 0`, so `x = 0` is fine on both sides).
- **Why it reduces.** The port's `Place.exists_of_orderMap` realises any `WithTop ℤ`-valued order map
  as `e` times a place's order. `HasRamBound d` puts every `(φ x).order` in `(1/d)ℤ`, so
  `d * (φ x).order ∈ ℤ` for every `x` — the pin's `exists_int_order_mul` — and
  `μ x := if φ x = 0 then ⊤ else (d * (φ x).order : ℤ)` is a `WithTop ℤ`-valued order map. The engine
  returns `w` and `e` with `d * order = e * ord`, i.e. `order = (e/d) * ord`; the node's `g` is
  `e/d`.
- **What the order writes.** The definition module (§4.1, 42 pin lines); the denominator lemma
  (≈11); the scaling adapter and its five axioms (≈40–60 — mathlib supplies the order algebra:
  `HahnSeries.order_mul`, `order_pow`, `order_C`, `min_order_le_order_add` are all in v4.34, so the
  pin's six `order_map_*` helpers are restatements, and only `order_algebraMap`/`order_inv` need a
  line each); the headline (≈15).
- **Where the general statement lives.** Public in `Place/ValueDictionary.lean`, beside the `ℤ`
  engine it reduces to, as a port-native theorem: the pin has no such statement, so it needs a
  manager `own:` row (suggested `Place.exists_of_orderMap_rat`; the name is the manager's). The
  pin's `ℤ`-valued `exists_of_orderMap` keeps its statement and wire untouched. As landed, the
  common-denominator hypothesis carries the guard `μ x ≠ ⊤` — the unguarded `∀ x, ∃ k, μ x = k/d`
  is uninhabited at `x = 0`, where `h_top` forces `μ 0 = ⊤` — and the engine's conclusion puts the
  scaling on the order-map side (`μ x = g * (P.ord x : ℚ)`), the headline keeping the pin's
  orientation.
- **What does *not* happen.** The pin's sixteen-declaration place construction (`valuationSubring`,
  `exists_generator`, `irreducible_gen`, `hasUnitMulPowIrreducibleFactorization`, `place`,
  `ord_mul_order_gen`, …) re-proves what the engine proves; it is not transcribed. 318 was the
  *transcription* price and is now an upper bound — and it landed at **284 net lines** (engine 163,
  headline 117 with an 81-line adapter), not at the ≈150 this section estimated: the estimate
  counted the ℚ↔ℤ rescaling once, where the derivation pays it twice (once in the engine's
  `ν = d · μ` construction, once in the headline's adapter), and it did not count the two
  statements' scaffolding. The route held: no transcription, no private port helper, no cycle, and
  the pin's six `order_map_*` helpers were not written (mathlib supplies the order algebra).
- **The residual.** The pin's `posOrders`/`exists_generator` block has one thing the engine does not
  hand over — the *irreducibility* of the constructed uniformiser, which the node does not state —
  so nothing is lost by dropping it here. If a later row wants it, it is a node of its own, not
  glue in this one.

## 5. Per-order notes — the traps recorded so far

**RP2.** The 646-line `eq_integers` file is 28 declarations: 27 public plus one `private` helper,
`residue_eq_zero_iff` (7 lines), which the port already declares public under that name — so the
checked surface is 27, the helper is imported rather than copied, and `port_advise`'s substitution
rows say which of the other 27 are already there. `constHom`/`residue_constHom` are written **once**
(they exist, 80/91); the pin repeats them in three of the four files.

**PC1.** The pin's `S_` file opens with three `attribute` walls (`[-instance]` / `[-simp]`) naming
≈150 instances; the port does not transcribe them (BC6/BC8 precedent) — drop them and keep the
proof bodies. Of its 49 declarations, 127 lines are already public in the port and 145 more are
trusted shape-tier substitutions (`evalAt_mul`, `evalAt_algebraMap`, `adicValuation_*`, `t_mem`,
`mem_of_ord_nonneg`, `ord_nonneg_of_mem`, `mem_iff_ord_nonneg`): import them, do not copy. The
new module's six imports are all on the wire already.

**RB1.** The pin's `valuationSubring` collides by *shape* with `ModularCurve.qIntegersBar` (33
lines) in `port_advise`'s substitution tier — a false positive of the `def … : Subring/Prop` tier;
the row's *engine* is what is genuinely new. Under §4.4's route the pin's 22 helper names
(`valuationSubring`, `place`, `posOrders`, `exists_generator`, …) are not transcribed at all, so
none of them has to be rectified or collision-checked. Two traps belong to the derivation instead:
`HahnSeries.order` and `Place.ord` both use `0` as the junk value at zero while
`exists_of_orderMap`'s `μ` is `WithTop`-valued, so the `x = 0` case is where the adapter's
bookkeeping lives; and the one statement with no pin source is the `ℚ`-valued engine itself, whose
`own:` row the manager writes before the worker runs.

**CFE2.** Two traps. (i) The pin's `regularDiffs_eq` is a local 25-line engine *inside* the node's
own `S_` file, whose proof is `exact S12R.regularDiffs_eq`; port the engine, not the three-line
`solution`. (ii) `Differential/RegularDiffs.lean` is the third insertion target and the promotion
target at once: promote first, insert second, or the worker will not see `coeffDer`/`coeffLin`.

**PIC1.** `SemilinearAut.pic0_correspondence_swap_smul` is 151 lines over 10 declarations, and the
pin's own prelude `ord_smul` (7 lines) is a copy of the port's public `Place.ord_smul` /
`SemilinearAut.ord_smul`: import, do not copy. `WeilDatum.symm_pairing` is `rfl`-level, but only
after §4.1's structure exists.

**TL1.** Five unrelated subjects, eleven rows, one character: each is the last public declaration
of an engine the port already has. Do them in one pass over the six files, and treat the four alias
rows (`evalFun_*`, `hasCanonicalLocalResidueK`) as *surface*, not proof: the mathematics is present,
the pin's name is not.

## 6. The gates, per order (unchanged from SET 4)

1. `python3 spec/check_port.py --force <module>` → **0 mismatch / 0 missing**, every added
   declaration `ok` (or a manager-written `own:`/`pin:` row).
2. `#print axioms` on every headline → `[propext, Classical.choice, Quot.sound]`.
3. The order's own modules only, under `flock` and `timeout`: **no tree build, no dependents**, and
   the module silent. A `Replayed` line is not evidence that its `.olean` exists (FR-0033).
4. `dedup.py` / `move_dead.py` on each module; wrapper-over-engine `shape` clusters are the pin's
   own pattern and stay, with the reason recorded.
5. Zero warnings; no `sorry`/`admit`/`axiom`; no `set_option maxHeartbeats`; the worker writes no
   `spec/decl_markers.tsv` row (the manager's `own:` row for RB1's `ℚ`-valued engine is the one this
   set needs, and it is written before dispatch, not by the order).
6. Each order appends the wrapper **and** the `S_` file of every node it adds to its module's
   `spec-pin:` block.

## 7. The six calls — decided (2026-10-27)

| call | decision | what it changes here |
|---|---|---|
| 1. RP2's home | insert `RegularProlongationFinrank.lean` | nothing: §1 and §3 as written |
| 2. PC1's module | new `Place/ChartedSpace.lean` | nothing: §1 and §3 as written |
| 3. RB1's route | **(b) generalise the engine, paid now** — not deferred as debt | §4.4 rewritten; RB1's budget ≈150, `port_advise`'s 318 is an upper bound; a manager `own:` row |
| 4. CFE2's generalisation | generalise in place; **no second copy** | nothing: §4.3.1 as written |
| 5. TL1's `FunctionField` pair | cut now | nothing: §3's new `AlgebraicCurve/FunctionField.lean` |
| 6. the set's size | six orders, as cut — no merge | nothing: §1 as written |

**Two consequences to carry into the work orders.** (i) RB1 now has a manager-side engine piece (the
name of the `ℚ`-valued statement and its `own:` row) and a worker-side proof, and its 318-line price
is replaced by a ≈150-line budget to be confirmed on the tree; the set's expected net new is
therefore **≈2,200**, and RB1 is the one figure to re-measure after landing. (ii) The generalised
engine is the set's only *port-native* public declaration; everything else added is a transcription
or an alias, so the review's surface experiment has a single `own:` case to settle, not a class of
them.

## 8. After the landing — the three numbers, as measured

1. **What the set consumed**: 29 rows, 3,623 silo, ≈2,400 declaration lines (2,941 with headers,
   docstrings and wires) over 21 modules, plus 2 definition modules, 4 wires, 11 promotions and
   2 generalisations. §1.2 has the per-order table.
2. **The new `needed [F terminal]`: 1,070 / 414,126 → 1,040 nodes / 410,470 lines** — a fall of 30 nodes / 3,656 lines, and the `AlgebraicCurve.` demand
   went **105 / 29,700 → 75 / 26,044**, which is the ≈76 / 26,100 this section predicted before the
   wave; the other namespaces moved only where a landed row sat in their demand. Ready candidates
   87 → **96**, leaves 320 → **296**.
3. **Which rows became ready because of the set: fourteen** — the successors of all six stories, led
   by `weilReciprocity` (1,273) and including four `WeilDatum` neighbours, three differential rows,
   the CFE2 successors and the two `evalFun` ones. §1.3 lists them with what unblocked each. The
   promotions and the wires did the rest (the separable generalisation alone produced two rows).

## 9. Reproduce

```bash
cd tools/deps
python3 frontier.py --ds --ready --include-leaves --rank-by silo --top 0 --json   # §0
python3 port_advise.py --with-defs <nodes of one order> --json …                   # §0.2, §3
python3 port_plan.py --json …                                                      # §1's net column
```

The per-order figures in §1 are each order's own read (`--with-defs`, 29 rows split 4/2/1/3/8/11);
they over-count the definition modules shared between orders, which is why their in-port column
sums to 827 against the set's 812.
