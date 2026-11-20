# SET-AF88 — the right-translate span, the `S`-part integrals, the `Kf`-smooth tensors, and the Siegel windows

**Status: LANDED (2026-11-14).** The fifth set of the
wave, and the first cut from the **leaf block**: the AF subject's ready block was down to four rows after
SET-AF87, so this set is the leaf rows the recipe says never to drop. **16 rows / 4,225 silo** in **four
orders**, four new modules.

> **Next session: read §6 first.** The AF subject's remaining rows are behind three unported `Def_` modules
> (316 + 120 + 30 lines, all their own imports ported, ≈1,016 silo unblocked). §6 is the hand-off: what the
> gate is, where each module homes, the four steps to port one, and the two ordinary orders that come before
> it.

| # | order | rows | silo | module | pin publics (= the target line) |
|---|---|---|---:|---|---:|
| A | the right-translate span and its consequences | 3 | 1,397 | `AutomorphicForm/Adelic/RightTranslateSpan.lean` (new) | 81 (24 + 34 + 23) |
| B | the `S`-part measure and its product integrals | 5 | 1,394 | `NumberTheory/NumberField/IdeleSPartIntegral.lean` (new) | 92 (28 + 39 + 13 + 9 + 3) |
| C | `Kf`-smooth test functions and pure tensors | 4 | 954 | `AutomorphicForm/Adelic/KfSmoothTensor.lean` (new) | 86 (25 + 25 + 16 + 20) |
| D | Siegel windows: compactness, monotone covers, the criterion | 4 | 480 | `AutomorphicForm/Adelic/Siegel/WindowCriterion.lean` (new) | 18 (9 + 7 + 1 + 1) |

**A target line here is exact, not an estimate.** Every one of the 17 pins is a *flattened* file — all of
its declarations are public, and the row is its `solution` — so the port declares exactly as many
declarations as the pin publishes, and `check_port` emits one verdict per declaration. The census
(`spec/statement_db.py`) gives 81 / 92 / 86 / 18, and each is also the order's step-1 size (minus the row
itself), which is the real work: four orders of 18–92 public declarations to transcribe before a proof is
written.

## 0. The read

```bash
cd tools/deps
python3 frontier.py --ds --ready --include-leaves --rank-by silo --top 0 --json > build/shelf_af88_read.json
```

| figure | before (AF87 landing) | after the scaffolds |
|---|---:|---:|
| `needed [F terminal]` | **527 / 243,269** | **511 / 239,044** |
| ready rows | 10 / 2,212 | **15 / 4,474** |
| leaves | 118 / 30,021 | **102 / 25,796** |
| withheld (FR-0044 guard) | 4 / 831 | 4 / 831 |

The 16 rows cut are all leaves: the delta is exactly −16 nodes / −4,225 lines, and the leaf block falls
30,021 → 25,796 — the first cut in four sets that takes a real bite out of it. What remains of the leaf
block is 102 rows, and the AF-subject part of it is dominated by the definition-gated rows (below).

## 1. The cut

| # | row | silo | lev |
|---|---|---|---:|
| A1 | `AutomorphicForm.exists_sum_prod_mul_of_rightTranslatesSpanFinite` | 576 | 2/2 |
| A2 | `AutomorphicForm.exists_depth_forall_apply_mul_lowerUnipotentGL2_eq_of_sum_translate` | 445 | 1/2 |
| A3 | `AutomorphicForm.exists_isArchBiFinite_rightConv_comp_inv` | 376 | 1/1 |
| B1 | `NumberField.Idele.lintegral_mul_prod_ord_sPartMeasure_eq_lintegral_sPartMeasure_empty_mul_prod_tsum` | 381 | 1/4 |
| B2 | `NumberField.Idele.exists_lintegral_prod_norm_sPartMeasure_empty_eq_mul_prod_lintegral` | 370 | 1/6 |
| B3 | `IsDedekindDomain.FiniteAdeleRing.exists_forall_sub_algebraMap_mem_adicCompletionIntegers` | 342 | 1/5 |
| B4 | `IsDedekindDomain.FiniteAdeleRing.exists_sub_algebraMap_mem_adicCompletionIntegers` | 228 | 1/5 |
| B5 | `NumberField.Idele.sPartMeasure_pos_of_isOpen_of_partAt_eq` | 73 | 1/1 |
| C1 | `AutomorphicForm.IsKfSmooth.exists_ideal_forall_apply_mul_conj_unipotentGL2_eq` | 328 | 3/4 |
| C2 | `AutomorphicForm.CuspidalConstituent.exists_isFactorizableTestFn_isArchBiFinite_conj` | 245 | 1/1 |
| C3 | `AutomorphicForm.exists_eq_mul_mem_levelOne_inf_finiteAdelicGL2Subgroup_commute_placeEmbed_of_forall_mem_localIntegralSet` | 192 | 1/1 |
| C4 | `AutomorphicForm.IsFactorizableTestFn.comp_mul_unipotentGL2_mul_mem_pureTensorSet` | 189 | 1/4 |
| D1 | `AutomorphicForm.WindowedSiegel.isCompact_centreCutSiegelSet_inter_heightCap` | 282 | **5/10** |
| D2 | `AutomorphicForm.coversModCentre_of_le_of_lt_of_coversModCentre` | 150 | 4/8 |
| D3 | `AutomorphicForm.exists_iUnion_centreCutSiegelSet_mem_nhds` | 25 | 1/1 |
| D4 | `AutomorphicForm.eq_zero_of_isLsXiFunction_of_coversModCentre_of_forall_mem_eq_zero` | 23 | 1/1 |

**The four stories.** A is the right-translate span: a generic tensor split (a function whose right translates
by finitely many commuting subgroups lie in a finite-dimensional span is a finite sum of products of
level-invariant factors), the *depth* such a finite sum acquires, and archimedean bi-finiteness under the
reflexion convolution. B is the `S`-part measure of the idèles: its two product formulas, the positivity on a
set with a nonempty slice, and the two finite-adèle approximation statements. C is `Kf`-smoothness: the level
ideal it implies, conjugation preserving the test-function class, the splitting of an integral element modulo
the level, and the pure-tensor set being preserved by the unipotent translate. D is the windowed Siegel
picture: compactness of a capped centre-cut Siegel set, monotone covers, the windows forming a neighbourhood
of the identity, and the vanishing criterion for an `L`-function that dies on a covering set.

## 2. The homes and the scaffolds

| module | home | notes |
|---|---|---|
| `AutomorphicForm/Adelic/RightTranslateSpan.lean` | new, above `RightConvolution` and the archimedean dictionary | A1 is *generic group theory* stated at the pin's name (as SET-AF86B's `Submodule` block was); the header says so |
| `NumberTheory/NumberField/IdeleSPartIntegral.lean` | new, beside `IdeleProductMeasure.lean` (its `Def_` module) | two namespaces: `NumberField.Idele` (three rows) and `IsDedekindDomain.FiniteAdeleRing` (two) |
| `AutomorphicForm/Adelic/KfSmoothTensor.lean` | new, beside `SmoothAutomorphicFn` and `FactorizableTestFn` | needed `LocalOrbitalBase` (`localIntegralSet`), `RepTheory/LocalLanglands/UnramifiedWhittaker` (`placeEmbed`) and `NumberTheory/AdelicFourier` (`pureTensorSet`) beyond the scaffold's first import list |
| `AutomorphicForm/Adelic/Siegel/WindowCriterion.lean` | new, under `Siegel/` | needed `Siegel/Covering` (`CoversModCentre`) and `open Filter Topology` (the `𝓝` notation) |

All four scaffolds are green at their row counts (3 / 5 / 4 / 4 ok), build, and their audits report the
step-1 blocks (77 / 87 / 82 / 14 MISSING rows after the rows themselves). **A, C and D have landed** — A at
`81 ok` (1,443 lines, 81 declarations, step 1 in one pass, `premise_imports.py` `# nothing to add`, probe
12,000 / 11,000), D at `18 ok` (518 lines, probe 25,000 / 12,500) and C at **`85 ok` + 0 dedup clusters**
(990 lines, 85 declarations, probe 10,000 / 5,000) — with one consumer each
(consumers `spec/AutomorphicFormSetAF88AConsumer.lean`, `spec/AutomorphicFormSetAF88CConsumer.lean` and
`spec/AutomorphicFormSetAF88DConsumer.lean`, all green); B is in flight.

C's landing settled one contradiction in the work order, and the resolution is the port's precedent rather
than the bigger number. The brief said both "the target is 86 (the pins' public count)" and "declare the
duplicate pair once at the row's name" — the two cannot both hold, because pin 4 states
`comp_mul_unipotentGL2_mul_mem_pureTensorSet_impl` and the row with the *same* statement. The house rule is
the one `Siegel/FiniteCover.lean` already records for exactly this shape: **declare once, at the row's
name**, take the pin's `_impl` body as the row's proof, and accept `85 ok` with `scaffold_audit` classifying
the un-declared `_impl` as `RENAMED?` (same statement, different last name) and still reading `complete`.
That keeps `dedup --within` at **0 clusters**, which is the gate that exists to catch this duplication; the
one-line-count target is the weaker claim. The row's inlined body needed six `SliceTensor.`-qualified names
(the pin's `_impl` sat inside that namespace), which the manager supplied — the only edit outside a worker's
file in this set.

A's landing produced the wave's two sharpest process corrections, both now in `logs/frictions.md`:
**FR-0231** (`continuous_mul_right` is `continuous_mul_const` in v4.34 — the `Continuous (· * g)` idiom is in
every adelic continuity proof) and **FR-0232** ("statements only, `sorry` bodies" is wrong for `def`s: a
stubbed `def` loses the section variables only its body mentions and the arity changes, so step 1 is
"theorem bodies `sorry`, `def` bodies verbatim"; a whole-declaration splice must stop at the next
declaration's `variable`/`include`/`section` prelude, not at its keyword; and a `def` can carry equations,
so FR-0228's `|`-clause cut is live outside the Whittaker module). No legacy home and no hub is
edited: four new files, four orders, only the build lock shared.

**Deferred: the definition gate — the next session starts here (§6).** The AF subject's remaining leaf rows
are *definition-gated*: their statements use vocabulary from three unported `Def_` modules. Those modules are
manager work (playbook §3.4/§4: the manager ports the definition layer), they are small, and every one of
their own imports is already ported — so the gate is a bounded job, and it is recorded in full in §6 below
rather than left implicit here.

## 3. The orders and the gates

Orders in `lean/tmp/af88/WO.md`, with SET-AF87's six gates unchanged.

## 4. The forecast, measured with the scaffolds on disk

| figure | §0 | forecast (AF88) |
|---|---:|---:|
| `needed [F terminal]` | 527 / 243,269 | **511 / 239,044** |
| ready rows | 10 / 2,212 | **15 / 4,474** |
| leaves | 118 / 30,021 | **102 / 25,796** |

**Five rows become ready**, and they are the set's own chains:

| row readied by the set | silo | by |
|---|---:|---|
| `NumberField.AdelicFourier.mem_range_algebraMap_of_forall_apply_mul_eq_one` | 1,179 | C3 |
| `AutomorphicForm.exists_forall_rightTranslate_eq_sum_mul_of_isArchKFinite_of_isKfSmooth` | 552 | C1 |
| `NumberField.AdelicLevel.exists_glFin_globalPoints_mul_mem_finiteLevelOne_rat` | 397 | B3/B4 |
| `AutomorphicForm.CuspidalConstituent.exists_isFactorizableTestFn_isArchBiFinite_rightConv_comp_inv` | 109 | C2 |
| `AutomorphicForm.eq_zero_of_isCuspAutomorphicFnAt_productionPinsOf_of_coversModCentre_of_forall_mem_eq_zero` | 25 | D4 |

The 1,179-silo `Fourier.mem_range_algebraMap_…` is the next set's order A, with the `Kf`-smooth tensor
identity (552) beside it.

## 5. The landing

All 16 rows in, no `sorry`, four new modules, four consumers.

| file | rows | lines | decls | checker | probe (silent / fails) | dedup |
|---|---|---:|---|---|---:|---|
| `AutomorphicForm/Adelic/RightTranslateSpan.lean` | A1–A3 | **1,443** | 81 (81 + 0) | **81 ok / 0 / 0** | 12,000 / 11,000 | 2 (pin's pairs) |
| `NumberTheory/NumberField/IdeleSPartIntegral.lean` | B1–B5 | **1,392** | 92 (92 + 0) | **92 ok / 0 / 0** | 13,000 / 6,500 | 7 (pin's pairs) |
| `AutomorphicForm/Adelic/KfSmoothTensor.lean` | C1–C4 | **990** | 85 (85 + 0) | **85 ok / 0 / 0** | 10,000 / 5,000 | **0** |
| `AutomorphicForm/Adelic/Siegel/WindowCriterion.lean` | D1–D4 | **518** | 18 (18 + 0) | **18 ok / 0 / 0** | 25,000 / 12,500 | 1 (pin's pair) |
| | **16** | **+4,343** | **276 (16 rows + 260 engines)** | **276 ok, 0 mismatch, 0 missing, 0 own** | | |

Every module is silent at `-DmaxHeartbeats=200000` with no in-file `set_option`; axioms
`[propext, Classical.choice, Quot.sound]` on every row and on the probed engines of all four; `move_dead`
reads `0 declarations, 0 lines` on all four; `scaffold_audit` **complete** on all four with every pin public
declaration accounted for (folded onto its row, satisfied by the import closure, or declared here).

Consumers, each silent, each *composing* two rows rather than restating one:
`spec/AutomorphicFormSetAF88AConsumer.lean` (the depth row at `r = 1`; the reflexion row unpacked),
`spec/AutomorphicFormSetAF88CConsumer.lean` (a conjugated factorizable test function fed through the
pure-tensor row — what the orbital analysis does; the `Kf`-level row at a point),
`spec/AutomorphicFormSetAF88DConsumer.lean` (the compactness row at `ℚ` and the pin's ample thresholds; the
neighbourhood row at a point; and vanishing on the *wider* window set, which composes the monotonicity row
into the vanishing criterion), and `spec/AutomorphicFormSetAF88BConsumer.lean` (the simultaneous
approximation in its general-field form and at `ℚ`).

### The three decisions of the landing

1. **C's duplicate pair is declared once** (the work order contradicted itself: "86 ok" and "declare it once at
   the row's name" cannot both hold when the pin states `_impl` and the row with the *same* statement). The
   house rule — `Siegel/FiniteCover.lean`'s — wins: declare once at the row's name, take the pin's `_impl`
   body as the row's proof, read **85 ok** with the un-declared `_impl` as `RENAMED?` in the audit, and keep
   `dedup --within` at **0 clusters**, which is the gate that exists to catch this duplication. The row's
   inlined body needed six `SliceTensor.`-qualified names (the pin's `_impl` sat in that namespace).
2. **B's nineteen re-declared prelude publics stay** (the pin's own duplication, not the port's). Pin 1's
   first 19 publics are the flattened prelude that the ported `Def_NumberField_IdeleProductMeasure` carries
   `private`; the wire requires one verdict per public, so they are re-declared at the pins' statements
   (92 ok). The alternative — promote the block in `IdeleProductMeasure.lean` and import it here — reads
   73 ok and needs 19 wire decisions on a foundational module plus its cascade; the pin duplicates exactly
   this way (private in the `Def_`, public in the `S_`), so the port's shape mirrors the authority. Recorded
   here as the place a future consumer would promote from, should one need the block without the pin's copy.
3. **No `own:`/`pin:` marker anywhere in the set.** Every declaration verifies at a tier the checker has.

### Frictions this set produced (all in `logs/frictions.md`)

* **FR-0231** — `continuous_mul_right` is `continuous_mul_const` in v4.34; the `Continuous (· * g)` idiom is
  in every adelic continuity proof, so this drift will be met again.
* **FR-0232** — **"statements only, `sorry` bodies" is wrong for `def`s** (a stubbed `def` loses the section
  variables only its body mentions and the elaborated arity changes: step 1 is *theorem bodies `sorry`, `def`
  bodies verbatim*); and a whole-declaration splice must stop at the next declaration's
  `variable`/`include`/`section` prelude, not at its keyword.
* **FR-0233** — a bare `end` no longer closes a `namespace` at v4.34 (only a `section` does), and the error is
  reported at the file's *last* `end`.
* **FR-0234** — `scaffold_audit.py` and `premise_imports.py` are CWD-relative (`tools/deps/`), unlike
  `check_port.py` (`lean/`); a work order must quote the working directory, not just the path.

Plus the v4.34 rename list the workers met, all proof-side: `if_pos/if_neg → ite_eq_left/ite_eq_right`,
`dif_* → dite_*`, `Set.mem_setOf_eq → Set.mem_ofPred_eq`, `Set.mem_diff → Set.mem_sdiff`,
`continuous_mul_left → continuous_const_mul`, `ENat.coe_le_coe → ENat.natCast_le_natCast`, `zero_le' →
zero_le`, and one `Matrix.of` change (`levelParam_zero`'s `of_apply` no longer reduces on its own).

### The set's numbers

| figure | before | **after** (measured; = the scaffold read) | forecast |
|---|---:|---:|---:|
| `needed [F terminal]` | 527 / 243,269 | **511 / 239,044** | 511 / 239,044 ✓ exact |
| ready rows | 10 / 2,212 | **15 / 4,474** | 15 / 4,474 ✓ exact |
| leaves | 118 / 30,021 | **102 / 25,796** | 102 / 25,796 ✓ exact |
| withheld | 4 / 831 | 4 / 831 | 4 / 831 ✓ exact |

The five readied rows are the forecast's five (1,179 + 552 + 397 + 109 + 25 = 2,262, the ready block's rise
while its membership turns over). **This is the first set whose landing read equals its scaffold read**: the
scaffolding already declared the 16 rows, and the shelf's name tier credits a `sorry`-bodied headline, so the
landing could only confirm it. That is a property of the instrument, recorded now because it will recur: for a
leaf-set, the scaffold read and the landing read are the same read, and the *scaffolding* is the measurement
point.

The next cut is §6's: the two rows this set readied (1,179 and 552) are ordinary orders and come before the
definition gate, which then unblocks ≈1,016 silo.

## 6. Start here next session — the definition gate

**This section is the hand-off.** The AF subject's ready block and its cheap leaves are exhausted; what
remains is behind three `Def_` modules that are not in the port. They are small, their own imports are all
ported, and together they unblock ≈1,016 silo of AF rows. Port them first, then cut the next set from the
shelf the re-read produces.

| unported `Def_` module | pin lines | pin imports (all ported) | port rows it unblocks |
|---|---:|---|---|
| `Def_AutomorphicForm_BoundedGenuineCuspRealization` | 316 | `Def_AutomorphicForm_ProductionPinsGeneral`, `Def_AutomorphicForm_WhittakerCoefficient`, `Def_NumberField_AdelicTraceFin` | `AutomorphicForm.exists_smoothCuspRealizationAt_productionPinsOf_toFun_eq_of_isBoundedOnSiegelWindows_of_coversModCentre` 69; `LanglandsTunnell.isBoundedOnSiegelWindows_weightOneLift` 501 |
| `Def_LocalLanglands_PadicHeckeCosetSystem` | 120 | (its own closure; `LocalLanglands_HeckeCosetSystem` is ported) | `LanglandsTunnell.exists_heckeCosetSystem_productionPinsCompact_of_not_dvd` 446 |
| `Def_AutomorphicForm_DihedralWeightOneLift` | 30 | — | the same weight-one row |

**What the gate is, per module.** `Def_AutomorphicForm_BoundedGenuineCuspRealization` is seven definitions —
`IsBoundedOnSiegelWindows` (`:15`), `IsBoundedGenuineFn` (`:19`), `IsBoundedGenuineCuspRealizationAt` (`:26`),
`IsBoundedGenuineCuspRealizable` (`:30`), `IsArithBoundedGenuineCuspRealizable` (`:34`),
`IsArithBoundedGenuineCuspRealizableVia` (`:38`) and `boundedGenuineCuspNotionOf` (`:43`) — i.e. the *bounded*
twin of the genuine-cusp-realization predicate the port already has. The 30-line
`Def_AutomorphicForm_DihedralWeightOneLift` is one more notion on the same weight-one row.

**How to port one** (the recipe the port uses for every `Def_` module; each step is measured on the last
three such ports):

1. **Pick the home by subject, then check the import direction.** These predicates belong with the
   realization dictionary (`AutomorphicForm/Adelic/IsotypicCuspSpace.lean` and the `SmoothCuspRealization`/
   `GenuineRealization` pair) — a `Def_` module's declarations are only placeable in a module **above** the
   modules that define their *statement's* vocabulary and **below** every module that will consume them.
   `premise_imports.py --nodes <the rows it unblocks> --missing-from <proposed home> --olean` answers the
   second half in one call.
2. **Transcribe at the pin's names**, the pin's namespace, `spec-pin:` wire to the pin `Def_` file — the
   `Def_` block is not legacy, so it wires itself (`spec-pin: Definitions/Def_….lean`) and `check_port`
   checks it like any other module. `def` bodies are transcribed verbatim, never stubbed (FR-0232).
3. **Gates:** `check_port --force` green with `0 mismatch / 0 missing`, silent at 200 k, axioms
   `[propext, Classical.choice, Quot.sound]`, `dedup` 0 clusters, `move_dead` `0 / 0`, a recorded probe.
4. **Then the rows.** Each unblocked row is an ordinary port order; `isBoundedOnSiegelWindows_weightOneLift`
   (501) is the largest and needs `Def_AutomorphicForm_DihedralWeightOneLift` as well, so it is one order of
   its own with two definition gates behind it.

**What is *not* in the gate**, and should not be re-litigated: the 1,179-silo
`NumberField.AdelicFourier.mem_range_algebraMap_of_forall_apply_mul_eq_one` and the 552-silo
`AutomorphicForm.exists_forall_rightTranslate_eq_sum_mul_of_isArchKFinite_of_isKfSmooth` row that SET-AF88
readied — those are ordinary orders and come *first*, before the gate: a set's readied block always precedes
its definition work (the recipe's §7).

**And a stale claim to correct at the same time.** SET-AF84's §1 and SET-AF86's §1 both deferred
`AutomorphicForm.SmoothCuspRealizationAt.centralChar_eq_of_agreesAwayFromFinite` (113 silo) on
`Def_HeckeCharacter_FiniteOrder`, which has since landed; the live gate is
`Def_AutomorphicForm_ViaCompactCuspNotion` (74 lines, all four of its imports ported), which the same
`Def_`-porting pass should take — it is the smallest of the four and unblocks a row with project leverage 16.

*(Follow-up, SET-AF89 2026-11-19: the gate was paid as part of that set's manager layer. Measured
there, the list above is one module short — `Def_LanglandsTunnell_DeltaLift` (46 lines, unported) is a
hard dependency of `Def_AutomorphicForm_DihedralWeightOneLift` — so the weight-one row needed five
`Def_` modules, not three. All five plus the two ordinary orders (1,179 and 552) landed; see
[SET-AF89.md](SET-AF89.md) §7.)*
