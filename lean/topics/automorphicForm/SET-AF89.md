# SET-AF89 — the faithful additive character, the `Kf`-translate span, the constituent right-convolution block, and the definition gate

**Status: LANDED (2026-11-19).** Five orders over eleven new modules; the AF subject's readied block plus the definition gate SET-AF88
§6 handed over. **12 rows / 3,488 silo** on the wire, and **586 pin lines of definition surface**
(`BoundedGenuineCuspRealization` 316, `PadicHeckeCosetSystem` 120, `ViaCompactCuspNotion` 74,
`DeltaLift` 46, `DihedralWeightOneLift` 30) paid by the manager before the proof bodies went out.

| # | order | rows | silo | modules | pin publics on the wire |
|---|---|---|---:|---|---:|
| A | faithfulness of the adelic additive character | 1 | 1,179 | `NumberTheory/AdelicFourier/Faithful.lean` (new) | 44 |
| B | the `Kf`-smooth right-translate span | 1 | 552 | `AutomorphicForm/Adelic/KfSmoothSpan.lean` (new) | 51 |
| C | right convolution on a cuspidal constituent | 6 | 628 | `AutomorphicForm/Adelic/Cusp/ConstituentRightConv.lean` (new) | 32 |
| D1 | the bounded genuine cusp realization and the dihedral weight-one lift | 2 | 570 | `AutomorphicForm/Adelic/Cusp/BoundedGenuineRealization.lean` (new), `LanglandsTunnell/DeltaLift.lean` (new, no proofs), `LanglandsTunnell/DihedralWeightOneLift.lean` (new, no proofs), `LanglandsTunnell/WeightOneBound.lean` (new) | 34 + 1 |
| D2 | the `p`-adic Hecke coset system and the compact cusp notion | 2 | 559 | `RepTheory/LocalLanglands/PadicHeckeCosetSystem.lean` (new), `LanglandsTunnell/HeckeCosetSystem.lean` (new), `AutomorphicForm/Adelic/Cusp/CompactCuspNotion.lean` (new), `AutomorphicForm/Adelic/Cusp/CentralCharacter.lean` (new) | 8 + 29 + 7 + 5 |

**The target line is the wire's public count, not the pin's line count.** `tools/deps/scaffold_audit.py`
reports 44 / 51 / 32 / 35 / 49 pin publics on these wires; each module's number in the table above is
the audit's figure at scaffolding, and the work order quotes it per order. Every one of these `S_`
pins is a *flattened* file — the row is its `solution` and the engine is its remaining declarations
at the same (public or private) visibility — so step 1 of each order is the pin's whole declaration
surface, not just the headline.

## 0. The read

```bash
cd tools/deps
python3 frontier.py --ds --ready --include-leaves --rank-by silo --top 0 --json > build/shelf_af89_read.json
```

| figure | before (SET-AF88 landing) | after this set's scaffolds |
|---|---:|---:|
| `needed [F terminal]` | 511 / 239,044 | **499 / 235,556** |
| ready rows | 15 / 4,474 | **12 / 2,944** |
| leaves | 102 / 25,796 | **96 / 24,416** |
| withheld (FR-0044 guard) | 3 rows | 3 rows |

The scaffolding is the measurement point for a set whose rows are all pre-declared (SET-AF88 §5's
recorded instrument property): the delta is **−12 nodes / −3,488 lines**, exactly the twelve rows
cut, and **three rows become ready** — `AutomorphicForm.CuspidalSpectrum.isIsotypicCuspFormAt_of_mem_of_sub_mem_orthogonal`
(280), `AutomorphicForm.CuspidalConstituent.isCuspSubrep_span_cyclic_and_mem_and_le` (173) and
`AutomorphicForm.CuspidalSpectrum.exists_rightConv_ne_zero_of_ne_bot` (125) — 578 silo, all in the
`CuspidalConstituent`/`CuspidalSpectrum` subject of order C. They are the next set's opening, not
this cut.

**Selfcheck is red on a pre-existing metadata block, not on this set.**
`frontier.py --selfcheck` fails its source-tier line with the fifteen `ModularCurve` `Thm_` rows
registered in [spec/METADATA-ISSUES.md](../spec/METADATA-ISSUES.md) (MD-005), plus the
`ModularCurve.PhiGen` family; none is an AF node and none is in the read above. The corrected read
(`--unport` each) is off by one node / 75 lines at `ModularCurve.ModularPolynomialData.eq_all`; the
AF shelf is unchanged.

**The remaining AF ready block is named, not cut.** After this set the AF-subject ready rows left
are `NumberField.AdelicLevel.exists_glFin_globalPoints_mul_mem_finiteLevelOne_rat` (397),
`AutomorphicForm.IsUnitFactorizableAbove.finComponent_glFin_mem_localIntegralSet_of_apply_ne_zero` (78),
`IsDedekindDomain.FiniteAdeleRing.exists_ne_zero_forall_mul_apply_mem_adicCompletionIntegers_of_isCompact`
(52), `IsDedekindDomain.HeightOneSpectrum.isAdicComplete_adicCompletionIntegers` (111),
`NumberField.AdeleRing.compactSpace_quotient_principalSubgroup` (32) and
`AutomorphicForm.eq_zero_of_isCuspAutomorphicFnAt_productionPinsOf_of_coversModCentre_of_forall_mem_eq_zero`
(25), plus the AF-subject leaves still behind other definition gates. They form two unrelated
stories (the adelic-level lattice and the adelic-Fourier/measure tail) and are deferred by subject,
not by cost.

## 1. The cut

| # | row | silo | lev | note |
|---|---|---|---:|---|
| A1 | `NumberField.AdelicFourier.mem_range_algebraMap_of_forall_apply_mul_eq_one` | 1,179 | 1/4 | 44 publics, 13 private engine declarations |
| B1 | `AutomorphicForm.exists_forall_rightTranslate_eq_sum_mul_of_isArchKFinite_of_isKfSmooth` | 552 | 2/6 | 51 publics |
| C1 | `AutomorphicForm.CuspidalConstituent.exists_isFactorizableTestFn_isArchBiFinite_rightConv_comp_inv` | 109 | 1/1 | |
| C2 | `AutomorphicForm.CuspidalConstituent.exists_rightConv_injOn_of_finiteDimensional_of_forall_apply_mul_eq` | 78 | 1/1 | |
| C3 | `AutomorphicForm.CuspidalConstituent.exists_rightConv_injOn_of_finiteDimensional_of_le` | 77 | 4/4 | |
| C4 | `AutomorphicForm.CuspidalConstituent.continuous_and_isSmoothCuspAutomorphicFnAt_rightTranslate_of_mem_cuspKFiniteSubmodule` | 154 | 8/19 | |
| C5 | `AutomorphicForm.CuspidalConstituent.forall_apply_mul_archRealGLAt_eq_of_isCuspConstituent_of_exists` | 148 | 2/2 | |
| C6 | `AutomorphicForm.CuspidalConstituent.isCuspConstituent_productionPinsOf_mono` | 62 | 1/2 | |
| D1a | `AutomorphicForm.exists_smoothCuspRealizationAt_productionPinsOf_toFun_eq_of_isBoundedOnSiegelWindows_of_coversModCentre` | 69 | 1/1 | definition-gated |
| D1b | `LanglandsTunnell.isBoundedOnSiegelWindows_weightOneLift` | 501 | 1/2 | definition-gated |
| D2a | `LanglandsTunnell.exists_heckeCosetSystem_productionPinsCompact_of_not_dvd` | 446 | 1/2 | definition-gated |
| D2b | `AutomorphicForm.SmoothCuspRealizationAt.centralChar_eq_of_agreesAwayFromFinite` | 113 | 1/16 | definition-gated; deferred four times, now paid |

**The four stories.**

* **A** is the self-duality input of the adelic Fourier transform: the annihilator of the diagonal
  is the diagonal. The proof is the pin's own explicit engine — the archimedean and finite slice
  decompositions `archSingle`/`finSingle`/`archSlice`/`finSlice`, the lattice bound, a Minkowski
  argument with the convex body, the level-shrinking lemma for the finite part, and the final
  `kernel = range` argument through the perp of the principal idèles. Twenty-one of the pin's
  forty-four public declarations are the two slice lemmas and their applications.
* **B** is SET-AF88A's generic tensor split applied to the `Kf`-smooth class: a continuous
  `IsArchKFinite` and `IsKfSmooth` function has a finite-dimensional right-translate span by
  `Kf`, with the translates of the compact open `Kf = maximalCompactAway ∅` splitting as finite
  sums of products of level-invariant functions and functions of the argument. The pin's public
  prelude is the `K`-decomposition engine (`Ksub`, `piece`, `eq_listProd_piece`), conjugation of
  the archimedean row isometries, and the closure of `IsArchKFinite`/`IsKfSmooth` under translation,
  addition and scalar multiplication. Four of its publics are already in the port by shape
  (`ext_glArch_glFin`, `isKfSmooth_add`, `isKfSmooth_smul`, and the arch component dictionary) —
  import and, where the statement is at the pin's binders, declare again at the pin's name.
* **C** is the test-function side of the cuspidal constituent: the reflexion convolution closes the
  factorizable arch-bi-finite class, the flat level-spherical test function makes right convolution
  injective on a finite-dimensional level-invariant space (both with the level as an ideal and as a
  compact `U = O ⊓ finiteAdelicGL2Subgroup`), the cuspidal `K`-finite span is continuous and
  translation-stable, a single real-unipotent-invariant vector forces invariance under all of
  real `GL₂⁺`, and cuspidality is monotone in the compact set `D`.
* **D** is the definition gate SET-AF88 §6 recorded, now measured in full and paid. It is three
  small notions plus the two headline rows they unblock: the *bounded* genuine cusp realization
  (the seven `IsBounded…` predicates, with the pin's 32-declaration API), the dihedral weight-one
  lift's `weightOneArchLift`/`HasWeightOneDecomp`/`weightOneLift` and its `DeltaLift` dependency,
  the `p`-adic Hecke coset system at `GL₂(ℚ_p)`, and the compact-cusp `CuspidalityNotion` built on
  the `ℤ[√-2]` character. The rows are `isBoundedOnSiegelWindows_weightOneLift` (the weight-one
  boundedness), `exists_heckeCosetSystem_productionPinsCompact_of_not_dvd` (the global coset system
  away from the level) and `centralChar_eq_of_agreesAwayFromFinite` (the central character is
  determined away from finite places). **`Def_LanglandsTunnell_DeltaLift` (46 lines) was not in
  SET-AF88 §6's list but is a hard dependency of the dihedral lift**, so the gate is five modules,
  not four.

## 2. The homes and the manager's layer

| module | home / direction | manager's work |
|---|---|---|
| `NumberTheory/AdelicFourier/Faithful.lean` | new, in the `AdelicFourier` directory beside the transform; imports only `AdelicFourier`, `AdelicBox`, `GlobalAddChar`, `IdeleSPartIntegral` | row statement + `spec-pin:` wire; 44-public target |
| `AutomorphicForm/Adelic/KfSmoothSpan.lean` | new, above `RightTranslateSpan` and `LevelCompactness` (measured by `premise_imports.py`) | row statement + wire; 51-public target |
| `AutomorphicForm/Adelic/Cusp/ConstituentRightConv.lean` | new, beside `Constituent.lean` and above `LevelSphericalLimit`/`RightTranslateSpan`/`TestFnTop` | six row statements + six wires; 32-public target |
| `AutomorphicForm/Adelic/Cusp/BoundedGenuineRealization.lean` | new, beside `GenuineRealization.lean`, above `ProductionPinsGeneral`/`WhittakerCoefficient`/`AdelicTraceFin` | **seven definitions verbatim**, all 32 API statements, the `IsGenuineCuspRealizationAt` and `of_toFun_eq` laws, and the 69 row; 34-public target |
| `LanglandsTunnell/DeltaLift.lean` | new; the `Def_LanglandsTunnell_DeltaLift` port | **complete, no `sorry`** (six definitions plus the pin's two `@[simp]` laws) |
| `LanglandsTunnell/DihedralWeightOneLift.lean` | new; the `Def_AutomorphicForm_DihedralWeightOneLift` port | **complete, no `sorry`** (three definitions) |
| `LanglandsTunnell/WeightOneBound.lean` | new; the flattening row for the dihedral lift | row statement + wire |
| `RepTheory/LocalLanglands/PadicHeckeCosetSystem.lean` | new, beside `HeckeCosetSystem.lean` | **eight definitions/statements**; the `padicDiagP`/`padicHeckeRep` bodies are data and are transcribed verbatim |
| `LanglandsTunnell/HeckeCosetSystem.lean` | new; the flattened global coset row above the `p`-adic module | row statement + wire; 29-public target |
| `AutomorphicForm/Adelic/Cusp/CompactCuspNotion.lean` | new, beside the realization dictionary | **all six definitions/statements**, including the `viaCompactCuspNotion` structure instance and the `iotaZsqrtdNegTwo` ring hom |
| `AutomorphicForm/Adelic/Cusp/CentralCharacter.lean` | new; the `113` row above `CompactCuspNotion` | row statement + wire; 5-public target |

All eleven scaffolds elaborate and their rows check (`1 / 1 / 6 / 33 / 1 / 1 / 8 / 1 / 7 / 1` `ok`
at scaffolding; the `BoundedGenuineRealization` module is green at 33 because its seven definitions
and the twenty-five API statements are already declared). Every module is in the tree's dependency
order: none of the ten new modules is imported by an existing module, so no hub is edited and the
five orders touch disjoint files.

## 3. The orders

Orders in `lean/tmp/af89/WO.md` (untracked, like the earlier sets' order files), five orders, disjoint
files, five dispatches in parallel.

## 4. The forecast

The scaffolds are the measurement point (§0): after them `needed` is **499 / 235,556**, ready is
**12 / 2,944**, leaves **96 / 24,416**. Landing can only confirm those three cells — every cut row
is a scaffolded headline — and the set's own return is the three readied rows recorded in §0
(578 silo, 0 nodes of `needed` until they land).

The definition gate's forecast is the one number SET-AF88 §6 quoted and this set re-measured:
1,016 silo of AF rows unblocked by `BoundedGenuineCuspRealization` + `PadicHeckeCosetSystem` +
`DihedralWeightOneLift` (plus the `DeltaLift` dependency), namely 501 + 446 + 69. All 1,016 is cut
here, together with the 113 row's own `ViaCompactCuspNotion` gate — **1,129 silo in all** — so the
gate is consumed by this set rather than left for the next.

## 5. The gates (per order)

1. `cd lean && python3 spec/check_port.py --force FLTForHuman/<module>.lean` → the order's target
   count, **0 mismatch / 0 missing**, every added declaration `ok`.
2. `cd tools/deps && python3 scaffold_audit.py ../../lean/FLTForHuman/<module>.lean` → **complete**
   (the acceptance test; `check_port` cannot see a missing declaration).
3. `cd lean && lake env lean -DautoImplicit=false -DmaxHeartbeats=200000 FLTForHuman/<module>.lean`
   → **no output at all**, then one `flock /tmp/flt-build.lock timeout 110 lake build <Target>`.
4. `#print axioms` on every row and the largest engines → `[propext, Classical.choice, Quot.sound]`.
5. `cd tools/deps && python3 dedup.py --within --module <stem>` → 0 clusters, or the pins' own
   `_impl` pairs with the reason recorded.
6. `python3 move_dead.py --source ../../lean/FLTForHuman/<module>.lean --target /dev/null --dry-run`
   → `0 declarations, 0 lines`.
7. A heartbeat probe recorded in the header, never installed (FR-0225).

## 6. Risks

| # | risk | mitigation |
|---|---|---|
| 1 | A is a 1,179-line transcription with 44 publics and a 13-declaration private engine; the pin's `p2m_open`/`p2m_export` stage makes the namespace hard to read | the engine names are transcribed at the pin's last names under a subject namespace; the work order lists the eight blocks in proof order and points at `AdelicR2`'s `eq_one_of_forall_pow_norm_sub_one_le` as the first public |
| 2 | B's four already-ported statements have different binder skeletons | declare at the pin's binders in the new module (a local restatement is cheaper than a promotion and is what the checker diffs); import the port's copy for the proof |
| 3 | C's `exists_rightConv_injOn…` rows share the level-spherical engine with `LevelSphericalLimit`; the pin's `_of_le` row calls the flat limit | import `LevelSphericalLimit`; the two rows are the same story and are one order |
| 4 | D's five definition modules are the manager layer and one (`DeltaLift`) was missing from SET-AF88 §6 | all are on disk, green, and wired; the worker transcribes the remaining API statements and proves the bodies |
| 5 | the `501` pin has 25 private helpers under one public row | transcribe them privately at the pin's last names; the checker verifies only the public row, the audit only publics, and `move_dead` will find the unused ones |
| 6 | the tree's oleans can be stale (FR-0033/FR-0230) | each order builds its own dependencies first, one module per bounded call |

## 7. The landing (2026-11-19)

All five orders landed with no `sorry`, no heartbeat floor, no linter option, and no hub or existing
module edited. **11 new modules, 4,057 lines, 251 declarations (211 public + 40 private).**

| module | rows | lines | decls (pub/priv) | checker | audit | dedup | probe (silent / fails) |
|---|---|---:|---|---|---|---:|---|
| `NumberTheory/AdelicFourier/Faithful.lean` | A1 | **1,233** | 57 (44/13) | **44 ok / 0 / 0** | complete (57 declared, 0 closure) | 1 (pin's `'`/`''` private pair) | 19,000 / 18,000 |
| `AutomorphicForm/Adelic/KfSmoothSpan.lean` | B1 | **570** | 48 (48/0) | **48 ok / 0 / 0** | complete (51 wire, 3 closure) | 1 (pin's `main`/`solution`) | 60,000 / 30,000 |
| `AutomorphicForm/Adelic/Cusp/ConstituentRightConv.lean` | C1–C6 | **522** | 25 (24/1) | **24 ok / 0 / 0** | complete (32 wire, 8 closure) | **0** | 10,000 / 5,000 |
| `AutomorphicForm/Adelic/Cusp/BoundedGenuineRealization.lean` | D1a | **360** | 35 (34/1) | **34 ok / 0 / 0** | complete (30 declared) | **0** | 2,000 / 1,500 |
| `LanglandsTunnell/DeltaLift.lean` | — | 61 | 8 (8/0) | **8 ok / 0 / 0** | complete | **0** | none (no proof) |
| `LanglandsTunnell/DihedralWeightOneLift.lean` | — | 45 | 3 (3/0) | **3 ok / 0 / 0** | — | **0** | none (no proof) |
| `LanglandsTunnell/WeightOneBound.lean` | D1b | **416** | 26 (1/25) | **1 ok / 0 / 0** | complete (1 wire) | **0** | 80,000 / 50,000 |
| `RepTheory/LocalLanglands/PadicHeckeCosetSystem.lean` | — | 142 | 8 (8/0) | **8 ok / 0 / 0** | complete | **0** | 1,000 / 500 |
| `LanglandsTunnell/HeckeCosetSystem.lean` | D2a | **472** | 29 (29/0) | **29 ok / 0 / 0** | complete | **0** | 50,000 / 20,000 |
| `AutomorphicForm/Adelic/Cusp/CompactCuspNotion.lean` | — | 100 | 7 (7/0) | **7 ok / 0 / 0** | complete | **0** | 500 / 200 |
| `AutomorphicForm/Adelic/Cusp/CentralCharacter.lean` | D2b | **136** | 5 (5/0) | **5 ok / 0 / 0** | complete | **0** | 50,000 / 20,000 |
| | **12** | **+4,057** | **251 (211/40)** | **211 ok, 0 mismatch, 0 missing, 0 own** | 11 complete | 2 pin-own | |

`move_dead` reads `0 declarations, 0 lines` on all eleven. Every row and every probed engine is on
`[propext, Classical.choice, Quot.sound]`; the five `Def_` ports are statement-clean (`BoundedGenuineRealization` 34 ok,
`DeltaLift` 8 ok, `DihedralWeightOneLift` 3 ok, `PadicHeckeCosetSystem` 8 ok, `CompactCuspNotion` 7 ok) and need no
axiom probe beyond their theorems. The eleven modules built one at a time under the lock.

**Consumers** — one per order, each silent, each composing across modules rather than restating a row:

* `spec/NumberFieldSetAF89AConsumer.lean` — the annihilator of the diagonal is exactly the diagonal
  (`Iff` of the faithfulness row with `IsGlobalAddChar.principalInvariant`).
* `spec/AutomorphicFormSetAF89BConsumer.lean` — the `Kf`-translate row read at `k = 1`: a continuous
  arch-`K`-finite `Kf`-smooth function is a finite ℂ-linear combination of functions of the same kind.
* `spec/AutomorphicFormSetAF89CConsumer.lean` — monotonicity of the constituent in `D`, then the
  real-`GL₂⁺` invariance row at the smaller compact set.
* `spec/AutomorphicFormSetAF89D1Consumer.lean` — bounded genuine ⇒ genuine ⇒ smooth cusp realizable.
* `spec/AutomorphicFormSetAF89D2Consumer.lean` — the compact-cusp notion at `ℚ` turned into arithmetic
  realizability, and the coset row read through `IsHeckeCosetSystem.mem_doubleCoset`.

### The decisions of the landing

1. **A's two slice statements keep the pin's qualified spelling.** `check_port` hashes statement
   text and does not erase a namespace prefix, so renaming the pin's `AdelicR2Slices` to `Slice`
   re-spells the two statements that mention a slice constructor (pin `:547`, `:857`) and reads
   `2 mismatch` (or `own`). The module keeps the pin's text on exactly those two hypothesis lines via
   two `local notation` lines (`AdelicR2Slices.archSlice`/`.finSlice` → `Slice.…`); **no declaration
   or namespace name contains an `R2`/`P2MW` token**. This is a checker accommodation, not a statement
   change — deleting the two notation lines and using `Slice.…` is a two-line edit that costs the two
   mismatches.
2. **B's `main`/`solution` pair stays declared twice** (the pin's own duplication; the row is
   `solution`'s body, `main` is the public engine with the same statement). C's two pins' `main`s are
   folded into their rows instead, because there the `solution` statement *is* `main`'s and the
   pin's own proof inlines it; `scaffold_audit` credits those two to unrelated `main`s, which FR-0237
   records as the instrument's last-name blind spot.
3. **D1's `memLp_two_restrict_of_bound` needed `letI` in term position**, not `have`/`let`: the goal
   type carries a `letI`-bound `MeasurableSpace` and only the inlining elaborates. This corrects
   FR-0223's blanket substitution (FR-0235).
4. **A `sorry` body hides `linter.unusedVariables`**: the 69 row's frozen `hd`/`hcov` are dead in the
   pin's proof, so the scaffold was silent only because of the `sorry`; both are spent once, by name
   (FR-0236).
5. **The manager's `DeltaLift` transcription missed the pin's two closing `@[simp]` theorems**
   (`deltaLiftSystem_level`, `deltaLiftSystem_toRawCentral`) because the pin's declaration count was
   taken with a regex, which does not see an `@[simp]`-prefixed declaration; `check_port` was green
   at 6 ok and only `scaffold_audit` caught it (8 publics, 2 missing). Both are now declared and the
   module audits `complete` at 8 ok — the recipe's "count with the corpus parser, never a regex"
   met from the manager's side.
6. **`Cusp/RealizationTwist`** is the one import added outside the scaffolds' lists: `CentralCharacter`
   needs `TwistRpow.det_diagOne` for the pin's `det_diagOne`. B added `AutomorphicForm/Adelic/AdelicMaximalCompact`
   (`maximalCompactAway`), A added four mathlib imports, all recorded in the headers.

### The set's numbers

| figure | before (AF88) | after scaffolds | **after landing** | forecast |
|---|---:|---:|---:|---:|
| `needed [F terminal]` | 511 / 239,044 | 499 / 235,556 | **499 / 235,556** | 499 / 235,556 exact |
| ready rows | 15 / 4,474 | 12 / 2,944 | **12 / 2,944** | 12 / 2,944 exact |
| leaves | 102 / 25,796 | 96 / 24,416 | **96 / 24,416** | 96 / 24,416 exact |
| withheld | 3 | 3 | **3** | 3 exact |

The landing read equals the scaffold read, as SET-AF88 §5 predicts for a set whose rows are all
pre-declared. The set's return is the three rows the scaffolding readied: 280 + 173 + 125 = **578
silo**, all AF and all in the `CuspidalSpectrum`/`CuspidalConstituent` subject of order C — the next
cut's opening, together with the 397 `AdelicLevel` row and the CARRY-FORWARD items.

### Frictions this set produced

* **FR-0235** — `haveI`/`letI` → `have`/`let` is not always safe: a `letI`-bound instance **in the goal
  type** needs the inlining; write the declaration in term position.
* **FR-0236** — a `sorry` body hides `linter.unusedVariables`; a scaffold's "silent and built" is not
  evidence that its frozen binders will be spent.
* **FR-0237** — `scaffold_audit.py` matches by **last name**, so an unrelated declaration can read a
  pin public as satisfied (`Kw` in B, the two `main`s in C); read `declared + imported + folded =
  wire` and name every non-identical `imported` match.

Proof-side, statement-neutral v4.34 drift met by the workers: `unfold archSlice`/`finSlice` →
project-then-`show` (`AdeleRing` is a product `def`), `Finset.prod_le_one`'s lost nonnegativity
argument, `Set.mem_preimage`'s `hsmg ▸ hsub hgpi` shape, `natGenerator_padicPlace`/`mem_integralSubgroup_of_norm_le`
under `Nat.Primes`/`ℤ_[p]` subtype transparency, `Measure.haar` → `haarMeasure`, and the standing
`if_pos`/`dif_pos`/`Set.mem_setOf_eq`/`continuous_mul_right` renames.
