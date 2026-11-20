# SET-AF90 — the constituent closure, the archimedean level lattice, the integral adeles, the box measure, and the adelic height

**Status: LANDED (2026-11-20).** The next cut after SET-AF89:
the `CuspidalSpectrum`/`CuspidalConstituent` block AF89 readied, the `AdelicLevel` arch
dictionary, the integral/compact structure of the adele ring, the adelic box measure, and the
adelic height's compact-set comparison. **21 rows / 3,582 silo** in five orders, five new
modules; no definition gate (every pin's own `Definitions/` imports are ported).

| # | order | rows | silo | module | wire (pin publics) |
|---|---|---|---:|---|---:|
| A | the constituent and isotypic closure of the cuspidal spectrum | 5 | 641 | `AutomorphicForm/Adelic/Cusp/SpectrumConstituentClosure.lean` (new) | 5 |
| B | the archimedean level lattice and its `diagOne` dictionary | 3 | 776 | `NumberTheory/AdelicLevel/ArchLevelLattice.lean` (new) | 52 |
| C | the integral and compact structure of the adele ring | 4 | 313 | `NumberTheory/NumberField/IntegralAdeles.lean` (new) | 12 |
| D | the box measure and the integral finite adèles | 7 | 1,177 | `NumberTheory/AdelicBox/Measure.lean` (new) | 70 |
| E | the adelic height on compact sets and under rational left multiplication | 2 | 675 | `NumberTheory/AdelicHeight/Compactness.lean` (new) | 50 |

## 0. The read

```bash
cd tools/deps
python3 frontier.py --ds --ready --include-leaves --rank-by silo --top 0 --json > build/shelf_af90_read.json
```

| figure | before (AF89 landing) | after this set's scaffolds |
|---|---:|---:|
| `needed [F terminal]` | 499 / 235,556 | **478 / 231,974** |
| ready rows | 12 / 2,944 | **14 / 4,621** |
| leaves | 96 / 24,416 | **79 / 21,809** |
| withheld (FR-0044 guard) | 3 | 3 |

The delta is exactly the 21 cut rows (**−21 nodes / −3,582 lines**). **Six rows become ready**,
all AF and all one to three edges above the cut:

| row readied | silo | by |
|---|---:|---|
| `AutomorphicForm.hasSum_whittakerCoefficient` | 1,156 | D (the box measure's `L²`/summability interface) |
| `AutomorphicForm.finite_setOf_exists_globalPoints_mul_mem_image_centreCutSiegelSetAmple` | 548 | A/B (the level lattice and the constituent closure) |
| `NumberField.TateGlobal.exists_isFundamentalDomain_principalIdeles_forall_exists_integrableOn_min_ideleNorm_pow` | 483 | C (compact quotient / integral structure) |
| `NumberField.AdeleRing.exists_finset_forall_mem_and_card_le_mul_prod_pow_of_isCompact` | 266 | C |
| `NumberField.AdelicLevel.exists_globalPoints_mul_mem_levelOne_rat` | 159 | B (the rational level row is the `levelOne` companion of the cut `finiteLevelOne` row) |
| `AutomorphicForm.isotypicCuspSubmodule_eq_bot_of_nonpos` | 40 | A |

That is **2,652 silo** of return, the set's opening for the next cut.

## 1. The cut

| # | row | silo | wire |
|---|---|---|---:|
| A1 | `AutomorphicForm.CuspidalSpectrum.isIsotypicCuspFormAt_of_mem_of_sub_mem_orthogonal` | 280 | 5 |
| A2 | `AutomorphicForm.CuspidalConstituent.isCuspSubrep_span_cyclic_and_mem_and_le` | 173 | |
| A3 | `AutomorphicForm.CuspidalSpectrum.exists_rightConv_ne_zero_of_ne_bot` | 125 | |
| A4 | `AutomorphicForm.CuspidalConstituent.eq_of_isCuspConstituent_of_exists_mem_ne_zero` | 33 | |
| A5 | `AutomorphicForm.IsIsotypicCuspFormAt.exists_smoothCuspRealizationAt_toFun_eq_of_ne_bot` | 30 | |
| B1 | `NumberField.AdelicLevel.exists_glFin_globalPoints_mul_mem_finiteLevelOne_rat` | 397 | 52 |
| B2 | `NumberField.AdelicLevel.diagOne_mul_archRealGLAt_unipotent_eq_and_stdAddChar_single_half` | 207 | |
| B3 | `NumberField.AdelicLevel.diagOne_eq_diagOne_mul_archRealLiftAt_mul_centralScalar` | 172 | |
| C1 | `IsDedekindDomain.HeightOneSpectrum.isAdicComplete_adicCompletionIntegers` | 111 | 12 |
| C2 | `IsDedekindDomain.FiniteAdeleRing.exists_ne_zero_forall_mul_apply_mem_adicCompletionIntegers_of_isCompact` | 52 | |
| C3 | `NumberField.AdeleRing.compactSpace_quotient_principalSubgroup` | 32 | |
| C4 | `NumberField.AdeleRing.exists_isOpen_inter_principalIdeles_eq_singleton` | 118 | |
| D1 | `NumberField.AdelicBox.exists_eq_sum_indicator_image_integralFiniteAdeles` | 483 | 70 |
| D2 | `NumberField.AdelicBox.absNorm_mul_measure_image_integralFiniteAdeles` | 229 | |
| D3 | `NumberField.AdelicBox.exists_ne_zero_forall_addChar_mul_eq_one` | 201 | |
| D4 | `NumberField.AdelicBox.integralFiniteAdeles_subset_closure_range_algebraMap_ringOfIntegers` | 109 | |
| D5 | `NumberField.AdelicBox.exists_denom_of_hasCompactSupport` | 70 | |
| D6 | `NumberField.AdelicBox.isLocallyConstant_and_hasCompactSupport_indicator_image_integralFiniteAdeles` | 44 | |
| D7 | `NumberField.AdelicBox.algebraMap_mem_image_integralFiniteAdeles_iff` | 41 | |
| E1 | `NumberField.AdelicHeight.exists_forall_mul_adelicHeight_le_adelicHeight_mul_of_isCompact` | 514 | 50 |
| E2 | `NumberField.AdelicHeight.adelicHeight_globalPoints_mul_of_apply_one_zero_eq_zero` | 161 | |

**The five stories.**

* **A** finishes the cuspidal-spectrum cluster SET-AF89 readied: the orthogonal-complement
  membership of an isotypic cusp form; the cyclic constituent spanned by the translates and
  right convolutions of one vector; the non-vanishing of a right convolution on the intersection
  of a level-invariant and an archimedean cut; the uniqueness of a constituent through a shared
  nonzero vector; and the smooth-cusp realization attached to a nonzero isotypic form.
* **B** is the adelic level layer's archimedean face: rational strong approximation into
  `finiteLevelOne N`; the commutation of `diagOne a` with the real unipotent subgroup, together
  with `stdAddChar`'s value `-1` at the half-characteristic; and the decomposition of `diagOne a`
  into a finite-level part, an archimedean lift and a central scalar.
* **C** is the integral/compact structure of `𝔸_F`: adic completeness of the local integer ring,
  a global denominator for a compact set of finite adèles, compactness of `𝔸_F ⧸ F`, and the
  discreteness of the principal idèles.
* **D** is the box `adelicBox F = infiniteBox F × integralFiniteAdeles`: an indicator
  decomposition over the box, the measure scaling `absNorm * measure (a • integralFiniteAdeles)`,
  the additive-character density, the closure of `𝓞 F` in the integral finite adèles, the
  denominator lemma for compactly supported functions, and the two local-constancy/support and
  membership criteria. It is the measure dictionary every `productionPins*` integral uses.
* **E** is the adelic height: its two-sided comparison under right multiplication by a compact
  set, and its invariance under the rational points with vanishing lower-left entry.

## 2. The homes and the manager's layer

| module | home / direction | manager's work |
|---|---|---|
| `AutomorphicForm/Adelic/Cusp/SpectrumConstituentClosure.lean` | new, above `ConstituentRightConv`, `IrreducibleSpine`, `SpectrumCarrierAPI`, `SpectrumTranslation`, `KfSmoothTensor`, `LeftCasimirTestFn`, `RightConvComm/Action`, `RightConvPreservation`, `TestFnTop` | five row statements + wires; the wire is 5 publics, all declared (the pins' engines are private) |
| `NumberTheory/AdelicLevel/ArchLevelLattice.lean` | new, above `AdelicLevel/{Level,StrongApproxRat}`, `IdeleSPartIntegral`, `UnimodularLift`, `AdelicTraceFin`, `ArchCasimir` | three row statements + wires; 52-public target |
| `NumberTheory/NumberField/IntegralAdeles.lean` | new, above `AdelicBox`, `AdelicLevel/Level`, `IdeleClass/Vocab`, `AdelicHaar/Adele` | four row statements + wires; 12-public target |
| `NumberTheory/AdelicBox/Measure.lean` | new, under the `AdelicBox` subject, above `AdelicBox`, `AdelicLevel/Level`, `FiniteIntegralConjugation`, `Siegel/CentreCutCover` | seven row statements + wires; 70-public target |
| `NumberTheory/AdelicHeight/Compactness.lean` | new, under `AdelicHeight/`, above `AdelicHeight`, `BoundedGenuineRealization`, `WindowedSiegel/Set` | two row statements + wires; 50-public target |

All five scaffolds elaborate and their rows check (`5 / 3 / 4 / 7 / 2` `ok` at scaffolding), and
all five are new files: no hub is edited and the five orders touch disjoint files.

**Duplication the advice found, and the decision.** `port_advise` reports five pin publics whose
port copies are `private` elsewhere and which the pins state publicly:
`continuous_of_mem_cuspKFiniteSubmodule` (private in `IrreducibleSpine`, needed by A3),
`exists_algebraMap_eq_of_mem_integralFiniteAdeles` (private in `LanglandsTunnell/WeightOneBound`, needed by B1),
`map_unipotentGL2` (private in `Cusp/LevelOneObstruction`, needed by B2),
`neg_mem_integralFiniteAdeles` (private in `FiniteIntegralConjugation`, needed by D1/D3), and the
height helpers (`entrySum`/`entryMax`/`archLower`/…, private or differently bound in
`AdelicHeight`/`WindowedSiegel/Set`). The decision is the pin's own shape: **declare them at the
pin's names in the new modules** and use the private copies' proofs as the bodies (they are the
pin's own duplicated prelude, public in the `S_` files, private in the `Def_`/other `S_` files);
no promotion and no cross-order edit. The one exception is a copy that is already public at the
pin's binders — then import it and let `scaffold_audit` credit the closure.

## 3. The orders

Orders in `lean/tmp/af90/WO.md` (untracked, like the earlier sets' order files), five orders,
disjoint files, five dispatches in parallel.

## 4. The forecast

The scaffolds are the measurement point: after them `needed` is **478 / 231,974**, ready
**14 / 4,621**, leaves **79 / 21,809**. Landing can only confirm those three cells, and the set's
return is the six readied rows of §0 (2,652 silo).

## 5. The gates (per order)

As SET-AF89 §5, unchanged: `check_port --force` at the order's wire count with `0 mismatch / 0
missing / 0 own`; `scaffold_audit` **complete**; `lake env lean -DautoImplicit=false
-DmaxHeartbeats=200000` silent, then one locked `lake build`; `#print axioms` on every row and the
largest engines; `dedup --within`; `move_dead`; a recorded heartbeat probe, never installed.

## 6. Risks

| # | risk | mitigation |
|---|---|---|
| 1 | B's 397 pin and D's 483 pin are the largest transcriptions (21 and 35 public declarations) | the pins' flattened preludes are transcribed once in each module; `port_advise` reports 26 importable substitutes for B and 10 for D, so the new math is smaller than the silo |
| 2 | A's five rows are short but their engine (the `W` subrepresentation and the `cuspSubcarrier` dictionary) is private in the pins | transcribe the private engines at the pin's names; A3 also needs the private `continuous_of_mem_cuspKFiniteSubmodule` |
| 3 | E's 514 pin has 46 public declarations, many with substitutes in `AdelicHeight` | import the substitutes; the remaining `entrySum`/`entryMax`/`archLower`/`archUpper` family is the pin's own spelling of `WindowedSiegel.localHeight`/`archHeight` and stays private |
| 4 | C's `compactSpace_quotient_principalSubgroup` and `exists_isOpen_inter_principalIdeles_eq_singleton` are topological inputs the port may not have assembled | both are leaves (0 graph premises); the pins' proofs are the authority, and the home imports the `IdeleClass/Vocab` and `AdelicHaar/Adele` modules |
| 5 | the tree's oleans can be stale (FR-0033/FR-0230) | each order builds its own dependencies first, one module per bounded call |
EOF

## 7. The landing (2026-11-20)

All five orders landed with no `sorry`, no heartbeat floor, no linter option, and no hub or existing
module edited. **5 new modules, 3,294 lines, 152 declarations (143 public + 9 private).**

| module | rows | lines | decls (pub/priv) | checker | audit | dedup | probe (silent / fails) |
|---|---|---:|---|---|---|---:|---|
| `AutomorphicForm/Adelic/Cusp/SpectrumConstituentClosure.lean` | A1–A5 | **652** | 13 (5/8) | **5 ok / 0 / 0** | complete (5 declared, 0 imported) | **0** | 60,000 / 30,000 |
| `NumberTheory/AdelicLevel/ArchLevelLattice.lean` | B1–B3 | **706** | 34 (34/0) | **34 ok / 0 / 0** | complete (52 wire, 12 imported) | **0** | 32,000 / 16,000 |
| `NumberTheory/NumberField/IntegralAdeles.lean` | C1–C4 | **341** | 12 (12/0) | **12 ok / 0 / 0** | complete (12 declared, 0 imported) | **0** | 20,000 / 10,000 |
| `NumberTheory/AdelicBox/Measure.lean` | D1–D7 | **924** | 44 (44/0) | **44 ok / 0 / 0** | complete (70 wire, 0 imported) | 5 (pins' own repeats) | 8,000 / 6,000 |
| `NumberTheory/AdelicHeight/Compactness.lean` | E1–E2 | **671** | 49 (48/1) | **48 ok / 0 / 0** | complete (50 wire, 2 imported) | 1 (pin's `main`/`solution`) | 8,000 / 4,000 |
| | **21** | **+3,294** | **152 (143/9)** | **143 ok, 0 mismatch, 0 missing, 0 own** | 5 complete | 6 pin-own | |

`move_dead` reads `0 declarations, 0 lines` on all five; every row and every probed engine is on
`[propext, Classical.choice, Quot.sound]`; the five modules build one at a time under the lock.

**Consumers** — one per order, each silent:

* `spec/AutomorphicFormSetAF90AConsumer.lean` — the orthogonal-complement membership row, then the
  realization row: a cusp form in the orthogonal complement of a closed cusp subrep is a smooth
  cusp realization's function.
* `spec/NumberFieldSetAF90BConsumer.lean` — rational strong approximation into `finiteLevelOne N`
  pushed one level down to `finiteLevelZero N`.
* `spec/NumberFieldSetAF90CConsumer.lean` — compact `𝔸_F ⧸ F` and discrete principal idèles, the
  adelic discreteness/cocompactness pair.
* `spec/NumberFieldSetAF90DConsumer.lean` — the box indicator's local constancy, compact support and
  scaled Haar measure, and its value at a principal adèle read through the arithmetic membership
  criterion.
* `spec/NumberFieldSetAF90EConsumer.lean` — the height comparison on a compact set survives rational
  left multiplication with vanishing lower-left entry.

### The decisions of the landing

1. **D's pin labels are renamed, with the two statement lines protected by `local notation`.**
   `LatKer0`/`LatIdx`/`LatDec` → `BoxKernel`/`BoxIndex`/`BoxDecomposition`; the two D1 statements
   that name `LatIdx.dBox` in their hashed text keep the pin's spelling through
   `local notation "LatIdx.dBox" => BoxIndex.dBox` (the AF89A `Faithful.lean` device), so no token
   survives in a declaration or namespace name and the checker stays at 44 ok.
2. **D's 44 declarations, not the wire's ≈66.** The three `S_` pins repeat one engine block each (26
   duplicated public entries) and fold seven `solution`s into the rows; the repeats are the pin's
   own, and the port declares each once. The five `dedup --within` clusters are exactly those
   repeated pairs; `move_dead` finds nothing dead.
3. **The FR-0237 collisions were real in D and E, not in A or C.** D's two "imported" credits were
   statement-different `AdelicLevel` lemmas and are declared here (so `imported` is 0); E's
   `rowMaxNorm_mul_le` credit is a different statement (the port's integrality form), so the pin's
   matrix form is carried as a private helper. A and C have no `imported` bucket at all.
4. **The pin's duplicated preludes are declared at the pin's names in the new modules** and are not
   promoted: `LevelCovering.exists_algebraMap_eq_of_mem_integralFiniteAdeles` (B1, body from the
   private copy in `LanglandsTunnell/WeightOneBound.lean`), `ArchLevel.map_unipotentGL2` (B2, from
   `Cusp/LevelOneObstruction.lean`), `neg_mem_integralFiniteAdeles` (D, with the pin's own body), and
   `continuous_of_mem_cuspKFiniteSubmodule` (A, re-proved). No existing module was edited.
5. **B needed one import the scaffold lacked** (`TateGlobal/IdeleNormValues` for the pin's public
   `map_diagOne`), recorded under `## Port deltas`; D added
   `Mathlib.Topology.LocallyConstant.Algebra` for `LocallyConstant.charFn`.

### The set's numbers

| figure | before (AF89) | after scaffolds | **after landing** | forecast |
|---|---:|---:|---:|---:|
| `needed [F terminal]` | 499 / 235,556 | 478 / 231,974 | **478 / 231,974** | 478 / 231,974 exact |
| ready rows | 12 / 2,944 | 14 / 4,621 | **14 / 4,621** | 14 / 4,621 exact |
| leaves | 96 / 24,416 | 79 / 21,809 | **79 / 21,809** | 79 / 21,809 exact |
| withheld | 3 | 3 | **3** | 3 exact |

The landing read equals the scaffold read, as for every set whose rows are all pre-declared. The
set's return is the six rows §0 readied — 2,652 silo, the largest the AF column has produced since
its definition-gate waves.

### Frictions this set produced

* **FR-0238** — `AdeleRing`/`InfiniteAdeleRing` are `def`s, so the pin's `rw`-into-`psiQ` scripts
  fail at implicit transparency; name the components with `set` and close through the named locals
  (FR-0219's class, on the two adele-ring abbreviations).
* **FR-0236 recurred** — A's six frozen binders (`hc`, `hd₁`, `hd`, `hcov`, `hσ`, `hirr`) are dead in
  the pins' own proofs and were hidden by the `sorry` bodies; spent with `have _ := …`, no rename.
* **FR-0237 recurred twice more** — D's two "imported" credits and E's `rowMaxNorm_mul_le` are
  last-name collisions on different statements; both are now declared or carried privately, and
  the reports name them.
* **FR-0231 recurred** — the pin's `ContinuousLinearMap.coe_sum'` is v4.34's `FunLike.coe_sum`
  (deprecated, warns unconditionally), proof-body only.
