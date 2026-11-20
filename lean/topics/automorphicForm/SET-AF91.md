# SET-AF91 — Whittaker summability, ample-window finiteness, the Tate fundamental domain, the adelic lattice, and the automorphic tail

**Status: LANDED (2026-11-20).** The third cut of the session, from the
ready block SET-AF90 readied plus the column's remaining cheap leaves. **11 rows / 3,088 silo** in
five orders and six new modules (order E carries two files); no definition gate (every pin's own
`Definitions/` imports is ported — the two mathlib `Def_` shims the Whittaker pin names are the
ported `LinearAlgebra/Countable.lean` and mathlib's `RestrictedProduct`).

| # | order | rows | silo | module | wire |
|---|---|---|---:|---|---:|
| A | summability of the Whittaker coefficient | 1 | 1,156 | `AutomorphicForm/Adelic/WhittakerSum.lean` (new) | 38 |
| B | finiteness of the rational points in an ample Siegel window | 1 | 548 | `AutomorphicForm/Adelic/Siegel/AmpleFiniteness.lean` (new) | 20 |
| C | the principal-idèle fundamental domain of the min-norm integral | 1 | 483 | `NumberTheory/NumberField/TateGlobal/FundamentalDomain.lean` (new) | 20 |
| D | counting, the level-one lattice, and the finite-adelic trace | 3 | 691 | `NumberTheory/AdelicLevel/LatticeCounting.lean` (new) | 15 |
| E | the automorphic API tail | 6 | 210 | `AutomorphicForm/Adelic/Cusp/IsotypicVanishing.lean`, `AutomorphicForm/Adelic/RankinSelbergSection.lean` (new) | 4 + 8 |

## 0. The read

```bash
cd tools/deps
python3 frontier.py --ds --ready --include-leaves --rank-by silo --top 0 --json > build/shelf_af91_read.json
```

| figure | before (AF90 landing) | after this set's scaffolds |
|---|---:|---:|
| `needed [F terminal]` | 478 / 231,974 | **466 / 228,886** |
| ready rows | 14 / 4,621 | **19 / 8,275** |
| leaves | 79 / 21,809 | **74 / 21,398** |
| withheld (FR-0044 guard) | 3 | 3 |

The delta is exactly the 11 cut rows (**−11 nodes / −3,088 lines**). **Twelve rows become ready**,
the largest return any set in this session has produced — **6,331 silo**:

| row readied | silo | by |
|---|---:|---|
| `AutomorphicForm.exists_forall_setLIntegral_nnnorm_sq_le_mul_archHeight_pow_mul_setLIntegral_of_isLsXiFunction_of_coversModCentre` | 1,945 | B + C |
| `AutomorphicForm.setLIntegral_nnnorm_sq_le_mul_archHeight_pow_mul_setLIntegral_of_isLsXiFunction_of_coversModCentre` | 1,942 | B + C |
| `AutomorphicForm.exists_forall_setLIntegral_nnnorm_sq_le_mul_archHeight_pow_mul_setLIntegral_of_isLsXiFunction_of_isFundamentalDomain` | 1,413 | C |
| `AutomorphicForm.exists_whittakerCoefficient_one_ne_zero` | 253 | A |
| `AutomorphicForm.integral_mul_conj_eq_tsum_whittakerCoefficient_mul_conj` | 224 | A |
| `NumberField.StandardAddChar.psiLocal_eq_psiLocal_trace` | 154 | D (trace) |
| `NumberField.Idele.idelicHaar_inter_setOf_ideleNorm_mem_Icc_pos_and_lt_top` | 149 | D |
| `AutomorphicForm.exists_forall_ncard_setOf_globalPoints_mul_mem_iUnion_centreCutSiegelSetAmple_le` | 91 | B |
| `AutomorphicForm.ext_of_invariant_of_forall_glFin_eq_one_rat` | 72 | B |
| `AutomorphicForm.exists_mem_productionPinsCompact_U_mul_eq_rat` | 63 | D |
| `AutomorphicForm.IsCuspidalFn.add` / `.smul` | 14 / 11 | E |

The three `setLIntegral`/`archHeight` rows are the L²-bound family of the `LsXi`/Petersson arguments:
together 5,300 silo, and they are the next cut's centre of gravity.

## 1. The cut

| # | row | silo | wire |
|---|---|---|---:|
| A1 | `AutomorphicForm.hasSum_whittakerCoefficient` | 1,156 | 38 |
| B1 | `AutomorphicForm.finite_setOf_exists_globalPoints_mul_mem_image_centreCutSiegelSetAmple` | 548 | 20 |
| C1 | `NumberField.TateGlobal.exists_isFundamentalDomain_principalIdeles_forall_exists_integrableOn_min_ideleNorm_pow` | 483 | 20 |
| D1 | `NumberField.AdeleRing.exists_finset_forall_mem_and_card_le_mul_prod_pow_of_isCompact` | 266 | 15 |
| D2 | `NumberField.AdelicLevel.exists_globalPoints_mul_mem_levelOne_rat` | 159 | |
| D3 | `NumberField.AdelicTrace.traceFinHom_apply_eq_sum_trace` | 266 | |
| E1 | `AutomorphicForm.isotypicCuspSubmodule_eq_bot_of_nonpos` | 40 | 4 |
| E2 | `AutomorphicForm.eq_zero_of_isCuspAutomorphicFnAt_productionPinsOf_of_coversModCentre_of_forall_mem_eq_zero` | 25 | |
| E3 | `AutomorphicForm.constantTerm_add` | 13 | |
| E4 | `AutomorphicForm.constantTerm_smul` | 11 | |
| E5 | `AutomorphicForm.RankinSelberg.section_diagOne_mul_eq_ideleNorm_cpow_mul_of_isInducedSection_etaFst_etaSnd` | 66 | 8 |
| E6 | `AutomorphicForm.exists_continuous_monoidHom_matrix_apply_ne_one_of_ne_one` | 55 | |

**The five stories.**

* **A** is the Poisson/Bessel summation input of the Whittaker development: a continuous function
  `x ↦ φ (unipotentGL2 x * g)` whose Whittaker coefficients are summable has `φ g` as their sum.
  The pin is a 1,156-line flattened file with 38 publics — the largest single row taken in this
  session — and its engine is the coefficient's Bessel/majorant analysis.
* **B** is lattice-point finiteness in an ample centre-cut Siegel window: for `x` with all
  archimedean components row isometries, only finitely many rational `γ` have a translate in the
  window over `x`. Its 20 publics are the window's arithmetic.
* **C** is the Tate global integral's fundamental-domain lemma: a fundamental domain for the
  principal idèles on which every function bounded by a power of the min idèle norm is integrable.
* **D** is the adelic lattice in three faces: a counting bound for a compact set inside a scaled box
  (the row AF90's compact-denominator lemma readies), the `levelOne` companion of AF90's
  `finiteLevelOne` approximation, and the finite trace's decomposition into local traces.
* **E** is the API tail the cusp/constant-term arguments call: the isotypic submodule at a
  nonpositive parameter, the cover-vanishing criterion, the constant term's additivity and
  homogeneity, the Rankin–Selberg section's diagonal scaling, and the separation of a continuous
  monoid homomorphism by a matrix entry.

## 2. The homes and the manager's layer

| module | home / direction | manager's work |
|---|---|---|
| `AutomorphicForm/Adelic/WhittakerSum.lean` | new, beside `WhittakerCoefficient`; imports `WhittakerCoefficient`, `AdelicBox`, AF90 `IntegralAdeles`, AF89 `Faithful`, `LinearAlgebra/Countable` | row statement (the pin's 38-public wire, 1 declared); no definition work |
| `AutomorphicForm/Adelic/Siegel/AmpleFiniteness.lean` | new, under `Siegel/`; imports `CentreCutSiegelSetAmple`, `RowIsometry`, `LsXi`, `AdelicHeight` + AF90 `Compactness`, `Siegel/WindowCriterion`, `AdelicDiscreteness` | row statement; 20-public target |
| `NumberTheory/NumberField/TateGlobal/FundamentalDomain.lean` | new, under `TateGlobal/`; imports `TateGlobal/Defs`, `IdeleClass/Vocab`, `TateGlobalNormSection`, `TateGlobalCompactness`, `GroupTheory/ExactFundamentalDomain`, AF90 `IntegralAdeles` | row statement; 20-public target |
| `NumberTheory/AdelicLevel/LatticeCounting.lean` | new, under `AdelicLevel/`; imports `AdelicBox`, `Level`, `AdelicTraceFin`, `CompletionBaseChange`, AF90 `Siegel/Reduction`, `IntegralAdeles` | three row statements; 15-public target |
| `AutomorphicForm/Adelic/Cusp/IsotypicVanishing.lean` | new, above `Constituent`/`ProductionPinsGeneral`/`CuspUnrealizable`/`Siegel/WindowCriterion` | four row statements (the wire is 4, all declared); proofs only |
| `AutomorphicForm/Adelic/RankinSelbergSection.lean` | new, above the section algebra (`WhittakerCoefficient`, `ArchType`, `ProductionPinsGeneral`, `AdelicMaximalCompact`, `IdeleProductMeasure`, `IsotypicCuspSpace`, `InducedSectionSpan`) | two row statements; 8-public target |

All six scaffolds elaborate and their rows check (`1 / 1 / 1 / 3 / 4 / 2` `ok` at scaffolding); no
hub is edited and the five orders touch disjoint files (E's two files are one order).

**One statement correction the manager already made.** The `constantTerm_add`/`_smul` pins state the
lemma at `(μ : Measure Q)` with unqualified `constantTerm`/`Integrable`, while the *wrapper* writes
`MeasureTheory.Measure`/`AutomorphicForm.constantTerm`; the checker's normaliser does not align the
qualified spelling, so both rows are stated in the pin's text in `IsotypicVanishing.lean` (that is
why check_port reads 4 ok there, not 2).

## 3. The orders

Orders in `lean/tmp/af91/WO.md` (untracked, like the earlier sets' order files), five orders,
disjoint files, five dispatches in parallel.

## 4. The forecast

The scaffolds are the measurement point: after them `needed` is **466 / 228,886**, ready
**19 / 8,275**, leaves **74 / 21,398**. Landing can only confirm those cells, and the set's return is
the twelve readied rows of §0 (**6,331 silo**).

## 5. The gates (per order)

As SET-AF89/AF90 §5, unchanged: `check_port --force` with `0 mismatch / 0 missing / 0 own`;
`scaffold_audit` **complete**; `lake env lean -DautoImplicit=false -DmaxHeartbeats=200000` silent,
then one locked `lake build`; `#print axioms` on every row and the largest engines; `dedup --within`;
`move_dead`; a recorded heartbeat probe, never installed.

## 6. Risks

| # | risk | mitigation |
|---|---|---|
| 1 | A is the largest row taken so far (1,156 silo, 38 publics) | its wire is flattened; transcribe the 37 remaining publics at the pin's names and prove; the engine's Bessel/majorant is self-contained in the pin |
| 2 | B's 20 publics are window arithmetic with several already-ported pieces (`isCompact_centreCutSiegelSet_inter_heightCap`, the AF90 height comparison) | import the ported copies; the pin's `finite_setOf_algebraMap_mem_of_isCompact` is in `AdelicDiscreteness` |
| 3 | C's premise `Subgroup.exists_exact_fundamental_domain_of_secondCountableTopology` is a mathlib supplement | it is ported at `GroupTheory/ExactFundamentalDomain.lean`; the row's own 20 publics are the tempered/shell-measure block |
| 4 | D's three rows are three namespaces in one module | one order, one file; the rows share only the `IntegralAdeles` import |
| 5 | E's four `IsotypicVanishing` rows are the wire's `solution`s (the pins' engines are private) | transcribe the private engines too; the two `constantTerm` rows are stated in the pin's text, not the wrapper's |

## 7. The landing (2026-11-20)

All five orders landed with no `sorry`, no heartbeat floor, no linter option, and no hub or existing
module edited. **6 new modules, 3,275 lines, 140 declaration commands (105 public + 35 private).**

| module | rows | lines | decls (pub/priv) | checker | audit | dedup | probe (silent / fails) |
|---|---|---:|---|---|---|---:|---|
| `AutomorphicForm/Adelic/WhittakerSum.lean` | A1 | **1,161** | 38 (38/0) | **38 ok / 0 / 0** | complete (38 wire, 0 imported) | 2 (pin's own pairs) | 30,000 / 20,000 |
| `AutomorphicForm/Adelic/Siegel/AmpleFiniteness.lean` | B1 | **612** | 20 (20/0) | **20 ok / 0 / 0** | complete (20 wire, 0 imported) | 1 (pin's `main`/`solution`) | 175,000 / 87,500 |
| `NumberTheory/NumberField/TateGlobal/FundamentalDomain.lean` | C1 | **523** | 20 (20/0) | **20 ok / 0 / 0** | complete (20 wire, 0 imported) | **0** | 12,000 / 6,000 |
| `NumberTheory/AdelicLevel/LatticeCounting.lean` | D1–D3 | **728** | 50 (15/35) | **15 ok / 0 / 0** | complete (15 wire, 0 imported) | 1 (pin's `main`/`solution`) | 25,000 / 12,500 |
| `AutomorphicForm/Adelic/Cusp/IsotypicVanishing.lean` | E1–E4 | **106** | 4 (4/0) | **4 ok / 0 / 0** | complete (4 wire, 0 imported) | **0** | 1,000 / 500 |
| `AutomorphicForm/Adelic/RankinSelbergSection.lean` | E5–E6 | **145** | 8 (8/0) | **8 ok / 0 / 0** | complete (8 wire, 0 imported) | **0** | 2,000 / 1,000 |
| | **11** | **+3,275** | **140 (105/35)** | **105 ok, 0 mismatch, 0 missing, 0 own** | 6 complete | 4 pin-own | |

`move_dead` reads `0 declarations, 0 lines` on all six; every row and every probed engine is on
`[propext, Classical.choice, Quot.sound]`; the six modules build one at a time under the lock.

**Consumers** — one per order, each silent:

* `spec/AutomorphicFormSetAF91AConsumer.lean` — the Whittaker expansion as a `tsum` identity.
* `spec/AutomorphicFormSetAF91BConsumer.lean` — the finite window points as an explicit `Finset`.
* `spec/NumberFieldSetAF91CConsumer.lean` — the fundamental domain at a prescribed growth rate `r`.
* `spec/NumberFieldSetAF91DConsumer.lean` — the box-counting finset paired with the finiteness of
  the points it covers.
* `spec/AutomorphicFormSetAF91EConsumer.lean` — constant-term additivity and homogeneity composed on
  `c·f₁ + f₂`.

### The decisions of the landing

1. **A's row moved to the end of the module.** The pin puts its engine `innerSolution` (`:1060`)
   before its `solution` (`:1140`); the scaffold had the row at the top, and Lean has no forward
   references, so the proved row follows the engine. Name, visibility and statement are byte-identical
   and the checker/audit are position-blind (FR-0239).
2. **The scaffold import lists were short in A, C, D and E.** A needed `AdelicDiscreteness`,
   `GlobalAddChar/Circle` and `Mathlib.MeasureTheory.Function.AEEqOfIntegral`; C needed
   `TateGlobalContinuousIdeleNorm`; D needed AF90's `ArchLevelLattice` (the `finiteLevelOne` row);
   E needed `RationalCentreHaar` and `SpectrumConstituentClosure`. Every line was measured with
   `premise_imports.py`/the compiler and recorded under `## Port deltas` — FR-0229's recurring class,
   now at seven sites in this set.
3. **FR-0237's collisions were real in B and C.** B's credited `main` was
   `AdelicHeight.main` and C's credited `shell`/`measurableSet_shell` were the zeta shell; in both
   cases the pin's declaration is different, so the module ends at its full wire count (20 each)
   rather than the ≈19/≈18 the raw closure arithmetic suggested. D and E had no `imported` bucket
   at all.
4. **The pin's own duplicated pairs stay.** A's `innerSolution`/row and
   `integrable_cond_adelicBox`/`integrable_cond_of_continuous`, B's and D's `main`/`solution` pairs
   are the pins' own engine/row duplication; each is declared once at each pin name with consumers,
   and the four `dedup --within` clusters are exactly those pairs (nothing removable).
5. **The `constantTerm` rows keep the pin's unqualified statement text** (`Measure Q`, `constantTerm`,
   `Integrable`), not the wrapper's qualified spelling — the checker's normaliser does not align the
   two, and the scaffold already read 4 ok as a result.

### The set's numbers

| figure | before (AF90) | after scaffolds | **after landing** | forecast |
|---|---:|---:|---:|---:|
| `needed [F terminal]` | 478 / 231,974 | 466 / 228,886 | **466 / 228,886** | 466 / 228,886 exact |
| ready rows | 14 / 4,621 | 19 / 8,275 | **19 / 8,275** | 19 / 8,275 exact |
| leaves | 79 / 21,809 | 74 / 21,398 | **74 / 21,398** | 74 / 21,398 exact |
| withheld | 3 | 3 | **3** | 3 exact |

The landing read equals the scaffold read, and the set's return is the twelve readied rows of §0 —
**6,331 silo**, the largest of the session, led by the three `setLIntegral`/`archHeight` L² bounds
(1,945 + 1,942 + 1,413 = 5,300) that B and C unlocked together.

### Frictions this set produced

* **FR-0239** — a scaffolded row cannot always stay at the top of its module: when the pin's
  `solution` follows its engine, the proved row must follow it too (statement byte-identical; the
  instruments are position-blind).
* **FR-0229 recurred at seven sites** — A (3), C (1), D (1), E (2) import lines the scaffolds lacked,
  each measured and recorded. The scaffold's imports are a lower bound, not a closure.
* **FR-0237 recurred twice** — B's `main` and C's `shell` credits were statement-different namesakes;
  both are declared, so the two modules end at 20, not 19/18.
* **FR-0231/FR-0235 recurred** — `Set.restrict`→`domRestrict`, `if_pos`/`if_neg`→`ite_eq_left`/`ite_eq_right`,
  the quotient second-countability rename (`RestrictedProduct.secondCountableTopology` →
  `NumberField.AdelicCountability.secondCountableTopology_restrictedProduct`), and the `haveI`/`letI`
  spelling; all proof-side and statement-neutral.
