# SET-AF81 — the Weyl-intertwining integral bound, and the Rankin–Selberg Euler polynomial

**Status: SCAFFOLDED-BY-WORKER, DISPATCHED (2026-11-14).** Read off the D–S shelf after SET-AF79/AF80: the
column's own rule, the two rows the last pair readied.

**2 rows / 620 silo** in **two new modules**, two orders.

| # | row | silo | lev | home |
|---|---|---:|---:|---|
| **A** | `AutomorphicForm.exists_pos_eventually_le_re_sub_one_half_mul_weylIntertwiningIntegral_one_of_nonneg_of_isArchKFinite_family` | 421 | 1/1 | new `AutomorphicForm/Adelic/WeylIntertwiningIntegralBound` |
| **B** | `LanglandsTunnell.RankinSelberg.exists_multipliable_differentiableOn_tprod_inv_eval_rsEulerPoly_of_norm_le_rpow` | 199 | 2/4 | new `LanglandsTunnell/RankinSelberg/EulerPolyProduct` |

## 0. The read

```bash
cd tools/deps
python3 frontier.py --ds --ready --include-leaves --rank-by silo --top 0 --json > build/shelf_after_af79_80.json
python3 frontier.py --selfcheck
```

| figure | value |
|---|---:|
| `needed [F terminal]` | **582 / 262,734** |
| ready rows, all namespaces | **21 / 4,877** |
| leaves, all namespaces | **140 / 36,013** |
| withheld by the FR-0044 guard | 4 / 831 |

These are exactly SET-AF79/AF80 §5's post-landing figures — the pair landed to the line, so this set opens
on their re-read. `--selfcheck` still FAILS on the fifteen MD-005 `ModularCurve.PhiGen` markers; no row cut
here cites one.

## 1. The rows

- **A** — for a *nonnegative* function on the adelic quotient whose archimedean part is `K`-finite, the real
  part of the Weyl-intertwining integral is eventually at least `(1/2 - ε)`-times the `L¹` mass along the
  unipotent orbit. The pin's file is 421 lines with **16 public declarations**, so the module is 16
  statements, not one headline: the two-sided estimate plus the pointwise, positivity and `K`-finiteness
  lemmas it is assembled from.
- **B** — the Rankin–Selberg Euler polynomial `rsEulerPoly`: its inverse is multiplicable and differentiable
  on `re s > 1/2` once `‖eval rsEulerPoly s‖ ≤ rpow` holds, the analytic half of the Rankin–Selberg
  Euler product. Five public declarations; the closest landed sibling is SET-AF79's
  `NumberTheory/LSeries/DedekindZetaEulerProduct.lean`, whose product/differentiability idiom is the model.

## 1.1 The shelf, quoted whole — every row cut or deferred

**The ready block: 21 rows / 4,877 silo — 2 cut (A, B), 19 deferred.**

| row | silo | lev | cut |
|---|---:|---:|---|
| `EisensteinGeneral.Piece.exists_forall_nonempty_factorizationDatum` | 890 | 3/5 | deferred (needs `AutomorphicForm/Adelic/WeilIntertwining`, not ported) |
| `WeierstrassCurve.natCard_torsionOrbit_and_exists_surjective_doubleCoset_of_char_two` | 697 | 1/1 | deferred (needs `IsCharTwoJNeZeroNF`, not ported) |
| `WeierstrassCurve.exists_isGalois_goodModel_inertia_faithful_of_two_ne_zero` | 599 | 1/4 | deferred |
| `GaloisRep.exists_isSemisimpleRepresentation_charpoly_map_eq_of_trace_det_frobenius_mem_range` | 495 | 1/1 | deferred |
| `MeasureTheory.exists_integral_conj_apply_smul_ne_zero_of_forall_norm_apply_eq_of_continuous` | 200 | 1/1 | deferred |
| `ValuationSubring.exists_aeval_div_eq_aeval_div_add_inv_pow_mul_add_aeval_inv` | 138 | 1/1 | deferred |
| `NumberField.TateGlobal.exists_isCompact_forall_eq_principal_mul_balanced_mul` | 120 | 1/2 | deferred |
| `AutomorphicForm.SmoothCuspRealizationAt.centralChar_eq_of_agreesAwayFromFinite` | 113 | 1/16 | deferred |
| `NumberField.AdelicHaar.isMulRightInvariant_of_isHaarMeasure_generalLinearGroup_infiniteAdeleRing` | 84 | 4/5 | deferred |
| `ModularForm.exists_gamma0_qExpansion_div_eq_E4_cube_div_discriminant` | 66 | 1/3 | deferred |
| `AlgebraicCurve.exists_placeMap_mapDomain_eq_ord_of_good_constantReduction` | 59 | 2/5 | deferred |
| `ModularCurve.exists_sum_smul_eq_of_isIntegralQExp_gamma1` | 36 | 1/3 | deferred |
| `ModularCurve.exists_coeffMap_diffQExp_x1FunctionFieldBar_eq_qExpansion` | 34 | 1/1 | deferred |
| `AutomorphicForm.SiegelCovering.centreCutSiegelSet_coversModCentre_rat` | 30 | 1/6 | deferred |
| `ModularCurve.rep_tateModule_jOne_comm` | 24 | 1/6 | deferred |

(The six rows cut by this set are the 421- and 199-line entries plus SET-AF82's four, which this set's
brief leaves to its sibling; the block above is the read *after* all six are ported, i.e. the shelf the
next scoping pass will see.)

**The leaves block: 140 rows / 36,013 silo — none cut, all deferred** (SET-AF79/AF80 §1.1's block).

## 2. The price and the homes

```bash
python3 port_advise.py --nodes <the six AF81+AF82 rows> --with-defs --json build/af81_82_advise.json
python3 port_plan.py --json build/af81_82_advise.json
```

| figure | value |
|---|---:|
| raw `S_` lines (both sets) | 1,292 |
| declaration lines | 1,168 |
| duplicate copies | 18 (port-once block: `algebraMap_mem_adicCompletionIntegers`, `valued_algebraMap` — all in already-ported `Definitions/` homes, so nothing to do) |
| **net new math lines** (both sets) | **564** |
| already in the port | **586 declaration lines / 369 declarations** (byte-identical substitutions, ≈3,518 pin lines not to re-prove) |

The 369 substitutions are the `Definitions/` surface these rows are stated against
(`Def_AutomorphicForm_*`: `ArchKFinite`, `BorelSubgroup`, `ConstantTerm`, `Induction`, `RowIsometry`,
`SmoothAutomorphicFnAt`, `WeylIntertwining`; `Def_NumberField_AdelicBox/AdelicHaar/AdelicLevel`;
`Def_LanglandsTunnell_RankinSelbergEuler`) — all already homed, so **no `Def_` work for these six rows**,
unlike SET-AF80's row A. 17 further `port_advise` "substitutions" are the parser's type-only `def` matches
(`rationalCentre ↔ adelicUnipotent`, `IsKfSmooth ↔ IsArchKFinite`, …): read, not applied.

## 3. The orders, and the method change

| order | row | content | public decls |
|---|---|---|---:|
| `WORKORDER-AF81A` | A | ≈350 | 16 |
| `WORKORDER-AF81B` | B | ≈150 | 5 |

Both orders are in `lean/tmp/af81/WO.md`. **The scaffolding is the worker's this time**, in a fixed
three-step discipline stated in the order: create the module and its header, transcribe every public
declaration of the pin verbatim with `sorry` bodies, prove `check_port --force` is `N ok / 0 mismatch /
0 missing`, and only then fill bodies. The reason is recorded rather than hidden — this session's context
is spent, and the scaffolding failure modes of the last four sets were *manager* failures (SET-AF75's A3
omission, SET-AF78's missing row statement), both of which the checker cannot see and the new audit below
can.

**The audit is the counter-measure.** `tools/deps/scaffold_audit.py <module>` compares a module against the
public surface of its own `spec-pin:` wire and classifies every pin public declaration as *declared here*,
*satisfied by the import closure* (the SET-AF79 port-once shape) or **absent**. It is run on every module
this wave lands; on the twenty modules of this session it reports one real gap
(`CARRY-FORWARD.md`: the unported tail of `Def_NumberField_PrimeNormSums`) and a set of intended folds and
substitutions, each named. A worker's `check_port` line alone cannot distinguish those cases.

## 4. The shelf effect

Forecast **measured with `--port`** on all six rows of AF81+AF82 (both sets open on this read):

| figure | §0 | forecast (AF81 + AF82) |
|---|---:|---:|
| `needed [F terminal]` | 582 / 262,734 | **576 / 261,442** |
| ready rows | 21 / 4,877 | **15 / 3,585** |
| leaves | 140 / 36,013 | 140 / 36,013 |

**No row is readied.** This is the first set pair in the wave whose cut returns nothing: the six rows are
the last of the "cheap ready" shelf, and what remains (890, 697, 599, 495) is either behind a definition
layer the port does not have or needs its own topic. The next scoping pass should therefore open on the
*leaves* block again — the twelve AdelicFourier rows were the last leaves cut, and 140 remain.

## 5. The landing

Both rows in, no `sorry`, two new modules, and the first order of the pair to use the delegated-scaffold
discipline end to end.

| file | row | lines | decls | checker | axioms |
|---|---|---:|---:|---|---|
| `AutomorphicForm/Adelic/WeylIntertwiningIntegralBound.lean` | A | **474** | 16 | **16 ok / 0 / 0** | clean (5 checked) |
| `LanglandsTunnell/RankinSelberg/EulerPolyProduct.lean` | B | **256** | 6 | **6 ok / 0 / 0** | clean |

Consumers `spec/AutomorphicFormSetAF81AConsumer.lean` (5 zones) and `spec/LanglandsTunnellSetAF81BConsumer.lean`
(201 lines, 4 zones): 0 errors, 0 warnings each. `dedup --within`: 0 clusters in A, **1 in B — the pin's own
`main`/`solution` pair**, which FR-0221 requires (the row's statement at the row's name and the engine at the
pin's); `move_dead`: 0 in both.

**Heartbeat floors**: A is silent at 100 000 and fails at 50 000 (the engine's closing `nlinarith`), so the
floor is bounded to (50 k, 100 k], ≈2× headroom — recorded as a bound, not a number. B's floor probe (all
proofs `sorry`) is silent at the cap, i.e. there is no statement-side cost at all.

### What the delegated scaffolds produced, and what the audit said

| module | pin publics on the wire | declared | import closure | verdict |
|---|---:|---:|---:|---|
| `WeylIntertwiningIntegralBound` | 16 | 16 | 2 | **complete** (one `RENAMED?`: the pin's `gl_ext`, renamed because `AutomorphicForm.gl_ext` already exists with a different statement) |
| `EulerPolyProduct` | 15 | 6 | 0 | **complete** modulo the `Def_` layer (below) |

Two things went *right* that the briefing had to teach: both workers put the statements in first and ran the
checker before writing a body (the checker line is identical at scaffold and at final in both reports — the
statements never drifted), and both dropped the label namespaces. One went wrong in a way worth recording:
order B discovered on arrival that `rsEulerPoly` was ported nowhere, and homed the pin's `def` **inside the
row module** — correct and minimal, but it left eight declarations of that same `Def_` file unported.

### The two definition layers, completed rather than deferred

`scaffold_audit.py` (FR-0222) reported both partial `Def_` transcriptions — 20 declarations behind
`PrimeNormSums`, 8 behind the Rankin–Selberg Euler data. The manager first recorded them in
`CARRY-FORWARD.md`, then (on the reviewer's instruction) **completed them**: `Definitions/Def_NumberField_PrimeNormSums`
is now ported whole (`PrimeNormSums.lean`, **32 ok**), and `Definitions/Def_LanglandsTunnell_HonestLDatum`
(the `LDatum` structure and its eight defs) plus `Definitions/Def_LanglandsTunnell_RankinSelbergEuler` (the
induced Euler factors and `rsDatum`) are new modules `LanglandsTunnell/HonestLDatum.lean` (**14 ok**) and
`LanglandsTunnell/RankinSelberg/Euler.lean` (**9 ok**), which `EulerPolyProduct` now imports instead of
carrying its own `rsEulerPoly` (the row module drops to **5 ok** — its own five declarations — and its
`Definitions/` wire is gone). One worker's order (`lean/tmp/fixdefs/WO-complete-defs.md`) filled the 20
bodies, made the `Ideal.inertiaDeg'` → `inertiaDeg` call compile, and rewired the row module; the
acceptance test was `scaffold_audit.py`, which now prints **complete** for all three definition modules.
The two `CARRY-FORWARD.md` entries written during the audit were **deleted** in the same touch — they are
no longer true, and a stale deferral note is worse than none.

### The set's numbers

| figure | before | **after** | forecast (joint with AF82) |
|---|---:|---:|---:|
| `needed [F terminal]` | 582 / 262,734 | **576 / 261,442** | 576 / 261,442 |
| ready rows | 21 / 4,877 | **15 / 3,585** | 15 / 3,585 |
| leaves | 140 / 36,013 | 140 / 36,013 | 140 / 36,013 |

Both rows were cut from the ready block, and the block's loss of six rows against no gain is the honest
shape of this pair: the cheap ready shelf is exhausted.
