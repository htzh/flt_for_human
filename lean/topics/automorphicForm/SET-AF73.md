# SET-AF73 — integration on the Haar quotient

**Status: LANDED (2026-11-14).** Read off the D–S shelf after SET-AF71/AF72 with the recipe in
[../deligneSerre/TOPIC-scoping-a-ds-set.md](../deligneSerre/TOPIC-scoping-a-ds-set.md). The seventy-third
set of the column, and a **one-row leaves set**: the row sits in the leaves block (all its `Def_` and
premise vocabulary is ported) and its `Def_` coverage is checked complete by the manager's scan.

**1 row / 616 silo / ≈520 net** in **one new module**, one order.

| # | row | silo | lev | home |
|---|---|---:|---:|---|
| **A** | `HaarQuotient.lintegral_eq_lintegral_lintegral_mul_out` | 616 | 2/48 | new `MeasureTheory/HaarQuotientFubini` |

The row is the Fubini identity of the Haar quotient: integrating over `H \ G` against the quotient
measure equals the iterated integral over the subgroup and the ambient Haar measure. It is the measure
theoretic floor the analytic `AutomorphicForm` rows integrate against, and its own engine (orbit slices,
weights, the fundamental-domain and `D2` sections) is one subject.

## 0. The read

```bash
cd tools/deps
python3 frontier.py --ds --ready --include-leaves --rank-by silo --top 0 --json > build/shelf31.json
python3 frontier.py --selfcheck
```

| figure | value |
|---|---:|
| `needed [F terminal]` | **610 / 270,200** |
| ready rows, all namespaces | **22 / 4,790** |
| leaves, all namespaces | **157 / 40,497** |
| `HaarQuotient` demand | **5 / 1,323** |
| withheld by the FR-0044 guard | 4 / 831 |

`needed` is exactly SET-AF71/AF72 §5's post-landing figure; the read was **taken on the cleaned tree**
(FR-0215 — the abandoned scaffolds of the previous wave were deleted before this read). `--selfcheck`
still FAILS on MD-005's fifteen rows; no row cut here cites any of them.

## 1.1 The shelf, quoted whole — every row cut or deferred

**The ready block: 22 rows / 4,790 silo — none cut, all deferred** (unchanged from SET-AF71 §1.1 apart
from the two rows that set and AF72 readied).

| row | silo | lev | cut |
|---|---:|---:|---|
| `EisensteinGeneral.Piece.exists_forall_nonempty_factorizationDatum` | 890 | 3/5 | deferred |
| `WeierstrassCurve.natCard_torsionOrbit_and_exists_surjective_doubleCoset_of_char_two` | 697 | 1/1 | deferred |
| `WeierstrassCurve.exists_isGalois_goodModel_inertia_faithful_of_two_ne_zero` | 599 | 1/4 | deferred |
| `GaloisRep.exists_isSemisimpleRepresentation_charpoly_map_eq_of_trace_det_frobenius_mem_range` | 495 | 1/1 | deferred |
| `AutomorphicForm.exists_finset_forall_exists_mem_valued_eq_max_and_contentHomFin_mul_sq_eq` | 333 | 1/1 | deferred |
| `LanglandsTunnell.TateLocal.integral_comp_inv_eq_integral_modulus_inv_sq_mul_adicCompletion` | 305 | 1/7 | deferred |
| `MeasureTheory.exists_integral_conj_apply_smul_ne_zero_of_forall_norm_apply_eq_of_continuous` | 200 | 1/1 | deferred |
| `AutomorphicForm.lintegral_rationalCentreUnipotentHaar_comp_heckeGen_mul_centralScalar_conj` | 179 | 1/1 | deferred |
| `ValuationSubring.exists_aeval_div_eq_aeval_div_add_inv_pow_mul_add_aeval_inv` | 138 | 1/1 | deferred |
| `LanglandsTunnell.dirichletIdeleChar_mul_modulus_det_gen` | 128 | 2/2 | deferred |
| `NumberField.TateGlobal.exists_isCompact_forall_eq_principal_mul_balanced_mul` | 120 | 1/2 | deferred |
| `AutomorphicForm.SmoothCuspRealizationAt.centralChar_eq_of_agreesAwayFromFinite` | 113 | 1/16 | deferred |
| `AutomorphicForm.constantTerm_adelicBox_globalPoints_mul_of_mem_borelSubgroup` | 104 | 1/15 | deferred |
| `LanglandsTunnell.TateLocal.measureReal_setOf_valued_le_exp` | 100 | 1/13 | deferred |
| `NumberField.AdelicHaar.isMulRightInvariant_of_isHaarMeasure_generalLinearGroup_infiniteAdeleRing` | 84 | 4/5 | deferred |
| `ModularForm.exists_gamma0_qExpansion_div_eq_E4_cube_div_discriminant` | 66 | 1/3 | deferred |
| `AlgebraicCurve.exists_placeMap_mapDomain_eq_ord_of_good_constantReduction` | 59 | 2/5 | deferred |
| `AutomorphicForm.isotypicCuspSubmodule_bot_eq_bot_of_productionPinsOf` | 56 | 3/5 | deferred |
| `ModularCurve.exists_sum_smul_eq_of_isIntegralQExp_gamma1` | 36 | 1/3 | deferred |
| `ModularCurve.exists_coeffMap_diffQExp_x1FunctionFieldBar_eq_qExpansion` | 34 | 1/1 | deferred |
| `AutomorphicForm.SiegelCovering.centreCutSiegelSet_coversModCentre_rat` | 30 | 1/6 | deferred |
| `ModularCurve.rep_tateModule_jOne_comm` | 24 | 1/6 | deferred |

**The leaves block: 157 rows / 40,497 silo — 1 cut (A), 156 deferred.** Its top:

| row | silo | lev | cut |
|---|---:|---:|---|
| `M4aTorus.completedRayL_fe` | 12126 | 1/2 | deferred |
| `NumberField.exists_continuousOn_exp_eq_rayClassLSeries` | 684 | 1/2 | deferred |
| `EisensteinGeneral.Piece.exists_summable_majorant_of_lattice_vanishing` | 666 | 1/1 | deferred |
| `AutomorphicForm.CuspidalConstituent.exists_forall_le_archTypeSubmoduleAt_of_isSimple_of_le_iSup` | 646 | 2/4 | deferred |
| `MeasureTheory.exists_continuous_convolution_self_eq_forall_integral_smul_isotypic` | 626 | 1/1 | deferred |
| `HaarQuotient.lintegral_eq_lintegral_lintegral_mul_out` | 616 | 2/48 | **cut AF73** |
| `NumberField.multipliable_differentiableOn_tprod_ne_zero_eulerProduct_of_norm_le_one` | 600 | 11/40 | deferred |
| `LocalNewvector.AdelicSpan.exists_mem_span_fixed_padicK1_of_fixedSubmodule_padicK1_ne_bot_of_apply_mul_finEmbed_eq` | 589 | 1/1 | deferred |
| `AutomorphicForm.exists_upperTriangular_globalPoints_mul_mul_scalar_mul_finIdeleDiag_inv_mem_finiteIntegralGL2` | 587 | 1/1 | deferred |
| `AutomorphicForm.exists_sum_prod_mul_of_rightTranslatesSpanFinite` | 576 | 2/2 | deferred |
| `NumberField.AdelicHeight.exists_forall_mul_adelicHeight_le_adelicHeight_mul_of_isCompact` | 514 | 1/33 | deferred |
| `LanglandsTunnell.isBoundedOnSiegelWindows_weightOneLift` | 501 | 2/2 | deferred |
| `WeierstrassCurve.finite_stabilizer_and_natCard_le_of_j` | 496 | 1/3 | deferred |
| `NumberField.AdelicBox.exists_eq_sum_indicator_image_integralFiniteAdeles` | 483 | 3/4 | deferred |
| `TateCurve.point_mul_eq_add_of_norm_le_one` | 471 | 1/1 | deferred |
| `LanglandsTunnell.exists_heckeCosetSystem_productionPinsCompact_of_not_dvd` | 446 | 1/2 | deferred |
| `AutomorphicForm.exists_depth_forall_apply_mul_lowerUnipotentGL2_eq_of_sum_translate` | 445 | 1/2 | deferred |
| `AutomorphicForm.WindowedSiegel.exists_forall_apply_one_zero_eq_zero_of_inv_mul_globalPoints_mul_mul_centralScalar_mem` | 386 | 3/4 | deferred |
| `AutomorphicForm.exists_norm_a_le_absNorm_rpow_and_norm_b_le_of_smoothCuspRealizationAt_of_peterssonPairing` | 384 | 1/2 | deferred |
| `NumberField.Idele.lintegral_mul_prod_ord_sPartMeasure_eq_lintegral_sPartMeasure_empty_mul_prod_tsum` | 381 | 1/4 | deferred |

The remaining 136 rows (≈ 36,000 silo) are deferred unchanged from SET-AF70 §1.1 — the `AutomorphicForm`
`CuspidalConstituent`/`WindowedSiegel` group, `M4aTorus.completedRayL_fe` (12,126, whose `Def_` layer is
not ported), the `NumberField` Euler-product leaves and the `MeasureTheory`/`TateCurve`/`WeierstrassCurve`
residue.

## 2. The price and the home

| module | rows | scaffold | `sorry` | `check_port` |
|---|---|---:|---:|---|
| `MeasureTheory/HaarQuotientFubini.lean` (new) | A | **536** lines | 21 | **1 ok / 0 / 0** (the rest of the module is the pin's private engine, which the checker does not diff) |

**Three scaffold defects are handed to the worker with the order** (pin-version drift in the scaffold's
own def/proof bodies: `:158`, `:202`, `:450`). They are body edits, not statement edits; the checker is
green before dispatch. No `Def_` work: `Def_HaarQuotient`'s port
(`MeasureTheory/HaarQuotient.lean`) carries the vocabulary.

## 3. The order and the gates

| order | rows | file | content | scaffold `sorry`s |
|---|---|---|---:|---:|
| `WORKORDER-AF73A` | A | `MeasureTheory/HaarQuotientFubini.lean` | ≈520 | 21 |

Gates: no tree build; edit loop at `-DmaxHeartbeats=200000`; `lake build` under `flock`/`timeout`;
`check_port --force` unchanged (0 mismatch / 0 missing); `#print axioms` on the headline; zero warnings;
no `sorry`; no `set_option` beyond `autoImplicit false`; no silencer without a recorded reason;
`dedup --within` / `move_dead` clean; one consumer zone. The work order is in `lean/tmp/af73/`.

## 4. The shelf effect

*To be measured on the landed tree against §0's baseline (610 / 270,200).* The forecast: `needed` falls by
this set's own **616 silo** to **609 / 269,584**, the ready block is unchanged at 22 / 4,790, and the
leaves block falls to **156 / 39,881**. No readiness return is forecast: the row is a leaf whose only
consumer in the cone (`AutomorphicForm.exists_norm_a_le_absNorm_rpow_and_norm_b_le_of_…`, 384) holds
another unported premise.

## 5. The landing

A in, 536 → **672** lines (+173/−37), 21 `sorry`s → **0**, **no import added**, no `set_option` beyond the
frozen `autoImplicit false`.

| file | lines | `sorry` | build | `check_port` | axioms |
|---|---:|---:|---|---|---|
| `MeasureTheory/HaarQuotientFubini.lean` | 536 → **672** | 21 → **0** | 3,358 jobs, 6.6 s, silent | **1 ok / 0 / 0** | **1/1 clean** |

The 21 proofs follow the pin (`:33`–`:401`, headline `:606`–`:614`); the module's other 25 declarations
already carried the pin's bodies. A body-level diff against the already-landed sibling
`MeasureTheory/HaarQuotient.lean` (the same pin prelude) shows the **43 shared declarations identical**
modulo the `:= term` / `:= by exact term` spelling — independent evidence that the transcription is
faithful.

**The three scaffold defects, as fixed** (pin-version drift, all body edits):
`:158` — v4.34 no longer infers `ENNReal.le_tsum`'s function argument, so it is named
(`(f := fun n => coef H μH n * μH (slice H n g))`); `:202` — `Measure.map_smul` now takes
`AEMeasurable Inv.inv μH`, supplied after the `rw` (the same fix the port already had at
`HaarQuotient.lean:358`); `:450` — `simp only [Subtype.mk.injEq] at h` no longer rewrites, replaced by a
`congrArg` on the coercion.

**The one systematic deviation: 23 new `omit […] in` blocks** (30 in the file; 7 were the pin's). The
gate demands an empty `error|warning` grep and the brief forbade a `set_option`; the 15
`unusedSectionVars` warnings clear only by `omit`, and each `omit` propagates to callers, so it took four
rounds. The consequence is exactly the one the project rule cares about and the one the amended rule
allows to be avoided: **private helpers lose instance binders they do not use** (e.g. `weight_eq` drops
`[BorelSpace G] [IsHaarMeasure] [IsMulRightInvariant]`), while the public statement and the call sites are
untouched and the checker is unaffected. The alternative — the tree's usual module-level
`set_option linter.unusedSectionVars false`, used in `ModularForms/*` and
`Analysis/Fourier/FundamentalDomainIntegration.lean` — preserves the binder telescopes exactly and would
have replaced 23 `omit`s with one documented line; the worker chose the stricter of the two because the
order said no `set_option`. **Ruling: kept as landed** (no silencer at all is the strictest reading of the
rule), with the trade recorded here: 23 `omit`s are noisier than one scoped silencer but they preserve the
linters instead of disabling one.

**The `move_dead` refactor — done at landing, not deferred.** The sweep found **11 dead declarations /
227 lines** (the whole `D2`/`FDae`/`OuterMeasurability` block plus `measurable_lintegral_mul_out`, whose
consumer is the sibling module's own copy) whose premises are five *live private* helpers of the same file.
`move_dead.py --copy` handled exactly that case: the source lost only the dead set and the shelf got it
closed under its premises, cut out of a copy of the source.

| side | file | lines | build | gate |
|---|---|---:|---|---|
| source | `MeasureTheory/HaarQuotientFubini.lean` | 672 → **425** | 3,358 jobs, 4.3 s, silent | `check_port` **1 ok / 0 / 0**, consumer **0 errors**, `move_dead` now **0 declarations / 0 lines** |
| shelf | `Reserve/MeasureTheory/HaarQuotientFubiniDead.lean` | **649** (44 declarations, 33 live premises travel with the block) | 3,358 jobs, 5.5 s, silent | built by the `Reserve` library, **not wired** to `check_port` (a `Reserve/` shelf is not statement-diffed) |

Four things the sweep cost, each fixed and worth carrying:
1. **An orphaned `omit … in` prefix.** The pin's `omit` block at `:49` belonged to `exists_mul_eq_out`,
   which moved to the shelf; the prefix stayed and attached to `measurable_comp_mul`, whose type *does*
   reference the omitted instance — `cannot omit referenced section variable inst✝¹`. Deleting it was
   right, and the linter then named the one instance `measurable_comp_mul` really does not use
   (`[LocallyCompactSpace G]`), which came back as a fresh `omit`;
2. **an `omit` is load-bearing for callers**: with `measurable_comp_mul`'s omit gone, `measurable_orb`
   (which omits the same instance) could no longer call it — `failed to synthesize LocallyCompactSpace G`;
   restoring the omit on the callee fixed both sides. `move_dead`'s docstring covers `open … in` prefixes
   but not `omit … in` ones; that is FR-0216;
3. **the shelved copies must be re-emitted with their own section context**, which `--copy` does — the
   shelf's 44 declarations are the dead eleven plus their 33 premises, so it is a self-contained module
   that imports only `FLTForHuman/MeasureTheory/HaarQuotient.lean` and Mathlib, never the source;
4. **a `Reserve/` shelf must not carry a `spec-pin:` line**: the header the tool takes from
   `--header-file` had one, which would wire the shelf into `check_port` and show its 44 declarations as
   a partial diff of the pin file. The line is now a note saying the module is deliberately unwired.

**Heartbeat headroom**: silent at 20 k / 10 k, first abort at 5 k (`isFundamentalDomain_fibre`) — floor
5–10 k, ≈20× under the cap.

`dedup --within`: 46 declarations, 0 clusters. Consumer zone
`spec/MeasureTheorySetAF73AConsumer.lean` (87 lines; `G = Multiplicative ℝ`, `H = ⊥`, `μH = δ₀`, `f`
constant): **0 errors, 0 warnings**.

### The set's numbers

| figure | before | **after** | forecast |
|---|---:|---:|---:|
| `needed [F terminal]` | 610 / 270,200 | **608 / 268,958** (with AF74) | −2 / −1,242 ✓ exact |
| ready rows | 22 / 4,790 | **22 / 4,790** | unchanged ✓ exact |
| leaves | 157 / 40,497 | **155 / 39,255** | −2 / −1,242 ✓ exact |

The row is a leaf whose consumers all hold other unported premises, so no readiness return — the first
time in five sets that the forecast's "no readiness return" was right, and for the stated reason.
