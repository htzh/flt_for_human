# SET-AF74 — the isotypic convolution projection

**Status: LANDED (2026-11-14).** Read off the D–S shelf after SET-AF71/AF72, with the recipe in
[../deligneSerre/TOPIC-scoping-a-ds-set.md](../deligneSerre/TOPIC-scoping-a-ds-set.md). The
seventy-fourth set of the column, and the second **one-row leaves set** of the wave.

**1 row / 626 silo / ≈560 net** in **one new module**, one order.

| # | row | silo | lev | home |
|---|---|---:|---:|---|
| **A** | `MeasureTheory.exists_continuous_convolution_self_eq_forall_integral_smul_isotypic` | 626 | 1/1 | new `MeasureTheory/IsotypicConvolution` |

The row: a continuous endomorphism of a finite-dimensional representation which is a convolution against
a compact group is the projection onto the isotypic part, is idempotent, and can be written with a
conjugation-invariant coefficient function (the Gram reproducer). It is the averaging operator behind the
isotypic decomposition the `AutomorphicForm` spectrum rows use, and its `Def_` coverage is complete.

## 0. The read

The read is SET-AF73 §0's (same command, `build/shelf31.json`); the row's own figures are `needed = 1`,
`premises_unported = 0`, `premises_pruned = 0`, 626 silo, leverage 1/1.

## 1.1 The shelf, quoted whole — every row cut or deferred

**The ready block: 22 rows / 4,790 silo — none cut, all deferred** (unchanged from SET-AF71 §1.1 apart
from the two rows SET-AF71/AF72 readied).

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
| `MeasureTheory.exists_continuous_convolution_self_eq_forall_integral_smul_isotypic` | 626 | 1/1 | **cut AF74** |
| `HaarQuotient.lintegral_eq_lintegral_lintegral_mul_out` | 616 | 2/48 | deferred |
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

The remaining 136 rows are deferred unchanged from SET-AF70 §1.1, as in SET-AF73 §1.1.

## 2. The price and the home

| module | rows | scaffold | `sorry` | `check_port` |
|---|---|---:|---:|---|
| `MeasureTheory/IsotypicConvolution.lean` (new) | A | **242** lines | 17 | **21 ok / 0 / 0** |

The scaffold elaborates silently at the edit-loop cap today (no pre-existing defects, unlike its sibling
in SET-AF73). No `Def_` work.

## 3. The order and the gates

| order | rows | file | content | scaffold `sorry`s |
|---|---|---|---:|---:|
| `WORKORDER-AF74A` | A | `MeasureTheory/IsotypicConvolution.lean` | ≈560 | 17 |

Gates: the same six as SET-AF73 §3 (the checker line is **21 ok / 0 / 0**). The work order is in
`lean/tmp/af73/` (shared with SET-AF73, which was dispatched at the same time).

## 4. The shelf effect

*To be measured on the landed tree against §0's baseline (610 / 270,200).* The forecast: `needed` falls
by **626 silo**, ready unchanged, leaves falling by one row; no readiness return is forecast — the row's
consumer, `AutomorphicForm.CuspidalSpectrum.exists_isArchBiFinite_flat` (304), holds another unported
premise.

## 5. The landing

A in, 244 → **664** lines (**+420**, of which 413 are proof lines and 7 are `omit … in` headers), 17
`sorry`s → **0**, **no import added**, no `set_option` of the worker's own.

| file | lines | `sorry` | build | `check_port` | axioms |
|---|---:|---:|---|---|---|
| `MeasureTheory/IsotypicConvolution.lean` | 244 → **664** | 17 → **0** | 3,478 jobs, 5.4 s, silent | **21 ok / 0 / 0** | **1/1 clean** |

The 17 proofs follow the pin body-for-body (`:15`–`:21` … `:586`–`:626`, headline from the wrapper at
`:570`); the Gram reproducer (`:82`–`:210`) is the cost centre. `dedup --within`: 21 declarations, 0
clusters. `move_dead`: 0 declarations. Consumer zone `spec/MeasureTheorySetAF74AConsumer.lean` (79 lines;
`K = Unit`, the trivial one-dimensional `ρ`, `μ = haarMeasure ⊤`, `π` trivial on `ℂ`, with `A (A 1) = A 1`
read out of `A.comp A = A`): **0 errors, 0 warnings**.

**Heartbeat headroom**: passes at 25 k / 10 k, first failures at 9 k inside `exists_gram_reproducer` —
floor is Lean's default 10 000, ≈20× under the cap.

Deviations, all outside the pin's proof text: `Measure.isProbabilityMeasure_map` is gone in v4.34 →
`inferInstance`, with `rw [Measure.inv_def]` first for `μ.inv` (instance search does not unfold
`Measure.inv`); `haveI` → `have` at four sites (FR-0198); **seven `omit […] in` headers** for
`linter.unusedSectionVars` (the same strict choice as the sibling set: no silencer at all, private helpers
lose unused instance binders, checker unaffected); two dead statement hypotheses of the wrappers spent
with `have _ := hiso` / `hπc`; `coe_comp'` → `coe_comp`; the pin's local `star` renamed `hstar`.

### The set's numbers, and the plan-vs-actual

| figure | before (opening read) | **after** | forecast |
|---|---:|---:|---:|
| `needed [F terminal]` | 610 / 270,200 | **608 / 268,958** | −2 / −1,242 (both sets) ✓ exact |
| ready rows | 22 / 4,790 | **22 / 4,790** | unchanged ✓ exact |
| leaves | 157 / 40,497 | **155 / 39,255** | −2 / −1,242 ✓ exact |

Both one-row sets came in exactly on the accounting, and neither readied a row — the first wave in five
whose readiness forecast held, because these two rows' consumers genuinely hold other unported premises
(`AutomorphicForm.CuspidalSpectrum.exists_isArchBiFinite_flat` and the 384-line norm bound, respectively).

Plan vs actual: the cut was exact; the price was **586 written proof lines against a ≈1,080-net estimate
(0.54×)** — the statement-surface effect of this family once more; the only friction was the FR-0207
missing `.olean` of each module, one targeted build each.
