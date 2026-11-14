# SET-AF69 — the spectral supplements: the high part of a compact operator, and the averaging operator

**Status: LANDED (2026-11-14).** Read off the D–S shelf after SET-AF68 with the recipe in
[../deligneSerre/TOPIC-scoping-a-ds-set.md](../deligneSerre/TOPIC-scoping-a-ds-set.md). The sixty-ninth
set of the column, and **a leaves-block set**: all seven rows sit in the `leaves_rank` block, not on the
ready shelf (§1.1), because every premise they consume is already ported — the plain `--ready` read drops
them, which is exactly the blind spot `--include-leaves` exists for.

**7 rows / 1,539 silo / ≈1,100 net** in **two new modules**, two orders.

| # | row (`ContinuousLinearMap.` dropped) | silo | lev | home |
|---|---|---:|---:|---|
| **A** | `eq_zero_of_forall_exists_mem_sub_real_smul_eq` | 385 | 1/1 | new `Analysis/InnerProductSpace/HighPart` |
| **B** | `le_ker_or_finiteDimensional_of_forall_inf_highPart_orthogonal` | 276 | 1/1 | same module |
| **C** | `map_highPart_orthogonal_le_of_commute` | 275 | 1/1 | same module |
| **D** | `orthogonal_iSup_eigenspace_ne_zero_eq_ker` | 275 | 2/4 | same module |
| **E** | `map_eigenspace_orthogonal_le_of_commute` | 40 | 1/2 | same module |
| **F** | `comp_eq_of_forall_apply_eq_integral_smul_apply_of_convolution` | 180 | 1/1 | new `Analysis/Group/AverageOperator` |
| **G** | `exists_forall_apply_eq_integral_smul_apply_of_forall_norm_le_of_continuous` | 108 | 1/1 | same module |

A–E are one subject (the spectral decomposition of a compact self-adjoint operator: the dense symmetric
range, the `highPart` subspace `⨆_{r ≤ ‖μ‖} eigenspace μ`, its orthogonal complement, and the fact that
commuting operators preserve it) and share a **250-line prelude written once** (§2). F–G are the other
subject (the integral representation of an averaging operator over a compact group). The two orders touch
disjoint files.

## 0. The read

```bash
cd tools/deps
python3 frontier.py --ds --ready --include-leaves --rank-by silo --top 0 --json > build/shelf26.json
python3 frontier.py --selfcheck
```

| figure | value |
|---|---:|
| `needed [F terminal]` | **629 / 274,935** |
| `needed [literal]` | 642 / 278,635 |
| frontier F | 1,789 / 852,686 |
| ready rows, all namespaces | **21 / 4,197** |
| leaves, all namespaces | **171 / 43,022** |
| `ContinuousLinearMap` demand | **7 / 1,539 — all seven in the leaves block** |
| withheld by the FR-0044 guard | 4 / 831 |
| cone / avoided | 2,103 / 982,173 · 140 / 74,620 |

`needed` is exactly SET-AF68 §5.3's post-landing figure, so this set opens on AF68's re-read; the read was
**taken before the two scaffolds were written** (FR-0201). `--selfcheck` still FAILS on MD-005's fifteen
rows; the correction is +1 node / +75 lines as in AF67/AF68, and no row cut here cites any of the fifteen.

## 1. What the set says

- **A** — *the symmetric range is dense* (`SymmetricRangeDensity`): if `u` is orthogonal to every
  `x − r • x` for real `r`, then `u = 0`. The engine is the bump-function approximation of the spectral
  measure (`bump`, `bumpC`, `quadForm`, `quadFormP`) against the continuous functional calculus.
- **B** — *the high part and the kernel*: for a compact symmetric `T` and a subspace `X` meeting each
  `(highPart T r)ᗮ` in either `⊥` or all of `X`, either `X ≤ ker T` or `X` is finite dimensional.
- **C** — an operator commuting with `T` preserves `(highPart T r)ᗮ`.
- **D** — `(⨆_{μ ≠ 0} eigenspace μ)ᗮ = ker T` for a compact symmetric `T`.
- **E** — an operator commuting with `T` preserves the orthogonal complement of every eigenspace.
- **F** — two linear maps that are both given by the convolution integral `v ↦ ∫ c, w c • S c v` agree.
- **G** — the averaging operator `∫ c, w c • S c (-)` is bounded by `B * M` and commutes with everything
  that commutes with each `S c`.

### 1.1 The shelf, quoted whole — every row cut or deferred

**The ready block: 21 rows / 4,197 silo — none cut, all deferred.** It is the post-AF68 shelf unchanged;
the two namespaces this set closes are not on it (§1.2).

| row | silo | lev | cut |
|---|---:|---:|---|
| `EisensteinGeneral.Piece.exists_forall_nonempty_factorizationDatum` | 890 | 3/5 | deferred |
| `GaloisRep.exists_isSemisimpleRepresentation_charpoly_map_eq_of_trace_det_frobenius_mem_range` | 495 | 1/1 | deferred |
| `ModularCurve.IsDiamondPullbackModL.apply_eq_one_iff_gamma0Units_mem` | 485 | 1/5 | deferred |
| `AutomorphicForm.exists_finset_forall_exists_mem_valued_eq_max_and_contentHomFin_mul_sq_eq` | 333 | 1/1 | deferred |
| `LanglandsTunnell.TateLocal.integral_comp_inv_eq_integral_modulus_inv_sq_mul_adicCompletion` | 305 | 1/7 | deferred |
| `CohCarrier.exists_surjective_doubleCoset_gammaH_zpowers_of_addOrderOf_eq` | 252 | 1/1 | (AF70) |
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
| `AutomorphicForm.SiegelCovering.centreCutSiegelSet_coversModCentre_rat` | 30 | 1/6 | deferred |
| `ModularCurve.rep_tateModule_jOne_comm` | 24 | 1/6 | deferred |

**The leaves block: 171 rows / 43,022 silo — 7 cut (A–G), 164 deferred.** It is otherwise as SET-AF67
§1.1 and SET-AF68 §1.1: the `AutomorphicForm` `CuspidalConstituent`/`WindowedSiegel` group,
`M4aTorus.completedRayL_fe` (12,126), the `NumberField` Euler-product leaves and the
`MeasureTheory`/`TateCurve`/`WeierstrassCurve` residue. The seven `ContinuousLinearMap` rows are the only
`ContinuousLinearMap` rows in the whole demand (1,539 lines, all seven), so this set **closes the
namespace**.

| row | silo | lev | cut |
|---|---:|---:|---|
| `M4aTorus.completedRayL_fe` | 12126 | 1/2 | deferred |
| `NumberField.exists_continuousOn_exp_eq_rayClassLSeries` | 684 | 1/2 | deferred |
| `EisensteinGeneral.Piece.exists_summable_majorant_of_lattice_vanishing` | 666 | 1/1 | deferred |
| `AutomorphicForm.CuspidalConstituent.exists_forall_le_archTypeSubmoduleAt_of_isSimple_of_le_iSup` | 646 | 2/4 | deferred |
| `MeasureTheory.exists_continuous_convolution_self_eq_forall_integral_smul_isotypic` | 626 | 1/1 | deferred |
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
| `ContinuousLinearMap.eq_zero_of_forall_exists_mem_sub_real_smul_eq` | 385 | 1/2 | **cut A** |
| `AutomorphicForm.exists_norm_a_le_absNorm_rpow_and_norm_b_le_of_smoothCuspRealizationAt_of_peterssonPairing` | 384 | 1/2 | deferred |
| `NumberField.Idele.lintegral_mul_prod_ord_sPartMeasure_eq_lintegral_sPartMeasure_empty_mul_prod_tsum` | 381 | 1/4 | deferred |
| `UnramifiedWhittaker.apply_mul_placeEmbed_diagZ_eq_mul_torusFactor` | 380 | 3/7 | deferred |
| `AutomorphicForm.exists_isArchBiFinite_rightConv_comp_inv` | 376 | 1/1 | deferred |
| `NumberField.Idele.exists_lintegral_prod_norm_sPartMeasure_empty_eq_mul_prod_lintegral` | 370 | 1/6 | deferred |
| `NumberField.AdelicFourier.fourierIntegral_pureTensor_eq` | 359 | 4/8 | deferred |
| `NumberField.dedekindZeta_ne_zero_of_one_lt_re` | 357 | 6/6 | deferred |
| `IsDedekindDomain.FiniteAdeleRing.exists_forall_sub_algebraMap_mem_adicCompletionIntegers` | 342 | 1/5 | deferred |
| `NumberField.hasProd_inv_one_sub_absNorm_cpow_neg_dedekindZeta` | 338 | 6/26 | deferred |
| `AutomorphicForm.IsKfSmooth.exists_ideal_forall_apply_mul_conj_unipotentGL2_eq` | 328 | 3/4 | deferred |
| `AutomorphicForm.exists_forall_adelicGLHaar_image2_unipotentGL2_mul_mul_le_of_isCompact` | 317 | 1/1 | deferred |
| `AutomorphicForm.CuspidalSpectrum.exists_isArchBiFinite_flat` | 304 | 1/1 | deferred |
| `WeierstrassCurve.finite_stabilizer_variableChange` | 285 | 1/10 | deferred |
| `AutomorphicForm.WindowedSiegel.isCompact_centreCutSiegelSet_inter_heightCap` | 282 | 5/10 | deferred |
| `ContinuousLinearMap.le_ker_or_finiteDimensional_of_forall_inf_highPart_orthogonal` | 276 | 1/1 | **cut B** |
| `ContinuousLinearMap.orthogonal_iSup_eigenspace_ne_zero_eq_ker` | 275 | 2/4 | **cut D** |
| `ContinuousLinearMap.map_highPart_orthogonal_le_of_commute` | 275 | 1/1 | **cut C** |
| `WeierstrassCurve.exists_variableChange_eq_legendreCurve_of_isUnit_two` | 274 | 1/2 | deferred |
| `ValuationSubring.ringKrullDim_le_ringKrullDim_comap_add_trdeg` | 269 | 1/3 | deferred |
| `NumberField.AdelicTrace.traceFinHom_apply_eq_sum_trace` | 266 | 1/1 | deferred |
| `ValuationSubring.exists_smul_mem_of_transcendental_residue` | 262 | 1/1 | deferred |
| `WeierstrassCurve.natCard_stabilizer_variableChange_eq_two_of_j_ne_zero_of_char_two_or_three` | 256 | 1/7 | deferred |
| `CohCarrier.charInvolution_comp_opFamily` | 247 | 1/3 | (AF70) |
| `TateCurve.point_mul_eq_add_of_norm_eq_one` | 247 | 1/1 | deferred |
| `AutomorphicForm.CuspidalConstituent.exists_isFactorizableTestFn_isArchBiFinite_conj` | 245 | 1/1 | deferred |
| `NumberField.mixedEmbedding.exists_forall_tsum_fractionalIdeal_weight_le_rpow_neg` | 237 | 2/11 | deferred |
| `NumberField.AdelicFourier.summable_translate_of_mem_schwartzBruhat` | 236 | 2/3 | deferred |
| `NumberField.AdelicFourier.integrable_of_mem_schwartzBruhat` | 235 | 5/20 | deferred |
| `EisensteinGeneral.Arch.exists_norm_archIntegral_le` | 233 | 2/2 | deferred |
| `NumberField.ncard_primesOver_eq_finrank_of_isCyclotomicExtension_of_absNorm_modEq_one` | 233 | 1/2 | deferred |
| `WeierstrassCurve.stepCurve_stepSubgroup_two_eq` | 231 | 1/5 | deferred |
| `LanglandsTunnell.RankinSelberg.exists_nonneg_exp_tsum_mul_pow_eq_inv_eval_rsEulerPoly_self_of_norm_eq_one` | 231 | 1/1 | deferred |
| `NumberField.AdelicBox.absNorm_mul_measure_image_integralFiniteAdeles` | 229 | 1/2 | deferred |
| `IsDedekindDomain.FiniteAdeleRing.exists_sub_algebraMap_mem_adicCompletionIntegers` | 228 | 1/5 | deferred |
| `MeasureTheory.Measure.exists_eq_smul_map_smul_of_forall_map_smul_eq_of_isCompact_stabilizer` | 222 | 1/2 | deferred |
| `NumberField.AdelicFourier.fourierIntegral_comp_mul_left` | 215 | 3/10 | deferred |
| `WeierstrassCurve.exists_isUnit_mul_pow_eight_eq_of_charTwo` | 215 | 1/3 | deferred |
| `WeierstrassCurve.exists_variableChange_eq_deuring_of_isUnit_three` | 213 | 1/1 | deferred |
| `NumberField.AdelicLevel.diagOne_mul_archRealGLAt_unipotent_eq_and_stdAddChar_single_half` | 207 | 4/4 | deferred |
| `UnramifiedWhittaker.tsum_heckeRecursionSeq_mul_heckeRecursionSeq_mul_pow_mul_rsEulerPoly_eval` | 207 | 1/2 | deferred |
| `UnramifiedWhittaker.summable_heckeRecursionSeq_mul_heckeRecursionSeq_mul_pow` | 205 | 1/2 | deferred |
| `NumberField.AdelicBox.exists_ne_zero_forall_addChar_mul_eq_one` | 201 | 1/3 | deferred |
| `AutomorphicForm.integral_prod_conj_eq_and_eq_conj_mul_of_conj_invariant_of_flat` | 196 | 4/5 | deferred |
| `ModularForm.exists_cuspForm_mul_eq_of_forall_analyticOrderAt_le` | 195 | 1/1 | deferred |
| `WeierstrassCurve.exists_map_eq_veluQuotient_and_map_residue_eq_veluQuotient_reduceHom` | 194 | 1/2 | deferred |
| `AutomorphicForm.exists_eq_mul_mem_levelOne_inf_finiteAdelicGL2Subgroup_commute_placeEmbed_of_forall_mem_localIntegralSet` | 192 | 1/1 | deferred |
| `EisensteinGeneral.Piece.continuous_and_continuous_of_isInducedSection_of_continuous_of_ne_zero` | 189 | 2/2 | deferred |
| `AutomorphicForm.IsFactorizableTestFn.comp_mul_unipotentGL2_mul_mem_pureTensorSet` | 189 | 1/4 | deferred |
| `WeierstrassCurve.natCard_stabilizer_variableChange_eq_two_of_j_ne_zero_of_j_ne_1728` | 187 | 1/8 | deferred |
| `NumberField.AdelicFourier.fourierIntegral_indicator_principalCoset_finiteAdeleRing_apply` | 181 | 1/1 | deferred |
| `ContinuousLinearMap.comp_eq_of_forall_apply_eq_integral_smul_apply_of_convolution` | 180 | 1/1 | **cut F** |
| `NumberField.AdelicFourier.exists_smul_eq_of_isAddHaarMeasure_adeleRing` | 179 | 2/4 | deferred |
| `ValuationSubring.natDegree_map_eq_card_roots_of_splits` | 174 | 1/1 | deferred |
| `NumberField.AdelicLevel.diagOne_eq_diagOne_mul_archRealLiftAt_mul_centralScalar` | 172 | 3/3 | deferred |
| `HaarQuotient.lintegral_density_mul_eq_one` | 170 | 2/39 | deferred |
| `LanglandsTunnell.TateLocal.realZeta_eq_localZeta` | 166 | 1/13 | deferred |
| `LanglandsTunnell.TateLocal.complexZeta_eq_localZeta` | 166 | 1/7 | deferred |
| `AutomorphicForm.isArchTestFactor_of_contDiff_of_hasCompactSupport_of_tsupport_subset_isUnit_det` | 165 | 1/5 | deferred |
| `EisensteinGeneral.Glue.whittakerCoefficientIntegrable_bruhatSeries_and_ae_summable_of_integrable` | 165 | 1/1 | deferred |
| `NumberField.AdelicHeight.adelicHeight_globalPoints_mul_of_apply_one_zero_eq_zero` | 161 | 1/22 | deferred |
| `TateCurve.tsum_succ_prod_eq_tsum_divisors` | 157 | 2/2 | deferred |
| `WeierstrassCurve.transcendental_j_perturb` | 156 | 1/2 | deferred |
| `AutomorphicForm.exists_borel_mul_gl2Weyl_mul_unipotentGL2_eq_of_integral` | 156 | 1/1 | deferred |
| `ModularForm.exists_levelOne_coe_eq_sum_slash` | 156 | 1/1 | deferred |
| `AutomorphicForm.CuspidalConstituent.continuous_and_isSmoothCuspAutomorphicFnAt_rightTranslate_of_mem_cuspKFiniteSubmodule` | 154 | 8/19 | deferred |
| `AutomorphicForm.typeSubmodule_inf_typeSubmodule_eq_bot` | 152 | 1/2 | deferred |
| `AutomorphicForm.coversModCentre_of_le_of_lt_of_coversModCentre` | 150 | 4/8 | deferred |
| `LanglandsTunnell.TateLocal.tateFourier_indicator_setOf_valued_sub_le` | 149 | 1/21 | deferred |
| `AutomorphicForm.CuspidalConstituent.forall_apply_mul_archRealGLAt_eq_of_isCuspConstituent_of_exists` | 148 | 2/2 | deferred |
| `MeasureTheory.Lp.finiteDimensional_and_finrank_le_of_forall_ae_norm_le_mul_norm` | 148 | 1/1 | deferred |
| `NumberField.AdelicFourier.fourierIntegral_indicator_principalCoset_finiteAdeleRing` | 140 | 1/2 | deferred |
| `EisensteinGeneral.Piece.integral_smul_add_mul_addChar_neg_mul_eq` | 125 | 4/6 | deferred |
| `AutomorphicForm.mem_rationalCentreUnipotent_iff_heckeGen_mul_centralScalar_conj_mem` | 119 | 1/1 | deferred |
| `NumberField.AdeleRing.exists_isOpen_inter_principalIdeles_eq_singleton` | 118 | 1/4 | deferred |
| `IsDedekindDomain.HeightOneSpectrum.isAdicComplete_adicCompletionIntegers` | 111 | 1/12 | deferred |
| `NumberField.AdelicBox.integralFiniteAdeles_subset_closure_range_algebraMap_ringOfIntegers` | 109 | 2/2 | deferred |
| `ContinuousLinearMap.exists_forall_apply_eq_integral_smul_apply_of_forall_norm_le_of_continuous` | 108 | 2/2 | **cut G** |
| `LanglandsTunnell.eq_zero_of_deriv_eq_div_add_mul_of_re_pos_of_isBigO_pow` | 104 | 1/1 | deferred |
| `MeasureTheory.integral_normSq_det_div_mul_comp_moebius_complex` | 104 | 1/1 | deferred |
| `NumberField.AdelicFourier.comp_mul_mem_schwartzBruhat` | 101 | 1/7 | deferred |
| `WeierstrassCurve.Affine.Point.zsmul_some_eq_some_div` | 100 | 2/41 | deferred |
| `MeasureTheory.differentiableOn_integral_of_forall_differentiableOn_of_locally_norm_le` | 99 | 3/6 | deferred |
| `MeasureTheory.lintegral_enorm_sub_integral_mul_sq_le_lintegral_mul_lintegral_enorm_sub_sq` | 98 | 2/3 | deferred |
| `NumberField.Units.exists_forall_abs_sub_mult_mul_log_le` | 98 | 2/2 | deferred |
| `MeasureTheory.integral_abs_det_div_sq_mul_comp_moebius_real` | 95 | 1/1 | deferred |
| `ModularForm.exists_qExpansion_eq_aeval_mul_pow_levelOne` | 94 | 5/8 | deferred |
| `NumberField.InfinitePlace.sign_norm_eq_prod_sign_embedding_of_isReal` | 94 | 1/2 | deferred |
| `NumberField.AdelicFourier.norm_apply_eq_one_of_isGlobalAddChar` | 93 | 25/74 | deferred |
| `NumberField.AdelicFourier.setIntegral_addChar_mul_eq_ite_of_isCompact` | 93 | 1/1 | deferred |
| `MeasureTheory.exists_integral_eq_inv_card_mul_sum_of_isOpen_subgroup` | 90 | 3/4 | deferred |
| `MeasureTheory.lintegral_mul_comp_eq_tsum_zpow_mul_setLIntegral_of_measure_image_eq_mul` | 84 | 1/1 | deferred |
| `NumberField.AdelicFourier.comp_mul_algebraMap_mem_pureTensorSet` | 84 | 1/1 | deferred |
| `ValuationSubring.IsFrobeniusAt.apply_eq_pow_of_pow_eq_one` | 83 | 2/21 | deferred |
| `AutomorphicForm.IsUnitFactorizableAbove.finComponent_glFin_mem_localIntegralSet_of_apply_ne_zero` | 78 | 1/1 | deferred |
| `ValuationSubring.tensorProduct_exists_primitive_factor` | 78 | 1/1 | deferred |
| `AutomorphicForm.CuspidalSpectrum.isClosedCuspSubrep_topologicalClosure_map_toCuspSubcarrier_of_isCuspSubrep` | 75 | 2/4 | deferred |
| `CohCarrier.H1_moduleFinite` | 74 | 1/70 | (AF70) |
| `NumberField.Idele.sPartMeasure_pos_of_isOpen_of_partAt_eq` | 73 | 1/1 | deferred |
| `NumberField.mixedEmbedding.exists_forall_norm_embedding_sub_le` | 71 | 1/1 | deferred |
| `WeierstrassCurve.exists_valuationSubring_with_transcendental_of_charZero` | 70 | 1/2 | deferred |
| `NumberField.AdelicBox.exists_denom_of_hasCompactSupport` | 70 | 1/1 | deferred |
| `NumberField.summable_heightOneSpectrum_absNorm_rpow_neg_of_one_lt` | 69 | 7/41 | deferred |
| `NumberField.StandardAddChar.psiLocal_rat_eq_psiV` | 69 | 1/38 | deferred |
| `TateCurve.exists_zpow_mul_mem_annulus` | 69 | 1/6 | deferred |
| `AutomorphicForm.exists_smoothCuspRealizationAt_productionPinsOf_toFun_eq_of_isBoundedOnSiegelWindows_of_coversModCentre` | 69 | 1/1 | deferred |
| `NumberField.mixedEmbedding.summable_norm_schwartzMap_ringOfIntegers_translate` | 67 | 1/1 | deferred |
| `AutomorphicForm.RankinSelberg.section_diagOne_mul_eq_ideleNorm_cpow_mul_of_isInducedSection_etaFst_etaSnd` | 66 | 1/1 | deferred |
| `AutomorphicForm.existsUnique_bruhatRepresentative_mul_mem_borelSubgroup` | 65 | 2/3 | deferred |
| `MeasureTheory.tendsto_lintegral_nhds_zero_of_le_of_limsup_lintegral_le` | 63 | 1/1 | deferred |
| `NumberField.StandardAddChar.stdAddChar_single_infinitePlace_of_isReal` | 62 | 3/6 | deferred |
| `AutomorphicForm.isLocallyConstant_iwasawaShellIndex_and_measurable` | 62 | 2/2 | deferred |
| `AutomorphicForm.CuspidalConstituent.isCuspConstituent_productionPinsOf_mono` | 62 | 1/2 | deferred |
| `ModularForm.exists_levelOne_qExpansion_eq_map_int_constantCoeff_one` | 62 | 1/1 | deferred |
| `NumberField.StandardAddChar.stdAddChar_single_infinitePlace_of_isComplex` | 61 | 2/2 | deferred |
| `LocalNewvector.AdelicSpan.exists_hasNewvectorConductor_le_factorization` | 58 | 1/2 | deferred |
| `ValuationSubring.exists_map_subtype_eq_C_inv_mul_and_map_residue_ne_zero` | 57 | 1/3 | deferred |
| `AutomorphicForm.exists_continuous_monoidHom_matrix_apply_ne_one_of_ne_one` | 55 | 1/1 | deferred |
| `IsDedekindDomain.FiniteAdeleRing.exists_ne_zero_forall_mul_apply_mem_adicCompletionIntegers_of_isCompact` | 52 | 3/14 | deferred |
| `CohCarrier.exists_eq_gammaH_of_gamma1_le_of_le_gamma0` | 49 | 1/11 | (AF70) |
| `AutomorphicForm.iwasawaShellIndex_mul_of_mem_rationalCentreUnipotent` | 46 | 2/2 | deferred |
| `LanglandsTunnell.TateLocal.psiLocal_eq_one_of_mem_integers` | 45 | 4/116 | deferred |
| `NumberField.AdelicBox.isLocallyConstant_and_hasCompactSupport_indicator_image_integralFiniteAdeles` | 44 | 1/4 | deferred |
| `NumberField.AdelicBox.algebraMap_mem_image_integralFiniteAdeles_iff` | 41 | 2/3 | deferred |
| `WeierstrassCurve.Affine.Point.some_add_some_eq_neg_some_of_pow_three_eq_one` | 40 | 1/3 | deferred |
| `ContinuousLinearMap.map_eigenspace_orthogonal_le_of_commute` | 40 | 1/2 | **cut E** |
| `LanglandsTunnell.TateLocal.forall_eq_one_and_exists_ne_one_of_addCharLevel` | 37 | 3/100 | deferred |
| `ValuationSubring.charP_residueField_of_liesOverPrime` | 37 | 1/27 | deferred |
| `WeierstrassCurve.Affine.Point.some_zero_add_self_eq_neg_of_a6_model` | 34 | 1/3 | deferred |
| `AutomorphicForm.CuspidalConstituent.eq_of_isCuspConstituent_of_exists_mem_ne_zero` | 33 | 1/2 | deferred |
| `CohCarrier.index_gammaH_eq_index_gamma0_mul_index` | 32 | 1/22 | (AF70) |
| `NumberField.AdeleRing.compactSpace_quotient_principalSubgroup` | 32 | 1/3 | deferred |
| `NumberField.AdelicFourier.comp_add_right_mem_pureTensorSet` | 31 | 1/1 | deferred |
| `AutomorphicForm.IsIsotypicCuspFormAt.exists_smoothCuspRealizationAt_toFun_eq_of_ne_bot` | 30 | 2/10 | deferred |
| `WeierstrassCurve.Affine.evalEval_psi_sq` | 29 | 2/44 | deferred |
| `WeierstrassCurve.Affine.Point.smul_some_eq_zero_iff` | 28 | 2/51 | deferred |
| `WeierstrassCurve.variableChange_mk_smul_eq_self_of_pow_three_eq_one` | 26 | 1/6 | deferred |
| `WeierstrassCurve.variableChange_mk_smul_eq_self_of_sq_eq_neg_one` | 26 | 1/6 | deferred |
| `CohCarrier.exists_gamma0_lift_dvd` | 25 | 1/10 | (AF70) |
| `AutomorphicForm.exists_iUnion_centreCutSiegelSet_mem_nhds` | 25 | 1/1 | deferred |
| `AutomorphicForm.eq_zero_of_isLsXiFunction_of_coversModCentre_of_forall_mem_eq_zero` | 23 | 1/1 | deferred |
| `ModularForm.exists_coe_eq_of_levelOne` | 22 | 1/4 | deferred |
| `TateCurve.nodal_xfun_yfun` | 22 | 1/1 | deferred |
| `IsDedekindDomain.HeightOneSpectrum.exists_prime_and_asIdeal_eq_span_ringOfIntegers_rat` | 20 | 2/9 | deferred |
| `TateCurve.pointX_q_mul` | 19 | 2/9 | deferred |
| `TateCurve.pointY_q_mul` | 19 | 2/7 | deferred |
| `MeasureTheory.measure_biUnion_finset_image_mul_right_lt_top` | 18 | 1/1 | deferred |
| `NumberField.mixedEmbedding.trace_mixedEmbedding` | 17 | 6/8 | deferred |
| `TateCurve.hasSum_xfun` | 17 | 3/3 | deferred |
| `TateCurve.hasSum_yfun` | 17 | 2/2 | deferred |
| `AutomorphicForm.constantTerm_add` | 13 | 1/2 | deferred |
| `AutomorphicForm.constantTerm_smul` | 11 | 1/1 | deferred |
| `NumberField.StandardAddChar.isGlobalAddChar_stdAddChar` | 10 | 17/59 | deferred |

### 1.2 Why the ready view cannot see them

All seven rows have `needed = 1` and **zero unported direct premises**: the port already holds
`IsCompactOperator`, the symmetric-operator API, `orthogonalFamily_eigenspaces`, the CFC instances and the
Haar measure. A node with no unported premise never reaches the frontier `F` through its own premises, so
`frontier_hops` has nothing to measure and the `--ready` view drops it as a leaf — the same failure SET 4
found on the `AlgebraicCurve` shelf. The corrected reading is the `leaves_rank` block, and the seven rows'
`needed = 1` there is the readiness statement.

## 2. The price and the homes

| module | rows | scaffold | decls | `sorry` | `check_port` |
|---|---|---:|---:|---:|---|
| `Analysis/InnerProductSpace/HighPart.lean` (new) | A–E | **278** lines | 37 | 31 | **18 ok / 0 / 0** |
| `Analysis/Group/AverageOperator.lean` (new) | F, G | **190** lines | 27 | 18 | **21 ok / 0 / 0** |

Two new modules, both elaborating at the low cap and checker-green before dispatch. The scaffold's only
non-`sorry` diagnostics are FR-0208-class items in the pin's own text (the dead `hν` binder of
`le_norm_sub_of_mem_eigenspace`, the auto-included section variables of
`AverageConvolution.continuous_integrand`); **the scaffold's count of them is a lower bound**, because the
linter is silent on a `sorry` body — filling module B's proofs exposed seven such declarations, not the
two the scaffold shows (FR-0213).

**The dedup ruling: the three `highPart` files share their engine, so it is written once.** `port_advise`
reports **15 names proved in ≥2 target files, ≈318 removable lines**: the 14-declaration `highPart`
prelude (`highPart`, `le_norm_sub_of_mem_eigenspace`, `finite_setOf_hasEigenvalue_le_norm`,
`finiteDimensional_highPart`, `apply_mem_iSup_eigenspace_ne_zero`, `orthogonal_iSup_eigenspace_ne_zero_eq_ker`,
`adjoint_comp_eq_of_isSymmetric`, `highPart_sup_orthogonal_eq_top`, `map_highPart_le_of_commute`,
`map_highPart_orthogonal_le_of_commute`, `iInf_highPart_orthogonal_eq_ker`,
`exists_inf_highPart_orthogonal_eq_bot_of_not_le_ker`,
`le_ker_or_finiteDimensional_of_forall_inf_highPart_orthogonal`) is byte-identical in the three `S_` files.
It is emitted **once**, into the sub-namespace `ContinuousLinearMap.HighPart`, and the pin's `_pf` suffix
(its marker for the `highPart`-spelled form of a result whose headline spells the join out) is dropped.
That split is what keeps the two spellings apart: the prelude variant and the headline have the **same
mathematics and different statements** (`highPart T r` vs `⨆ (μ) (_ : r ≤ ‖μ‖), eigenspace μ`), so both are
needed, and inside one module the pin's flat `namespace ContinuousLinearMap` would be a redeclaration. The
checker matches the pin's `_pf` copies by statement hash (§2.1).

The `AverageOperator` module's two files share only `hasCompactSupport_of_compactSpace'` (12 lines); the
port writes that once, in `AverageConvolution`.

**The premise audit.** Every premise of all seven rows is ported (`premises_unported = 0`,
`premises_pruned = 0`), and the statements use no `Definitions/Def_*` vocabulary: the pin's `S_` files
import `Mathlib` and `P2M.Util` only. The manager's Def layer is therefore **empty** for this set — the
`highPart` def is the pin's own local definition and is transcribed with the prelude.

### 2.1 The scaffold's import finding

The pin imports `Mathlib` wholesale, so the scaffold's import list had to be found by hand: the
`quadForm` engine needs the CFC **instances** (`ContinuousFunctionalCalculus.Instances`) *and* the
`CStarAlgebra` structure on `E →L[ℂ] E` (`ContinuousFunctionalCalculus.Basic`,
`Analysis.CStarAlgebra.ContinuousLinearMap`), the compact-operator API
(`Normed.Operator.Compact.Basic`), the eigenspace orthogonality (`InnerProductSpace.JointEigenspace`,
`InnerProductSpace.Adjoint`) and `Topology.ContinuousMap.CompactlySupported`. Importing
`Mathlib.MeasureTheory.Integral.Bochner` (the aggregator) fails on this tree — its olean is not built;
`…Bochner.Set` is.

## 3. The orders and the gates

| order | rows | file | content | scaffold `sorry`s |
|---|---|---|---:|---:|
| `WORKORDER-AF69A` | A, B, C, D, E | `Analysis/InnerProductSpace/HighPart.lean` | ≈900 | 31 |
| `WORKORDER-AF69B` | F, G | `Analysis/Group/AverageOperator.lean` | ≈250 | 18 |

Gates per module: no tree build; edit loop at `-DmaxHeartbeats=200000`; `lake build <module>` under
`flock`/`timeout`; `check_port --force` unchanged (**18 ok**, **21 ok**); `#print axioms` on all seven
headlines; zero warnings; no `sorry`; no `set_option` beyond `autoImplicit false`; no silencer;
`dedup --within` / `move_dead` clean; one consumer zone per order. The work orders are in
`lean/tmp/af69/`.

## 4. The shelf effect

*To be measured on the landed tree against §0's baseline (629 / 274,935), with the `unported ⊆ cut` rule.*
The forecast: `needed` falls by this set's own **1,539 silo** to **622 / 273,396** (the `--port` probe of
all seven rows reads 622 / 273,396 on the same marker set), the ready block is unchanged at 21 / 4,197
(none of these rows is on it), and the leaves block falls from 171 / 43,022 to **164 / 41,483**. Return:
**0 rows readied for 1,539 consumed** — the second set of the column with no readiness return, and for the
structural reason the leaves reading names: a leaf's consumers are already ported, so nothing above it
becomes ready. The `ContinuousLinearMap` namespace closes.

## 5. The landing

### 5.1 Order A — the high part of a compact self-adjoint operator (landed 2026-11-14)

A–E in, 278 → **785** lines (**+507**), 31 `sorry`s → **0**, **one import added**
(`Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real`: `core` needs `RealRMK.rieszMeasure`), no
`set_option` beyond the frozen `autoImplicit false`.

| file | lines | decls | `sorry` | build | `check_port` | axioms |
|---|---:|---:|---:|---|---|---|
| `Analysis/InnerProductSpace/HighPart.lean` | 278 → **785** | 37 | 31 → **0** | 3,607 jobs, 16 s, silent | **18 ok / 0 / 0** | **5/5 clean** |

Per row: A **285** lines against pin `:18`–`:381` (the bump/`quadForm`/`core` engine plus the headline);
the shared prelude **193** lines against the pin's `:39`–`:267`; B, C, D **3** lines each (one application
of a prelude lemma); E **28** lines against `:16`–`:40`. `dedup --within`: **1 cluster / 7 lines**, the
`shape` pair between the prelude's `HighPart.orthogonal_iSup_eigenspace_ne_zero_eq_ker` and the root
headline of the same name — **a finding, not removable**: for row D the pin's `_pf` form and the headline
have the *same* statement, so §2's two-spelling ruling requires both, and dropping either breaks a wire.
`move_dead`: 2 declarations / 7 lines, the pin's own unused `rfl` lemmas `bumpC_apply` and
`quadFormP_apply` — dead but frozen (the checker matches them), so kept. Consumer zone
`spec/AnalysisSetAF69AConsumer.lean` (five zones, one per headline, `T = 0`, `E = ℂ` or `ℂ`, `X = ⊤`):
**0 errors, 0 warnings**.

**Heartbeat headroom, probed downward**: silent at **40,000**, first failure at 20,000 (`quadForm_le`,
`whnf` timeout), 7 errors at 10,000 — so the worst declaration is in [20 k, 40 k) and the gate's 200,000 has
**≥5×** headroom. No `set_option` anywhere.

Deviations, all proof-side: the v4.34 rename table plus the orthogonal-projection family
(`orthogonalProjection` → `orthogonalProjectionOnto` and its four companions,
`one_apply` → `one_apply_eq_self`, `mul_apply` → `mul_apply_eq_comp`, `coe_comp'` → `coe_comp`); six
`haveI` → `have` (FR-0198); and **five FR-0208 witness spends** — `hν`/`hμ` of
`le_norm_sub_of_mem_eigenspace` (the pin's one-line `nlinarith` is the only non-`sorry` scaffold line
replaced), `[CompleteSpace E]` in `finite_setOf_hasEigenvalue_le_norm` (v4.34's compact-operator lemma no
longer needs it, so the Cauchy-sequence limit is now genuinely extracted with
`cauchySeq_tendsto_of_complete` and an ε/2 argument — the pin's `:62`–`:68`), and `[CompleteSpace E]`/`hT'`
/`hT`/`hμ` in three further declarations.

### 5.2 Order B — the integral representation of an averaging operator (landed 2026-11-14)

F, G in, 190 → **361** lines (**+171**), 18 `sorry`s → **0**, **three imports added**
(`Topology.UrysohnsLemma`, `Topology.ContinuousMap.StoneWeierstrass`, `MeasureTheory.Integral.Prod`), no
`set_option`.

| file | lines | decls | `sorry` | build | `check_port` | axioms |
|---|---:|---:|---:|---|---|---|
| `Analysis/Group/AverageOperator.lean` | 190 → **361** | 27 | 18 → **0** | 3,469 jobs, 8.4 s, silent | **21 ok / 0 / 0** | **2/2 clean** |

**Heartbeat headroom**: silent at 20,000 / 10,000, first failure at 5,000 and only in
`ProductMeasurable.measurable_of_continuous` (the Stone--Weierstrass density proof) — worst declaration in
[5 k, 10 k), **≥20×** under the cap.

Deviations, all proof-side: `map_le` — the pin's `integral_inner` rewrite lives in
`MeasureTheory.Function.L2Space`, outside the module's cone, so the same identity is proved locally from
`ContinuousLinearMap.integral_comp_comm (innerSL ℂ u)` (no fourth large import); `comp_eq` — the pin's
`:142` `positivity` hack replaced by an explicit `mul_le_mul` chain on the same bound; `coe_comp'` →
`coe_comp`; the headline's `fun v => rfl` → `fun _ => rfl`.

**The linter finding (FR-0213).** The scaffold's "two FR-0208-class items" was a **lower bound**: the
linter is silent on a `sorry` body, so filling the proofs exposed **seven** declarations with dead
auto-included section variables in this module alone (six in `AverageConvolution.continuous_integrand`,
then five more across the `AverageOperator` block). All seven were *spent* with the sanctioned
`have _ := …` form — `continuous_inv`/`isCompact_univ`/`isClosed_singleton`/`isClosed_univ.measurableSet`/
`isComplete_univ`, `μ univ = 1`, `hSb 1`, `hSc 0`, `Continuous w`, and
`Measure.IsHaarMeasure.toIsMulLeftInvariant` — never `omit` for a variable the pin does not omit, never a
silencer.

`dedup --within`: **1 cluster / 12 lines**, the `hasCompactSupport_of_compactSpace'` copy in both
`AverageConvolution` and `AverageOperator` — the scaffold's *mandated* double emission (the pin copies it
into both files and the checker matches both by statement hash), so kept. `move_dead`: 0. Consumer zone
`spec/AnalysisSetAF69BConsumer.lean` (141 lines; `C = Unit` with the Dirac mass, `H = ℂ`, the identity
representation, constant weights): **0 errors, 0 warnings**.

### 5.3 The set's numbers, and the plan-vs-actual

| figure | before (opening read) | **after** | forecast |
|---|---:|---:|---:|
| `needed [F terminal]` | 629 / 274,935 | **622 / 273,396** | −7 / −1,539 ✓ exact |
| `needed [literal]` | 642 / 278,635 | **635 / 277,096** | −7 / −1,539 ✓ |
| frontier F | 1,789 / 852,686 | **1,796 / 854,225** | +7 / +1,539 |
| ready rows | 21 / 4,197 | **21 / 4,197** | unchanged ✓ |
| leaves | 171 / 43,022 | **164 / 41,483** | −7 / −1,539 ✓ exact |
| `ContinuousLinearMap` demand | 7 / 1,539 | **absent** | closed ✓ |

**The return forecast was exact, and it was a zero**: none of the seven was on the ready shelf (all seven
were leaves), so no row above them becomes ready. That is the second set of the column with no readiness
return, and it is a structural property of a leaves-block set, not a bad cut: the namespace is closed, and
the seven statements are the port's spectral-theory supplement.

Plan vs actual: the cut was exact (seven rows, 1,539 silo), the dedup came out as ruled (the prelude
written once: the pin's 318 removable lines became one 193-line engine plus three 3-line headlines), and
the price was **678 written proof lines against a ≈1,100-net estimate (0.62×)** — the `∃`-headed
statement-surface effect of AF68 again, weaker here because the `highPart` prelude is real proof. The
wave's one failure was again a *tree-state* one: two import-chain modules (`Defs/CohCarrierLower` and its
neighbours) had no oleans on this tree, and the scaffold could not elaborate until `lake build` had
rebuilt the chain — FR-0207's mechanism, one targeted build, no rework.

## 6. Reproduce

```bash
cd tools/deps
python3 frontier.py --ds --ready --include-leaves --rank-by silo --top 0 --json > build/shelf26.json
python3 frontier.py --ds --ready --include-leaves --rank-by silo --top 0 --json \
  --port ContinuousLinearMap.eq_zero_of_forall_exists_mem_sub_real_smul_eq \
  --port ContinuousLinearMap.le_ker_or_finiteDimensional_of_forall_inf_highPart_orthogonal \
  --port ContinuousLinearMap.map_highPart_orthogonal_le_of_commute \
  --port ContinuousLinearMap.orthogonal_iSup_eigenspace_ne_zero_eq_ker \
  --port ContinuousLinearMap.map_eigenspace_orthogonal_le_of_commute \
  --port ContinuousLinearMap.comp_eq_of_forall_apply_eq_integral_smul_apply_of_convolution \
  --port ContinuousLinearMap.exists_forall_apply_eq_integral_smul_apply_of_forall_norm_le_of_continuous
python3 frontier.py --selfcheck
cd .. && python3 lean/tmp/af69/gen69.py all --force   # the two scaffolds (after the opening read; §0)
cd lean && python3 spec/check_port.py --force FLTForHuman/Analysis/InnerProductSpace/HighPart.lean
python3 spec/check_port.py --force FLTForHuman/Analysis/Group/AverageOperator.lean
```
