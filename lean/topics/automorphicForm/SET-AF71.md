# SET-AF71 — the `q`-expansion of a differential, and the diamond pullback mod `λ`

**Status: LANDED (2026-11-14).** Read off the D–S shelf after SET-AF70 with the recipe in
[../deligneSerre/TOPIC-scoping-a-ds-set.md](../deligneSerre/TOPIC-scoping-a-ds-set.md). The seventy-first
set of the column, and the first cut taken from the **post-AF70 ready block** — both rows are rows AF70
readied, which is the column's rule for the next cut.

**2 rows / 1,072 silo / ≈950 net** in **two new modules**, two orders (one row each).

| # | row | silo | lev | home |
|---|---|---:|---:|---|
| **A** | `ModularCurve.exists_coeffMap_qExpansionDiffAlong_laurentBaseChange_qExpFunctionFieldC_eq_qExpansion` | 587 | 2/4 | new `ModularCurve/QExpansionDifferentialLift` |
| **B** | `ModularCurve.IsDiamondPullbackModL.apply_eq_one_iff_gamma0Units_mem` | 485 | 1/5 | new `ModularCurve/IsDiamondPullbackModL` |

The two are separate stories and separate modules: A is the function-field descent for the `q`-expansion
of a differential (`LiftDGamma`'s `coeffMap`/`coeffEmb` machinery over an intermediate field of the
Laurent series), B is the mod-`λ` diamond action on the `X_H`-component. A is the row AF70 readied through
its double-coset row; B has been on the shelf since SET-AF63 and is the last of the small `ModularCurve`
rows.

## 0. The read

```bash
cd tools/deps
python3 frontier.py --ds --ready --include-leaves --rank-by silo --top 0 --json > build/shelf28.json
python3 frontier.py --selfcheck
```

| figure | value |
|---|---:|
| `needed [F terminal]` | **614 / 271,831** |
| `needed [literal]` | 627 / 275,531 |
| frontier F | 1,804 / 855,790 |
| ready rows, all namespaces | **22 / 5,229** |
| leaves, all namespaces | **159 / 41,056** |
| withheld by the FR-0044 guard | 4 / 831 |
| cone / avoided | 2,103 / 982,173 · 140 / 74,620 |

`needed` is exactly SET-AF70 §5.3's post-landing figure, so this set opens on AF70's re-read; the read was
**taken before the two scaffolds were written** (FR-0201). `--selfcheck` still FAILS on MD-005's fifteen
rows; the correction is +1 node / +75 lines as before, and no row cut here cites any of the fifteen.

## 1. What the set says

- **A** — for `Γ₁(M) ≤ Γ ≤ Γ₀(M)` and a form whose `q`-expansion lies in the Laurent base change of a
  number field `K`, the coefficient map of the differential `qExpansionDiffAlong` along
  `qExpFunctionFieldC` equals the form's `q`-expansion: the descent computation (`IsComb`, `IsRat`,
  `bcSubmodule`) that turns a `q`-expansion identity over `K` into one over `ℂ`.
- **B** — on the `X_H`-component, the diamond operator `⟨d⟩` acts through `Γ₀(M)`'s projection only for
  `d` in the image of `Γ_H(M)`: `IsDiamondPullbackModL.apply_eq_one_iff_gamma0Units_mem`, through the
  faithfulness of the `Γ_H`-action (`faith_exact`) and the `SL(2, ℤ)`-slash of `-1`.

### 1.1 The shelf, quoted whole — every row cut or deferred

**The ready block: 22 rows / 5,229 silo — 2 cut (A, B), 20 deferred.** The block is AF70's, with A
(587) and B (485) at its head: the 697-line `WeierstrassCurve` row and the 890-line
`EisensteinGeneral.Piece` row are the two largest deferred rows.

| row | silo | lev | cut |
|---|---:|---:|---|
| `EisensteinGeneral.Piece.exists_forall_nonempty_factorizationDatum` | 890 | 3/5 | deferred |
| `WeierstrassCurve.natCard_torsionOrbit_and_exists_surjective_doubleCoset_of_char_two` | 697 | 1/1 | deferred |
| `ModularCurve.exists_coeffMap_qExpansionDiffAlong_laurentBaseChange_qExpFunctionFieldC_eq_qExpansion` | 587 | 1/1 | **AF71 A** |
| `GaloisRep.exists_isSemisimpleRepresentation_charpoly_map_eq_of_trace_det_frobenius_mem_range` | 495 | 1/1 | deferred |
| `ModularCurve.IsDiamondPullbackModL.apply_eq_one_iff_gamma0Units_mem` | 485 | 1/5 | **AF71 B** |
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
| `AutomorphicForm.SiegelCovering.centreCutSiegelSet_coversModCentre_rat` | 30 | 1/6 | deferred |
| `ModularCurve.rep_tateModule_jOne_comm` | 24 | 1/6 | deferred |

**The leaves block: 159 rows / 41,056 silo — none cut, all deferred.** It is AF70's leaves block (the
`AutomorphicForm` `CuspidalConstituent`/`WindowedSiegel` group, `M4aTorus.completedRayL_fe` 12,126, the
`NumberField` Euler-product leaves and the `MeasureTheory`/`TateCurve`/`WeierstrassCurve` residue).

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
| `WeierstrassCurve.exists_variableChange_eq_legendreCurve_of_isUnit_two` | 274 | 1/2 | deferred |
| `ValuationSubring.ringKrullDim_le_ringKrullDim_comap_add_trdeg` | 269 | 1/3 | deferred |
| `NumberField.AdelicTrace.traceFinHom_apply_eq_sum_trace` | 266 | 1/1 | deferred |
| `ValuationSubring.exists_smul_mem_of_transcendental_residue` | 262 | 1/1 | deferred |
| `WeierstrassCurve.natCard_stabilizer_variableChange_eq_two_of_j_ne_zero_of_char_two_or_three` | 256 | 1/7 | deferred |
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
| `AutomorphicForm.iwasawaShellIndex_mul_of_mem_rationalCentreUnipotent` | 46 | 2/2 | deferred |
| `LanglandsTunnell.TateLocal.psiLocal_eq_one_of_mem_integers` | 45 | 4/116 | deferred |
| `NumberField.AdelicBox.isLocallyConstant_and_hasCompactSupport_indicator_image_integralFiniteAdeles` | 44 | 1/4 | deferred |
| `NumberField.AdelicBox.algebraMap_mem_image_integralFiniteAdeles_iff` | 41 | 2/3 | deferred |
| `WeierstrassCurve.Affine.Point.some_add_some_eq_neg_some_of_pow_three_eq_one` | 40 | 1/3 | deferred |
| `LanglandsTunnell.TateLocal.forall_eq_one_and_exists_ne_one_of_addCharLevel` | 37 | 3/100 | deferred |
| `ValuationSubring.charP_residueField_of_liesOverPrime` | 37 | 1/27 | deferred |
| `WeierstrassCurve.Affine.Point.some_zero_add_self_eq_neg_of_a6_model` | 34 | 1/3 | deferred |
| `AutomorphicForm.CuspidalConstituent.eq_of_isCuspConstituent_of_exists_mem_ne_zero` | 33 | 1/2 | deferred |
| `NumberField.AdeleRing.compactSpace_quotient_principalSubgroup` | 32 | 1/3 | deferred |
| `NumberField.AdelicFourier.comp_add_right_mem_pureTensorSet` | 31 | 1/1 | deferred |
| `AutomorphicForm.IsIsotypicCuspFormAt.exists_smoothCuspRealizationAt_toFun_eq_of_ne_bot` | 30 | 2/10 | deferred |
| `WeierstrassCurve.Affine.evalEval_psi_sq` | 29 | 2/44 | deferred |
| `WeierstrassCurve.Affine.Point.smul_some_eq_zero_iff` | 28 | 2/51 | deferred |
| `WeierstrassCurve.variableChange_mk_smul_eq_self_of_pow_three_eq_one` | 26 | 1/6 | deferred |
| `WeierstrassCurve.variableChange_mk_smul_eq_self_of_sq_eq_neg_one` | 26 | 1/6 | deferred |
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

## 2. The price and the homes

| module | rows | scaffold | `sorry` | `check_port` |
|---|---|---:|---:|---|
| `ModularCurve/QExpansionDifferentialLift.lean` (new) | A | **411** lines | 41 | **56 ok / 0 / 0** |
| `ModularCurve/IsDiamondPullbackModL.lean` (new) | B | **344** lines | 7 | **5 ok / 0 / 0** |

Both new, elaborating, checker-green before dispatch; the only non-`sorry` diagnostic is one
`linter.style.haveILetI` in A's engine (FR-0198, the worker's to fix). **No definition work**: every
`Def_*` module both rows import is ported (`Def_ModularCurve_X1`, `LaurentCoeff`, `QExpansionDiff`,
`XH`, `XHDiamondModL`), and every premise is ported — both rows read `needed = 1` with zero unported and
zero pruned direct premises.

**The dedup ruling.** `port_advise` on the two files reports no shared prelude (they are different
subjects and neither copies the other); the only repeats are the pin's own `open` lines. `dedup --within`
and `move_dead` are the workers' gates.

## 3. The orders and the gates

| order | rows | file | content | scaffold `sorry`s |
|---|---|---|---:|---:|
| `WORKORDER-AF71A` | A | `ModularCurve/QExpansionDifferentialLift.lean` | ≈520 | 41 |
| `WORKORDER-AF71B` | B | `ModularCurve/IsDiamondPullbackModL.lean` | ≈430 | 7 |

Gates per module: no tree build; edit loop at `-DmaxHeartbeats=200000`; `lake build <module>` under
`flock`/`timeout`; `check_port --force` unchanged (**56 ok**, **5 ok**); `#print axioms` on both
headlines; zero warnings; no `sorry`; no `set_option` beyond `autoImplicit false`; no silencer without a
recorded reason; `dedup --within` / `move_dead` clean; one consumer zone per order. The work orders are in
`lean/tmp/af71/`.

## 4. The shelf effect

*To be measured on the landed tree against §0's baseline (614 / 271,831), with the `unported ⊆ cut` rule.*
**The forecast is the accounting one — the two rows' own 1,072 silo — with the caveat the probe forces**
(AF70 §4's lesson, extended): the post-scaffold read is **contaminated**, because `frontier.py`'s name
tier counts every *declaration* of a scaffold on disk as ported, and the scaffolds carry the pin's engine
(~86 declarations each). On this tree the contaminated read is **605 / 267,705** with ready 21 / 3,900
and leaves 153 / 38,892 — i.e. it removes five nodes and ≈3,050 lines beyond the two rows, and it readies
one row that the accounting does not (`WeierstrassCurve.exists_isGalois_goodModel_inertia_faithful_of_two_ne_zero`,
599, readied by AF72's module rather than by this one). So §5 measures **only the set's own rows** and
says which read it used; a clean forecast here would need the probe `--unport`ing every declaration the
scaffolds carry, which no flag does in one command.

## 5. The landing

### 5.1 Order B — the diamond pullback modulo `λ` (landed 2026-11-14)

B in, 344 → **517** lines (**+171**, all inside the seven `sorry` bodies), 7 `sorry`s → **0**, no import
added, no `set_option` beyond the frozen `autoImplicit false`.

| file | lines | `sorry` | build | `check_port` | axioms |
|---|---:|---:|---|---|---|
| `ModularCurve/IsDiamondPullbackModL.lean` | 344 → **517** | 7 → **0** | 4,152 jobs, 10 s, silent | **5 ok / 0 / 0** | **4/4 clean** (headline + `faith_exact` + the `CohCarrier` row + `neg_one_zpow_eq_pow_natAbs`) |

The seven proofs and their pin lines: `faithCoeff_neg` (`:21`–`:26`), `faithCoeff_one` (`:28`–`:30`),
`faith_ne_neg` (`:32`–`:46`), `faith_sum_even` (`:48`–`:72`),
`CohCarrier.mem_or_neg_mem_of_mem_sup_zpowers_neg_one` (`:80`–`:95`),
`neg_one_zpow_eq_pow_natAbs` (`:363`–`:367`) and the headline (the `solution` wrapper `:374`–`:485`).
**The order's trap 1 was stale**: the 485's `faith_exact` engine (pin `:108`–`:347`) had already been
transcribed in the scaffold, so the seven `sorry`s were only the small rows and the headline.

`dedup --within`: 0 clusters, 0 removable. `move_dead`: 0 declarations. Consumer zone
`spec/ModularCurveSetAF71BConsumer.lean` (58 lines, `M = 2`, `H = ⊤`, the row fired at `d = 1`, at the
image of a `Γ_H`-unit, and in the converse direction): **0 errors, 0 warnings**.

**Heartbeat headroom**: pass at 100 k / 60 k / **55 k**, fail at 50 k (`isDefEq` in the closing `simpa`)
— floor ≈ 55 k, i.e. 27 % of the edit-loop cap and 1.4 % of the lakefile's 4 M. The headline is the cost
centre.

Deviations, all proof-side: the headline body writes the slash action as `SlashAction.map k g f` instead
of the pin's `f ∣[k] g`, because the theorem's `open scoped MatrixGroups in` does not carry
`ModularForm` (the `scoped[ModularForm]` notation dies with the `section` that closes at `:93`) and the
`open` is not the worker's to edit — **the one textual deviation of the order, kept and recorded**;
`if_false` → `ite_false` (deprecated 2026-07-21); `ModularCurve.translation_mem_GammaH` →
`CohCarrier.translation_mem_GammaH` (the port's home for the pin's `Def_ModularCurve_XH` row); the pin's
`set_option maxHeartbeats 3200000 in` dropped; and six **pre-existing** scaffold warnings cleared to
reach the empty-grep gate (`ModularForm.coe_add` → `FunLike.coe_add`, `IsGLPos.coe_smul` →
`FunLike.coe_smul` ×4, and two FR-0198 `haveI` → `have`, both probed to still register as instances).

**One tree-state finding (FR-0207).** The target's olean was missing *and*
`ModularForms.CohCarrier.DiamondDivisorSum`'s cached olean was stale — it re-elaborated (7.5 s) inside the
target build. That module's cache is not to be trusted on this tree.

### 5.2 Order A — the `q`-expansion of a differential along the base change (landed 2026-11-14)

A in, 411 → **594** lines (**+183**, 224 proof lines into 41 bodies), 41 `sorry`s → **0**, **five imports
added** (`ModularCurve.X1.QExpansionDiv`, `ModularCurve.JqIntegralRatios`, `ModularForms.QCoeffLevelOne`,
`ModularForms.CohCarrier.GammaHAlgebra` — the pin's `p2m_open` cone, spread over modules the scaffold did
not import), no `set_option` of the worker's own.

| file | lines | `sorry` | build | `check_port` | axioms |
|---|---:|---:|---|---|---|
| `ModularCurve/QExpansionDifferentialLift.lean` | 411 → **594** | 41 → **0** | 4,312 jobs, 12 s, silent | **56 ok / 0 / 0** | **7/7 clean** (headline + the six engine lemmas) |

The proofs follow the pin's body line-for-line (the worker regenerated the pin-to-port slice with
`gen71.py`'s own `transform` and diffed: only proof bodies differ). `dedup --within`: 0 clusters; the two
pre-filled engine lemmas (`isRat_of_mem`, `mem_laurentBaseChange_of_coeffMap_mem`) were left untouched.
`move_dead`: 0. Consumer zone `spec/ModularCurveSetAF71AConsumer.lean` (`M = 2`, `Γ = Γ₁(2)`,
`ι₀ = IsAlgClosed.lift`, `f = 0`, reading the `qL` consistency and `coeffMap` at `n = 1`): **0 errors,
0 warnings**.

**Heartbeat headroom**: silent at 32 k / 28 k, first failures at 24 k — floor ≈ 26 k, ≈7× under the
edit-loop cap; the binding consumers are the pin's own `mem_laurentBaseChange_of_coeffMap_mem` and
`xBar_mem`, not the new transcription.

Deviations, all proof-side except two `omit` prefixes: `omit [Algebra ℚ K] in` on `exists_retraction` and
`linearIndependent_coeffMap` (the pin silences `unusedSectionVars` file-wide there; the instance is dead
in both elaborated statements, and the checker stays 56 / 0 / 0); `haveI` → `have` (FR-0198) and the
sibling `letI` → `let`; `push_neg` → `push Not` at two sites; `ModularForm.coe_zero` →
`FunLike.coe_zero` at two; the pin's `first | exact this | …` pruned to `exact this` (the other branches
are unreachable tactics in this mathlib); and the headline calls `ModularCurve.QExpansionLift.omega`
qualified, since the pin's `open … LiftDGamma in` is not part of the frozen header.

### 5.3 The set's numbers, and the plan-vs-actual

| figure | before (opening read) | **after** | forecast |
|---|---:|---:|---:|
| `needed [F terminal]` | 614 / 271,831 | **610 / 270,200** | −4 / −1,631 (both sets) ✓ exact |
| ready rows | 22 / 5,229 | **22 / 4,790** | −2 / −1,072, and **two rows readied** |
| leaves | 159 / 41,056 | **157 / 40,497** | −2 / −559 (AF72's share) ✓ exact |

**Both readiness returns are genuine, and both were missed by the forecasts.** This set readies the
34-line `ModularCurve.exists_coeffMap_diffQExp_x1FunctionFieldBar_eq_qExpansion` (A's consumer) and the
sibling set readies the 599-line
`WeierstrassCurve.exists_isGalois_goodModel_inertia_faithful_of_two_ne_zero` (whose only premise is
AF72's A row); 5,229 − 1,072 + 34 + 599 = **4,790** ✓. The §4 forecast said "not readied here, because
their own demands still hold the other row" — wrong on both counts, and the reason is the same as
AF72 §5.2's: a row being in the *leaves* block says its premises are ported, not that its consumers are
already satisfied.

**A read-cleanliness lesson (FR-0215).** The first post-landing read was 605 / 267,705 with ready
21 / 3,900 — off by five nodes and ~3,050 lines — because three **abandoned scaffolds** (a broken
`EisensteinGeneral/Piece*` pair and a `WeierstrassCurve/Automorphism/Stabilizer`) were still on disk, and
the frontier's name tier counts every declaration of every port file as ported. Deleting them (and the
orphan `Factorization/Datum.lean`, whose `hasseInvariant`/`legendreCurve` names also shadow graph nodes)
makes the read exact. **An abandoned scaffold must be deleted in the same touch, not left for the next
wave.**

Plan vs actual: the cut was exact; the price was **407 written proof lines against a ≈950-net estimate
(0.43×)** — the `∃`-headed statement-surface effect once more — and the wave's one failure was the
FR-0207 cache staleness of `CohCarrier/DiamondDivisorSum`.
