# SET-AF72 — the Legendre normal form and the finite automorphism group

**Status: LANDED (2026-11-14).** Read off the D–S shelf after SET-AF70 with the recipe in
[../deligneSerre/TOPIC-scoping-a-ds-set.md](../deligneSerre/TOPIC-scoping-a-ds-set.md). The seventy-second
set of the column, and the first that **opens a `Def_` layer of its own**: the two rows sit in the leaves
block, and their statements need `WeierstrassCurve.hasseInvariant`/`legendreCurve`, which the port did not
have.

**2 rows / 559 silo / ≈500 net** in **one new module**, one order (two rows in one subject).

| # | row | silo | lev | home |
|---|---|---:|---:|---|
| **A** | `WeierstrassCurve.exists_variableChange_eq_legendreCurve_of_isUnit_two` | 274 | 1/2 | new `WeierstrassCurve/Automorphism/NormalForm` |
| **B** | `WeierstrassCurve.finite_stabilizer_variableChange` | 285 | 1/10 | same module |

The two are one subject — the normal form of a curve over a ring where `2` is a unit, and the finiteness
of its automorphism group — and they are the two rows of the `WeierstrassCurve` leaves block that the
manager's new definition layer unlocks.

## 0. The read

```bash
cd tools/deps
python3 frontier.py --ds --ready --include-leaves --rank-by silo --top 0 --json > build/shelf28.json
python3 frontier.py --selfcheck
```

| figure | value |
|---|---:|
| `needed [F terminal]` | **614 / 271,831** |
| ready rows, all namespaces | **22 / 5,229** |
| leaves, all namespaces | **159 / 41,056** |
| `WeierstrassCurve` demand | **27 / 8,717** (of which 23 rows in the leaves block) |
| withheld by the FR-0044 guard | 4 / 831 |

`needed` is exactly SET-AF70 §5.3's post-landing figure; the read was **taken before the scaffold was
written** (FR-0201). `--selfcheck` still FAILS on MD-005's fifteen rows; no row cut here cites any of
them.

## 1. What the set says

- **A** — over a base in which `2` is a unit, every elliptic curve is isomorphic to the Legendre curve
  `y² = x(x - 1)(x - t)`: the valuation-ring splitting of the two-torsion cubic (`section Val`) and the
  model computation (`section Model`, `variableChange_eq_legendre`), then the local statement `main` at
  a valuation ring `A` with `IsUnit (2 : A)`.
- **B** — the stabilizer of an elliptic curve in the group of variable changes is finite: the unipotent
  part is cut out by polynomial identities (`ccgaf_quad/cubic/quart`), the diagonal part satisfies
  `u ^ 12 = 1` (`ccgaf_u_pow_twelve`), and the two give `ccgaf_stabilizer_finite` through the monoid
  homomorphism `ccgaf_uHom`.

### 1.1 The shelf, quoted whole — every row cut or deferred

**The ready block: 22 rows / 5,229 silo — none cut, all deferred** (SET-AF71 §1.1 quotes it whole and cuts
its two rows).

**The leaves block: 159 rows / 41,056 silo — 2 cut (A, B), 157 deferred.** The `WeierstrassCurve` rows it
holds are the automorphism/normal-form family (the `IsCharTwoJNeZeroNF`/`IsCharThreeJNeZeroNF` rows that
need a further definition layer are **deferred**, not cut: the char-two/three normal-form classes are not
in the port, and this set does not open that layer).

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
| `WeierstrassCurve.finite_stabilizer_variableChange` | 285 | 1/10 | **AF72 B** |
| `AutomorphicForm.WindowedSiegel.isCompact_centreCutSiegelSet_inter_heightCap` | 282 | 5/10 | deferred |
| `WeierstrassCurve.exists_variableChange_eq_legendreCurve_of_isUnit_two` | 274 | 1/2 | **AF72 A** |
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

## 2. The price and the home

| module | rows | scaffold | decls | `sorry` | `check_port` |
|---|---|---:|---:|---:|---|
| `WeierstrassCurve/Automorphism/NormalForm.lean` (new) | A, B | **193** lines | 22 | 21 | **22 ok / 0 / 0** |

**The manager's definition layer.** `Definitions/Def_WeierstrassCurve_HasseInvariant.lean` (24 lines) is
transcribed in `WeierstrassCurve/Defs/HasseInvariant.lean`: `WeierstrassCurve.hasseInvariant` (the
coefficient of degree `q - 1` in the `(q - 1)/2`-th power of the two-torsion cubic),
`WeierstrassCurve.legendreCurve t = ⟨0, -(1 + t), 0, t, 0⟩` and `ModularCurve.ssJSetHasse` (the
supersingular locus). A's statement needs `legendreCurve`; the other two are the module's completion
(the definition file is small and the whole `Def_` node is transcribed, not a slice of it).

**The dedup ruling.** The two pin files share nothing (different engines: the valuation-ring/model
computation against the polynomial tools of the stabilizer); `dedup --within` and `move_dead` are the
worker's gates.

## 3. The order and the gates

| order | rows | file | content | scaffold `sorry`s |
|---|---|---|---:|---:|
| `WORKORDER-AF72A` | A, B | `WeierstrassCurve/Automorphism/NormalForm.lean` | ≈500 | 21 |

Gates: no tree build; edit loop at `-DmaxHeartbeats=200000`; `lake build` under `flock`/`timeout`;
`check_port --force` unchanged (**22 ok**); `#print axioms` on both headlines; zero warnings; no `sorry`;
no `set_option` beyond `autoImplicit false`; no silencer without a recorded reason; `dedup --within` /
`move_dead` clean; one consumer zone. The work order is in `lean/tmp/af71/` (shared with SET-AF71, which
was dispatched at the same time).

## 4. The shelf effect

*To be measured on the landed tree against §0's baseline (614 / 271,831), with the `unported ⊆ cut` rule.*
The two rows are leaves: their own 559 silo is what the set consumes, and — as with SET-AF69 — a leaf's
consumers are already ported, so **no row above them becomes ready** and the leaves block falls by
2 / 559. The post-scaffold probe is contaminated by the scaffolds' declarations (SET-AF71 §4), so §5
measures the two rows only.

## 5. The landing

### 5.1 The order — the normal form and the finite stabilizer (landed 2026-11-14)

A, B in, 195 → **582** lines (**+387** proof lines over 21 `sorry`s), 21 `sorry`s → **0**, **no import
added**, no `set_option` beyond the frozen `autoImplicit false`.

| file | lines | `sorry` | build | `check_port` | axioms |
|---|---:|---:|---|---|---|
| `WeierstrassCurve/Automorphism/NormalForm.lean` | 195 → **582** | 21 → **0** | 3,096 jobs, 6.8 s, silent | **22 ok / 0 / 0** | **2/2 clean** |

A's proofs: `val_lambda` (pin `:23`–`:106`), `legendre_Δ`/`legendre_c₄`/`legendre_map`
(`:115`–`:126`), `variableChange_eq_legendre` (`:134`–`:180`), `j_legendre_mul` (`:184`–`:192`),
`j_mul_of_legendre` (`:199`–`:209`), `main` (`:220`–`:261`); B's: the six `ccgaf_*` polynomial tools
(`:16`–`:42`), `ccgaf_coeff_eqs` (`:59`–`:75`), `ccgaf_finite_unipotentStabilizer` (`:85`–`:216`),
`ccgaf_uHom_apply`/`ccgaf_u_pow_twelve` (`:229`–`:241`) and `ccgaf_stabilizer_finite` (`:245`–`:273`).
`dedup --within`: **1 cluster / 18 lines**, the pin's own `main`-vs-headline pair — the wrapper-over-engine
pattern, kept. `move_dead`: 0. Consumer zone `spec/WeierstrassCurveSetAF72AConsumer.lean` (headline A at
`ℚ`, `⊤`, `legendreCurve 2` with the roots `{0,1,2}` computed in-file and `(l : ℚ) = 2`; headline B at
`ℚ`, `legendreCurve 2` with `IsElliptic` carried): **0 errors, 0 warnings**.

**Heartbeat headroom**: the whole module elaborates at **20,000** (10× under the cap); first failure at
10,000 in `val_lambda`.

Deviations, all forced by v4.34 linters, none by a silencer: `j_mul_of_legendre` replaces the pin's
`haveI : (legendreCurve l).IsElliptic` (which trips `linter.style.haveILetI`) by a `have` over explicit
instance binders using the pin's own `rintro _ _ rfl` device; six further `haveI` → `have` (`have` still
registers local instances in this Lean — verified load-bearing); `zero_le'` → `zero_le` (6×); and the
dead `[E.IsElliptic]` section instance of `variableChange_eq_legendre` is **spent** (`have hΔ : IsUnit
E.Δ := E.isUnit_Δ`), not omitted. The pin silences `unusedSectionVars` file-wide; the port does not.

### 5.2 The set's numbers

| figure | before (opening read) | **after** | forecast |
|---|---:|---:|---:|
| `needed [F terminal]` | 614 / 271,831 | **610 / 270,200** | −4 / −1,631 (both sets) ✓ |
| ready rows | 22 / 5,229 | **22 / 4,790** | 0 / 0 ✗ — **1 row readied** |
| leaves | 159 / 41,056 | **157 / 40,497** | −2 / −559 ✓ exact |

**The readability return is genuine and the forecast missed it**: A readies the 599-line
`WeierstrassCurve.exists_isGalois_goodModel_inertia_faithful_of_two_ne_zero`, whose only premise it is —
verified against the graph, and visible in the measured ready block. So this set consumes **559 silo and
readies 599** (1.07 readied per consumed), the column's best ratio, and its consumer is the
`ModularCurve` torsion-reduction family (four further consumers, one of 4,896 lines). The §4 forecast said
"no row above them becomes ready" because the two rows are leaves — the mistake was assuming a leaf's
consumers are all already ported (they are, for the row itself, but this one row was *not* ported, it was
merely in the ready block of the *pin's* closure; the ready/leaves partition is not a statement about a
row's consumers).

Plan vs actual: the cut was exact; the price was **387 written proof lines against a ≈500-net estimate
(0.77×)**; the manager's Def layer (24 lines) was the gate; and the wave's only friction was the stale
cache of `ModularForms/CohCarrier/DiamondDivisorSum` in the sibling order (FR-0207).
