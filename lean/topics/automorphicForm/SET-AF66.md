# SET-AF66 — the coset-sum slash block, and the existence of a primitive form

**Status: DISPATCHED (2026-11-14).** Read off the D–S shelf after SET-AF65 with the recipe in
[../deligneSerre/TOPIC-scoping-a-ds-set.md](../deligneSerre/TOPIC-scoping-a-ds-set.md). The sixty-sixth
set of the column, and the set that continues AF65 §5.3's named chain: the primitive-form block.

**9 rows / 1,600 silo / ≈1,360 net** in **two new modules**, two orders.

| # | row (`CuspForm.` dropped) | silo | lev | home |
|---|---|---:|---:|---|
| **A** | `exists_gamma1_apply_eq_conj_and_qCoeff_eq_conj` | 126 | 3/8 | new `ModularForms/PrimitiveFormSlash` |
| **B** | `exists_gamma1_apply_eq_zpow_mul_apply_of_mul_eq_neg_one` | 168 | 1/1 | same module |
| **C** | `isPrimitiveForm_inv_of_qCoeff_eq_conj` | 177 | 1/6 | same module |
| **D** | `exists_apply_eq_mul_zpow_mul_apply_of_isPrimitiveForm` | 115 | 1/2 | same module |
| **E** | `IsPrimitiveForm.sum_slash_S_mul_T_zpow_mul_S_inv_apply_eq_of_dvd` | 188 | 1/1 | same module |
| **F** | `IsPrimitiveForm.sum_slash_S_mul_T_zpow_mul_S_inv_comp_heckeDiagMatrix_apply_eq_of_not_dvd` | 250 | 1/1 | same module |
| **G** | `exists_isPrimitiveForm_of_hasNebentypus_qCoeff_hecke_eigen` | 253 | 1/10 | new `ModularForms/PrimitiveFormExistence` |
| **H** | `exists_isPrimitiveForm_of_qCoeff_hecke_eigen` | 254 | 1/4 | same module |
| **I** | `exists_apply_eq_conj_apply_J_smul_of_forall_jConjSL_mem` *(leaf)* | 69 | 2/3 | same module |

**Order A is one chain and it is the cut the graph dictates**: A (the conjugate form) is ready, C needs A,
D needs B and C, and E and F need D — and **E and F together readies the 802-line
`IsPrimitiveForm.pow_dvd_of_pow_dvd_of_sq_dvd_of_factorsThrough_of_forall_coprime_qCoeff_eq`**, which is a
premise of the 907-line `level_eq_and_qCoeff_eq_…`, which readies the 277, which with AF65's four `Γ_H`
rows readies the 419. That is the deepest chain the column has cut, and this set is its first two links.
**Order B is the existence half**: G and H are the two `exists_isPrimitiveForm_…` rows (ready now, and their
consumers include the D–S cone's `DeligneSerre.exists_tsum_norm_qCoeff_sq_mul_rpow_le_log_of_weightOne_hecke_eigen`),
plus the `j`-conjugation leaf I.

## 0. The read

```bash
cd tools/deps
python3 frontier.py --ds --ready --include-leaves --rank-by silo --top 0 --json > build/shelf23.json
python3 frontier.py --selfcheck
```

| figure | value |
|---|---:|
| `needed [F terminal]` | **644 / 279,728** |
| `needed [literal]` | 657 / 283,428 |
| frontier F | 1,774 / 847,893 |
| ready rows, all namespaces | **23 / 4,704** |
| leaves, all namespaces | **174 / 43,385** |
| `CuspForm` demand | 17 / 5,648 |
| withheld by the FR-0044 guard | 4 / 831 |
| cone / avoided | 2,103 / 982,173 · 140 / 74,620 |

`needed` is exactly SET-AF65's post-landing figure, so this set opens on AF65's re-read; **the read was
taken before the two scaffolds were written** (FR-0201). `--selfcheck` still FAILS on MD-005's fifteen rows;
the correction is +1 node / +75 lines (`645 / 279,803`), unchanged. No row cut here cites any of the fifteen.

## 1. What the set says

- **A** — a `Γ₁(N)`-cusp form is determined by its conjugate: `∃ g, g = conj ∘ f ∧ ∀ n, qCoeff g n =
  conj (qCoeff f n)`.
- **B** — the Fricke half: for `d² = 1`, `∃ g, ∀ τ, g τ = d ^ k • f (d⁻¹ • τ)`.
- **C** — the inverse of a primitive form (in the `q`-coefficient sense) is primitive.
- **D** — the Fricke pseudo-eigenvalue for a primitive form: `∃ c, ∀ τ, g (d • τ) = c • g τ` with `c` a
  `d ^ k`-multiple, from B plus the conjugacy of the eigenvalue (AF63's row).
- **E, F** — the two halves of the `S · T^{z} · S⁻¹` coset sum: readable at `d ∣ n` (the `q`-coefficients
  of the sum), and collapsing under `heckeDiagMatrix q` at `q ∤ n`.
- **G, H** — every Hecke eigenform (with or without a nebentypus) has a *primitive* form with the same
  eigenvalues: the `q`-expansion of a primitive form's degeneracy lifts.
- **I** — a cusp form invariant under the `j`-conjugation on `SL(2, ℤ)` is determined by `J • τ`'s values.

### 1.1 The shelf, quoted whole — every row cut or deferred

**The ready block: 23 rows / 4,704 silo — 4 cut (A, B, G, H), 19 deferred.** The block's top is unchanged
(`EisensteinGeneral` 890, the `GaloisRep` semisimplicity row 495, the `ModularCurve` diamond row 485); the
`CuspForm` rows on it are now exactly this set's primitive-form block plus three `AutomorphicForm` residues.

| row | silo | lev | cut |
|---|---:|---:|---|
| `EisensteinGeneral.Piece.exists_forall_nonempty_factorizationDatum` | 890 | 3/5 | deferred |
| `GaloisRep.exists_isSemisimpleRepresentation_charpoly_map_eq_of_trace_det_frobenius_mem_range` | 495 | 1/1 | deferred |
| `ModularCurve.IsDiamondPullbackModL.apply_eq_one_iff_gamma0Units_mem` | 485 | 1/5 | deferred |
| `AutomorphicForm.exists_finset_forall_exists_mem_valued_eq_max_and_contentHomFin_mul_sq_eq` | 333 | 1/1 | deferred |
| `LanglandsTunnell.TateLocal.integral_comp_inv_eq_integral_modulus_inv_sq_mul_adicCompletion` | 305 | 1/7 | deferred |
| `CuspForm.exists_isPrimitiveForm_of_qCoeff_hecke_eigen` | 254 | 1/4 | **cut H** |
| `CuspForm.exists_isPrimitiveForm_of_hasNebentypus_qCoeff_hecke_eigen` | 253 | 1/10 | **cut G** |
| `CohCarrier.exists_surjective_doubleCoset_gammaH_zpowers_of_addOrderOf_eq` | 252 | 1/1 | deferred |
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

**The leaves block: 174 rows / 43,385 silo — 1 cut (I), 173 deferred.** It still holds the
`AutomorphicForm` `CuspidalConstituent`/`WindowedSiegel` group, `M4aTorus.completedRayL_fe` (12,126), the
`NumberField` Euler-product leaves and the `MeasureTheory`/`TateCurve`/`WeierstrassCurve` residue — all
unchanged from SET-AF65 §1.1 but for AF65's three rows.

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
| `ContinuousLinearMap.eq_zero_of_forall_exists_mem_sub_real_smul_eq` | 385 | 1/2 | deferred |
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
| `ContinuousLinearMap.le_ker_or_finiteDimensional_of_forall_inf_highPart_orthogonal` | 276 | 1/1 | deferred |
| `ContinuousLinearMap.orthogonal_iSup_eigenspace_ne_zero_eq_ker` | 275 | 2/4 | deferred |
| `ContinuousLinearMap.map_highPart_orthogonal_le_of_commute` | 275 | 1/1 | deferred |
| `WeierstrassCurve.exists_variableChange_eq_legendreCurve_of_isUnit_two` | 274 | 1/2 | deferred |
| `ValuationSubring.ringKrullDim_le_ringKrullDim_comap_add_trdeg` | 269 | 1/3 | deferred |
| `NumberField.AdelicTrace.traceFinHom_apply_eq_sum_trace` | 266 | 1/1 | deferred |
| `ValuationSubring.exists_smul_mem_of_transcendental_residue` | 262 | 1/1 | deferred |
| `WeierstrassCurve.natCard_stabilizer_variableChange_eq_two_of_j_ne_zero_of_char_two_or_three` | 256 | 1/7 | deferred |
| `CohCarrier.charInvolution_comp_opFamily` | 247 | 1/3 | deferred |
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
| `ContinuousLinearMap.comp_eq_of_forall_apply_eq_integral_smul_apply_of_convolution` | 180 | 1/1 | deferred |
| `NumberField.AdelicFourier.exists_smul_eq_of_isAddHaarMeasure_adeleRing` | 179 | 2/4 | deferred |
| `ValuationSubring.natDegree_map_eq_card_roots_of_splits` | 174 | 1/1 | deferred |
| `NumberField.AdelicLevel.diagOne_eq_diagOne_mul_archRealLiftAt_mul_centralScalar` | 172 | 3/3 | deferred |
| `HaarQuotient.lintegral_density_mul_eq_one` | 170 | 2/39 | deferred |
| `CuspForm.exists_gamma1_apply_eq_zpow_mul_apply_of_mul_eq_neg_one` | 168 | 1/1 | **cut B** |
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
| `CuspForm.exists_gamma1_apply_eq_conj_and_qCoeff_eq_conj` | 126 | 3/8 | **cut A** |
| `EisensteinGeneral.Piece.integral_smul_add_mul_addChar_neg_mul_eq` | 125 | 4/6 | deferred |
| `AutomorphicForm.mem_rationalCentreUnipotent_iff_heckeGen_mul_centralScalar_conj_mem` | 119 | 1/1 | deferred |
| `NumberField.AdeleRing.exists_isOpen_inter_principalIdeles_eq_singleton` | 118 | 1/4 | deferred |
| `IsDedekindDomain.HeightOneSpectrum.isAdicComplete_adicCompletionIntegers` | 111 | 1/12 | deferred |
| `NumberField.AdelicBox.integralFiniteAdeles_subset_closure_range_algebraMap_ringOfIntegers` | 109 | 2/2 | deferred |
| `ContinuousLinearMap.exists_forall_apply_eq_integral_smul_apply_of_forall_norm_le_of_continuous` | 108 | 2/2 | deferred |
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
| `CohCarrier.H1_moduleFinite` | 74 | 1/70 | deferred |
| `NumberField.Idele.sPartMeasure_pos_of_isOpen_of_partAt_eq` | 73 | 1/1 | deferred |
| `NumberField.mixedEmbedding.exists_forall_norm_embedding_sub_le` | 71 | 1/1 | deferred |
| `WeierstrassCurve.exists_valuationSubring_with_transcendental_of_charZero` | 70 | 1/2 | deferred |
| `NumberField.AdelicBox.exists_denom_of_hasCompactSupport` | 70 | 1/1 | deferred |
| `NumberField.summable_heightOneSpectrum_absNorm_rpow_neg_of_one_lt` | 69 | 7/41 | deferred |
| `CuspForm.exists_apply_eq_conj_apply_J_smul_of_forall_jConjSL_mem` | 69 | 2/3 | **cut I** |
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
| `CohCarrier.exists_eq_gammaH_of_gamma1_le_of_le_gamma0` | 49 | 1/11 | deferred |
| `AutomorphicForm.iwasawaShellIndex_mul_of_mem_rationalCentreUnipotent` | 46 | 2/2 | deferred |
| `LanglandsTunnell.TateLocal.psiLocal_eq_one_of_mem_integers` | 45 | 4/116 | deferred |
| `NumberField.AdelicBox.isLocallyConstant_and_hasCompactSupport_indicator_image_integralFiniteAdeles` | 44 | 1/4 | deferred |
| `NumberField.AdelicBox.algebraMap_mem_image_integralFiniteAdeles_iff` | 41 | 2/3 | deferred |
| `WeierstrassCurve.Affine.Point.some_add_some_eq_neg_some_of_pow_three_eq_one` | 40 | 1/3 | deferred |
| `ContinuousLinearMap.map_eigenspace_orthogonal_le_of_commute` | 40 | 1/2 | deferred |
| `LanglandsTunnell.TateLocal.forall_eq_one_and_exists_ne_one_of_addCharLevel` | 37 | 3/100 | deferred |
| `ValuationSubring.charP_residueField_of_liesOverPrime` | 37 | 1/27 | deferred |
| `WeierstrassCurve.Affine.Point.some_zero_add_self_eq_neg_of_a6_model` | 34 | 1/3 | deferred |
| `AutomorphicForm.CuspidalConstituent.eq_of_isCuspConstituent_of_exists_mem_ne_zero` | 33 | 1/2 | deferred |
| `CohCarrier.index_gammaH_eq_index_gamma0_mul_index` | 32 | 1/22 | deferred |
| `NumberField.AdeleRing.compactSpace_quotient_principalSubgroup` | 32 | 1/3 | deferred |
| `NumberField.AdelicFourier.comp_add_right_mem_pureTensorSet` | 31 | 1/1 | deferred |
| `AutomorphicForm.IsIsotypicCuspFormAt.exists_smoothCuspRealizationAt_toFun_eq_of_ne_bot` | 30 | 2/10 | deferred |
| `WeierstrassCurve.Affine.evalEval_psi_sq` | 29 | 2/44 | deferred |
| `WeierstrassCurve.Affine.Point.smul_some_eq_zero_iff` | 28 | 2/51 | deferred |
| `WeierstrassCurve.variableChange_mk_smul_eq_self_of_pow_three_eq_one` | 26 | 1/6 | deferred |
| `WeierstrassCurve.variableChange_mk_smul_eq_self_of_sq_eq_neg_one` | 26 | 1/6 | deferred |
| `CohCarrier.exists_gamma0_lift_dvd` | 25 | 1/10 | deferred |
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

| module | rows | scaffold | decls | `sorry` | `check_port` |
|---|---|---:|---:|---:|---|
| `ModularForms/PrimitiveFormSlash.lean` (new) | A–F | **630** lines | 90 | 90 | **104 ok / 0 / 0** |
| `ModularForms/PrimitiveFormExistence.lean` (new) | G–I | **235** lines | 19 | 19 | **24 ok / 0 / 0** |

Both new, disjoint, **elaborating at the low cap with `error` empty** (FR-0206's gate, applied as a command
this time) and checker-green before dispatch. Two scaffold findings: each of the nine pin files opens its own
namespace vocabulary *before* its namespace line, so the slice must start at the first `open` (a slice that
starts at `namespace` loses `Gamma1`/`qCoeff`/`mapGL` — the AF64 class of scaffold bug); and the `jConj`
leaf needs `FLTForHuman.ModularCurve.PeriodHomPair` for `ModularCurve.Period.jConjSL`.

**The dedup ruling: nothing to cut.** The nine pin files do not copy each other's preludes; the two modules'
namespaces are disjoint; the only repeats are the pin's own `open` lines. `dedup --within` and
`move_dead --dry-run` are the workers' gates.

**The premise audit.** A, B and I have no `Thm_` premise. C needs A; D needs B, C, AF63's
`conj_heckeEigenvalue_eq_of_hasNebentypus` and AF65's `eq_smul_of_isPrimitiveForm_of_qCoeff_hecke_eigen`; E
and F need A, C, D, AF65's `exists_gamma1_coe_eq_heckeU_of_dvd` (`HeckeULevel.lean`) and
`ModularFormClass.eq_of_forall_qCoeff_eq`; G and H need AF65's newform decomposition and each other's
`exists_hasNebentypus_of_qCoeff_hecke_eigen` (ported). All verified present before dispatch.

## 3. The orders and the gates

| order | rows | file | content | scaffold `sorry`s |
|---|---|---|---:|---:|
| `WORKORDER-AF66A` | A → B → C → D → E, F | `ModularForms/PrimitiveFormSlash.lean` | ≈880 | 90 |
| `WORKORDER-AF66B` | G, H, I | `ModularForms/PrimitiveFormExistence.lean` | ≈480 | 19 |

Gates per module: no tree build; edit loop at `-DmaxHeartbeats=200000`; `lake build <module>` under
`flock`/`timeout`; `check_port --force` unchanged (**104 ok**, **24 ok**); `#print axioms` on all nine
headlines; zero warnings; no `sorry`; no `set_option` beyond `autoImplicit false`; no silencer;
`dedup --within` / `move_dead` clean; one consumer zone per order. The work orders are in `lean/tmp/af66/`.

## 4. The shelf effect

*To be measured on the landed tree against §0's baseline (644 / 279,728), with the `unported ⊆ cut` rule.*
The forecast: `needed` falls by this set's own 1,600 silo, and **one row is readied** — the 802-line
`IsPrimitiveForm.pow_dvd_of_pow_dvd_of_sq_dvd_of_factorsThrough_of_forall_coprime_qCoeff_eq`, whose only
unported premises are E and F. Nothing else, because the 907 needs the 802 (readied, not ported) and the 419
needs the 277. So the return is **1 row / 802 silo for 1,600 consumed (0.50)** — and the next cut is the
pair `802 → 907`, which is AF67's order A.

## 5. The landing

### 5.1 Order A — the conjugate form, the Fricke action and the coset sums (landed 2026-11-14)

All six rows in, **+401 net lines** over the 630-line scaffold (630 → **1,031**), 90 `sorry`s → **0**, two
imports added (`HeckeNebentypusFricke` for row D's premise, `HeckeFrickeTrace` for E/F's coset identity),
no `set_option` beyond the frozen `autoImplicit false`.

| file | lines | decls | `sorry` | build | `check_port` | axioms |
|---|---:|---:|---:|---|---|---|
| `ModularForms/PrimitiveFormSlash.lean` | 630 → **1,031** | 104 | 90 → **0** | 4,318 jobs, silent | **104 ok / 0 / 0** | **6/6 clean** |

`dedup --within`: **17 clusters / 112 lines**, all `[intra]` and all the pin's own — each of the six pin
namespaces keeps its own copy of the Fricke/conjugation prelude (`frickeGL`, `det_frickeGL_pos`,
`qCoeff_zero_fun`, `conjNeg`, `conjNeg_apply_*`, `one_mem_strictPeriods`, `analytic`, `qCoeff_smul`,
`ne_zero_of_isPrimitiveForm`), which the 104-declaration pinned API requires; kept, as AF64/AF65 ruled.
`move_dead`: 0 declarations. Consumer zone `spec/ModularFormsSetAF66AConsumer.lean` (229 lines, 16
declarations, six zones incl. the A→C composition and the `z = 0` splits of E and F): **0 errors, 0
warnings**.

**Deviations**, all v4.34 drift: the renames the column knows (`FunLike.coe_*`, `ite_eq_left`,
`smul_apply`/`zero_apply`/`sub_apply` for the deprecated `CuspForm.IsGLPos.smul_apply` family), `haveI` →
`have` at six sites, `Subtype.ext` before `ext` in `conjNeg_conjNeg` (v4.34's `ext` picks an ℝ-entry
lemma), the `SL → GL` coercion rewrites in `J_mul_coe_mul_J`, one pin clause whose rewrite target is the
goal rather than `this`, and — the interesting one — **`OldFormCosetSum.qCoeff_sub`'s frozen statement
carries an unused `[NeZero M]`**, where `linter.unusedSectionVars` fires: the proof now spends
`NeZero.ne M` (and `periodic f`), which keeps the statement byte-identical and the module silent (FR-0208,
the FR-0198 class in a new linter).

**Two tree-state notes.** Row D's premise module `HeckeNebentypusFricke` had **no `.olean`** on the tree
(30 oleans were absent, including `HeckeEigenNebentypus`), so the worker built that one target first —
targeted, not tree-wide. And the scaffold carried four pre-existing deprecation warnings
(`CuspForm.coe_smul`, three `CuspForm.coe_zero`) which the worker rewrote for the silence gate: my
scaffold gate greps `error` (FR-0206) and therefore does not see deprecations, which is why the work orders
say zero warnings is the *worker's* gate.

### 5.2 Order B — the existence of a primitive form behind an eigenform (landed 2026-11-14)

All three rows in, 235 → **572** lines (+337 net), 19 `sorry`s → **0**, one import added
(`HeckeNebentypusExistence`, row H's premise), no `set_option`.

| file | lines | decls | `sorry` | build | `check_port` | axioms |
|---|---:|---:|---:|---|---|---|
| `ModularForms/PrimitiveFormExistence.lean` | 235 → **572** | 24 | 19 → **0** | 4,320 jobs, silent | **24 ok / 0 / 0** | **3/3 clean** |

Silent at 40,000 heartbeats (≥5× headroom); `dedup --within` 8 clusters / 125 lines, all pin-forced (the two
word-name label namespaces `PrimitiveFormOfEigenvector`/`PrimitiveFormOfEigenform` over one helper set, plus
G's headline being the `main` wrapper the pin's own `solution` is); `move_dead` 0; consumer zone
`spec/ModularFormsSetAF66BConsumer.lean` (118 lines, four zones) **0 errors**.

**This order found and repaired the tree's latent build break** (FR-0207): `HeckeNebentypusExistence.lean`
did not compile at HEAD — `Ambiguous term T_mem_Gamma1`, two namespaces both in scope via that file's own
two `open`s — and its `.olean` was only ever a prebuilt cache; another order's cascade rebuilt
`HeckeEigenNebentypus.olean`, lake re-elaborated the module, the rebuild failed and **lake deleted the
olean, blocking every importer**. The one-line qualification
(`CuspForm.HeckeEigenNebentypus.T_mem_Gamma1 M`, reviewed and adopted by the manager) restores it;
`lake build HeckeNebentypusExistence` → 4,144 jobs, zero errors. The lesson is in FR-0207: a green
`lake build <module>` over cached oleans says nothing about the modules it did not re-elaborate.

Remaining deviations, all proof-side: `ite_eq_left`/`ite_eq_right`, `have` for `haveI` (FR-0198),
`FunLike.coe_zero`, and dropping a now-unneeded `haveI : NeZero M` in `changeLevel_apply_natCast`.

### 5.3 The set's numbers, and the plan-vs-actual

| figure | before (opening read) | **after** | forecast |
|---|---:|---:|---:|
| `needed [F terminal]` | 644 / 279,728 | **635 / 278,128** | −9 / −1,600 ✓ exact |
| `needed [literal]` | 657 / 283,428 | **648 / 281,828** | −9 / −1,600 ✓ exact |
| ready rows | 23 / 4,704 | **22 / 4,999** | +1 / +802 ✓ exact |
| leaves | 174 / 43,385 | **171 / 43,022** | −3 / −363 ✓ |
| `CuspForm` demand | 17 / 5,648 | **8 / 4,048** | −9 / −1,600 ✓ exact |

**The return forecast was exact, for the second set running**: one row readied, the 802-line
`IsPrimitiveForm.pow_dvd_of_pow_dvd_…`, at 0.50 readied silo per consumed silo. That is the third
independent confirmation that the `unported ⊆ cut` rule (introduced after AF64's mis-forecast) is the right
one.

Plan vs actual: the cut was exact (nine rows, 1,600 silo); the dedup came out as ruled (nothing in-module
cuttable, 25 clusters / 237 lines of pin-inherent repeats recorded across the two modules); the price was
738 written proof lines against a 1,360-net estimate — the column's ratio for prelude-heavy rows again; and
the wave's one failure was **not** a proof: it was the latent hub break, found at first belief by order B's
worker and repaired in one line. Frictions: **FR-0207** (the two-`open` name collision, a latent build break
hidden by a cached olean) and **FR-0208** (`unusedSectionVars` on a frozen statement, resolved by spending
the witness).

## 6. Reproduce


```bash
cd tools/deps
python3 frontier.py --ds --ready --include-leaves --rank-by silo --top 0 --json > build/shelf23.json
python3 frontier.py --selfcheck
cd .. && python3 lean/tmp/af66/gen66.py --force   # the two scaffolds (before the opening read; §0)
cd lean && python3 spec/check_port.py --force FLTForHuman/ModularForms/PrimitiveFormSlash.lean
python3 spec/check_port.py --force FLTForHuman/ModularForms/PrimitiveFormExistence.lean
```
