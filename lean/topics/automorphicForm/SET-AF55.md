# SET-AF55 — the archimedean cut's closure, and the cuspidal carrier's window

**Status: LANDED (2026-11-13).** Read off the D–S shelf after SET-AF54 with the
recipe in [../deligneSerre/TOPIC-scoping-a-ds-set.md](../deligneSerre/TOPIC-scoping-a-ds-set.md);
the D–S column's fifty-fifth set, and the first of the recent run cut out of the
**`AutomorphicForm` ready block** rather than the `AlgebraicCurve` residue chain.

**13 rows / 1,197 silo / 923 net (`port_plan`)** in five new modules and three appends (eight
files): the
archimedean cut's closure properties (the general-type Casimir dictionary at both kinds of place,
the test-factor algebra, the projector, and the cut's interaction with the level and the
character), and the cuspidal carrier's window monotonicity, modulus and orthogonality.

| # | row (`AutomorphicForm.` dropped) | silo | lev | home |
|---|---|---:|---:|---|
| **A1** | `isArchSmoothAt_rightConv_and_exists_archCasimirAt_rightConv_eq_of_isArchBiFinite` | 72 | 1/1 | append `LeftCasimirTestFn` |
| **A2** | `isArchSmoothAtComplex_rightConv_and_exists_archCasimirAtComplex_rightConv_eq_of_isArchBiFinite` | 140 | 1/1 | append `LeftCasimirTestFn` |
| **A3** | `isFactorizableTestFn_comp_inv_mul` | 133 | 2/3 | append `TestFnInvariance` |
| **A4** | `isFinTestFactor_integral_mul_of_isFinTestFactor_of_hasCompactSupport` | 48 | 1/1 | new `TestFactorIntegral` |
| **A5** | `isArchTestFactor_integral_mul_of_isArchTestFactor_of_hasCompactSupport` *(leaf)* | 177 | 1/1 | new `TestFactorIntegral` |
| **A6** | `exists_linearMap_archCutProjector` | 29 | 2/3 | append `ArchApproximation` |
| **A7** | `CuspidalConstituent.rightConv_mem_levelInvariantSubmodule_inf_archCutSubmodule_of_isArchBiFinite` | 52 | 3/5 | append `LeftCasimirTestFn` |
| **A8** | `CuspidalConstituent.exists_inf_archCutSubmodule_ofChar_ne_bot_of_ne_bot` | 56 | 1/1 | new `Cusp/ConstituentCharCut` |
| **B1** | `isotypicCuspSubmodule_le_isotypicCuspSubmodule_of_le_of_ne_bot` | 68 | 1/1 | new `Cusp/CarrierWindowMonotonicity` |
| **B2** | `CuspidalConstituent.cuspKFiniteSubmodule_le_cuspKFiniteSubmodule_of_le_of_exists_ne_zero` | 66 | 1/2 | new `Cusp/CarrierWindowMonotonicity` |
| **B3** | `CuspidalSpectrum.exists_hasModulus_of_isCuspConstituent` | 37 | 3/8 | new `Cusp/ConstituentModulus` |
| **B4** | `CuspidalSpectrum.isFinTestFactor_conj_inv_mul_ideleNorm_det_rpow` | 59 | 1/1 | new `Cusp/ConstituentModulus` |
| **B5** | `CuspidalSpectrum.apply_eq_zero_of_mem_orthogonal_cuspLevelSubcarrier_of_isLift_rightConv_of_rightInvariant` | 260 | 1/1 | new `Cusp/SpectrumOrthogonality` |

**Premise audit closed**: all twenty premise nodes are ported at the right statements (the check is
in §3 by hand, not by last name). **Definition gate closed**: the nine `Definitions/Def_AutomorphicForm_*`
(and `Def_AdelicDock_LocalEmbedding`) modules the thirteen wrappers import are all ported (§3).
**No promotion, no migration, one legacy ruling (§3.3).** Two orders, disjoint files, one wave.

**The landing**: both orders are in, **695 written proof lines** over 3,378 scaffold lines, **0
`sorry`**, 0 imports and 0 `set_option`s added, all thirteen headlines axiom-clean, both consumer
zones at 0 errors, `dedup` clean on all eight files and `move_dead` clean apart from one pre-existing
dead `private` theorem. The record is §6; the three deviations the gates forced are FR-0189, FR-0192
and FR-0193, and the import-direction failure §3.4 is FR-0191.

## 0. The read

```bash
cd tools/deps
python3 frontier.py --ds --ready --include-leaves --rank-by silo --top 0 --json > build/shelf11.json
python3 frontier.py --selfcheck
```

The plain read (no `--unport`) is quoted; the correction is MD-005's ten and MD-006's one, applied
below as the frontier column only — `needed` is untouched by both, so the shelf is the same read
on either marker set.

| figure | value |
|---|---:|
| `needed [F terminal]` | **691 / 291,010** |
| `needed [literal]` | 712 / 297,932 |
| frontier F | 1,726 / 836,542 (**1,715 / 832,015** with MD-005's ten + MD-006's one removed) |
| ready rows, all namespaces | **45 / 8,516** |
| leaves, all namespaces | **185 / 46,068** |
| `AutomorphicForm` ready rows | **23 / 3,650** |
| `AutomorphicForm` leaves | 39 / 7,531 |
| `AutomorphicForm` demand | 260 / 113,790 |
| withheld by the FR-0044 guard | 4 / 831 |
| cone / avoided | 2,103 / 982,173 · 140 / 74,620 |

`needed` is exactly SET-AF54's post-landing figure (691 / 291,010), which is the read this set
opens on: nothing has landed since, so the delta of this set is measured against it.

**`--selfcheck` still FAILS**, on MD-005's ten `ModularCurve` phi rows (the source tier claims ten
`PhiGen`/`ModularPolynomialData` nodes no declaration carries) plus the MD-006 shadow
(`ValuationSubring.isIntegral_of_forall_mem`, a name-tier map onto two `RegularProlongation`
declarations). Both are recorded and **open** in
[../../spec/METADATA-ISSUES.md](../../spec/METADATA-ISSUES.md), both are the phi workstream's, and
neither touches this set: no row cut here cites any of the eleven. The corrected frontier figure in
the table is the plain read minus their 4,527 lines — 1,715 / 832,015, which is exactly the figure
SET-AF54's re-read left. A future scoping read should still subtract them (or re-run the check)
before quoting the frontier.

**The shelf, quoted whole** — 45 ready rows and 185 leaves, every row marked cut or deferred, in
§1. **`AutomorphicForm` is where the ready shelf's weight is**: 23 of 45 rows and 3,650 of 8,516
silo, the largest single namespace block, ahead of `LanglandsTunnell`'s 5 / 1,223.

## 1. The shelf, quoted whole

### ready shelf (45 rows / 8,516 silo)

| row | silo | prem | lev | cut |
|---|---:|---:|---:|---|
| `AlgebraicCurve.exists_placeMap_mapDomain_eq_ord_of_good_constantReduction` | 59 | 2 | 2/5 | deferred |
| `AutomorphicForm.CuspidalConstituent.cuspKFiniteSubmodule_le_cuspKFiniteSubmodule_of_le_of_exists_ne_zero` | 66 | 2 | 1/2 | **cut** |
| `AutomorphicForm.CuspidalConstituent.exists_inf_archCutSubmodule_ofChar_ne_bot_of_ne_bot` | 56 | 1 | 1/1 | **cut** |
| `AutomorphicForm.CuspidalConstituent.rightConv_mem_levelInvariantSubmodule_inf_archCutSubmodule_of_isArchBiFinite` | 52 | 1 | 3/5 | **cut** |
| `AutomorphicForm.CuspidalSpectrum.apply_eq_zero_of_mem_orthogonal_cuspLevelSubcarrier_of_isLift_rightConv_of_rightInvariant` | 260 | 6 | 1/1 | **cut** |
| `AutomorphicForm.CuspidalSpectrum.exists_hasModulus_of_isCuspConstituent` | 37 | 1 | 3/8 | **cut** |
| `AutomorphicForm.CuspidalSpectrum.isFinTestFactor_conj_inv_mul_ideleNorm_det_rpow` | 59 | 1 | 1/1 | **cut** |
| `AutomorphicForm.IsKfSmooth.exists_isCompact_isOpen_eq_inf_forall_apply_mul_eq` | 108 | 1 | 1/1 | deferred |
| `AutomorphicForm.SiegelCovering.centreCutSiegelSet_coversModCentre_rat` | 30 | 1 | 1/6 | deferred |
| `AutomorphicForm.SmoothCusp.not_isHeckeCosetEigenfunctionAt_levelOne_bot_inf_finiteAdelicGL2Subgroup` | 229 | 1 | 1/1 | deferred |
| `AutomorphicForm.SmoothCuspRealizationAt.centralChar_eq_of_agreesAwayFromFinite` | 113 | 2 | 1/16 | deferred |
| `AutomorphicForm.apply_mul_eq_of_isKfSmooth_of_forall_placeEmbed_of_mem_maximalCompactAway` | 209 | 1 | 1/3 | deferred |
| `AutomorphicForm.exists_finset_forall_exists_mem_valued_eq_max_and_contentHomFin_mul_sq_eq` | 333 | 1 | 1/1 | deferred |
| `AutomorphicForm.exists_isFundamentalDomain_globalPoints_range` | 165 | 3 | 1/11 | deferred |
| `AutomorphicForm.exists_linearMap_archCutProjector` | 29 | 2 | 2/3 | **cut** |
| `AutomorphicForm.exists_pos_forall_rightConv_integral_prod_mul_indicator_eq_mul_integral_of_forall_integral_mul_apply_mul_eq` | 437 | 3 | 4/5 | deferred |
| `AutomorphicForm.integral_mul_eq_integral_mul_weight_mul_tsum_sub_average_of_isCuspidalFn` | 635 | 1 | 1/1 | deferred |
| `AutomorphicForm.isArchSmoothAtComplex_rightConv_and_exists_archCasimirAtComplex_rightConv_eq_of_isArchBiFinite` | 140 | 3 | 1/1 | **cut** |
| `AutomorphicForm.isArchSmoothAt_rightConv_and_exists_archCasimirAt_rightConv_eq_of_isArchBiFinite` | 72 | 3 | 1/1 | **cut** |
| `AutomorphicForm.isFactorizableTestFn_comp_inv_mul` | 133 | 1 | 2/3 | **cut** |
| `AutomorphicForm.isFinTestFactor_integral_mul_of_isFinTestFactor_of_hasCompactSupport` | 48 | 1 | 1/1 | **cut** |
| `AutomorphicForm.isotypicCuspSubmodule_le_isotypicCuspSubmodule_of_le_of_ne_bot` | 68 | 2 | 1/1 | **cut** |
| `AutomorphicForm.lintegral_rationalCentreUnipotentHaar_comp_heckeGen_mul_centralScalar_conj` | 179 | 1 | 1/1 | deferred |
| `AutomorphicForm.peterssonIntegral_self_ne_zero_of_isFundamentalDomain_of_continuous` | 192 | 2 | 5/8 | deferred |
| `CohCarrier.exists_surjective_doubleCoset_gammaH_zpowers_of_addOrderOf_eq` | 252 | 1 | 1/1 | deferred |
| `CuspForm.IsEigenformWith.fg_adjoin_qCoeff` | 291 | 1 | 1/8 | deferred |
| `CuspForm.coe_diamondLinH_and_coe_heckeTLinH_and_coe_heckeULinH_of_hasNebentypus` | 51 | 3 | 1/3 | deferred |
| `EisensteinGeneral.Piece.exists_forall_nonempty_factorizationDatum` | 890 | 2 | 3/5 | deferred |
| `GaloisRep.exists_isSemisimpleRepresentation_charpoly_map_eq_of_trace_det_frobenius_mem_range` | 495 | 3 | 1/1 | deferred |
| `LanglandsTunnell.TateLocal.integral_comp_inv_eq_integral_modulus_inv_sq_mul_adicCompletion` | 305 | 1 | 1/7 | deferred |
| `LanglandsTunnell.TateLocal.measureReal_setOf_valued_le_exp` | 100 | 1 | 1/13 | deferred |
| `LanglandsTunnell.dirichletIdeleChar_mul_modulus_det_gen` | 128 | 1 | 2/2 | deferred |
| `LanglandsTunnell.exists_rpow_bound_near_zero_of_whittaker_ode_of_discrete_tower_of_moderateGrowth` | 329 | 1 | 2/2 | deferred |
| `LanglandsTunnell.linearDependent_string_of_gl2Complex_whittaker_system_of_moderateGrowth` | 361 | 1 | 1/1 | deferred |
| `MeasureTheory.exists_integral_conj_apply_smul_ne_zero_of_forall_norm_apply_eq_of_continuous` | 200 | 1 | 1/1 | deferred |
| `ModularCurve.IsDiamondPullbackModL.apply_eq_one_iff_gamma0Units_mem` | 485 | 1 | 1/5 | deferred |
| `ModularCurve.exists_sum_smul_eq_of_isIntegralQExp_gamma1` | 36 | 2 | 1/3 | deferred |
| `ModularCurve.rep_tateModule_jOne_comm` | 24 | 1 | 1/6 | deferred |
| `ModularForm.exists_gamma0_qExpansion_div_eq_E4_cube_div_discriminant` | 66 | 1 | 1/3 | deferred |
| `NumberField.AdelicBox.integral_cond_adelicBox_comp_mul_algebraMap` | 122 | 2 | 1/11 | deferred |
| `NumberField.AdelicBox.setLIntegral_adelicBox_comp_mul_add_eq_of_periodic` | 129 | 1 | 1/2 | deferred |
| `NumberField.AdelicHaar.exists_integral_glArch_mul_glFin_eq_mul_integral_mul_integral` | 201 | 2 | 1/6 | deferred |
| `NumberField.AdelicHaar.isMulRightInvariant_of_isHaarMeasure_generalLinearGroup_infiniteAdeleRing` | 84 | 3 | 4/5 | deferred |
| `NumberField.TateGlobal.exists_isCompact_forall_eq_principal_mul_balanced_mul` | 120 | 2 | 1/2 | deferred |
| `ValuationSubring.exists_aeval_div_eq_aeval_div_add_inv_pow_mul_add_aeval_inv` | 138 | 1 | 1/1 | deferred |

### leaves (185 rows / 46,068 silo)

| row | silo | lev | cut |
|---|---:|---:|---|
| `AutomorphicForm.CuspidalConstituent.continuous_and_isSmoothCuspAutomorphicFnAt_rightTranslate_of_mem_cuspKFiniteSubmodule` | 154 | 8/19 | deferred |
| `AutomorphicForm.CuspidalConstituent.eq_of_isCuspConstituent_of_exists_mem_ne_zero` | 33 | 1/2 | deferred |
| `AutomorphicForm.CuspidalConstituent.exists_forall_le_archTypeSubmoduleAt_of_isSimple_of_le_iSup` | 646 | 2/4 | deferred |
| `AutomorphicForm.CuspidalConstituent.exists_isFactorizableTestFn_isArchBiFinite_conj` | 245 | 1/1 | deferred |
| `AutomorphicForm.CuspidalConstituent.forall_apply_mul_archRealGLAt_eq_of_isCuspConstituent_of_exists` | 148 | 2/2 | deferred |
| `AutomorphicForm.CuspidalConstituent.isCuspConstituent_productionPinsOf_mono` | 62 | 1/2 | deferred |
| `AutomorphicForm.CuspidalSpectrum.exists_isArchBiFinite_flat` | 304 | 1/1 | deferred |
| `AutomorphicForm.CuspidalSpectrum.isClosedCuspSubrep_topologicalClosure_map_toCuspSubcarrier_of_isCuspSubrep` | 75 | 2/4 | deferred |
| `AutomorphicForm.IsFactorizableTestFn.comp_mul_unipotentGL2_mul_mem_pureTensorSet` | 189 | 1/4 | deferred |
| `AutomorphicForm.IsIsotypicCuspFormAt.exists_smoothCuspRealizationAt_toFun_eq_of_ne_bot` | 30 | 2/10 | deferred |
| `AutomorphicForm.IsKfSmooth.exists_ideal_forall_apply_mul_conj_unipotentGL2_eq` | 328 | 3/4 | deferred |
| `AutomorphicForm.IsUnitFactorizableAbove.finComponent_glFin_mem_localIntegralSet_of_apply_ne_zero` | 78 | 1/1 | deferred |
| `AutomorphicForm.RankinSelberg.section_diagOne_mul_eq_ideleNorm_cpow_mul_of_isInducedSection_etaFst_etaSnd` | 66 | 1/1 | deferred |
| `AutomorphicForm.WindowedSiegel.exists_forall_apply_one_zero_eq_zero_of_inv_mul_globalPoints_mul_mul_centralScalar_mem` | 386 | 3/4 | deferred |
| `AutomorphicForm.WindowedSiegel.isCompact_centreCutSiegelSet_inter_heightCap` | 282 | 5/10 | deferred |
| `AutomorphicForm.constantTerm_add` | 13 | 1/2 | deferred |
| `AutomorphicForm.constantTerm_adelicBox_unipotentGL2_mul` | 144 | 1/14 | deferred |
| `AutomorphicForm.constantTerm_smul` | 11 | 1/1 | deferred |
| `AutomorphicForm.coversModCentre_of_le_of_lt_of_coversModCentre` | 150 | 4/8 | deferred |
| `AutomorphicForm.eq_zero_of_isLsXiFunction_of_coversModCentre_of_forall_mem_eq_zero` | 23 | 1/1 | deferred |
| `AutomorphicForm.existsUnique_bruhatRepresentative_mul_mem_borelSubgroup` | 65 | 2/3 | deferred |
| `AutomorphicForm.exists_borel_mul_gl2Weyl_mul_unipotentGL2_eq_of_integral` | 156 | 1/1 | deferred |
| `AutomorphicForm.exists_continuous_monoidHom_matrix_apply_ne_one_of_ne_one` | 55 | 1/1 | deferred |
| `AutomorphicForm.exists_depth_forall_apply_mul_lowerUnipotentGL2_eq_of_sum_translate` | 445 | 1/2 | deferred |
| `AutomorphicForm.exists_eq_mul_mem_levelOne_inf_finiteAdelicGL2Subgroup_commute_placeEmbed_of_forall_mem_localIntegralSet` | 192 | 1/1 | deferred |
| `AutomorphicForm.exists_forall_adelicGLHaar_image2_unipotentGL2_mul_mul_le_of_isCompact` | 317 | 1/1 | deferred |
| `AutomorphicForm.exists_iUnion_centreCutSiegelSet_mem_nhds` | 25 | 1/1 | deferred |
| `AutomorphicForm.exists_isArchBiFinite_rightConv_comp_inv` | 376 | 1/1 | deferred |
| `AutomorphicForm.exists_norm_a_le_absNorm_rpow_and_norm_b_le_of_smoothCuspRealizationAt_of_peterssonPairing` | 384 | 1/2 | deferred |
| `AutomorphicForm.exists_smoothCuspRealizationAt_productionPinsOf_toFun_eq_of_isBoundedOnSiegelWindows_of_coversModCentre` | 69 | 1/1 | deferred |
| `AutomorphicForm.exists_sum_prod_mul_of_rightTranslatesSpanFinite` | 576 | 2/2 | deferred |
| `AutomorphicForm.exists_upperTriangular_globalPoints_mul_mul_scalar_mul_finIdeleDiag_inv_mem_finiteIntegralGL2` | 587 | 1/1 | deferred |
| `AutomorphicForm.integral_prod_conj_eq_and_eq_conj_mul_of_conj_invariant_of_flat` | 196 | 4/5 | deferred |
| `AutomorphicForm.isArchTestFactor_integral_mul_of_isArchTestFactor_of_hasCompactSupport` | 177 | 1/1 | **cut** |
| `AutomorphicForm.isArchTestFactor_of_contDiff_of_hasCompactSupport_of_tsupport_subset_isUnit_det` | 165 | 1/5 | deferred |
| `AutomorphicForm.isLocallyConstant_iwasawaShellIndex_and_measurable` | 62 | 2/2 | deferred |
| `AutomorphicForm.iwasawaShellIndex_mul_of_mem_rationalCentreUnipotent` | 46 | 2/2 | deferred |
| `AutomorphicForm.mem_rationalCentreUnipotent_iff_heckeGen_mul_centralScalar_conj_mem` | 119 | 1/1 | deferred |
| `AutomorphicForm.typeSubmodule_inf_typeSubmodule_eq_bot` | 152 | 1/2 | deferred |
| `CohCarrier.H1_moduleFinite` | 74 | 1/70 | deferred |
| `CohCarrier.charInvolution_comp_opFamily` | 247 | 1/3 | deferred |
| `CohCarrier.exists_eq_gammaH_of_gamma1_le_of_le_gamma0` | 49 | 1/11 | deferred |
| `CohCarrier.exists_gamma0_lift_dvd` | 25 | 1/10 | deferred |
| `CohCarrier.index_gammaH_eq_index_gamma0_mul_index` | 32 | 1/22 | deferred |
| `ContinuousLinearMap.comp_eq_of_forall_apply_eq_integral_smul_apply_of_convolution` | 180 | 1/1 | deferred |
| `ContinuousLinearMap.eq_zero_of_forall_exists_mem_sub_real_smul_eq` | 385 | 1/2 | deferred |
| `ContinuousLinearMap.exists_forall_apply_eq_integral_smul_apply_of_forall_norm_le_of_continuous` | 108 | 2/2 | deferred |
| `ContinuousLinearMap.le_ker_or_finiteDimensional_of_forall_inf_highPart_orthogonal` | 276 | 1/1 | deferred |
| `ContinuousLinearMap.map_eigenspace_orthogonal_le_of_commute` | 40 | 1/2 | deferred |
| `ContinuousLinearMap.map_highPart_orthogonal_le_of_commute` | 275 | 1/1 | deferred |
| `ContinuousLinearMap.orthogonal_iSup_eigenspace_ne_zero_eq_ker` | 275 | 2/4 | deferred |
| `CuspForm.HasNebentypus.qCoeff_eq_zero_of_coprime_of_apply_eq_sum_slash` | 582 | 1/1 | deferred |
| `CuspForm.HasNebentypus.sum_filter_eq_of_sum_eq` | 185 | 3/3 | deferred |
| `CuspForm.exists_apply_eq_conj_apply_J_smul_of_forall_jConjSL_mem` | 69 | 2/3 | deferred |
| `CuspForm.exists_finset_dirichlet_sum_eq_and_independent_of_gammaH` | 340 | 1/1 | deferred |
| `CuspForm.exists_gamma1_apply_eq_conj_and_qCoeff_eq_conj` | 126 | 3/8 | deferred |
| `CuspForm.exists_gamma1_apply_eq_zpow_mul_apply_of_mul_eq_neg_one` | 168 | 1/1 | deferred |
| `CuspForm.exists_gamma1_coe_eq_of_gammaH` | 51 | 1/3 | deferred |
| `CuspForm.exists_gamma1_qCoeff_eq_ite_coprime` | 339 | 2/4 | deferred |
| `CuspForm.exists_gammaH_coe_eq_of_hasNebentypus` | 68 | 1/2 | deferred |
| `CuspForm.peterssonOn_add_smul_conj` | 142 | 2/2 | deferred |
| `CuspForm.peterssonOn_self_re_nonneg_im_eq_zero_eq_zero_iff` | 249 | 2/2 | deferred |
| `EisensteinGeneral.Arch.exists_norm_archIntegral_le` | 233 | 2/2 | deferred |
| `EisensteinGeneral.Glue.whittakerCoefficientIntegrable_bruhatSeries_and_ae_summable_of_integrable` | 165 | 1/1 | deferred |
| `EisensteinGeneral.Piece.continuous_and_continuous_of_isInducedSection_of_continuous_of_ne_zero` | 189 | 2/2 | deferred |
| `EisensteinGeneral.Piece.exists_summable_majorant_of_lattice_vanishing` | 666 | 1/1 | deferred |
| `EisensteinGeneral.Piece.integral_smul_add_mul_addChar_neg_mul_eq` | 125 | 4/6 | deferred |
| `HaarQuotient.lintegral_density_mul_eq_one` | 170 | 2/39 | deferred |
| `HaarQuotient.lintegral_eq_lintegral_lintegral_mul_out` | 616 | 2/48 | deferred |
| `IsDedekindDomain.FiniteAdeleRing.exists_forall_sub_algebraMap_mem_adicCompletionIntegers` | 342 | 1/5 | deferred |
| `IsDedekindDomain.FiniteAdeleRing.exists_ne_zero_forall_mul_apply_mem_adicCompletionIntegers_of_isCompact` | 52 | 3/14 | deferred |
| `IsDedekindDomain.FiniteAdeleRing.exists_sub_algebraMap_mem_adicCompletionIntegers` | 228 | 1/5 | deferred |
| `IsDedekindDomain.HeightOneSpectrum.exists_prime_and_asIdeal_eq_span_ringOfIntegers_rat` | 20 | 2/9 | deferred |
| `IsDedekindDomain.HeightOneSpectrum.isAdicComplete_adicCompletionIntegers` | 111 | 1/12 | deferred |
| `LanglandsTunnell.RankinSelberg.exists_nonneg_exp_tsum_mul_pow_eq_inv_eval_rsEulerPoly_self_of_norm_eq_one` | 231 | 1/1 | deferred |
| `LanglandsTunnell.TateLocal.complexZeta_eq_localZeta` | 166 | 1/7 | deferred |
| `LanglandsTunnell.TateLocal.forall_eq_one_and_exists_ne_one_of_addCharLevel` | 37 | 3/100 | deferred |
| `LanglandsTunnell.TateLocal.psiLocal_eq_one_of_mem_integers` | 45 | 4/116 | deferred |
| `LanglandsTunnell.TateLocal.realZeta_eq_localZeta` | 166 | 1/13 | deferred |
| `LanglandsTunnell.TateLocal.tateFourier_indicator_setOf_valued_sub_le` | 149 | 1/21 | deferred |
| `LanglandsTunnell.eq_zero_of_deriv_eq_div_add_mul_of_re_pos_of_isBigO_pow` | 104 | 1/1 | deferred |
| `LanglandsTunnell.exists_heckeCosetSystem_productionPinsCompact_of_not_dvd` | 446 | 1/2 | deferred |
| `LanglandsTunnell.isBoundedOnSiegelWindows_weightOneLift` | 501 | 2/2 | deferred |
| `LocalNewvector.AdelicSpan.exists_hasNewvectorConductor_le_factorization` | 58 | 1/2 | deferred |
| `LocalNewvector.AdelicSpan.exists_mem_span_fixed_padicK1_of_fixedSubmodule_padicK1_ne_bot_of_apply_mul_finEmbed_eq` | 589 | 1/1 | deferred |
| `M4aTorus.completedRayL_fe` | 12126 | 1/2 | deferred |
| `MeasureTheory.Lp.finiteDimensional_and_finrank_le_of_forall_ae_norm_le_mul_norm` | 148 | 1/1 | deferred |
| `MeasureTheory.Measure.exists_eq_smul_map_smul_of_forall_map_smul_eq_of_isCompact_stabilizer` | 222 | 1/2 | deferred |
| `MeasureTheory.differentiableOn_integral_of_forall_differentiableOn_of_locally_norm_le` | 99 | 3/6 | deferred |
| `MeasureTheory.exists_continuous_convolution_self_eq_forall_integral_smul_isotypic` | 626 | 1/1 | deferred |
| `MeasureTheory.exists_integral_eq_inv_card_mul_sum_of_isOpen_subgroup` | 90 | 3/4 | deferred |
| `MeasureTheory.integral_abs_det_div_sq_mul_comp_moebius_real` | 95 | 1/1 | deferred |
| `MeasureTheory.integral_normSq_det_div_mul_comp_moebius_complex` | 104 | 1/1 | deferred |
| `MeasureTheory.lintegral_enorm_sub_integral_mul_sq_le_lintegral_mul_lintegral_enorm_sub_sq` | 98 | 2/3 | deferred |
| `MeasureTheory.lintegral_mul_comp_eq_tsum_zpow_mul_setLIntegral_of_measure_image_eq_mul` | 84 | 1/1 | deferred |
| `MeasureTheory.measure_biUnion_finset_image_mul_right_lt_top` | 18 | 1/1 | deferred |
| `MeasureTheory.tendsto_lintegral_nhds_zero_of_le_of_limsup_lintegral_le` | 63 | 1/1 | deferred |
| `ModularForm.exists_coe_eq_of_levelOne` | 22 | 1/4 | deferred |
| `ModularForm.exists_cuspForm_mul_eq_of_forall_analyticOrderAt_le` | 195 | 1/1 | deferred |
| `ModularForm.exists_levelOne_coe_eq_sum_slash` | 156 | 1/1 | deferred |
| `ModularForm.exists_levelOne_qExpansion_eq_map_int_constantCoeff_one` | 62 | 1/1 | deferred |
| `ModularForm.exists_qExpansion_eq_aeval_mul_pow_levelOne` | 94 | 5/8 | deferred |
| `ModularForm.heckeU_add_smul_slash_heckeDiagMatrix_slash_of_mem_Gamma0` | 406 | 1/3 | deferred |
| `NumberField.AdeleRing.compactSpace_quotient_principalSubgroup` | 32 | 1/3 | deferred |
| `NumberField.AdeleRing.exists_isOpen_inter_principalIdeles_eq_singleton` | 118 | 1/4 | deferred |
| `NumberField.AdelicBox.absNorm_mul_measure_image_integralFiniteAdeles` | 229 | 1/2 | deferred |
| `NumberField.AdelicBox.algebraMap_mem_image_integralFiniteAdeles_iff` | 41 | 2/3 | deferred |
| `NumberField.AdelicBox.exists_denom_of_hasCompactSupport` | 70 | 1/1 | deferred |
| `NumberField.AdelicBox.exists_eq_sum_indicator_image_integralFiniteAdeles` | 483 | 3/4 | deferred |
| `NumberField.AdelicBox.exists_ne_zero_forall_addChar_mul_eq_one` | 201 | 1/3 | deferred |
| `NumberField.AdelicBox.integralFiniteAdeles_subset_closure_range_algebraMap_ringOfIntegers` | 109 | 2/2 | deferred |
| `NumberField.AdelicBox.isLocallyConstant_and_hasCompactSupport_indicator_image_integralFiniteAdeles` | 44 | 1/4 | deferred |
| `NumberField.AdelicFourier.comp_add_right_mem_pureTensorSet` | 31 | 1/1 | deferred |
| `NumberField.AdelicFourier.comp_mul_algebraMap_mem_pureTensorSet` | 84 | 1/1 | deferred |
| `NumberField.AdelicFourier.comp_mul_mem_schwartzBruhat` | 101 | 1/7 | deferred |
| `NumberField.AdelicFourier.exists_smul_eq_of_isAddHaarMeasure_adeleRing` | 179 | 2/4 | deferred |
| `NumberField.AdelicFourier.fourierIntegral_comp_mul_left` | 215 | 3/10 | deferred |
| `NumberField.AdelicFourier.fourierIntegral_indicator_principalCoset_finiteAdeleRing` | 140 | 1/2 | deferred |
| `NumberField.AdelicFourier.fourierIntegral_indicator_principalCoset_finiteAdeleRing_apply` | 181 | 1/1 | deferred |
| `NumberField.AdelicFourier.fourierIntegral_pureTensor_eq` | 359 | 4/8 | deferred |
| `NumberField.AdelicFourier.integrable_of_mem_schwartzBruhat` | 235 | 5/20 | deferred |
| `NumberField.AdelicFourier.norm_apply_eq_one_of_isGlobalAddChar` | 93 | 25/74 | deferred |
| `NumberField.AdelicFourier.setIntegral_addChar_mul_eq_ite_of_isCompact` | 93 | 1/1 | deferred |
| `NumberField.AdelicFourier.summable_translate_of_mem_schwartzBruhat` | 236 | 2/3 | deferred |
| `NumberField.AdelicHeight.adelicHeight_globalPoints_mul_of_apply_one_zero_eq_zero` | 161 | 1/22 | deferred |
| `NumberField.AdelicHeight.exists_forall_mul_adelicHeight_le_adelicHeight_mul_of_isCompact` | 514 | 1/33 | deferred |
| `NumberField.AdelicLevel.diagOne_eq_diagOne_mul_archRealLiftAt_mul_centralScalar` | 172 | 3/3 | deferred |
| `NumberField.AdelicLevel.diagOne_mul_archRealGLAt_unipotent_eq_and_stdAddChar_single_half` | 207 | 4/4 | deferred |
| `NumberField.AdelicTrace.traceFinHom_apply_eq_sum_trace` | 266 | 1/1 | deferred |
| `NumberField.Idele.exists_lintegral_prod_norm_sPartMeasure_empty_eq_mul_prod_lintegral` | 370 | 1/6 | deferred |
| `NumberField.Idele.lintegral_mul_prod_ord_sPartMeasure_eq_lintegral_sPartMeasure_empty_mul_prod_tsum` | 381 | 1/4 | deferred |
| `NumberField.Idele.sPartMeasure_pos_of_isOpen_of_partAt_eq` | 73 | 1/1 | deferred |
| `NumberField.InfinitePlace.sign_norm_eq_prod_sign_embedding_of_isReal` | 94 | 1/2 | deferred |
| `NumberField.StandardAddChar.isGlobalAddChar_stdAddChar` | 10 | 17/59 | deferred |
| `NumberField.StandardAddChar.psiLocal_rat_eq_psiV` | 69 | 1/38 | deferred |
| `NumberField.StandardAddChar.stdAddChar_single_infinitePlace_of_isComplex` | 61 | 2/2 | deferred |
| `NumberField.StandardAddChar.stdAddChar_single_infinitePlace_of_isReal` | 62 | 3/6 | deferred |
| `NumberField.Units.exists_forall_abs_sub_mult_mul_log_le` | 98 | 2/2 | deferred |
| `NumberField.dedekindZeta_ne_zero_of_one_lt_re` | 357 | 6/6 | deferred |
| `NumberField.exists_continuousOn_exp_eq_rayClassLSeries` | 684 | 1/2 | deferred |
| `NumberField.hasProd_inv_one_sub_absNorm_cpow_neg_dedekindZeta` | 338 | 6/26 | deferred |
| `NumberField.mixedEmbedding.exists_forall_norm_embedding_sub_le` | 71 | 1/1 | deferred |
| `NumberField.mixedEmbedding.exists_forall_tsum_fractionalIdeal_weight_le_rpow_neg` | 237 | 2/11 | deferred |
| `NumberField.mixedEmbedding.summable_norm_schwartzMap_ringOfIntegers_translate` | 67 | 1/1 | deferred |
| `NumberField.mixedEmbedding.trace_mixedEmbedding` | 17 | 6/8 | deferred |
| `NumberField.multipliable_differentiableOn_tprod_ne_zero_eulerProduct_of_norm_le_one` | 600 | 11/40 | deferred |
| `NumberField.ncard_primesOver_eq_finrank_of_isCyclotomicExtension_of_absNorm_modEq_one` | 233 | 1/2 | deferred |
| `NumberField.summable_heightOneSpectrum_absNorm_rpow_neg_of_one_lt` | 69 | 7/41 | deferred |
| `TateCurve.exists_zpow_mul_mem_annulus` | 69 | 1/6 | deferred |
| `TateCurve.hasSum_xfun` | 17 | 3/3 | deferred |
| `TateCurve.hasSum_yfun` | 17 | 2/2 | deferred |
| `TateCurve.nodal_xfun_yfun` | 22 | 1/1 | deferred |
| `TateCurve.pointX_q_mul` | 19 | 2/9 | deferred |
| `TateCurve.pointY_q_mul` | 19 | 2/7 | deferred |
| `TateCurve.point_mul_eq_add_of_norm_eq_one` | 247 | 1/1 | deferred |
| `TateCurve.point_mul_eq_add_of_norm_le_one` | 471 | 1/1 | deferred |
| `TateCurve.tsum_succ_prod_eq_tsum_divisors` | 157 | 2/2 | deferred |
| `UnramifiedWhittaker.apply_mul_placeEmbed_diagZ_eq_mul_torusFactor` | 380 | 3/7 | deferred |
| `UnramifiedWhittaker.summable_heckeRecursionSeq_mul_heckeRecursionSeq_mul_pow` | 205 | 1/2 | deferred |
| `UnramifiedWhittaker.tsum_heckeRecursionSeq_mul_heckeRecursionSeq_mul_pow_mul_rsEulerPoly_eval` | 207 | 1/2 | deferred |
| `ValuationSubring.IsFrobeniusAt.apply_eq_pow_of_pow_eq_one` | 83 | 2/21 | deferred |
| `ValuationSubring.charP_residueField_of_liesOverPrime` | 37 | 1/27 | deferred |
| `ValuationSubring.exists_map_subtype_eq_C_inv_mul_and_map_residue_ne_zero` | 57 | 1/3 | deferred |
| `ValuationSubring.exists_smul_mem_of_transcendental_residue` | 262 | 1/1 | deferred |
| `ValuationSubring.natDegree_map_eq_card_roots_of_splits` | 174 | 1/1 | deferred |
| `ValuationSubring.ringKrullDim_le_ringKrullDim_comap_add_trdeg` | 269 | 1/3 | deferred |
| `ValuationSubring.tensorProduct_exists_primitive_factor` | 78 | 1/1 | deferred |
| `WeierstrassCurve.Affine.Point.smul_some_eq_zero_iff` | 28 | 2/51 | deferred |
| `WeierstrassCurve.Affine.Point.some_add_some_eq_neg_some_of_pow_three_eq_one` | 40 | 1/3 | deferred |
| `WeierstrassCurve.Affine.Point.some_zero_add_self_eq_neg_of_a6_model` | 34 | 1/3 | deferred |
| `WeierstrassCurve.Affine.Point.zsmul_some_eq_some_div` | 100 | 2/41 | deferred |
| `WeierstrassCurve.Affine.evalEval_psi_sq` | 29 | 2/44 | deferred |
| `WeierstrassCurve.exists_isUnit_mul_pow_eight_eq_of_charTwo` | 215 | 1/3 | deferred |
| `WeierstrassCurve.exists_map_eq_veluQuotient_and_map_residue_eq_veluQuotient_reduceHom` | 194 | 1/2 | deferred |
| `WeierstrassCurve.exists_valuationSubring_with_transcendental_of_charZero` | 70 | 1/2 | deferred |
| `WeierstrassCurve.exists_variableChange_eq_deuring_of_isUnit_three` | 213 | 1/1 | deferred |
| `WeierstrassCurve.exists_variableChange_eq_legendreCurve_of_isUnit_two` | 274 | 1/2 | deferred |
| `WeierstrassCurve.finite_stabilizer_and_natCard_le_of_j` | 496 | 1/3 | deferred |
| `WeierstrassCurve.finite_stabilizer_variableChange` | 285 | 1/10 | deferred |
| `WeierstrassCurve.natCard_stabilizer_variableChange_eq_two_of_j_ne_zero_of_char_two_or_three` | 256 | 1/7 | deferred |
| `WeierstrassCurve.natCard_stabilizer_variableChange_eq_two_of_j_ne_zero_of_j_ne_1728` | 187 | 1/8 | deferred |
| `WeierstrassCurve.stepCurve_stepSubgroup_two_eq` | 231 | 1/5 | deferred |
| `WeierstrassCurve.transcendental_j_perturb` | 156 | 1/2 | deferred |
| `WeierstrassCurve.variableChange_mk_smul_eq_self_of_pow_three_eq_one` | 26 | 1/6 | deferred |
| `WeierstrassCurve.variableChange_mk_smul_eq_self_of_sq_eq_neg_one` | 26 | 1/6 | deferred |

### 1.1 What the set does not cut, and why

- **The `AutomorphicForm` cuspidal-integral pair** —
  `integral_mul_eq_integral_mul_weight_mul_tsum_sub_average_of_isCuspidalFn` (635, 31 declarations)
  and `exists_pos_forall_rightConv_integral_prod_mul_indicator_eq_mul_integral_of_forall_integral_mul_apply_mul_eq`
  (437, 9) — is the **next** story and the head of the block by silo: the unfolding of a cuspidal
  integral along rational unipotents, and the archimedean × finite double integral. They are one
  subject (both feed `norm_integral_mul_le_mul_setIntegral_norm_of_isCuspidalFn`) and about twice
  this set's hardest row; cutting them beside these thirteen would have made one dispatch of
  ~1,100 silo of measure theory and no room for the rest.
- **`exists_finset_forall_exists_mem_valued_eq_max_and_contentHomFin_mul_sq_eq`** (333),
  **`SmoothCusp.not_isHeckeCosetEigenfunctionAt_…`** (229), **`apply_mul_eq_of_isKfSmooth_of_forall_placeEmbed_…`**
  (209), **`peterssonIntegral_self_ne_zero_…`** (192), **`lintegral_rationalCentreUnipotentHaar_…`**
  (179), **`exists_isFundamentalDomain_globalPoints_range`** (165), **`SmoothCuspRealizationAt.centralChar_eq_of_agreesAwayFromFinite`**
  (113), **`IsKfSmooth.exists_isCompact_isOpen_eq_inf_forall_apply_mul_eq`** (108),
  **`SiegelCovering.centreCutSiegelSet_coversModCentre_rat`** (30): nine ready `AutomorphicForm` rows
  of other subjects (the content/height bound, the level-one obstruction, the `K`/`f`-smooth
  factorization, the Petersson self-pairing, the rational-centre unipotent measure, the global-points
  fundamental domain, the character-matching row, the `Kf`-smooth compact-open factorization, the
  Siegel-centre covering). Each is ready and each is its own story; none shares a premise or a home
  with this set.
- **`EisensteinGeneral.Piece.exists_forall_nonempty_factorizationDatum`** (890, lev 3/5) stays out
  for the reason SET-AF54 recorded: its **definition gate is not ported** (six `Def_` modules, no
  port declarations), so it needs a definition wave before an order.
- **Every other namespace's ready rows and all 185 leaves** are deferred as listed in the tables
  above; the largest are `ModularCurve.IsDiamondPullbackModL.apply_eq_one_iff_gamma0Units_mem` (485),
  `GaloisRep.exists_isSemisimpleRepresentation_charpoly_map_eq_of_trace_det_frobenius_mem_range`
  (495), `LanglandsTunnell`'s four rows (1,223 in total), and the `M4aTorus.completedRayL_fe` leaf
  (12,126 — one node, no consumers, the single largest row on the whole shelf).

## 2. The cut and the price

Two stories, one wave.

**Order A — the archimedean cut's closure** (707 silo): A1/A2 the general-type Casimir dictionary at
a real and at a complex place; A3 the test functions' closure under `(g k)⁻¹`-conjugation; A4/A5 the
same closure under integration against a compactly supported factor, at the finite and at the
archimedean place (the pin's twin pair, one finite row and one leaf); A6 the projector's three
properties without the translate commutation; A7 the constituent's right convolution staying in
`levelInvariantSubmodule ⊓ archCutSubmodule`; A8 a non-trivial constituent meeting the
character-typed cut.

**Order B — the cuspidal carrier and the spectrum** (490 silo): B1/B2 the carrier's monotonicity in
the slab window, for the isotypic and for the `K`-finite carrier; B3 the modulus of a cusp
constituent's central character; B4 the finite test factor's closure under the conjugation twist
`conj (ff b⁻¹) * ‖det b‖^{-σ}`; B5 the orthogonality theorem that kills a level-orthogonal
right-conv-equivariant functional on the spectrum.

| figure | SET-AF55 |
|---|---:|
| raw `S_` lines | 1,197 |
| declaration lines | 974 |
| distinct declaration groups | 39 |
| duplicate copies inside the set | 0 |
| boilerplate dropped | 223 |
| already in the port (vetted, tier 1) | 51 (5 declarations) |
| **net new math lines** | **923** |

The five substitutes are all in order A's preludes and are **imported, not copied**
(`comp_mem_typeSubmodule_of_map`, `comp_mem_iSup_of_forall`, `commute_of_glArch_eq_one_of_glFin_eq_one`
from `Adelic/RightConvIntegral.lean`; `CuspidalSpectrum.eq_of_glArch_eq_of_glFin_eq` from
`Cusp/SpectrumLift.lean`; `continuous_archEntries` from `Adelic/TestFnTop.lean` for A5's primed
copy). A2's `archDerivAtComplex_archDelAt` has a port twin with a different binder skeleton
(`ArchCxGL.*`, function equality rather than pointwise); the pin's pointwise copy is kept in the
module's `CasimirRightConv` prelude, since its statement is not the same one and the arch headline
consumes the pointwise form.

`twin_scan` on all thirteen rows: **`new` for every one** — no statement twin, so the FR-0041
question (a port theorem with weaker hypotheses to rebuild on) does not arise.

## 3. The homes, and the manager's landed layer

### 3.1 Homes

Chosen by subject, then checked against the import direction (every premise's module must sit at or
below the home); confirmed against each pin proof's first lines.

| module | rows | subject | imports added |
|---|---|---|---|
| `AutomorphicForm/Adelic/LeftCasimirTestFn.lean` (append) | A1, A2, A7 | the Casimir dictionary of a right convolution (real and complex) and its `levelInvariantSubmodule ⊓ archCutSubmodule` membership | none |
| `AutomorphicForm/Adelic/TestFnInvariance.lean` (append) | A3 | `IsFactorizableTestFn` stability under the right action | none |
| `AutomorphicForm/Adelic/ArchApproximation.lean` (append) | A6 | the type projector's three properties, read through `exists_rightConv_eq_of_archCutProjector` | none |
| `AutomorphicForm/Adelic/TestFactorIntegral.lean` (new) | A4, A5 | the test factors' closure under integration | the pin's parametric-integral prelude |
| `AutomorphicForm/Adelic/Cusp/ConstituentCharCut.lean` (new) | A8 | a constituent meeting the character-typed cut | `Cusp/CutWeightDecomposition`, `ArchWeightChar` |
| `AutomorphicForm/Adelic/Cusp/CarrierWindowMonotonicity.lean` (new) | B1, B2 | the carrier's `d₁`-monotonicity | `Siegel/DetWindowCover`, `Siegel/CentreCutCover` |
| `AutomorphicForm/Adelic/Cusp/ConstituentModulus.lean` (new) | B3, B4 | the constituent's modulus and the twisted finite test factor | `Cusp/SpectrumCarrierAPI`, `IdeleNormDetGlue`, `AdelicDock/LocalEmbedding` |
| `AutomorphicForm/Adelic/Cusp/SpectrumOrthogonality.lean` (new) | B5 | orthogonality to the level subcarrier on the spectrum | `Cusp/Spectrum{Translation,Pairing}`, `LevelCompactness`, `IdeleNormDetGlue`, `TateGlobalContinuousIdeleNorm` |

Two placements are worth the sentence:

- **A1/A2 are appended to `LeftCasimirTestFn`**, which is the module that *proves* them: it holds the
  general `isFactorizableTestFn_leftCasimir{,Complex}_and_rightConv_mem_of_isArchBiFinite` rows
  (`:552`, `:1022`) and the whole Casimir/test-function engine. Their special cases — the `_ofChar`
  twins — sit one module below in `ArchDerivRightConv(.Complex)`, so A1's proof is the twin's read
  with `tys` for `ArchTypeFamily.ofChar K χ` (the two statements differ by exactly that substitution
  and neither is an instance of the other). **The first cut had these in the twin's modules and was
  wrong**: see §3.4, the import-direction failure this set found and fixed before dispatch.
- **B1/B2 are their premises' first consumers**: `Siegel/DetWindowCover.lean` and
  `Siegel/CentreCutCover.lean` (SET-AF30/AF31) are imported by nothing else in the port, so the
  monotonicity rows are the wiring that brings them onto the tree. `IsotypicCuspSpace.lean`, the
  obvious subject home, is **below** both (it is in their import closure), so the rows cannot live
  there: this is the import-direction rule, not a preference.

### 3.2 The manager's layer, landed and measured before dispatch

| module | lines | decls | `sorry` | `lake build` | `check_port --force` |
|---|---:|---:|---:|---|---|
| `LeftCasimirTestFn.lean` (+A1, A2, A7) | 1,174 → 1,355 → **1,464** | +8 | 8 → **0** | ok | **89 ok / 0 / 0** |
| `TestFnInvariance.lean` (+A3) | 243 → 304 → **384** | +5 | 5 → **0** | ok | **15 ok / 0 / 0** |
| `ArchApproximation.lean` (+A6) | 1,229 → 1,258 → **1,260** | +1 | 1 → **0** | ok | **8 ok / 0 / 0** |
| `TestFactorIntegral.lean` (new) | 151 → **251** | 15 | 11 → **0** | ok | **15 ok / 0 / 0** |
| `Cusp/ConstituentCharCut.lean` (new) | 65 → **83** | 1 | 1 → **0** | ok | **1 ok / 0 / 0** |
| `Cusp/CarrierWindowMonotonicity.lean` (new) | 99 → **175** | 2 | 2 → **0** | ok | **2 ok / 0 / 0** |
| `Cusp/ConstituentModulus.lean` (new) | 80 → **132** | 2 | 2 → **0** | ok | **2 ok / 0 / 0** |
| `Cusp/SpectrumOrthogonality.lean` (new) | 66 → **324** | 1 | 1 → **0** | ok | **1 ok / 0 / 0** |
| | **3,378 → 4,073** | **35** | **31 → 0** | | **180 ok, 0 mismatch, 0 missing** |

Every pin source is wired by the module's own `spec-pin:` header (two lines per row: the `Theorems/`
wrapper and the `P2M/Sol/` copy). Each new module was elaborated *and* `#check`ed by name before
dispatch: `check_port` resolving `0 mismatch / 0 missing` is the statement gate, and it is green on
all ten files (eight after the re-home of §3.4), so the workers only ever fill proof bodies.

Three findings of the scaffold pass, for the record:

1. **`TestFactorIntegral` needs `open scoped Classical`.** The pin's prelude is `open scoped Topology
   Pointwise ContDiff Classical`; without the `Classical`, `NormedAddCommGroup (Xm F)` does not
   synthesize — `mixedSpace F` is a product of Pis over the *subtypes* `{w // IsReal w}` /
   `{w // IsComplex w}`, and the `Fintype` of those needs `Classical.propDecidable`. `inferInstance`
   on the same type in `RightConvRegularity.lean` works only because that file opens `Classical`
   elsewhere. The scaffold carries the pin's `open scoped` line verbatim.
2. **A3's pin prelude restates four rows the port already holds**; they are imported
   (`RightConvIntegral`, `SpectrumLift`) and the four *new* rows are transcribed in the rectified
   label namespace `ArchCutConjugation`. The pin's two-line `namespace Ws1` / `namespace F4R` label is
   a machine token and is rectified (no token survives in a port name).
3. **`ArchDerivRightConv` did not carry `AutomorphicForm.CuspidalSpectrum`**, and
   `ArchDerivRightConvComplex` did not carry the cusp/level vocabulary at all; both now import what
   their appended statement mentions. The imports are the statement's, not the proof's — the
   `check_port` run is what confirmed the statement elaborates.

### 3.3 The one legacy ruling

A8's subject home is `Cusp/CutWeightDecomposition.lean` (its only premise lives there), but that
module is still wired through the frozen `spec/old_check_stmts.py` (`PORT_FILES`). Appending the row
there would drag a full legacy migration — a `spec-pin:` wire over a 906-line pin source, deletion
from `PORT_FILES`, a public-surface diff of ~76 declarations — into this wave, for a 56-line row.
The row is homed one import above it in `Cusp/ConstituentCharCut.lean`, and the migration stays on
the legacy work list. This is a **deferral, not a ruling against the home**: when
`CutWeightDecomposition` is next opened, A8 moves down into it.

### 3.4 The import-direction failure this set hit, and how it was fixed before dispatch

The first cut put A1 and A2 in the modules holding their `_ofChar` twins
(`ArchDerivRightConv`, `ArchDerivRightConvComplex`) and A6 in `ArchCutProjector`. **All three homes
sit *below* their own premises**, so none of the three rows was writable: the worker's first report
found it with a transitive import check, before any statement was touched.

| row | premise it needs | the premise's module | the first home | direction |
|---|---|---|---|---|
| A1 | `isFactorizableTestFn_leftCasimir_and_rightConv_mem_of_isArchBiFinite` | `LeftCasimirTestFn` (`:552`) | `ArchDerivRightConv` | home **below** premise |
| A2 | `isFactorizableTestFn_leftCasimirComplex_and_rightConv_mem_of_isArchBiFinite` | `LeftCasimirTestFn` (`:1022`) | `ArchDerivRightConvComplex` | home **below** premise |
| A6 | `exists_rightConv_eq_of_archCutProjector` (+ its `lamData` helpers) | `ArchApproximation` | `ArchCutProjector` | home **below** premise |

The cure was to re-home, not to refactor: A1 and A2 are appended to `LeftCasimirTestFn` (the module
that holds the general engines, and A7's home too — one module now carries the whole Casimir
dictionary), and A6 to `ArchApproximation` (which holds the `rightConv` reformulation it is stated
with). No statement changed, no `_ofChar` twin moved, and `ArchDerivRightConv`,
`ArchDerivRightConvComplex` and `ArchCutProjector` are back to their pre-set state (their only
change is recompilation): their `check_port` readings fell back to the pre-set **5 ok**, **1 ok** and
**48 ok** (0 mismatch / 0 missing on all three), against the 6 / 7 / 49 they carried with the rows in
them.

**Why the plan missed it, and the check that would have caught it**: the scoping audit verified that
each premise node was *ported* and that each home's *subject* matched — it did not verify that the
home is above the premise's **module**. The recipe's §4 step 3 asks for exactly that, and the cheap
mechanical form of it is three lines of Python: build `module -> imports` over `FLTForHuman`, then
require `premise_module ∈ closure(home)` for every premise of every row, *before* scaffolding. That
check is now in the recipe's register (FR-0191) and was run over all thirteen rows here after the
fix (green for all of them).

**A3's substitutes, the same failure in miniature.** Four of A3's prelude rows are ported, but in
`RightConvIntegral` and `Cusp/SpectrumLift` — both *above* `TestFnInvariance`, so importing them is
the same cycle. The row stays in `TestFnInvariance` and the four generic proofs are **transcribed
there**, which is what the pin does in its own file: they are generic type-submodule lemmas with no
test-function content, and their true home is a `RepTheory` module below both — a small refactor
recorded in [../../CARRY-FORWARD.md](../../CARRY-FORWARD.md), not paid here. `dedup.py` will report
their `shape` clusters against `RightConvIntegral`; that is the ruling, and neither side is deleted.

## 4. The orders and the gates

Two dispatches, disjoint files, concurrent:

- `tmp/af55/WORKORDER-AF55A-arch-cut-calculus.md` — order A (A1–A8, 707 silo, five files);
- `tmp/af55/WORKORDER-AF55B-carrier-and-spectrum.md` — order B (B3, B4, B1, B2, B5, 490 silo, three
  new modules).

The gates, per module, are the recipe's §6 and are written into each order: no tree build; the edit
loop at `-DmaxHeartbeats=200000`; `lake build <module>` under `flock`/`timeout` per finished file;
`check_port` at **0 mismatch / 0 missing**; `#print axioms` on every headline
`[propext, Classical.choice, Quot.sound]`; zero warnings; no `sorry`; no `set_option` beyond
`autoImplicit false`; no silencer; `dedup.py` / `move_dead.py` clean. The two orders touch disjoint
files — order A's three appends and two new modules are outside order B's import closure, and order B's
three modules are new — so only the build lock is shared.

## 5. The shelf effect, measured (statements in, proofs in flight)

The shelf reads a pin node as ported from a **declared statement**, so the scaffolds themselves —
not the proofs — move it (FR-0114: the SET-AF47 lesson, where three rows readied on the scaffolds
alone). Re-read with the same command as §0, after the ten scaffolds landed:

| figure | before | **after** | forecast |
|---|---:|---:|---:|
| `needed [F terminal]` | 691 / 291,010 | **678 / 289,813** | 678 / 289,813 ✓ |
| `needed [literal]` | 703 / 294,475 | **690 / 293,278** | — |
| frontier F | 1,726 / 836,542 | **1,739 / 837,739** | +1,197 ✓ |
| ready rows | 45 / 8,516 | **35 / 7,854** | — |
| leaves | 185 / 46,068 | **184 / 46,068** | — |
| `AutomorphicForm` demand | 260 / 113,790 | **247 / 112,593** | 247 / 112,593 ✓ |
| `AutomorphicForm` ready rows | 23 / 3,650 | **13 / 2,988** | — |
| rows readied | — | **2 / 358** | not forecast, as stated |

Every cell closes on the set's own arithmetic: `needed` −13 nodes / −1,197 lines, the frontier
+13 / +1,197, twelve rows off the ready shelf (1,020 of the set's silo; A5's 177 was a leaf) and A5
off the leaves block, and the
`AutomorphicForm` block down from 23 rows / 3,650 to 13 / 2,988.

**Two rows readied by this set**:

- `AutomorphicForm.CuspidalSpectrum.exists_commute_lift_heckeCosetSum_of_isLevelSphericalOfType`
  (295, ten premises, lev 1/1) — the level-spherical commutation of a lift with a Hecke coset sum;
- `AutomorphicForm.CuspidalSpectrum.isFactorizableTestFn_flat` (63, two premises, lev 1/3) — the flat
  test function's factorizability.

Both are `CuspidalSpectrum` rows whose premise sets this set's A4/A5 and A7 close. They are the
natural next cut of the same block, beside the cuspidal-integral pair of §1.1.

**The proof-side landing record** — the files' final line counts, the `check_port` and axiom
readings, the two consumer zones, dedup/move_dead and the deviations — is §6 below; the shelf
readings above do not depend on it.

## 6. The landing record

### 6.1 Order B (landed 2026-11-13)

Five rows, three modules, **257 written proof lines**, zero `sorry`, zero imports added, zero
`set_option` beyond each file's `autoImplicit false`, and no statement, import, namespace, `open`,
`spec-pin:` line or docstring touched — `check_port` reads the dispatch figures unchanged.

| module | lines | decls | `sorry` | build | `check_port` | axioms |
|---|---:|---:|---:|---|---|---|
| `Cusp/CarrierWindowMonotonicity.lean` | 99 → **175** | 2 | 2 → **0** | 4,044 jobs, 3.9 s, silent | **2 ok / 0 / 0** | clean |
| `Cusp/ConstituentModulus.lean` | 80 → **132** | 2 | 2 → **0** | 4,088 jobs, 3.4 s, silent | **2 ok / 0 / 0** | clean |
| `Cusp/SpectrumOrthogonality.lean` | 66 → **324** | 1 | 1 → **0** | 4,092 jobs, 7.7 s, silent | **1 ok / 0 / 0** | clean |
| | | **5** | **5 → 0** | | **5 ok, 0 mismatch, 0 missing** | **5/5** |

`#print axioms` on all five headlines: `[propext, Classical.choice, Quot.sound]`; `#check` at each
fully qualified name resolves (FR-0186). `dedup --within --min-cost 0`: 0 clusters, 0 removable
lines, on each. `move_dead --dry-run`: 0 declarations, 0 lines, 0 live private helpers.

**The two `Siegel` rows are sound and are now consumed.** `B1`/`B2` are the first consumers of
`norm_apply_archCentralUnit_lt_one_of_memLp_of_coversModCentre` (`Siegel/DetWindowCover.lean:911`) and
`memLp_iUnion_centreCutSiegelSet_of_detWindow_le` (`Siegel/CentreCutCover.lean:1773`); both were
re-read clause for clause against the pin and are consumed with the pin's argument order, so the two
modules that had no importer now have one and no statement needed a report.

**Heartbeat behaviour worth recording.** The 259-line orthogonality row is the set's long pole:
it fails the low cap at 30k/35k/40k/45k (at a different line each time — the cost is cumulative) and
passes at 50,000, so it sits at ~46–50k against the module gate's 200,000. That is not the
instance-inference defect the cap is a bisector for; it is one long declaration. At 25,000 it times
out in the `he_coe`/`map_sum` rewrite over the `O.attach` sum.

**One deviation, and it is FR-0187's family seen from a new side.** The pin's `have inner_toCarrier`
is stated over `(a b : … → ℂ) (ha : a ∈ memberSubmodule Φ₀ ξ)`; rewriting it into a goal whose
`toCarrier` arguments are subtypes `⟨↑ψ, ⋯⟩` fails at **application elaboration**, because the
pattern unfolds `memberSubmodule`'s carrier to `IsAutomorphicFnAt F (fdPins F Φ₀) ξ ?a` and then
demands `↥⊤ ≡ ↥(fdPins F Φ₀).Z`. Restating that one local `have` over elements of
`↥(memberSubmodule F Φ₀ ξ)` — same proof body, headline untouched — fixes it. Recorded as FR-0192:
it is the hazard the next consumer of these carriers will hit.

Two further v4.34 adaptations, both statement-preserving and both recorded by the worker: the pin's
four `haveI`s for non-typeclass `let`s became `have` (the linter's own suggestion), and the pin's
`Submodule.orthogonalProjection` family is `orthogonalProjectionOnto` at v4.34. The frozen-but-unused
wrapper binders (`hc` in B1/B2, `hf` in B5) are consumed with a one-line comment rather than
`omit`ted, which is what the zero-warning gate requires.

### 6.2 Order A (landed 2026-11-13)

Eight rows on five files, **309 written proof lines** on top of order B's 386 (the wave's total is
**695 written lines** against 3,378 scaffold lines), zero `sorry`, zero imports added, zero
`set_option` added, and every statement, import, namespace, `open`, `spec-pin:` line and docstring
untouched — `check_port` reads the dispatch figures unchanged.

| file | lines | rows | `sorry` | build | `check_port` |
|---|---:|---|---:|---|---|
| `Adelic/LeftCasimirTestFn.lean` | 1,355 → **1,464** | A1 (:1259), A7 (:1200), A2 prelude (:1333–:1371), A2 (:1378) | 6 → **0** | 3,933 jobs, 8.0 s, silent | **89 ok / 0 / 0** |
| `Adelic/TestFnInvariance.lean` | 304 → **384** | A3 prelude (:270, :303, :339, :357), A3 (:377) | 5 → **0** | nothing to rebuild (in the `ArchApproximation` chain) | **15 ok / 0 / 0** |
| `Adelic/TestFactorIntegral.lean` | 151 → **251** | A4 (:179), A5 (:218) | 11 → **0** | 3,673 jobs, 5.0 s, silent | **15 ok / 0 / 0** |
| `Adelic/ArchApproximation.lean` | 1,258 → **1,260** | A6 (:1245) | 1 → **0** | 3,915 jobs, silent | **8 ok / 0 / 0** |
| `Adelic/Cusp/ConstituentCharCut.lean` | 65 → **83** | A8 (:44) | 1 → **0** | 3,979 jobs, 3.1 s, silent | **1 ok / 0 / 0** |
| | | **8** | **24 → 0** | | **128 ok, 0 mismatch, 0 missing** |

`#print axioms` on all eight headlines: `[propext, Classical.choice, Quot.sound]`; `#check` at each
fully qualified name resolves. `dedup --within` (and at the `shape`/`body` tiers, plus `--cross` on
`TestFnInvariance`): **0 clusters on all five modules** — the four generic helpers of A3 are local
`have`s inside the two proofs that need them (a declaration-level copy would have shown a `shape`
cluster against `RightConvIntegral`), so the pin's duplication stays on the pin side.
`move_dead --dry-run`: 0 declarations on four of the five; `ArchApproximation` reports **one
pre-existing** dead `private theorem LamData_toEcf_coe` (:852, 6 lines, referenced nowhere in the
port, unrelated to A6) — recorded, not moved, since it is not this set's declaration and the module is
a hub.

**The three blocks in `LeftCasimirTestFn` are independent** (A7 uses
`rightConv_mem_archCutSubmodule_of_isArchBiFinite` and the level vocabulary; A1/A2 use the general
Casimir engines and nothing of A7), so the append order is not load-bearing.

**Five deviations, all statement-preserving:**

1. **A3's four generic helpers are inlined as local `have`s** rather than imported — the substitutes
   sit *above* `TestFnInvariance` (§3.4), and the approved ruling is to follow the pin, which restates
   them in its own file.
2. **A5 needs `open AutomorphicForm.ArchConvIntegral in` on its headline** — the pin's own
   `open ARCHCONV in`. The module's `scoped instance : NormedAddCommGroup (PP F)` is only active in
   its namespace, and without the prefix `NormedAddCommGroup (Xm F × PP F)` does not synthesize: a
   three-level product loses the instance search that the two-level `Xm F` wins. Statement text
   untouched, checker unchanged. (`TestFactorIntegral` is the second instance of the `mixedSpace`
   instance-scoping family this set hit — see FR-0189 and FR-0193.)
3. **Three `omit … in` prefixes in `TestFactorIntegral`** for Lean 4.34's `linter.unusedSectionVars`,
   which only fires once a body is no longer `sorry`: the pin's existing `omit [FiniteDimensional ℝ X]`
   before `D1_vanish` extended with `[TopologicalSpace Y] [T2Space Y] [MeasurableSpace Y] [BorelSpace Y]`,
   plus `omit [NumberField F]` before `archEntries_mul` and `continuous_archEntries'`. That is the
   linter's own prescription (the forbidden `set_option linter.…` is *not* used), it drops only
   auto-bound instance binders absent from the statements, and `check_port` is byte-identical.
4. Two pin `haveI`s for `Prop`-classes became `have` (the `linter.style.haveILetI` suggestion).
5. A2's prelude proofs name `archDerivAtComplex_add`/`_smul` unqualified: at v4.34 they live in
   `AutomorphicForm` (`ArchDerivCasimirComplexAPI`), not in `ArchCxGL`; the file opens `AutomorphicForm`.
   The two `archDelBarAt` rows are re-proved pointwise as the pin does, **not** copied from the port's
   `private archDelBarAt_apply'` (whose statement is the function-equality form).

**Heartbeats.** Every AF55A proof fits 200,000 with room (three of the five files pass whole-file at
25,000); the two 25k timeouts are **pre-existing** declarations below the appends
(`LeftCasimirTestFn:1134`, `ArchApproximation:397`), not this set's rows. No cap was raised.

**Consumer zone** `spec/AutomorphicFormSetAF55AConsumer.lean` (291 lines, 8 executed compositions, no
`#check`, no `sorry`): A1/A2 spent as the `(β, βb, memberships)` dictionary, A3 iterated twice to a
double conjugation, A4/A5 as `tsupport`-vanishing, A6 as `Q φ = φ` plus the orbit-span property, A7 as
the pointwise level identity plus the cut half, A8 as the character type read off a non-zero witness.
**0 errors**, silent.

## 7. Reproduce

```bash
cd tools/deps
python3 frontier.py --ds --ready --include-leaves --rank-by silo --top 0 --json > build/shelf11.json
python3 twin_scan.py --node <each of the thirteen rows>            # new × 13
python3 port_advise.py --nodes <each> --json build/af55_advise.json
python3 port_plan.py --json build/af55_advise.json                 # 1,197 raw / 923 net
python3 ../tmp/af55/gen.py new && python3 ../tmp/af55/gen.py append  # the scaffolds
cd .. && for m in <the ten modules>; do python3 spec/check_port.py --force $m; done
```
