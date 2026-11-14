# SET-AF64 — the nebentypus eigenbasis, and the character separation of a sum

**Status: LANDED (2026-11-14).** Read off the D–S shelf after SET-AF63 with the recipe in
[../deligneSerre/TOPIC-scoping-a-ds-set.md](../deligneSerre/TOPIC-scoping-a-ds-set.md). The sixty-fourth
set of the column, and the set that **pays AF63's forward reference**: AF63 §4 named exactly these four
rows as the next cut, and the two Petersson rows it landed are two of row B's eleven premises.

**4 rows / 2,037 silo / ≈1,500 net** in **two new modules**, two orders.

| # | row | silo | lev | home |
|---|---|---:|---:|---|
| **A** | `ModularForm.heckeU_add_smul_slash_heckeDiagMatrix_slash_of_mem_Gamma0` *(leaf)* | 406 | 1/3 | new `ModularForms/NebentypusEigenbasis` |
| **B** | `CuspForm.exists_basis_hasNebentypus_qCoeff_hecke_eigen` | 864 | 1/5 | same module |
| **C** | `CuspForm.HasNebentypus.sum_filter_eq_of_sum_eq` *(leaf)* | 185 | 3/3 | new `ModularForms/NebentypusDirectSum` |
| **D** | `CuspForm.HasNebentypus.qCoeff_eq_zero_of_coprime_of_apply_eq_sum_slash` *(leaf)* | 582 | 1/1 | same module |

Two chains again, and this time the return is measured to be real. **A → B**: the `Γ₀(N)`-invariance of
`T_p` on a nebentypus eigenspace, then the simultaneous eigenbasis of the whole cusp space. **C → D**:
the character separation of a sum of cusp forms, then the slash-sum trace's coefficient vanishing.
Between them they **ready three rows / 1,433 silo**: `exists_hasNebentypus_qCoeff_eq_sum_primeFactors_…`
(201), `exists_qCoeff_eq_sum_isPrimitiveForm_of_hasNebentypus` (733) and
`eq_smul_of_isPrimitiveForm_of_qCoeff_hecke_eigen` (499) — the newform decomposition and
multiplicity-one rows, whose premises are exactly B, C and the already-ported AF63 rows.

## 0. The read

```bash
cd tools/deps
python3 frontier.py --ds --ready --include-leaves --rank-by silo --top 0 --json > build/shelf20.json
python3 frontier.py --selfcheck
```

| figure | value |
|---|---:|
| `needed [F terminal]` | **656 / 283,999** |
| `needed [literal]` | 669 / 287,699 |
| frontier F | 1,761 / 843,606 |
| ready rows, all namespaces | **23 / 4,539** |
| leaves, all namespaces | **180 / 45,017** |
| `CuspForm` demand | 28 / 9,513 |
| withheld by the FR-0044 guard | 4 / 831 |
| cone / avoided | 2,103 / 982,173 · 140 / 74,620 |

`needed` is exactly SET-AF63's post-landing figure (656 / 283,999) — this set opens on AF63's own
re-read, and nothing has landed since. **`--selfcheck` still FAILS on MD-005's fifteen rows** (the
frontier reads 1,761 / 843,606, which is also its own live size); the correction is **+1 node /
+75 lines in `needed`** (`ModularCurve.ModularPolynomialData.eq_all`), i.e. **657 / 284,074** — the
first scoping read on which MD-005 moves the terminal column, recorded in
[../../spec/METADATA-ISSUES.md](../../spec/METADATA-ISSUES.md) and in SET-AF63 §0. No row cut here
cites any of the fifteen.

**The opening read is taken with AF63's two modules in the tree** (they are landed, not in flight), so
this brief's baseline is the honest one and §4's delta is measured against it — FR-0201's rule.

## 1. What the set says

- **A** — *`T_p` preserves the nebentypus law on `Γ₀(N)`*: for `p ∤ N`, `f` with
  `f ∣[k] γ = ε(γ 1 1) • f` for every `γ ∈ Γ₀(N)` satisfies the same law after
  `T_p f = heckeU k p f + ε(p) • (f ∣[k] heckeDiagMatrix p)`. The proof rewrites `T_p` as the double-coset
  sum over the `p + 1` representatives (`heckeRep`, `sum_eq`), computes the `Γ₀`-cocycle through the
  lift `lift` and the reduction `redMatrix`, and splits the sum over the `OnePoint (ZMod p)` orbit; the
  diamond is the pin's `exists_diamondLift`: `σ ∈ Γ₀(N)` with `σ 1 1 ≡ p (mod N)` exists because `p` is
  invertible mod `N`.
- **B** — *the simultaneous eigenbasis*: the `Γ₁(N)`-cusp space of weight `k` has a `ℂ`-basis of forms
  each of which has a nebentypus `ε` and is an eigenform of every `T_p`, `p ∤ N`. The route: the
  `ε`-isotypic pieces `nebSpace N k ε` are finite dimensional (`finiteDimensional_of_isArithmetic`) and
  span the space (`sum_proj`, `mem_iSup_nebSpace`), the `T_p` commute on them (`heckeLin_comm`) and are
  self-adjoint for the Petersson product (`heckeFamily_selfAdjoint`, which spends A and the ported
  `peterssonOn_hecke_eq_conj_mul_of_hasNebentypus`), and a commuting self-adjoint family is
  simultaneously diagonalizable (`span_eigen_eq_top`, via `SimulEigen`/`IsPosDefHerm`).
- **C** — *distinct characters separate a sum*: if `∑ i ∈ s, v i = 0` and each `v i` is an eigenvector of
  every operator `T p` with eigenvalue `β i p`, and the `β i` are pairwise separated at some `p`, then
  every `v i = 0`. The engine is a strong induction on the index set (`eq_zero_of_sum_eq_zero`), applied
  to the nebentypus twists `twist`.
- **D** — *the trace preserves coefficient vanishing*: for `q ∣ t`, `E` a `Γ₁(q * t)`-form with
  nebentypus, the trace `Φ = ∑ j < q, E ∣[k] (S T^{j t} S⁻¹)` has `qCoeff Φ n = 0` at every `n` prime to
  `K` when `qCoeff E n = 0` there and `K` is coprime to `q`. The proof computes the trace's `q`-expansion
  (`hasSum_depAll`, `sum_exp_two_pi_mul`) and moves the operators through the `Γ₁`-invariance package
  `Inv`.

### 1.1 The shelf, quoted whole — every row cut or deferred

**The ready block: 23 rows / 4,539 silo — none of this set's rows is in it, all 23 are
deferred.** (B is neither ready nor a leaf: it owes A, so the shelf lists it in neither block — the
reason it is written in the same module as A.) `AutomorphicForm`'s seven remaining rows are all ≤ 333 and
unchanged from SET-AF63 §1.1; the top of the block is still `EisensteinGeneral` (890), the `GaloisRep`
semisimplicity row (495) and the `ModularCurve` diamond row (485).

| row | silo | lev | cut |
|---|---:|---:|---|
| `EisensteinGeneral.Piece.exists_forall_nonempty_factorizationDatum` | 890 | 3/5 | deferred |
| `GaloisRep.exists_isSemisimpleRepresentation_charpoly_map_eq_of_trace_det_frobenius_mem_range` | 495 | 1/1 | deferred |
| `ModularCurve.IsDiamondPullbackModL.apply_eq_one_iff_gamma0Units_mem` | 485 | 1/5 | deferred |
| `AutomorphicForm.exists_finset_forall_exists_mem_valued_eq_max_and_contentHomFin_mul_sq_eq` | 333 | 1/1 | deferred |
| `LanglandsTunnell.TateLocal.integral_comp_inv_eq_integral_modulus_inv_sq_mul_adicCompletion` | 305 | 1/7 | deferred |
| `CuspForm.IsEigenformWith.fg_adjoin_qCoeff` | 291 | 1/8 | deferred |
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
| `CuspForm.coe_diamondLinH_and_coe_heckeTLinH_and_coe_heckeULinH_of_hasNebentypus` | 51 | 1/3 | deferred |
| `ModularCurve.exists_sum_smul_eq_of_isIntegralQExp_gamma1` | 36 | 1/3 | deferred |
| `AutomorphicForm.SiegelCovering.centreCutSiegelSet_coversModCentre_rat` | 30 | 1/6 | deferred |
| `ModularCurve.rep_tateModule_jOne_comm` | 24 | 1/6 | deferred |

**The leaves block: 180 rows / 45,017 silo — 3 cut (A, C, D), 177 deferred.** Three of this set's four
rows are here. What the block still holds, unchanged from SET-AF63 §1.1 in every row but its three: the
`AutomorphicForm` `CuspidalConstituent`/`WindowedSiegel` group (each owing two or three premises), the
`CuspForm` block's remaining rows (`fg_adjoin_qCoeff` 291 and `coe_diamondLinH_…` 51 are the next of that
family), `M4aTorus.completedRayL_fe` (12,126), and the
`NumberField`/`MeasureTheory`/`WeierstrassCurve`/`TateCurve`/`CohCarrier` leaves.

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
| `CuspForm.HasNebentypus.qCoeff_eq_zero_of_coprime_of_apply_eq_sum_slash` | 582 | 1/1 | **cut D** |
| `AutomorphicForm.exists_sum_prod_mul_of_rightTranslatesSpanFinite` | 576 | 2/2 | deferred |
| `NumberField.AdelicHeight.exists_forall_mul_adelicHeight_le_adelicHeight_mul_of_isCompact` | 514 | 1/33 | deferred |
| `LanglandsTunnell.isBoundedOnSiegelWindows_weightOneLift` | 501 | 2/2 | deferred |
| `WeierstrassCurve.finite_stabilizer_and_natCard_le_of_j` | 496 | 1/3 | deferred |
| `NumberField.AdelicBox.exists_eq_sum_indicator_image_integralFiniteAdeles` | 483 | 3/4 | deferred |
| `TateCurve.point_mul_eq_add_of_norm_le_one` | 471 | 1/1 | deferred |
| `LanglandsTunnell.exists_heckeCosetSystem_productionPinsCompact_of_not_dvd` | 446 | 1/2 | deferred |
| `AutomorphicForm.exists_depth_forall_apply_mul_lowerUnipotentGL2_eq_of_sum_translate` | 445 | 1/2 | deferred |
| `ModularForm.heckeU_add_smul_slash_heckeDiagMatrix_slash_of_mem_Gamma0` | 406 | 1/3 | **cut A** |
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
| `CuspForm.exists_finset_dirichlet_sum_eq_and_independent_of_gammaH` | 340 | 1/1 | deferred |
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
| `CuspForm.HasNebentypus.sum_filter_eq_of_sum_eq` | 185 | 3/3 | **cut C** |
| `NumberField.AdelicFourier.fourierIntegral_indicator_principalCoset_finiteAdeleRing_apply` | 181 | 1/1 | deferred |
| `ContinuousLinearMap.comp_eq_of_forall_apply_eq_integral_smul_apply_of_convolution` | 180 | 1/1 | deferred |
| `NumberField.AdelicFourier.exists_smul_eq_of_isAddHaarMeasure_adeleRing` | 179 | 2/4 | deferred |
| `ValuationSubring.natDegree_map_eq_card_roots_of_splits` | 174 | 1/1 | deferred |
| `NumberField.AdelicLevel.diagOne_eq_diagOne_mul_archRealLiftAt_mul_centralScalar` | 172 | 3/3 | deferred |
| `HaarQuotient.lintegral_density_mul_eq_one` | 170 | 2/39 | deferred |
| `CuspForm.exists_gamma1_apply_eq_zpow_mul_apply_of_mul_eq_neg_one` | 168 | 1/1 | deferred |
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
| `CuspForm.exists_gamma1_apply_eq_conj_and_qCoeff_eq_conj` | 126 | 3/8 | deferred |
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
| `CuspForm.exists_apply_eq_conj_apply_J_smul_of_forall_jConjSL_mem` | 69 | 2/3 | deferred |
| `NumberField.StandardAddChar.psiLocal_rat_eq_psiV` | 69 | 1/38 | deferred |
| `TateCurve.exists_zpow_mul_mem_annulus` | 69 | 1/6 | deferred |
| `AutomorphicForm.exists_smoothCuspRealizationAt_productionPinsOf_toFun_eq_of_isBoundedOnSiegelWindows_of_coversModCentre` | 69 | 1/1 | deferred |
| `CuspForm.exists_gammaH_coe_eq_of_hasNebentypus` | 68 | 1/2 | deferred |
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
| `CuspForm.exists_gamma1_coe_eq_of_gammaH` | 51 | 1/3 | deferred |
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

```bash
cd tools/deps
python3 port_advise.py --nodes ModularForm.heckeU_add_smul_slash_heckeDiagMatrix_slash_of_mem_Gamma0 \
  --nodes CuspForm.exists_basis_hasNebentypus_qCoeff_hecke_eigen \
  --nodes CuspForm.HasNebentypus.sum_filter_eq_of_sum_eq \
  --nodes CuspForm.HasNebentypus.qCoeff_eq_zero_of_coprime_of_apply_eq_sum_slash \
  --json build/af64_advise.json
```

| module | rows | scaffold | decls | `sorry` | `check_port` |
|---|---|---:|---:|---:|---|
| `ModularForms/NebentypusEigenbasis.lean` (new) | A, B | **801** lines | 84 | 84 | **121 ok / 0 / 0** |
| `ModularForms/NebentypusDirectSum.lean` (new) | C, D | **390** lines | 55 | 55 | **60 ok / 0 / 0** |

Both new, disjoint, elaborating at the low cap with `sorry` warnings only, both checker-green before
dispatch. Three scaffold findings: the `Fintype (DirichletCharacter ℂ N)` instance lives in
`Mathlib.NumberTheory.DirichletCharacter.Orthogonality` and `IsAlgClosed ℂ` in
`Mathlib.Analysis.Complex.Polynomial.Basic` — neither is reached transitively, so both are imported
explicitly (the wrapper's own `attribute [-instance]` lines are the pin's, dropped); and seven
deprecation warnings (`CuspForm.coe_add`, `CuspForm.IsGLPos.coe_smul`) sit inside `def` bodies the
scaffold keeps verbatim, so they are the worker's first edit, not a statement item.

**The dedup ruling: nothing is cut, and it is a measurement, not a preference.** *In-module* there is
nothing to cut — the four pin files do not copy each other's preludes, and `dedup --within` reports one
2-line `body`-tier cluster on the two anonymous constructors of `proj` (`NebentypusEigenbasis:162/164`),
which disappears when those bodies are real. *Across modules*, 33 of A's 36
prelude declarations already exist **public** in the port (`ModularForm.HeckeRepresentatives.heckeRep`,
`redMatrix`, `heckeU_eq_sum_zmod`, `ModularForm.Level.wt`/`lift`, `CuspForm.Gamma1Hecke.sum_slash_mapGL`,
…), and 11 of B's do (`ModularForm.periodic_of_slash_T` and `cusp_*` in `HeckePrelude`, `dd`/`dd_mul`/
`isUnit_dd`/`mem_Gamma1_iff_dd`/`T_mem_Gamma1` in `HeckeEigenNebentypus`, `mapGL_apply`,
`T_pow_mem_Gamma1` in `Analytic/HeckeEigenvalueConj`). They are the pin's per-file copies, under
*different namespaces*, and the port's own copies differ in binder form in several places; cutting them
here would mean rewriting the new module's frozen statements against foreign spellings, which is a
statement change, not a dedup. So the copies stay, the checker verifies them, and the merge is the
refactor round's — the two namespaces are named in each module's header so the merge is mechanical. What
a worker **may** do, and is encouraged to do, is to prove a prelude row by *calling* the ported twin
(`exact ModularForm.HeckeRepresentatives.heckeMatrix_mul_of_eq …`) instead of re-deriving the pin's
argument: the declaration stays, only its body changes.

**The definition gate is closed.** The wrappers import `Def_ModularForm_HeckeOperator`,
`Def_FLTPrelim_Modularity`, `Def_CuspForm_PrimitiveFormGamma1` and `Def_CuspForm_PeterssonOn` — all four
are ported (`ModularForms/Defs/*.lean`, `ModularForms/Analytic/Petersson.lean`), and so is the
fundamental-domain/Petersson layer B spends.

**The premise audit, by hand.** A has no `Thm_` premise. B's eleven: A (this set), the two AF63 rows
`peterssonOn_add_smul_conj`/`peterssonOn_self_re_nonneg_im_eq_zero_eq_zero_iff`, the ported tier-3
`peterssonOn_hecke_eq_conj_mul_of_hasNebentypus`, and seven ported rows
(`finiteDimensional_of_isArithmetic`, `mdifferentiable_heckeU`, `isZeroAt_heckeU`, `isZeroAt_heckeT`,
`qCoeff_heckeU`, `qCoeff_comp_heckeDiagMatrix_smul`, `eq_of_forall_qCoeff_eq`) — all verified present
in `ModularForms/{SturmBound,HeckeQCoeff,HeckeCusps,HeckePrelude}.lean` before dispatch.

**One correction to that audit, found by the worker (ORDER A, its first report):** the premise the row
needs is the **`Γ₁`** form, `CuspForm.finiteDimensional_Gamma1` (`Gamma1CuspStructure.lean:242`), not the
`Γ₀` `finiteDimensional_of_isArithmetic` (`WeightOne/Basic.lean:1567`) that a name-anchored sweep
surfaces — FR-0041's class again, a twin the tool cannot see. The module therefore imports
`FLTForHuman.ModularForms.Gamma1CuspStructure` (also the source of the
`HasEnoughRootsOfUnity ℂ (Monoid.exponent (ZMod N)ˣ)` instance `sum_proj` needs, which
`DirichletCharacter.Orthogonality` does not carry), plus one specific mathlib module,
`Mathlib.LinearAlgebra.Eigenspace.Pi`, for the simultaneous-diagonalization lemmas
`span_common_eigen` uses (`Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_…_of_commute`,
`Eigenspace/Pi.lean`). Both approved at first belief; re-proving 120–150 lines of spectral induction to
avoid a mathlib import would have been the wrong trade. C and D have no
`Thm_` premise; both import `Def_CuspForm_PrimitiveFormGamma1` (ported as
`ModularForms/Defs/PrimitiveFormGamma1.lean`).

## 3. The orders and the gates

| order | rows | file | content | scaffold `sorry`s |
|---|---|---|---:|---:|
| `WORKORDER-AF64A` | A → B | `ModularForms/NebentypusEigenbasis.lean` | ≈1,063 | 84 |
| `WORKORDER-AF64B` | C → D | `ModularForms/NebentypusDirectSum.lean` | ≈653 | 55 |

Gates per module: no tree build; edit loop at `-DmaxHeartbeats=200000`; `lake build <module>` under
`flock`/`timeout`; `check_port --force` unchanged (**121 ok**, **60 ok**); `#print axioms` on all four
headlines; zero warnings; no `sorry`; no `set_option` beyond `autoImplicit false`; no silencer;
`dedup --within` / `move_dead` clean; one consumer zone per order. The work orders are in
`lean/tmp/af64/`.

## 4. The shelf effect

*To be measured on the landed tree against §0's baseline (656 / 283,999).* The forecast, measured on the
graph as it stands:

- `needed` falls by this set's own 2,037 silo;
- **three rows readied, 1,433 silo**: `exists_hasNebentypus_qCoeff_eq_sum_primeFactors_…` (201, which
  needs C, B and AF63's C-row), `exists_qCoeff_eq_sum_isPrimitiveForm_of_hasNebentypus` (733, which needs
  B, the 201 and C) and `eq_smul_of_isPrimitiveForm_of_qCoeff_hecke_eigen` (499, which needs B, the 201
  and C).

That was the forecast — **0.70 silo readied per silo consumed, the column's best since SET-AF44** — and
it was **wrong by two rows**: §5.3 measures one row readied, 201 silo, because the 733 and the 499 each
owe the *201* and a set that readies a row does not ready its consumers. The forecast's error is recorded
there with the rule it should have applied.

## 5. The landing

### 5.1 Order B — the character separation and the slash-sum trace (landed 2026-11-14)

Both rows in, **360 written proof lines** over the 390-line scaffold (390 → **750**), 55 `sorry`s → **0**,
one import added and no `set_option` beyond the frozen `autoImplicit false`.

| file | lines | decls | `sorry` | build | `check_port` | axioms |
|---|---:|---:|---:|---|---|---|
| `ModularForms/NebentypusDirectSum.lean` | 390 → **750** | 55 | 55 → **0** | 3,936 jobs, 8.2 s, silent | **60 ok / 0 / 0** | **2/2 clean** |

Silent at the gate and still silent at **20,000** heartbeats (10 % of it); first failures at 10,000, on the
two matrix-entry `simp`s of `exists_conj_transGL`/`exists_cocycle` — a ~20× margin. `dedup --within`: **0
clusters / 0 lines**; `move_dead --dry-run`: 0 declarations. Consumer zone
`spec/ModularFormsSetAF64BConsumer.lean` (129 lines, 4 executed applications): **0 errors, 0 warnings**.

**The set's own dedup, taken by the worker (trap 1 of the order).** `TraceDepletion.sum_exp_two_pi_mul`
keeps its frozen declaration but its body is now `Depletion.sum_exp_two_pi_mul p hp n` — AF63's copy, the
same statement — so the module imports `ModularForms/AtkinLehnerLowering` and nothing is proved twice. The
manager's review updated the header's "assumes from earlier modules" line to name it (a prose line, not
the frozen part; the worker was forbidden to touch docstrings, so it reported instead).

**Deviations**, all proof-side: FR-0203's `@[expose]` `SpecialLinearGroup` in two sites (`exists_conj_transGL`,
`exists_cocycle` — the anonymous constructor bound at its named type before `val_mapGL_eq` will rewrite
`↑(mapGL ℝ ·)`); the v4.34 renames (`ite_eq_left`/`ite_eq_right`/`ite_true`, `FunLike.coe_zero`,
`IsZeroApply.zero_apply`, `push Not`); `haveI` → `have` for `Fact (IsCusp ∞ (Γ₁ L))` and `NeZero q`;
`ring` → `ring_nf` and one dropped `push_cast` for `linter.unusedTactic`; `convert … <;> try rfl` →
`convert … ; try rfl` for `linter.unnecessarySeqFocus`; and one `change` re-spelled because the port's
`HasNebentypus` body names the matrix entry.

**One correction to the order's own reading suggestion**, found by the worker: the brief proposed zone D
at `q = 2, t = 1`, which the row forbids (`q ∣ t`). The consumer reads it at `q = t = 2` instead (level
`q * t = 4` down to `t = 2`), plus the `q = t = 1` degenerate case where the trace is the identity — a
better pair of readings than the one ordered, since the degenerate case is where the vanishing is inherited
with no work and the `4 → 2` case is where the depletion actually acts.

### 5.2 Order A — the `Γ₀(N)`-invariance of `T_p` and the simultaneous eigenbasis (landed 2026-11-14)

Both rows in, **363 written proof lines** over the 801-line scaffold (801 → **1,164**), 84 `sorry`s →
**0**, two imports added (both approved at first belief, §2), no `set_option` beyond the frozen
`autoImplicit false`.

| file | lines | decls | `sorry` | build | `check_port` | axioms |
|---|---:|---:|---:|---|---|---|
| `ModularForms/NebentypusEigenbasis.lean` | 801 → **1,164** | 84 | 84 → **0** | 4,262 jobs, silent | **121 ok / 0 / 0** | **2/2 clean** |

`dedup --within`: 2 clusters / 6 lines, both the pin's own recorded duplications — `det_eq` declared in
both of the pin's namespaces (`HeckeNebentypus` and `SSbasis`, 4 lines) and the doubled
`scoped instance : NeZero p` at pin `:163`/`:165` (2 lines); kept, as the pin writes them and as FR-0200
resolves them. `move_dead --dry-run`: 0 declarations. Consumer zone
`spec/ModularFormsSetAF64AConsumer.lean` (107 lines, 3 executed zones): **0 errors**.

**Twelve prelude rows were proved by *calling* the ported twin** rather than re-derived — the order's
trap-1 instruction, taken: `mapGL_apply`, `det_eq`, `heckeMatrix_mul_of_eq(+')`,
`heckeDiagMatrix_mul_of_eq(+')`, `sum_range_eq_sum_zmod`, `heckeU_eq_sum_zmod`, `heckeT_eq_sum_onePoint`,
`heckeRep_mul` → `ModularForm.HeckeRepresentatives.*`, and `periodic_of_slash_T` →
`ModularForm.periodic_of_slash_T`. The declarations stay (the checker verifies them against the pin's own
copies); only the bodies call. That is what the recorded non-dedup of §2 was for, and it worked.

**Deviations**, all proof-side: the seven deprecation warnings (`FunLike.coe_add`/`coe_smul`); FR-0203
again in `exists_diamondLift`/`exists_lift`; `T_mem_Gamma1` by bare `simp`; `map_smul` → `_root_.map_smul`
at four sites (the scaffold opens `OnePoint`, whose `OnePoint.map_smul` shadows it — FR-0204);
`if_true` → `ite_true`; `haveI`/`letI` → `have`/`let` for the Prop-valued classes; the roots-of-unity
instance the orthogonality sum actually needs is `NeZero ((Monoid.exponent (ZMod N)ˣ : ℕ) : ℂ)`, not
`NeZero (Monoid.exponent …)` (FR-0205); `isPosDefHerm_B`'s `where` literal rebuilt in tactic mode (the
frozen slot is `:= by`); one `simp only … at this` re-spelled because the v4.34 instance lemma carries a
proof term; and `finiteDimensional_Gamma1` for the `Γ₀` `finiteDimensional_of_isArithmetic` (§2).

**One offered follow-up, declined.** The worker offered to drop the `Gamma1CuspStructure` import and
re-prove `FiniteDimensional ℂ (CuspForm Γ₁(N) k)` locally (~40 lines) to keep the module off a large cone.
Declined, and recorded as a ruling: the import *is* the subject (the Γ₁ cusp space's finite
dimensionality), build time is explicitly not a homing consideration, and 40 lines of re-derived
Sturm-bound machinery is duplicated mathematics — the one thing a port must not do to save a build.

### 5.3 The set's numbers, and the plan-vs-actual

| figure | before (opening read) | **after** | forecast |
|---|---:|---:|---:|
| `needed [F terminal]` | 656 / 283,999 | **652 / 281,962** | −4 / −2,037 ✓ exact |
| `needed [literal]` | 669 / 287,699 | **665 / 285,662** | −4 / −2,037 ✓ exact |
| frontier F | 1,761 / 843,606 | **1,765 / 845,643** | +4 / +2,037 ✓ exact |
| ready rows | 23 / 4,539 | **24 / 4,740** | +3 / +1,433 ✗ **+1 / +201** |
| leaves | 180 / 45,017 | **177 / 43,844** | −3 / −1,173 ✓ (A, C, D) |
| `CuspForm` demand | 28 / 9,513 | **25 / 7,882** | −4 / −2,037 ✓ (A is `ModularForm`-namespaced) |

**The forecast was wrong on the return, and the error is instructive.** One row was readied, not three:
`exists_hasNebentypus_qCoeff_eq_sum_primeFactors_…` (201). The other two I predicted —
`exists_qCoeff_eq_sum_isPrimitiveForm_of_hasNebentypus` (733) and
`eq_smul_of_isPrimitiveForm_of_qCoeff_hecke_eigen` (499) — each owe **that** row, so a set that *readies*
the 201 does not *ready* them; on the measured graph they go from owing two unported premises to owing
one. The rule the forecast should have applied is the one `frontier.py` applies: a row is readied iff
**every** unported premise it has is ported after the set — i.e. the same `unported ⊆ cut` test the
scoping script runs, and never "one of its premises is readied". So the honest return figure is **201 silo
readied for 2,037 consumed (0.10)**, not the 0.70 §4 claimed, and §4's sentence stands only as the record
of a mis-forecast.

What the set *did* buy is the shelf's shape: the `CuspForm` block's three newform rows are now a single
chain (`201 → {733, 499}`) with the 253/254 pair behind the 733 and the 907 behind all four, so AF65's
order A is cut straight off it (§6 of the plan).

**Plan vs actual.** The cut was exact to the line (four rows, 2,037 silo); the dedup came out as measured
(0 in-module cuts — the six lines the checker flags are the pin's own — plus 12 prelude rows proved by
calling the ported twins, and one cross-set reuse of AF63's `sum_exp_two_pi_mul`); the price was 723
written proof lines against a 1,500-net estimate, the same prelude-heavy ratio SET-AF63 recorded; and **two
premise-audit corrections came from the workers** (`finiteDimensional_Gamma1` vs the `Γ₀` twin; the
ℂ-valued `NeZero`), plus one consumer-reading correction (`q ∣ t`). Frictions: FR-0204 (`OnePoint`'s
`map_smul` shadow) and FR-0205 (the roots-of-unity `NeZero`), with FR-0203 and FR-0202 both recurring
exactly as logged.

## 6. Reproduce

```bash
cd tools/deps
python3 frontier.py --ds --ready --include-leaves --rank-by silo --top 0 --json > build/shelf20.json
python3 frontier.py --selfcheck
cd .. && python3 lean/tmp/af64/gen64.py --force   # the two scaffolds (before the opening read; §0)
cd lean && python3 spec/check_port.py --force FLTForHuman/ModularForms/NebentypusEigenbasis.lean
python3 spec/check_port.py --force FLTForHuman/ModularForms/NebentypusDirectSum.lean
lake env lean spec/ModularFormsSetAF64AConsumer.lean
lake env lean spec/ModularFormsSetAF64BConsumer.lean
```
