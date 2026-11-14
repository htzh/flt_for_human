# SET-AF63 — the `Γ₁` depletion, Atkin–Lehner lowering, and the Petersson product's definiteness

**Status: LANDED (2026-11-14).** Read off the D–S shelf after SET-AF62 with the recipe in
[../deligneSerre/TOPIC-scoping-a-ds-set.md](../deligneSerre/TOPIC-scoping-a-ds-set.md). The
sixty-third set of the column, and its first cut into the **`CuspForm` / `ModularForms` ready block**
that every set since SET-AF43 has listed and deferred: two chains, both of them premises of the
column's own headlines.

**6 rows / 1,985 silo / ≈1,490 net after dedup** in **two new modules**, two orders.

| # | row (`CuspForm.` dropped) | silo | lev | home |
|---|---|---:|---:|---|
| **A** | `exists_gamma1_qCoeff_eq_ite_coprime` *(leaf)* | 339 | 2/4 | new `ModularForms/AtkinLehnerLowering` |
| **B** | `qCoeff_eq_zero_of_coprime_level_of_forall_coprime_qCoeff_eq_zero` | 118 | 1/1 | same module |
| **C** | `exists_qCoeff_eq_sum_primeFactors_of_forall_coprime_qCoeff_eq_zero` | 868 | 2/3 | same module |
| **D** | `peterssonOn_self_re_nonneg_im_eq_zero_eq_zero_iff` *(leaf)* | 249 | 2/2 | new `ModularForms/Analytic/HeckeEigenvalueConj` |
| **E** | `peterssonOn_add_smul_conj` *(leaf)* | 142 | 2/2 | same module |
| **F** | `conj_heckeEigenvalue_eq_of_hasNebentypus` | 269 | 2/2 | same module |

The set is two **chains**, not two grab bags: A → B → C is the coefficient-vanishing ⇒ lower-level
sequence, and C is what readies the 159-line
`exists_hasNebentypus_qCoeff_eq_sum_primeFactors_…`, itself a premise of the 733-line
`IsPrimitiveForm.level_eq_and_qCoeff_eq_of_forall_prime_notMem_qCoeff_eq`; D, E → F is the Petersson
definiteness that
makes the conjugate Hecke eigenvalue a one-line cancellation, and F is a premise of the 431-line
`IsEigenformWith.exists_ringHom_rationalHeckeAlgebraOne_mul_eq`, which is a premise of
`IsEigenformWith.exists_galoisRepAdic_charpoly_frobenius_eq_and_isUnramifiedAt` — the weight-two
`GaloisRep` headline of the D–S route. **A is a premise of the D–S weight-one headline itself**
(`DeligneSerre.exists_residual_galoisRep_charpoly_frobenius_eq_of_weightOne_hecke_eigen`).

## 0. The read

```bash
cd tools/deps
python3 frontier.py --ds --ready --include-leaves --rank-by silo --top 0 --json > build/shelf19.json
python3 frontier.py --selfcheck
```

**The plain read is the one quoted; the correction is not zero this time** (below). Taken on the
landed tree **before** the scaffolds were written (§2 says why that order matters).

| figure | value |
|---|---:|
| `needed [F terminal]` | **662 / 285,984** |
| `needed [literal]` | 675 / 289,684 |
| frontier F | 1,754 / 841,333 |
| ready rows, all namespaces | **23 / 4,539** |
| leaves, all namespaces | **183 / 45,747** |
| `AutomorphicForm` demand | 236 / 109,906 |
| `CuspForm` demand | 34 / 11,498 |
| withheld by the FR-0044 guard | 4 / 831 |
| cone / avoided | 2,103 / 982,173 · 140 / 74,620 |

**`--selfcheck` FAILS on fifteen rows, not ten.** MD-005's ten `PhiGen`/`ModularPolynomialData` rows
are joined by five more of the same family that the `jq refactor` commit (HEAD, `656567c`) added to
`spec/old_check_stmts.py`'s `SOURCES`: `ModularCurve.ModularPolynomialData.eq_all`,
`ModularCurve.exists_phiIrreducible`, `…_of_finrank_eq`, `ModularCurve.phiIrreducible_all` and
`…_of_prime`. Its live size reads **1,761 nodes / 843,606**. The registry is the phi workstream's (see
[../../spec/METADATA-ISSUES.md](../../spec/METADATA-ISSUES.md) MD-005, which has the list updated).

**The correction is one node, and it is not the frontier column only.** On this read the eleven-row
correction of SET-AF50/55 moved nothing in `needed`; of the fifteen rows, exactly one
(`ModularCurve.ModularPolynomialData.eq_all`, 75 silo) is in the terminal demand, so the corrected
read is **663 / 286,059**, `needed [literal]` is **689 / 294,631**, and the frontier
1,746 / 837,765. No row cut here cites any of
the fifteen (the premise audit is §2), so the shelf this set reads is the same on either marker set.

**The scaffold moves the instrument (FR-0201, measured).** The two scaffolds put 142 public
declarations in the tree, and `frontier.py`'s name tier counts a declaration as ported whether or not
it is proved: on the current tree the same read reports **656 / 283,999**, exactly the six rows'
1,985 silo below the opening figure. So the opening read is the honest one, and the post-landing read
(§4) must be compared against it, never against a read taken with the scaffolds in flight — the rule
FR-0114 already stated, here with its price.

**Cut on the leaves block, as §1 of the recipe says to read it.** Four of the six rows are `leaf`
(A, D, E are premise-free; F's two premises are D and E), the ready block holds only B and C — and the
shelf's best return was on the leaves: porting A (339) readies B (118) which with two ported premises
readies C (868); porting D (249) and E (142) readies F (269). That is 1,985 silo of work that moves
four of the AF/CuspForm block's largest unported nodes.

## 1. What the set says

- **A** — *depletion at `Q`*: for `N * Q ^ 2 ∣ M` a `Γ₁(N)`-cusp form of weight `k` has a `Γ₁(M)`
  sibling `g` whose `n`-th coefficient is `f`'s exactly at the indices coprime to `Q` and zero
  elsewhere. The construction is the average of the `Q` translates `f ∣[k] (S T^{j M / Q} S⁻¹)` minus
  `Q⁻¹` times their sum (`depleteForm`), then the level restriction `Γ₁(N Q²) → Γ₁(M)`; the
  coefficient statement is the exponential-sum identity `sum_exp_two_pi_mul` — the pin's own route,
  no Hecke operator in it.
- **B** — *the criterion in the level*: if the coefficients of `f` vanish at every index coprime to
  `K`, they vanish at every index coprime to `N` (`K` arbitrary, `N` the level), by applying A at each
  prime not dividing `N` and iterating the induction over the prime factors of `N / gcd`.
- **C** — *Atkin–Lehner lowering*: such an `f` at `Γ₁(N)` is a sum `∑_{p ∣ N} (V_p g_p)` of
  `p`-th subsequences of forms at the levels `Γ₁(N / p)`. The proof is the operator half of the
  pin's file: the Atkin–Lehner element `w_ε` (`wGL`), the average `avgV` of the level-`p` translates,
  the decomposition `exists_decomp`/`exists_pieces` into the pieces `pieceForm`, and the
  degeneracy lift `exists_degeneracy_gamma1_hasNebentypus` (ported) to read each piece's `q`-series.
- **D** — *positive definiteness*: `⟪f, f⟫` is real and `≥ 0`, and it vanishes iff `f = 0`. The
  density `dens` is integrated over the standard fundamental domain `𝒟`; the vanishing half is
  analytic continuation on the upper half plane from the open subset `𝒟ᵒ` where the density is
  positive, with `w₀ = 2i` the witness point.
- **E** — *Hermitian symmetry*: additivity in the second slot, `ℂ`-homogeneity, and
  `conj ⟪g, f⟫ = ⟪f, g⟫` for the coset-summed `peterssonOn` — the polarization that lets D be applied
  to a single eigenform.
- **F** — *the conjugate eigenvalue*: for `g ≠ 0` with nebentypus `ε` and eigenvalue `λ` at `p ∤ M`,
  `conj λ = ε⁻¹(p) λ`. The pin's route: the Hecke eigenvalue identity as
  `T_p g = λ g` (`phi_eq_smul_of_qCoeff`), the adjointness
  `⟪T_p g, g⟫ = conj ε(p) ⟪g, T_p g⟫` (`peterssonOn_hecke_eq_conj_mul_of_hasNebentypus`, ported tier
  3), then `⟪g, g⟫ ≠ 0` from D and cancellation.

### 1.1 The shelf, quoted whole — 23 ready rows and 183 leaves, every row cut or deferred

**The ready block: 23 rows / 4,539 silo — 2 cut (B, C), 21 deferred.** The block's weight has moved
off `AutomorphicForm` (its seven remaining rows are all ≤ 333 and are the residues SET-AF62 §1.1 names);
the top of the block is now `EisensteinGeneral` (890), the `GaloisRep` semisimplicity row (495) and the
`ModularCurve` diamond row (485) — each a story of its own, each deferred because this set is the
`CuspForm` chain that feeds the D–S headlines.

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

The three rows this set's two chains feed are **not** on the shelf and are **not** readied by it
(§4 measures the return): `exists_hasNebentypus_qCoeff_eq_sum_primeFactors_of_forall_coprime_qCoeff_eq_zero`
(201) and `IsEigenformWith.exists_ringHom_rationalHeckeAlgebraOne_mul_eq` (536) each still owe two
further premises after this set.

**The leaves block: 183 rows / 45,747 silo — 3 cut (A, D, E; F is a ready-block row, not in this
block), 45,017 silo deferred.** Four of this set's six rows are here, which is the recipe's point
about leaves (cheap declarations, disproportionate readiness): A 339, D 249, E 142 are three of the
block's cheaper rows and they unblock 118 + 868 + 269. What the block still holds, and why none of it
is cut here:

- the `AutomorphicForm` block (≈25 rows, 646 down to 11) — the `CuspidalConstituent`/`WindowedSiegel`
  leaves, each of which owes two or three unported premises and so readies nothing on its own;
- the `CuspForm` block's remaining rows (`exists_finset_dirichlet_sum_eq_and_independent_of_gammaH`
  340, `HasNebentypus.qCoeff_eq_zero_of_coprime_of_apply_eq_sum_slash` 582, and the 864-line
  `exists_basis_hasNebentypus_qCoeff_hecke_eigen` with its 185-line `sum_filter` sibling) — the next
  wave of this same story, each one premise behind a row this set ported;
- `M4aTorus.completedRayL_fe` (12,126) — a leaf that is a whole column of its own, untouched since
  SET-AF47 named it;
- the `NumberField`/`MeasureTheory`/`WeierstrassCurve`/`TateCurve`/`CohCarrier` leaves, all unchanged
  from SET-AF62 §1.1.

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
| `CuspForm.HasNebentypus.qCoeff_eq_zero_of_coprime_of_apply_eq_sum_slash` | 582 | 1/1 | deferred |
| `AutomorphicForm.exists_sum_prod_mul_of_rightTranslatesSpanFinite` | 576 | 2/2 | deferred |
| `NumberField.AdelicHeight.exists_forall_mul_adelicHeight_le_adelicHeight_mul_of_isCompact` | 514 | 1/33 | deferred |
| `LanglandsTunnell.isBoundedOnSiegelWindows_weightOneLift` | 501 | 2/2 | deferred |
| `WeierstrassCurve.finite_stabilizer_and_natCard_le_of_j` | 496 | 1/3 | deferred |
| `NumberField.AdelicBox.exists_eq_sum_indicator_image_integralFiniteAdeles` | 483 | 3/4 | deferred |
| `TateCurve.point_mul_eq_add_of_norm_le_one` | 471 | 1/1 | deferred |
| `LanglandsTunnell.exists_heckeCosetSystem_productionPinsCompact_of_not_dvd` | 446 | 1/2 | deferred |
| `AutomorphicForm.exists_depth_forall_apply_mul_lowerUnipotentGL2_eq_of_sum_translate` | 445 | 1/2 | deferred |
| `ModularForm.heckeU_add_smul_slash_heckeDiagMatrix_slash_of_mem_Gamma0` | 406 | 1/3 | deferred |
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
| `CuspForm.exists_gamma1_qCoeff_eq_ite_coprime` | 339 | 2/4 | **cut A** |
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
| `CuspForm.peterssonOn_self_re_nonneg_im_eq_zero_eq_zero_iff` | 249 | 2/2 | **cut D** |
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
| `CuspForm.HasNebentypus.sum_filter_eq_of_sum_eq` | 185 | 3/3 | deferred |
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
| `CuspForm.peterssonOn_add_smul_conj` | 142 | 2/2 | **cut E** |
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
python3 port_advise.py --nodes CuspForm.exists_gamma1_qCoeff_eq_ite_coprime … --json build/af63_advise.json
```

| module | rows | scaffold (final: §5) | decls | `sorry` | `check_port` |
|---|---|---:|---:|---:|---|
| `ModularForms/AtkinLehnerLowering.lean` (new) | A, B, C | **578** lines | 84 | 70 | **84 ok / 0 / 0** |
| `ModularForms/Analytic/HeckeEigenvalueConj.lean` (new) | D, E, F | **375** lines | 58 | 53 | **58 ok / 0 / 0** |

Both are **new modules**, so neither re-elaborates an existing one, and they are **disjoint files** (the
two orders are safe concurrently; only the build lock is shared). Both elaborate at the low cap with
`sorry` warnings only, and both are checker-green before dispatch — the manager's statement gate is
closed, so a statement a worker cannot match is a report, never a weakening.

**Two dedup rulings, both taken (measured).**

- **A's prelude is written once, for C.** The pin's third file re-copies the first's 25-declaration
  prelude (`intCast_zmod_eq_one_iff_dvd`, `transGL`, `restrictLevel`, `translate`, `depleteForm`,
  `hasSum_qExp`, the `Γ₁`-monotonicity lemmas, …) — the pin's own per-file copy, in the `Γ₁(N)`
  notation. The port writes those declarations **once**, in namespace `Depletion` (A's spelling), and
  `AtkinLehnerMain` opens it: **25 declarations / ≈180 content lines not written twice**, and the
  checker still reports **ok** for both pin copies because it matches the port declaration against the
  copy whose statement hash agrees (the `Γ₁` notation of C's copy hashes differently — the tiers are
  name-first, hash-second, so this resolves, measured on the scaffold — the finding is FR-0200).
- **D and E share a twelve-declaration coset-integral prelude** (`cosum`, `integrand_eq`,
  `petersson_add_right`, `petersson_bounded`, `integrable_cosum`, …), **byte-identical** in the two
  pin files. Written **once**, in `SelfPairing`; `Polarization` opens it. **12 declarations / ≈90
  content lines** not written twice.

**Recorded, not taken: F's prelude against `ModularForms/WeightOne/PrimitiveQCoeffNorm.lean`.** Of
F's 22 prelude declarations, 19 already exist **public** in the port — `CuspForm.PrimitiveQCoeffNorm`'s
`GLReps.phi`, `Phi.phi_props`, `Phi.phi_eq_smul_of_qCoeff`, `T_mem_Gamma1`, `cusp_*`,
`slash_heckeDiagMatrix_slash_T`, … — from the same pin prelude block, which the pin copies into three
`S_` files. Reusing them would need three sub-namespace opens (`GLReps`, `Phi`, and
`HeckePrelude`'s `ModularForm.periodic_of_slash_T`), and the statements are the pin's copies of one
block; the copy stays local so F's proof reads against one namespace, and the cross-module merge is
left to the refactor round. The within-module duplications above are the ones taken now.

**The definition gate is closed for all six rows.** The three `Definitions/` modules the wrappers
import — `Def_FLTPrelim_Modularity`, `Def_CuspForm_PrimitiveFormGamma1`, `Def_CuspForm_PeterssonOn`
— are ported (`ModularForms/HeckeQCoeff.lean`, `Defs/PrimitiveFormGamma1.lean`,
`Analytic/Petersson.lean`), and so is the fundamental-domain layer D's proof spends
(`AutomorphicForm/UpperHalfPlane/{FundamentalDomainVolume,ModularFundamentalDomain}.lean`, whose `𝒟`,
`𝒟ᵒ`, `isOpen_fdo`, `fdo_subset_fd`, `volume_pos_of_isOpen` the proof names).

**The premise audit, by hand** (the recipe's §4 warns that `needed = 1` is a premise claim): A's pin
file imports no `Thm_` module at all; B's two premises are A and
`gamma1_eq_zero_of_prime_not_dvd_of_qCoeff_eq_zero` (`ModularForms/HeckeDiagDegeneracy.lean`); C's
three are B, `exists_sum_eq_forall_gamma1_div_slash_eq` (`ModularForms/NebentypusSeparation.lean`) and
`exists_degeneracy_gamma1_hasNebentypus` (`HeckeDiagDegeneracy.lean`); D and E have no `Thm_` premise;
F's two are D and E, plus the ported tier-3 adjointness `peterssonOn_hecke_eq_conj_mul_of_hasNebentypus`
(`Analytic/PeterssonHeckeTheorems.lean`, registered in `spec/UNWIRED-PUBLIC.md`). None of the fifteen
MD-005 rows is cited by any of them.

## 3. The orders and the gates

Two dispatches, disjoint files, one wave:

| order | rows | file | content | scaffold `sorry`s |
|---|---|---|---:|---:|
| `WORKORDER-AF63A` | A → B → C | `ModularForms/AtkinLehnerLowering.lean` | ≈1,055 | 70 |
| `WORKORDER-AF63B` | D, E → F | `ModularForms/Analytic/HeckeEigenvalueConj.lean` | ≈430 | 53 |

Both orders are chains and both say so: **A before B before C**, **D and E before F** — the later rows'
statements need the earlier ones' conclusions, and the scaffold already places them in that order.

Gates per module: no tree build; edit loop at `-DmaxHeartbeats=200000`; `lake build <module>` under
`flock`/`timeout`; `check_port --force` unchanged (**84 ok**, **58 ok**); `#print axioms` on all six
headlines; zero warnings; no `sorry`; no `set_option` beyond `autoImplicit false`; no silencer;
`dedup --within` / `move_dead` clean; one consumer zone per order. The work orders are in
`lean/tmp/af63/`.

## 4. The shelf effect

*To be measured on the landed tree and quoted against the opening read of §0 (662 / 285,984) — not
against a read taken with the scaffolds in flight (§0, FR-0201).* The **forecast, stated before
dispatch and measured on the graph as it stood**:

- `needed` falls by exactly the six rows' 1,985 silo;
- **the set readies nothing on the shelf.** Every consumer of the six owes at least one further
  unported premise: `CuspForm.exists_hasNebentypus_qCoeff_eq_sum_primeFactors_…` (201) owes three —
  C, `CuspForm.exists_basis_hasNebentypus_qCoeff_hecke_eigen` (864) and
  `CuspForm.HasNebentypus.sum_filter_eq_of_sum_eq` (185) — and drops to owing two;
  `CuspForm.IsEigenformWith.exists_ringHom_rationalHeckeAlgebraOne_mul_eq` (536) owes four — F,
  `ModularCurve.linearIndependent_rationalHeckeRepOne_of_linearIndependent` (875),
  `ModularCurve.exists_injective_ringHom_adjoin_heckeDiamondGenBar_cuspForm` (767) and
  `ModularCurve.moduleFinite_padicInt_tateModule_jOne` (283) — and drops to owing three.

So the return is **zero rows / 1,985 silo consumed** — the shape SET-AF42 recorded for a chain head,
and the reason is stated: the two consumers are 864 + 185 and 875 + 767 + 283 away. **What the set
does buy is the next cut**: the 864 is the `HasNebentypus` basis row and the 185 its `sum_filter`
sibling, and with them the 201 is ready; on the other chain the row that is already ready,
`CuspForm.IsEigenformWith.fg_adjoin_qCoeff` (291, lev 1/8, a premise of the D–S *weight-two* headline),
is a one-row chain into `IsEigenformWith.OperatorAlgebra.finite_adjoin_qCoeff` (16).

## 5. The landing

### 5.1 Order B — the Petersson definiteness and the conjugate eigenvalue (landed 2026-11-14)

All three rows in, **272 written proof lines** over the 375-line scaffold (375 → **597**), 53 `sorry`s →
**0**, no import added, no `set_option` beyond the frozen `autoImplicit false`.

| file | lines | decls | `sorry` | build | `check_port` | axioms |
|---|---:|---:|---:|---|---|---|
| `ModularForms/Analytic/HeckeEigenvalueConj.lean` | 375 → **597** | 58 | 53 → **0** | 3,910 jobs, 6.1 s, silent | **58 ok / 0 / 0** | **3/3 clean** |

Silent at 200,000, 100,000, 60,000 and 30,000 heartbeats — the proofs sit ≥6× under the cap, and the
row's own `peterssonOn_add_smul_conj` needs the finite-index instance, so no bump was ever going to be
the answer. `dedup --within` after the manager's review: **0 clusters / 0 lines**; `move_dead
--dry-run`: 0 declarations. Consumer zone `spec/ModularFormsSetAF63BConsumer.lean` (145 lines, three
zones: D at `⊤`/`k = 0` with the `↔` fired both ways, E at `c = 0`, F at `λ = 1` and at a general real
`λ ≠ 0`): **0 errors**.

**Two findings worth carrying forward.**

- **The scaffold carried a spurious `omit [Γ.FiniteIndex] in` (FR-0202), and the checker cannot see
  that class.** The pin's `S_…add_smul_conj.lean:76` puts the `omit` before `petersson_continuous'`,
  one of the twelve declarations the manager deduped out of `Polarization`; the scaffolder's chunker
  made the `omit` its own chunk, the drop-by-name list left it, and it landed on
  `peterssonOn_add_right`, where it removes the instance the row's proof needs. The worker reported it
  at first belief and deleted the orphan line — which restores exactly the pin's binder set, leaves
  the compared text untouched, and keeps `58/0/0`. The general lesson is logged: `check_port`'s
  declaration regex starts at `theorem`/`def`/…, so **a misplaced `… in` prefix is a silent statement
  change that reads `ok`**; the scaffolder now attaches such a prefix to the chunk it modifies, and
  the per-order skeleton diff is the instrument that catches it.
- **FR-0198's class, resolved by a sibling route instead of a silencer**: the pin proves `cusp_bdd`
  through `haveI : Fact (IsCusp ∞ Γ₁)`, and `Fact` is a `Prop`-valued class, so `haveI` trips
  `linter.style.haveILetI` and `Fact` is not synthesizable from the `Subgroup.map` form of `Γ₁ℝ`.
  The worker proved it as
  `(OnePoint.isZeroAt_infty_iff.mp (F.zero_at_cusps' hc)).isBoundedAtInfty` — same mathematics, no
  `Fact`, no silencer. Together with ORDER A's `haveI` → `have` in `translate`'s `zero_at_cusps'`,
  that is the second resolution of this class this set.

Three further, purely proof-level deviations: `T_mem_Gamma1` by bare `simp`; `periodic_of_slash_T`
delegating to the already-ported `ModularForm.periodic_of_slash_T` (`HeckePrelude.lean:62`) instead of
re-transcribing 20 lines; and `mdifferentiable_heckeU`/`isBoundedAtImInfty_heckeU` kept as the pin's
own inductions because the frozen statements take `k`/`p` as section variables. F's prelude was **not**
deduped against `PrimitiveQCoeffNorm` (recorded in §2, as ordered).

**The manager's review found one miss of its own** — the two `scoped instance`s the pin copies into
both `S_` files (`sl2zContinuousConstSMul`, `fintypeQuot`, 13 lines) were still duplicated in
`Polarization`; the dedup list the manager built had missed them (they are `instance` declarations, not
`theorem`s, and the list was built from the theorem diff). Removed in the review, `open SelfPairing`
supplies them: 13 duplicated lines replaced by a 4-line comment (line count unchanged),
`check_port` still **58 ok / 0 / 0**, `dedup --within` **0/0**, axioms still clean, consumer still 0
errors.

### 5.2 Order A — the `Γ₁` depletion and the Atkin–Lehner lowering (landed 2026-11-14)

All three rows in, **521 written proof lines** over the 578-line scaffold (578 → **1,099**), 70
`sorry`s → **0**, no import and no `set_option` added, no `private` declaration.

| file | lines | decls | `sorry` | build | `check_port` | axioms |
|---|---:|---:|---:|---|---|---|
| `ModularForms/AtkinLehnerLowering.lean` | 578 → **1,099** | 84 | 70 → **0** | 3,935 jobs, 11 s, silent | **84 ok / 0 / 0** | **3/3 clean** |

Per row: `Depletion` 148 → 320 (A), `CoprimeLevel` 24 → 96 (B), `AtkinLehnerMain` 319 → 594 (C). C's
proofs use `Depletion`'s prelude through the frozen `open Depletion` — **the pin's 25-declaration
re-copy is not repeated**, which is the set's main dedup and it held through the proofs. `dedup
--within`: one cluster / 14 lines, `Depletion.main` against headline A — the pin's own staged
`main` + wrapper `solution` pair, both public and both checked; kept, as SET-AF62 ruled its two
wrapper-over-engine clusters. `move_dead --dry-run`: 0 declarations. Consumer zone
`spec/ModularFormsSetAF63AConsumer.lean` (137 lines, 9 compositions: A at `Q = 2` with the odd/even
halves; B at `K = N` and `K = 1`; C collapsed at prime `N` and at `N = 5` reading the single term):
**0 errors, 0 warnings**.

**The heartbeat measurement (FR-0168's instrument, on this pin family).** The pin's file for row C
opens with `set_option maxHeartbeats 3200000` and the port does not carry it. Re-elaborated at 40,000 /
30,000 / 20,000 / 15,000: silent at all four; first failure at **14,000**, in
`Depletion.exists_cocycle_trans` (its `simp` entry computation). So the worst proof sits in
**[14k, 15k] — a 13× margin** under the 200,000 cap, and the pin's 40×-class override is again
genuinely unnecessary rather than merely dropped. No instance-inference defect, nothing raised.

**One proof-level adaptation, hit twice (FR-0203).** v4.34's `SpecialLinearGroup` is `@[expose]`, so
the pin's anonymous constructors `⟨!![…], hdet⟩` elaborate at the *unfolded* subtype and the following
`mapGL ℝ` / `Gamma1_mem` steps stop unifying ("has type `{A // A.det = 1}` but expected `SL(2, ℤ)`").
Both cocycle lemmas bind the element (`let δ : SL(2, ℤ) := ⟨…⟩`) and record
`hδcoe : (δ : Matrix …) = !![…] := rfl`, then rewrite with it — the playbook §6 "state the intermediate
at the named type" rule in its `@[expose]` form. That is the only reason either proof is not verbatim.

Five further, purely proof-level deviations: v4.34's 3-argument `hasSum_qExpansion` spelling;
`map_sum` → `FunLike.coe_sum`; the deprecation renames (`coe_sub`/`coe_smul`/`coe_zero` →
`FunLike.*`, `if_pos`/`if_neg` → `ite_eq_left`/`ite_eq_right`, `dif_pos` → `dite_eq_left`); two
`tac1 <;> tac2` → `;` and two dropped no-op `push_cast` for the linter; and the five `haveI : NeZero …`
→ `have` sites (the scaffold's own `translate` fix, extended). One frozen statement carries an unused
`hp : p ≠ 0` (`slashV_lowU_avgV`), where the pin's own proof never spends it: the port binds it with
`have _hp : p ≠ 0 := hp` plus a comment rather than rename the binder — a statement byte change is worse
than a dead `have`, and the alternative (`set_option`) is forbidden.

### 5.3 The set's numbers, and the plan-vs-actual

| figure | before (opening read) | **after** | forecast |
|---|---:|---:|---:|
| `needed [F terminal]` | 662 / 285,984 | **656 / 283,999** | −6 / −1,985 ✓ exact |
| `needed [literal]` | 675 / 289,684 | **669 / 287,699** | −6 / −1,985 ✓ exact |
| frontier F | 1,754 / 841,333 | **1,761 / 843,606** | +7 / +2,273 (the six rows' 1,985 plus 288 lines the name tier now maps) |
| ready rows | 23 / 4,539 | **23 / 4,539** | unchanged ✓ |
| leaves | 183 / 45,747 | **180 / 45,017** | −3 / −730 ✓ (A, D, E) |
| `CuspForm` demand | 34 / 11,498 | **28 / 9,513** | −6 / −1,985 ✓ exact |

**The forecast's zero return is what actually happened: no row was readied.** The shelf's composition
is unchanged and the six rows left exactly their own silo behind. That is the honest shape of a chain
head, and §4 recorded it before dispatch; the set's value is that the two chains are now *short*:
`CuspForm.exists_hasNebentypus_qCoeff_eq_sum_primeFactors_…` (201) is two premises away (864 + 185) and
`IsEigenformWith.exists_ringHom_rationalHeckeAlgebraOne_mul_eq` (536) three (875 + 767 + 283), while
`CuspForm.IsEigenformWith.fg_adjoin_qCoeff` (291, lev 1/8) is ready and readies the 16-line
`OperatorAlgebra.finite_adjoin_qCoeff`.

Plan vs actual: **the cut** was right to the line (six rows, 1,985 silo consumed, 1,985 lines of
`needed` gone); **the dedup** came out 25 + 12 + 2 declarations not written twice (the last, two `scoped
instance`s, found by the manager at review, §5.1); **the price** was 793 written proof lines against a 1,490-net estimate —
the estimate counted *content*, and a large part of the pin's content in these two modules is prelude
whose proofs are short in the port; the two orders needed no re-cut and no blocker beyond FR-0202's
orphan `omit`, which the worker fixed inside its dispatch. **Frictions**: FR-0200 (the checker resolves
a once-written prelude), FR-0201 (the scaffold moves the instrument), FR-0202 (the orphan `… in`
prefix), FR-0203 (`@[expose]` `SpecialLinearGroup`).

## 6. Reproduce

```bash
cd tools/deps
python3 frontier.py --ds --ready --include-leaves --rank-by silo --top 0 --json > build/shelf19.json
python3 frontier.py --selfcheck
python3 lean/tmp/af63/gen.py --force          # the two scaffolds — run BEFORE the opening read (§0)
cd .. && python3 spec/check_port.py --force FLTForHuman/ModularForms/AtkinLehnerLowering.lean
python3 spec/check_port.py --force FLTForHuman/ModularForms/Analytic/HeckeEigenvalueConj.lean
cd lean && lake env lean spec/ModularFormsSetAF63AConsumer.lean
lake env lean spec/ModularFormsSetAF63BConsumer.lean
```
