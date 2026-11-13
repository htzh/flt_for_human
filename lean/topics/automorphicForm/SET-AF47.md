# SET-AF47 — the value group of a complete splitting, and the residue field of a valuation subring

**Status: LANDED (2026-11-12)** — §0 the read, §1 the cut and the price, §2 the homes and the
manager's landed layer, §3 the orders and gates, §4 the forecast and its measurement, §5 what the set
does not do, **§6 the landing record and the re-read**. Read off
the D–S shelf with the recipe in
[../deligneSerre/TOPIC-scoping-a-ds-set.md](../deligneSerre/TOPIC-scoping-a-ds-set.md), on the read
SET-AF46's landing left. Forty-seventh set of the column, and the chain AF46 §4 named as next: the
`e = 1` half of the fundamental inequality, in two steps (the independent member, then complete
splitting), with the two small nodes that gate the residue-field side of the same cone.

**5 rows / 2,153 silo / 1,475 net (`port_plan`) in 55 declaration groups and 630 written scaffold
lines.** Return, **measured on the read taken once the scaffolds were in the tree: three rows / 2,786
silo** — `existsUnique_place_forall_residue_sub_mem_nonunits` (1,083, lev 3/9),
`ord_residue_le_sum_ord_of_isIntegral_adjoin` (1,090, lev 2/2) and
`exists_prolongation_of_card_roots_eq` (613, lev 1/2). The third is the D2 unlock: the two big rows were
gated on **C1** and on **D2** respectively, and `ord_residue_le_sum_ord_of_isIntegral_adjoin` is the row
D2's 200 in-graph consumers produce. **Note which instrument moved it:** the shelf reads a pin node as
ported from a declared statement, so the scaffolds themselves (not the proofs) moved it — FR-0114, and
the landing adds no shelf movement of its own.

| # | row | silo | lev | what it says |
|---|---|---:|---:|---|
| **A1** | `ValuationSubring.exists_le_forall_mem_iff_apply_mem` | 168 | 2/2 | the composite `O ≤ O'` of a valuation subring `O` with a valuation subring `W` of its residue field |
| **B1** | `ValuationSubring.exists_valuation_mul_eq_one_of_forall_sup_eq_top` | 870 | 1/1 | an independent prolongation with enough residual witnesses has `e = 1` |
| **C1** | `ValuationSubring.exists_valuation_mul_eq_one_of_finrank_le_card` | 1,062 | 1/1 | complete splitting forces trivial ramification in the value group |
| **D1** | `ValuationSubring.exists_root_mem_of_monic` | 23 | 1/2 | a monic polynomial over a valuation subring of an algebraically closed field has its root in the subring |
| **D2** | `ValuationSubring.isAlgClosed_residueField` | 30 | off-shelf | the residue field of such a subring is algebraically closed |

## 0. The read

`frontier.py --ds --ready --include-leaves --rank-by silo --top 0 --json`:

| figure | instrument | corrected |
|---|---:|---:|
| `needed [F terminal]` | **712 / 299,802** | **712 / 299,802** |
| `needed [literal]` | 724 / 303,267 | 733 / 306,724 |
| frontier F | 1,704 / 827,574 | 1,694 / 823,223 |
| ready rows | 50 / 10,210 | 50 / 10,210 |
| leaves | 187 / 46,259 | 187 / 46,259 |
| `AutomorphicForm` demand | 260 / 113,790 | 260 / 113,790 |
| `AlgebraicCurve` demand | 42 / 16,769 | 42 / 16,769 |
| `ValuationSubring` demand | 16 / 3,380 | 16 / 3,380 |
| withheld (`premises_pruned`) | 4 rows | 4 rows |

**The corrected read.** `--selfcheck` fails its one line with **ten** `ModularCurve` source markers that
resolve to no port declaration: the five AF41 recorded (`ModularPolynomialData.evalSymm_of_irreducible`,
`…transposeToAdjoin_monic_of_qExpansion`, `PhiGen.evalSymm_of_coeff_evalAtJ_eq`, `PhiGen.evalSymm_of_splits`,
`PhiGen.splits_of_coeff_evalAtJ_eq`) **plus five more from the same workstream**
(`PhiGen.PhiGenDescends.c_eq_zero`, `….c_top`, `….poleOrderLE`, `….sum_mul_jqN_pow_eq_zero`,
`PhiGen.exists_modularPolynomialData_coeff_eq`). They are the **phi-refactor workstream's** pin sides,
not this column's: `spec/old_check_stmts.py` lists those `S_`/`Thm_` files for declarations a later
topic *would* promote (the comments say so), and `twin_scan --node` reports `new` — the mathematics is
not in the port under another name either. The read used the documented `--unport` × 10, and the
inventory is registered as **MD-005** in [spec/METADATA-ISSUES.md](../../spec/METADATA-ISSUES.md).
Note that `needed` does not move (none of the ten is in the terminal mask) while the literal column
moves by nine nodes; the corrected figure is the one to quote.

**The withheld block**, quoted as the recipe requires — all four are the pruned complex-analytic
subject's residue, none is cut here: `ModularCurve.moduleFinite_and_free_padicInt_tateModule_jH`,
`ModularCurve.moduleFinite_padicInt_tateModule_jOne`,
`AlgebraicCurve.Place.exists_natCast_dvd_ord_sub_single_sub_single_complex`,
`AlgebraicCurve.Pic0.finite_torsion_of_isAlgClosed_of_charZero`.

**The premise audit is closed, and it is the cut's warrant.** The five rows' premises are either already
ported or inside the set: A1 has none (`premises = 0`, a leaf row); B1 cites only
`ValuationSubring.exists_forall_mem_and_sub_mem_nonunits` (`FieldTheory/ValuationSubringApproximation.lean`,
landed AF44); C1 cites that one plus **A1 and B1 themselves**; D1 has none; D2 cites D1. `port_plan`'s
layers agree: `{A1, B1, D1}` is layer 0 and `{C1, D2}` layer 1. **Proof-reached targets outside the
set: none** — the five rows' proofs consume only ported declarations and each other.

**The definition gate is closed.** None of the five wrappers imports a `Definitions/Def_*` module (they
import `Mathlib`, `P2M.Util`, and each other's `Theorems/` files), and `port_advise --with-defs` adds no
`Def_` file to the target set. The pin's `ResidueField`/`Polynomial.lifts` objects are mathlib's.

## 1. The cut, and the price

**Why these five.** C1 is the row AF46 §4 named as next, and B1 is its *only* unported premise; A1 and
D1 are its *other* unported premises' gate — A1 gates the AC successor directly, D1 gates D2, and D2 is
the premise of the 1,083-line `existsUnique_place_forall_residue_sub_mem_nonunits` and of ~200 in-cone
consumers. So the five are one closed measurement: the value-group chain (A1 → B1 → C1) and the
residue-field gate (D1 → D2), each row taken whole.

`port_advise` + `port_plan`:

| figure | value |
|---|---:|
| raw `S_` lines | 2,153 |
| declaration lines | 2,090 |
| — duplicate copies (port once) | 284 |
| — boilerplate | 63 |
| distinct declaration groups | 55 |
| once-cost after dedup | 1,806 |
| — already in the port (vetted, `runs` 18 declarations ≈ 331 lines) | 331 |
| **net new math lines** | **1,475** |

**The dedup is the pin's, and it is large.** The pin copies a ~500-line prelude into both the 870- and
the 1,062-line file (`Over`, `Incomparable`, `valuation_sum_eq_one_of_sub`, `locAt` and the Nagata
witness lemmas), and the port had already landed that prelude in two modules while porting the *sibling*
nodes: `FieldTheory/ValuationSubringFinrank.lean` holds `mul_lt_one_aux`, `mem_iff`, `lt_one_iff`,
`le_one`, `eq_one_iff`, `valuation_eq_one_of_le`, `sum_ne_zero`, `eq_of_le` publicly in
`ValuationSubring.CompleteSplitting`, and `FieldTheory/ValuationSubringApproximation.lean` holds
`pow_eq_self_of_orderOf_dvd`, `eq_of_pow_eq_pow_of_not_isOfFinOrder`, `exists_exponent`,
`exists_mul_mem_forall` publicly in `ValuationSubring.W7XK3A`. **18 declarations (331 lines) are
imported, not copied**; the only prelude still written is `locAt` + its three lemmas +
`valuation_sum_eq_one_of_sub`, once, in B1's module, and C1 imports them. `port_advise`'s *drags* block
reports `0 helpers` for every pin file — these files are flat public surfaces, so there is no private
prelude to find.

**No promotions are needed**: every pin-public declaration the set consumes is already public in the
port. **No migration**: all four homes are non-legacy modules (none is in
`spec/old_check_stmts.py`'s `PORT_FILES`).

## 2. The homes, and the manager's landed layer

The homes are by subject, and the import direction is the pin's own (C1's file imports B1's and A1's
`Theorems/` files, so the modules must sit above them):

| module | rows | namespace | imports |
|---|---|---|---|
| `FieldTheory/ValuationSubringComposite.lean` | A1 | `ValuationSubring.Composite` (pin label `W9OComposite`) | mathlib only |
| `FieldTheory/ValuationSubringResidueField.lean` | D1, D2 | `ValuationSubring` | mathlib only |
| `FieldTheory/ValuationSubringIndependent.lean` | B1 | `ValuationSubring`, `ValuationSubring.Independent` (pin label `IndepMember`) | `ValuationSubringFinrank`, `ValuationSubringApproximation` |
| `FieldTheory/ValuationSubringCompleteSplitting.lean` | C1 | `ValuationSubring.CompleteSplitting` (pin label `CompleteSplittingE`) | `ValuationSubringIndependent`, `ValuationSubringFinrank`, `ValuationSubringApproximation` |

**The manager's layer is landed and measured** (scaffolds generated mechanically from the pinned text:
statements verbatim, def bodies verbatim, every theorem body `sorry`):

| module | lines | decls | `sorry` | `check_port --force` |
|---|---:|---:|---:|---|
| `ValuationSubringComposite.lean` | 131 | 8 | 7 | **8 ok / 0 / 0** |
| `ValuationSubringResidueField.lean` | 50 | 2 | 2 | **2 ok / 0 / 0** |
| `ValuationSubringIndependent.lean` | 189 | 8 | 7 | **8 ok / 0 / 0** |
| `ValuationSubringCompleteSplitting.lean` | 260 | 24 | 19 | **23 ok / 0 / 0** |
| | **630** | **42** | **35** | **41 ok, 0 mismatch, 0 missing** |

So **all 41 pin-faithful public statements of the set are verified before a proof is written**, the
headlines sit at the wrappers' names, and the five data definitions (`composite`, `locAt`, `coarsen`,
`bar`, `resHom`, `residueAlgebra`, `isLocalHom_resHom`) are transcribed and building — no `def` is left
`sorry`-closed. The pin's task-label namespaces are **rectified** (`W9OComposite` → `Composite`,
`IndepMember` → `Independent`, `CompleteSplittingE` → `CompleteSplitting`), per instructions.md's
"no random tokens in names"; the checker matches last names, so no marker row is needed. Three v4.34
deprecations inside the transcribed def bodies were fixed at generation time (`Set.mem_setOf_eq` →
`Set.mem_ofPred_eq`, `zero_le'` → `zero_le`, twice). No `set_option` beyond `autoImplicit false`.

## 3. The orders, and the gates

Three dispatches, disjoint files:

| order | modules | silo | `sorry`s | dispatch |
|---|---|---:|---:|---|
| **AF47A** | `ValuationSubringComposite`, `ValuationSubringResidueField` | 191 | 9 | parallel (owns both, mathlib-only) |
| **AF47B** | `ValuationSubringIndependent` | 870 | 7 | parallel |
| **AF47C** | `ValuationSubringCompleteSplitting` | 1,062 | 19 | **after B lands** (its headline consumes B's) |

The orders are `tmp/af47/WORKORDER-AF47A-composite-and-residue-field.md`,
`…-AF47B-independent-prolongation.md`, `…-AF47C-complete-splitting.md`. C was dispatched after B landed so that
its `#print axioms` gate is meaningful (its headline's proof consumes B's, and a `sorryAx` upstream
would read through); its module and its statements are in the tree from the start, so nothing blocks on
it structurally. The gates are the recipe's §6, per module: `lake env lean` at
`-DautoImplicit=false -DmaxHeartbeats=200000` silent and `sorry`-free, the module's own `lake build`
under `flock`/`timeout` with no dependents and no tree build, the checker at the counts of §2, `#print
axioms` on the five headlines, `dedup`/`move_dead`, and one `spec/FieldTheorySetAF47*Consumer.lean` zone
per order with a real cross-module composition.

## 4. Forecast, and the measurement that realised it at scaffold time

| figure | before the set | **measured after the scaffolds** | (my pre-scaffold forecast) |
|---|---:|---:|---:|
| `needed [F terminal]` | 712 / 299,802 | **707 / 297,649** | 707 / 297,649 ✓ |
| `needed [literal]` | 733 / 306,724 | **728 / 304,571** | — |
| frontier F (corrected) | 1,694 / 823,223 | **1,699 / 825,376** | 1,699 / 825,376 ✓ |
| ready rows | 50 / 10,210 | **52 / 12,126** | 51 / 11,036 ✗ |
| leaves | 187 / 46,259 | **185 / 46,068** | 185 / 46,068 ✓ |
| `ValuationSubring` demand | 16 / 3,380 | **11 / 1,227** | 11 / 1,227 ✓ |
| `AlgebraicCurve` demand | 42 / 16,769 | **42 / 16,769** | 41 / 15,686 ✗ |
| rows readied | — | **3 / 2,786** (1,083 + 1,090 + 613) | 2 / 1,696 ✗ |

**Two cells were wrong, and both for the same reason: `isAlgClosed_residueField` (D2) unlocks one more
row than its own consumer list names.** Its 200 in-graph consumers produce a third ready row,
`ord_residue_le_sum_ord_of_isIntegral_adjoin` (1,090, lev 2/2), which my forecast did not count; and the
`AlgebraicCurve` demand does not fall at all, because the rows that become ready are themselves
`AlgebraicCurve` nodes that remain unported (demand counts unported nodes).

**Read the instrument column carefully.** A pin node counts as ported as soon as the port *declares* its
statement, so **the scaffold, not the proof, moves the shelf** (FR-0114): these five rows left `needed`
the moment the four modules were written with `sorry` bodies, and the landing's own contribution is
`#print axioms` and silence, not demand. The set's `needed` movement is therefore measured once, on the
scaffold read, and is not expected to move again.

## 5. What this set does not do

**The ready block (50 rows / 10,210 silo, before the scaffolds; 52 / 12,126 after them)** — every row
is *deferred as a block* except B1 and, after the set, the three rows §4 measures; the rest are the
column's normal queue. The table is the **pre-set** shelf, so the three rows that entered are not in it:

| silo | lev | row |
|---:|---|---|
| 890 | 3/5 | `EisensteinGeneral.Piece.exists_forall_nonempty_factorizationDatum` |
| 635 | 1/1 | `AutomorphicForm.integral_mul_eq_integral_mul_weight_mul_tsum_sub_average_of_isCuspidalFn` |
| 580 | 1/2 | `NumberField.exists_differentiableOn_eq_tprod_inv_one_sub_absNorm_cpow_neg_and_tendsto_sub_one_mul` |
| 495 | 1/1 | `GaloisRep.exists_isSemisimpleRepresentation_charpoly_map_eq_of_trace_det_frobenius_mem_range` |
| 485 | 1/5 | `ModularCurve.IsDiamondPullbackModL.apply_eq_one_iff_gamma0Units_mem` |
| 361 | 1/1 | `LanglandsTunnell.linearDependent_string_of_gl2Complex_whittaker_system_of_moderateGrowth` |
| 333 | 1/1 | `AutomorphicForm.exists_finset_forall_exists_mem_valued_eq_max_and_contentHomFin_mul_sq_eq` |
| 329 | 2/2 | `LanglandsTunnell.exists_rpow_bound_near_zero_of_whittaker_ode_of_discrete_tower_of_moderateGrowth` |
| 305 | 1/7 | `LanglandsTunnell.TateLocal.integral_comp_inv_eq_integral_modulus_inv_sq_mul_adicCompletion` |
| 291 | 1/8 | `CuspForm.IsEigenformWith.fg_adjoin_qCoeff` |
| 261 | 1/6 | `AlgebraicCurve.RegularProlongation.exists_basis_mem_integers_piResidue_linearIndependent_of_sum_finrank_eq` |
| 260 | 1/1 | `AutomorphicForm.CuspidalSpectrum.apply_eq_zero_of_mem_orthogonal_cuspLevelSubcarrier_of_isLift_rightConv_of_rightInvariant` |
| 252 | 1/1 | `CohCarrier.exists_surjective_doubleCoset_gammaH_zpowers_of_addOrderOf_eq` |
| 229 | 1/1 | `AutomorphicForm.SmoothCusp.not_isHeckeCosetEigenfunctionAt_levelOne_bot_inf_finiteAdelicGL2Subgroup` |
| 215 | 3/5 | `NumberField.AdelicHaar.exists_map_adelicGLHaar_eq_smul_prod` |
| 209 | 1/3 | `AutomorphicForm.apply_mul_eq_of_isKfSmooth_of_forall_placeEmbed_of_mem_maximalCompactAway` |
| 200 | 1/1 | `MeasureTheory.exists_integral_conj_apply_smul_ne_zero_of_forall_norm_apply_eq_of_continuous` |
| 192 | 5/8 | `AutomorphicForm.peterssonIntegral_self_ne_zero_of_isFundamentalDomain_of_continuous` |
| 179 | 1/1 | `AutomorphicForm.lintegral_rationalCentreUnipotentHaar_comp_heckeGen_mul_centralScalar_conj` |
| 170 | 2/13 | `AlgebraicCurve.RegularProlongation.exists_monic_coeff_natDegree_le_of_forall_valuationSubring` |
| 165 | 1/11 | `AutomorphicForm.exists_isFundamentalDomain_globalPoints_range` |
| 140 | 1/1 | `AutomorphicForm.isArchSmoothAtComplex_rightConv_and_exists_archCasimirAtComplex_rightConv_eq_of_isArchBiFinite` |
| 138 | 1/1 | `ValuationSubring.exists_aeval_div_eq_aeval_div_add_inv_pow_mul_add_aeval_inv` |
| 133 | 2/3 | `AutomorphicForm.isFactorizableTestFn_comp_inv_mul` |
| 129 | 1/2 | `NumberField.AdelicBox.setLIntegral_adelicBox_comp_mul_add_eq_of_periodic` |
| 128 | 2/2 | `LanglandsTunnell.dirichletIdeleChar_mul_modulus_det_gen` |
| 128 | 1/1 | `NumberField.AdelicHaar.adelicAddHaar_setOf_fst_apply_eq_eq_zero` |
| 122 | 1/11 | `NumberField.AdelicBox.integral_cond_adelicBox_comp_mul_algebraMap` |
| 120 | 1/2 | `NumberField.TateGlobal.exists_isCompact_forall_eq_principal_mul_balanced_mul` |
| 119 | 1/1 | `NumberField.AdelicHaar.adelicAddHaar_setOf_snd_apply_eq_zero` |
| 113 | 1/16 | `AutomorphicForm.SmoothCuspRealizationAt.centralChar_eq_of_agreesAwayFromFinite` |
| 108 | 1/1 | `AutomorphicForm.IsKfSmooth.exists_isCompact_isOpen_eq_inf_forall_apply_mul_eq` |
| 105 | 6/18 | `NumberField.exists_differentiable_eq_sub_one_mul_dedekindZeta_and_apply_neg_two_mul_add_one_eq_zero` |
| 100 | 1/13 | `LanglandsTunnell.TateLocal.measureReal_setOf_valued_le_exp` |
| 72 | 1/1 | `AutomorphicForm.isArchSmoothAt_rightConv_and_exists_archCasimirAt_rightConv_eq_of_isArchBiFinite` |
| 68 | 1/1 | `AutomorphicForm.isotypicCuspSubmodule_le_isotypicCuspSubmodule_of_le_of_ne_bot` |
| 66 | 1/3 | `ModularForm.exists_gamma0_qExpansion_div_eq_E4_cube_div_discriminant` |
| 66 | 1/2 | `AutomorphicForm.CuspidalConstituent.cuspKFiniteSubmodule_le_cuspKFiniteSubmodule_of_le_of_exists_ne_zero` |
| 59 | 1/1 | `AutomorphicForm.CuspidalSpectrum.isFinTestFactor_conj_inv_mul_ideleNorm_det_rpow` |
| 56 | 1/1 | `AutomorphicForm.CuspidalConstituent.exists_inf_archCutSubmodule_ofChar_ne_bot_of_ne_bot` |
| 52 | 3/5 | `AutomorphicForm.CuspidalConstituent.rightConv_mem_levelInvariantSubmodule_inf_archCutSubmodule_of_isArchBiFinite` |
| 51 | 1/3 | `CuspForm.coe_diamondLinH_and_coe_heckeTLinH_and_coe_heckeULinH_of_hasNebentypus` |
| 48 | 1/1 | `AutomorphicForm.isFinTestFactor_integral_mul_of_isFinTestFactor_of_hasCompactSupport` |
| 37 | 3/8 | `AutomorphicForm.CuspidalSpectrum.exists_hasModulus_of_isCuspConstituent` |
| 36 | 1/3 | `ModularCurve.exists_sum_smul_eq_of_isIntegralQExp_gamma1` |
| 30 | 1/6 | `AutomorphicForm.SiegelCovering.centreCutSiegelSet_coversModCentre_rat` |
| 29 | 2/3 | `AutomorphicForm.exists_linearMap_archCutProjector` |
| 27 | 3/5 | `AlgebraicCurve.RegularProlongation.finiteDimensional_adjoin_residue_of_sum_finrank_eq` |
| 24 | 1/6 | `ModularCurve.rep_tateModule_jOne_comm` |

**The leaves block (187 rows / 46,259 silo)** — deferred as a block; the two rows this set cuts from it
are A1 and D1, and the block's composition by namespace is the record of what is left:

| namespace | rows | silo | largest rows |
|---|---:|---:|---|
| `M4aTorus` | 1 | 12,126 | `completedRayL_fe` — the queued big effort (four unported `Def_` modules) |
| `NumberField` | 45 | 8,485 | `exists_continuousOn_exp_eq_rayClassLSeries` (684), `multipliable_differentiableOn_tprod_ne_zero_eulerProduct_of_norm_le_one` (600) |
| `AutomorphicForm` | 39 | 7,531 | `CuspidalConstituent.exists_forall_le_archTypeSubmoduleAt_of_isSimple_of_le_iSup` (646), `exists_upperTriangular_globalPoints_mul_mul_scalar_mul_finIdeleDiag_inv_mem_finiteIntegralGL2` (587) |
| `WeierstrassCurve` | 18 | 2,860 | `finite_stabilizer_and_natCard_le_of_j` (496) |
| `CuspForm` | 11 | 2,319 | `HasNebentypus.qCoeff_eq_zero_of_coprime_of_apply_eq_sum_slash` (582) |
| `LanglandsTunnell` | 9 | 1,845 | `isBoundedOnSiegelWindows_weightOneLift` (501) |
| `MeasureTheory` | 11 | 1,647 | `exists_continuous_convolution_self_eq_forall_integral_smul_isotypic` (626) |
| `ContinuousLinearMap` | 7 | 1,539 | `eq_zero_of_forall_exists_mem_sub_real_smul_eq` (385) |
| `EisensteinGeneral` | 5 | 1,378 | `Piece.exists_summable_majorant_of_lattice_vanishing` (666) |
| `ValuationSubring` | 9 | 1,151 | `ringKrullDim_le_ringKrullDim_comap_add_trdeg` (269), `exists_smul_mem_of_transcendental_residue` (262) |
| `TateCurve` | 9 | 1,038 | `point_mul_eq_add_of_norm_le_one` (471) |
| the remaining six namespaces | 23 | 4,340 | `ModularForm` 6, `UnramifiedWhittaker` 3, `HaarQuotient` 2, `IsDedekindDomain` 5, `LocalNewvector` 2, `CohCarrier` 5 |

**Also not this set**: `M4aTorus.completedRayL_fe` (12,126 silo) remains the queued big effort — four
unported `Def_` modules (1,139 pin lines, 82 declarations) then 742 declarations of mechanical
transcription; the `EisensteinGeneral.Piece.exists_forall_nonempty_factorizationDatum` story (890, six
`Def_` wrappers, five consumer rows of 595–3,295); and the `NumberField` Dedekind-zeta pair
(580 + 105, 18 consumers on the 105).

## 6. The landing (2026-11-12)

Three orders, all green, **zero `sorry` left in the set**, and no statement moved (every checker count is
the scaffold's):

| order | module | lines | decls | `sorry` → | `check_port` | build | axioms | consumer |
|---|---|---:|---:|---|---|---:|---|---:|
| **47A** | `ValuationSubringComposite.lean` | 131 → **198** | 8 | 7 → 0 | **8 ok / 0 / 0** | 3,092 jobs, 4.9 s | 3/3 | 132 lines, 0 err |
| **47A** | `ValuationSubringResidueField.lean` | 50 → **78** | 2 | 2 → 0 | **2 ok / 0 / 0** | 3,095 jobs, 3.2 s | | |
| **47B** | `ValuationSubringIndependent.lean` | 189 → **572** | 8 | 7 → 0 | **8 ok / 0 / 0** | 3,099 jobs, 7.6 s | 1/1 | 123 lines, 0 err |
| **47C** | `ValuationSubringCompleteSplitting.lean` | 260 → **804** | 24 | 19 → 0 | **23 ok / 0 / 0** | 3,101 jobs, 6.7 s | 4/4 | 111 lines, 0 err |
| | | **630 → 1,652** | **42** | **35 → 0** | **41 ok, 0 mismatch, 0 missing** | | **8/8** | **366 lines, 0 err** |

Each module is silent at `-DautoImplicit=false -DmaxHeartbeats=200000` with zero warnings, carries no
`set_option maxHeartbeats`, no `omit` used as a silencer and no linter silencing; every module builds
alone under `flock`/`timeout` (no tree build, no dependents). `dedup` over the four together reports **0
duplicate clusters / 0 removable lines** and `move_dead` reports **0 declarations** on each. The
manager re-ran the checker, the axioms probes and the three consumer zones independently of the workers'
reports. **No promotions were needed and no `private` declaration exists in the set**, so the surface
gate is closed trivially: the checked surface *is* the pin's public surface.

### 6.1 What the three orders found

1. **`main` is 200 lines of the pin's induction, verbatim, inside budget.** The worker transcribed
   `Nat.strong_induction_on` on `S.card` with no restructure — coarsen, recurse on `S.image co`,
   renormalize, descend to `bar`/`card_add_card_le_finrank`, finish with AF47B's criterion at
   `bar QR Q` — and the 200,000-heartbeat cap held with room; the whole 804-line module elaborates in
   ~6.5 s. Its proof-side drift is the v4.34 rename family only (`if_pos`/`if_neg`/`dif_pos`/`dif_neg` →
   `ite_eq_left`/`ite_eq_right`/`dite_eq_left`/`dite_eq_right`, `zero_le'` → `zero_le`), at 18 sites.
2. **AF47B's headline is the induction, not the pin's `solution`** — the port declares the statement
   once, at the wrapper's name, and the pin's `:857` application refers to an inner copy the port
   deliberately does not have. Measured cost: 313 lines against the pin's 314.
   **Its heartbeat floor is a budget fact worth keeping**: the file elaborates at 50,000, fails at
   25,000 (inside the headline's `hXval`), i.e. ~4× headroom at the project cap, and no override.
3. **The scaffold's import list was not closed over the set's own modules** (FR-0181). 47C's worker found
   `bar_sup_bar_eq_top` needs A1 (`exists_le_forall_mem_iff_apply_mem`, pin `:586`), whose home the
   brief named — but the scaffold's imports were derived from the *pin's* import lines, which point at
   `Theorems/…` files, not at the port's modules, so the edge was missing. The worker added
   `import FLTForHuman.FieldTheory.ValuationSubringComposite` and reported it; **ruling: keep it.** The
   suggested alternative — putting that import in `ValuationSubringFinrank.lean` — inverts the
   dependency order, since `Composite` is a sibling *above* `Finrank`, not below it.
4. **A `local instance` does not travel through `import`** (FR-0182). 47C's consumer zone had to repeat
   `attribute [local instance] ValuationSubring.CompleteSplitting.residueAlgebra`, otherwise the
   `Module (ResidueField ↥(R.comap …)) (ResidueField ↥R)` hypothesis of
   `card_add_card_le_finrank` is not synthesizable — the `ResidueField`-is-a-`def` trap (FR-0177) seen
   from the consumer side. The zone installs the existing def locally, so nothing is `private` and no new
   named instance was invented.
5. **The consumer instances again needed checking against the structure, not the hypotheses**
   (FR-0171's class, fifth instance): `W = ⊥` and `O' = ⊥` are untypeable — `ValuationSubring` has
   `OrderTop` and **no `OrderBot`**, and `{0}` fails `mem_or_inv_mem'` at `x = 1`. 47A substituted the
   `⊤`-and-`ℤ_(2)` readings, which read both the "no cut" and the "cuts `O` down" case.

### 6.2 The re-read

| figure | before the set | after (measured twice) | forecast |
|---|---:|---:|---:|
| `needed [F terminal]` | 712 / 299,802 | **707 / 297,649** | ✓ |
| `needed [literal]` (corrected read) | 733 / 306,724 | **728 / 304,571** | — |
| frontier F (corrected) | 1,694 / 823,223 | **1,699 / 825,376** | ✓ |
| ready rows | 50 / 10,210 | **52 / 12,126** | 51 / 11,036 ✗ |
| leaves | 187 / 46,259 | **185 / 46,068** | ✓ |
| `ValuationSubring` demand | 16 / 3,380 | **11 / 1,227** | ✓ |
| `AlgebraicCurve` demand | 42 / 16,769 | **42 / 16,769** | 41 / 15,686 ✗ |
| rows readied | — | **3 / 2,786** | 2 / 1,696 ✗ |

**The read was taken twice — once with the scaffolds and once with every proof in — and the two are
identical in all eight cells.** That is the set's instrument finding, stated at scale: the shelf reads a
pin node as ported from a *declared statement*, so a scaffold of `sorry`s already books the demand
(FR-0114), and a set's landing has no shelf movement of its own. The forecast's three misses are all one
cause: `isAlgClosed_residueField` readies **three** rows, not the two its own consumer list names — the
third, `ord_residue_le_sum_ord_of_isIntegral_adjoin` (1,090, lev 2/2), is the row its 200 in-graph
consumers produce — and since the rows that enter are themselves unported `AlgebraicCurve` nodes, the AC
demand does not fall. The `needed` model was exact.

**Named next**: the three readied rows (`existsUnique_place_forall_residue_sub_mem_nonunits` 1,083,
`ord_residue_le_sum_ord_of_isIntegral_adjoin` 1,090, `exists_prolongation_of_card_roots_eq` 613 — one
story: the prolongation of regular local data, and the two `exists_pow_eq_of_residue_eq_pow_of_…`
successors it gates), then `M4aTorus.completedRayL_fe` (12,126 silo, four unported `Def_` modules), then
the `EisensteinGeneral.Piece` factorization story (890, six `Def_` wrappers).
