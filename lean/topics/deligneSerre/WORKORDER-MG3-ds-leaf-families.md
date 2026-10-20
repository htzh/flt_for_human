# WORKORDER-MG3 — the D-S cone's leaf families (waves 1–2)

**Status (both phases closed 2026-10-20; this front of the column is done).** Phase 2 landed **29 modules,
9,874 port lines, 417 statement-checked declarations** (+417 = checker 2434 → **2851 ok**, 0 mismatch / 0
missing / 4 own, **107 modules**), **44 of 49 dispatched nodes**, 5 deferred on missing definition gates (all
in `CARRY-FORWARD.md`); record: [logs/ds-leaf-families-wave2.md](../../logs/ds-leaf-families-wave2.md).
The front's scope criterion, the phase-3 cut it admits (37 nodes / 3,641 lines, recorded and unscheduled), and
the phase-2 overshoot are in [TOPIC-ds-leaf-families.md](TOPIC-ds-leaf-families.md) §8 and
[TOPIC-phase3-small-supplements.md](TOPIC-phase3-small-supplements.md). Phase 1 landed **18 modules, 6,291 port
lines, 323 statement-checked declarations** (+323 = checker 2111 → **2434 ok**, 0 mismatch / 0 missing /
4 own, 78 modules), **28 of its 31 priced nodes** plus the bonus `ModularCurve.theta_mul`; the `ZLattice`
pair (3 nodes / 1,321 pin lines) is deferred on elaboration cost with its drafts parked and its hotspots
diagnosed, and `Def_ModularCurve_EigenformIdeal` is deferred with a recorded trigger. Record:
[logs/ds-leaf-families-wave1.md](../../logs/ds-leaf-families-wave1.md). Phase 2 (§5) is a
separate dispatch. One order, **two phases**, dispatched as three coding groups plus the five small
definition gates. Pricing, readiness and the family survey:
[TOPIC-ds-leaf-families.md](TOPIC-ds-leaf-families.md) §7. This order is its §7.4 wave 1 and
wave 2:

* **Phase 1 — the nine pairs** (§1): 31 nodes / 5,927 raw lines, closing 14 families. Four of the pairs
  need a small definition gate (232 lines, §3).
* **Phase 2 — the free-standing small families** (§5): the 34 remaining ready one-to-three-node
  families, 46 nodes / 9,344 raw lines, ~596 wired declarations.

Expected on completion: checker **2111 → ~3,600**, every module listed and fully diffed, no host edit,
no promotion.

**Audience.** Three fresh coding sessions (groups A–C, §2) plus the manager's gate wave (§3). Method:
[porting-playbook.md](../../porting-playbook.md) §3–§5; wire: the per-module protocol — `spec-pin:`
header, `spec/check_port.py`, no in-source per-declaration marker.

## 1. Phase 1 — the nine pairs, node by node

Each "pair" is a blocked family plus the one ready leaf it needs; the union below is the whole set,
measured with `frontier.needed` on the D-S tree and `port_advise` per group.

| pair | nodes (lines) | union | module(s) |
|---|---|---:|---|
| `Polynomial` | `Polynomial.natDegree_aeval_symm_minpoly_adjoin_coeff_le_of_transcendental` 154, `Polynomial.natDegree_le_of_aeval_mul_inv_pow_mem_adjoin_inv` 53, `Subalgebra.isIntegrallyClosed_adjoin_singleton_of_transcendental` 36 | 243 | 1 |
| `GaussProlongation` | `GaussProlongation.residue_mem_adjoin_residue_of_mem_adjoin_integers` 181, `AlgebraicCurve.RegularProlongation.coeff_mem_of_aeval_mem_integers` 121 *(gate, §3)* | 302 | 1 |
| `IsAlgClosed` | `ValuationSubring.exists_ringHom_extend_of_isAlgClosed` 343, `IsAlgClosed.exists_valuationSubring_ringHom_retraction_forall_valuation_eq_one` 67, `IsAlgClosed.exists_valuationSubring_ringHom_retraction` 26 | 436 | 1 |
| `Int` | `Nat.exists_squarefree_sq_add` 305, `Int.exists_modEq_and_modEq_and_isCoprime` 95, `Int.exists_squarefree_sq_add_mul_add_mul_sq_of_sq_lt_four_mul` 22 | 422 | 1 |
| `EisensteinSeries` | `EisensteinSeries.sum_eisensteinG_vecCons_eq_mul_tsum_divisorSum_mul_cexp_pow` 277, `EisensteinSeries.tsum_inv_cube_congr_one_ne_zero_and_exists_isIntegral` 212, `ZMod.tsum_intCast_pow_inv_eq_sum_bernoulliFun` 101 | 590 | 1–2 |
| `ZLattice` | `SchwartzMap.tsum_eq_tsum_fourier_euclideanSpace` 563, `ZLattice.tsum_translate_eq_inv_covolume_mul_tsum_fourierIntegral` 229, `ZLattice.summable_fourierIntegral_mul_fourierChar_dualSubmodule` 221 | 1,013 | 1–2 |
| `HeckeCharacter` | `HeckeCharacter.eq_of_forall_apply_localUnit_uniformizerUnit_eq` 459 *(gate, §3)*, `NumberField.denseRange_algebraMap_adicCompletion_pi_prod_infinitePlace_pi` 140, `AbsoluteValue.exists_forall_sub_lt_of_pairwise_not_isEquiv` 91 | 690 | 1 |
| `AddCommGroup` | `AddCommGroup.natCard_torsionOrbit_gammaH_eq_index` 368, `AddCommGroup.exists_torsionBy_coords_of_dicyclic_relations` 331, `AddCommGroup.exists_addEquiv_prod_torsionBy_apply_eq_of_forall_exists_ne_smul` 309, `CohCarrier.exists_bottomRow_eq_and_torsionOrbit_bottomRow_eq_iff` 300 | 1,308 | 1–2 |
| `omegaRow_T2` | `omegaRow_T2` 447, `ModularForm.exists_rankinCohen_one_qExpansion_eq` 301, `ModularForm.levelOne_weight_twelve_qCoeff_eq_qCoeff_one_mul_discriminant` 52, `ModularCurve.thetaL_coeffMap_eq_coeffMap_single_mul_derivative` 39, `ModularForm.exists_gamma0_qExpansion_eq_of_levelOne` 36, `ModularForm.levelOne_weight_four_qCoeff_one` 24, `ModularForm.levelOne_weight_six_qCoeff_one` 24 | 923 | 1–2 |

**One extra node is authorized at dispatch:** `ModularCurve.theta_mul` (185 pin lines, its own
`Theorems/` wrapper, outside the D-S cone) — the only declaration `omegaRow_T2`'s proof was missing, and
its ingredient `ModularCurve.theta_coeff` is already public in
`FLTForHuman/ModularCurve/Period/QExpansionDerivative.lean`. It is homed as its own module
`FLTForHuman/ModularCurve/Period/ThetaMul.lean` (a bonus landing, not a gate).

Nothing here is a hub edit, and only §3's gates are new definition modules.

## 2. Groups

| group | pairs | nodes | raw lines |
|---|---|---:|---:|
| **A** | `Polynomial`, `Int`, `IsAlgClosed`, `GaussProlongation` | 11 | 1,403 |
| **B** | `EisensteinSeries`, `ZLattice`, `AddCommGroup` | 10 | 2,911 |
| **C** | `HeckeCharacter`, `omegaRow_T2` (+ `theta_mul`) | 11 | 1,798 |

Groups are disjoint in files and namespaces; the checker wiring stays with the manager and **every
`lake build` is serialized** by `flock .lake/flt_build.lock`. Write your group's modules, build them one
at a time, and report.

## 3. The definition gate (manager's wave, before groups A, C start on their gated pair)

Four pin `Definitions/` modules are **not** homed and are owed whole (playbook §2.3/§4a):

| module | pin lines | for | homed as |
|---|---:|---|---|
| `Def_AlgebraicCurve_ConstantReduction` | 127 | prerequisite of the next row | `FLTForHuman/AlgebraicCurve/ConstantReduction.lean` |
| `Def_AlgebraicCurve_RegularProlongation` | 84 | `GaussProlongation` | `FLTForHuman/AlgebraicCurve/RegularProlongation.lean` |
| `Def_HeckeCharacter_FiniteOrder` | 30 | `HeckeCharacter` | `FLTForHuman/HeckeCharacter/FiniteOrder.lean` |
| `Def_ModularCurve_OmegaOf` | 94 | `omegaRow_T2` | `FLTForHuman/ModularCurve/Defs/OmegaOf.lean` |

All five are new leaf modules with no dependents in the port: home them whole, transcribed verbatim,
with their own `spec-pin:` header; nothing is promoted and nothing is registered. `ConstantReduction` is
a **hub definition module in the pin** (1,944 `S_`/`Theorems/` files import it, and it has its own
unported pin node), and the 3-declaration `toRegularProlongation` bridge that `RegularProlongation` ends
with is named in a dozen `Theorems/` wrappers' `attribute [-simp]` preludes — so omitting either would
leave the gate incomplete in the §4(a) sense. That is why the order carries five gates (359 lines), not
four.

**`Def_ModularCurve_EigenformIdeal` (24 lines) is deferred, not owed by this order.** Its three
declarations are *defined in terms of* `eigenIdeal`, `EigenformSupport` and `EichlerShimuraDataReduced`
from `Definitions/Def_HeckeGalois_EichlerShimura.lean`, which the port records as blocked
(`ModularForms/HeckeFiniteAlgebra.lean`, "Still blocked"; `CARRY-FORWARD.md`). `omegaRow_T2` and its six
premises reference none of the three (`rg -c` → 0), so the pair lands without the gate; the deferral and
its trigger are in `CARRY-FORWARD.md`. The manager may **delegate a gate to
the group that needs it** (a leaf module with no dependents is not a hub edit); the group then homes it
whole and reports it. The four gates are the only new definition modules this order creates. The other eight gate imports the
pair nodes carry are **already homed** and are imported, never re-proved: `Def_EisensteinSeries_EisensteinG`
(`ModularForms/EisensteinSeries.lean`), `Def_NumberField_AdelicLevel` (`NumberTheory/AdelicLevel/Level.lean`),
`Def_CohCarrier_Level` (`ModularForms/Defs/CohCarrierLower.lean`), `Def_FLTPrelim_Modularity`
(`WeierstrassCurve/Defs/Modularity.lean`), `Def_ModularCurve_HeckeModule`/`JqCoeff`/`X0`,
`Def_CuspForm_IntegralStructure`.

## 4. Route and recorded negatives

* **Transcribe, do not restate.** Each node's statement is its `Theorems/` wrapper's text, verbatim;
  the `S_` file's proof body is transcribed; the pin's `solution` wrapper is not ported; `p2m_*` lines are
  dropped; `scoped`/`open scoped` are kept where the pin has them.
* **Namespace:** drop only the pin's `P2MW.S_<stem>` prefix, keep the pin's inner namespaces verbatim
  (statements reference siblings by short name, so a rename breaks the statement hash).
* **Imports targeted**, never bare `import Mathlib`; the pin's `import Mathlib` (where present) becomes
  the modules the proof names.
* **0 substitutions expected** — every one of these 31 nodes is new to the port (`port_advise` reports
  none for the family; if your group's run reports one, read it, it is probably a type-only `def` match).
* **Mathlib-first, as always.** Before transcribing any lemma that looks like mathlib's own, run the
  check of [TOPIC-mathlib-supplements.md](../TOPIC-mathlib-supplements.md) §1 (name `rg`, concept `rg`,
  and the statement's own words) and record the negative in the module header. A hit means *import*, not
  transliterate; a "more general mathlib lemma" is the trap that matters (the pin's `antipode_antipode`
  and `isInvInvariant_of_isMulRightInvariant` are both re-proofs of broader mathlib statements).
* **No promotions**, no `decl_markers.tsv` entries, no `-- pin:`/`-- own:` markers: every module is listed
  and every public declaration is the pin's.
* **Drift:** these files were not scouted. Fix `v4.34.0` drift minimally and record every site (the MG2
  record, [logs/matrix-family-four.md](../../logs/matrix-family-four.md), is the model: `convert`
  between `Membership.mem` props, `haveI` → `have`, `omit … in`, a deprecated import path).
* `omegaRow_T2` is a *single* pin `S_` file (447 lines) whose own name is the node; its statement is the
  wrapper's, and its 6 premises are the `ModularForm`/`ModularCurve` leaves in §1.

## 5. Phase 2 — the free-standing small families (dispatched after phase 1's review)

The 34 ready one-to-three-node families left after the nine pairs and the free-group premises:
`PeriodPair` (1,111), `MulAction` (848), `jacobiTheta_two_eq_tprod` (702), `LocalNewvector` (647),
`Function` (626), `LSeries` (414), `BrauerNesbitt` (414), `LinearEquiv` (398), `HexagonalLattice` (394),
`AddAut` (370), `RatIdele` (312), `RatAdele` (309), `Complex` (272), `IntermediateField` (258),
`LocalGL2` (241), `VectorFourier` (235), `ZSpan` (223), `integralClosure` (221), `IsLocalRing` (204),
`IsLocallyConstant` (157), `WittVector` (152), the `tsupport` bound (145), `CuspFormClass` (98),
`Submodule` (83), `LaurentSeries` (77), `LinearMap` (77), `ContinuousMap` (68), `HeckeEis` (59),
`RingHom` (58), `ValuationRing` (52), `AddChar` (45), `integrableOn_Ioi…` (42), `ClassGroup` (18),
`IsAddCyclic` (14) — **46 nodes / 9,344 raw lines / ~596 wired**. One module per family; the 11 entries
under 80 lines (546 lines, 20 declarations) are single declarations and may ride with the neighbouring
family of the same area rather than each being a module of its own.

Phase 2 is a **separate dispatch** after phase 1 is reviewed; this order fixes its scope and price, not
its schedule.

## 6. Build discipline (verbatim)

```
tier 0  edit loop    timeout 120 lake env lean -DautoImplicit=false -DmaxHeartbeats=200000 <file>
tier 1  module done  flock .lake/flt_build.lock timeout 300 lake build <module>
tier 2  wave         none — no existing module is edited
tier 3  milestone    no whole-tree build without the user's permission
```

Report each edit loop's wall time and each `lake build`'s jobs/seconds; 0 warnings required. A module
over ~60 s elaboration is worth reporting, over ~120 s is a defect to report, not to work around. Never
raise `maxHeartbeats` and never add a `set_option maxHeartbeats`, module-wide or per-declaration.

**If a declaration exceeds the 200,000 edit-loop budget**, run the diagnosis first
(`-DmaxHeartbeats=200000`, then bisect). Two outcomes, and they are treated differently:

* **cost is instance synthesis** — that is the defect the cap exists to find: diagnose it, fix the
  inference, never raise the cap;
* **cost is measured arithmetic defeq** (`Add.add`/`Nat.rec` unfolding, no instance search) — the
  diagnostic has done its job. The library builds at the lakefile's `maxHeartbeats 4000000`, so the
  module is green at tier 1; **accept it, add no `set_option`, and record the pin's own bump, the
  bisection and the diagnosis in the module header** (the `EisensteinSeries.sum_eisensteinG_…` row is
  the first instance: pin 4,000,000, port needs 300k–400k, `lake build` 31 s). Report it as a measured
  deviation from the edit-loop budget, not as drift.

Stop and report only if a proof fails to **close** at any budget — that is the `HeckeCosetSeam.of_dvd`
case, and deferral is reserved for it.

## 7. Verification

```bash
cd lean
python3 spec/check_port.py --force FLTForHuman/<module>.lean    # per module, every public decl
python3 spec/check_port.py --all                                # expect 2111 + your wired delta
flock .lake/flt_build.lock timeout 300 lake build <each module>
```

plus `#print axioms` on every headline and, where a module has several, on each; an `rg` sweep for
`sorry`/`admit`/top-level `axiom`/`native_decide`/bare `import Mathlib`/heartbeat override; 0 warnings.

## 8. Report shape

Per module: path, lines, public/private counts, checker verdict, build numbers, axioms. Then: your
group's total vs the priced lines, every drift site with module:line, the gate consumption (which gate
declarations your proof actually used), and anything unexpected. Stop-and-report items separately.

## 9. Hub prohibition and stop conditions

No subagent edits an existing module, appends to `spec/old_check_stmts.py`, touches
`spec/decl_markers.tsv`, or promotes anything. If a gate module's declaration is missing from the port,
if a pin statement cannot be reproduced verbatim (a `MISMATCH` not fixable by the pin's binder spelling),
or if a proof exceeds the 200,000 heartbeat cap — **stop and report** with the declaration, the host and
the `build_ladder.py --edit` price. The manager decides.

## 10. Phase 2 dispatch — groups D, E, F

Phase 2 is the 34 free-standing one-to-three-node families plus the one standalone `Subgroup` leaf:
**48 nodes / 9,552 raw lines**, ~596 wired, ~9,000 net new. Three groups, disjoint file sets, each
≤ ~3,600 pin lines; the phase-1 rules (§4, §6, §9) apply unchanged — in particular **quick isolation
only**: no re-elaboration of a whole file to bisect, use `import`/`sorry`-stubbed preludes and ≤60 s
probes, one long profiled run per module at most.

**Group D — 9 nodes / 3,063 lines**
| family | nodes (lines) |
|---|---|
| `PeriodPair` | `exists_gamma1_two_eq_weierstrassP_and_slash_and_qExpansion_coeff` 319, `lattice_eq_of_g2_eq_of_g3_eq` 234, `weierstrassP_torsion_modularForm_slash_tendsto_atImInfty` 558 |
| `MulAction` | `card_mul_natCard_orbitRel_quotient_eq_of_natCard_eq_prime` 51, `natCard_fixedBy_of_isPretransitive_of_card_eq_twelve` 797 |
| `jacobiTheta_two_eq_tprod` | the headline, 702 |
| `AddAut` | `exists_mem_apply_eq_of_addOrderOf_eq_of_transvection_mem` 370 |
| `ClassGroup` | `exists_finset_forall_exists_mk0_eq_of_dvd` 18 |
| `IsAddCyclic` | `of_squarefree_natCard` 14 |

**Group E — 10 nodes / 2,893 lines**
| family | nodes (lines) |
|---|---|
| `LocalNewvector` | `AdelicSpan.exists_hasNewvectorConductor_le_factorization` 58, `AdelicSpan.exists_mem_span_fixed_padicK1_of_fixedSubmodule_padicK1_ne_bot_of_apply_mul_finEmbed_eq` 589 |
| `Function` | `exists_eq_sum_mul_prod_apply_update_of_forall_exists_forall_apply_update_eq_sum_mul` 220, `mul_pow_card_sub_one_eq_mul_prod_update_of_forall_exists_linearCombination_update_eq_zero` 91, `orbitCensus_of_dihedralThree_relations` 315 |
| `LSeries` | `abscissaOfAbsConv_le_of_forall_analyticAt_ofReal_of_exp_lseries_eq` 218, `exists_nonneg_hasSum_tsum_mul_cpow_eq_lseries_of_le_mul_pow` 196 |
| `BrauerNesbitt` | `exists_linearEquiv_of_span_range_eq_top_of_trace_eq` 414 |
| `LinearEquiv` | `exists_forall_finrank_inf_map_pow_add_finrank_inf_le` 398 |
| `HexagonalLattice` | `summable_thetaTerm_and_tsum_neg_inv_three_mul` 394 |

**Group F — 29 nodes / 3,596 lines** (mostly one declaration each; the `≤ 80`-line entries may ride
together where they share an area — report the grouping)
| family | nodes (lines) |
|---|---|
| `RatAdele`/`RatIdele` | `denseRange_algebraMap_add_adeleSingleAt` 309, `exists_norm_apply_eq_ideleNorm_rpow` 312 |
| `Complex` | `exists_norm_le_of_continuousOn_of_exp_eq_of_tendsto` 161, `exists_ringHom_integralClosure_int_apply_eq_of_isPrimitiveRoot` 111 |
| `IntermediateField` | `exists_algHom_adjoin_apply_eq_of_isAlgebraic_of_transcendental` 258 |
| `LocalGL2` | `iwasawa_decomposition` 241 |
| `VectorFourier` | `fourierIntegral_flip_fourierIntegral_eq` 235 |
| `ZSpan` | `norm_setIntegral_fundamentalDomain_cexp_mul_le_inv_pow_mul_setIntegral_norm_of_hasDerivAt` 223 |
| `integralClosure` | `finite_and_isDiscreteValuationRing_and_isAdicComplete_maximalIdeal` 221 |
| `Subgroup` | `exists_exact_fundamental_domain_of_secondCountableTopology` 208 |
| `IsLocalRing` | `exists_dvd_pow_of_krullDimLE_one` 33, `exists_sub_algebraMap_mem_map_maximalIdeal_of_mul_self_sub_mem_of_smul_eq_add` 171 |
| `IsLocallyConstant` | `exists_nhds_one_forall_apply_mul_mul_eq_of_hasCompactSupport` 95, `isLocallyConstant_fun_mul_apply_mul_of_hasCompactSupport` 62 |
| `WittVector` | `exists_valuationSubring_lift_with_transcendental` 152 |
| `tsupport` | `exists_isCompact_tsupport_subset_and_norm_pow_mul_norm_iteratedFDeriv_comp_le_of_hasCompactSupport` 145 |
| `CuspFormClass` | `isZeroAt_slash_of_mem_Gamma0` 42, `isZeroAt_slash_slash_heckeDiagMatrix_of_mem_Gamma0` 56 |
| `Submodule` | `finiteDimensional_of_isCompactOperator_of_forall_apply_eq` 38, `finite_torsionBy_pow_of_finite_torsionBy` 45 |
| `LaurentSeries` | `eq_C_coeff_zero_of_isAlgebraic` 77 |
| `LinearMap` | `exists_forall_eq_zero_of_tendsto_apply_of_finiteDimensional` 77 |
| `ContinuousMap` | `ae_eq_zero_of_forall_mem_starSubalgebra_integral_mul_eq_zero` 68 |
| `HeckeEis` | `coresHom_eq_transfer` 59 |
| `RingHom` | `finiteDimensional_adjoin_range_of_finite_of_forall_mem_range` 58 |
| `ValuationRing` | `exists_ne_zero_forall_smul_eq_zero_of_module_finite` 52 |
| `AddChar` | `exists_continuousLinearMap_fourierChar_eq` 45 |
| `integrableOn_Ioi…` | the one-liner, 42 |

**Out of phase 2:** `M4aTorus.completedRayL_fe` (12,126 lines — its own topic), the `SchwartzMap` 563-line
node and the `ZLattice` pair (deferred, `lean/tmp/zlattice/`), `ModularGroup.exists_mulEquiv_freeProduct_quotient_center`
and `SimpleGraph.exists_walkConnected_transversal_of_preconnected` and `Subgroup.card_orbitRelQuotient_mul_card_eq_index`
(the free-group family, which belongs with the four `Matrix.SpecialLinearGroup` rows).
