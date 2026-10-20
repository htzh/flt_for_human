# Phase 3 — the genuinely small mathlib-shaped families (recorded, **not scheduled**)

**Status: recorded 2026-10-20, not dispatched.** The column stopped cutting this front after WORKORDER-MG3's
phase 2 ([logs/ds-leaf-families-wave2.md](../logs/ds-leaf-families-wave2.md)), and this note is
the re-scoped cut that phase 2 failed to be: the survivors of the four tests written in
[TOPIC-ds-leaf-families.md](TOPIC-ds-leaf-families.md) §8. It exists so the next session starts
from a cut that meets the criterion instead of rediscovering it.

## 0. Where the "about 1,000 lines" tail went (it is done)

The §8 note's survivor list — `ClassGroup` 18, `IsAddCyclic` 14, `Subalgebra` 36, `integrableOn_Ioi…` 42,
`AddChar` 45, `ValuationRing` 52, `Polynomial` 53, `RingHom` 58, `ContinuousMap` 68, `LinearMap` /
`LaurentSeries` 77, `Submodule` 83, `AbsoluteValue` 91, `Int` / `IsLocallyConstant` 95, `ZMod` 101 — was a
snapshot taken while phase 2 was in flight, and **all of it has since landed**, mostly by the groups that
were already dispatched:

| node (pin lines) | landed in |
|---|---|
| `ClassGroup.exists_finset_forall_exists_mk0_eq_of_dvd` (18) | phase 2 D — `RingTheory/DedekindDomain/ClassGroupSupport.lean` |
| `IsAddCyclic.of_squarefree_natCard` (14) | phase 2 D — `Algebra/IsAddCyclicSquarefree.lean` |
| `Subalgebra.isIntegrallyClosed_adjoin_singleton_of_transcendental` (36) | phase 1 A — `FieldTheory/TranscendentalAdjoin.lean` |
| `integrableOn_Ioi_min_one_rpow…` (42) | phase 2 F — `Analysis/DecayEstimates.lean` |
| `AddChar.exists_continuousLinearMap_fourierChar_eq` (45) | phase 2 F — `Analysis/FourierIntegralFlip.lean` |
| `ValuationRing.exists_ne_zero_forall_smul_eq_zero_of_module_finite` (52) | phase 2 F — `Algebra/TorsionFinite.lean` |
| `Polynomial.natDegree_le_of_aeval_mul_inv_pow_mem_adjoin_inv` (53) | phase 1 A — `FieldTheory/TranscendentalAdjoin.lean` |
| `RingHom.finiteDimensional_adjoin_range_of_finite_of_forall_mem_range` (58) | phase 2 F — `FieldTheory/AdjoinExtension.lean` |
| `ContinuousMap.ae_eq_zero_of_forall_mem_starSubalgebra_integral_mul_eq_zero` (68) | phase 2 F — `Analysis/StarSubalgebraIntegral.lean` |
| `LinearMap.exists_forall_eq_zero_of_tendsto_apply_of_finiteDimensional` (77) | phase 2 F — `Analysis/CompactOperatorFiniteDimensional.lean` |
| `LaurentSeries.eq_C_coeff_zero_of_isAlgebraic` (77) | phase 2 F — `Algebra/LaurentSeriesAlgebraic.lean` |
| `Submodule.finite_torsionBy_pow…` / `finiteDimensional_of_isCompactOperator…` (38 + 45) | phase 2 F — `Algebra/TorsionFinite.lean`, `Analysis/CompactOperatorFiniteDimensional.lean` |
| `AbsoluteValue.exists_forall_sub_lt_of_pairwise_not_isEquiv` (91) | phase 1 C — `HeckeCharacter/Equality.lean` |
| `Int.exists_modEq_and_modEq_and_isCoprime` (95) | phase 1 A — `NumberTheory/UnimodularLift.lean` |
| `IsLocallyConstant` pair (95 + 62) | phase 2 F |
| `ZMod.tsum_intCast_pow_inv_eq_sum_bernoulliFun` (101) | phase 1 B — `NumberTheory/ZModPowerTsum.lean` |

All sixteen entries are gone from the demand (`frontier.py --ds --include-leaves --list` of 2026-10-20 →
zero hits). So the cut below is **not** a re-run of that tail: it is the next layer the same four tests
admit once the tail is in. The sentence in the survey — "that is the only part of this pool I'd cut
again" — is now *done*; what follows is what replaces it.

## 1. The cut

Computed on the D-S demand of 2026-10-20 after the phase-2 landings (`frontier.py --ds --include-leaves
--list`, then per node: pin line count, imports, and `frontier.needed`):

**37 nodes / 3,641 pin `S_` lines / 283 public declarations / 7 families — every node `needed 1` (all
premises ported), every pin file importing mathlib plus `P2M.Util` only (no `Definitions/`, no gate), and
every subject read and accepted as mathlib-shaped.** At the wave's measured 0.92 ratio that is ≈ **3,350 net
new lines** and **≈320 wired declarations** (283 publics + 37 wrapper headlines), i.e. the checker goes
2,79x → ≈ 3,1xx.

| family | nodes | pin lines | publics | module shape |
|---|---:|---:|---:|---|
| `MeasureTheory` (integration, `IsFundamentalDomain`, `Lp`) | 13 | 1,336 | 33 | 2–3 modules |
| `ValuationSubring` (residue/degree/Krull-dim criteria) | 7 | 738 | 19 | 1–2 modules |
| `Representation` (compact-group representations) — **landed 2026-10-20** as five mathlib-shaped modules (`RepresentationTheory/{Burnside,InvariantPairing,CompactGroup,SubrepresentationExtension}.lean`, `LinearAlgebra/Matrix/SubfieldBasis.lean`): 21 wired, 0 mismatch/0 missing, record [logs/representation-leaves.md](../../logs/representation-leaves.md) | 4 (+1 over-threshold basis node) | 659 | 21 | 5 modules |
| `Algebra` (norms, integral closure of a simple adjoin) | 5 | 349 | 13 | 1 module |
| `ContinuousLinearMap` (integral-representation of operators) | 3 | 328 | 20 | 1 module |
| `PowerSeries` (coefficient/subring criteria) | 3 | 265 | 11 | 1 module |
| `Module.End` (eigenspace/divisor-string lemmas) | 2 | 257 | 5 | 1 module |
| **total** | **37** | **3,641** | **283** | **~8–10 modules** |

## 2. The nodes

`MeasureTheory` — `Measure.exists_eq_smul_map_smul_of_forall_map_smul_eq_of_isCompact_stabilizer` 222,
`Lp.finiteDimensional_and_finrank_le_of_forall_ae_norm_le_mul_norm` 148,
`exists_finset_forall_exists_eLpNorm_sub_lt_of_equicontinuous_of_forall_ae_norm_le` 139,
`integral_normSq_det_div_mul_comp_moebius_complex` 104,
`IsFundamentalDomain.setLIntegral_iUnion_inv_smul_eq_and_setIntegral_eq_of_leftCosetRepresentatives` 99,
`differentiableOn_integral_of_forall_differentiableOn_of_locally_norm_le` 99,
`lintegral_enorm_sub_integral_mul_sq_le_lintegral_mul_lintegral_enorm_sub_sq` 98,
`integral_abs_det_div_sq_mul_comp_moebius_real` 95,
`exists_integral_eq_inv_card_mul_sum_of_isOpen_subgroup` 90,
`lintegral_mul_comp_eq_tsum_zpow_mul_setLIntegral_of_measure_image_eq_mul` 84,
`IsFundamentalDomain.iUnion_inv_smul_of_leftCosetRepresentatives` 77,
`tendsto_lintegral_nhds_zero_of_le_of_limsup_lintegral_le` 63,
`measure_biUnion_finset_image_mul_right_lt_top` 18.

`ValuationSubring` — `natDegree_map_eq_card_roots_of_splits` 174, `exists_le_forall_mem_iff_apply_mem` 168,
`mem_of_forall_mem_iff_of_subset` 126, `exists_mul_pow_inv_mem_of_finiteDimensional_adjoin` 112,
`tensorProduct_exists_primitive_factor` 78,
`exists_map_subtype_eq_C_inv_mul_and_map_residue_ne_zero` 57, `exists_root_mem_of_monic` 23.

`Representation` — `span_range_eq_top_of_isIrreducible` 151,
`exists_isCompl_forall_mem_of_compactSpace_of_continuous` 112,
`exists_extend_forall_apply_mul_of_injective` 69,
`pairing_eq_zero_of_invariant_of_isSimpleOrder_of_exists_ne_zero` 36.

`Algebra` — `finite_integralClosure_adjoin_singleton_of_isAlgClosed` 236,
`exists_adjoin_ne_zero_mul_forall_valuationSubring_mem` 79,
`norm_eq_pow_finrank_of_isNilpotent_sub_algebraMap` 18, `norm_prod` 10, `norm_of_subsingleton` 6.

`ContinuousLinearMap` — `comp_eq_of_forall_apply_eq_integral_smul_apply_of_convolution` 180,
`exists_forall_apply_eq_integral_smul_apply_of_forall_norm_le_of_continuous` 108,
`map_eigenspace_orthogonal_le_of_commute` 40.

`PowerSeries` — `exists_map_eq_sum_smul_map_of_forall_map_algEquiv_mem` 186,
`coeff_mem_subring_of_coeff_mul_mem` 41, `exists_sum_smul_eq_of_forall_coeff_mem` 38.

`Module.End` — `mem_span_prod_apply_and_finrank_iInf_eigenspace_le_one_of_divisorString` 181,
`exists_mem_adjoin_apply_eq_self_and_apply_eq_zero_of_forall_ne_exists_ne` 76.

## 3. What is excluded, and why (so it is not re-litigated)

| excluded | why |
|---|---|
| `Matrix.SpecialLinearGroup.{exists_addMonoidHom_conj_T_pow_minimalPeriod…, nonempty_freeGroupBasis_map_quotient_center…, exists_generators_free_mod_neg_one…, finrank_addMonoidHom_eq…}` (686 lines, 4 nodes) | small and clean, but **not ready**: they need the free-group family (`Monoid.CoprodI` + `ModularGroup.exists_mulEquiv_freeProduct_quotient_center` + `SimpleGraph` + `Subgroup.card_orbitRel…`, 3,275 raw lines). Priced at 3,291 net / 2 modules in the leaf-families note §3. |
| `UpperHalfPlane.qExpansion_*`, `CongruenceSubgroup.*` (~500 lines) | modular forms — FLT-flavoured subject, test 2. |
| `AlgebraicCurve.FunctionField.*` (187) | curve-theory vocabulary (`ratFuncAlgHom`, `placeInfty`) — FLT's own function-field layer, not mathlib's. |
| `LocalGL2.iwasawa_decomposition` (241), `UnramifiedWhittaker.*` (412), `HaarQuotient.*` (446) | adelic/Whittaker vocabulary — FLT-flavoured despite clean imports. |
| the other seven `ValuationSubring.*` (`exists_aeval_div_eq_aeval_div_add_inv_pow_mul_add_aeval_inv` 138, `IsFrobeniusAt.apply_eq_pow_of_pow_eq_one` 83, `ringKrullDim_le_toENat_trdeg_rat_add_one` 75, `exists_polynomial_map_residue_ne_zero_eval_mul_mem` 42, `charP_residueField_of_liesOverPrime` 37, `isAlgClosed_residueField` 30, `krullDimLE_one_of_isAlgebraic_rat` 12) | **not `needed 1`** — they want the bigger `ValuationSubring` nodes as premises. A "phase 3b" once those land, or a single order that takes the whole 1,155-line family. |
| `jacobiTheta`, `PeriodPair`, `RatAdele`/`RatIdele`, `LocalNewvector`, `HeckeEis`, `AddAut`-class material | already landed in phase 2 (or deferred with a recorded gate); see the wave records. |

## 4. If it is ever dispatched

Three groups of ≤ ~1,350 pin lines each, disjoint: (i) `MeasureTheory` 1,336; (ii) `ValuationSubring`+`Algebra`
1,087; (iii) `Representation`+`ContinuousLinearMap`+`PowerSeries`+`Module.End` 1,218. The rules are the
wave's own: transcription with the wrapper's statement, targeted imports, no `set_option maxHeartbeats`, the
mathlib-first check with a recorded negative, fix linters at the source or narrow to one declaration and
report, quick isolation only (no long bisection runs), 0 warnings, `--force` + tier-1 + axioms per module.

One honest caveat: the readiness and subject judgements above are the manager's, computed on **one** tree
on 2026-10-20. Recompute (`frontier.py --ds --include-leaves --list` + `needed` per node) before cutting,
because phase 2's other landings move the demand, and read each `Theorems/` statement before believing the
namespace-based subject filter — that is precisely the mistake this note exists to prevent.
