# SET-M2 route recon (manager, 2026-09-23)

Untracked working notes for the next set's work orders. Read the pin at
`~/proj/fermats-last-theorem@aa2d8b3`; do not treat this as the order.

## m4 — Fricke invariance and the field inclusion (M8, 8 nodes)

**The finding.** The three files share the block at lines 50–861 / 50–861 /
53–863 (content 651 each); f1 and f2 differ by 12 lines (all `p2m_*` + the final
`solution`); f3's prelude differs from f1's by 2 lines. Content measurement:

```
f1 whole 656, prelude(50-861) 651, tail 2
f3 whole 913, prelude(53-864) 651, fricke_transport(983-1138) 137, tail 17
```

So: write the prelude **once** in `Analytic/Gamma0InvariantCore.lean` (namespace
`ModularCurve.QExpN` to match the pin's dotted names), then one thin module for
the three headlines + `fricke_transport`.

**Already ported, import don't rewrite:** the `RealL` block (pin lines 262–417)
= `ModularForms/Hauptmodul.lean:230–` `RealL` + `add/neg/sub/mul/single/C/one/
zero/congr/prod/coeff_prod_X_sub_C`. **Missing from the port** (write in the
core): `RealL.sum`, `RealL.interpPoly_coeff`, `RealL.conjPoly_coeff` (pin
299–380), plus the non-`RealL` prelude (`interpPoly`, `conjPoly`, `slotH`,
`liftPerm`, `coeffMap_{qTwist,conj}`, `zeta_*`, `qTwist_slotH`, `qTwist_conj`,
`interpK`, `conjK`, `exists_{interpK,conjK}_coeff_eq`, `realL_*`,
`realL_one_of_realL_qExpand`, `realL_qExpand_of_realL_one`, `expRoot`,
`isPrimitiveRoot_expRoot`, `expRoot_pow_zpow`, `qParam_T_pow_smul`, `realL_twist`,
`jt`, `jtN`, `castC`, `coeffMap_sigma_coeffEmb`, `cosetRep`, `slotF`, `slotJ`,
`realL_{fC,gC,slotH,jqC,conj}`, `interpFun`, `conjFun`, `jtN_smul`, `slots_smul`,
`{interpFun,conjFun}_smul`, `mem_adjoin_of_{interpK,conjK}_coeff_eq`, `iota` +
`iota_apply`/`coeffEmb_injective'`/`iota_injective`/`iota_eq_slotH_zero`/
`iota_jqN`, `dHat`, `dHat_ne_zero`, `exists_sum_eq_mul_dHat`,
`mem_modularFunctionField_of_data`, `isIntegral_of_data`, `sigma`, `sigma_zeta`,
`mem_modularFunctionField`, `isIntegral_adjoin_jq`).

The third file's distinctive block: `natDegree_interpPoly_lt`, `realL_jtN_S`,
`realL_sum_qExpand_mul_jq_pow`, `coeffMap_castC_injective`, `embW`(+`_apply`,
`_of_mem_adjoin`), `fricke_transport` (137) → goes in
`Analytic/FrickeInvariance.lean`.

**Public targets (verbatim):** `mem_modularFunctionField_of_hasSum_of_gamma0_invariant`
(656), `isIntegral_adjoin_jq_of_hasSum_of_gamma0_invariant` (656),
`coe_frickeInvolutionFull_eq_of_hasSum_of_gamma0_invariant` (913) — all with the
same binder block `(ℓ) [Fact (Nat.Prime ℓ)] (f g : LaurentSeries ℚ)
(F : UpperHalfPlane → ℂ) (hF …) (hG …) (hinv …)`; plus
`modularUnitSeries_mem_modularFunctionField(Full)`,
`isIntegral_adjoin_jq_modularUnitSeries(_inv)`,
`coe_frickeInvolutionFull_modularUnitSeries`.

**Risk.** `fricke_transport` is the one hard block; scout it after the core
builds. `RealL` name collision: the port's `RealL` is `ModularCurve.RealL`; the
pin's is `ModularCurve.QExpN.RealL` — the checker matches by last name, so either
namespace works, but the core module should `open ModularCurve` and reuse the
ported one.

## m6 — the Φ datum family (M5, 14 nodes)

**One-liners over the ported Φ_p effort (verify each, record):**
- `exists_modularPolynomialData_evalSymm` (31) = `exists_phiIrreducible_evalSymm`
  with `PhiIrreducible` dropped (port `ModularPolynomialProperties.lean:138`);
- `modularPolynomialFamily` (29) = the same, universally;
- `full_eq_of_prime` (3) from `functionFieldGeneration_of_prime` (8) +
  ported `functionFieldGeneration_iff_full_eq`; `functionFieldGeneration_of_prime`
  imports only `Def_ModularCurve_X0` → should be ported `gen_prime`;
- `ModularPolynomialData.isIntegral_jqN` (5) imports only `Def_ModularCurve_X0`
  → ported `aeval_jqN_toAdjoin`/`minpoly_jqN_eq`;
- `isIntegral_jqNModC_mul` (12) = private `isIntegral_of_eval₂_eq_zero` +
  `eval_jqNModC_mul_eq_zero`;
- `ModularPolynomialData.eval_jqNModC_{mul_eq_zero,of_mul_eq_zero}` (29+32) from
  ported `coeffMap_qExpand`/`coeffMap_injective` and a private
  `coeffMap_eval₂_jqNModC`;
- `isIntegral_jqNModC_all_of_modularPolynomialFamily` (47): induction on
  `ModularPolynomialFamily`, base `IsIntegral F₀ (jqModC K)`.

**Real proofs:** `nonempty_modularPolynomialData_of_squarefree` (363; the
biresultant: `squarefreeIndicator`, `fibrePoly`, `compositeFibrePoly`,
`resLift*`, `biResultant`, `coeff_biResultant_*`, `evalModularPair_*`) and
`finrank_adjoin_jqNModC_le` (65; private `phiAt`/`coeffMap_phiAt`/`phiAt_rat`/
`phiAt_eq_zero`/`phiOver`/`aeval_phiOver`), plus `transcendental_jqModC` (61;
`jqModC_pow`/coeff triangularity/`aeval_jqModC_eq_zero`) and
`finiteDimensional_adjoin_jqNModC` (65, from `finrank_adjoin_jqNModC_le` +
`transcendental_jqModC`).

**Prereq note.** m5's `eq_cuspInftyBar_or_eq_cuspZeroBar` and
`modularFunctionFieldBar_eq_restrictScalars` consume
`nonempty_modularPolynomialData_of_squarefree`, `finrank_adjoin_jqNModC_le` and
`transcendental_jqModC` → m6 runs before m5.

## m5 — cusp dichotomy, Fricke automorphisms, cusp bookkeeping (M9, 17 nodes)

**Short (assembly):** `ord_qInftyPlaceBar` (33 raw, from the `qInftyPlaceBar`
definition), `ord_cuspInftyBar` (3), `ord_cusp{Infty,Zero}Bar_coeffEmb_{jq,qExpand}`,
`cuspZeroBar_ne_cuspInftyBar`, `isCusp_iff_ord_neg`, `isCusp_cusp{Infty,Zero}Bar`,
`frickeInvolutionBar_coeffEmb_qExpand`, `exists_isFrickeAut` (5) and
`exists_isFrickeAutFull` (33) from `exists_phiIrreducible_evalSymm` +
`exists_isFrickeAut_of_modularPolynomialData`, and
`isFrickeAutFull_frickeInvolutionFull_prime` (5).

**Real proofs:** `exists_isFrickeAut_of_modularPolynomialData` (197; `AdjoinRoot`/
`IntermediateField`: `algHom_ext_of_eq_on_gens`, `exists_isFrickeAut_of_endo`,
`minpoly_jqN_eq`, `frickeBaseHom`/`frickeRelativeHom`/`frickeAbsoluteHom`/
`frickeEndoAlgHom`, `mem_of_apply_gens_mem`, `frickeAbsoluteHom_mem`);
`eq_cuspInftyBar_or_eq_cuspZeroBar` (163; the `RatFunc 𝕂 →+* modularFunctionFieldBar ℓ`
model, `Module.finite`/`finrank_le`/`IsSeparable`, then a place count);
`modularFunctionFieldBar_eq_restrictScalars` (169; the `ubar`/`fricke_ubar`/
`ord_inf`/`isPrincipal_smul_cuspidalDivisor`/`addOrderOf_cuspidalClass_dvd` block
plus the M8 heads).

## Set plan

SET-M2 = m4, m6, m5 (in that order). SET-M3 = m7, m8, m9.
SET-M4 = m10, m11, m12. Capstone = human.
