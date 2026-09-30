#!/usr/bin/env python3
"""Diff every Layer 0 port declaration's *statement* against the pinned FLT source.

The name/statement check was first run by hand on Layer 0a, and automating it was
a stated follow-up. This does that: for each declaration in the port, it
finds the declaration of the same name in the pinned FLT clone and compares the
statement (signature up to the first top-level `:=` / `where`; for a `structure`,
the header plus the ordered field names). Proof bodies are deliberately ignored —
the port adapts proofs, never statements.

Matching is by the last name component, so the port's namespacing need not match
the pin's. That is ambiguous for the few declarations the port *promotes* out of
FLT's `private` shared prelude (e.g. `TPoleOrderLE.neg`, whose last component
`neg` also names an unrelated top-level lemma): when the last-name lookup does not
reproduce the port's statement, the checker retries against the pin's `private`
declarations under the port declaration's dotted name (`TPoleOrderLE.neg`), which
is what the port writes. Those are reported as "promoted from pin-private
declarations".

Since SET-3 T5 the fallback additionally registers each pin declaration under its
**enclosing-namespace-qualified** name, so a last name that occurs twice in the
pin under two namespaces (e.g. `ModularForm.heckeTLin` and `CuspForm.heckeTLin`)
also resolves; the bare last-name key is still registered, so earlier matches are
unchanged.

Usage:

    python3 spec/check_flt_statements.py [--flt ~/proj/fermats-last-theorem]

Exit status is 0 when every statement matches, 1 otherwise.
"""
from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
LEAN = HERE.parent  # lean/

# Port module -> the pinned FLT files its declarations are transcribed from.
# A declaration is looked up by name across all of these.
SOURCES = [
    "Definitions/Def_ModularCurve_X0.lean",
    "Definitions/Def_ModularCurve_LaurentCoeff.lean",
    "Definitions/Def_ModularCurve_PhiGen.lean",
    # The cone's outbound interface. These nine live in `Defs/Laurent.lean` and
    # `Defs/Jq.lean` with the objects they concern; their pin statements are the
    # `Theorems/` wrappers, so they are *verified* rather than exempted. The
    # wrappers come before the solution file because `coeffEmb_qExpand` also
    # occurs there in the `W1` implicit-`K` form; the public wrapper (explicit
    # `L`, matching our `coeffEmb`) is the interface we match.
    "Theorems/Thm_ModularCurve_coeffMap_qExpand.lean",
    "Theorems/Thm_ModularCurve_coeffEmb_qExpand.lean",
    "Theorems/Thm_ModularCurve_coeffMap_injective.lean",
    "Theorems/Thm_ModularCurve_coeffEmb_injective.lean",
    "Theorems/Thm_ModularCurve_dedekindPsi_prime.lean",
    "Theorems/Thm_ModularCurve_dedekindPsi_prime_pow.lean",
    "Theorems/Thm_ModularCurve_dedekindPsi_mul_of_coprime.lean",
    # Two out-of-cone ψ facts FLT publishes but the port did not carry until the
    # 2026-09-22 audit sweep (`Defs/Jq.lean`); both are `Them_` wrappers, so they
    # verify by direct name match.
    "Theorems/Thm_ModularCurve_dedekindPsi_mul_prime.lean",
    "Theorems/Thm_ModularCurve_dedekindPsi_pos.lean",
    "Theorems/Thm_ModularCurve_aeval_jq_eq_zero.lean",
    "Theorems/Thm_ModularCurve_transcendental_jq.lean",
    "P2M/Sol/S_ModularCurve_functionFieldGeneration.lean",
    "Theorems/Thm_ModularCurve_functionFieldGeneration_iff_full_eq.lean",
    # The generic kernel of `FLTForHuman/FieldTheory/CommonRoot.lean`. The three
    # `Polynomial.*` lemmas are stated verbatim from their `Theorems/` wrappers;
    # the pin's `S_Polynomial_mem_range_of_unique_common_root.lean` carries them
    # as `private` declarations, which the checker skips, so the wrappers are the
    # only comparable copy.
    "Theorems/Thm_Polynomial_mem_range_of_unique_common_root.lean",
    "Theorems/Thm_Polynomial_mem_range_of_eval_eq_const.lean",
    "Theorems/Thm_Polynomial_irreducible_of_transitive_ringAut.lean",
    # The peel: `ModularCurve.relfinrank_modularFunctionField`, now a public
    # lemma in `Defs/Fields.lean` beside the fields it concerns.
    "Theorems/Thm_ModularCurve_relfinrank_modularFunctionField.lean",
    # R1's constancy kernel, `FLTForHuman/ModularForms/QExpansionPrinciple.lean`.
    # Its statement is the pin wrapper verbatim; the pin's proof is the `S_` file
    # of the same name (namespace `ModularCurve.Realized`), whose 14 helpers are
    # private and either replaced by public mathlib lemmas or re-derived privately
    # in the port (see the module header). The wrapper is the comparable copy.
    "Theorems/Thm_ModularCurve_coeff_eq_zero_of_hasSum_of_slash_invariant.lean",
    # Topic 6, `FLTForHuman/ModularForms/JqAnalyticModel.lean`: the analytic model
    # of `jq`. Both public statements are the pin wrappers verbatim; the pin's
    # intermediate `hasSum_jNum_qParam` is `private` in the port, so the checker
    # never sees it (the two wrappers are the comparable copies).
    "Theorems/Thm_ModularCurve_hasSum_jq_qParam.lean",
    "Theorems/Thm_ModularCurve_E4_cube_div_discriminant_smul.lean",
    # The η/`gfun` Taylor-series engine (`truncPoly`/`etaPow`/`gfun`/
    # `coeff_trunc_eq_coeff_etaPow`/`tendstoLocallyUniformlyOn_trunc`), promoted
    # public in `JqAnalyticModel.lean` so `LevelOneHauptmodul.lean` can drop its
    # private copies. The pin file carries them `private`; listing it lets the
    # promoted-from-pin-private lookup verify them instead of reporting missing.
    "P2M/Sol/S_ModularCurve_qExpansion_discriminant_eq_X_mul_tprod.lean",
    # The two outbound >=5-indegree exports promoted on 2026-09-22 (PORTING-FFG
    # §2.1): both were `private` even though their statements are the wrappers
    # verbatim. They live in T6's module, so they are listed with it.
    "Theorems/Thm_ModularCurve_qExpansion_discriminant_eq_map_X_mul_dedekindEtaUnit.lean",
    "Theorems/Thm_ModularCurve_qExpansion_E4_eq_map_eisenstein4.lean",
    # Topic 7, `FLTForHuman/ModularForms/Hauptmodul.lean`: the Hauptmodul form.
    # The headline and the two Cauchy-product lemmas are the pin wrappers verbatim.
    # `RealL` and its closure are *transcribed* rather than wrapper-declared (FLT
    # has no `Thm_` file for them), so the `S_` file's own public block is the
    # comparable copy. The `S_` file comes after the wrappers: it is the only
    # source for `RealL`/`add`/`neg`/... , and those generic names do not occur in
    # any earlier source.
    "Theorems/Thm_ModularCurve_hasSum_qParam_mul.lean",
    "Theorems/Thm_ModularCurve_hasSum_qParam_mul_laurent.lean",
    "Theorems/Thm_ModularCurve_mem_adjoin_jq_of_hasSum_of_slash_invariant.lean",
    "P2M/Sol/S_ModularCurve_mem_adjoin_jq_of_hasSum_of_slash_invariant.lean",
    # Topic 8, the Φ_p application. Four wrappers for the exported theorem and the
    # Hecke/coset interface, plus FLT's own Hecke-operator *definitions* file:
    # mathlib has no `heckeMatrix`, so `FLTForHuman/ModularForms/Defs/HeckeOperator.lean`
    # transcribes the subset the cone uses and is diffed against the pin's def file.
    "Theorems/Thm_ModularCurve_hasSum_qParam_heckeMatrix_smul.lean",
    "Theorems/Thm_ModularCurve_hasSum_qParam_heckeDiagMatrix_smul.lean",
    "Theorems/Thm_ModularCurve_cosetPoly_smul.lean",
    "Theorems/Thm_ModularCurve_PhiGen_mem_adjoin_jq_of_phiGenDescends.lean",
    "Definitions/Def_ModularForm_HeckeOperator.lean",
    # Topic 9, the integrality. Two shared triangularity lemmas were promoted out
    # of T7's `Hauptmodul.lean` into `Defs/Jq.lean` and `Defs/PhiGen.lean`:
    # `coeff_aeval_jq_neg` and `poleOrderLE_aeval_jq`. FLT keeps both `private` in
    # most of the nine `S_` files that repeat them; this one file has them public,
    # so it is the comparable copy. It is listed last because its other
    # declarations (`poleOrderLE_iff_le_order`, `exists_poleOrderLE`) are private
    # in the port and so never diffed.
    "P2M/Sol/S_ModularCurve_exists_aeval_jq_sub_holomorphicAtInfty.lean",
    # Topic 9, the integrality itself. The two public statements of
    # `FLTForHuman/ModularCurve/PhiGenIntegrality.lean` are the pin wrappers
    # verbatim; Route A's bridging helpers are `private` in the port and so are
    # invisible to the checker.
    "Theorems/Thm_ModularCurve_PhiGen_PhiGenDescends_intCoeffs.lean",
    "Theorems/Thm_ModularCurve_PhiGen_aeval_jq_intCoeffs_descent.lean",
    # Topic 10, the cone's (b) pole bounds and the shared `TPoleOrderLE` prelude.
    # The two public statements of `FLTForHuman/ModularCurve/PhiGenPoleBounds.lean`
    # are the pin wrappers verbatim. The shared prelude promoted into
    # `Defs/PhiGen.lean` is *public* in
    # `S_ModularCurve_PhiGen_aeval_jq_intCoeffs_descent.lean` (the closure, the
    # conjugate bounds and the polynomial-coefficient bounds) and in
    # `S_ModularCurve_PhiGen_PhiGenDescends_c_eq_zero.lean` (`jSimplePole_jqK`,
    # `tPoleOrderLE_coeffEmb_iff`, `tPoleOrderLE_of_qExpand`); the `phiProd_conj`
    # `S_` file is listed for the declarations that pin keeps `private` there
    # (`.mono`/`.neg`/`.mul`/`.qTwist`/`.qExpand`, `tPoleOrderLE_zero`,
    # `conjPoleBound*`, `sum_conjPoleBound`, `tPoleOrderLE_conj`), which the
    # checker's dotted fallback reads.
    "Theorems/Thm_ModularCurve_PhiGen_phiProd_conj_coeff_zero_lead.lean",
    "Theorems/Thm_ModularCurve_PhiGen_phiProd_conj_coeff_eq_zero_of_le.lean",
    "P2M/Sol/S_ModularCurve_PhiGen_aeval_jq_intCoeffs_descent.lean",
    "P2M/Sol/S_ModularCurve_PhiGen_PhiGenDescends_c_eq_zero.lean",
    "P2M/Sol/S_ModularCurve_PhiGen_phiProd_conj_coeff_eq_zero_of_le.lean",
    # Topic 11, the construction: (a)'s descent, the 328 block and the (d)
    # assembly. The eight public statements are the pin wrappers verbatim, so the
    # wrappers alone suffice for them; the three `S_` files listed last carry the
    # `private` originals the checker's dotted fallback reads for the promoted
    # helper lemmas (and would verify the block's `c_top` etc. if a later topic
    # promotes more of it).
    "Theorems/Thm_ModularCurve_PhiGen_PhiGenDescends_c_top.lean",
    "Theorems/Thm_ModularCurve_PhiGen_PhiGenDescends_c_eq_zero.lean",
    "Theorems/Thm_ModularCurve_PhiGen_PhiGenDescends_poleOrderLE.lean",
    "Theorems/Thm_ModularCurve_PhiGen_PhiGenDescends_sum_mul_jqN_pow_eq_zero.lean",
    "Theorems/Thm_ModularCurve_PhiGen_evalAtJ_injective.lean",
    "Theorems/Thm_ModularCurve_PhiGen_exists_phiGenDescends.lean",
    "Theorems/Thm_ModularCurve_PhiGen_exists_modularPolynomialData_coeff_eq.lean",
    "Theorems/Thm_ModularCurve_PhiGen_splits_of_coeff_evalAtJ_eq.lean",
    "P2M/Sol/S_ModularCurve_PhiGen_PhiGenDescends_c_top.lean",
    "P2M/Sol/S_ModularCurve_PhiGen_exists_phiGenDescends.lean",
    "P2M/Sol/S_ModularCurve_PhiGen_exists_modularPolynomialData_coeff_eq.lean",
    # Topic 12, the properties. Thirteen wrappers for the positivity, the 895
    # block's public surface and the two (e)-join statements; the `S_` files
    # supply the block's non-wrapper public declarations (`aeval_jq_ne_jqN`,
    # `jqN_not_mem_adjoin_jq`, `evalSymm_of_swapBivar_eq`,
    # `eval_swap_eq_zero_of_splits`, `aeval_jq_ne_jqN_of_isPrimitiveRoot`,
    # `swapBivar_monic_of_coeff_bounds`) and `coeff_jq_ne_zero`.
    "Theorems/Thm_ModularCurve_one_le_coeff_jq.lean",
    "Theorems/Thm_ModularCurve_PhiGen_phiIrreducible_of_splits.lean",
    "Theorems/Thm_ModularCurve_PhiGen_evalSymm_of_splits.lean",
    "Theorems/Thm_ModularCurve_ModularPolynomialData_transposeToAdjoin_monic_of_qExpansion.lean",
    "Theorems/Thm_ModularCurve_PhiGen_evalSymm_of_coeff_evalAtJ_eq.lean",
    "Theorems/Thm_ModularCurve_exists_phiIrreducible_evalSymm.lean",
    "Theorems/Thm_ModularCurve_evalAtJGen_injective.lean",
    "Theorems/Thm_ModularCurve_swapBivar_monic_of_coeff_bounds.lean",
    "Theorems/Thm_ModularCurve_ModularPolynomialData_evalSymm_of_irreducible.lean",
    "Theorems/Thm_ModularCurve_swapBivar_eq_of_evalSymm.lean",
    "Theorems/Thm_ModularCurve_PhiGen_conj_injective.lean",
    "Theorems/Thm_ModularCurve_aeval_jqN_toAdjoin.lean",
    "Theorems/Thm_ModularCurve_ModularPolynomialData_minpoly_jqN_eq.lean",
    "P2M/Sol/S_ModularCurve_PhiGen_evalSymm_of_splits.lean",
    "P2M/Sol/S_ModularCurve_one_le_coeff_jq.lean",
    # Topic 13, the consequence and the cone's last topic: uniqueness, the degree,
    # and the splitting. The four public statements are the pin wrappers verbatim:
    # `ModularPolynomialUniqueness.lean` and `PhiGenSplits.lean`. The pin's
    # `splits_of_prime`/`splits_prime_at_slot` prelude declarations are `private`
    # in the port, so no `S_` file is listed for them.
    "Theorems/Thm_ModularCurve_finrank_adjoin_jqN_eq_of_prime.lean",
    "Theorems/Thm_ModularCurve_ModularPolynomialData_eq_of_prime.lean",
    "Theorems/Thm_ModularCurve_PhiGen_splits_of_prime.lean",
    "Theorems/Thm_ModularCurve_PhiGen_splits_prime_at_slot.lean",
    # T13 also promoted the cyclotomic roots out of the FFG spine's private copies
    # into the public `Defs/Cyclotomic.lean`. They are public in the two pin
    # `splits_*` files (the `_of_isPrimitiveRoot` siblings repeat them), so those
    # `S_` files are the comparable copies.
    "P2M/Sol/S_ModularCurve_PhiGen_splits_of_prime.lean",
    "P2M/Sol/S_ModularCurve_PhiGen_splits_prime_at_slot.lean",
    # Topic 14, the shared slot prelude. Its declarations have no `Theorems/`
    # wrapper, so the pin's own `S_` files are the comparable copies. Most are
    # already *public* in `P2M/Sol/S_ModularCurve_functionFieldGeneration.lean`
    # (listed far above, and so still the first `source` hit); these two carry
    # the rest: the `_prime_not_mem_full` file has the `private`
    # `prod_form_ne_zero`/`jqN_congr`, and the `_pow_not_mem_adjoin_full` file
    # carries `aeval_intermediateField_eq_zero`, `phiAtSeed_eval_of_injective`,
    # `phiAtSeed_eval_symm`, `phiAtSeed_jqN_eval_down` and
    # `qExpand_qTwist_notMem_range_qExpand` *publicly*. Both are appended after
    # the `Theorems/`/`Defs` sources so no existing match can flip.
    "P2M/Sol/S_ModularCurve_jqN_prime_not_mem_full.lean",
    "P2M/Sol/S_ModularCurve_jqN_pow_not_mem_adjoin_full.lean",
    # Topic 15, descent by one prime and the one-prime reduction. Both nodes have
    # `Theorems/` wrappers, and the wrappers are public with matching last names,
    # so they verify by direct match; no `S_` carrier is needed. (The pin's own
    # copies are `private` in the two byte-identical `S_` files, which also carry
    # T14's prelude.)
    "Theorems/Thm_ModularCurve_jqN_div_mem_modularFunctionField.lean",
    "Theorems/Thm_ModularCurve_modularFunctionField_eq_full_of.lean",
    # Topic 16, the degree step. The three nodes are public wrappers, so they
    # verify by direct match. The three `S_` carriers are appended last for the
    # promoted bridges: the prime and pow-succ files carry `iota_injective`
    # (public) and `coeffMapEquiv`/`_apply` (public in pow-succ); the relfinrank
    # file carries the `private` `w1_relfinrank_insert`, which the checker's
    # dotted fallback reads. They are appended after every existing source so no
    # earlier match can flip.
    "Theorems/Thm_ModularCurve_finrank_adjoin_jqN_prime_of_not_mem.lean",
    "Theorems/Thm_ModularCurve_finrank_adjoin_jqN_pow_succ_of_not_mem.lean",
    "Theorems/Thm_ModularCurve_relfinrank_full_eq_mul.lean",
    "P2M/Sol/S_ModularCurve_finrank_adjoin_jqN_prime_of_not_mem.lean",
    "P2M/Sol/S_ModularCurve_finrank_adjoin_jqN_pow_succ_of_not_mem.lean",
    "P2M/Sol/S_ModularCurve_relfinrank_full_eq_mul.lean",
    # Topic 17, the non-membership tower and the two-prime separation. Both nodes
    # are public wrappers, so they verify by direct match. No `S_` carrier is
    # needed: the tower file is already listed above (T14) and the port's
    # `jqN_pow_not_mem_adjoin_full_key`/`step_contradiction`/
    # `jqN_prime_not_mem_adjoin_key` are `private`, so the checker never sees
    # them. The base file's own public block would otherwise supply the two
    # helpers, but neither is part of the port's public surface.
    "Theorems/Thm_ModularCurve_jqN_pow_not_mem_adjoin_full.lean",
    "Theorems/Thm_ModularCurve_jqN_prime_not_mem_adjoin.lean",
    # Topic 18, one new generator per prime power. The node is a public wrapper, so
    # it verifies by direct match. No `S_` carrier is needed: the pin's
    # `jqN_mem_of_div_primes`/`w1_jqN_mem_adjoin_top_insert` are `private` in
    # files that are not listed. `gen_prime` (the audit's T19 substitution) is our
    # own and is exempted in `OWN_PROOFS`; the promoted `tight_one`/`gen_one`
    # verify through the `S_ModularCurve_functionFieldGeneration.lean` dotted
    # fallback (that file is already listed above, under topic 2 / T14).
    "Theorems/Thm_ModularCurve_full_eq_adjoin_full_div_prime.lean",
    # Topic 19, the slot product and the prime non-membership. Both nodes are public
    # wrappers, so they verify by direct match. The slot-count helpers, `sv`,
    # `rval_aux` and the private M-arbitrary `jqN_prime_not_mem_adjoin` are
    # `private` in the port, so the checker never sees them.
    "Theorems/Thm_ModularCurve_minpoly_jqN_map_eq_prod_slots.lean",
    "Theorems/Thm_ModularCurve_jqN_prime_not_mem_full.lean",
    # Topic 20, the unconditional capstone. The theorem and its three corollaries
    # are public `Theorems/` wrappers, so they verify by direct match. `inputs` and
    # the now-public `hall_all` are handled in `OWN_PROOFS` (the latter is FLT's
    # strong induction, restated against the port's `Inputs` bundle).
    "Theorems/Thm_ModularCurve_functionFieldGeneration.lean",
    "Theorems/Thm_ModularCurve_modularFunctionField_eq_full.lean",
    "Theorems/Thm_ModularCurve_finrank_adjoin_jqN_eq_dedekindPsi.lean",
    "Theorems/Thm_ModularCurve_relfinrank_full_eq_dedekindPsi.lean",
    # Topic 20's interface tail: the last of §2.1's five out-of-cone nodes and its
    # two neighbours. All three are public wrappers.
    "Theorems/Thm_ModularCurve_exists_monic_evalAtJ_jqN_eq_zero.lean",
    "Theorems/Thm_ModularCurve_exists_phiIrreducible_of_finrank_eq.lean",
    "Theorems/Thm_ModularCurve_exists_phiIrreducible.lean",
    # --- The AlgebraicCurve layer (SET 1: AC0 + T1) -------------------------
    # T1's nineteen ord/valuation interface nodes. They are declared in the pin
    # under `P2M.Dup.AlgebraicCurve.*`, so the checker matches the last name
    # component; their statements are the wrappers, hence the port writes the
    # wrappers' explicit binders and these files come *before* the definition
    # files (SET-1 §5: the definition files are appended after the wrappers that
    # share a last name).
    "Theorems/Thm_AlgebraicCurve_Place_ord_nonneg_of_mem.lean",
    "Theorems/Thm_AlgebraicCurve_Place_mem_of_ord_nonneg.lean",
    "Theorems/Thm_AlgebraicCurve_Place_mem_iff_ord_nonneg.lean",
    "Theorems/Thm_AlgebraicCurve_Place_ord_algebraMap.lean",
    "Theorems/Thm_AlgebraicCurve_Place_ord_smul_of_ne_zero.lean",
    "Theorems/Thm_AlgebraicCurve_Place_mem_toValuationSubring_of_isIntegral_adjoin.lean",
    "Theorems/Thm_AlgebraicCurve_Place_ord_eq_zero_of_isIntegral_adjoin.lean",
    "Theorems/Thm_AlgebraicCurve_Place_mem_iff_adicValuation_le_one.lean",
    "Theorems/Thm_AlgebraicCurve_Place_mem_maximalIdeal_iff_adicValuation_lt_one.lean",
    "Theorems/Thm_AlgebraicCurve_Place_adicValuation_valuationSubring.lean",
    "Theorems/Thm_AlgebraicCurve_Place_isEquiv_adicValuation_of_valuationSubring_eq.lean",
    "Theorems/Thm_AlgebraicCurve_Place_ord_eq_neg_log_of_valuationSubring_eq.lean",
    "Theorems/Thm_AlgebraicCurve_Place_adicValuation_isRankOneDiscrete.lean",
    "Theorems/Thm_AlgebraicCurve_Place_adicValuation_isTrivialOn.lean",
    "Theorems/Thm_AlgebraicCurve_Place_isEquiv_adicValuation_ofHeightOneSpectrum.lean",
    "Theorems/Thm_AlgebraicCurve_Place_ord_ofHeightOneSpectrum_ne_zero_iff.lean",
    "Theorems/Thm_AlgebraicCurve_isIntegral_adjoin_intermediateField_mk.lean",
    "Theorems/Thm_AlgebraicCurve_isIntegral_adjoin_map_algHom.lean",
    "Theorems/Thm_AlgebraicCurve_isIntegral_adjoin_of_isScalarTower.lean",
    # Three pin-`private` ord helpers AC0 promotes because the cone reaches them
    # through wrappers (they are written with the wrappers' explicit binders).
    "Theorems/Thm_AlgebraicCurve_Place_exists_ord_pos.lean",
    "Theorems/Thm_AlgebraicCurve_Place_comap_algebraMap_ne_top.lean",
    "Theorems/Thm_AlgebraicCurve_Place_mem_comap_iff_ord_nonneg.lean",
    # The AlgebraicCurve *definition* modules the port transcribes. They are
    # listed after the wrappers above so those wrappers' binders stay the
    # authority for the shared last names. `Def_AlgebraicCurve_RatFuncPlaceInfty`
    # is the module `PORTING-AC.md` §2.2's six-module table omits; AC0 adds it.
    # `BaseChangeGalois` precedes `DivisorClassGroup`: the latter carries a
    # *second*, dropped Galois action (`F ≃ₐ[K] F` on `Pic0`) whose `smul_def`/
    # `ord_smul`/`deg_smul` share last names with the `SemilinearAut` block the
    # port transcribes.
    "Definitions/Def_AlgebraicCurve_BaseChangeGalois.lean",
    "Definitions/Def_AlgebraicCurve_DivisorClassGroup.lean",
    "Definitions/Def_AlgebraicCurve_DivisorPushPull.lean",
    "Definitions/Def_AlgebraicCurve_PlacesOverDVR.lean",
    "Definitions/Def_AlgebraicCurve_Correspondence.lean",
    "Definitions/Def_AlgebraicCurve_RatFuncPlaces.lean",
    "Definitions/Def_AlgebraicCurve_RatFuncPlaceInfty.lean",
    # T2 (the fibre dictionary). The three nodes are public wrappers, so they
    # match by direct last-name lookup with the wrappers' binders. The pin's
    # `S_..._fiberOver.lean` carries the 17 promoted dictionary declarations as
    # `private`; it is appended after the wrappers so the checker's dotted
    # fallback reads those originals (their port copies are the public statements
    # at the pinned names under `AlgebraicCurve.Place`).
    "Theorems/Thm_AlgebraicCurve_Place_sum_ramificationIndex_mul_inertiaDeg_fiberOver.lean",
    "Theorems/Thm_AlgebraicCurve_Place_sum_ramificationIndex_mul_inertiaDeg_le_finrank.lean",
    "Theorems/Thm_AlgebraicCurve_Place_inertiaDeg_pos.lean",
    "P2M/Sol/S_AlgebraicCurve_Place_sum_ramificationIndex_mul_inertiaDeg_fiberOver.lean",
    # T3 (Galois ramification/inertia). All seven are public wrappers with
    # explicit binders, so they verify by direct last-name lookup.
    "Theorems/Thm_AlgebraicCurve_Place_exists_algEquiv_smul_eq_of_restrict_eq.lean",
    "Theorems/Thm_AlgebraicCurve_Place_restrict_ofAlgAut_smul.lean",
    "Theorems/Thm_AlgebraicCurve_SemilinearAut_ramificationIndex_smul.lean",
    "Theorems/Thm_AlgebraicCurve_SemilinearAut_inertiaDeg_smul.lean",
    "Theorems/Thm_AlgebraicCurve_SemilinearAut_ord_algebraMap_smul.lean",
    "Theorems/Thm_AlgebraicCurve_Place_ramificationIndex_eq_of_restrict_eq.lean",
    "Theorems/Thm_AlgebraicCurve_Place_inertiaDeg_eq_of_restrict_eq.lean",
    # T4 (along-map transport + `Pic0` descent). The sixteen nodes are public
    # wrappers; the pin's `bifiber` `S_` file then carries the six public prelude
    # declarations (`inertiaDegAlong_congr`, `isIntegral_toAlgHom`,
    # `toAlgHom_comp_toAlgHom`, `restrict_restrict` and the two `Place.*_restrict`)
    # that the port writes once in `Transport.lean`.
    "Theorems/Thm_AlgebraicCurve_Place_restrictAlong_restrictAlong.lean",
    "Theorems/Thm_AlgebraicCurve_Place_ramificationIndexAlong_comp.lean",
    "Theorems/Thm_AlgebraicCurve_Place_inertiaDegAlong_comp.lean",
    "Theorems/Thm_AlgebraicCurve_Divisor_pushforwardAlong_pushforwardAlong.lean",
    "Theorems/Thm_AlgebraicCurve_Divisor_pullbackAlong_pullbackAlong.lean",
    "Theorems/Thm_AlgebraicCurve_Divisor_correspondence_congr.lean",
    "Theorems/Thm_AlgebraicCurve_Divisor_correspondence_correspondence.lean",
    "Theorems/Thm_AlgebraicCurve_Pic0_correspondence_correspondence_comm.lean",
    "Theorems/Thm_AlgebraicCurve_Pic0_mk_eq_zero_iff.lean",
    "Theorems/Thm_AlgebraicCurve_Pic0_zsmul_mk.lean",
    "Theorems/Thm_AlgebraicCurve_Pic0_nsmul_mk_eq_zero_of_isPrincipal.lean",
    "Theorems/Thm_AlgebraicCurve_Pic0_zsmul_mk_eq_zero_of_isPrincipal.lean",
    "Theorems/Thm_AlgebraicCurve_Pic0_addOrderOf_mk_dvd_of_isPrincipal.lean",
    "Theorems/Thm_AlgebraicCurve_finiteAlong_comp.lean",
    "Theorems/Thm_AlgebraicCurve_finiteAlong_of_surjective.lean",
    "Theorems/Thm_AlgebraicCurve_separableAlong_of_charZero.lean",
    # T5's wrappers come **before** the pin's `bifiber` `S_` file: that file's
    # internal `BifibreDev` copy of `sum_ramificationIndex_mul_inertiaDeg_bifiber`
    # makes `M` implicit (`{K F F₁ F₂ E M : Type*}`), while the wrapper makes it an
    # explicit binder (`{K F F₁ F₂ E : Type*} (M : Type*)`). The wrapper is the
    # statement authority (SET-2 §1.2), so it must win the checker's first-name
    # lookup; the divergence is recorded in `logs/ac-port.md`.
    "Theorems/Thm_MulAction_ncard_orbit_inter_orbit_mul_card.lean",
    "Theorems/Thm_Subgroup_exists_eq_mul_of_index_inf_eq.lean",
    "Theorems/Thm_AlgebraicCurve_Place_card_fiberOver_mul_ramificationIndex_mul_inertiaDeg.lean",
    "Theorems/Thm_AlgebraicCurve_Place_exists_restrict_eq.lean",
    "Theorems/Thm_AlgebraicCurve_Place_sum_ramificationIndex_mul_inertiaDeg_bifiber.lean",
    "P2M/Sol/S_AlgebraicCurve_Place_sum_ramificationIndex_mul_inertiaDeg_bifiber.lean",
    # T6 (the local exchange + the normal closure). The public node is the wrapper;
    # the pin's `S_` file carries its two public stages (`exchange_of_isGalois`,
    # `sum_ramificationIndex_mul_inertiaDeg_bifiber_of_isSeparable`) whose names have
    # no wrapper of their own. The envelope plumbing is `private` in the port, so the
    # checker never asks for the pin's public `BifibreW2.Env`/`algebraEnv`.
    "Theorems/Thm_AlgebraicCurve_Place_sum_ramificationIndex_mul_inertiaDeg_exchange.lean",
    "P2M/Sol/S_AlgebraicCurve_Place_sum_ramificationIndex_mul_inertiaDeg_exchange.lean",
    # T8 (the `P¹` places and degree). All eleven nodes have wrappers; ten have no
    # other source, and `deg_ofHeightOneSpectrum` is already AC0's (the
    # definition-file copy wins this name's lookup, and the port matches it, not
    # the `P2M.Dup` wrapper's explicit-`K` spelling).
    "Theorems/Thm_AlgebraicCurve_RationalFunctionField_finite_setOf_ord_ne_zero.lean",
    "Theorems/Thm_AlgebraicCurve_RationalFunctionField_subsingleton_setOf_forall_ne_ofHeightOneSpectrum.lean",
    "Theorems/Thm_AlgebraicCurve_RationalFunctionField_exists_forall_ne_ofHeightOneSpectrum.lean",
    "Theorems/Thm_AlgebraicCurve_RationalFunctionField_degree_eq_zero_of_forall_eq_ord_algebraMap.lean",
    "Theorems/Thm_AlgebraicCurve_RationalFunctionField_deg_ofHeightOneSpectrum.lean",
    "Theorems/Thm_AlgebraicCurve_RationalFunctionField_deg_eq_one_of_forall_ne_ofHeightOneSpectrum.lean",
    "Theorems/Thm_AlgebraicCurve_RationalFunctionField_degree_eq_zero_of_forall_eq_ord.lean",
    "Theorems/Thm_AlgebraicCurve_RationalFunctionField_ord_eq_neg_intDegree_of_forall_ne_ofHeightOneSpectrum.lean",
    "Theorems/Thm_AlgebraicCurve_RationalFunctionField_ord_ofHeightOneSpectrum_of_span.lean",
    "Theorems/Thm_AlgebraicCurve_RationalFunctionField_ord_ofHeightOneSpectrum_eq_neg_log.lean",
    "Theorems/Thm_AlgebraicCurve_RationalFunctionField_toValuationSubring_eq_of_forall_ne_ofHeightOneSpectrum.lean",
    # R2: the last two `P¹` nodes promoted from port-private. The two `Theorems/`
    # wrappers are the statement authority and come **first**: the `eq_` wrapper
    # spells K implicitly (`{K : Type*}`), matching the port, while the
    # `placeInfty_` wrapper spells it explicitly (`(K : Type*)`), which is the
    # pin's public form (`Def_AlgebraicCurve_RatFuncPlaceClassification`) and the
    # port's now too. The `finite_setOf_ord_ne_zero` `S_` file (the provenance the
    # port header names) is appended last for the dotted-name fallback, where the
    # pin repeats both privately.
    "Theorems/Thm_AlgebraicCurve_RationalFunctionField_eq_ofHeightOneSpectrum_or_eq_placeInfty.lean",
    "Theorems/Thm_AlgebraicCurve_RationalFunctionField_placeInfty_ne_ofHeightOneSpectrum.lean",
    "P2M/Sol/S_AlgebraicCurve_RationalFunctionField_finite_setOf_ord_ne_zero.lean",
    # T9 (`HasPrincipalDivisors` via transcendence). The three nodes have
    # wrappers. The pin's `of_finiteDimensional_ratFunc` `S_` file makes the shared
    # finite-dimensional statement public (as `solution`); the `of_transcendental`
    # `S_` file carries it `private` under its proper name and the adjoin `S_` file
    # carries `W2.hasPrincipalDivisors_adjoin`. Both stages are appended so those
    # public/private originals are available.
    "Theorems/Thm_AlgebraicCurve_hasPrincipalDivisors_of_finiteDimensional_ratFunc.lean",
    "Theorems/Thm_AlgebraicCurve_hasPrincipalDivisors_of_transcendental.lean",
    "Theorems/Thm_AlgebraicCurve_hasPrincipalDivisors_adjoin_of_transcendental.lean",
    "P2M/Sol/S_AlgebraicCurve_hasPrincipalDivisors_of_finiteDimensional_ratFunc.lean",
    "P2M/Sol/S_AlgebraicCurve_hasPrincipalDivisors_of_transcendental.lean",
    "P2M/Sol/S_AlgebraicCurve_hasPrincipalDivisors_adjoin_of_transcendental.lean",
    # --- T7, the divisor-exchange capstone (the human's topic) ---------------
    # The one wrapper. The pin's `S_` file is *not* listed: its only other public
    # declaration is `BifibreWEX.restrict_restrict`, which the port does not
    # reproduce (it imports `AlgebraicCurve.BifibreDev.restrict_restrict` from
    # `WeilExchange/Transport.lean`, already verified through the `bifiber` source).
    "Theorems/Thm_AlgebraicCurve_Divisor_pullbackAlong_pushforwardAlong_eq_pushforwardAlong_pullbackAlong.lean",
    # --- The Hecke-operator topic (Tier 0 + Tier 1) --------------------------
    # The five Tier-1 slash-invariance nodes are public `Theorems/` wrappers, so
    # they verify by direct name match. The wrappers come *before* the pin's `S_`
    # carrier so their binder spelling is the authority. The `S_` file supplies
    # the shared representative block promoted into
    # `FLTForHuman/ModularForms/Defs/HeckeRepresentatives.lean` (`det_eq`, the
    # four `_mul_of_eq` lemmas, `heckeRep`/`redMatrix`/`heckeRep_mul`,
    # `sum_range_eq_sum_zmod`, `affinePerm`, `heckeMatrix_mul_of_dvd` and the two
    # `_slash_mapGL` workhorses); it is the exact Γ₀ copy whose statements carry
    # the `g' 1 0 = …` conjunct the port's old private copy had dropped.
    "Theorems/Thm_ModularForm_heckeU_slash_eq_self_of_mem_Gamma0.lean",
    "Theorems/Thm_ModularForm_heckeT_slash_eq_self_of_mem_Gamma0.lean",
    "Theorems/Thm_ModularForm_heckeU_slash_eq_self_of_mem_Gamma0_div.lean",
    "Theorems/Thm_ModularForm_heckeU_add_slash_fricke_eq_zero.lean",
    "Theorems/Thm_ModularForm_exists_levelOne_coe_eq_zpow_smul_add_heckeU_slash_fricke.lean",
    "P2M/Sol/S_ModularForm_heckeU_slash_eq_self_of_mem_Gamma0.lean",
    # --- SET-2 T3: the analytic regularity layer ----------------------------
    # The seven regularity targets are public `Theorems/` wrappers, so they
    # verify by direct name match. The wrappers come before the pin's `S_`
    # carriers because the checker is textual and the wrappers' explicit binders
    # are the statement authority. The pin repeats this analytic head in ten
    # `S_` files; only the first is listed, for the two promoted `1 0 = 0`
    # matrix helpers if a later topic makes them public (they stay `private`
    # here, so the checker never asks for them).
    "Theorems/Thm_ModularForm_mdifferentiable_heckeU.lean",
    "Theorems/Thm_ModularForm_mdifferentiable_heckeT.lean",
    "Theorems/Thm_ModularForm_mdifferentiable_slash_heckeDiagMatrix.lean",
    "Theorems/Thm_ModularForm_periodic_heckeU_comp_ofComplex.lean",
    "Theorems/Thm_ModularForm_periodic_heckeT_comp_ofComplex.lean",
    "Theorems/Thm_ModularForm_isBoundedAtImInfty_heckeU.lean",
    "Theorems/Thm_ModularForm_isBoundedAtImInfty_heckeT.lean",
    "P2M/Sol/S_ModularForm_mdifferentiable_heckeU.lean",
    # --- SET-2 T4: the cusp-class layer -------------------------------------
    # The four nodes are public `Theorems/` wrappers, so they verify by direct
    # name match. The pin's four `S_` files are 132 lines each with an identical
    # block; everything in the block is `private` in the port, so no carrier is
    # needed. `upperTriangularGL`/`val_upperTriangularGL` were promoted public in
    # `Defs/HeckeOperator.lean` and match the pin's definition file (listed far
    # above).
    "Theorems/Thm_ModularFormClass_isBoundedAt_heckeU.lean",
    "Theorems/Thm_ModularFormClass_isBoundedAt_heckeT.lean",
    "Theorems/Thm_CuspFormClass_isZeroAt_heckeU.lean",
    "Theorems/Thm_CuspFormClass_isZeroAt_heckeT.lean",
    # --- SET-3 T5: the `q`-coefficient layer ---------------------------------
    # The fifteen targets are public `Theorems/` wrappers, so they verify by name.
    # The three pairs with the same last name in two namespaces
    # (`qCoeff_hecke{U,T}`, `qCoeff_comp_heckeDiagMatrix_smul`: once under
    # `UpperHalfPlane`, once under `ModularFormClass`) are declared in the port
    # with their dotted wrapper names so the checker's dotted fallback routes each
    # copy to its own wrapper; `SOURCES` order is therefore irrelevant for them.
    # `ModularFormClass.qCoeff` is the pin's definition from
    # `Definitions/Def_FLTPrelim_Modularity.lean`, whose definition module is
    # appended last (its only overlapping last name is `qCoeff` itself).
    # `Definitions/Def_PowerSeries_FormalHeckeOperators.lean` is the source for
    # the five non-colliding `PowerSeries` declarations; its `heckeU`/`heckeT`
    # are the dotted `OWN_PROOFS` exemptions.
    "Theorems/Thm_UpperHalfPlane_qCoeff_heckeU.lean",
    "Theorems/Thm_UpperHalfPlane_qCoeff_heckeT.lean",
    "Theorems/Thm_UpperHalfPlane_qCoeff_comp_heckeDiagMatrix_smul.lean",
    "Theorems/Thm_UpperHalfPlane_eq_of_forall_qCoeff_eq.lean",
    "Theorems/Thm_ModularFormClass_qCoeff_heckeU.lean",
    "Theorems/Thm_ModularFormClass_qCoeff_heckeT.lean",
    "Theorems/Thm_ModularFormClass_qCoeff_comp_heckeDiagMatrix_smul.lean",
    "Theorems/Thm_ModularFormClass_qExpansion_heckeU_eq_heckeU.lean",
    "Theorems/Thm_ModularFormClass_qExpansion_heckeT_eq_heckeT.lean",
    "Theorems/Thm_ModularForm_qExpansion_heckeDiagMatrix_smul_eq_qExpand_of_levelOne.lean",
    "Theorems/Thm_ModularForm_coeffHeckeT_comm.lean",
    "Theorems/Thm_ModularForm_coeffHeckeU_comm.lean",
    "Theorems/Thm_ModularForm_coeffHeckeT_coeffHeckeU_comm.lean",
    "Theorems/Thm_ModularForm_coeffHeckeT_int.lean",
    "Theorems/Thm_ModularForm_coeffHeckeU_int.lean",
    "Definitions/Def_PowerSeries_FormalHeckeOperators.lean",
    "Definitions/Def_FLTPrelim_Modularity.lean",
    # --- SET-3 T6: the bundled linear maps -----------------------------------
    # The twelve bundled declarations have no `Theorems/` wrapper; they verify by
    # name against the pin's `Definitions/Def_ModularForm_HeckeOperatorForms.lean`.
    # The pin declares them once under `namespace ModularForm` and once under
    # `namespace CuspForm`; the checker's namespace-qualified fallback (SET-3 T5)
    # is what lets the `CuspForm` copies match their own declarations. The three
    # thin downstream wrappers are public `Theorems/` files.
    "Definitions/Def_ModularForm_HeckeOperatorForms.lean",
    "Theorems/Thm_CuspForm_qExpansion_heckeTLin.lean",
    "Theorems/Thm_CuspForm_exists_coe_eq_heckeT.lean",
    "Theorems/Thm_CuspForm_exists_coe_eq_heckeU.lean",
    # --- SET-3 T7: commutation and the Hecke algebra -------------------------
    # The five `LaurentSeries` definition declarations have no `Theorems/`
    # wrapper in the pin, so their two definition modules are the comparable
    # copies; `heckeU`/`heckeT`/`coeff_hecke{U,T}` also occur in the PowerSeries
    # and ModularForm definition files, and the checker's namespace-qualified
    # fallback separates the `LaurentSeries.*` copies. The Hecke algebra's
    # fourteen declarations likewise verify against
    # `Definitions/Def_CuspForm_HeckeAlgebra.lean`. The thirteen commutation
    # targets are public `Theorems/` wrappers.
    "Definitions/Def_LaurentSeries_HeckeU.lean",
    "Definitions/Def_LaurentSeries_HeckeV.lean",
    "Definitions/Def_CuspForm_HeckeAlgebra.lean",
    "Theorems/Thm_ModularFormClass_heckeU_heckeU_comm.lean",
    "Theorems/Thm_ModularFormClass_heckeT_heckeT_comm.lean",
    "Theorems/Thm_ModularFormClass_heckeT_heckeU_comm.lean",
    "Theorems/Thm_CuspForm_heckeTLin_comm.lean",
    "Theorems/Thm_CuspForm_heckeULin_comm.lean",
    "Theorems/Thm_CuspForm_heckeTLin_heckeULin_comm.lean",
    "Theorems/Thm_ModularForm_heckeTLin_comm.lean",
    "Theorems/Thm_LaurentSeries_commute_heckeU_heckeU.lean",
    "Theorems/Thm_LaurentSeries_commute_heckeU_heckeV.lean",
    "Theorems/Thm_LaurentSeries_commute_heckeV_heckeV.lean",
    "Theorems/Thm_LaurentSeries_commute_heckeU_heckeT.lean",
    "Theorems/Thm_LaurentSeries_commute_heckeT_heckeT.lean",
    # --- SET-4 T8: the eigenform interface ------------------------------------
    # The structure `CuspForm.IsNormalizedEigenform` is verified against the
    # already-listed `Definitions/Def_FLTPrelim_Modularity.lean` (which SET-3 T5
    # appended for `ModularFormClass.qCoeff`). The thirteen targets are public
    # `Theorems/` wrappers. `Thm_CuspForm_qCoeff_zero` is an extra dependency the
    # topic consumes (`isNormalizedEigenform_iff_coeffHecke` needs `qCoeff f 0 = 0`)
    # and which the port had not carried; it is ported publicly here and its
    # wrapper appended, rather than hidden as a private helper.
    "Theorems/Thm_CuspForm_qCoeff_zero.lean",
    "Theorems/Thm_CuspForm_isNormalizedEigenform_iff_coeffHecke.lean",
    "Theorems/Thm_ModularFormClass_heckeT_eq_smul_iff.lean",
    "Theorems/Thm_ModularFormClass_heckeU_eq_smul_iff.lean",
    "Theorems/Thm_CuspForm_heckeTLin_apply_eq_smul_iff.lean",
    "Theorems/Thm_CuspForm_heckeULin_apply_eq_smul_iff.lean",
    "Theorems/Thm_CuspForm_isNormalizedEigenform_iff_heckeT.lean",
    "Theorems/Thm_CuspForm_isNormalizedEigenform_iff_heckeTLin.lean",
    "Theorems/Thm_CuspForm_IsNormalizedEigenform_heckeTLin_apply_eq_qCoeff_smul.lean",
    "Theorems/Thm_CuspForm_IsNormalizedEigenform_heckeULin_apply_eq_qCoeff_smul.lean",
    "Theorems/Thm_ModularForm_eq_zero_of_coeffHecke_eigen_of_apply_one_eq_zero.lean",
    "Theorems/Thm_ModularForm_coeffHecke_eigenvalue_eq_apply_of_apply_one_eq_one.lean",
    "Theorems/Thm_LaurentSeries_eq_zero_of_heckeT_eq_smul_of_heckeU_eq_smul_of_coeff_one_eq_zero.lean",
    "Theorems/Thm_PowerSeries_coeff_heckeT_pow_sub_mem_span.lean",
    # --- SET-4 T9: the integral lattice ---------------------------------------
    # The two definitions have no `Theorems/` wrapper and verify by name against
    # the pin's 8-line definition file. The three lattice-action targets are
    # public `Theorems/` wrappers. The weight-2 auxiliary vocabulary
    # (`Def_CuspForm_IntegralLattice.lean`) is T10's and is not appended here.
    "Definitions/Def_CuspForm_IntegralStructure.lean",
    "Theorems/Thm_CuspForm_mem_intLattice_of_coe_eq_heckeT.lean",
    "Theorems/Thm_CuspForm_mem_intLattice_of_coe_eq_heckeU.lean",
    "Theorems/Thm_CuspForm_mem_intLattice_of_mem_heckeAlgebra.lean",
    # --- SET-4 T10: the two self-contained definition modules ----------------
    # The `χ₋₃` Eisenstein vocabulary and the weight-2 auxiliary lattice have no
    # `Theorems/` wrapper in the pin and verify by name against their definition
    # files. In SET 4 T10's *theorem* targets were blocked; route C′ has since
    # supplied `HasIntegralStructure` for `2 ≤ k` (`WeightOne/IntegralStructure.lean`)
    # and the port carries the Sturm bound, so the finiteness targets are ported
    # too — see the "T10 completion" block below.
    "Definitions/Def_ModularForm_EisensteinChiNegThree.lean",
    "Definitions/Def_CuspForm_IntegralLattice.lean",
    # --- T10 completion: the finite/free Hecke algebra ------------------------
    # `WeightOne/IntegralStructure.lean` supplies `CuspForm.HasIntegralStructure`
    # and `SturmBound.lean` supplies `ModularForm.sturm_bound_Gamma0`, so T10's
    # theorem targets are now statable and provable. `HeckeFiniteAlgebra.lean`
    # carries the Hecke-algebra finiteness half; `HeckeLattice.lean` gained
    # `intLattice_fg`/`intLattice_free_and_finite` (reusing its private
    # coefficient-linearity block, so the Sturm-bound truncation is written once),
    # and `HeckeQCoeff.lean` gained `ModularFormClass.eq_of_forall_qCoeff_eq` (the
    # bundled q-coefficient uniqueness the `finrank` span proof consumes). Every
    # statement is the pin's `Theorems/` wrapper verbatim. The eigenbasis-span
    # family (`span_heckeTLin_eigen_eq_top`, `exists_cyclic_span_heckeAlgebra`,
    # `heckeEvalForms_range_eq_top`, `exists_top_eq_heckeAlgebra_adjoin_smul`)
    # remains blocked on the Petersson inner product, the newform/Atkin–Lehner
    # separation and `Def_CuspForm_HeckeEvalForms` respectively; see
    # `logs/hecke-port.md` §T10.
    "Theorems/Thm_ModularFormClass_eq_of_forall_qCoeff_eq.lean",
    "Theorems/Thm_CuspForm_HasIntegralStructure_eq_zero_of_forall_mem_intLattice.lean",
    "Theorems/Thm_CuspForm_intLattice_fg.lean",
    "Theorems/Thm_CuspForm_intLattice_free_and_finite.lean",
    "Theorems/Thm_CuspForm_HasIntegralStructure_moduleFinite_heckeAlgebra.lean",
    "Theorems/Thm_CuspForm_HasIntegralStructure_moduleFree_heckeAlgebra.lean",
    "Theorems/Thm_CuspForm_moduleFinite_heckeAlgebra.lean",
    "Theorems/Thm_CuspForm_moduleFinite_heckeAlgebra_two.lean",
    "Theorems/Thm_CuspForm_fg_toSubmodule_heckeAlgebra.lean",
    "Theorems/Thm_CuspForm_finrank_span_heckeAlgebra_eq_finrank.lean",
    # --- SET-M1 m1: the Hecke correspondence vocabulary -----------------------
    # The five definition modules have no `Theorems/` wrapper, so they verify by
    # name against their `Definitions/` files (binders verbatim). Two of the
    # pin's *private* supply lemmas in `HeckeOperator` are themselves wrapper
    # targets: `laurentBaseChange_mono` (pin-private `'` in `HeckeOperator`,
    # `''` in `DegeneracyTower`) and `qExpand_mem_laurentBaseChange` are ported
    # **publicly** from their wrappers, so the wrappers are listed first and the
    # port writes one home for a lemma the pin writes twice privately. The other
    # two supply lemmas dedup to the already-ported public
    # `Defs/Laurent.lean` `coeffMap_qExpand`/`coeffEmb_qExpand`.
    "Theorems/Thm_ModularCurve_laurentBaseChange_mono.lean",
    "Theorems/Thm_ModularCurve_qExpand_mem_laurentBaseChange.lean",
    "Definitions/Def_ModularCurve_ArithmeticGalois.lean",
    "Definitions/Def_ModularCurve_HeckeOperator.lean",
    "Definitions/Def_ModularCurve_DegeneracyTower.lean",
    "Definitions/Def_ModularCurve_HeckeOperatorTotal.lean",
    "Definitions/Def_ModularCurve_HeckeInputsAll.lean",
    "Definitions/Def_ModularCurve_HeckeModule.lean",
    # The two `HeckeAlg`/`heckeGen` definitions the optional Hecke-module payoff
    # needs. The pin's `Def_ModularCurve_HeckeModule.lean` imports them from this
    # large-cone file; the port restates them locally (3 lines) and registers the
    # pin original here so the checker verifies them. Appended last so its other
    # declarations cannot shadow any existing first-name match.
    "Definitions/Def_HeckeGalois_EichlerShimura.lean",
    # --- SET-M1 m2: geometric base change, cusps, q-adic place, modular unit ---
    # The six definition modules verify by name against their `Definitions/`
    # files. `GeometricBaseChange` is the pin's tensor-product shape; its
    # `PicAction`-free declarations are all transcribed. `QAdicPlace` and
    # `ModularUnit` adapt to v4.34 (`Subalgebra.toIntermediateField'` instead of
    # the removed `Subfield.toIntermediateField'`, `Set.mem_ofPred_eq`,
    # `dite_eq_left`/`dite_eq_right`), but the statements are the pin's verbatim.
    "Definitions/Def_ModularCurve_JqCoeff.lean",
    "Definitions/Def_ModularCurve_GeometricBaseChange.lean",
    "Definitions/Def_ModularCurve_QAdicPlace.lean",
    "Definitions/Def_ModularCurve_ModularUnit.lean",
    "Definitions/Def_ModularCurve_AtkinLehner.lean",
    "Definitions/Def_ModularCurve_CuspidalClass.lean",
    # --- SET-M1 m3: the modular-unit q-expansion core -------------------------
    # The nine targets are public `Theorems/` wrappers, so they verify by direct
    # name match. The port's public generic heads `hasSum_modularUnit` /
    # `hasSum_modularUnitInv` are the pin's *private* per-file heads, repeated in
    # four `S_` files; the first `qParam` and first `inv` files are listed so the
    # checker's dotted fallback reads those private originals (the port's
    # statements use the pin's `𝕢`/`ℍ` notation, so the text matches). All other
    # prelude helpers are `private` in the port and invisible to the checker.
    "Theorems/Thm_ModularCurve_hasSum_modularUnitSeries_qParam.lean",
    "Theorems/Thm_ModularCurve_hasSum_modularUnitSeries_inv_qParam.lean",
    "Theorems/Thm_ModularCurve_hasSum_smul_modularUnitSeries_qParam.lean",
    "Theorems/Thm_ModularCurve_hasSum_smul_modularUnitSeries_inv_qParam.lean",
    "Theorems/Thm_ModularCurve_qParam_coeff_unique.lean",
    "Theorems/Thm_ModularCurve_laurent_qParam_coeff_unique.lean",
    "Theorems/Thm_ModularCurve_exists_perm_gamma0_cosetReps.lean",
    "Theorems/Thm_ModularCurve_exists_sl2_heckeDiagMatrix_smul_eq.lean",
    "Theorems/Thm_ModularCurve_discriminant_div_discriminant_heckeDiagMatrix_smul.lean",
    "P2M/Sol/S_ModularCurve_hasSum_modularUnitSeries_qParam.lean",
    "P2M/Sol/S_ModularCurve_hasSum_modularUnitSeries_inv_qParam.lean",
    # SET-M2 m4: the Fricke/inclusion core and the first two headlines. The two
    # `of_hasSum_of_gamma0_invariant` wrappers are the statement authority; the
    # shared 651-content-line prelude is transcribed from the first `S_` file
    # (the dotted fallback resolves the `ModularCurve.QExpN` names), and the
    # third `S_` file is the comparable copy for the transport block
    # (`natDegree_interpPoly_lt`, `realL_jtN_S`, `realL_sum_qExpand_mul_jq_pow`,
    # `coeffMap_castC_injective`, `embW*`, `fricke_transport`).
    "Theorems/Thm_ModularCurve_mem_modularFunctionField_of_hasSum_of_gamma0_invariant.lean",
    "Theorems/Thm_ModularCurve_isIntegral_adjoin_jq_of_hasSum_of_gamma0_invariant.lean",
    "Theorems/Thm_ModularCurve_modularUnitSeries_mem_modularFunctionField.lean",
    "Theorems/Thm_ModularCurve_modularUnitSeries_mem_modularFunctionFieldFull.lean",
    "Theorems/Thm_ModularCurve_isIntegral_adjoin_jq_modularUnitSeries.lean",
    "Theorems/Thm_ModularCurve_isIntegral_adjoin_jq_modularUnitSeries_inv.lean",
    "P2M/Sol/S_ModularCurve_mem_modularFunctionField_of_hasSum_of_gamma0_invariant.lean",
    "P2M/Sol/S_ModularCurve_coe_frickeInvolutionFull_eq_of_hasSum_of_gamma0_invariant.lean",
    # SET-M2 m4, the third headline (delivered with m5 in `FrickeAut.lean`): its
    # two `Thm_` wrappers are the statement authority.
    "Theorems/Thm_ModularCurve_coe_frickeInvolutionFull_eq_of_hasSum_of_gamma0_invariant.lean",
    "Theorems/Thm_ModularCurve_coe_frickeInvolutionFull_modularUnitSeries.lean",
    # SET-M2 m5, the Fricke-automorphism module's internal helpers: the pin's
    # `S_` file is their comparable copy (the port exposes them publicly; the
    # dotted fallback resolves the names).
    "P2M/Sol/S_ModularCurve_exists_isFrickeAut_of_modularPolynomialData.lean",
    # SET-M2 m6: the Φ datum family and its degree tail.
    "Theorems/Thm_ModularCurve_exists_modularPolynomialData_evalSymm.lean",
    "Theorems/Thm_ModularCurve_modularPolynomialFamily.lean",
    "Theorems/Thm_ModularCurve_full_eq_of_prime.lean",
    "Theorems/Thm_ModularCurve_functionFieldGeneration_of_prime.lean",
    "Theorems/Thm_ModularCurve_ModularPolynomialData_isIntegral_jqN.lean",
    "Theorems/Thm_ModularCurve_isIntegral_jqNModC_mul.lean",
    "Theorems/Thm_ModularCurve_ModularPolynomialData_eval_jqNModC_mul_eq_zero.lean",
    "Theorems/Thm_ModularCurve_ModularPolynomialData_eval_jqNModC_of_mul_eq_zero.lean",
    "Theorems/Thm_ModularCurve_isIntegral_jqNModC_all_of_modularPolynomialFamily.lean",
    "Theorems/Thm_ModularCurve_nonempty_modularPolynomialData_of_squarefree.lean",
    "Theorems/Thm_ModularCurve_transcendental_jqModC.lean",
    "Theorems/Thm_ModularCurve_finiteDimensional_adjoin_jqNModC.lean",
    "Theorems/Thm_ModularCurve_finrank_adjoin_jqNModC_le.lean",
    # --- SET-M2 m5: the cusp bookkeeping and the Fricke automorphisms ---------
    # The 15 M9 nodes whose modules landed before the m5 `CuspDichotomy` re-scope.
    # The remaining m5 wrappers (`eq_cuspInftyBar_or_eq_cuspZeroBar`,
    # `finrank_adjoin_jqNModC_eq_of_prime`, `modularFunctionFieldBar_eq_restrictScalars`)
    # and m4's third headline are (re)delivered by the focused `m5b` topic; see
    # `logs/mc-port.md` §Friction.
    "Theorems/Thm_ModularCurve_ord_qInftyPlaceBar.lean",
    "Theorems/Thm_ModularCurve_ord_cuspInftyBar.lean",
    "Theorems/Thm_ModularCurve_ord_cuspInftyBar_coeffEmb_jq.lean",
    "Theorems/Thm_ModularCurve_ord_cuspInftyBar_coeffEmb_qExpand.lean",
    "Theorems/Thm_ModularCurve_ord_cuspZeroBar_coeffEmb_jq.lean",
    "Theorems/Thm_ModularCurve_ord_cuspZeroBar_coeffEmb_qExpand.lean",
    "Theorems/Thm_ModularCurve_cuspZeroBar_ne_cuspInftyBar.lean",
    "Theorems/Thm_ModularCurve_isCusp_iff_ord_neg.lean",
    "Theorems/Thm_ModularCurve_isCusp_cuspInftyBar.lean",
    "Theorems/Thm_ModularCurve_isCusp_cuspZeroBar.lean",
    "Theorems/Thm_ModularCurve_frickeInvolutionBar_coeffEmb_qExpand.lean",
    "Theorems/Thm_ModularCurve_exists_isFrickeAut_of_modularPolynomialData.lean",
    "Theorems/Thm_ModularCurve_exists_isFrickeAut.lean",
    "Theorems/Thm_ModularCurve_exists_isFrickeAutFull.lean",
    "Theorems/Thm_ModularCurve_isFrickeAutFull_frickeInvolutionFull_prime.lean",
    # --- m13, the capstone: the target theorem (reserved for the reviewer) ------
    "Theorems/Thm_ModularCurve_heckeOperatorsCommuteBar.lean",
    # The capstone's internal helpers (`heckeExchangeAt_of_WEX`, `hfin_of_legR`,
    # `heckeExchangeAt_of_rows`, `heckeOperatorsCommuteBar_of_rows`, the three
    # dischargers) are the pin's `S_` file written once; it is their comparable
    # copy (the port exposes them publicly).
    "P2M/Sol/S_ModularCurve_heckeOperatorsCommuteBar.lean",
    # --- SET-M2 m5b: the `RatFunc` cusp model, the cusp dichotomy, the folded
    # prime degree and the restrict-scalars identity (the re-scope of the blocked
    # `CuspDichotomy`). The two `S_` files are the comparable copies for the
    # shared 160-content-line `TwoCuspAux` model (`jTr`, `φ`, `finrank_tower_eq`,
    # …); they are byte-identical there, so either supplies the statements. The
    # third target's pin proof takes the `DivUSol` divisor route and the port
    # proves it from `TwoCuspAux.bar_eq_restrictScalars`, so that `S_` file is
    # not needed for a statement match.
    "Theorems/Thm_ModularCurve_eq_cuspInftyBar_or_eq_cuspZeroBar.lean",
    "Theorems/Thm_ModularCurve_finrank_adjoin_jqNModC_eq_of_prime.lean",
    "Theorems/Thm_ModularCurve_modularFunctionFieldBar_eq_restrictScalars.lean",
    "P2M/Sol/S_ModularCurve_eq_cuspInftyBar_or_eq_cuspZeroBar.lean",
    "P2M/Sol/S_ModularCurve_finrank_adjoin_jqNModC_eq_of_prime.lean",
    # --- SET-M3 m7: the Laurent/`coeffEmb` glue and the two relative-degree
    # theorems. The eight short M4 nodes are `Degree/LaurentGlue.lean`; the two
    # heavy ones live in `Degree/Relfinrank.lean`. The `S_` files share the
    # `TS`/slot prelude, which the port already publishes in
    # `Defs/{TS,PhiAtSlot,Twist,Cyclotomic}.lean`/`PhiSlotRoots.lean`; they are
    # listed so the statement checker sees the pin's private originals too.
    "Theorems/Thm_ModularCurve_coeffEmb_jq.lean",
    "Theorems/Thm_ModularCurve_coeffEmb_jqN.lean",
    "Theorems/Thm_ModularCurve_order_qExpand.lean",
    "Theorems/Thm_ModularCurve_order_coeffEmb.lean",
    "Theorems/Thm_ModularCurve_laurentBaseChange_adjoin.lean",
    "Theorems/Thm_ModularCurve_laurentBaseChange_modularFunctionField.lean",
    "Theorems/Thm_ModularCurve_laurentBaseChange_modularFunctionFieldFull.lean",
    "Theorems/Thm_ModularCurve_transcendental_jqN.lean",
    "Theorems/Thm_ModularCurve_relfinrank_laurentBaseChange.lean",
    "Theorems/Thm_ModularCurve_relfinrank_qExpand_full.lean",
    "P2M/Sol/S_ModularCurve_relfinrank_laurentBaseChange.lean",
    "P2M/Sol/S_ModularCurve_relfinrank_qExpand_full.lean",
    # --- SET-M3 m9: the roof generation and the diagonal degree. The two
    # wrappers are the headlines of `Degree/Roof.lean`; the three AC
    # `finrankAlong` wrappers are the generic helpers the pin defines privately
    # in its two degree/roof `S_` files. The port promoted them to
    # `AlgebraicCurve/Defs/Correspondence.lean`, where they verify as identical.
    "Theorems/Thm_ModularCurve_heckeRoof_adjoin_range_union_eq_top.lean",
    "Theorems/Thm_ModularCurve_finrankAlong_towerSubstBar_comp_heckeAlphaBar.lean",
    "P2M/Sol/S_ModularCurve_heckeRoof_adjoin_range_union_eq_top.lean",
    "P2M/Sol/S_ModularCurve_finrankAlong_towerSubstBar_comp_heckeAlphaBar.lean",
    "Theorems/Thm_AlgebraicCurve_finrankAlong_comp.lean",
    "Theorems/Thm_AlgebraicCurve_finrankAlong_id.lean",
    "Theorems/Thm_AlgebraicCurve_finrankAlong_eq_relfinrank_fieldRange.lean",
    # --- SET-M4 m10: tower integrality/finiteness and the Hecke integrality
    # predicates. The 13 wrappers are the statement authority; the two heavy `S_`
    # files carry the pin's private `gens`/`isIntegral_gens` blocks (the port
    # keeps them `private` in `HeckeInputs/Integrality.lean`), so they are listed
    # for the record.
    "Theorems/Thm_ModularCurve_towerInclBar_isIntegral.lean",
    "Theorems/Thm_ModularCurve_towerSubstBar_isIntegral.lean",
    "Theorems/Thm_ModularCurve_towerInclBar_finiteAlong.lean",
    "Theorems/Thm_ModularCurve_towerSubstBar_finiteAlong.lean",
    "Theorems/Thm_ModularCurve_towerInclBar_surjective_of_dvd_dvd.lean",
    "Theorems/Thm_ModularCurve_finiteAlong_heckeAlphaBar_of_modularPolynomialData.lean",
    "Theorems/Thm_ModularCurve_finiteAlong_heckeBetaBar_of_modularPolynomialData.lean",
    "Theorems/Thm_ModularCurve_heckeAlphaBarIntegral_of_modularPolynomialData.lean",
    "Theorems/Thm_ModularCurve_heckeBetaBarIntegral_of_modularPolynomialData.lean",
    "Theorems/Thm_ModularCurve_finiteAlong_heckeAlphaBar_of_prime.lean",
    "Theorems/Thm_ModularCurve_finiteAlong_heckeBetaBar_of_prime.lean",
    "Theorems/Thm_ModularCurve_heckeAlphaBarIntegral_of_prime.lean",
    "Theorems/Thm_ModularCurve_heckeBetaBarIntegral_of_prime.lean",
    "P2M/Sol/S_ModularCurve_finiteAlong_heckeAlphaBar_of_modularPolynomialData.lean",
    "P2M/Sol/S_ModularCurve_finiteAlong_heckeBetaBar_of_modularPolynomialData.lean",
    # --- SET-M4 m11: `HasPrincipalDivisors` for the modular function fields.
    # The layer form collapses onto AC's `hasPrincipalDivisors_adjoin_of_transcendental`
    # (the coverage report's "nearly a corollary" prediction); the `bar` form is
    # the layer form at `AlgebraicClosure ℚ`.
    "Theorems/Thm_ModularCurve_hasPrincipalDivisors_laurentBaseChange_modularFunctionFieldFull.lean",
    "Theorems/Thm_ModularCurve_hasPrincipalDivisors_modularFunctionFieldBar.lean",
    "P2M/Sol/S_ModularCurve_hasPrincipalDivisors_laurentBaseChange_modularFunctionFieldFull.lean",
    # --- SET-M4 m12: the exchange reduction. The four `Theorems/` wrappers are
    # the statement authority; the pin's four `S_` files are short transcriptions
    # over the ported `Divisor.correspondence_correspondence`/`correspondence_congr`
    # and `Pic0.correspondence_correspondence_comm`, so they are listed too.
    "Theorems/Thm_ModularCurve_heckeDivBar_heckeDivBar_of_heckeExchangeAt.lean",
    "Theorems/Thm_ModularCurve_heckeDivBar_comm_of_heckeExchangeAt.lean",
    "Theorems/Thm_ModularCurve_heckeOperatorBar_comm_of_heckeExchangeAt.lean",
    "Theorems/Thm_ModularCurve_heckeOperatorsCommuteBar_of_heckeExchangeAt.lean",
    "P2M/Sol/S_ModularCurve_heckeDivBar_heckeDivBar_of_heckeExchangeAt.lean",
    "P2M/Sol/S_ModularCurve_heckeDivBar_comm_of_heckeExchangeAt.lean",
    "P2M/Sol/S_ModularCurve_heckeOperatorBar_comm_of_heckeExchangeAt.lean",
    "P2M/Sol/S_ModularCurve_heckeOperatorsCommuteBar_of_heckeExchangeAt.lean",
    # --- The level-2/level-1 cusp-form vanishing: FLT's own norm/index layer on
    # top of mathlib's level-one dimension formula. The two `Theorems/` wrappers
    # are the statement authority; the two `S_` files carry the public helpers.
    "Theorems/Thm_ModularForm_S2_Gamma0_2_eq_zero.lean",
    "Theorems/Thm_ModularForm_S2_Gamma0_one_eq_zero.lean",
    "P2M/Sol/S_ModularForm_S2_Gamma0_2_eq_zero.lean",
    "P2M/Sol/S_ModularForm_S2_Gamma0_one_eq_zero.lean",
    # --- The Sturm bound: the arithmetic-level form and its inputs. All eight
    # declarations below are `Theorems/` wrapper targets.
    "Theorems/Thm_ModularForm_sturm_bound_of_isArithmetic.lean",
    "Theorems/Thm_ModularForm_sturm_bound_Gamma0.lean",
    "Theorems/Thm_ModularForm_eq_zero_of_lt_order_qExpansion_of_isArithmetic.lean",
    "Theorems/Thm_ModularForm_levelOne_eq_zero_of_lt_order_qExpansion.lean",
    "Theorems/Thm_Subgroup_IsArithmetic_exists_nat_mem_strictPeriods_conj.lean",
    "Theorems/Thm_UpperHalfPlane_qExpansion_coeff_nat_mul.lean",
    "Theorems/Thm_UpperHalfPlane_qExpansion_prod.lean",
    "Theorems/Thm_CongruenceSubgroup_one_mem_strictPeriods_Gamma0.lean",
    # The coefficient-form Sturm bounds. FLT states both in the `section
    # SturmBound` of this file, with a ~300-line `normCofactor` prelude around
    # `CuspForm.norm`; the port re-derives them from
    # `sturm_bound_of_isArithmetic` (see `SturmBound.lean`'s header). The same
    # file carries `qCoeffTrunc`, whose truncation the port's finite-dimensionality
    # corollary uses. The wrapper is the statement authority for
    # `CuspForm.finiteDimensional_cuspForm`; FLT's `scoped instance
    # finiteDimensional_Gamma0` is invisible to the checker (its `DECL_RE` reads
    # no `scoped` modifier), so it is transcribed without a diff. Both this file
    # and the wrapper are appended last.
    "Theorems/Thm_CuspForm_finiteDimensional_cuspForm.lean",
    "P2M/Sol/S_CuspForm_finiteDimensional_cuspForm.lean",
    # --- SET-5 order 1: the weight-one toolbox layer --------------------------
    # The seven headlines are public `Theorems/` wrappers, so they verify by
    # direct name match; the wrappers are the statement authority (the port's
    # binders are the wrappers' verbatim). The pin's `S_` carriers are *not*
    # listed: every helper the port needs is `private`, so the checker never
    # sees them. The two `finiteDimensional_of_isArithmetic` nodes depend on the
    # already-listed `SturmBound.lean` declarations.
    "Theorems/Thm_PowerSeries_mem_range_map_of_monic_of_mul_mem_range.lean",
    "Theorems/Thm_IsIntegral_mem_span_of_adjoin_simple_constants.lean",
    "Theorems/Thm_IsIntegral_mem_span_of_adjoin_simple_constants_transcendental.lean",
    "Theorems/Thm_IsAlgClosed_exists_algEquiv_apply_ne_of_notMem_range.lean",
    "Theorems/Thm_UpperHalfPlane_linearIndependent_complex_of_qExpansion_coeff_mem.lean",
    "Theorems/Thm_ModularForm_finiteDimensional_of_isArithmetic.lean",
    "Theorems/Thm_CuspForm_finiteDimensional_of_isArithmetic.lean",
    # --- SET-5 order 2: the Eisenstein series --------------------------------
    # The two headlines are public `Theorems/` wrappers (direct match). The
    # series itself, `EisensteinSeries.eisensteinG`, has no wrapper; its
    # definition file is the comparable copy and is appended last so its single
    # last name cannot shadow anything already listed.
    "Theorems/Thm_EisensteinSeries_exists_modularForm_coe_eq_eisensteinG.lean",
    "Theorems/Thm_EisensteinSeries_qExpansion_eisensteinG_coeff.lean",
    "Definitions/Def_EisensteinSeries_EisensteinG.lean",
    # The general API was promoted to public in `ModularForms/EisensteinSeries.lean`
    # (`congrSet`, `eisensteinGSIF`, `eisensteinGMF`, the slash/analytic lemmas,
    # the `cls` vocabulary, ...). The pin keeps the same declarations non-`private`
    # inside its `P2MW.S_...CardG1`/`CardC` implementation namespaces, so the
    # last-name lookup reads them from the two `S_` files below. They are appended
    # after the definition file so an earlier registration always wins a last-name
    # collision; the only promoted name with a mathlib twin in the project's own
    # `EisensteinSeries` namespace (`norm_le_tsum_norm`) is kept `private` in the
    # port precisely to avoid the clash, so it never reaches this check.
    "P2M/Sol/S_EisensteinSeries_exists_modularForm_coe_eq_eisensteinG.lean",
    "P2M/Sol/S_EisensteinSeries_qExpansion_eisensteinG_coeff.lean",
    # --- SET-6 order 1: the four closure-1 Hauptmodul leaves ------------------
    # All four are public `Theorems/` wrappers (direct name match); the pin's
    # self-contained `S_` helpers are all `private` here, so the checker never
    # sees them. The two order-2 declarations follow below.
    "Theorems/Thm_ModularCurve_surjective_specialLinearGroup_map_zmod.lean",
    "Theorems/Thm_ModularCurve_qExpansion_discriminant_eq_X_mul_tprod.lean",
    "Theorems/Thm_WLight_isZeroAtImInfty_mul_disc_iff_qExpansion_coeff_le.lean",
    "Theorems/Thm_WLight_linearIndependent_complex_of_qExpansion_rational.lean",
    # --- SET-6 order 2: the χ₋₃ weight-one Eisenstein series -------------------
    # The single public headline is the wrapper verbatim. Its vocabulary
    # (`chiNegThree`, `sigmaChi`, `e1Chi3`, `E1Chi3IsModular`) is imported from
    # the already-registered `Definitions/Def_ModularForm_EisensteinChiNegThree.lean`
    # (listed above); every one of the ~400 ported analytic/arithmetic helpers is
    # `private`, so the checker sees only the headline.
    "Theorems/Thm_EisensteinWeightOne_e1Chi3IsModular.lean",
    # --- SET-7 order 1: the two big level-one Hauptmodul packages -------------
    # Both are public `Theorems/` wrappers (direct name match). The pin's
    # self-contained `S_` developments are transcribed `private` here, so the
    # checker sees only the two new headlines in the already-listed
    # `FLTForHuman/ModularForms/WeightOne/LevelOneHauptmodul.lean`.
    "Theorems/Thm_WLight_levelOne_hauptmodul_package.lean",
    "Theorems/Thm_WLight_weierstrassP_qExpansion_package.lean",
    # --- SET-7 order 2: the torsion ℘ q-expansion bundle ----------------------
    # The single public headline is the wrapper verbatim; the pin's 1,317-line
    # self-contained helper development is `private` in `WeierstrassPTorsion.lean`.
    "Theorems/Thm_ModularForm_weierstrassP_torsion_qExpansion_package.lean",
    # --- SET-8 order 1: the four monic-relation leaves ------------------------
    # All four are public `Theorems/` wrappers (direct name match). The pin
    # repeats its valuation-engine and flat-descent blocks across the four `S_`
    # files; the port writes each block once, and its five shared helpers are
    # **public promotions of pin-private names**, so the `S_` files are listed
    # too: the checker's promoted-from-pin-private lookup then verifies them
    # against the originals instead of reporting them missing.
    "Theorems/Thm_WLight_exists_analyticOnNhd_div_of_monicRel.lean",
    "Theorems/Thm_WLight_exists_mdifferentiable_div_of_monicRel.lean",
    "Theorems/Thm_WLight_exists_twist_of_flat.lean",
    "Theorems/Thm_WLight_span_inter_rational_of_twist_stable.lean",
    "P2M/Sol/S_WLight_exists_analyticOnNhd_div_of_monicRel.lean",
    "P2M/Sol/S_WLight_exists_mdifferentiable_div_of_monicRel.lean",
    "P2M/Sol/S_WLight_exists_twist_of_flat.lean",
    "P2M/Sol/S_WLight_span_inter_rational_of_twist_stable.lean",
    # --- SET-8 order 2: the three fricke-function packages --------------------
    # All three are public `Theorems/` wrappers (direct name match). The pin's
    # helpers are `private` in `FrickeFunction.lean`, one namespace per package
    # (the three pin `S_` files repeat `periodPairOfTau`/`zetaN`/`wpNorm`/
    # `frickeF`/`KPoleAt`/... and would otherwise collide), so the checker sees
    # only the three headlines. The packages' cross-edges are the pin's own and
    # are all ported: orbit → modularity + `levelOne_hauptmodul_package`;
    # intBaseChange → modularity + orbit + the order-1
    # `exists_mdifferentiable_div_of_monicRel` + SET-5's two `IsIntegral` leaves.
    "Theorems/Thm_WLight_frickeFunction_modularity_package.lean",
    "Theorems/Thm_WLight_frickeFunction_orbit_package.lean",
    "Theorems/Thm_WLight_frickeFunction_intBaseChange.lean",
    # --- SET-9 order 1: the level-fraction packages ---------------------------
    # All four are public `Theorems/` wrappers (direct name match). The pin's four
    # self-contained `S_` developments are transcribed with every helper `private`
    # inside the pin's own (renamed) namespace, so the checker sees only the four
    # headlines in `LevelFraction.lean`. The cross-edges are the pin's own:
    # `exists_levelFraction_...`/`levelN_structure_package` consume SET-7's
    # `levelOne_hauptmodul_package` plus SET-8's `frickeFunction_*` packages;
    # `exists_monicRel_j_K_...` additionally consumes order 1's
    # `exists_monicRel_j_of_mdifferentiable_levelFraction` and SET-5's
    # `UpperHalfPlane.linearIndependent_complex_of_qExpansion_coeff_mem`.
    "Theorems/Thm_WLight_qExpansion_sigmaTransport_package.lean",
    "Theorems/Thm_WLight_exists_qExpansion_coeff_mem_of_mdifferentiable_levelFraction.lean",
    "Theorems/Thm_WLight_exists_levelFraction_of_stable_family.lean",
    "Theorems/Thm_WLight_exists_monicRel_j_of_mdifferentiable_levelFraction.lean",
    # --- SET-9 order 2: the level-N structure and sigmaTransport --------------
    # All three are public `Theorems/` wrappers (direct name match); the pin's
    # self-contained `S_` developments are transcribed `private`, so the checker
    # sees only the three headlines in `LevelN.lean`. The
    # `ModularFunction....sigmaTransport` node consumes order 1's
    # `qExpansion_sigmaTransport_package` and
    # `exists_qExpansion_coeff_mem_...` plus SET-8's
    # `exists_mdifferentiable_div_of_monicRel`.
    "Theorems/Thm_WLight_levelN_structure_package.lean",
    "Theorems/Thm_WLight_exists_monicRel_j_K_of_mdifferentiable_frickeQuotient.lean",
    "Theorems/Thm_ModularFunction_exists_mdifferentiable_sigmaTransport_of_frickeQuotient.lean",
    # --- SET-10 order 1: Γ₀-rationality ---------------------------------------
    # All four are public `Theorems/` wrappers (direct name match); the pin's four
    # self-contained `S_` developments are transcribed with every helper
    # `private` inside the pin's own (renamed) namespace, so the checker sees only
    # the four headlines in `Gamma0Rationality.lean`. The cross-edges are the
    # pin's own: SET-7's `weierstrassP_qExpansion_package`, SET-8's
    # `frickeFunction_modularity_package`/`frickeFunction_intBaseChange` and
    # SET-9's five level-fraction / level-N headlines.
    "Theorems/Thm_ModularCurve_exists_ne_zero_forall_mul_qExpansion_coeff_fricke_mem_adjoin.lean",
    "Theorems/Thm_ModularForm_gamma1_qExpansion_coeff_mem_of_frickeRational.lean",
    "Theorems/Thm_ModularCurve_exists_ratCast_qExpansion_comp_smul_of_mem_Gamma0.lean",
    "Theorems/Thm_ModularCurve_exists_mvPolynomial_mul_aeval_fricke_eq_of_qExpansion_coeff_mem.lean",
    # --- SET-10 order 2: bounded-denominator integrality ----------------------
    # The three headlines are public `Theorems/` wrappers; the pin's `S_`
    # developments are transcribed `private`. `Def_ModularCurve_X1.lean` is the
    # source for `ModularCurve.IsIntegralQExp`, a public *definition* that the
    # third wrapper's statement names (the pin's two proof-only X1 helpers are
    # carried `private` in the port, so they are not diffed).
    "Theorems/Thm_ModularCurve_exists_ne_zero_forall_intCast_mul_qExpansion_coeff_of_gamma_invariant.lean",
    "Theorems/Thm_ModularCurve_exists_ratCast_qExpansion_slash_of_mem_Gamma0.lean",
    "Theorems/Thm_ModularCurve_exists_isIntegralQExp_smul_of_ratCast_qExpansion.lean",
    "Definitions/Def_ModularCurve_X1.lean",
    # --- SET-11 order 1: the Γ₁-basis from Galois rationality ----------------
    # All six are public `Theorems/` wrappers (direct name match); the pin's six
    # self-contained `S_` developments are transcribed with every helper
    # `private` in the pin's own inner namespace, so the checker sees only the
    # six headlines in `Gamma1Basis.lean`. The `ModularCurve.IsIntegralQExp`
    # definition is consumed from SET-10 (already listed). Cross-edges are the
    # pin's own: SET-7/8/9 packages, plus SET-10's `Def_ModularCurve_X1`
    # definition for the Eisenstein headline.
    "Theorems/Thm_CuspForm_exists_mul_E4_pow_mul_E6_pow_eq_iff.lean",
    "Theorems/Thm_ModularCurve_exists_gamma1_eisenstein_isIntegralQExp_and_slash_eq.lean",
    "Theorems/Thm_CuspForm_exists_gamma1_frickeRational_sigmaTransport.lean",
    "Theorems/Thm_CuspForm_span_frickeRational_E4_pow_E6_pow_eq_top.lean",
    "Theorems/Thm_CuspForm_exists_gamma1_qCoeff_eq_algEquiv_apply_of_even.lean",
    "Theorems/Thm_CuspForm_exists_gamma1_qCoeff_eq_algEquiv_apply.lean",
    # The two shared analytic helpers were promoted to public in `MonicRel.lean`
    # (`differentiableAt_comp_ofComplex`, `eq_zero_of_mul_eq_zero`); the pin's
    # `S_` files carry them `private`, so they are listed for the
    # promoted-from-pin-private lookup.
    "P2M/Sol/S_CuspForm_exists_mul_E4_pow_mul_E6_pow_eq_iff.lean",
    "P2M/Sol/S_ModularCurve_exists_gamma1_eisenstein_isIntegralQExp_and_slash_eq.lean",
    "P2M/Sol/S_CuspForm_exists_gamma1_frickeRational_sigmaTransport.lean",
    "P2M/Sol/S_CuspForm_span_frickeRational_E4_pow_E6_pow_eq_top.lean",
    "P2M/Sol/S_CuspForm_exists_gamma1_qCoeff_eq_algEquiv_apply_of_even.lean",
    "P2M/Sol/S_CuspForm_exists_gamma1_qCoeff_eq_algEquiv_apply.lean",
    # --- SET-11 order 2: the integral-slash Γ₁-basis -------------------------
    # The four are public `Theorems/` wrappers (direct name match); the pin's
    # four `S_` developments are transcribed `private`, so the checker sees only
    # the four headlines in `Gamma1IntegralBasis.lean`. Inside the module the
    # dependency chain is `adjoin_exp_of_even → adjoin_exp → ratCast →
    # slash_intCast`.
    "Theorems/Thm_CuspForm_exists_basis_gamma1_qCoeff_mem_adjoin_exp_of_even.lean",
    "Theorems/Thm_CuspForm_exists_basis_gamma1_qCoeff_mem_adjoin_exp.lean",
    "Theorems/Thm_CuspForm_exists_basis_gamma1_qCoeff_mem_range_ratCast.lean",
    "Theorems/Thm_CuspForm_exists_basis_gamma1_qCoeff_slash_mem_range_intCast.lean",
    # --- The capstone: the trace lemma and the integral structure ------------
    # The two corollaries are public `Theorems/` wrappers (direct name match).
    # `CuspForm.hasIntegralStructure_of_basis_gamma1` is *ours* (the pin reaches
    # this statement only through the Eichler–Shimura tower), so it is exempted
    # in `OWN_PROOFS`. Every helper above the three headlines is `private`.
    "Theorems/Thm_CuspForm_hasIntegralStructure_of_two_le.lean",
    "Theorems/Thm_CuspForm_hasIntegralStructure_two.lean",
    # --- The congruence-subgroup / level vocabulary (PORTING-Level.md, SET-1) ---
    # These four pin `Definitions/` files have no `Theorems/` wrappers for the L1
    # declarations, so they are the comparable copies (the FFG definition-layer
    # arrangement). They are appended after every existing source so no earlier
    # last-name match can flip.
    "Definitions/Def_CohCarrier_Level.lean",
    "Definitions/Def_CohCarrier_Inst.lean",
    "Definitions/Def_ModularCurve_XH.lean",
    "Definitions/Def_CuspForm_HeckeOperatorFormsGammaH.lean",
    # SET-2 (PORTING-Level.md, l2): the Γ₁ / diamond vocabulary. The pin's public
    # home for the group layer (`CuspForm.Gamma1Hecke`) and the diamond layer
    # (`CuspForm`); it is also the Tier-2 authority for the strengthened
    # `heckeRep_mul` (see `HeckeRepresentatives.lean` and `logs/level-port.md` §2).
    "Definitions/Def_CuspForm_Gamma1HeckeOperators.lean",
    # --- SET-3 (PORTING-Level.md, l3): cosets and the index ψ(N) ---
    # The three `Theorems/` wrappers are the comparable copies for the public
    # headlines. The two `Definitions/` files are the verbatim definition-layer
    # sources. The three `S_` files supply the pin's `private` block for the
    # checker's dotted fallback (the promoted `exists_sl2_int_lift`/`sl2_surj`).
    # Appended last so no earlier last-name match can flip.
    "Theorems/Thm_ModularCurve_Gamma0_index.lean",
    "Theorems/Thm_ModularCurve_card_projectiveLine_zmod.lean",
    "Theorems/Thm_ModularCurve_card_primCosetReps_eq_dedekindPsi.lean",
    "Definitions/Def_ModularCurve_ProjectiveLine.lean",
    "Definitions/Def_ModularCurve_PrimCosetReps.lean",
    "P2M/Sol/S_ModularCurve_Gamma0_index.lean",
    "P2M/Sol/S_ModularCurve_card_projectiveLine_zmod.lean",
    "P2M/Sol/S_ModularCurve_card_primCosetReps_eq_dedekindPsi.lean",
    # --- The Eichler–Shimura period map (TOPIC-period-map-injectivity) ---------
    # The five externals, the nine leaves and the eight analytic-chain nodes are
    # stated verbatim by their `Theorems/` wrappers; the three definition modules
    # are the comparable copies for `BinaryForm` / `CoeffCohomology` /
    # `EichlerIntegral`. The one pin-private declaration the port promotes,
    # `apply_eq_apply_of_hasDerivAt_zero`, is read from its `S_` carrier below.
    # Appended last so no earlier last-name match can flip.
    "Definitions/Def_HeckeEis_BinaryFormRep.lean",
    "Definitions/Def_Gamma0CoeffCohomology.lean",
    "Definitions/Def_HeckeEis_EichlerIntegral.lean",
    "Theorems/Thm_MvPolynomial_IsHomogeneous_iterate_pderiv_eq_zero_of_lt.lean",
    "Theorems/Thm_Complex_exists_hasDerivAt_of_starConvex.lean",
    "Theorems/Thm_UpperHalfPlane_isBoundedAtImInfty_of_hasDerivAt_of_periodic.lean",
    "Theorems/Thm_UpperHalfPlane_apply_add_eq_apply_of_hasDerivAt_of_isZeroAtImInfty.lean",
    "Theorems/Thm_ModularGroup_exists_eq_conj_T_zpow_of_trace_sq_eq_four.lean",
    "Theorems/Thm_HeckeEis_IsEichlerIntegral_add.lean",
    "Theorems/Thm_HeckeEis_IsEichlerIntegral_smul.lean",
    "Theorems/Thm_HeckeEis_IsEichlerIntegral_slash.lean",
    "Theorems/Thm_HeckeEis_IsEichlerIntegral_exists_sub_eq_const.lean",
    "Theorems/Thm_HeckeEis_binaryFormRepSL_neg_one_apply.lean",
    "Theorems/Thm_HeckeEis_coeff_single_one_eq_eval_of_mem_binaryForm.lean",
    "Theorems/Thm_HeckeEis_mem_range_binaryFormRepSL_T_zpow_sub_one.lean",
    "Theorems/Thm_HeckeEis_IsEquivariantPrimitiveWith_cocycle_sub_cocycle_mem_coeffCoboundaries.lean",
    "Theorems/Thm_HeckeEis_jFactor_pow_mul_eval_binaryFormRepSL.lean",
    "Theorems/Thm_HeckeEis_IsEichlerIntegral_hasDerivAt_eval_iterate_pderiv.lean",
    "Theorems/Thm_HeckeEis_IsEichlerIntegral_eq_zero_of_eval_eq_const.lean",
    "Theorems/Thm_HeckeEis_IsEichlerIntegral_isBoundedAtImInfty_eval.lean",
    "Theorems/Thm_HeckeEis_exists_isEichlerIntegral.lean",
    "Theorems/Thm_HeckeEis_isEquivariantPrimitiveWith_of_isEichlerIntegral.lean",
    "Theorems/Thm_HeckeEis_IsEichlerIntegral_vadd_sub_T_zpow_apply_mem_range.lean",
    "Theorems/Thm_HeckeEis_isParabolicCocycle_cocycle_of_isEichlerIntegral.lean",
    "Theorems/Thm_HeckeEis_exists_isEichlerIntegral_isParabolicCocycle.lean",
    "P2M/Sol/S_HeckeEis_IsEichlerIntegral_exists_sub_eq_const.lean",
    # --- Topic 11, the T-side definition layer --------------------------------
    # The T-side substrate. `Definitions/Def_FLTPrelim_Modularity.lean` is already
    # listed above (SET-3 T5 / SET-4 T8), so the `WeierstrassCurve` block of
    # `WeierstrassCurve/Defs/Modularity.lean` is checked without a new entry; the
    # eigenform half it imports is already verified there too. The three algebra
    # theorems are verified against their `Theorems/` wrappers (the pin's `S_`
    # copies are private/namespace-local, and the port keeps every helper
    # `private`, so the wrappers are the comparable copies). Appended last so no
    # earlier last-name match can flip: `LiesOverPrime`, `inertiaSubgroupIn`,
    # `IsFrobeniusAt`, `residual` … occur in other pin modules outside this set.
    "Definitions/Def_FLTPrelim_GaloisRep.lean",
    "Definitions/Def_FLTPrelim_Ramification.lean",
    "Definitions/Def_EllipticCurve_FrobeniusTrace.lean",
    "Definitions/Def_GaloisRep_Residual.lean",
    "Definitions/Def_GaloisRep_ResidualEquiv.lean",
    "Definitions/Def_GaloisRep_Adic.lean",
    "Definitions/Def_GaloisRep_DeformationRingData.lean",
    "Definitions/Def_FLTPrelim_FreyPackage.lean",
    "Definitions/Def_CuspForm_HeckeGaloisRepDatum.lean",
    "Definitions/Def_CuspForm_HeckeLocal.lean",
    "Definitions/Def_Algebra_PatchingDatum.lean",
    "Theorems/Thm_Algebra_finite_maximalSpectrum_and_bijective_localization_of_module_finite.lean",
    "Theorems/Thm_IsAdicComplete_of_module_finite.lean",
    "Theorems/Thm_IsLocalRing_isAdicComplete_of_module_finite.lean",
    # --- T12, SET 1: the surjection half of `R = T` ---------------------------
    # The seven nodes are public `Theorems/` wrappers, so they verify by direct
    # name match. The pin's `PlaceTransitivity` block is `private` in the port
    # (playbook §7.1), so no `S_` carrier is needed for it. The one shared
    # promotion, `ValuationSubring.mem_of_isIntegral` (the pin's `int_mem` and
    # `PlaceTransitivity.coe_mem` written once), has no standalone wrapper and is
    # exempted in `OWN_PROOFS`. Appended last so no earlier last-name match can
    # flip — `charpoly_baseChangeAlong` also names a `ResidualGaloisRep` node in
    # the pin, and `exists_isFrobeniusAt_of_liesOverPrime` / `_rat` have many
    # `S_` copies outside this cone.
    "Theorems/Thm_ValuationSubring_exists_integral_mul_eq_of_liesOverPrime.lean",
    "Theorems/Thm_ValuationSubring_exists_isFrobeniusAt_of_liesOverPrime.lean",
    "Theorems/Thm_ValuationSubring_exists_isFrobeniusAt_rat.lean",
    "Theorems/Thm_GaloisRepAdic_charpoly_baseChangeAlong.lean",
    "Theorems/Thm_GaloisRepAdic_charpoly_eq_of_isEquiv.lean",
    "Theorems/Thm_CuspForm_HeckeGaloisRepDatum_surjective_of_isEquiv_baseChangeAlong.lean",
    "Theorems/Thm_GaloisRep_DeformationRingData_exists_surjective_algHom_of_heckeGaloisRepDatum.lean",
    # --- T12, SET 2: the eigenform-extraction chain ---------------------------
    # The nine nodes are public `Theorems/` wrappers, so they verify by direct
    # name match. `Thm_CuspForm_mem_intLattice_iff.lean` is the carrier of the
    # one public promotion this set makes: `HeckeLattice`'s formerly-private
    # `mem_intLattice_iff` (needed by `linearIndependent_of_mem_intLattice`).
    # The pin's `FrobChareqEngine`/`FrobChareqC2`/`DegeneracyPort` blocks are
    # `private` in the port, so no `S_` carrier is needed for them, and the
    # pin's third `sturmB`/`trunc`/`trunc_injective` is not ported at all (the
    # public `CuspForm.qCoeffTrunc` is reused). Appended last so no earlier
    # last-name match can flip — `exists_degeneracy_Gamma0` also names the
    # *ModularForm* degeneracy node in the pin (not ported here).
    "Theorems/Thm_RingHom_exists_comp_algebraMap_eq_of_isIntegral_of_isAlgClosed.lean",
    "Theorems/Thm_Ideal_exists_ringHom_integralClosure_ker_eq.lean",
    "Theorems/Thm_Module_End_exists_ne_zero_forall_apply_eq_smul_of_ringHom.lean",
    "Theorems/Thm_CuspForm_exists_degeneracy_Gamma0.lean",
    "Theorems/Thm_CuspForm_exists_isNormalizedEigenform_level_mul.lean",
    "Theorems/Thm_CuspForm_exists_isNormalizedEigenform_of_dvd.lean",
    "Theorems/Thm_CuspForm_mem_intLattice_iff.lean",
    "Theorems/Thm_CuspForm_linearIndependent_of_mem_intLattice.lean",
    "Theorems/Thm_CuspForm_HasIntegralStructure_exists_ne_zero_forall_apply_eq_smul.lean",
    "Theorems/Thm_CuspForm_HasIntegralStructure_exists_isNormalizedEigenform_qCoeff_eq.lean",
    # --- T12, SET 3: the conditional capstone ---------------------------------
    # The verbatim node `WeierstrassCurve.isModularModelOfLevel_of_patchingDatum`
    # is **not** ported in SET 3: the port's `…_of_patchingLevel` replaces the
    # patching datum by the three facts `free_and_ker_eq_span` extracts, and is
    # exempted in `OWN_PROOFS`. The wrapper is registered now so that SET 4, which
    # adds the verbatim declaration once the patching cluster lands, needs no
    # further checker edit. Its only last name is unique in the pin, so appending
    # it cannot flip any existing match.
    "Theorems/Thm_WeierstrassCurve_isModularModelOfLevel_of_patchingDatum.lean",
    # --- T12, SET 4: patching descent and freeness -----------------------------
    # The four §0 nodes are public `Theorems/` wrappers, so they verify by direct
    # name match; every helper (the `OnePrime`/`PDescent` blocks) is `private` in
    # the port and so invisible to the checker. The three `MvPowerSeries.*`
    # wrappers are appended because `free_and_ker_eq_span` imports and uses those
    # facts: work order §0 claims the node is independent of SET 5, but the pin's
    # node needs four `MvPowerSeries.*` lemmas. Three are ported in
    # `FLTForHuman/Algebra/MvPowerSeriesRegular.lean` (the pin's duplicated
    # `vanishIdeal` engine is written once there); the fourth,
    # `MvPowerSeries.isNoetherianRing_of_finite`, is now a mathlib instance, so it
    # is *not* ported. All four last names below are unique in the pin, so
    # appending them cannot flip an earlier match.
    "Theorems/Thm_RingHom_bijective_of_surjective_of_smul_eq.lean",
    "Theorems/Thm_Module_Free_of_surjective_of_smul_eq.lean",
    "Theorems/Thm_Module_free_of_isWeaklyRegular_of_isRegular_ofList_eq_maximalIdeal.lean",
    "Theorems/Thm_Algebra_PatchingLevel_free_and_ker_eq_span.lean",
    "Theorems/Thm_MvPowerSeries_isRegular_C_cons_X.lean",
    "Theorems/Thm_MvPowerSeries_ofList_C_cons_X_eq_maximalIdeal.lean",
    "Theorems/Thm_MvPowerSeries_mem_pow_span_X_of_coeff_eq_zero.lean",
    # --- T12, SET 5: the power-series patching algebra -------------------------
    # The three §0 nodes are public `Theorems/` wrappers, so they verify by direct
    # name match. SET 5 extends `MvPowerSeriesRegular.lean` with
    # `residue_comp_C_surjective` and `isAdicComplete_maximalIdeal` (all helpers —
    # `dropVar`, `maximalIdeal_eq_comap`, `mem_span_X_of_constantCoeff_eq_zero`,
    # `maximalIdeal_eq_map_C_sup_span_X`, the `LocalCoeff` block — are `private`),
    # and adds the generic `FLTForHuman/Algebra/AdicCompleteMap.lean`. The pin's
    # `Theorems/Thm_MvPowerSeries_isNoetherianRing_of_finite.lean` is deliberately
    # *not* appended: that fact is mathlib's instance and is not ported. All three
    # last names below are unique in the pin, so appending them cannot flip an
    # earlier match.
    "Theorems/Thm_MvPowerSeries_residue_comp_C_surjective.lean",
    "Theorems/Thm_MvPowerSeries_isAdicComplete_maximalIdeal.lean",
    "Theorems/Thm_IsAdicComplete_map_of_surjective.lean",
    # --- T12, SET 6: the patching construction --------------------------------
    # The one §0 node is a public `Theorems/` wrapper, so it verifies by direct
    # name match. Everything below it in the port module is `private` scaffolding
    # (the pin's ~3,300 lines of carriers and the `FrobDictPC.Limit` construction),
    # so no `S_` carrier is needed and no `OWN_PROOFS` entry arises. Appended last
    # so no earlier last-name match can flip.
    "Theorems/Thm_Algebra_PatchingDatum_nonempty_patchingLevel_bot.lean",
    # --- T12, SET 7: the patching exit and the verbatim assembly ---------------
    # The exit's wrapper is a public `Theorems/` node, so it verifies by direct
    # name match; the verbatim `…_of_patchingDatum` wrapper was already registered
    # in SET 3, so the assembly needs no new `SOURCES` entry. Appended last so no
    # earlier last-name match can flip.
    "Theorems/Thm_Algebra_PatchingDatum_bijective_and_free_of_surjective.lean",
    # --- Sources for the shared homes created by the WeightOne rectification ---
    # These carry the pin-private originals of the declarations lifted into
    # `ModularForms/DiscPow.lean`, `QExpansionCoeff.lean`, `WeightOne/Defs/*`
    # and `WeightOne/Fricke.lean`; without them the promoted-from-pin-private
    # lookup reports the homes' public declarations missing.
    "P2M/Sol/S_CuspForm_TWLevel_exists_heckeEquivariant_dual_ML_range_eq_idempotent_baseChange_tateModule_jH.lean",
    "P2M/Sol/S_CuspForm_exists_basis_gamma1_qCoeff_mem_adjoin_exp_of_even.lean",
    "P2M/Sol/S_CuspForm_exists_basis_gamma1_qCoeff_mem_range_ratCast.lean",
    "P2M/Sol/S_CuspForm_exists_gamma1_frickeRational_sigmaTransport.lean",
    "P2M/Sol/S_CuspForm_exists_gamma1_qCoeff_eq_algEquiv_apply_of_even.lean",
    "P2M/Sol/S_CuspForm_exists_isPrimitiveForm_basis_gammaH_and_heckeTLinH_and_diamondLinH_and_heckeULinH_apply.lean",
    "P2M/Sol/S_CuspForm_exists_kaehlerDifferential_diffQExp_eq_ofPowerSeries_and_forall_valuationSubring_of_isIntegralQExp.lean",
    "P2M/Sol/S_CuspForm_exists_mul_E4_pow_mul_E6_pow_eq_iff.lean",
    "P2M/Sol/S_CuspForm_heckeTLinH_heckeULinH_diamondLinH_comm.lean",
    "P2M/Sol/S_CuspForm_nonempty_basis_fin_one_gammaH_and_finrank_eigenspace_eq_one.lean",
    "P2M/Sol/S_CuspForm_span_frickeRational_E4_pow_E6_pow_eq_top.lean",
    "P2M/Sol/S_ModularCurve_FullLevel_exists_ratCast_slash_conjElemN_eq_sum_exp_pow_smul_of_mem_Gamma0.lean",
    "P2M/Sol/S_ModularCurve_FullLevel_exists_ratCast_slash_conjElemN_eq_sum_exp_pow_smul_of_mem_Gamma0_of_eq_levelH_inf_ker.lean",
    "P2M/Sol/S_ModularCurve_FullLevel_exists_ratCast_slash_conjElem_eq_sum_exp_pow_smul_of_mem_Gamma0.lean",
    "P2M/Sol/S_ModularCurve_JOne_degeneracyPullbackInputs.lean",
    "P2M/Sol/S_ModularCurve_SiegelUnit_exists_modularForm_gamma1_isIntegralQExp_coeff_eq_one_and_forall_slash_isIntegral.lean",
    "P2M/Sol/S_ModularCurve_SiegelUnit_isIntegral_qExpansion_slash_S_coeff_of_coe_eq_prod_siegelFun_pow_mul_discriminant_pow.lean",
    "P2M/Sol/S_ModularCurve_XOneP_comp_alpha_eq_beta_and_comp_beta_eq_alpha_comp_diamondAutBar_of_atkinLehnerSlash_p.lean",
    "P2M/Sol/S_ModularCurve_apply_eq_qExpand_jqModC_of_coe_eq_qExpand_jqModC_of_cuspExpansion_S.lean",
    "P2M/Sol/S_ModularCurve_exists_algHom_igusaFunctionFieldX1C_apply_eq_jqNModC_and_apply_eq_jqModC.lean",
    "P2M/Sol/S_ModularCurve_exists_algHom_qExpFunctionFieldC_gammaH_coe_eq_div_of_map_eq_smul_qExpansion_slash.lean",
    "P2M/Sol/S_ModularCurve_exists_algHom_qExpFunctionFieldC_gammaH_cuspZero_apply_eq_and_apply_div_pow_eq.lean",
    "P2M/Sol/S_ModularCurve_exists_algHom_qExpFunctionFieldC_gammaH_eq_slot_and_diamondPullbackModL_eq_qTwist.lean",
    "P2M/Sol/S_ModularCurve_exists_algHom_slot_mul_qExpansion_slash_eq.lean",
    "P2M/Sol/S_ModularCurve_exists_coeffMap_diffQExpBar_eq_qExpansion.lean",
    "P2M/Sol/S_ModularCurve_exists_coeffMap_qExpansionDiffAlong_laurentBaseChange_qExpFunctionFieldC_eq_qExpansion.lean",
    "P2M/Sol/S_ModularCurve_exists_gamma1_peaked_auxiliary_form.lean",
    "P2M/Sol/S_ModularCurve_exists_isIntegralQExp_smul_atkinLehnerSlash_of_even.lean",
    "P2M/Sol/S_ModularCurve_exists_isIntegralQExp_smul_of_ratCast_qExpansion.lean",
    "P2M/Sol/S_ModularCurve_exists_isIntegral_level_pow_mul_qExpansion_slash_coeff.lean",
    "P2M/Sol/S_ModularCurve_exists_isIntegral_level_pow_mul_qExpansion_slash_fricke_coeff.lean",
    "P2M/Sol/S_ModularCurve_exists_mvPolynomial_mul_aeval_fricke_eq_of_qExpansion_coeff_mem.lean",
    "P2M/Sol/S_ModularCurve_exists_ne_zero_forall_intCast_mul_qExpansion_coeff_of_gamma_invariant.lean",
    "P2M/Sol/S_ModularCurve_exists_ne_zero_forall_mul_qExpansion_coeff_fricke_mem_adjoin.lean",
    "P2M/Sol/S_ModularCurve_exists_qExpansion_S_smul_eq_and_conj_eq_of_ratCast_qExpansion.lean",
    "P2M/Sol/S_ModularCurve_exists_qExpansion_comp_smul_coeff_eq_and_comp_mul_smul_coeff_eq_apply_of_gamma1_mul.lean",
    "P2M/Sol/S_ModularCurve_exists_qExpansion_comp_smul_coeff_eq_and_eq_apply_of_gamma_invariant.lean",
    "P2M/Sol/S_ModularCurve_exists_qExpansion_slash_coeff_eq_and_eq_apply_of_gamma_of_even.lean",
    "P2M/Sol/S_ModularCurve_exists_qExpansion_slash_fricke_eq_and_conj_eq_slash_gamma0.lean",
    "P2M/Sol/S_ModularCurve_exists_ratCast_qExpansion_comp_smul_of_mem_Gamma0.lean",
    "P2M/Sol/S_ModularCurve_exists_ratCast_qExpansion_comp_smul_of_mem_Gamma0_of_dvd.lean",
    "P2M/Sol/S_ModularCurve_exists_ratCast_qExpansion_slash_of_mem_Gamma0.lean",
    "P2M/Sol/S_ModularCurve_finrank_adjoin_jqNModC_mul_igusaFunctionFieldX1C_eq_of_dvd.lean",
    "P2M/Sol/S_ModularCurve_isIntegralElem_div_delta_pow_and_div_eisenstein4_pow_of_forall_qExpansion_slash_isIntegral.lean",
    "P2M/Sol/S_ModularCurve_isIntegralElem_div_delta_pow_and_div_eisenstein4_pow_of_isIntegralQExp_gamma1.lean",
    "P2M/Sol/S_ModularCurve_mem_laurentBaseChange_of_coeffMap_eq_qExpansion_div.lean",
    "P2M/Sol/S_ModularCurve_qExpansion_coeff_comp_smul_mem_adjoin_exp_of_gamma1_mul.lean",
    "P2M/Sol/S_ModularForm_exists_basis_gamma1_qCoeff_mem_adjoin_exp_of_even.lean",
    "P2M/Sol/S_ModularForm_exists_basis_gamma1_qCoeff_mem_range_ratCast.lean",
    "P2M/Sol/S_ModularForm_exists_gamma0_forall_tendsto_slash_atImInfty_of_three_le.lean",
    "P2M/Sol/S_ModularForm_exists_gamma1_frickeRational_sigmaTransport.lean",
    "P2M/Sol/S_ModularForm_exists_gamma1_qCoeff_eq_algEquiv_apply_of_even.lean",
    "P2M/Sol/S_ModularForm_exists_gamma_weight_two_forall_tendsto_slash_atImInfty.lean",
    "P2M/Sol/S_ModularForm_exists_mul_E4_pow_mul_E6_pow_eq_iff.lean",
    "P2M/Sol/S_ModularForm_gamma1_qExpansion_coeff_mem_of_frickeRational.lean",
    "P2M/Sol/S_ModularForm_span_frickeRational_E4_pow_E6_pow_eq_top.lean",
    "P2M/Sol/S_ModularForm_weierstrassP_torsion_qExpansion_package.lean",
    "P2M/Sol/S_ModularFunction_exists_mdifferentiable_sigmaTransport_of_frickeQuotient.lean",
    "P2M/Sol/S_UpperHalfPlane_linearIndependent_complex_of_qExpansion_coeff_mem.lean",
    "P2M/Sol/S_WLight_exists_levelFraction_of_stable_family.lean",
    "P2M/Sol/S_WLight_exists_monicRel_j_K_of_mdifferentiable_frickeQuotient.lean",
    "P2M/Sol/S_WLight_exists_monicRel_j_of_mdifferentiable_levelFraction.lean",
    "P2M/Sol/S_WLight_exists_qExpansion_coeff_mem_of_mdifferentiable_levelFraction.lean",
    "P2M/Sol/S_WLight_frickeFunction_intBaseChange.lean",
    "P2M/Sol/S_WLight_frickeFunction_modularity_package.lean",
    "P2M/Sol/S_WLight_frickeFunction_orbit_package.lean",
    "P2M/Sol/S_WLight_isBoundedAtImInfty_iff_qExpansion_coeff_lt.lean",
    "P2M/Sol/S_WLight_isZeroAtImInfty_mul_disc_iff_qExpansion_coeff_le.lean",
    "P2M/Sol/S_WLight_levelN_structure_package.lean",
    "P2M/Sol/S_WLight_levelOne_hauptmodul_package.lean",
    "P2M/Sol/S_WLight_qExpansion_sigmaTransport_package.lean",
    "P2M/Sol/S_WLight_weierstrassP_qExpansion_package.lean",
    # --- Phase D (Deligne–Serre weight-one definition layer, D0) ---
    # `Def_ModularForm_HeckeOperator`, `Def_FLTPrelim_Ramification` and
    # `Def_FLTPrelim_Modularity` are already listed above; D0 adds the seven
    # definition modules below. Appended last so no earlier last-name match flips.
    "Definitions/Def_Deformations_MatrixRepresentation.lean",
    "Definitions/Def_EisensteinSeries_WeierstrassZeta.lean",
    "Definitions/Def_FieldTheory_RatAlgClosureGalois.lean",
    "Definitions/Def_Gamma0Away.lean",
    "Definitions/Def_IharaIota.lean",
    "Definitions/Def_RepTheory_BrauerNesbitt_TraceCharZero.lean",
    "Definitions/Def_TaylorWiles_Primes.lean",
    # --- Phase D, D1 ---
    "Definitions/Def_CuspForm_Gamma1HeckeOperators.lean",
    "Definitions/Def_CuspForm_PrimitiveFormGamma1.lean",
    "Definitions/Def_FrobeniusDensity_DegOneAsymptotic.lean",
    "Definitions/Def_IharaAmalgam.lean",
    # --- Phase D, D2 ---
    "Definitions/Def_FrobeniusDensity_BadPrimes.lean",
    "Definitions/Def_GaloisRep_FrobeniusPowerDense.lean",
    "Definitions/Def_IharaAmalgamMap.lean",
    # --- Phase D, D3 ---
    "Definitions/Def_FrobeniusDensity_PrimeSums.lean",
    # --- Phase H1 (Deligne–Serre homes) ---
    # GR home: the pin copies of `finite_range_of_factorsThroughFiniteLevel`.
    "P2M/Sol/S_DeligneSerre_exists_galoisRep_complex_trace_frobenius_eq_of_forall_residual.lean",
    "P2M/Sol/S_GaloisRep_exists_conj_eq_of_charpoly_frobenius_eq_of_galoisFactorsThroughFiniteLevel.lean",
    # EIS home: the pin copies of the Eisenstein cotangent prelude.
    "P2M/Sol/S_EisensteinSeries_hasSum_weierstrassZeta_sub_mul_G2.lean",
    "P2M/Sol/S_EisensteinSeries_isBoundedAtImInfty_eisensteinG1_and_hasSum_eisensteinG1.lean",
    "P2M/Sol/S_EisensteinSeries_weierstrassZeta_add_one_and_add_tau_and_smul.lean",
    "P2M/Sol/S_EisensteinSeries_eisensteinG1_apply_smul_and_eisensteinG1_add.lean",
    # FD home: the pin copies of the Frobenius-density prelude.
    "P2M/Sol/S_FrobeniusDensity_sum_moebius_mul_pos.lean",
    "P2M/Sol/S_FrobeniusDensity_weight_eq.lean",
    "P2M/Sol/S_FrobeniusDensity_idealSum_ne_top.lean",
    "P2M/Sol/S_FrobeniusDensity_tendsto_sub_one_mul_idealSum_test.lean",
    "P2M/Sol/S_FrobeniusDensity_ncard_degreeOne_primesOver_under.lean",
    "P2M/Sol/S_FrobeniusDensity_stabilizer_eq_zpowers_arithFrobAt.lean",
    "P2M/Sol/S_FrobeniusDensity_degOneSum_add_log_isBigO.lean",
    "P2M/Sol/S_FrobeniusDensity_primeSum_toReal_add_log_isBigO.lean",
    "P2M/Sol/S_FrobeniusDensity_summable_degOne_term.lean",
    # HK home: the pin copies of the Hecke/cusp prelude.
    "P2M/Sol/S_CuspForm_qCoeff_heckeTLinOne.lean",
    "P2M/Sol/S_CuspForm_slash_eq_dirichlet_smul_of_qCoeff_hecke_eigen.lean",
    "P2M/Sol/S_DeligneSerre_exists_subalgebra_qCoeff_mem_forall_ringHom_exists_qCoeff_eq_of_weightOne_hecke_eigen.lean",
    # --- Phase H2 (clash reconciliation) ---
    # The pin's Γ₁ copy of the `HeckeGamma1` block: it carries the authoritative
    # `heckeRep_mul` Γ₁ statement (no extra `g 1 1` factor), the `isUnit_wt`
    # statement without `hp : p.Prime`, and the Γ₁-indexed copies of the
    # Hecke-matrix lemmas. Appended last so no earlier last-name match flips.
    "P2M/Sol/S_ModularForm_heckeU_add_slash_heckeDiagMatrix_slash_eq_of_mem_Gamma1.lean",
    # --- S1 (Deligne–Serre weight-one Eisenstein set) ---
    # The five pin solution files, in the pin's import order, each preceded by its
    # `Theorems/` wrapper: the wrapper carries the public target's name (the
    # `S_` file calls it `solution`), so it is the comparable copy for the
    # target, while the `S_` file supplies the intermediate declarations.
    # Appended last so no earlier last-name match can flip.
    "Theorems/Thm_EisensteinSeries_hasSum_weierstrassZeta_sub_mul_G2.lean",
    "P2M/Sol/S_EisensteinSeries_hasSum_weierstrassZeta_sub_mul_G2.lean",
    "Theorems/Thm_EisensteinSeries_weierstrassZeta_add_one_and_add_tau_and_smul.lean",
    "P2M/Sol/S_EisensteinSeries_weierstrassZeta_add_one_and_add_tau_and_smul.lean",
    "Theorems/Thm_EisensteinSeries_eisensteinG1_apply_smul_and_eisensteinG1_add.lean",
    "P2M/Sol/S_EisensteinSeries_eisensteinG1_apply_smul_and_eisensteinG1_add.lean",
    "Theorems/Thm_EisensteinSeries_isBoundedAtImInfty_eisensteinG1_and_hasSum_eisensteinG1.lean",
    "P2M/Sol/S_EisensteinSeries_isBoundedAtImInfty_eisensteinG1_and_hasSum_eisensteinG1.lean",
    "Theorems/Thm_ModularForm_exists_weightOne_eisenstein_qCoeff_eq_of_isPrimitive_of_odd.lean",
    "P2M/Sol/S_ModularForm_exists_weightOne_eisenstein_qCoeff_eq_of_isPrimitive_of_odd.lean",
    # --- S2 (Deligne–Serre Hecke / Γ₁ vanishing and nebentypus set) ---
    # The nine pin solution files, each preceded by its `Theorems/` wrapper: the
    # wrapper carries the public target's name (the `S_` file calls it
    # `solution`), so it is the comparable copy for the target, while the `S_`
    # file supplies the intermediate declarations. Three of the `S_` files are
    # already registered by the H1/H2 blocks above; they are repeated inside the
    # pairs to keep the set self-contained (extra candidates cannot flip an
    # earlier match). Appended last so no earlier last-name match can flip.
    "Theorems/Thm_ModularForm_heckeU_add_slash_heckeDiagMatrix_slash_eq_of_mem_Gamma1.lean",
    "P2M/Sol/S_ModularForm_heckeU_add_slash_heckeDiagMatrix_slash_eq_of_mem_Gamma1.lean",
    "Theorems/Thm_CuspForm_qCoeff_heckeTLinOne.lean",
    "P2M/Sol/S_CuspForm_qCoeff_heckeTLinOne.lean",
    "Theorems/Thm_CuspForm_heckeTLinOne_slashOfMemGamma0.lean",
    "P2M/Sol/S_CuspForm_heckeTLinOne_slashOfMemGamma0.lean",
    "Theorems/Thm_CuspForm_HasNebentypus_diamondLinOne_apply_eq_smul.lean",
    "P2M/Sol/S_CuspForm_HasNebentypus_diamondLinOne_apply_eq_smul.lean",
    "Theorems/Thm_CuspForm_vadd_inv_pow_eq_of_slash_heckeDiagMatrix_invariant.lean",
    "P2M/Sol/S_CuspForm_vadd_inv_pow_eq_of_slash_heckeDiagMatrix_invariant.lean",
    "Theorems/Thm_CuspForm_eq_zero_of_forall_vadd_inv_pow_eq.lean",
    "P2M/Sol/S_CuspForm_eq_zero_of_forall_vadd_inv_pow_eq.lean",
    "Theorems/Thm_CuspForm_eq_zero_of_slash_heckeDiagMatrix_slash_eq_of_mem_Gamma1.lean",
    "P2M/Sol/S_CuspForm_eq_zero_of_slash_heckeDiagMatrix_slash_eq_of_mem_Gamma1.lean",
    "Theorems/Thm_CuspForm_slash_eq_dirichlet_smul_of_qCoeff_hecke_eigen.lean",
    "P2M/Sol/S_CuspForm_slash_eq_dirichlet_smul_of_qCoeff_hecke_eigen.lean",
    "Theorems/Thm_Ihara_amalgamToGamma0Away_surjective.lean",
    "P2M/Sol/S_Ihara_amalgamToGamma0Away_surjective.lean",
    # --- S3 (Deligne–Serre relèvement and weight-one → weight-two lifting, two
    # nodes) ---
    # Each pin `S_` file preceded by its `Theorems/` wrapper: the wrapper carries
    # the public target's name (the `S_` file calls it `solution`), while the `S_`
    # file supplies the intermediates (`locKer`, `adjoinRoot'` are the only two
    # public ones ported besides the targets). Appended last so no earlier
    # last-name match can flip.
    "Theorems/Thm_DeligneSerre_exists_hecke_eigen_reduction_eq_of_qCoeff_hecke_congr.lean",
    "P2M/Sol/S_DeligneSerre_exists_hecke_eigen_reduction_eq_of_qCoeff_hecke_congr.lean",
    "Theorems/Thm_DeligneSerre_exists_weightTwo_hecke_eigen_reduction_eq_of_weightOne_hecke_eigen.lean",
    "P2M/Sol/S_DeligneSerre_exists_weightTwo_hecke_eigen_reduction_eq_of_weightOne_hecke_eigen.lean",
    # --- S4 (Deligne–Serre coefficient ring and Galois conjugation, six nodes) ---
    # Each pin `S_` file preceded by its `Theorems/` wrapper. Five of the six are
    # generic algebra; the wrappers carry the public target names (the `S_` files
    # call them `solution`), and the `S_` files supply any public intermediates.
    # Appended last so no earlier last-name match can flip.
    "Theorems/Thm_Module_Basis_repr_mem_range_ratCast_of_forall_dual.lean",
    "P2M/Sol/S_Module_Basis_repr_mem_range_ratCast_of_forall_dual.lean",
    "Theorems/Thm_Module_Basis_exists_forall_apply_eq_ringHom_smul_of_repr_mem_range_ratCast.lean",
    "P2M/Sol/S_Module_Basis_exists_forall_apply_eq_ringHom_smul_of_repr_mem_range_ratCast.lean",
    "Theorems/Thm_Submodule_moduleFinite_adjoin_eigenvalues_of_map_le_of_span_eq_top.lean",
    "P2M/Sol/S_Submodule_moduleFinite_adjoin_eigenvalues_of_map_le_of_span_eq_top.lean",
    "Theorems/Thm_integralClosure_exists_complex_ringEquiv_apply_eq.lean",
    "P2M/Sol/S_integralClosure_exists_complex_ringEquiv_apply_eq.lean",
    "Theorems/Thm_DeligneSerre_exists_eigenvector_of_mem_minimalPrimes_of_faithfulSMul.lean",
    "P2M/Sol/S_DeligneSerre_exists_eigenvector_of_mem_minimalPrimes_of_faithfulSMul.lean",
    "Theorems/Thm_DeligneSerre_exists_subalgebra_qCoeff_mem_forall_ringHom_exists_qCoeff_eq_of_weightOne_hecke_eigen.lean",
    "P2M/Sol/S_DeligneSerre_exists_subalgebra_qCoeff_mem_forall_ringHom_exists_qCoeff_eq_of_weightOne_hecke_eigen.lean",
    # --- S5 (Deligne–Serre semisimple descent of a reducible residual
    # representation, one node) ---
    # The wrapper carries the public target name (the `S_` file calls it `main`);
    # the `S_` file also supplies the three engines the port homes publicly in
    # `FLTForHuman/GaloisRep/SemisimpleDescent.lean` for the deferred
    # density-dependent half: `charpoly_fin_two`,
    # `finrank_eq_one_of_ne_bot_of_ne_top` and
    # `isSemisimpleRepresentation_of_forall_exists_isCompl`. Appended last so no
    # earlier last-name match can flip.
    "Theorems/Thm_DeligneSerre_exists_isSemisimpleRepresentation_charpoly_map_eq_of_add_mem_range_of_mul_mem_range.lean",
    "P2M/Sol/S_DeligneSerre_exists_isSemisimpleRepresentation_charpoly_map_eq_of_add_mem_range_of_mul_mem_range.lean",
    # --- S7-I (Deligne–Serre Frobenius density, place / Frobenius vocabulary) ---
    # Four targets extend the already-listed `NumberTheory/FrobeniusAtPlace.lean`
    # (nodes 1–4). Each pin `S_` file is preceded by its `Theorems/` wrapper: the
    # wrapper carries the public target name (the `S_` file calls it `solution`),
    # while the `S_` file supplies the pin's private `IsLoc` prelude. Appended last
    # so no earlier last-name match can flip.
    "Theorems/Thm_ValuationSubring_isFrobeniusAt_of_forall_smul_sub_pow_mem.lean",
    "P2M/Sol/S_ValuationSubring_isFrobeniusAt_of_forall_smul_sub_pow_mem.lean",
    "Theorems/Thm_ValuationSubring_exists_liesOverPrime_algebraicClosure_rat.lean",
    "P2M/Sol/S_ValuationSubring_exists_liesOverPrime_algebraicClosure_rat.lean",
    "Theorems/Thm_ValuationSubring_exists_isFrobeniusAt_of_liesOverPrime_algebraicClosure_rat.lean",
    "P2M/Sol/S_ValuationSubring_exists_isFrobeniusAt_of_liesOverPrime_algebraicClosure_rat.lean",
    "Theorems/Thm_ValuationSubring_exists_liesOverPrime_isFrobeniusAt_ratAlgClosure.lean",
    "P2M/Sol/S_ValuationSubring_exists_liesOverPrime_isFrobeniusAt_ratAlgClosure.lean",
    "Theorems/Thm_NumberField_exists_valuationSubring_eq_localization.lean",
    "P2M/Sol/S_NumberField_exists_valuationSubring_eq_localization.lean",
    "Theorems/Thm_NumberField_exists_isFrobenius_lift_arithFrobAt.lean",
    "P2M/Sol/S_NumberField_exists_isFrobenius_lift_arithFrobAt.lean",
    "Theorems/Thm_IsOpen_exists_numberField_ker_restrictNormalHom_le.lean",
    "P2M/Sol/S_IsOpen_exists_numberField_ker_restrictNormalHom_le.lean",
    # --- S7-II (Deligne–Serre Frobenius density, zeta / coset / Möbius counting
    # chain to `degOneAsymptotic`) ---
    # Each pin `S_` file is preceded by its `Theorems/` wrapper: the wrapper
    # carries the public target name (the `S_` file calls it `solution`), while
    # the `S_` file supplies the pin's private prelude. Several of these `S_`
    # files were already listed by phase H1 for the shared prelude; those are not
    # repeated. Appended last so no earlier last-name match can flip.
    "Theorems/Thm_ArithmeticFunction_sum_moebius_filter_dvd.lean",
    "P2M/Sol/S_ArithmeticFunction_sum_moebius_filter_dvd.lean",
    "Theorems/Thm_FrobeniusDensity_sum_moebius_mul_pos.lean",
    "Theorems/Thm_FrobeniusDensity_weight_eq.lean",
    "Theorems/Thm_FrobeniusDensity_idealSum_ne_top.lean",
    "Theorems/Thm_FrobeniusDensity_tendsto_sub_one_mul_idealSum_test.lean",
    "Theorems/Thm_FrobeniusDensity_summable_degOne_term.lean",
    "Theorems/Thm_FrobeniusDensity_stabilizer_eq_zpowers_arithFrobAt.lean",
    "Theorems/Thm_FrobeniusDensity_ncard_degreeOne_primesOver_under.lean",
    "Theorems/Thm_FrobeniusDensity_ncard_degreeOne_primesOver_eq_ncard_frobFixed.lean",
    "P2M/Sol/S_FrobeniusDensity_ncard_degreeOne_primesOver_eq_ncard_frobFixed.lean",
    "Theorems/Thm_FrobeniusDensity_primeSum_eq_degOneSum_add.lean",
    "P2M/Sol/S_FrobeniusDensity_primeSum_eq_degOneSum_add.lean",
    "Theorems/Thm_FrobeniusDensity_primeSum_toReal_add_log_isBigO.lean",
    "Theorems/Thm_FrobeniusDensity_degOneSum_add_log_isBigO.lean",
    "Theorems/Thm_FrobeniusDensity_degOneAsymptotic.lean",
    "P2M/Sol/S_FrobeniusDensity_degOneAsymptotic.lean",
    # --- S7-III (Deligne–Serre Frobenius density, the density statement and its
    # applications) plus the S7-I tail node ---
    # Each pin `S_` file is preceded by its `Theorems/` wrapper: the wrapper
    # carries the public target name (the `S_` file calls it `solution`), while
    # the `S_` file supplies the pin's helpers. `exists_frobenius_conj_pow_of_statement`
    # contributes the public `C6P1CFD` block (`galoisLevel`, `le_galoisLevel`,
    # `exists_pow_pow_eq`) and the tail S_ file contributes its seven public
    # helpers (`exists_int_ne_zero_eq_mul` … `infinite_setOf_degOneCount_ne_zero`),
    # all transcribed at the pinned names. Appended last so no earlier last-name
    # match can flip.
    "Theorems/Thm_FrobeniusDensity_statement_of_degOneAsymptotic.lean",
    "P2M/Sol/S_FrobeniusDensity_statement_of_degOneAsymptotic.lean",
    "Theorems/Thm_FrobeniusDensity_statement.lean",
    "P2M/Sol/S_FrobeniusDensity_statement.lean",
    "Theorems/Thm_FrobeniusDensity_exists_frobenius_conj_pow_of_statement.lean",
    "P2M/Sol/S_FrobeniusDensity_exists_frobenius_conj_pow_of_statement.lean",
    "Theorems/Thm_FrobeniusDensity_frobeniusPowerDense_of_le_ker.lean",
    "P2M/Sol/S_FrobeniusDensity_frobeniusPowerDense_of_le_ker.lean",
    "Theorems/Thm_FrobeniusDensity_ncard_conj_gen_ne_zero_iff.lean",
    "P2M/Sol/S_FrobeniusDensity_ncard_conj_gen_ne_zero_iff.lean",
    "Theorems/Thm_Subgroup_exists_prime_isFrobeniusAt_conj_pow_mem_of_isOpen.lean",
    "P2M/Sol/S_Subgroup_exists_prime_isFrobeniusAt_conj_pow_mem_of_isOpen.lean",
    "Theorems/Thm_CommRing_infinite_setOf_prime_nonempty_ringHom_zmod_of_moduleFinite_int.lean",
    "P2M/Sol/S_CommRing_infinite_setOf_prime_nonempty_ringHom_zmod_of_moduleFinite_int.lean",
    # --- S6a (Deligne–Serre representation lifting): the mod-`ℓ` → char-0 lift
    # with matching characteristic polynomials, and its Witt-vector private
    # closure. All of the pin's helpers are `private` in the port, so only the
    # wrapper's single target declaration is comparable. Appended last so no
    # earlier last-name match can flip.
    "Theorems/Thm_Representation_exists_monoidHom_complex_charpoly_map_eq_of_not_dvd_natCard.lean",
    "P2M/Sol/S_Representation_exists_monoidHom_complex_charpoly_map_eq_of_not_dvd_natCard.lean",
    # --- S6b (character determines a finite-image representation up to
    # conjugacy). The pin's helpers are `private` in the port, so the wrapper is
    # the only comparable copy. Appended last so no earlier last-name match can
    # flip.
    "Theorems/Thm_Representation_exists_conj_eq_of_charpoly_eq_of_finite_range.lean",
    "P2M/Sol/S_Representation_exists_conj_eq_of_charpoly_eq_of_finite_range.lean",
    # --- S6c (equal Frobenius charpolys imply global conjugacy). Helpers are
    # `private` in the port; the wrapper is the comparable copy. Appended last so
    # no earlier last-name match can flip.
    "Theorems/Thm_GaloisRep_exists_conj_eq_of_charpoly_frobenius_eq_of_galoisFactorsThroughFiniteLevel.lean",
    "P2M/Sol/S_GaloisRep_exists_conj_eq_of_charpoly_frobenius_eq_of_galoisFactorsThroughFiniteLevel.lean",
    # --- S8 (the complex-trace assembly, the capstone). The pin's helpers are
    # `private` in the port, so the wrapper is the only comparable copy of the
    # target; the pin `S_` file itself is already registered above (the H1 block
    # lists it for the `finite_range_of_factorsThroughFiniteLevel` prelude), so it
    # is not repeated. Appended last so no earlier last-name match can flip.
    "Theorems/Thm_DeligneSerre_exists_galoisRep_complex_trace_frobenius_eq_of_forall_residual.lean",
    # --- D (the Riemann–Roch definition layer). Seven pin `Definitions/` files
    # with no `Theorems/` wrappers: the `Definitions/` files are the authority.
    # `Def_ModularCurve_CanonicalDivisor` first, since the pin's
    # `Def_AlgebraicCurve_CanonicalDivisor` imports it (the port merges the two
    # into one module). Appended last so no earlier last-name match can flip.
    "Definitions/Def_ModularCurve_CanonicalDivisor.lean",
    "Definitions/Def_AlgebraicCurve_CanonicalDivisor.lean",
    "Definitions/Def_AlgebraicCurve_Repartitions.lean",
    "Definitions/Def_AlgebraicCurve_AdelicIndex.lean",
    "Definitions/Def_AlgebraicCurve_IsCurveOver.lean",
    "Definitions/Def_AlgebraicCurve_RiemannRochRows.lean",
    "Definitions/Def_AlgebraicCurve_PoleDivisorPackage.lean",
    # --- H1a (the adelic-index / `ell` prelude and the index targets). The five
    # `Theorems/` wrappers come first: they are the interface copies whose binders
    # the port's public targets spell. The `S_` file then supplies the shared
    # prelude's declarations, in its own declaration order. Appended last so no
    # earlier last-name match can flip.
    "Theorems/Thm_AlgebraicCurve_indexOfSpecialty_eq_of_genusReached.lean",
    "Theorems/Thm_AlgebraicCurve_indexOfSpecialty_eq_zero_of_genusReached.lean",
    "Theorems/Thm_AlgebraicCurve_RiemannGenusReachedAt_eq_of_ge.lean",
    "Theorems/Thm_AlgebraicCurve_omegaSpace_finite_of_genusReached.lean",
    "Theorems/Thm_AlgebraicCurve_exists_genus_riemannIndex_of_stichtenothGenusExists.lean",
    "P2M/Sol/S_AlgebraicCurve_exists_genus_riemannIndex_of_stichtenothGenusExists.lean",
    # --- R (refactor): the 15th H1a-adjacent helper target the H2 assembly reached,
    # promoted into `Genus/Index.lean`. The wrapper comes first (the interface copy
    # whose binders the port's public target spells); the `S_` file carries the
    # `solution` body.
    "Theorems/Thm_AlgebraicCurve_exists_indexOfSpecialty_nsmul_single_eq_zero_of_genusReached.lean",
    "P2M/Sol/S_AlgebraicCurve_exists_indexOfSpecialty_nsmul_single_eq_zero_of_genusReached.lean",
    # --- H1b (the Stichtenoth genus-existence tower). The two `Theorems/` wrappers
    # come first: they are the interface copies whose binders the port's two public
    # targets spell. The `S_` file then supplies the shared tower. Appended last so
    # no earlier last-name match can flip.
    "Theorems/Thm_AlgebraicCurve_RationalFunctionField_stichtenothGenusExists.lean",
    "Theorems/Thm_AlgebraicCurve_RationalFunctionField_finiteDimensional_lSpace_zero_of_constantsAreBase.lean",
    "P2M/Sol/S_AlgebraicCurve_RationalFunctionField_stichtenothGenusExists.lean",
    # --- R (refactor): `IsCurveOver.exists_separating_transcendental`, promoted into
    # `AlgebraicCurve/IsCurveOver/SeparatingTranscendental.lean`. The wrapper comes
    # first (the interface copy whose binders the port's public target spells); the
    # `S_` file supplies the pin-public support lemmas (`kaehlerAdjoinBasis`,
    # `finrank_kaehler_eq_card_of_separating`, the `trdeg` chain) in declaration order.
    "Theorems/Thm_AlgebraicCurve_IsCurveOver_exists_separating_transcendental.lean",
    "P2M/Sol/S_AlgebraicCurve_IsCurveOver_exists_separating_transcendental.lean",
    # --- H2 (assembly, the Weil canonical divisor, and the `H¹` identification).
    # Each `Theorems/` wrapper comes first: it is the interface copy whose binders
    # the port's public target spells (the `S_` file calls it `solution`).  The `S_`
    # file then supplies the shared prelude.  The curve-level helper
    # `stichtenothGenusExists_of_isCurveOver` (H2 re-provisioned it `private`;
    # the refactor round promoted it from the now-public
    # `IsCurveOver.exists_separating_transcendental`) is wired here with its own
    # wrapper + `S_` file, wrapper first.  Appended last so no earlier last-name
    # match can flip.
    "Theorems/Thm_AlgebraicCurve_stichtenothGenusExists_of_isCurveOver.lean",
    "P2M/Sol/S_AlgebraicCurve_stichtenothGenusExists_of_isCurveOver.lean",
    "Theorems/Thm_AlgebraicCurve_indexOfSpecialty_eq_finrank_H1.lean",
    "P2M/Sol/S_AlgebraicCurve_indexOfSpecialty_eq_finrank_H1.lean",
    "Theorems/Thm_AlgebraicCurve_exists_genus_riemannIndex_of_isCurveOver.lean",
    "P2M/Sol/S_AlgebraicCurve_exists_genus_riemannIndex_of_isCurveOver.lean",
    "Theorems/Thm_AlgebraicCurve_weilDifferentialRankOne_of_isCurveOver.lean",
    "P2M/Sol/S_AlgebraicCurve_weilDifferentialRankOne_of_isCurveOver.lean",
    "Theorems/Thm_AlgebraicCurve_weilDualityAdelic_of_functionFieldRiemannRoch_of_stichtenothGenusExists.lean",
    "P2M/Sol/S_AlgebraicCurve_weilDualityAdelic_of_functionFieldRiemannRoch_of_stichtenothGenusExists.lean",
    "Theorems/Thm_AlgebraicCurve_exists_weilCanonical_riemannRoch.lean",
    "P2M/Sol/S_AlgebraicCurve_exists_weilCanonical_riemannRoch.lean",
    "Theorems/Thm_AlgebraicCurve_exists_riemannGenusReachedAt_nsmul_single_of_stichtenothGenusExists.lean",
    "P2M/Sol/S_AlgebraicCurve_exists_riemannGenusReachedAt_nsmul_single_of_stichtenothGenusExists.lean",
    # --- H3 (the differentials bridge and the Weil-differential interface). The
    # target's `Theorems/` wrapper comes first: it is the interface copy whose
    # binders the port's public headline spells. The four pin `Definitions/` files
    # then supply the definition layer (their own inventories are the authority,
    # there are no `Thm_` wrappers for them) and the `S_` file the shared prelude
    # plus the `'` copy of the headline.  The two proof-reached helper targets H3
    # re-provisioned `private` are wired with their own wrappers + `S_` files
    # (wrapper first); the refactor round promoted them into
    # `Defs/WeilOfKaehler.lean`.  Appended last so no earlier last-name match can
    # flip.
    "Theorems/Thm_AlgebraicCurve_weilOfKaehler_mem_omegaSpace_of_residueTheorem.lean",
    "P2M/Sol/S_AlgebraicCurve_weilOfKaehler_mem_omegaSpace_of_residueTheorem.lean",
    "Theorems/Thm_AlgebraicCurve_weilOfKaehler_ne_zero_and_maximal.lean",
    "P2M/Sol/S_AlgebraicCurve_weilOfKaehler_ne_zero_and_maximal.lean",
    "Theorems/Thm_AlgebraicCurve_exists_linearEquiv_regularDifferentials_omegaSpace_zero.lean",
    "Definitions/Def_ModularCurve_CanonicalDivisorUniformizer.lean",
    "Definitions/Def_AlgebraicCurve_LocalResidue.lean",
    "Definitions/Def_AlgebraicCurve_WeilOfKaehler.lean",
    "Definitions/Def_AlgebraicCurve_RegularDifferentials.lean",
    "P2M/Sol/S_AlgebraicCurve_exists_linearEquiv_regularDifferentials_omegaSpace_zero.lean",
    # --- P2 (the canonical divisor and its two Kähler prerequisites). The three
    # `Theorems/` wrappers come first (the interface copies whose binders the
    # port's three public headlines spell), then the three `S_` files: the two
    # Kähler files supply the shared private `exists_basis` prelude and the
    # `S_AlgebraicCurve_hasCanonicalDivisor_of_isCurveOver.lean` the 140-row
    # public model-predicate chain + private engine. Appended last so no earlier
    # last-name match can flip.
    "Theorems/Thm_AlgebraicCurve_hasCanonicalDivisor_of_isCurveOver.lean",
    "Theorems/Thm_KaehlerDifferential_span_D_eq_top_of_transcendental.lean",
    "Theorems/Thm_KaehlerDifferential_D_ne_zero_of_transcendental.lean",
    "P2M/Sol/S_KaehlerDifferential_span_D_eq_top_of_transcendental.lean",
    "P2M/Sol/S_KaehlerDifferential_D_ne_zero_of_transcendental.lean",
    "P2M/Sol/S_AlgebraicCurve_hasCanonicalDivisor_of_isCurveOver.lean",
]

PORT_FILES = [
    "FLTForHuman/FieldTheory/CommonRoot.lean",
    "FLTForHuman/ModularCurve/Defs/Laurent.lean",
    "FLTForHuman/ModularCurve/Defs/Twist.lean",
    "FLTForHuman/ModularCurve/Defs/Jq.lean",
    "FLTForHuman/ModularCurve/FunctionFieldGeneration/Target.lean",
    "FLTForHuman/ModularCurve/Defs/Polynomial.lean",
    "FLTForHuman/ModularCurve/Defs/Fields.lean",
    "FLTForHuman/ModularCurve/Defs/PhiGen.lean",
    "FLTForHuman/ModularCurve/Defs/TS.lean",
    "FLTForHuman/ModularCurve/FunctionFieldGeneration/Collapse.lean",
    "FLTForHuman/ModularCurve/JqCoefficients.lean",
    "FLTForHuman/ModularCurve/FunctionFieldGeneration/Spine.lean",
    "FLTForHuman/ModularCurve/Defs/Cyclotomic.lean",
    "FLTForHuman/ModularForms/QExpansionPrinciple.lean",
    "FLTForHuman/ModularForms/JqAnalyticModel.lean",
    "FLTForHuman/ModularForms/Hauptmodul.lean",
    "FLTForHuman/ModularForms/Defs/HeckeOperator.lean",
    "FLTForHuman/ModularForms/Defs/HeckeRepresentatives.lean",
    "FLTForHuman/ModularForms/HeckeInvariance.lean",
    "FLTForHuman/ModularForms/HeckeFricke.lean",
    "FLTForHuman/ModularForms/HeckeAnalytic.lean",
    "FLTForHuman/ModularForms/HeckeCusps.lean",
    # SET-3 T5: the formal `PowerSeries` operators and the shared `q`-coefficient tail.
    "FLTForHuman/ModularForms/Defs/FormalHeckeOperators.lean",
    "FLTForHuman/ModularForms/HeckeQCoeff.lean",
    # SET-3 T6: the bundled `heckeTLin`/`heckeULin` and the three thin wrappers.
    "FLTForHuman/ModularForms/HeckeOperatorForms.lean",
    # SET-3 T7: the formal-series operators, the commutations and the algebra.
    "FLTForHuman/ModularCurve/Defs/LaurentSeriesHecke.lean",
    "FLTForHuman/ModularForms/HeckeCommute.lean",
    "FLTForHuman/ModularForms/HeckeAlgebra.lean",
    # SET-4 T8: the normalized-eigenform structure and its operator dictionary.
    "FLTForHuman/ModularForms/Defs/Eigenform.lean",
    "FLTForHuman/ModularForms/HeckeEigenform.lean",
    # SET-4 T9: the integral-lattice definitions and the lattice action.
    "FLTForHuman/ModularForms/Defs/IntegralStructure.lean",
    "FLTForHuman/ModularForms/HeckeLattice.lean",
    # SET-4 T10 definitions survived; T10's theorem half is complete with route
    # C′/the Sturm bound — the finiteness family lives in `HeckeFiniteAlgebra.lean`
    # and the lattice facts in `HeckeLattice.lean`. The eigenbasis-span family is
    # still absent (see the `SOURCES` note and `logs/hecke-port.md` §T10).
    "FLTForHuman/ModularForms/Defs/EisensteinChiNegThree.lean",
    "FLTForHuman/ModularForms/Defs/IntegralLattice.lean",
    "FLTForHuman/ModularForms/HeckeFiniteAlgebra.lean",
    "FLTForHuman/ModularForms/HeckeQExpansion.lean",
    "FLTForHuman/ModularForms/PhiGenDescends.lean",
    "FLTForHuman/ModularCurve/PhiGenIntegrality.lean",
    "FLTForHuman/ModularCurve/PhiGenPoleBounds.lean",
    "FLTForHuman/ModularCurve/PhiGenDescent.lean",
    "FLTForHuman/ModularCurve/PhiGenDescendsStructure.lean",
    "FLTForHuman/ModularCurve/ModularPolynomialAssembly.lean",
    "FLTForHuman/ModularCurve/JqCoeffPositivity.lean",
    "FLTForHuman/ModularCurve/ModularPolynomialIrreducible.lean",
    "FLTForHuman/ModularCurve/ModularPolynomialProperties.lean",
    "FLTForHuman/ModularCurve/ModularPolynomialUniqueness.lean",
    "FLTForHuman/ModularCurve/PhiGenSplits.lean",
    # Topic 14, the shared slot prelude: the upstream vocabulary and the
    # downstream at-slot roots API.
    "FLTForHuman/ModularCurve/Defs/PhiAtSlot.lean",
    "FLTForHuman/ModularCurve/PhiSlotRoots.lean",
    # Topic 15, the descent and the one-prime reduction.
    "FLTForHuman/ModularCurve/FunctionFieldGeneration/Descent.lean",
    # Topic 16, the degree step.
    "FLTForHuman/ModularCurve/FunctionFieldGeneration/DegreeStep.lean",
    # Topic 17, the non-membership tower and the two-prime separation.
    "FLTForHuman/ModularCurve/FunctionFieldGeneration/Nonmembership.lean",
    # Topic 18, one new generator per prime power.
    "FLTForHuman/ModularCurve/FunctionFieldGeneration/Generation.lean",
    # Topic 19, the slot product and the prime non-membership.
    "FLTForHuman/ModularCurve/FunctionFieldGeneration/SlotProduct.lean",
    # Topic 20, the unconditional capstone.
    "FLTForHuman/ModularCurve/FunctionFieldGeneration/Capstone.lean",
    # SET 1 (AC0 + T1), the generic curve vocabulary and the ord interface.
    "FLTForHuman/AlgebraicCurve/Defs/Place.lean",
    "FLTForHuman/AlgebraicCurve/Defs/Divisor.lean",
    "FLTForHuman/AlgebraicCurve/Defs/PushPull.lean",
    "FLTForHuman/AlgebraicCurve/Defs/PlacesOverDVR.lean",
    "FLTForHuman/AlgebraicCurve/Defs/Correspondence.lean",
    "FLTForHuman/AlgebraicCurve/Defs/SemilinearAut.lean",
    "FLTForHuman/AlgebraicCurve/Defs/RatFuncPlaces.lean",
    "FLTForHuman/AlgebraicCurve/Defs/IntegralAdjoin.lean",
    # T2 (the promoted fibre dictionary and the bifibre count).
    "FLTForHuman/AlgebraicCurve/Defs/PlaceDictionary.lean",
    "FLTForHuman/AlgebraicCurve/WeilExchange/FiberOverCount.lean",
    # T3 (Galois ramification/inertia).
    "FLTForHuman/AlgebraicCurve/WeilExchange/GaloisRamification.lean",
    # T4 (along-map transport + `Pic0` descent, and the shared prelude).
    "FLTForHuman/AlgebraicCurve/WeilExchange/Transport.lean",
    # T5 (the generic orbit/index engine + the bifibre count).
    "FLTForHuman/FieldTheory/FiniteGroupAction.lean",
    "FLTForHuman/AlgebraicCurve/WeilExchange/Bifibre.lean",
    # T6 (the local exchange + the normal closure).
    "FLTForHuman/AlgebraicCurve/WeilExchange/LocalExchange.lean",
    # T8 (the `P¹` places and degree).
    "FLTForHuman/AlgebraicCurve/PrincipalDivisors/RatFuncDegree.lean",
    # T9 (`HasPrincipalDivisors` via transcendence).
    "FLTForHuman/AlgebraicCurve/PrincipalDivisors/Transcendence.lean",
    # T7, the divisor-exchange capstone (reserved for the human reviewer).
    "FLTForHuman/AlgebraicCurve/WeilExchange/DivisorExchange.lean",
    # SET-M1 m1: the Hecke correspondence vocabulary.
    "FLTForHuman/ModularCurve/Defs/HeckeOperator.lean",
    "FLTForHuman/ModularCurve/Defs/DegeneracyTower.lean",
    "FLTForHuman/ModularCurve/Defs/HeckeTotal.lean",
    "FLTForHuman/ModularCurve/Defs/ArithmeticGalois.lean",
    "FLTForHuman/ModularCurve/Defs/HeckeModule.lean",
    # SET-M1 m2: the geometric/cusp/q-adic/modular-unit vocabulary.
    "FLTForHuman/ModularCurve/Defs/JqCoeff.lean",
    "FLTForHuman/ModularCurve/Defs/GeometricBaseChange.lean",
    "FLTForHuman/ModularCurve/Defs/QAdicPlace.lean",
    "FLTForHuman/ModularCurve/Defs/ModularUnit.lean",
    "FLTForHuman/ModularCurve/Defs/AtkinLehner.lean",
    "FLTForHuman/ModularCurve/Defs/CuspidalClass.lean",
    # SET-M1 m3: the analytic modular-unit q-expansion core.
    "FLTForHuman/ModularCurve/Analytic/QParamUnique.lean",
    "FLTForHuman/ModularCurve/Analytic/Gamma0Cosets.lean",
    "FLTForHuman/ModularCurve/Analytic/ModularUnitQExpansion.lean",
    # SET-M2 m4: the shared Γ₀-invariant prelude, written once, and the first
    # two M8 headlines plus the four small `modularUnitSeries` targets. The third
    # headline and `coe_frickeInvolutionFull_modularUnitSeries` are downstream of
    # m5's `exists_isFrickeAutFull` and are delivered with m5.
    "FLTForHuman/ModularCurve/Analytic/Gamma0InvariantCore.lean",
    "FLTForHuman/ModularCurve/Analytic/FrickeInvariance.lean",
    # SET-M2 m6: the Φ datum family (the biresultant, the jqNModC evaluation
    # and integrality tails, the prime generation facts) and its degree tail.
    "FLTForHuman/ModularCurve/Degree/PhiData.lean",
    "FLTForHuman/ModularCurve/Degree/PhiDegree.lean",
    # SET-M2 m5 (first half): the cusp bookkeeping and the Fricke automorphisms.
    # The remaining m5 module (`Analytic/CuspDichotomy.lean`) is re-scoped to
    # `m5b`; see `logs/mc-port.md` §Friction.
    "FLTForHuman/ModularCurve/Analytic/CuspBookkeeping.lean",
    "FLTForHuman/ModularCurve/Analytic/FrickeAut.lean",
    # SET-M2 m5b: the `RatFunc` cusp model written once (the dichotomy and the
    # folded prime degree share it), the restrict-scalars identity, and the two
    # Fricke-automorphism consumers. `jTr` is built through the private generic
    # `ifRE` so the kernel never normalises `mem_bar_iff`'s heavy proof; see
    # `logs/mc-port.md` §Friction.
    "FLTForHuman/ModularCurve/Analytic/CuspDichotomy.lean",
    # SET-M3 m7: the Laurent/`coeffEmb` glue (the eight short M4 nodes).
    "FLTForHuman/ModularCurve/Degree/LaurentGlue.lean",
    # SET-M3 m7: `relfinrank_laurentBaseChange` (the pin's `TransportDev` block).
    "FLTForHuman/ModularCurve/Degree/Relfinrank.lean",
    # SET-M3 m9: the roof generation and the diagonal degree. The three generic
    # `AlgebraicCurve.finrankAlong` helpers were promoted (post-effort) to
    # `AlgebraicCurve/Defs/Correspondence.lean`; only the roof nodes live here.
    "FLTForHuman/ModularCurve/Degree/Roof.lean",
    # SET-M4 m10: tower integrality/finiteness and the Hecke integrality
    # predicates. The pin's private `gens`/`isIntegral_gens` supply block is
    # transcribed `private` here (the four `_of_prime` forms are
    # `exists_modularPolynomialData_evalSymm` at the general forms).
    "FLTForHuman/ModularCurve/HeckeInputs/Integrality.lean",
    # SET-M4 m11: `HasPrincipalDivisors` for the modular function fields (the
    # AC `hasPrincipalDivisors_adjoin_of_transcendental` corollary). The pin's
    # private `gens`/`mem_gens_iff`/`insert_gens` `Finset` block is transcribed
    # `private` here.
    "FLTForHuman/ModularCurve/PrincipalDivisors/ModularCurveBar.lean",
    # SET-M4 m12: the exchange reduction. The junk branches of the operator node
    # use `heckeOperatorAlong_of_not` at the bare linear-map shape rather than the
    # pin's `heckeOperatorBar_apply` pointwise rewrite (the port's `Nat.Primes`
    # subtype proof makes the pointwise goal fail `rw`'s implicit-transparency
    # type check); the statement is unchanged.
    "FLTForHuman/ModularCurve/HeckeExchange/Reduction.lean",
    # m13, the capstone (written by the reviewer; assembly over m9-m12).
    "FLTForHuman/ModularCurve/HeckeCommuteBar.lean",
    # The cusp-form vanishing layer (`base/003`): the `Γ₀(2)` first-column index
    # count (`Gamma0TwoIndex`) and the two wrapper theorems, now Sturm-bound
    # corollaries in `SturmBound.lean`.
    "FLTForHuman/ModularForms/Gamma0TwoIndex.lean",
    # Reserve: the cusp-form norm (`CuspForm.{norm, norm_eq_zero_iff,
    # coe_norm_eq_...}`), kept verified as a standalone mathlib-gap API. The
    # reserve norm-route module `Reserve/ModularForms/LevelTwoCuspVanishing.lean`
    # is built by the `Reserve` library but deliberately not listed here: it
    # proves the same wrapper theorems as `SturmBound.lean`, so there is nothing
    # new to diff.
    "Reserve/ModularForms/CuspFormNorm.lean",
    # The Sturm bound (the finiteness sub-cone): the two `q`-expansion order
    # lemmas, the arithmetic period input, the level-one and general vanishing,
    # and the two headline statements. All eight public declarations are wrapper
    # targets; `relIndex_map_mapGL_W2D` and the norm-analyticity helper stay
    # `private`.
    "FLTForHuman/ModularForms/QExpansionOrder.lean",
    "FLTForHuman/ModularForms/SturmBound.lean",
    # SET-5, the route-C' foundations: the weight-one toolbox layer and the
    # general Eisenstein series. The SET-5 headlines are public; the weight-one
    # toolbox's own `WLightR7b`/`WLightR8a`/`WLightR11g`/`WLight` helpers are
    # `private`, while the general `eisensteinG` helpers are public (promoted when
    # that module moved to `ModularForms/EisensteinSeries.lean`). The two generic
    # antidiagonal `tsum` rearrangements of the pin's `CardC` block broke out into
    # their own generic module (they are not modular-forms material); their public
    # statements are the pin's `CardC` copies in the `S_` file listed above.
    "FLTForHuman/ModularForms/WeightOne/Basic.lean",
    "FLTForHuman/ModularForms/EisensteinSeries.lean",
    "FLTForHuman/NumberTheory/TsumDivisorsAntidiagonal.lean",
    # SET-6, order 1: the four closure-1 Hauptmodul leaves. Only the four
    # headlines are public; the pin's self-contained `S_` helpers are `private`.
    "FLTForHuman/ModularForms/WeightOne/LevelOneHauptmodul.lean",
    # SET-6, order 2: the χ₋₃ weight-one Eisenstein series. The single headline
    # is public; the pin's ~400 helpers are all `private` here.
    "FLTForHuman/ModularForms/WeightOne/EisensteinChiNegThree.lean",
    # SET-7, order 2: the torsion ℘ q-expansion bundle. The single headline is
    # public; the pin's self-contained helpers are all `private` here. The
    # extended order-1 module above carries SET-7's other two headlines.
    "FLTForHuman/ModularForms/WeightOne/WeierstrassPTorsion.lean",
    # SET-8, order 1: the four monic-relation leaves. Only the four headlines are
    # public; the pin's repeated valuation-engine/flat-descent helpers are
    # `private` here, and the pin's unused
    # `mdifferentiable_eq_zero_or_eq_zero_of_mul_eq_zero` (mathlib's
    # `UpperHalfPlane.mul_eq_zero_iff`) is not transcribed.
    "FLTForHuman/ModularForms/WeightOne/MonicRel.lean",
    # SET-8, order 2: the three fricke-function packages. Only the three
    # headlines are public; each package's pin helpers are `private` in their own
    # namespace inside `WLight`, so the pin's repeated definitions do not collide.
    "FLTForHuman/ModularForms/WeightOne/FrickeFunction.lean",
    # SET-9, order 1: the four level-fraction packages. Only the four headlines
    # are public; each pin file's helpers are `private` in the pin's own namespace
    # (renamed `WLightS9.*`), so the four packages' repeated vocabulary does not
    # collide. Cross-package reuse is through the already-ported public headlines.
    "FLTForHuman/ModularForms/WeightOne/LevelFraction.lean",
    # SET-9, order 2: the level-N structure package, the frickeQuotient
    # monic-relation node and the `ModularFunction` sigmaTransport node. Only the
    # three headlines are public; the pin's helpers are `private` throughout.
    "FLTForHuman/ModularForms/WeightOne/LevelN.lean",
    # SET-10, order 1: the four Γ₀-rationality headlines. Pin helpers are
    # `private` inside the pin's own `FrickeIntegral`/`FrickeToInfinity`/
    # `X1DiamondRational`/`GammaNDescent` namespaces (nested in `WLightS10.*`).
    "FLTForHuman/ModularForms/WeightOne/Gamma0Rationality.lean",
    # SET-10, order 2: the three bounded-denominator headlines plus the public
    # `ModularCurve.IsIntegralQExp` definition the third statement names; all
    # other pin helpers `private`. Imports order 1.
    "FLTForHuman/ModularForms/WeightOne/Gamma0Integral.lean",
    # SET-11, order 1: the six Γ₁-basis headlines. Each pin `S_` file's helpers
    # are `private` in the pin's own inner namespace (`WeightLoweringCriterion` /
    # `Gamma1Eisenstein` / `FrickeCuspTransport` / `FrickeSpan` /
    # `GammaOneGaloisEven` / `GammaOneGaloisAllWeights`, nested in
    # `WLightS11.*`), so the checker sees only the six headlines.
    "FLTForHuman/ModularForms/WeightOne/Gamma1Basis.lean",
    # SET-11, order 2: the four integral-slash Γ₁-basis headlines; imports
    # order 1. The four pin inner namespaces are `GammaOneCyclotomicEven` /
    # `GammaOneCyclotomic` / `GammaOneRationalStructure` / `DeligneSerre271`.
    "FLTForHuman/ModularForms/WeightOne/Gamma1IntegralBasis.lean",
    # The capstone: the trace lemma and the two corollaries. Only the three
    # headlines are public; the `IsFiniteRelIndex` instance, the `Γ₀ → Γ₁`
    # restriction, the translate bundle, the `qCoeff` linear map and the trace
    # additivity are all `private`.
    "FLTForHuman/ModularForms/WeightOne/IntegralStructure.lean",
    # The shared homes (WeightOne rectification): their public declarations are the
    # lifted pin-private proofs; each is verified against the `S_` sources above.
    "FLTForHuman/ModularForms/QExpansionCoeff.lean",
    "FLTForHuman/ModularForms/DiscPow.lean",
    "FLTForHuman/ModularForms/WeightOne/Defs/PeriodPair.lean",
    "FLTForHuman/ModularForms/WeightOne/Defs/PTorsion.lean",
    "FLTForHuman/ModularForms/WeightOne/Defs/Gamma.lean",
    "FLTForHuman/ModularForms/WeightOne/Defs/GammaRational.lean",
    # The `RatAt`/width vocabulary, split out of `Defs/GammaRational` so `LevelN`
    # can share it (the γ-rationality home imports LevelN). Its declarations come
    # from the same Γ-package pin sources already in SOURCES.
    "FLTForHuman/ModularForms/WeightOne/Defs/RatAt.lean",
    "FLTForHuman/ModularForms/WeightOne/Fricke.lean",
    # The two homes created by the rectification's later waves. Their declarations
    # were lifted verbatim from pin-private regions of
    # `S_WLight_levelN_structure_package` / `S_WLight_isZeroAtImInfty_mul_disc_iff_qExpansion_coeff_le`
    # (both already in SOURCES), so the promoted-from-pin-private fallback verifies
    # them; `CuspBound`'s namespace differs (`WLightCusp`) and matches by last name.
    "FLTForHuman/ModularForms/WeightOne/LevelField.lean",
    "FLTForHuman/ModularForms/WeightOne/CuspBound.lean",
    # SET-1 (PORTING-Level.md): the Γ_H vocabulary. Definition-module port with no
    # `Theorems/` wrappers; verified by name against the four pin sources above.
    "FLTForHuman/ModularForms/Defs/GammaH.lean",
    # SET-2 (PORTING-Level.md, l2): the Γ₁ / diamond vocabulary. Definition-module
    # port with no `Theorems/` wrappers; verified by name against
    # `Definitions/Def_CuspForm_Gamma1HeckeOperators.lean` above.
    "FLTForHuman/ModularForms/Level/Diamond.lean",
    # SET-3 (PORTING-Level.md, l3): the projective line / coset index theory.
    # Definitions module (`Defs/ProjectiveLine.lean`, `Defs/PrimCosetReps.lean`)
    # plus the theory `Gamma0Index.lean` carrying the three public headlines.
    "FLTForHuman/ModularCurve/Defs/ProjectiveLine.lean",
    "FLTForHuman/ModularCurve/Defs/PrimCosetReps.lean",
    "FLTForHuman/ModularCurve/Gamma0Index.lean",
    # Post-SET-3 dedup: the counting core shared by SlotProduct and Gamma0Index.
    "FLTForHuman/NumberTheory/DedekindPsiCount.lean",
    # The general-weight Eichler–Shimura period map and its injectivity
    # (TOPIC-period-map-injectivity): the four generic facts in their subject
    # homes, the definitions, the leaves and the map.
    "FLTForHuman/Algebra/MvPolynomialHomogeneous.lean",
    "FLTForHuman/ModularForms/Analytic/StarConvexPrimitive.lean",
    "FLTForHuman/ModularForms/Analytic/CuspBoundedness.lean",
    "FLTForHuman/ModularForms/ModularGroup.lean",
    "FLTForHuman/ModularForms/EichlerShimura/BinaryForm.lean",
    "FLTForHuman/ModularForms/EichlerShimura/CoeffCohomology.lean",
    "FLTForHuman/ModularForms/EichlerShimura/EichlerIntegral.lean",
    "FLTForHuman/ModularForms/EichlerShimura/PeriodMap.lean",
    # Topic 11, the T-side definition layer (SET A/B/C). Every definition module
    # is transcribed verbatim (structures in the pin's field order); the three
    # algebra theorems are the pin's `Theorems/` wrappers verbatim with their
    # proofs ported from the `P2M/Sol/S_*` files and every helper `private`.
    "FLTForHuman/Patching/Defs/PatchingDatum.lean",
    "FLTForHuman/WeierstrassCurve/Defs/Modularity.lean",
    "FLTForHuman/WeierstrassCurve/Defs/FreyPackage.lean",
    "FLTForHuman/GaloisRep/Defs/GaloisAction.lean",
    "FLTForHuman/GaloisRep/Defs/Ramification.lean",
    "FLTForHuman/GaloisRep/Defs/FrobeniusTrace.lean",
    "FLTForHuman/GaloisRep/Defs/Residual.lean",
    "FLTForHuman/GaloisRep/Defs/ResidualEquiv.lean",
    "FLTForHuman/GaloisRep/Defs/Adic.lean",
    "FLTForHuman/GaloisRep/Defs/DeformationRingData.lean",
    "FLTForHuman/Algebra/FiniteAlgebraComplete.lean",
    # Topic 11, SET D: the T package and the local Hecke algebra.
    "FLTForHuman/HeckeGalois/Defs/HeckeGaloisRepDatum.lean",
    "FLTForHuman/HeckeGalois/Defs/HeckeLocal.lean",
    # T12, SET 1: the surjection half of `R = T`. The shared membership lemma and
    # the `exists_integral_mul_eq` node live in their number-theory subject home;
    # the Frobenius-existence node and its `rat` corollary in a second
    # number-theory module; the two charpoly bridges in the Galois-rep home; only
    # the two R=T interface statements in `HeckeGalois/`.
    "FLTForHuman/NumberTheory/ValuationAtPlace.lean",
    "FLTForHuman/NumberTheory/FrobeniusAtPlace.lean",
    "FLTForHuman/GaloisRep/AdicCharpoly.lean",
    "FLTForHuman/HeckeGalois/Surjective.lean",
    # T12, SET 2: the eigenform-extraction chain, at its natural subject homes.
    # Two generic algebra modules under `Algebra/`, the degeneracy map under
    # `ModularForms/Level/` (beside `Diamond.lean`), the two level-raising
    # headlines, and the extraction itself. `HeckeLattice.lean` is already
    # listed above; its one additive §2 change (publishing `mem_intLattice_iff`)
    # is verified through `Thm_CuspForm_mem_intLattice_iff.lean`.
    "FLTForHuman/Algebra/IntegralExtensionCharacters.lean",
    "FLTForHuman/Algebra/FaithfulLatticeEigenvector.lean",
    "FLTForHuman/ModularForms/Level/Degeneracy.lean",
    "FLTForHuman/ModularForms/EigenformLevel.lean",
    "FLTForHuman/ModularForms/EigenformExtraction.lean",
    # T12, SET 3: the conditional capstone. The `R ≅ T` assembly at its natural
    # subject home (beside `WeierstrassCurve/Defs/Modularity.lean`); its single
    # public declaration is own-proof, and the verbatim pinned statement is left
    # to SET 4.
    "FLTForHuman/WeierstrassCurve/ModularityLifting.lean",
    # T12, SET 4: the descent-and-freeness engine of the patching exit. Two
    # generic algebra facts (`FaithfulFreeness`), freeness from a full-length
    # weakly regular sequence (`RegularSequenceFreeness`), the `MvPowerSeries`
    # facts `free_and_ker_eq_span` needs (`MvPowerSeriesRegular`; see the
    # `SOURCES` note), and the patching-level descent itself (`LevelDescent`).
    "FLTForHuman/Algebra/FaithfulFreeness.lean",
    "FLTForHuman/Algebra/RegularSequenceFreeness.lean",
    "FLTForHuman/Algebra/MvPowerSeriesRegular.lean",
    "FLTForHuman/Patching/LevelDescent.lean",
    # T12, SET 5: the power-series patching algebra. `MvPowerSeriesRegular.lean` is
    # already listed above (SET 5 extends it additively); the generic
    # `IsAdicComplete.map_of_surjective` lives in its own module.
    "FLTForHuman/Algebra/AdicCompleteMap.lean",
    # T12, SET 6: the Taylor–Wiles patching construction. `nonempty_patchingLevel_bot`
    # is the only public declaration; the pin's `PCPortSpine*`, patching carriers and
    # `FrobDictPC.Limit` scaffolding are all `private`.
    "FLTForHuman/Patching/PatchingConstruction.lean",
    # T12, SET 7: the abstract patching exit. The one public declaration is the
    # pin's `Theorems/` statement; SET 6's construction and SET 4's descent engine
    # are on its import path. `FLTForHuman/WeierstrassCurve/ModularityLifting.lean`
    # above gains the verbatim `…_of_patchingDatum` additively, so both the
    # conditional and the unconditional assembly are checked through that one entry.
    "FLTForHuman/Patching/Exit.lean",
    # --- Phase D (Deligne–Serre weight-one definition layer, D0) ---
    "FLTForHuman/GaloisRep/Defs/MatrixRepresentation.lean",
    "FLTForHuman/ModularForms/Eisenstein/WeierstrassZeta.lean",
    "FLTForHuman/FieldTheory/RatAlgClosureGalois.lean",
    "FLTForHuman/ModularCurve/Defs/Gamma0Away.lean",
    "FLTForHuman/ModularCurve/Defs/IharaIota.lean",
    "FLTForHuman/Algebra/BrauerNesbitt.lean",
    "FLTForHuman/NumberTheory/FrobeniusDensity/TaylorWilesPrimes.lean",
    # --- Phase D, D1 ---
    "FLTForHuman/ModularForms/Defs/Gamma1HeckeOperators.lean",
    "FLTForHuman/ModularForms/Defs/PrimitiveFormGamma1.lean",
    "FLTForHuman/NumberTheory/FrobeniusDensity/DegOneAsymptotic.lean",
    "FLTForHuman/ModularCurve/Defs/IharaAmalgam.lean",
    # --- Phase D, D2 ---
    "FLTForHuman/NumberTheory/FrobeniusDensity/BadPrimes.lean",
    "FLTForHuman/GaloisRep/Defs/FrobeniusPowerDense.lean",
    "FLTForHuman/ModularCurve/Defs/IharaAmalgamMap.lean",
    # --- Phase D, D3 ---
    "FLTForHuman/NumberTheory/FrobeniusDensity/PrimeSums.lean",
    # --- Phase H1 (Deligne–Serre homes) ---
    "FLTForHuman/GaloisRep/Prelude.lean",
    "FLTForHuman/ModularForms/Eisenstein/Cotangent.lean",
    "FLTForHuman/NumberTheory/FrobeniusDensity/Basic.lean",
    "FLTForHuman/ModularForms/HeckePrelude.lean",
    # --- S1 (Deligne–Serre weight-one Eisenstein set) ---
    # Five modules under `ModularForms/Eisenstein/`, one per pin `S_` file, in the
    # pin's import order. Appended last.
    "FLTForHuman/ModularForms/Eisenstein/WeierstrassZetaSum.lean",
    "FLTForHuman/ModularForms/Eisenstein/WeierstrassZetaQuasiPeriod.lean",
    "FLTForHuman/ModularForms/Eisenstein/EisensteinG1Transform.lean",
    "FLTForHuman/ModularForms/Eisenstein/EisensteinG1QExpansion.lean",
    "FLTForHuman/ModularForms/Eisenstein/WeightOneMultiplier.lean",
    # --- S2 (Deligne–Serre Hecke / Γ₁ vanishing and nebentypus set) ---
    # Five modules, in dependency order (the Ihara module is independent and the
    # `HeckeEigenNebentypus` module imports `Gamma1Vanishing`). Appended last.
    "FLTForHuman/ModularForms/HeckeTLinOneQCoeff.lean",
    "FLTForHuman/ModularForms/HeckeNebentypus.lean",
    "FLTForHuman/ModularForms/Gamma1Vanishing.lean",
    "FLTForHuman/ModularForms/HeckeEigenNebentypus.lean",
    "FLTForHuman/ModularCurve/IharaSurjective.lean",
    # --- S3 (Deligne–Serre relèvement and weight-one → weight-two lifting) ---
    # The weight-generic relèvement first, then the weight-one instance that
    # imports it. Appended last.
    "FLTForHuman/DeligneSerre/Relevement.lean",
    "FLTForHuman/DeligneSerre/Lifting.lean",
    # --- S4 (Deligne–Serre coefficient ring and Galois conjugation) ---
    # The two new modules. `FLTForHuman/Algebra/IntegralExtensionCharacters.lean`
    # and `FLTForHuman/Algebra/FaithfulLatticeEigenvector.lean`, extended by S4,
    # are already listed above. Appended last.
    "FLTForHuman/Algebra/LatticeEigenvalues.lean",
    "FLTForHuman/DeligneSerre/CoefficientRing.lean",
    # --- S5 (Deligne–Serre semisimple descent of a reducible residual
    # representation) ---
    # The single new module, under `GaloisRep` (its only import home). It carries
    # the three shared engines as public declarations and the one target. Appended
    # last.
    "FLTForHuman/GaloisRep/SemisimpleDescent.lean",
    # --- S7-I (Deligne–Serre Frobenius density, place / Frobenius vocabulary) ---
    # Node 5: the localisation place of `ℚ̄` at a maximal ideal of `𝓞 ℚ̄`. Its pin
    # `S_` file's public `C6P1T3a` block is transcribed `private`, so the wrapper
    # is the comparable copy. Appended last.
    "FLTForHuman/NumberTheory/FrobeniusDensity/ValuationSubringLocalization.lean",
    # Node 6: the lift of an arithmetic Frobenius from `𝓞 E` to `𝓞 ℚ̄`. Its pin
    # `S_` file's public `C6P1T2` block (three scoped instances,
    # `restrictNormal_restrictScalars`) is transcribed `private`, so the wrapper
    # is the comparable copy. Appended last.
    "FLTForHuman/NumberTheory/FrobeniusDensity/FrobeniusLift.lean",
    # Node 7: the Krull-topology statement that an open subgroup contains the
    # restriction kernel of a finite Galois number field. Its pin `S_` file's
    # public `P2mWs11LV` helpers are transcribed `private`, so the wrapper is the
    # comparable copy. Appended last.
    "FLTForHuman/NumberTheory/FrobeniusDensity/KerRestrictNormalHom.lean",
    # --- S7-II (Deligne–Serre Frobenius density, zeta / coset / Möbius counting
    # chain to `degOneAsymptotic`) ---
    # One module per subject, in dependency order: the Möbius/`zpowers` group
    # chain (`Basic.lean` provides only the shared prelude), the ideal-sum
    # analytic block, the prime-sum split, the factored-sum/Euler-product Big-O
    # module, the degree-one asymptotic chain, the `degOneAsymptotic` theorem
    # (which imports the D1 definition module), and the coset count. Appended
    # last so no earlier last-name match can flip.
    "FLTForHuman/NumberTheory/FrobeniusDensity/MobiusZeta.lean",
    "FLTForHuman/NumberTheory/FrobeniusDensity/IdealSum.lean",
    "FLTForHuman/NumberTheory/FrobeniusDensity/PrimeSumSplit.lean",
    "FLTForHuman/NumberTheory/FrobeniusDensity/PrimeSumAsymptotic.lean",
    "FLTForHuman/NumberTheory/FrobeniusDensity/DegOneSumAsymptotic.lean",
    "FLTForHuman/NumberTheory/FrobeniusDensity/DegOneAsymptoticProof.lean",
    "FLTForHuman/NumberTheory/FrobeniusDensity/DegreeOneCount.lean",
    # --- S7-III (the density statement and its applications) plus the S7-I tail
    # node. One module per pin `S_` subject, in dependency order: the generic
    # group criterion, the density-from-asymptotic proof, its unconditional form,
    # the valuation realisation, the `FrobeniusPowerDense` application, the open
    # subgroup corollary, and the `ZMod`-prime infinitude tail. Appended last so
    # no earlier last-name match can flip.
    "FLTForHuman/NumberTheory/FrobeniusDensity/NcardConjGen.lean",
    "FLTForHuman/NumberTheory/FrobeniusDensity/StatementOfDegOneAsymptotic.lean",
    "FLTForHuman/NumberTheory/FrobeniusDensity/Statement.lean",
    "FLTForHuman/NumberTheory/FrobeniusDensity/ExistsFrobeniusConjPow.lean",
    "FLTForHuman/NumberTheory/FrobeniusDensity/FrobeniusPowerDense.lean",
    "FLTForHuman/NumberTheory/FrobeniusDensity/PrimeIsFrobeniusAtConjPow.lean",
    "FLTForHuman/NumberTheory/FrobeniusDensity/DegreeOnePrimesInfinite.lean",
    # --- S6 (representation conjugacy and lifting). `RepConj` first (S6b's
    # character-determines-conjugacy), then the `RepLift` target (S6a), then the
    # `ConjFromFrobenius` glue (S6c), in dependency order. Appended last so no
    # earlier last-name match can flip.
    "FLTForHuman/GaloisRep/RepConj.lean",
    "FLTForHuman/GaloisRep/RepLift.lean",
    "FLTForHuman/GaloisRep/ConjFromFrobenius.lean",
    # --- S8 (the complex-trace assembly). The capstone, conditional on the
    # residual family `hfam`; the only public declaration is the target, all
    # helpers are `private`. Appended last so no earlier last-name match can flip.
    "FLTForHuman/DeligneSerre/Assembly.lean",
    # --- D (the Riemann–Roch definition layer), in the pin's own import order.
    # `Pic` (the pin's `Def_AlgebraicCurve_DivisorClassGroup:221`, already in
    # SOURCES) lives in `Defs/Divisor.lean` beside `Pic0`; the refactor round moved
    # it there from `CanonicalDivisor`, where the earlier AC effort had left it.
    # Appended last so no earlier last-name match can flip.
    "FLTForHuman/AlgebraicCurve/Defs/CanonicalDivisor.lean",
    "FLTForHuman/AlgebraicCurve/Defs/Repartitions.lean",
    "FLTForHuman/AlgebraicCurve/Defs/AdelicIndex.lean",
    "FLTForHuman/AlgebraicCurve/Defs/IsCurveOver.lean",
    "FLTForHuman/AlgebraicCurve/Defs/RiemannRochRows.lean",
    "FLTForHuman/AlgebraicCurve/Defs/PoleDivisorPackage.lean",
    # --- H1a (the adelic-index / `ell` prelude and the index targets), the
    # module that consumes the D layer. Appended last so no earlier last-name
    # match can flip.
    "FLTForHuman/AlgebraicCurve/Genus/Index.lean",
    # --- H1b (the Stichtenoth genus-existence tower), the module that consumes H1a.
    # Appended last so no earlier last-name match can flip.
    "FLTForHuman/AlgebraicCurve/Genus/Stichtenoth.lean",
    # --- R (refactor): the promoted curve-level prerequisite
    # `IsCurveOver.exists_separating_transcendental`, the module H2's Assembly
    # imports. Appended before Assembly so no earlier last-name match can flip.
    "FLTForHuman/AlgebraicCurve/IsCurveOver/SeparatingTranscendental.lean",
    # --- H2 (assembly, the Weil canonical divisor, and the `H¹` identification),
    # the module that consumes H1a/H1b. Appended last so no earlier last-name
    # match can flip.
    "FLTForHuman/AlgebraicCurve/RiemannRoch/Assembly.lean",
    # --- H3 (the differentials bridge and the Weil-differential interface): the
    # four definition modules in the pin's import order, then the headline module
    # that consumes them and H2. Appended last so no earlier last-name match can
    # flip.
    "FLTForHuman/AlgebraicCurve/Defs/CanonicalDivisorUniformizer.lean",
    "FLTForHuman/AlgebraicCurve/Defs/LocalResidue.lean",
    "FLTForHuman/AlgebraicCurve/Defs/WeilOfKaehler.lean",
    "FLTForHuman/AlgebraicCurve/Defs/RegularDifferentials.lean",
    "FLTForHuman/AlgebraicCurve/Canonical/WeilDifferential.lean",
    # --- P2 (the canonical divisor and its two Kähler prerequisites), the modules
    # that consume the D/H3 layer. KaehlerTranscendental first (the two headlines
    # the HasCanonicalDivisor chain applies), then the construction. Appended last
    # so no earlier last-name match can flip.
    "FLTForHuman/AlgebraicCurve/Defs/KaehlerTranscendental.lean",
    "FLTForHuman/AlgebraicCurve/Canonical/HasCanonicalDivisor.lean",
]


# Declarations whose *statement* has no FLT source, so there is nothing to diff:
# they are our own, not transcribed. `coeff_jq_zero` / `coeff_jq_one` state the
# regular low coefficients of `jq` (base/004: `q⁻¹ + 744 + 196884 q + ⋯`). FLT
# reaches those numbers only inside the deferred modular-form q-expansion cluster
# (`hasSum_jq_qParam` is a different statement), and its declarations there carry
# different names, so the pin has no name/statement to compare against. The proof
# here uses mathlib's pentagonal route over `etaProd`; see
# `FLTForHuman/ModularCurve/JqCoefficients.lean` and `topics/functionFieldGeneration/TOPIC-jq-coefficients.md`.
# Listing them explicitly keeps "0 missing" meaningful: an unlisted new
# declaration still fails the check. Entries may be either a last name (the usual
# form) or a dotted name, which exempts only that qualified declaration.
OWN_PROOFS = {
    # The WeightOne shared homes: these two are the port's own spellings, not
    # transcriptions -- `qExpansion_coeff_width_fn` is the function form of the
    # width formula (the pin has it only inlined), and `map_eq` is a local
    # helper of the Γ-rationality region.
    "qExpansion_coeff_width_fn",
    "map_eq",
    # `NumberTheory/DedekindPsiCount.lean`: the generic block count is FLT-private in
    # the pin and promoted here; `dedekindPsiFibre` is the port's rename of the pin's
    # `h`/`slotH` (the name `slotH` is taken publicly by `ModularCurve.QExpN.slotH`),
    # so `card_fibre`'s statement is the pin's modulo that rename.
    "dedekindPsiFibre",
    "card_fibre",
    "coeff_jq_zero",
    "coeff_jq_one",
    # `Spine.lean`'s public surface. `Tight`/`Gen`/`Hall` are FLT's private
    # abbreviations in `P2M/Sol/S_ModularCurve_functionFieldGeneration.lean`
    # (lines 413–419), promoted to public here so a later discharge can name them;
    # the script only reads non-private declarations, so it cannot see the pin's.
    # `Inputs` and `functionFieldGeneration_of` are ours: `Inputs` bundles FLT's
    # significant statements and has no counterpart to diff, and the capstone is
    # the conditional artifact of TOPIC-conditional-capstone.md, not a node in the
    # pin. Their auxiliaries are `private` and so are invisible to the checker.
    "Tight",
    "Gen",
    "Hall",
    "Inputs",
    "functionFieldGeneration_of",
    # `hall_all` (T20) is FLT's strong induction, but the pin states its seven
    # hypotheses as section variables (`: ∀ N : ℕ, N ≠ 0 → Hall N`), while the port
    # bundles them as `Inputs` — the device immediately above, which is ours.
    # So the port's statement is the pin's modulo that bundling, exactly as
    # `functionFieldGeneration_of` is.
    "hall_all",
    # `inputs` (T20) is the port's assembly of the seven proved field theorems
    # into `Inputs`. FLT has no counterpart: its `hall_all` is applied directly to
    # the hypotheses. This is the one declaration the capstone adds that is ours.
    "inputs",
    # `mem_adjoin_jq_of_poleOrderLE_zero` is ours, like `coeff_jq_zero` /
    # `coeff_jq_one`: it states the `n = 0` end of R1's Hauptmodul form
    # (base/013 §3, §5.5) as a corollary of the transcribed kernel. FLT has no
    # declaration for it — the pin's nearest statement,
    # `mem_adjoin_jq_of_hasSum_of_slash_invariant`, drops the pole bound and is a
    # different (topic 7) theorem, reached through pole killing — so there is no
    # name/statement to diff. See
    # `FLTForHuman/ModularForms/QExpansionPrinciple.lean`.
    "mem_adjoin_jq_of_poleOrderLE_zero",
    # `gen_prime` (T18) is ours, like `Tight`/`Gen`/`Hall`: it is the 2026-09-22
    # route audit's replacement for the pin's `functionFieldGeneration_of_squarefree`
    # detour at `S_ModularCurve_jqN_prime_not_mem_full.lean:1638`. FLT has no such
    # declaration (`Gen p` is definitional: both sides are `ℚ(jq, jqN p)`), so
    # there is no name/statement to diff. The promoted `tight_one`/`gen_one` are
    # FLT's and verify through the pin's `private` copies instead.
    "gen_prime",
    # `card_slotFilter_eq_dedekindPsi` (T19) is the audit's recommended single
    # public counting export (`audit-slot-counting-mathlib.md` §5). FLT's nearest
    # statement is `card_primCosetReps_eq_dedekindPsi`, a different (triple) shape,
    # so there is no name/statement to diff; the pin's own `slots_eq_dedekindPsi`
    # is `private`.
    "card_slotFilter_eq_dedekindPsi",
    # `correspondence` (SET 1, `Defs/Correspondence.lean`) is the one last-name
    # collision the AC block cannot resolve: `Def_AlgebraicCurve_Correspondence.lean`
    # declares `Divisor.correspondence` (line 137) and `Pic0.correspondence`
    # (line 183) with the same last name, and `declarations()` keeps only the
    # first, so no `SOURCES` ordering can verify the second. Both port copies are
    # transcribed verbatim from that file; the exemption covers the pair.
    "correspondence",
    # The capstone trace lemma. FLT has no wrapper for it: the pin's route to
    # this statement is the Eichler–Shimura tower (`S_CuspForm_hasIntegralStructure_of_two_le`
    # and the 657-node HeckeEis/Eichler–Shimura development), which the port
    # replaces with mathlib's `CuspForm.trace` plus SET-11's integral-slash
    # Γ₁-basis. See `WeightOne/IntegralStructure.lean` and math/013 §5.
    "hasIntegralStructure_of_basis_gamma1",
    # --- The Eichler–Shimura period map (TOPIC-period-map-injectivity) ---------
    # `MvPolynomial.coeff` is not a name in mathlib v4.34 (only the
    # `AddMonoidAlgebra.coeff` projection), so these two pin statements cannot be
    # spelled as their wrappers spell them; the port writes
    # `(·).coeff (Finsupp.single 1 n)` and the statements are otherwise identical.
    "coeff_single_one_eq_eval_of_mem_binaryForm",
    "mem_range_binaryFormRepSL_T_zpow_sub_one",
    # The recorded divergence: the port replaces the pin's `dif`ed
    # `eichlerShimuraMap : (ℍ → ℂ) → coeffH1par …` by the structural linear map
    # `periodMap` on cusp forms (`TOPIC-period-map-injectivity.md` §3, Tier 1).
    # There is no pin declaration of these names/shapes to diff; the pin's
    # `eichlerShimuraMap_injective` is reproduced by `periodMap_injective`.
    "periodMap",
    "periodMap_eq_coeffH1parMk",
    "periodMap_injective",
    # --- Topic 11, the T-side definition layer --------------------------------
    # The `GaloisRepAdic.Equiv` groupoid laws collide, by last name *and* by the
    # checker's two-component dotted key, with the `ResidualGaloisRep.Equiv`
    # copies in `Definitions/Def_GaloisRep_ResidualEquiv.lean` (`refl`/`symm`/
    # `trans`/`baseChangeAlong`). Both port copies are transcribed verbatim; no
    # `SOURCES` ordering can verify both, because the first-name lookup and the
    # dotted fallback share one value per key — the `correspondence` situation
    # again. The **residual** copies are verified (`source['refl']` is theirs);
    # the adic copies are exempted here by their full dotted names, so the
    # exemption is precise and no other `refl`/`symm`/`trans` is affected.
    "GaloisRepAdic.Equiv.refl",
    "GaloisRepAdic.Equiv.symm",
    "GaloisRepAdic.Equiv.trans",
    "GaloisRepAdic.Equiv.baseChangeAlong",
    # --- T12, SET 1: the surjection half of `R = T` ---------------------------
    # `ValuationSubring.mem_of_isIntegral` is the port's promotion of the pin's
    # two copies of the same argument — the local `int_mem` of
    # `S_ValuationSubring_exists_integral_mul_eq_of_liesOverPrime.lean` (lines
    # 97–111) and `PlaceTransitivity.coe_mem` of
    # `S_ValuationSubring_exists_isFrobeniusAt_of_liesOverPrime.lean` (lines
    # 17–28), the latter being the same result specialised to `b : ℤ̄`. The port
    # writes it once, publicly, and both modules use it; the pin has no standalone
    # wrapper to diff it against. A *dotted* name is used so the exemption cannot
    # leak to any other `mem_of_isIntegral`.
    "ValuationSubring.mem_of_isIntegral",
    # --- T12, SET 3: the conditional capstone ---------------------------------
    # `WeierstrassCurve.isModularModelOfLevel_of_patchingLevel` is the pin's
    # `…_of_patchingDatum` with the patching facts taken as hypotheses: the
    # `P : Algebra.PatchingDatum 𝒪 p r D.R M` binder and the two lines that
    # consume it (`P.nonempty_patchingLevel_bot hp𝒪`, `L.free_and_ker_eq_span`)
    # are replaced by an `L : Algebra.PatchingLevel 𝒪 r D.R M ⊥` and the three
    # outputs of `Algebra.PatchingLevel.free_and_ker_eq_span` (`hfree`, `hann`,
    # `hker`). The 3,789-line patching construction is therefore not on this
    # module's import path; SET 4 discharges the three hypotheses and adds the
    # verbatim `…_of_patchingDatum` (whose wrapper is already in `SOURCES`). The
    # statement differs from the pin's, so it is exempted here rather than
    # diffed; a *dotted* name keeps the exemption from leaking to any other
    # `isModularModelOfLevel_*`.
    "WeierstrassCurve.isModularModelOfLevel_of_patchingLevel",
}

# Declaration keywords. `instance` matters for PhiGen; `structure` for Polynomial.
# The optional `mods` group carries `private` and/or `noncomputable`. `private`
# is what lets the *source* side see the pin's `private` helpers: FLT keeps the
# shared `TPoleOrderLE` prelude private in the six files that repeat it (or
# exposes it only through its `p2m_export` alias, a command the text checker
# cannot follow), yet the port promotes it into `Defs/` so later modules can
# import it. Port declarations are still read without the `private` flag, so a
# `private` port helper is never diffed. `noncomputable` (SET-3 T7) exposes the
# pin's inline `noncomputable def`s, e.g. `Def_LaurentSeries_Hecke{U,V}.lean`'s
# `heckeU`/`heckeV`/`heckeT`; the port writes `noncomputable section` + plain
# `def`, so only the source side needed the extra alternative.
# The optional leading `attrs` group makes an attributed declaration on a single
# line (`@[scoped simp] theorem qTwistEquiv_apply …`, T14) visible. Without it
# the regex anchors on `theorem`, so such a declaration was invisible on *both*
# sides; with it, the port's copy is verified like any other. Adding it changed
# no other match (T14 re-ran the checker: 0 mismatched, 0 missing).
DECL_RE = re.compile(
    r"^(?P<attrs>(?:@\[[^\]\n]*\]\s*)*)(?P<mods>(?:(?:private|noncomputable)\s+)*)"
    r"(?P<kind>def|theorem|lemma|abbrev|structure|instance)\s+"
    r"(?P<name>[\w.'ₐ]+)",
    re.MULTILINE,
)
FIELD_RE = re.compile(r"^\s{2,}([\w'ₐ]+)\s*:", re.MULTILINE)

# Enclosing-namespace tracking.  The same last name can occur twice in one pinned
# file under two different namespaces (e.g. `ModularForm.heckeTLin` and
# `CuspForm.heckeTLin` in `Def_ModularForm_HeckeOperatorForms.lean`, or
# `PowerSeries.heckeU` and `ModularForm.heckeU` across two definition files).  The
# last-name lookup keeps only the first; qualifying each declaration by its
# enclosing `namespace` gives the checker's dotted fallback a key for the second.
# `section`/`mutual` openers are tracked too, because `end` closes whichever is
# innermost.  Only key construction changes; the last-name (`name`) lookups are
# untouched.
ENCLOSE_RE = re.compile(
    r"^(?P<indent>\s*)(?:(?P<ns>namespace)\s+(?P<nsname>[\w.']+)"
    r"|(?P<sec>(?:(?:noncomputable|private|protected)\s+)*section)\b"
    r"|(?P<mut>mutual)\b"
    r"|(?P<end>end)\b)",
    re.MULTILINE,
)


def strip_line_comments(text: str) -> str:
    """Drop `--` comments (used only for the namespace scan)."""
    return re.sub(r"--[^\n]*", "", text)


def namespace_events(text: str) -> list[tuple[int, str, str | None]]:
    """(position, kind, name) for every namespace/section/mutual/end at line start."""
    out: list[tuple[int, str, str | None]] = []
    for m in ENCLOSE_RE.finditer(strip_line_comments(text)):
        if m.group("ns"):
            out.append((m.start(), "ns", m.group("nsname")))
        elif m.group("mut"):
            out.append((m.start(), "sec", None))
        elif m.group("sec"):
            out.append((m.start(), "sec", None))
        else:
            out.append((m.start(), "end", None))
    return out


def enclosing_namespace(stack: list[str | None]) -> str:
    return ".".join(x for x in stack if x)


def strip_comments(text: str) -> str:
    """Remove Lean block comments so prose does not pollute a statement."""
    return re.sub(r"/-.*?-/", " ", text, flags=re.DOTALL)


def top_level_cut(text: str) -> int:
    """Index of the first `:=` or `where` outside any bracket pair."""
    depth = 0
    i = 0
    n = len(text)
    while i < n:
        c = text[i]
        if c in "([{":
            depth += 1
        elif c in ")]}":
            depth -= 1
        elif depth == 0:
            if text.startswith(":=", i):
                return i
            if text.startswith("where", i):
                before = text[i - 1] if i else " "
                after = text[i + 5] if i + 5 < n else " "
                if not (before.isalnum() or before == "_") and not (
                    after.isalnum() or after == "_"
                ):
                    return i
        i += 1
    return n


def norm(text: str) -> str:
    # Both the port and the definitions layer spell these declarations inside
    # `namespace ModularCurve`/`namespace AlgebraicCurve`, but the `Theorems/`
    # wrappers additionally qualify every occurrence with the namespace. That
    # qualification is noise for a statement diff, so drop it on both sides
    # before comparing.
    text = re.sub(r"\bModularCurve\.", "", strip_comments(text))
    text = re.sub(r"\bAlgebraicCurve\.", "", text)
    return re.sub(r"\s+", " ", text).strip()


def raw_declarations(text: str, include_private: bool = False) -> list[tuple[str, str, str]]:
    """(raw name, kind, normalized statement) for each declaration in `text`.

    With `include_private`, the pin's `private` declarations are read too; the
    port side never passes it (a private port helper is not part of the surface
    being verified).
    """
    text = strip_comments(text)
    matches = list(DECL_RE.finditer(text))
    events = namespace_events(text)
    out: list[tuple[str, str, str]] = []
    stack: list[str | None] = []
    ei = 0
    for idx, m in enumerate(matches):
        while ei < len(events) and events[ei][0] < m.start():
            _, ekind, ename = events[ei]
            if ekind == "ns":
                stack.append(ename)
            elif ekind == "sec":
                stack.append(None)
            elif stack:
                stack.pop()
            ei += 1
        if "private" in m.group("mods") and not include_private:
            continue
        end = matches[idx + 1].start() if idx + 1 < len(matches) else len(text)
        chunk = text[m.end() : end]
        kind = m.group("kind")
        if kind == "structure":
            stmt = norm(chunk[: top_level_cut(chunk)]) + " FIELDS " + " ".join(
                FIELD_RE.findall(chunk)
            )
        else:
            stmt = norm(chunk[: top_level_cut(chunk)])
        prefix = enclosing_namespace(stack)
        name = m.group("name")
        raw = f"{prefix}.{name}" if prefix else name
        out.append((raw, kind, stmt))
    return out


def declarations(text: str) -> dict[str, tuple[str, str]]:
    """last name component -> (kind, normalized statement)."""
    out: dict[str, tuple[str, str]] = {}
    for raw, kind, stmt in raw_declarations(text):
        # First occurrence wins; later duplicates would be redefinitions.
        out.setdefault(raw.rsplit(".", 1)[-1], (kind, stmt))
    return out


def promoted_key(raw: str) -> str:
    """The dotted name of a promoted declaration, for matching a public port
    declaration against the pin's `private` original.

    The port writes the shared prelude's methods as `theorem TPoleOrderLE.mono`
    (two components); the pin writes them as
    `private theorem _root_.ModularCurve.PhiGen.TPoleOrderLE.mono` (many). Both
    reduce to the last two components. Single-component names are unchanged, so
    `conjPoleBound` et al. still match, while the generic `neg`/`mul`/`qTwist`/
    `qExpand` no longer collide with the unrelated top-level declarations the
    last-name public lookup finds first.
    """
    # `_root_.` may now be preceded by an enclosing-namespace prefix, so strip it
    # wherever it occurs rather than only at the start.
    raw = re.sub(r"(?:^|\.)_root_\.", ".", raw).lstrip(".")
    parts = raw.split(".")
    return ".".join(parts[-2:]) if len(parts) >= 2 else parts[-1]


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument(
        "--flt",
        default=str(Path.home() / "proj" / "fermats-last-theorem"),
        help="path to the pinned fermats-last-theorem clone",
    )
    args = ap.parse_args()
    flt = Path(args.flt)

    source: dict[str, list[tuple[str, str, str]]] = {}
    # The pin's `private` declarations, keyed by their dotted name. Consulted
    # only when the public last-name lookup fails, so it can never change a
    # match that the public surface already supplies; it verifies the promoted
    # prelude against FLT's own (private) statements instead of exempting them.
    # Both maps hold *all* candidates for a name: several pin files can declare
    # the same last name with different statements, and a port declaration is
    # identical when it matches any of them (not merely the first file read).
    dotted_source: dict[str, list[tuple[str, str, str]]] = {}
    for rel in SOURCES:
        p = flt / rel
        if not p.exists():
            print(f"warning: missing source {p}", file=sys.stderr)
            continue
        text = p.read_text(encoding="utf-8")
        for name, (kind, stmt) in declarations(text).items():
            source.setdefault(name, []).append((kind, stmt, rel))
        for raw, kind, stmt in raw_declarations(text, include_private=True):
            dotted_source.setdefault(promoted_key(raw), []).append((kind, stmt, rel))
            # Keep the pre-namespace-tracking behaviour as well: the bare last
            # name is registered too, so a port declaration that spells the pin's
            # promoted prelude as `ModularCurve.tight_one` (whose dotted key the
            # pin's nested `W1` namespace would not supply) still matches by last
            # name. The qualified key is what disambiguates a genuine same-file
            # collision (`CuspForm.heckeTLin` vs `ModularForm.heckeTLin`).
            dotted_source.setdefault(promoted_key(raw.rsplit(".", 1)[-1]), []).append(
                (kind, stmt, rel))

    def find(cands, kind, stmt):
        for c in cands or ():
            if c[0] == kind and c[1] == stmt:
                return c
        return None

    ok = promoted = missing = mismatch = own = 0
    for rel in PORT_FILES:
        p = LEAN / rel
        for raw, kind, stmt in raw_declarations(p.read_text(encoding="utf-8")):
            name = raw.rsplit(".", 1)[-1]
            if raw in OWN_PROOFS or name in OWN_PROOFS:
                own += 1
                continue
            if find(source.get(name), kind, stmt):
                ok += 1
                continue
            # Promoted from a pin-private declaration: the last-name lookup
            # either missed it (attributed `@[scoped simp]` in the public pin
            # copy) or found an unrelated same-named declaration; the dotted
            # name disambiguates.
            hit = find(dotted_source.get(promoted_key(raw)), kind, stmt) \
                or find(dotted_source.get(name), kind, stmt)
            if hit:
                ok += 1
                promoted += 1
                continue
            cands = (source.get(name) or dotted_source.get(promoted_key(raw))
                     or dotted_source.get(name))
            if not cands:
                print(f"MISSING IN FLT  {rel}: {raw}")
                missing += 1
                continue
            skind, sstmt, srel = cands[0]
            if skind != kind or sstmt != stmt:
                mismatch += 1
                print(f"MISMATCH  {rel}: {name}  (source {srel}, {skind})")
                print(f"    port: {stmt}")
                print(f"    flt : {sstmt}")

    print(
        f"\n{ok} statements identical ({promoted} promoted from pin-private "
        f"declarations), {mismatch} mismatched, {missing} missing, "
        f"{own} own-proof declarations exempted "
        f"({ok + mismatch + missing + own} port declarations checked)"
    )
    return 0 if mismatch == 0 and missing == 0 else 1


if __name__ == "__main__":
    raise SystemExit(main())
