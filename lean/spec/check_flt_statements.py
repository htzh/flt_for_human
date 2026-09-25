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
    # files. T10's *theorem* targets (`hasIntegralStructure_of_two_le`,
    # `moduleFinite_heckeAlgebra`, the `_two` one-liners and the eigenbasis-span
    # family) are NOT ported in SET 4: they need infrastructure the port does not
    # carry (HeckeEis coefficient cohomology / Eichler-Shimura / `Def_CuspForm_ModPForms`
    # for the 515-line existence proof; the Petersson inner product for the span
    # family; the Sturm bound for `intLattice_fg`). Their wrappers are therefore
    # not appended, and `HeckeFiniteAlgebra.lean` is not created; see
    # `logs/hecke-port.md` §T10.
    "Definitions/Def_ModularForm_EisensteinChiNegThree.lean",
    "Definitions/Def_CuspForm_IntegralLattice.lean",
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
    # files; the port writes each block once and keeps every helper `private`, so
    # the checker sees only the four headlines in `MonicRel.lean`.
    "Theorems/Thm_WLight_exists_analyticOnNhd_div_of_monicRel.lean",
    "Theorems/Thm_WLight_exists_mdifferentiable_div_of_monicRel.lean",
    "Theorems/Thm_WLight_exists_twist_of_flat.lean",
    "Theorems/Thm_WLight_span_inter_rational_of_twist_stable.lean",
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
    # SET-4 T10 (definitions only; the theorem targets are blocked, see the
    # `SOURCES` note and `logs/hecke-port.md` §T10).
    "FLTForHuman/ModularForms/Defs/EisensteinChiNegThree.lean",
    "FLTForHuman/ModularForms/Defs/IntegralLattice.lean",
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
    # general Eisenstein series. Only the headlines are public; every ported
    # `S_` helper is `private` (the pin keeps them in `WLightR7b`/`WLightR8a`/
    # `WLightR11g`/`WLight`/`CardG1`/`CardC`, made `private` here).
    "FLTForHuman/ModularForms/WeightOne/Basic.lean",
    "FLTForHuman/ModularForms/WeightOne/EisensteinSeries.lean",
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

    source: dict[str, tuple[str, str, str]] = {}
    # The pin's `private` declarations, keyed by their dotted name. Consulted
    # only when the public last-name lookup fails, so it can never change a
    # match that the public surface already supplies; it verifies the promoted
    # prelude against FLT's own (private) statements instead of exempting them.
    dotted_source: dict[str, tuple[str, str, str]] = {}
    for rel in SOURCES:
        p = flt / rel
        if not p.exists():
            print(f"warning: missing source {p}", file=sys.stderr)
            continue
        text = p.read_text(encoding="utf-8")
        for name, (kind, stmt) in declarations(text).items():
            source.setdefault(name, (kind, stmt, rel))
        for raw, kind, stmt in raw_declarations(text, include_private=True):
            dotted_source.setdefault(promoted_key(raw), (kind, stmt, rel))
            # Keep the pre-namespace-tracking behaviour as well: the bare last
            # name is registered too, so a port declaration that spells the pin's
            # promoted prelude as `ModularCurve.tight_one` (whose dotted key the
            # pin's nested `W1` namespace would not supply) still matches by last
            # name. The qualified key is what disambiguates a genuine same-file
            # collision (`CuspForm.heckeTLin` vs `ModularForm.heckeTLin`).
            dotted_source.setdefault(promoted_key(raw.rsplit(".", 1)[-1]), (kind, stmt, rel))

    ok = promoted = missing = mismatch = own = 0
    for rel in PORT_FILES:
        p = LEAN / rel
        for raw, kind, stmt in raw_declarations(p.read_text(encoding="utf-8")):
            name = raw.rsplit(".", 1)[-1]
            if raw in OWN_PROOFS or name in OWN_PROOFS:
                own += 1
                continue
            if name in source and source[name][0] == kind and source[name][1] == stmt:
                ok += 1
                continue
            # Promoted from a pin-private declaration: the last-name lookup
            # either missed it (attributed `@[scoped simp]` in the public pin
            # copy) or found an unrelated same-named declaration; the dotted
            # name disambiguates.
            srel = None
            sstmt = None
            skind = None
            for key in (promoted_key(raw), name):
                if key in dotted_source and dotted_source[key][0] == kind \
                        and dotted_source[key][1] == stmt:
                    skind, sstmt, srel = dotted_source[key]
                    break
            if srel is not None:
                ok += 1
                promoted += 1
                continue
            if name in source:
                skind, sstmt, srel = source[name]
            elif promoted_key(raw) in dotted_source:
                skind, sstmt, srel = dotted_source[promoted_key(raw)]
            elif name in dotted_source:
                skind, sstmt, srel = dotted_source[name]
            else:
                print(f"MISSING IN FLT  {rel}: {raw}")
                missing += 1
                continue
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
