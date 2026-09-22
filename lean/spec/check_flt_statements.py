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
# declaration still fails the check.
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
}

# Declaration keywords. `instance` matters for PhiGen; `structure` for Polynomial.
# The optional `private` prefix is what lets the *source* side see the pin's
# `private` helpers: FLT keeps the shared `TPoleOrderLE` prelude private in the
# six files that repeat it (or exposes it only through its `p2m_export` alias, a
# command the text checker cannot follow), yet the port promotes it into `Defs/`
# so later modules can import it. Port declarations are still read without the
# prefix, so a `private` port helper is never diffed.
# The optional leading `attrs` group makes an attributed declaration on a single
# line (`@[scoped simp] theorem qTwistEquiv_apply …`, T14) visible. Without it
# the regex anchors on `theorem`, so such a declaration was invisible on *both*
# sides; with it, the port's copy is verified like any other. Adding it changed
# no other match (T14 re-ran the checker: 0 mismatched, 0 missing).
DECL_RE = re.compile(
    r"^(?P<attrs>(?:@\[[^\]\n]*\]\s*)*)(?P<priv>private\s+)?"
    r"(?P<kind>def|theorem|lemma|abbrev|structure|instance)\s+"
    r"(?P<name>[\w.'ₐ]+)",
    re.MULTILINE,
)
FIELD_RE = re.compile(r"^\s{2,}([\w'ₐ]+)\s*:", re.MULTILINE)


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
    # `namespace ModularCurve`, but the `Theorems/` wrappers additionally qualify
    # every occurrence with the namespace. That qualification is noise for a
    # statement diff, so drop it on both sides before comparing.
    text = re.sub(r"\bModularCurve\.", "", strip_comments(text))
    return re.sub(r"\s+", " ", text).strip()


def raw_declarations(text: str, include_private: bool = False) -> list[tuple[str, str, str]]:
    """(raw name, kind, normalized statement) for each declaration in `text`.

    With `include_private`, the pin's `private` declarations are read too; the
    port side never passes it (a private port helper is not part of the surface
    being verified).
    """
    text = strip_comments(text)
    matches = list(DECL_RE.finditer(text))
    out: list[tuple[str, str, str]] = []
    for idx, m in enumerate(matches):
        if m.group("priv") and not include_private:
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
        out.append((m.group("name"), kind, stmt))
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
    raw = re.sub(r"^_root_\.", "", raw)
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

    ok = promoted = missing = mismatch = own = 0
    for rel in PORT_FILES:
        p = LEAN / rel
        for raw, kind, stmt in raw_declarations(p.read_text(encoding="utf-8")):
            name = raw.rsplit(".", 1)[-1]
            if name in OWN_PROOFS:
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
