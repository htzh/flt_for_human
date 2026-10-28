#!/usr/bin/env python3
"""LEGACY / FROZEN -- the grandfathered statement checker and its registry.

This checker still decides what is verified from two hand-maintained lists
(`PORT_FILES`, `SOURCES`).  That does not scale (it is 87 % of this file at 5 % of
the pin), so it is **frozen**: do not add modules or sources here.  New modules
wire themselves in their own header with `spec-pin:` and are checked by
`spec/check_port.py`; a module is removed from `PORT_FILES` when it is handed over.
The parser functions below (`DECL_RE`, `ENCLOSE_RE`, `norm`, `top_level_cut`) are
still the single definition of "the same statement" and are imported by the new
checker and the statement corpus; only the *lists* are retired.

Diff every Layer 0 port declaration's *statement* against the pinned FLT source.

The name/statement check was first run by hand on Layer 0a, and automating it was
a stated follow-up. This does that: for each declaration in the port, it
finds the declaration of the same name in the pinned FLT clone and compares the
statement (signature up to the first top-level `:=` / `where`; for a `structure`,
the header plus the ordered field names). Proof bodies are deliberately ignored —
the port adapts proofs, never statements. The one exception is a **propositional**
definition: `def foo : Prop := P` has a *statement* for a body, and the main pass
would compare only its type, which is `Prop`. `--prop-bodies` additionally diffs
that body (and only for `Prop`-valued defs; a computational `def` may legitimately
be reimplemented as long as it is definitionally equal).

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

**Tier 3 (unwired) is read from the provenance comments.** The policy is: everything
a listed module wires is checked, but no public declaration is *forced* to be wired —
a statement with no listed source stays in `spec/UNWIRED-PUBLIC.md`, and its
`-- pin: <pin name> (<pin file>:<line>)` comment is the exemption. That comment is
what the register (via `spec/unwired_register.py`) is built from, and it is
the only record of an unwired declaration's pin source. The checker consults it as
a fallthrough, never as a way to skip a diff that `SOURCES` can perform:

* if the marker names a pin file that `SOURCES` does not read, the declaration is
  registered tier 3 and is **exempted** (`UNWIRED`) instead of reported
  `MISSING IN FLT`, and no last-name collision with an unrelated `SOURCES`
  declaration can turn it into a spurious `MISMATCH`;
* if the marker names a pin file that `SOURCES` does read, the marker's pin name is
  the exact pin original to diff (it reaches a renamed declaration the by-name
  lookups cannot); a counterpart that exists but differs is a real `MISMATCH`, and
  only a missing counterpart is exempted.

So a marker can only *remove* a `missing`/`mismatch` that no `SOURCES` copy could
justify; it never suppresses a statement a listed pin file already provides.

Usage:

    python3 spec/old_check_stmts.py [--flt ~/proj/fermats-last-theorem]

Exit status is 0 when every statement matches, 1 otherwise.
"""
from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path

_here = str(Path(__file__).resolve().parent)
if _here not in sys.path:
    sys.path.insert(0, _here)
from lean_parser import (  # noqa: E402  (the parser now lives in its own module)
    DECL_RE, FIELD_RE, ENCLOSE_RE, strip_line_comments, namespace_events,
    enclosing_namespace, pop_frames, strip_comments, top_level_cut,
    KW_PREFIX_RE, KW_FAMILY_RE, norm, raw_declarations, declarations,
    declaration_body, declaration_bodies, prop_body_key, promoted_key,
    PIN_PREFIXES, strip_pin_prefix, KIND_EQUIV, same_kind,
)

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
    # The lower leg of the `CohCarrier` definition layer
    # (TOPIC-cohcarrier-comm-triplet.md §4): no `Theorems/` wrapper exists, so this
    # is the comparable copy for `FLTForHuman/ModularForms/Defs/CohCarrierLower.lean`.
    # Its declarations are disjoint from `Def_CohCarrier_Level`'s, so its position
    # cannot flip an earlier last-name match.
    "Definitions/Def_CohCarrier_Lower.lean",
    "Definitions/Def_CohCarrier_Inst.lean",
    "Definitions/Def_ModularCurve_XH.lean",
    # SET-H-A (TOPIC-xH-hecke-diamond-inputs.md): the `X_H(M)` definition layer.
    # The two sibling definition modules of `Def_ModularCurve_XH.lean` are the
    # comparable copies for `FLTForHuman/ModularCurve/XH/{HeckeOperator,Operators}.lean`.
    # Only the declarations those two modules actually carry are matched; the pin's
    # off-cone `heckeDivHBar`/`heckeOperatorHAlong`/`genOpH`/`diamondHBar` blocks have
    # no port declaration, so they cannot report `missing`. Inserted beside their
    # sibling — no name here collides with any earlier source (checked).
    "Definitions/Def_ModularCurve_XHHeckeOperator.lean",
    "Definitions/Def_ModularCurve_XHOperators.lean",
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
    # The `dCoordGenerates` sibling: its chain was already verified through the
    # `hasCanonicalDivisor` `S_` file above, and only the headline is new, so its
    # wrapper is the comparable copy. Appended here beside its sibling (the name is
    # unique, so no earlier last-name match can flip).
    "Theorems/Thm_AlgebraicCurve_dCoordGenerates_of_isCurveOver.lean",
    # --- P3.1a (the adic-completion layer): the pin `Definitions/` file itself is
    # the statement authority (no `Theorems/` wrapper). Appended last so no earlier
    # last-name match can flip.
    "Definitions/Def_AlgebraicCurve_PlaceCompletion.lean",
    # --- P3.1b-i (the `Place` pole/Laurent layer of the canonical-local-residue
    # construction): the pin `Definitions/` file itself is the statement authority
    # (no `Theorems/` wrapper). Appended last so no earlier last-name match can
    # flip; the pin is the full V2 file (2,173 ln) while the port module carries
    # only lines 1–789 so far (set 3.1b-ii appends the rest).
    "Definitions/Def_AlgebraicCurve_CanonicalLocalResidueInstanceV2.lean",
    # --- P3.2a (the ℙ¹ place/ord dictionary). The generic place-evaluation
    # definition file, then the eleven `Theorems/` wrappers (the interface copies
    # whose binders the eleven public nodes spell), then the eleven `S_` files
    # (the 1263-line big file supplies the 66 non-headline public declarations at
    # the pin names). Appended last so no earlier last-name match can flip.
    "Definitions/Def_AlgebraicCurve_PlaceEvaluation.lean",
    "Theorems/Thm_AlgebraicCurve_Place_evalAt_algebraMap.lean",
    "Theorems/Thm_AlgebraicCurve_Place_evalAt_congr.lean",
    "Theorems/Thm_AlgebraicCurve_Place_evalAt_inv.lean",
    "Theorems/Thm_AlgebraicCurve_Place_evalAt_mul.lean",
    "Theorems/Thm_AlgebraicCurve_Place_evalAt_ne_zero.lean",
    "Theorems/Thm_AlgebraicCurve_Place_evalAt_zpow.lean",
    "Theorems/Thm_AlgebraicCurve_Place_isRational_iff_deg_eq_one.lean",
    "Theorems/Thm_AlgebraicCurve_RationalFunctionField_deg_placeInfty.lean",
    "Theorems/Thm_AlgebraicCurve_RationalFunctionField_ord_placeInfty.lean",
    "Theorems/Thm_AlgebraicCurve_RationalFunctionField_ord_placeInfty_algebraMap.lean",
    "Theorems/Thm_AlgebraicCurve_RationalFunctionField_ord_placeOfPoint_algebraMap.lean",
    "P2M/Sol/S_AlgebraicCurve_Place_evalAt_algebraMap.lean",
    "P2M/Sol/S_AlgebraicCurve_Place_evalAt_congr.lean",
    "P2M/Sol/S_AlgebraicCurve_Place_evalAt_inv.lean",
    "P2M/Sol/S_AlgebraicCurve_Place_evalAt_mul.lean",
    "P2M/Sol/S_AlgebraicCurve_Place_evalAt_ne_zero.lean",
    "P2M/Sol/S_AlgebraicCurve_Place_evalAt_zpow.lean",
    "P2M/Sol/S_AlgebraicCurve_Place_isRational_iff_deg_eq_one.lean",
    "P2M/Sol/S_AlgebraicCurve_RationalFunctionField_deg_placeInfty.lean",
    "P2M/Sol/S_AlgebraicCurve_RationalFunctionField_ord_placeInfty.lean",
    "P2M/Sol/S_AlgebraicCurve_RationalFunctionField_ord_placeInfty_algebraMap.lean",
    "P2M/Sol/S_AlgebraicCurve_RationalFunctionField_ord_placeOfPoint_algebraMap.lean",
    # --- P3.2a, the out-of-measurement `Divisor.evalFun_*` algebra. The pin's
    # `Definitions/Def_AlgebraicCurve_PlaceEvaluationAlgebra.lean` is the
    # `Place`/`Divisor` law layer; `evalFun_single_sub_single` is published only
    # through its wrapper. Appended last so no earlier last-name match can flip.
    "Definitions/Def_AlgebraicCurve_PlaceEvaluationAlgebra.lean",
    "Theorems/Thm_AlgebraicCurve_Divisor_evalFun_single_sub_single.lean",
    "P2M/Sol/S_AlgebraicCurve_Divisor_evalFun_single_sub_single.lean",
    # --- P3.2b (the ℙ¹ residue core, chunk 1: declarations #0–#144 of the master
    # ℙ¹ `S_` file). The `Theorems/` wrapper is the interface copy; the master
    # `S_` file supplies the chunk's statements (and the pin names the later
    # chunks 3.2c–e append). Appended last so no earlier last-name match can flip.
    "Theorems/Thm_AlgebraicCurve_RationalFunctionField_trace_localResidue_placeInfty_X_pow_eq_zero.lean",
    "P2M/Sol/S_AlgebraicCurve_RationalFunctionField_trace_localResidue_placeInfty_X_pow_eq_zero.lean",
    # --- P3.2d′ (the generic local residue calculus). The `Theorems/` wrapper is
    # the interface copy for the headline; the generic `S_` file supplies the
    # `p0n22_cpf_*` family and the two `res_differentialCoeff_D_of_*` rows.
    # Appended last so no earlier last-name match can flip — the master ℙ¹ `S_`
    # file above carries `RatFunc K`-specialized copies of several of these names.
    "Theorems/Thm_AlgebraicCurve_Place_CanonicalLocalResidueDataK_res_differentialCoeff_D_mul_pow_inv_eq_zero_of_surjective_algebraMap.lean",
    "P2M/Sol/S_AlgebraicCurve_Place_CanonicalLocalResidueDataK_res_differentialCoeff_D_mul_pow_inv_eq_zero_of_surjective_algebraMap.lean",
    # --- P3.2f (the row-2 sibling atom tails). The three `Theorems/` wrappers are
    # the interface copies whose binders the port's public names spell; the three
    # `P2M/Sol/S_` files supply the unique tails. Appended last so no earlier
    # last-name match can flip. The atom-3 headline and the PF base case were
    # gated on the Tate agreement when 3.2f landed; set 3.2g now supplies them in
    # `P1/DivPowEnding.lean` and `P1/PerfectBase.lean` (registered in
    # `PORT_FILES` below), so these sources are live.
    "Theorems/Thm_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_add_trace_localResidue_placeInfty_eq_zero.lean",
    "Theorems/Thm_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.lean",
    "Theorems/Thm_AlgebraicCurve_residueTheorem_ratFunc_of_perfectField.lean",
    "P2M/Sol/S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_add_trace_localResidue_placeInfty_eq_zero.lean",
    "P2M/Sol/S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.lean",
    "P2M/Sol/S_AlgebraicCurve_residueTheorem_ratFunc_of_perfectField.lean",
    # --- P3.3a (the Tate agreement, finiteness half) ---
    # The row-3.3 shared definitions' source and the `tateCommFinite` cone. The
    # `Thm_` wrapper is the statement authority for the one target (the pin's `S_`
    # file calls it `solution`), so it comes first; the `S_` file then supplies the
    # 51 intermediate declarations (`maximalIdeal_le`, the `ValuationSubring.*`
    # valuation facts, the `tateProj`/`poleWindow*`/`kwF4R1V410a_*` blocks and the
    # `DVRQuotPow`/`DVRCotangent` discharge chain). The `Def_` file is appended last
    # because its names (`tateComm`, `tateProj`, the `KwF4gRRTate*` atoms) do not
    # collide with the `S_` surface. Two `S_` declarations — `ord_nonneg_of_mem` and
    # `mem_of_ord_nonneg` — are not re-proved: the port's `Defs/PushPull.lean`
    # public lemmas already match their wrappers. Appended last so no earlier
    # last-name match can flip.
    "Theorems/Thm_AlgebraicCurve_tateCommFinite.lean",
    "P2M/Sol/S_AlgebraicCurve_tateCommFinite.lean",
    "Definitions/Def_AlgebraicCurve_TateResidueCurrency.lean",
    # The `S_` file's `kwF4R1V410a_*` block reaches `completionIdeal` and
    # `mem_completionIdeal_pow` from the unported InlineSpecific module. The port
    # carries that closure `private` (promotion debt), so the checker does not diff
    # those copies; the source is registered so a later promotion verifies against
    # the pin's originals instead of reporting them missing.
    "Definitions/Def_DedekindDomain_AdicValuation_InlineSpecific.lean",
    # --- P3.3b (the Tate chain rule) ---
    # The wrapper is the statement authority for the one target (the pin's `S_` file
    # calls it `solution`); the `S_` file then supplies the chain-rule tail
    # (`kaehlerPullback_D`, `tateProj_idem`, the `finrankTrace` algebra, the abstract
    # Leibniz defect, `DualDom`/`tateResSndDer` and the derivation-factor assembly).
    # The pin's first 1,637 lines are the set-3.3a prelude, already verified against
    # the sources above, and 40 of the `S_` rows are the port's public
    # `Tate/CommFinite.lean` / `P1/EnginePrelude.lean` declarations; the checker
    # matches them there. Appended last so no earlier last-name match can flip.
    "Theorems/Thm_AlgebraicCurve_tateChainRule.lean",
    "P2M/Sol/S_AlgebraicCurve_tateChainRule.lean",
    # --- P3.3d (the Tate trace compatibility) ---
    # The wrapper is the statement authority for the one target (the pin's `S_` file
    # calls it `solution`); the `S_` file then supplies the trace-compatibility tail
    # (`finrankTrace` cyclicity/additivity, `SameRangeIdemProjectors` and the
    # projector-independence computation, the block decomposition along an integral
    # basis and the separable global headline). The pin's first ~2,250 lines are the
    # set-3.3a prelude, already verified against the sources above, and 53 of the
    # `S_` rows are the port's public `Tate/CommFinite.lean` /
    # `Defs/PushPull.lean` / `P1/EnginePrelude.lean` declarations; the checker
    # matches them there. Appended last so no earlier last-name match can flip.
    "Theorems/Thm_AlgebraicCurve_tateTraceCompat_of_isSeparable.lean",
    "P2M/Sol/S_AlgebraicCurve_tateTraceCompat_of_isSeparable.lean",
    # --- P3.3c (the Tate agreement) ---
    # The wrapper is the statement authority for the headline `tateAgreement` (the
    # pin's `S_` file calls it `solution`); the `S_` file then supplies the agreement
    # tail. 37 of its rows are byte-identical to the already-verified
    # `Tate/CommFinite.lean` (the shared `tateCommFinite` chain) or `P1/DivPow.lean`
    # (`kwHgfV352_localResidueCompletion_{spec,algebraMap}`), and the three pin-private
    # `Place` ord helpers are `Defs/PushPull.lean`'s public lemmas; the checker matches
    # those imports there. 8 `def … : Prop` rows plus `cohenB` are `port_advise`
    # false positives (`EisensteinWeightOne.E1Chi3IsModular` / `adicIntegersKSubmod`
    # are the `def`-body attractors) and are genuinely new. Appended last so no
    # earlier last-name match can flip.
    "Theorems/Thm_AlgebraicCurve_tateAgreement.lean",
    "P2M/Sol/S_AlgebraicCurve_tateAgreement.lean",
    # --- P3.4 (trace-completion commutation then the completion trace sum) ---
    # The two `Theorems/` wrappers are the statement authority for the two targets
    # (both pin `S_` files call them `solution`), so they come first; the `S_` files
    # then supply the wire lemma `kwF4gRRTate_RTCC_of_tate` (3.4a) and the
    # completionTraceSum engine rows (3.4b). The pin's `_v2` twin is dropped per the
    # PORTING-RR §3 name policy (one name per piece). Appended last so no earlier
    # last-name match can flip.
    "Theorems/Thm_AlgebraicCurve_residueTraceCompletionCommute.lean",
    "Theorems/Thm_AlgebraicCurve_completionTraceSum_of_isSeparable.lean",
    "P2M/Sol/S_AlgebraicCurve_residueTraceCompletionCommute.lean",
    "P2M/Sol/S_AlgebraicCurve_completionTraceSum_of_isSeparable.lean",
    # --- P3.6 (row 6, the K ending) ---
    # The two `Theorems/` wrappers are the statement authority for the two public
    # headlines (the pin `S_` files call both `solution`), so they come first; the
    # `S_` files then supply the row-6 engine (`KCotrace.lean`) and its assembly
    # (`KFamily.lean`), and the `RatFunc` file's `p0n22_cpf_*` row. The four
    # `def … : Prop` rows (`FiberKaehlerCotraceResidueIdentity`,
    # `CotraceResidueIdentityOnFiberLocalized`, `CotraceFiberLocalizedPolarApprox`,
    # `IsSeparatingTranscendental`) plus `KwF4R1V384a{CompletionSemilocalBij,
    # DistinctKernels,FinrankCompletionEF}` are `port_advise` false positives
    # (`EisensteinWeightOne.E1Chi3IsModular` is the `def`-body attractor) and are
    # genuinely new; the three `KwF4R1V384a*` rows stay `private` in
    # `Tate/CompletionTraceSum.lean`. Appended last so no earlier last-name match
    # can flip.
    "Theorems/Thm_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.lean",
    "P2M/Sol/S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.lean",
    "Theorems/Thm_AlgebraicCurve_residueTheoremK_of_isAlgClosed.lean",
    "P2M/Sol/S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.lean",
    # --- P3.7 (row 3.7, the RR assembly against the K ending) ---
    # The public headline, verbatim from its `Thm_` wrapper, then the pin's `S_`
    # file. Its 277 declarations include the inlined phase-1 engine (already
    # sourced by the rows-2–3.6 entries above) plus the residual K-route chain
    # (`p0n20_rr_constantsAreBase_of_isAlgClosed`, the `p0n25_wkc_*`
    # `MirrorAssembly` and the adapters over `Genus/Index`/`Genus/Stichtenoth`).
    # Appended last so no earlier last-name match can flip.
    "Theorems/Thm_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.lean",
    "P2M/Sol/S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.lean",
    # --- P3.7b (the K-route general `ResidueTheorem`) ---
    # Two tiny producers: the 21-line bridge `residueTheorem_of_residueTheoremK`
    # (`weilOfKaehler = weilOfKaehlerK`) and `residueTheorem_of_isAlgClosed`
    # (`residueTheorem_of_residueTheoremK residueTheoremK_of_isAlgClosed`, row 3.6).
    # The perfect-field producer `residueTheorem_of_perfectField` is row 3.5 and is
    # not here. Wrappers first, then the `S_` files. Appended last.
    "Theorems/Thm_AlgebraicCurve_residueTheorem_of_residueTheoremK.lean",
    "P2M/Sol/S_AlgebraicCurve_residueTheorem_of_residueTheoremK.lean",
    "Theorems/Thm_AlgebraicCurve_residueTheorem_of_isAlgClosed.lean",
    "P2M/Sol/S_AlgebraicCurve_residueTheorem_of_isAlgClosed.lean",
    # --- The Capstone interface tail, continued: the pin's existence corollary ---
    # `nonempty_modularPolynomialData` is `Theorems/Thm_ModularCurve_nonempty_modularPolynomialData.lean`,
    # landed in `Capstone.lean` from the port's stronger `exists_phiIrreducible`
    # (FLT proves it by the same `minpoly` block). Appended last so no earlier
    # last-name match can flip; the wrapper is the comparable copy.
    "Theorems/Thm_ModularCurve_nonempty_modularPolynomialData.lean",
    # --- The degree-one place layer ---
    # `isAlgebraic_adjoin_of_transcendental` (generic) and
    # `relfinrank_laurentBaseChange_modularFunctionFieldFull` (the all-divisors
    # specialization of the ported general `relfinrank_laurentBaseChange`) are
    # public wrappers. The headline `deg_eq_one_modularFunctionFieldBar` is a
    # wrapper too; its `B2Deg` helpers live in the pin's `S_` file, which also
    # supplies the promoted `deg_eq_one_of_isAlgebraic_adjoin` (the only helper
    # the port makes public). Wrappers before the `S_` file; appended last so no
    # earlier last-name match can flip.
    "Theorems/Thm_AlgebraicCurve_isAlgebraic_adjoin_of_transcendental.lean",
    "Theorems/Thm_ModularCurve_relfinrank_laurentBaseChange_modularFunctionFieldFull.lean",
    "Theorems/Thm_ModularCurve_deg_eq_one_modularFunctionFieldBar.lean",
    "P2M/Sol/S_ModularCurve_deg_eq_one_modularFunctionFieldBar.lean",
    # --- The bar principal divisors and the `jqModC` integral ratio ---
    # `hasPrincipalDivisors_modularFunctionFieldBar_unconditional` is the
    # unconditional wrapper over the ported `hasPrincipalDivisors_..._bar` +
    # `modularPolynomialFamily`. `jqModC_mem_intFormRatiosC` is a wrapper; the
    # `intSeriesC`/`intFormRatiosC` vocabulary it exposes is diffed against
    # `Definitions/Def_ModularCurve_X1.lean` (already listed above). Appended last
    # so no earlier last-name match can flip.
    "Theorems/Thm_ModularCurve_hasPrincipalDivisors_modularFunctionFieldBar_unconditional.lean",
    "Theorems/Thm_ModularCurve_jqModC_mem_intFormRatiosC.lean",
    # --- Two more short corollaries reusing ported machinery ---
    # `transcendental_coeffEmb_jq` is the bar-field analogue of the ported
    # `transcendental_jqModC` (via `coeffEmb_jq` and the `Subalgebra` subtype
    # transport); `jqModC_eq_qExpansion_E4_cube_div_discriminant` is the ported
    # `jqModC_eq_div` with the two ported `q`-expansion identities substituted.
    # Appended last so no earlier last-name match can flip.
    "Theorems/Thm_ModularCurve_transcendental_coeffEmb_jq.lean",
    "Theorems/Thm_ModularCurve_jqModC_eq_qExpansion_E4_cube_div_discriminant.lean",
    # --- The integral weight-one form's existence ---
    # `IntegralWeightOneForm` is the pin's `Def_ModularCurve_IgusaFunctionFieldX1.lean`
    # structure (only the structure is ported; the Igusa function-field defs after it
    # are deferred). The headline is a wrapper; the construction's helpers are
    # pin-internal and transcribed `private`. Appended last so no earlier last-name
    # match can flip.
    "Definitions/Def_ModularCurve_IgusaFunctionFieldX1.lean",
    "Theorems/Thm_ModularCurve_nonempty_integralWeightOneForm.lean",
    # The J-side Frobenius-charpoly payload. The port promotes its rank-two
    # conversion helper `charpoly_eq_of_quadratic_of_det` (public in the pin's
    # generated `E1G1ES` namespace, conceptually private, re-proved in eight `S_`
    # files) as `LinearMap.charpoly_eq_of_quadratic_of_det`. Registering this
    # carrier lets the checker diff the promotion against the pin's own statement
    # instead of exempting it. Appended last so no earlier last-name match flips.
    "P2M/Sol/S_ModularCurve_exists_galoisRepAdic_charpoly_frobenius_of_heckeDiamondChar.lean",
    # --- The characteristic-ℓ Frobenius q-expansion relation (charLFrobenius) ---
    # The ten prerequisite wrappers plus the target; the definition modules the
    # ported `qExpFrobenius*` API is transcribed from. `Def_ModularCurve_X1.lean`
    # is already listed above (for `intSeriesC`/`intFormRatiosC`); the generic
    # `Def_ModularCurve_X0ModL` / `_FrobeniusModL` files are listed *only* as
    # sources for the three generic Frobenius-identity lemmas and the two
    # `qExpandAlgHomC`/`coeffMap_ofPowerSeries` declarations the ported `qExp`
    # copy consumes — the generic `modularFunctionFieldFullC` module itself is
    # deliberately not ported (dedup decision). Appended last so no earlier
    # last-name match can flip.
    "Theorems/Thm_Algebra_IsSeparable_of_finrank_fieldRange_frobenius_eq.lean",
    "Theorems/Thm_AlgebraicCurve_isCurveOver_of_transcendental.lean",
    "Theorems/Thm_AlgebraicCurve_isCurveOver_of_transcendental_of_perfectField.lean",
    "Theorems/Thm_AlgebraicCurve_exists_separating_transcendental_of_perfectField.lean",
    "Theorems/Thm_AlgebraicCurve_Divisor_degree_eq_sum.lean",
    "Theorems/Thm_AlgebraicCurve_finrank_frobeniusSubfield_eq_of_transcendental.lean",
    "Theorems/Thm_AlgebraicCurve_hasPrincipalDivisors_of_finiteDimensional_of_isSeparable.lean",
    "Theorems/Thm_AlgebraicCurve_hasPrincipalDivisors_of_transcendental_of_isSeparable.lean",
    "Theorems/Thm_AlgebraicCurve_kaehlerRankOne_of_transcendental.lean",
    "Theorems/Thm_AlgebraicCurve_Place_finite_residueField_of_finiteDimensional.lean",
    "Theorems/Thm_AlgebraicCurve_RationalFunctionField_hasPrincipalDivisors.lean",
    # `eq_placeInfty_iff_forall_ne_ofHeightOneSpectrum` is the last literal
    # frontier node the name-collision on `hasPrincipalDivisors` hides; it is the
    # two-line corollary of the ported `placeInfty_ne_ofHeightOneSpectrum` and
    # `subsingleton_setOf_forall_ne_ofHeightOneSpectrum`.
    "Theorems/Thm_AlgebraicCurve_RationalFunctionField_eq_placeInfty_iff_forall_ne_ofHeightOneSpectrum.lean",
    "Theorems/Thm_ModularCurve_qExpFrobeniusPullbackModL_qExpFrobeniusPushforwardModL_of_transcendental.lean",
    "Definitions/Def_ModularCurve_QExpFrobeniusModL.lean",
    "Definitions/Def_ModularCurve_X0ModL.lean",
    "Definitions/Def_ModularCurve_FrobeniusModL.lean",
    # --- Factorisable test functions on GL₂(𝔸_K) (AutomorphicForm) ---
    # The adele-ring Hausdorff instances (AdelicHaar), the level projections
    # (AdelicLevel), the factorisable-test-function definitions, and the
    # headline's `Theorems/` wrapper. Appended last.
    "Definitions/Def_NumberField_AdelicHaar.lean",
    "Definitions/Def_NumberField_AdelicLevel.lean",
    "Definitions/Def_AutomorphicForm_FactorizableTestFn.lean",
    "Theorems/Thm_AutomorphicForm_continuous_and_hasCompactSupport_of_isFactorizableTestFn.lean",
    # The `K(x)` finite-extension `EssFiniteType` headline. The pin's `S_` proof
    # is pure mathlib (`Mathlib` + `P2M.Util` only), so the wrapper is the only
    # comparable copy. Appended last.
    "Theorems/Thm_AlgebraicCurve_essFiniteType_of_transcendental_of_finiteDimensional.lean",
    # --- Principal divisors on a Weierstrass curve (the capstone route only) ---
    # The function-field-quadratic vocabulary, the two prerequisite nodes
    # (`adjoin_yCoord_eq_top`, `finiteDimensional_ratFunc_functionField`) and the
    # headline. The pin `S_` file's place/RR/class-group API is deferred, so its
    # `P2M/Sol/...` file is deliberately not listed. Appended last.
    "Definitions/Def_WeierstrassCurve_FunctionFieldQuadratic.lean",
    "Theorems/Thm_WeierstrassCurve_Affine_adjoin_yCoord_eq_top.lean",
    "Theorems/Thm_WeierstrassCurve_Affine_finiteDimensional_ratFunc_functionField.lean",
    "Theorems/Thm_WeierstrassCurve_Affine_hasPrincipalDivisors_functionField.lean",
    # --- The ModularCurve.Period API and the equivariant-primitive headline ---
    # The `ModularCurve.Period` vocabulary, the `Γ₀` period integral/lattice, the
    # general `periodOf`/`periodMapOf` layer, and the headline's wrapper. The
    # pin's `Hecke`/`PeriodTransfer`/Petersson declarations are deliberately not
    # ported, so their `Definitions/` files are only listed where used. Appended
    # last.
    "Definitions/Def_ModularCurve_PeriodMap.lean",
    "Definitions/Def_ModularCurve_PeriodMapBundled.lean",
    "Definitions/Def_ModularCurve_PeriodLattice.lean",
    "Definitions/Def_ModularCurve_PeriodOf.lean",
    "Theorems/Thm_ModularCurve_exists_hasEquivariantPrimitiveOf.lean",
    # --- SET-X1-A: the X₁ Hecke/diamond vocabulary and the two AC `Along` facts ---
    # The three pin `Definitions/` files have no `Theorems/` wrappers, so they are
    # the comparable copies for the X₁ modules. `Def_ModularCurve_X1.lean` is
    # already listed above (for `intSeriesC`/`intFormRatiosC`/`IsIntegralQExp`).
    # The two `Along` targets and the promoted `Divisor.pushforwardNormFormula`
    # take their statements from the three `Theorems/` wrappers (the `S_` files
    # call the targets `solution`). Appended last so no earlier last-name match
    # can flip.
    "Definitions/Def_ModularCurve_X1HeckeOperator.lean",
    "Definitions/Def_ModularCurve_X1Diamond.lean",
    "Definitions/Def_ModularCurve_X1HeckeModule.lean",
    "Theorems/Thm_AlgebraicCurve_Divisor_pushforwardNormFormula.lean",
    "Theorems/Thm_AlgebraicCurve_fundamentalIdentityAlong.lean",
    "Theorems/Thm_AlgebraicCurve_normFormulaAlong.lean",
    # --- SET-X1-B: the two `JOneES` function-field nodes. The `S_` files call
    # the targets `solution`, so the comparable copies are the two `Theorems/`
    # wrappers (explicit binders, one per headline). Appended last so no earlier
    # last-name match can flip.
    "Theorems/Thm_ModularCurve_JOneES_exists_transcendental_finiteDimensional_qExpFunctionFieldC.lean",
    "Theorems/Thm_ModularCurve_JOneES_exists_transcendental_finiteDimensional_laurentBaseChange.lean",
    # --- SET-X1-C: the Hecke/diamond face. Four headlines across three modules
    # (`DiamondAut.lean` carries the integral-slash assembly and the diamond
    # automorphism). The `S_` files call the targets `solution`, so the
    # comparable copies are the `Theorems/` wrappers. Appended last.
    "Theorems/Thm_ModularCurve_qExpand_image_intFormRatiosC_subset.lean",
    "Theorems/Thm_ModularCurve_exists_isIntegralQExp_smul_slash_of_mem_Gamma0.lean",
    "Theorems/Thm_ModularCurve_exists_isDiamondAut.lean",
    "Theorems/Thm_ModularCurve_exists_algEquiv_laurentBaseChange_cover.lean",
    # --- SET-X1-C capstone: `ModularCurve.heckeDiamondInputsAll` (written by the
    # manager as the effort's final wire test). Every `X1HDIGeneric`/`X1HDIInputs`
    # helper is `private`, so the only diffed declaration is the headline.
    # Appended last.
    "Theorems/Thm_ModularCurve_heckeDiamondInputsAll.lean",
    # --- The Vélu port, H0: the Weierstrass generic-point bridge ---------------
    # `transcendental_polyToFunctionField_X`, `yGen`,
    # `equation_map_polyToFunctionField_yGen` and `polyToFunctionField_eq_aeval`
    # have no `Theorems/` wrapper: the pin inlines them into every `S_` file that
    # needs them (ten in the Vélu slice). This `S_` file is the smallest of the
    # ten and declares all four publicly, so it is the comparable copy; the
    # port's home is `FLTForHuman/WeierstrassCurve/FunctionFieldQuadratic.lean`.
    # Appended last so no earlier last-name match can flip.
    "P2M/Sol/S_WeierstrassCurve_Affine_exists_algHom_functionField_baseChange_finrankAlong_eq.lean",
    # --- SET-1 (the Vélu port): the Weierstrass place dictionary and the Vélu
    # vocabulary/formulas. The four `Definitions/` modules carry the transcribed
    # `velu*` declarations; the map `S_` file is the canonical statement copy for
    # the B/C/D clusters and the res `S_` file repeats them with the adapted proof
    # bodies. The hasPrincipalDivisors `S_` file (A1) is appended last, as the
    # work order requires, so no earlier last-name match can flip.
    "Definitions/Def_WeierstrassCurve_Velu.lean",
    "Definitions/Def_WeierstrassCurve_VeluQuotientMap.lean",
    "Definitions/Def_WeierstrassCurve_VeluPointMap.lean",
    "Definitions/Def_WeierstrassCurve_OddOrderSummingSet.lean",
    "P2M/Sol/S_WeierstrassCurve_velu_map_equation_of_oddOrderSummingSet_of_isAlgClosed.lean",
    "P2M/Sol/S_WeierstrassCurve_exists_veluFunctionFieldHom_restrictAlong_placeOfPoint_eq_of_isAlgClosed.lean",
    "P2M/Sol/S_WeierstrassCurve_Affine_hasPrincipalDivisors_functionField.lean",
    # --- Capstone H3 (`Velu/MapEquation.lean`). The two headline statements are
    # the `Theorems/` wrappers' (the map `S_` file declares them only as
    # `solution`), so they are appended last: the statement authority for
    # `velu_map_equation_of_oddOrderSummingSet{,_of_isAlgClosed}` is the wrapper,
    # not the `S_` file.
    "Theorems/Thm_WeierstrassCurve_velu_map_equation_of_oddOrderSummingSet_of_isAlgClosed.lean",
    "Theorems/Thm_WeierstrassCurve_velu_map_equation_of_oddOrderSummingSet.lean",
    # --- Capstone H4 (`Velu/RestrictAlong.lean`). The two headline statements are
    # the `Theorems/` wrappers' (the res `S_` file declares them only as
    # `solution`), so they are appended last; the module currently carries the
    # engine only (the headlines are blocked on unported upstream -- see the
    # module header), so these two entries are inert until the headlines land.
    "Theorems/Thm_WeierstrassCurve_exists_veluFunctionFieldHom_restrictAlong_placeOfPoint_eq_of_isAlgClosed.lean",
    "Theorems/Thm_WeierstrassCurve_exists_veluFunctionFieldHom_restrictAlong_placeOfPoint_eq.lean",
    # --- H5a: the Weierstrass genus-one place gate (`GenusOnePlaceGate`,
    # `placeOfPoint`, the divisor/`Pic0` dictionary and `AbelTheorem`) and the
    # conditional-currency isogeny dictionary. The three `Definitions/` modules
    # carry the transcribed vocabulary; the three `Theorems/` wrappers are the
    # statement authority for `placeOfPoint_some_eq_ofHeightOneSpectrum`,
    # `algebraMap_mk_C_X_notMem_toValuationSubring_placeOfPoint_zero` and
    # `GenusOnePlaceGate.ext_of_isCentred`. Appended last so no earlier last-name
    # match can flip.
    "Definitions/Def_WeierstrassCurve_GenusOnePic0.lean",
    "Definitions/Def_WeierstrassCurve_GenusOnePlaceGateCentred.lean",
    "Definitions/Def_Isogeny_ConditionalCurrency.lean",
    "Theorems/Thm_WeierstrassCurve_Affine_placeOfPoint_some_eq_ofHeightOneSpectrum.lean",
    "Theorems/Thm_WeierstrassCurve_Affine_algebraMap_mk_C_X_notMem_toValuationSubring_placeOfPoint_zero.lean",
    "Theorems/Thm_WeierstrassCurve_Affine_GenusOnePlaceGate_ext_of_isCentred.lean",
    # The Patching vocabulary. The checker now matches `class` declarations
    # (2026-10-04), so the four port classes in
    # `FLTForHuman/Patching/PatchingConstruction.lean` (`IsAdicTopology`,
    # `Algebra.TopologicallyFG`, `IsPatchingSystem`, `PatchingAlgebra.smulData`)
    # need their pin source to be diffable. Appended last.
    "Definitions/Def_Patching_SystemTypes.lean",
    # --- H5b: the kernel-cardinality engine (`WeierstrassCurve/Isogeny/NatCard.lean`).
    # The headline and the three helper wrappers are stated by their `Theorems/`
    # wrappers (appended last); the three `S_` files are the statement authority
    # for the proof-local helpers that the module transcribes verbatim in its
    # `section Prerequisites` blocks (`IntegralAt`, the polar-locus finiteness
    # lemmas, `ord_deriv_pos_of_ramificationIndex_ne_one`, `S13Bridge.*`,
    # `mk_Y_ne_zero`/`mk_Y_mul_mk_Y_add`/`algebraMap_mk_C_C` and the whole
    # `ModularCurve.kw_fdn2_qephod_hend*` chain).
    "Theorems/Thm_WeierstrassCurve_Affine_natCard_ker_pointMapOfPushforward_eq_finrankAlong_of_separableAlong.lean",
    "Theorems/Thm_AlgebraicCurve_Place_restrictAlong_surjective.lean",
    "Theorems/Thm_AlgebraicCurve_Place_eq_ofHeightOneSpectrum_of_XClass_mem_nonunits_of_YClass_mem_nonunits.lean",
    "Theorems/Thm_WeierstrassCurve_Affine_FunctionField_exists_eq_valuationSubring_of_X_mem.lean",
    "P2M/Sol/S_WeierstrassCurve_Affine_natCard_ker_pointMapOfPushforward_eq_finrankAlong_of_separableAlong.lean",
    "P2M/Sol/S_AlgebraicCurve_Place_eq_ofHeightOneSpectrum_of_XClass_mem_nonunits_of_YClass_mem_nonunits.lean",
    "P2M/Sol/S_WeierstrassCurve_Affine_FunctionField_exists_eq_valuationSubring_of_X_mem.lean",
    # CARRY-FORWARD entry #1 intersection: the `Theorems/` wrapper for the
    # `relNorm_eq_pow_of_isMaximal_of_isSeparable` node, whose `S_`-private
    # helper the Vélu restrictAlong route transcribed. The public wrapper is
    # promoted beside it in `Velu/RestrictAlong.lean`; appended last.
    "Theorems/Thm_AlgebraicCurve_relNorm_eq_pow_of_isMaximal_of_isSeparable.lean",
    # --- H5 SET-1: the `DualEndData` algebra the isogeny-endomorphism column is
    # stated in. A mathlib-only leaf, transcribed verbatim from its definition
    # file. Appended last so no earlier last-name match can flip.
    "Definitions/Def_DualIsogenyAPI.lean",
    # --- H5 SET-1: the two big `S_` files are the statement authority for the
    # shared `IsogenyEndDatum` engine
    # (`FLTForHuman/WeierstrassCurve/IsogenyEndDatum/Engine.lean`). The primary
    # file comes first (declaration order), the second copy second. Appended
    # last so no earlier last-name match can flip.
    "P2M/Sol/S_WeierstrassCurve_Affine_IsogenyEndDatum_exists_dualEndData_dual_mem_and_norm_eq_finrankAlong.lean",
    "P2M/Sol/S_WeierstrassCurve_Affine_IsogenyEndDatum_exists_restrictAlong_placeOfPoint_eq_add.lean",
    # --- H5 SET-2: the `restrictAlong`-add column
    # (`FLTForHuman/WeierstrassCurve/IsogenyEndDatum/RestrictAlongAdd.lean`). The
    # canonical specialize node's own `S_` file is listed for the 97 declarations
    # it shares with the res `S_` file (the res file already wins those lookups);
    # the two `Theorems/` wrappers are the statement authority for the node's
    # public name and for the additivity headline (neither last name occurs in
    # the `S_` files). Appended last so no earlier last-name match can flip.
    "P2M/Sol/S_WeierstrassCurve_Affine_FunctionField_addX_addY_specialize_at_place.lean",
    "Theorems/Thm_WeierstrassCurve_Affine_FunctionField_addX_addY_specialize_at_place.lean",
    "Theorems/Thm_WeierstrassCurve_Affine_IsogenyEndDatum_exists_restrictAlong_placeOfPoint_eq_add.lean",
    # --- H5 SET-3: the dual-end-data column
    # (`FLTForHuman/WeierstrassCurve/IsogenyEndDatum/DualEndData.lean`). The dual
    # `S_` file is already registered above (SET-1) as the shared-engine
    # authority; the public headline's statement is the `Theorems/` wrapper,
    # which carries a last name absent from the `S_` files. Appended last so no
    # earlier last-name match can flip.
    "Theorems/Thm_WeierstrassCurve_Affine_IsogenyEndDatum_exists_dualEndData_dual_mem_and_norm_eq_finrankAlong.lean",
    # --- H5 SET-3: the H5 vocabulary tail
    # (`FLTForHuman/WeierstrassCurve/IsogenyEndDatum/Vocabulary.lean`). The four
    # `S_` files carry the proofs; their `Theorems/` wrappers are the statement
    # authority. The plain `natCard_ker_pointMapOfPushforward` sibling is
    # registered beside its landed `_of_separableAlong` copy (the latter is
    # listed earlier, so it keeps winning the shared last names). Appended last
    # so no earlier last-name match can flip.
    "P2M/Sol/S_WeierstrassCurve_Affine_IsogenyEndDatum_pointEnd_apply_eq_sub.lean",
    "P2M/Sol/S_WeierstrassCurve_Affine_IsogenyHomDatum_pointHom_apply_eq_sub.lean",
    "P2M/Sol/S_WeierstrassCurve_Affine_IsogenyEndDatum_exists_pointEnd_eq_add.lean",
    "P2M/Sol/S_WeierstrassCurve_Affine_natCard_ker_pointMapOfPushforward_eq_finrankAlong.lean",
    "Theorems/Thm_WeierstrassCurve_Affine_IsogenyEndDatum_pointEnd_apply_eq_sub.lean",
    "Theorems/Thm_WeierstrassCurve_Affine_IsogenyHomDatum_pointHom_apply_eq_sub.lean",
    "Theorems/Thm_WeierstrassCurve_Affine_IsogenyEndDatum_exists_pointEnd_eq_add.lean",
    "Theorems/Thm_WeierstrassCurve_Affine_natCard_ker_pointMapOfPushforward_eq_finrankAlong.lean",
    # --- The torsion-API promotion (H5 follow-up). The generic `ZMod n × ZMod n`
    # classification of `A[n]` (Mathlib-only, `FLTForHuman/Algebra/ZModTorsion.lean`)
    # and the elliptic char-free `zsmul` surjectivity plus its torsion
    # classification (`FLTForHuman/Elliptic/TorsionZMod.lean`). The three
    # `Theorems/` wrappers are the statement authority; the two `S_` files are
    # listed after them so the promoted public helpers (`nsmul_surjective_charfree`,
    # `exists_zsmul_eq`, the `preΨ'` companions and the generic engine) diff against
    # their pin originals. The pin's public `solution` is not exposed in the port
    # (SET-2 pattern), so the wrapper names carry the headline statements. Appended
    # last so no earlier last-name match can flip.
    "Theorems/Thm_AddCommGroup_nonempty_zmod_prod_addEquiv_torsionBy_of_card_torsionBy_eq_sq.lean",
    "Theorems/Thm_WeierstrassCurve_Affine_Point_exists_zsmul_eq_of_isAlgClosed.lean",
    "Theorems/Thm_WeierstrassCurve_nonempty_torsionBy_addEquiv_zmod_prod_of_isAlgClosed.lean",
    "P2M/Sol/S_AddCommGroup_nonempty_zmod_prod_addEquiv_torsionBy_of_card_torsionBy_eq_sq.lean",
    "P2M/Sol/S_WeierstrassCurve_Affine_Point_exists_zsmul_eq_of_isAlgClosed.lean",
    # --- V1 SET-1 (the Vélu port), the order-two quotient column. The thirteen
    # `Theorems/` wrappers are the statement authority for the twelve `OrderTwo`
    # nodes and the `OrderTwoMap` headline; the three `Definitions/` files are
    # the authority for the vocabulary they declare (`veluQuotient2`/its
    # projections, `velu2QuadDisc`/`velu2XNum`/`velu2YNum`/`velu2X`/`velu2Y`/
    # `veluPointMap2` and the `velu2_map_*` lemmas, plus `Δ_mul_j`). The pin's
    # `S_` files are *not* listed: every proof-local helper is `private` in the
    # port, so the checker sees only the wrappers' public surface. Appended last
    # so no earlier last-name match can flip.
    "Theorems/Thm_WeierstrassCurve_veluQuotient2_cFour.lean",
    "Theorems/Thm_WeierstrassCurve_Delta_eq_veluGx_sq_mul_velu2QuadDisc.lean",
    "Theorems/Thm_WeierstrassCurve_veluQuotient2_Delta_eq.lean",
    "Theorems/Thm_WeierstrassCurve_velu2_tangent_addX_cleared_identity.lean",
    "Theorems/Thm_WeierstrassCurve_velu2_secant_negAddY_cleared_identity.lean",
    "Theorems/Thm_WeierstrassCurve_velu2_tangent_negAddY_cleared_identity.lean",
    "Theorems/Thm_WeierstrassCurve_veluGx_ne_zero_of_two_torsion.lean",
    "Theorems/Thm_WeierstrassCurve_velu2QuadDisc_ne_zero_of_two_torsion.lean",
    "Theorems/Thm_WeierstrassCurve_veluQuotient2_Delta_ne_zero.lean",
    "Theorems/Thm_WeierstrassCurve_isElliptic_veluQuotient2_of_isElliptic.lean",
    "Theorems/Thm_WeierstrassCurve_veluQuotient2_j.lean",
    "Theorems/Thm_WeierstrassCurve_exists_enum_twoTorsion_veluQuotient2_discriminant_ne_zero.lean",
    "Theorems/Thm_WeierstrassCurve_exists_addMonoidHom_coe_eq_veluPointMap2.lean",
    "Definitions/Def_WeierstrassCurve_VeluOrderTwo.lean",
    "Definitions/Def_WeierstrassCurve_VeluPointMap2.lean",
    "Definitions/Def_WeierstrassCurve_VeluQuotientJInvariant.lean",
    # --- V1 SET-2: the four odd-order wrappers, the two counting wrappers, and
    # the `Definitions/` files the new modules port (a vocabulary block has no
    # wrapper). `Def_..._VeluEquivariance` is listed whole; the port carries its
    # `map_velu*`/`map_veluQuotient` block only. `Def_..._VeluVariableChange` is
    # listed whole, as ported. `Def_..._VariableChangePointEquiv` supplies the
    # `vcX`/`vcY`/`vcXInv`/`vcYInv`/`vcFun`/`vcInvFun`/`variableChangeEquiv` core
    # that `Def_..._VeluVariableChange` imports; appended last.
    "Theorems/Thm_WeierstrassCurve_isOddVeluSet_oddOrderSummingSet.lean",
    "Theorems/Thm_WeierstrassCurve_veluQuotient_oddOrderSummingSet_discriminant_prod_veluU_pow.lean",
    "Theorems/Thm_WeierstrassCurve_veluQuotient_oddOrderSummingSet_discriminant_ne_zero_of_addOrderOf_eq.lean",
    "Theorems/Thm_WeierstrassCurve_exists_enum_cyclicKernels_veluQuotient_discriminant_ne_zero.lean",
    "Theorems/Thm_ZMod_natCard_isAddCyclic_addSubgroup_prod_eq_dedekindPsi.lean",
    "Theorems/Thm_AddCommGroup_natCard_isAddCyclic_addSubgroup_eq_dedekindPsi_of_addEquiv_torsionBy.lean",
    "Definitions/Def_WeierstrassCurve_VeluVariableChange.lean",
    "Definitions/Def_WeierstrassCurve_VeluEquivariance.lean",
    "Definitions/Def_WeierstrassCurve_VariableChangePointEquiv.lean",
    # --- V1 SET-3: the quotient-`j` column. The three `Theorems/` wrappers are the
    # statement authority for `Affine.Point.vcInvFun_add` (the set's off-subject
    # prerequisite, carried by the `ucl` rule) and the two `cyclicQuotientJ_*`
    # well-definedness nodes; the pin's `Def_..._CyclicQuotientJ.lean` (207 lines,
    # **52** public declarations — the work order's "46" is the count before the
    # checker's `attrs` group made the six `@[simp] theorem a₁…a₆` projections
    # visible) is the comparable copy for the vocabulary block, which has no
    # wrapper. The pin's two `S_` files (`P2MKcCQJvc`, `P2MKcCQJbc`) are *not*
    # listed: every proof-local helper is `private` in the port, so the checker
    # never sees them. `VariableChangePoint.lean` carries `Affine.Point.vcInvFun_add`
    # only and imports the `VariableChangePointEquiv` core from
    # `Velu/Equivariance.lean` (registered above) rather than redeclaring it.
    # Appended last so no earlier last-name match can flip.
    "Theorems/Thm_WeierstrassCurve_Affine_Point_vcInvFun_add.lean",
    "Theorems/Thm_WeierstrassCurve_cyclicQuotientJ_variableChange_eq.lean",
    "Theorems/Thm_WeierstrassCurve_cyclicQuotientJ_baseChange_map_eq_of_isAlgClosed.lean",
    "Definitions/Def_WeierstrassCurve_CyclicQuotientJ.lean",
    # --- The genus-one place-gate capstone.  The headline is stated by its
    # `Theorems/` wrapper (appended last so no earlier last-name match can flip);
    # its proof-local declarations are the A1 file's, already in `SOURCES`, so only
    # the wrapper is needed for the checker to see the headline's name/statement.
    "Theorems/Thm_WeierstrassCurve_Affine_exists_genusOnePlaceGate_isCentred_and_abelTheorem.lean",
    # --- V2 SET-1 (the two Mazur gateways). The `Theorems/` wrappers are the
    # statement authority for the two headlines and for the shared coordinate-ring
    # pair and the two light torsion aliases (the two coordinate-ring `S_` files are
    # *not* listed: the port transcribes only their statements, and the wrappers
    # carry them). The gateway-1 `S_` file is the statement authority for the helper
    # declarations the wrappers do not carry (the inertia-degree composite, the two
    # `Along` maps, the `Pic0` composite, the `IsogenyEndDatum` closure block and the
    # submonoid bridge); it is listed whole, and the port's module carries each of its
    # relevant declarations at the pin name. The gateway-2 `S_` file is the authority
    # for the whole `Ws13S7` prelude and the `s7_…` headline. Appended last so no
    # earlier last-name match can flip.
    "Theorems/Thm_WeierstrassCurve_Affine_CoordinateRing_isDedekindDomain.lean",
    "Theorems/Thm_WeierstrassCurve_Affine_CoordinateRing_exists_eq_XYIdeal.lean",
    "Theorems/Thm_WeierstrassCurve_card_torsion_of_isAlgClosed_light.lean",
    "Theorems/Thm_WeierstrassCurve_card_torsionBy_eq_sq_of_isAlgClosed.lean",
    "Theorems/Thm_WeierstrassCurve_Affine_IsogenyEndDatum_exists_pointEnd_eq_of_mem_isogenyEndSubring.lean",
    "P2M/Sol/S_WeierstrassCurve_Affine_IsogenyEndDatum_exists_pointEnd_eq_of_mem_isogenyEndSubring.lean",
    "Theorems/Thm_WeierstrassCurve_Affine_IsogenyEndDatum_exists_sq_lt_four_mul_and_forall_exists_finrankAlong_eq.lean",
    "P2M/Sol/S_WeierstrassCurve_Affine_IsogenyEndDatum_exists_sq_lt_four_mul_and_forall_exists_finrankAlong_eq.lean",
    # --- V2 SET-2 (the Ribet-side completion). The `Theorems/` wrappers are the
    # statement authority for the two headlines and for the five prerequisites the
    # port lacked at the pin names: the separate-principal-divisors interface
    # (`Divisor.pushforwardNormFormula_of_isSeparable`, `normFormulaAlong_of_separableAlong`,
    # the `ratFunc` principal-divisors alias), the generic separable-coprime lemma,
    # the characteristic-free function-field pair and the point-map surjectivity
    # wrapper. The two headline `S_` files carry the helper declarations the wrappers
    # do not (the `P2MA6` char-free seam block for target 4). Appended last so no
    # earlier last-name match can flip.
    "Theorems/Thm_Algebra_IsSeparable_of_coprime_finrank_expChar.lean",
    "Theorems/Thm_AlgebraicCurve_Divisor_pushforwardNormFormula_of_isSeparable.lean",
    "Theorems/Thm_AlgebraicCurve_normFormulaAlong_of_separableAlong.lean",
    "Theorems/Thm_AlgebraicCurve_hasPrincipalDivisors_of_finiteDimensional_ratFunc_of_isSeparable.lean",
    "Theorems/Thm_WeierstrassCurve_Affine_hasPrincipalDivisors_functionField_of_two_ne_zero_or.lean",
    "Theorems/Thm_WeierstrassCurve_hasPrincipalDivisors_functionField_of_isElliptic.lean",
    "Theorems/Thm_WeierstrassCurve_Affine_pointMapOfPushforward_surjective.lean",
    "Theorems/Thm_WeierstrassCurve_exists_veluFunctionFieldHom_pointMapOfPushforward_ker_eq_zmultiples.lean",
    "Theorems/Thm_WeierstrassCurve_exists_veluPointHom_oddOrderSummingSet_of_isAlgClosed.lean",
    "P2M/Sol/S_WeierstrassCurve_exists_veluFunctionFieldHom_pointMapOfPushforward_ker_eq_zmultiples.lean",
    "P2M/Sol/S_WeierstrassCurve_exists_veluPointHom_oddOrderSummingSet_of_isAlgClosed.lean",
    # --- V3 (the translation automorphism of the function field by a point, and its
    # action on the places). The two `Theorems/` wrappers are the statement authority
    # and are appended last so no earlier last-name match can flip. The two `S_` files
    # are deliberately *not* listed: every helper this module carries beyond the
    # headlines is `private`, so the checker never reads them, and both files carry
    # the same 188 declaration names. The `DualEndData`-resident prerequisites the
    # module imports (`ord_placeOfEquation_XClass_self`,
    # `AlgebraicCurve.Place.ord_ofHeightOneSpectrum_eq_neg_log`, …) are already
    # covered by the `DualEndData` entry in `PORT_FILES`.
    "Theorems/Thm_WeierstrassCurve_Affine_exists_algEquiv_restrictAlong_placeOfPoint_eq_add.lean",
    "Theorems/Thm_WeierstrassCurve_Affine_exists_algEquiv_forall_restrictAlong_placeOfPoint_eq_add.lean",
    # --- SET-V4: the H5 vocabulary tail appended to `Vocabulary.lean` (the
    # function-field rigidity node and the kernel-to-range node). The two wrappers
    # are the only comparable copies: every helper in both `S_` files (the
    # `no3ahbad_riqsucr_a1a_*` chain and the kernel-to-range helpers) is `private` in
    # the port and the pin, and neither `S_` file is listed. Appended last.
    "Theorems/Thm_WeierstrassCurve_Affine_algHom_ext_of_forall_restrictAlong_placeOfPoint_eq.lean",
    "Theorems/Thm_WeierstrassCurve_Affine_IsogenyHomDatum_exists_pointHom_comp_eq_of_ker_le_of_isCentred.lean",
    # --- P-SET-1 (the `PeriodPair` uniformization core). The `Definitions/` entry gives
    # the dictionary its by-name coverage; the two `Theorems/` wrappers are the statement
    # authority (playbook §4.1); the two `S_` files carry the pin-private helper
    # declarations the wrappers do not. `Discriminant.lean` promotes some of those
    # helpers at the `kw_`-stripped name, verified through the §2.1 `stripped_source`
    # fallback (the `S_` file is the source of the pin's `kw_*` statements). Appended
    # last so no earlier last-name match can flip.
    "Definitions/Def_PeriodPair_Uniformization.lean",
    "Theorems/Thm_PeriodPair_discriminant_ne_zero.lean",
    "P2M/Sol/S_PeriodPair_discriminant_ne_zero.lean",
    "Theorems/Thm_PeriodPair_isUniformization_toPoint.lean",
    "P2M/Sol/S_PeriodPair_isUniformization_toPoint.lean",
    # --- P-SET-2 (the `PeriodPair` `j`-line). The two `Theorems/` wrappers are the
    # statement authority (playbook §4.1); the two `S_` files carry the pin-private
    # helpers and the `kwQepw*` pencil scaffolding the wrappers do not. The pin's
    # `kw_jLattice_ofTau_eq` is promoted at the `kw_`-stripped name
    # `PeriodPair.jLattice_ofTau_eq` (verified through the §2.1 `stripped_source`
    # fallback); the pin's `kwQepw115c_jH_surjective` (the hard core of the second
    # node) is not re-proved — it is the landed `ModularForm.j_surjective`. Appended
    # last so no earlier last-name match can flip.
    "Theorems/Thm_PeriodPair_jLattice_ofTau.lean",
    "P2M/Sol/S_PeriodPair_jLattice_ofTau.lean",
    "Theorems/Thm_PeriodPair_jLattice_surjective.lean",
    "P2M/Sol/S_PeriodPair_jLattice_surjective.lean",
    # --- D-1 (the shared base-change prelude,
    # `FLTForHuman/WeierstrassCurve/Isogeny/BaseChange.lean`). The two `S_` files
    # carry the `NoAC` spelling (§2.1: `TreeIsogenyEndDatum`, the function-field
    # map-along and the tensor-product base change) and the `General` spelling
    # (§2.3: `IsogenyEndDatum`, `[IsAlgClosed F] [IsAlgClosed F']`); the `pointPullback`
    # column and `kw_functionField_algHom_ext`/`kw_coordinateRingBasis` occur in both.
    # The two `Theorems/` wrappers are the statement authority for §2.1/§2.3 and come
    # before their `S_` files. The third `S_` file
    # (`S_WeierstrassCurve_Affine_isAddCyclic_...of_baseChange_algHom.lean`) is
    # deliberately not listed: every D-1 declaration occurs in one of these two, and
    # the declarations it alone carries (`restrictAlong_eq_infinitePlace`,
    # `pointEnd'_eq_of_seam`, the `kw_surge_hgf4_*`/`KwD5BetweenCurves*` seam) belong to
    # D-4/D-5. Appended last so no earlier last-name match can flip.
    "Theorems/Thm_WeierstrassCurve_exists_intermediateField_countable_map_eq_and_finrankAlong_eq.lean",
    "P2M/Sol/S_WeierstrassCurve_exists_intermediateField_countable_map_eq_and_finrankAlong_eq.lean",
    "Theorems/Thm_WeierstrassCurve_Affine_exists_algHom_functionField_baseChange_finrankAlong_eq.lean",
    # (`P2M/Sol/S_WeierstrassCurve_Affine_exists_algHom_functionField_baseChange_finrankAlong_eq.lean`
    # is already listed above as the H0 home of the Weierstrass generic-point bridge;
    # appending it again would only duplicate the candidate list.)
    #
    # --- D-3: the base change to an `AlgebraHom` (`BaseChangeAlgHom.lean`, whose only new
    # declaration is the headline, already matched against the wrapper above) and the
    # variable change (`VariableChangeAlgEquiv.lean`). The variable-change file's public
    # surface is the pin's `mrtw60a*` block — kept at its pin names (a solution-file prefix,
    # not a `kw_` promotion token) — plus the headline, which resolves against the wrapper.
    # The wrapper comes before its `S_` file; both are appended last so no earlier last-name
    # match can flip. Neither was listed before D-3 (checked).
    "Theorems/Thm_WeierstrassCurve_nonempty_functionField_algEquiv_of_variableChange.lean",
    "P2M/Sol/S_WeierstrassCurve_nonempty_functionField_algEquiv_of_variableChange.lean",
    # --- D-4: the conjugation headline (`Isogeny/KernelCyclicTransfer.lean`), its
    # `KwD5BetweenCurvesPMOPConjKerEquiv` seam and the `kw_surgehgf4_pck_*` block. The
    # wrapper is the statement authority for the headline; the `S_` file is the only
    # source for the seam vocabulary (the `kw_fdn2_qephod_hend2[17]*` block and the
    # `kw_surgehgf4_pck_*`/`KwD5BetweenCurvesPMOPConjKerEquiv`/`pck_s17` block are public
    # in that file and occur nowhere else in the pin). Both are appended last so no
    # earlier last-name match can flip; neither was listed before D-4 (checked).
    # `KwD5BetweenCurvesHoloLift` and `kw_fdn2_qephod_hend7_pmopKerCard_proved` are *not*
    # declared by D-4 — see the module header and the friction log.
    "Theorems/Thm_WeierstrassCurve_Affine_isAddCyclic_ker_pointMapOfPushforward_of_algEquiv_conj.lean",
    "P2M/Sol/S_WeierstrassCurve_Affine_isAddCyclic_ker_pointMapOfPushforward_of_algEquiv_conj.lean",
    # --- S-1 §1.5 (the `ℂ`-analytic seam). The `Theorems/` wrapper is the statement
    # authority for the headline; the `S_` entry below carries the *proof* and the
    # prelude, and declares no `PeriodPair.exists_differentiable_…` at all. Inserted
    # immediately **above** the `S_` file rather than appended last (the one entry of
    # this set that is not), because the wrapper must win the first-match lookup for the
    # headline; it carries exactly one declaration, whose name the `S_` entry already
    # serves, so no other row's lookup can move.
    "Theorems/Thm_PeriodPair_exists_differentiable_toPoint_comp_eq_pointMapOfPushforward_toPoint.lean",
    # --- D-5 §1.5 (the `PeriodPair` uniformization promotion set). The seam
    # `ModularCurve.KwD5BetweenCurvesHoloLift` needs `PeriodPair.kw_toPointHom`, which
    # the pin declares `private` and re-exports with `p2m_export`; set D-5 promotes it
    # (and its four companions) publicly in `Elliptic/PeriodPair/Uniformization.lean`
    # at the prefix-stripped name, verified through the §2.1 `stripped_source`
    # fallback. This `S_` file is the only source for those pin-private statements.
    # Appended last so no earlier last-name match can flip.
    "P2M/Sol/S_PeriodPair_exists_differentiable_toPoint_comp_eq_pointMapOfPushforward_toPoint.lean",
    # --- D-5 (the two `IsAddCyclic`-kernel base-change silos,
    # `FLTForHuman/WeierstrassCurve/Isogeny/KernelBaseChange.lean`). The two wrappers are
    # the statement authority (the first quantifies `(R₀ : Type u)` and concludes a
    # conjunction, the second `(R₀ : Type)` and concludes the existential over `ι₁` with
    # `∀ hN₁`); the two `S_` files then supply the shared silo surface the wrappers do not
    # — the seams (`KwD5BetweenCurvesHoloLift`, `…FFSeamBaseChange`,
    # `…KerTransportAlongEmbed`), the `kw_surge_hgf4_bc*`/`kw_surgehgf4_hfgkd_ktd_*` block
    # and the `PeriodPair`/`Place` prelude copies (which the port imports from D-1, D-2,
    # `Place/Dictionary.lean`, `IsogenyEndDatum/Engine.lean`, `Isogeny/NatCard.lean` and
    # `Elliptic/PeriodPair/`). The silo's `solution` rows are *not* ported as such: the two
    # headlines at the wrapper statements replace them. Neither file was listed before
    # D-5 (checked); `S_…of_baseChange_algHom.lean` was explicitly left out by D-1 for
    # exactly this set. Appended last so no earlier last-name match can flip.
    "Theorems/Thm_WeierstrassCurve_Affine_isAddCyclic_ker_pointMapOfPushforward_of_baseChange_algHom.lean",
    "P2M/Sol/S_WeierstrassCurve_Affine_isAddCyclic_ker_pointMapOfPushforward_of_baseChange_algHom.lean",
    "Theorems/Thm_WeierstrassCurve_Affine_exists_algHom_baseChange_of_isAddCyclic_ker_pointMapOfPushforward.lean",
    "P2M/Sol/S_WeierstrassCurve_Affine_exists_algHom_baseChange_of_isAddCyclic_ker_pointMapOfPushforward.lean",
    # --- D-6 (the two-curve countable descent,
    # `FLTForHuman/WeierstrassCurve/Isogeny/TwoCurveDescent.lean`). The wrapper is the
    # statement authority for the headline (binders spelled verbatim, including the
    # `letI : Algebra ℚ K` and the `∀ [gate instances] (hN₀)` block of the conclusion);
    # the `S_` file is the only source for the pin's `kw_iotaDescent*` family (promoted
    # at the prefix-stripped names, verified through the §2.1 `stripped_source`
    # fallback) and for the `kw_surgehgf4_hfgkd_bcIota₁NoAC` engine transcribed here.
    # The wrapper comes before its `S_` file, and both are appended last so no earlier
    # last-name match can flip. Neither was listed before D-6 (checked).
    "Theorems/Thm_WeierstrassCurve_Affine_exists_intermediateField_countable_map_eq_of_isAddCyclic_ker_pointMapOfPushforward.lean",
    "P2M/Sol/S_WeierstrassCurve_Affine_exists_intermediateField_countable_map_eq_of_isAddCyclic_ker_pointMapOfPushforward.lean",
    # --- S-2 (the lattice/index arithmetic, `Elliptic/PeriodPair/LatticeIndex.lean`).
    # Each `Theorems/` wrapper is the statement authority for its headline; its `S_` file
    # carries the proof and the pin's shared `hID_*`/torsion prelude (the pin ships both
    # twice; the port writes them once). The 978 node comes before the 2,021 node because
    # the latter's `hID` is the former's headline. Appended last so no earlier last-name
    # match can flip; none of the four was listed before S-2 (checked).
    "Theorems/Thm_PeriodPair_exists_scale_lattice_subset_and_sublatticeIndex_eq_natCard_ker.lean",
    "P2M/Sol/S_PeriodPair_exists_scale_lattice_subset_and_sublatticeIndex_eq_natCard_ker.lean",
    "Theorems/Thm_PeriodPair_exists_scale_lattice_subset_and_sublatticeIndex_eq_and_isAddCyclic_sublatticeQuotient.lean",
    "P2M/Sol/S_PeriodPair_exists_scale_lattice_subset_and_sublatticeIndex_eq_and_isAddCyclic_sublatticeQuotient.lean",
    # --- S-3 (the primitive-coset / `jLattice` column,
    # `FLTForHuman/Elliptic/PeriodPair/PrimCosetReps.lean` and
    # `FLTForHuman/Algebra/IntPairSubgroup.lean`). The wrapper is the statement authority
    # for the headline; its `S_` file carries the transport/`hu5c`/`qtzz` content and the
    # pin-private `PeriodPair` prelude lemmas re-derived in the port (the generic `ℤ²`
    # block is re-homed in `IntPairSubgroup`, matched by last name). The wrapper comes
    # before its `S_` file. Appended last so no earlier last-name match can flip; neither
    # was listed before S-3 (checked).
    "Theorems/Thm_PeriodPair_exists_mem_primCosetReps_and_jLattice_eq_of_isAddCyclic.lean",
    "P2M/Sol/S_PeriodPair_exists_mem_primCosetReps_and_jLattice_eq_of_isAddCyclic.lean",
    # --- S-4 (the `E₄³ − E₆²` / `jLattice` modular-polynomial tail,
    # `ModularCurve/ModularPolynomialE4Cube.lean` and
    # `Algebra/SpecialLinearGroupSmith.lean`). Each of the four `Theorems/` wrappers is
    # the statement authority for its headline; its `S_` file carries the pin's public
    # helper surface (the `E₄³`/`Δ` forms, the `q`-expansion bookkeeping, `jt` and the
    # `upperTriangularGL` pair, and the `SL₂(ℤ)` Smith leaf's `exists_coprime_mul_add`
    # /`main`). Each wrapper comes immediately above its `S_` file. Appended last so no
    # earlier last-name match can flip; none was listed before S-4 (checked).
    #
    # The audit's one prerequisite surprise: the work order recorded
    # `ModularForm.exists_degeneracy_Gamma0` as landed, but only its `CuspForm` twin
    # was; its wrapper is the statement authority for the twin ported into
    # `ModularForms/Level/Degeneracy.lean` for S-4. No `S_` file is needed (its
    # helpers stay `private` in the port, so the checker cannot see them).
    "Theorems/Thm_ModularForm_exists_degeneracy_Gamma0.lean",
    "Theorems/Thm_Matrix_SpecialLinearGroup_exists_eq_mul_diagonal_mul_of_gcd_eq_one.lean",
    "P2M/Sol/S_Matrix_SpecialLinearGroup_exists_eq_mul_diagonal_mul_of_gcd_eq_one.lean",
    "Theorems/Thm_ModularCurve_ModularPolynomialData_eval_E4_cube_div_discriminant_smul_eq_zero.lean",
    "P2M/Sol/S_ModularCurve_ModularPolynomialData_eval_E4_cube_div_discriminant_smul_eq_zero.lean",
    "Theorems/Thm_ModularCurve_ModularPolynomialData_eval_E4_cube_div_discriminant_coset_eq_zero.lean",
    "P2M/Sol/S_ModularCurve_ModularPolynomialData_eval_E4_cube_div_discriminant_coset_eq_zero.lean",
    "Theorems/Thm_ModularCurve_ModularPolynomialData_eval_jLattice_eq_zero_of_isAddCyclic.lean",
    "P2M/Sol/S_ModularCurve_ModularPolynomialData_eval_jLattice_eq_zero_of_isAddCyclic.lean",
    # --- SC, row S's terminal set (`topics/velu/WORKORDER-SC-capstone.md`). Three
    # modules: the two already-landed leaves
    # (`Elliptic/PeriodPair/VariableChange.lean`, `FieldTheory/NonemptyRingHomComplex.lean`)
    # and the capstone `ModularCurve/ModularPolynomialEvalJ.lean`. Each `Theorems/`
    # wrapper is the statement authority for its headline and comes immediately above
    # its `S_` file; the capstone file additionally carries the pin's `conjSeam` /
    # `separableAlong_of_charZero` / `normFormulaAlong_of_charZero` / `map_eval_map_Φ` /
    # `isElliptic_map` / `j_eq_div` / `jLattice_eq_j` / `complexCase` / `solution0` /
    # `solution` surface, all matched here. The pin's `PeriodPair` scale prelude
    # (`:45–129`) is *not* re-declared (it is S-3's `Lattice.lean`/`PrimCosetReps.lean`);
    # only `jLattice_scale` is re-derived `private`, so it is invisible to this checker.
    # Appended last so no earlier last-name match can flip; none of the six was listed
    # before SC (checked).
    "Theorems/Thm_PeriodPair_exists_variableChange_smul_weierstrassCurve_eq.lean",
    "P2M/Sol/S_PeriodPair_exists_variableChange_smul_weierstrassCurve_eq.lean",
    "Theorems/Thm_Field_nonempty_ringHom_complex_of_countable.lean",
    "P2M/Sol/S_Field_nonempty_ringHom_complex_of_countable.lean",
    "Theorems/Thm_WeierstrassCurve_Affine_eval_modularPolynomial_map_j_eq_zero_of_isAddCyclic_ker_pointMapOfPushforward.lean",
    "P2M/Sol/S_WeierstrassCurve_Affine_eval_modularPolynomial_map_j_eq_zero_of_isAddCyclic_ker_pointMapOfPushforward.lean",
    # --- ds-head (`topics/riemannRoch/WORKORDER-ds-head.md`): the four pin
    # ``AlgebraicCurve`` differential/ramification nodes. Each `Theorems/` wrapper is
    # the statement authority for its headline and comes immediately above its `S_`
    # file; the `S_` files carry the pin's public helper surface (the Hurwitz engine
    # in the `map_ne_zero_of_tame` / `two_mul_genus_sub_two_eq_of_degree_canonical`
    # pair — the same file twice — plus the `s12` prelude and the `ℙ¹` genus
    # profile). Appended last so no earlier last-name match can flip; none of the
    # eight was listed before ds-head (checked).
    "Theorems/Thm_AlgebraicCurve_genus_ratFunc_eq_zero_of_perfectField.lean",
    "P2M/Sol/S_AlgebraicCurve_genus_ratFunc_eq_zero_of_perfectField.lean",
    "Theorems/Thm_AlgebraicCurve_exists_mem_D_eq_smul_D_of_isCurveOver.lean",
    "P2M/Sol/S_AlgebraicCurve_exists_mem_D_eq_smul_D_of_isCurveOver.lean",
    "Theorems/Thm_AlgebraicCurve_map_ne_zero_of_tame.lean",
    "P2M/Sol/S_AlgebraicCurve_map_ne_zero_of_tame.lean",
    "Theorems/Thm_AlgebraicCurve_two_mul_genus_sub_two_eq_of_degree_canonical.lean",
    "P2M/Sol/S_AlgebraicCurve_two_mul_genus_sub_two_eq_of_degree_canonical.lean",
    # --- ds-head riders: the two small deferred nodes folded into existing
    # modules (`Genus/RatFunc.lean`, `Defs/KaehlerTranscendental.lean`). The
    # `CharZero` genus variant cites `genus_ratFunc_eq_zero_of_perfectField`; the
    # Kähler leaf cites `span_D_eq_top_of_transcendental` /
    # `D_ne_zero_of_transcendental`. Each wrapper immediately above its `S_` file;
    # appended last so no earlier last-name match can flip (checked).
    "Theorems/Thm_AlgebraicCurve_genus_ratFunc_eq_zero.lean",
    "P2M/Sol/S_AlgebraicCurve_genus_ratFunc_eq_zero.lean",
    "Theorems/Thm_KaehlerDifferential_exists_unique_smul_D_of_transcendental.lean",
    "P2M/Sol/S_KaehlerDifferential_exists_unique_smul_D_of_transcendental.lean",
    # --- ds-head rider: the `genusFF` `ℙ¹` closure (`topics/riemannRoch/ds-head-recon.md`
    # §10). Seven nodes; the two already-present-under-another-name rows
    # (`isCurveOver_ratFunc` = the scoped `instIsCurveOverRatFunc`,
    # `constantsAreBase_of_isAlgClosed` = `ModularCurve.p0n20_rr_…`) are landed as
    # public wrappers at the pin names, and the remaining five are thin
    # transcriptions over the ported `indexOfSpecialty_eq_finrank_H1` /
    # `functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed`. Each wrapper
    # immediately above its `S_` file; appended last so no earlier last-name match
    # can flip (checked).
    "Theorems/Thm_AlgebraicCurve_isCurveOver_ratFunc.lean",
    "P2M/Sol/S_AlgebraicCurve_isCurveOver_ratFunc.lean",
    "Theorems/Thm_AlgebraicCurve_ell_canonicalDivisor_eq_genus_of_riemannRoch.lean",
    "P2M/Sol/S_AlgebraicCurve_ell_canonicalDivisor_eq_genus_of_riemannRoch.lean",
    "Theorems/Thm_AlgebraicCurve_genus_eq_genusFF.lean",
    "P2M/Sol/S_AlgebraicCurve_genus_eq_genusFF.lean",
    "Theorems/Thm_AlgebraicCurve_constantsAreBase_of_isAlgClosed.lean",
    "P2M/Sol/S_AlgebraicCurve_constantsAreBase_of_isAlgClosed.lean",
    "Theorems/Thm_AlgebraicCurve_functionFieldRiemannRoch_of_isAlgClosed.lean",
    "P2M/Sol/S_AlgebraicCurve_functionFieldRiemannRoch_of_isAlgClosed.lean",
    "Theorems/Thm_AlgebraicCurve_functionFieldRiemannRoch_of_isAlgClosed_of_isCurveOver.lean",
    "P2M/Sol/S_AlgebraicCurve_functionFieldRiemannRoch_of_isAlgClosed_of_isCurveOver.lean",
    "Theorems/Thm_AlgebraicCurve_genusFF_ratFunc_eq_zero_of_isAlgClosed.lean",
    "P2M/Sol/S_AlgebraicCurve_genusFF_ratFunc_eq_zero_of_isAlgClosed.lean",
    # SET-H-A (`topics/hecke/TOPIC-xH-hecke-diamond-inputs.md`): the pin-public
    # originals of the X₁ diamond prelude promoted at SET-H-A. The copies in the
    # port's `X1/QExpandStretch.lean` (`isCusp_heckeDiagMatrix_smul`,
    # `heckeDiagMatrix_mul_eq`, `expandPS`, `coeff_expandPS`, `intSeriesC_expandPS`),
    # `X1/DiamondAut.lean` (`IsRatio`, `ratioField`, `toC_injective`,
    # `toC_algebraMap`, `qC_zero`, `qC_one`, `slash_inv_slash`, `slash_slash_inv`)
    # and `X1/FunctionField.lean` (`intSeriesC_add'`, `intSeriesC_neg'`) were
    # `private` while the pin writes them public in these `S_` files; dropping
    # `private` makes the checker diff them, and the pin's public statement is the
    # comparable copy. `S_…heckeDiamondInputsHAll` also supplies the two primed
    # `intSeriesC_*'` names. Appended last so no earlier last-name match can flip
    # (checked: the pre-promotion pass is unchanged). SET-H-B/C append their own
    # `S_` files and `Theorems/` wrappers beside this entry.
    "P2M/Sol/S_ModularCurve_exists_algEquiv_intertwinesAlong_diamondAutBar.lean",
    "P2M/Sol/S_ModularCurve_exists_algEquiv_intertwinesAlong_diamondAutHBar.lean",
    "P2M/Sol/S_ModularCurve_heckeDiamondInputsHAll.lean",
    # SET-H-B: the two `Theorems/` wrappers are the comparable copies of the pair
    # of headlines (the `S_` files carry the same statements as inner `solution`).
    "Theorems/Thm_ModularCurve_exists_algEquiv_intertwinesAlong_diamondAutHBar.lean",
    "Theorems/Thm_ModularCurve_exists_algEquiv_intertwinesAlong_diamondAutBar.lean",
    # SET-H-C: the seven inputs `ModularCurve.heckeInputsHAlong`. The pin's `S_`
    # file is a public `S_` file, so it is the comparable copy for the 32
    # declarations inside `HeckeInputsHAll` (its own `solution` is at a different
    # last name and is not transcribed); the wrapper is needed for the headline,
    # whose explicit binders differ from the `S_` file's section-variable inner
    # copy that shares its last name. `expandInt` needs no other source: the
    # checker diffs its statement against this file (see `PORT_FILES` and the
    # module's header). Appended last so no earlier last-name match can flip.
    "P2M/Sol/S_ModularCurve_heckeInputsHAlong.lean",
    "Theorems/Thm_ModularCurve_heckeInputsHAlong.lean",
    # SET-H-C capstone: `ModularCurve.heckeDiamondInputsHAll`. The wrapper is the
    # comparable copy — the pin's own `S_` file registers the statement only as the
    # inner `solution`. Every helper of the port's capstone is `private`, so the
    # wrapper plus `Definitions/Def_ModularCurve_XHOperators.lean` (already listed)
    # is the whole surface. Appended last so no earlier last-name match can flip.
    "Theorems/Thm_ModularCurve_heckeDiamondInputsHAll.lean",
    # --- SET-R-C prerequisite: the `JOneES` promotion. The port's
    # `ModularCurve/X1/FunctionField.lean` transcribed the pin's JOneES `S_` file
    # as four `private` inner blocks with only the headline public; the qexp head's
    # finrank target (and the relrank target) consume 51 of those helpers, so the
    # blocks were promoted to public. The pin's two files that declare them are
    # appended here (the JOneES `S_` file is the transcription source; the
    # `...le_index.lean` file carries the `eisenstein4` spelling the port uses in
    # `isIntegralQExp_A12`/`isIntegralQExp_E4` and the pin name
    # `intSeriesC_E4_cube_ne_zero`). One helper (`coeff_one_eisenstein4`, whose pin
    # counterpart `coeff_one_P4` needs the pin's `P4`) stays `private` and is not
    # diffed. Appended last so no earlier last-name match can flip.
    "P2M/Sol/S_ModularCurve_JOneES_exists_transcendental_finiteDimensional_qExpFunctionFieldC.lean",
    "P2M/Sol/S_ModularCurve_finrank_adjoin_jqModC_laurentBaseChange_qExpFunctionFieldC_le_index.lean",
    # --- SET-R-A (`topics/functionFieldGeneration/SET-R-A.md`): the two
    # Gamma0-rationality headlines. The two `S_` files above are already listed
    # (their helpers are pin copies); their headline copies are named `solution`,
    # so the comparable copies of the headlines are the `Theorems/` wrappers.
    # Appended last so no earlier last-name match can flip.
    "Theorems/Thm_ModularCurve_exists_ratCast_qExpansion_comp_smul_of_mem_Gamma0_of_dvd.lean",
    "Theorems/Thm_ModularCurve_exists_qExpansion_S_smul_eq_and_conj_eq_of_ratCast_qExpansion.lean",
    # --- SET-R-B (`topics/functionFieldGeneration/SET-R-B.md`): the `X_H`
    # relative-degree bound. The `S_` file carries the pin's public prelude
    # (matched by the new module's own declarations); the comparable copy of the
    # headline is the `Theorems/` wrapper. Appended last so no earlier last-name
    # match can flip.
    "P2M/Sol/S_ModularCurve_le_relrank_xHFunctionField_xHTopFunctionFieldC_of_not_dvd.lean",
    "Theorems/Thm_ModularCurve_le_relrank_xHFunctionField_xHTopFunctionFieldC_of_not_dvd.lean",
    # --- SET-R-C order 1 (`topics/functionFieldGeneration/SET-R-C.md`): the
    # `JOneES` finrank/index bound. The target-4 `S_` file is already listed above
    # (from the promotion pass); the comparable copy of the headline is the
    # `Theorems/` wrapper appended here. Appended last so no earlier last-name
    # match can flip.
    "Theorems/Thm_ModularCurve_finrank_adjoin_jqModC_laurentBaseChange_qExpFunctionFieldC_le_index.lean",
    # --- SET-R-C order 2 (`topics/functionFieldGeneration/SET-R-C.md`): the
    # residue-field model. Target 5's `S_` file and its `Theorems/` wrapper are
    # both new here (nothing of it was ported before), so both are appended, the
    # wrapper last. Appended last so no earlier last-name match can flip.
    "P2M/Sol/S_ModularCurve_exists_transcendental_finiteDimensional_qExpFunctionFieldC_residueField.lean",
    "Theorems/Thm_ModularCurve_exists_transcendental_finiteDimensional_qExpFunctionFieldC_residueField.lean",
    # --- SET-R-D prerequisite: the `Gamma0Integral` hub promotion. Sixteen
    # declarations of `…X1DiamondRationalForms` were `private` while the pin's
    # Atkin–Lehner `S_` file declares them publicly (and they are the engine of
    # the successor headline); they are promoted and verified against this `S_`
    # file. The same names survive `private` in two sibling namespaces of the
    # module (`…GammaNBounded`, `…X1BoundedDenominators`); the refactor round should
    # collapse the duplication. Appended last so no earlier match can flip.
    "P2M/Sol/S_ModularCurve_exists_isIntegralQExp_smul_atkinLehnerSlash_of_even.lean",
    # --- SET-R-D order 1 (`topics/functionFieldGeneration/SET-R-D.md`): Deuring's
    # degree inequality over a valuation subring. The whole engine is `private` in
    # the new module (its last names collide with other pin `S_` files already in
    # `SOURCES`), so only the headline is comparable and it is matched against its
    # `Theorems/` wrapper. Appended last so no earlier last-name match can flip.
    "Theorems/Thm_ModularCurve_finrank_adjoin_qExpFunctionFieldC_le_of_valuationSubring.lean",
    # --- SET-R-D order 2 (`topics/functionFieldGeneration/SET-R-D.md`): finiteness
    # of the `q`-expansion function field over `K(j)` for algebraically closed `K`.
    # The target's `S_` file carries the 14 public engine declarations (matched by
    # the new module's own copies) and the headline is matched against its
    # `Theorems/` wrapper. Both appended last so no earlier last-name match can
    # flip.
    "P2M/Sol/S_ModularCurve_exists_transcendental_finiteDimensional_qExpFunctionFieldC_of_isAlgClosed.lean",
    "Theorems/Thm_ModularCurve_exists_transcendental_finiteDimensional_qExpFunctionFieldC_of_isAlgClosed.lean",
    # --- SET-R-D order 3 (`topics/functionFieldGeneration/SET-R-D.md`): the
    # Atkin–Lehner / diamond slash integrality. The pin `S_` file is already listed
    # above (the prerequisite promotion appended it); the comparable copy of the
    # headline is its `Theorems/` wrapper, appended last so no earlier last-name
    # match can flip.
    "Theorems/Thm_ModularCurve_exists_isIntegralQExp_smul_atkinLehnerSlash_of_even.lean",
    # --- SET-R-E prerequisite: the definition layer. The opening
    # `ValuationSubring` block of the pin's `Def_WeierstrassCurve_ReductionMap.lean`
    # (`liesOverPrime_iff`, `natCast_mem'`,
    # `natCast_mem_maximalIdeal_of_liesOverPrime`,
    # `charP_residueField_of_liesOverPrime_def`) is homed publicly in
    # `FLTForHuman/NumberTheory/ValuationAtPlace.lean`, so the pin definition file
    # is appended to verify it. The rest of that pin module (the Weierstrass
    # reduction map) is unported. Appended last so no earlier last-name match can
    # flip.
    "Definitions/Def_WeierstrassCurve_ReductionMap.lean",
    # --- SET-R-E order 1 (`topics/functionFieldGeneration/SET-R-E.md`): the
    # `isAlgClosed` finrank/index bound in the `q`-expansion model. The `S_` file
    # supplies the pin names of the four genuinely-new rows
    # (`jqModC_eq_div` / `jqModC_mem_laurentBaseChange` / `bound_of_place` /
    # `solution`); its SET-R-D engine block (`isAlgebraic_residueField`,
    # `coe_eq_zero_of_mem_maximalIdeal_top`, `residueTopHom`) is already public in
    # `FLTForHuman/ModularCurve/X1/FunctionFieldIsAlgClosed.lean`. Its `Theorems/`
    # wrapper is appended last so the public headline copy wins a last-name match.
    "P2M/Sol/S_ModularCurve_finrank_adjoin_jqModC_qExpFunctionFieldC_le_index_of_isAlgClosed.lean",
    "Theorems/Thm_ModularCurve_finrank_adjoin_jqModC_qExpFunctionFieldC_le_index_of_isAlgClosed.lean",
    # --- SET-R-E order 2 (`topics/functionFieldGeneration/SET-R-E.md`): the two
    # Atkin–Lehner exchanges, written as one module. Both `S_` files supply the pin
    # names of the shared engine (the `H`-independent lines are homed once in
    # `FLTForHuman/ModularCurve/X1/AtkinLehnerExchange.lean`; the `Γt`/`Γb`-dependent
    # lines appear once per target under its own sub-namespace) and the pin names of
    # the two headlines (`solution`). The two `Theorems/` wrappers are the statement
    # authority and are appended last so the public headline copies win a last-name
    # match.
    "P2M/Sol/S_ModularCurve_exists_algEquiv_atkinLehner_heckeAlphaHBar_heckeBetaHBar.lean",
    "Theorems/Thm_ModularCurve_exists_algEquiv_atkinLehner_heckeAlphaHBar_heckeBetaHBar.lean",
    "P2M/Sol/S_ModularCurve_exists_algEquiv_x1x0FunctionFieldC_atkinLehner.lean",
    "Theorems/Thm_ModularCurve_exists_algEquiv_x1x0FunctionFieldC_atkinLehner.lean",
    # --- WORKORDER-W1 order 1 (`topics/deligneSerre/WORKORDER-W1-automorphisms.md`):
    # the shared point-transport prelude of the exceptional-automorphism set. Both
    # `S_` files carry the block byte-identically (char 2 under `§Action`, char 3
    # lines 18–84) and both `Theorems/` wrappers are the headline statement
    # authority. Appended last so no earlier last-name match can flip.
    "Theorems/Thm_WeierstrassCurve_exists_addMonoidHom_vcInvFun_pow_heq_and_forall_exists_ne_smul_of_char_two.lean",
    "P2M/Sol/S_WeierstrassCurve_exists_addMonoidHom_vcInvFun_pow_heq_and_forall_exists_ne_smul_of_char_two.lean",
    "Theorems/Thm_WeierstrassCurve_exists_addMonoidHom_i_tau_vcInvFun_of_char_three.lean",
    "P2M/Sol/S_WeierstrassCurve_exists_addMonoidHom_i_tau_vcInvFun_of_char_three.lean",
    # --- WORKORDER-W2 order 1 (`topics/deligneSerre/WORKORDER-W2-division-fields.md`):
    # the count-`N²` structure theorem, matched against its `Theorems/` wrapper; the
    # pin's `torsionEquiv` and `main` stay `private`, so the headline is the module's
    # only compared declaration. Appended last so no earlier last-name match can flip.
    "Theorems/Thm_WeierstrassCurve_nonempty_torsionBy_addEquiv_zmod_prod_of_natCard_torsion_eq_sq.lean",
    "P2M/Sol/S_WeierstrassCurve_nonempty_torsionBy_addEquiv_zmod_prod_of_natCard_torsion_eq_sq.lean",
    # --- WORKORDER-W2 order 2 (`topics/deligneSerre/WORKORDER-W2-division-fields.md`):
    # the `n`-division field, matched against its `Theorems/` wrapper; every helper
    # stays `private`, so the headline is the module's only compared declaration.
    # Appended last so no earlier last-name match can flip.
    "Theorems/Thm_WeierstrassCurve_exists_intermediateField_isGalois_card_torsion_eq_sq.lean",
    "P2M/Sol/S_WeierstrassCurve_exists_intermediateField_isGalois_card_torsion_eq_sq.lean",
    # --- WORKORDER-W3 (`topics/deligneSerre/WORKORDER-W3-stepcurve.md`): the odd
    # prime-degree step of the abscissa-indexed Vélu construction, matched against
    # its `Theorems/` wrapper; every helper stays `private` (including the recorded
    # local re-derivation of `sigma_eq_of_eq`), so the headline is the module's only
    # compared declaration. Appended last so no earlier last-name match can flip.
    "Theorems/Thm_WeierstrassCurve_stepCurve_stepSubgroup_eq_of_prime_ne_two.lean",
    "P2M/Sol/S_WeierstrassCurve_stepCurve_stepSubgroup_eq_of_prime_ne_two.lean",
    # --- WORKORDER-W3b (`topics/deligneSerre/WORKORDER-W3b-zmultiples.md`): equal
    # Vélu-quotient `j` forces equal cyclic subgroups, matched against its
    # `Theorems/` wrapper; every helper stays `private`, so the headline is the
    # module's only compared declaration. Appended last so no earlier last-name
    # match can flip.
    "Theorems/Thm_WeierstrassCurve_zmultiples_eq_of_veluQuotient_j_eq_of_forall_isogenyEndDatum_exists_int.lean",
    "P2M/Sol/S_WeierstrassCurve_zmultiples_eq_of_veluQuotient_j_eq_of_forall_isogenyEndDatum_exists_int.lean",
    # --- WORKORDER-W4 stage 2 (`topics/deligneSerre/WORKORDER-W4-definition-wave.md`):
    # the pin's `Def_WeierstrassCurve_TorsionIntegral.lean` is ported whole
    # (`FLTForHuman/WeierstrassCurve/Reduction/TorsionIntegral.lean`), so the pin
    # definition file is appended to verify it. Appended last so no earlier
    # last-name match can flip.
    "Definitions/Def_WeierstrassCurve_TorsionIntegral.lean",
    # --- WORKORDER-W4 stage 3: the pin's `Def_WeierstrassCurve_ReduceHom.lean` is ported
    # whole (`FLTForHuman/WeierstrassCurve/Reduction/ReduceHom.lean`), so the pin
    # definition file is appended to verify it. Appended last so no earlier last-name
    # match can flip.
    "Definitions/Def_WeierstrassCurve_ReduceHom.lean",
    # --- WORKORDER-W4 stage 4: the pin's `Def_WeierstrassCurve_ZeroComponentReduction.lean`
    # is ported whole (`FLTForHuman/WeierstrassCurve/Reduction/ZeroComponent.lean`), so the
    # pin definition file is appended to verify it. Appended last so no earlier last-name
    # match can flip.
    "Definitions/Def_WeierstrassCurve_ZeroComponentReduction.lean",
    # --- WORKORDER-W5 (set C1, `topics/deligneSerre/WORKORDER-W5-reducehom-surjective.md`):
    # reduction is surjective on the prime-to-`p` torsion. The headline is the module's only
    # public declaration; appended last so no earlier last-name match can flip.
    "Theorems/Thm_WeierstrassCurve_exists_reduceHom_eq_of_nsmul_eq_zero_of_natCast_ne_zero.lean",
    "P2M/Sol/S_WeierstrassCurve_exists_reduceHom_eq_of_nsmul_eq_zero_of_natCast_ne_zero.lean",
    # --- WORKORDER-W6 (set C2, `topics/deligneSerre/WORKORDER-W6-inertia-reduction.md`): the
    # inertia-equivariant good-reduction map. The headline is the module's only public
    # declaration; appended last so no earlier last-name match can flip.
    "Theorems/Thm_WeierstrassCurve_exists_inertia_equivariant_reduction_of_variableChange_eq_map.lean",
    "P2M/Sol/S_WeierstrassCurve_exists_inertia_equivariant_reduction_of_variableChange_eq_map.lean",
    # --- ModularCurve set C1 (manager append into an existing module): the q-expansion
    # Frobenius inputs. The headline is added to `Frobenius/QExpModL.lean` (already in
    # `PORT_FILES`), whose private machinery it concludes; appended last so no earlier
    # last-name match can flip.
    "Theorems/Thm_ModularCurve_qExpFrobeniusInputsModL_and_finrankAlong_of_transcendental.lean",
    "P2M/Sol/S_ModularCurve_qExpFrobeniusInputsModL_and_finrankAlong_of_transcendental.lean",
    # --- WORKORDER-D1 (`topics/modularCurve/WORKORDER-D1-petersson.md`) phase 1: the pin's
    # four `Def_AutomorphicForm_*` modules ported whole. Appended last so no earlier
    # last-name match can flip.
    "Definitions/Def_AutomorphicForm_HyperbolicMeasure.lean",
    "Definitions/Def_AutomorphicForm_FundamentalDomainVolume.lean",
    "Definitions/Def_AutomorphicForm_SiegelSetCover.lean",
    "Definitions/Def_AutomorphicForm_Gamma0FundamentalSet.lean",
    # --- WORKORDER-D1 phase 2: the Petersson pairing pair, matched against their
    # `Theorems/` wrappers and their `S_` engines. Appended last so no earlier last-name
    # match can flip.
    "Theorems/Thm_ModularCurve_exists_cuspForm_petersson_eq_gammaH.lean",
    "P2M/Sol/S_ModularCurve_exists_cuspForm_petersson_eq_gammaH.lean",
    "Theorems/Thm_ModularCurve_exists_cuspForm_petersson_eq_of_finiteIndex.lean",
    "P2M/Sol/S_ModularCurve_exists_cuspForm_petersson_eq_of_finiteIndex.lean",
    # --- WORKORDER-D2 (`topics/modularCurve/WORKORDER-D2-period-map.md`): the period map of a
    # finite-index subgroup, four headlines matched against their `Theorems/` wrappers and
    # `S_` engines. `Def_ModularCurve_QExpansionDiff.lean` and `Thm_ModularCurve_theta_coeff.lean`
    # supply the theta definition layer the fourth needs. Appended last so no earlier last-name
    # match can flip.
    "Theorems/Thm_ModularCurve_addSubgroupClosure_range_periodAlongOf_eq_top.lean",
    "P2M/Sol/S_ModularCurve_addSubgroupClosure_range_periodAlongOf_eq_top.lean",
    "Theorems/Thm_ModularCurve_sum_periodAlongOf_mem_periodLatticeOf_of_boundary_eq_zero.lean",
    "P2M/Sol/S_ModularCurve_sum_periodAlongOf_mem_periodLatticeOf_of_boundary_eq_zero.lean",
    "Theorems/Thm_ModularCurve_coe_qExpansion_normalizedDerivOfComplex.lean",
    "P2M/Sol/S_ModularCurve_coe_qExpansion_normalizedDerivOfComplex.lean",
    "Definitions/Def_ModularCurve_QExpansionDiff.lean",
    "Theorems/Thm_ModularCurve_theta_coeff.lean",
    # --- WORKORDER-C2 (`topics/modularCurve/WORKORDER-C2-x1-function-field.md`) phase 1: the
    # pin definition layer of the `X₁`/`X_H` function-field rows. Three unported
    # `Definitions/Def_ModularCurve_*` modules are ported whole, plus — a §7 stop condition the
    # manager authorised — `Def_AlgebraicCurve_DifferentialPushPull.lean`, the
    # `Differential.pullbackAlong`/`traceAlong`/`correspondence` layer that
    # `Def_ModularCurve_HeckeDifferential.lean` itself imports. Appended last so no earlier
    # last-name match can flip (`Differential.pullbackAlong`/`correspondence` share their bare
    # last names with the ported `Divisor.*` ones and resolve through the dotted fallback).
    "Definitions/Def_ModularCurve_HeckeDifferential.lean",
    "Definitions/Def_ModularCurve_SL2Elementary.lean",
    "Definitions/Def_ModularCurve_X0ModL.lean",
    "Definitions/Def_AlgebraicCurve_DifferentialPushPull.lean",
    # --- WORKORDER-C2 phase 2: the ten landed leaf headlines, each matched against its
    # `Theorems/Thm_ModularCurve_<stem>.lean` wrapper and its `P2M/Sol/S_ModularCurve_<stem>.lean`
    # engine (the `S_` row is listed for the record and for the promoted-private fallback; the
    # `S_`-local helpers are transcribed `private` and so are skipped by the checker). The 11th
    # row, `exists_sum_smul_eq_of_isIntegralQExp_gamma1`, is DEFERRED: its one substantive proof
    # step is the unported pin node `ModularForm.exists_basis_gamma1_qCoeff_mem_range_ratCast`
    # (only the `CuspForm` twin is ported), so no port declaration and no source row exist for
    # it. Appended last so no earlier last-name match can flip.
    "Theorems/Thm_ModularCurve_qExpansion_div_mem_laurentBaseChange_xHFunctionField.lean",
    "P2M/Sol/S_ModularCurve_qExpansion_div_mem_laurentBaseChange_xHFunctionField.lean",
    "Theorems/Thm_ModularCurve_isIntegral_jqNModC_of_modularPolynomialData.lean",
    "P2M/Sol/S_ModularCurve_isIntegral_jqNModC_of_modularPolynomialData.lean",
    "Theorems/Thm_ModularCurve_exists_gamma0_qExpansion_div_eq_jqNModC.lean",
    "P2M/Sol/S_ModularCurve_exists_gamma0_qExpansion_div_eq_jqNModC.lean",
    "Theorems/Thm_ModularCurve_eisenstein4_cube_sub_mk_sq.lean",
    "P2M/Sol/S_ModularCurve_eisenstein4_cube_sub_mk_sq.lean",
    "Theorems/Thm_ModularCurve_diffQExp_x1FunctionFieldBar_injective.lean",
    "P2M/Sol/S_ModularCurve_diffQExp_x1FunctionFieldBar_injective.lean",
    "Theorems/Thm_ModularCurve_modularFunctionFieldC_eq_modularFunctionFieldFullC_of_charZero.lean",
    "P2M/Sol/S_ModularCurve_modularFunctionFieldC_eq_modularFunctionFieldFullC_of_charZero.lean",
    "Theorems/Thm_ModularCurve_modularFunctionFieldFullC_le_qExpFunctionFieldC_gamma0.lean",
    "P2M/Sol/S_ModularCurve_modularFunctionFieldFullC_le_qExpFunctionFieldC_gamma0.lean",
    "Theorems/Thm_ModularCurve_closure_elemSet_eq_top.lean",
    "P2M/Sol/S_ModularCurve_closure_elemSet_eq_top.lean",
    "Theorems/Thm_ModularCurve_isCurveOver_x1FunctionFieldBar.lean",
    "P2M/Sol/S_ModularCurve_isCurveOver_x1FunctionFieldBar.lean",
    "Theorems/Thm_ModularCurve_essFiniteType_x1FunctionFieldBar.lean",
    "P2M/Sol/S_ModularCurve_essFiniteType_x1FunctionFieldBar.lean",
    # --- WORKORDER-B1 (the modular polynomial `Φ_N`): the five subject-B rows. The wrapper is the
    # comparable statement; the `S_` file is listed so the pin-private helpers and the three
    # extra public rows of `S_..._eq_all`/`S_..._phiIrreducible_of_prime` (the
    # `evalAtJGen_injective`/`aeval_jqN_toAdjoin`/`natDegree_toAdjoin`/`toAdjoin_eq_minpoly*`
    # copies) resolve through the dotted/pin-private lookup instead of reporting missing. The
    # port writes every helper `private`, so only the five headlines are compared. Appended last
    # so no earlier last-name match can flip.
    "Theorems/Thm_ModularCurve_ModularPolynomialData_isUnit_leadingCoeff_diag_of_not_isSquare.lean",
    "P2M/Sol/S_ModularCurve_ModularPolynomialData_isUnit_leadingCoeff_diag_of_not_isSquare.lean",
    "Theorems/Thm_ModularCurve_ModularPolynomialData_eq_all.lean",
    "P2M/Sol/S_ModularCurve_ModularPolynomialData_eq_all.lean",
    "Theorems/Thm_ModularCurve_phiIrreducible_of_prime.lean",
    "P2M/Sol/S_ModularCurve_phiIrreducible_of_prime.lean",
    "Theorems/Thm_ModularCurve_ModularPolynomialData_evalSymm_of_prime.lean",
    "P2M/Sol/S_ModularCurve_ModularPolynomialData_evalSymm_of_prime.lean",
    "Theorems/Thm_ModularCurve_StarBank_press.lean",
    "P2M/Sol/S_ModularCurve_StarBank_press.lean",
    # --- Manager wave of 2026-10-09: the definition layer of subject A and of subject B2.
    # `Def_ModularCurve_LevelNFunctionField.lean` (53 lines, 11 declarations) is subject A's
    # whole new layer, homed at `ModularCurve/LevelN/FunctionField.lean`.
    # `Def_ModularCurve_ClassicalModularPolynomials.lean` (the `phiTwo`/`phiThree`/`intFibre`
    # constants) and `Def_ModularCurve_FibrePoly.lean` (`fibrePoly` and its three theorems)
    # are B2's, homed at `ModularCurve/Defs/{ClassicalModularPolynomials,FibrePoly}.lean`.
    # From `Def_ModularCurve_KroneckerTransport.lean` only the `ReduceModBivar` block
    # (`reduceModBivar`, `reduceModBivar_X`, `reduceModBivar_C_X`) has a consumer on this
    # cone and is homed in `Defs/FibrePoly.lean`; the module's other 35 declarations are
    # deliberately unported, and listing the file adds them only as unmatched candidates
    # (the checker iterates `PORT_FILES`, never `SOURCES`). Appended last so no earlier
    # last-name match can flip.
    "Definitions/Def_ModularCurve_LevelNFunctionField.lean",
    "Definitions/Def_ModularCurve_ClassicalModularPolynomials.lean",
    "Definitions/Def_ModularCurve_FibrePoly.lean",
    "Definitions/Def_ModularCurve_KroneckerTransport.lean",
    # --- WORKORDER-B2: the `N = 2` fibre row of subject B — `fibrePoly phiTwo W.j` as a product
    # over the three order-two Vélu quotients. The wrapper is the comparable statement; the `S_`
    # file is listed so its `S_`-local (`p2m_export`-suppressed) public rows (`fibrePoly_phiTwo_eq`,
    # `cubic_expand`, `coeff_{two,one,zero}_identity`, `main`) and the pin-private `sixteen_ne_zero`
    # resolve through the pin-private/dotted lookup instead of reporting missing. The port writes
    # every helper `private`, so only the headline is compared. Appended last so no earlier
    # last-name match can flip.
    "Theorems/Thm_ModularCurve_fibrePoly_phiTwo_j_eq_prod_veluQuotient2_j.lean",
    "P2M/Sol/S_ModularCurve_fibrePoly_phiTwo_j_eq_prod_veluQuotient2_j.lean",
    # --- WORKORDER-A (`topics/modularCurve/WORKORDER-A-levelN-field.md`): the
    # level-`N` function field of `X(N)`. Subject A's eight headlines and the `S_`
    # files that carry their shared prelude. `LevelN/Prelude.lean` writes the
    # duplicated blocks once, publicly, at the pin's own names; the `Theorems/`
    # wrappers are the interface copies for the eight headlines. Appended last so
    # no earlier last-name match can flip.
    "Theorems/Thm_ModularCurve_LevelN_isDomain_ring.lean",
    "Theorems/Thm_ModularCurve_LevelN_slash_eq_self_of_mem_Gamma_of_mul_eq.lean",
    "Theorems/Thm_ModularCurve_LevelN_exists_monoidHom_algEquiv_fixedField_eq_adjoin.lean",
    "Theorems/Thm_ModularCurve_LevelN_exists_algHom_laurentSeries_qExpansion.lean",
    "Theorems/Thm_ModularCurve_LevelN_exists_place_ord_neg_forall_smul_eq.lean",
    "Theorems/Thm_ModularCurve_LevelN_exists_place_ord_sub_pos_forall_smul_eq.lean",
    "Theorems/Thm_ModularCurve_LevelN_exists_place_analyticOrderAt_eq_mul_ord.lean",
    "Theorems/Thm_ModularCurve_LevelN_valuation_apply_smul_le_one_of_tendsto_div_smul.lean",
    "P2M/Sol/S_ModularCurve_LevelN_isDomain_ring.lean",
    "P2M/Sol/S_ModularCurve_LevelN_slash_eq_self_of_mem_Gamma_of_mul_eq.lean",
    "P2M/Sol/S_ModularCurve_LevelN_exists_monoidHom_algEquiv_fixedField_eq_adjoin.lean",
    "P2M/Sol/S_ModularCurve_LevelN_exists_algHom_laurentSeries_qExpansion.lean",
    "P2M/Sol/S_ModularCurve_LevelN_exists_place_ord_neg_forall_smul_eq.lean",
    "P2M/Sol/S_ModularCurve_LevelN_exists_place_ord_sub_pos_forall_smul_eq.lean",
    "P2M/Sol/S_ModularCurve_LevelN_exists_place_analyticOrderAt_eq_mul_ord.lean",
    "P2M/Sol/S_ModularCurve_LevelN_valuation_apply_smul_le_one_of_tendsto_div_smul.lean",
    # --- The Weil-pairing entry points. `Def_EllipticCurve_FunctionFieldPullback`
    # is the *partial* node boundary for `Place/PointPlace.lean`: only the pin's
    # `Point.xc`/`yc`, `placeOf` and `transEquiv` are carried there (the rest of
    # the 1,218-line node is deferred; see CARRY-FORWARD.md). Appended last so no
    # earlier last-name match can flip.
    "Definitions/Def_EllipticCurve_FunctionFieldPullback.lean",
    "Definitions/Def_EllipticCurve_WeilPairingFun.lean",
    "Definitions/Def_GaloisRep_WeilPairing.lean",
    # The `[n]`-fibre finiteness: the wrapper first (its `fibSet_finite` is the
    # interface), then the `S_` file for the promoted `torsion_finite` /
    # `card_torsion_toFinset` and the local `fibSet_finite'`.
    "Theorems/Thm_WeierstrassCurve_Affine_fibSet_finite.lean",
    "P2M/Sol/S_WeierstrassCurve_Affine_fibSet_finite.lean",
    # --- WORKORDER-E: the level-`N` `q`-expansion bridge. The two pin `S_` files are
    # twins (98 of their 101 declaration groups are statement-identical; only
    # `main2`/`solution` in the `_qExpansion` file and `solution` in the `_levelN`
    # file live alone). The port writes the stronger development once in
    # `ModularCurve/LevelN/QExpBridge.lean` and derives the `_levelN` headline as the
    # projection of `main2`. Both wrappers and both `S_` files are listed so the pin's
    # public prelude rows can resolve; every port helper is `private`, so only the two
    # public headlines are diffed. Appended last so no earlier last-name match can flip.
    "Theorems/Thm_ModularCurve_exists_ringHom_laurentBaseChange_qExpFunctionFieldC_levelN.lean",
    "P2M/Sol/S_ModularCurve_exists_ringHom_laurentBaseChange_qExpFunctionFieldC_levelN.lean",
    "Theorems/Thm_ModularCurve_exists_ringHom_laurentBaseChange_qExpFunctionFieldC_levelN_qExpansion.lean",
    "P2M/Sol/S_ModularCurve_exists_ringHom_laurentBaseChange_qExpFunctionFieldC_levelN_qExpansion.lean",
    # --- WORKORDER-S8: the Γ₁/Nebentypus pair. Both wrappers and both `S_` files are
    # listed; the `S_` files also carry the public `dd`/Γ₁ prelude that
    # `ModularForms/HeckeEigenNebentypus.lean` now promotes, so the promoted
    # declarations verify against the pin's public copies. Appended last so no earlier
    # last-name match can flip.
    "Theorems/Thm_CuspForm_exists_hasNebentypus_of_qCoeff_hecke_eigen.lean",
    "P2M/Sol/S_CuspForm_exists_hasNebentypus_of_qCoeff_hecke_eigen.lean",
    "Theorems/Thm_CuspForm_hasNebentypus_inv_and_qCoeff_hecke_eigen_of_fricke.lean",
    "P2M/Sol/S_CuspForm_hasNebentypus_inv_and_qCoeff_hecke_eigen_of_fricke.lean",
    # --- PORTING-AutomorphicForm D0 (`topics/PORTING-AutomorphicForm.md`): the
    # mathlib-only leaves. The pin `Def_AutomorphicForm_AdelicLsXi` is split into
    # `Adelic/Basic` + `Adelic/LsXi`, so both port modules look it up. Appended last.
    "Definitions/Def_Deformations_ContinuousSMulDiscrete.lean",
    "Definitions/Def_AutomorphicForm_AdelicLsXi.lean",
    "Definitions/Def_AutomorphicForm_ConstantTerm.lean",
    # --- PORTING-AutomorphicForm D2: smooth vectors (generic representation theory).
    # Appended last.
    "Definitions/Def_RepTheory_SmoothVectors.lean",
    # --- PORTING-AutomorphicForm D4: the automorphic carrier pins and right convolution.
    # `Def_AutomorphicForm_FactorizableTestFn` is already listed above. Appended last.
    "Definitions/Def_AutomorphicForm_CarrierPins.lean",
    "Definitions/Def_AutomorphicForm_RightConvolution.lean",
    # --- PORTING-AutomorphicForm D5: automorphic and smooth automorphic functions.
    # Appended last.
    "Definitions/Def_AutomorphicForm_AutomorphicFnAt.lean",
    "Definitions/Def_AutomorphicForm_SmoothAutomorphicFnAt.lean",
    # --- PORTING-AutomorphicForm D6: the windowed Siegel norms and row isometries.
    # Appended last.
    "Definitions/Def_AutomorphicForm_WindowedSiegelSet.lean",
    "Definitions/Def_AutomorphicForm_RowIsometryInvariance.lean",
    # --- PORTING-AutomorphicForm D7: the archimedean inclusion and archimedean types.
    # Appended last.
    "Definitions/Def_AutomorphicForm_ArchType.lean",
    # --- PORTING-AutomorphicForm H1: the shared `isFactorizableTestFn` prelude.
    # The public `Ws1.H2K.Scaffold` block of the `hasArchCharacterAt` file is listed
    # first so the bare last-name lookup finds the public copy; the two private siblings
    # follow as fallbacks. Appended last.
    "P2M/Sol/S_AutomorphicForm_exists_isFactorizableTestFn_hasArchCharacterAt_rightConv_ne_zero_of_hasArchCharacterAt.lean",
    "P2M/Sol/S_AutomorphicForm_exists_isFactorizableTestFn_rightConv_ne_zero_of_levelOne_invariant.lean",
    "P2M/Sol/S_AutomorphicForm_exists_isFactorizableTestFn_rightConv_ne_zero_of_principalLevel_invariant.lean",
    # --- PORTING-AutomorphicForm T1: the `rightConv_ne_zero_of_*` headlines and the
    # principal-level def module. The wrappers carry the public headline statements; the
    # `S_` files' `solution` theorems are the proofs. Appended last.
    "Theorems/Thm_AutomorphicForm_exists_isFactorizableTestFn_rightConv_ne_zero_of_levelOne_invariant.lean",
    "Theorems/Thm_AutomorphicForm_exists_isFactorizableTestFn_rightConv_ne_zero_of_principalLevel_invariant.lean",
    "Definitions/Def_NumberField_PrincipalLevel.lean",
    # --- PORTING-AutomorphicForm: the arch-weight-character def layer. Appended last.
    "Definitions/Def_AutomorphicForm_ArchWeightChar.lean",
    "Definitions/Def_AutomorphicForm_ArchWeightCharTransport.lean",
    # --- PORTING-AutomorphicForm T1: the arch-character headline and the measure development
    # it uses. The hasArchCharacterAt `S_` file is already listed above (as H1's public copy);
    # the wrappers carry the public headline statements. Appended last.
    "Theorems/Thm_AutomorphicForm_exists_isFactorizableTestFn_hasArchCharacterAt_rightConv_ne_zero_of_hasArchCharacterAt.lean",
    "Theorems/Thm_NumberField_AdelicHaar_isMulRightInvariant_adelicGLHaar.lean",
    # --- TOPIC-rightConv-comm W1: the adèlic box. The pin node is a definition layer
    # with no `Theorems/` wrapper; the port's finite-half declarations
    # (`integralFiniteAdeles` and its openness/closedness/compactness) live in
    # `AdelicLevel/IdealBall.lean` above, and this source supplies the remaining 29.
    # Appended last.
    "Definitions/Def_NumberField_AdelicBox.lean",
    # --- TOPIC-rightConv-comm W2: the adèlic centre and the projective quotient. The pin
    # node is a definition layer with no `Theorems/` wrapper; `Matrix.GeneralLinearGroup.scalar`
    # and `center_eq_range_scalar` are mathlib `v4.34.0`. Appended last.
    "Definitions/Def_NumberField_AdelicCentre.lean",
    # --- TOPIC-rightConv-comm W3: the generic measure-theoretic decay engines. Both pin
    # nodes are mathlib-only definitions with no `Theorems/` wrapper; their home is
    # `MeasureTheory/` (playbook §3.1). Appended last.
    "Definitions/Def_MeasureTheory_ContractionDecay.lean",
    "Definitions/Def_MeasureTheory_ScalingDichotomy.lean",
    # --- TOPIC-rightConv-comm W4: the windowed-Siegel topology and coordinates. Both pin
    # nodes are definition layers with no `Theorems/` wrapper; they import the landed
    # `Def_AutomorphicForm_WindowedSiegelSet`. Appended last.
    "Definitions/Def_AutomorphicForm_WindowedSiegelTopology.lean",
    "Definitions/Def_AutomorphicForm_SiegelCoordinates.lean",
    # --- TOPIC-rightConv-comm W5: the Hecke/local vocabulary. Four definition nodes with no
    # `Theorems/` wrapper: the generic abstract Hecke operator, the automorphic Hecke
    # eigensystem, the local-newvector congruence subgroups, and the idèle-class/Galois-descent
    # vocabulary. Appended last.
    "Definitions/Def_AbstractHeckeOperator.lean",
    "Definitions/Def_AutomorphicForm_HeckeEigensystem.lean",
    "Definitions/Def_LocalNewvector_CongruenceSubgroupK1.lean",
    "Definitions/Def_M4aHerbrand_IdeleClassVocab.lean",
    # --- TOPIC-rightConv-comm W6: the mathlib-gap stubs in the twin's definition closure.
    # Two substitutions: `Submonoid.units_isOpen` is mathlib's renamed `Submonoid.isOpen_units`
    # (whole `Def_Mathlib_Topology_Algebra_Group_Units` node, no port module), and
    # `RestrictedProduct.singleAddMonoidHom` is mathlib's `@[to_additive]`-generated constant
    # (so `RestrictedProduct_Basic` lands 22 of its 23 declarations). The other seven nodes are
    # residue, ported to a mathlib-mirroring tree under `FLTForHuman/{Order,Topology}/`.
    # Appended last.
    "Definitions/Def_Mathlib_Order_Filter_Cofinite.lean",
    "Definitions/Def_Mathlib_Topology_Bases.lean",
    "Definitions/Def_Mathlib_Topology_Algebra_Module_Quotient.lean",
    "Definitions/Def_Mathlib_Topology_Algebra_ContinuousMonoidHom.lean",
    "Definitions/Def_Mathlib_Topology_Algebra_RestrictedProduct_Basic.lean",
    "Definitions/Def_Mathlib_Topology_Algebra_RestrictedProduct_Equiv.lean",
    "Definitions/Def_Mathlib_Topology_Algebra_RestrictedProduct_TopologicalSpace.lean",
    # --- TOPIC-rightConv-comm W7+ (the definition gate proper), ready set. Appended last.
    "Definitions/Def_LocalLanglands_HeckePair.lean",
    "Definitions/Def_AdelicDock_LocalEmbedding.lean",
    "Definitions/Def_NumberField_AdelicVolume.lean",
    "Definitions/Def_AutomorphicForm_SiegelReduction.lean",
    "Definitions/Def_AutomorphicForm_SigmaAdelicAction.lean",
    "Definitions/Def_AutomorphicForm_HeckeEigensystemMap.lean",
    "Definitions/Def_LocalLanglands_HeckeCosetSystem.lean",
    "Definitions/Def_AutomorphicForm_CentreCutSiegelSet.lean",
    "Definitions/Def_AutomorphicForm_SmoothCuspRealization.lean",
    "Definitions/Def_AutomorphicForm_SiegelCovering.lean",
    "Definitions/Def_NumberField_SiegelVolume.lean",
    "Definitions/Def_AutomorphicForm_ProductionPins.lean",
    "Definitions/Def_AutomorphicForm_ArithCuspRealization.lean",
    "Definitions/Def_AutomorphicForm_ProductionPinsCompact.lean",
    "Definitions/Def_AutomorphicForm_ProductionPinsGeneral.lean",
    # --- TOPIC-rightConv-comm W11: the isotypic cusp space. Appended last.
    "Definitions/Def_AutomorphicForm_IsotypicCuspSpace.lean",
    # --- TOPIC-rightConv-comm W12: the cuspidal constituent and the archimedean
    # spherical predicate. Appended last.
    "Definitions/Def_AutomorphicForm_CuspidalConstituent.lean",
    "Definitions/Def_AutomorphicForm_ArchSpherical.lean",
    # --- WORKORDER-P-rightConv-comm P1
    # (`topics/automorphicForm/WORKORDER-P-rightConv-comm.md`): the three proof silos whose
    # shared engine the four `RepTheory/` modules transcribe, and their `Theorems/` wrappers
    # (the statement authority; P3). The engine is `private` at the pin, so it is registered
    # through the checker's promoted-from-pin-private lookup. Appended last so no earlier
    # last-name match can flip.
    "P2M/Sol/S_AutomorphicForm_rightConv_rightConv_comm_of_isLevelSphericalOfType.lean",
    "P2M/Sol/S_AutomorphicForm_rightConv_rightConv_comm_of_isLevelSphericalOfType_of_isCompact.lean",
    "P2M/Sol/S_AutomorphicForm_rightConv_rightConv_comm_of_isLevelSphericalOfType_principal.lean",
    "Theorems/Thm_AutomorphicForm_rightConv_rightConv_comm_of_isLevelSphericalOfType.lean",
    "Theorems/Thm_AutomorphicForm_rightConv_rightConv_comm_of_isLevelSphericalOfType_of_isCompact.lean",
    "Theorems/Thm_AutomorphicForm_rightConv_rightConv_comm_of_isLevelSphericalOfType_principal.lean",
    # The constant-field-extension linear-independence pair: the `of_isAlgClosed`
    # node and its characteristic-zero twin. The twin is listed for its three
    # `[CharZero K]` spellings, which are not the general `[IsSeparable]` ones;
    # the two wrappers carry the headlines. The port transcribes both once, in
    # `AlgebraicCurve/IsCurveOver/ConstantFieldExtension.lean`; see
    # `topics/algebraicCurve/TOPIC-constant-field-extension.md`.
    "Theorems/Thm_AlgebraicCurve_linearIndependent_of_constantFieldExtension_of_isAlgClosed.lean",
    "Theorems/Thm_AlgebraicCurve_linearIndependent_of_constantFieldExtension.lean",
    "P2M/Sol/S_AlgebraicCurve_linearIndependent_of_constantFieldExtension_of_isAlgClosed.lean",
    "P2M/Sol/S_AlgebraicCurve_linearIndependent_of_constantFieldExtension.lean",
    # --- WORKORDER Z1 (`topics/numberTheory/WORKORDER-Z1-completed-dedekind-zeta.md`):
    # the completed Dedekind zeta façade. The `Theorems/` wrapper carries the headline
    # the façade spells, so it is that declaration's statement authority.
    "Theorems/Thm_NumberField_exists_completedDedekindZeta_package.lean",
    # The silo is listed so that later wiring of the development's other declarations
    # needs no new source; today only the headline in the façade is checked.
    "P2M/Sol/S_NumberField_exists_completedDedekindZeta_package.lean",
    # --- WORKORDER T1 (`topics/numberTheory/tateGlobal/WORKORDER-T1-tateglobal-core.md`):
    # the TateGlobal analytic core. The three `Theorems/` wrappers carry the headlines
    # the façade spells, so they are those declarations' statement authorities; the
    # three `S_` silos are listed so that later wiring of the development's other
    # declarations needs no new source (the port transcribes the caps once, in
    # `TateGlobal/EulerFactors.lean`, `…/IntegrableZetaIntegrand.lean` and
    # `…/IndicatorEulerFactors.lean`). Appended last so no earlier last-name match
    # can flip.
    "Theorems/Thm_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean",
    "Theorems/Thm_NumberField_TateGlobal_integrable_zetaIntegrand.lean",
    "Theorems/Thm_NumberField_TateGlobal_exists_forall_zetaIntegral_mul_eulerFactors_eq_of_eq_indicator.lean",
    "P2M/Sol/S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean",
    "P2M/Sol/S_NumberField_TateGlobal_integrable_zetaIntegrand.lean",
    "P2M/Sol/S_NumberField_TateGlobal_exists_forall_zetaIntegral_mul_eulerFactors_eq_of_eq_indicator.lean",
    # --- WORKORDER-Q turn 2: the archimedean approximate-identity façade. The wrapper
    # carries the headline the façade spells, so it is that declaration's statement
    # authority; the `S_` silo is listed because the wrapper alone does not carry the
    # proof, and so that later wiring of the development's other declarations needs no
    # new source. Appended last so no earlier last-name match can flip.
    "Theorems/Thm_AutomorphicForm_exists_isArchTestFactor_isArchFactorBiFinite_tendsto_integral_of_mem_archCutSubmodule.lean",
    "P2M/Sol/S_AutomorphicForm_exists_isArchTestFactor_isArchFactorBiFinite_tendsto_integral_of_mem_archCutSubmodule.lean",
    # --- WORKORDER-R turn 2 (`topics/automorphicForm/WORKORDER-R-bruhat-transversal.md`):
    # the Bruhat-transversal / Weyl-integrand trio. The three `Theorems/` wrappers carry
    # the headlines the façade `AutomorphicForm/Adelic/WeylIntegrable.lean` spells, so they
    # are those declarations' statement authority; the three `S_` silos are listed so that
    # later wiring of the development's other declarations needs no new source (the port
    # transcribes the shared block once, in
    # `AutomorphicForm/Adelic/WeylIntegrable/{LatticeEstimates,Assembly,UniformBound,Caps}.lean`).
    # Appended last so no earlier last-name match can flip.
    "Theorems/Thm_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean",
    "Theorems/Thm_AutomorphicForm_continuous_bruhatTransversal_tsum_of_re_gt_half.lean",
    "Theorems/Thm_AutomorphicForm_weylIntertwiningIntegrand_integrable_of_re_gt_half.lean",
    "P2M/Sol/S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean",
    "P2M/Sol/S_AutomorphicForm_continuous_bruhatTransversal_tsum_of_re_gt_half.lean",
    "P2M/Sol/S_AutomorphicForm_weylIntertwiningIntegrand_integrable_of_re_gt_half.lean",
    # --- The ModularCurve weight-4 Tate-slot cluster, definition layer. `frontier.py
    # --include-leaves` shows 14 `S_ModularCurve_*` leaves at ~1650 lines; all 14 import
    # `Def_ModularCurve_TateSlots`, which imports `Def_ModularCurve_TateFormal`, which
    # imports the already-listed `Def_ModularCurve_JqCoeff`. Both new modules are homed
    # whole (playbook §2.3) at `Defs/TateFormal.lean` / `Defs/TateSlots.lean`; the pin's
    # downstream consumers (`TatePoint`, `TateVeluRing`, `TateOrigin`, `ShimuraGenerator`,
    # `Thm_ModularCurve_Delta_tatePowerSeries`) name the same declarations, so the whole
    # node and not only the `S_`-visible block. Neither has a `Theorems/` wrapper, so they
    # verify by name against their `Definitions/` files. Appended last so no earlier
    # last-name match can flip.
    "Definitions/Def_ModularCurve_TateFormal.lean",
    "Definitions/Def_ModularCurve_TateSlots.lean",
    # --- WORKORDER-F1: the weight-4 Tate-slot headline façade. The fourteen pin
    # `S_ModularCurve_*` files are near-identical copies of one shared development
    # (see topics/modularCurve/TOPIC-tate-slots-weight-four.md); the engine is
    # tier 3 (`TateSlots/Convergence.lean`, `TateSlots/SlotCoeff.lean`) and only
    # the façade module is listed. Each `Theorems/Thm_ModularCurve_<name>.lean`
    # wrapper is the statement authority (listed first); its `S_` file follows so
    # the engine's promoted `ModularCurve.TateSlots.<name>` kernels resolve through
    # the pin-private dotted fallback. Appended last so no earlier last-name match
    # can flip.
    "Theorems/Thm_ModularCurve_tsum_lambertTerm_eq.lean",
    "Theorems/Thm_ModularCurve_single_div_one_sub_sq.lean",
    "Theorems/Thm_ModularCurve_single_sq_div_one_sub_cube.lean",
    "Theorems/Thm_ModularCurve_slotSubst_gen_injective.lean",
    "Theorems/Thm_ModularCurve_coeff_slotSubst_tateUnivX.lean",
    "Theorems/Thm_ModularCurve_coeff_slotSubst_tateUnivY.lean",
    "Theorems/Thm_ModularCurve_equation_tateBase_iff.lean",
    "Theorems/Thm_ModularCurve_toricPoint_fst_coeff_mul.lean",
    "Theorems/Thm_ModularCurve_toricPoint_fst_coeff_of_not_dvd.lean",
    "Theorems/Thm_ModularCurve_toricPoint_fst_coeff_zero.lean",
    "Theorems/Thm_ModularCurve_toricPoint_snd_coeff_mul_eq_sum_divisors.lean",
    "Theorems/Thm_ModularCurve_toricPoint_snd_coeff_of_not_dvd.lean",
    "Theorems/Thm_ModularCurve_toricPoint_snd_coeff_zero.lean",
    "Theorems/Thm_ModularCurve_tsum_of_coeff_lt_eq_zero.lean",
    "P2M/Sol/S_ModularCurve_tsum_lambertTerm_eq.lean",
    "P2M/Sol/S_ModularCurve_single_div_one_sub_sq.lean",
    "P2M/Sol/S_ModularCurve_single_sq_div_one_sub_cube.lean",
    "P2M/Sol/S_ModularCurve_slotSubst_gen_injective.lean",
    "P2M/Sol/S_ModularCurve_coeff_slotSubst_tateUnivX.lean",
    "P2M/Sol/S_ModularCurve_coeff_slotSubst_tateUnivY.lean",
    "P2M/Sol/S_ModularCurve_equation_tateBase_iff.lean",
    "P2M/Sol/S_ModularCurve_toricPoint_fst_coeff_mul.lean",
    "P2M/Sol/S_ModularCurve_toricPoint_fst_coeff_of_not_dvd.lean",
    "P2M/Sol/S_ModularCurve_toricPoint_fst_coeff_zero.lean",
    "P2M/Sol/S_ModularCurve_toricPoint_snd_coeff_mul_eq_sum_divisors.lean",
    "P2M/Sol/S_ModularCurve_toricPoint_snd_coeff_of_not_dvd.lean",
    "P2M/Sol/S_ModularCurve_toricPoint_snd_coeff_zero.lean",
    "P2M/Sol/S_ModularCurve_tsum_of_coeff_lt_eq_zero.lean",
    # --- WORKORDER-F2: the `tateCurve` twins and triplet, definition layer. Two
    # clusters of near-identical pin `S_` files (see
    # topics/modularCurve/TOPIC-tate-curve-twins.md) import six unported
    # `Definitions/` modules, homed whole (playbook §2.3) at
    # `Algebra/LaurentSeriesXAdic.lean`, `TateCurve/{QSeries,PointSeries}.lean`,
    # `ModularForms/KatzLevelOne.lean` and `ModularCurve/Defs/{KatzLevelP,KatzLevelPCusps}.lean`.
    # None has a `Theorems/` wrapper, so all verify by name against their
    # `Definitions/` files. Appended last so no earlier last-name match can flip.
    "Definitions/Def_LaurentSeries_XAdic.lean",
    "Definitions/Def_TateCurve_QSeries.lean",
    "Definitions/Def_TateCurve_PointSeries.lean",
    "Definitions/Def_ModularForm_KatzLevelOne.lean",
    "Definitions/Def_ModularCurve_KatzLevelP.lean",
    "Definitions/Def_ModularCurve_KatzLevelPCusps.lean",
    # --- WORKORDER-F2: the `tateCurve` twin/triplet public headline module. Five
    # near-identical pin `S_` files carry one `BridgeX` development; the engine is
    # tier 3 (`TateCurve/Bridge.lean`, `TateCurve/NonToricSlot.lean`) and only the
    # façade (`TateCurve/QPow.lean`) is listed. Each
    # `Theorems/Thm_ModularCurve_<name>.lean` wrapper is the
    # statement authority (listed first); its `S_` file follows so the engine's
    # promoted `ModularCurve.TateCurve.<kernel>` aliases resolve through the
    # pin-private dotted fallback. Appended last so no earlier last-name match can
    # flip.
    "Theorems/Thm_ModularCurve_tateCurve_curve_X_pow_eq_tateBase.lean",
    "Theorems/Thm_ModularCurve_tateCurve_pointX_C_eq_tateToricPoint_fst.lean",
    "Theorems/Thm_ModularCurve_tateCurve_pointY_C_eq_tateToricPoint_snd.lean",
    "Theorems/Thm_ModularCurve_tateCurve_pointX_C_mul_X_pow_eq_nonToricPoint_fst.lean",
    "Theorems/Thm_ModularCurve_tateCurve_pointY_C_mul_X_pow_eq_nonToricPoint_snd.lean",
    "P2M/Sol/S_ModularCurve_tateCurve_curve_X_pow_eq_tateBase.lean",
    "P2M/Sol/S_ModularCurve_tateCurve_pointX_C_eq_tateToricPoint_fst.lean",
    "P2M/Sol/S_ModularCurve_tateCurve_pointY_C_eq_tateToricPoint_snd.lean",
    "P2M/Sol/S_ModularCurve_tateCurve_pointX_C_mul_X_pow_eq_nonToricPoint_fst.lean",
    "P2M/Sol/S_ModularCurve_tateCurve_pointY_C_mul_X_pow_eq_nonToricPoint_snd.lean",
    # --- the `continuous_ideleNorm` façade
    # (`topics/numberTheory/tateGlobal/TOPIC-continuous-ideleNorm.md`): the shared
    # `FujisakiC3` block is tier 3 (`…/TateGlobal/FujisakiC3.lean`) and only the thin
    # façade (`…/NumberField/TateGlobalContinuousIdeleNorm.lean`) is listed. Each
    # `Theorems/Thm_NumberField_TateGlobal_continuous_ideleNorm*.lean` wrapper is the
    # statement authority (listed first); its `S_` file follows so the engine's public
    # block resolves through the pin-private dotted fallback. Appended last so no
    # earlier last-name match can flip.
    "Theorems/Thm_NumberField_TateGlobal_continuous_ideleNorm.lean",
    "Theorems/Thm_NumberField_TateGlobal_continuous_ideleNorm_det.lean",
    "P2M/Sol/S_NumberField_TateGlobal_continuous_ideleNorm.lean",
    "P2M/Sol/S_NumberField_TateGlobal_continuous_ideleNorm_det.lean",
    # --- TOPIC-adelic-modulus definition gate
    # (`topics/numberTheory/adelicModulus/TOPIC-adelic-modulus.md`): the pin node
    # `Def_NumberField_AdelicHeight` is a definition layer with no `Theorems/` wrapper,
    # imported (and left unused in the proof) by the headline's `S_` silo and named by
    # 525 pin theorems elsewhere, so it is homed whole (playbook §2.3). Its prerequisite
    # `Definitions/Def_AutomorphicForm_SiegelReduction.lean` is listed above, and
    # `NumberField.FinitePlace.*`, `NumberField.prod_abs_eq_one` and
    # `NumberField.InfinitePlace.prod_eq_abs_norm` are mathlib `v4.34.0`. Appended last so
    # no earlier last-name match can flip.
    "Definitions/Def_NumberField_AdelicHeight.lean",
    # --- WORKORDER-T2 (`topics/numberTheory/tateGlobal/WORKORDER-T2-ideleNorm-det-slab.md`):
    # the two `GL₂` idele-norm headlines that read the landed `continuous_ideleNorm_det`
    # wire. Each `Theorems/` wrapper is the statement authority (listed first); its `S_`
    # file follows. The module
    # (`FLTForHuman/NumberTheory/NumberField/TateGlobalIdeleNormDet.lean`) is tier 1.
    # Appended last so no earlier last-name match can flip.
    "Theorems/Thm_NumberField_TateGlobal_measurableSet_setOf_ideleNorm_det_mem_Icc.lean",
    "Theorems/Thm_NumberField_TateGlobal_ideleNorm_det_eq_one_of_isCompact_of_mem.lean",
    "P2M/Sol/S_NumberField_TateGlobal_measurableSet_setOf_ideleNorm_det_mem_Icc.lean",
    "P2M/Sol/S_NumberField_TateGlobal_ideleNorm_det_eq_one_of_isCompact_of_mem.lean",
    # --- TOPIC-adelic-modulus, WORKORDER-A2: the four-node principal-idele product
    # formula. Each `Theorems/` wrapper is the statement authority (listed first); its
    # `S_` file follows. The engine
    # (`FLTForHuman/NumberTheory/AdelicHaar/ProductFormula.lean`) stays tier 3 and is
    # recorded in spec/UNWIRED-PUBLIC.md. Appended last so no earlier last-name match can
    # flip.
    "Theorems/Thm_NumberField_AdelicBox_isAddFundamentalDomain_preimage_mul_algebraMap_adelicBox.lean",
    "Theorems/Thm_NumberField_AdeleRing_measurePreserving_mul_algebraMap.lean",
    "Theorems/Thm_NumberField_AdelicHaar_measurePreserving_mul_algebraMap_adelicAddHaar.lean",
    "Theorems/Thm_NumberField_AdeleRing_distribHaarChar_algebraMap.lean",
    "P2M/Sol/S_NumberField_AdelicBox_isAddFundamentalDomain_preimage_mul_algebraMap_adelicBox.lean",
    "P2M/Sol/S_NumberField_AdeleRing_measurePreserving_mul_algebraMap.lean",
    "P2M/Sol/S_NumberField_AdelicHaar_measurePreserving_mul_algebraMap_adelicAddHaar.lean",
    "P2M/Sol/S_NumberField_AdeleRing_distribHaarChar_algebraMap.lean",
    # --- TOPIC-adelic-modulus, WORKORDER-A1: the two modulus headlines. Each
    # `Theorems/` wrapper is the statement authority (listed first); its `S_` file follows.
    # The two engines (`FLTForHuman/NumberTheory/AdelicHaar/AdelicModulus.lean`,
    # `…/ArchModulus.lean`) stay tier 3 and are recorded in spec/UNWIRED-PUBLIC.md.
    # Appended last so no earlier last-name match can flip.
    "Theorems/Thm_NumberField_AdeleRing_distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm.lean",
    "Theorems/Thm_NumberField_InfiniteAdeleRing_distribHaarChar_eq_prod_norm_pow_mult.lean",
    "P2M/Sol/S_NumberField_AdeleRing_distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm.lean",
    "P2M/Sol/S_NumberField_InfiniteAdeleRing_distribHaarChar_eq_prod_norm_pow_mult.lean",
    # --- TOPIC-compactness-twins definition gate: `Def_NumberField_Completion_Finite`
    # (the adic-completion integrality instances) is a definition layer with no
    # `Theorems/` wrapper, homed whole at
    # `FLTForHuman/NumberTheory/NumberField/Completion/Finite.lean`. It was tier 3 until
    # the Fujisaki compactness pair gave it a consumer
    # (`NumberField.isCompactAdicCompletionIntegers` at the pin's lines 595 and 638).
    # Appended last so no earlier last-name match can flip.
    "Definitions/Def_NumberField_Completion_Finite.lean",
    # --- TOPIC-compactness-twins, WORKORDER-T3: the Fujisaki compactness pair. Each
    # `Theorems/` wrapper is the statement authority (listed first); its `S_` file follows.
    # The engine (`FLTForHuman/NumberTheory/NumberField/TateGlobal/FujisakiCompact.lean`)
    # stays tier 3 and is recorded in spec/UNWIRED-PUBLIC.md. Appended last so no earlier
    # last-name match can flip.
    "Theorems/Thm_NumberField_TateGlobal_exists_isCompact_subset_normOneIdeles_forall_mem_exists_eq_map_algebraMap_mul.lean",
    "Theorems/Thm_NumberField_TateGlobal_compactSpace_normOneIdeleClass.lean",
    "P2M/Sol/S_NumberField_TateGlobal_exists_isCompact_subset_normOneIdeles_forall_mem_exists_eq_map_algebraMap_mul.lean",
    "P2M/Sol/S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.lean",
    # --- The `AutomorphicForm.LocalIntertwining` cluster, set LI-1
    # (topics/automorphicForm/WORKORDER-LI1-weyl-unramified.md). The `Theorems/` wrapper is the
    # statement authority (listed first); the `S_` file is the proof source and re-carries the
    # whole T1 prelude the port already has. The rest of the cluster is not yet listed.
    "Theorems/Thm_AutomorphicForm_LocalIntertwining_integral_unramifiedWeylIntegrand_adicCompletion.lean",
    "P2M/Sol/S_AutomorphicForm_LocalIntertwining_integral_unramifiedWeylIntegrand_adicCompletion.lean",
    # --- The other half of the pair, set LI-2 (topics/automorphicForm/WORKORDER-LI2-weyl-smooth.md).
    # Same shape as LI-1: the `Theorems/` wrapper first, the `S_` file second.
    # `Definitions/Def_LanglandsTunnell_TateLocalConstantsAt.lean` carries `higherUnitsAt`, which
    # the smooth headline's hypothesis names and which has no other port home; the rest of that
    # Definitions file stays unported (CARRY-FORWARD).
    "Theorems/Thm_AutomorphicForm_LocalIntertwining_integral_smoothWeylIntegrand_adicCompletion.lean",
    "P2M/Sol/S_AutomorphicForm_LocalIntertwining_integral_smoothWeylIntegrand_adicCompletion.lean",
    "Definitions/Def_LanglandsTunnell_TateLocalConstantsAt.lean",
    # --- TOPIC-iwasawa-analytic-core definition gate
    # (topics/automorphicForm/TOPIC-iwasawa-analytic-core.md): `Def_AutomorphicForm_ComplexIwasawa`
    # homed whole at `FLTForHuman/AutomorphicForm/Iwasawa/Complex/Basic.lean` (see PORT_FILES). Its
    # `botP`/`botQ`/`radC`/`kC` are the statement vocabulary of the complex-place headlines. The
    # topic's shared generic `M4aP3B.FourierDecay` block is homed at
    # `FLTForHuman/MeasureTheory/FourierDecay.lean`; the pin's complex `norm` `S_` file carries its
    # two statements, so it is listed here too, and it is also the complex wave's kernel source.
    # Appended last so no earlier last-name match can flip.
    "Definitions/Def_AutomorphicForm_ComplexIwasawa.lean",
    "P2M/Sol/S_AutomorphicForm_ComplexIwasawa_norm_fourierIntegral_cpow_radC_mul_le_polyDecay.lean",
    # --- WORKORDER-I3 (the real Iwasawa engine; see PORT_FILES): each `Theorems/` wrapper is the
    # statement authority (listed first), its `S_` file follows and supplies the engine's prelude
    # statements. The three engine modules stay tier 3 and are recorded in spec/UNWIRED-PUBLIC.md.
    # Appended last so no earlier last-name match can flip.
    "Theorems/Thm_AutomorphicForm_RealIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kR_apply.lean",
    "Theorems/Thm_AutomorphicForm_RealIwasawa_norm_fourierIntegral_cpow_rad_mul_le_polyDecay.lean",
    "Theorems/Thm_AutomorphicForm_RealIwasawa_exists_forall_norm_fourierIntegral_cpow_rad_mul_le_polyDecay_of_isCompact.lean",
    "Theorems/Thm_AutomorphicForm_RealIwasawa_continuousOn_differentiableOn_norm_le_polyDecay_weightFourierIntegral.lean",
    "P2M/Sol/S_AutomorphicForm_RealIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kR_apply.lean",
    "P2M/Sol/S_AutomorphicForm_RealIwasawa_norm_fourierIntegral_cpow_rad_mul_le_polyDecay.lean",
    "P2M/Sol/S_AutomorphicForm_RealIwasawa_exists_forall_norm_fourierIntegral_cpow_rad_mul_le_polyDecay_of_isCompact.lean",
    "P2M/Sol/S_AutomorphicForm_RealIwasawa_continuousOn_differentiableOn_norm_le_polyDecay_weightFourierIntegral.lean",
    # --- WORKORDER-I1 (the complex Iwasawa engine, base layer; see PORT_FILES): each `Theorems/`
    # wrapper is the statement authority (listed first), its `S_` file follows and supplies the
    # engine's prelude statements. The complex `norm` `S_` file is already listed above (it carries
    # the shared FourierDecay statements). The two engine modules stay tier 3 and are recorded in
    # spec/UNWIRED-PUBLIC.md. Appended last so no earlier last-name match can flip.
    "Theorems/Thm_AutomorphicForm_ComplexIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kC_apply.lean",
    "Theorems/Thm_AutomorphicForm_ComplexIwasawa_exists_forall_bound_iteratedFDeriv_kC_apply_of_isCompact.lean",
    "Theorems/Thm_AutomorphicForm_ComplexIwasawa_kC_mem_specialUnitaryGroup.lean",
    "Theorems/Thm_AutomorphicForm_ComplexIwasawa_weyl_mul_unipotent_mul_eq_borel_mul_kC.lean",
    "Theorems/Thm_AutomorphicForm_ComplexIwasawa_exists_forall_integrable_integral_rpow_neg_radC_le_of_isCompact.lean",
    "Theorems/Thm_AutomorphicForm_ComplexIwasawa_norm_fourierIntegral_cpow_radC_mul_le_polyDecay.lean",
    "P2M/Sol/S_AutomorphicForm_ComplexIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kC_apply.lean",
    "P2M/Sol/S_AutomorphicForm_ComplexIwasawa_exists_forall_bound_iteratedFDeriv_kC_apply_of_isCompact.lean",
    "P2M/Sol/S_AutomorphicForm_ComplexIwasawa_kC_mem_specialUnitaryGroup.lean",
    "P2M/Sol/S_AutomorphicForm_ComplexIwasawa_weyl_mul_unipotent_mul_eq_borel_mul_kC.lean",
    "P2M/Sol/S_AutomorphicForm_ComplexIwasawa_exists_forall_integrable_integral_rpow_neg_radC_le_of_isCompact.lean",
    # --- WORKORDER-I2 (the complex Iwasawa engine, successors; see PORT_FILES): same shape, the
    # three successor wrappers then their `S_` files. Appended last so no earlier last-name match
    # can flip.
    "Theorems/Thm_AutomorphicForm_ComplexIwasawa_contDiff_and_exists_forall_bound_iteratedFDeriv_cpow_neg_radC_of_isCompact.lean",
    "Theorems/Thm_AutomorphicForm_ComplexIwasawa_exists_forall_norm_fourierIntegral_cpow_radC_mul_le_polyDecay_of_isCompact.lean",
    "Theorems/Thm_AutomorphicForm_ComplexIwasawa_continuousOn_differentiableOn_norm_le_polyDecay_weightFourierIntegral.lean",
    "P2M/Sol/S_AutomorphicForm_ComplexIwasawa_contDiff_and_exists_forall_bound_iteratedFDeriv_cpow_neg_radC_of_isCompact.lean",
    "P2M/Sol/S_AutomorphicForm_ComplexIwasawa_exists_forall_norm_fourierIntegral_cpow_radC_mul_le_polyDecay_of_isCompact.lean",
    "P2M/Sol/S_AutomorphicForm_ComplexIwasawa_continuousOn_differentiableOn_norm_le_polyDecay_weightFourierIntegral.lean",
    # --- The adelic Siegel-covering definition layer (`topics/PORTING-DeligneSerre.md` §4(a)):
    # the pin `Definitions/Def_AutomorphicForm_CentreCutSiegelSetAmple.lean` ported whole
    # (11 declarations), homed beside its sibling `Def_AutomorphicForm_CentreCutSiegelSet`
    # at `AutomorphicForm/Adelic/WindowedSiegel/CentreCutSiegelSetAmple.lean`. Every name is
    # unique, so no earlier last-name match can flip. Appended last.
    "Definitions/Def_AutomorphicForm_CentreCutSiegelSetAmple.lean",
    # --- WORKORDER-SC1 (`topics/automorphicForm/WORKORDER-SC1-slab-covering.md`): the (central)
    # slab-covering headlines. Each is matched against its `Theorems/` wrapper and its `S_` engine;
    # the `S_`-local helpers are transcribed `private` in the tier-3 engine and so are skipped by
    # the checker. Appended last so no earlier last-name match can flip.
    "Theorems/Thm_AutomorphicForm_exists_finset_central_slab_covering_of_coversModCentre.lean",
    "P2M/Sol/S_AutomorphicForm_exists_finset_central_slab_covering_of_coversModCentre.lean",
    "Theorems/Thm_AutomorphicForm_exists_finset_central_slab_covering_of_coversModCentre_centreCutSiegelSetAmple.lean",
    "P2M/Sol/S_AutomorphicForm_exists_finset_central_slab_covering_of_coversModCentre_centreCutSiegelSetAmple.lean",
    "Theorems/Thm_AutomorphicForm_exists_finset_slab_covering_of_coversModCentre.lean",
    "P2M/Sol/S_AutomorphicForm_exists_finset_slab_covering_of_coversModCentre.lean",
    # --- Landau's theorem for L-series (`topics/numberTheory/WORKORDER-LS1-landau.md`): the
    # headline from its `Theorems/` wrapper, the engine/helper/corollaries from the `S_` file's
    # `P2M_Landau` section. The same `S_` file's ~2,960-line Landau–Siegel silo is unported and
    # has no consumer anywhere (it is not even in the pin's citation graph), so no port
    # declaration matches it and nothing is owed for it. Appended last.
    "Theorems/Thm_LSeries_abscissaOfAbsConv_lt_of_differentiableOn_ball.lean",
    "P2M/Sol/S_LSeries_abscissaOfAbsConv_lt_of_differentiableOn_ball.lean",
    # --- The manager's ground for the weighted-Petersson node (sesqForm): the pin
    # `Definitions/Def_AutomorphicForm_PeterssonIntegral.lean` (homed whole at
    # `AutomorphicForm/Adelic/PeterssonIntegral.lean`) and the public node
    # `AutomorphicForm.ideleNorm_det_globalPoints` (wrapper + `S_` file), which was previously
    # carried `private` in the slab engine and is now homed at
    # `AutomorphicForm/Adelic/IdeleNormDet.lean`. Appended last so no earlier last-name match
    # can flip.
    "Definitions/Def_AutomorphicForm_PeterssonIntegral.lean",
    "Theorems/Thm_AutomorphicForm_ideleNorm_det_globalPoints.lean",
    "P2M/Sol/S_AutomorphicForm_ideleNorm_det_globalPoints.lean",
    # --- WORKORDER-SC2 §5 (`topics/automorphicForm/WORKORDER-SC2-sesqForm.md`): the weighted
    # Petersson headline. The `S_` file's 70 private helpers are transcribed `private` in the
    # tier-3 engine and so are skipped by the checker; its public `solution` has no port
    # counterpart (the façade states the wrapper). Appended last so no earlier last-name match
    # can flip.
    "Theorems/Thm_AutomorphicForm_exists_sesqForm_eq_peterssonIntegral_of_isGenuineCuspRealizationAt_of_isFundamentalDomain.lean",
    "P2M/Sol/S_AutomorphicForm_exists_sesqForm_eq_peterssonIntegral_of_isGenuineCuspRealizationAt_of_isFundamentalDomain.lean",
    # --- WORKORDER-SC3 (`topics/automorphicForm/WORKORDER-SC3-fundamental-domain.md`): the
    # determinant-norm slab fundamental domain. The headline is matched against its `Theorems/`
    # wrapper; the pin's 25 private helpers are transcribed `private` (two of them imported from
    # tier-3 `AdelicLevel/Countability.lean`) and so are skipped by the checker. Appended last.
    "Theorems/Thm_AutomorphicForm_exists_isFundamentalDomain_globalPoints_range_restrict_ideleNorm_det_Icc.lean",
    "P2M/Sol/S_AutomorphicForm_exists_isFundamentalDomain_globalPoints_range_restrict_ideleNorm_det_Icc.lean",
    # --- WORKORDER-SC4 pre-wave: the shared archimedean-`K`-finiteness vocabulary
    # (`Definitions/Def_AutomorphicForm_ArchKFinite.lean`, 9 declarations, imported by 731 pin
    # files), homed whole. Appended last so no earlier last-name match can flip.
    "Definitions/Def_AutomorphicForm_ArchKFinite.lean",
    # --- WORKORDER-SC4 (`topics/automorphicForm/WORKORDER-SC4-induced-section-pair.md`): the
    # `IsInducedSection` pair. Both headlines are matched against their `Theorems/` wrappers and
    # the pin-public helpers against the `S_` files; the 4 re-carried modulus prelude rows are
    # imported from tier 3, so no port declaration matches them. Appended last.
    "Theorems/Thm_AutomorphicForm_isInducedSection_adelicHeight_cpow.lean",
    "P2M/Sol/S_AutomorphicForm_isInducedSection_adelicHeight_cpow.lean",
    "Theorems/Thm_AutomorphicForm_IsInducedSection_apply_globalPoints_mul_of_mem_borelSubgroup_and_apply_unipotentGL2_mul.lean",
    "P2M/Sol/S_AutomorphicForm_IsInducedSection_apply_globalPoints_mul_of_mem_borelSubgroup_and_apply_unipotentGL2_mul.lean",
    # --- WORKORDER-P1 (`topics/algebraicCurve/WORKORDER-P1-isPrimeOverValuationSubring.md`): the place realising a prime over a valuation subring; the wrapper carries the sole public headline and the `S_` silo is listed for it and the dotted fallback. Appended last.
    "Theorems/Thm_AlgebraicCurve_Place_exists_of_isPrime_over_valuationSubring.lean",
    "P2M/Sol/S_AlgebraicCurve_Place_exists_of_isPrime_over_valuationSubring.lean",
    # --- The `AlgebraicCurve.CellDissection.*`/`RadialRegion.*` cluster pre-wave: the two
    # pinned `Definitions/` modules every cluster node imports, homed whole. Appended last
    # so no earlier last-name match can flip.
    "Definitions/Def_AlgebraicCurve_ComplexLineIntegral.lean",
    "Definitions/Def_AlgebraicCurve_CellDissection.lean",
    # --- WORKORDER-R1 (`topics/algebraicCurve/WORKORDER-R1-radial-rectangle.md`): the two
    # radial-rectangle nodes. Statements from the `Theorems/` wrappers, proofs from the `S_`
    # silos; the tier-3 engines are unlisted (see `PORT_FILES`) and registered in
    # `spec/UNWIRED-PUBLIC.md`. Appended last so no earlier last-name match can flip.
    "Theorems/Thm_AlgebraicCurve_RadialRegion_exists_rect_sixArcs.lean",
    "P2M/Sol/S_AlgebraicCurve_RadialRegion_exists_rect_sixArcs.lean",
    "Theorems/Thm_AlgebraicCurve_RadialRegion_exists_refine_exact.lean",
    "P2M/Sol/S_AlgebraicCurve_RadialRegion_exists_refine_exact.lean",
    # --- WORKORDER-R2 (`topics/algebraicCurve/WORKORDER-R2-window-perimeter.md`): the window-perimeter node. Statement from the `Theorems/` wrapper, proof from the `S_` silo; the tier-3 engine is unlisted (see `PORT_FILES`) and registered in `spec/UNWIRED-PUBLIC.md`. Appended last so no earlier last-name match can flip.
    "Theorems/Thm_AlgebraicCurve_RadialRegion_exists_window_perimeter.lean",
    "P2M/Sol/S_AlgebraicCurve_RadialRegion_exists_window_perimeter.lean",
    # --- WORKORDER-R3a (`topics/algebraicCurve/WORKORDER-R3a-reparam-twin.md`): the reparametrisation
    # twin. The two `S_` files are byte-identical through line 704 (the shared development and both
    # internal theorems); statements from the `Theorems/` wrappers, proofs from the `S_` silos; the
    # single tier-3 engine is unlisted (see `PORT_FILES`) and registered in `spec/UNWIRED-PUBLIC.md`.
    # Appended last so no earlier last-name match can flip.
    "Theorems/Thm_AlgebraicCurve_RadialRegion_exists_reparam_across_edge.lean",
    "P2M/Sol/S_AlgebraicCurve_RadialRegion_exists_reparam_across_edge.lean",
    "Theorems/Thm_AlgebraicCurve_RadialRegion_exists_reparam_same_side.lean",
    "P2M/Sol/S_AlgebraicCurve_RadialRegion_exists_reparam_same_side.lean",
    # --- WORKORDER-R3b (`topics/algebraicCurve/WORKORDER-R3b-grid-geometry.md`): the grid-geometry
    # node. Statement from the `Theorems/` wrapper, proof from the `S_` silo; the tier-3 engine is
    # unlisted (see `PORT_FILES`) and registered in `spec/UNWIRED-PUBLIC.md`. Appended last so no
    # earlier last-name match can flip.
    "Theorems/Thm_AlgebraicCurve_RadialRegion_exists_grid_geometry.lean",
    "P2M/Sol/S_AlgebraicCurve_RadialRegion_exists_grid_geometry.lean",
    # --- WORKORDER-R4 (`topics/algebraicCurve/WORKORDER-R4-radial-miscellany.md`): the three radial
    # miscellany nodes (isOpen_starConvex_subset, recip, pow_pullback_laps). Statements from the
    # `Theorems/` wrappers, proofs from the `S_` silos; the tier-3 engines are unlisted (see
    # `PORT_FILES`) and registered in `spec/UNWIRED-PUBLIC.md`. Appended last so no earlier
    # last-name match can flip.
    "Theorems/Thm_AlgebraicCurve_RadialRegion_exists_isOpen_starConvex_subset.lean",
    "P2M/Sol/S_AlgebraicCurve_RadialRegion_exists_isOpen_starConvex_subset.lean",
    "Theorems/Thm_AlgebraicCurve_RadialRegion_exists_recip.lean",
    "P2M/Sol/S_AlgebraicCurve_RadialRegion_exists_recip.lean",
    "Theorems/Thm_AlgebraicCurve_RadialRegion_exists_pow_pullback_laps.lean",
    "P2M/Sol/S_AlgebraicCurve_RadialRegion_exists_pow_pullback_laps.lean",
    # --- WORKORDER-KF1 (`topics/automorphicForm/WORKORDER-KF1-kfinite-family-span.md`): the
    # K-finite-family local-finite-type leaf. Statement from the `Theorems/` wrapper, proof from
    # the `S_` silo; the two tier-3 engines (`RepTheory/TranslateSpan.lean`,
    # `AutomorphicForm/Adelic/ArchKFiniteFamily.lean`) stay unlisted (see `PORT_FILES`) and are
    # registered in `spec/UNWIRED-PUBLIC.md`. Appended last so no earlier last-name match can flip.
    "Theorems/Thm_AutomorphicForm_exists_isOpen_forall_exists_apply_eq_sum_of_isArchKFinite_of_continuous.lean",
    "P2M/Sol/S_AutomorphicForm_exists_isOpen_forall_exists_apply_eq_sum_of_isArchKFinite_of_continuous.lean",
    # --- WORKORDER-TO4 (`topics/automorphicForm/WORKORDER-TO4-unit-factorizable-trio.md`): the
    # unit-factorizable trio. Statements from the three `Theorems/` wrappers, proofs from the three
    # `S_` silos; the tier-3 engine `AutomorphicForm/Adelic/UnitFactorizableEngine.lean` stays
    # unlisted (see `PORT_FILES`) and is registered in `spec/UNWIRED-PUBLIC.md`. Appended last so
    # no earlier last-name match can flip.
    "Theorems/Thm_AutomorphicForm_exists_isUnitFactorizableAboveOfType_tendsto_rightConv_of_mem_archCutSubmodule.lean",
    "P2M/Sol/S_AutomorphicForm_exists_isUnitFactorizableAboveOfType_tendsto_rightConv_of_mem_archCutSubmodule.lean",
    "Theorems/Thm_AutomorphicForm_exists_finTestFactor_isUnitFactorizableAboveOfType_tendsto_rightConv_of_mem_archCutSubmodule.lean",
    "P2M/Sol/S_AutomorphicForm_exists_finTestFactor_isUnitFactorizableAboveOfType_tendsto_rightConv_of_mem_archCutSubmodule.lean",
    "Theorems/Thm_AutomorphicForm_exists_isUnitFactorizableAboveOfType_principalLevel_tendsto_rightConv_of_mem_archCutSubmodule.lean",
    "P2M/Sol/S_AutomorphicForm_exists_isUnitFactorizableAboveOfType_principalLevel_tendsto_rightConv_of_mem_archCutSubmodule.lean",
    # --- WORKORDER-CT1 (`topics/deligneSerre/WORKORDER-CT1-comm-triplet.md`): the
    # `CohCarrier` Hecke–diamond commutation triplet. The three `Theorems/` wrappers are the
    # statement authority for the three tier-1 headlines; the shared `S_` development is the
    # pin original for the tier-3 engine `CohCarrier/Engine/CommTriplet.lean` (unlisted,
    # registered in `spec/UNWIRED-PUBLIC.md`), so it is listed for the register's pin-original
    # column even though no declaration of it is diffed directly. Appended last so no earlier
    # last-name match can flip.
    "Theorems/Thm_CohCarrier_heckeT_diamondRaw_comm.lean",
    "Theorems/Thm_CohCarrier_heckeT_comm_of_prime.lean",
    "Theorems/Thm_CohCarrier_diamondRaw_comm.lean",
    "P2M/Sol/S_CohCarrier_heckeT_diamondRaw_comm.lean",
    # --- The Hahn-series algebraic-closure supplement (pure mathlib content,
    # `FLTForHuman/RingTheory/HahnSeries/IsAlgClosed.lean`). The module is **unlisted**
    # (tier 3): nothing of it is statement-diffed here. These two sources are the pin
    # originals its 67 public declarations resolve against -- the wrapper for the
    # headline, the `S_` development for the other 66 -- so the tier-3 register
    # `spec/UNWIRED-PUBLIC.md` can fill its pin-original column. Appended last.
    "Theorems/Thm_HahnSeries_isAlgClosed_rat.lean",
    "P2M/Sol/S_HahnSeries_isAlgClosed_rat.lean",
    # --- The Petersson adjointness on a nebentypus component. The wrapper is the tier-1
    # headline's statement authority; the `S_` development is the pin original for the
    # tier-3 engine `ModularForms/Analytic/PeterssonHecke.lean` (unlisted, registered in
    # `spec/UNWIRED-PUBLIC.md`), so it is listed for the register's pin-original column.
    "Theorems/Thm_CuspForm_peterssonOn_hecke_eq_conj_mul_of_hasNebentypus.lean",
    "P2M/Sol/S_CuspForm_peterssonOn_hecke_eq_conj_mul_of_hasNebentypus.lean",
    # --- The Petersson definition layer and the fundamental-domain ground it needs.
    # `Def_CuspForm_PeterssonOn` is the source of the three `peterssonOn` definitions;
    # `Def_AutomorphicForm_ModularFundamentalDomain` of the sixteen `goodSet`/translate
    # lemmas the port keeps (its four gate theorems are deferred in CARRY-FORWARD).
    "Definitions/Def_CuspForm_PeterssonOn.lean",
    "Definitions/Def_AutomorphicForm_ModularFundamentalDomain.lean",
    # --- The coset-space Petersson definition layer
    # (`topics/deligneSerre/TOPIC-petersson-coset-and-level-prime-eigenvalue.md`
    # §5, set P1): the source of all 56 declarations of
    # `ModularForms/Analytic/PeterssonCoset.lean`. Appended last.
    "Definitions/Def_CuspForm_PeterssonCoset.lean",
    # --- Set P2, the level-prime eigenvalue (`WORKORDER-P2-normsq.md`): the wrapper is the
    # headline's statement authority, the `S_` file the source of the 71 `LiNormSq`
    # declarations. Appended last.
    "Theorems/Thm_CuspForm_norm_sq_eq_pow_of_qCoeff_mul_eq_of_not_factorsThrough.lean",
    "P2M/Sol/S_CuspForm_norm_sq_eq_pow_of_qCoeff_mul_eq_of_not_factorsThrough.lean",
    # --- The archimedean Casimir definition layer (`WORKORDER-AC1-defs.md`,
    # `topics/automorphicForm/TOPIC-arch-casimir.md` §4): the two pin `Definitions/`
    # modules the whole 78-file arch-derivative subject is phrased against. A
    # definition module has no `Theorems/` wrapper, so both verify by name against
    # their `Definitions/` files. Appended last.
    "Definitions/Def_LanglandsTunnell_ArchParam.lean",
    "Definitions/Def_AutomorphicForm_ArchDerivCasimir.lean",
    # --- Set A (`WORKORDER-AC2-cascore-trio.md`): the statement authority for the three
    # real-place headlines. The engine `S_` files are deliberately NOT listed: every
    # non-headline public declaration of `ArchCasimir.lean` carries a `-- pin:` marker into
    # one of them, which is the checker's UNWIRED (tier-3) exemption, and they are registered
    # in spec/UNWIRED-PUBLIC.md. Appended last so no earlier last-name match can flip.
    "Theorems/Thm_AutomorphicForm_archCasimirAt_rightTranslate_archRealGLAt.lean",
    "Theorems/Thm_AutomorphicForm_leftCasimir_eq_archCasimirAt_of_isArchSmoothAt.lean",
    "Theorems/Thm_AutomorphicForm_iterate_raise_iterate_lower_eq_smul_of_archCasimirAt_eq_smul.lean",
    # --- The cut-vector weight decomposition's definition layer
    # (`topics/automorphicForm/TOPIC-cut-weight-decomposition.md`): the first of the six
    # unported pin `Definitions/` modules its closure needs. Appended last.
    "Definitions/Def_AutomorphicForm_WhittakerCoefficient.lean",
    "Definitions/Def_NumberField_StandardGlobalAddCharRat.lean",
    # --- `WORKORDER-CD1-def-wave.md`: the rest of the cut-weight definition wave, all four
    # transcribed verbatim by the set and reviewed here. Appended last.
    "Definitions/Def_NumberField_StandardGlobalAddChar.lean",
    "Definitions/Def_NumberField_AdelicTraceProducer.lean",
    "Definitions/Def_NumberField_IntegralAdelicTrace.lean",
    "Definitions/Def_NumberField_AdelicTraceFin.lean",
    # --- `WORKORDER-CD2-cut-weight-proof.md`: statement authority for the cut-vector weight
    # decomposition headline. The `S_` file is deliberately NOT listed — every other public
    # declaration of the module carries a `-- pin:` marker into it (the checker's UNWIRED tier 3)
    # and is registered in spec/UNWIRED-PUBLIC.md. Appended last.
    "Theorems/Thm_AutomorphicForm_CuspidalConstituent_exists_eq_sum_hasArchCharacterAt_archWeightCharAt_of_isCuspConstituent.lean",
    # --- The centre-cut vanishing leaf (`AutomorphicForm.eq_zero_of_isAutomorphicFnAt_of_continuous_of_nonpos_of_lt_of_coversModCentre`).
    # The wrapper is the headline's statement authority; the `S_` file is the pin original
    # for the shared engine and the headline. The engine itself is unlisted (tier 3,
    # `Cusp/CentreCutEngine.lean`), so only the façade is diffed. Appended last.
    "Theorems/Thm_AutomorphicForm_eq_zero_of_isAutomorphicFnAt_of_continuous_of_nonpos_of_lt_of_coversModCentre.lean",
    "P2M/Sol/S_AutomorphicForm_eq_zero_of_isAutomorphicFnAt_of_continuous_of_nonpos_of_lt_of_coversModCentre.lean",
    # --- The sibling (`AutomorphicForm.not_isArithGenuineCuspRealizable_of_nonpos_of_lt_of_coversModCentre`):
    # same shared engine, one headline. The wrapper is the statement authority, the `S_`
    # file the pin original of the sibling's tail; the engine is not re-listed. Appended last.
    "Theorems/Thm_AutomorphicForm_not_isArithGenuineCuspRealizable_of_nonpos_of_lt_of_coversModCentre.lean",
    "P2M/Sol/S_AutomorphicForm_not_isArithGenuineCuspRealizable_of_nonpos_of_lt_of_coversModCentre.lean",
    # --- The centre-cut fundamental-domain trio: automorphy transfer (325) and the two
    # measurable-fundamental-domain twins (267/266). The wrappers are the statement
    # authorities; the `S_` files are deliberately NOT listed — the shared 20-declaration
    # slab prelude promoted public in `PeterssonSlabPairing.lean` carries `-- pin:` markers
    # into them (the checker's UNWIRED tier 3) and is registered in
    # `spec/UNWIRED-PUBLIC.md`. Appended last so no earlier last-name match can flip.
    "Theorems/Thm_AutomorphicForm_isAutomorphicFnAt_of_isFundamentalDomain_of_isAutomorphicFnAt_of_coversModCentre.lean",
    "Theorems/Thm_AutomorphicForm_exists_measurableSet_isFundamentalDomain_subset_iUnion_integralWindowedSiegelSet_of_coversModCentre.lean",
    "Theorems/Thm_AutomorphicForm_exists_measurableSet_isFundamentalDomain_subset_iUnion_centreCutSiegelSet_of_coversModCentre.lean",
    # --- The complex archimedean Casimir definition layer (two pin `Definitions/` modules) and
    # the complex engine's headline. The two Definitions modules have no wrappers, so they verify
    # by name against their `Definitions/` files; the engine `S_` file is deliberately NOT listed
    # (its ~96 public declarations carry `-- pin:` markers into it, the checker's UNWIRED tier 3,
    # and are registered in `spec/UNWIRED-PUBLIC.md`). Appended last so no earlier last-name
    # match can flip.
    "Definitions/Def_AutomorphicForm_ArchDerivCasimirComplex.lean",
    "Definitions/Def_AutomorphicForm_ArchDerivCasimirComplexAPI.lean",
    "Theorems/Thm_AutomorphicForm_archCasimirAtComplex_rightTranslate_archComplexGLAt.lean",
    # --- The continuous norm section (`topics/numberTheory/tateGlobal/TOPIC-norm-section.md`;
    # WORKORDER-T4): `NumberField.TateGlobal.exists_continuous_monoidHom_ideleNorm_apply_eq`. The
    # wrapper is the statement authority; the `S_` file is deliberately NOT listed — the shared
    # 25-declaration engine (`…/TateGlobal/NormSection.lean`) carries `-- pin:` markers into it
    # (the checker's UNWIRED tier 3) and is registered in `spec/UNWIRED-PUBLIC.md`. Appended last
    # so no earlier last-name match can flip.
    "Theorems/Thm_NumberField_TateGlobal_exists_continuous_monoidHom_ideleNorm_apply_eq.lean",
    # --- GL₂ strong approximation over ℚ (`topics/numberTheory/adelicLevel/TOPIC-gl2-strong-approximation.md`;
    # WORKORDER-T5): `NumberField.AdelicLevel.exists_globalPoints_mul_mem_finiteIntegralGL2_rat`.
    # The wrapper is the statement authority; the `S_` file is deliberately NOT listed — the
    # 45-declaration engine (`…/AdelicLevel/StrongApprox/*.lean`) carries `-- pin:` markers into
    # it (the checker's UNWIRED tier 3) and is registered in `spec/UNWIRED-PUBLIC.md`. Appended
    # last so no earlier last-name match can flip.
    "Theorems/Thm_NumberField_AdelicLevel_exists_globalPoints_mul_mem_finiteIntegralGL2_rat.lean",
    # --- WORKORDER-E1, the definition gate of the local twisted-integral set
    # (`topics/numberTheory/eisensteinGeneral/TOPIC-local-twisted-integral.md`): the pin's
    # `Def_LanglandsTunnell_TateLocalConstantsAt` has no `Theorems/` wrapper, so it is its own
    # statement authority and the port module is diffed whole (`higherUnitsAt`,
    # `HasConductorExponentAt`, `conductorExponentAt`, `localLFactorAt`, `localEpsilonAt`, 21
    # declarations). Appended last so no earlier last-name match can flip.
    "Definitions/Def_LanglandsTunnell_TateLocalConstantsAt.lean",
    # --- WORKORDER-E1, Set A of the local twisted-integral cluster
    # (`topics/numberTheory/eisensteinGeneral/TOPIC-local-twisted-integral.md`): the three
    # `EisensteinGeneral.LocalRam` headlines at a ramified place. The wrappers are the statement
    # authorities; the three `S_` files are deliberately NOT listed — the two engines
    # (`EisensteinGeneral/LocalTwisted.lean`, `…/LocalRamShells.lean`) carry `-- pin:` markers into
    # them (the checker's UNWIRED tier 3) and are registered in `spec/UNWIRED-PUBLIC.md`.
    # Appended last so no earlier last-name match can flip.
    "Theorems/Thm_EisensteinGeneral_LocalRam_integral_twisted_smooth_eq.lean",
    "Theorems/Thm_EisensteinGeneral_LocalRam_integrable_twisted_smooth.lean",
    "Theorems/Thm_EisensteinGeneral_LocalRam_integral_twisted_smooth_eq_zero_of_exp_lt.lean",
    # --- WORKORDER-E2, Set B of the same cluster: the unramified pair. Here the two `S_` files ARE
    # listed, unlike Set A: this set's machinery has no other consumer, so it is written into the
    # one listed module `EisensteinGeneral/LocalUnr.lean` and every declaration of it is diffed
    # against the wrappers (statement authority) or the `S_` files (the machinery). The pin's
    # `private` machinery is matched through the checker's promoted-from-pin-private fallback.
    "Theorems/Thm_EisensteinGeneral_LocalUnr_integrable_twisted_and_integral_norm_eq.lean",
    "Theorems/Thm_EisensteinGeneral_LocalUnr_integral_twisted_eq_zero_of_exp_lt.lean",
    "P2M/Sol/S_EisensteinGeneral_LocalUnr_integrable_twisted_and_integral_norm_eq.lean",
    "P2M/Sol/S_EisensteinGeneral_LocalUnr_integral_twisted_eq_zero_of_exp_lt.lean",
    # --- WORKORDER-E3: the finite-adelic integral as an Euler product
    # (`topics/numberTheory/eisensteinGeneral/TOPIC-factorization.md`). Unlike Sets A/B, the pin `S_`
    # file IS listed and all six port modules are in `PORT_FILES`: the silo is 57 unique public
    # declarations with no other consumer, so every one of them is statement-diffed through the
    # `-- pin:` markers (the checker's exact-pin-name route) instead of being exempted as tier 3.
    # The wrapper comes FIRST: it is the statement authority for the headline, whose pin-private
    # copy inside the `S_` file has `F` as a section variable and would shadow it by last name
    # (that pairing was caught as a MISMATCH on the first run). The `S_` file follows so the
    # engine's public block resolves through the pin-private dotted fallback.
    "Theorems/Thm_EisensteinGeneral_Factorization_integrable_finprod_and_inv_measure_mul_integral_eq_tprod.lean",
    "P2M/Sol/S_EisensteinGeneral_Factorization_integrable_finprod_and_inv_measure_mul_integral_eq_tprod.lean",
    # --- WORKORDER-P3: the nebentypus Hecke bound (`topics/deligneSerre/WORKORDER-P3-normsq-lt.md`),
    # the sibling of the `NormSqPow` silo. The wrapper comes FIRST: it is the statement authority
    # for the headline; the `S_` file follows so the 32 new engine declarations resolve through
    # their `-- pin:` markers. The 24 declarations this silo shares with `NormSqPow.lean` are NOT
    # redeclared (they are already checked there), so they are not diffed twice.
    "Theorems/Thm_CuspForm_norm_sq_lt_of_hasNebentypus_qCoeff_hecke_eigen.lean",
    "P2M/Sol/S_CuspForm_norm_sq_lt_of_hasNebentypus_qCoeff_hecke_eigen.lean",
]


PORT_FILES = [
    "FLTForHuman/FieldTheory/CommonRoot.lean",
    # (removed) `FLTForHuman/ModularCurve/Defs/Laurent.lean` — now wired by its own
    # `spec-pin:` lines (`Def_ModularCurve_X0`, `Def_ModularCurve_LaurentCoeff`, the four
    # outbound `Thm_` wrappers and the two `HeckeCompositum` files).
    "FLTForHuman/ModularCurve/Defs/Twist.lean",
    "FLTForHuman/ModularCurve/Defs/Jq.lean",
    # The pin-namespaced spelling of the Dedekind `ψ` function. The mathematics
    # moved on 2026-10-09 to `NumberTheory/DedekindPsi.lean` (listed below); this
    # shim keeps the pin's `ModularCurve.dedekindPsi…` names for the five qualified
    # uses and the `spec/` probes. Both files are listed, so the pin names are
    # diffed twice — harmless, and it keeps the moved statements verified even if
    # the shim is ever dropped.
    "FLTForHuman/ModularCurve/Defs/DedekindPsi.lean",
    "FLTForHuman/ModularCurve/FunctionFieldGeneration/Target.lean",
    "FLTForHuman/ModularCurve/Defs/Polynomial.lean",
    "FLTForHuman/ModularCurve/Defs/Fields.lean",
    "FLTForHuman/ModularCurve/Defs/PhiGen.lean",
    "FLTForHuman/ModularCurve/FunctionFieldGeneration/Collapse.lean",
    "FLTForHuman/ModularCurve/JqCoefficients.lean",
    "FLTForHuman/ModularCurve/FunctionFieldGeneration/Spine.lean",
    "FLTForHuman/ModularCurve/Defs/Cyclotomic.lean",
    "FLTForHuman/ModularForms/QExpansionPrinciple.lean",
    "FLTForHuman/ModularForms/JqAnalyticModel.lean",
    "FLTForHuman/ModularForms/Hauptmodul.lean",
    "FLTForHuman/ModularForms/Defs/HeckeOperator.lean",
    "FLTForHuman/ModularForms/Defs/HeckeRepresentatives.lean",
    "FLTForHuman/ModularForms/HeckeFricke.lean",
    "FLTForHuman/ModularForms/HeckeCusps.lean",
    # SET-3 T5: the formal `PowerSeries` operators and the shared `q`-coefficient tail.
    "FLTForHuman/ModularForms/Defs/FormalHeckeOperators.lean",
    # SET-3 T6: the bundled `heckeTLin`/`heckeULin` and the three thin wrappers.
    "FLTForHuman/ModularForms/HeckeOperatorForms.lean",
    # SET-3 T7: the formal-series operators, the commutations and the algebra.
    "FLTForHuman/ModularCurve/Defs/LaurentSeriesHecke.lean",
    "FLTForHuman/ModularForms/HeckeCommute.lean",
    "FLTForHuman/ModularForms/HeckeAlgebra.lean",
    # SET-4 T8: the normalized-eigenform structure and its operator dictionary.
    "FLTForHuman/ModularForms/Defs/Eigenform.lean",
    # SET-4 T9: the integral-lattice definitions and the lattice action.
    "FLTForHuman/ModularForms/Defs/IntegralStructure.lean",
    # SET-4 T10 definitions survived; T10's theorem half is complete with route
    # C′/the Sturm bound — the finiteness family lives in `HeckeFiniteAlgebra.lean`
    # and the lattice facts in `HeckeLattice.lean`. The eigenbasis-span family is
    # still absent (see the `SOURCES` note and `logs/hecke-port.md` §T10).
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
    # Topic 20, the unconditional capstone.
    "FLTForHuman/ModularCurve/FunctionFieldGeneration/Capstone.lean",
    # SET 1 (AC0 + T1), the generic curve vocabulary and the ord interface.
    "FLTForHuman/AlgebraicCurve/Defs/Place.lean",
    # `Divisor.lean` is now wired to `spec/check_port.py` (2026-10-27) by its own
    # `spec-pin:` block over `Def_AlgebraicCurve_DivisorClassGroup.lean` and
    # `S_AlgebraicCurve_Divisor_degree_eq_sum.lean` (18 ok / 0 mismatch / 0 missing).
    # Handed over: do not re-list it here.
    # MIGRATED 2026-10-27 (SET 3 ground prep): both now carry their own `spec-pin:`
    # wire and are owned by `spec/check_port.py` — `PushPull` 63 ok / 0 mismatch /
    # 0 missing (its pin Def module plus the five `S_` files the promoted ord
    # helpers come from), `PlacesOverDVR` 36 ok / 0 / 0. Their `SOURCES` entries
    # stay, since other listed modules still match against them. Do not re-list
    # either module here.
    "FLTForHuman/AlgebraicCurve/Defs/Correspondence.lean",
    # `SemilinearAut.lean` is now wired to `spec/check_port.py` (2026-10-27) by its own
    # `spec-pin:` block, over `Def_AlgebraicCurve_BaseChangeGalois.lean` and
    # `Def_AlgebraicCurve_DivisorClassGroup.lean` (43 ok / 0 mismatch / 0 missing / 0 own).
    # Handed over: do not re-list it here.
    "FLTForHuman/AlgebraicCurve/Defs/RatFuncPlaces.lean",
    "FLTForHuman/AlgebraicCurve/Defs/IntegralAdjoin.lean",
    # T2 (the promoted fibre dictionary and the bifibre count).
    "FLTForHuman/AlgebraicCurve/Defs/PlaceDictionary.lean",
    # T3 (Galois ramification/inertia).
    # MIGRATED 2026-10-27 (SET 4 ground prep): the module carries its own `spec-pin:`
    # wire (the seven T3 wrappers) and checks 7 ok / 0 mismatch / 0 missing. The
    # `SOURCES` entries above stay — appended last so the dotted fallback still reads
    # the pin-private originals other listed modules match. Do not re-list it here.
    # T4 (along-map transport + `Pic0` descent, and the shared prelude).
    "FLTForHuman/AlgebraicCurve/WeilExchange/Transport.lean",
    # T5 (the generic orbit/index engine + the bifibre count).
    "FLTForHuman/FieldTheory/FiniteGroupAction.lean",
    # `Bifibre.lean` is now wired to `spec/check_port.py` (2026-10-26) by its own
    # `spec-pin:` block — the bifibre count, the fibre/cardinality bridge,
    # `Place.exists_restrict_eq` and `Place.restrictAlong_surjective`. Do not re-list it.
    # T6 (the local exchange + the normal closure).
    "FLTForHuman/AlgebraicCurve/WeilExchange/LocalExchange.lean",
    # T8 (the `P¹` places and degree).
    "FLTForHuman/AlgebraicCurve/PrincipalDivisors/RatFuncDegree.lean",
    # T9 (`HasPrincipalDivisors` via transcendence).
    # MIGRATED 2026-10-27 (SET 3 ground prep): the module carries its own `spec-pin:`
    # wire (the two T9 `S_` files, the norm block's two, and the wrapper whose binders
    # the public `pushforwardNormFormula` transcribes) and checks 6 ok / 0 mismatch /
    # 0 missing, the promoted `Place.ord_norm_eq_sum_fiberOver` included. Do not
    # re-list it here.
    # T7, the divisor-exchange capstone (reserved for the human reviewer).
    "FLTForHuman/AlgebraicCurve/WeilExchange/DivisorExchange.lean",
    # SET-M1 m1: the Hecke correspondence vocabulary.
    "FLTForHuman/ModularCurve/Defs/HeckeOperator.lean",
    "FLTForHuman/ModularCurve/Defs/DegeneracyTower.lean",
    "FLTForHuman/ModularCurve/Defs/HeckeTotal.lean",
    # `ArithmeticGalois.lean` is now wired to `spec/check_port.py` (2026-10-27) by its own
    # `spec-pin:` block over `Def_ModularCurve_ArithmeticGalois.lean` (13 ok / 0 mismatch /
    # 0 missing). Handed over: do not re-list it here.
    "FLTForHuman/ModularCurve/Defs/HeckeModule.lean",
    # SET-M1 m2: the geometric/cusp/q-adic/modular-unit vocabulary.
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
    # --- `FLTForHuman/ModularCurve/Degree/PhiDegree.lean` is handed over to
    # `spec/check_port.py` (2026-10-25, when the `coeff_jqModC_*` trio was promoted
    # into its home `Defs/JqCoeff.lean` and this module took a `spec-pin:` wire):
    # it checks 3 ok / 0 mismatch / 0 missing. Do not re-list it here.
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
    # SET-M3 m7: the Laurent/`coeffEmb` glue (the eight short M4 nodes).
    # (removed) `FLTForHuman/ModularCurve/Degree/LaurentGlue.lean` — now wired by its own
    # `spec-pin:` lines (`laurentBaseChange_adjoin` and the two `HeckeCompositum` files).
    # SET-M3 m7: `relfinrank_laurentBaseChange` (the pin's `TransportDev` block).
    # (removed) `FLTForHuman/ModularCurve/Degree/Relfinrank.lean` — now wired by its own
    # `spec-pin:` lines (`relfinrank_laurentBaseChange` and the two `HeckeCompositum` files).
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
    # SET-6, order 2: the χ₋₃ weight-one Eisenstein series — MIGRATED 2026-10-20 to the per-module
    # wire (`spec-pin:` in its header, checked by `spec/check_port.py`): three headlines are public
    # now, and the two blocks that were `private` transplants of other pin modules (the Γ₀(3)
    # generation engine, the ν₃ numerics) have moved to their own modules. Deliberately no entry
    # here, per the playbook's migration rule: a module moves when it is edited for another reason.
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
    # SET-10, order 2: the three bounded-denominator headlines. This module used to
    # be listed here; it now carries its own `spec-pin:` header (2026-10-21), and
    # `ModularCurve.IsIntegralQExp` moved to `X1/Integral.lean` (also wired).
    # SET-11, order 1: the six Γ₁-basis headlines. Each pin `S_` file's helpers
    # are `private` in the pin's own inner namespace (`WeightLoweringCriterion` /
    # `Gamma1Eisenstein` / `FrickeCuspTransport` / `FrickeSpan` /
    # `GammaOneGaloisEven` / `GammaOneGaloisAllWeights`, nested in
    # `WLightS11.*`), so the checker sees only the six headlines.
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
    # Post-SET-3 dedup: the counting core shared by SlotProduct and Gamma0Index,
    # and (2026-10-09) the whole Dedekind `ψ` subject moved out of `Defs/Jq.lean`
    # and merged with `DedekindPsiCount.lean` into this one `NumberTheory/` module.
    "FLTForHuman/NumberTheory/DedekindPsi.lean",
    # The general-weight Eichler–Shimura period map and its injectivity
    # (TOPIC-period-map-injectivity): the four generic facts in their subject
    # homes, the definitions, the leaves and the map.
    "FLTForHuman/Algebra/MvPolynomialHomogeneous.lean",
    "FLTForHuman/ModularForms/Analytic/StarConvexPrimitive.lean",
    "FLTForHuman/ModularForms/Analytic/CuspBoundedness.lean",
    "FLTForHuman/ModularForms/ModularGroup.lean",
    "FLTForHuman/ModularForms/EichlerShimura/BinaryForm.lean",
    "FLTForHuman/ModularForms/EichlerShimura/CoeffCohomology.lean",
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
    "FLTForHuman/ModularForms/HeckeNebentypus.lean",
    "FLTForHuman/ModularForms/Gamma1Vanishing.lean",
    "FLTForHuman/ModularCurve/IharaSurjective.lean",
    # --- S3 (Deligne–Serre relèvement and weight-one → weight-two lifting) ---
    # The weight-generic relèvement first, then the weight-one instance that
    # imports it. Appended last.
    "FLTForHuman/DeligneSerre/Lifting.lean",
    # --- S4 (Deligne–Serre coefficient ring and Galois conjugation) ---
    # The two new modules. `FLTForHuman/Algebra/IntegralExtensionCharacters.lean`
    # and `FLTForHuman/Algebra/FaithfulLatticeEigenvector.lean`, extended by S4,
    # are already listed above. Appended last.
    "FLTForHuman/Algebra/LatticeEigenvalues.lean",
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
    # --- `FLTForHuman/AlgebraicCurve/Defs/CanonicalDivisor.lean` is handed over to
    # `spec/check_port.py` (2026-10-25): its `spec-pin:` wire checks 21 ok / 0 mismatch
    # / 0 missing / 1 own. Do not re-list it here.
    "FLTForHuman/AlgebraicCurve/Defs/Repartitions.lean",
    # (removed) `Defs/AdelicIndex.lean` — SET 6 deleted this stale row: the module has
    # carried its own `spec-pin:` wire since 2026-10-26 (H1a; 69 ok / 0 / 0) and was being
    # checked twice. Its `SOURCES` rows stay.
    "FLTForHuman/AlgebraicCurve/Defs/IsCurveOver.lean",
    "FLTForHuman/AlgebraicCurve/Defs/RiemannRochRows.lean",
    # MIGRATED 2026-10-27 (SET 3 ground prep): `Defs/PoleDivisorPackage.lean` carries
    # its own `spec-pin:` wire over `Definitions/Def_AlgebraicCurve_PoleDivisorPackage.lean`
    # and checks 10 ok / 0 mismatch / 0 missing. Do not re-list it here.
    # --- H1a (the adelic-index / `ell` prelude and the index targets): handed over to
    # `spec/check_port.py` (2026-10-26) by its own `spec-pin:` wire — 72 ok / 0 mismatch /
    # 0 missing / 0 own. Do not re-list it here.
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
    # --- P2 (the canonical divisor and its two Kähler prerequisites), the modules
    # that consume the D/H3 layer. KaehlerTranscendental first (the two headlines
    # the HasCanonicalDivisor chain applies), then the construction. Appended last
    # so no earlier last-name match can flip.
    "FLTForHuman/AlgebraicCurve/Defs/KaehlerTranscendental.lean",
    # --- the canonical-divisor layer is handed over to `spec/check_port.py`
    # (2026-10-25) and split by subject: `Canonical/ValSubringKaehler.lean` (50 ok /
    # 7 own), `Canonical/AffineChart.lean` (37 ok / 0 own),
    # `Canonical/DCoordGenerates.lean` (10 ok / 0 own) and
    # `Canonical/HasCanonicalDivisor.lean` (11 ok / 2 own); every wire is 0 mismatch /
    # 0 missing. Do not re-list any of them here.
    # --- P3.1a (the adic-completion layer the `HasCanonicalLocalResidueKStar`
    # producer of P3.1b runs over). Appended last so no earlier last-name match can
    # flip.
    # --- P3.1b-i: the `Place` pole/Laurent layer of the V2 producer (pin lines
    # 1–789). Set 3.1b-ii appends the Hensel engine and the final instance to the
    # same module. Appended last so no earlier last-name match can flip.
    # --- P3.2a (the ℙ¹ place/ord dictionary): the generic place-evaluation
    # interface, the `Divisor.evalFun_*` algebra it consumes, and the ℙ¹
    # dictionary itself. Appended last so no earlier last-name match can flip.
    # MIGRATED 2026-10-27: `Defs/PlaceEvaluation.lean` now carries its own
    # `spec-pin:` wire — the pin Def module plus the six `S_` files holding its
    # `evalAt`/`isRational` algebra — and `spec/check_port.py` owns it
    # (21 ok / 0 mismatch / 0 missing). The module's `SOURCES` entries stay,
    # since other listed modules still match against them.
    "FLTForHuman/AlgebraicCurve/Defs/PlaceEvaluationAlgebra.lean",
    # (removed) `P1/Dictionary.lean` — SET 6 migrated it: the module now carries its own
    # 26-line `spec-pin:` wire (the two `Def_` files, the eleven wrappers, the eleven `S_`
    # files and the `weilReciprocity` pair) and checks 69 ok / 0 mismatch / 0 missing
    # before the capstone, 70 after. Its `SOURCES` rows stay.
    # --- P3.2b–e (the ℙ¹ residue core), split by the R1 definitions round into the
    # `P1/` module family (see `topics/riemannRoch/PLAN-RECTIFY-DEFS.md`). The
    # declarations and their order are unchanged; building `P1/Core` builds the
    # whole chain. `P1/Core.lean` has since been handed over to `spec/check_port.py`
    # (its `spec-pin:` wire checks 42 ok / 0 / 0); the earlier slices below stay
    # listed. Appended last so no earlier last-name match can flip.
    # --- `P1/EnginePrelude.lean` and `P1/DivisorAction.lean` are handed over to
    # `spec/check_port.py` (2026-10-27, when the `ord_add_eq_of_lt` duplicate was
    # retired for the public node in `Place/OrdCalculus.lean`): their `spec-pin:`
    # wires check 40 ok and 19 ok, both 0 mismatch / 0 missing. Do not re-list.
    "FLTForHuman/AlgebraicCurve/P1/Differential.lean",
    "FLTForHuman/AlgebraicCurve/P1/UnitNormalForm.lean",
    "FLTForHuman/AlgebraicCurve/P1/DXCoeff.lean",
    # --- `FLTForHuman/AlgebraicCurve/P1/UnitFinite.lean` is handed over to `spec/check_port.py`: its `spec-pin:` wire
    # checks 15 ok / 0 mismatch / 0 missing. Do not re-list it here.
    "FLTForHuman/AlgebraicCurve/P1/FinitePlaceResidue.lean",
    "FLTForHuman/AlgebraicCurve/P1/TraceEngine.lean",
    "FLTForHuman/AlgebraicCurve/P1/Separating.lean",
    "FLTForHuman/AlgebraicCurve/P1/Adjoin.lean",
    "FLTForHuman/AlgebraicCurve/P1/PerfectPrelude.lean",
    "FLTForHuman/AlgebraicCurve/P1/KaehlerIntegral.lean",
    "FLTForHuman/AlgebraicCurve/P1/PerfectField.lean",
    "FLTForHuman/AlgebraicCurve/P1/PerfectResidue.lean",
    # --- P3.2d′ (the generic local residue calculus): the char-free toolkit plus the
    # headline, homed before engine chunk 3 so the ℙ¹ core imports it instead of
    # re-transcribing. `Defs/PushPull.lean`'s `ord_nonneg_of_mem`/`mem_of_ord_nonneg`/
    # `mem_iff_ord_nonneg` are imported, not re-proved. `LocalResidue/Calculus.lean` has
    # since been handed over to `spec/check_port.py` (its `spec-pin:` wire checks
    # 32 ok / 0 / 0). Do not re-list it here.
    # --- P3.2f: the atom-2 two-place cancellation tail (see the `SOURCES` note
    # above). Appended last so no earlier last-name match can flip.
    "FLTForHuman/AlgebraicCurve/P1/TwoPlace.lean",
    # --- P3.2f: the atom-3 `P1Tower` tail. The headline
    # `trace_localResidue_finitePlace_div_pow_eq_zero` was gated on the Tate
    # agreement when 3.2f landed; set 3.2g supplies it in
    # `P1/DivPowEnding.lean` (registered below).
    # --- P3.3a: the Tate agreement finiteness half. `Defs/TateResidueCurrency.lean`
    # is the row-3.3 shared API definitions home (PLAN-RECTIFY-DEFS §2/§8.2); the
    # proof theory is `Tate/CommFinite.lean`. Appended last.
    # --- P3.3b: the Tate chain rule. Imports `Defs/TateResidueCurrency.lean` (the
    # shared row-3.3 API) and `Tate/CommFinite.lean` (the prelude substitutes). The
    # ten `scoped instance`s of the tail are checker-invisible and are landed for
    # elaboration only. Appended last.
    # --- P3.3d: the Tate trace compatibility. Imports `Tate/CommFinite.lean` (the
    # 3.3a prelude substitutes) and `LocalResidue/Instance.lean` (the canonical
    # local residue instance and `Place.uniformizer_mem`). Appended last.
    # --- P3.3c: the Tate agreement. Imports `Tate/CommFinite.lean` (the shared
    # finiteness chain), `Defs/TateResidueCurrency.lean` (the vocabulary),
    # `LocalResidue/Instance.lean` (the `Lg37` completion layer and `aCoeff`) and
    # `P1/DivPow.lean` (`kwHgfV352_localResidueCompletion_{spec,algebraMap}`). The five
    # `scoped instance`s are checker-invisible and are landed for elaboration only.
    # Appended last.
    # --- Refactor round (row 3.3 shared prelude): the 25 declarations that
    # `Tate/ChainRule.lean` (3.3b) and `Tate/TraceCompat.lean` (3.3d) had each
    # re-proved statement-identically are hoisted here, and the duplicate copies
    # are deleted from the two consumers. No new `SOURCES` entry: these rows are
    # already sourced by the `tateChainRule`/`tateTraceCompat` `S_` files above.
    # Appended last so no earlier last-name match can flip.
    # --- Refactor round (row 3.4): the P3.3 detector's "Agreement declares no
    # public overlap" was wrong — `Tate/Agreement.lean` still declared 22 public
    # copies colliding with `Prelude.lean` (4) and `TraceCompat.lean` (18), which
    # blocks any module importing Agreement together with ChainRule/TraceCompat
    # (exactly what 3.4 needs). The refactor imports both and deletes the 40
    # duplicate copies; the names are still supplied by `Prelude`/`TraceCompat`, so
    # the checker's identical count is unchanged. Appended last.
    # --- P3.2f: the atom-3 `P1Tower` tail, completed by the gated headline. The
    # `P1Tower` block is in `P1/DivPow.lean` above; this module adds the pin's
    # `P1Tower.trace_localResidue_finitePlace_div_pow_eq_zero` (S_ line 2016) and
    # the public wrapper at the `Thm_` binders (S_ lines 2140–2150). Its proof
    # consumes the surviving `AlgebraicCurve.residueTraceCompletionCommute` (the
    # `_v2` twin is dropped) and `completionTraceSum_of_isSeparable`; the private
    # `kwHgfV352_localResidueCompletion_{spec,algebraMap}₀` bridges restate the
    # DivPow copies about the public `Defs/TateResidueCurrency.lean` def. Appended
    # last so no earlier last-name match can flip.
    # --- `FLTForHuman/AlgebraicCurve/P1/DivPowEnding.lean` is handed over to `spec/check_port.py`: its `spec-pin:` wire
    # checks 2 ok / 0 mismatch / 0 missing. Do not re-list it here.
    # --- P3.2f/P3.2g: the perfect-field base case `residueTheorem_ratFunc_of_perfectField`.
    # The pin's 38-declaration tail (the `K →ₗ[K] K` residue functional, the
    # kernel/subrow assembly, the `MOne`/`MGeTwo` reduction and the perfect-field
    # specialisations) over the imported `P1/` engine. `P1PrincipalPartTwoPlaceCancelMOne`
    # is imported from `P1/TwoPlace.lean` and the p1-place twins are stated at the
    # pin's `placeInfty` and adapted from the port's `p1PlaceInfty`. Appended last.
    "FLTForHuman/AlgebraicCurve/P1/PerfectBase.lean",
    # --- P3.2 refactor round (R8): the InlineSpecific uniformizer chain hoisted out
    # of the three Tate modules into one public home. Its declarations are matched
    # against `Definitions/Def_DedekindDomain_AdicValuation_InlineSpecific.lean`
    # (registered above) and the `tate*`/`completionTraceSum` `S_` sources; the one
    # v4.34 adapter (`isUnit_adicCompletionIntegers_of_valued_eq_one`) stays
    # `private`. Appended last so no earlier last-name match can flip.
    "FLTForHuman/AlgebraicCurve/Place/Completion.lean",
    # --- P3.6 (row 6, the K ending) ---
    # The `RatFunc` headline (`KRatFunc.lean`), the Kähler-cotrace/fiber-localized
    # engine (`KCotrace.lean`) and the residue-theorem assembly + public headline
    # (`KFamily.lean`). Statements are the pin's; the wrapper headlines are verbatim
    # from their `Thm_` files. Appended last so no earlier last-name match can flip.
    # --- `FLTForHuman/AlgebraicCurve/ResidueTheorem/KRatFunc.lean` is handed over to `spec/check_port.py`: its `spec-pin:` wire
    # checks 1 ok / 0 mismatch / 0 missing. Do not re-list it here.
    # --- P3.7 (row 3.7, the RR assembly against the K ending) ---
    # `ResidueTheorem/RRAssembly.lean` (the K-route chain over the phase-1 engine
    # `Genus/Index.lean`/`Genus/Stichtenoth.lean`/`RiemannRoch/Assembly.lean`, the
    # `ModularCurve.p0n20_*`/`p0n25_wkc_*` assembly, the public headline, and the
    # bare-hypothesis wrapper `functionFieldRiemannRoch_of_isAlgClosed_of_transcendental`
    # landed 2026-10-23) has been handed over to `spec/check_port.py`: its seven pin
    # sources are named by `spec-pin:` lines in the module itself, and it checks
    # 42 ok / 0 mismatch / 0 missing / 0 own. Do not re-list it here.
    # --- P3.7b (the K-route general `ResidueTheorem`) ---
    # `ResidueTheorem/GeneralFromK.lean`: the bridge `residueTheorem_of_residueTheoremK`
    # and the algebraically-closed general headline `residueTheorem_of_isAlgClosed`.
    # Appended last so no earlier last-name match can flip.
    "FLTForHuman/AlgebraicCurve/ResidueTheorem/GeneralFromK.lean",
    # --- The degree-one place layer (`deg_eq_one_modularFunctionFieldBar`) ---
    # `AlgebraicCurve/Place/DegreeOne.lean` carries the generic
    # `isAlgebraic_adjoin_of_transcendental` node and the pin's `B2Deg`
    # `deg_eq_one_of_isAlgebraic_adjoin` (the pin declares the latter publicly in
    # its `S_` file, so it is matched there); `ModularCurve/Degree/PlaceDegree.lean`
    # carries the bar-field headline and the pin-private `finiteDimensional_adjoin_jBar`.
    # Appended last so no earlier last-name match can flip.
    "FLTForHuman/AlgebraicCurve/Place/DegreeOne.lean",
    "FLTForHuman/ModularCurve/Degree/PlaceDegree.lean",
    # --- (removed) X1's `FunctionField` vocabulary and the `jqModC` ratio ---
    # `FLTForHuman/ModularCurve/JqIntegralRatios.lean` used to sit here. It now
    # carries its own `spec-pin:` lines (the `Def_ModularCurve_X1` block, the
    # `jqModC` ratio `S_`/`Thm_` pair and the `E₄³/Δ` identity pair) and is
    # verified by `spec/check_port.py` — `23 ok / 0 mismatch / 0 missing`.
    # The bar-embedded `j(q)`'s transcendence (a leaf module: `PhiDegree` +
    # `LaurentGlue` + `QAdicPlace`). Appended last so no earlier match can flip.
    "FLTForHuman/ModularCurve/Degree/TranscendentalCoeffEmb.lean",
    # `IntegralWeightOneForm` (the pin's X1/Igusa vocabulary) and its existence.
    # Appended last so no earlier last-name match can flip.
    "FLTForHuman/ModularForms/WeightOne/IntegralWeightOneForm.lean",
    # The promoted rank-two charpoly conversion (a generic `LinearMap` lemma, so
    # it lives in `Algebra/`, not under a theory's `Defs/`). Appended last.
    "FLTForHuman/Algebra/CharpolyOfQuadratic.lean",
    # --- The characteristic-ℓ Frobenius q-expansion relation (charLFrobenius) ---
    # The generic perfect-field engine (`Algebra/` leaf, `IsCurveOver/` pair and
    # the Frobenius-subfield degree), the principal-divisor pair, the residue
    # field node, the `qExpFrobenius*` API and the target. Appended last.
    "FLTForHuman/Algebra/IsSeparableFrobenius.lean",
    "FLTForHuman/AlgebraicCurve/IsCurveOver/PerfectField.lean",
    # `IsCurveOver/Transcendental.lean` is now wired to `spec/check_port.py`
    # (three `spec-pin` pairs, W4 checkpoint A1), so it is released from this list.
    "FLTForHuman/AlgebraicCurve/PrincipalDivisors/IsSeparable.lean",
    "FLTForHuman/ModularCurve/Frobenius/QExpModL.lean",
    # --- Factorisable test functions on GL₂(𝔸_K) (AutomorphicForm) ---
    # The adele-ring topology/Haar layer (the former `AdelicHaar/Topology.lean` stub is
    # absorbed into the three D1 role modules), the level projections, the definitions,
    # and the headline. The pin `S_` helpers are `private` here, so only the
    # headline is diffed.
    "FLTForHuman/NumberTheory/AdelicHaar/Local.lean",
    "FLTForHuman/NumberTheory/AdelicHaar/Adele.lean",
    "FLTForHuman/NumberTheory/AdelicHaar/GeneralLinear.lean",
    "FLTForHuman/NumberTheory/AdelicLevel/Projections.lean",
    "FLTForHuman/NumberTheory/AdelicLevel/IdealBall.lean",
    "FLTForHuman/NumberTheory/AdelicLevel/Level.lean",
    "FLTForHuman/NumberTheory/AdelicLevel/HeckeGen.lean",
    "FLTForHuman/AutomorphicForm/Adelic/FactorizableTestFn.lean",
    "FLTForHuman/AutomorphicForm/Adelic/TestFnTop.lean",
    # The `K(x)` finite-extension `EssFiniteType` headline. Appended last.
    "FLTForHuman/AlgebraicCurve/IsCurveOver/EssFiniteType.lean",
    # --- Principal divisors on a Weierstrass curve (capstone route only) ---
    # Vocabulary + the two function-field prerequisites + the headline. The
    # deferred place/RR/class-group API is not declared here, so the checker does
    # not see it; that is intended until a consumer needs it. Appended last.
    "FLTForHuman/WeierstrassCurve/FunctionFieldQuadratic.lean",
    "FLTForHuman/WeierstrassCurve/FunctionFieldFinite.lean",
    "FLTForHuman/WeierstrassCurve/PrincipalDivisors.lean",
    # --- The ModularCurve.Period API and the equivariant-primitive headline ---
    # Vocabulary, the `Γ₀` period integral/lattice (`PeriodIntegral.lean`, only
    # the pin's `Period` section), the general `periodOf`/`periodMapOf` layer,
    # and the headline construction (pin helpers `private`). Appended last.
    "FLTForHuman/ModularForms/EichlerShimura/PeriodIntegral.lean",
    # --- SET-X1-A: the X₁ function-field/Jacobian vocabulary, the Hecke operator,
    # the diamond vocabulary and the `HeckeDiamondInputsAll` predicate. The pin's
    # `JOne.torsionGaloisRep{,_apply}`/`coe_torsionGaloisRep_apply` and
    # `X1/Diamond.lean` is now wired to `spec/check_port.py` (2026-10-27) by its own
    # `spec-pin:` block over `Def_ModularCurve_X1Diamond.lean`, `diamondOneBar{,_apply}`
    # included (14 ok / 0 mismatch / 0 missing). Handed over: do not re-list it.
    # `X1/Defs.lean` used to sit here; it is now wired by its own `spec-pin:`
    # header (2026-10-21), whose single pin source `Definitions/Def_ModularCurve_X1.lean`
    # covers the module's whole public surface.
    "FLTForHuman/ModularCurve/X1/HeckeOperator.lean",
    # --- SET-X1-B: the pin's `Integral` block and the two `JOneES` function-field
    # nodes. Every helper in the two `JOneES` modules is `private`, so the only
    # diffed declarations are the five `Integral` lemmas and the two headlines.
    # Appended last.
    # `X1/Integral.lean` used to sit here; it is now wired by its own `spec-pin:`
    # header (2026-10-21) and holds the pin's whole `Integral` block, `def` included.
    # `X1/FunctionField.lean` used to sit here; wired by its own `spec-pin:` header
    # (2026-10-21), with three `pin:` rows in `spec/decl_markers.tsv` for the pin
    # prelude it shares with two sibling `S_` files.
    "FLTForHuman/ModularCurve/X1/FunctionFieldBaseChange.lean",
    # --- SET-X1-C: the Hecke/diamond face. Every helper is `private`; the four
    # headlines are the only diffed declarations. Appended last.
    "FLTForHuman/ModularCurve/X1/QExpandStretch.lean",
    "FLTForHuman/ModularCurve/X1/DiamondAut.lean",
    "FLTForHuman/ModularCurve/X1/BaseChangeCover.lean",
    # --- SET-X1-C capstone (manager): the `X1HDIGeneric`/`X1HDIInputs` prelude is
    # entirely `private`; `ModularCurve.heckeDiamondInputsAll` is the sole public
    # declaration. Appended last.
    # --- SET-1 (the Vélu port). The general `Place` calculus, the Weierstrass
    # place dictionary, the Vélu vocabulary and the explicit-Vélu formulas.
    # Appended last so no earlier last-name match can flip.
    "FLTForHuman/AlgebraicCurve/Defs/PlaceCalculus.lean",
    "FLTForHuman/WeierstrassCurve/Place/Dictionary.lean",
    "FLTForHuman/WeierstrassCurve/Velu/Defs.lean",
    "FLTForHuman/WeierstrassCurve/Velu/Formula.lean",
    # --- SET-2 (the Vélu port): the cleared-polynomial degree engine (E) and the
    # generic point / translation / function-field layer (F). Its statements are
    # in the map `S_` file already in `SOURCES`; the res `S_` file supplies the
    # adapted proof bodies. Appended last so no earlier last-name match can flip.
    # --- SET-3 (the Vélu port): the deficit-fun `ord`/`evalAt` discharge (G) and
    # the odd-order summing-set combinatorics (H). Statements come from the map
    # `S_` file already in `SOURCES` (with the res `S_` file as the second copy).
    # Two declarations are already ported elsewhere and are imported, not
    # redeclared: `eq_algebraMap_of_forall_ord_nonneg` and `evalAt_inv`. The
    # `Prerequisites` section at the top of each module holds pin declarations
    # that G/H consume but that SET-1/SET-2 did not port; they are checked here
    # like any other declaration. The H5r refactor round moved the A1 place
    # dictionary out of these two modules into `Place/Dictionary.lean` (checked
    # there) and folded `exists_some_of_ne_zero` to `Velu/Formula.lean`.
    # Appended last so no earlier last-name match can flip.
    "FLTForHuman/WeierstrassCurve/Velu/Discharge.lean",
    # --- Capstone H3: the explicit-Vélu map equation. The general and plain
    # headlines (statements from the `Theorems/` wrappers, appended to `SOURCES`
    # above), the `VeluThmOneOddAt` carrier, its `kw_no6_hroute_*` discharge and
    # the `wqDiscPoly`/Galois/HasPrincipalDivisors dictionary block that supplies
    # it. Appended last so no earlier last-name match can flip.
    # --- Capstone H4: the explicit-Vélu `restrictAlong` engine. The two headline
    # theorems are blocked on unported upstream (see the module header); the 65
    # engine declarations whose types do not mention `placeOfPoint` /
    # `pointMapOfPushforward` / `GenusOnePlaceGate` / `AbelTheorem` /
    # `IsogenyEndDatum` are diffed here. Appended last so no earlier last-name
    # match can flip.
    # --- H5a: the Weierstrass genus-one place gate and the conditional-currency
    # isogeny dictionary (the two modules that unblock the H4 wire test). Appended
    # last so no earlier last-name match can flip.
    "FLTForHuman/WeierstrassCurve/GenusOnePlaceGate.lean",
    "FLTForHuman/WeierstrassCurve/Isogeny/ConditionalCurrency.lean",
    # --- H5b: the kernel-cardinality engine. The separable-along headline, its
    # three helper wrappers, and the verbatim `section Prerequisites` (the pin
    # `S_` chain for `natCard_ker_pointMapOfPushforward`). Appended last so no
    # earlier last-name match can flip.
    # --- H5 SET-1: the `AddMonoidHom.IsDualPair`/`AddMonoid.End.DualEndData`
    # algebra (mathlib-only) and the extracted `restrictAlong` place calculus.
    # Appended last so no earlier last-name match can flip.
    "FLTForHuman/WeierstrassCurve/Isogeny/DualAPI.lean",
    "FLTForHuman/AlgebraicCurve/Defs/RestrictAlongAPI.lean",
    # --- H5 SET-1: the shared `IsogenyEndDatum` engine (the declarations whose
    # names occur in both H5 `S_` files, plus the H5 `normFormulaAlong_of_elliptic`).
    # Appended last so no earlier last-name match can flip.
    # --- H5 SET-2: the `restrictAlong`-add column (the `addX_addY_specialize_at_place`
    # node, the res-only engine, the three `kw_hk5f_*_proved` producers and the
    # additivity headline). Appended last so no earlier last-name match can flip.
    # --- H5 SET-3: the dual-end-data column and the H5 vocabulary tail (the two
    # headline modules of the home). Appended last so no earlier last-name match
    # can flip.
    # --- The torsion-API promotion (H5 follow-up): the `Mathlib`-only `A[n] ≅ (Z/n)²`
    # classification and the elliptic char-free torsion theory. Appended last.
    "FLTForHuman/Algebra/ZModTorsion.lean",
    "FLTForHuman/Elliptic/TorsionZMod.lean",
    # --- V1 SET-1 (the Vélu port): the order-two quotient column. The two new
    # modules are leaves (they import only `Velu/Defs.lean`), so no set cascades.
    # `OrderTwo.lean` carries the pin's `Def_..._VeluOrderTwo` /
    # `Def_..._VeluPointMap2` vocabulary and the twelve headline nodes;
    # `OrderTwoMap.lean` carries `exists_addMonoidHom_coe_eq_veluPointMap2` and
    # its proof-local (private) helpers. The vocabulary statements diff against
    # the two `Definitions/` files and `Δ_mul_j` against
    # `Def_..._VeluQuotientJInvariant`, all appended to `SOURCES` just above.
    # Appended last so no earlier last-name match can flip.
    "FLTForHuman/WeierstrassCurve/Velu/OrderTwo.lean",
    # --- V1 SET-2 (the Vélu port): the discriminant identity of the odd-order
    # quotient. `Equivariance.lean` is the variable-change/base-change definition
    # layer — the pin's `Def_..._VeluVariableChange` whole, the
    # `Def_..._VeluEquivariance` `map_velu*`/`map_veluQuotient` block, and the
    # `Def_..._VariableChangePointEquiv` core (a strict prerequisite of the first,
    # and absent from the port when this set was dispatched; SET-3's
    # `VariableChangePoint.lean` order is amended to import it rather than
    # redeclare it). `Discriminant.lean` is the identity, its nonvanishing
    # corollary, and `isOddVeluSet_oddOrderSummingSet` (the port's own proof
    # through the promoted `Velu/OddOrder.lean` lemma). `CyclicCount.lean` is the
    # ψ-counting pair and the cyclic-kernel enumeration. Every proof-local helper
    # is `private`. Appended last so no earlier last-name match can flip.
    "FLTForHuman/WeierstrassCurve/Velu/Equivariance.lean",
    "FLTForHuman/WeierstrassCurve/Velu/Discriminant.lean",
    "FLTForHuman/WeierstrassCurve/Velu/CyclicCount.lean",
    # --- V1 SET-3 (the Vélu port): the quotient-`j` column. `VariableChangePoint.lean`
    # carries the one off-subject prerequisite `WeierstrassCurve.Affine.Point.vcInvFun_add`
    # (its statement is the `Theorems/` wrapper, appended to `SOURCES` above; its
    # proof-local helpers are `private`). `CyclicQuotientJ.lean` carries the pin's
    # `Def_..._CyclicQuotientJ` vocabulary and the two headline nodes
    # `cyclicQuotientJ_variableChange_eq` / `cyclicQuotientJ_baseChange_map_eq_of_isAlgClosed`
    # (their statements are the two `Theorems/` wrappers, also above) with every
    # `P2MKcCQJvc`/`P2MKcCQJbc` helper `private`. Both are leaves importing
    # SET-2's `Velu/Equivariance.lean` and the already-public `Velu/Formula.lean`
    # `map_velu*` block, so no set cascades. Appended last so no earlier last-name
    # match can flip.
    "FLTForHuman/WeierstrassCurve/Velu/VariableChangePoint.lean",
    "FLTForHuman/WeierstrassCurve/Velu/CyclicQuotientJ.lean",
    # --- The genus-one place-gate silo: the RR space + infinite place
    # (`RRSpace.lean`), the geometric point↔place bijection (`GeometricPlace.lean`),
    # the generic Dedekind count bridge (`PrincipalDivisors/Count.lean`), the
    # unit-ideal/class-group/Abel block (`Place/UnitIdeal.lean`) and the capstone
    # (`GenusOnePlaceGateCentred.lean`).
    "FLTForHuman/WeierstrassCurve/Place/RRSpace.lean",
    "FLTForHuman/WeierstrassCurve/Place/GeometricPlace.lean",
    "FLTForHuman/AlgebraicCurve/PrincipalDivisors/Count.lean",
    "FLTForHuman/WeierstrassCurve/Place/UnitIdeal.lean",
    "FLTForHuman/WeierstrassCurve/GenusOnePlaceGateCentred.lean",
    # --- V2 SET-1 (the two Mazur gateways). Four leaves: the shared coordinate-ring
    # pair (`Place/CoordinateRingDedekind.lean`), the two light torsion aliases
    # (`Elliptic/TorsionCardLight.lean`), gateway 1 plus its pin helper surface
    # (`IsogenyEndDatum/PointEndSubring.lean`, now wired by its own `spec-pin:`
    # header and no longer listed here) and gateway 2, the `Ws13S7` prelude and
    # the number-theoretic headline (`IsogenyEndDatum/CharPolySquare.lean`). Each
    # imports only downward, so no set cascades. `Elliptic/TorsionCard.lean` itself is
    # *not* in `PORT_FILES` (it is the `card_torsion_of_isAlgClosed` home); only its
    # two SET-1 aliases are diffed against the two `Theorems/` wrappers appended above.
    # Appended last so no earlier last-name match can flip.
    "FLTForHuman/WeierstrassCurve/Place/CoordinateRingDedekind.lean",
    "FLTForHuman/Elliptic/TorsionCardLight.lean",
    "FLTForHuman/WeierstrassCurve/IsogenyEndDatum/CharPolySquare.lean",
    # --- V2 SET-2 (the Ribet-side completion). Five leaves: the generic
    # separable-coprime lemma (`FieldTheory/SeparableOfCoprime.lean`), the `ratFunc`
    # principal-divisors alias (`AlgebraicCurve/PrincipalDivisors/SeparableRatFunc.lean`),
    # the characteristic-free function-field pair
    # (`WeierstrassCurve/PrincipalDivisorsSeparable.lean`), the point-map
    # surjectivity wrapper (`WeierstrassCurve/Isogeny/PointMapSurjective.lean`) and the
    # two odd-order headlines (`WeierstrassCurve/Velu/PointMapOddOrder.lean`). Each
    # imports only downward, so no set cascades. `Velu/RestrictAlong.lean` is already
    # in `PORT_FILES`, so its two promoted declarations are picked up without a wiring
    # change; the two new `Theorems/` wrapper entries above are what lets the checker
    # diff them. Appended last so no earlier last-name match can flip.
    "FLTForHuman/FieldTheory/SeparableOfCoprime.lean",
    "FLTForHuman/AlgebraicCurve/PrincipalDivisors/SeparableRatFunc.lean",
    "FLTForHuman/WeierstrassCurve/PrincipalDivisorsSeparable.lean",
    "FLTForHuman/WeierstrassCurve/Isogeny/PointMapSurjective.lean",
    # --- V3: the translation automorphism of `W.FunctionField` by a point and its
    # action on the places. The two headlines are the only public declarations, so
    # only they are diffed; every helper (the taylor block, the single
    # `ord_ofHeightOneSpectrum_algebraMap_eq_zero` leaf and the whole `kw_*` chain)
    # is `private`. It imports `IsogenyEndDatum/DualEndData.lean`, whose cone supplies
    # `Engine`, `Velu/Engine` and `Place/Dictionary`. Appended last.
    # --- P-SET-1: the `PeriodPair` uniformization core (new-file-only). `Basic.lean` is
    # the dictionary at the pin's `PeriodPair.*` names; `Discriminant.lean` carries the
    # discriminant headline plus the public `kw_`-stripped promotions the `j`-line set
    # shares (`riemannZeta_six`, `G_ofTau_eq`, `g₂_ofTau`, `g₃_ofTau`) and the public
    # scale/lattice-equality API (`G_scale`, `g₂_scale`, `g₃_scale`, `scale_lattice`,
    # `scaleLatticeEquiv`, `G_eq_of_lattice_eq`, `g₂_eq_of_lattice_eq`,
    # `g₃_eq_of_lattice_eq`); its remaining helpers are `private`. `Uniformization.lean`
    # carries the uniformization headline and every helper is `private`, so it
    # contributes exactly one compared declaration. `Uniformization.lean` imports `Basic`
    # and `Discriminant` (the latter by the module DAG; the proof of
    # `isUniformization_toPoint` uses its own `h` and does not cite `discriminant_ne_zero`).
    #
    # P-1b moved the shared scale/lattice prelude out of `Discriminant.lean` into
    # `Lattice.lean` and promoted the `WeightOne`/`FrickeFunction` private copies to it;
    # `Discriminant.lean` now imports `Lattice`. The pin sources are the ones already
    # listed above (the `S_PeriodPair_discriminant_ne_zero` and
    # `S_WLight_frickeFunction_modularity_package` files carry every moved name), so
    # `SOURCES` is unchanged.
    "FLTForHuman/Elliptic/PeriodPair/Basic.lean",
    # `Lattice.lean`, `Discriminant.lean` and `Uniformization.lean` migrated to the
    # `spec-pin:` protocol on 2026-10-23 (WORKORDER-V6's promotion pass): each now carries a
    # header wire and `spec/check_port.py` owns it, so none of the three is exempt here.
    # `Basic.lean` is still on the frozen checker.
    # --- P-SET-2: the `PeriodPair` `j`-line. Two modules. `ModularForms/JInvariant.lean`
    # is the neutral home of the generic level-one `j`-invariant and its surjectivity
    # (`ModularForm.j` / `ModularForm.j_surjective`), promoted out of the weight-one
    # package namespace `WLight`: both are level-one modular-form mathematics, not
    # `WLight` API, and `LevelField.lean` now keeps the pin's `WLight.j` /
    # `WLight.j_surjective` as one-line shims over them (same names, same statements,
    # so the weight-one consumers are untouched). `Elliptic/PeriodPair/JLine.lean`
    # carries the two pin headlines `PeriodPair.jLattice_ofTau` /
    # `PeriodPair.jLattice_surjective` plus the `kw_`-stripped
    # `PeriodPair.jLattice_ofTau_eq`; every other helper is `private`. It imports
    # `ModularForms/JInvariant.lean` upward (a leaf: diamond, not cycle) and only
    # downward otherwise, so no set cascades. Appended last so no earlier last-name
    # match can flip.
    "FLTForHuman/ModularForms/JInvariant.lean",
    "FLTForHuman/Elliptic/PeriodPair/JLine.lean",
    # --- D-1: the shared base-change prelude. Appended last so no earlier last-name
    # match can flip.
    # --- D-2: the countable function-field descent (set D-2 of
    # `topics/velu/WORKORDER-P2-basechange.md`; order
    # `topics/velu/WORKORDER-P2b-intermediate-field.md`). Its public surface is the
    # pin's self-contained descent predicates at their pin names plus the headline
    # (which resolves against the `Theorems/` wrapper in `SOURCES`); the descent
    # helpers are `private` with their `kw_` prefix stripped, so the checker does not
    # read them — except the ones set D-6 promoted for the two-curve descent
    # (`iA_crCoeffsIn`, `iA_phi`, `iA_ffDescend_exists`, `iCa_ffNum`, `iCa_ffDen`,
    # `iCa_ffCoeffSet`, `iCa_crCoeffsIn_of_ffCoeffSet_subset`,
    # `iPFA_finiteDimensional_adjoin_transcendental`, `iPFE_functionField_ringHom_ext`,
    # `iotaSubd_countable_of_fg`), which the checker now reads and verifies through the
    # `stripped_source` fallback. Appended last so no earlier last-name match can flip.
    # --- D-3: the two mid-size base-change nodes of
    # `topics/velu/WORKORDER-P2c-basechange-alghom-and-variablechange.md`.
    # `BaseChangeAlgHom.lean` is the `bcff` headline; everything else the pin's `S_` file
    # carries was already landed by D-1, at D-1's prefix-stripped names, so the module has
    # exactly one public declaration. `VariableChangeAlgEquiv.lean` is the `varCh` node:
    # the `mrtw60a*` block at its pin names (it is pin-public and its prefix is a
    # solution-file token, not a `kw_` promotion) plus the headline. Both import D-1
    # downward and are leaves. Appended last so no earlier last-name match can flip.
    "FLTForHuman/WeierstrassCurve/Isogeny/BaseChangeAlgHom.lean",
    "FLTForHuman/WeierstrassCurve/Isogeny/VariableChangeAlgEquiv.lean",
    # --- D-4: the conjugation headline plus the seam (`KernelCyclicTransfer.lean`).
    # The module's whole surface is public at the pin names: the headline (matched against
    # its wrapper), the `kw_fdn2_qephod_hend21_*` conjugation block, the
    # `KwD5BetweenCurvesPMOPConjKerEquiv` `Prop`, the `kw_surgehgf4_pck_*` engine and
    # `pck_s17`; there are no `private` helpers. It imports D-1 downward and the
    # `IsogenyEndDatum/Engine.lean` cone (which the pin's own `S_` file needs), and it is a
    # leaf. Appended last so no earlier last-name match can flip.
    # --- D-5: the two `IsAddCyclic`-kernel base-change silos in **one** home
    # (`KernelBaseChange.lean`, `topics/velu/WORKORDER-P2e-kernel-base-change.md`). The
    # two pin `S_` files are 5,357 / 5,338 lines and share 163 of their 176 declarations
    # (4,926 removable lines); the module declares the shared new surface once (the three
    # `KwD5BetweenCurves*` seams, the `kw_surge_hgf4_bc*`/`χE`/`pmop_naturality`/`hBC_proved`
    # tensor transport and the `kw_surgehgf4_hfgkd_ktd_*` kernel-transport block) and the
    # two headlines at the `Theorems/` wrappers' statements. Everything else the pin
    # re-proves is imported from D-1/D-4 and the `Place`/`IsogenyEndDatum`/`PeriodPair`
    # homes; `ModularCurve.kw_fdn2_qephod_hend7_pmopKerCard_proved` is deliberately **not**
    # re-declared (the name owns a differently stated `Prop` in `Isogeny/NatCard.lean`), and
    # the pin's `solution` rows are superseded by the two headlines. It imports D-4 and the
    # `IsogenyEndDatum/Engine.lean` cone and is a leaf. Appended last so no earlier
    # last-name match can flip.
    # --- D-6: the two-curve countable descent and its headline. Public surface: the
    # pin's `iotaDescent{Curve_map_FF,Phi,Phi_equation,Phi_transcendental,Phi_X,Phi_yGen}`
    # at the prefix-stripped names (verified through the §2.1 `stripped_source`
    # fallback), the port-own `ModularCurve.exists_twoCurveDescent` (`OWN_PROOFS`), and
    # the headline (matched against its wrapper in `SOURCES`). Everything else — the
    # gate-free `NoAC` base-change engine and the descent helpers — is `private` with a
    # content name. Appended last so no earlier last-name match can flip.
    # `WeierstrassCurve/Isogeny/TwoCurveDescent.lean` used to sit here; wired by its own
    # `spec-pin:` header (2026-10-21) in the build-time round that removed the two
    # `set_option maxHeartbeats` overrides it had been hiding behind.
    # --- S-1: the `ℂ`-analytic seam (`topics/velu/WORKORDER-S1-analytic-seam.md`). Public
    # surface: the four pin-public chain `Prop`s, the nine `kw_surgehgf4_hH2*` chain lemmas
    # at their pin names, the three `kw_surgehgf4_hH2f_geomMorphBC*` atoms, the two
    # `kw_fdn2_qephod_hend10_*` finite-kernel lemmas, the pin-public
    # `WeierstrassCurve.Affine.kw_evalAt_placeOfEquation_mk`, and the headline (matched
    # against its `Theorems/` wrapper in `SOURCES`). `ModularCurve.KwD5BetweenCurvesHoloLift`
    # is **imported**, never redeclared: the module proves it. Everything else — the
    # covering-map layer, `countable_toPointHom_preimage`, the ℘-differentiability of
    # `evalEval` and the `surjective_toPointHom` bridge — is `private` with a content name,
    # as the pin has them. The `kw_fdn2_qephod_hend7_geomMorphBC*` block is the ported
    # `Isogeny/NatCard.lean` generalisation, not re-declared. Appended last so no earlier
    # last-name match can flip.
    # --- S-2: the lattice/index arithmetic (`topics/velu/WORKORDER-S2-lattice-index.md`).
    # Public surface: the two headlines (matched against their `Theorems/` wrappers in
    # `SOURCES`), the three `ModularCurve` classes, the shared `hID_*` block written once,
    # the shared torsion prelude written once, the `kqe_*` engine, and the pin-public
    # `kwLatticeCoeAddEquiv`/`kw_card_torsionBy_zlatticeQuotient*`/`kwSublatticeIndex_scale`/
    # `kw_scale_lattice_toAddSubgroup`/`kw_surgehgf4_hID_betweenCurvesIndexDual_proved`/
    # `kw_surgehgf4_kqe_proved`/`kw_surgehgf4_hscd_pointHomSublatticeCyc_of_three`.
    # Everything else (the `mem_scale_lattice_iff`/Liouville layer,
    # `exists_smul_mem_and_apply_eq_of_forall_sub_mem`, `toPoint_add_mem`, `infinite_point`)
    # is `private` with a content name. The pin's inlined uniformization prelude,
    # `MilneI72IntersectionData` and the `*_axiomAnchor` stubs are not transcribed. Appended
    # last so no earlier last-name match can flip.
    # --- S-3: the primitive-coset / `jLattice` column
    # (`topics/velu/WORKORDER-S3-primcoset-jlattice.md`). Two modules: the generic
    # mathlib-only `ℤ²`-lattice invariants (`IntPairSubgroup`, re-homed from the pin's
    # `QuaternionAlgebra` scaffolding) appended first, then the `PeriodPair` transport.
    # Public surface: the headline (matched against its `Theorems/` wrapper in `SOURCES`),
    # the `:449–600` transport block, the `hu5c` product-cyclicity/coprimality criterion,
    # the `KwSublatticeQuotientZZTransport` class and the `qtzz_*` block, and the generic
    # block in `(a)`. `ModularCurve.kw_scale_lattice_toAddSubgroup`/`kwSublatticeIndex_scale`
    # are **imported** from S-2's `LatticeIndex.lean`, never redeclared. The pin-private
    # prelude helpers (`mem_scale_lattice_iff`, `im_div_ne_zero`, `span_neg_fst`,
    # `ofTau_latticeEquivProd_symm_apply`, `g₂_cubed_scale`, `jLattice_scale`) are re-derived
    # `private`; the pin's `p2m_*` scaffolding and the `qtzz_axiomAnchor : True` stub are not
    # transcribed. Appended last so no earlier last-name match can flip.
    "FLTForHuman/Algebra/IntPairSubgroup.lean",
    # --- S-4: the `E₄³ − E₆²` / `jLattice` modular-polynomial tail
    # (`topics/velu/WORKORDER-S4-e4cube-jlattice.md`). Two new leaves:
    # `Algebra/SpecialLinearGroupSmith.lean` (the mathlib-only `SL₂(ℤ)` Smith
    # diagonalisation at the pin's `Matrix.SpecialLinearGroup.PrimitiveSmith`
    # namespace) and `ModularCurve/ModularPolynomialE4Cube.lean` (the three
    # `ModularCurve.ModularPolynomialData` headlines, the `E₄³`/`Δ` forms and the
    # `q`-expansion bookkeeping in `ModularCurve.DeepCosetAux`, plus `jt` and the
    # `upperTriangularGL` pair in `ModularCurve.CosetRootAux`). The pin-public
    # helpers are kept at their pin names, so the four `S_` files are in `SOURCES`;
    # everything the pin declares `private` is not transcribed. `exists_degeneracy_Gamma0`
    # is **imported** from `ModularForms/Level/Degeneracy.lean` (ported there for
    # this set), as are `heckeDiagMatrix`/`coe_heckeDiagMatrix_smul`,
    # `upperTriangularGL`/`val_upperTriangularGL`, `jqModC_eq_qExpansion_E4_cube_div_discriminant`,
    # `mem_primCosetReps`, `PeriodPair.jLattice_ofTau` and S-3's headline. Appended
    # last so no earlier last-name match can flip.
    "FLTForHuman/Algebra/SpecialLinearGroupSmith.lean",
    "FLTForHuman/ModularCurve/ModularPolynomialE4Cube.lean",
    # --- SC: row S's terminal set (`topics/velu/WORKORDER-SC-capstone.md`). The two
    # leaves first, then the capstone (appended last, as the work order requires).
    # Public surface: the `variableChange` leaf's headline, the field-embedding leaf's
    # `Field.nonempty_ringHom_complex_of_countable`, and the capstone's wrapper headline
    # plus the pin's `conjSeam*` / char-`0` bridges / `map_eval_map_Φ` / `isElliptic_map`
    # / `j_eq_div` / `jLattice_eq_j` / `complexCase` / `solution0` / `solution`. The
    # pin's `PeriodPair` scale prelude is imported (S-3's modules), not re-declared;
    # `jLattice_scale` is re-derived `private`, so this checker cannot see it. Appended
    # last so no earlier last-name match can flip.
    "FLTForHuman/Elliptic/PeriodPair/VariableChange.lean",
    "FLTForHuman/FieldTheory/NonemptyRingHomComplex.lean",
    # `ModularPolynomialEvalJ.lean` migrated to the `spec-pin:` protocol on 2026-10-23
    # (WORKORDER-V6 follow-up): it carries a header wire and the new checker owns it.
    # --- ds-head (`topics/riemannRoch/WORKORDER-ds-head.md`): the three new leaf
    # modules. `Differential/Hurwitz.lean` writes the pin's duplicated pair once
    # (engine + both headlines); `Differential/Generation.lean` and `Genus/RatFunc.lean`
    # are thin wrappers over the already-ported `s12`/`ℙ¹` surface. Appended last so
    # no earlier last-name match can flip.
    "FLTForHuman/AlgebraicCurve/Differential/Hurwitz.lean",
    # --- `FLTForHuman/AlgebraicCurve/Differential/Coefficient.lean` (until
    # 2026-10-25 `Differential/Generation.lean`) is handed over to
    # `spec/check_port.py` (2026-10-24, when the `diffCoeff` layer was absorbed into
    # it): its `spec-pin:` wire checks 8 ok / 0 mismatch / 0 missing / 1 own. Do not
    # re-list it here. The absorption and the rename are
    # `topics/algebraicCurve/TOPIC-diffCoeff-integrality.md` §10.
    # --- `FLTForHuman/AlgebraicCurve/Genus/RatFunc.lean` is handed over to `spec/check_port.py`: its `spec-pin:` wire
    # checks 7 ok / 0 mismatch / 0 missing. Do not re-list it here.
    # --- SET-H-A (`topics/hecke/TOPIC-xH-hecke-diamond-inputs.md`): the `X_H(M)`
    # definition layer. The pin's `Groups` block is the ported `CohCarrier` Γ_H
    # vocabulary; these three modules are the `FunctionField`/`Bar` block, the
    # `α`/`β` Hecke degeneracy maps with `HeckeInputsHAlong`, and the diamond
    # predicate `IsDiamondAutHBar` with `HeckeDiamondInputsHAll`. The pin's
    # off-cone Jacobian blocks (`JH`, `heckeOperatorHAlong`, `genOpH`,
    # `diamondHBar`) are deliberately absent; the checker iterates `PORT_FILES`,
    # so they cannot report `missing`. Appended last so no earlier last-name match
    # can flip.
    "FLTForHuman/ModularCurve/XH/Operators.lean",
    # --- SET-H-B (`topics/hecke/SET-H-B.md`): the diamond-lift pair, written once.
    # The general-`Γ` engine shared by the two headlines, then the two level
    # specialisations with their headlines. Appended last so no earlier last-name
    # match can flip.
    "FLTForHuman/ModularCurve/XH/DiamondLiftPrelude.lean",
    "FLTForHuman/ModularCurve/XH/DiamondLift.lean",
    "FLTForHuman/ModularCurve/X1/DiamondLift.lean",
    # --- SET-H-C (`topics/hecke/SET-H-C.md`): the seven inputs
    # `ModularCurve.heckeInputsHAlong`, the public `S_` file transcribed at its own
    # names plus the wrapper's headline. Appended last so no earlier last-name
    # match can flip.
    "FLTForHuman/ModularCurve/XH/HeckeInputs.lean",
    # --- SET-H-C capstone (manager): the whole module is `private` except
    # `ModularCurve.heckeDiamondInputsHAll` (matched against its wrapper in
    # `SOURCES`), so this is the effort's final wire test. Appended last.
    "FLTForHuman/ModularCurve/XH/Inputs.lean",
    # --- SET-R-A (`topics/functionFieldGeneration/SET-R-A.md`): the
    # Gamma0-rationality pair's shared engine written once, plus the two
    # headlines, which are matched against their `Theorems/` wrappers appended to
    # `SOURCES` last. Appended last so no earlier last-name match can flip.
    # --- SET-R-B (`topics/functionFieldGeneration/SET-R-B.md`): the `X_H`
    # relative-degree headline and its engine, matched against the `S_` file and
    # `Theorems/` wrapper appended to `SOURCES` last. Appended last so no earlier
    # last-name match can flip.
    "FLTForHuman/ModularCurve/XH/Relrank.lean",
    # --- SET-R-C order 1 (`topics/functionFieldGeneration/SET-R-C.md`): the
    # `JOneES` finrank/index bound over the promoted `X1/FunctionField.lean`
    # engine, matched against the `S_` file and the `Theorems/` wrapper appended
    # to `SOURCES` last. Appended last so no earlier last-name match can flip.
    # --- `FLTForHuman/ModularCurve/X1/FunctionFieldDegree.lean` is handed over to
    # `spec/check_port.py` (2026-10-25, when its `hvmap` `simp only` was repaired and its
    # three file-wide linter suppressions were narrowed): its own `spec-pin:` wire checks
    # 36 ok / 0 mismatch / 0 missing. The proof broke on 2026-10-21 when a57f777 added the
    # general `ModularCurve.coeffEmb_intSeriesC` to `JqIntegralRatios.lean`: the proof's
    # *unqualified* name had been reaching the `open`ed `.map` copy in `X1/FunctionField.lean`
    # and began resolving to the enclosing namespace's general lemma instead (repaired
    # 2026-10-25 by unfolding `intSeriesC`; the `.map` copy is kept — it has a consumer).
    # Do not re-list it here.
    # --- SET-R-C order 2 (`topics/functionFieldGeneration/SET-R-C.md`): the
    # residue-field model, matched against target 5's `S_` file and `Theorems/`
    # wrapper appended to `SOURCES` last. Appended last so no earlier last-name
    # match can flip.
    # --- SET-R-D order 1 (`topics/functionFieldGeneration/SET-R-D.md`): Deuring's
    # degree inequality over a valuation subring, matched against its `Theorems/`
    # wrapper appended to `SOURCES` last. The engine stays `private`, so the
    # headline is the module's only compared declaration. Appended last so no
    # earlier last-name match can flip.
    "FLTForHuman/ModularCurve/Defs/QExpValuationReduction.lean",
    # --- SET-R-D order 2 (`topics/functionFieldGeneration/SET-R-D.md`): finiteness
    # of the `q`-expansion function field over `K(j)` for algebraically closed `K`,
    # matched against target's `S_` file and `Theorems/` wrapper appended to
    # `SOURCES` last. Appended last so no earlier last-name match can flip.
    # --- SET-R-D order 3 (`topics/functionFieldGeneration/SET-R-D.md`): the
    # Atkin–Lehner / diamond slash integrality; its pin `S_` file is already in
    # `SOURCES`, and the headline is matched against its `Theorems/` wrapper
    # appended last. The twenty already-public prelude declarations are imported,
    # not re-declared. Appended last so no earlier last-name match can flip.
    "FLTForHuman/ModularCurve/X1/IsIntegralAtkinLehner.lean",
    # --- SET-R-E order 1 (`topics/functionFieldGeneration/SET-R-E.md`): the
    # `isAlgClosed` finrank/index bound, matched against its `S_` file and
    # `Theorems/` wrapper appended to `SOURCES` last. The SET-R-D engine block is
    # imported from `FunctionFieldIsAlgClosed.lean`, not re-declared. Appended last
    # so no earlier last-name match can flip.
    "FLTForHuman/ModularCurve/X1/FunctionFieldFinrankIsAlgClosed.lean",
    # --- SET-R-E order 2 (`topics/functionFieldGeneration/SET-R-E.md`): the two
    # Atkin–Lehner exchanges. The `H`-independent engine lines are written once in
    # the module's `ModularCurve.A2K1A` namespace (or imported from
    # `X1/IsIntegralAtkinLehner.lean` / the `JOneES.JOneESRat` block); the
    # `Γt`/`Γb`-dependent lines appear once per target in `…A2K1A.Hecke` and
    # `…A2K1A.X1x0`, and the two headlines are matched against their `Theorems/`
    # wrappers appended to `SOURCES` last. Appended last so no earlier last-name
    # match can flip.
    "FLTForHuman/ModularCurve/X1/AtkinLehnerExchange.lean",
    # --- WORKORDER-W1 order 1 (`topics/deligneSerre/WORKORDER-W1-automorphisms.md`):
    # the shared point-transport prelude of the exceptional-automorphism set, the
    # 11 declarations both story-A `S_` files repeat byte-identically. Appended last
    # so no earlier last-name match can flip.
    "FLTForHuman/WeierstrassCurve/Automorphism/Basic.lean",
    # --- WORKORDER-W1 order 2 (`topics/deligneSerre/WORKORDER-W1-automorphisms.md`):
    # the char-2 exceptional automorphisms; only the headline is public, matched
    # against its `Theorems/` wrapper appended to `SOURCES` above. Appended last so
    # no earlier last-name match can flip.
    "FLTForHuman/WeierstrassCurve/Automorphism/CharTwo.lean",
    # --- WORKORDER-W1 order 3 (`topics/deligneSerre/WORKORDER-W1-automorphisms.md`):
    # the char-3 exceptional automorphisms; only the headline is public, matched
    # against its `Theorems/` wrapper appended to `SOURCES` above. Appended last so
    # no earlier last-name match can flip.
    "FLTForHuman/WeierstrassCurve/Automorphism/CharThree.lean",
    # --- WORKORDER-W2 order 1 (`topics/deligneSerre/WORKORDER-W2-division-fields.md`):
    # the count-`N²` structure theorem; only the headline is public, matched against
    # its `Theorems/` wrapper appended to `SOURCES` above. Appended last so no earlier
    # last-name match can flip.
    "FLTForHuman/WeierstrassCurve/Torsion/NatCardStructure.lean",
    # --- WORKORDER-W2 order 2 (`topics/deligneSerre/WORKORDER-W2-division-fields.md`):
    # the `n`-division field; only the headline is public, matched against its
    # `Theorems/` wrapper appended to `SOURCES` above. Appended last so no earlier
    # last-name match can flip.
    "FLTForHuman/WeierstrassCurve/Torsion/DivisionField.lean",
    # --- WORKORDER-W3 (`topics/deligneSerre/WORKORDER-W3-stepcurve.md`): the odd
    # prime-degree step of the abscissa-indexed Vélu construction; only the headline
    # is public, matched against its `Theorems/` wrapper appended to `SOURCES` above.
    # Appended last so no earlier last-name match can flip.
    "FLTForHuman/WeierstrassCurve/Velu/StepCurveSubgroup.lean",
    # --- WORKORDER-W4 (`topics/deligneSerre/WORKORDER-W4-definition-wave.md`), stage 1:
    # the reduction-point definition layer. Its pin source
    # `Definitions/Def_WeierstrassCurve_ReductionMap.lean` is already in `SOURCES` from the
    # earlier `ValuationSubring` promotion, so no new source row is needed; the four
    # `ValuationSubring` tool rows of the same pin file are appended to
    # `FLTForHuman/NumberTheory/ValuationAtPlace.lean`, which is already in `PORT_FILES`.
    # Appended last so no earlier last-name match can flip.
    "FLTForHuman/WeierstrassCurve/Reduction/Point.lean",
    # --- WORKORDER-W3b (`topics/deligneSerre/WORKORDER-W3b-zmultiples.md`): equal
    # Vélu-quotient `j` forces equal cyclic subgroups; only the headline is public,
    # matched against its `Theorems/` wrapper appended to `SOURCES` above. Appended
    # last so no earlier last-name match can flip.
    # --- WORKORDER-W4 stage 2 (`topics/deligneSerre/WORKORDER-W4-definition-wave.md`):
    # the whole pin `Def_WeierstrassCurve_TorsionIntegral.lean`, matched against the pin
    # definition file appended to `SOURCES` above. Appended last so no earlier last-name
    # match can flip.
    "FLTForHuman/WeierstrassCurve/Reduction/TorsionIntegral.lean",
    # --- WORKORDER-W4 stage 3: the whole pin `Def_WeierstrassCurve_ReduceHom.lean`,
    # matched against the pin definition file appended to `SOURCES` above. Appended last
    # so no earlier last-name match can flip.
    "FLTForHuman/WeierstrassCurve/Reduction/ReduceHom.lean",
    # --- WORKORDER-W4 stage 4: the whole pin `Def_WeierstrassCurve_ZeroComponentReduction.lean`,
    # matched against the pin definition file appended to `SOURCES` above. Appended last so no
    # earlier last-name match can flip.
    "FLTForHuman/WeierstrassCurve/Reduction/ZeroComponent.lean",
    # --- WORKORDER-W5 (set C1): the headline `exists_reduceHom_eq_of_nsmul_eq_zero_of_natCast_ne_zero`
    # is the module's only public declaration, matched against its `Theorems/` wrapper appended to
    # `SOURCES` above. Appended last so no earlier last-name match can flip.
    "FLTForHuman/WeierstrassCurve/Reduction/ReduceHomSurjective.lean",
    # --- WORKORDER-W6 (set C2): the headline
    # `exists_inertia_equivariant_reduction_of_variableChange_eq_map` is the module's only
    # public declaration, matched against its `Theorems/` wrapper appended to `SOURCES` above.
    # Appended last so no earlier last-name match can flip.
    "FLTForHuman/WeierstrassCurve/Reduction/InertiaReduction.lean",
    # --- WORKORDER-D1 (`topics/modularCurve/WORKORDER-D1-petersson.md`) phase 1: the four
    # pin `Def_AutomorphicForm_*` modules ported whole, matched against the pin definition
    # files appended to `SOURCES` above. Appended last so no earlier last-name match can flip.
    "FLTForHuman/AutomorphicForm/UpperHalfPlane/HyperbolicMeasure.lean",
    "FLTForHuman/AutomorphicForm/UpperHalfPlane/FundamentalDomainVolume.lean",
    "FLTForHuman/AutomorphicForm/UpperHalfPlane/SiegelSetCover.lean",
    "FLTForHuman/AutomorphicForm/UpperHalfPlane/Gamma0FundamentalSet.lean",
    # --- WORKORDER-D1 phase 2: the Petersson pairing pair. The shared Riesz-representation
    # prelude is written once, `private`; the two headlines are matched against their
    # `Theorems/` wrappers appended to `SOURCES` above. Appended last so no earlier last-name
    # match can flip.
    "FLTForHuman/ModularCurve/Analytic/PeterssonPairing.lean",
    # --- WORKORDER-D2 (`topics/modularCurve/WORKORDER-D2-period-map.md`): the period-map
    # modules, matched against their `Theorems/` wrappers appended to `SOURCES` above.
    "FLTForHuman/ModularCurve/Period/PeriodLatticeBoundary.lean",
    "FLTForHuman/ModularCurve/Period/QExpansionDerivative.lean",
    # --- WORKORDER-D2, node completion (whole-node rule, playbook §2.3): the remainder of
    # `Def_ModularCurve_QExpansionDiff.lean` — its `QExpansionDiff` and `TraceDiff` halves —
    # in their own subject modules. The pin definition file is in `SOURCES` above.
    "FLTForHuman/ModularCurve/Period/QExpansionDiff.lean",
    "FLTForHuman/AlgebraicCurve/Differential/TraceDiff.lean",
    # --- WORKORDER-C2 phase 1: the pin definition layer ported whole, matched against the pin
    # definition files appended to `SOURCES` above. `PushPull.lean` is the manager-authorised
    # fourth module; `SL2Elementary`/`HeckeDifferential` are the pin's own modules; and
    # `X0/FunctionFieldFull.lean` is `Def_ModularCurve_X0ModL.lean` (its two Frobenius-layer
    # declarations `coeffMap_ofPowerSeries`/`qExpandAlgHomC` are dedup'd to `Frobenius/Defs.lean`,
    # which already records them as taken from this pin module). Appended last so no earlier
    # last-name match can flip.
    "FLTForHuman/AlgebraicCurve/Differential/PushPull.lean",
    "FLTForHuman/ModularCurve/Defs/SL2Elementary.lean",
    "FLTForHuman/ModularCurve/Defs/HeckeDifferential.lean",
    # --- WORKORDER-C2 phase 2: the ten landed leaf headlines. Only the headline(s) of each
    # module are public; the `S_`-local helpers are transcribed `private` and so are skipped by
    # the checker. `IntegralityJqNModC.lean` carries 3 of the 4 rows of its group (the 4th,
    # `exists_sum_smul_eq_of_isIntegralQExp_gamma1`, is the deferred node documented in `SOURCES`
    # above and in that module's docstring). Appended last so no earlier last-name match can flip.
    "FLTForHuman/ModularCurve/X1/QExpansionDiv.lean",
    # `X1/Structure.lean` is handed over to `spec/check_port.py` (2026-10-27, SET MC-3):
    # its four `spec-pin:` wires check 4 ok / 0 / 0. Do not re-list it here.
    # --- WORKORDER-B1: the modular polynomial `Φ_N` (subject B's five ready rows). One module
    # per story: the leading coefficient, the uniqueness/irreducibility/symmetry trio, and the
    # star action. Only the headline(s) of each are public; the pin's helpers are re-derived
    # `private`, so the checker sees exactly five new declarations. Appended last.
    # `ModularPolynomialLeadingCoeff.lean` is **handed over (2026-10-23)**: it carries
    # `spec-pin:` for its wrapper and `spec/check_port.py` owns it, so it is no longer
    # listed here.
    # --- `FLTForHuman/ModularCurve/ModularPolynomialUniquenessIrreducible.lean` is handed
    # over to `spec/check_port.py` (2026-10-25, when `phiIrreducible_all` landed and the
    # engine `toAdjoin_eq_minpoly_all` was promoted): its `spec-pin:` wire checks 5 ok / 0
    # mismatch / 0 missing / 0 own. Do not re-list it here.
    # --- `FLTForHuman/ModularCurve/ModularPolynomialStarBank.lean` is handed over to
    # `spec/check_port.py` (2026-10-25, same round: it took a `spec-pin:` wire for its
    # wrapper and `S_` file and lost its `private` copies of the `coeff_jqModC_*` trio):
    # it checks 1 ok / 0 mismatch / 0 missing. Do not re-list it here.
    # --- Manager wave of 2026-10-09: the definition layer of subject A and subject B2.
    # `LevelN/FunctionField.lean` is the pin's `Def_ModularCurve_LevelNFunctionField.lean`
    # whole (`wp`, `fricke`, `jAnalytic`, `generators`, `ring`, `jGen` and the membership
    # lemmas); `Defs/ClassicalModularPolynomials.lean` is `phiTwo`/`phiThree`/`intFibre`;
    # `Defs/FibrePoly.lean` is `fibrePoly` — which was `private` in `Degree/PhiData.lean`
    # and is now public at the pin's name there, with `PhiData` importing it (dedup) —
    # together with its three theorems and the `ReduceModBivar` block. It is **handed
    # over (2026-10-23)**: it now carries `spec-pin:` for the pin definition file, the
    # `ReduceModBivar` block and the three promoted `*_fibrePoly` theorem wrappers, and
    # `spec/check_port.py` owns it, so it is no longer listed here.
    "FLTForHuman/ModularCurve/LevelN/FunctionField.lean",
    "FLTForHuman/ModularCurve/Defs/ClassicalModularPolynomials.lean",
    # --- WORKORDER-B2: the `N = 2` fibre row of subject B. One public headline
    # (`ModularCurve.fibrePoly_phiTwo_j_eq_prod_veluQuotient2_j`); the pin silo's other six
    # declarations are `S_`-local and re-derived `private`, so the checker sees exactly one new
    # declaration. Appended last.
    "FLTForHuman/ModularCurve/ModularPolynomialFibreTwo.lean",
    # --- WORKORDER-A (`topics/modularCurve/WORKORDER-A-levelN-field.md`): the
    # level-`N` function field of `X(N)`. `Prelude.lean` is the one home of the
    # shared blocks (written once, public, at the pin's names and statements);
    # `FieldGalois.lean` and `Places.lean` are phase A1's and phase A2's four
    # headlines each, with their `S_`-local helpers `private`. Appended last so no
    # earlier last-name match can flip.
    "FLTForHuman/ModularCurve/LevelN/Prelude.lean",
    # The Weil-pairing entry points: the needed `Def_EllipticCurve_FunctionFieldPullback`
    # slice (`PointPlace`), the `weilPairing0` construction, and the six-law
    # `IsWeilPairing` interface.
    "FLTForHuman/WeierstrassCurve/Place/PointPlace.lean",
    "FLTForHuman/WeierstrassCurve/WeilPairingFun.lean",
    "FLTForHuman/WeierstrassCurve/WeilPairing.lean",
    # The next node on the shelf: the `[n]`-fibre finiteness (and the shared
    # `torsion_finite`/`card_torsion_toFinset` promotion).
    "FLTForHuman/WeierstrassCurve/FibSetFinite.lean",
    # WORKORDER-E: the level-`N` `q`-expansion bridge, the deduped twin development.
    "FLTForHuman/ModularCurve/LevelN/QExpBridge.lean",
    # WORKORDER-S8: the Γ₁/Nebentypus pair. The promoted `dd`/Γ₁ API lives in
    # `HeckeEigenNebentypus.lean` (already listed); each of these two modules exposes
    # exactly its one wrapper headline, so the delta is +2.
    # --- PORTING-AutomorphicForm D0 (`topics/PORTING-AutomorphicForm.md`): the
    # mathlib-only leaves. `Adelic/Basic` and `Adelic/LsXi` split the pin's
    # `Def_AutomorphicForm_AdelicLsXi`. Appended last.
    "FLTForHuman/RepTheory/ContinuousSMulDiscrete.lean",
    "FLTForHuman/AutomorphicForm/Adelic/Basic.lean",
    "FLTForHuman/AutomorphicForm/Adelic/LsXi.lean",
    "FLTForHuman/AutomorphicForm/Adelic/ConstantTerm.lean",
    # --- PORTING-AutomorphicForm D2: smooth vectors. Appended last.
    "FLTForHuman/RepTheory/SmoothVectors.lean",
    # --- PORTING-AutomorphicForm D4: carrier pins and right convolution. Appended last.
    "FLTForHuman/AutomorphicForm/Adelic/CarrierPins.lean",
    "FLTForHuman/AutomorphicForm/Adelic/RightConvolution.lean",
    # --- PORTING-AutomorphicForm D5: automorphic / smooth automorphic functions. Appended last.
    "FLTForHuman/AutomorphicForm/Adelic/AutomorphicFn.lean",
    "FLTForHuman/AutomorphicForm/Adelic/SmoothAutomorphicFn.lean",
    # --- PORTING-AutomorphicForm D6: windowed Siegel set and row isometries. Appended last.
    "FLTForHuman/AutomorphicForm/Adelic/WindowedSiegel/Set.lean",
    "FLTForHuman/AutomorphicForm/Adelic/WindowedSiegel/RowIsometry.lean",
    # --- PORTING-AutomorphicForm D7: archimedean inclusion and types. Appended last.
    "FLTForHuman/AutomorphicForm/Adelic/ArchType.lean",
    # --- PORTING-AutomorphicForm H1: the public shared `isFactorizableTestFn` prelude home.
    "FLTForHuman/AutomorphicForm/Adelic/TestFnNearIdentity.lean",
    # --- PORTING-AutomorphicForm T1: the levelOne and principalLevel headlines.
    "FLTForHuman/NumberTheory/AdelicLevel/PrincipalLevel.lean",
    "FLTForHuman/AutomorphicForm/Adelic/RightConvNeZero.lean",
    "FLTForHuman/AutomorphicForm/Adelic/RightConvNeZeroPrincipal.lean",
    # --- PORTING-AutomorphicForm: the arch-weight-character def layer (groundwork for the
    # `hasArchCharacterAt` headline, which needs its own `ArchProfile`-parameterised prelude).
    "FLTForHuman/AutomorphicForm/Adelic/ArchWeightChar.lean",
    "FLTForHuman/AutomorphicForm/Adelic/ArchWeightCharTransport.lean",
    # --- PORTING-AutomorphicForm T1: the arch-character headline and its measure input.
    "FLTForHuman/NumberTheory/AdelicHaar/MulRightInvariant.lean",
    "FLTForHuman/AutomorphicForm/Adelic/RightConvNeZeroArch.lean",
    # --- TOPIC-rightConv-comm W1: the adèlic box (and the pin home of
    # `continuous_ringEquiv_mixedSpace`, promoted out of `TestFnNearIdentity`).
    "FLTForHuman/NumberTheory/AdelicBox.lean",
    # --- TOPIC-rightConv-comm W2: the adèlic centre and the projective quotient.
    "FLTForHuman/NumberTheory/AdelicCentre.lean",
    # --- TOPIC-rightConv-comm W3: the generic measure-theoretic decay engines, homed
    # under `MeasureTheory/` rather than `AutomorphicForm/` (playbook §3.1).
    "FLTForHuman/MeasureTheory/ContractionDecay.lean",
    "FLTForHuman/MeasureTheory/ScalingDichotomy.lean",
    # --- TOPIC-rightConv-comm W4: the windowed-Siegel topology and coordinates, beside
    # the landed `WindowedSiegel/{Set,RowIsometry}.lean`.
    "FLTForHuman/AutomorphicForm/Adelic/WindowedSiegel/Topology.lean",
    "FLTForHuman/AutomorphicForm/Adelic/WindowedSiegel/Coordinates.lean",
    # --- TOPIC-rightConv-comm W5: the Hecke/local vocabulary, cut by mathematical role — the
    # generic Hecke operator and the local congruence subgroups under `RepTheory/`, the
    # eigensystem under `AutomorphicForm/Adelic/`, the idèle-class vocabulary under
    # `NumberTheory/NumberField/IdeleClass/`.
    "FLTForHuman/RepTheory/AbstractHeckeOperator.lean",
    "FLTForHuman/AutomorphicForm/Adelic/HeckeEigensystem.lean",
    "FLTForHuman/RepTheory/LocalNewvector/CongruenceSubgroupK1.lean",
    "FLTForHuman/NumberTheory/NumberField/IdeleClass/Vocab.lean",
    # --- TOPIC-rightConv-comm W6: the residue of the mathlib-gap stubs, homed in a
    # mathlib-mirroring tree. `Def_Mathlib_Topology_Algebra_Group_Units` is fully
    # substituted by mathlib `Submonoid.isOpen_units` and has no port module.
    "FLTForHuman/Order/Filter/Cofinite.lean",
    "FLTForHuman/Topology/Bases.lean",
    "FLTForHuman/Topology/Algebra/Module/Quotient.lean",
    "FLTForHuman/Topology/Algebra/ContinuousMonoidHom.lean",
    "FLTForHuman/Topology/Algebra/RestrictedProduct/Basic.lean",
    "FLTForHuman/Topology/Algebra/RestrictedProduct/Equiv.lean",
    "FLTForHuman/Topology/Algebra/RestrictedProduct/TopologicalSpace.lean",
    # --- TOPIC-rightConv-comm W7+ (the definition gate proper), ready set.
    "FLTForHuman/RepTheory/LocalLanglands/HeckePair.lean",
    "FLTForHuman/NumberTheory/AdelicDock/LocalEmbedding.lean",
    "FLTForHuman/NumberTheory/AdelicVolume.lean",
    "FLTForHuman/AutomorphicForm/Adelic/Siegel/Reduction.lean",
    "FLTForHuman/AutomorphicForm/Adelic/SigmaAdelicAction.lean",
    "FLTForHuman/AutomorphicForm/Adelic/HeckeEigensystemMap.lean",
    "FLTForHuman/AutomorphicForm/Adelic/WindowedSiegel/CentreCutSet.lean",
    "FLTForHuman/AutomorphicForm/Adelic/Cusp/SmoothRealization.lean",
    "FLTForHuman/AutomorphicForm/Adelic/Siegel/Covering.lean",
    "FLTForHuman/NumberTheory/SiegelVolume.lean",
    "FLTForHuman/AutomorphicForm/Adelic/ProductionPins.lean",
    "FLTForHuman/AutomorphicForm/Adelic/Cusp/ArithRealization.lean",
    "FLTForHuman/AutomorphicForm/Adelic/ProductionPinsCompact.lean",
    "FLTForHuman/AutomorphicForm/Adelic/ProductionPinsGeneral.lean",
    "FLTForHuman/AutomorphicForm/Adelic/IsotypicCuspSpace.lean",
    "FLTForHuman/AutomorphicForm/Adelic/Cusp/Constituent.lean",
    "FLTForHuman/AutomorphicForm/Adelic/ArchSpherical.lean",
    # --- WORKORDER-P-rightConv-comm P1
    # (`topics/automorphicForm/WORKORDER-P-rightConv-comm.md`): the four generic engine modules
    # of the right-convolution commutation proof, written once from the shared block of the
    # three `S_` silos (all `private` at the pin, hence `promoted`). The pin proof silos and the
    # `Theorems/` wrappers are appended to `SOURCES` above. Appended last so no earlier last-name
    # match can flip.
    "FLTForHuman/RepTheory/TypeSpan.lean",
    "FLTForHuman/RepTheory/AntiInvolutionHaar.lean",
    "FLTForHuman/RepTheory/ProjectedHaar.lean",
    "FLTForHuman/RepTheory/BiIsotypic.lean",
    # --- P2/P3 (`topics/automorphicForm/WORKORDER-P-rightConv-comm.md`, round 2): the
    # adèlic instantiation of the P1 engine and the three headlines. The pin's three
    # silos and wrappers are already in `SOURCES` above. `Frame` is the adèlic
    # `ProjectedHaar` frame and `MeasureGlue`; `PlaceClassData` the place-class datum and
    # `thetaArch`; `SliceCentrality` the slice centrality engine at the general-`U`
    # spelling; `MeasureAssembly` the archimedean projection measure and the level-`N`
    # side facts. The three headlines are matched against their `Theorems/` wrappers (so
    # `identical`, not `promoted`). Appended last so no earlier last-name match can flip.
    "FLTForHuman/AutomorphicForm/Adelic/RightConvComm/Frame.lean",
    "FLTForHuman/AutomorphicForm/Adelic/RightConvComm/PlaceClassData.lean",
    "FLTForHuman/AutomorphicForm/Adelic/RightConvComm/SliceCentrality.lean",
    "FLTForHuman/AutomorphicForm/Adelic/RightConvComm/MeasureAssembly.lean",
    "FLTForHuman/AutomorphicForm/Adelic/RightConvComm/Compact.lean",
    "FLTForHuman/AutomorphicForm/Adelic/RightConvComm/Level.lean",
    "FLTForHuman/AutomorphicForm/Adelic/RightConvComm/Principal.lean",
    # MIGRATED 2026-10-27 (SET 4 homing): the linear-independence pair now carries its own
    # `spec-pin:` wire (both `Theorems/` wrappers, both `S_` copies, and the separable-adjoin
    # node, which moved here from `IsCurveOver/Transcendental.lean` because the constant field
    # extension is this module's subject). `spec/check_port.py` owns it at 26 ok / 0 mismatch /
    # 0 missing. Its `SOURCES` entries stay: other listed modules still match against the two
    # linear-independence `S_` files. Do not re-list it here.
    # --- WORKORDER Z1: the completed Dedekind zeta façade, the topic's only checked
    # module. It declares exactly one declaration — the consumed headline
    # `NumberField.exists_completedDedekindZeta_package`, stated from the pin wrapper
    # and proved by `…/CompletedDedekindZeta/Bounds.lean`. The nine development modules
    # of the topic stay unlisted (tier 3); `spec/UNWIRED-PUBLIC.md` lists what they hold.
    "FLTForHuman/NumberTheory/NumberField/CompletedDedekindZeta.lean",
    # --- WORKORDER T1: the TateGlobal analytic core façade, the topic's only checked
    # module. It declares exactly the three consumed headlines
    # `NumberField.TateGlobal.zetaIntegral_mul_eulerFactors_eq`,
    # `NumberField.TateGlobal.integrable_zetaIntegrand` and
    # `NumberField.TateGlobal.exists_forall_zetaIntegral_mul_eulerFactors_eq_of_eq_indicator`,
    # each stated from its pin wrapper and proved by the corresponding cap module
    # (`…/TateGlobal/EulerFactors.lean`, `…/IntegrableZetaIntegrand.lean`,
    # `…/IndicatorEulerFactors.lean`). The twenty development modules of the topic stay
    # unlisted (tier 3). Appended last so no earlier last-name match can flip.
    "FLTForHuman/NumberTheory/NumberField/TateGlobal.lean",
    # --- WORKORDER-Q turn 2: MIGRATED 2026-10-25. The archimedean approximate-identity
    # façade and its four development modules now carry their own `spec-pin:` wires
    # (`AutomorphicForm/Adelic/ArchApproxIdentity.lean`,
    # `…/ArchApproxIdentity/{Instantiate,ArchInfra,EntryBall}.lean`,
    # `RepTheory/{TypeReproducer,ConvolutionLimit}.lean`), so the frozen checker gives up
    # the façade and the new checker owns the lot. Nothing from this topic is listed here.
    # --- WORKORDER-R turn 2 (`topics/automorphicForm/WORKORDER-R-bruhat-transversal.md`):
    # the Bruhat-transversal / Weyl-integrand façade, the topic's only checked module. It
    # declares exactly the three headlines
    # `AutomorphicForm.bruhatTransversal_summand_norm_summable_of_re_gt_half`,
    # `AutomorphicForm.continuous_bruhatTransversal_tsum_of_re_gt_half` and
    # `AutomorphicForm.weylIntertwiningIntegrand_integrable_of_re_gt_half`, each stated
    # from its pin wrapper and proved by the corresponding cap in
    # `…/WeylIntegrable/Caps.lean` (the shared `…_impl` lives in `…/WeylIntegrable/Assembly.lean`).
    # The four development modules stay unlisted (tier 3). Appended last so no earlier
    # last-name match can flip.
    "FLTForHuman/AutomorphicForm/Adelic/WeylIntegrable.lean",
    # --- The ModularCurve weight-4 Tate-slot cluster, definition layer (see SOURCES).
    # Two new leaf modules; no existing module was edited, so no hub wave is owed.
    "FLTForHuman/ModularCurve/Defs/TateFormal.lean",
    "FLTForHuman/ModularCurve/Defs/TateSlots.lean",
    # --- WORKORDER-F1: the weight-4 Tate-slot tier-1 façade. The engine modules
    # (`TateSlots/Convergence.lean`, `TateSlots/SlotCoeff.lean`) stay tier 3 and
    # are recorded in spec/UNWIRED-PUBLIC.md; only the façade
    # (`TateSlots/CoefficientFormulas.lean`) was diffed; it is handed over to
    # `spec/check_port.py` (2026-10-27, SET MC-2): its fourteen `spec-pin:` wires check
    # 14 ok / 0 / 0. Do not re-list it here.
    # --- WORKORDER-F2: the `tateCurve` twins/triplet definition layer (see SOURCES).
    # Six new leaf modules; no existing module was edited, so no hub wave is owed.
    "FLTForHuman/Algebra/LaurentSeriesXAdic.lean",
    "FLTForHuman/TateCurve/QSeries.lean",
    "FLTForHuman/TateCurve/PointSeries.lean",
    "FLTForHuman/ModularForms/KatzLevelOne.lean",
    "FLTForHuman/ModularCurve/Defs/KatzLevelP.lean",
    "FLTForHuman/ModularCurve/Defs/KatzLevelPCusps.lean",
    # --- WORKORDER-F2: the `tateCurve` twin/triplet tier-1 façade. The engine
    # (`TateCurve/Bridge.lean`, `TateCurve/NonToricSlot.lean`) stays tier 3 and is
    # recorded in spec/UNWIRED-PUBLIC.md; only the façade (`TateCurve/QPow.lean`) is
    # diffed.
    "FLTForHuman/ModularCurve/TateCurve/QPow.lean",
    # --- the `continuous_ideleNorm` thin tier-1 façade. It declares exactly the two
    # consumed headlines `NumberField.TateGlobal.continuous_ideleNorm` and
    # `NumberField.TateGlobal.continuous_ideleNorm_det`, each stated from its pin wrapper
    # (`Theorems/Thm_NumberField_TateGlobal_continuous_ideleNorm*.lean`) and proved by
    # the shared `FujisakiC3` engine. The engine
    # (`FLTForHuman/NumberTheory/NumberField/TateGlobal/FujisakiC3.lean`) stays tier 3 and
    # is recorded in spec/UNWIRED-PUBLIC.md. Appended last so no earlier last-name match
    # can flip.
    "FLTForHuman/NumberTheory/NumberField/TateGlobalContinuousIdeleNorm.lean",
    # --- TOPIC-adelic-modulus definition gate: `Def_NumberField_AdelicHeight` homed
    # whole at `NumberTheory/AdelicHeight.lean` (see SOURCES). One new leaf module; no
    # existing module was edited, so no hub wave is owed. Appended last so no earlier
    # last-name match can flip.
    "FLTForHuman/NumberTheory/AdelicHeight.lean",
    # --- WORKORDER-T2: the `GL₂` idele-norm slab headlines (see SOURCES). Two public
    # statements from their pin wrappers; no engine module, no promotion, no existing
    # module edited. Appended last so no earlier last-name match can flip.
    "FLTForHuman/NumberTheory/NumberField/TateGlobalIdeleNormDet.lean",
    # --- TOPIC-adelic-modulus: the façade (see SOURCES). It declares the four
    # principal-idele product-formula headlines from their pin wrappers and proves them by
    # `NumberTheory/AdelicHaar/ProductFormula.lean` (tier 3). The two modulus headlines
    # (WORKORDER-A1) land into this same module. Appended last so no earlier last-name
    # match can flip.
    "FLTForHuman/NumberTheory/AdelicModulus.lean",
    # --- TOPIC-compactness-twins definition gate: the adic-completion integrality
    # instances (see SOURCES). One already-homed leaf module, promoted from tier 3 to
    # tier 1 because the Fujisaki compactness pair consumes
    # `isCompactAdicCompletionIntegers`. No existing module was edited.
    "FLTForHuman/NumberTheory/NumberField/Completion/Finite.lean",
    # --- TOPIC-compactness-twins, WORKORDER-T3: the two Fujisaki compactness headlines
    # (see SOURCES). They read the public kernels `M4aLocalCFT.FujisakiR1.exists_isCompact_impl`
    # and `M4aLocalCFT.FujisakiC2c.compactSpace_normOneIdeleClass_impl` of the tier-3 engine
    # `…/TateGlobal/FujisakiCompact.lean`. No existing module was edited.
    "FLTForHuman/NumberTheory/NumberField/TateGlobalCompactness.lean",
    "FLTForHuman/RingTheory/DiscreteValuationRing/Order.lean",
    # --- The `AutomorphicForm.LocalIntertwining` prelude and its unramified headline, set LI-1
    # (topics/automorphicForm/WORKORDER-LI1-weyl-unramified.md; see SOURCES). `WeylPrelude` is
    # the manager's Set-0 definition layer (the pin's `ValuationOrd` block and the shell API the
    # T1 port did not need), `WeylShell` the residual prelude, `WeylUnramified` the headline.
    # No existing module was edited.
    "FLTForHuman/NumberTheory/NumberField/TateGlobal/WeylPrelude.lean",
    "FLTForHuman/NumberTheory/NumberField/TateGlobal/WeylShell.lean",
    "FLTForHuman/NumberTheory/NumberField/TateGlobal/WeylUnramified.lean",
    # Set LI-2: the smooth headline and its private development (see SOURCES).
    "FLTForHuman/NumberTheory/NumberField/TateGlobal/WeylSmooth.lean",
    # --- TOPIC-iwasawa-analytic-core definition gate (see SOURCES): the pin's complex Iwasawa
    # vocabulary homed whole, and the shared generic Fourier-decay block. Both are manager-owned
    # leaves; the complex/real engine modules of the two waves stay tier 3. Appended last so no
    # earlier last-name match can flip.
    "FLTForHuman/AutomorphicForm/Iwasawa/Complex/Basic.lean",
    "FLTForHuman/MeasureTheory/FourierDecay.lean",
    # --- WORKORDER-I3 (the real Iwasawa engine; see SOURCES): the four public real-place headlines,
    # proved by the tier-3 `AutomorphicForm.RealIwasawa.Engine.*` kernels of
    # `…/Iwasawa/Real/{Core,Decay,Continuation}.lean`. Appended last so no earlier last-name match
    # can flip.
    "FLTForHuman/AutomorphicForm/Iwasawa/Real/Estimates.lean",
    # --- WORKORDER-I1/I2 (the complex Iwasawa engine; see SOURCES): the nine public complex-place
    # headlines, proved by the tier-3 `AutomorphicForm.ComplexIwasawa.Engine.*` kernels of
    # `…/Iwasawa/Complex/{Core,Decay,UniformDecay,Continuation}.lean`. Appended last so no earlier
    # last-name match can flip.
    "FLTForHuman/AutomorphicForm/Iwasawa/Complex/Estimates.lean",
    # --- The adelic Siegel-covering definition layer (`topics/PORTING-DeligneSerre.md` §4(a)):
    # the pin `Def_AutomorphicForm_CentreCutSiegelSetAmple.lean` ported whole at the natural
    # theory home beside `CentreCutSet.lean`. A leaf (no dependents). Appended last so no
    # earlier last-name match can flip.
    "FLTForHuman/AutomorphicForm/Adelic/WindowedSiegel/CentreCutSiegelSetAmple.lean",
    # --- The archimedean-norm block of the Fujisaki-compactness prelude, homed by subject:
    # the pin `S_NumberField_TateGlobal_exists_isCompact_subset_normOneIdeles_forall_mem_exists_eq_map_algebraMap_mul.lean`
    # carries `ideleNorm_archCentralUnit` / `ideleNorm_archUnitHom` / `exists_norm_pow_mult_eq`
    # `private`, re-copied into 21 / 35 / 13 pin `S_` files, so they are public mathematics.
    # Their pin source is already listed above; this module is the diffed home and
    # `TateGlobal/FujisakiCompact.lean` now imports them. Appended last so no earlier
    # last-name match can flip.
    "FLTForHuman/NumberTheory/NumberField/TateGlobal/ArchNorm.lean",
    # --- WORKORDER-SC1 (`topics/automorphicForm/WORKORDER-SC1-slab-covering.md`): the tier-1
    # façade stating the three slab-covering headlines and delegating to the tier-3
    # `AutomorphicForm.SiegelCovering.Engine` kernels of `Siegel/SlabCovering.lean` (unlisted).
    # Appended last so no earlier last-name match can flip.
    "FLTForHuman/AutomorphicForm/Adelic/Siegel/SlabCoveringTheorems.lean",
    # --- Landau's theorem for L-series (`topics/numberTheory/WORKORDER-LS1-landau.md`): the
    # `P2M_Landau` section of the pin `S_LSeries_abscissaOfAbsConv_lt_of_differentiableOn_ball`
    # plus its headline wrapper. The rest of that `S_` file (the Landau–Siegel silo) is dropped.
    # Appended last so no earlier last-name match can flip.
    "FLTForHuman/NumberTheory/LSeries/Landau.lean",
    # --- The manager's ground for the weighted-Petersson node (sesqForm): the homed
    # `Def_AutomorphicForm_PeterssonIntegral` and the promoted public node
    # `AutomorphicForm.ideleNorm_det_globalPoints` (the slab engine now imports the latter).
    # Appended last so no earlier last-name match can flip.
    "FLTForHuman/AutomorphicForm/Adelic/PeterssonIntegral.lean",
    "FLTForHuman/AutomorphicForm/Adelic/IdeleNormDet.lean",
    # --- WORKORDER-SC2 (§5): the weighted-Petersson module, listed. It states the headline from
    # the pin `Theorems/` wrapper and exposes the engine `AutomorphicForm.PeterssonSlabPairing.main`
    # (the pin's private `main`); the checker verifies both. Appended last.
    "FLTForHuman/AutomorphicForm/Adelic/PeterssonSlabPairing.lean",
    # --- WORKORDER-SC3: the listed determinant-norm slab fundamental-domain module (headline +
    # private prelude, the two countability substitutions imported). Appended last.
    "FLTForHuman/AutomorphicForm/Adelic/DetNormSlabFundamentalDomain.lean",
    # --- WORKORDER-SC4 pre-wave: the archimedean-`K`-finiteness definition module (9 public
    # declarations, homed whole beside the `ArchType` vocabulary it depends on). Appended last.
    "FLTForHuman/AutomorphicForm/Adelic/ArchKFinite.lean",
    # --- WORKORDER-SC4: the listed `IsInducedSection` pair module (both headlines plus the
    # pin-public helper surface, the 4 modulus-prelude rows imported). Appended last.
    "FLTForHuman/AutomorphicForm/Adelic/InducedSectionFlat.lean",
    # --- WORKORDER-P1 (`topics/algebraicCurve/WORKORDER-P1-isPrimeOverValuationSubring.md`): the place realising a prime over a valuation subring; every declaration but the headline is `private`, so the checker sees only the headline. Appended last.
    "FLTForHuman/AlgebraicCurve/Place/IsPrimeOverValuationSubring.lean",
    # --- The `AlgebraicCurve.CellDissection.*`/`RadialRegion.*` cluster pre-wave: the two
    # definition modules homed whole (tier 1, beside the other `Defs/` modules). Appended
    # last so no earlier last-name match can flip.
    "FLTForHuman/AlgebraicCurve/Defs/ComplexLineIntegral.lean",
    "FLTForHuman/AlgebraicCurve/Defs/CellDissection.lean",
    # --- WORKORDER-R1 (`topics/algebraicCurve/WORKORDER-R1-radial-rectangle.md`): the two
    # radial-rectangle façades only (their tier-3 engines stay unlisted, registered in
    # `spec/UNWIRED-PUBLIC.md`). Appended last.
    "FLTForHuman/AlgebraicCurve/RadialRegion/RectSixArcs.lean",
    "FLTForHuman/AlgebraicCurve/RadialRegion/RefineExact.lean",
    # --- WORKORDER-R2 (`topics/algebraicCurve/WORKORDER-R2-window-perimeter.md`): the window-perimeter façade only (its tier-3 engine stays unlisted, registered in `spec/UNWIRED-PUBLIC.md`). Appended last.
    "FLTForHuman/AlgebraicCurve/RadialRegion/WindowPerimeter.lean",
    # --- WORKORDER-R3a (`topics/algebraicCurve/WORKORDER-R3a-reparam-twin.md`): the two reparametrisation
    # façades only (the single shared tier-3 engine `Engine/Reparam.lean` stays unlisted, registered in
    # `spec/UNWIRED-PUBLIC.md`). Appended last.
    "FLTForHuman/AlgebraicCurve/RadialRegion/ReparamAcrossEdge.lean",
    "FLTForHuman/AlgebraicCurve/RadialRegion/ReparamSameSide.lean",
    # --- WORKORDER-R3b (`topics/algebraicCurve/WORKORDER-R3b-grid-geometry.md`): the grid-geometry
    # façade only (its tier-3 engine `Engine/GridGeometry.lean` stays unlisted, registered in
    # `spec/UNWIRED-PUBLIC.md`). Appended last.
    "FLTForHuman/AlgebraicCurve/RadialRegion/GridGeometry.lean",
    # --- WORKORDER-R4 (`topics/algebraicCurve/WORKORDER-R4-radial-miscellany.md`): the three radial
    # miscellany façades only (their tier-3 engines
    # `Engine/{IsOpenStarConvex,Recip,PowPullback}.lean` stay unlisted, registered in
    # `spec/UNWIRED-PUBLIC.md`). Appended last.
    "FLTForHuman/AlgebraicCurve/RadialRegion/IsOpenStarConvex.lean",
    "FLTForHuman/AlgebraicCurve/RadialRegion/Recip.lean",
    "FLTForHuman/AlgebraicCurve/RadialRegion/PowPullbackLaps.lean",
    # --- WORKORDER-KF1 (`topics/automorphicForm/WORKORDER-KF1-kfinite-family-span.md`): the
    # façade only (its tier-3 engines `RepTheory/TranslateSpan.lean` and
    # `AutomorphicForm/Adelic/ArchKFiniteFamily.lean` stay unlisted, registered in
    # `spec/UNWIRED-PUBLIC.md`). Appended last.
    "FLTForHuman/AutomorphicForm/Adelic/ArchKFiniteFamilyTheorems.lean",
    # --- WORKORDER-TO4 (`topics/automorphicForm/WORKORDER-TO4-unit-factorizable-trio.md`): the
    # façade only (its tier-3 engine `AutomorphicForm/Adelic/UnitFactorizableEngine.lean` stays
    # unlisted, registered in `spec/UNWIRED-PUBLIC.md`). Appended last.
    "FLTForHuman/AutomorphicForm/Adelic/UnitFactorizableTheorems.lean",
    # --- The `CohCarrier` Hecke–diamond triplet's definition layer
    # (`topics/deligneSerre/TOPIC-cohcarrier-comm-triplet.md` §4–§6): the two pin
    # `Definitions/` modules homed whole. This ground is shared by all twelve needed
    # `CohCarrier` nodes, not only the triplet. Appended last so no earlier last-name
    # match can flip.
    "FLTForHuman/ModularForms/Defs/CohCarrierLevel.lean",
    "FLTForHuman/ModularForms/Defs/CohCarrierLower.lean",
    # --- WORKORDER-CT1's triplet has been handed over to `spec/check_port.py`: its
    # three `Theorems/` wrappers are named by `spec-pin:` lines in
    # `FLTForHuman/ModularForms/CohCarrier/CommTriplet.lean`, and its tier-3 engine
    # (`.../Engine/CommTriplet.lean`) stays unlisted, registered in
    # `spec/UNWIRED-PUBLIC.md`. Do not re-list it here.
    # --- The Petersson definition layer (`peterssonOn`) and the fundamental-domain
    # ground (`goodSet`, the translate-double-counting identities). Both are transcribed
    # verbatim and wired so they stay verified; the deferred exact-volume/L2 surface is in
    # CARRY-FORWARD.md. Appended last.
    "FLTForHuman/ModularForms/Analytic/Petersson.lean",
    "FLTForHuman/AutomorphicForm/UpperHalfPlane/ModularFundamentalDomain.lean",
    # --- The Petersson adjointness (tier 1): the headline façade only. Its tier-3
    # engine `FLTForHuman/ModularForms/Analytic/PeterssonHecke.lean` stays unlisted
    # (registered in `spec/UNWIRED-PUBLIC.md`). Appended last.
    "FLTForHuman/ModularForms/Analytic/PeterssonHeckeTheorems.lean",
    # --- The coset-space Petersson definition layer (set P1 of
    # `TOPIC-petersson-coset-and-level-prime-eigenvalue.md`): wired, because it is
    # the definition layer both `norm_sq` leaves consume. Appended last.
    "FLTForHuman/ModularForms/Analytic/PeterssonCoset.lean",
    # --- Set P2 (`WORKORDER-P2-normsq.md`): the silo, wired whole — its 71 helpers and the
    # headline are all statement-diffed (+72 against the wrapper + `S_` sources above).
    "FLTForHuman/ModularForms/Analytic/NormSqPow.lean",
    # --- The archimedean Casimir definition layer (`WORKORDER-AC1-defs.md`,
    # `topics/automorphicForm/TOPIC-arch-casimir.md` §4): two new leaf modules, both
    # wired — the pin has no `private` declaration in either, so the whole surface is
    # statement-diffed (+84). Appended last.
    "FLTForHuman/LanglandsTunnell/ArchParam.lean",
    "FLTForHuman/AutomorphicForm/Adelic/ArchDerivCasimir.lean",
    # --- Set A (`WORKORDER-AC2-cascore-trio.md`): one listed module whose wire is exactly the
    # three headlines (+3). The shared `CasCore17` engine and the three pin tails are public and
    # tier 3 — `-- pin:`-marked into the three `S_` files above, which `SOURCES` does not read —
    # so a later proof can import them; they are registered in spec/UNWIRED-PUBLIC.md.
    "FLTForHuman/AutomorphicForm/Adelic/ArchCasimir.lean",
    "FLTForHuman/AutomorphicForm/Adelic/WhittakerCoefficient.lean",
    "FLTForHuman/NumberTheory/NumberField/StandardGlobalAddCharRat.lean",
    "FLTForHuman/NumberTheory/NumberField/StandardGlobalAddChar.lean",
    "FLTForHuman/NumberTheory/NumberField/AdelicTraceProducer.lean",
    "FLTForHuman/NumberTheory/NumberField/IntegralAdelicTrace.lean",
    "FLTForHuman/NumberTheory/NumberField/AdelicTraceFin.lean",
    "FLTForHuman/AutomorphicForm/Adelic/Cusp/CutWeightDecomposition.lean",
    # --- The centre-cut vanishing leaf and its `not_isArithGenuineCuspRealizable` sibling: two
    # listed façades, one headline each (+1 each). The shared 49-declaration engine is unlisted
    # (`Cusp/CentreCutEngine.lean`, tier 3, registered in `spec/UNWIRED-PUBLIC.md`).
    "FLTForHuman/AutomorphicForm/Adelic/Cusp/CentreCutVanishing.lean",
    "FLTForHuman/AutomorphicForm/Adelic/Cusp/CuspUnrealizable.lean",
    # --- The centre-cut fundamental-domain trio: one automorphy-transfer headline and the
    # two measurable-fundamental-domain twins (+1 each). The shared slab prelude is public
    # tier 3 in `PeterssonSlabPairing.lean` (already listed).
    "FLTForHuman/AutomorphicForm/Adelic/DetNormSlab.lean",
    "FLTForHuman/AutomorphicForm/Adelic/MeasurableFundamentalDomainCover.lean",
    # --- The complex archimedean Casimir definition layer and engine. The two definition
    # modules are checked whole; the engine `ArchCasimirComplex.lean` wires only the headline
    # and keeps its ~96 declarations public tier 3 (registered in `spec/UNWIRED-PUBLIC.md`).
    "FLTForHuman/AutomorphicForm/Adelic/ArchDerivCasimirComplex.lean",
    "FLTForHuman/AutomorphicForm/Adelic/ArchDerivCasimirComplexAPI.lean",
    "FLTForHuman/AutomorphicForm/Adelic/ArchCasimirComplex.lean",
    # --- WORKORDER-T4: the continuous norm section. One headline (+1); the engine
    # (`NumberTheory/NumberField/TateGlobal/NormSection.lean`) stays tier 3 and is registered
    # in `spec/UNWIRED-PUBLIC.md`. No existing module was edited, so no hub wave is owed.
    "FLTForHuman/NumberTheory/NumberField/TateGlobalNormSection.lean",
    # --- WORKORDER-T5: GL₂ strong approximation over ℚ. One headline (+1); the five engine
    # modules (`NumberTheory/AdelicLevel/StrongApprox/*.lean`) stay tier 3 and are registered in
    # `spec/UNWIRED-PUBLIC.md`. No existing module was edited, so no hub wave is owed.
    "FLTForHuman/NumberTheory/AdelicLevel/StrongApproxRat.lean",
    # --- WORKORDER-E1: the local-constants definition layer homed whole from the pin's
    # `Def_LanglandsTunnell_TateLocalConstantsAt` (21 declarations, checked). It is the gate of
    # the `EisensteinGeneral.LocalRam`/`LocalUnr` local-integral set that follows.
    "FLTForHuman/LanglandsTunnell/TateLocalConstantsAt.lean",
    # --- WORKORDER-E1 (Set A): the three `EisensteinGeneral.LocalRam` headlines (+3). The two
    # engines (`EisensteinGeneral/LocalTwisted.lean`, `…/LocalRamShells.lean`) stay tier 3 and are
    # registered in `spec/UNWIRED-PUBLIC.md`.
    "FLTForHuman/EisensteinGeneral/LocalRam.lean",
    # --- WORKORDER-E2 (Set B): the two `EisensteinGeneral.LocalUnr` headlines and their
    # machinery, all in one listed module (see SOURCES for why the `S_` files are listed here and
    # not for Set A).
    "FLTForHuman/EisensteinGeneral/LocalUnr.lean",
    # --- WORKORDER-E3: the factorization silo. Five engines + one façade, all listed (see SOURCES
    # for why). Expected delta: every declaration of the six modules except the substituted
    # `integralOffSet`, whose port copy is a one-line alias of `TateGlobal.ShellSupport.integralOff`.
    "FLTForHuman/EisensteinGeneral/Factorization/ProductMeasure.lean",
    "FLTForHuman/EisensteinGeneral/Factorization/Stratum.lean",
    "FLTForHuman/EisensteinGeneral/Factorization/Measure.lean",
    "FLTForHuman/EisensteinGeneral/Factorization/Integrability.lean",
    "FLTForHuman/EisensteinGeneral/Factorization/Tprod.lean",
    "FLTForHuman/EisensteinGeneral/Factorization.lean",
    # --- WORKORDER-P3: the nebentypus Hecke bound. One listed module: 32 new engine declarations at
    # the pin names (namespace `CuspForm.HeckeBoundGamma1`) plus the headline; the 24 declarations
    # shared with the already-ported `NormSqPow.lean` are imported from `CuspForm.LiNormSq`.
    "FLTForHuman/ModularForms/Analytic/NormSqLt.lean",
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
    # `NumberTheory/DedekindPsi.lean`: the generic block count is FLT-private in
    # the pin and promoted here; `dedekindPsiFibre` is the port's rename of the pin's
    # `h`/`slotH` (the name `slotH` is taken publicly by `ModularCurve.QExpN.slotH`),
    # so `card_fibre`'s statement is the pin's modulo that rename.
    "dedekindPsiFibre",
    "card_fibre",
    # The two prime-step case splits of `ψ`. The pin has them only inlined, and the
    # port had written them privately in both `Spine.lean` and `SlotProduct.lean`
    # (2026-10-09: one public copy, in `NumberTheory/DedekindPsi.lean`); the pin's
    # `dedekindPsi_mul_prime` is the general form and is matched separately.
    "dedekindPsi_mul_prime_dvd",
    "dedekindPsi_mul_prime_not_dvd",
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
    # `AlgebraicCurve.Pic0.correspondence` (SET 1, `Defs/Correspondence.lean`) is the
    # one last-name collision the AC block cannot resolve:
    # `Def_AlgebraicCurve_Correspondence.lean` declares `Divisor.correspondence`
    # (line 137) and `Pic0.correspondence` (line 183) with the same last name, and
    # `declarations()` keeps only the first, so no `SOURCES` ordering can verify the
    # second. The exemption is *dotted* so it does not also swallow the other
    # same-last-name declarations, which do verify: `Divisor.correspondence` and
    # `AlgebraicCurve.Differential.correspondence` (`Differential/PushPull.lean`).
    "AlgebraicCurve.Pic0.correspondence",
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
    # The exemption is the **dotted** name `HeckeEis.periodMap`: the unrelated
    # `ModularCurve.periodMap` (`PeriodMapBundled`, ported faithfully in
    # `EichlerShimura/PeriodPrimitive.lean`) shares the last name and must still
    # be diffed against its pin declaration.
    "HeckeEis.periodMap",
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
    # `WeierstrassCurve.Affine.Point.xOrZero` (Vélu SET-1, `Velu/Formula.lean`):
    # the pin declares it `private` with pattern-matching equations and *no*
    # top-level `:=`/`where`, so the checker's `top_level_cut` does not cut and
    # the pinned statement swallows the following `p2m_export` line — its dotted
    # copy cannot be matched textually by any port declaration. The port promotes
    # it (the odd-order layer's `kw_veluX_xOrZero_add_gen_odd` names
    # `(P + Q).xOrZero`, so it must be public), transcribing the pin's statement
    # `: W.Point → R` and body verbatim; only the checker's extraction is at
    # fault, so it is exempted by last name (unique in the port).
    "xOrZero",
    # --- Patching-port `class` binder spelling (found 2026-10-04) ---------------
    # The checker now matches `class` declarations (it previously did not, so
    # these were never diffed). The four classes in
    # `FLTForHuman/Patching/PatchingConstruction.lean` predate this check and
    # spell their binders via section variables where the pin
    # (`Definitions/Def_Patching_SystemTypes.lean`) is explicit, or differ
    # textually: `IsAdicTopology` writes `(R)` for the pin's `(R : Type*)`;
    # `Algebra.TopologicallyFG` and `IsPatchingSystem` rely on surrounding
    # `variable`s; `PatchingAlgebra.smulData` has no textual counterpart under
    # that name. These are **pre-existing, non-Vélu** deviations of the Patching
    # effort, registered as a residual in CARRY-FORWARD.md; they are exempted by
    # dotted name so this list cannot leak to any other `TopologicallyFG` etc.
    "PatchingConstruction.IsLocalRing.IsAdicTopology",
    "PatchingConstruction.Algebra.TopologicallyFG",
    "PatchingConstruction.IsPatchingSystem",
    "PatchingConstruction.PatchingAlgebra.smulData",
    # H5 SET-1: `InfinitePlace` is a *class* in `Place/Dictionary.lean` (the H5r
    # dictionary extraction), so the pin's `InfinitePlace.place`,
    # `not_isFinitePlace` and `deg_eq_one`/`eq_of_not_isFinitePlace` survive as
    # its fields.  The engine recovers the instance from the pin's gate
    # vocabulary with the pin's own proofs; the class has no pin counterpart
    # under this name, so the instance is the port's own declaration.  Dotted,
    # so the exemption cannot leak to any other `instInfinitePlace`.
    "WeierstrassCurve.Affine.instInfinitePlace",
    # D-6: the two-curve countable descent. The pin states this content only inside its
    # `KwD5BetweenCurvesSubfieldDescent` staging `Prop`, whose body is `∀ K … E E' ι …`;
    # the port lands it as a theorem at the port's own name
    # `ModularCurve.exists_twoCurveDescent`, so no pin declaration of that name — or of
    # that statement shape — exists for the checker to diff. The module's other public
    # declarations are at the pin names (the `iotaDescent*` family, and the headline
    # against its wrapper).
    "ModularCurve.exists_twoCurveDescent",
    # Refactor wave (2026-10-08): the character-free copy of
    # `WeierstrassCurve.Affine.normFormulaAlong_of_elliptic` in
    # `FLTForHuman/WeierstrassCurve/Velu/RestrictAlong.lean`. The pin declares that name
    # twice at two different statements — this one (`[IsAlgClosed F]` with an explicit
    # `hsep`) and the `[IsAlgClosed F] [CharZero F]`, `hsep`-free special case, which the
    # port carries in `IsogenyEndDatum/Engine.lean`. Two different declarations cannot
    # share one fully qualified name, so `Engine.lean` and `Velu/RestrictAlong.lean` were
    # unimportable together, and the ready node
    # `WeierstrassCurve.zmultiples_eq_of_veluQuotient_j_eq_of_forall_isogenyEndDatum_exists_int`
    # needs both cones. The Engine copy keeps the pin name (it has ~100 references across
    # the library and the `spec/` zones); this copy is renamed to the file's own `_cf`
    # convention with its statement unchanged, so the last-name lookup can no longer find
    # its pin counterpart. Dotted, so the exemption cannot leak. See
    # `topics/deligneSerre/TOPIC-weierstrass-ready-shelf.md` §5.1 and the declaration's
    # docstring.
    "WeierstrassCurve.Affine.normFormulaAlong_of_elliptic_cf",
    # --- D-5, the kernel-base-change seam (2026-10-16 build-time work) ---------
    # `FLTForHuman/WeierstrassCurve/Isogeny/KernelBaseChange.lean` transcribes the
    # pin's `kw_surge_hgf4_bc*` tensor transport, but the 2026-10-16 build-time pass
    # (commit e39a2bb, "improve build time") replaced two inline terms with named
    # helpers, so the checker's textual diff no longer sees them:
    #
    # * `kw_surge_hgf4_tensorUnit` / `…_apply` are the port's own. They name the
    #   canonical `F`-algebra map `b ↦ algebraMap (b ⊗ₜ 1)` that the pin writes
    #   inline in both naturality squares of `kw_surge_hgf4_bcIota₁_compat`. FLT has
    #   no declaration for it, so there is no name or statement to diff.
    # * `kw_surge_hgf4_bcTensorFracIotaFinrank` is likewise the port's own: it names
    #   the `letI`/`@Module.finrank … Algebra.toModule` left-hand side of the seam,
    #   because spelling that inline made the seam's statement `whnf` past the
    #   default heartbeat budget.
    # * `kw_surge_hgf4_bcTensorFracIotaSeam` reads
    #   `kw_surge_hgf4_bcTensorFracIotaFinrank E₀ E₀' F F' ι₀ = finrankAlong F ι₀`
    #   where the pin spells the same term out. The two statements are the pin's
    #   modulo that transparent helper (its body verbatim), so the diff cannot see
    #   them as equal; spelling the term inline again would restore direct coverage.
    # The rest of the pin's `kw_surge_hgf4_bc*`/`kw_surge_hgf4_χE_*` block is at the
    # pin names and still diffs against the pin's private originals.
    "ModularCurve.kw_surge_hgf4_tensorUnit",
    "ModularCurve.kw_surge_hgf4_tensorUnit_apply",
    "ModularCurve.kw_surge_hgf4_bcTensorFracIotaFinrank",
    "ModularCurve.kw_surge_hgf4_bcTensorFracIotaSeam",
}


# The provenance convention of playbook §4 and `spec/UNWIRED-PUBLIC.md`: a public
# declaration transcribed from the pin carries the pin original on a comment line
# just above it,
#     -- pin: gapsw80_t9_completedDedekindZeta (S_..._package.lean:5577)
# `spec/unwired_register.py` builds the tier-3 register from exactly these
# comments, and they are the only record of an unwired declaration's pin source.
# The checker reads them for the same reason (see `pin_markers`): a marker naming a
# pin file that `SOURCES` does not list must not turn into `MISSING IN FLT`, and a
# marker naming a listed file hands the diff the exact pin original to compare.
PIN_MARKER_RE = re.compile(
    r"--\s*pin:\s*([\w.'\u2080-\u209c]+)(?:\s*\(([^):\s]+)(?::(\d+))?\))?"
)



# A `-- pin:` comment sits above its declaration, but between the two the port may
# write `@[…]` attribute lines and the inline scoping commands (`omit … in`,
# `include … in`, `set_option … in`, `variable … in`).  Association therefore walks
# *forward* from the marker over exactly those and stops at anything else.  A marker
# that cannot see its declaration — the `scoped instance` the checker cannot read, a
# declaration whose header it does not recognise — associates with nothing, rather
# than attaching itself to whatever declaration happens to follow: a stray marker
# must never exempt an unrelated statement.  (The register's three-line window has
# this hazard; the checker is stricter, so it can only exempt less.)
PIN_MARKER_MAX_GAP = 8
PIN_MARKER_LEAD_RE = re.compile(
    r"^(?:@\[|omit\b|include\b|variable\b|set_option\b|attribute\b|open\b|local\b|"
    r"noncomputable\b|unsafe\b|private\b|protected\b|scoped\b|nonrec\b)"
)


def _code_lines(text: str) -> list[str]:
    """`text` line by line, with block comments blanked and `--` comments kept.

    Used only for the marker scan.  `strip_comments` cannot serve: it removes a
    multi-line block comment outright, shifting every later line number, and the
    marker is associated *by line*.  Keeping the line count and blanking the
    comment interior makes a `-- pin:` example inside a docstring invisible while a
    real comment line stays where it was.
    """
    out: list[str] = []
    depth = 0
    for line in text.split("\n"):
        buf: list[str] = []
        i = 0
        while i < len(line):
            if line.startswith("/-", i):
                depth += 1
                i += 2
            elif depth and line.startswith("-/", i):
                depth -= 1
                i += 2
            elif depth:
                buf.append(" ")
                i += 1
            elif line.startswith("--", i):
                # Keep the comment: it is where the marker lives.  `DECL_RE` still
                # sees a declaration that opens the line before one.
                buf.append(line[i:])
                i = len(line)
            else:
                buf.append(line[i])
                i += 1
        out.append("".join(buf))
    return out


def pin_markers(text: str) -> dict[str, list[tuple[str, str | None]]]:
    """`-- pin:` provenance per public declaration name, in source order.

    Returns `bare name -> [(pin name, pin file), …]`, one entry per non-`private`
    declaration of that name (a marker-less declaration contributes `("", None)`,
    so a name declared twice keeps its markers aligned positionally).  The caller
    consumes each list with a cursor in `raw_declarations` order; both sides skip
    `private` declarations, so the sequences agree.
    """
    code = _code_lines(text)
    n = len(code)
    targets: dict[int, tuple[str, str | None]] = {}
    for j, line in enumerate(code):
        m = PIN_MARKER_RE.search(line)
        if not m:
            continue
        mark = (m.group(1), m.group(2))
        k, gap = j + 1, 0
        while k < n and gap < PIN_MARKER_MAX_GAP:
            stripped = code[k].strip()
            if not stripped or stripped.startswith("--"):
                k += 1
                gap += 1
                continue
            if DECL_RE.match(code[k]):
                targets[k] = mark
                break
            if stripped.startswith("@["):
                # an attribute may wrap; skip to the line that closes it
                while k < n and "]" not in code[k]:
                    k += 1
                k += 1
                gap += 1
                continue
            if PIN_MARKER_LEAD_RE.match(stripped):
                k += 1
                gap += 1
                continue
            break
    out: dict[str, list[tuple[str, str | None]]] = {}
    for i, line in enumerate(code):
        m = DECL_RE.match(line)
        if not m or "private" in m.group("mods"):
            continue
        out.setdefault(m.group("name"), []).append(targets.get(i, ("", None)))
    return out




def check_prop_bodies(flt: Path) -> int:
    """Audit the body of every public port `def … : Prop` against the pin.

    The main pass compares a `def`'s *type*, which for `def foo : Prop := P` is
    just `Prop`; two same-named `Prop`-valued defs match whatever their bodies
    say.  For a proposition that body is the statement (downstream declarations
    unfold it), so this pass compares it, with the same normalisation the main
    pass uses for statements.  Only `Prop`-valued defs are compared: a
    computational `def` may legitimately be reimplemented as long as it is
    definitionally equal, but a propositional body is a statement.

    Candidates are keyed both by dotted name (for promoted pin-private
    declarations) and by last name, mirroring the main pass's fallback.  The pass
    is **advisory**: a textual difference can be elaboration spelling (dot
    notation, implicit-argument placement), so it reports rather than fails.
    Returns the number of bodies that differ from every candidate at the
    normalised-text level.
    """
    body_source: dict[str, list[tuple[str, str, str, str]]] = {}
    for rel in SOURCES:
        p = flt / rel
        if not p.exists():
            continue
        for raw, kind, stmt, body in declaration_bodies(
            p.read_text(encoding="utf-8"), include_private=True
        ):
            if kind not in ("def", "abbrev") or not body:
                continue
            for key in (promoted_key(raw), promoted_key(raw.rsplit(".", 1)[-1])):
                body_source.setdefault(key, []).append((kind, stmt, body, rel))

    ok = diff = 0
    for rel in PORT_FILES:
        p = LEAN / rel
        for raw, kind, stmt, body in declaration_bodies(p.read_text(encoding="utf-8")):
            if kind not in ("def", "abbrev") or not body:
                continue
            if ": Prop" not in stmt:
                continue
            name = raw.rsplit(".", 1)[-1]
            cands = body_source.get(promoted_key(raw)) or body_source.get(name) or []
            typed = [c for c in cands if c[0] == kind and c[1] == stmt]
            if not typed:
                continue
            if any(prop_body_key(c[2]) == prop_body_key(body) for c in typed):
                ok += 1
            else:
                diff += 1
                print(f"PROP BODY (review)  {rel}: {name}")
                print(f"    port: {body[:240]}")
                print(f"    flt : {typed[0][2][:240]}  (source {typed[0][3]})")
    print(
        f"\n{ok} Prop-valued def bodies identical, {diff} differ textually "
        f"({ok + diff} propositional definitions with a statement-matched "
        f"counterpart); each difference is advisory — confirm it is elaboration "
        f"spelling (dot notation, implicit arguments), not a different proposition"
    )
    return diff






def match_candidate(cands: list[tuple] | None, kind: str, stmt: str) -> tuple | None:
    """The first candidate whose kind and normalized statement both equal the port's."""
    for c in cands or ():
        if same_kind(c[0], kind) and c[1] == stmt:
            return c
    return None


def selftest() -> int:
    """Unit tests for the checker's own sensitivity.

    The historical review ritual was a manual one-token mutation of a headline
    followed by a revert.  That tests a property of *this instrument*, not of the
    set being landed, so it belongs here and runs when the checker changes rather
    than on every set: the parser, `norm`, and the (kind, statement) equality are
    exercised on a synthetic pin/port pair, and a one-token mutation of the
    statement must fail to match.  `--selftest`.
    """
    checks = 0

    def check(cond: bool, msg: str) -> None:
        nonlocal checks
        if not cond:
            raise SystemExit(f"check_flt_statements selftest FAILED: {msg}")
        checks += 1

    # The normalisation the textual diff relies on.
    check(norm("a   b\n  c") == "a b c", "whitespace is not collapsed")
    check(norm("kw_foo") == "foo", "leading kw_ is not erased")
    check(norm("L.kw_foo") == "L.foo", "method kw_ is not erased")
    check(norm("kwF4R1V384a_foo") == "foo", "generated kw prefix is not erased")
    check(norm("kwTISDα_charFree") == "charFree", "Greek kw prefix is not erased")
    check(norm("kwVeluPointMap") == "VeluPointMap", "standalone kw word is not erased")
    check(norm("kwHgf_v277_foo") == "v277_foo", "kw abbreviation prefix is not erased")
    check(norm("kw_surgehgf4_hfgkd_ktd_kerTransport_proved") == "kerTransport_proved",
          "deep kw junk prefix is not erased")
    check(norm("kw_surgehgf4_hH2c_between") == "between",
          "hH2 subfamily token is not erased")
    check(norm("kw_mlc_hrtCharP9_foo") == "hrtCharP9_foo",
          "kw_ junk token is not erased")
    check(norm("kw_es_residueTheoremK") == "residueTheoremK",
          "two-letter kw_ token is not erased")
    check(norm("kw_dualEndData_proof") == "dualEndData_proof",
          "meaningful kw_ name was erased")
    check(norm("kw_velu2X_apply") == "velu2X_apply",
          "legitimate velu kw_ name was erased")
    check(norm("pck_s17") == "s17", "a step stub token was not erased")
    check(norm("backward") == "backward", "kw inside a word was erased")
    # The same matcher is the port-side residual-name guard in check_port:
    # what `norm` erases is exactly what that guard rejects.
    check(KW_PREFIX_RE.search("kw_foo") is not None, "guard misses kw_")
    check(KW_PREFIX_RE.search("kwF4R1V384a_foo") is not None, "guard misses kwX")
    check(KW_PREFIX_RE.search("kwVeluPointMap") is not None, "guard misses standalone kw word")
    check(KW_PREFIX_RE.search("backward") is None, "guard falsely matches inside a word")
    check(KW_PREFIX_RE.search("foo_kw_bar") is not None,
          "guard misses a middle kw_ token")
    check(norm("foo_kw_bar") == "foo_bar", "middle kw_ token is not erased")
    check(KW_FAMILY_RE.search("Piece_KwVelu") is not None,
          "guard misses a middle Kw token")
    check(KW_PREFIX_RE.search("dualEndData") is None, "guard matches a clean name")
    # The capital-Kw name policy, shared with check_port's residual guard.
    check(KW_FAMILY_RE.search("KwD5BetweenCurvesHoloLift") is not None, "guard misses KwD5")
    check(KW_FAMILY_RE.search("KwF4gRRTate") is not None, "guard misses KwF4")
    check(KW_FAMILY_RE.search("KwTateRR3") is not None, "guard misses KwTate")
    check(KW_FAMILY_RE.search("Kw") is None, "guard matches the exact Kw abbrev")
    check(KW_FAMILY_RE.search("Kwota") is None, "guard matches a lowercase Kw word")
    check(norm("KwD5BetweenCurvesHoloLift") == "BetweenCurvesHoloLift",
          "capital Kw prefix is not erased in statements")
    check(norm("KwF4gRRTate.KwF4gRRTateCommFinite")
          == "Tate.TateCommFinite",
          "capital Kw namespace prefix is not erased in statements")
    check(norm("Kw") == "Kw", "the exact Kw abbrev was erased")
    check(norm("KwF4gRRTate") == "Tate",
          "generated F4gRR token was not stripped as a unit")
    check(norm("KwF4R1V384aCompletion") == "Completion",
          "generated F4R1V token was not stripped as a unit")
    check(norm("KwTateRR3Cohen") == "Cohen",
          "generated TateRR3 token was not stripped as a unit")
    check(norm("KwNo6Pin") == "Pin", "generated No6 token was not stripped")
    check(norm("KwD5Between") == "Between", "generated D5 token was not stripped")
    check(norm("KwOdaDHDR") == "", "an empty generated namespace did not vanish")
    check(norm("LocalResiduePin") == "Pin", "canonical No6Pin map is missing")
    check(norm("tisdCharFreeα") == "charFree", "canonical charFree map is missing")
    check(norm("sublatticeCoords_index") == "index",
          "canonical HZZ map is missing")
    check(norm("VeluPointMap_zero") == "zero",
          "canonical VeluPointMap lemma map is missing")
    check(norm("ModularCurve.foo") == "foo", "namespace qualifier is not erased")

    # One-token mutation sensitivity: an identical copy matches, a mutated
    # statement does not.  Bodies are outside the statement and must not matter.
    pin = "theorem foo (h : 0 < r) : P := by\n  sorry\n"
    copy = "theorem foo (h : 0 < r) : P := by\n  trivial\n"
    mutant = "theorem foo (h : 0 ≤ r) : P := by\n  trivial\n"
    pk = raw_declarations(pin)[0]
    ck = raw_declarations(copy)[0]
    mk = raw_declarations(mutant)[0]
    check(pk[0] == ck[0] == mk[0], "the parser disagrees on the declaration name")
    check(pk[1] == ck[1] == mk[1] == "theorem", "the parser disagrees on the kind")
    cands = [(pk[1], pk[2])]
    check(match_candidate(cands, ck[1], ck[2]) is not None,
          "an identical copy is not matched")
    check(match_candidate(cands, mk[1], mk[2]) is None,
          "a one-token mutation is not caught")
    check(ck[2] != mk[2], "a one-token mutation normalises to the same statement")

    # Kind equivalence: a `def` and a `theorem` with the same statement match (the
    # body-only `@[reducible] def` → `theorem` adaptation), but a `structure` (whose
    # statement carries FIELDS and is a different signature) still does not.
    check(match_candidate([("def", pk[2])], "theorem", pk[2]) is not None,
          "def/theorem with the same statement do not match")
    check(match_candidate([("theorem", pk[2])], "lemma", pk[2]) is not None,
          "theorem/lemma with the same statement do not match")
    check(match_candidate([("def", pk[2])], "structure", pk[2]) is None,
          "def/structure with the same text wrongly match")

    # The tier-3 provenance marker: a `-- pin:` comment binds to the declaration
    # it stands above, and to nothing else.  A marker that cannot see its own
    # declaration must not leak to the next one — that would exempt an unrelated
    # statement from the diff (the whole reason the marker is read at all).
    prov = pin_markers("-- pin: foo (S_X.lean:12)\ntheorem foo : P := by\n  sorry\n")
    check(prov == {"foo": [("foo", "S_X.lean")]}, "a marker does not bind to its declaration")
    prov = pin_markers("/- -- pin: fake (S_Nope.lean:1) -/\ntheorem foo : P := by\n  sorry\n")
    check(prov == {"foo": [("", None)]}, "a marker inside a docstring is not a marker")
    prov = pin_markers(
        "-- pin: foo (S_X.lean:1)\ntheorem foo : P := by\n  sorry\n\n"
        "theorem bar : Q := by\n  sorry\n")
    check(prov["bar"] == [("", None)], "a marker leaks onto the next declaration")
    prov = pin_markers(
        "-- pin: foo (S_X.lean:1)\nomit [NeZero n] in\ntheorem foo : P := by\n  sorry\n")
    check(prov["foo"] == [("foo", "S_X.lean")],
          "a marker does not bind across an inline scoping command")
    prov = pin_markers(
        "-- pin: helper (S_X.lean:1)\nprivate theorem helper : P := by\n  sorry\n\n"
        "theorem foo : Q := by\n  sorry\n")
    check(prov == {"foo": [("", None)]},
          "a private declaration's marker leaks onto the next public one")
    prov = pin_markers(
        "-- pin: a (S_X.lean:1)\ntheorem foo : P := by\n  sorry\n"
        "-- pin: b (S_X.lean:2)\ntheorem foo : Q := by\n  sorry\n")
    check(prov["foo"] == [("a", "S_X.lean"), ("b", "S_X.lean")],
          "two declarations of one name do not keep their markers in order")

    print(f"check_flt_statements selftest ok ({checks} assertions)")
    return 0


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument(
        "--flt",
        default=str(Path.home() / "proj" / "fermats-last-theorem"),
        help="path to the pinned fermats-last-theorem clone",
    )
    ap.add_argument(
        "--prop-bodies",
        action="store_true",
        help="also compare the body of every public `def … : Prop` (its real "
        "statement); the main pass compares only the type, i.e. `Prop`",
    )
    ap.add_argument(
        "--selftest",
        action="store_true",
        help="run the checker's own unit tests (parser, normalisation, one-token "
        "mutation sensitivity) and exit",
    )
    args = ap.parse_args()
    if args.selftest:
        return selftest()
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
    # The pin's prefix-stripped last names (`kw_g₂_ofTau` → `g₂_ofTau`), the §2.1
    # promotion path.  Consulted only after the public and dotted lookups fail; `kind`
    # and the normalised statement must still match, and the strip is applied to the
    # pin side only.  The pin's `p2m_export` visibility is invisible to this text
    # checker, so a `kw_*` declaration whose name is suppressed by `p2m_export` (but
    # not written `private`) is indexed here too; indexing a textually public `kw_*`
    # name is harmless, because `source`/`dotted_source` still run first.  Entries are
    # `(kind, stmt, rel, pin_raw)`.
    stripped_source: dict[str, list[tuple[str, str, str, str]]] = {}
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
            stripped = strip_pin_prefix(raw.rsplit(".", 1)[-1])
            if stripped is not None:
                stripped_source.setdefault(stripped, []).append((kind, stmt, rel, raw))

    ok = promoted = renamed = missing = mismatch = own = unwired = 0
    source_basenames = {rel.rsplit("/", 1)[-1] for rel in SOURCES}

    def pin_source_listed(pin_file: str | None) -> bool:
        """Whether the pin file a `-- pin:` marker names is one `SOURCES` reads."""
        if not pin_file:
            return False
        return pin_file in SOURCES or pin_file.rsplit("/", 1)[-1] in source_basenames

    for rel in PORT_FILES:
        p = LEAN / rel
        text = p.read_text(encoding="utf-8")
        markers = pin_markers(text)
        consumed: dict[str, int] = {}
        for raw, kind, stmt in raw_declarations(text):
            name = raw.rsplit(".", 1)[-1]
            # This declaration's provenance marker, if any (`pin_markers` skips the
            # same `private` declarations, so the two sequences stay aligned).
            seen = consumed.get(name, 0)
            consumed[name] = seen + 1
            marks = markers.get(name) or []
            pin_name, pin_file = marks[seen] if seen < len(marks) else ("", None)
            if raw in OWN_PROOFS or name in OWN_PROOFS:
                own += 1
                continue
            if match_candidate(source.get(name), kind, stmt):
                ok += 1
                continue
            # Promoted from a pin-private declaration: the last-name lookup
            # either missed it (attributed `@[scoped simp]` in the public pin
            # copy) or found an unrelated same-named declaration; the dotted
            # name disambiguates.
            hit = match_candidate(dotted_source.get(promoted_key(raw)), kind, stmt) \
                or match_candidate(dotted_source.get(name), kind, stmt)
            if hit:
                ok += 1
                promoted += 1
                continue
            # Promoted at the prefix-stripped pin name: a pure fallback after the
            # public and dotted lookups, still requiring kind and statement to match.
            hit = match_candidate(stripped_source.get(name), kind, stmt)
            if hit:
                ok += 1
                renamed += 1
                print(f"RENAMED  {rel}: {raw}  ->  {hit[3]} ({hit[2]})")
                continue
            # The `-- pin:` provenance comment decides the fallthrough.  It is the
            # register's marker, and it names the pin file holding the statement:
            #   * pin file not in `SOURCES` — the statement is transcribed from a
            #     file this run does not read, so no diff is possible.  It is tier 3
            #     (`spec/UNWIRED-PUBLIC.md`), and the marker is its provenance, so
            #     it is exempted rather than reported `MISSING IN FLT` (or wrongly
            #     `MISMATCH`ed against an unrelated `SOURCES` declaration that
            #     happens to share the last name);
            #   * pin file in `SOURCES` — the marker names the exact pin original,
            #     which may be a renamed declaration the by-name lookups cannot
            #     reach; diff against it, and exempt only if it is not there (a
            #     counterpart that exists but differs is a genuine `MISMATCH`).
            if pin_name:
                pin_last = pin_name.rsplit(".", 1)[-1]
                if pin_source_listed(pin_file):
                    pin_cands = (source.get(pin_last)
                                 or dotted_source.get(promoted_key(pin_name))
                                 or dotted_source.get(pin_last))
                    if match_candidate(pin_cands, kind, stmt):
                        ok += 1
                        continue
                    if pin_cands:
                        mismatch += 1
                        print(f"MISMATCH  {rel}: {name}  (pin marker {pin_name}, "
                              f"source {pin_cands[0][2]}, {pin_cands[0][0]})")
                        print(f"    port: {stmt}")
                        print(f"    flt : {pin_cands[0][1]}")
                        continue
                unwired += 1
                print(f"UNWIRED  {rel}: {raw}  (pin: {pin_name}, "
                      f"{pin_file or 'no file named'}; register only, not diffed)")
                continue
            cands = (source.get(name) or dotted_source.get(promoted_key(raw))
                     or dotted_source.get(name))
            if not cands:
                print(f"MISSING IN FLT  {rel}: {raw}")
                missing += 1
                continue
            skind, sstmt, srel = cands[0]
            if not same_kind(skind, kind) or sstmt != stmt:
                mismatch += 1
                print(f"MISMATCH  {rel}: {name}  (source {srel}, {skind})")
                print(f"    port: {stmt}")
                print(f"    flt : {sstmt}")

    exempt = f", {unwired} registered-unwired declarations exempted" if unwired else ""
    print(
        f"\n{ok} statements identical ({promoted} promoted from pin-private "
        f"declarations, {renamed} renamed), {mismatch} mismatched, {missing} missing, "
        f"{own} own-proof declarations exempted{exempt} "
        f"({ok + mismatch + missing + own + unwired} port declarations checked)"
    )
    if args.prop_bodies:
        print()
        check_prop_bodies(flt)
    # `--prop-bodies` is advisory: a textual body difference can be elaboration
    # spelling, so it never changes the exit status.
    return 0 if mismatch == 0 and missing == 0 else 1


if __name__ == "__main__":
    raise SystemExit(main())
