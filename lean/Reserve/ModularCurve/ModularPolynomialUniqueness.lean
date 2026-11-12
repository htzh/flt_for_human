/-
  T13 — the consequence, part 1: uniqueness and the degree.

  Two facts about the level-`p` datum that the splitting reads off:

  * `finrank_adjoin_jqN_eq_of_prime` — `[ℚ(j)(j(q^p)) : ℚ(j)] = p + 1`, the degree
    of the minimal polynomial, obtained from T12's
    `exists_phiIrreducible_evalSymm` and `dedekindPsi_prime`;
  * `ModularPolynomialData.eq_of_prime` — any two data at a prime are equal,
    because each `toAdjoin` is the minimal polynomial of `j(q^p)`.

  Together they are the "uniqueness" that lets `splits_of_prime` identify the
  caller's datum with the one assembled from the descended family.

  ## Source

  FLT `anthropics/fermats-last-theorem@aa2d8b3`:
  `P2M/Sol/S_ModularCurve_finrank_adjoin_jqN_eq_of_prime.lean` (52 lines) and
  `P2M/Sol/S_ModularCurve_ModularPolynomialData_eq_of_prime.lean` (73 lines). The
  two public statements are the `Theorems/` wrappers verbatim; the pin's
  `minpoly_jqN_eq_toAdjoin` is T12's `ModularPolynomialData.minpoly_jqN_eq`, and
  its `evalAtJGen_injective`/`aeval_jqN_toAdjoin` are T12's public ones.

  ## Assumptions

  `Defs/Fields`'s `toAdjoin`/`toAdjoin_monic`/`evalAtJGen`; `Defs/Jq`'s
  `jq`/`jqN`/`dedekindPsi`/`dedekindPsi_prime`; `Defs/PhiGen`'s `PhiIrreducible`;
  T12's `ModularPolynomialProperties.exists_phiIrreducible_evalSymm` and
  `ModularPolynomialIrreducible`'s `evalAtJGen_injective`, `aeval_jqN_toAdjoin`,
  `minpoly_jqN_eq`.
  Wired here, not in the frozen registry: the module left `PORT_FILES`
  (`spec/old_check_stmts.py`) on 2026-11-06 and carries its own `spec-pin:` wire.

  spec-pin: Theorems/Thm_ModularCurve_ModularPolynomialData_eq_of_prime.lean
  spec-pin: Theorems/Thm_ModularCurve_finrank_adjoin_jqN_eq_of_prime.lean
-/

-- Body retired: this module's content now lives in
-- `FLTForHuman.ModularCurve.ModularEquation.Split`.
