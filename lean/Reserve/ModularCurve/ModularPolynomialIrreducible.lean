/-
  T12 — the 895 block: irreducibility and symmetry of the datum.

  The block is FLT's single largest shared development: it ships in five pin files
  (the three graph nodes `phiIrreducible_of_splits`, `evalSymm_of_splits`,
  `transposeToAdjoin_monic_of_qExpansion`, plus the two hidden exports
  `swapBivar_monic_of_coeff_bounds` and `evalSymm_of_irreducible`), `5 × 895 ≈
  4,475` pin lines. This module is the block's irreducibility half, with the level
  embedding both halves share: it exports the irreducibility headline, the prime
  non-membership, the datum's minimal-polynomial facts, and the level embedding
  `qEmbedT` with the evaluation `evalAtJK` that every splitting hypothesis of the cone is
  stated with, together with the conjugates' leading terms. Everything else the
  symmetry argument is built from — the transposed evaluation read off the
  splitting, the transpose engine, the q-expansion dictionary, the descended pole
  bounds — is in `ModularPolynomialProperties.lean`, beside the capstone that runs
  them.

  ## What it proves

  * `conj_injective` — the `ℓ + 1` conjugates are distinct (separated by their
    `q⁻¹` coefficients);
  * `jqN_not_mem_adjoin_jq` (private) — `j(q ^ ℓ)` is not a polynomial in `j(q)`, the
    prime non-membership: the twist-sum refutation, using `one_le_coeff_jq` at
    `n = ℓ`. The pin has it public (`aeval_jq_ne_jqN_of_isPrimitiveRoot`,
    `aeval_jq_ne_jqN`, `jqN_not_mem_adjoin_jq`) but no file outside the block's own
    copies cites any of the three, so the port keeps the statement and inlines the
    chain into one private fact (its only consumer is the irreducibility proof);
  * `phiIrreducible_of_splits` — the datum is irreducible over `ℚ(j)`, by the
    factor-counting argument: a nonzero `D ∈ ℚ[j(q)]` with `D(jq) = 0` has degree
    `≥ ℓ` (the conjugates are distinct), so one factor of any factorisation has
    degree `≤ 1`, and it is a unit because `j(q^ℓ) ∉ ℚ[j(q)]`;
  * `aeval_jqN_toAdjoin`, `minpoly_jqN_eq` — `data.toAdjoin` annihilates `j(q^ℓ)`,
    and is its minimal polynomial when the datum is irreducible;
  * `evalAtJGen_injective` — the injectivity that lets the symmetry step be decided
    over `ℚ(j(q))`;
  * `qEmbedT`, `qEmbedT_injective`, `qEmbedT_jq`, `qEmbedT_eq_coeffEmb_qExpand`,
    `qEmbedT_jqN`, `evalAtJK`, `conj_succ_zero` — the level embedding `ℚ((q)) → K((q))`, its
    readings, and the evaluation `ℤ[X] → K((q))` that the splitting hypotheses of the cone are
    stated with; exported because the transposed evaluation runs the same transport.

  ## Reuse (work order §3.1)

  The block's private `evalAtJ_injective` is T11's public one; its private
  `coeff_aeval_jq_neg` is T9's; its private `evalAtJ_eq_aeval_map_rat` is the
  `Defs/Jq.lean` promotion; its private `coeff_aeval_jq_of_lt` is
  `Defs/PhiGen.lean`'s `poleOrderLE_aeval_jq` and its private
  `coeff_aeval_jq_neg_natDegree` is `Defs/Jq.lean`'s `coeff_aeval_jq_neg` at
  `m = P.natDegree`; `evalAtJGen_injective` is derived from
  `evalAtJ_injective` through `algebraMap_comp_evalAtJGen` (the `eq_of_prime` file's
  two-line proof), and `conj_injective` is written once and exported.

  ## Source

  FLT `anthropics/fermats-last-theorem@aa2d8b3`:
  `P2M/Sol/S_ModularCurve_PhiGen_evalSymm_of_splits.lean` (895 lines). The public
  statements are the `Theorems/` wrappers verbatim where a wrapper exists; the level
  embedding is the `S_` file's own (private) machinery, promoted here because the
  transpose half of the block imports it. The port keeps the block's headlines and
  the statements the argument needs, and does not name the pin's staging nodes
  (`transposeToAdjoin_monic_of_qExpansion`, `evalSymm_of_irreducible`,
  `evalSymm_of_splits`), whose hypotheses are the transpose's monic and degree facts
  — one step's output handed to the next; the capstone carries that argument on its
  own main line instead.

  ## Assumptions

  `Defs/PhiGen`'s `conj`/`conj_zero`/`conj_succ`/`phiProd`/`phiProd_eval_conj`/
  `ModularPolynomialData`/`EvalSymm`/`PhiIrreducible`/`adjoinJq`/`jAdj`/
  `evalAtJAdj`/`swapBivar`; `Defs/Fields`'s `jGen`/`evalAtJGen`/
  `algebraMap_comp_evalAtJGen`/`toAdjoin`/`toAdjoin_monic`; `Defs/Jq`'s `jq`/
  `jqN`/`evalAtJ`/`evalAtJ_eq_aeval_map`/`coeff_aeval_jq_neg`/`transcendental_jq`/
  `dedekindPsi_prime`; `Defs/BivariateEval`'s `ev`/`ev_swap`/`ev_int`/`ev_sub`/
  `swap_eq_of_evalSymm`; T11's `PhiGen.evalAtJ_injective`; T12's `one_le_coeff_jq`.
  Checked by `spec/check_port.py` through the `spec-pin:` lines below; the module is
  not listed in `spec/old_check_stmts.py`.

  spec-pin: P2M/Sol/S_ModularCurve_PhiGen_evalSymm_of_splits.lean
  spec-pin: Theorems/Thm_ModularCurve_ModularPolynomialData_minpoly_jqN_eq.lean
  spec-pin: Theorems/Thm_ModularCurve_PhiGen_conj_injective.lean
  spec-pin: Theorems/Thm_ModularCurve_PhiGen_phiIrreducible_of_splits.lean
  spec-pin: Theorems/Thm_ModularCurve_aeval_jqN_toAdjoin.lean
  spec-pin: Theorems/Thm_ModularCurve_evalAtJGen_injective.lean
-/

-- Body retired: this module's content now lives in
-- `FLTForHuman.ModularCurve.ModularEquation.Existence`.
