/-
  T12 — the properties, concluded: the irreducible symmetric datum.

  The module owns the **symmetry** argument: the transpose engine (`swapBivar` is
  mathlib's `Bivariate.swap`; a coefficient-bounded polynomial has a monic
  transpose of a computable degree), the q-expansion dictionary that reads pole
  bounds as those coefficient bounds, `EvalSymm` and its two conversions to the
  transpose identity, the transposed evaluation `Φ(j(q ^ ℓ), j(q)) = 0` read off the
  splitting, the descent dictionary that turns a descended family into that
  splitting and into the pole bounds, and the minimal polynomial of the transposed
  evaluation. On top of it sits `exists_phiIrreducible_evalSymm`, the cone's own
  construction: it chooses a primitive `ℓ`-th root in `CyclotomicField ℓ ℚ` (mathlib
  supplies one) and runs (a) descent (T11) → (b) integrality (T9) → (c) membership
  (T8) → T11's assembly → the splitting, which gives irreducibility, the transposed
  evaluation and — through T10's pole-bound exports
  (`phiProd_conj_coeff_zero_lead`, `phiProd_conj_coeff_eq_zero_of_le`) — the
  coefficient bounds. The dictionary turns those into
  `(swapBivar Φ).map evalAtJGen` being monic of degree `ψ(ℓ)`, and the datum
  annihilates `j(q ^ ℓ)`, so the transpose is `Φ` itself by uniqueness of the
  minimal polynomial. It is a join, not new mathematics, and it is T13's entry
  point.

  ## Source

  FLT `anthropics/fermats-last-theorem@aa2d8b3`:
  `P2M/Sol/S_ModularCurve_PhiGen_evalSymm_of_splits.lean` (895 lines) for the
  transpose half, `P2M/Sol/S_ModularCurve_swapBivar_eq_of_evalSymm.lean` (95 lines)
  for the converse, `P2M/Sol/S_ModularCurve_PhiGen_evalSymm_of_coeff_evalAtJ_eq.lean`
  (124 lines) and `P2M/Sol/S_ModularCurve_exists_phiIrreducible_evalSymm.lean` (62
  lines). The capstone's statement is the `Theorems/` wrapper of the last verbatim;
  the others contribute the engine and the symmetry argument, which the capstone
  proves.

  ## Assumptions

  `Defs/PhiGen`, `Defs/Polynomial`, `Defs/Fields`, `Defs/Jq`,
  `Defs/BivariateEval` (`ev`, `swap_eq_of_evalSymm`); T10's `PhiGenPoleBounds`;
  T11's `ModularPolynomialAssembly` (the assembly) and `PhiGenDescent`
  (`exists_phiGenDescends`); T9's `PhiGenIntegrality`; T8's
  `ModularForms/PhiGenDescends`; `ModularPolynomialIrreducible` (`phiIrreducible_of_splits`,
  `minpoly_jqN_eq`, `evalAtJGen_injective`, and the level embedding `qEmbedT` with
  `qEmbedT_injective`/`qEmbedT_jq`/`qEmbedT_jqN`, `qEmbedT_eq_coeffEmb_qExpand`, and the evaluation
  `evalAtJK` the splitting is stated with, `conj_succ_zero`).
  Checked by `spec/check_port.py` through the `spec-pin:` lines below; the module is
  not listed in `spec/old_check_stmts.py`.

  spec-pin: P2M/Sol/S_ModularCurve_PhiGen_evalSymm_of_splits.lean
  spec-pin: Theorems/Thm_ModularCurve_exists_phiIrreducible_evalSymm.lean
  spec-pin: Theorems/Thm_ModularCurve_swapBivar_eq_of_evalSymm.lean
  spec-pin: Theorems/Thm_ModularCurve_swapBivar_monic_of_coeff_bounds.lean
-/

-- Body retired: this module's content now lives in
-- `FLTForHuman.ModularCurve.ModularEquation.Existence`.
