/-
  Pins for the composite-level statements retired from
  `ModularPolynomialUniquenessIrreducible`.

  The statements are either deleted as trivial corollaries or live elsewhere:
  `toAdjoin_eq_minpoly_all` stays in `ModularPolynomialUniquenessIrreducible`, and
  `natDegree_coeff_le`/`evalSymm_of_prime` live in `ModularEquation.Split`. The
  existence statement `exists_phiIrreducible` is retired in favour of the canonical
  datum `dataMinpoly N` (`ModularPolynomialExistence`), whose existence wrapper is
  `nonempty_modularPolynomialData`. The empty body keeps the frontier from
  re-suggesting the ported content.

  spec-pin: Theorems/Thm_ModularCurve_ModularPolynomialData_eq_all.lean
  spec-pin: Theorems/Thm_ModularCurve_phiIrreducible_of_prime.lean
  spec-pin: Theorems/Thm_ModularCurve_phiIrreducible_all.lean
  spec-pin: P2M/Sol/S_ModularCurve_phiIrreducible_all.lean   -- comparable copy
  spec-pin: Theorems/Thm_ModularCurve_ModularPolynomialData_evalSymm_of_prime.lean
  spec-pin: Theorems/Thm_ModularCurve_ModularPolynomialData_natDegree_coeff_le.lean
  spec-pin: P2M/Sol/S_ModularCurve_ModularPolynomialData_natDegree_coeff_le.lean
  spec-pin: Theorems/Thm_ModularCurve_exists_phiIrreducible.lean
-/
