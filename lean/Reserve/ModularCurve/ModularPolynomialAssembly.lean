/-
  T11 — piece (d): assembling the modular-polynomial datum.

  With a descended family `c` in hand (`PhiGenDescends`, produced by
  `PhiGenDescendsStructure`'s interface and `PhiGen.exists_phiGenDescends`), the
  passage from a family of series to a genuine `ModularPolynomialData ℓ` is three
  steps, each an input already landed:

  1. `hmem : ∀ k, c k ∈ ℚ[jq]` (T8) gives `P k ∈ ℚ[X]` with `c k = P k (jq)`;
  2. `PhiGenDescends.poleOrderLE` bounds `deg (P k) ≤ ℓ + 1`;
  3. `hint : ∀ k, IntCoeffs (c k)` plus T9's `aeval_jq_intCoeffs_descent` forces
     `P k ∈ ℤ[X]` — this is `PhiGenDescends.exists_intPoly`.

  Then `Φ = ∑_{k ≤ ℓ+1} Q k (X) * Y^k` is the datum: `c_top` makes it monic,
  `c_eq_zero`/`hΦdeg` give degree `ℓ + 1 = ψ(ℓ)`, and
  `sum_mul_jqN_pow_eq_zero` is the vanishing at `j(q ^ ℓ)`.

  ## Source

  FLT `anthropics/fermats-last-theorem@aa2d8b3`:
  `P2M/Sol/S_ModularCurve_PhiGen_exists_modularPolynomialData_coeff_eq.lean` (191
  lines). The assembly is `private` in the pin and exposed through its wrapper,
  which the port statement is verbatim.

  ## Reuse

  The pin's private `coeff_aeval_jq_neg` is T9's public `Defs/Jq.lean` lemma, and
  the pin's private `evalAtJ_eq_aeval_map` is the public `Defs/Jq.lean` bridge
  (promoted by T12); both are imported rather than re-declared.

  ## Assumptions

  `evalAtJ`, `jq`, `jqN`, `coeff_aeval_jq_neg`, `dedekindPsi_prime` are the port's
  `Defs/Jq`; `PoleOrderLE`, `IntCoeffs`, `PhiGenDescends`, `conj`, `phiProd`,
  `ModularPolynomialData` the port's `Defs/PhiGen`/`Defs/Polynomial`;
  `aeval_jq_intCoeffs_descent` and `PhiGenDescends.intCoeffs` T9's
  `PhiGenIntegrality`; the five `PhiGenDescends.*`/`evalAtJ_injective` exports
  this topic's `PhiGenDescendsStructure`.
  Checked by `spec/check_port.py` through the `spec-pin:` lines below; the module is
  not listed in `spec/old_check_stmts.py`.

  spec-pin: Theorems/Thm_ModularCurve_PhiGen_exists_modularPolynomialData_coeff_eq.lean
-/

-- Body retired: this module's content now lives in
-- `FLTForHuman.ModularCurve.ModularEquation.Construction`.
