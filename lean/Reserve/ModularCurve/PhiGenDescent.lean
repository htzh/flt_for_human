/-
  T11 — piece (a): the coefficients of the conjugate product descend to `ℚ((q))`.

  `PhiGenDescends ℓ ζ c` records that each `X`-coefficient of
  `phiProd ℓ (conj ℓ ζ)` lies in the image of the level substitution
  `coeffEmb K ∘ qExpand ℚ ℓ`; this module *produces* such a family `c`, from the
  two invariances of the product:

  * the nome twist `q ↦ ζ q` cycles the `ℓ` finite-slope roots and fixes the
    extra root `j(q ^ (ℓ * ℓ))`, so every coefficient is twist-fixed — hence lies
    in the range of `qExpand ℚ ℓ` (its support collapses onto multiples of `ℓ`);
  * every `σ : K ≃ₐ[ℚ] K` permutes the roots `ζ ^ b`, so every coefficient is
    Galois-fixed — hence lies in the range of `coeffEmb K`.

  Intersecting the two ranges (`mem_range_coeffEmb_qExpand_of_mem_inter`) gives
  the descent. This is base/006 §6.2 verbatim; no analysis is involved.

  ## Source

  FLT `anthropics/fermats-last-theorem@aa2d8b3`:
  `P2M/Sol/S_ModularCurve_PhiGen_exists_phiGenDescends.lean` (315 lines). The pin
  keeps `exists_phiGenDescends` `private` and exposes it through its wrapper
  `Theorems/Thm_ModularCurve_PhiGen_exists_phiGenDescends.lean`; the port's one
  public statement is that wrapper verbatim. Every helper is `private`, because
  the module's surface is the single export (the pin makes most of them public,
  but nothing else consumes them).

  ## Assumptions

  `qExpand`, `qExpand_coeff_mul`, `qExpand_coeff_of_not_dvd`, `qExpand_qExpand`,
  `coeffMap`, `coeffMap_coeff`, `coeffEmb`, `coeffEmb_coeff`, `coeffMap_coeffEmb`,
  `coeffMap_qExpand` are the port's `Defs/Laurent`; `qTwist`, `qTwist_coeff`,
  `qTwist_one_apply`, `qTwist_qTwist`, `qTwist_qExpand`, `coeffMap_qTwist` the port's
  `Defs/Twist`;
  `jq`, `jqN` the port's `Defs/Jq`; `conj`, `conj_zero`, `conj_succ`, `phiProd`,
  `PhiGenDescends` the port's `Defs/PhiGen`. `IsGalois`/`FiniteDimensional` and
  `IsPrimitiveRoot` are mathlib's.
  Wired here, not in the frozen registry: the module left `PORT_FILES`
  (`spec/old_check_stmts.py`) on 2026-11-06 and carries its own `spec-pin:` wire.

  spec-pin: Theorems/Thm_ModularCurve_PhiGen_exists_phiGenDescends.lean
-/

-- Body retired: this module's content now lives in
-- `FLTForHuman.ModularCurve.ModularEquation.Construction`.
