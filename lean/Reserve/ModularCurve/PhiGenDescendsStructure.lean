/-
  T11 — the 328 block: the shape of a descended family.

  `PhiGenDescends ℓ ζ c` says the `X`-coefficients of the conjugate product
  `phiProd ℓ (conj ℓ ζ)` descend to series `c k ∈ ℚ((q))` along the level
  substitution `q ↦ q ^ ℓ`. This module reads the *shape* of `c` off the product,
  using only that the product is monic of degree `ℓ + 1` and T10's pole bound:

  * `PhiGenDescends.c_top` — `c (ℓ + 1) = 1` (the top coefficient);
  * `PhiGenDescends.c_eq_zero` — `c k = 0` above degree `ℓ + 1`;
  * `PhiGenDescends.poleOrderLE` — every `c k` has pole order `≤ ℓ + 1`;
  * `PhiGenDescends.sum_mul_jqN_pow_eq_zero` — the modular-equation relation
    `∑_{k ≤ ℓ+1} c k * j(q^ℓ)^k = 0`;
  * `evalAtJ_injective` — `P ↦ P(j(q))` from `ℤ[X]` to `ℚ((q))` is injective.

  The last is stated over `ℤ` but is really the triangularity of `jq`'s pole; it
  is what makes the descent faithful, and T12's 895 block consumes this public
  copy instead of carrying the pin's private one.

  ## The shared prelude is T10's

  The pin's file opens with the ~170-line `TPoleOrderLE` prelude; the port does
  not repeat it. `Defs/PhiGen.lean` carries it public (FLT ships it in twelve
  `S_` files), and the `poleOrderLE` proof below reads
  `tPoleOrderLE_phiProd_coeff` / `tPoleOrderLE_coeffEmb_iff` /
  `tPoleOrderLE_of_qExpand` straight from there.

  ## Source

  FLT `anthropics/fermats-last-theorem@aa2d8b3`:
  `P2M/Sol/S_ModularCurve_PhiGen_PhiGenDescends_c_top.lean` (328 lines; the
  `c_eq_zero`/`poleOrderLE`/`sum_mul_jqN_pow_eq_zero`/`evalAtJ_injective` files
  are byte-equivalent copies). The five public statements are verbatim from their
  `Theorems/` wrappers.

  ## `evalAtJ_injective` by the mathlib route

  The pin proves it through a private 19-line `aeval_jq_eq_zero` (the `q ^ -d`
  coefficient reads off the leading coefficient). The port reuses the public
  `transcendental_jq` from `Defs/Jq.lean` via mathlib's
  `transcendental_iff_injective`, keeping only the six-line
  `evalAtJ_eq_aeval_map` bridge; the port's own `aeval_jq_eq_zero` stays public as
  the `Thm_ModularCurve_aeval_jq_eq_zero` interface. See the log for the spike.

  ## Assumptions

  `phiProd_monic`, `phiProd_natDegree`, `phiProd_eval_conj`, `conj_zero`,
  `conj_succ`, `PhiGenDescends`, `PoleOrderLE`/`TPoleOrderLE` and the prelude are
  the port's `Defs/PhiGen`; `coeffEmb`, `qExpand`, `coeffMap_qExpand`,
  `qExpand_qExpand` the port's `Defs/Laurent`; `jq`, `jqN`, `evalAtJ`,
  `transcendental_jq` the port's `Defs/Jq`.
  Wired here, not in the frozen registry: the module left `PORT_FILES`
  (`spec/old_check_stmts.py`) on 2026-11-06 and carries its own `spec-pin:` wire.

  spec-pin: Theorems/Thm_ModularCurve_PhiGen_PhiGenDescends_c_eq_zero.lean
  spec-pin: Theorems/Thm_ModularCurve_PhiGen_PhiGenDescends_c_top.lean
  spec-pin: Theorems/Thm_ModularCurve_PhiGen_PhiGenDescends_poleOrderLE.lean
  spec-pin: Theorems/Thm_ModularCurve_PhiGen_PhiGenDescends_sum_mul_jqN_pow_eq_zero.lean
  spec-pin: Theorems/Thm_ModularCurve_PhiGen_evalAtJ_injective.lean
-/

-- Body retired: this module's content now lives in
-- `FLTForHuman.ModularCurve.ModularEquation.Construction`.
