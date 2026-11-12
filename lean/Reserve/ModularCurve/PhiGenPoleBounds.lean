/-
  T10 — the pole bounds, the second half of the cone's (b).

  The candidate product `phiProd ℓ (conj ℓ ζ)` is `∏_i (Y - j(ζ ^ b q ^ a))`. Its
  degree-`0` coefficient has a pole of order exactly `ℓ * ℓ + ℓ` at `q = 0`, with
  residue `1` (`phiProd_conj_coeff_zero_lead`), and every non-constant
  coefficient is bounded by the same order (`phiProd_conj_coeff_eq_zero_of_le`).
  Together with T9's integrality (`FLTForHuman/ModularCurve/PhiGenIntegrality.lean`,
  the first half of (b)) this makes the descended family `c` a degree-`(ℓ + 1)`
  integer datum of pole order `≤ ℓ + 1` — what (d) assembles.

  ## The shared prelude

  The `TPoleOrderLE` closure this module consumes (`.mono`, `.zero`, `.one`,
  `.neg`, `.add`, `.mul`, `.qTwist`, `.qExpand`, `of_jSimplePole`, the conjugate
  bounds and the coefficient bounds) is **not** written here: it is public in
  `Defs/PhiGen.lean`, because the pin copies it into six files and T11's 328 block
  imports it too. This module is the distinctive part only: the leading-coefficient
  computation of the product and the sharp pole bound for `k ≠ 0`.

  ## Source

  FLT `anthropics/fermats-last-theorem@aa2d8b3`:
  `P2M/Sol/S_ModularCurve_PhiGen_phiProd_conj_coeff_eq_zero_of_le.lean` (391
  lines; its twin `…_phiProd_conj_coeff_zero_lead.lean` is a byte-equivalent copy
  with the exported name flipped). The two public statements are verbatim from
  their `Theorems/` wrappers. The pin's ~180-line `TPoleOrderLE` prelude is not
  ported here (see above).

  ## Assumptions

  `LaurentSeries`, `HahnSeries`, `Polynomial`, `Finset`/`Fin` are mathlib's;
  `TPoleOrderLE`, `JSimplePole`, `phiProd`, `conj`, `conj_zero`, `conj_succ`,
  `jSimplePole_jqK` and the coefficient/order lemmas are the port's
  `Defs/PhiGen`; `qExpand`, `coeffEmb`, `qTwist` are the port's
  `Defs/Laurent`/`Defs/Twist`; `jq`, `coeff_jq_neg_one` the port's `Defs/Jq`.
  Wired here, not in the frozen registry: the module left `PORT_FILES`
  (`spec/old_check_stmts.py`) on 2026-11-06 and carries its own `spec-pin:` wire.

  spec-pin: Theorems/Thm_ModularCurve_PhiGen_phiProd_conj_coeff_eq_zero_of_le.lean
  spec-pin: Theorems/Thm_ModularCurve_PhiGen_phiProd_conj_coeff_zero_lead.lean
-/

-- Body retired: this module's content now lives in
-- `FLTForHuman.ModularCurve.ModularEquation.Support.PoleBounds`.
