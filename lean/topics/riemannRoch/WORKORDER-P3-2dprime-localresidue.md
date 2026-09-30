# Work order — P3.2d′: the generic local residue calculus (`LocalResidueCalculus.lean`)

**Status: ready to dispatch.** Row 2's one generic block with its own natural
subject home (human decision, 2026-09-30: it is large enough — 1,244 pin lines /
38 declarations — and generic over `Place`, so it must not live inside the ℙ¹ core).
**Boilerplate, build discipline, checker-wiring mechanics and the report shape are
as [WORKORDER-P3-2b-p1core-1.md](WORKORDER-P3-2b-p1core-1.md) §4–§7 — read that
order first and follow it verbatim; this order states only what differs.** Loop:
[WORKFLOW.md](WORKFLOW.md); a parallel `AUDIT-mathlib-p3-2dprime.md` is dispatched
with this order.

Baseline: checker **3422 identical / 0 mismatched / 0 missing / 30 own-proof**
(3452 checked); `Defs/P1ResidueCore.lean` (chunks 1–2) green.

## 0. Scope — ONE NEW MODULE

`FLTForHuman/AlgebraicCurve/Defs/LocalResidueCalculus.lean`, from the pin
`P2M/Sol/S_AlgebraicCurve_Place_CanonicalLocalResidueDataK_res_differentialCoeff_D_mul_pow_inv_eq_zero_of_surjective_algebraMap.lean`
(1,244 ln, 38 declarations) plus its `Theorems/Thm_*` wrapper. Measured
(`build/p32dprime_advise.log`): 39 target declarations, 7 substitutions / 192 ln,
no shared prelude → **≈1,050 written**.

This is the **generic** local-residue calculus: for a `CanonicalLocalResidueDataK`
`R` at a place `v`, the residue of `differentialCoeff (D t) * (t^(n+1))⁻¹` vanishes
when `v.ord t = 1` and `algebraMap` to the residue field is surjective. Content:

- `mem_iff_ord_nonneg`, `D_pow_succ_inv`;
- `CanonicalLocalResidueDataK.res_differentialCoeff_D_of_mem_poleSubmodule`,
  `…_of_surj`;
- `gate_canonicalLocalResidueDataK_uniformizer_inv`;
- the whole `p0n22_cpf_*` family (`uniformizer_pow_mul_mem_cases`, `one_add_*`,
  `logDeriv_*`, `differentialCoeff_D_one_add_*`, `exists_residue_lift_decomp`,
  `exists_elementary_peel`, `exists_laurent_expansion_one`, `res_geom_core`,
  `res_logDeriv_*`, `row_integrand_eq_pow_mul_dlog`, `res_zpow_mul_logDeriv_cartier`,
  `res_pow_mul_dlog_unit`, `res_row_at_unit_mul_uniformizer`,
  `res_differentialCoeff_D_mul_pow_inv_of_surj`);
- the **headline** (pin `solution`, published as
  `CanonicalLocalResidueDataK.res_differentialCoeff_D_mul_pow_inv_eq_zero_of_surjective_algebraMap`),
  which splits by `ringChar K`: prime → `p0n22_cpf_res_differentialCoeff_D_mul_pow_inv_of_surj`,
  zero → `ModularCurve.MilneAvAg9bRd13T2CoordIndepChar3.ag9b13t_res_differentialCoeff_D_mul_pow_inv_of_surj_of_natCast_ne_zero`.

**Why this comes before the engine's chunk 3:** the master ℙ¹ file re-uses these
same names (`CanonicalLocalResidueDataK.res_differentialCoeff_D_of_surj`,
`D_pow_succ_inv`, `gate_canonicalLocalResidueDataK_uniformizer_inv`, …) in its later
part, so homing them here lets **3.2d import them instead of re-transcribing** —
the same dedup as 3.2b/c. `ag9b13t_*` is the char-0 engine already ported (check
`Defs/CanonicalLocalResidueInstanceV2.lean`; the `ag9b13t_res_differentialCoeff_D_mul_pow_inv_of_surj_of_natCast_ne_zero`
row may be a substitution or a small transcription).

**Explicitly not this set:** the ℙ¹ specializations
(`canonicalLocalResidueDataK_res_differentialCoeff_D_mul_pow_inv_ratFunc` /
`…_placeInfty`, pin master lines ~10734–10775) — those belong to the ℙ¹ core chunks
3.2d/e, which will import this module.

## 1. Deliverable

`FLTForHuman/AlgebraicCurve/Defs/LocalResidueCalculus.lean` — **new** file (no
cascade). Keep the pin namespaces (`AlgebraicCurve.Place`,
`CanonicalLocalResidueDataK.*`, `ModularCurve.*`). Drop the pin's `p2m_*`/`attribute`
scaffolding; replace `import Mathlib` with specific imports + port `Defs/` modules
(`Defs/{LocalResidue,CanonicalDivisor,Place,PushPull,CanonicalLocalResidueInstanceV2}`,
`Mathlib.RingTheory.Kaehler.Basic`, …). Module header names the pin file + pinned
URL and what it assumes.

## 2. Statements

Verbatim from the pin / the `Thm_*` wrapper; the wrapper is the interface copy for
the headline. Never change a statement to ease a proof.

## 3. Reuse

Re-check every row against `build/p32dprime_advise.log` §1 and the port before
writing. The 7 substitutions include `Place.mem_of_ord_nonneg` / `ord_nonneg_of_mem`
/ `mem_iff_ord_nonneg` (`Defs/PushPull.lean`), and `differentialCoeff_*`
(`Defs/LocalResidue.lean`). The `ag9b13t_*` char-0 engine is in
`Defs/CanonicalLocalResidueInstanceV2.lean` (phase 3.1b-ii) — check for an exact
substitute before transcribing. The parallel audit adds mathlib rows (likely
`Polynomial.divByMonic`, `LaurentSeries`, `Polynomial.X_pow_dvd_iff`,
`IsLocalRing.residue`); do not bank an unelaborated claim.

**Audit result (`AUDIT-mathlib-p3-2dprime.md`, landed — 9 SUBSTITUTE / 29
PROOF-INGREDIENT / **0 BESPOKE** over the 38 rows; first phase-3 block with no new
vocabulary).** Correction to this order's lead: the char-0 `ag9b13t_*` / `ag9b14c_*`
engine is **NOT in the port** (grep 0 over `FLTForHuman/`; `#check` errors) — only
the private `ag9b15u_*` block is. So rows 10/15 and the headline's `ringChar = 0`
branch are new. Substitutes: rows 1–3 → `Defs/PushPull.lean:43/60/69`; row 4
`ord_add_eq_min` and rows 11–14 (`ag9b15u_*`) → **private in
`Defs/P1ResidueCore.lean`** (131 / 1102 / 1122 / 1170 / 1210), so they cannot be
imported by a predecessor module — transcribed `private` here (see the debt below);
row 16 `gate_canonicalLocalResidueDataK_uniformizer_inv` → public
`P1ResidueCore.lean:1090`. Mathlib leaves: `Derivation.{leibniz_pow,leibniz_inv,leibniz,map_algebraMap,map_one_eq_zero}`,
`Valuation.map_add_of_distinct_val`, `geom_sum_mul`, the full char-p Frobenius API
(`add_pow_char`, `sum_pow_char`, `frobenius_def`, `CharP.cast_eq_zero_iff`, …) and
`CharP.char_is_prime_or_zero` + `charP_to_charZero` + `ringChar.charP` for the
headline split. Negatives: no `Polynomial.logDeriv` (only `Differential.logDeriv`,
needing a `Differential` instance — route option, not adopted); all `LaurentSeries`/
`Polynomial.divByMonic`/`PartialFractions` lemmas are off-path (the file has no
polynomial content; its "Cartier" rows are char-p Frobenius).

**Promotion debt (recorded, deferred to the 3.2 closeout refactor round).** Five
helpers are duplicated `private` in both `LocalResidueCalculus.lean` and
`P1ResidueCore.lean` — `Place.ord_add_eq_min` and the four
`ModularCurve.MilneAvAg9bRd15UnitNormalFormLaurentSeed.ag9b15u_*` — because the
generic module must precede the core's later chunks and so cannot import them.
Nothing imports either module yet, so the fix is cheap and cascade-free: make the
five public here and have `P1ResidueCore` import this module and drop its copies.

## 4. Build discipline, checker wiring, report shape

As 3.2b §4–§7. `SOURCES` += the `Thm_*` wrapper then the `S_*` file;
`PORT_FILES` += the new module. Append friction under `### Set 3.2d′`.

## 5. Stop-early / gaps

As 3.2b §6. Forward references to the ℙ¹ specializations are expected to be **none**
(this file is self-contained); if one appears, stop and report.
