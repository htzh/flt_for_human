# Mathlib-first substitution audit — the phase-3.2d′ generic local-residue calculus (P3.2d′)

**Method:** `lean/porting-playbook.md` §2.2 (audit the route, mathlib first), after the
phase-1/2/3.1/3.2a/3.2b/3.2c templates [`AUDIT-mathlib.md`](AUDIT-mathlib.md),
[`AUDIT-mathlib-p2.md`](AUDIT-mathlib-p2.md),
[`AUDIT-mathlib-p3-1.md`](AUDIT-mathlib-p3-1.md),
[`AUDIT-mathlib-p3-2a.md`](AUDIT-mathlib-p3-2a.md),
[`AUDIT-mathlib-p3-2b.md`](AUDIT-mathlib-p3-2b.md) and
[`AUDIT-mathlib-p3-2c.md`](AUDIT-mathlib-p3-2c.md). Pin:
`anthropics/fermats-last-theorem@aa2d8b3` (read-only clone at
`~/proj/fermats-last-theorem`); port mathlib `v4.34.0`
(`lean/.lake/packages/mathlib`). Pre-port advice:
[`tools/deps/build/p32dprime_advise.log`](../../../tools/deps/build/p32dprime_advise.log)
(7 substitutions / 192 ln) and its machine-readable twin
[`p32dprime_advise.json`](../../../tools/deps/build/p32dprime_advise.json). Work order:
[`WORKORDER-P3-2dprime-localresidue.md`](WORKORDER-P3-2dprime-localresidue.md).

Source, the single pin `S_` file (1,244 ln, 38 declarations), plus its one-declaration
`Theorems/` wrapper (39 target declarations):

- [`P2M/Sol/S_AlgebraicCurve_Place_CanonicalLocalResidueDataK_res_differentialCoeff_D_mul_pow_inv_eq_zero_of_surjective_algebraMap.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_Place_CanonicalLocalResidueDataK_res_differentialCoeff_D_mul_pow_inv_eq_zero_of_surjective_algebraMap.lean)
  (rows 1–38),
- [`Theorems/Thm_AlgebraicCurve_Place_CanonicalLocalResidueDataK_res_differentialCoeff_D_mul_pow_inv_eq_zero_of_surjective_algebraMap.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_AlgebraicCurve_Place_CanonicalLocalResidueDataK_res_differentialCoeff_D_mul_pow_inv_eq_zero_of_surjective_algebraMap.lean)
  (the interface copy of the headline, `#check`ed as probe H4).

**Class convention** (unchanged from phases 1–3.2c). SUBSTITUTE = the port can import an
existing declaration instead of proving the row: an already-landed port lemma or a
mathlib constant whose *type* is the pin's, or a pin `def`/`abbrev`/instance whose body is
`rfl`-equal to a mathlib/port term. A statement that differs from the port copy only by
binder spelling or by a `_root_.`-qualified pin header is counted SUBSTITUTE with that
difference recorded. PROOF-INGREDIENT = the statement is bespoke (it mentions pin
vocabulary) but the proof is a short assembly of named mathlib/port lemmas. BESPOKE = a
definition/structure/class/`Prop` introducing new vocabulary, or an instance with no
mathlib/port counterpart; these are the recorded negatives and the real work.

**Scratch evidence:** `lean/ScratchAuditP32dprime.lean` (gitignored, 205 ln), compiled
from `lean/` with

```bash
timeout 120 lake env lean -DmaxHeartbeats=4000000 -DautoImplicit=false ScratchAuditP32dprime.lean
```

**final run clean, exit 0, 4.5 s wall** (87 resolving `#check`s, no errors; one
`linter.style.haveILetI` note, §10). The probe ledger:

- **P** — the port-substitute `#check`s (§A of the scratch): every substitute row
  tabulated below, plus the engine vocabulary the new rows consume
  (`CanonicalLocalResidueDataK.{res_higherPoleMonomial,
  res_algebraMap_mul_uniformizer_pow_inv, res_eq_zero_of_ord_nonneg}`,
  `Place.{differentialCoeff_unique, differentialCoeff_smul, differentialCoeff_dCoord,
  differentialCoeff_zero, differentialCoeff_smul_dCoord, differentialCoeff_ne_zero,
  laurentTail_remainder_mem_poleSubmodule, exists_mem_poleSubmodule,
  coe_poleSubmodule_zero, uniformizer_pow_ne_zero, ord_uniformizer_pow, ord_mul,
  ord_inv, ord_zpow, exists_unit_mul_zpow}`) and the second copy of the ord interface
  (`Place.ord_nonneg_of_mem_vs`, `Place.mem_vs_of_ord_nonneg`).
- **M** — the mathlib `#check` ledger (§B): `Polynomial.{X_pow_dvd_iff, X_dvd_iff,
  divByMonic, modByMonic, divByMonic_eq_zero_iff, modByMonic_eq_zero_iff_dvd, derivative,
  mul_prod_pow_inverse_eq_quo_add_sum_rem_mul_pow_inverse}`, `LaurentSeries`,
  `HahnSeries`, `Differential.{logDeriv, logDeriv_mul, logDeriv_div, logDeriv_pow}`,
  `IsLocalRing.{residue, ResidueField, residue_eq_zero_iff, ResidueField.algebraMap_eq,
  mem_maximalIdeal}`, `mem_nonunits_iff`, `Valuation.map_add_of_distinct_val`,
  `WithZero.log_le_log`, `ValuationSubring.mem_or_inv_mem`,
  `IsDiscreteValuationRing.{exists_irreducible, eq_unit_mul_pow_irreducible}`,
  `Derivation.{leibniz, leibniz_pow, leibniz_inv, leibniz_div, leibniz_of_mul_eq_one,
  map_algebraMap, map_one_eq_zero, map_aeval}`, `geom_sum_mul`, `add_pow_char`,
  `add_pow_char_pow`, `sum_pow_char`, `neg_one_pow_char`, `frobenius_def`,
  `charP_of_injective_ringHom`, `charP_of_injective_algebraMap`, `CharP.cast_eq_zero_iff`,
  `CharP.char_is_prime_or_zero`, `CharP.charP_to_charZero`, `ringChar.charP`,
  `Nat.cast_smul_eq_nsmul`, `Algebra.algebraMap_eq_smul_one`,
  `IsScalarTower.algebraMap_apply`, `mul_inv_cancel₀`, `inv_mul_cancel_left₀`, `map_inv₀`,
  `zpow_sub_one₀`, `zpow_mul`, `smul_pow`, `Finset.{sum_eq_single_of_mem, sum_range_succ,
  sum_insert}`, `Int.natCast_ne_zero`, `Int.natCast_ne_zero_iff_pos`.
- **H** — compile-checked prototypes: `H1` the pin's `D_pow_succ_inv` body verbatim
  (row 5); `H2` `differentialCoeff_add''` in two lines from the port's
  `differentialCoeff_unique` (row 6); `H3` the pin's inherited-field dot notation
  (`R.res_of_mem`, `R.res_simplePole`, `R.res_higherPoleMonomial`) resolving on the
  port's `CanonicalLocalResidueDataK`; `H4` the headline's `ringChar` split
  (`CharP.char_is_prime_or_zero`, `ringChar.charP`, `CharP.charP_to_charZero`).

## 1. Summary — class counts

| block (rows) | SUBSTITUTE | PROOF-INGREDIENT | BESPOKE | rows |
|---|---:|---:|---:|---:|
| ord prelude (1–4) | 4 | 0 | 0 | 4 |
| differential prelude (5–7) | 0 | 3 | 0 | 3 |
| `res_differentialCoeff_D` engine (8–9) | 0 | 2 | 0 | 2 |
| `ag9b13t`/`ag9b15u`/`ag9b14c` blocks (10–15) | 4 | 2 | 0 | 6 |
| gate + char-free `p0n22` toolkit (16–31) | 1 | 15 | 0 | 16 |
| char-p Cartier + row + headline (32–38) | 0 | 7 | 0 | 7 |
| **total** | **9** | **29** | **0** | **38** |

**Headline.** This is a *calculus* file: all 38 declarations are theorems, there is no
`def`/`structure`/`class`/instance and no new vocabulary, so the BESPOKE count is **zero**
— a first for this phase. A quarter of the rows import outright (9), and the other 29 are
named-lemma assemblies. The genuine work is one connected story — the `p0n22_cpf_*`
characteristic-free toolkit (rows 17–31), its characteristic-`p` Cartier refinement
(rows 32–36), the prime-characteristic engine (row 37) and the headline's `ringChar` split
(row 38) — plus the five-lemma differential prelude (rows 5–7) and the two `res` engine
lemmas (rows 8–9). Three reuse wins dominate the route: `Defs/PushPull.lean` already
carries the ord interface, `Defs/P1ResidueCore.lean` already carries the four `ag9b15u_*`
lemmas and `ord_add_eq_min` (as `private`), and mathlib's `Derivation` API supplies every
differential-calculus step.

**Correction 1 — the brief's "already-ported char-0 engine" is a false positive.**
`Defs/CanonicalLocalResidueInstanceV2.lean` does **not** contain
`MilneAvAg9bRd13T2CoordIndepChar3.ag9b13t_res_differentialCoeff_D_mul_pow_inv_of_surj_of_natCast_ne_zero`
(row 10) or `MilneAvAg9bRd14CubeRowCartierSliceStart.ag9b14c_…` (row 15). Greps over
`FLTForHuman/`, `Reserve/` and `spec/` for `ag9b13t`, `ag9b14c`, `MilneAvAg9bRd13T2`,
`MilneAvAg9bRd14` return **nothing**, and `#check` errors on both names. Only the sibling
`MilneAvAg9bRd15UnitNormalFormLaurentSeed.ag9b15u_*` block (rows 11–14) is ported, in
`Defs/P1ResidueCore.lean:1102–1227`, and it is **private**. So the characteristic-zero
branch of `solution` (the `ringChar K = 0` case) and the `ag9b14c` monomial-vanishing row
must be transcribed, not imported. The same grep establishes that `D_pow_succ_inv`,
`Place.differentialCoeff_add''`, `Place.differentialCoeff_D_uniformizer_pow_inv`,
`CanonicalLocalResidueDataK.res_differentialCoeff_D_of_mem_poleSubmodule`,
`…_of_surj` and the whole `p0n22_cpf_*` family are new.

**Correction 2 — the substitution count is 9, not 7.** The advice log's §1 counts seven
(three public ord lemmas are two of those, five port-private). The checker additionally
accepts two *binder-spelling* matches the log lists only in §3:
`mem_iff_ord_nonneg` (`Defs/PushPull.lean:69`) and
`gate_canonicalLocalResidueDataK_uniformizer_inv` (`Defs/P1ResidueCore.lean:1090`,
public). All nine are probed in §P and span-diffed in §8.

**Correction 3 — the file is not self-contained in one respect: five port-private
declarations are load-bearing.** `Place.ord_add_eq_min` (row 4) and the four `ag9b15u_*`
lemmas (rows 11–14) are `private` in `Defs/P1ResidueCore.lean`. The new generic module
cannot import them, so it must either **promote** them (playbook §2.4, §5) or consume them
inside that module — and the generic home is the right one, since the master ℙ¹ file
re-uses the names too (Correction 4). Promotion is the route the audit recommends; the
span diffs in §8 show the statements are identical up to the pin's `_root_.` prefix.

**Correction 4 — the dedup is real and quantified.** The master ℙ¹ file
`P2M/Sol/S_AlgebraicCurve_RationalFunctionField_trace_localResidue_placeInfty_X_pow_eq_zero.lean`
mentions `p0n22_cpf_` **63** times, `ag9b15u_` **13**, `D_pow_succ_inv` **4**,
`gate_canonicalLocalResidueDataK_uniformizer_inv` **4**, `res_differentialCoeff_D_of_`
**5**, `ag9b14c_` **6**, `ag9b13t_` **3**, `differentialCoeff_add` **9**,
`differentialCoeff_D_uniformizer_pow_inv` **3**, `ord_add_eq_min` **3** and
`mem_iff_ord_nonneg` **7**. Homing the block here is what lets 3.2d/e import instead of
re-transcribing the ~1,050 content lines.

**Correction 5 — the headline is `solution`, published under the wrapper's dotted name.**
Row 38 is the pin's top-level `solution`; the interface the checker compares is
`AlgebraicCurve.Place.CanonicalLocalResidueDataK.res_differentialCoeff_D_mul_pow_inv_eq_zero_of_surjective_algebraMap`,
whose statement is the pin's `solution` verbatim and whose body is
`p2m_exact_reverting …solution`. The statement is

$$R.\mathrm{res}\big(v.\mathrm{differentialCoeff}(D_{F/K}\\,t)\cdot (t^{n+1})^{-1}\big)=0,\qquad v.\mathrm{ord}\\,t=1,\ n\ge 1.$$

Rows 1–37 are the `S_` file's own declarations, so the deliverable exposes 38 statements
plus one alias.

## 2. The ord prelude (rows 1–4)

All four are import-only; the three public copies are phase-3.2b output.

| row | pin decl (line) | class | mathlib / port name | evidence |
|---:|---|---|---|---|
| 1 | `_root_.AlgebraicCurve.Place.ord_nonneg_of_mem` (32, priv) | SUBSTITUTE | `AlgebraicCurve.Place.ord_nonneg_of_mem` (`Defs/PushPull.lean:43`, public) | probe P; second public copy `Place.ord_nonneg_of_mem_vs` (`Canonical/WeilDifferential.lean:57`); body is `IsDiscreteValuationRing.eq_unit_mul_pow_irreducible` + `ord_unit_smul_zpow` |
| 2 | `_root_.AlgebraicCurve.Place.mem_of_ord_nonneg` (48, priv) | SUBSTITUTE | `Place.mem_of_ord_nonneg` (`PushPull.lean:60`) | probe P; advice log §3 binder-spelling (the pin is under section variables) |
| 3 | `Place.mem_iff_ord_nonneg` (57, pub) | SUBSTITUTE | `Place.mem_iff_ord_nonneg` (`PushPull.lean:69`) | probe P; `⟨v.ord_nonneg_of_mem, v.mem_of_ord_nonneg hf⟩` is the port body |
| 4 | `_root_.AlgebraicCurve.Place.ord_add_eq_min` (61, priv) | SUBSTITUTE (promote) | `Place.ord_add_eq_min` (`Defs/P1ResidueCore.lean:131`, **private**) | span-diff §8.1: body identical; probe P verifies the surrounding ord API. Called by rows 19 and 33, so it must be visible |

Mathlib path for all four: `Valuation.map_add_of_distinct_val`
(`Mathlib/RingTheory/Valuation/Basic.lean:291`), `WithZero.log_le_log`,
`IsDiscreteValuationRing.{exists_irreducible, eq_unit_mul_pow_irreducible}`
(`RingTheory/DiscreteValuationRing/Basic.lean:105,338`). The 3.2b audit called row 4
"PROOF-INGREDIENT, no port copy"; the port has since written the copy, so it is now a
SUBSTITUTE — a dedup win the 3.2b record predates.

## 3. The differential prelude (rows 5–7)

No port copy exists for any of the three; each is a short mathlib assembly. Probe H1
compiles row 5's pin body unchanged.

| row | pin decl (line) | class | mathlib / port name | evidence |
|---:|---|---|---|---|
| 5 | `D_pow_succ_inv` (92, pub) | PROOF-INGREDIENT | `Derivation.leibniz_pow` (`RingTheory/Derivation/Basic.lean:139`), `Derivation.leibniz_inv` (`:494`), `Nat.add_sub_cancel`, `Nat.cast_smul_eq_nsmul` (`Algebra/Module/NatInt.lean:114`), `inv_pow`, `smul_smul` | probe M + H1; the pin's `rw` chain transcribes verbatim |
| 6 | `_root_.AlgebraicCurve.Place.differentialCoeff_add''` (107, priv) | PROOF-INGREDIENT | `Place.differentialCoeff_unique` (`Defs/CanonicalDivisor.lean:85`), `differentialCoeff_smul_dCoord` (`:80`), `add_smul` | probe H2; two lines. `differentialCoeff` is a `Classical.choose` `def` (`CanonicalDivisor.lean:70`), not a `LinearMap`, so no `map_add` exists — the uniqueness lemma is the route |
| 7 | `_root_.AlgebraicCurve.Place.differentialCoeff_D_uniformizer_pow_inv` (113, priv) | PROOF-INGREDIENT | row 5, `Place.differentialCoeff_smul` (`:103`), `differentialCoeff_dCoord` (`:94`), `Place.dCoord` (`:57`) | probe P; two lines; consumed by rows 8, 10 |

## 4. The `res_differentialCoeff_D` engine (rows 8–9)

| row | pin decl (line) | class | mathlib / port name | evidence |
|---:|---|---|---|---|
| 8 | `CanonicalLocalResidueDataK.res_differentialCoeff_D_of_mem_poleSubmodule` (131, pub) | PROOF-INGREDIENT | `Place.{mem_poleSubmodule, laurentTailCoeff, laurentTail_remainder_mem_poleSubmodule, coe_algebraMap}`, `CanonicalLocalResidueDataK.res_algebraMap_mul_uniformizer_pow_inv` (`Defs/CanonicalLocalResidueInstanceV2.lean:340`), `LocalResidueData.res_of_mem` (`Defs/LocalResidue.lean:34`), rows 4/6, `IsScalarTower.algebraMap_apply` (`Algebra/Algebra/Tower.lean:131`), `IsLocalRing.ResidueField.algebraMap_eq`, `Derivation.{leibniz, map_algebraMap}` | no port copy; induction on the pole depth `N`; probe M verifies every mathlib leaf |
| 9 | `CanonicalLocalResidueDataK.res_differentialCoeff_D_of_surj` (175, pub) | PROOF-INGREDIENT | row 8 + `Place.exists_mem_poleSubmodule` (`CanonicalLocalResidueInstanceV2.lean:317`) | one line |

`res_algebraMap_mul_uniformizer_pow_inv` is a one-line `(Algebra.smul_def c _).symm`
already landed in 3.1b, so row 8 is glue over the engine, not new mathematics.

## 5. The `ag9b13t` / `ag9b15u` / `ag9b14c` blocks (rows 10–15)

Rows 11–14 are the only four rows in this file with a port copy, and that copy is
`private`. Rows 10 and 15 are new — see Correction 1.

| row | pin decl (line) | class | mathlib / port name | evidence |
|---:|---|---|---|---|
| 10 | `MilneAvAg9bRd13T2CoordIndepChar3.ag9b13t_res_differentialCoeff_D_mul_pow_inv_of_surj_of_natCast_ne_zero` (196, priv) | PROOF-INGREDIENT | rows 5/8, `Place.differentialCoeff_smul`, `map_natCast`, `map_ne_zero_iff`, `inv_mul_cancel_left₀`, `Algebra.smul_def`, `map_smul` | **no port copy**; the brief's "char-0 engine already ported" is false (grep 0, `#check` errors). Consumed by rows 36 and 38 |
| 11 | `MilneAvAg9bRd15UnitNormalFormLaurentSeed.ag9b15u_eq_zero_or_one_le_ord_of_residue_eq_zero` (240, priv) | SUBSTITUTE | `Defs/P1ResidueCore.lean:1102` (**private**) | span-diff §8.2 identical; probe P verifies the ord/residue leaves |
| 12 | `…ag9b15u_exists_unit_normal_form_of_surj` (261, priv) | SUBSTITUTE | `Defs/P1ResidueCore.lean:1122` (**private**) | span-diff §8.3 identical |
| 13 | `…ag9b15u_exists_K_truncation_of_mem_poleSubmodule` (310, priv) | SUBSTITUTE | `Defs/P1ResidueCore.lean:1170` (**private**) | span-diff §8.4 identical except the port's `if_pos`/`if_neg` → `ite_eq_left`/`ite_eq_right` (v4.34 drift, §10) |
| 14 | `…ag9b15u_differentialCoeff_D_unit_mul_uniformizer` (351, priv) | SUBSTITUTE | `Defs/P1ResidueCore.lean:1210` (**private**) | span-diff §8.5 identical |
| 15 | `MilneAvAg9bRd14CubeRowCartierSliceStart.ag9b14c_res_uniformizer_zpow_eq_zero_of_ne_neg_one` (376, priv) | PROOF-INGREDIENT | `CanonicalLocalResidueDataK.{res_of_mem, res_higherPoleMonomial}`, `Place.{mem_of_ord_nonneg, ord_zpow, ord_uniformizer}` | **no port copy**; 13 lines; consumed by rows 28 and 35 |

Rows 11, 12, 13, 14 and 15 are referenced from the `p0n22` bodies at pin lines 549, 606,
999, 857 and 754/769 (row 15), so once promoted they are the file's internal interface.

## 6. The gate and the characteristic-free `p0n22` toolkit (rows 16–31)

The gate is import-only; the fifteen `p0n22_cpf_*` rows are new named assemblies.

| row | pin decl (line) | class | mathlib / port name | evidence |
|---:|---|---|---|---|
| 16 | `gate_canonicalLocalResidueDataK_uniformizer_inv` (399, pub) | SUBSTITUTE | `AlgebraicCurve.gate_canonicalLocalResidueDataK_uniformizer_inv` (`Defs/P1ResidueCore.lean:1090`, public) | probe P / H3; advise log §3 binder-spelling; the port body is `gate_localResidueData_uniformizer_inv v R.toLocalResidueData` (`Defs/LocalResidue.lean:108`) |
| 17 | `p0n22_cpf_uniformizer_pow_mul_mem_cases` (412) | PROOF-INGREDIENT | `Place.{ord_mul, ord_uniformizer_pow, uniformizer_pow_ne_zero}`, row 1, `omega` | no port copy |
| 18 | `p0n22_cpf_one_add_ne_zero` (423) | PROOF-INGREDIENT | `Place.{ord_mul, ord_one, ord_zero, ord_inv}`, `neg_ne_zero` | no port copy |
| 19 | `p0n22_cpf_ord_one_add_eq_zero` (439) | PROOF-INGREDIENT | row 4 (`ord_add_eq_min`), `Place.ord_one` | no port copy |
| 20 | `p0n22_cpf_one_add_inv_mem` (454) | PROOF-INGREDIENT | rows 18/19, `Place.{mem_of_ord_nonneg, ord_inv}` | no port copy |
| 21 | `p0n22_cpf_logDeriv_mul` (461) | PROOF-INGREDIENT | `Derivation.leibniz`, row 6, `Place.differentialCoeff_smul`, `linear_combination` | no port copy; mathlib's `Differential.logDeriv_mul` (`FieldTheory/Differential/Basic.lean:39`) is the general form — route option R4 |
| 22 | `p0n22_cpf_logDeriv_mem` (480) | PROOF-INGREDIENT | rows 2/20, `Place.ord_inv`, `mul_mem` | no port copy |
| 23 | `p0n22_cpf_differentialCoeff_D_one_add_algebraMap_mul_pow` (494) | PROOF-INGREDIENT | `Place.differentialCoeff_unique`, `Derivation.{leibniz, leibniz_pow, map_algebraMap, map_one_eq_zero}`, `Nat.cast_smul_eq_nsmul` | no port copy |
| 24 | `p0n22_cpf_differentialCoeff_D_one_add_pow_mul` (509) | PROOF-INGREDIENT | idem + `Place.differentialCoeff_smul_dCoord` | no port copy |
| 25 | `p0n22_cpf_exists_residue_lift_decomp` (528) | PROOF-INGREDIENT | row 11 (port-private), `IsLocalRing.{residue, residue_eq_zero_iff, mem_maximalIdeal}`, `mem_nonunits_iff`, `IsScalarTower.algebraMap_apply`, `IsLocalRing.ResidueField.algebraMap_eq`, rows 2/20 | no port copy |
| 26 | `p0n22_cpf_exists_elementary_peel` (565) | PROOF-INGREDIENT | rows 17/18/20/25, `linear_combination` | no port copy |
| 27 | `p0n22_cpf_exists_laurent_expansion_one` (597) | PROOF-INGREDIENT | row 13 (port-private `ag9b15u_exists_K_truncation…`), row 25, `Finset.{sum_insert, sum_image, sum_congr}`, `zpow_neg`, `zpow_natCast` | no port copy; the pin calls the port-private lemma by its full name at line 606, so promotion is **required**, not optional |
| 28 | `p0n22_cpf_res_geom_core` (632) | PROOF-INGREDIENT | `geom_sum_mul` (`Algebra/Ring/GeomSum.lean:232`), `CanonicalLocalResidueDataK.{res_of_mem, res_higherPoleMonomial}`, row 15, row 16, `Finset.sum_eq_single_of_mem`, `Algebra.algebraMap_eq_smul_one`, `zpow_add₀`, `map_sum` | no port copy; the largest row (~140 pin ln) but pure named assembly over the geometric series |
| 29 | `p0n22_cpf_res_logDeriv_elementary` (772) | PROOF-INGREDIENT | rows 23/28, `Algebra.smul_def`, `map_smul` | no port copy |
| 30 | `p0n22_cpf_res_logDeriv_highLevel_vanish` (800) | PROOF-INGREDIENT | rows 17/20/24, `CanonicalLocalResidueDataK.res_of_mem`, `linear_combination` | no port copy |
| 31 | `p0n22_cpf_row_integrand_eq_pow_mul_dlog` (846) | PROOF-INGREDIENT | row 14 (port-private `ag9b15u_differentialCoeff_D_unit_mul_uniformizer`), `linear_combination` | no port copy |

## 7. The characteristic-`p` Cartier block and the headline (rows 32–38)

The Cartier identity here is the characteristic-`p` Frobenius fact that the residue of the
log-derivative row is a `p`-th power — not the partial-fraction identity (§11.5).

| row | pin decl (line) | class | mathlib / port name | evidence |
|---:|---|---|---|---|
| 32 | `p0n22_cpf_res_logDeriv_elementary_cartier` (874) | PROOF-INGREDIENT | row 29, `charP_of_injective_ringHom` (`Algebra/CharP/Algebra.lean:56`), `CharP.cast_eq_zero_iff` (`Algebra/CharP/Defs.lean:47`), `neg_one_pow_char` (`Algebra/CharP/Lemmas.lean:231`), `frobenius_def` (`Algebra/CharP/Frobenius.lean:32`), `mul_pow`, `zero_pow` | no port copy |
| 33 | `p0n22_cpf_res_logDeriv_principalUnit_cartier_aux` (926) | PROOF-INGREDIENT | rows 17/18/21/26/30, `add_pow_char` (`Algebra/CharP/Lemmas.lean:176`), induction on the peel depth | no port copy |
| 34 | `p0n22_cpf_res_zpow_mul_logDeriv_cartier` (971) | PROOF-INGREDIENT | rows 22/26/33, `CanonicalLocalResidueDataK.res_of_mem`, `zpow_neg`, `zpow_natCast` | no port copy |
| 35 | `p0n22_cpf_res_pow_mul_dlog_unit` (1035) | PROOF-INGREDIENT | rows 16/22/27/28/34, `charP_of_injective_algebraMap` (`Algebra/CharP/Algebra.lean:62`), `add_pow_char`, `sum_pow_char` (`Algebra/CharP/Lemmas.lean:340`), `smul_pow` (`Algebra/Group/Action/Defs.lean:489`), `zpow_mul`, `zpow_sub_one₀` | no port copy |
| 36 | `p0n22_cpf_res_row_at_unit_mul_uniformizer` (1148) | PROOF-INGREDIENT | rows 10/31/35, `Nat.strong_induction_on`, `CharP.cast_eq_zero_iff`, `zero_pow`, `inv_pow` | no port copy; strong induction on `n`, with the `p ∣ n` case reduced to row 35 and the `p ∤ n` case to row 10 |
| 37 | `p0n22_cpf_res_differentialCoeff_D_mul_pow_inv_of_surj` (1197) | PROOF-INGREDIENT | row 36, `Place.{ord_mul, ord_inv, ord_uniformizer}`, `mul_ne_zero` | no port copy; the prime-characteristic engine |
| 38 | `solution` (1230, pub) | PROOF-INGREDIENT | `CharP.char_is_prime_or_zero` (`Algebra/CharP/Defs.lean:245`), `ringChar.charP` (`:160`), `CharP.charP_to_charZero` (`:108`), rows 10/37 | no port copy; probe H4 checks the `ringChar` split. Published by the `Theorems/` wrapper as `AlgebraicCurve.Place.CanonicalLocalResidueDataK.res_differentialCoeff_D_mul_pow_inv_eq_zero_of_surjective_algebraMap` |

## 8. Reuse wins, with probe and diff evidence

### 8.1 The ord interface is phase-3.2b output (rows 1–3)

`Defs/PushPull.lean:43/60/69` carries all three at the pin statements; probe P resolves
them, and the 3.2b checker already counts them. Import them; do not re-land. There is a
second public copy of row 1 in `Canonical/WeilDifferential.lean:57`
(`Place.ord_nonneg_of_mem_vs`) — the port's own dedup debt, not a reason to transcribe a
third.

### 8.2 `Defs/P1ResidueCore.lean` already carries the `ag9b15u_*` block and `ord_add_eq_min` (rows 4, 11–14)

Span diffs (pin vs port, `diff <(sed -n 'a,bp' pin) <(sed -n 'c,dp' port)`):

- `ord_add_eq_min` (pin 61–88 vs port 131–158): only the header differs
  (`private theorem _root_.AlgebraicCurve.Place.ord_add_eq_min …` vs
  `private theorem ord_add_eq_min …`); bodies byte-identical.
- `ag9b15u_eq_zero_or_one_le_ord_of_residue_eq_zero` (240–259 vs 1102–1121): header only.
- `ag9b15u_exists_unit_normal_form_of_surj` (261–308 vs 1122–1169): header only.
- `ag9b15u_exists_K_truncation_of_mem_poleSubmodule` (310–349 vs 1170–1209): header plus
  the `if_pos rfl`/`if_neg …` → `ite_eq_left rfl`/`ite_eq_right …` rename at port lines
  1198/1201.
- `ag9b15u_differentialCoeff_D_unit_mul_uniformizer` (351–369 vs 1210–1227): header plus
  the dropped `p2m_export` line.

The five declarations are `private` in the port. The new module must either promote them
(the recommended route) or keep the whole `p0n22` cone in `P1ResidueCore` — which would
defeat the work order's reason for a generic home. Promotion touches nothing but the
`private` keyword, and these names have no public collision (grep over `FLTForHuman/`
finds only `P1ResidueCore`).

### 8.3 mathlib's `Derivation` API carries the whole differential prelude (rows 5–8, 21, 23, 24, 28)

`Derivation.{leibniz, leibniz_pow, leibniz_inv, map_algebraMap, map_one_eq_zero}`
(`Mathlib/RingTheory/Derivation/Basic.lean:118/139/494/131/127`) are exactly the leaves the
pin uses; probe H1 compiles row 5's body unchanged, and probe M resolves every other leaf.
`Valuation.map_add_of_distinct_val` supplies the non-archimedean additivity for rows 4/19.
No derivation step in this file needs a new mathlib lemma.

### 8.4 The characteristic-`p` Frobenius API is complete (rows 32–38)

`add_pow_char`, `sum_pow_char`, `neg_one_pow_char`, `frobenius_def`,
`charP_of_injective_ringHom`, `charP_of_injective_algebraMap`,
`CharP.{cast_eq_zero_iff, char_is_prime_or_zero, charP_to_charZero}` and `ringChar.charP`
all exist at the names probed in §M and are the pin's own calls. The headline's
`rcases CharP.char_is_prime_or_zero K (ringChar K)` split transcribes (probe H4).

### 8.5 The dedup is against the master ℙ¹ file (Correction 4)

The master file carries copies of rows 1–3 and of the `p0n22_cpf_*` cone; homing the cone
here means 3.2d/e import it. This is the same dedup pattern as 3.2b/c and is the reason
the work order schedules this file before the ℙ¹ file's later part.

## 9. Route options

- **R1 — import the nine substitutes; promote the five `private` ones.** Rows 1–4, 11–14,
  16. Do not re-prove any of them; the pin bodies are already the port bodies (§8.1–8.2).
- **R2 — transcribe the differential prelude (rows 5–7) and the two `res` engine lemmas
  (rows 8–9).** Rows 5–7 are 2–8 lines each over mathlib's `Derivation` API; row 8 is the
  pole-depth induction and row 9 is one line.
- **R3 — transcribe the `p0n22_cpf_*` cone verbatim (rows 17–38).** Every proof is a named
  assembly; the two long rows (28 and 35) are geometric-series and Frobenius bookkeeping.
  Use mathlib's names from §M rather than re-deriving them.
- **R4 — do not build a `Differential F` instance to reach `Differential.logDeriv_mul`.**
  mathlib's `Differential` (`RingTheory/Derivation/DifferentialRing.lean:21`) is a
  `Derivation ℤ R R` typeclass, while the pin's `logDeriv` is
  `v.differentialCoeff (D x) * x⁻¹`; matching them needs a `Differential F` instance plus
  `DifferentialAlgebra K F`, and row 21 is already a 14-line `linear_combination`. Recorded
  as a route option, not adopted.
- **R5 — no polynomial or Laurent-series route.** This file has no polynomial content; see
  §11.

## 10. API drift (`v4.34.0`) — what the worker must change

| pin call / assumption | `v4.34.0` status | worker action |
|---|---|---|
| `if_pos h` / `if_neg h` in the promoted `ag9b15u_exists_K_truncation_of_mem_poleSubmodule` | renamed `ite_eq_left h` / `ite_eq_right h` (drift table, 3.2b §2) | the port copy at `P1ResidueCore.lean:1198/1201` already uses the new names; when promoting, keep the port text |
| `haveI : CharP K 0`, `haveI : CharZero K`, `haveI : CharP v.ResidueField p`, `haveI : CharP F p` in `Prop` goals (rows 32, 33, 35, 38) | `linter.style.haveILetI` fires (probe H warns on `haveI : CharP K 0`) | keep `haveI`: instance search needs the instance inline. Suppress the linter locally if the project is warning-strict, per playbook §7; do not weaken to `have` |
| pin `private theorem _root_.AlgebraicCurve.Place.foo` / `_root_.ModularCurve.…foo` headers | the port writes `private theorem foo` inside the same namespace | no statement change; the checker normalises namespace qualification |
| `Polynomial.multiplicity` / `Polynomial.emultiplicity` | do not exist (3.2c §15) | not used here |
| `Set.mem_setOf_eq`, `dif_pos`, `Polynomial.degree_sub_lt` | the drift table's renames | not used in rows 1–38 |

No other drift: the file names no deprecated constant, and probes M/H resolve at the pin
spellings.

## 11. Recorded negatives

Confirmed against mathlib `v4.34.0` and the port; phrased so the search is not repeated.

1. **No `ag9b13t_*`, `ag9b14c_*`, `p0n22_cpf_*`, `D_pow_succ_inv`,
   `differentialCoeff_add''`, `differentialCoeff_D_uniformizer_pow_inv`,
   `res_differentialCoeff_D_of_mem_poleSubmodule` or `res_differentialCoeff_D_of_surj` in
   the port.** Greps over `FLTForHuman/`, `Reserve/` and `spec/` for `ag9b13t`,
   `ag9b14c`, `p0n22`, `D_pow_succ_inv` are empty; `#check` errors on the names. The
   brief's "the `ag9b13t_*`/`ag9b15u_*` char-0 engine is in
   `Defs/CanonicalLocalResidueInstanceV2.lean`" is half right: `ag9b15u_*` is ported (in
   `P1ResidueCore`), `ag9b13t_*` is not.
2. **No `Polynomial.logDeriv` in `v4.34.0`.** The only algebraic log derivative is
   `Differential.logDeriv` (`Mathlib/FieldTheory/Differential/Basic.lean:29`), which needs a
   `Differential` instance (route option R4); `Analysis.Calculus.logDeriv` and
   `Meromorphic.logDeriv` are analytic and off-path.
3. **No route from `LaurentSeries` / `HahnSeries` to `Place.ord`.** `LaurentSeries R` is
   `HahnSeries ℤ R` (`Mathlib/RingTheory/LaurentSeries.lean`), and it has an `X`-adic
   valuation, but this file's Laurent expansion (row 27) is a finite-sum-plus-remainder
   statement in the valuation subring, not a `LaurentSeries` equality. Do not route the
   `p0n22` expansion through `HahnSeries`.
4. **`Polynomial.divByMonic` / `modByMonic` / `X_pow_dvd_iff` / `derivative` exist but are
   off this file's path.** They are the right tools for 3.2a's `placeOfPoint` block (the
   3.2c audit's §16.5), not for the generic local-residue calculus: no declaration in
   rows 1–38 mentions a polynomial.
5. **`Polynomial.mul_prod_pow_inverse_eq_quo_add_sum_rem_mul_pow_inverse`
   (`Mathlib/Algebra/Polynomial/PartialFractions.lean:341`) is off-path.** The pin's
   "Cartier" rows (32–36) are characteristic-`p` Frobenius identities (`add_pow_char`,
   `sum_pow_char`), not partial fractions. Probe M resolves the partial-fraction lemma, but
   no row consumes it.
6. **No `Place.differentialCoeff_add` in the port** — only the pin-private `add''` (row 6),
   and `differentialCoeff` is not a `LinearMap` (`Defs/CanonicalDivisor.lean:70`). A port
   needs the uniqueness-lemma proof, not `map_add`.
7. **The four `ag9b15u_*` lemmas and `ord_add_eq_min` have no public home.** They are
   `private` in `Defs/P1ResidueCore.lean`; the generic module must promote them (R1) or
   the dedup of Correction 4 is lost.
8. **No `Place.res_higherPoleMonomial`/`res_algebraMap_mul_uniformizer_pow_inv` outside
   the `CanonicalLocalResidueDataK` structure.** They are fields (`Defs/LocalResidue.lean:41`)
   with the constructor lemma at `Defs/CanonicalLocalResidueInstanceV2.lean:340`; probe H3
   checks the dot notation the pin uses.

## 12. What this changes for `WORKORDER-P3-2dprime-localresidue.md`

**Scope / measurement.**

- 38 `S_` declarations plus one `Theorems/` wrapper = the advice log's 39 targets; the
  file is 1,244 raw lines. **9 SUBSTITUTE / 29 PROOF-INGREDIENT / 0 BESPOKE.**
- The brief's substitute list needs two edits: (a) `ag9b13t_*` and `ag9b14c_*` are **not**
  ported, so the "char-0 engine" row is new work; (b) the substitution count is 9, not 7
  (`mem_iff_ord_nonneg` and `gate_canonicalLocalResidueDataK_uniformizer_inv` are
  binder-spelling matches the log lists only in §3).

**Discharged proofs (mark import-discharged; the statements still land).**

- rows 1–3 — import `Defs/PushPull.lean` (already in `PORT_FILES` via 3.2b);
- rows 4, 11–14 — **promote** `Place.ord_add_eq_min`, the four `ag9b15u_*` from
  `Defs/P1ResidueCore.lean:131/1102/1122/1170/1210` (single keyword edit; no collision);
- row 16 — import `AlgebraicCurve.gate_canonicalLocalResidueDataK_uniformizer_inv`
  (`Defs/P1ResidueCore.lean:1090`).

**New work, budgeted.**

- rows 5–9 (the differential prelude and the two `res` engine lemmas);
- rows 10, 15 (the `ag9b13t_*` and `ag9b14c_*` lemmas; Correction 1);
- rows 17–38 (the `p0n22_cpf_*` cone, its Cartier refinement, the prime engine and the
  headline). The two long rows are 28 (`res_geom_core`, ~140 pin ln) and 35
  (`res_pow_mul_dlog_unit`, ~110 pin ln); both are named assembly over `geom_sum_mul`
  and the char-p Frobenius API.

**Imports the worker may use.** The port modules
`Defs/{PushPull, CanonicalDivisor, LocalResidue, CanonicalLocalResidueInstanceV2,
P1ResidueCore}` plus, on the mathlib side, `Mathlib.RingTheory.Derivation.Basic`,
`Mathlib.Algebra.CharP.{Lemmas,Frobenius,Algebra}`,
`Mathlib.RingTheory.Valuation.Basic`, `Mathlib.RingTheory.LocalRing.ResidueField.Basic`,
`Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic`, `Mathlib.Algebra.Ring.GeomSum`,
`Mathlib.Algebra.CharP.Defs`, `Mathlib.Algebra.Group.Basic`,
`Mathlib.Algebra.GroupWithZero.Basic`. Do **not** import
`Mathlib.RingTheory.LaurentSeries`, `Mathlib.Algebra.Polynomial.PartialFractions` or
`Mathlib.FieldTheory.Differential.Basic` — they are off-path (§11.3, §11.5, route R4).

**Checker wiring.** `SOURCES` += the `Thm_*` wrapper then the `S_*` file; `PORT_FILES` +=
`Defs/LocalResidueCalculus.lean`. The new public surface to reconcile is rows 1–10 and
15–38 (the promoted rows 4/11–14 verify through the checker's dotted-name fallback; row 16
is a binder-spelling match). The headline's interface copy is the `Theorems/` wrapper's
dotted name `AlgebraicCurve.Place.CanonicalLocalResidueDataK.res_differentialCoeff_D_mul_pow_inv_eq_zero_of_surjective_algebraMap`.

**Stop-early.** The one unanticipated item is Correction 1: a worker who banks the brief's
"the `ag9b13t_*` engine is in `Defs/CanonicalLocalResidueInstanceV2.lean`" will not find it;
rows 10 and 15 are new transcriptions.

## 13. Appendix — module map for the named constants

| name | module |
|---|---|
| `Polynomial.{X_pow_dvd_iff, X_dvd_iff, divByMonic, modByMonic, divByMonic_eq_zero_iff, modByMonic_eq_zero_iff_dvd}` | `Mathlib/Algebra/Polynomial/{Div,RingDivision}.lean` |
| `Polynomial.derivative` | `Mathlib/Algebra/Polynomial/Derivative.lean` |
| `Polynomial.mul_prod_pow_inverse_eq_quo_add_sum_rem_mul_pow_inverse` | `Mathlib/Algebra/Polynomial/PartialFractions.lean` |
| `LaurentSeries`, `HahnSeries` | `Mathlib/RingTheory/LaurentSeries.lean`, `Mathlib/RingTheory/HahnSeries/*` |
| `Differential.{logDeriv, logDeriv_mul, logDeriv_div, logDeriv_pow}` | `Mathlib/FieldTheory/Differential/Basic.lean` |
| `Differential` class, `DifferentialAlgebra` | `Mathlib/RingTheory/Derivation/DifferentialRing.lean` |
| `Derivation.{leibniz, leibniz_pow, leibniz_inv, leibniz_div, map_algebraMap, map_one_eq_zero, map_aeval}` | `Mathlib/RingTheory/Derivation/Basic.lean` |
| `IsLocalRing.{residue, residue_eq_zero_iff, ResidueField.algebraMap_eq}` | `Mathlib/RingTheory/LocalRing/ResidueField/Basic.lean` |
| `IsLocalRing.mem_maximalIdeal` | `Mathlib/RingTheory/LocalRing/MaximalIdeal/Basic.lean` |
| `Valuation.map_add_of_distinct_val`, `WithZero.log_le_log` | `Mathlib/RingTheory/Valuation/Basic.lean` |
| `ValuationSubring.mem_or_inv_mem` | `Mathlib/RingTheory/Valuation/ValuationSubring.lean` |
| `IsDiscreteValuationRing.{exists_irreducible, eq_unit_mul_pow_irreducible}` | `Mathlib/RingTheory/DiscreteValuationRing/Basic.lean` |
| `add_pow_char`, `sum_pow_char`, `neg_one_pow_char` | `Mathlib/Algebra/CharP/Lemmas.lean` |
| `frobenius_def` | `Mathlib/Algebra/CharP/Frobenius.lean` |
| `charP_of_injective_ringHom`, `charP_of_injective_algebraMap` | `Mathlib/Algebra/CharP/Algebra.lean` |
| `CharP.{cast_eq_zero_iff, char_is_prime_or_zero, charP_to_charZero}`, `ringChar.charP` | `Mathlib/Algebra/CharP/Defs.lean` |
| `geom_sum_mul` | `Mathlib/Algebra/Ring/GeomSum.lean` |
| `smul_pow` | `Mathlib/Algebra/Group/Action/Defs.lean` |
| `Nat.cast_smul_eq_nsmul` | `Mathlib/Algebra/Module/NatInt.lean` |
| `Algebra.algebraMap_eq_smul_one` | `Mathlib/Algebra/Algebra/Defs.lean` |
| `IsScalarTower.algebraMap_apply` | `Mathlib/Algebra/Algebra/Tower.lean` |
| `zpow_sub_one₀` | `Mathlib/Algebra/GroupWithZero/Basic.lean` |
| `zpow_mul` | `Mathlib/Algebra/Group/Basic.lean` |
