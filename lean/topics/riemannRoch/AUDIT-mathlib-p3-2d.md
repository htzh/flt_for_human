# Mathlib-first substitution audit — the phase-3.2d ℙ¹ residue core, chunk 3 (P3.2d)

**Method:** `lean/porting-playbook.md` §2.2 (audit the route, mathlib first), after the
phase-1/2/3.1/3.2a/3.2b/3.2c/3.2d′ templates
[`AUDIT-mathlib.md`](AUDIT-mathlib.md), [`AUDIT-mathlib-p2.md`](AUDIT-mathlib-p2.md),
[`AUDIT-mathlib-p3-1.md`](AUDIT-mathlib-p3-1.md),
[`AUDIT-mathlib-p3-2a.md`](AUDIT-mathlib-p3-2a.md),
[`AUDIT-mathlib-p3-2b.md`](AUDIT-mathlib-p3-2b.md),
[`AUDIT-mathlib-p3-2c.md`](AUDIT-mathlib-p3-2c.md) and
[`AUDIT-mathlib-p3-2dprime.md`](AUDIT-mathlib-p3-2dprime.md). Pin:
`anthropics/fermats-last-theorem@aa2d8b3` (read-only clone at
`~/proj/fermats-last-theorem`); port mathlib `v4.34.0`
(`lean/.lake/packages/mathlib`). Measured inventory:
[`tools/deps/build/p32_master_inventory.txt`](../../../tools/deps/build/p32_master_inventory.txt),
rows #290–#434, with the pre-port advice in
[`tools/deps/build/p32_engine_advise.log`](../../../tools/deps/build/p32_engine_advise.log)
and its machine-readable twin
[`p32_engine_advise.json`](../../../tools/deps/build/p32_engine_advise.json). Work order:
[`WORKORDER-P3-2d-p1core-3.md`](WORKORDER-P3-2d-p1core-3.md).

Source, the single pin `S_` file (13,173 ln, 580 declarations):

- [`P2M/Sol/S_AlgebraicCurve_RationalFunctionField_trace_localResidue_placeInfty_X_pow_eq_zero.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_RationalFunctionField_trace_localResidue_placeInfty_X_pow_eq_zero.lean),
  rows #290–#434 = pin lines 6745–9499 (145 rows).

**Class convention** (unchanged from phases 1–3.2d′). SUBSTITUTE = the port can import an
existing declaration instead of proving the row: an already-landed port lemma or a mathlib
constant whose *type* is the pin's, or a pin `def`/`abbrev`/instance whose body is `rfl`-equal
to a mathlib/port term. A statement that differs from the port copy only by binder spelling, a
`p1PlaceInfty` → `placeInfty` name translation, a dropped/added `_s12` suffix, or a
`_root_.`-qualified pin header is counted SUBSTITUTE with that difference recorded.
PROOF-INGREDIENT = the statement is bespoke (it mentions pin vocabulary) but the proof is a
short assembly of named mathlib/port lemmas. BESPOKE = a definition/structure/class/`Prop`
introducing new vocabulary, or an instance with no mathlib/port counterpart; these are the
recorded negatives and the real work. As in 3.2b/c, instances that assemble already-ported
vocabulary are counted PROOF-INGREDIENT.

**Scratch evidence:** `lean/ScratchAuditP32d.lean` (gitignored, 442 ln, 233 `#check`s),
compiled from `lean/` with

```bash
timeout 120 lake env lean -DmaxHeartbeats=4000000 -DautoImplicit=false ScratchAuditP32d.lean
```

**final run clean, exit 0, 5.7 s wall** (707 lines of output; no errors; three warnings: the
two deliberate `Polynomial.degree_sub_lt` deprecation probes and one `linter.style.haveILetI`
note on the §H9 prototype binder, §9). The probe ledger:

- **P** — the port-substitute `#check`s (§P1–§P6 of the scratch): every port name tabulated
  below, plus the chunk-1/2 vocabulary the new rows consume
  (`OrdDifferentialWellDefined`, `P1DifferentialCoeffRegularFinite`, `KaehlerRankOne`,
  `RamificationInertiaIdentity`, `p1PrincipalPartAtom`, `AlgebraicCurve.dX` /
  `dX_ne_zero` / `D_algebraMap_polynomial` / `denom_sq_smul_D_eq`,
  `p1DifferentialCoeffRegularFinite_dX`, `ord_finitePlace_self`,
  `ord_finitePlace_p1PrincipalPartAtom`, `one_le_ord_placeInfty_p1PrincipalPartAtom`,
  `ord_placeInfty_algebraMap'`, `finitePlace_ne_placeInfty`,
  `ratFuncDXCoeff_ne_zero_and_ord_eq_zero_of_ord_eq_one`,
  `exists_ord_zero_smul_of_smul_dX_eq`,
  `exists_dXCoeff_ord_two_of_ord_placeInfty_eq_one`,
  `ordDifferential_placeInfty_D_ratFuncX`, `eq_ofHeightOneSpectrum_or_eq_placeInfty`,
  `exists_irreducible_span`, `Place.{simplePoleResidueAux_eq_zero_of_mem,
  mem_simplePoleSubmodule_of_mem, simplePoleResidueAux_apply, poleSubmodule_one,
  mem_poleSubmodule, localResidueData_res_eq_simplePoleResidueAux}`,
  `FLT.EulerDualBasis.{trace_root_pow_div_derivative_self,
  trace_root_pow_div_derivative_of_lt}`, the ℙ¹ base-case instance
  `AlgebraicCurve.RationalFunctionField.instHasPrincipalDivisors`, the `Lg37`/`Mp72a102T1`/
  `KwNo6Section`/`KwNo6Pin` engine names, `IsCurveOver.{kaehler_free_rank_one,
  finrank_kaehler, instFreeKaehler}`), and the fibre engine
  (`FundamentalIdentity`, `SumRamificationInertia`,
  `Place.sum_ramificationIndex_mul_inertiaDeg_fiberOver`,
  `Place.deg_restrict_mul_inertiaDeg`, `Place.ord_restrict`). All resolve; that is the
  by-probe verification of every SUBSTITUTE port name tabulated below.
- **M** — the mathlib `#check` ledger (§M1–§M6): `KaehlerDifferential.{polynomialEquiv,
  tensorKaehlerEquivOfFormallyEtale, mvPolynomialBasis, map, map_D, map_surjective, D,
  span_range_derivation, finite, span_range_map_derivation_of_isLocalization}`,
  `Algebra.FormallyEtale.{of_isLocalization, of_isSeparable, comp, of_equiv}`,
  `Algebra.FormallyUnramified.{of_isSeparable, subsingleton_kaehlerDifferential}`,
  `Module.Basis.{singleton, baseChange, map, span_eq, ne_zero}`,
  `Module.{Free.of_basis, finrank_eq_card_basis, nontrivial_of_finrank_eq_succ}`,
  `RatFunc.{algEquivOfTranscendental, algEquivOfTranscendental_X, algebraMap_X}`,
  `PerfectField.{ofCharZero, separable_of_irreducible}`,
  `Algebra.IsAlgebraic.isSeparable_of_perfectField`, `Algebra.IsSeparable.{of_integral,
  of_equiv_equiv}`, `IntermediateField.{charZero, equivOfEq, adjoin_simple_le_iff,
  mem_adjoin_simple_self}`, `Module.Finite.of_equiv_equiv`,
  `exists_isTranscendenceBasis_and_isSeparable_of_perfectField`, `IsAlgebraic.inv_iff`,
  `Polynomial.{derivative, derivative_add, derivative_X, derivative_C, Monic.eq_X_add_C,
  degree_eq_natDegree, eq_C_of_degree_le_zero, natDegree_lt_natDegree,
  coeff_eq_zero_of_natDegree_lt, leadingCoeff, eraseLead, eraseLead_add_C_mul_X_pow,
  eraseLead_natDegree_lt_or_eraseLead_eq_zero, degree_X_pow, natDegree_X_pow, degree_sub_lt,
  leadingCoeff_X_pow, X_ne_zero, C_eq_algebraMap, aeval_def, eval₂_eq_sum_range'}`,
  `Nat.WithBot.lt_one_iff_le_zero`,
  `ValuationSubring.{idealOfLE, ofPrime_idealOfLE, ofPrime_bot, ofPrime_top,
  eq_of_le_of_ne_top, mem_or_inv_mem, toSubring_injective, prime_idealOfLE}`,
  `ValuationRing.isInteger_or_isInteger`, `isIntegrallyClosed_iff`, `IsIntegral.tower_top`,
  `integralClosure.{isDedekindDomain, isFractionRing_of_finite_extension}`,
  `IsIntegralClosure.finite`, `IsPrincipalIdealRing.{of_surjective, isDedekindDomain}`,
  `IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain`,
  `Algebra.FiniteType.{adjoin_of_finite, trans}`, `IsFractionRing.div_surjective`,
  `nonZeroDivisors.ne_zero`, `AdjoinRoot.{mk, root, aeval_eq, powerBasis,
  minpoly_powerBasis_gen_of_monic, powerBasis_dim, powerBasis_gen}`,
  `Algebra.trace`, `Algebra.trace_eq_of_algEquiv`, `Algebra.IsIntegral.isIntegral`,
  `minpoly.{monic, aeval}`, `Algebra.IsSeparable.isSeparable`,
  `Field.exists_primitive_element`,
  `IsDedekindDomain.HeightOneSpectrum.{valuation_eq_one_iff_notMem, valuation_lt_one_iff_mem}`,
  `IsLocalRing.{residue, residue_eq_zero_iff}`, `map_div₀`,
  `Ideal.{sum_ramification_inertia_eq_finrank, sum_ramification_inertia_eq_finrank_fiber,
  inertiaDeg, ramificationIdx}`, `IsDedekindDomain.mem_primesOverFinset_iff`,
  `Finset.{sum_bij, sum_congr, mul_sum, sum_eq_single, sum_mul}`,
  `Valuation.map_add_of_distinct_val`, `WithZero.log_le_log`,
  `IsDiscreteValuationRing.{exists_irreducible, eq_unit_mul_pow_irreducible}`,
  `IsLocalRing.eq_maximalIdeal`, `IsAlgClosed.degree_eq_one_of_irreducible`,
  `Finset.sum_div` (see negative 7). Everything listed resolves in the final probe; the pin
  spellings that v4.34 lacks are recorded in §10 (negatives 5–7).
- **H** — compile-checked prototypes: `H1` the whole ℙ¹ Kähler basis block (rows
  #292–#296) transcribes and discharges `instIsCurveOverRatFunc`; `H2`
  `degree_X_pow_natDegree_sub_lt_of_monic` (#434) verbatim; `H3` the two char-0
  separability leaves (#427/#428); `H4` `eq_of_isDiscreteValuationRing_of_le` (#310) is
  `ValuationSubring.eq_of_le_of_ne_top`; `H5`/`H6` the two mathlib instances
  (`IsIntegrallyClosed v.toValuationSubring`, `IsScalarTower K B ↥(integralClosure B F)`);
  `H7` the four `valSubringKaehlerFinite_of_*` wrappers (#318/#353/#371/#407) in two
  lines each; `H8` `p1DifferentialCoeffRegularFinite_of_unitFinite` (#291); `H9`
  `hasSeparatingTranscendental_of_core` (#430); `H10`–`H12` the ramification–inertia
  wrappers (#297–#299) one line each off `Place.sum_ramificationIndex_mul_inertiaDeg_fiberOver`.

## 1. Summary — class counts

| block (rows) | SUBSTITUTE | PROOF-INGREDIENT | BESPOKE | rows |
|---|---:|---:|---:|---:|
| ℙ¹ differential-coefficient / Kähler prelude (#290–#296) | 0 | 4 | 3 | 7 |
| ramification–inertia wrappers (#297–#299) | 0 | 3 | 0 | 3 |
| degree-one / principal-part computation (#300–#306) | 0 | 6 | 1 | 7 |
| Dedekind-model / affine-chart / integral-closure block (#307–#404) | 59 | 33 | 6 | 98 |
| separating-transcendental wrappers (#405–#407) | 2 | 1 | 0 | 3 |
| `placeInfty` Euler value / monomial (#408–#420) | 0 | 11 | 2 | 13 |
| `IntermediateField` inv / separability leaves (#421–#428) | 6 | 2 | 0 | 8 |
| `HasSeparatingTranscendentalCore` / core (#429–#434) | 0 | 5 | 1 | 6 |
| **total** | **67** | **65** | **13** | **145** |

**Headline.** Nearly half of the chunk is already paid for: **67 of 145 rows are SUBSTITUTE**,
65 are short assemblies of named port/mathlib lemmas, and only **13 introduce a new object**.
The single dominating fact is **Correction 1**: rows **#307–#404** (98 rows, 68% of the chunk)
are the pin's *duplicate* of
[`S_AlgebraicCurve_hasCanonicalDivisor_of_isCurveOver.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_hasCanonicalDivisor_of_isCurveOver.lean),
which phase P2 already landed in `Canonical/HasCanonicalDivisor.lean` — 59 of those 98 rows are
statement-identical imports under the pin-`private` `_s12` names or the exact public names. The
13 BESPOKE rows are `P1DifferentialCoeffUnitFinite` (#290), `kaehlerPolynomialBasis` (#292),
`kaehlerRatFuncBasis` (#294), `P1FinitePlaceCanonicalResidueAtomMGeTwoHigherDeg` (#304),
`P1PrincipalPartMOneSimplePoleCancel` (#327),
`P1FinitePlaceCanonicalResidueAtomMGeTwoTrace` (#329),
`P1FinitePlaceCanonicalResidueAtomMGeTwoTraceHigherDeg` (#330),
`finitePlaceResidueFieldAlgEquivAdjoinRoot` (#356),
`P1FinitePlaceSimplePoleResidueAdjoinRootValue` (#359),
`P1PlaceInftySimplePoleResidueEulerValue` (#360),
`P1PlaceInftySimplePoleResidueEulerValueTopDeg` (#411),
`P1PlaceInftySimplePoleResidueEulerValueMonomial` (#412) and
`HasSeparatingTranscendentalCore` (#429) — three plain `def`s (#292, #294, #356) and ten
`def … : Prop`s.

The genuinely new proof work is four connected stories:

1. the ℙ¹ Kähler/rank-one block (#290–#296) — **mathlib-only**, the pin body compiles as-is
   (probe H1), the `Basis`/`FormallyEtale`/`KaehlerDifferential` API is complete;
2. the pin-`private` `AdjoinRoot` trace engine (#354–#362), the finite-place residue engine
   (#374–#387) and the `placeInfty` Euler-value/eraseLead cone (#408–#420);
3. the ℙ¹ capstone `ordDifferentialWellDefined_ratFunc_of_perfectField` (#321),
   which is pure assembly over chunk-3.2c's `ratFuncDXCoeff`/`dX` blocks;
4. the `HasSeparatingTranscendentalCore`/char-0 separability tail (#427–#434).

Three reuse wins dominate the route: `Canonical/HasCanonicalDivisor.lean` already carries 59 of
the rows (#307–#404), `Defs/CanonicalLocalResidueInstanceV2.lean` carries #319/#320 outright,
and the fibre dictionary (`Defs/PushPull.lean:632` + `WeilExchange/FiberOverCount.lean:33`)
answers #297–#299 in one line each.

## 2. Corrections to the brief and the work order

**Correction 1 — the chunk is two developments, and rows #307–#404 are duplicates.**
The brief's content list (and `WORKORDER-P3-2d-p1core-3.md` §0) names only the ℙ¹
differential/Kähler/principal-part rows and the separability leaves; it omits the 98-row
middle. Those rows are the master file's copies of the abstract canonical-divisor development
already ported in phase P2 (`AUDIT-mathlib-p2.md` §2.3 names the same declarations in
`S_AlgebraicCurve_hasCanonicalDivisor_of_isCurveOver.lean`). Because the pin's copies differ
only in name (`_s12` suffix on the second file's copies, `_root_.` prefixes, `p2m_*`
scaffolding), 59 of them are SUBSTITUTE. **Do not re-prove the Dedekind-model chain**; import
`Canonical/HasCanonicalDivisor.lean` and land aliases for the checker.

**Correction 2 — the `_s12` suffix is the *pin's*, not the port's.** The phase-2 pin file
declares `ofPrime_congr_s12`, `adjoin_simple_inv_s12`, `Transcendental.isPrincipalIdealRing_adjoin_s12`,
… while the master file declares the same statements without the suffix. The port transcribed
the phase-2 file verbatim, so the suffix is in `HasCanonicalDivisor.lean`. Span diffs of
master vs phase-2 pin sources (pin 7135–7158 vs 394–416, 8824–8868 vs 860–895, 9330–9370 vs
1036–1066) differ **only** in the suffix, the `ofPrime_congr` call sites and the
`p2m_alias`/`p2m_reactivate` lines; the port copies are therefore statement-identical to this
chunk's rows.

**Correction 3 — ten of the block's substitutes are `private` and cannot be imported.**
`ofPrime_congr_s12` (`HasCanonicalDivisor.lean:372`), `inv_mem_of_not_mem_centerIdeal`
(`:498`), `div_mem_of_not_mem_centerIdeal` (`:512`), `coe_toKSubalgebra` (`:764`) and the six
`Transcendental.*_adjoin_s12` / `Algebra.FiniteType.adjoin_singleton_s12` / `Transcendental.inv_s12`
(`:788–:813`) are `private` in `HasCanonicalDivisor.lean`, so the chunk-3 module (which appends
to `Defs/P1ResidueCore.lean`) cannot `#check`, let alone import, them. Each must either be
**promoted** (a one-keyword edit, no name collision: grep over `FLTForHuman/` finds exactly one
copy) or re-landed `private` in the new module. Promotion is the route the audit recommends —
it is the same promotion 3.2d′ chose for the `ag9b15u_*` block. The public `_s12` names
(`*_s12` at `:376/:381/:385/:948/:955/:960/:965/:970/:974`) import directly.

**Correction 4 — `P1DifferentialCoeffUnitFinite` (#290) is the chunk's first row and is new.**
Reconfirms 3.2c Correction 1 / negative 9: the name is not a 3.2c declaration. Grep over
`FLTForHuman/` is empty and `#check` errors. The 3.2c name is the distinct
`P1DifferentialCoeffRegularFinite` (`P1ResidueCore.lean:437`, consumed by #291).

**Correction 5 — the four `valSubringKaehlerFinite_of_*` rows are one-liners, not new math.**
The port has `valSubringKaehlerFinite_of_essFiniteType` (`:341`) and
`valSubringKaehlerFinite_of_finiteTypeModel` (`:360`) but **not** the
`_of_dedekindModel` (#318), `_of_dedekindFractionModel` (#353), `_of_twoAffineCharts` (#371) or
`_of_hasSeparatingTranscendental` (#407) wrappers. Each is one application of the existing
engines (probe H7); the four together are ~8 content lines.

**Correction 6 — `instHasPrincipalDivisorsRatFuncSelf` (#328) is already satisfied.**
`AlgebraicCurve.RationalFunctionField.instHasPrincipalDivisors` (`P1ResidueCore.lean:866`, the
phase-3.2c ℙ¹ base case) is a `scoped instance` of *the same class and type*. The pin's route
through `RationalFunctionField.instHasPrincipalDivisorsOfIsGalois` does **not** exist in the
port (grep 0, `#check` errors), and does not need to: #328 should be a scoped-instance alias
(`:= inferInstance`, or `:= instHasPrincipalDivisors`) so the checker sees the pin name. Note
the pin's own `scoped instance` has lower priority (`priority := 50`) than the port's; keep
`set_option linter.overlappingInstances false` if both are landed.

**Correction 7 — `ordDifferentialWellDefined_ratFunc_of_perfectField` (#321) is not the 3.2d′
headline.** It is a *second* ℙ¹ capstone for the generic `OrdDifferentialWellDefined` (chunk 1,
`P1ResidueCore.lean:120`), proved over `[PerfectField K]` rather than `[CharZero K]`; its proof
is the chunk-3.2c `ratFuncDXCoeff` engine plus `PerfectField.separable_of_irreducible`. The
3.2d′ `res_differentialCoeff_D_mul_pow_inv_eq_zero_of_surjective_algebraMap` is a different
statement and does not discharge it.

## 3. The ℙ¹ differential-coefficient / Kähler prelude (rows #290–#296, #300–#306)

Row #290 is new vocabulary; #292/#294/#304 are new definitions; the rest are short assemblies.
The Kähler half is **entirely mathlib** (probe H1).

| row | pin decl (line) | class | mathlib / port name | evidence |
|---:|---|---|---|---|
| 290 | `P1DifferentialCoeffUnitFinite` (6745) | **BESPOKE** | — | new `def … : Prop`; no port copy (grep 0, `#check` errors). The 3.2c name is `P1DifferentialCoeffRegularFinite` |
| 291 | `p1DifferentialCoeffRegularFinite_of_unitFinite` (6753) | PROOF-INGREDIENT | port `P1DifferentialCoeffRegularFinite` (`P1ResidueCore.lean:437`), `Place.mem_of_ord_nonneg` (`PushPull.lean:60`), `Place.differentialCoeff_ne_zero` | probe H8; one line |
| 292 | `kaehlerPolynomialBasis` (6795) | **BESPOKE** | `KaehlerDifferential.polynomialEquiv`, `Module.Basis.singleton`/`map` | new `def` (`Basis Unit K[X] Ω[K[X]⁄K]`); probe H1 |
| 293 | `instFormallyEtalePolynomialRatFunc` (6798) | PROOF-INGREDIENT | `Algebra.FormallyEtale.of_isLocalization (nonZeroDivisors K[X])` | probe H1; one line |
| 294 | `kaehlerRatFuncBasis` (6801) | **BESPOKE** | `Module.Basis.baseChange`/`map`, `KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale` | new `def`; probe H1 |
| 295 | `kaehlerRankOne_ratFunc` (6805) | PROOF-INGREDIENT | port `KaehlerRankOne` (`P1ResidueCore.lean:1625`), `Module.Free.of_basis`, `Module.finrank_eq_card_basis` | probe H1; two lines |
| 296 | `instIsCurveOverRatFunc` (6809) | PROOF-INGREDIENT | port `RationalFunctionField.isCurveOver_of_kaehlerRankOne` (`P1ResidueCore.lean:1646`) + row #295 | probe H1; the 54-line pin span is `p2m` scaffolding around a one-line body |
| 300 | `derivative_monic_natDegree_one_eq_one` (7000) | PROOF-INGREDIENT | `Polynomial.Monic.eq_X_add_C`, `derivative_add`, `derivative_X`, `derivative_C` | probe M |
| 301 | `D_algebraMap_polynomial_degOne` (7007) | PROOF-INGREDIENT | port `AlgebraicCurve.D_algebraMap_polynomial` (`P1ResidueCore.lean:1258`), row #300, `map_one`, `one_smul` | probe P |
| 302 | `eq_C_coeff_zero_of_degree_lt_degOne` (7015) | PROOF-INGREDIENT | `Polynomial.degree_eq_natDegree`, `Polynomial.eq_C_of_degree_le_zero`, `Nat.WithBot.lt_one_iff_le_zero` | probe M |
| 303 | `p1PrincipalPartAtom_mul_differentialCoeff_dX_degOne` (7025) | PROOF-INGREDIENT | row #302, `Polynomial.C_eq_algebraMap`, `IsScalarTower.algebraMap_apply` | probe M |
| 304 | `P1FinitePlaceCanonicalResidueAtomMGeTwoHigherDeg` (7047) | **BESPOKE** | — | new `def … : Prop`; no port copy |
| 305 | `p1FinitePlaceCanonicalResidueAtom_of_coordIndep_degOne` (7063) | PROOF-INGREDIENT | rows #303, port `CanonicalLocalResidueKDifferentialCoordIndep` (3.2c `:246`), `ord_finitePlace_self` | probe P |
| 306 | `p1FinitePlaceCanonicalResidueAtomMGeTwoHigherDeg_of_algClosed` (7095) | PROOF-INGREDIENT | `IsAlgClosed.degree_eq_one_of_irreducible`, `Polynomial.degree_eq_natDegree` | probe M |

## 4. The ramification–inertia wrappers (rows #297–#299)

The port's `RamificationInertiaIdentity` (`P1ResidueCore.lean:1659`, pin row #236 of 3.2c) is
already the pin's `Finset s` shape. What is missing is the `forall_mem_iff` sum and the
`deg` form; both follow from the existing fibre engine in one line (probes H10–H12).

| row | pin decl (line) | class | mathlib / port name | evidence |
|---:|---|---|---|---|
| 297 | `sum_ramificationIndex_mul_inertiaDeg_of_forall_mem_iff` (6863) | PROOF-INGREDIENT | `Place.sum_ramificationIndex_mul_inertiaDeg_fiberOver` (`WeilExchange/FiberOverCount.lean:33`), `Place.mem_fiberOver` (`PlacesOverDVR.lean:430`), `Finset.ext` | probe H10: `rw [Finset.ext …]` then the engine; the alternative is the pin's `Ideal.sum_ramification_inertia_eq_finrank` + `Finset.sum_bij` assembly already transcribed in `FiberOverCount.lean:44–100` (v4.34 drift, §7) |
| 298 | `sum_ramificationIndex_mul_deg_of_forall_mem_iff` (6905) | PROOF-INGREDIENT | row #297, `Place.deg_restrict_mul_inertiaDeg` (`PushPull.lean:460`), `Finset.mul_sum` | probe H11; pure `calc` |
| 299 | `ramificationInertiaIdentity_of_finiteDimensional` (6927) | PROOF-INGREDIENT | row #298 into port `RamificationInertiaIdentity` | probe H12; one line |

## 5. The Dedekind-model / affine-chart / integral-closure block (rows #307–#404)

98 rows. **59 are SUBSTITUTE** in `Canonical/HasCanonicalDivisor.lean` (phase P2); the table
below gives the mapping. `HasCanonicalDivisor.lean` is already imported by
`P1ResidueCore.lean:31`, so no new import is needed for the public copies. Rows marked
**(private)** are `private` in the port and need promotion (Correction 3).

| row | pin decl | class | port name (file:line) |
|---:|---|---|---|
| 307 | `ofPrime_congr` | SUBSTITUTE (private; `_s12`) | `ofPrime_congr_s12` (`HasCanonicalDivisor.lean:372`) |
| 308 | `eq_top_of_idealOfLE_eq_bot` | SUBSTITUTE (`_s12`) | `eq_top_of_idealOfLE_eq_bot_s12` (`:376`) |
| 309 | `idealOfLE_ne_bot_of_ne_top` | SUBSTITUTE (`_s12`) | `idealOfLE_ne_bot_of_ne_top_s12` (`:381`) |
| 310 | `eq_of_isDiscreteValuationRing_of_le` | SUBSTITUTE (`_s12`; also mathlib) | `eq_of_isDiscreteValuationRing_of_le_s12` (`:385`); `ValuationSubring.eq_of_le_of_ne_top` (probe H4) |
| 311 | `centerIdeal_isPrime` | SUBSTITUTE | `AlgebraicCurve.Place.centerIdeal_isPrime` (`:421`) |
| 312 | `Place.isUnit_modelInclusion_of_not_mem_centerIdeal` | SUBSTITUTE | `AlgebraicCurve.Place.isUnit_modelInclusion_of_not_mem_centerIdeal` (`:425`) |
| 313 | `Place.isUnit_modelInclusion_of_mem_primeCompl` | SUBSTITUTE | `…isUnit_modelInclusion_of_mem_primeCompl` (`:434`) |
| 314 | `Place.modelAlgebra_isScalarTower` | SUBSTITUTE | `…modelAlgebra_isScalarTower` (`:438`) |
| 315 | `Place.essFiniteType_of_finiteType_isLocalization_centerIdeal` | SUBSTITUTE | `…essFiniteType_of_finiteType_isLocalization_centerIdeal` (`:447`) |
| 316 | `ValSubringDedekindModel` | SUBSTITUTE | `ValSubringDedekindModel` (`:464`) |
| 317 | `valSubringEssFiniteType_of_dedekindModel` | SUBSTITUTE | `valSubringEssFiniteType_of_dedekindModel` (`:473`) |
| 318 | `valSubringKaehlerFinite_of_dedekindModel` | PROOF-INGREDIENT | no port copy; `valSubringKaehlerFinite_of_essFiniteType` (`:341`) + #317 (probe H7) |
| 319 | `completionSection_nonempty_generic` | SUBSTITUTE | `completionSection_nonempty_generic` (`CanonicalLocalResidueInstanceV2.lean:1656`) |
| 320 | `instHasCanonicalLocalResidueKStar` | SUBSTITUTE | `instHasCanonicalLocalResidueKStar` (`CanonicalLocalResidueInstanceV2.lean:1668`) |
| 321 | `ordDifferentialWellDefined_ratFunc_of_perfectField` | PROOF-INGREDIENT | chunk-3.2c `ratFuncDXCoeff_*`, `exists_ord_zero_smul_of_smul_dX_eq`, `exists_dXCoeff_ord_two_of_ord_placeInfty_eq_one`, `D_eq_ratFuncDXCoeff_smul_dX`, `PerfectField.separable_of_irreducible` (probe M) |
| 322 | `p1DifferentialCoeffUnitFinite_dX` | PROOF-INGREDIENT | chunk-3.2c `ord_differentialCoeff_dX_ofHeightOneSpectrum`, `eq_ofHeightOneSpectrum_or_eq_placeInfty`, `exists_irreducible_span` (probe P) |
| 323 | `ord_finitePlace_mOneAtom_mul_differentialCoeff` | PROOF-INGREDIENT | `Place.{ord_mul, differentialCoeff_ne_zero}`, `ord_finitePlace_p1PrincipalPartAtom`, `finitePlace_ne_placeInfty` (probe P) |
| 324 | `ord_placeInfty_mOneAtom_mul_differentialCoeff_ge_neg_one` | PROOF-INGREDIENT | `one_le_ord_placeInfty_p1PrincipalPartAtom`, `Place.ord_mul`, `omega` |
| 325 | `p1MOneAtom_mul_differentialCoeff_mem_simplePole_finitePlace` | PROOF-INGREDIENT | `Place.poleSubmodule_one`, `Place.mem_poleSubmodule`, `Place.mem_of_ord_nonneg`, row #323 |
| 326 | `p1MOneAtom_mul_differentialCoeff_mem_simplePole_placeInfty` | PROOF-INGREDIENT | idem with row #324; both are `rcases c = 0` + one `omega` |
| 327 | `P1PrincipalPartMOneSimplePoleCancel` | **BESPOKE** | new `def … : Prop` |
| 328 | `instHasPrincipalDivisorsRatFuncSelf` | SUBSTITUTE | port `RationalFunctionField.instHasPrincipalDivisors` (`P1ResidueCore.lean:866`); the Galois route `instHasPrincipalDivisorsOfIsGalois` is **not** ported (Correction 6) |
| 329 | `P1FinitePlaceCanonicalResidueAtomMGeTwoTrace` | **BESPOKE** | new `def … : Prop` |
| 330 | `P1FinitePlaceCanonicalResidueAtomMGeTwoTraceHigherDeg` | **BESPOKE** | new `def … : Prop` |
| 331 | `p1FinitePlaceCanonicalResidueAtomMGeTwoTraceHigherDeg_of_higherDeg` | PROOF-INGREDIENT | row #304, `map_zero`; one line |
| 332 | `p1FinitePlaceCanonicalResidueAtomTrace_of_coordIndep_degOne` | PROOF-INGREDIENT | row #305, `map_zero`; one line |
| 333 | `p1FinitePlaceCanonicalResidueAtomMGeTwoTrace_of_coordIndep_higherDeg` | PROOF-INGREDIENT | rows #331/#332, `Nat.lt_or_ge` |
| 334 | `p1FinitePlaceCanonicalResidueAtomMGeTwoTraceHigherDeg_of_algClosed` | PROOF-INGREDIENT | rows #306/#331; one line |
| 335 | `inv_mem_of_not_mem_centerIdeal` | SUBSTITUTE (private) | `inv_mem_of_not_mem_centerIdeal` (`:498`) |
| 336 | `div_mem_of_not_mem_centerIdeal` | SUBSTITUTE (private) | `div_mem_of_not_mem_centerIdeal` (`:512`) |
| 337 | `Place.centerIdeal_ne_bot_of_isFractionRing` | SUBSTITUTE | `…centerIdeal_ne_bot_of_isFractionRing` (`:519`) |
| 338 | `centerLocalizationSubalgebra_isLocalization` | SUBSTITUTE | `…centerLocalizationSubalgebra_isLocalization` (`:549`) |
| 339 | `centerLocalizationSubalgebra_isDomain` | SUBSTITUTE | `…centerLocalizationSubalgebra_isDomain` (`:553`) |
| 340 | `Place.centerLocalizationSubalgebra_isDiscreteValuationRing` | SUBSTITUTE | `…centerLocalizationSubalgebra_isDiscreteValuationRing` (`:557`) |
| 341 | `centerLocalizationSubalgebra_isFractionRing` | SUBSTITUTE | `…centerLocalizationSubalgebra_isFractionRing` (`:563`) |
| 342 | `Place.centerLocalizationSubalgebra_subset` | SUBSTITUTE | `…centerLocalizationSubalgebra_subset` (`:567`) |
| 343 | `Place.centerLocalizationValuationSubring` | SUBSTITUTE | `…centerLocalizationValuationSubring` (`:577`) |
| 344 | `coe_centerLocalizationValuationSubring` | SUBSTITUTE | `coe_centerLocalizationValuationSubring` (`:587`) |
| 345 | `centerLocalizationValuationSubring_isDiscreteValuationRing` | SUBSTITUTE | `…centerLocalizationValuationSubring_isDiscreteValuationRing` (`:591`) |
| 346 | `Place.centerLocalizationValuationSubring_le` | SUBSTITUTE | `…centerLocalizationValuationSubring_le` (`:596`) |
| 347 | `Place.centerLocalizationValuationSubring_eq` | SUBSTITUTE | `…centerLocalizationValuationSubring_eq` (`:600`) |
| 348 | `coe_centerLocalizationSubalgebra_eq` | SUBSTITUTE | `coe_centerLocalizationSubalgebra_eq` (`:605`) |
| 349 | `Place.mem_centerLocalizationSubalgebra_of_mem` | SUBSTITUTE | `…mem_centerLocalizationSubalgebra_of_mem` (`:611`) |
| 350 | `Place.isLocalization_centerIdeal_of_isDedekindDomain` | SUBSTITUTE | `…isLocalization_centerIdeal_of_isDedekindDomain` (`:616`) |
| 351 | `ValSubringDedekindFractionModel` | SUBSTITUTE | `ValSubringDedekindFractionModel` (`:652`) |
| 352 | `valSubringDedekindModel_of_dedekindFractionModel` | SUBSTITUTE | `valSubringDedekindModel_of_dedekindFractionModel` (`:659`) |
| 353 | `valSubringKaehlerFinite_of_dedekindFractionModel` | PROOF-INGREDIENT | no port copy; one line from #318 (probe H7) |
| 354 | `aeval_root_eq_sum_range` | PROOF-INGREDIENT | `Polynomial.aeval_def`, `eval₂_eq_sum_range'`, `Algebra.smul_def` (probe M) |
| 355 | `trace_adjoinRoot_mk_div_mk_derivative_of_degree_lt` | PROOF-INGREDIENT | `FLT.EulerDualBasis.trace_root_pow_div_derivative_{self,of_lt}` (`P1ResidueCore.lean:88/101`), `AdjoinRoot.powerBasis`, `AdjoinRoot.aeval_eq`, `Finset.sum_eq_single` | `Finset.sum_div` drift, §7 |
| 356 | `finitePlaceResidueFieldAlgEquivAdjoinRoot` | **BESPOKE** | new `def`; body is port `residueFieldEquivOfHeightOneSpectrum` |
| 357 | `finitePlaceResidueFieldAlgEquivAdjoinRoot_mk` | PROOF-INGREDIENT | `rfl` |
| 358 | `trace_finitePlace_residueField_eq_trace_adjoinRoot` | PROOF-INGREDIENT | `Algebra.trace_eq_of_algEquiv`, `AlgEquiv.apply_symm_apply` |
| 359 | `P1FinitePlaceSimplePoleResidueAdjoinRootValue` | **BESPOKE** | new `def … : Prop` |
| 360 | `P1PlaceInftySimplePoleResidueEulerValue` | **BESPOKE** | new `def … : Prop` |
| 361 | `trace_finitePlace_simplePoleResidue_of_adjoinRootValue` | PROOF-INGREDIENT | rows #355/#358, the named carrier #359 |
| 362 | `p1PrincipalPartMOneSimplePoleCancel_of_eulerBridge` | PROOF-INGREDIENT | rows #359/#360/#361, `add_neg_cancel` |
| 363 | `Place.isIntegrallyClosed_toValuationSubring` | SUBSTITUTE | `…isIntegrallyClosed_toValuationSubring` (`:677`); mathlib instance (probe H5) |
| 364 | `Place.mem_valuationSubring_of_isIntegral` | SUBSTITUTE | `…mem_valuationSubring_of_isIntegral` (`:680`) |
| 365 | `Place.modelAlgebra_isScalarTower_top` | SUBSTITUTE | `…modelAlgebra_isScalarTower_top` (`:689`) |
| 366 | `Place.mem_valuationSubring_of_isIntegral_subalgebra` | SUBSTITUTE | `…mem_valuationSubring_of_isIntegral_subalgebra` (`:697`) |
| 367 | `Place.integralClosure_subset_valuationSubring` | SUBSTITUTE | `…integralClosure_subset_valuationSubring` (`:705`) |
| 368 | `IsAffineChart` | SUBSTITUTE | `IsAffineChart` (`:718`) |
| 369 | `ValSubringTwoAffineCharts` | SUBSTITUTE | `ValSubringTwoAffineCharts` (`:721`) |
| 370 | `valSubringDedekindFractionModel_of_twoAffineCharts` | SUBSTITUTE | `valSubringDedekindFractionModel_of_twoAffineCharts` (`:728`) |
| 371 | `valSubringKaehlerFinite_of_twoAffineCharts` | PROOF-INGREDIENT | no port copy; one line from #353 (probe H7) |
| 372 | `Place.coe_toKSubalgebra` | SUBSTITUTE (private) | `…coe_toKSubalgebra` (`:764`) |
| 373 | `gate_adjoin_subset_valuationSubring_of_mem` | SUBSTITUTE | `gate_adjoin_subset_valuationSubring_of_mem` (`:769`) |
| 374 | `Place.simplePoleResidueAux_mul_of_mem` | PROOF-INGREDIENT | `Place.simplePoleResidueAux_apply`, `IsLocalRing.residue`, `map_mul` |
| 375 | `Place.mul_mem_simplePoleSubmodule_of_mem` | PROOF-INGREDIENT | `Place.mem_simplePoleSubmodule`, `mul_mem` |
| 376 | `denom_notMem_of_mem_ofHeightOneSpectrum` | PROOF-INGREDIENT | `IsDedekindDomain.HeightOneSpectrum.{valuation_eq_one_iff_notMem, valuation_lt_one_iff_mem}`, `RatFunc.isCoprime_num_denom`, `RatFunc.num_div_denom` (probe M) |
| 377 | `differentialCoeff_add'` | PROOF-INGREDIENT | `Place.differentialCoeff_unique`, `differentialCoeff_smul_dCoord` |
| 378 | `differentialCoeff_D_algebraMap_polynomial` | PROOF-INGREDIENT | port `D_algebraMap_polynomial` (`:1258`), `Place.differentialCoeff_smul` |
| 379 | `differentialCoeff_D_mem_finitePlace` | PROOF-INGREDIENT | port `denom_sq_smul_D_eq` (`:1265`), row #376, `ord_differentialCoeff_dX_ofHeightOneSpectrum` |
| 380 | `uniformizer_div_mem_finitePlace` | PROOF-INGREDIENT | `Place.{ord_mul, ord_inv, ord_uniformizer, mem_of_ord_nonneg}`, `ord_finitePlace_self` |
| 381 | `one_sub_uniformizer_div_mul_differentialCoeff_D` | PROOF-INGREDIENT | `Derivation.leibniz`, row #377, `div_mul_cancel₀`, `linear_combination` |
| 382 | `uniformizer_div_mul_differentialCoeff_D_mem_finitePlace` | PROOF-INGREDIENT | rows #378/#380, `algebraMap_mem_ofHeightOneSpectrum`, `mul_mem` |
| 383 | `residue_uniformizer_div_mul_differentialCoeff_D_eq_one` | PROOF-INGREDIENT | `IsLocalRing.residue_eq_zero_iff`, `Place.mem_maximalIdeal_iff_adicValuation_lt_one`, row #379 |
| 384 | `residue_algebraMap_derivative_ne_zero` | PROOF-INGREDIENT | `Place.mem_maximalIdeal_iff_adicValuation_lt_one`, `HeightOneSpectrum.valuation_lt_one_iff_mem`, `Polynomial.Separable.isUnit_of_dvd'` |
| 385 | `simplePoleResidueAux_finitePlace_p1PrincipalPartAtom_mOne` | PROOF-INGREDIENT | row #384, `Place.simplePoleResidueAux_apply`, rows #378/#382, `map_mul` |
| 386 | `p1FinitePlaceSimplePoleResidueAdjoinRootValue_dX` | PROOF-INGREDIENT | row #385, `AlgEquiv.symm_apply_eq`, `map_div₀`, row #357 |
| 387 | `p1PrincipalPartMOneSimplePoleCancel_of_inftyBridge` | PROOF-INGREDIENT | rows #362/#386; one line |
| 388 | `Transcendental.isPrincipalIdealRing_adjoin` | SUBSTITUTE (private; `_s12`) | `Transcendental.isPrincipalIdealRing_adjoin_s12` (`:788`) |
| 389 | `Transcendental.isDedekindDomain_adjoin` | SUBSTITUTE (private; `_s12`) | `…isDedekindDomain_adjoin_s12` (`:794`) |
| 390 | `Transcendental.isIntegrallyClosed_adjoin` | SUBSTITUTE (private; `_s12`) | `…isIntegrallyClosed_adjoin_s12` (`:799`) |
| 391 | `Transcendental.isNoetherianRing_adjoin` | SUBSTITUTE (private; `_s12`) | `…isNoetherianRing_adjoin_s12` (`:804`) |
| 392 | `Algebra.FiniteType.adjoin_singleton` | SUBSTITUTE (private; `_s12`) | `Algebra.FiniteType.adjoin_singleton_s12` (`:809`); mathlib `adjoin_of_finite` |
| 393 | `Transcendental.inv` | SUBSTITUTE (private; `_s12`) | `Transcendental.inv_s12` (`:813`); mathlib `IsAlgebraic.inv_iff` |
| 394 | `coe_transcendentalChart` | SUBSTITUTE | `coe_transcendentalChart` (`:826`) |
| 395 | `transcendentalChart_subset_valuationSubring_of_mem` | SUBSTITUTE | `…transcendentalChart_subset_valuationSubring_of_mem` (`:833`) |
| 396 | `transcendentalChart_subset_or_inv_subset` | SUBSTITUTE | `…transcendentalChart_subset_or_inv_subset` (`:840`) |
| 397 | `isScalarTower_integralClosure_subalgebra` | SUBSTITUTE | `isScalarTower_integralClosure_subalgebra` (`:857`); mathlib instance (probe H6) |
| 398 | `finiteType_integralClosure_of_moduleFinite` | SUBSTITUTE | `finiteType_integralClosure_of_moduleFinite` (`:862`) |
| 399 | `isDedekindDomain_integralClosure_adjoin` | SUBSTITUTE | `isDedekindDomain_integralClosure_adjoin` (`:871`) |
| 400 | `isFractionRing_integralClosure_adjoin` | SUBSTITUTE | `isFractionRing_integralClosure_adjoin` (`:877`) |
| 401 | `moduleFinite_integralClosure_adjoin` | SUBSTITUTE | `moduleFinite_integralClosure_adjoin` (`:882`) |
| 402 | `finiteType_integralClosure_adjoin` | SUBSTITUTE | `finiteType_integralClosure_adjoin` (`:891`) |
| 403 | `isAffineChart_restrictScalars_integralClosure` | SUBSTITUTE | `isAffineChart_restrictScalars_integralClosure` (`:897`) |
| 404 | `isAffineChart_transcendentalChart` | SUBSTITUTE | `isAffineChart_transcendentalChart` (`:904`) |

All 59 SUBSTITUTE names are probed in §P1/§P2; the public exact-name copies import through the
existing `P1ResidueCore.lean:31` import.

## 6. Separating transcendental, the `placeInfty` Euler value, and the core (rows #405–#434)

| row | pin decl (line) | class | mathlib / port name | evidence |
|---:|---|---|---|---|
| 405 | `HasSeparatingTranscendental` (8966) | SUBSTITUTE | `HasSeparatingTranscendental` (`HasCanonicalDivisor.lean:918`) | probe P; identical `def` |
| 406 | `valSubringTwoAffineCharts_of_hasSeparatingTranscendental` (8973) | SUBSTITUTE | `…` (`:925`) | probe P |
| 407 | `valSubringKaehlerFinite_of_hasSeparatingTranscendental` (8982) | PROOF-INGREDIENT | no port copy; one line from #371 (probe H7) |
| 408 | `ord_placeInfty_mOneAtom_mul_differentialCoeff_dX` (9050) | PROOF-INGREDIENT | `Place.{ord_mul, differentialCoeff_ne_zero}`, `ord_placeInfty_p1PrincipalPartAtom`, `dX_ne_zero` |
| 409 | `p1MOneAtom_mul_differentialCoeff_dX_mem_placeInfty` (9065) | PROOF-INGREDIENT | row #408, `Place.mem_of_ord_nonneg`; `omega` |
| 410 | `trace_placeInfty_simplePoleResidue_mOne_of_lowDeg` (9095) | PROOF-INGREDIENT | row #409, `Place.simplePoleResidueAux_eq_zero_of_mem`, `Polynomial.coeff_eq_zero_of_natDegree_lt` |
| 411 | `P1PlaceInftySimplePoleResidueEulerValueTopDeg` (9121) | **BESPOKE** | new `def … : Prop` |
| 412 | `P1PlaceInftySimplePoleResidueEulerValueMonomial` (9129) | **BESPOKE** | new `def … : Prop` |
| 413 | `p1PrincipalPartAtom_add_mul_differentialCoeff` (9147) | PROOF-INGREDIENT | `map_add`, `ring` |
| 414 | `p1PrincipalPartAtom_C_mul_mul_differentialCoeff` (9161) | PROOF-INGREDIENT | `map_mul`, `Polynomial.C_eq_algebraMap`, `IsScalarTower.algebraMap_apply`, `ring` |
| 415 | `trace_placeInfty_simplePoleResidueAux_mOne_add` (9173) | PROOF-INGREDIENT | row #413, `map_add` |
| 416 | `trace_placeInfty_simplePoleResidueAux_mOne_C_mul` (9192) | PROOF-INGREDIENT | row #414, `map_smul`, `smul_eq_mul` |
| 417 | `p1PlaceInftySimplePoleResidueEulerValue_of_topDeg` (9207) | PROOF-INGREDIENT | row #410, the named carrier #411, `omega` |
| 418 | `p1PlaceInftySimplePoleResidueEulerValueTopDeg_of_monomial` (9219) | PROOF-INGREDIENT | rows #412–#417, `Polynomial.{eraseLead_add_C_mul_X_pow, eraseLead_natDegree_lt_or_eraseLead_eq_zero, leadingCoeff, coeff_eq_zero_of_natDegree_lt}`, `p1MOneAtom_mul_differentialCoeff_mem_simplePole_placeInfty` (#326) |
| 419 | `p1PlaceInftySimplePoleResidueEulerValue_of_monomial` (9275) | PROOF-INGREDIENT | rows #417/#418; one line |
| 420 | `p1PrincipalPartMOneSimplePoleCancel_of_inftyMonomial` (9291) | PROOF-INGREDIENT | rows #387/#419, `ordDifferential_placeInfty_D_ratFuncX` |
| 421 | `IntermediateField.adjoin_simple_inv` (9330) | SUBSTITUTE (`_s12`) | `IntermediateField.adjoin_simple_inv_s12` (`:948`) |
| 422 | `IntermediateField.algebraMap_comp_equivOfEq` (9337) | SUBSTITUTE (`_s12`) | `…algebraMap_comp_equivOfEq_s12` (`:955`) |
| 423 | `IntermediateField.finiteDimensional_of_eq` (9342) | SUBSTITUTE (`_s12`) | `…finiteDimensional_of_eq_s12` (`:960`) |
| 424 | `IntermediateField.isSeparable_of_eq` (9347) | SUBSTITUTE (`_s12`) | `…isSeparable_of_eq_s12` (`:965`) |
| 425 | `IntermediateField.finiteDimensional_adjoin_inv` (9352) | SUBSTITUTE (`_s12`) | `…finiteDimensional_adjoin_inv_s12` (`:970`) |
| 426 | `IntermediateField.isSeparable_adjoin_inv` (9356) | SUBSTITUTE (`_s12`) | `…isSeparable_adjoin_inv_s12` (`:974`) |
| 427 | `isSeparable_of_charZero_of_finiteDimensional` (9371) | PROOF-INGREDIENT | `IntermediateField.charZero`, `Algebra.IsSeparable.of_integral` (probe H3) |
| 428 | `isSeparable_adjoin_of_charZero_of_finiteDimensional` (9377) | PROOF-INGREDIENT | row #427; one line |
| 429 | `HasSeparatingTranscendentalCore` (9388) | **BESPOKE** | new `def … : Prop` |
| 430 | `hasSeparatingTranscendental_of_core` (9393) | PROOF-INGREDIENT | row #427, `IntermediateField.{finiteDimensional,isSeparable}_adjoin_inv_s12` (probe H9) |
| 431 | `valSubringKaehlerFinite_of_core` (9403) | PROOF-INGREDIENT | rows #407/#430; one line |
| 432 | `ord_placeInfty_X_pow_natDegree_div` (9469) | PROOF-INGREDIENT | `Place.{ord_mul, ord_inv}`, `ord_placeInfty_algebraMap'` (`:588`), `natDegree_X_pow` |
| 433 | `X_pow_natDegree_div_mem_placeInfty` (9482) | PROOF-INGREDIENT | row #432, `Place.mem_of_ord_nonneg` |
| 434 | `degree_X_pow_natDegree_sub_lt_of_monic` (9493) | PROOF-INGREDIENT | `Polynomial.degree_X_pow`, `degree_eq_natDegree`, `Polynomial.degree_sub_lt` (deprecated, §7), `leadingCoeff_X_pow` (probe H2) |

## 7. Reuse wins, with probe evidence

### 7.1 The whole ℙ¹ Kähler block is mathlib-only (rows #292–#296)

Probe H1 transcribes the pin's five declarations verbatim with `open Polynomial
KaehlerDifferential Module` and discharges `instIsCurveOverRatFunc` through the port's own
`RationalFunctionField.isCurveOver_of_kaehlerRankOne` (`P1ResidueCore.lean:1646`). The pin's
`kaehlerPolynomialBasis`/`kaehlerRatFuncBasis` are `(Basis.singleton _ _).map
(polynomialEquiv K).symm` and its `baseChange`/`tensorKaehlerEquivOfFormallyEtale` image;
`kaehlerRankOne_ratFunc` is `Module.Free.of_basis` + `Module.finrank_eq_card_basis`. No new
mathematics, no pin prelude — the same finding as `AUDIT-mathlib-p2.md` §3.1 for the two
`KaehlerTranscendental` headlines.

### 7.2 The Dedekind-model block is phase-P2 output (rows #307–#404)

`Canonical/HasCanonicalDivisor.lean` already carries 59 of the 98 rows, with the phase-2 pin
file's own `_s12` names and the master file's exact names for the public copies. The 10 private
ones need promotion (Correction 3). The two Kähler wrappers #318/#353/#371/#407 are the only
*new* declarations in the block, and all four are one-liners over the existing
`valSubringKaehlerFinite_of_essFiniteType`/`_of_finiteTypeModel` engines (probe H7). This is the
same pattern 3.2c found for its `KaehlerRankOne` wrappers.

### 7.3 The fibre dictionary answers the ramification–inertia wrappers (rows #297–#299)

`Place.sum_ramificationIndex_mul_inertiaDeg_fiberOver` (`FiberOverCount.lean:33`) already proves
the ℤ-valued inertia sum over `v.fiberOver F'`, and `Place.mem_fiberOver`
(`PlacesOverDVR.lean:430`) is exactly `w ∈ v.fiberOver F' ↔ w.restrict F = v`. So the pin's
arbitrary `Finset s` with `∀ w, w ∈ s ↔ w.restrict F = v` is that fibre by `Finset.ext`, and
#297 is one rewrite (probe H10). #298 is the pin's `deg` conversion over
`Place.deg_restrict_mul_inertiaDeg` (`PushPull.lean:460`, probe H11), and #299 is the one-line
instance of the port's own `RamificationInertiaIdentity` (probe H12). Do **not** re-transcribe
the pin's 42-line `Finset.sum_bij` proof against `Ideal.ramificationIdx`/`inertiaDeg` — that
assembly is already in `FiberOverCount.lean:44–100` in its v4.34 form.

### 7.4 The `AdjoinRoot` trace engine is chunk-1 output (rows #354–#358)

The pin's `aeval_root_eq_sum_range` and
`trace_adjoinRoot_mk_div_mk_derivative_of_degree_lt` rest on
`FLT.EulerDualBasis.trace_root_pow_div_derivative_self` (`P1ResidueCore.lean:101`) and
`…_of_lt` (`:88`), which are inventory rows #4/#5, already ported in chunk 1. The only new
ingredient is the `AdjoinRoot`-vs-`PowerBasis` bookkeeping (`AdjoinRoot.powerBasis`,
`AdjoinRoot.aeval_eq`, `AdjoinRoot.minpoly_powerBasis_gen_of_monic`), all mathlib (probe M).

### 7.5 `instHasPrincipalDivisorsRatFuncSelf` is already an instance (row #328)

The port's ℙ¹ base case `RationalFunctionField.instHasPrincipalDivisors`
(`P1ResidueCore.lean:866`, phase 3.2c row #156) is the same class and type as the pin's #328.
The pin's Galois route (`instHasPrincipalDivisorsOfIsGalois`, itself one line from #299) is not
ported and is not needed; land #328 as a scoped-instance alias so the checker sees the pin
name.

## 8. Route options

- **R1 — import `Canonical/HasCanonicalDivisor.lean` for all 59 SUBSTITUTE rows of
  #307–#404.** Add aliases for the exact-name declarations the checker compares (the public
  ones already carry the pin's exact names; the `_s12` ones need a name-translation alias, and
  the 10 private ones need promotion first). Do not re-prove any of them.
- **R2 — promote, do not re-transcribe, the 10 private `HasCanonicalDivisor` helpers**
  (`ofPrime_congr_s12`, `inv_mem_of_not_mem_centerIdeal`, `div_mem_of_not_mem_centerIdeal`,
  `coe_toKSubalgebra`, the `Transcendental.*_adjoin_s12` family,
  `Algebra.FiniteType.adjoin_singleton_s12`, `Transcendental.inv_s12`). Single-keyword edits,
  no collisions; the same route 3.2d′ chose.
- **R3 — the four Kähler wrappers #318/#353/#371/#407 are 1–2 lines each.** Write them in pin
  order so #407 and #431 can consume #371.
- **R4 — #297–#299: use the fibre engine, not the pin's `Finset.sum_bij`.** `Finset.ext` +
  `Place.mem_fiberOver` + `sum_ramificationIndex_mul_inertiaDeg_fiberOver` (probe H10) is the
  shortest faithful route; the pin's `Ideal.sum_ramification_inertia` call is a v4.33 name that
  no longer exists (§9).
- **R5 — the char-0 separability tail (#427–#434) is four one-liners plus two `def`s.**
  `IntermediateField.charZero` + `Algebra.IsSeparable.of_integral` answers #427; the rest is
  composition.
- **R6 — the genuinely new mathematics is the ℙ¹ principal-part/residue cone
  (#321–#327, #354–#362, #374–#387, #408–#420) plus the ℙ¹ capstone #321.** Every proof in
  those blocks is a named assembly over the already-ported `Place.differentialCoeff`/
  `p1PrincipalPartAtom`/`simplePoleResidueAux` API; the only new statements are the nine
  `def`s/`Prop`s listed in §1.

## 9. API drift (`v4.34.0`) — what the worker must change

| pin call / assumption | `v4.34.0` status | worker action |
|---|---|---|
| `Ideal.sum_ramification_inertia` (row #297's proof, pin line 6869) | **does not exist**; renamed/re-shaped to `Ideal.sum_ramification_inertia_eq_finrank` (`RingTheory/RamificationInertia/Basic.lean:72`), which sums over the subtype `p.primesOver S` with `ℕ`-valued `ramificationIdx`/`inertiaDeg` and needs `[IsDomain R] [Module.Finite R S] [Module.Flat R S] [Fintype (p.primesOver S)]`. `Ideal.sum_ramification_inertia_eq_finrank_fiber` (`:44`) is the fibre form | `WeilExchange/FiberOverCount.lean:33–100` already carries the two bridges (`IsDedekindDomain.coe_primesOverFinset` + `Finset.sum_subtype`, `IsFractionRing.finrank_eq`). Reuse them (route R4) or take the one-line `fiberOver` route |
| `Polynomial.degree_sub_lt` (row #434, and the §H2 probe) | **deprecated** toward `Polynomial.degree_sub_lt_left` (probe warning) | transcribe the pin, or switch to `degree_sub_lt_left`; keep the warning list clean |
| generic `Finset.sum_div` (row #355's proof, pin line 8151) | **does not exist** in v4.34 (only `Nat.sum_div` and `ENNReal.sum_div`; `Finset.sum_mul`/`div_eq_mul_inv` exist) | replace by `div_eq_mul_inv` + `Finset.sum_mul` (or prove the division push in place); recorded negative 7 |
| `RationalFunctionField.instHasPrincipalDivisorsOfIsGalois` (row #328) | **not ported** (grep 0) | land #328 as a scoped-instance alias of the existing `RationalFunctionField.instHasPrincipalDivisors` (`P1ResidueCore.lean:866`); do not rebuild the Galois route |
| `Ideal.ramificationIdx'` / `Ideal.inertiaDeg'` | half-migrated (3.2c §15): the primed pin text is kept under `set_option linter.deprecated false` in `PlaceDictionary`/`FiberOverCount` | this chunk's row #297 statement does not mention the primed names; the proof may keep the `FiberOverCount` bridges |
| `if_pos` / `if_neg` | renamed `ite_eq_left` / `ite_eq_right` (drift table) | not used in rows #290–#434 |
| `open scoped IntermediateField.algebraAdjoinAdjoin` alone | the `K⟮t⟯` notation did **not** elaborate in the probe until `open IntermediateField` was added alongside it (same as `SeparatingTranscendental.lean:37` which opens both) | the new module must `open IntermediateField` (or the concrete `IntermediateField.adjoin K {t}` spelling) for rows #427–#431 |
| `linter.style.haveILetI` on the `haveI : Algebra.IsSeparable K⟮t⟯ F` of row #430 (probe H9) | fires on a `Prop` goal | keep `haveI` (instance search needs it inline) and `set_option linter.style.haveILetI false` as the phase-1/2 modules do; do not weaken to `have` |

No other drift: the file names no other deprecated constant, and probes M/H resolve at the pin
spellings (`IsDedekindDomain.HeightOneSpectrum.valuation_*` resolves both qualified and through
`open IsDedekindDomain`; `IsAlgClosed.degree_eq_one_of_irreducible`,
`AdjoinRoot.minpoly_powerBasis_gen_of_monic`, `Polynomial.eraseLead_*` all resolve).

## 10. Recorded negatives

Confirmed against mathlib `v4.34.0` and the port; phrased so the search is not repeated.

1. **No `ofPrime_congr` / `eq_top_of_idealOfLE_eq_bot` / `idealOfLE_ne_bot_of_ne_top` /
   `eq_of_isDiscreteValuationRing_of_le` under those exact names in the port** — only the
   `_s12` copies in `HasCanonicalDivisor.lean:372–385`, and `ofPrime_congr_s12` is `private`.
   Landing the master names is a name-translation job, not new mathematics.
2. **No port `P1DifferentialCoeffUnitFinite` (`P1DifferentialCoeffRegularFinite` is a different
   def), no `kaehlerPolynomialBasis` / `kaehlerRatFuncBasis` / `kaehlerRankOne_ratFunc` /
   `instIsCurveOverRatFunc`, and no `valSubringKaehlerFinite_of_{dedekindModel,
   dedekindFractionModel, twoAffineCharts, hasSeparatingTranscendental, core}`.** These are the
   chunk's new names; the Kähler ones are mathlib-only.
3. **No port `instHasPrincipalDivisorsOfIsGalois`.** The ℙ¹ `HasPrincipalDivisors` instance
   exists only as `RationalFunctionField.instHasPrincipalDivisors`
   (`P1ResidueCore.lean:866`); the Galois variant is not needed.
4. **No port counterpart for `ordDifferentialWellDefined_ratFunc_of_perfectField` (#321),
   `p1DifferentialCoeffUnitFinite_dX` (#322), the `mOneAtom`/simple-pole rows (#323–#326), the
   `Trace`/`Cancel` predicates (#327, #329–#334), the `AdjoinRoot` trace engine (#354–#362),
   the finite-place residue engine (#374–#387), the `placeInfty` Euler-value cone (#408–#420),
   the char-0 separability leaves (#427/#428), `HasSeparatingTranscendentalCore` (#429) or the
   monic-ratio rows (#432–#434).** `#check` errors on every one; they are the chunk's real
   work. The pin-`private` ones (`simplePoleResidueAux_mul_of_mem`, `mul_mem_simplePoleSubmodule_of_mem`,
   `differentialCoeff_add'`) stay `private`.
5. **No mathlib `Ideal.sum_ramification_inertia`** — only
   `Ideal.sum_ramification_inertia_eq_finrank` / `…_eq_finrank_fiber` / `…_eq_card`
   (`RingTheory/RamificationInertia/Basic.lean:44/72/81`), stated over `p.primesOver S` rather
   than the pin's `Finset`+`∀w` (see §9). The pin's doc-site name is a v4.33 spelling.
6. **No mathlib `IsLocalRing.residue_mul`.** `IsLocalRing.residue` is a `RingHom`, so the
   multiplication law is `map_mul _ _ _` (probe M negative; rows #374/#385 use it).
7. **No generic `Finset.sum_div` in v4.34.** Only `Nat.sum_div` (protected, `namespace Nat`) and
   `ENNReal.sum_div` exist; `Finset.sum_mul` and `div_eq_mul_inv` are the leaves (probe M
   negative). Row #355 must route around it.
8. **No mathlib `KaehlerRankOne`, `ValSubringKaehlerFinite`, `ValSubringDedekindModel`,
   `ValSubringTwoAffineCharts`, `IsAffineChart`, `HasSeparatingTranscendental`,
   `HasSeparatingTranscendentalCore`, `transcendentalChart` or `centerIdeal`** — reconfirms
   `AUDIT-mathlib-p2.md` §5.3. The nearest mathlib objects are the generic
   `KaehlerDifferential`/`Algebra.FormallyEtale` API and the `integralClosure` API.
9. **No mathlib `P1DifferentialCoeffUnitFinite` / `P1DifferentialCoeffRegularFinite` /
   `P1PrincipalPartMOneSimplePoleCancel` / `P1FinitePlaceSimplePoleResidueAdjoinRootValue` /
   `P1PlaceInftySimplePoleResidueEulerValue*`** — the pin's ℙ¹ vocabulary has no mathlib
   analogue; all are port-local.
10. **No mathlib packaging of the Euler-dual-basis trace** (`∃ b, b () = D K F x`): the pin
    duplicates its `exists_basis` prelude across files and the port homed it once in
    `Defs/KaehlerTranscendental.lean`; this chunk's #354/#355 are the `AdjoinRoot` concretisation
    of chunk-1's `FLT.EulerDualBasis.*`, not a new search.
11. **`Algebra.FiniteType.adjoin_singleton` is not a mathlib name** (negative 7 of
    `AUDIT-mathlib-p2.md`); only `Algebra.FiniteType.adjoin_of_finite`, which is the port's
    `adjoin_singleton_s12` body.
12. **`IsIntegrallyClosed v.toValuationSubring` and `IsScalarTower K B ↥(integralClosure B F)`
    are mathlib instances** (probes H5/H6, reconfirming `AUDIT-mathlib-p2.md` §3.3–3.4). Rows
    #363/#397 are SUBSTITUTE by `inferInstance`.

## 11. What this changes for `WORKORDER-P3-2d-p1core-3.md`

**Scope / measurement.**

- 145 rows: **67 SUBSTITUTE / 65 PROOF-INGREDIENT / 13 BESPOKE**.
- The content list in §0 omits rows **#307–#404** (98 rows, the abstract canonical-divisor
  development). They are in scope (they are in the master `S_` file between #306 and #405) and
  59 of them are imports from `Canonical/HasCanonicalDivisor.lean`. The work order's reuse
  paragraph is right that the block is phase-P2 output, but it does not say how large it is or
  that 7 of its copies are `private`.
- The `P1DifferentialCoeffUnitFinite` name is confirmed as row #290 (3.2c Correction 1).

**Discharged proofs (mark import-discharged; the statements still land).**

- rows #307–#404 — import `Canonical/HasCanonicalDivisor.lean`; **promote** the 10 private
  helpers (R2) or keep local aliases; the public copies import through the existing
  `P1ResidueCore.lean:31` import;
- rows #319/#320 — import `Defs/CanonicalLocalResidueInstanceV2.lean`;
- row #328 — scoped-instance alias of `RationalFunctionField.instHasPrincipalDivisors`;
- rows #297–#299 — one-liners off `WeilExchange/FiberOverCount.lean` (R4).

**New work, budgeted.**

- rows #290–#296 (the ℙ¹ Kähler basis block; mathlib-only, probes H1);
- rows #300–#306 (the degree-one/principal-part computation);
- rows #321–#327, #329–#334 (the ℙ¹ capstone and the mOne/trace predicates);
- row #318, #353, #371, #407 (the four Kähler wrappers; 1–2 lines each);
- rows #354–#362 (the `AdjoinRoot` trace engine and the Euler bridge);
- rows #374–#387 (the finite-place residue engine, including the `Finset.sum_div` workaround);
- rows #408–#420 (the `placeInfty` Euler value and eraseLead linearity);
- rows #427–#434 (the char-0 separability and core tail).

**Imports the worker may use.** The port modules
`Defs/{P1ResidueCore, CanonicalLocalResidueInstanceV2, P1Dictionary, PushPull, PlacesOverDVR}`,
`Canonical/HasCanonicalDivisor`, `WeilExchange/FiberOverCount`, plus, on the mathlib side,
`Mathlib.RingTheory.Kaehler.{Basic,Polynomial}`, `Mathlib.RingTheory.Etale.{Kaehler,Field,Basic}`,
`Mathlib.RingTheory.AdjoinRoot`, `Mathlib.FieldTheory.{Perfect,PrimitiveElement,Separable}`,
`Mathlib.RingTheory.DedekindDomain.AdicValuation` (for `HeightOneSpectrum.valuation_*`),
`Mathlib.RingTheory.RamificationInertia.{Inertia,Ramification,Basic}`,
`Mathlib.RingTheory.Valuation.{ValuationSubring,LocalSubring}`,
`Mathlib.RingTheory.DiscreteValuationRing.Basic`,
`Mathlib.RingTheory.Localization.AtPrime.Basic`,
`Mathlib.RingTheory.IntegralClosure.IntegrallyClosed`,
`Mathlib.Algebra.Polynomial.{Derivative,Degree.Domain,Degree.Operations,EraseLead}`,
`Mathlib.Algebra.BigOperators.Ring.Finset`. Do **not** import
`Mathlib.RingTheory.LaurentSeries` or `Mathlib.Algebra.Polynomial.PartialFractions` — they are
off this chunk's path (rows #354–#387 use `AdjoinRoot`/`PowerBasis`, not Laurent series or
partial fractions).

**Checker wiring.** Already done per the order: the master `S_` file and wrapper are in
`SOURCES`, and `Defs/P1ResidueCore.lean` is in `PORT_FILES`. The new public surface to
reconcile is rows #290–#296, #300–#306, #318, #321–#334, #353, #354–#362, #371, #374–#387,
#407–#420, #427–#434; the 59 block-C SUBSTITUTE statements verify through the checker's
name-translation fallback (record the `_s12` translations explicitly, as 3.2d′ did), and the 10
promotions verify through the dotted-name fallback.

**Stop-early.** The two unanticipated items are (a) the 98-row duplicate block (Correction 1) —
a worker who reads the brief's content list may under-scope by two thirds; and (b) the
`Ideal.sum_ramification_inertia` rename (negative 5) — a worker transcribing row #297's proof
verbatim will not compile. Both are resolved by routes R1/R4.

## 12. Appendix — module map for the named constants

| name | module |
|---|---|
| `KaehlerDifferential.{polynomialEquiv, tensorKaehlerEquivOfFormallyEtale, mvPolynomialBasis, map, map_D, map_surjective, D, span_range_derivation, finite, span_range_map_derivation_of_isLocalization}` | `Mathlib/RingTheory/Kaehler/{Basic,Polynomial}.lean` |
| `Algebra.FormallyEtale.*`, `Algebra.FormallyUnramified.*` | `Mathlib/RingTheory/Etale/{Kaehler,Field,Basic}.lean` |
| `Module.Basis.{singleton, baseChange, map, span_eq, ne_zero}`, `Module.{Free.of_basis, finrank_eq_card_basis}` | `Mathlib/LinearAlgebra/Basis/Basic.lean`, `Mathlib/LinearAlgebra/FiniteDimensional/Basic.lean`, `Mathlib/LinearAlgebra/TensorProduct/Basis.lean` |
| `RatFunc.{algEquivOfTranscendental, algEquivOfTranscendental_X, algebraMap_X}` | `Mathlib/FieldTheory/RatFunc/AsPolynomial.lean` |
| `PerfectField.{ofCharZero, separable_of_irreducible}`, `Algebra.IsAlgebraic.isSeparable_of_perfectField`, `exists_isTranscendenceBasis_and_isSeparable_of_perfectField` | `Mathlib/FieldTheory/{Perfect,SeparablyGenerated}.lean` |
| `Algebra.IsSeparable.{of_integral, of_equiv_equiv}`, `IntermediateField.{charZero, equivOfEq, adjoin_simple_le_iff, mem_adjoin_simple_self}`, `Module.Finite.of_equiv_equiv`, `IsAlgebraic.inv_iff` | `Mathlib/FieldTheory/Separable.lean`, `Mathlib/FieldTheory/IntermediateField/*.lean`, `Mathlib/FieldTheory/Algebraic.lean` |
| `Polynomial.{derivative*, Monic.eq_X_add_C, degree_eq_natDegree, eq_C_of_degree_le_zero, natDegree_lt_natDegree, coeff_eq_zero_of_natDegree_lt, leadingCoeff, eraseLead*, degree_X_pow, natDegree_X_pow, degree_sub_lt, leadingCoeff_X_pow, X_ne_zero, C_eq_algebraMap, aeval_def, eval₂_eq_sum_range'}` | `Mathlib/Algebra/Polynomial/{Derivative,Degree/Domain,Degree/Operations,EraseLead}.lean` |
| `ValuationSubring.{idealOfLE, ofPrime_*, eq_of_le_of_ne_top, mem_or_inv_mem, prime_idealOfLE}`, `ValuationRing.isInteger_or_isInteger`, `Valuation.map_add_of_distinct_val` | `Mathlib/RingTheory/Valuation/{ValuationSubring,Basic}.lean` |
| `isIntegrallyClosed_iff`, `IsIntegral.tower_top`, `integralClosure.{isDedekindDomain, isFractionRing_of_finite_extension}`, `IsIntegralClosure.finite` | `Mathlib/RingTheory/IntegralClosure/*.lean` |
| `IsPrincipalIdealRing.{of_surjective, isDedekindDomain}`, `IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain`, `IsLocalRing.eq_maximalIdeal` | `Mathlib/RingTheory/{PrincipalIdealDomain,Localization/AtPrime/Basic,LocalRing/Basic}.lean` |
| `AdjoinRoot.{mk, root, aeval_eq, powerBasis, minpoly_powerBasis_gen_of_monic, powerBasis_dim, powerBasis_gen}` | `Mathlib/RingTheory/AdjoinRoot.lean` |
| `Algebra.trace`, `Algebra.trace_eq_of_algEquiv` | `Mathlib/LinearAlgebra/Trace.lean`, `Mathlib/FieldTheory/Trace.lean` |
| `Field.exists_primitive_element`, `minpoly.{monic, aeval}` | `Mathlib/FieldTheory/PrimitiveElement.lean`, `Mathlib/FieldTheory/Minpoly/*.lean` |
| `IsDedekindDomain.HeightOneSpectrum.{valuation_eq_one_iff_notMem, valuation_lt_one_iff_mem}` | `Mathlib/RingTheory/DedekindDomain/AdicValuation.lean` |
| `Ideal.{sum_ramification_inertia_eq_finrank, sum_ramification_inertia_eq_finrank_fiber, inertiaDeg, ramificationIdx}` | `Mathlib/RingTheory/RamificationInertia/{Basic,Inertia,Ramification}.lean` |
| `IsDedekindDomain.mem_primesOverFinset_iff`, `Finset.{sum_bij, sum_congr, mul_sum, sum_eq_single, sum_mul}` | `Mathlib/RingTheory/DedekindDomain/*.lean`, `Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean` |
| `FLT.EulerDualBasis.{trace_root_pow_div_derivative_self, trace_root_pow_div_derivative_of_lt}` | `FLTForHuman/AlgebraicCurve/Defs/P1ResidueCore.lean:88/101` |
