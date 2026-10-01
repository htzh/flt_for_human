# Mathlib-first substitution audit — the P3.2f ℙ¹ sibling atom tails

**Method:** [`lean/porting-playbook.md`](../porting-playbook.md) §2.2 (audit the route,
mathlib first), after the phase-1/2/3.1/3.2a–3.2e templates
[`AUDIT-mathlib.md`](AUDIT-mathlib.md), [`AUDIT-mathlib-p2.md`](AUDIT-mathlib-p2.md),
[`AUDIT-mathlib-p3-1.md`](AUDIT-mathlib-p3-1.md),
[`AUDIT-mathlib-p3-2a.md`](AUDIT-mathlib-p3-2a.md),
[`AUDIT-mathlib-p3-2b.md`](AUDIT-mathlib-p3-2b.md),
[`AUDIT-mathlib-p3-2c.md`](AUDIT-mathlib-p3-2c.md),
[`AUDIT-mathlib-p3-2d.md`](AUDIT-mathlib-p3-2d.md),
[`AUDIT-mathlib-p3-2dprime.md`](AUDIT-mathlib-p3-2dprime.md) and
[`AUDIT-mathlib-p3-2e.md`](AUDIT-mathlib-p3-2e.md) (whose §19 is the format this note
answers). Pin: `anthropics/fermats-last-theorem@aa2d8b3` (read-only clone at
`~/proj/fermats-last-theorem`); port mathlib `v4.34.0`
(`lean/.lake/packages/mathlib`). Work order:
[`WORKORDER-P3-2f-tails.md`](WORKORDER-P3-2f-tails.md). Pre-port measurements:
[`tools/deps/build/p32f_atom2.log`](../../../tools/deps/build/p32f_atom2.log),
[`p32f_atom3.log`](../../../tools/deps/build/p32f_atom3.log),
[`p32f_pfbase.log`](../../../tools/deps/build/p32f_pfbase.log) (and the matching
`.json`, from `port_advise.py --target P2M/Sol/<file>`).

**Sources.** The three sibling `S_` files and their one-declaration `Theorems/` wrappers.
They are *siblings* of the already-ported master ℙ¹ file, not copies of it: each shares a
long prelude with the master (now the `P1/` chain) and ends in a unique tail.

- [`P2M/Sol/S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_add_trace_localResidue_placeInfty_eq_zero.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_add_trace_localResidue_placeInfty_eq_zero.lean)
  (5,776 ln; atom 2, the two-place ending),
- [`P2M/Sol/S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.lean)
  (2,150 ln; atom 3, the higher-pole `div_pow` ending),
- [`P2M/Sol/S_AlgebraicCurve_residueTheorem_ratFunc_of_perfectField.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_residueTheorem_ratFunc_of_perfectField.lean)
  (4,340 ln; the perfect-field base case).

**Baseline.** The audit is measured against the `port_advise` corpus as of the `p32f_*`
logs, i.e. the `P1/` chain *before* the three new tail modules land. The port already
contains the master engine: `P1/{Adjoin,Core,DXCoeff,Dictionary,Differential,DivisorAction,EnginePrelude,FinitePlaceResidue,KaehlerIntegral,PerfectField,PerfectPrelude,PerfectResidue,Separating,TraceEngine,UnitFinite,UnitNormalForm}.lean`,
plus `Defs/{Place,PushPull,PlacesOverDVR,LocalResidue,…}.lean`,
`LocalResidue/{Instance,Calculus}.lean`,
`PrincipalDivisors/RatFuncDegree.lean`, `Canonical/HasCanonicalDivisor.lean`,
`Genus/Index.lean`. The audit deliberately ignores the three in-flight tail modules
(`P1/TwoPlace.lean` and the forthcoming `P1/DivPow.lean`, `P1/PerfectBase.lean`); every
"absent from the port" claim below is relative to that pre-tail baseline. (The audit was
written while a parallel worker was landing `P1/TwoPlace.lean`; its rows are the
`NEW` rows of §4 and the tables do not cite it.)

**Class convention** (unchanged from phases 1–3.2e). SUBSTITUTE = the port can import an
existing declaration instead of proving the row (a port lemma, or a pin `def`/instance
`rfl`-equal to a port term). A statement that differs from the port copy only by binder
spelling, notation, or the `p1PlaceInfty` ↔ `placeInfty` alias counts SUBSTITUTE with the
difference recorded. PROOF-INGREDIENT = the statement is bespoke (it mentions pin
vocabulary) but the proof is a short assembly of named mathlib/port lemmas. BESPOKE = a
new `def`/`structure`/`Prop`/class/instance introducing vocabulary. The audit adds a
fourth, because the three tails are *siblings*: IMPORT/ADAPT = the port already declares
the row under the same last name at its own binder spelling, so the worker imports it and
must **not** re-declare it.

**Scratch evidence.** A scratch file (gitignored, ~135 probes, deleted after use) was
compiled from `lean/` with

```bash
timeout 600 lake env lean -DmaxHeartbeats=4000000 -DautoImplicit=false ScratchAuditP32f.lean
```

**final run clean, exit 0** (no errors, no warnings). The probe ledger:

- **A** — the port substitutes and their exact namespaces, all `#check`ed:
  `AlgebraicCurve.RationalFunctionField.placeInfty_eq_p1PlaceInfty`,
  `AlgebraicCurve.Place.{ord_neg, ord_eq_neg_log_of_valuationSubring_eq, simplePoleResidueAux_apply, mem_iff_ord_nonneg}`,
  `AlgebraicCurve.RationalFunctionField.{ord_ofHeightOneSpectrum_eq_neg_log, ord_ofHeightOneSpectrum_of_span, eq_ofHeightOneSpectrum_or_eq_placeInfty, placeInfty_ne_ofHeightOneSpectrum}`,
  `AlgebraicCurve.{kaehlerRatFuncBasis, dX, surjective_algebraMap_residueField_of_deg_eq_one, gate_canonicalLocalResidueDataK_uniformizer_inv, ord_placeInfty_X_inv, ordDifferential_placeInfty_D_ratFuncX, one_le_ord_placeInfty_p1PrincipalPartAtom, kaehlerResidueTerm}`,
  `AlgebraicCurve.{ResidueTheorem, ResidueTheoremK}`,
  `FLT.AlgebraicCurve.{p1PartialFractionSpan_eq_top, P1PrincipalPartGenerators, P1PolynomialGenerators, P1PartialFractionGenerators}`.
- **M** — the mathlib `#check` ledger, all present in `v4.34.0`:
  `Polynomial.{aeval, comp_eq_aeval, aeval_algebraMap_apply, comp_eq_zero_iff, C_comp, X_comp, derivative_map, derivative_sub, derivative_C, aeval_map_algebraMap, aeval_C, aeval_def, aeval_mem_adjoin_singleton, aeval_eq_sum_range', Monic.sub_of_left, degree_C, degree_map, degree_eq_natDegree, transcendental_X, separable_def, isCoprime_iff_aeval_ne_zero_of_isAlgClosed, exists_eq_pow_rootMultiplicity_mul_and_not_dvd, rootMultiplicity, rootMultiplicity_X_sub_C, dvd_iff_isRoot, X_dvd_iff, isUnit_C, natDegree_eq_zero_of_isUnit, eq_of_monic_of_dvd_of_natDegree_le, natDegree_lt_natDegree}`,
  `natDegree_sub_eq_left_of_natDegree_lt`, `Polynomial.C_eq_algebraMap`,
  `RatFunc.{liftAlgHom, liftAlgHom_apply, num_algebraMap, denom_algebraMap, algebraMap_X, induction_on, X_ne_zero}`,
  `IntermediateField.{algebra_adjoin_le_adjoin, adjoin.finiteDimensional, topEquiv, equivOfEq, adjoin.powerBasis, adjoin.powerBasis_gen, adjoin.powerBasis_dim, adjoin.finrank}`,
  `Algebra.IsIntegral.{of_finite, isIntegral}`, `Module.finrank_eq_card_basis`,
  `IsScalarTower.{of_algebraMap_eq, algebraMap_apply}`, `IsFractionRing.injective`,
  `minpoly.{aeval, monic, degree_le, dvd}`, `PowerBasis.{map, map_dim}`,
  `Valuation.{map_neg, map_add_of_distinct_val}`, `WithZero.log_le_log`,
  `IsLocalRing.{residue, residue_eq_zero_iff}`, `Derivation.{map_aeval, leibniz_div}`,
  `KaehlerDifferential.{span_range_derivation, polynomialEquiv, tensorKaehlerEquivOfFormallyEtale}`,
  `Algebra.FormallyEtale.of_isLocalization`, `Module.Basis.singleton`,
  `Submodule.eq_top_iff'`, `Set.union_subset`, `LinearMap.{ext, mem_ker}`,
  `Submodule.span_le`, `finsum_eq_finsetSum_of_support_subset`, `Finset.sum_pair`,
  `Fintype.linearIndependent_iff`, `LinearIndependent.fintype_card_le_finrank`,
  `Finset.sum_filter_of_ne`, `Int.eq_zero_of_dvd_of_natAbs_lt_natAbs`.
- **H** — compile-checked prototypes: `placeInfty K = p1PlaceInfty K` by `rfl`; the
  one-line wrapper shape a pin twin needs
  (`rw [RationalFunctionField.placeInfty_eq_p1PlaceInfty]; exact AlgebraicCurve.ord_placeInfty_X_inv K`);
  and `ord_neg'` (atom 3) discharged by the ported `Place.ord_neg`.

## 1. Summary — class counts

The three files have 186 + 108 + 120 = **414** checked rows (`port_advise`, excluding
`scoped instance`s; see Correction 4). Counts below are for the pre-tail port:

| tail | rows | SUBSTITUTE | IMPORT/ADAPT | NEW |
|---|---:|---:|---:|---:|
| atom 2 (`…finitePlace_add…placeInfty_eq_zero`) | 186 | 131 | 49 | 6 |
| atom 3 (`…finitePlace_div_pow_eq_zero`) | 108 | 43 | 11 | 54 |
| pfbase (`residueTheorem_ratFunc_of_perfectField`) | 120 | 55 | 27 | 38 |
| **total** | **414** | **229** | **87** | **98** |

The work order's "237 substituted" is high by 8: `port_advise` over-counts `def`
substitutions because the checker's normalisation drops a `def` body, so every
`def … : Prop` with the same binder block matches every other one (Correction 1).

**Headline.** The three tails are not three new engines. The master ℙ¹ engine is already
in `P1/`, and 229 of the 414 rows are importable verbatim; another 87 are the same rows
under the port's `p1PlaceInfty` spelling or under an explicit-binder spelling and need no
new proof at all. The only genuinely new mathematics is

- **atom 2** — 6 rows: the two-place `MOne` carrier and its four-step discharge to the
  simple-pole cancellation, plus the headline
  `RationalFunctionField.trace_localResidue_finitePlace_add_trace_localResidue_placeInfty_eq_zero`;
- **atom 3** — 54 rows: the `P1Tower` construction `Kx := RatFunc K` with the `p`-substitution
  algebra structure, its valuation/ramification dictionary, the power basis, and the
  trace-of-derivative identity, ending in
  `RationalFunctionField.trace_localResidue_finitePlace_div_pow_eq_zero`;
- **pfbase** — 38 rows: the Kähler residue functional and the
  generators → partial fractions → subrows assembly of `ResidueTheorem K (RatFunc K)`,
  ending in `AlgebraicCurve.residueTheorem_ratFunc_of_perfectField`.

**Correction to the work order's "measured delta".** The `p32f_*.log` "N new private
helpers" is the `drags` section only — the private helpers of the public target
declarations. It is not the new surface. Atom 3 in particular is **not** "3 new private
helpers": it is 54 declarations, 52 of them public, because the `P1Tower`/`Kx` block is a
different construction from the master's `p1PlaceInfty` engine and exists nowhere in the
port.

## 2. Corrections to the work order and the measurement

**Correction 1 — the `def` substitutions are unreliable, and 8 are false positives.**
`checker.raw_declarations` returns a `def`'s signature without its body. Every
`def … : Prop` with the same binder block therefore has the same normalised "statement",
and `port_advise` matches across names. Eight of the measured 237 are such false
positives — the named port declaration does not exist, and the reported `port_name` is an
unrelated `def`:

| file | pin ln | pin `def` | bogus `port_name` | really |
|---|---:|---|---|---|
| atom 2 | 4,852 | `P1PrincipalPartTwoPlaceCancelMOne` | `FLT.AlgebraicCurve.P1DifferentialCoeffRegularFinite` | NEW |
| pfbase | 3,682 | `P1PartialFractionSpan` | `EisensteinWeightOne.E1Chi3IsModular` | NEW |
| pfbase | 3,804 | `P1PolynomialResidueAtInfinity` | `FLT.AlgebraicCurve.P1DifferentialCoeffRegularFinite` | NEW |
| pfbase | 3,831 | `P1PrincipalPartTermZeroOffSupport` | `FLT.AlgebraicCurve.P1DifferentialCoeffRegularFinite` | NEW |
| pfbase | 3,837 | `P1PrincipalPartTwoPlaceCancel` | `FLT.AlgebraicCurve.P1DifferentialCoeffRegularFinite` | NEW |
| pfbase | 3,943 | `P1OrdDifferentialPlaceInftyEqNegTwo` | `FLT.AlgebraicCurve.P1DifferentialCoeffRegularFinite` | NEW |
| pfbase | 3,946 | `P1PrincipalPartTwoPlaceCancelMOne` | `FLT.AlgebraicCurve.P1DifferentialCoeffRegularFinite` | NEW |
| pfbase | 4,020 | `P1FinitePlaceTermZeroMGeTwo` | `FLT.AlgebraicCurve.P1DifferentialCoeffRegularFinite` | NEW |

The other `def` matches are real: `P1DifferentialCoeffUnitFinite` (`UnitFinite.lean:24`),
`P1PrincipalPartMOneSimplePoleCancel` (`FinitePlaceResidue.lean:203`),
`P1PlaceInftySimplePoleResidueEulerValue{,TopDeg,Monomial,X}`
(`TraceEngine.lean:260/757/765`, `Separating.lean:196`),
`P1FinitePlaceSimplePoleResidueAdjoinRootValue` (`TraceEngine.lean:251`),
`CanonicalLocalResidueKSimplePoleCoordIndep` (`PerfectPrelude.lean:39`),
`OrdDifferentialWellDefined` (`EnginePrelude.lean:102`),
`higherPoleCorrection` (`LocalResidue/Instance.lean:411`),
`P1PolynomialGenerators` / `P1PrincipalPartGenerators` / `P1PartialFractionGenerators`
(`EnginePrelude.lean:329/331/335`), `simplePoleSubmodule`, `poleSubmodule`,
`simplePoleResidueAux`, `localResidueExtend`, `uniformizerSubring'`, `ratFuncDXCoeff`,
`finitePlaceResidueFieldAlgEquivAdjoinRoot` — all exist under that last name. Theorem
substitutions are reliable (the type carries the hypotheses).

**Correction 2 — `ord_neg'` (atom 3, pin 1,342) is not new.** The work order lists it as
one of the three genuinely-new private helpers. It is a verbatim re-proof of the ported
public `AlgebraicCurve.Place.ord_neg` (`Defs/PlacesOverDVR.lean:51`); probe H discharges
it in one line. The worker imports `Place.ord_neg` and drops `ord_neg'`.

**Correction 3 — `ord_eq_neg_log_of_valuationSubring_eq` is not new either.** Atom 2's
pin-private helper (1,643, 37 ln) and pfbase's public copy (1,404) are both the ported
public `AlgebraicCurve.Place.ord_eq_neg_log_of_valuationSubring_eq`
(`Defs/Place.lean:302`); the only spelling differences are `ℤᵐ⁰` for
`WithZero (Multiplicative ℤ)` and unqualified `exp`/`log` for `WithZero.exp`/`WithZero.log`.
`port_advise` missed it only because of that notation. So atom 2 has **zero** new private
helpers, not two.

**Correction 4 — every `scoped instance` is missing from the measurement.** The `p32f_*`
declaration counts (186 / 108 / 120) contain no `scoped instance`; the pin files declare
3 (atom 2), 16 (atom 3) and 3 (pfbase). The checker's `raw_declarations` does not see them
either, so they are unchecked, but they must still be *elaborated* for the tails to
compile. The port already has `instFormallyEtalePolynomialRatFunc`
(`P1/UnitFinite.lean:45`), `instDCoordGeneratesPerfectField` (`P1/PerfectField.lean`),
`instFiniteResidue` (`LocalResidue/Instance.lean`), `instIsCurveOverRatFunc`
(`P1/UnitFinite.lean`) and `RationalFunctionField.hasPrincipalDivisors`; the genuinely new
instance layer is atom 2/pfbase's `instNontrivialKaehlerRatFunc` (from
`kaehlerRatFuncBasis`) and atom 3's whole `Kx` block — `Field (Kx …)`, `Algebra K (Kx …)`,
`DecidableEq (Kx …)`, `algebraKx`, `IsScalarTower K (RatFunc K) (Kx …)`,
`hasPrincipalDivisors_Kx`, `instFiniteResiduePlaceKx`, `isCurveOver_Kx`,
`nontrivialKaehler_Kx`, `dCoordGenerates_Kx`. This is the same omission pattern as
`AUDIT-mathlib-p3-2e.md` Correction 1.

**Correction 5 — the sibling "twins" (87 rows) are already declared; do not re-state them.**
Atom 2 and pfbase each re-open with a long prelude that the master file already carries
under the `p1PlaceInfty` spelling (and, for `HeightOneSpectrum`/`WithZero`, under a
different notation). Those rows are in the port *now*, under the same last name. A second
declaration is a hard "already declared" error. The port declaration matches the master
`SOURCES` row, and the checker accepts a match against any source candidate
(`AUDIT-mathlib-p3-2e.md` Correction 3), so appending the sibling sources cannot flip the
existing rows to `MISMATCH`. Atom 2 imports 49 such rows, pfbase 27, atom 3 11.

**Correction 6 — the atom-3 headline's binders.** The pin proves
`trace_localResidue_finitePlace_div_pow_eq_zero` inside `namespace P1Tower` with `p` and
`hp : 0 < p.natDegree` as explicit section arguments, but the wrapper
[`Theorems/Thm_…div_pow_eq_zero.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.lean)
publishes `AlgebraicCurve.RationalFunctionField.trace_localResidue_finitePlace_div_pow_eq_zero`
with `{p c : K[X]}` implicit, `[AlgebraicCurve.IsCurveOver K (RatFunc K)]` in the binder
set, and `{m} (hm : 2 ≤ m)` after `(hc)`. The worker states it at the wrapper's binders in
`namespace RationalFunctionField` (a one-line application of the `P1Tower` version with
`p := p`, `hp := hp.natDegree_pos` or the wrapper's own `hp`). The checker keys by last
name, so either namespace verifies; the wrapper is the authority for the public spelling.

## 3. The `placeInfty` / `p1PlaceInfty` rule and the import tables

`P1/UnitNormalForm.lean:21` defines `dX`; `P1/EnginePrelude.lean:260` defines
`p1PlaceInfty` as a `@[reducible] def` equal to `placeInfty`, and `P1/Core.lean` proves
`RationalFunctionField.placeInfty_eq_p1PlaceInfty : placeInfty K = p1PlaceInfty K` by
`rfl` (probe A/H). Consequently a port row stated at `p1PlaceInfty` *is* the pin sibling's
row at `placeInfty`, definitionally. The worker has three legal moves, in order of
preference:

1. **Import** the port row as-is; it is already checked against the master source. No new
   declaration.
2. Where the tail's proof text needs the `placeInfty` spelling, state the goal at
   `placeInfty` and `rw [RationalFunctionField.placeInfty_eq_p1PlaceInfty]` before
   `exact`; probe H compiles exactly this shape for `ord_placeInfty_X_inv`. The same works
   for a *hypothesis* in `p1PlaceInfty` form.
3. Never re-state the row at the pin's spelling: the last name is globally taken.

The three tables below are the complete import/adapt sets (all rows not already
byte-identical in the port). "alias" = equal after `p1PlaceInfty`→`placeInfty` and
whitespace normalisation; "adapt" = equal after binder/notation normalisation only.
Module paths are relative to `lean/FLTForHuman/AlgebraicCurve/`.

### 3.1 atom 2 — 49 rows (`P1/TwoPlace.lean` imports them)

| pin ln | name | port home | kind |
|---:|---|---|---|
| 940 | `simplePoleResidueAux_apply` | `LocalResidue/Instance.lean:145` | alias |
| 1091 | `finitePlace_ne_placeInfty` | `P1/EnginePrelude.lean:445` | alias |
| 1188 | `ord_placeInfty_eq_zero_of_intDegree_eq_zero` | `P1/EnginePrelude.lean:524` | alias |
| 1195 | `ord_placeInfty_eq_intDegree_mul` | `P1/EnginePrelude.lean:531` | alias |
| 1747 | `ord_placeInfty_X_inv` | `P1/Differential.lean:41` | alias |
| 1750 | `ord_placeInfty_X_pow` | `P1/Differential.lean:45` | alias |
| 1772 | `differentialCoeff_placeInfty_D_X_eq` | `P1/Differential.lean:72` | alias |
| 1779 | `ord_differentialCoeff_placeInfty_D_X_inv_eq_zero` | `P1/Differential.lean:80` | alias |
| 1795 | `ordDifferential_placeInfty_D_ratFuncX` | `P1/Differential.lean:93` | alias |
| 2213 | `dX` | `P1/UnitNormalForm.lean:21` | alias |
| 2483 | `ord_placeInfty_p1PrincipalPartAtom` | `P1/UnitNormalForm.lean:356` | alias |
| 2496 | `one_le_ord_placeInfty_p1PrincipalPartAtom` | `P1/UnitNormalForm.lean:370` | alias |
| 2890 | `ord_placeInfty_ratFuncDXCoeff_ge` | `P1/DivisorAction.lean:200` | alias |
| 2919 | `exists_dXCoeff_ord_ge_two_of_ord_placeInfty_eq_zero` | `P1/DivisorAction.lean:229` | alias |
| 2954 | `exists_unit_dXCoeff_of_ord_placeInfty_eq_neg_one` | `P1/DivisorAction.lean:264` | alias |
| 3002 | `exists_dXCoeff_ord_two_of_ord_placeInfty_eq_one` | `P1/DivisorAction.lean:312` | alias |
| 3443 | `ord_finitePlace_mOneAtom_mul_differentialCoeff` | `P1/FinitePlaceResidue.lean:108` | alias |
| 3460 | `ord_placeInfty_mOneAtom_mul_differentialCoeff_ge_neg_one` | `P1/FinitePlaceResidue.lean:125` | alias |
| 3478 | `p1MOneAtom_mul_differentialCoeff_mem_simplePole_finitePlace` | `P1/FinitePlaceResidue.lean:143` | alias |
| 3503 | `p1MOneAtom_mul_differentialCoeff_mem_simplePole_placeInfty` | `P1/FinitePlaceResidue.lean:168` | alias |
| 4000 | `ord_placeInfty_mOneAtom_mul_differentialCoeff_dX` | `P1/TraceEngine.lean:682` | alias |
| 4015 | `p1MOneAtom_mul_differentialCoeff_dX_mem_placeInfty` | `P1/TraceEngine.lean:697` | alias |
| 4042 | `trace_placeInfty_simplePoleResidue_mOne_of_lowDeg` | `P1/TraceEngine.lean:729` | alias |
| 4112 | `trace_placeInfty_simplePoleResidueAux_mOne_add` | `P1/TraceEngine.lean:807` | alias |
| 4131 | `trace_placeInfty_simplePoleResidueAux_mOne_C_mul` | `P1/TraceEngine.lean:826` | alias |
| 4146 | `p1PlaceInftySimplePoleResidueEulerValue_of_topDeg` | `P1/TraceEngine.lean:841` | alias |
| 4158 | `p1PlaceInftySimplePoleResidueEulerValueTopDeg_of_monomial` | `P1/TraceEngine.lean:853` | alias |
| 4214 | `p1PlaceInftySimplePoleResidueEulerValue_of_monomial` | `P1/TraceEngine.lean:909` | alias |
| 4296 | `ord_placeInfty_X_pow_natDegree_div` | `P1/Separating.lean:97` | alias |
| 4309 | `X_pow_natDegree_div_mem_placeInfty` | `P1/Separating.lean:110` | alias |
| 4327 | `residue_placeInfty_X_pow_natDegree_div_monic_eq_one` | `P1/Separating.lean:145` | alias |
| 4386 | `p1MonomialAtom_eq_monicRatio_mul` | `P1/Separating.lean:212` | alias |
| 4404 | `p1XInvAtom_mul_differentialCoeff_dX_mem_simplePole_placeInfty` | `P1/Separating.lean:230` | alias |
| 4411 | `simplePoleResidueAux_placeInfty_monomial_eq_X` | `P1/Separating.lean:237` | alias |
| 4434 | `p1PlaceInftySimplePoleResidueEulerValueMonomial_of_X` | `P1/Separating.lean:260` | alias |
| 4548 | `p1XAtom_mul_differentialCoeff_dX_eq_neg` | `P1/PerfectPrelude.lean:57` | alias |
| 4568 | `trace_placeInfty_residueField_one` | `P1/PerfectPrelude.lean:79` | alias |
| 4574 | `simplePoleResidueAux_placeInfty_p1XAtom_eq_neg_one` | `P1/PerfectPrelude.lean:85` | alias |
| 5023 | `ordDifferential_dX_placeInfty_of_perfectField` | `P1/PerfectField.lean:92` | alias |
| 5163 | `ratFuncDXCoeff_ne_zero_and_ord_placeInfty_eq_two_of_ord_eq_one` | `P1/KaehlerIntegral.lean:233` | alias |
| 5170 | `ratFuncDXCoeff_eq_zero_or_two_le_ord_placeInfty_of_ord_nonneg` | `P1/KaehlerIntegral.lean:240` | alias |
| 447 | `mem_iff_ord_nonneg` | `Defs/PushPull.lean:69` | adapt |
| 558 | `placeInfty_ne_ofHeightOneSpectrum` | `PrincipalDivisors/RatFuncDegree.lean:78` | adapt |
| 569 | `eq_ofHeightOneSpectrum_or_eq_placeInfty` | `PrincipalDivisors/RatFuncDegree.lean:61` | adapt |
| 1643 | `ord_eq_neg_log_of_valuationSubring_eq` | `Defs/Place.lean:302` | adapt |
| 1680 | `ord_ofHeightOneSpectrum_eq_neg_log` | `PrincipalDivisors/RatFuncDegree.lean:164` | adapt |
| 1691 | `ord_ofHeightOneSpectrum_of_span` | `PrincipalDivisors/RatFuncDegree.lean:176` | adapt |
| 2116 | `gate_canonicalLocalResidueDataK_uniformizer_inv` | `LocalResidue/Calculus.lean:384` | adapt |
| 4811 | `kaehlerRatFuncBasis` | `P1/UnitFinite.lean:49` | adapt |

### 3.2 pfbase — 27 rows

| pin ln | name | port home | kind |
|---:|---|---|---|
| 917 | `algebraMap_polynomial_mem_of_ne_placeInfty'` | `P1/EnginePrelude.lean:388` | alias |
| 924 | `pow_X_mem_of_ne_placeInfty` | `P1/EnginePrelude.lean:395` | alias |
| 931 | `pow_X_mul_mem_of_ne_placeInfty` | `P1/EnginePrelude.lean:402` | alias |
| 965 | `finitePlace_ne_placeInfty` | `P1/EnginePrelude.lean:445` | alias |
| 1004 | `ord_placeInfty_eq_zero_of_intDegree_eq_zero` | `P1/EnginePrelude.lean:524` | alias |
| 1011 | `ord_placeInfty_eq_intDegree_mul` | `P1/EnginePrelude.lean:531` | alias |
| 1499 | `ord_placeInfty_X_inv` | `P1/Differential.lean:41` | alias |
| 1502 | `ord_placeInfty_X_pow` | `P1/Differential.lean:45` | alias |
| 1523 | `differentialCoeff_placeInfty_D_X_eq` | `P1/Differential.lean:72` | alias |
| 1530 | `ord_differentialCoeff_placeInfty_D_X_inv_eq_zero` | `P1/Differential.lean:80` | alias |
| 1545 | `ordDifferential_placeInfty_D_ratFuncX` | `P1/Differential.lean:93` | alias |
| 1785 | `dX` | `P1/UnitNormalForm.lean:21` | alias |
| 2056 | `ord_algebraMap_irreducible_eq_zero_of_ne` | `P1/UnitNormalForm.lean:325` | alias |
| 2065 | `inv_algebraMap_pow_mem_of_ne_finitePlace` | `P1/UnitNormalForm.lean:335` | alias |
| 2075 | `p1PrincipalPartAtom_mem_of_ne_finitePlace` | `P1/UnitNormalForm.lean:346` | alias |
| 2089 | `ord_placeInfty_p1PrincipalPartAtom` | `P1/UnitNormalForm.lean:356` | alias |
| 2435 | `ord_placeInfty_ratFuncDXCoeff_ge` | `P1/DivisorAction.lean:200` | alias |
| 2464 | `exists_dXCoeff_ord_ge_two_of_ord_placeInfty_eq_zero` | `P1/DivisorAction.lean:229` | alias |
| 2499 | `exists_unit_dXCoeff_of_ord_placeInfty_eq_neg_one` | `P1/DivisorAction.lean:264` | alias |
| 2547 | `exists_dXCoeff_ord_two_of_ord_placeInfty_eq_one` | `P1/DivisorAction.lean:312` | alias |
| 2605 | `two_le_ord_placeInfty_p1PrincipalPartAtom` | `P1/DivisorAction.lean:397` | alias |
| 530 | `placeInfty_ne_ofHeightOneSpectrum` | `PrincipalDivisors/RatFuncDegree.lean:78` | adapt |
| 541 | `eq_ofHeightOneSpectrum_or_eq_placeInfty` | `PrincipalDivisors/RatFuncDegree.lean:61` | adapt |
| 1404 | `ord_eq_neg_log_of_valuationSubring_eq` | `Defs/Place.lean:302` | adapt |
| 1439 | `ord_ofHeightOneSpectrum_eq_neg_log` | `PrincipalDivisors/RatFuncDegree.lean:164` | adapt |
| 1450 | `ord_ofHeightOneSpectrum_of_span` | `PrincipalDivisors/RatFuncDegree.lean:176` | adapt |
| 3549 | `kaehlerRatFuncBasis` | `P1/UnitFinite.lean:49` | adapt |

The five `adapt` rows are notation/binder only: explicit binder vs section variable
(530/541/1404/1439/1450), `HeightOneSpectrum K[X]` for
`IsDedekindDomain.HeightOneSpectrum (Polynomial K)` (530/541/1439/1450), `ℤᵐ⁰`/`exp`/`log`
for `WithZero (Multiplicative ℤ)`/`WithZero.exp`/`WithZero.log` (1404), and explicit
`(K) [Field K] : Module.Basis …` for a section variable in `Basis …` (3549). No new
mathematics.

### 3.3 atom 3 — 11 rows

| pin ln | name | port home | kind |
|---:|---|---|---|
| 361 | `finitePlace_ne_placeInfty` | `P1/EnginePrelude.lean:445` | alias |
| 455 | `ord_placeInfty_X_inv` | `P1/Differential.lean:41` | alias |
| 476 | `dX` | `P1/UnitNormalForm.lean:21` | alias |
| 603 | `surjective_algebraMap_residueField_placeInfty` | `P1/DXCoeff.lean:308` | alias |
| 781 | `ord_placeInfty_ratFuncDXCoeff_ge` | `P1/DivisorAction.lean:200` | alias |
| 810 | `exists_dXCoeff_ord_ge_two_of_ord_placeInfty_eq_zero` | `P1/DivisorAction.lean:229` | alias |
| 845 | `exists_unit_dXCoeff_of_ord_placeInfty_eq_neg_one` | `P1/DivisorAction.lean:264` | alias |
| 893 | `exists_dXCoeff_ord_two_of_ord_placeInfty_eq_one` | `P1/DivisorAction.lean:312` | alias |
| 1055 | `ratFuncDXCoeff_ne_zero_and_ord_placeInfty_eq_two_of_ord_eq_one` | `P1/KaehlerIntegral.lean:233` | alias |
| 1062 | `ratFuncDXCoeff_eq_zero_or_two_le_ord_placeInfty_of_ord_nonneg` | `P1/KaehlerIntegral.lean:240` | alias |
| 1319 | `surjective_algebraMap_residueField_of_deg_eq_one` | `P1/KaehlerIntegral.lean:474` | adapt |

Row 1319 is the port's explicit-binder form of the pin's `(K : Type*) [Field K] {F} …`
wrapper; no proof change. Additionally the pin-private `ord_neg'` (1,342) is
`Place.ord_neg` (Correction 2), and the pin-private `ord_add_eq_min` / `ord_add_eq_left`
are the port-private `LocalResidue/Calculus.lean` / `P1/EnginePrelude.lean` originals
(work order §2 holds: re-land `private` verbatim in the consuming module).

## 4. atom 2 — the six new rows

Everything else in the 5,776-line pin file is the master engine. The unique tail is the
two-place cancellation:

| pin ln | name | class | discharge |
|---:|---|---|---|
| 4852 | `P1PrincipalPartTwoPlaceCancelMOne` | BESPOKE | new `def : Prop` (`∀ p c, … finitePlace + placeInfty = 0`) |
| 4908 | `kaehlerResidueTerm_eq_of_mem_simplePoleSubmodule` | PROOF-INGREDIENT | unfold `kaehlerResidueTerm`, `diagonalHom_apply`, `Place.localResidue_simplePole`; `rfl` |
| 4917 | `p1PrincipalPartTwoPlaceCancelMOne_of_simplePoleCancel` | PROOF-INGREDIENT | `p1MOneAtom_mul_differentialCoeff_mem_simplePole_{finitePlace,placeInfty}` (`P1/FinitePlaceResidue.lean:143/168`), row 4908, the hypothesis `P1PrincipalPartMOneSimplePoleCancel` |
| 5608 | `ag9b12c_p1TwoPlaceCancelMOne_dX_of_inftyEulerValue_of_perfectField` | PROOF-INGREDIENT | row 4917 + `p1DifferentialCoeffUnitFinite_dX_of_perfectField`, `ordDifferential_dX_placeInfty_of_perfectField`, `ag9b12c_p1MOneSimplePoleCancel_dX_of_inftyEulerValue_of_perfectField` |
| 5736 | `ag9b13e_p1TwoPlaceCancelMOne_dX_of_perfectField` | PROOF-INGREDIENT | one line: row 5608 + `ag9b13e_p1PlaceInftySimplePoleResidueEulerValue_of_perfectField` (`P1/Core.lean`) |
| 5760 | `solution` → `RationalFunctionField.trace_localResidue_finitePlace_add_trace_localResidue_placeInfty_eq_zero` | PROOF-INGREDIENT | row 5736, `simpa only [kaehlerResidueTerm, diagonalHom_apply, p1PrincipalPartAtom, pow_one]` |

The headline is the trace form of row 5736; the pin's proof is the `simpa` shown. It needs
**no** `ord_add_eq_min`/`ord_add_eq_left`, `algebraMap_ne_zero`,
`ag9b12c_differentialCoeff_add` or `uniformizer_ne_zero'` (the four port-private helpers
`port_advise` flags as potential drags): the tail's proof goes through the already-public
simple-pole chain.

## 5. atom 3 — the `P1Tower` block (54 new rows)

The atom-3 file does not extend the master engine; it builds a **new curve** `Kx` and
transfers the finite-place residue value to it. `Kx K p hp` is definitionally `RatFunc K`
but carries the `p`-substitution algebra structure
`algebraMap (RatFunc K) (Kx …) f = toKx (subst f)`, so the finite place of `K[X]` above
`(X)` becomes the unique place above `placeOfPoint 0` in the tower. This block exists
nowhere in the port (probe A: every name absent; `P1PartialFraction*`,
`P1PrincipalPartGenerators` etc. are unrelated master-engine objects).

### 5.1 `P1Tower` scaffolding (1,392–1,545)

| pin ln | name | class | mathlib/port lead |
|---:|---|---|---|
| 1392 | `substPoly` | BESPOKE | `def : K[X] →ₐ[K] RatFunc K := Polynomial.aeval (algebraMap K[X] (RatFunc K) p)` |
| 1395 | `substPoly_apply` | PROOF-INGREDIENT | `Polynomial.comp_eq_aeval`, `Polynomial.aeval_algebraMap_apply` |
| 1400 | `substPoly_ne_zero` | PROOF-INGREDIENT | `Polynomial.comp_eq_zero_iff`, `IsFractionRing.injective`, `nonZeroDivisors.ne_zero` |
| 1405 | `subst` | BESPOKE | `RatFunc.liftAlgHom` on `substPoly` |
| 1410 | `subst_algebraMap` | PROOF-INGREDIENT | `RatFunc.{liftAlgHom_apply, num_algebraMap, denom_algebraMap}` |
| 1415 | `Kx` | BESPOKE | `def Kx _hp := RatFunc K` |
| 1423 | `toKx` | BESPOKE | `AlgEquiv.refl` |
| 1428 | `algebraMap_Kx_apply` | PROOF-INGREDIENT | `rfl` |
| 1437 | `subst_X` | PROOF-INGREDIENT | `RatFunc.algebraMap_X`, `Polynomial.X_comp` |
| 1446 | `gen` (private) | BESPOKE | `toKx (RatFunc.X)` |
| 1450 | `minP` | BESPOKE | `p.map (algebraMap K (RatFunc K)) - C RatFunc.X` |
| 1452 | `toKx_apply` | PROOF-INGREDIENT | `rfl` |
| 1454 | `aeval_gen_map` | PROOF-INGREDIENT | `Polynomial.aeval_map_algebraMap` |
| 1459 | `aeval_gen_minP` | PROOF-INGREDIENT | `map_sub`, `aeval_C`, `sub_self` |
| 1463 | `monic_minP` | PROOF-INGREDIENT | `Polynomial.Monic.sub_of_left`, `Polynomial.{degree_C, degree_map}`, `degree_eq_natDegree` |
| 1470 | `isIntegral_gen` (private) | PROOF-INGREDIENT | `IsIntegral` via `minP`, `monic_minP`, `aeval_def` |
| 1477 | `minP_ne_zero` | PROOF-INGREDIENT | `monic_minP` |
| 1479 | `toKx_algebraMap_mem_adjoin` | PROOF-INGREDIENT | `Polynomial.aeval_mem_adjoin_singleton`, `IntermediateField.algebra_adjoin_le_adjoin` |
| 1484 | `adjoin_gen_eq_top` | PROOF-INGREDIENT | `RatFunc.induction_on`, `div_mem` |
| 1493 | `finiteDimensional_Kx` | PROOF-INGREDIENT | `IntermediateField.adjoin.finiteDimensional`, `IntermediateField.topEquiv` |
| 1498 | `isIntegral_Kx` | PROOF-INGREDIENT | `Algebra.IsIntegral.of_finite` |
| 1502 | `derivative_minP` | PROOF-INGREDIENT | `Polynomial.derivative_map` |
| 1505 | `transcendental_ratFuncX` | PROOF-INGREDIENT | `Polynomial.transcendental_X`, `transcendental_algebraMap_iff` |
| 1511 | `separable_minP` | PROOF-INGREDIENT | `Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed` (route through the algebraic closure) |
| 1542 | `isSeparable_gen` | PROOF-INGREDIENT | `separable_minP`, `minpoly`/`Algebra.IsSeparable` |
| 1545 | `isSeparable_Kx` | PROOF-INGREDIENT | `IntermediateField.adjoin` separability, `adjoin_gen_eq_top` |

### 5.2 the valuative dictionary for the substitution (1,574–1,768)

All PROOF-INGREDIENT over the ported `Place` API:

| pin ln | name | lead |
|---:|---|---|
| 1579 | `ord_finitePlace_pos_iff_dvd` | `Place.ord_ofHeightOneSpectrum_ne_zero_iff`, `heightOneSpectrumOfIrreducible_asIdeal`, `finitePlace_def`, `omega` |
| 1591 | `ord_finitePlace_eq_zero_iff_not_dvd` | as 1579 |
| 1598 | `not_dvd_comp_of_eval_zero_ne_zero` | `Polynomial.X_dvd_iff`, `Polynomial.{sub_comp, C_comp, mul_comp, X_comp}`, `isUnit_C` |
| 1616 | `not_isUnit_p` | `Polynomial.natDegree_eq_zero_of_isUnit` |
| 1619 | `ord_finitePlace_subst_algebraMap` | `Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd`, `Place.{ord_mul, ord_zpow}`, `IsFractionRing.injective` |
| 1644 | `ord_finitePlace_subst` | `RatFunc.{num_div_denom, num_ne_zero, denom_ne_zero}`, `ord_placeOfPoint_algebraMap`, row 1619 |
| 1665 | `restrict_finitePlace` | `Place.{ext, mem_restrict_iff, mem_iff_ord_nonneg}` |
| 1688 | `eq_finitePlace_of_ord_pos` | `eq_ofHeightOneSpectrum_or_eq_placeInfty`, `exists_irreducible_span`, `HeightOneSpectrum.ext`, `ord_placeInfty` |
| 1709 | `finitePlace_mem_fiber` | `Place.mem_fiber`, row 1665 |
| 1713 | `fiber_placeOfPoint_zero` | `Place.{mem_fiber, ord_restrict, ramificationIndex_pos}`, `rootMultiplicity_X_sub_C`, row 1688 |
| 1737 | `ord_placeInfty_subst_algebraMap` | `ord_placeInfty`, `RatFunc.intDegree_polynomial`, `Polynomial.natDegree_comp` |
| 1749 | `ord_placeInfty_subst` | row 1737, `RatFunc.{num_div_denom, num_ne_zero, denom_ne_zero}` |
| 1768 | `ord_sum_of_injOn` | `Valuation.map_add_of_distinct_val`, `Finset.induction_on`, `WithZero.log_le_log`, `Finset.inf'` |

### 5.3 power basis, trace and completion (1,798–1,966)

| pin ln | name | class | lead |
|---:|---|---|---|
| 1798 | `linearIndependent_pow_gen` | PROOF-INGREDIENT | `Fintype.linearIndependent_iff`, `ord_sum_of_injOn`, `Int.eq_zero_of_dvd_of_natAbs_lt_natAbs`, `Finset.sum_filter_of_ne` |
| 1850 | `natDegree_le_finrank` | PROOF-INGREDIENT | `LinearIndependent.fintype_card_le_finrank`, `finiteDimensional_Kx` |
| 1855 | `minpoly_gen` | PROOF-INGREDIENT | `minpoly.{dvd,monic}`, `Polynomial.eq_of_monic_of_dvd_of_natDegree_le`, `IntermediateField.adjoin.finrank`, `natDegree_sub_eq_left_of_natDegree_lt` |
| 1887 | `pbGen` | BESPOKE | `PowerBasis` from `IntermediateField.adjoin.powerBasis` |
| 1891 | `pbGen_gen` | PROOF-INGREDIENT | `IntermediateField.adjoin.powerBasis_gen`, `PowerBasis.map` |
| 1894 | `pbGen_dim` | PROOF-INGREDIENT | `PowerBasis.map_dim`, `IntermediateField.adjoin.powerBasis_dim`, `minpoly_gen` |
| 1898 | `aeval_gen_derivative_minpoly` | PROOF-INGREDIENT | `minpoly_gen`, `derivative_minP`, `aeval_gen_map` |
| 1903 | `toKx_algebraMap_eq_sum` | PROOF-INGREDIENT | `Polynomial.aeval_eq_sum_range'` |
| 1909 | `trace_mul_inv_derivative` | PROOF-INGREDIENT | `FLT.EulerDualBasis.trace_pow_div_aeval_derivative_minpoly_{self,of_lt}` (`P1/EnginePrelude.lean`), `Finset.sum_eq_single`, `PowerBasis` |
| 1949 | `kwHgfV352_localResidueCompletion_spec` | PROOF-INGREDIENT | `kwHgfV352_exists_sub_mem_adicCompletionIntegers`, `kwHgfV352_algebraMap_mem_adicCompletionIntegers_iff`, `Place.localResidue_of_mem` |
| 1966 | `kwHgfV352_localResidueCompletion_algebraMap` | PROOF-INGREDIENT | one line of 1949 |

### 5.4 the headline (1,996–2,140)

| pin ln | name | class | lead |
|---:|---|---|---|
| 1996 | `D_ratFuncX_ne_zero` | PROOF-INGREDIENT | `KaehlerDifferential.span_range_derivation`, `Derivation.{map_aeval, leibniz_div}`, `D_ratFuncX_eq_neg_X_sq_smul_D_inv` (`P1/Differential.lean`) |
| 2016 | `trace_localResidue_finitePlace_div_pow_eq_zero` | PROOF-INGREDIENT | `kaehlerPullback`, `KaehlerDifferential.map_D`, `CanonicalLocalResidueDataK.res_differentialCoeff_D_mul_pow_inv_eq_zero_of_surjective_algebraMap`, `ag9b13e_differentialCoeff_D_mem_of_mem_of_perfectField`, rows 1665/1709/1713/1909 |
| 2140 | `solution` (wrapper headline) | PROOF-INGREDIENT | row 2016 at the wrapper's binders (Correction 6) |

No declaration in atom 3 has a mathlib substitute that lets the port *drop* it: every new
name is either a `P1Tower`-specific `def`/`Prop` or a bespoke statement over pin
vocabulary. The `ord_neg'` row is the one exception (Correction 2).

## 6. pfbase — the partial-fraction residue engine (38 new rows)

pfbase proves `ResidueTheorem K (RatFunc K)` over `[PerfectField K]` by a *different*
route from the master's `ResidueTheoremK` cone: a `K →ₗ[K] K` residue functional on
`F`, a kernel `Submodule`, and the named subrow decomposition. None of it is in the port
(the port's `kaehlerResidueFunctionalK`, `ResidueTheoremK` etc. are the `Rfam`-indexed
master route). The block's statements are generic in `{K F}` where the pin gives them
generically, then specialised to `RatFunc K`.

### 6.1 smul reduction (3,574–3,595) and the kernel/functional vocabulary (3,641–3,693)

| pin ln | name | class | lead |
|---:|---|---|---|
| 3574 | `kaehlerResidueTerm_smul_left` | PROOF-INGREDIENT | `kaehlerResidueTerm`, `Place.differentialCoeff_smul`, `mulAdele_apply` |
| 3580 | `weilSmul_weilOfKaehler` | PROOF-INGREDIENT | `LinearMap.ext`, `weilSmul_apply`, `weilOfKaehler_apply`, `finsum_congr`, row 3574 |
| 3587 | `weilOfKaehler_smul_diagonal` | PROOF-INGREDIENT | row 3580, `Subtype.ext`, `funext`, `adeleSpaceMul_coe` |
| 3595 | `residueTheorem_iff_of_ne_zero` | PROOF-INGREDIENT | `exists_smul_eq_of_ne_zero`, row 3587 |
| 3641 | `kaehlerResidueFunctional` | BESPOKE | `def : F →ₗ[K] K := (weilOfKaehler K F hω).comp (principalAdele K F)` |
| 3646 | `kaehlerResidueKernel` | BESPOKE | `def : Submodule K F := LinearMap.ker (kaehlerResidueFunctional …)` |
| 3649 | `mem_kaehlerResidueKernel` | PROOF-INGREDIENT | `Iff.rfl` |
| 3654 | `residueTheorem_iff_kaehlerResidueKernel_eq_top` | PROOF-INGREDIENT | row 3595, `Submodule.eq_top_iff'` |
| 3661 | `residueTheorem_of_span_le_kernel` | PROOF-INGREDIENT | `Submodule.{span_le, eq_top_iff'}`, `top_unique` |
| 3668 | `residueTheorem_of_union_span_le_kernel` | PROOF-INGREDIENT | `Set.union_subset` |
| 3682 | `P1PartialFractionSpan` | BESPOKE (def `Prop`) | equal to the ported theorem `p1PartialFractionSpan_eq_top` (`P1/EnginePrelude.lean:783`) |
| 3685 | `P1ResiduePolynomialPart` | BESPOKE (def `Prop`) | `P1PolynomialGenerators K ⊆ kaehlerResidueKernel …` |
| 3688 | `P1ResiduePrincipalPart` | BESPOKE (def `Prop`) | `P1PrincipalPartGenerators K ⊆ kaehlerResidueKernel …` |
| 3693 | `residueTheorem_ratFunc_of_partialFractions` | PROOF-INGREDIENT | rows 3668/3682/3685/3688 |
| 3723 | `residueTheorem_ratFunc_of_generators_residue` | PROOF-INGREDIENT | row 3693 + `p1PartialFractionSpan_eq_top` (`P1/EnginePrelude.lean`) |

### 6.2 the kernel/finsum lemmas and the subrows (3,752–3,921)

| pin ln | name | class | lead |
|---:|---|---|---|
| 3752 | `mem_kaehlerResidueKernel_iff_finsum` | PROOF-INGREDIENT | `Iff.rfl` |
| 3757 | `mem_kaehlerResidueKernel_of_term_zero_compl` | PROOF-INGREDIENT | `finsum_eq_finsetSum_of_support_subset`, `by_contra` |
| 3767 | `mem_kaehlerResidueKernel_of_singleton` | PROOF-INGREDIENT | row 3757, `Finset.mem_singleton` |
| 3777 | `mem_kaehlerResidueKernel_of_pair` | PROOF-INGREDIENT | row 3757, `Finset.sum_pair` |
| 3804 | `P1PolynomialResidueAtInfinity` | BESPOKE (def `Prop`) | `∀ n, kaehlerResidueTerm ω₀ (diagonalHom ((X)^n)) (placeInfty K) = 0` |
| 3810 | `p1ResiduePolynomialPart_of_subrows` | PROOF-INGREDIENT | row 3767, `pow_X_mul_mem_of_ne_placeInfty`, `kaehlerResidueTerm_eq_zero_of_ord_nonneg` |
| 3831 | `P1PrincipalPartTermZeroOffSupport` | BESPOKE (def `Prop`) | off-support vanishing of the atom |
| 3837 | `P1PrincipalPartTwoPlaceCancel` | BESPOKE (def `Prop`) | the `MOne`-plus-higher atom cancellation |
| 3847 | `p1ResiduePrincipalPart_of_subrows` | PROOF-INGREDIENT | row 3777, `finitePlace_ne_placeInfty` |
| 3865 | `residueTheorem_ratFunc_of_four_subrows` | PROOF-INGREDIENT | row 3723, rows 3810/3847 |
| 3909 | `p1PrincipalPartTermZeroOffSupport_of_differentialCoeffRegularFinite` | PROOF-INGREDIENT | `p1PrincipalPartAtom_mem_of_ne_finitePlace`, `P1DifferentialCoeffRegularFinite` |
| 3921 | `residueTheorem_ratFunc_of_three_subrows` | PROOF-INGREDIENT | row 3865, row 3909 |

### 6.3 the two-place reduction and the perfect-field specialisations (3,943–4,288)

| pin ln | name | class | lead |
|---:|---|---|---|
| 3943 | `P1OrdDifferentialPlaceInftyEqNegTwo` | BESPOKE (def `Prop`) | `(placeInfty K).ordDifferential ω₀ = -2` |
| 3946 | `P1PrincipalPartTwoPlaceCancelMOne` | BESPOKE (def `Prop`) | pfbase's copy of the atom-2 carrier (same statement) |
| 3985 | `kaehlerResidueTerm_placeInfty_eq_zero_of_two_le_m` | PROOF-INGREDIENT | `two_le_ord_placeInfty_p1PrincipalPartAtom`, `ordDifferential_placeInfty_D_ratFuncX`, `omega` |
| 4020 | `P1FinitePlaceTermZeroMGeTwo` | BESPOKE (def `Prop`) | finite-place vanishing for `2 ≤ m` |
| 4035 | `p1PrincipalPartTwoPlaceCancel_of_mOne` | PROOF-INGREDIENT | row 3985, `Nat.lt_or_ge` |
| 4093 | `D_ratFuncX_ne_zero` | PROOF-INGREDIENT | `D_ratFuncX_eq_neg_X_sq_smul_D_inv`, `D_ratFuncX_inv_ne_zero` |
| 4107 | `p1OrdDifferentialPlaceInftyEqNegTwo_D_X` | PROOF-INGREDIENT | one line: `ordDifferential_placeInfty_D_ratFuncX` |
| 4156 | `p1PrincipalPartTwoPlaceCancel_dX_of_mOne_mGeTwo` | PROOF-INGREDIENT | row 4035, row 4107 |
| 4281 | `residueTheorem_ratFunc_of_two_subrows_of_perfectField` | PROOF-INGREDIENT | row 3921 + `p1DifferentialCoeffRegularFinite_dX_of_perfectField` |
| 4288 | `p1PrincipalPartTwoPlaceCancel_dX_of_mOne_mGeTwo_of_perfectField` | PROOF-INGREDIENT | row 4156 + `ordDifferentialWellDefined_ratFunc_of_perfectField` |
| 4314 | `solution` → `AlgebraicCurve.residueTheorem_ratFunc_of_perfectField` | PROOF-INGREDIENT | rows 4281/4288 + the atom-2 and atom-3 headlines (`trace_localResidue_placeInfty_X_pow_eq_zero`, `…finitePlace_add…`, `…finitePlace_div_pow…`) |

**The pfbase instance layer.** `instFormallyEtalePolynomialRatFunc` is already in the port
(`P1/UnitFinite.lean:45`), but `instNontrivialKaehlerRatFunc` (pin 3555, from
`kaehlerRatFuncBasis.ne_zero`) and `scoped instance (priority := low) instDCoordGeneratesPerfectField`
(pin 4211) need care: the latter is already in `P1/PerfectField.lean` and must be
imported, not re-declared (Correction 4).

## 7. Reuse wins, with probe evidence

1. **The whole sibling prelude is the already-ported master engine.** 131 + 43 + 55 = 229
   rows importable; 49 + 27 + 11 = 87 more are the same rows at the port's binders. The
   only reason the sibling spellings look different is that the master file shipped the
   same engine twice, once under `p1PlaceInfty` (ported) and once under `placeInfty` (the
   siblings). Probe H compiles the alias bridge for a representative row.
2. **`ord_neg'` and `ord_eq_neg_log_of_valuationSubring_eq` are already public.** Probe A
   `#check`s both port names; Correction 2/3. This removes two of the four private helpers
   the work order's §3 "genuinely new" table names — atom 2's
   `ord_eq_neg_log_of_valuationSubring_eq` and atom 3's `ord_neg'`. The only genuinely new
   private helpers left are atom 3's `gen` and `isIntegral_gen`.
3. **The atom-3 trace identity reuses the ported Euler-dual-basis engine.**
   `FLT.EulerDualBasis.trace_pow_div_aeval_derivative_minpoly_{self,of_lt}`
   (`P1/EnginePrelude.lean:69/82`) carry `trace_mul_inv_derivative` (pin 1,909); the pin
   needs no new trace algebra.
4. **The atom-3 residue ending reuses the ported Cartier/perfect-field cone.**
   `CanonicalLocalResidueDataK.res_differentialCoeff_D_mul_pow_inv_eq_zero_of_surjective_algebraMap`
   (`LocalResidue/Calculus.lean:1,212`) and
   `ag9b13e_differentialCoeff_D_mem_of_mem_of_perfectField` (`P1/Core.lean:86`) are
   the two leaves of the pin's `hres` step.
5. **The pfbase reduction is pure order theory on `Submodule`.** Every non-`def` pfbase
   row is `Submodule.{span_le, eq_top_iff'}`, `LinearMap.{ext, mem_ker}`,
   `finsum_eq_finsetSum_of_support_subset`, `Finset.sum_pair`, `Set.union_subset`; no
   mathlib gap.

## 8. Route options

- **R1 — import the 229 substitutes and state only the 98 new rows.** Atom 2 needs 6 new
  declarations (its `P1/TwoPlace.lean` is already the model); atom 3 needs the 54-declaration
  `P1Tower` block; pfbase needs the 38-declaration residue-functional engine. Do not
  re-transcribe any of §3.
- **R2 — for the sibling twins, prefer import + `rw [RationalFunctionField.placeInfty_eq_p1PlaceInfty]`
  over a re-statement.** A re-statement collides on the global last name; the checker
  accepts the existing port row against the master source. Probe H is the prototype.
- **R3 — atom 3's `Kx` is definitionally `RatFunc K`; do not build a `IntermediateField`
  or `AdjoinRoot` for it.** `Kx` is a `def … := RatFunc K` with a *new* `Algebra (RatFunc K) (Kx …)`
  structure (`algebraKx`), so the tower is a change of scalar structure on the same type,
  not a new field extension. The `PowerBasis` (row 1887) is then
  `IntermediateField.adjoin.powerBasis` mapped across `adjoin_gen_eq_top` —
  `IntermediateField.{equivOfEq, topEquiv}`, not a fresh `AdjoinRoot`.
- **R4 — atom 3's `separable_minP` goes through `AlgebraicClosure`.** The pin uses
  `Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed (RatFunc K) L` with
  `L := AlgebraicClosure (RatFunc K)` (probe M). There is no direct
  `Polynomial.Separable.map` shortcut the pin needs; do not look for one.
- **R5 — pfbase is not the master's `ResidueTheoremK` route.** The port's
  `kaehlerResidueFunctionalK`/`p0n21_rtk_*`/`p0n22_cpf_*` cone is `Rfam`-indexed and
  proves `ResidueTheoremK`; pfbase proves `ResidueTheorem` via the `K`-functional and the
  `P1ResiduePolynomialPart`/`P1ResiduePrincipalPart` subrows. Do not try to instantiate the
  master cone; the names are different and the statements are not `rfl`-equal.
- **R6 — do not route pfbase's "partial fractions" through
  `Polynomial.mul_prod_pow_inverse_eq_quo_add_sum_rem_mul_pow_inverse`.** The pin's only
  partial-fraction input is the ported theorem `p1PartialFractionSpan_eq_top`; "partial
  fractions" here is the name of the generator decomposition
  (`P1PartialFractionGenerators`), not the mathlib partial-fraction expansion
  (recorded negative §11.3).

## 9. API drift (`v4.34.0`) — what the worker must change

| pin call / assumption | `v4.34.0` status | worker action |
|---|---|---|
| `port_advise` "substitute" for a `def` (Correction 1) | the checker's normalisation drops `def` bodies, so `def … : Prop` rows cross-match | verify every `def` substitution by last name; the 8 rows in Correction 1 are NEW |
| `HeightOneSpectrum K[X]` | notation for `IsDedekindDomain.HeightOneSpectrum (Polynomial K)`; the port writes the expanded form | import the port lemma (probe A); no statement change |
| `ℤᵐ⁰`, unqualified `exp`/`log` (pin 1,643/1,404) | the port writes `WithZero (Multiplicative ℤ)`, `WithZero.exp`, `WithZero.log` | import `Place.ord_eq_neg_log_of_valuationSubring_eq` (`Defs/Place.lean:302`) |
| `Module.Basis Unit …` with explicit `(K)` (pin 4,811/3,549) | the port's `kaehlerRatFuncBasis` is a section-variable `Basis …` (`P1/UnitFinite.lean:49`) | import; the explicit form is the same term |
| pin `private theorem _root_.AlgebraicCurve.Place.ord_neg'` (1,342) | the port's public `Place.ord_neg` has this exact statement (`Defs/PlacesOverDVR.lean:51`) | drop `ord_neg'`, use `Place.ord_neg` |
| pin `private` `ord_add_eq_min` / `ord_add_eq_left` | port-private in `LocalResidue/Calculus.lean` / `P1/EnginePrelude.lean` | re-land `private` verbatim per work order §2 if consumed |
| pin's `scoped instance`s (Correction 4) | invisible to `port_advise`/the checker | land the `Kx` instance layer and `instNontrivialKaehlerRatFunc` explicitly |
| `finsum_eq_finsetSum_of_support_subset` (pfbase 3,757) | exists and is canonical (`BigOperators/Finprod.lean`), confirmed by probe M | keep the camelCase spelling |
| pin `Polynomial.rootMultiplicity` API (atom 3, 1,619/1,713) | present: `exists_eq_pow_rootMultiplicity_mul_and_not_dvd`, `rootMultiplicity_X_sub_C`, `dvd_iff_isRoot` (probe M) | no rename |
| pin `natDegree_sub_eq_left_of_natDegree_lt` (atom 3, 1,855/1,894) | present (probe M) | no rename |
| pin `IntermediateField.adjoin.powerBasis{,_gen,_dim}`, `adjoin.finrank`, `equivOfEq` (atom 3) | present (probe M) | no rename |
| `minpoly.dvd`, `Polynomial.eq_of_monic_of_dvd_of_natDegree_le` (atom 3, 1,855) | present (probe M) | no rename |
| pin `Derivation.{map_aeval, leibniz_div}`, `KaehlerDifferential.span_range_derivation` (atom 3, 1,996) | present (probe M) | no rename |

## 10. Recorded negatives

Confirmed against mathlib `v4.34.0` and the pre-tail port; phrased so the search is not
repeated.

1. **No `P1Tower`, `substPoly`, `subst`, `Kx`, `toKx`, `minP`, `gen`, `pbGen`, `P1PolynomialResidueAtInfinity`,
   `P1PrincipalPartTermZeroOffSupport`, `P1PrincipalPartTwoPlaceCancel{,MOne}`,
   `P1OrdDifferentialPlaceInftyEqNegTwo`, `P1FinitePlaceTermZeroMGeTwo`,
   `P1PartialFractionSpan`, `P1ResiduePolynomialPart`, `P1ResiduePrincipalPart`,
   `kaehlerResidueFunctional{,Kernel}`, `residueTheorem_ratFunc_of_*subrows*` in the
   port.** Greps over `FLTForHuman/` (excluding the in-flight `P1/TwoPlace.lean`) return
   nothing. These are the 98 new rows.
2. **No mathlib declaration lets any of the 98 new rows be dropped.** Every new name is
   either a `P1Tower`/pfbase-specific `def`/`Prop` or a statement over pin vocabulary
   (`gen`, `minP`, `kaehlerResidueTerm`, `ResidueTheorem`, `finitePlace`); the mathlib
   leaves are proof ingredients only (probe M).
3. **`Polynomial.mul_prod_pow_inverse_eq_quo_add_sum_rem_mul_pow_inverse`
   (`Mathlib/Algebra/Polynomial/PartialFractions.lean`) is off-path for pfbase.** The
   pin's `residueTheorem_ratFunc_of_partialFractions` is a `Submodule.span_le` statement
   over `P1PolynomialGenerators`/`P1PrincipalPartGenerators`, and its partial-fraction
   input is the ported `p1PartialFractionSpan_eq_top`; no polynomial division or
   expansion is used. Do not route the "partial fractions" block through mathlib's
   `PartialFractions`.
4. **`Valuation`/`WithZero` supply no `ord_sum_of_injOn`.** Mathlib has
   `Valuation.map_add_of_distinct_val` and `WithZero.log_le_log` (probe M) but no
   finset-minimum-sum lemma; atom 3's row 1,768 is a genuine induction.
5. **No `Place.ord_neg'` and no separate `ord_neg` at the `RatFunc` level.** The only
   `ord_neg` is the general `AlgebraicCurve.Place.ord_neg` (probe A); a search for a
   `RatFunc`-specialised twin is empty.
6. **No `AdjoinRoot`/`IntermediateField` substitute for atom 3's `Kx`.** `Kx` is the type
   `RatFunc K` recycled; `AdjoinRoot p` (the port's `finitePlaceResidueFieldAlgEquivAdjoinRoot`)
   is the *residue field*, not the tower, and is unrelated.
7. **No `def : Prop` substitution can be trusted without a last-name check.** Recorded as
   the general lesson of Correction 1: `EisensteinWeightOne.E1Chi3IsModular` and
   `FLT.AlgebraicCurve.P1DifferentialCoeffRegularFinite` are the two attractors for
   `def … : Prop` in this measurement.
8. **There is no `instNontrivialKaehlerRatFunc` or `Kx`-instance layer in the port.** The
   port's `Nontrivial Ω[(RatFunc K)⁄K]` is obtained through `kaehlerRankOne_ratFunc`
   (`P1/UnitFinite.lean`), not as the pin's named `scoped instance` (Correction 4).

## 11. What this changes for `WORKORDER-P3-2f-tails.md`

**Scope / measurement.**

- Corrected substituted counts: **229 SUBSTITUTE / 87 IMPORT-ADAPT / 98 NEW** over 414
  rows; the work order's "237 substituted" is high by the 8 `def`-body false positives
  (Correction 1).
- The work order's atom-3 "3 new private helpers" is a `drags` count only. Atom 3 is a
  54-declaration block (`P1Tower`), 52 of them public; the work order's §3 table should be
  read as "new *private* helpers", not "new declarations".
- Atom 2 has **zero** new private helpers: its one listed helper
  `ord_eq_neg_log_of_valuationSubring_eq` is ported (Correction 3). Atom 3's listed
  `ord_neg'` is also ported (Correction 2); its only new private helpers are `gen` and
  `isIntegral_gen`.

**Discharged rows (mark import-discharged; the statements still land in `SOURCES`).**

- Atom 2 — the 49 rows of §3.1; atom 3 — the 11 rows of §3.3; pfbase — the 27 rows of
  §3.2. None of these may be re-declared (Correction 5).
- `P1DifferentialCoeffUnitFinite`, `P1PrincipalPartMOneSimplePoleCancel`,
  `P1PlaceInftySimplePoleResidueEulerValue{,TopDeg,Monomial,X}`,
  `P1FinitePlaceSimplePoleResidueAdjoinRootValue`,
  `CanonicalLocalResidueKSimplePoleCoordIndep`, `OrdDifferentialWellDefined`,
  `higherPoleCorrection`, `simplePoleSubmodule`, `poleSubmodule`, `simplePoleResidueAux`,
  `localResidueExtend`, `ratFuncDXCoeff`, `finitePlaceResidueFieldAlgEquivAdjoinRoot`,
  `P1PolynomialGenerators`, `P1PrincipalPartGenerators`, `P1PartialFractionGenerators` —
  all ported under the same last name.

**New work, budgeted.**

- Atom 2 — 6 rows: `P1PrincipalPartTwoPlaceCancelMOne`, rows 4908/4917, the two
  perfect-field `dX` rows, and the headline. The `P1/TwoPlace.lean` model already uses
  `p1MOneAtom_…_{finitePlace,placeInfty}` and the ported Euler-value chain.
- Atom 3 — 54 rows: the `P1Tower` construction (`substPoly`, `subst`, `Kx`, `toKx`,
  `minP`, `gen`, `pbGen`), the field-theory and valuation dictionary, the power basis and
  `trace_mul_inv_derivative`, and the headline. The `Kx` instance layer (Correction 4) is
  in addition to the measured 108 rows.
- pfbase — 38 rows: the `K →ₗ[K] K` residue functional, the kernel/subrow assembly, the
  `MOne`/`MGeTwo` reduction, and the perfect-field specialisations. `instNontrivialKaehlerRatFunc`
  and the `P1PartialFractionSpan`/`P1PolynomialResidueAtInfinity` `def`s are in addition to
  the measured 120 rows.

**Imports the worker may use.** `P1/Core` (the chain head; it transitively supplies every
`P1/*` module), plus the narrow homes `Defs/{Place,PushPull,PlacesOverDVR}`,
`PrincipalDivisors/RatFuncDegree`, `LocalResidue/{Instance,Calculus}`, `Genus/Index`. On
the mathlib side the new blocks need `Mathlib.RingTheory.PowerBasis`,
`Mathlib.FieldTheory.Minpoly.MinpolyDiv`, `Mathlib.RingTheory.AdjoinRoot`,
`Mathlib.RingTheory.Kaehler.{Basic,Polynomial}`, `Mathlib.LinearAlgebra.Basis.Basic`,
`Mathlib.Algebra.BigOperators.Field`. Do **not** import
`Mathlib.Algebra.Polynomial.PartialFractions` (negative §10.3) or
`Mathlib.RingTheory.LaurentSeries`/`HahnSeries` (still off-path from 3.2e §18).

**Checker wiring.** `SOURCES` does not yet list the three `Theorems/Thm_AlgebraicCurve_…`
wrappers or the three `P2M/Sol/S_AlgebraicCurve_…` files; `PORT_FILES` does not yet list
`P1/TwoPlace.lean`, `P1/DivPow.lean`, `P1/PerfectBase.lean`. Append them as work order §5
says. Because the checker matches a port declaration against *any* source candidate by
last name (`AUDIT-mathlib-p3-2e.md` Correction 3), appending the sibling sources cannot
flip the already-ported twin rows to `MISMATCH`; the existing `p1PlaceInfty` rows keep
matching the master source.

**Stop-early.** The two unanticipated items are Correction 1 (the measurement's substituted
set contains 8 rows that are not in the port) and Correction 4 (every `scoped instance` is
invisible to both the measurement and the checker, so the atom-3 `Kx` instance layer must
be budgeted by hand). A worker who trusts the work order's atom-3 "3 new private helpers"
or the 237-row substitute count will under-scope atom 3 by an order of magnitude.
