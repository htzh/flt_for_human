# Work order — P3.2c: the ℙ¹ residue core, chunk 2 (differential-coefficient / principal-part ord layer)

**Status: ready to dispatch.** Row 2 of [../PORTING-RR.md](../PORTING-RR.md) §3,
block 3.2c. **Boilerplate, build discipline, checker-wiring mechanics and the
report shape are exactly as in [WORKORDER-P3-2b-p1core-1.md](WORKORDER-P3-2b-p1core-1.md)
§4–§7 — read that order first and follow it verbatim; this order states only what
differs.** Loop: [WORKFLOW.md](WORKFLOW.md); a parallel `AUDIT-mathlib-p3-2c.md` is
dispatched with this order.

Baseline: checker **3356 identical / 0 mismatched / 0 missing / 30 own-proof**
(3386 checked); `Defs/P1ResidueCore.lean` (848 ln, chunk 1) green.

## 0. Scope — APPEND to the existing `Defs/P1ResidueCore.lean`

Declarations **#145–#289** (pin lines **3388–6744**) of the master ℙ¹ `S_` file
(inventory `tools/deps/build/p32_master_inventory.txt` rows 145–289, 145 rows).
The file's chunk 1 is already there; append after it in pin order. **Do not
transcribe past the last line of #289 (line 6744)**, and do not restructure chunk 1.

Content (the ℙ¹ differential-coefficient / principal-part `ord` layer):

- the ℙ¹ `ord` leaves — `ord_ofHeightOneSpectrum_of_span` (row 145),
  `ord_ofHeightOneSpectrum_eq_zero_of_notMem`, `ord_placeInfty`,
  `ord_placeInfty_algebraMap`, `single_add_single_apply_eq_ord`,
  `degree_single_add_single`, `ord_placeInfty_X_inv`, `ord_placeInfty_X_pow`,
  `ord_placeInfty_ratFuncDXCoeff_ge`, …;
- the ℙ¹ divisor / degree block — `degree_eq_zero_of_forall_eq_ord{,_algebraMap}`,
  `principalDivisor`, `principalDivisor_apply`, `degree_principalDivisor`,
  `instHasPrincipalDivisors`, `eq_ord_of_addHom_of_nonneg_iff`,
  `ordDifferentialWellDefined_ratFunc`;
- the differential-coefficient layer — `D_ratFuncX_eq_neg_X_sq_smul_D_inv`,
  `differentialCoeff_placeInfty_D_X_eq`,
  `ord_differentialCoeff_placeInfty_D_X_inv_eq_zero`,
  `ordDifferential_placeInfty_D_ratFuncX`, `P1DifferentialCoeffUnitFinite`,
  `exists_dXCoeff_*`, `exists_unit_dXCoeff_*`, `exists_ord_zero_smul_of_smul_dX_eq`;
- the principal-part atoms — `p1PrincipalPartAtom`, `one_le_/two_le_ord_placeInfty_p1PrincipalPartAtom`,
  `ord_finitePlace_p1PrincipalPartAtom`, `not_dvd_of_degree_lt`,
  `ord_finitePlace_of_degree_lt`;
- the `ag9b*`/`mp72*`/`canonicalLocal*` rows on this path.

**Explicitly not this set:** rows #290+ (chunks 3.2d–e) and the atom/base files.
`ord_ofHeightOneSpectrum_of_span` (row #145) is the **first** row of this chunk.

## 1. Deliverable

Append-only edits to `FLTForHuman/AlgebraicCurve/Defs/P1ResidueCore.lean`. No
statement of chunk 1 changes. New public declarations land at the pin names; the
pin-private helpers stay `private`.

## 2. Statements

From the pin `S_` file verbatim (no `Theorems/` wrappers for most). Where the port
already has the statement, import it (§3).

## 3. Reuse — import, do not re-prove

Re-check every row against `build/p32_engine_advise.log` §1 and against the
**now-ported phase 3.1/3.2a/3.2b modules** before writing it. On this chunk:

- `ord_placeInfty`, `ord_placeInfty_algebraMap`, `single_add_single_apply_eq_ord`,
  `degree_single_add_single`, `exists_sub_algebraMap_intDegree_neg`,
  `degree_eq_zero_of_forall_eq_ord` — **phase 3.2a** `Defs/P1Dictionary.lean`
  (some are public there; some are the `RatFuncDegree` private copies transcribed in
  P1Dictionary — check the exact name);
- `OrdDifferentialWellDefined`, `principalAdele`, `P1*`/`p1PrincipalPartAtom`,
  `P1DifferentialCoeffUnitFinite` — **chunk 1 of this module** (rows 6/40–43/79/80);
- `Lg37`/`Mp72*`/`KwNo6Pin` machinery — `Defs/CanonicalLocalResidueInstanceV2.lean`;
- `inertiaDeg_eq_inertiaDeg_fiberCenter`, `surjective_residueOfCenter`,
  `neg_log_valuation_fiberCenter_eq_ord` — `Defs/PlaceDictionary.lean` (the audit
  places these pin lines 4038/3951/3829 in this chunk's range);
- mathlib (audit): `Valuation.map_add_of_distinct_val`, `WithZero.*`,
  `IsDiscreteValuationRing.*`, `Polynomial.mul_prod_pow_inverse_eq_quo_add_sum_rem_mul_pow_inverse`
  (`Mathlib.Algebra.Polynomial.PartialFractions`), `RatFunc.monic_denom`.

**Audit leads for this chunk** (the parallel `AUDIT-mathlib-p3-2c.md` confirms):
`RatFunc.inftyValuation`/`intDegree` via the port's `placeInfty` connection;
`RatFunc.num_div_denom`, `isCoprime_num_denom`; `Finsupp.prod_*`/`Finset.prod_zpow`
for the coefficient atoms; `Ideal.inertiaDeg`/`Ideal.ramificationIdx` (unprimed,
v4.34 — the primed names are deprecated). Do not bank an unelaborated claim.

**Audit result (`AUDIT-mathlib-p3-2c.md`, landed — 72 SUBSTITUTE / 67
PROOF-INGREDIENT / 6 BESPOKE over 145 rows).** Substitutes: rows #145–#155 →
`P1Dictionary`/`RatFuncDegree` (11); #164–#176 → `Defs/PlaceDictionary.lean` (13,
but #164 `eq_ord_of_addHom_of_nonneg_iff` is **`private` at `:44`** — promote or
consume in-file); #177–#186, #189, #251–#253 → `HasCanonicalDivisor.lean` (14);
#192–#202, #208–#211, #254–#270 → `CanonicalLocalResidueInstanceV2.lean` (32; note
the port's `higherPoleCorrection` has **no prime**); #220 → `Defs/CanonicalDivisor`;
#237 → `Genus/Index`. **#156 `instHasPrincipalDivisors` is NOT in the port** (chunk
1 only assumes `[HasPrincipalDivisors K (RatFunc K)]`) — land it first.
BESPOKE (6): `dX` #212, `KaehlerRankOne` #233, `RamificationInertiaIdentity` #236,
`principalDivisorOf` #242, `CanonicalLocalResidueKDifferentialCoordIndep` #246,
`ratFuncDXCoeff` #272. **Reuse win:** mathlib
`Mathlib/RingTheory/Polynomial/Wronskian.lean` (`Polynomial.wronskian`,
`natDegree_wronskian_lt_add:111`, `IsCoprime.wronskian_eq_zero_iff`) — the pin's
`n'd − nd'` is `-wronskian n d`, so #271 collapses. **Route:** #236–#244 need not
re-derive the fibre count — `PushPull`'s `FundamentalIdentity` (:632) /
`SumRamificationInertia` (:677) / `WeilExchange/FiberOverCount.lean:33` already
carry it; `Place.IsRational` is defeq #245; `IsCurveOver.kaehler_free_rank_one` is
#233's conjunction. **Correction:** `P1DifferentialCoeffUnitFinite` is row **#290**
(pin 6745) — out of scope; the in-scope name is `P1DifferentialCoeffRegularFinite`.
Drift: `inertiaDeg'_algebraMap` deprecated → `Ideal.inertiaDeg_eq_of_isMaximal`;
`Ideal.ramificationIdx_spec` deprecated → the primed one; `PerfectField.ofCharZero`
is an instance; `Polynomial.multiplicity` does not exist.

## 4. Build discipline, checker wiring, report shape

Exactly [WORKORDER-P3-2b-p1core-1.md](WORKORDER-P3-2b-p1core-1.md) §4–§7. The
checker wiring is **already done** (the master `S_` file and wrapper are in
`SOURCES`; the module is in `PORT_FILES`), so no `spec/check_flt_statements.py`
edit is needed. Verify the checker rises and stays `0 mismatched / 0 missing`.
Append friction under `### Set 3.2c`.

## 5. Stop-early / gaps

As 3.2b §6. In particular: if a row's proof reaches a declaration from a **later**
chunk (a forward reference), stop and report — the chunk boundary moves, it is not
worked around. If the port's public copy of a row differs from the pin's statement
by binders, the checker is the arbiter; report the row.
