# Work order — P3.2d: the ℙ¹ residue core, chunk 3 (differential coefficient / Kähler / principal-part core)

**Status: ready to dispatch.** Row 2 of [../PORTING-RR.md](../PORTING-RR.md) §3,
block 3.2d. **Boilerplate, build discipline, checker-wiring mechanics and the report
shape are exactly as [WORKORDER-P3-2b-p1core-1.md](WORKORDER-P3-2b-p1core-1.md)
§4–§7 — read that order first and follow it verbatim; this order states only what
differs.** Loop: [WORKFLOW.md](WORKFLOW.md); a parallel `AUDIT-mathlib-p3-2d.md` is
dispatched with this order.

Baseline: checker **3448 identical / 0 mismatched / 0 missing / 30 own-proof**
(3478 checked); `Defs/P1ResidueCore.lean` (chunks 1–2, 2,429 ln) and
`Defs/LocalResidueCalculus.lean` (3.2d′, 1,229 ln) green.

## 0. Scope — APPEND to the existing `Defs/P1ResidueCore.lean`

Declarations **#290–#434** (pin lines **6745–9499**) of the master ℙ¹ `S_` file
(inventory `tools/deps/build/p32_master_inventory.txt` rows 290–434, 145 rows).
Append after chunk 2 in pin order. **Do not transcribe past the last line of #434
(line 9499)**; do not restructure chunks 1–2.

Content (the ℙ¹ differential-coefficient / Kähler / principal-part core):

- `P1DifferentialCoeffUnitFinite` (#290 — the 3.2c audit notes this name was
  mis-attributed to 3.2c in the brief; it is the **first row of this chunk**),
  `p1DifferentialCoeffRegularFinite_of_unitFinite`;
- the Kähler/RatFunc structure block — `kaehlerPolynomialBasis`,
  `instFormallyEtalePolynomialRatFunc`, `kaehlerRatFuncBasis`, `kaehlerRankOne_ratFunc`,
  `instIsCurveOverRatFunc`, and the `HasSeparatingTranscendentalCore` /
  `hasSeparatingTranscendental_of_core` / `valSubringKaehlerFinite_of_core` rows;
- the ramification-inertia wrappers — `sum_ramificationIndex_mul_inertiaDeg_of_forall_mem_iff`,
  `sum_ramificationIndex_mul_deg_of_forall_mem_iff`,
  `ramificationInertiaIdentity_of_finiteDimensional`;
- the degree-one / principal-part computation — `derivative_monic_natDegree_one_eq_one`,
  `D_algebraMap_polynomial_degOne`, `eq_C_coeff_zero_of_degree_lt_degOne`,
  `p1PrincipalPartAtom_mul_differentialCoeff_dX_degOne`,
  `P1FinitePlaceCanonicalResidueAtomMGeTwoHigherDeg`,
  `ord_placeInfty_X_pow_natDegree_div`, `X_pow_natDegree_div_mem_placeInfty`,
  `degree_X_pow_natDegree_sub_lt_of_monic`;
- the separability leaves — `isSeparable_of_charZero_of_finiteDimensional`,
  `isSeparable_adjoin_of_charZero_of_finiteDimensional`.

**Explicitly not this set:** rows #435+ (chunk 4 / 3.2e). `P1DifferentialCoeffUnitFinite`
(#290) is the first row.

## 1. Deliverable

Append-only edits to `FLTForHuman/AlgebraicCurve/Defs/P1ResidueCore.lean`. No
statement of chunks 1–2 changes. **Add `import FLTForHuman.AlgebraicCurve.Defs.LocalResidueCalculus`**
(3.2d′) and import the generic residue names from it rather than re-transcribing
them — the master re-uses `p0n22_cpf_res_*` (63 references) and the
`res_differentialCoeff_D_*` names. The five helpers that are `private` in **both**
modules (`Place.ord_add_eq_min`, `ModularCurve.MilneAvAg9bRd15UnitNormalFormLaurentSeed.ag9b15u_*`)
are already private in this module (chunk 1/2) — keep using the module-local copies
(the duplication is recorded debt for the closeout refactor round; do **not** edit
`LocalResidueCalculus`).

## 2. Statements

From the pin `S_` file verbatim. Where the port already has the statement, import it
(§3).

## 3. Reuse — import, do not re-prove

Re-check every row against `build/p32_engine_advise.log` §1 and the now-ported
phase 3.1/3.2a/3.2b/3.2c/3.2d′ modules before writing. On this chunk:

- the generic local-residue names (`p0n22_cpf_res_*`, `res_differentialCoeff_D_*`,
  `D_pow_succ_inv`, `gate_canonicalLocalResidueDataK_uniformizer_inv`) —
  **`Defs/LocalResidueCalculus.lean`** (3.2d′), import;
- the `valSubringKaehler*`/`HasSeparatingTranscendentalCore`/Kaehler machinery —
  `Canonical/HasCanonicalDivisor.lean` (phase 2) and
  `IsCurveOver/SeparatingTranscendental.lean` (phase-1 R);
- `sum_ramificationIndex_mul_inertiaDeg` and its fibre API —
  `Defs/PushPull.lean:678` + `WeilExchange/FiberOverCount.lean` (already ported);
- the ℙ¹ dictionary and the `ag9b15u_*`/`Mp72*`/`KwNo6Pin` machinery — `P1Dictionary`,
  `P1ResidueCore` chunks 1–2, `CanonicalLocalResidueInstanceV2`.

**Audit leads** (the parallel `AUDIT-mathlib-p3-2d.md` confirms): `KaehlerDifferential`
API (`KaehlerDifferential.map`, `.D`, basis/rank-one lemmas), `PerfectField`/
`IsSeparable` for the char-0 leaves, `Polynomial.derivative`/`natDegree`/`degree_lt`
for the monic computations, `Valuation.map_add_of_distinct_val`. Do not bank an
unelaborated claim.

**Audit result (`AUDIT-mathlib-p3-2d.md`, landed — 67 SUBSTITUTE / 65
PROOF-INGREDIENT / 13 BESPOKE over 145 rows).** The headline: **rows #307–#404
(98 rows!) merely duplicate the phase-2 pin file
`S_AlgebraicCurve_hasCanonicalDivisor_of_isCurveOver.lean`**, whose port is
`Canonical/HasCanonicalDivisor.lean` — import, do not re-transcribe. 59 rows have
exact public copies there (unsuffixed names); some phase-2 copies carry the pin's
own `_s12` suffix (`eq_top_of_idealOfLE_eq_bot_s12`, the six
`IntermediateField.*_s12`, …) and need aliases. **Ten substitutes are `private` in
`HasCanonicalDivisor`** (`ofPrime_congr_s12`, `inv_mem`/`div_mem_of_not_mem_centerIdeal`,
`coe_toKSubalgebra`, the `Transcendental.*_s12`/`inv_s12` at :788–:813) — re-land
them `private` locally at the pin names and report as promotion debt; **do not edit
`HasCanonicalDivisor`**. #319/#320 import from
`Defs/CanonicalLocalResidueInstanceV2.lean:1656/1668`; #328 is already
`RationalFunctionField.instHasPrincipalDivisors` (`P1ResidueCore.lean:866`); the ℙ¹
Kähler block #292–#296 is mathlib-only. The genuinely new rows are #290–#306, #321,
#354–#362 (AdjoinRoot trace engine), #374–#387 (finite-place residue engine),
#408–#420 (placeInfty Euler value), #429–#434. Drift: `Ideal.sum_ramification_inertia`
does not exist in v4.34 — it is `Ideal.sum_ramification_inertia_eq_finrank`; reuse
`WeilExchange/FiberOverCount.lean:44–100`; generic `Finset.sum_div` is gone;
`Polynomial.degree_sub_lt` → `degree_sub_lt_left`; `K⟮t⟯` needs `open IntermediateField`.

## 4. Build discipline, checker wiring, report shape

As 3.2b §4–§7. The checker wiring is **already done** for this module (the master
`S_` file and wrapper are in `SOURCES`), so no `spec/check_flt_statements.py` edit is
needed; verify the checker rises and stays `0 mismatched / 0 missing`. Append
friction under `### Set 3.2d`.

## 5. Stop-early / gaps

As 3.2b §6. A forward reference past line 9499 → stop and report; the boundary moves.
An out-of-measured-file declaration → resolve locally `private` with the statement
verbatim and report the pin `file:line`.
