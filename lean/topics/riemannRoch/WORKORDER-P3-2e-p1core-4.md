# Work order — P3.2e: the ℙ¹ residue core, chunk 4 (the residue computation and the atom-1 headline)

**Status: ready to dispatch.** Row 2 of [../PORTING-RR.md](../PORTING-RR.md) §3,
block 3.2e (the final master-file chunk). **Boilerplate, build discipline,
checker-wiring mechanics and the report shape are exactly as
[WORKORDER-P3-2b-p1core-1.md](WORKORDER-P3-2b-p1core-1.md) §4–§7 — read that order
first and follow it verbatim; this order states only what differs.** Loop:
[WORKFLOW.md](WORKFLOW.md); a parallel `AUDIT-mathlib-p3-2e.md` is dispatched with
this order.

Baseline: checker **3529 identical / 0 mismatched / 0 missing / 30 own-proof**
(3559 checked); `Defs/P1ResidueCore.lean` chunks 1–3 (3,971 ln) and
`Defs/LocalResidueCalculus.lean` (3.2d′) green, and the core now **imports**
`LocalResidueCalculus` (the 2026-09-30 dedup refactor).

## 0. Scope — APPEND to the existing `Defs/P1ResidueCore.lean`

Declarations **#435–#579** (pin lines **9500–13173**, the end of the file) of the
master ℙ¹ `S_` file (inventory `tools/deps/build/p32_master_inventory.txt` rows
435–579, 145 rows). Append after chunk 3 in pin order. This completes the master
file; the last row #579 is pin `solution`, the atom-1 headline
`trace_localResidue_placeInfty_X_pow_eq_zero`.

Content (the ℙ¹ residue computation and its headline):

- the simple-pole / Euler-value machinery — `P1PlaceInftySimplePoleResidueEulerValueX`,
  `p1MonomialAtom_eq_monicRatio_mul`,
  `p1XInvAtom_mul_differentialCoeff_dX_mem_simplePole_placeInfty`,
  `simplePoleResidueAux_placeInfty_monomial_eq_X`,
  `p1PlaceInftySimplePoleResidueEulerValueMonomial_of_X`,
  `p1PrincipalPartMOneSimplePoleCancel_of_inftyX`;
- the separability/transcendence block — `IsPurelyTranscendentalSimple`,
  `hasSeparatingTranscendentalCore_of_isPurelyTranscendentalSimple`, ….;
- the main computation — `p0n22_cpf_*` ℙ¹ rows (`res_differentialCoeff_*`,
  `canonicalLocalResidueKDifferentialCoordIndep_ratFunc_of_isAlgClosed`,
  `residueTheoremK_ratFunc_of_isAlgClosed_of_charP` / `_main`), the `ag9b*` and
  `kaehlerResid*`/`canonicalLoc*` rows, `RationalFunctionField.placeInfty_eq_p1PlaceInfty`,
  and the headline `solution`.

**Shares with row 6:** the `residueTheoremK_ratFunc_of_isAlgClosed_*` rows here
*are* the K base file's shared engine — the port writes them once in this module
(row 6's own work item stays its residual, per the recorded decision).

## 1. Deliverable

Append-only to `FLTForHuman/AlgebraicCurve/Defs/P1ResidueCore.lean`. No statement of
chunks 1–3 changes. **Import the generic names from `LocalResidueCalculus`** (the
core already imports it) rather than re-transcribing: the master references
`p0n22_cpf_` 63× and the `res_differentialCoeff_D_*`/`D_pow_succ_inv`/`gate_…` names.
The five helpers private in both modules remain duplicated (recorded debt) — keep
using the module-local copies.

## 2. Statements

From the pin `S_` file verbatim; the last row `solution` is the atom-1 headline and
its public name is `RationalFunctionField.trace_localResidue_placeInfty_X_pow_eq_zero`
(check the `Thm_*` wrapper's binders). Never change a statement to ease a proof.

## 3. Reuse — import, do not re-prove

Re-check every row against `build/p32_engine_advise.log` §1 and the now-ported
modules. On this chunk especially:

- **`Defs/LocalResidueCalculus.lean`** — the whole generic `p0n22_cpf_res_*` /
  `res_differentialCoeff_D_*` layer (import; this is the reason the core now imports
  it);
- `Defs/P1ResidueCore.lean` chunks 1–3 — the ℙ¹ dictionary, the `OrdDifferential*`
  / `p1DifferentialCoeff*` layer, `ratFuncDXCoeff`, the `p0n22_cpf_*` ℙ¹ rows already
  landed;
- `Defs/{CanonicalLocalResidueInstanceV2,P1Dictionary,PlaceDictionary,RatFuncPlaces}.lean`
  and `Canonical/HasCanonicalDivisor.lean` as before.

**Audit leads** (the parallel `AUDIT-mathlib-p3-2e.md` confirms): the `p0n22`/`ag9b`
computation is mostly pin-bespoke (`Place.ord`, `uniformizer`, `differentialCoeff`,
`LaurentSeries`-free); mathlib supplies `geom_sum_mul`, the char-p Frobenius API,
`Polynomial`/`Finsupp` leaves and `Derivation.*`. Do not bank an unelaborated claim.

## 4. Build discipline, checker wiring, report shape

As 3.2b §4–§7. Checker wiring is already done; no `spec/check_flt_statements.py`
edit. Verify the checker rises and stays `0 mismatched / 0 missing`. Append friction
under `### Set 3.2e`.

## 5. Stop-early / gaps

As 3.2b §6. This is the last chunk, so there is no forward reference; if a proof
reaches a declaration outside the measured files, resolve it locally `private` with
the statement verbatim and report the pin `file:line`.
