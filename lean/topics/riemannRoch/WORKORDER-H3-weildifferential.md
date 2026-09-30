# Work order — H3: the differentials bridge and the Weil-differential interface

**Status: DISPATCHED (2026-09-29).** H2 reviewed green (checker 2848/0/0).
Boilerplate/build clauses: `WORKORDER-H1a-index.md` §4–§5. Plan: `PLAN.md` §2.

## 0. Scope

The conditional interface at the end of phase 1: regular differentials ≃
`omegaSpace 0`, plus the pin definition modules it needs. The pin states the
headline with `(hRT : ResidueTheorem K F)` and `[HasCanonicalDivisor (K := K) (F := F)]`,
so it lands **with those hypotheses** and is fed later (PORTING-RR §1, the last row).

**Target:** `exists_linearEquiv_regularDifferentials_omegaSpace_zero` (295 ln).

**Definition modules to port** (not in Set D):
| module | pin | decls |
|---|---|---:|
| `Def_ModularCurve_CanonicalDivisorUniformizer.lean` | 35 ln | — |
| `Def_AlgebraicCurve_LocalResidue.lean` | 308 ln | 30 |
| `Def_AlgebraicCurve_WeilOfKaehler.lean` | 133 ln | 10 (incl. `def ResidueTheorem`) |
| `Def_AlgebraicCurve_RegularDifferentials.lean` | 46 ln | 3 |

**S_ union to home:** 25 names / 248 lines (`rr_homes.txt` §H3): `kaehlerToWeil`,
`kaehlerToWeilLinear`, `kaehlerToWeil_*`, `kaehlerResidueTerm_*`, `regularToOmega`,
`coe_regularToOmega_apply`, `weilSmul_kaehlerToWeil`,
`mem_regularDifferentials_of_canonicalDivisorOf_nonneg`,
`canonicalDivisorOf_nonneg_of_mem_regularDifferentials`, `mem_vs_of_ord_nonneg`,
`ord_nonneg_of_mem_vs`, `differentialCoeff_{add,smul_algebraMap}_s2`,
`hasSeparableResidue_of_perfectField`, `nonempty_place_of_constantsAreBase`,
`exists_linearEquiv_regularDifferentials_omegaSpace_zero'`.

**Not this set:** the analytic `ResidueTheorem` producers (`residueTheoremK`,
`tateAgreement`, `CellDissection` — phase 3, out of phase-1 scope). H3 only
*assumes* `ResidueTheorem`.

## 1. Deliverables

- `FLTForHuman/AlgebraicCurve/Canonical/WeilDifferential.lean` (the S_ union + the headline).
- `FLTForHuman/AlgebraicCurve/Defs/{LocalResidue,WeilOfKaehler,RegularDifferentials,CanonicalDivisorUniformizer}.lean` (the four pin definition modules, in pin import order).
- namespace `AlgebraicCurve`, pin names verbatim; `Place`-level helpers as the pin
  namespaces them.

## 2. Route and risk

- The chain is: `ResidueTheorem` → `weilOfKaehler` → `kaehlerToWeil` =
  `weilOfKaehler` → `regularToOmega` → the linear equivalence onto `omegaSpace 0`.
  `RegularDifferentials.regularDifferentials` is a `Submodule K Ω[F⁄K]`; `omegaSpace 0`
  is the dual annihilator in `Defs/AdelicIndex.lean`.
- The two `s2` helpers (`differentialCoeff_add_s2`, `differentialCoeff_smul_algebraMap_s2`)
  are `Place.differentialCoeff` additivity/scalar facts against Set D's
  `Place.differentialCoeff`; if Set D's `differentialCoeff` has a different binder
  shape, stop and report.
- Stop-early risk: `WeilOfKaehler`/`LocalResidue` may need a `Def_ModularCurve_*`
  or `ResidueDiscs`/`StandardAnnulus` declaration outside this set — report it, do
  not inline.
- The headline must keep the pin's `hRT`/`HasCanonicalDivisor` hypotheses verbatim;
  do not discharge them.

## 3. Verification

Checker `SOURCES` += the five pin files (four `Definitions/Def_*` + the `S_…` file)
and their `Theorems/Thm_*` wrappers, wrappers first; `PORT_FILES` += the five new
modules. `#print axioms` on the headline and on `ResidueTheorem`. Build clause as
H1a §4. Confirm the headline is **conditional** by checking its statement text in the
checker output.

## Appendix

`tools/deps/build/rr_homes.txt` §H3 (25 rows); the four definition modules'
inventories regenerate with `port_advise`'s inventory as in `PLAN.md` §6.
