# P-2a work order — the base-change prelude (D-1)

**Status: open, 2026-10-06.** Set D-1 of [WORKORDER-P2-basechange.md](WORKORDER-P2-basechange.md).
New-file-only. Pin `anthropics/fermats-last-theorem@aa2d8b3`; port mathlib `v4.34.0`.
Method: [../../porting-playbook.md](../../porting-playbook.md) §2.4, §3.1–§3.2, §3.5,
§3.7, §4.

## 1. Scope

Port the **shared prelude** of the base-change column: the two function-field
`pointPullback` maps and the function-field extension lemma, the `Degree`/basis
vocabulary they rest on, and the **tensor-product base change** of a Weierstrass curve's
function field, in both the `General` and the `NoAC` spellings, together with the
`IsogenyEndDatum` base-change block built on it.

This set has **no headline of its own**. It exists so that D-2 (`interm`), D-3 (`bcff`,
`varCh`), D-4 (`conj`) and D-5 (the two silos) import one home instead of each
re-proving 88 declarations (2,393 pin lines; `port_advise` blocks A/B/C). Every
declaration here is a pin declaration, so the checker diffs all of them.

**Not this set:** the `kw_i*` descent block (D-2), the `mrtw60a*` variable-change block
(D-3), `kw_surgehgf4_pck*` (D-4), and the `kw_surge_hgf4_*` / `KwD5BetweenCurves*` seam
(D-4/D-5). If a declaration's only consumers are in those blocks, leave it out.

## 2. Source (pin) and the declaration list

Every path is relative to the pin root. Read the enclosing `namespace` of each
declaration in the pin; declare it at that namespace and the pin's name (the checker
matches by last name, but `norm` strips only `ModularCurve.`/`AlgebraicCurve.`, so the
`PeriodPair.`/`ModularForm.` qualification is part of the diff).

### 2.1 `P2M/Sol/S_WeierstrassCurve_exists_intermediateField_countable_map_eq_and_finrankAlong_eq.lean`

| line | declaration | notes |
|---:|---|---|
| 51 | `structure TreeIsogenyEndDatum` | 4 fields; the checker compares header + ordered field names |
| 58 | `TreeIsogenyEndDatum.degree` | 100 lines |
| 158 | `kw_coordinateRingBasis` (def, 46) | |
| 204 | `kw_functionField_algHom_ext` (100) | |
| 375 | `pointPullbackHomTo_yGen` (57) | |
| 982 | `kw_equation_tensorFracXYGeneralNoAC` (19) | |
| 1001 | `kw_transcendental_tensorFracXGeneralNoAC` (49) | |
| 1050–1071 | `kw_functionFieldTensorFracHomGeneralNoAC{,,_X,_yGen,_bijective}` | 5+6+5+37 |
| 1103 | `kw_functionFieldTensorFracEquivGeneralNoAC` (4) | |
| 1107–1131 | `kw_tensorIotaRingHomGeneralNoAC{,,_tmul,_injective}` | 4+4+4 |
| 1119–1136 | `kw_tensorFracIotaRingHomGeneralNoAC{,,_algebraMap}` | 7+10 |
| 1143 | `kw_isogenyEndDatumBaseChangeIotaGeneralNoAC` (19) | |
| 1162 | `KwIsogenyEndDatumBaseChangeAlongGeneralNoAC` (4) | |
| 1166, 1194 | `…Along_of_isDomain_tensorGeneralNoAC` (28), `…Along_of_tensorIsDomainGeneralNoAC` (27) | |
| 1308 | `kw_tensorIotaRingHom_finiteGeneralNoAC` (4) | |
| 1312 | `kw_tensorFracIotaFinrankSeam_dischargeGeneralNoAC` (157) | |
| 1469 | `kw_isogenyEndDatumBaseChangeAlong_dischargeGeneralNoAC` (13) | |

### 2.2 `P2M/Sol/S_WeierstrassCurve_Affine_isAddCyclic_ker_pointMapOfPushforward_of_baseChange_algHom.lean`

| line | declaration | notes |
|---:|---|---|
| 3278 | `eval₂_polynomial_of_equation_map_target` (11) | |
| 3289–3321 | `pointPullbackCoordHomTo{,,_mk,_comp_algebraMap,_injective}` | 12+6+8+13 |
| 3328–3348 | `pointPullbackHomTo{,,_algebraMap,_polyToFunctionField_X}` | 6+7+8 |
| 3405–3440 | `kw_transcendental_polyToFunctionField_X_over_baseGeneralNoAC` (5), `kw_equation_map_polyToFunctionField_yGen_over_baseGeneralNoAC` (12), `kw_functionFieldMapAlongGeneralNoAC` (6), `…_polyToFunctionField_X` (5), `…_yGen` (4) | |
| 3437 | `KwFunctionFieldTensorIsDomainGeneralNoAC` (`def … : Prop`) | |
| 3485–3505 | `kw_coordinateRingMap_basisGeneralNoAC` (14), `kw_coordinateRingMapAlongGeneralNoAC` (19) | |
| 3518 | `kw_coordinateRingTensor_isDomainGeneralNoAC` (21) | |
| 3539 | `kw_functionFieldTensorIsDomain_dischargeGeneralNoAC` (77) | |
| 3616–3650 | the `General` twins: `kw_transcendental_polyToFunctionField_X_over_baseGeneral` (5), `kw_functionFieldMapAlongGeneral` (6), `…_polyToFunctionField_X` (5), `…_yGen` (4), `KwFunctionFieldTensorIsDomainGeneral` | |
| 3679 | `kw_equation_tensorFracXYGeneral` (19) | |
| 3747–3800 | `kw_functionFieldTensorFracHomGeneral{,,_X,_yGen,_bijective}` (5+6+5+37), `kw_functionFieldTensorFracEquivGeneral` (57) | |
| 3857–3935 | `kw_coordinateRingMap_basisGeneral` (14), `kw_coordinateRingMapAlongGeneral` (19), `kw_coordinateRingTensor_isDomainGeneral` (21), `kw_functionFieldTensorIsDomain_dischargeGeneral` (127) | |

`equation_map_polyToFunctionField_yGen_over_baseGeneral` (14) is at
`S_WeierstrassCurve_Affine_exists_algHom_functionField_baseChange_finrankAlong_eq.lean:707`
— use the copy in whichever file you read first, and record where the other lives.

### 2.3 `P2M/Sol/S_WeierstrassCurve_Affine_exists_algHom_functionField_baseChange_finrankAlong_eq.lean`

| line | declaration | notes |
|---:|---|---|
| 149 | `ofHeightOneSpectrum_injective` (21) | check whether the port already has it under another name |
| 707 | `kw_equation_map_polyToFunctionField_yGen_over_baseGeneral` (14) | |
| 786 | `kw_transcendental_tensorFracXGeneral` (51) | |
| 894–923 | `kw_tensorIotaRingHomGeneral{,,_tmul,_injective}` (4+4+4), `kw_tensorFracIotaRingHomGeneral{,,_algebraMap}` (7+10) | |
| 930 | `kw_isogenyEndDatumBaseChangeIotaGeneral` (19) | |
| 949 | `KwIsogenyEndDatumBaseChangeAlongGeneral` (4) | |
| 953, 980 | `…Along_of_isDomain_tensorGeneral` (27), `…Along_of_tensorIsDomainGeneral` (62) | |
| 1129 | `kw_tensorIotaRingHom_finiteGeneral` (4) | |
| 1133 | `kw_tensorFracIotaFinrankSeam_dischargeGeneral` (157) | |
| 1290 | `kw_isogenyEndDatumBaseChangeAlong_dischargeGeneral` (35) | |

## 3. Deliverable

**`FLTForHuman/WeierstrassCurve/Isogeny/BaseChange.lean`** (new). Pin names, pin
namespaces; public where the pin is public. Helpers local to the module stay
`private` with content names (**no `kw_` prefix** — the port no longer uses it when
promoting new private helpers, and the checker follows that). Its public surface is the
union of the pin-public declarations of §2; do not invent names.

Imports: `FLTForHuman.WeierstrassCurve.FunctionFieldQuadratic`,
`FLTForHuman.WeierstrassCurve.Isogeny.ConditionalCurrency`,
`FLTForHuman.WeierstrassCurve.GenusOnePlaceGateCentred`,
`FLTForHuman.WeierstrassCurve.Place.Dictionary`, plus the specific mathlib modules the
pin uses (`Mathlib.RingTheory.TensorProduct.*` is likely; never `import Mathlib`).

## 4. Route, with recorded negatives

- **Most of the vocabulary is already ported under other names.** `yGen`,
  `transcendental_polyToFunctionField_X`, `equation_map_polyToFunctionField_yGen`,
  `algebraMap_polynomial_eq_mk_C`, `IsFinitePlace.*`, `restrictAlong_eq_infinitePlace`,
  `pointEnd'_eq_of_seam` live in `FunctionFieldQuadratic.lean`, `Place/Dictionary.lean`
  and `IsogenyEndDatum/Engine.lean`. Before transcribing anything, run
  `port_advise.py --nodes <this set's pin decls>` and import the hits; the tool's
  statement test is the contract.
- **The `NoAC`/`General` pair is not a copy.** `…NoAC` drops the algebraically-closed /
  algebraic-closure hypothesis. Port both spellings at their pin names; only merge them
  if one is a strict specialisation and the pin's `NoAC` proof is a two-line derivation —
  and then record it.
- **`def … : Prop` bodies.** `KwFunctionFieldTensorIsDomainGeneral{,NoAC}`,
  `KwIsogenyEndDatumBaseChangeAlongGeneral{,NoAC}` and the like are opaque `Prop`s; the
  checker sees only `Prop`, so do **not** drop any of them on the strength of a
  substitution hit. `grep -c` their bodies in the pin first.
- **Do not port the `kw_surge_hgf4_*` / `KwD5BetweenCurves*` seam.** It is D-4/D-5; if the
  tensor block's `_of_tensorIsDomainGeneral` lemmas seem to need it, they do not — those
  lemmas are the interface D-5 consumes.

## 5. Bound and stop conditions

Stop and report (do not push): an unported prerequisite outside §2; a `NoAC`/`General`
pair that is not a specialisation and cannot both be stated; a pin statement that does
not transcribe to `v4.34.0`; any pull toward the S row or `eval_modularPolynomial_…`.

## 6. Build discipline (binding)

> `lake env lean -DmaxHeartbeats=4000000 -DautoImplicit=false <file>` is the edit loop;
> `lake build <module>` when done; **one** `lake build` per wave, `flock`ed on
> `.lake/flt_build.lock` and bounded (`timeout 60`/`90`/`300`), timed wall + user/sys.
> Never raise `maxHeartbeats`. Iterate in bounded blocks, not per declaration.

This module imports the 16 MB `LevelField`/`WeightOne` oleans through
`Elliptic/PeriodPair/Discriminant.lean` (via `Place/Dictionary.lean`): **time the first
`lake env lean` on a stub before writing the whole file**, and report the figure.

## 7. Verification

- `lake env lean` clean; `lake build FLTForHuman.WeierstrassCurve.Isogeny.BaseChange`.
- Append to `PORT_FILES` (last): `FLTForHuman/WeierstrassCurve/Isogeny/BaseChange.lean`.
- Append to `SOURCES` (last, wrapper before its `S_` file) the two wrappers
  `Theorems/Thm_WeierstrassCurve_exists_intermediateField_countable_map_eq_and_finrankAlong_eq.lean`,
  `Theorems/Thm_WeierstrassCurve_Affine_exists_algHom_functionField_baseChange_finrankAlong_eq.lean`
  and the two `S_` files of §2.1 and §2.3. (D-1 draws nothing from `siloBC` that the
  other three do not also carry; if a declaration forces `siloBC`, add it too and say so.)
- `python3 spec/check_flt_statements.py` → **0 mismatched / 0 missing**. Baseline
  `5869 identical (313 promoted, 5 renamed), 0 mismatched, 0 missing, 36 own, 5905 checked`.
  Reconcile the delta against §2 (it is the count of §2 declarations that the checker
  had not already seen; a mismatch is a bug).
- Whole-tree `flock`ed `lake build` at the wave end; report jobs and seconds.
- No `sorry`; `grep -c` of every declaration dropped as already-present, with the
  survivor's name, in the friction log entry.
