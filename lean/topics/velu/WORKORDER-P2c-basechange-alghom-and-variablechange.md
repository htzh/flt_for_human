# P-2c work order — base change to ℂ and the variable-change equiv (D-3)

**Status: open, 2026-10-06.** Set D-3 of [WORKORDER-P2-basechange.md](WORKORDER-P2-basechange.md).
New-file-only. Pin `anthropics/fermats-last-theorem@aa2d8b3`; port mathlib `v4.34.0`.
Depends on D-1 (`BaseChange.lean`). Method:
[../../porting-playbook.md](../../porting-playbook.md) §2.4, §3.1–§3.2, §3.5, §4.

## 1. Scope

Two mid-size, independent nodes:

| node | pin raw | module |
|---|---:|---|
| `WeierstrassCurve.Affine.exists_algHom_functionField_baseChange_finrankAlong_eq` | 1,336 | `WeierstrassCurve/Isogeny/BaseChangeAlgHom.lean` |
| `WeierstrassCurve.nonempty_functionField_algEquiv_of_variableChange` | 744 | `WeierstrassCurve/Isogeny/VariableChangeAlgEquiv.lean` |

The first pushes an isogeny datum from the algebraic closure of a countable subfield to ℂ
along an `AlgebraHom`, preserving `finrankAlong`; the second produces an `AlgEquiv` of
function fields from a variable change.

**Not this set:** D-1's prelude (import it), D-2's `kw_i*` block, D-4's `kw_surgehgf4_pck*`
and the seam, D-5's silos, the S row.

## 2. Source (pin)

- `P2M/Sol/S_WeierstrassCurve_Affine_exists_algHom_functionField_baseChange_finrankAlong_eq.lean` (1,336).
  Wrapper `Theorems/Thm_WeierstrassCurve_Affine_exists_algHom_functionField_baseChange_finrankAlong_eq.lean`
  is the statement authority. The node-unique declarations (13 / 358 lines) are
  `kw_isogenyEndDatumBaseChangeAlong_{of_isDomain_tensorGeneral,of_tensorIsDomainGeneral,dischargeGeneral}`,
  `kw_tensorFracIotaRingHomGeneral{,,_algebraMap}`, `kw_isogenyEndDatumBaseChangeIotaGeneral`,
  `KwIsogenyEndDatumBaseChangeAlongGeneral`, `kw_tensorIotaRingHomGeneral{,,_tmul,_injective}`,
  `kw_tensorIotaRingHom_finiteGeneral`, `kw_tensorFracIotaFinrankSeam_dischargeGeneral`,
  `ofHeightOneSpectrum_injective`, `kw_equation_map_polyToFunctionField_yGen_over_baseGeneral`.
  **Careful:** `kw_tensorIotaRingHomGeneral*`, `kw_tensorFracIotaRingHomGeneral*`,
  `kw_isogenyEndDatumBaseChangeIotaGeneral`, `KwIsogenyEndDatumBaseChangeAlongGeneral{,_…}`,
  `kw_tensorFracIotaFinrankSeam_dischargeGeneral` are shared with D-1 — they belong to D-1
  if D-1's list has them; port only what D-1 did not.
- `P2M/Sol/S_WeierstrassCurve_nonempty_functionField_algEquiv_of_variableChange.lean` (744).
  Wrapper `Theorems/Thm_WeierstrassCurve_nonempty_functionField_algEquiv_of_variableChange.lean`
  is the statement authority. The 25 node-unique declarations (276 lines) are the `mrtw60a*`
  block: `mrtw60a_{coordHom_ext,funHom_ext,funHomInv_comp_funHom,funHom_comp_funHomInv,transcendental_affine,transcendental_xFwd,equation_fwd,aeval_xFwd_injective,yInv_shape,yFwd_eq_vcY,xInv_shape,yFwd_shape,inv_smul,xFwd_shape,xFwd_eq_vcX,inv_u_mul_u,xFwd,yFwd}`
  and `mrtw60aVC{,FunHom,FunHomInv,FunHom_X,FunHom_yGen,FunHomInv_X,FunHomInv_yGen,VCPlaceSeamAlgEquiv}`.
  It imports `Def_WeierstrassCurve_VariableChangePointEquiv` (ported as
  `WeierstrassCurve/VariableChangePoint.lean`) — reuse it.

Run `port_advise.py --nodes <both>` before transcribing and import the hits.

## 3. Deliverable

Two new modules, both importing D-1 (and only the ported modules below them):
`FLTForHuman/WeierstrassCurve/Isogeny/BaseChangeAlgHom.lean` and
`FLTForHuman/WeierstrassCurve/Isogeny/VariableChangeAlgEquiv.lean`. Pin names/namespaces;
headlines from the wrappers' binders; helpers `private` with content names (**no `kw_`
prefix**). Never `import Mathlib`.

## 4. Route, with recorded negatives

- **Both nodes are generic over the base field.** `bcff` is `WeierstrassCurve.Affine.*`; the
  variable-change one is `WeierstrassCurve.*`. Keep the pin's namespaces.
- **`mrtw60a_*` is the `VariableChangePointEquiv` dictionary inlined.** The ported
  `VariableChangePoint.lean` (`vcInvFun*`) is the reuse target; do not re-derive.
- **Binder spellings.** Headline binders come from the wrappers. `norm` strips only
  `ModularCurve.`/`AlgebraicCurve.`.

## 5. Bound and stop conditions

Stop and report: an unported prerequisite outside §2; a statement that does not transcribe
to `v4.34.0`; a shared declaration D-1 claimed differently; any pull toward the S row.

## 6. Build discipline (binding)

> `lake env lean -DmaxHeartbeats=4000000 -DautoImplicit=false <file>`; `lake build <module>`;
> **one** `lake build` per wave, `flock`ed on `.lake/flt_build.lock`, bounded and timed.
> Never raise `maxHeartbeats`. Iterate in bounded blocks.

## 7. Verification

- `lake env lean` clean on both; `lake build` each.
- Append both modules to `PORT_FILES` (last); append the two wrappers and their `S_` files to
  `SOURCES` (last, wrapper first) — unless D-1 already did.
- `python3 spec/check_flt_statements.py` → 0 mismatched / 0 missing; reconcile the delta.
- A `spec/` zone per module (or one shared zone) with a real executed cross-module
  composition; deleting either module must make it fail.
- `#print axioms` clean on both headlines; no `sorry`. Whole-tree `flock`ed `lake build`;
  jobs + seconds. `grep -c` of every drop, in the log.
