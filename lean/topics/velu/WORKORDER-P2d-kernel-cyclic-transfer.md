# P-2d work order — the conjugation seam (D-4)

**Status: landed, 2026-10-06.** Set D-4 of [WORKORDER-P2-basechange.md](WORKORDER-P2-basechange.md).
New-file-only. Pin `anthropics/fermats-last-theorem@aa2d8b3`; port mathlib `v4.34.0`. Depends
on D-1 (`BaseChange.lean`), D-2 and D-3, all landed. Method:
[../../porting-playbook.md](../../porting-playbook.md) §2.4, §3.1–§3.2, §3.5, §4.

> **Close-out (D-4).** `FLTForHuman/WeierstrassCurve/Isogeny/KernelCyclicTransfer.lean`, new,
> **472 lines written (`wc -l`; 407 non-blank, 328 code), 19 public declarations, no `private` helpers**. The
> headline at the wrapper statement, `ModularCurve.KwD5BetweenCurvesPMOPConjKerEquiv`, the
> `kw_fdn2_qephod_hend21_*` block, the `kw_surgehgf4_pck_*` engine and `pck_s17` — all pin
> **transcriptions** (the `kw_` prefix is a solution-file token, not a promotion), so the
> checker counts 19 `identical` and the `renamed` count is unchanged. Measured pre-D-4:
> 50 of the file's 116 declarations (632 pin lines) already had an identical-statement port
> copy and are imported; D-4's own slice is 19 declarations / 382 pin lines. Two pin
> declarations are **deliberately not declared**: `KwD5BetweenCurvesHoloLift` (all five
> pin copies are byte-identical, `sha256 e7b7d5fe…`; its body needs the unported
> `PeriodPair.kw_toPointHom`, and declaring it here would collide with D-5's copy) and the
> `Nat.card` form of `kw_fdn2_qephod_hend7_pmopKerCard_proved` (the name is owned by the
> `Prop`-valued `Isogeny/NatCard.lean:785`; the statement is the imported
> `natCard_ker_pointMapOfPushforward_eq_finrankAlong`). Both are registered in
> [../../CARRY-FORWARD.md](../../CARRY-FORWARD.md). Checker `5980 (313 promoted, 61 renamed)
> → 5999 (313, 61)`, `0 mismatched / 0 missing`, `6016 → 6035` checked; one-token mutation
> probe `5998 / 1 / 0`. Consumer `spec/KernelCyclicTransferConsumer.lean` exit 0, four zones;
> deletion probe fails it. Whole tree **9315 jobs, green, cached 11.0 s**. `#print axioms` on
> the headline `[propext, Classical.choice, Quot.sound]`. Full record:
> [../../logs/velu-port.md](../../logs/velu-port.md) §P-2.

> **Re-measured 2026-10-06, after D-1/D-2/D-3 landed.** `port_plan` on the `conj` node now
> reports: raw 1,821 lines / 117 declarations, once-cost 1,765, **already in the port 804,
> net-new 961**, 115 distinct declaration groups, 62 trusted substitutions. D-1 landed the
> point-pullback/tensor prelude (at its **stripped** names) and `Engine.lean` supplies
> `pointEnd'_eq_of_seam` (264) and the `restrictAlong`/`pushforwardAlong` seam lemmas. So
> this set is **≈960 new lines**: the `conj` headline, its `KwD5BetweenCurvesPMOPConjKerEquiv`
> seam, and the `kw_surgehgf4_pck_*` block. `KwD5BetweenCurvesHoloLift` is **11 lines and
> byte-identical in all five pin files** (the 748/151/83/25 numbers were `p2m_*` span
> artefacts), and it is undeclarable here: its body needs `PeriodPair.kw_toPointHom`, absent
> from the port, and the name belongs to D-5's module. D-4 therefore does not declare it;
> D-5 ports it, with the `kw_toPointHom` promotion set first (D-5 §1.5).

## 1. Scope

Port the **seam** and the conjugation headline:

```
WeierstrassCurve.Affine.isAddCyclic_ker_pointMapOfPushforward_of_algEquiv_conj   (1,821)
```

plus the `KwD5BetweenCurves*` seam vocabulary that D-5 (and, later, the S row's
`exists_differentiable_toPoint_comp_eq_pointMapOfPushforward_toPoint` and
`exists_scale_lattice_…_isAddCyclic_sublatticeQuotient`) import. The seam is block D of P-2 —
**1,719 once-lines across five pin files**, so it gets one home here.

**Not this set:** the two `…of_baseChange_algHom` / `…exists_algHom_baseChange_…` headlines
(D-5); the tensor/point-pullback prelude (D-1); the `kw_i*` (D-2) and `mrtw60a*` (D-3)
blocks; the S row.

## 2. Source (pin)

- `P2M/Sol/S_WeierstrassCurve_Affine_isAddCyclic_ker_pointMapOfPushforward_of_algEquiv_conj.lean` (1,821)
  — the headline. Wrapper `Theorems/Thm_WeierstrassCurve_Affine_isAddCyclic_ker_pointMapOfPushforward_of_algEquiv_conj.lean`
  is the statement authority.
- the `KwD5BetweenCurves*` declarations as they first appear, in
  `P2M/Sol/S_WeierstrassCurve_Affine_isAddCyclic_ker_pointMapOfPushforward_of_baseChange_algHom.lean`
  (`KwD5BetweenCurvesHoloLift` — 11 lines, not the 748 a `port_advise` span reports;
  `pointEnd'_eq_of_seam`, `KwD5BetweenCurvesFFSeamBaseChange`,
  `KwD5BetweenCurvesKerTransportAlongEmbed`, `KwD5BetweenCurvesPMOPConjKerEquiv`, …), and in
  `…isAddCyclic_…_of_algEquiv_conj.lean` (`KwD5BetweenCurvesPMOPConjKerEquiv` and the
  `kw_fdn2_qephod_hend21_conjSeam` block). **A same-name declaration in two pin files is not
  evidence of a different statement**: `KwD5BetweenCurvesHoloLift`'s five copies are
  byte-identical (`sha256`), and `port_advise`'s span measures the `p2m_*` scaffolding between
  declarations. Diff normalised bodies before treating a pair as a generalisation.

The `conj` file's declarations (21 node-unique, 565 lines): `pushforwardAlong_pushforwardAlong{,',}`
(66+72), `finiteAlong_comp` (58), `inertiaDegAlong_comp` (34), `restrictAlong_restrictAlong` (8),
`restrictAlong_*` helpers, and the `kw_surgehgf4_pck_*` block (`kw_fdn2_qephod_hend21_conjSeam{,_,_finiteAlong,_isIntegral}`,
`kw_fdn2_qephod_hend21_finrankAlong_conj` 43, `kw_surgehgf4_pck_{proved_core,pmop_conjSeam_factor,pmop_comp_apply,pmop_equiv_bijective,pmop_equiv_left_inv,pmop_equiv_right_inv,pmop_id,proved,algEquiv_finiteAlong,algEquiv_isIntegral,pmop_congr}`,
`pck_s17`). Run `port_advise.py --nodes WeierstrassCurve.Affine.isAddCyclic_ker_pointMapOfPushforward_of_algEquiv_conj`
first and import the hits (`AlgebraicCurve.Place.*`, `IsogenyEndDatum.*`, `pushforwardAlong*`
in `IsogenyEndDatum/Engine.lean`).

## 3. Deliverable

**`FLTForHuman/WeierstrassCurve/Isogeny/KernelCyclicTransfer.lean`** (new). The seam
vocabulary public at the pin names/namespaces (the S row and D-5 import it); the headline at
the wrapper statement; helpers `private` with content names (**no `kw_` prefix**). Imports
D-1 plus the ported `Place/Dictionary.lean`, `IsogenyEndDatum/Engine.lean`,
`Elliptic/PeriodPair/` material and mathlib specifics.

## 4. Route, with recorded negatives

- **Import rule.** `IsogenyEndDatum/Engine.lean` (the seam's `pointEnd'_eq_of_seam`,
  `restrictAlong_eq_infinitePlace`, `normFormulaAlong_of_elliptic`) is importable here
  because D-1 imports `GenusOnePlaceGate.lean`, not the producer. Do **not** import
  `WeierstrassCurve/GenusOnePlaceGateCentred.lean` or `WeierstrassCurve/Place/RRSpace.lean`
  — `RRSpace`'s `scoped instance instInfinitePlace` collides at the name level with
  `Engine`'s. See P-2 §3.1.
- **Naming (P-2 §3.2).** D-1's shared prelude is at its **stripped** names; import those
  (`functionField_algHom_ext`, `coordinateRingBasis`, `pointPullback*`, the tensor block,
  …). A helper local to your module is `private` with a content name (no `kw_`). A public
  helper you introduce is a promotion: name it at the prefix-stripped pin name. The
  `kw_surgehgf4_pck_*` names are **pin-public** as written, so they are transcriptions —
  keep them verbatim unless you decide a specific one is a promotion, in which case strip
  it and say so. Never leave a declaration public and stripped.
- **The seam is `Prop`-valued.** `KwD5BetweenCurvesHoloLift` and friends are
  `def … : Prop`; the checker compares only `Prop`, so port the bodies faithfully and never
  drop one on a substitution hit.
- **The headline is about conjugation invariance.** Given `eE : D.FunctionField ≃ₐ E.FunctionField`
  and `ι''` conjugated to `ι`, cyclicity and the kernel cardinal transfer. Follow the pin.
- **Do not port `KwD5BetweenCurves*` twice.** The S row's copies are 151/83 lines and are
  *not* this set's; if they turn out to be different Props, record the pair in the log and
  in `CARRY-FORWARD.md` so the S set can decide.

## 5. Bound and stop conditions

Stop and report: the seam names with genuinely different bodies in two files; an unported
prerequisite outside §2; a statement that does not transcribe to `v4.34.0`; any pull toward
the S headlines.

## 6. Build discipline (binding)

> `lake env lean -DmaxHeartbeats=4000000 -DautoImplicit=false <file>`; `lake build <module>`;
> **one** `lake build` per wave, `flock`ed on `.lake/flt_build.lock`, bounded and timed.
> Never raise `maxHeartbeats`. Iterate in bounded blocks.

## 7. Verification

- `lake env lean` clean; `lake build FLTForHuman.WeierstrassCurve.Isogeny.KernelCyclicTransfer`.
- Append the module to `PORT_FILES` (last); append the `conj` wrapper and `S_` file to
  `SOURCES` (last) — unless D-1 already did.
- `python3 spec/check_flt_statements.py` → 0 mismatched / 0 missing; reconcile the delta.
- A `spec/` zone exercising the headline and the seam at concrete complex curves, or a
  hypothesis-form test; deleting the module must make it fail.
- `#print axioms` clean; no `sorry`. Whole-tree `flock`ed `lake build`; jobs + seconds.
