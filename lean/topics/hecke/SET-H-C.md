# SET-H-C (dispatched half) — the seven inputs `ModularCurve.heckeInputsHAlong`

Work order for the dispatched half of SET-H-C of
[TOPIC-xH-hecke-diamond-inputs.md](TOPIC-xH-hecke-diamond-inputs.md) §5. Pin
`aa2d8b3`, port mathlib `v4.34.0`. SET-H-A and SET-H-B are landed
([logs/xh-hecke-set-a.md](../../logs/xh-hecke-set-a.md),
[logs/xh-hecke-set-b.md](../../logs/xh-hecke-set-b.md)). **The capstone
`XH/Inputs.lean` and `ModularCurve.HeckeDiamondInputsHAll` are manager-reserved and
are NOT part of this order.**

## 1. Subject

Port `P2M/Sol/S_ModularCurve_heckeInputsHAlong.lean` (326 raw / 297 declaration
lines, 33 declarations) and its wrapper
`Theorems/Thm_ModularCurve_heckeInputsHAlong.lean` into
`FLTForHuman/ModularCurve/XH/HeckeInputs.lean`.

Target statement (verbatim from the wrapper):

```lean
theorem ModularCurve.heckeInputsHAlong (L : Type*) [Field L] [Algebra ℚ L]
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (ℓ : ℕ) [NeZero ℓ] :
    ModularCurve.HeckeInputsHAlong L M H ℓ
```

`port_plan.py` measures 326 raw → 297 once-cost → 0 already in the port → **297 net
new lines**, one block, one layer.

## 2. Module layout

`FLTForHuman/ModularCurve/XH/HeckeInputs.lean`, mirroring the pin's namespaces:

```
namespace ModularCurve
namespace HeckeInputsHAll
  section Group       -- conjMat, det_conjMat, conjSL, conjSL_apply_00/01/10/11,
                      -- dvd_of_mem_Gamma0_mul, conjSL_mem_Gamma0, conjSL_mem_GammaH,
                      -- heckeDiag_mul_mul_inv, inf_le_conj, T_mem_inf, one_mem_strictPeriods
  section LevelRaise  -- levelRaise, levelRaise_apply, coe_levelRaise,
                      -- coeff_qExpansion_levelRaise, heckeBetaHDefined
  section Along       -- transcendental_map, finiteAlong_of_finiteDimensional_adjoin,
                      -- isIntegral_of_finiteAlong, hasPrincipalDivisors_of_exists,
                      -- finiteAlong_of_exists
  section Hecke       -- the two scoped instances, hasPrincipalDivisors_top,
                      -- finiteAlong_of_hom, charZero_bot, heckeInputsHAlong
end HeckeInputsHAll
theorem heckeInputsHAlong ...   -- the public headline, verbatim from the wrapper
end ModularCurve
```

**All 33 declarations are transcribed at their pin names and are public**, as the pin
writes them. This is deliberate: the checker verifies the port's public surface, and
this set's 297 lines are exactly the mathematics the set exists to land. (Contrast
`X1/Inputs.lean`, whose prelude is private because the pin's X₁ analogue is an inner
block of a capstone file; here the pin's file is a public `S_` file.) If a declaration
cannot be given the pin's exact statement, **stop and report** rather than spell it
differently — a `MISMATCH` is the signal that the transcription is wrong.

Wiring: append `P2M/Sol/S_ModularCurve_heckeInputsHAlong.lean` and
`Theorems/Thm_ModularCurve_heckeInputsHAlong.lean` to `SOURCES` beside the other
`S_ModularCurve_*` entries, and the module to `PORT_FILES` last. The wrapper is
**needed**: the `S_` file's own copy is the inner `HeckeInputsHAll.heckeInputsHAlong`
(section-variable binders), while the port's headline spells the wrapper's explicit
binders.

## 3. Route and reuse map

The pin's file is self-contained over the ported vocabulary. Reuse, do not restate:

| pin declaration(s) | ported home |
|---|---|
| `expandInt`, `coeff_expandInt`, `intSeriesC_expandInt` | `ModularCurve.expandPS`, `coeff_expandPS`, `intSeriesC_expandPS` (`X1/QExpandStretch.lean`, public); the pin's `expandInt` is byte-identical to `expandPS` — measured by `port_advise`, which flags it as the set's one substitution |
| `restrictForm` | `ModularCurve.restrictForm` (`JqIntegralRatios.lean:43`) |
| `ModularForm.heckeDiagMatrix`, `ModularForm.translate`, `ModularForm.slash_heckeDiagMatrix_apply` | `ModularForms/Defs/HeckeOperator.lean` |
| `ModularFormClass.qCoeff_comp_heckeDiagMatrix_smul` | `ModularForms/HeckeQCoeff.lean` |
| `exists_transcendental_finiteDimensional_laurentBaseChange` | `ModularCurve.JOneES.*` (`X1/FunctionField.lean`) |
| `hasPrincipalDivisors_of_transcendental`, `finiteDimensional_adjoin_of_transcendental` | `AlgebraicCurve/PrincipalDivisors/Transcendence.lean`, `IsCurveOver/PerfectField.lean` |
| `fundamentalIdentityAlong`, `normFormulaAlong`, `separableAlong_of_charZero` | `AlgebraicCurve/WeilExchange/Transport.lean` |
| `HeckeInputsHAlong`, `heckeInputsHAlong_intro`, `heckeAlphaHBar`/`heckeBetaHBar`, `HeckeBetaHDefined` | `XH/HeckeOperator.lean`, `XH/FunctionField.lean` (SET-H-A) |
| `CohCarrier.GammaH`, `translation_mem_GammaH`, `Gamma1_le_GammaH`, `Gamma1_in_Gamma0`, `Gamma1_le_of_dvd`, `conj_mem_GammaH`, `mem_GammaH_iff` | `ModularForms/Defs/GammaH.lean` |
| `intSeriesC`, `intFormRatiosC`, `mem_intFormRatiosC`, `div_mem_qExpFunctionFieldC` | `ModularCurve/JqIntegralRatios.lean` |
| `qExpand`, `qExpandₐ`, `qExpand_coeff_mul`, `qExpand_injective`, `coeffMap`, `coeffEmb`, `laurentBaseChange`, `laurentBaseChange_mono`, `qExpand_mem_laurentBaseChange` | `ModularCurve/Defs/Laurent.lean` |

The `Hecke` section's two `scoped instance`s (`gammaH_finiteIndex`,
`gammaH_inf_finiteIndex`) stay `scoped` exactly as the pin writes them.

## 4. Recorded negatives (do not repeat the searches)

* `HeckeInputsHAlong` is **not** `ModularCurve.HeckeInputsAlong`
  (`Defs/HeckeTotal.lean`): the ported predicate is on
  `modularFunctionFieldFull`/`heckeAlphaBar`, this one on
  `xHTopFunctionFieldC`/`heckeAlphaHBar`. SET-H-A's `XH/HeckeOperator.lean` has the
  right one. Do not substitute.
* Four target names are **already in the port with a different statement**
  (`port_advise` §3): `isIntegral_of_finiteAlong` and `hasPrincipalDivisors_top`
  (`X1/Inputs.lean`, both `private`), `conjSL` (`Analytic/Gamma0Cosets.lean`,
  different binders), `one_mem_strictPeriods` (28 files). The checker's `find`
  disambiguates by statement, so writing the pin's own copy at the pin's name is
  correct; do **not** try to reuse or promote those.
* `xHFunctionFieldC`/`xHTopFunctionFieldC`/`xHFunctionField` are `def`/`abbrev` in
  `XH/FunctionField.lean`; the pin's `FB`/`FT` are that module's `xHFunctionFieldC`/
  `xHTopFunctionFieldC` — this file does not use them.

## 5. Build discipline

* Edit loop: `lake env lean -DmaxHeartbeats=4000000 -DautoImplicit=false <file>`
  (from `lean/`).
* `flock .lake/flt_build.lock timeout 600 lake build FLTForHuman.ModularCurve.XH.HeckeInputs`
  when the file is done; **one** `flock .lake/flt_build.lock timeout 900 lake build`
  for the whole tree at the end. Never a bare whole-tree build inside the work;
  never raise `maxHeartbeats`.
* Time builds with wall **and** user/sys.

## 6. Verification

1. Checker: `python3 spec/check_flt_statements.py`; target `0 mismatched /
   0 missing`. Baseline before this set is `6486 identical (312 promoted,
   83 renamed), 0 mismatched, 0 missing, 36 own (6522 checked)`; the delta is the
   33 declarations (+1, since the pin's `HeckeInputsHAll.heckeInputsHAlong` and the
   wrapper share a last name — reconcile it exactly). One-token mutation check
   (expect exactly one more `mismatched`) and revert.
2. `--prop-bodies` (advisory): the set has no `def … : Prop`; the count should not
   move.
3. `#print axioms ModularCurve.heckeInputsHAlong` → `[propext, Classical.choice,
   Quot.sound]`; no `sorry`.
4. Whole-tree `lake build` green; the two existing consumers
   (`spec/XHConsumer.lean`, `spec/ModularCurveHeckeConsumer.lean`) stay at
   `0` errors / `0` warnings. **Do not** add a consumer zone: the capstone's wire
   test is the manager's and consumes this headline.

## 7. Out of scope

`XH/Inputs.lean` and `ModularCurve.HeckeDiamondInputsHAll` (manager-reserved); any
edit to `XH/FunctionField.lean`, `XH/HeckeOperator.lean`, `XH/Operators.lean`,
`XH/DiamondLift*.lean`, `X1/Inputs.lean`, or `X1/QExpandStretch.lean`; the
`JH`/`genOpH`/`diamondHBar` layer.
