# Topic m2 — the geometric base change, the cusps, the `q`-adic place and the modular unit (M3)

**Status: work order written, not started.** Second topic of
[SET-M1](SET-M1.md). Read [SET-M1](SET-M1.md) §2–§3 first.

**Goal.** Six definition modules, with statements verified by name against the
pin's definition files:

- `FLTForHuman/ModularCurve/Defs/GeometricBaseChange.lean` — the tensor-product
  model of base change and `geomAut`.
- `FLTForHuman/ModularCurve/Defs/QAdicPlace.lean` — the `q`-adic valuation ring,
  the place at `q = 0`, the rational-level cusps, and `IsCusp`.
- `FLTForHuman/ModularCurve/Defs/CuspidalClass.lean` — `frickeInvolutionBar`,
  `cuspZeroBar`, the cuspidal divisor and class.
- `FLTForHuman/ModularCurve/Defs/AtkinLehner.lean` — the Fricke automorphisms
  (`IsFrickeAut`/`IsFrickeAutFull`, `frickeInvolution`/`frickeInvolutionFull`),
  `order_coeffEmb_jq`, `cuspInftyBar`.
- `FLTForHuman/ModularCurve/Defs/ModularUnit.lean` — `IsMonicOfOrder`, the
  `Δ`-series and the modular unit `modularUnitSeries`, `eisensteinNumerator`.
- `FLTForHuman/ModularCurve/Defs/JqCoeff.lean` — the `jq`-constants over a
  general field, `jqModC`/`jqNModC`, `modularFunctionFieldC`.

**Why this topic.** These are the objects the analytic cluster (m3 and SET-M2's
Fricke core) is stated about, and the objects `heckeRoof_adjoin_range_union_eq_top`
and the cusp bookkeeping name. The one **one-time shape decision** of the effort
is here: `geomAut`'s base-change model. Take the pin's.

## 1. The pin sources and the write order

| order | pin module | lines | port home |
|---|---|---|---|
| 1 | `Definitions/Def_ModularCurve_JqCoeff.lean` | 83 | `Defs/JqCoeff.lean` |
| 2 | `Definitions/Def_ModularCurve_GeometricBaseChange.lean` | 227 | `Defs/GeometricBaseChange.lean` |
| 3 | `Definitions/Def_ModularCurve_QAdicPlace.lean` | 380 | `Defs/QAdicPlace.lean` |
| 4 | `Definitions/Def_ModularCurve_ModularUnit.lean` | 185 | `Defs/ModularUnit.lean` |
| 5 | `Definitions/Def_ModularCurve_AtkinLehner.lean` | 107 | `Defs/AtkinLehner.lean` |
| 6 | `Definitions/Def_ModularCurve_CuspidalClass.lean` | 55 | `Defs/CuspidalClass.lean` |

Ordering: `JqCoeff` needs only `X0`/`Laurent`; `GeometricBaseChange` needs
`Laurent`; `QAdicPlace` needs `X0` and the AC `Place`; `ModularUnit` needs
`Jq`; `AtkinLehner` needs `QAdicPlace` + `Jq`; `CuspidalClass` needs
`AtkinLehner` + `GeometricBaseChange` + AC's `SemilinearAut` `Place` action.

## 2. What to write, declaration by declaration

### 2.1 `Defs/JqCoeff.lean` (small, write first)

`jqModC` (the `jq` series over a general `K`), `jqNModC` (`= qExpand K N (jqModC K)`),
`@[simp] jqNModC_one`, `jqModC_rat` (`rfl`), `map_jqModC`,
`jqModC_eq_map_intCast`; `modularFunctionFieldC`, `jqModC_mem`, `jqNModC_mem`,
`modularFunctionFieldC_rat`, `modularFunctionFieldC_one`.

**Seam.** The port's `Defs/Jq.lean` has `jq`, `jqN`, `evalAtJ`; the pin's
`jqModC` is the `LaurentSeries K` analogue via `PowerSeries.map`. Check whether
`Defs/JqCoeff.lean`'s declarations should be *restated over the ported*
`jq`/`jqN` where `K = ℚ` (`jqModC_rat` is `rfl`) — the pin already does this.
Keep the names and binders as the pin writes them.

### 2.2 `Defs/GeometricBaseChange.lean`

Port the whole module. The declarations, in order: `linearIndependent_coeffEmb`;
private `algebraMap_mul_eq_smul`; `baseChangeRatAlgHom` (+ `_tmul`);
`baseChangeHom` (+ `_tmul`, `_one_tmul`); private `baseChangeLinear`,
`baseChangeLinear_apply`, `valRatLinear`, `valRatLinear_apply`,
`baseChangeLinear_injective`, `isField_range_baseChangeHom`;
`baseChangeHom_injective`, `baseChangeHom_mem`, `instIsDomainTensorProduct`,
`isField_tensorProduct`, `exists_baseChangeHom_eq`; `baseChangeEquiv` (+
`coe_baseChangeEquiv_apply`, `baseChangeEquiv_one_tmul`,
`baseChangeEquiv_symm_coeffEmb`, `baseChangeEquiv_tmul`); `geomAut` (+
`geomAut_apply`, `geomAut_baseChangeEquiv_tmul`, `geomAut_coeffEmb`,
`coe_geomAut_coeffEmb`).

**Risks / seam.** This is AC0-shaped: a tensor-product model
`L ⊗[ℚ] F₀ ≃ₐ[L] laurentBaseChange L F₀`. mathlib's `TensorProduct`,
`Algebra.TensorProduct`, `IsFractionRing`/`IsField` and `IntermediateField.adjoin`
are the interface. Watch: (a) `IsDomain (L ⊗[ℚ] F₀)` and `IsField` need the
field/tensor instances to fire; (b) `geomAut` is a `→*` into `≃ₐ[L]`, and its
`coe_geomAut_coeffEmb` must be the `rfl`-level bridge `CuspidalClass` needs.
Scout `baseChangeEquiv` in `Scratch.lean` before pricing the rest. If the pin's
`linearIndependent_coeffEmb` is already covered by `Defs/Laurent.lean`'s
`iota_injective`/`coeffMapEquiv`, import instead and record.

### 2.3 `Defs/QAdicPlace.lean`

In order:

- `order_jq` (`jq.order = -1`);
- the `OrderArithBar` block: `order_mul_of_ne_zero_bar`,
  `order_inv_of_ne_zero_bar`, `order_pow_of_ne_zero_bar`,
  `order_zpow_of_ne_zero_bar`, `order_div_of_ne_zero_bar`;
- `qSeriesBar` + the `@[simp]` algebra laws (`zero`, `one`, `mul`, `add`, `neg`,
  `sub`, `inv`, `div`, `pow`), `qSeriesBar_zpow`, `qSeriesBar_eq_zero_iff`,
  `qSeriesBar_ne_zero`, `qSeriesBar_algebraMap`, `order_qSeriesBar_mul`;
- `qIntegersBar` (the `ValuationSubring F`), `mem_qIntegersBar_iff`,
  `isUnit_qIntegersBar_iff`;
- the `Witness` block: `ne_zero_of_order_eq_neg_one`,
  `notMem_qIntegersBar_of_order_eq_neg_one`, `qIntegersBar_ne_top`,
  `order_inv_of_order_eq_neg_one`, `inv_mem_qIntegersBar_of_order_eq_neg_one`,
  `uniformizerBar`, `@[simp] coe_uniformizerBar`, `uniformizerBar_ne_zero`,
  `irreducible_uniformizerBar`, `qIntegersBar_isPrincipalIdealRing`;
- `qInftyPlaceBar` (+ `qInftyPlaceBar_toValuationSubring`);
- the `RationalTwin` block: `qInftyPlaceRat` (+ `_toValuationSubring`),
  `cuspInfty` (+ `_toValuationSubring`), `jq_mem_full`, `cuspInftyFull`
  (+ `_toValuationSubring`);
- `IsCusp`, `isCusp_iff`, `isCusp_qInftyPlaceBar`, `isCusp_qInftyPlaceRat`,
  `isCusp_cuspInfty`, `isCusp_cuspInftyFull`.

**Seam.** `qIntegersBar` is mathlib's `ValuationSubring` built from
`HahnSeries.order`; `irreducible_uniformizerBar` and
`qIntegersBar_isPrincipalIdealRing` are the substantive lemmas. `Place` and its
`isPrincipalIdealRing'` field are AC's (`Defs/Place.lean`). Since
`qInftyPlaceBar` is a `Place L F` from a valuation subring, check AC's
constructor name and the `Place.toValuationSubring` projection before writing.
`jq_mem_full`: the port has `Defs/Fields.lean`'s `jq_mem`/`jqd_mem_full`; use
them, do not re-prove.

### 2.4 `Defs/ModularUnit.lean`

- `IsMonicOfOrder` + its namespace (`ne_zero`, `coeff_self`, `coeff_of_lt`,
  `single`, `ofPowerSeries`, `mul`, `of_mul_right`, `qExpand`);
- `dedekindEtaUnitQ`, `@[simp] constantCoeff_dedekindEtaUnitQ`;
- `deltaSeries`, `isMonicOfOrder_deltaSeries`, `deltaSeries_ne_zero`;
- `deltaSeriesN`, `isMonicOfOrder_deltaSeriesN`, `deltaSeriesN_ne_zero`;
- `modularUnitSeries` (`= deltaSeries * (deltaSeriesN p)⁻¹`),
  `modularUnitSeries_mul_deltaSeriesN`, `isMonicOfOrder_modularUnitSeries`,
  `modularUnitSeries_ne_zero`, `order_modularUnitSeries`,
  `coeff_modularUnitSeries_self`, `coeff_modularUnitSeries_of_lt`,
  `deltaSeriesN_one`, `modularUnitSeries_one`, `deltaSeriesN_mul`,
  `modularUnitSeries_mul`;
- `eisensteinNumerator`, `eisensteinNumerator_dvd`, and the seven `@[simp]`
  decisions.

**Seam.** `dedekindEtaUnit` is in the port's `Defs/Jq.lean`; build
`dedekindEtaUnitQ` by `PowerSeries.map (Int.castRingHom ℚ)`. The `order`
lemmas are `HahnSeries.order` API — check the v4.34 names in `Scratch.lean`.

### 2.5 `Defs/AtkinLehner.lean`

- `IsFrickeAut`, `frickeInvolution` (the `if h : ∃ … then h.choose else refl`),
  `isFrickeAut_frickeInvolution`, `frickeInvolution_eq_refl`, `cuspZero`
  (+ `cuspZero_def`);
- `IsFrickeAutFull`, `frickeInvolutionFull`, `isFrickeAutFull_frickeInvolutionFull`,
  `frickeInvolutionFull_eq_refl`, `cuspZeroFull` (+ `cuspZeroFull_def`);
- `order_coeffEmb_jq`;
- `cuspInftyBar`, `cuspInftyBar_toValuationSubring`.

`cuspZero`/`cuspZeroFull` are rational/`Full`-level API the cone does not use
(the cone uses `cuspZeroBar`, which is `CuspidalClass`'s). Port them anyway if
they are short; otherwise defer with a count. `cuspInftyBar` uses
`qInftyPlaceBar` (m2.3) and `order_coeffEmb_jq`.

### 2.6 `Defs/CuspidalClass.lean`

`frickeInvolutionBar` (`geomAut (AlgebraicClosure ℚ) (modularFunctionFieldFull N)
(frickeInvolutionFull N)`), `frickeInvolutionBar_def`, `cuspZeroBar`,
`cuspZeroBar_def`, `cuspidalDivisor`, `cuspidalDivisor_def`,
`degree_cuspidalDivisor`, `cuspidalDivisor₀`, `@[simp] coe_cuspidalDivisor₀`,
`cuspidalClass`, `cuspidalClass_def`.

**Seam.** `degree_cuspidalDivisor` uses `Divisor.degree_single`,
`Place.deg_smul` and `cuspZeroBar_def`; `Place.deg_smul` is AC's
`Defs/SemilinearAut.lean`. `frickeInvolutionBar • cuspInftyBar` needs the AC
`SMul (F ≃ₐ[K] F) (Place K F)` instance — confirm it synthesizes for
`AlgebraicClosure ℚ`. `cuspidalDivisor₀` uses `Divisor.mem_degZero`. If a needed
AC lemma is missing, report it rather than reproving.

## 3. Verification

- Append the six pin definition files to the checker's `SOURCES` and the six port
  modules to `PORT_FILES`.
- Run `python3 spec/check_flt_statements.py`: 0 mismatched, 0 missing, identical
  count ≥ 802.
- `#print axioms` on `geomAut`, `qInftyPlaceBar`,
  `qIntegersBar_isPrincipalIdealRing`, `modularUnitSeries`,
  `frickeInvolutionFull`, `frickeInvolutionBar`, `degree_cuspidalDivisor`.
- Consumer Zone A extension: `#check` `modularUnitSeries`, `qInftyPlaceBar`,
  `cuspInftyBar`, `cuspZeroBar`, `jqNModC`, `frickeInvolutionFull` at their pin
  signatures; one concrete `qInftyPlaceBar` at `N = 1`; assert `jqNModC ℚ = jqN`
  if the pin states it.

## 4. Budget

**3 goal rounds, checkpoint at 1 and 2.** Round 1: `JqCoeff` +
`GeometricBaseChange` + the `geomAut` scout. Round 2: `QAdicPlace` (the likely
stall: `irreducible_uniformizerBar` / `qIntegersBar_isPrincipalIdealRing`) +
`ModularUnit`. Round 3: `AtkinLehner` + `CuspidalClass` + log/README/consumer.

**Stop early on**: a `geomAut`/`baseChangeEquiv` model that will not fire (report
the instance goal, do not weaken the statement); `qIntegersBar_isPrincipalIdealRing`
needing a mathlib route the pin's proof does not have; or `ModularUnit`'s `order`
lemmas needing a v4.34 API migration larger than the module.

## 5. Reporting back

1. Module/line/decl table and checker before/after.
2. **The `geomAut` shape decision**: the tensor model's exact statement and
   whether `baseChangeEquiv` closed first try; the instance goals that fired.
3. `qIntegersBar_isPrincipalIdealRing` and `irreducible_uniformizerBar`: the
   route and where it bit.
4. The per-declaration port/defer decision for the out-of-cone API
   (`cuspZero`(Full), `cuspidalClass`, `eisensteinNumerator`, the `map_jqModC`
   family), each with a `grep -c`.
5. Anything m3 or SET-M2's Fricke core must import from here, and any promotion
   that should move a helper into `Defs/Laurent.lean`/`Defs/Jq.lean`.
