# Mathlib-first substitution audit — P3.3b, the Tate chain rule (`tateChainRule`)

**Method:** [`lean/porting-playbook.md`](../porting-playbook.md) §2.2 (audit the route,
mathlib first), after the phase-1/2/3.1/3.2a–3.2f and 3.3a templates
[`AUDIT-mathlib.md`](AUDIT-mathlib.md), [`AUDIT-mathlib-p2.md`](AUDIT-mathlib-p2.md),
[`AUDIT-mathlib-p3-1.md`](AUDIT-mathlib-p3-1.md),
[`AUDIT-mathlib-p3-2a.md`](AUDIT-mathlib-p3-2a.md) … `-p3-2f.md`, and
[`AUDIT-mathlib-p3-3a.md`](AUDIT-mathlib-p3-3a.md). Pin:
`anthropics/fermats-last-theorem@aa2d8b3` (read-only clone at `~/proj/fermats-last-theorem`);
port mathlib `v4.34.0` (`lean/.lake/packages/mathlib`). Work order:
[`PLAN-P3-3.md`](PLAN-P3-3.md) §1–§2. Pre-port measurement:
[`tools/deps/build/p33b_advise.{log,json}`](../../../tools/deps/build/p33b_advise.log)
(the set-3.3b target run).

**Sources.** One `S_` file and its one-declaration `Theorems/` wrapper:

- [`P2M/Sol/S_AlgebraicCurve_tateChainRule.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_tateChainRule.lean)
  (2,832 ln, 108 declarations, of which 101 public and 7 pin-`private`),
- [`Theorems/Thm_AlgebraicCurve_tateChainRule.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_AlgebraicCurve_tateChainRule.lean)
  (25 ln, the public interface copy `AlgebraicCurve.tateChainRule`).

The new home is `FLTForHuman/AlgebraicCurve/Tate/ChainRule.lean`, importing
`Defs/TateResidueCurrency.lean` (the shared row-3.3 API, PLAN-P3-3 §2) and
`Tate/CommFinite.lean` (set 3.3a's finiteness theory, which supplies most of the
pin's shared prelude).

**Baseline.** 3779 identical / 0 mismatched / 0 missing / 30 own-proof (3809 checked),
i.e. the port after set 3.3a. This audit is measured against that baseline: every
"already in the port" claim is a *public* declaration in a module already listed in
`PORT_FILES` (or a pin-`private` original reached through the checker's dotted
fallback).

**Class convention** (unchanged from phases 1–3.3a). SUBSTITUTE = the port can import
an already-landed declaration instead of proving the row, or a pin `def`/`abbrev`
whose body is `rfl`-equal to a port/mathlib term. GENERALISE/ADAPT = the port already
declares the row under the same last name at a different binder spelling, so the
worker imports it and must **not** re-declare it. KEEP/NEW splits into
PROOF-INGREDIENT (bespoke statement over pin vocabulary, proof a short assembly of
named mathlib/port lemmas) and BESPOKE (a new `def`/`Prop`/instance introducing
vocabulary).

**Scratch evidence.** A scratch file (`lean/ScratchAuditP33b.lean`, gitignored,
deleted after use) was compiled from `lean/` with

```bash
timeout 300 lake env lean -DmaxHeartbeats=4000000 -DautoImplicit=false ScratchAuditP33b.lean
```

**final run clean, exit 0** (no errors, no warnings). The probe ledger:

- **M** — the mathlib `#check` ledger, all present in `v4.34.0`:
  `KaehlerDifferential.map_D`, `Derivation.liftKaehlerDifferential_comp_D`,
  `Derivation.mk'`, `LinearMap.trace_comp_comm'`, `LinearMap.trace_comp_comm`,
  `LinearMap.trace`, `Submodule.finiteDimensional_of_le`,
  `Submodule.finiteDimensional_sup`, `Submodule.quotEquivOfEq`,
  `Submodule.Quotient.restrictScalarsEquiv`, `Submodule.quotientQuotientEquivQuotient`,
  `Submodule.equivMapOfInjective`, `LinearMap.quotKerEquivRange`, `Submodule.map_mono`,
  `LinearMap.range_comp`, `LinearMap.range_comp_le_range`, `Submodule.range_subtype`,
  `Submodule.ker_mkQ`, `Submodule.liftQ`, `LinearMap.codRestrict`,
  `IsDiscreteValuationRing.exists_irreducible`, `Ideal.mem_span_singleton`,
  `Submodule.mem_sup_left`, `Submodule.mem_sup_right`, `LinearMap.mulLeft`,
  `LinearMap.mem_range`, `Module.Finite.of_submodule_quotient`, `LinearMap.smul_apply`,
  `Submodule.coe_smul`, `map_add`, `map_smul`, `map_sub`, `IsScalarTower.algebraMap_apply`,
  `Algebra.algebraMap_eq_smul_one`, `Algebra.smul_def`, `smul_mul_assoc`,
  `mul_smul_comm`, `Submodule.mem_comap`, `LinearMap.mem_ker`, `Submodule.coe_sub`.
- **A** — the port rows the new declarations build on, all `#check`ed from the set-3.3a
  homes: `ModularCurve.KwF4gRRTate.{tateProj, tateProj_of_mem, tateProj_mem_integers,
  range_tateProj, tateComm, tateCommRestrict, tateCommTrace, tateRes, lmulK,
  finrankTrace, adicIntegersKSubmod, poleWindowKSubmod, kwF4gRRTate_clearPole,
  KwF4gRRTatePoleWindowFinite, kwF4gRRTate_poleWindowFinite_of_DVRQuotPowKFinite,
  kwF4gRRTate_DVRQuotPowKFinite_of_cotangent, kwF4gRRTate_DVRCotangentKFinite,
  KwF4gRRTateCommFinite, KwF4gRRTateChainRule}` and
  `AlgebraicCurve.{kaehlerPullback, Place.differentialCoeff_smul_dCoord,
  Place.differentialCoeff, Place.dCoord, Place.DCoordGenerates, Place.uniformizer,
  Place.adicCompletion, Place.adicCompletionIntegers}`.
- **N** (recorded negatives) — `Submodule.finiteDimensional_iff` and
  `LinearMap.liftQ` report `unknown constant`; the v4.34 names are
  `Submodule.finiteDimensional_sup`/`Submodule.finiteDimensional_of_le` and
  `Submodule.liftQ`.
- **E** — compile-checked prototypes: the pin's `kaehlerPullback_D` body
  `KaehlerDifferential.map_D K K E F e` at the pin's binders (the port's
  `kaehlerPullback` `def` unfolds under elaboration); `w.differentialCoeff ω • w.dCoord
  = ω` from `Place.differentialCoeff_smul_dCoord`; and the `range_comp_le_range`
  orientation used by the two `scoped instance`s `instFinDimRangeComp{Left,Right}`.

## 1. Summary — class counts

| set | rows | SUBSTITUTE | GENERALISE/ADAPT | KEEP/NEW | NEW: proof-ingredient | NEW: bespoke |
|---|---:|---:|---:|---:|---:|---:|
| `S_…tateChainRule.lean` | 101 | 40 | 2 | 59 | 50 | 9 |
| `Thm_…tateChainRule.lean` | 1 | 0 | 0 | 1 | 1 | 0 |
| **total** | **102** | **40** | **2** | **60** | **51** | **9** |

Plus **10 checker-invisible `scoped instance`s** in the `S_` tail (Correction 3):
`instFinDimRangeSub` (pin 1850), `instFinDimRangeNeg` (1975), `instFinDimRangeZero`
(1983), `instFinDimRangeAdd` (2002), `instFinDimRangeCompRight` (2176),
`instFinDimRangeCompLeft` (2181), and the four `DualDom` instances (2559/2572/2595/2602).
These must be landed by hand for the file to elaborate.

**Headline.** The pin's 2,832 lines are *the entire set-3.3a prelude plus the chain-rule
tail*: 40 rows are already public in the port (import, do not re-prove), 2 more are
the port's `Defs/PushPull.lean` rows under the pin's explicit-binder spelling, and
only 60 rows are genuinely new. Those 60 are the trace algebra of an endomorphism
(`finrankTrace` additivity, cyclicity, the commutator-vanishing identity), the abstract
Leibniz defect (`piRestrict`/`epsRestrict`/`tateCommRestrict_eq_bracket` and the long
`tateCommTrace_leibniz_snd` assembly), the `E`-linear derivation `tateResSndDer` into
the dual `DualDom`, and the final `kwTateRR2_derivationFactorSnd → … → tateChainRule`
glue. No new field theory, completions or quotients: every new row is an assembly of
named mathlib/port lemmas.

## 2. Corrections to the work order and the measurement

**Correction 1 — the four `def … : Prop` "substitutions" are false positives.**
`p33b_advise` reports 47 substitutions, including `KwF4gRRTatePoleWindowFinite`,
`KwF4gRRTatePoleWindowImageFinite`, `KwF4gRRTateDVRQuotPowKFinite`,
`KwF4gRRTateDVRCotangentKFinite`, `epsRestrict` (against
`EisensteinWeightOne.E1Chi3IsModular` or `tateCommRestrict`). The checker's
`raw_declarations` drops a `def`'s body *and* its section-variable binders, so every
`def … : Prop` normalises to ` : Prop` and cross-matches. Verified by last name
(playbook §6, the P3.2f lesson):

| pin ln | pin `def` | bogus `port_name` | really |
|---:|---|---|---|
| 923 | `KwF4gRRTatePoleWindowFinite` | `EisensteinWeightOne.E1Chi3IsModular` | SUBSTITUTE — really in `Tate/CommFinite.lean:319` |
| 1232 | `KwF4gRRTateDVRQuotPowKFinite` | `EisensteinWeightOne.E1Chi3IsModular` | SUBSTITUTE — `Tate/CommFinite.lean:649` |
| 1461 | `KwF4gRRTateDVRCotangentKFinite` | `EisensteinWeightOne.E1Chi3IsModular` | SUBSTITUTE — `Tate/CommFinite.lean:696` |
| 1688 | `KwF4gRRTatePoleWindowImageFinite` | `EisensteinWeightOne.E1Chi3IsModular` | **NEW** (pin tail, §5) |
| 2204 | `epsRestrict` | `ModularCurve.KwF4gRRTate.tateCommRestrict` | **NEW** (pin tail, §5) |

So the true counts are 40 SUBSTITUTE / 2 GENERALISE / 60 NEW, not 47 / 6 / 55.

**Correction 2 — the set has no unmeasured dependency.** Unlike set 3.3a, the
chain-rule tail never reaches the unported
`Def_DedekindDomain_AdicValuation_InlineSpecific.lean` slice: it uses only the
already-public `CommFinite` rows (`kwF4gRRTate_clearPole`,
`kwF4gRRTate_poleWindowFinite_of_DVRQuotPowKFinite`,
`kwF4gRRTate_DVRQuotPowKFinite_of_cotangent`, `kwF4gRRTate_DVRCotangentKFinite`) and
never names `completionIdeal`, `exists_uniformizer`, `maximalIdeal_eq_span_uniformizer`
or `mem_completionIdeal_pow`. **No pin-private prelude has to be re-landed in
`Tate/ChainRule.lean`; promotion debt is empty.** (`kaehlerPullback_D` at pin 692 is
the one row of the "CorrectedCarrier" block that is genuinely new — the pin states it
in the definitions file's neighbourhood but the port's `Defs/TateResidueCurrency.lean`
does not carry it.)

**Correction 3 — the ten `scoped instance`s are invisible to both tools.** The
checker's `DECL_RE` (`spec/check_flt_statements.py:2395`) only accepts the modifiers
`private`/`noncomputable`, so `scoped instance` is never read; `port_advise` likewise
reports 108 declarations with none of the tail instances. They still must elaborate:
the six trace-range instances and the four `DualDom` instances. Land them explicitly.
This is the same omission pattern as `AUDIT-mathlib-p3-3a.md` Correction 3 and
`AUDIT-mathlib-p3-2f.md` Correction 4.

**Correction 4 — the pin's `maxHeartbeats` raises are not transcribed.** The pin sets
`maxHeartbeats 12800000`/`synthInstance.maxHeartbeats 6400000` on the tail sections
and a local `25600000` before `finiteDimensional_restrictScalarsQuot_pow`. The last is
in set 3.3a (substituted); the tail raises exceed the project cap 4,000,000 and are
dropped. The two heavy steps are `tateCommTrace_leibniz_snd` (pin 2240) and
`tateResSndDer` (pin 2724); both are re-checked at 4,000,000 and no declaration was
raised.

## 3. SUBSTITUTE rows (40) — import, do not re-declare

Pin line numbers are into `S_AlgebraicCurve_tateChainRule.lean`. "pin-private" rows
are invisible to the checker but the port's *public* row with the same name is what
the checker matches (the pin's statement text is the source). Homes are relative to
`lean/FLTForHuman/AlgebraicCurve/`.

| pin ln | name | port home | note |
|---:|---|---|---|
| 122 | `IsLocalRing.maximalIdeal_le` | `Tate/CommFinite.lean:46` | exact |
| 362 | `isUnit_mk_comap_iff` | `P1/EnginePrelude.lean:153` | exact |
| 409 | `isPrincipalIdealRing_comap` | `P1/EnginePrelude.lean:180` | exact |
| 480 | `ValuationSubring.valued_eq_one_of_isUnit` | `Tate/CommFinite.lean:55` | exact |
| 491 | `ValuationSubring.isUnit_of_valued_eq_one` | `Tate/CommFinite.lean:61` | exact |
| 502 | `ValuationSubring.isUnit_iff_valued_eq_one` | `Tate/CommFinite.lean:67` | exact |
| 782 | `mem_adicIntegersKSubmod_iff` | `Tate/CommFinite.lean:218` | exact |
| 785 | `tateProj_mem_integers` | `Tate/CommFinite.lean:221` | exact |
| 792 | `tateProj_of_mem` | `Tate/CommFinite.lean:228` | exact |
| 805 | `range_tateProj` | `Tate/CommFinite.lean:236` | exact |
| 871 | `poleWindowKSubmod` | `Tate/CommFinite.lean:251` | exact |
| 883 | `mem_poleWindowKSubmod_iff` | `Tate/CommFinite.lean:263` | exact |
| 888 | `adicIntegersKSubmod_le_poleWindowKSubmod` | `Tate/CommFinite.lean:268` | exact |
| 892 | `kwF4gRRTate_clearPole` | `Tate/CommFinite.lean:272` | exact |
| 923 | `KwF4gRRTatePoleWindowFinite` | `Tate/CommFinite.lean:319` | Correction 1 |
| 970 | `isOpen_setOf_valued_le` | `Tate/CommFinite.lean:443` | exact |
| 1046 | `kwF4R1V410a_algebraMap_mem_completionIdeal_pow_iff` | `Tate/CommFinite.lean:486` | exact |
| 1057 | `kwF4R1V410a_exists_sub_mem_completionIdeal_pow` | `Tate/CommFinite.lean:497` | exact |
| 1100 | `kwF4R1V410a_quotientEquiv` | `Tate/CommFinite.lean:541` | exact |
| 1116 | `kwF4R1V410a_quotientEquiv_mk` | `Tate/CommFinite.lean:558` | exact |
| 1158 | `coe_smul_K` | `Tate/CommFinite.lean:576` | exact |
| 1163 | `poleWindowShift` | `Tate/CommFinite.lean:581` | exact |
| 1174 | `poleWindowShift_injective` | `Tate/CommFinite.lean:592` | exact |
| 1189 | `poleWindowShift_surjective` | `Tate/CommFinite.lean:606` | exact |
| 1202 | `poleWindowShiftEquiv` | `Tate/CommFinite.lean:619` | exact |
| 1207 | `piPowKSubmod` | `Tate/CommFinite.lean:624` | exact |
| 1216 | `poleWindowShift_image_integers` | `Tate/CommFinite.lean:633` | exact |
| 1232 | `KwF4gRRTateDVRQuotPowKFinite` | `Tate/CommFinite.lean:649` | Correction 1 |
| 1237 | `kwF4gRRTate_poleWindowFinite_of_DVRQuotPowKFinite` | `Tate/CommFinite.lean:654` | exact |
| 1446 | `piPowKSubmod_eq_restrictScalars` | `Tate/CommFinite.lean:681` | exact |
| 1453 | `quotPiPowEquivIdealQuot` | `Tate/CommFinite.lean:688` | exact |
| 1461 | `KwF4gRRTateDVRCotangentKFinite` | `Tate/CommFinite.lean:696` | Correction 1 |
| 1466 | `range_mulLeft_eq_restrictScalars_span` | `Tate/CommFinite.lean:701` | exact |
| 1476 | `finiteDimensional_restrictScalarsQuot_pow` | `Tate/CommFinite.lean:709` | exact |
| 1542 | `finiteDimensional_idealQuot_pow` | `Tate/CommFinite.lean:775` | exact |
| 1550 | `kwF4gRRTate_DVRQuotPowKFinite_of_cotangent` | `Tate/CommFinite.lean:783` | exact |
| 1605 | `span_irreducible_eq_completionIdeal_pow_one` | `Tate/CommFinite.lean:813` | exact |
| 1611 | `quotientEquivKAlg` | `Tate/CommFinite.lean:819` | exact |
| 1625 | `quotSpanIrreducibleEquivResidueField` | `Tate/CommFinite.lean:834` | exact |
| 1634 | `kwF4gRRTate_DVRCotangentKFinite` | `Tate/CommFinite.lean:843` | exact |

The seven pin-`private` prelude rows the checker skips (`ord_nonneg_of_mem` 284,
`mem_of_ord_nonneg` 300, `mem_iff_ord_nonneg` 309, `algebraMap_ne_zero` 328,
`comap_algebraMap_ne_top` 333, `exists_ord_algebraMap_pos` 387,
`ramificationIndex_set_nonempty` 404) are resolved by the imported public rows
`Defs/PushPull.lean` and `Tate/CommFinite.lean` (the latter's private `algebraMap_ne_zero`
is not needed by the tail).

## 4. GENERALISE / ADAPT rows (2)

| pin ln | name | port home | kind |
|---:|---|---|---|
| 314 | `exists_ord_pos` | `Defs/PushPull.lean:74` | explicit-binder spelling of the pin's section-variable form; import, do not re-declare (a re-declaration collides on the global last name) |
| 354 | `mem_comap_iff_ord_nonneg` | `Defs/PushPull.lean:107` | same; the pin's `variable {w} in` block spells the same statement with `{f : F} (hf : f ≠ 0)` only, the port carries the full binder set |

Neither row is reached by the chain-rule tail, so neither is restated; both keep
verifying against the `Thm_AlgebraicCurve_Place_*` wrappers already in `SOURCES`.
(`port_advise` additionally reports `ext` as a "generalise" collision: that is
`DualDom.ext` matching `Defs/Place.lean`'s unrelated `ext`; it is NEW, §5.)

## 5. KEEP/NEW rows (60) — the chain-rule tail

All statements are transcribed verbatim from the pin at the pin's binders; the
"lead" column is the mathlib/port ingredient the port's proof uses. `PI` =
proof-ingredient, `B` = bespoke.

### 5.1 the Kähler pullback lemma and the projection idempotent (pin 692, 800)

| pin ln | name | class | lead |
|---:|---|---|---|
| 692 | `kaehlerPullback_D` | PI | `KaehlerDifferential.map_D K K E F` (probe M/E); `@[scoped simp]` |
| 800 | `tateProj_idem` | PI | `tateProj_of_mem` (`Tate/CommFinite.lean:228`), `tateProj_mem_integers` (`:221`), `LinearMap.{ext, comp_apply}` |

### 5.2 trace cyclicity and additivity on a superspace (pin 1289–1405)

| pin ln | name | class | lead |
|---:|---|---|---|
| 1289 | `range_comp_map_left` | PI | `LinearMap.mem_range_self`, `Submodule.mem_range` |
| 1294 | `finrankTrace_comp_comm` | PI | `LinearMap.trace_comp_comm'` (probe M), `finrankTrace` |
| 1350 | `finrankTrace_eq_trace_on_superspace` | PI | `Submodule.finiteDimensional_of_le`, `Submodule.inclusion`, `LinearMap.trace_comp_comm'` |
| 1380 | `finrankTrace_sub_eq` | PI | `Submodule.finiteDimensional_sup`, `map_sub`, `LinearMap.trace` |

### 5.3 the pole-window image finiteness (pin 1688–1796)

| pin ln | name | class | lead |
|---:|---|---|---|
| 1688 | `KwF4gRRTatePoleWindowImageFinite` | B | new `def : Prop` (the image of `lmulK u fh` on the completion integers, modulo them, is finite-dimensional) |
| 1740 | `kwF4gRRTate_poleWindowFinite` | PI | `kwF4gRRTate_poleWindowFinite_of_DVRQuotPowKFinite` + `kwF4gRRTate_DVRQuotPowKFinite_of_cotangent` + `kwF4gRRTate_DVRCotangentKFinite` (`Tate/CommFinite.lean:654/783/843`) |
| 1752 | `lmul_adicIntegers_subset_poleWindow` | PI | `mem_poleWindowKSubmod_iff`, `Submodule.map`, `lmulK`, `mul_mem` |
| 1772 | `kwF4gRRTate_poleWindowImageFinite` | PI | `IsDiscreteValuationRing.exists_irreducible` (probe M), `kwF4gRRTate_clearPole`, `Submodule.map_mono`, `LinearMap.{range_comp}`, `Submodule.range_subtype`, `LinearMap.quotKerEquivRange` |

### 5.4 the trace algebra of `finrankTrace` (pin 1838–2217, 2636–2677)

| pin ln | name | class | lead |
|---:|---|---|---|
| 1838 | `finrankTrace_congr` | PI | `subst` |
| 1844 | `range_sub_le` | PI | `sub_mem`, `Submodule.mem_sup_left/right`, `LinearMap.mem_range_self` |
| 1859 | `finrankTrace_sub` | PI | `finrankTrace_sub_eq`, `finrankTrace_eq_trace_on_superspace` |
| 1886 | `alphaMap` | B | new `def` (the `mkQ ∘ lmulK ∘ subtype` term map out of `range (tateProj u)`) |
| 1892 | `finiteDimensional_range_alphaMap` | PI | `Submodule.quotEquivOfEq` + `range_tateProj`, `Submodule.equivMapOfInjective` |
| 1986 | `finrankTrace_zero` | PI | `LinearMap.range_zero`, `map_zero` |
| 1994 | `finrankTrace_neg` | PI | `finrankTrace_sub`, `finrankTrace_zero` |
| 2009 | `finrankTrace_add` | PI | `finrankTrace_sub`, `finrankTrace_neg`, `sub_neg_eq_add` |
| 2026 | `tateComm_add_fst` | PI | `unfold tateComm`, `LinearMap.add_apply`, `abel` |
| 2033 | `tateCommRestrict_add_fst` | PI | `tateCommRestrict_apply` + `tateComm_add_fst` |
| 2042 | `tateCommTrace_add_fst` | PI | `tateCommRestrict_add_fst`, `finrankTrace_add`, `finrankTrace_congr` |
| 2061 | `tateRes_add_fst` | PI | `lmulK` is `map_add`, `tateCommTrace_add_fst` |
| 2141 | `tateComm_add_snd` | PI | mirror of 2026 |
| 2148 | `tateCommRestrict_add_snd` | PI | mirror of 2033 |
| 2157 | `tateCommTrace_add_snd` | PI | mirror of 2042 |
| 2636 | `range_smul_le` | PI | `Submodule.smul_mem`, `LinearMap.mem_range_self` |
| 2641 | `finDimRangeSMul` | PI | `Submodule.finiteDimensional_of_le` + `range_smul_le` |
| 2646 | `finrankTrace_smul` | PI | `finrankTrace_eq_trace_on_superspace`, `LinearMap.map_smul` |
| 2658 | `tateCommRestrict_smul_snd` | PI | `unfold tateComm`, `LinearMap.smul_apply`, `Submodule.coe_smul` |
| 2668 | `tateCommRestrict_smul_fst` | PI | mirror of 2658 |

### 5.5 commutator vanishing and the abstract Leibniz defect (pin 2186–2357)

| pin ln | name | class | lead |
|---:|---|---|---|
| 2186 | `finrankTrace_commutator_eq_zero` | PI | `finrankTrace_sub`, `finrankTrace_comp_comm`, `sub_self` |
| 2198 | `piRestrict` | B | new `def` (`(pA ∘ φ)` restricted to `range pA`) |
| 2201 | `piRestrict_apply` | PI | `rfl` |
| 2204 | `epsRestrict` | B | new `def` (correction 1: the advice's `tateCommRestrict` match is bogus) |
| 2208 | `epsRestrict_apply` | PI | `LinearMap.sub_apply`, `LinearMap.id_apply` |
| 2213 | `piRestrict_comp_eq` | PI | `epsRestrict_apply`, `map_add`, `abel` |
| 2222 | `tateCommRestrict_eq_bracket` | PI | `tateCommRestrict_apply`, `tateComm_apply`, `piRestrict_apply` |
| 2230 | `bracket_leibniz_defect` | PI | pure module algebra; `abel` after `LinearMap.comp_apply`/`map_sub` |
| 2240 | `tateCommTrace_leibniz_snd` | PI | 2186 + 2213 + 2222 + 2230; the long `set`/`calc` assembly, transcribed verbatim |
| 2367 | `finiteDimensional_range_epsRestrict_lmulK` | PI | `Submodule.liftQ` (probe M/N), `tateProj_idem`, `finiteDimensional_range_alphaMap`, `LinearMap.range_comp` |
| 2394 | `tateRes_leibniz_snd` | PI | `tateCommTrace_leibniz_snd`, `finiteDimensional_range_epsRestrict_lmulK`, `finrankTrace_congr` |
| 2447 | `tateRes_congr_fst` | PI | `subst` |
| 2678 | `tateRes_congr_snd` | PI | `subst` |
| 2686 | `tateRes_add_snd` | PI | `tateCommTrace_add_snd`, `finrankTrace_congr` |

### 5.6 the `DualDom` dual and the derivation `tateResSndDer` (pin 2462–2802)

| pin ln | name | class | lead |
|---:|---|---|---|
| 2462 | `KwF4gRRTateDerivationFactorSnd` | B | new `def : Prop` (the pin's `KaehlerDifferential.D` form of the chain rule) |
| 2484 | `kwF4gRRTate_chainRule_of_derivationFactor` | PI | `kaehlerPullback_D`, `tateRes_congr_fst`; the only place the `E`/`F` dictionary meets the derivation factor |
| 2557 | `DualDom` | B | `def … := w.adicCompletion →ₗ[K] K` |
| 2562 | `DualDom.toLM` | B | the identity coercion; `def` |
| 2564 | `DualDom.ext` | PI | `LinearMap.ext`; `@[scoped ext]` |
| 2568 | `DualDom.toLM_add` | PI | `rfl`; `@[scoped simp]` |
| 2590 | `DualDom.smul_apply` | PI | `rfl`; `@[scoped simp]` |
| 2598 | `DualDom.k_smul_apply` | PI | `rfl` |
| 2617 | `derivation_apply_eq_diffCoeff_smul` | PI | `Derivation.liftKaehlerDifferential_comp_D` (probe M), `Place.differentialCoeff_smul_dCoord` (`Defs/CanonicalDivisor.lean:80`), `map_smul` |
| 2701 | `tateResFstLM` | B | new `def` into `DualDom w` via structure `where`; `tateRes_add_fst`, `tateCommRestrict_smul_fst`, `finrankTrace_smul` |
| 2718 | `tateResFstLM_apply` | PI | `rfl`; `@[scoped simp]` |
| 2724 | `tateResSndDer` | B | new `def` via `Derivation.mk'` (probe M) with the Leibniz law assembled from `tateRes_leibniz_snd` + `tateRes_congr_{fst,snd}` |
| 2767 | `tateResSndDer_apply` | PI | `rfl`; `@[scoped simp]` |
| 2780 | `kwTateRR2_derivationFactorSnd` | PI | `derivation_apply_eq_diffCoeff_smul` with `M := DualDom w`, `DualDom.smul_apply`, `tateResSndDer_apply`, `tateRes_congr_fst` |
| 2830 | `solution` | PI | one application of `kwF4gRRTate_chainRule_of_derivationFactor`; ported as the wrapper's public name `AlgebraicCurve.tateChainRule` |

**The wrapper row (60th).** `Theorems/Thm_AlgebraicCurve_tateChainRule.lean` publishes
`AlgebraicCurve.tateChainRule` at exactly the pin `solution`'s binders; the port writes
that one declaration (not `solution`) and the checker matches it against either source.

## 6. Reuse wins, with probe evidence

1. **The whole 3.3a prelude is imported, not re-proved.** 40 of the pin's 101 public
   rows are `Tate/CommFinite.lean` (38) and `P1/EnginePrelude.lean` (2); probes A
   `#check` every one. This is the largest single lever of the set: ≈1,000 pin lines
   not written.
2. **The trace algebra is mathlib's.** `finrankTrace_comp_comm` is
   `LinearMap.trace_comp_comm'` on the restricted maps, and
   `finrankTrace_eq_trace_on_superspace` is the same lemma at the superspace
   `W` (probe M/E). The pin's `finrankTrace` cannot be replaced by
   `LinearMap.trace K V` (its hypothesis is finiteness of the *range*; see
   `AUDIT-mathlib-p3-3a.md` Correction 5), so `finrankTrace` stays as the currency.
3. **The abstract Leibniz identity is pure module algebra.** `bracket_leibniz_defect`
   and `tateCommRestrict_eq_bracket` mention no `Place`/completion vocabulary; their
   proofs are `LinearMap.ext` + `simp` + `abel`. Do not route them through a Lie
   algebra structure (`tateComm` is a `Ring.lie_def`-style bracket but
   `LieRing.ofAssociativeRing` is only a local instance; `AUDIT-mathlib-p3-3a.md`
   negative §10.3).
4. **`Submodule.liftQ` is the v4.34 name** for the pin's
   `(LinearMap.range pA).liftQ` (probe M/N); `Submodule.finiteDimensional_of_le`
   and `Submodule.finiteDimensional_sup` are the two finiteness leaves.
5. **The derivation factor is one mathlib lemma.** `derivation_apply_eq_diffCoeff_smul`
   is `Derivation.liftKaehlerDifferential_comp_D` + the ported
   `Place.differentialCoeff_smul_dCoord`; there is no new Kähler mathematics in the
   tail. `Derivation.mk'` is the only construction used by `tateResSndDer`.

## 7. API drift (`v4.34.0`) — what the worker must change

| pin call / assumption | `v4.34.0` status | worker action |
|---|---|---|
| `(LinearMap.range pA).liftQ f h` (pin 2375) | the method is on `Submodule`: `Submodule.liftQ` (probe M) | dot-notation `(LinearMap.range pA).liftQ …` resolves; no statement change |
| `set_option maxHeartbeats 12800000` / `synthInstance.maxHeartbeats 6400000` (pin 1658 and following) | project cap 4,000,000 | drop; the tail re-elaborates under the cap (Correction 4) |
| pin `p2m_export`/`p2m_open`/`p2m_reactivate` scaffolding (passim) | not declarations | drop |
| pin `scoped instance`s (Correction 3) | invisible to `port_advise`/the checker | land explicitly |
| `Submodule.finiteDimensional_iff` (a tempting name) | does **not** exist (probe N) | use `finiteDimensional_of_le`/`finiteDimensional_sup` |
| `LinearMap.liftQ` (a tempting name) | does **not** exist (probe N) | `Submodule.liftQ` |
| `LinearMap.range_comp_le_range` orientation | `range_comp_le_range f g : (g ∘ f).range ≤ g.range` (probe E) | the two `instFinDimRangeComp{Left,Right}` instances use it with the pin's argument order |
| `KaehlerDifferential.map_D` (pin 695) | present (probe M); the port's `kaehlerPullback` is a `def`, but it unfolds under elaboration | transcribe the body verbatim (probe E) |
| `Derivation.liftKaehlerDifferential_comp_D`, `Derivation.mk'`, `LinearMap.trace_comp_comm'` (pin 2621/2726/1309) | present (probe M) | no rename |

## 8. Recorded negatives

Confirmed against mathlib `v4.34.0` and the set-3.3a port; phrased so the search is
not repeated.

1. **No `tateChainRule`, `KwF4gRRTatePoleWindowImageFinite`, `kaehlerPullback_D`,
   `piRestrict`, `epsRestrict`, `alphaMap`, `DualDom`, `tateResFstLM`, `tateResSndDer`
   or `bracket_leibniz_defect` in the pre-3.3b port.** Greps over `FLTForHuman/`
   return nothing. These are the 60 new rows.
2. **No mathlib declaration replaces a new row.** Every new name is either a
   `Prop`/`def`/instance introducing pin vocabulary or a statement over `tateComm`/
   `finrankTrace`/`tateRes`/`DualDom`; the mathlib leaves are proof ingredients only
   (probe M). In particular there is no mathlib `finrankTrace` (the pin's range-only
   finiteness is not `LinearMap.trace`'s binder) and no mathlib
   `derivationFactorSnd`.
3. **`Submodule.finiteDimensional_iff` and `LinearMap.liftQ` do not exist** in
   `v4.34.0` (probe N). Do not search for them; the names are
   `Submodule.finiteDimensional_sup`/`_of_le` and `Submodule.liftQ`.
4. **The tail does not reach the unported InlineSpecific slice** (Correction 2): no
   `completionIdeal`/`exists_uniformizer` re-landing is needed, so promotion debt is
   empty for this set.
5. **`epsRestrict` is not `tateCommRestrict`** (Correction 1). The advice's
   `def`-body match is the P3.2f/P3.3a false-positive pattern; the last-name check is
   the only reliable test.
6. **The `DualDom` instances cannot be avoided.** `DualDom w` is a type synonym, so
   mathlib's `Module F (w.adicCompletion →ₗ[K] K)` is not found for it; the pin's
   four `scoped instance`s are genuine (a `F`-semilinear action on the dual, plus the
   `K`/`IsScalarTower` coherence), not a diamond with the ambient module structure.

## 9. What this changes for the work order / verification

- **Scope.** 40 SUBSTITUTE / 2 GENERALISE / 60 NEW over 102 checked rows, plus 10
  checker-invisible `scoped instance`s. The measured "47 substituted" is high by the
  four `def : Prop` false positives and the `epsRestrict` match.
- **Imports.** `Tate/ChainRule.lean` imports `Defs/TateResidueCurrency.lean` (as the
  plan requires) and `Tate/CommFinite.lean` (the 37 prelude substitutes). No
  `Def_DedekindDomain_AdicValuation_InlineSpecific` re-landing.
- **Checker wiring.** Append `Theorems/Thm_AlgebraicCurve_tateChainRule.lean` then
  `P2M/Sol/S_AlgebraicCurve_tateChainRule.lean` to `SOURCES`; append
  `FLTForHuman/AlgebraicCurve/Tate/ChainRule.lean` to `PORT_FILES`, last.
- **Discharged rows.** The 40 substitutes and the 2 adapters land no new
  declaration; their statements still land in `SOURCES` and keep verifying against
  their existing port homes.
- **`#print axioms`.** The public nodes are `AlgebraicCurve.tateChainRule`,
  `ModularCurve.KwF4gRRTate.kwF4gRRTate_chainRule_of_derivationFactor` and
  `kwTateRR2_derivationFactorSnd`; all should print
  `[propext, Classical.choice, Quot.sound]`.
