# Mathlib-first substitution audit — P3.3d, the Tate trace compatibility

**Method:** [`lean/porting-playbook.md`](../porting-playbook.md) §2.2 (audit the route,
mathlib first), after the phase-1/2/3.1/3.2a–3.2f and
[`AUDIT-mathlib-p3-3a.md`](AUDIT-mathlib-p3-3a.md) templates. Pin:
`anthropics/fermats-last-theorem@aa2d8b3` (read-only clone at
`~/proj/fermats-last-theorem`); port mathlib `v4.34.0`
(`lean/.lake/packages/mathlib`). Work order: `PLAN-P3-3.md` §1–§2. Pre-port
measurement: `tools/deps/build/p33d_advise.{log,json}` (2 targets, 146
declarations).

**Source.** One pin file, its home the new
`FLTForHuman/AlgebraicCurve/Tate/TraceCompat.lean`:

- [`P2M/Sol/S_AlgebraicCurve_tateTraceCompat_of_isSeparable.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_tateTraceCompat_of_isSeparable.lean)
  (4,418 ln, 145 declarations) — the trace-cyclicity and additivity algebra of the
  pin's bespoke `finrankTrace`, the `SameRangeIdemProjectors` vocabulary and the
  projector-independence computation, the block decomposition along an integral
  basis, and the separable global headline, published as
  `AlgebraicCurve.tateTraceCompat_of_isSeparable` by
  [`Theorems/Thm_AlgebraicCurve_tateTraceCompat_of_isSeparable.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_AlgebraicCurve_tateTraceCompat_of_isSeparable.lean).

**Baseline.** Checker at dispatch **3779 identical / 0 mismatched / 0 missing / 30
own-proof** (3809); at close **3932 / 0 / 0 / 30** (3962), the +153 being the
independently dispatched set 3.3b (`Tate/ChainRule.lean`, +~59) and this set
(+94 net new checked declarations; see §1).

**Scratch evidence.** `lean/ScratchAuditP33d.lean` (gitignored, deleted after use)
was compiled from `lean/` with

```bash
timeout 600 lake env lean -DmaxHeartbeats=4000000 -DautoImplicit=false ScratchAuditP33d.lean
```

and ran with **one recorded negative** (`Basis.repr`, a structure projection that
does not `#check` by its full name — see §6.8) and no other errors. The 49 verified
mathlib constants are in §4. `#print axioms` on the public nodes (headline, the
global lift, the block-sum and integral-basis compat, the projector-independence
computation, `finrankTrace_comp_comm`) returned
`[propext, Classical.choice, Quot.sound]` (§4.1).

## 1. Summary — class counts

`port_advise` reads 145 declarations in the pin `S_` file. Nine are `private` and
the checker skips them; the remaining **136 public** rows split as follows.

| class | rows | disposition |
|---|---:|---|
| SUBSTITUTE — importable public port copy | 40 | import `Tate/CommFinite.lean` / `P1/EnginePrelude.lean` |
| SUBSTITUTE — port copy is `private` (pin `private` too) | 7 | omitted; the checker skips pin-privates |
| GENERALISE — same conclusion, port binder spelling | 2 | import `Defs/PushPull.lean` |
| KEEP/NEW — public | **94** | transcribed |
| — of which proof-ingredient `theorem`s | 76 | short assemblies of named mathlib/port lemmas |
| — of which bespoke `def`/`structure` | 18 | vocabulary |
| pin `scoped instance`s (checker-invisible) | 16 | 14 landed here; 2 imported from 3.3a |

**Headline.** This file is 3.3a's `tateCommFinite` prelude (≈2,250 ln) followed by
the genuinely new trace-compatibility theory (≈2,000 ln). Of the 136 public rows,
42 are already in the port with an identical statement — 40 of them from the 3.3a
home `Tate/CommFinite.lean`, two from `Defs/PushPull.lean` — so the new module
transcribes only the 94 rows the port does not already carry. `#print axioms` is
clean on every public node.

## 2. Corrections to the measurement

**Correction 1 — six of the `def` "substitutions" are false positives.** The
checker's declaration statement for a `def` stops at `:=`, so every
`def … : Prop` with the same binder block matches the port attractor
`EisensteinWeightOne.E1Chi3IsModular`; `port_advise` reports nine such rows for
this file. Three are genuine (`KwF4gRRTatePoleWindowFinite` pin 1324,
`KwF4gRRTateDVRQuotPowKFinite` pin 1633, `KwF4gRRTateDVRCotangentKFinite` pin 2071,
all public in `Tate/CommFinite.lean`). Six are **NEW**, either because no port
declaration carries the body or because the matched port name has a different last
name:

| pin ln | new `def` | bogus port match |
|---:|---|---|
| 1847 | `KwF4gRRTateProjectorIndep` | `EisensteinWeightOne.E1Chi3IsModular` |
| 2309 | `KwF4gRRTatePoleWindowImageFinite` | `EisensteinWeightOne.E1Chi3IsModular` |
| 2322 | `KwF4gRRTateCommFiniteGen` | `EisensteinWeightOne.E1Chi3IsModular` |
| 3096 | `tateCommDual` | `ModularCurve.KwF4gRRTate.tateComm` |
| 3265 | `KwF4gRRTateTraceCompatBlockSum` | `ModularCurve.KwF4gRRTate.KwF4gRRTateTraceCompat` |
| 3624 | `KwF4gRRTateIntegralBasisCompat` | `EisensteinWeightOne.E1Chi3IsModular` |

All six are landed here. The same attractor also flags the four `Prop` values
inside `Tate/CommFinite.lean` (3.3a audit Correction 1); the pattern is general.

**Correction 2 — the pin's section/`variable` structure must be preserved.** The
checker diffs the statement text after the declaration name, which for a
section-variable row is the short form (`∃ f : F, …`, not
`{K F} [Field K] … (v : Place K F) → …`). The port therefore keeps the pin's
`section`/`variable` blocks rather than spelling binders explicitly; this is what
lets the 94 new rows diff verbatim against the pin's `S_` file.

**Correction 3 — two checker-invisible `scoped instance`s already live in 3.3a.**
`kwF4R1V410a_subsingletonHeightOneSpectrumDVR` (pin 1431) and
`instIsScalarTower_K_to_ValuationSubring_adicCompletionIntegers` (pin 2206) are
declared by `Tate/CommFinite.lean:469/804`. They cannot be re-landed (a
same-namespace duplicate is a hard error) and are not needed by 3.3d's own proofs
(they serve the substituted `kwF4R1V410a_*`/cotangent block); they are dropped from
the pin text and the imports supply them.

**Correction 4 — the unported `Def_DedekindDomain_AdicValuation_InlineSpecific`
slice is not reached anew.** The pin's `completionIdeal`/uniformizer chain is used
only by the substituted first half (already resolved `private` in
`Tate/CommFinite.lean:84–212`, promotion debt from 3.3a). No new copy is landed
here. The `import` of the pin `S_` file's own private `uniformizer_mem` is *not*
used: the three occurrences of `(w.restrict E).uniformizer_mem` at pin
4133/4121 are the port's public `AlgebraicCurve.Place.uniformizer_mem`
(`LocalResidue/Instance.lean`), now imported.

## 3. SUBSTITUTE and GENERALISE rows

### 3.1 The 40 importable public rows

Read off `p33d_advise.log` §1, each port copy byte-identical to the pin statement
(the checker confirms). Thirty-six live in `Tate/CommFinite.lean` (the 3.3a home)
and are the `tateProj`/`poleWindow*`/`clearPole`/`DVRQuotPow`/`DVRCotangent`
discharge chain plus `maximalIdeal_le`, the `ValuationSubring` unit triple,
`coe_smul_K`, `range_mulLeft_eq_restrictScalars_span`, `piPowKSubmod*`,
`quotientEquivKAlg` and `quotSpanIrreducibleEquivResidueField`. Three live in
`P1/EnginePrelude.lean` (`isPrincipalIdealRing_comap` pin 449,
`isUnit_mk_comap_iff` pin 402) and one in `LocalResidue/Instance.lean`
(`uniformizer_mem` pin 1053, pin-private). The 3.3a audit (§3.1) already showed the
`ValuationSubring` triple is mathlib's `Valuation.Integers.*`; the port's copies
are public there, so 3.3d imports them and does not re-open that review item.

### 3.2 The two public GENERALISE rows

The pin declares both inside `section SinglePlace` / `section Restrict` with the
section variables `{K F} [Field K] [Field F] [Algebra K F] (v : Place K F)` (resp.
`w : Place K F'`); the port's `Defs/PushPull.lean` states them with explicit
binders. The statements agree up to binder spelling and the port copies are already
in `PORT_FILES`, so they are omitted here:

| pin ln | name | port home |
|---:|---|---|
| 354 | `Place.exists_ord_pos` | `Defs/PushPull.lean` |
| 394 | `Place.mem_comap_iff_ord_nonneg` | `Defs/PushPull.lean` |

The remaining three binder-variant rows (`mem_of_ord_nonneg` pin 340,
`mem_iff_ord_nonneg` pin 349, `comap_algebraMap_ne_top` pin 373) are pin-`private`
and skipped by the checker.

## 4. KEEP/NEW — the 94 rows, and their mathlib ingredients

The 94 new rows are the trace-compatibility theory. They are transcribed verbatim
from the pin; only the proof terms are adapted, and the recurring ingredients are
mathlib's, `#check`-verified in `ScratchAuditP33d.lean`.

### 4.1 The trace/range cyclicity kernel (all mathlib)

The pin's `finrankTrace φ = LinearMap.trace K (range φ) (φ.restrict _)` is
bespoke, so its lemmas stay; their proofs are one-liners over mathlib:

| new row | mathlib ingredient (verified) |
|---|---|
| `range_comp_map_left` (1750) | no mathlib name; `rintro ⟨y, rfl⟩` |
| `finrankTrace_comp_comm` (1755) | `LinearMap.trace_comp_comm'` |
| `finrankTrace_eq_trace_on_superspace` (1960) | `LinearMap.trace_comp_comm'`, `Submodule.inclusion` |
| `finrankTrace_sub_eq` (1990) | `Submodule.finiteDimensional_sup`, `map_sub` |
| `finrankTrace_sub` (2645) | `finrankTrace_sub_eq`, `finrankTrace_eq_trace_on_superspace` |
| `range_conj_eq_map` (2665) | `LinearEquiv.conj_apply`, `LinearMap.range_comp`, `LinearEquiv.range`, `Submodule.map_top` |
| `finrankTrace_conj` (2670) | `Submodule.equivMapOfInjective`, `finrankTrace_comp_comm` |
| `finrankTrace_zero/neg/add` (2941/2949/2964) | `LinearMap.range_zero`, `sub_neg_eq_add`, `map_zero` |
| `finrankTrace_sum` (3151) | `Finset` induction over the additivity rows |
| `range_sub_le` (2630) | `Submodule.mem_sup_left/right`, `mem_range_self` |

`LinearMap.trace_restrict_eq_of_forall_mem`
(`Mathlib/LinearAlgebra/PID.lean:35`) is the *stronger* available substitute: with
`[FiniteDimensional K V]` and `[IsDomain K] [IsPrincipalIdealRing K]` it collapses
`finrankTrace` to `LinearMap.trace K V` directly. It is deliberately **not** used:
the pin's rows carry only range-finiteness hypotheses and the five `Prop` atoms
would have to be strengthened (3.3a audit Correction 5).

### 4.2 Submodule/quotient algebra (mathlib)

`Submodule.liftQ` (`deltaQuotFactor` 2290), `LinearMap.quotKerEquivRange` +
`Submodule.range_subtype` + `Submodule.ker_mkQ` (`kwF4gRRTate_poleWindowImageFinite`
2398), `Submodule.map_mono`/`Submodule.finiteDimensional_of_le` (both),
`Submodule.quotEquivOfEq` (`finiteDimensional_range_alphaMap` 2726),
`Submodule.equivMapOfInjective` (many), `Submodule.finiteDimensional_sup`
(`kwF4gRRTate_commFiniteGen` 2538). All verified.

### 4.3 The integral-basis and block-sum layer (mathlib)

`Algebra.TensorProduct.lift` (4085), `Basis.equivFun`-style `Module.Basis`
(`IntegralBasisData` 3611, `integralBasisEquivFunK` 3638), `Module.finrank`,
`Module.free_of_finite_type_torsion_free'` + `IsIntegralClosure.isNoetherian` +
`Module.IsNoetherian.finite` (`kwF4gRRTate_free_adicCompletionIntegers` 3588),
`Matrix`-indexed `matMulLin`/`scalarLin` (3405/3416, no mathlib name — bespoke
`LinearMap`s over `Fin n → _`). All verified except the projection `Basis.repr`
(§6.8); `Finset.sum` trace additivity is `finrankTrace_sum`.

### 4.4 The spectral/separability layer (mathlib)

The six `kw_ffgc_*` rows (pin 723–931) are statements over the port's existing
`Place.kw_ffgc_*` completion dictionary; their proofs are mathlib's:
`Valuation.Integers.isIntegrallyClosed` + `IsIntegrallyClosed.isIntegral_iff`
(847), `spectralNorm_unique_field_norm_ext` +
`spectralValue_le_one_iff` + `Polynomial.lifts_and_degree_eq_and_monic`
(798/847, all in `Mathlib/Analysis/Normed/Unbundled/SpectralNorm.lean` /
`Mathlib/Algebra/Polynomial/Lifts.lean`), `isIntegral_algHom_iff`, and
`valueGroup₀_equiv_withZeroMulInt_restrict_apply_of_surjective`
(`Mathlib/RingTheory/Valuation/Discrete/RankOne.lean`). The separable fiber tail
(4223/4244/4355) uses `IntermediateField.isSeparable_adjoin_iff_isSeparable` and
`Algebra.IsSeparable.of_algHom`, plus `TensorProduct.induction_on` for the adjoin
generation.

### 4.5 The bespoke vocabulary (18 rows)

`SameRangeIdemProjectors` (1811, `structure`), `IntegralBasisData` (3611,
`structure`), the `Prop` atoms `KwF4gRRTateProjectorIndep` (1847),
`KwF4gRRTatePoleWindowImageFinite` (2309), `KwF4gRRTateCommFiniteGen` (2322),
`KwF4gRRTateTraceCompatBlockSum` (3265), `KwF4gRRTateIntegralBasisCompat` (3624),
and the data `def`s `deltaQuotFactor` (2290), `alphaMap` (2704), `mulOnRange`
(2711), `tateCommDual` (3096), `prodTateProj` (3386), `matMulLin` (3405),
`scalarLin` (3416), `integralBasisEquivFunK` (3638), `integralProdProj` (3646),
`integralBasisDataOf` (3952), `kwF4R1V384a_semilocalComponent` (4085). None has a
mathlib counterpart; they carry the pin's statement surface.

## 5. API drift (`v4.34.0`) — what the worker had to change

| pin text | `v4.34.0` | worker action |
|---|---|---|
| `Algebra.TensorProduct.lift f g (fun _ _ => mul_comm _ _)` (pin 3952) | the `hfg` argument is now `∀ x y, Commute (f x) (g y)` (`Mathlib/RingTheory/TensorProduct/Maps.lean:155`) | `fun _ _ => Commute.all _ _` |
| `TensorProduct.induction_on` (pin 4215 block) | deprecated; `inductionOn` has a different case split (no `zero`) | keep the pin's deprecated name under a local `set_option linter.deprecated false in` |
| `NNReal.coe_pow` after the `letI`-carrying `kw_ffgc_norm_adicCompletion_eq` rewrites (pin 786) | `rw [NNReal.coe_pow]` cannot match the `letI`-shaped occurrence | `push_cast` after the norm rewrites |
| `𝓞` in the pin `section NumberField` (pin 1392) | `scoped notation` (`Mathlib/NumberTheory/NumberField/Basic.lean:108`) | `open scoped NumberField` |
| `⊗[E]`, `→ₐ[R]` (pin 4085 ff.) | scoped `TensorProduct` notation | `open scoped TensorProduct` |
| pin `maxHeartbeats 6400000`/`12800000`/`25600000`, `synthInstance.maxHeartbeats` | project cap 4,000,000 | dropped; no declaration exceeded the cap |
| pin `p2m_*` scaffolding, outer `P2MW.S_...` namespace | not declarations | dropped |
| `attribute [-ext] IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext` (pin 16) | present | transcribed |

No other rename/reorder was needed: the port's `Defs/TateResidueCurrency.lean`
bodies (`finrankTrace`, `tateComm`, `tateCommRestrict`, `tateCommTrace`,
`lmulK`, `tateProj`, the `KwF4gRRTate*` atoms) coincide with the pin's, so the
proofs transcribe.

## 6. Recorded negatives

1. **No mathlib declaration replaces any of the 94 new rows.** They are the pin's
   bespoke `finrankTrace` algebra, the `SameRangeIdemProjectors`/integral-basis
   vocabulary, or statements over the port's `Place`/`adicCompletion` dictionary;
   the mathlib constants in §4 are proof ingredients only.
2. **No single mathlib lemma gives `LinearMap.range (g ∘ₗ f) ⊆ …` in the pin's
   membership form** (`range_comp_map_left`, pin 1750); it is a two-line rintro.
3. **No mathlib name states the projector-independence trace equality**
   (`KwF4gRRTateProjectorIndep`, pin 1847); `LinearMap.trace_restrict_eq_of_forall_mem`
   needs ambient finite-dimensionality the pin does not have.
4. **`lie_skew`/`LieRing.neg_lie` are not usable at `Module.End K V`** (3.3a audit
   §9.3); `tateComm_antisymm` stays a `neg_sub`.
5. **There is no `Subring`/`ValuationSubring → Submodule` coercion** (3.3a audit
   §9.4), so `adicIntegersKSubmod` remains a genuine `def`.
6. **The `completionIdeal`-power API is pin-local** (3.3a audit §9.7); 3.3d reaches
   it only through substituted rows and lands no new copy.
7. **The six `def … : Prop` "substitutions" are false positives** (§2 Correction 1);
   the checker cannot see `def` bodies and `EisensteinWeightOne.E1Chi3IsModular` is
   the attractor.
8. **`#check @Basis.repr` fails by full name** (it is a structure projection,
   reached as `D.basis.repr`); not a gap, but do not search for the constant.
9. **`LinearMap.trace_restrict_eq_of_forall_mem` requires
   `Mathlib.LinearAlgebra.PID`**, which is not in this module's import closure; it
   was verified in the audit scratch only and is not used by the port.

## 7. Duplication debt — the shared 3.3 prelude is copied across sibling sets

The pin's four `tate*` `S_` files are each self-contained and re-prove a common
trace/projector prelude. Because 3.3b/3.3c/3.3d were dispatched in parallel and may
not edit one another, all three land that prelude again. Cross-module last-name
overlap of the new module (computed with the checker's `raw_declarations`):

| sibling | shared last names |
|---|---:|
| `Tate/CommFinite.lean` (3.3a) | 0 (all imported) |
| `Tate/Agreement.lean` (3.3c) | 37 |
| `Tate/ChainRule.lean` (3.3b) | 21 |

The shared rows include `finrankTrace_comp_comm`, `finrankTrace_sub_eq`,
`finrankTrace_eq_trace_on_superspace`, `range_comp_map_left`, `range_sub_le`,
`pA_fixes_range`/`pA'_fixes_range`, `delta_zero_on_range`/`delta_range_subset`,
`SameRangeIdemProjectors`, `KwF4gRRTateProjectorIndep`/`kwF4gRRTate_projectorIndep`,
`alphaMap`/`mulOnRange`/`deltaQuotFactor`, `tateProj_idem`,
`KwF4gRRTatePoleWindowImageFinite` and the `tateComm*_add_fst` family. They compile
independently (no module imports two of the three), but **a consumer importing two
of them collides**. This is a dedup/refactor-round item: hoist the common prelude
once (the trace/algebra rows into `Defs/TateResidueCurrency.lean` or a new shared
`Tate/ProjectorPrelude.lean`) and delete the copies. It is *not* resolved here
because it would edit the sibling modules, which this set may not do. The checker's
`identical` count is inflated by the copies (each is counted once per module).

## 8. Module map for the new constants

| home | constants |
|---|---|
| `Tate/CommFinite.lean` | the 3.3a finiteness prelude (36 of the 40 substitutes, incl. `range_tateProj`, `tateProj_of_mem`, `mem_adicIntegersKSubmod_iff`, `poleWindowKSubmod`, `kwF4gRRTate_clearPole`, the `DVRQuotPow`/`DVRCotangent` chain, `maximalIdeal_le`, the `ValuationSubring` triple) |
| `P1/EnginePrelude.lean` | `isPrincipalIdealRing_comap`, `isUnit_mk_comap_iff` |
| `Defs/PushPull.lean` | `Place.exists_ord_pos`, `Place.mem_comap_iff_ord_nonneg` |
| `LocalResidue/Instance.lean` | `Place.uniformizer_mem` |
| `Defs/TateResidueCurrency.lean` | `finrankTrace`, `tateComm*`, `tateProj`, `lmulK`, the `KwF4gRRTate*` atoms reused in statements |
| `Tate/TraceCompat.lean` (new) | the 94 new rows, incl. `finrankTrace_comp_comm`, `SameRangeIdemProjectors`, `kwF4gRRTate_projectorIndep`, `kwF4gRRTate_poleWindowImageFinite`, `kwF4gRRTate_commFiniteGen`, the block decomposition, `kwTateRR3_traceCompat_of_isSeparable_global` and `AlgebraicCurve.tateTraceCompat_of_isSeparable` |
| mathlib `v4.34.0` | `LinearMap.trace_comp_comm'`, `Submodule.{finiteDimensional_of_le, finiteDimensional_sup, equivMapOfInjective, liftQ, quotEquivOfEq}`, `LinearMap.quotKerEquivRange`, `LinearMap.range_comp`, `LinearEquiv.{conj_apply, range}`, `Algebra.TensorProduct.{lift, lift_tmul}`, `IntermediateField.isSeparable_adjoin_iff_isSeparable`, `Algebra.IsSeparable.of_algHom`, `spectralNorm_unique_field_norm_ext`, `spectralValue_le_one_iff`, `Polynomial.lifts_and_degree_eq_and_monic`, `Valuation.Integers.isIntegrallyClosed`, `Module.free_of_finite_type_torsion_free'` |
