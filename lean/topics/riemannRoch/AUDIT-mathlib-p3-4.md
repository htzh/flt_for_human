# Mathlib-first substitution audit — P3.4, trace-completion commutation and the completion trace sum

**Method:** [`lean/porting-playbook.md`](../porting-playbook.md) §2.2 (audit the route,
mathlib first), after the phase-1/2/3.1/3.2a–3.2f/3.3a–3.3d templates
[`AUDIT-mathlib.md`](AUDIT-mathlib.md) … [`AUDIT-mathlib-p3-3d.md`](AUDIT-mathlib-p3-3d.md).
Pin: `anthropics/fermats-last-theorem@aa2d8b3` (read-only clone at
`~/proj/fermats-last-theorem`); port mathlib `v4.34.0`
(`lean/.lake/packages/mathlib`). Work order target: [`PLAN-P3-3.md`](PLAN-P3-3.md) §2
(the row-3.4 entry) and the P3.4 dispatch brief. Measurement:
[`tools/deps/build/p34_advise.log`](../../../tools/deps/build/p34_advise.log) and its
`.json` (4 targets, 55 declarations), plus a `--drags-full` run for the closure.

**Sources.** Two pin `S_` files, their homes the new
`FLTForHuman/AlgebraicCurve/Tate/TraceCompletionCommute.lean` (3.4a) and
`FLTForHuman/AlgebraicCurve/Tate/CompletionTraceSum.lean` (3.4b):

- [`P2M/Sol/S_AlgebraicCurve_residueTraceCompletionCommute.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_residueTraceCompletionCommute.lean)
  (1,109 ln, 15 declarations) — almost all scaffolding: 8 public rows (6 prelude
  declarations already public in the port, `kwF4gRRTate_RTCC_of_tate`, and `solution`),
  7 `private` prelude helpers, and the `_v2` byte-identical twin (dropped).
- [`P2M/Sol/S_AlgebraicCurve_completionTraceSum_of_isSeparable.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_completionTraceSum_of_isSeparable.lean)
  (867 ln, 38 checked declarations) — 1 public row (`solution`) + 37 `private`
  helpers, of which 13 are already public in `Tate/TraceCompat.lean`.

The two published targets are the pin wrappers
[`Thm_AlgebraicCurve_residueTraceCompletionCommute.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_AlgebraicCurve_residueTraceCompletionCommute.lean)
and
[`Thm_AlgebraicCurve_completionTraceSum_of_isSeparable.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_AlgebraicCurve_completionTraceSum_of_isSeparable.lean).

**Baseline.** Checker **4044 identical / 0 mismatched / 0 missing / 30 own-proof**
(4074 checked) before this set.

## 1. Summary — class counts

| file | rows | SUBSTITUTE | GENERALISE | KEEP/NEW |
|---|---:|---:|---:|---:|
| `TraceCompletionCommute.lean` (3.4a) | 8 public + 1 target | 7 | 0 | 2 |
| `CompletionTraceSum.lean` (3.4b) | 1 public + 37 private | 13 | 0 | 25 public-irrelevant + 1 target |
| **total** | **47** | **20** | **0** | **27** |

**Headline.** The set is *transcription*, not new mathematics: every row is either a
statement already in the port (20) or the pin's own proof carried at the pin's text
(27). The three levers are (i) the port's `Tate/TraceCompat.lean` already carries 13 of
the 37 `completionTraceSum` helpers, so 3.4 imports them; (ii) the pin's InlineSpecific
residue-field density chain is **not** re-landed — the same comparison is reached
through the port's public `kwF4R1V410a_quotientEquiv` at `n = 1`; (iii) the refactor
finding below, which is a prerequisite the P3.3 measurement got wrong.

## 2. Corrections to the work order and the measurement

**Correction 1 — the `def … : Prop` "substitutions" are false positives.** The
`port_advise` substitute and drags tables mark `KwF4R1V384aCompletionSemilocalBij`,
`KwF4R1V384aFinrankCompletionEF` and `KwF4R1V384aDistinctKernels` "in-port", all three
against `EisensteinWeightOne.E1Chi3IsModular` (`ModularForms/Defs/EisensteinChiNegThree.lean`,
the `def`-body attractor) or against a `def`-body copy. Verified by last name across the
whole port (`grep -rn` over `FLTForHuman/`): none of the three exists before 3.4. All
three are genuinely NEW (and land `private`).

**Correction 2 — the P3.3 "Agreement declares no public overlap" is false, and it
blocks 3.4.** The P3.3 collision measurement (PLAN-P3-3 §`Collision measurement`) claims
`Tate/Agreement.lean`'s copies are `private`. They are public: an import of `Agreement`
together with `ChainRule`/`TraceCompat`/`Prelude` fails with
``environment already contains 'ModularCurve.KwF4gRRTate.alphaMap'``. The full set is
**40** colliding public declarations — the manager's source-level detector found 22
(4 with `Prelude.lean`, 18 with `Tate/TraceCompat.lean`), and after deleting those,
Lean's own "already been declared" list revealed 18 more (all in
`ModularCurve.KwF4gRRTate`: `range_comp_map_left`, `finrankTrace_comp_comm`,
`SameRangeIdemProjectors`, `finrankTrace_eq_trace_on_superspace`, `finrankTrace_sub_eq`,
`KwF4gRRTatePoleWindowImageFinite`, `KwF4gRRTateCommFiniteGen`,
`kwF4gRRTate_poleWindowFinite`, `lmul_adicIntegers_subset_poleWindow`,
`finrankTrace_congr`, `range_sub_le`, `instFinDimRangeSub`, `finrankTrace_sub`,
`range_conj_eq_map`, `finrankTrace_conj`, `alphaMap_apply`, `mulOnRange`,
`mulOnRange_apply`) — because the detector's hand-rolled namespace tracker mishandles
`end A.B` closing two `namespace` scopes. Since 3.4a's `solution` needs `tateAgreement`
**and** `tateTraceCompat_of_isSeparable`, no 3.4a module could be written without a
bounded refactor. The parent authorised the refactor: `Tate/Agreement.lean` now imports
`Tate/Prelude.lean` and `Tate/TraceCompat.lean`, its 40 duplicate public declarations are
deleted (all statement-identical to the imported copy; verified textually before
deletion), and the four Tate theory modules now import together with **0 shared public
FQNs**. The deleted names are still supplied by `Prelude`/`TraceCompat`, so the checker
count moves only by the de-dup arithmetic (see §6).

**Correction 3 — the residue-field comparison has a cheaper port route.** The pin's
`kwF4R1V386a_inertiaDeg_completion_eq` gets
`V.ResidueField ≃+* IsLocalRing.ResidueField V.adicCompletionIntegers` from
`ResidueFieldEquivCompletionResidueField` (InlineSpecific pin 318/325), whose proof
reaches a 130-line density chain (`exists_adicValued_sub_lt_of_adicValued_le_one`,
`closureAlgebraMapIntegers_eq_integers`, `exists_adicValued_sub_lt_of_adicCompletionInteger`).
The port does **not** need that chain: the public
`ModularCurve.KwF4R1V410a.kwF4R1V410a_quotientEquiv V 1` is already
`V.toValuationSubring ⧸ maximalIdeal ≃+* V.adicCompletionIntegers ⧸ completionIdeal`
(`Tate/CommFinite.lean:541`, public), and `V.ResidueField` /
`IsLocalRing.ResidueField V.adicCompletionIntegers` are definitionally the two quotient
sides, so two `Ideal.quotEquivOfEq (pow_one _)` bridges close it. This is a measured
route win: the InlineSpecific residue chain is **not** transcribed.

**Correction 4 — `SumRamificationInertia`'s class parameters are plain implicit.** The
port's class (`Defs/PushPull.lean:677`) has its `[IsScalarTower]`/`[Algebra.IsIntegral]`/
`[HasPrincipalDivisors]` parameters as *implicit* (not instance-implicit) arguments of
`SumRamificationInertia.sum_ramificationIndex_mul_inertiaDeg`, so a call at
`(K := K) (F := E) (F' := F)` leaves them as metavariables. The port supplies them
explicitly (`@…`). The pin's own `Place.sum_ramificationIndex_mul_inertiaDeg` is a
theorem, so the pin never hits this.

## 3. SUBSTITUTE rows, with `#check` evidence

All checks run in `lean/` with

```bash
timeout 500 lake env lean -DmaxHeartbeats=4000000 -DautoImplicit=false ScratchP34Check.lean
```

`ScratchP34Check.lean` (gitignored, deleted after use) imported
`FLTForHuman.AlgebraicCurve.Tate.CompletionTraceSum` and `#check`ed the ledger below;
the run was clean (exit 0, only the two deprecation warnings recorded in §7).

### 3.1 3.4a — the pin's prelude is the port's public API

| pin row (ln) | substitute | note |
|---|---|---|
| `exists_ord_pos` (296) | `AlgebraicCurve.Place.exists_ord_pos`, `Defs/PushPull.lean` | same statement, binder-spelled |
| `mem_comap_iff_ord_nonneg` (336) | `AlgebraicCurve.Place.mem_comap_iff_ord_nonneg`, `Defs/PushPull.lean` | same |
| `isUnit_mk_comap_iff` (344) | `AlgebraicCurve.Place.isUnit_mk_comap_iff`, `P1/EnginePrelude.lean` | same |
| `isPrincipalIdealRing_comap` (391) | `AlgebraicCurve.Place.isPrincipalIdealRing_comap`, `P1/EnginePrelude.lean` | same (the 512-line row) |
| `kwHgfV352_localResidueCompletion_spec` (903) | `AlgebraicCurve.kwHgfV352_localResidueCompletion_spec`, `P1/DivPow.lean:687` | public; stated about DivPow's `private` def |
| `kwHgfV352_localResidueCompletion_algebraMap` (921) | `AlgebraicCurve.kwHgfV352_localResidueCompletion_algebraMap`, `P1/DivPow.lean:704` | public; ditto |

The 7 pin-`private` prelude helpers (`ord_nonneg_of_mem`, `mem_of_ord_nonneg`,
`mem_iff_ord_nonneg`, `algebraMap_ne_zero`, `comap_algebraMap_ne_top`,
`exists_ord_algebraMap_pos`, `ramificationIndex_set_nonempty`) are also already in
`Defs/PushPull.lean` / `P1/EnginePrelude.lean`; they are pin-`private`, so the checker
never requires them, and 3.4a does not transcribe them.

Because DivPow's public `_algebraMap` is stated about that module's **`private`**
`kwHgfV352_localResidueCompletion` while the wire proof's goal uses the **public**
`Defs/TateResidueCurrency.lean` def, 3.4a re-lands the `algebraMap` specialisation of
the public def `private` (`kwHgfV352_localResidueCompletion_algebraMap₀`), exactly as
3.3c's `Tate/Agreement.lean:895` does. This is the recorded promotion debt of P3.3a
§3.5 / the P3.3 pause note item 2.

### 3.2 3.4b — 13 helpers already public in `Tate/TraceCompat.lean`

Byte-for-byte statement-identical to the pin's `completionTraceSum` copies (the pin
repeats them from its `tateTraceCompat` file); imported, not re-proved:

`kw_ffgc_norm_adicCompletion_eq`, `kw_ffgc_absoluteValue_extends`,
`kw_ffgc_isIntegral_adicCompletionIntegers_of_algebraic`,
`kw_ffgc_isIntegralClosure_adicCompletionIntegers`,
`kwF4R1V384a_instAlgebraFiberCompletion`,
`kwF4R1V384a_instIsScalarTowerFiberCompletion`, `kwF4R1V384a_semilocalComponent`,
`kwF4R1V384a_semilocalComponent_tmul`,
`kwF4R1V384a_completionLinearCombination_surjective`,
`kwF4R1V384a_semilocalComponent_surjective`,
`kwF4R1V384a_instModuleFiberCompletion`,
`kwF4R1V386a_isSeparable_algebraMap_fiberCompletion`,
`kwF4R1V386a_isSeparable_fiberCompletion`.

The pin's 3 `Prop`/`def` rows `KwF4R1V384aCompletionSemilocalBij`,
`KwF4R1V384aFinrankCompletionEF`, `KwF4R1V384aDistinctKernels` are NOT in that list
(Correction 1); they are new and land `private`.

### 3.3 Mathlib ledger (all confirmed in `v4.34.0`)

| constant | role | file |
|---|---|---|
| `Algebra.trace_eq_matrix_trace`, `Algebra.leftMulMatrix_eq_repr_mul`, `Pi.basis`, `Pi.basis_apply`, `Pi.basis_repr`, `Pi.single_eq_of_ne`, `Matrix.blockDiagonal'_apply_eq`, `Matrix.blockDiagonal'_apply_ne`, `Matrix.trace_blockDiagonal'` | the product trace `gapsw7_x3x_trace_pi` | `Mathlib/LinearAlgebra/Matrix/Trace.lean`, `…/Basis.lean` |
| `LinearMap.trace_baseChange`, `Algebra.baseChange_lmul`, `Algebra.trace_eq_of_algEquiv` | `gapsw7_x3x_trace_baseChange` / `…_decomposition_of_prod_iso` | `Mathlib/LinearAlgebra/Trace.lean`, `Mathlib/Algebra/Algebra/TensorProduct.lean` |
| `Ideal.quotientInfToPiQuotient_surj`, `Ideal.quotientInfToPiQuotient_mk'`, `Ideal.isCoprime_of_isMaximal`, `RingHom.ker_isMaximal_of_surjective`, `Ideal.Quotient.mk_surjective`, `Ideal.Quotient.eq` | the distinct-kernel CRT surjectivity | `Mathlib/RingTheory/Ideal/Quotient/Operations.lean`, `Mathlib/RingTheory/Ideal/Maximal.lean` |
| `Module.finrank_pi_fintype`, `Module.finrank_tensorProduct`, `Module.finrank_self`, `LinearMap.injective_iff_surjective_of_finrank_eq_finrank` | the `finrank` sandwich | `Mathlib/LinearAlgebra/Finrank/Pi.lean`, `…/TensorProduct.lean`, `…/LinearMap.lean` |
| `Ideal.quotientKerAlgEquivOfSurjective`, `Ideal.Quotient.liftₐ`, `Ideal.Quotient.lift_mk`, `AlgEquiv.symm_apply_apply`, `minpoly.algHom_eq` | the induced residue/spectral equiv `σ` | `Mathlib/RingTheory/Ideal/Quotient/Operations.lean`, `Mathlib/FieldTheory/Minpoly/Basic.lean` |
| `spectralNorm_unique_field_norm_ext`, `Real.one_lt_rpow_iff_of_pos`, `Real.rpow_le_rpow`, `Real.one_rpow`, `Valued.toNormedField.norm_le_one_iff` | the absolute-value/norm comparison | `Mathlib/Analysis/Normed/Unbundled/SpectralNorm.lean` |
| `Algebra.IsAlgebraic.of_finite`, `IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm`, `Valuation.norm_add_le` | the spectral setup | `Mathlib/FieldTheory/IsAlgClosed/Basic.lean` etc. |
| `Ideal.ramificationIdx_spec`, `Ideal.inertiaDeg_algebraMap`, `Ideal.ramificationIdx_mul_inertiaDeg_of_isLocalRing` | the two completion comparisons | `Mathlib/NumberTheory/RamificationInertia/*` (§7 drift) |
| `IsIntegralClosure.isNoetherian`, `Module.IsNoetherian.finite`, `IsLocalRing.local_hom_TFAE`, `IsLocalRing.isField_iff_maximalIdeal_eq`, `IsDiscreteValuationRing.not_isField` | the `finrankCompletionEF` discharge | `Mathlib/RingTheory/IntegralClosure/IsIntegralClosure/*`, `…/LocalRing/Basic.lean` |
| `Polynomial.lifts_and_degree_eq_and_monic`, `spectralValue_le_one_iff`, `Polynomial.lifts_iff_coeff_lifts`, `isIntegral_algHom_iff`, `Valuation.Integers.isIntegrallyClosed` | `kw_ffgc_isIntegralClosure_adicCompletionIntegers` (already in `TraceCompat`) | reused |
| `AlgebraicCurve.Place.sum_ramificationIndex_mul_inertiaDeg_fiberOver` | the port's `SumRamificationInertia` producer | `WeilExchange/FiberOverCount.lean:33` (public) |
| `ModularCurve.KwF4R1V410a.kwF4R1V410a_quotientEquiv` | the residue-field comparison (Correction 3) | `Tate/CommFinite.lean:541` (public) |
| `Ideal.quotEquivOfEq` | the two `pow_one` bridges | `Mathlib/RingTheory/Ideal/Quotient/Operations.lean` |

`#check` output confirmed each has the pin's type at the pin's binders. No substitute
needed a binder change.

## 4. GENERALISE rows

None. Every shared last name is byte-identical in statement between the pin's
`completionTraceSum` copy and the port's `TraceCompat` copy (verified textually by
extracting each declaration block from both pin files and diffing); the only differences
are proof-body spellings (`map_zero` vs `_root_.map_zero`) and blank lines, which the
checker ignores for `private` rows.

## 5. Re-landed `private` pieces and promotion debt

**InlineSpecific uniformizer slice** (pin
`Definitions/Def_DedekindDomain_AdicValuation_InlineSpecific.lean`), re-landed `private`
verbatim because the port's `Tate/CommFinite.lean` copies are module-local and do not
cross an import:

| pin ln | row |
|---:|---|
| 299 | `IsDedekindDomain.HeightOneSpectrum.completionIdeal` (abbrev) |
| 302 | `…HeightOneSpectrum.mem_completionIdeal_iff` |
| 430 | `…HeightOneSpectrum.adicCompletion.exists_uniformizer` |
| 438 | `…uniformizer_ne_zero` |
| 447 | `…uniformizer_not_isUnit` |
| 455 | `…isUnit_adicCompletionIntegers_of_valued_eq_one` |
| 464 | `…eq_pow_uniformizer_mul_unit` |
| 513 | `…maximalIdeal_eq_span_uniformizer` |
| 525 | `…mem_completionIdeal_pow` |

Named future home: `Place/Completion.lean` (P3.3a review, PLAN-P3-3 pause debt item 3).
These are new debt added by 3.4b (the P3.3a copies are the same debt, carried in
`Tate/CommFinite.lean:82–208`); the refactor round that opens `Place/Completion.lean`
should absorb both.

**NOT promoted:** `ResidueFieldEquivCompletionResidueField` and its density chain
(InlineSpecific pin 167/223/262/277/318/325) — replaced by the public
`kwF4R1V410a_quotientEquiv` route (Correction 3). Recorded as a route win, not debt.

## 6. Reuse wins, route options, and the checker delta

**Route win (measured).** Correction 3 removes ~130 pin lines (the InlineSpecific
density chain) from the port at no statement cost: the two residue fields are
definitionally quotients of `toValuationSubring` / `adicCompletionIntegers` by their
maximal ideals, and the port already has the ring isomorphism between the `n`-th
quotients.

**Refactor finding (Correction 2).** `Tate/Agreement.lean` lost 22 public duplicate
declarations and imports `Prelude`/`TraceCompat`. Acceptance condition met: importing
`Prelude` + `ChainRule` + `Agreement` + `TraceCompat` in one module compiles (0
collisions — `lake env lean` exit 0 on the probe; the whole-tree build then rebuilt
dependent-free leaves). The `PORT_FILES` note records the refactor at
`FLTForHuman/AlgebraicCurve/Tate/Agreement.lean`'s registration.

**Checker delta.** **4044 → 4010 identical** (4074 → 4040 checked), still **0
mismatched / 0 missing / 30 own-proof**. The −34 is the de-dup arithmetic: the refactor
de-registered 37 Agreement declarations the checker had been counting (all still
supplied by `Prelude`/`TraceCompat`), and the two new modules added 3 public rows
(`kwF4gRRTate_RTCC_of_tate`, `residueTraceCompletionCommute`,
`completionTraceSum_of_isSeparable`); 3 of the 40 deleted were forms the checker's
`raw_declarations` did not count. The `promoted` count is unchanged at 135.

**`#print axioms`** on the three public nodes (scratch, deleted):
`AlgebraicCurve.residueTraceCompletionCommute`,
`ModularCurve.KwF4gRRTate.kwF4gRRTate_RTCC_of_tate`,
`AlgebraicCurve.completionTraceSum_of_isSeparable` each report
`[propext, Classical.choice, Quot.sound]`.

## 7. API drift (`v4.34.0`) — what the worker changed

| pin call / assumption | `v4.34.0` status | worker action |
|---|---|---|
| `Pi.algHom R _ f` (`kwF4R1V384a_semilocalDiag`) | deprecated: use `AlgHom.pi` | kept the pin's call under a file-scope `linter.deprecated false` (private row; the deprecation warning is benign). A future cleanup can switch to `AlgHom.pi`. |
| `Ideal.ramificationIdx_mul_inertiaDeg_of_isLocalRing` | deprecated ("use results of `RingTheory.RamificationInertia.Basic`") but still present only in the deprecated import `Mathlib.NumberTheory.RamificationInertia.Basic`; the new module `Mathlib.RingTheory.RamificationInertia.Basic` has the sum form `Ideal.sum_ramification_inertia_eq_finrank` but no local-case product | imported the deprecated module, used the deprecated lemma under `linter.deprecated false`. Recorded residual: a later round can re-derive the local product from `Ideal.sum_ramification_inertia_eq_finrank` and drop the deprecated import. |
| `Ideal.inertiaDeg'`, `Ideal.inertiaDeg_algebraMap` | deprecated (`inertiaDeg'` → `inertiaDeg`; `inertiaDeg_algebraMap` → `inertiaDeg'_algebraMap` — the two aliases cross) | kept the pin's text on the private statements/proofs (deprecated names are what the pin S file spells), suppressed with `linter.deprecated false`, as `Defs/PlaceDictionary.lean` does. |
| `Ideal.ramificationIdx_spec` | deprecated | kept (private proof step). |
| `TFAE.out 0 4` (pin's `local_hom_TFAE`) | `TFAE.out` is 1-based in v4.34 (playbook §7) | **`.out 1 5`**. |
| pin `set_option maxHeartbeats 6400000/16000000`, `synthInstance.maxHeartbeats 3200000/8000000` | project cap `maxHeartbeats := 4_000_000` | dropped the `maxHeartbeats` raises; kept a local `synthInstance.maxHeartbeats 800000` where the port's instance search needs headroom (the `finrank`/`pi` synthesis), matching `Defs/PlaceCompletion.lean`. |
| `Tactic \`introN\` / `RingHom.ker f` vs `.toRingHom` mismatch in `kwF4R1V386a_distinctKernels` | the pin's `erw [hstep1, Ideal.Quotient.lift_mk]` is not type-correct at v4.34's `implicit` transparency (the AlgHom-coercion `RingHom.ker` differs from `.toRingHom`) | wrapped the proof in `set_option backward.isDefEq.respectTransparency false in` (the same device the pin uses on `kwF4R1V386a_integersToCompletion_commute`). |
| `Place.sum_ramificationIndex_mul_inertiaDeg` (a pin theorem) | the port's producer is the class field `SumRamificationInertia.sum_ramificationIndex_mul_inertiaDeg`, whose class parameters are plain implicit (Correction 4) | supplied the parameters with `@…`; re-landed the port's `private` `SumRamificationInertia` producer (`Genus/Stichtenoth.lean`'s is `private`) over the public `Place.sum_ramificationIndex_mul_inertiaDeg_fiberOver`. |

## 8. Recorded negatives

1. **No `ResidueFieldEquivCompletionResidueField` (or an equivalent completion residue
   field isomorphism) in mathlib `v4.34.0` or the pre-3.4 port.** `grep -rn "ResidueFieldEquiv" FLTForHuman/` finds none; mathlib's `DedekindDomain/AdicValuation.lean` has no
   residue-field comparison. The port reaches it via `kwF4R1V410a_quotientEquiv` at
   `n = 1` (Correction 3); do not re-search mathlib.
2. **No mathlib local-case `ramificationIdx' * inertiaDeg' = finrank`** in the new
   `Mathlib.RingTheory.RamificationInertia.Basic` (only the `primesOver` sum);
   `Ideal.ramificationIdx_mul_inertiaDeg_of_isLocalRing` lives only in the deprecated
   module (§7).
3. **No `HeightOneSpectrum.completionIdeal`, `…adicCompletion.exists_uniformizer`,
   `…maximalIdeal_eq_span_uniformizer`, `…mem_completionIdeal_pow` or
   `…mem_completionIdeal_iff` in mathlib** — pin-local InlineSpecific rows, re-landed
   `private` (§5). The P3.3a audit's probe N recorded the same negatives.
4. **The three `def … : Prop` "in-port" hits are false positives** (Correction 1); the
   `port_advise` `def`-body blind spot's attractor is `EisensteinWeightOne.E1Chi3IsModular`.
5. **The `Agreement` collision is real and was missed by both the P3.3 detector and the
   checker's namespace-qualified fallback** (Correction 2). The checker's last-name
   matching is immune (it never needed Agreement's copies), which is why the checker was
   green while the module could not be imported with its siblings.
6. **`SumRamificationInertia`'s class parameters are not instance-implicit**
   (Correction 4); a `(K := …) (F := …) (F' := …)` call does not synthesize them.

## 9. What this changes for the P3.4 review

**Scope.** 3.4a is 8 public rows (6 imported, 2 landed) — the pin's 1,109 lines are
almost entirely `p2m_*` scaffolding and empty sections. 3.4b is 1 public + 25 new
`private` rows (13 imported from `TraceCompat`, 3 `Prop` mints, 8 InlineSpecific
uniformizer rows, the residue comparison via `quotientEquiv`, the tensor-trace engine,
the semilocal `finrank` sandwich and the discharge). Measured written:
`Tate/TraceCompletionCommute.lean` 156 ln, `Tate/CompletionTraceSum.lean` 824 ln.

**Undischarged rows.** None of this set: both targets are unconditional given the pin
binders, and the checker is `0 missing`. The two row-2 headlines of set 3.2g
(`trace_localResidue_finitePlace_div_pow_eq_zero`,
`residueTheorem_ratFunc_of_perfectField`) are now unblocked — they consume
`residueTraceCompletionCommute` (`P1/DivPow.lean`'s comment names the dropped `_v2`
spelling; the gated re-dispatch must use the surviving name).

**Promotion debt.** §5's nine InlineSpecific rows (new copies in
`Tate/CompletionTraceSum.lean`, future home `Place/Completion.lean`), plus the
pre-existing `Tate/CommFinite.lean` and `Tate/Agreement.lean` copies of the same slice.
The `P1/DivPow.lean` private `kwHgfV352_localResidueCompletion` / public `_spec` /
`_algebraMap` split (P3.3 pause debt item 2) is unchanged by this set.

**Residual.** The deprecated `Mathlib.NumberTheory.RamificationInertia.Basic` import
(§7) is the one wart; it is local to 3.4b's private proof and can be retired when the
InlineSpecific debt round opens `Place/Completion.lean`.
