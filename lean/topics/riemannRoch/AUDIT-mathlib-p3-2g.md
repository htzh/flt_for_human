# Mathlib-first substitution audit — P3.2g, the two gated row-2 ℙ¹ headlines

**Method:** [`lean/porting-playbook.md`](../porting-playbook.md) §2.2 (audit the route,
mathlib first), after the phase-1/2/3.1/3.2a–3.2f/3.3a–3.3d/3.4 templates
[`AUDIT-mathlib.md`](AUDIT-mathlib.md) … [`AUDIT-mathlib-p3-4.md`](AUDIT-mathlib-p3-4.md).
Pin: `anthropics/fermats-last-theorem@aa2d8b3` (read-only clone at
`~/proj/fermats-last-theorem`); port mathlib `v4.34.0`
(`lean/.lake/packages/mathlib`). Measurement:
[`tools/deps/build/p32g_advise.log`](../../../tools/deps/build/p32g_advise.log) and its
`.json`, from

```bash
python3 port_advise.py \
  --target P2M/Sol/S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.lean \
  --target P2M/Sol/S_AlgebraicCurve_residueTheorem_ratFunc_of_perfectField.lean \
  --json build/p32g_advise.json > build/p32g_advise.log
```

**Sources.** The two gated row-2 headlines, whose port homes are
`FLTForHuman/AlgebraicCurve/P1/DivPowEnding.lean` (3.2g-a) and
`FLTForHuman/AlgebraicCurve/P1/PerfectBase.lean` (3.2g-b):

- [`P2M/Sol/S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.lean)
  (2,150 ln) — the atom-3 headline `P1Tower.trace_localResidue_finitePlace_div_pow_eq_zero`
  (lines 2016–2138) and its public wrapper (2140–2150), at the wrapper
  [`Thm_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.lean)
  binders. Everything below line 2016 is already `P1/DivPow.lean` (set 3.2f).
- [`P2M/Sol/S_AlgebraicCurve_residueTheorem_ratFunc_of_perfectField.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_residueTheorem_ratFunc_of_perfectField.lean)
  (4,340 ln) — the perfect-field base case, statement authority
  [`Thm_AlgebraicCurve_residueTheorem_ratFunc_of_perfectField.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_AlgebraicCurve_residueTheorem_ratFunc_of_perfectField.lean).
  Its 38-declaration tail (3574–4340) is new; the preceding ~3,500 lines are the sibling
  prelude already carried by the `P1/` chain.

**Baseline (pre-3.2g).** Checker **4010 identical / 0 mismatched / 0 missing / 30
own-proof** (4040 checked), after sets 3.2f and 3.4. Prerequisites landed by 3.4 and used
here: `AlgebraicCurve.residueTraceCompletionCommute`
(`Tate/TraceCompletionCommute.lean`) and
`AlgebraicCurve.completionTraceSum_of_isSeparable`
(`Tate/CompletionTraceSum.lean`). The pin calls the `_v2` twin of the first; the port uses
the surviving name (the `_v2` spelling was dropped, PORTING-RR §3 name policy).

**Scratch evidence.** A probe (`ScratchP32gCheck.lean`, gitignored, deleted) compiled from
`lean/` with

```bash
timeout 500 lake env lean -DmaxHeartbeats=4000000 -DautoImplicit=false ScratchP32gCheck.lean
```

**final run clean, exit 0**, `#check`ing the mathlib leaves and the imported substitutes
listed in §3–§4. The two modules themselves were edit-loop checked with the same options.

## 1. Summary — class counts

`port_advise` reads 4 targets (the two `S_` files and their two `Thm_` wrappers) with 230
declarations, and reports 154 "already in port" (147 public importable, 7 only as
port-private), 12 in-target binder variants and 34 already-in-port-different-statement rows.

| file | rows | SUBSTITUTE | ADAPT (placeInfty twins) | NEW |
|---|---:|---:|---:|---:|
| atom 3 `DivPowEnding` (tail 2016–2150) | 2 | 0 | 0 | 2 |
| pfbase `PerfectBase` (tail 3574–4340) | 42 | 4 | 27 | 11 |
| **total** | **44** | **4** | **27** | **13** |

"NEW" counts *new public declarations still to land*: atom 3's `P1Tower` headline + the
wrapper (2); pfbase's 38-declaration tail minus the `P1PrincipalPartTwoPlaceCancelMOne`
`def` (already in `P1/TwoPlace.lean`), minus the four perfect-field profile rows already in
`P1/PerfectField.lean`, minus the `scoped instance` and the wrapper counted with the
`solution` = 37 in `P1/PerfectBase.lean`. The port gained **39** checked rows (2 + 37).

**Headline.** Neither file is new mathematics. Atom 3 is a 120-line proof carried at the
pin's text against the `P1/DivPow.lean` tower and set-3.4 Tate engine; pfbase is the pin's
`K →ₗ[K] K` residue functional, its kernel, the generator/partial-fraction decomposition and
the `MOne`/`MGeTwo` reduction, all over the already-ported `P1/` API, ending in the two
3.2f headlines. The only non-`rfl` adaptation is the `placeInfty`/`p1PlaceInfty` alias.

## 2. Corrections to the measurement

**Correction 1 — the `def … : Prop` "in-port" hits are the known body blind spot.**
`port_advise` matches `P1PrincipalPartTwoPlaceCancelMOne` (pfbase 3946) to
`FLT.AlgebraicCurve.P1DifferentialCoeffRegularFinite` and `OrdDifferentialWellDefined`
(pfbase 300) to `EisensteinWeightOne.E1Chi3IsModular`. Verified by last name: the real port
homes are `AlgebraicCurve.P1PrincipalPartTwoPlaceCancelMOne` (`P1/TwoPlace.lean:34`, imported
here) and `AlgebraicCurve.OrdDifferentialWellDefined` (`P1/EnginePrelude.lean:102`). The
`def`-body blind spot's attractors are unchanged from 3.2f/3.4.

**Correction 2 — the pin's `scoped instance`s are invisible to `port_advise` and the
checker.** The pfbase instance layer is `instFormallyEtalePolynomialRatFunc` (pin 3542),
`kaehlerRatFuncBasis` (3549) and `instNontrivialKaehlerRatFunc` (3555); the port has the
first two (`P1/UnitFinite.lean:46/49`) and the `scoped instance (priority := low)
instDCoordGeneratesPerfectField` (`P1/PerfectField.lean:52`). `instNontrivialKaehlerRatFunc`
is **not** re-declared here: the pfbase tail carries `[Nontrivial Ω[(RatFunc K)⁄K]]` as a
section variable / wrapper binder throughout, so the instance is never needed. The pin's
`RationalFunctionField.hasPrincipalDivisors` is the port's scoped instance
`instHasPrincipalDivisors` (`P1/Differential.lean:20`), also checker-invisible.

**Correction 3 — `D_ratFuncX_ne_zero` has two distinct pin copies.** Atom 3's copy
(1996, inside `P1Tower`) is hypothesis-free; pfbase's (4093) takes
`(hwd : OrdDifferentialWellDefined K (RatFunc K))`. They live in different namespaces
(`AlgebraicCurve.P1Tower.` vs `AlgebraicCurve.`) and are **not** a substitution: the port
has both (`P1/DivPow.lean` and `P1/PerfectBase.lean`). `port_advise`'s
"already in port under a different statement" row is the namespace-free last-name collision,
not a match.

## 3. SUBSTITUTE rows, with `#check` evidence

All rows below are imported, never re-proved. The `#check` run of `ScratchP32gCheck.lean`
confirmed each has the pin's type at the pin's binders.

### 3.1 the set-3.4 Tate engine (atom 3)

| pin row | substitute | note |
|---|---|---|
| `residueTraceCompletionCommute_v2` | `AlgebraicCurve.residueTraceCompletionCommute`, `Tate/TraceCompletionCommute.lean:138` | surviving name; `_v2` dropped |
| `completionTraceSum_of_isSeparable` | `AlgebraicCurve.completionTraceSum_of_isSeparable`, `Tate/CompletionTraceSum.lean:815` | same binders |
| `kwHgfV352_completionTraceAt` | `AlgebraicCurve.kwHgfV352_completionTraceAt`, `Defs/TateResidueCurrency.lean` | shared def |
| `Place.CanonicalLocalResidueDataK.res_differentialCoeff_D_mul_pow_inv_eq_zero_of_surjective_algebraMap` | `AlgebraicCurve.Place.CanonicalLocalResidueDataK.…`, `LocalResidue/Calculus.lean` | public |
| `ag9b13e_differentialCoeff_D_mem_of_mem_of_perfectField` | same name, `P1/Core.lean:86` | public |
| `finrank_eq_one_iff_of_nonzero'`, `finsum_eq_finsetSum_of_support_subset`, `Finset.sum_pair`, … | mathlib `v4.34.0` | §5 |

### 3.2 the perfect-field profile (pfbase)

| pin row (ln) | substitute | note |
|---|---|---|
| `p1DifferentialCoeffUnitFinite_dX_of_perfectField` (4229) | same name, `P1/PerfectField.lean:73` | public |
| `p1DifferentialCoeffRegularFinite_dX_of_perfectField` (4238) | same name, `P1/PerfectField.lean:82` | public |
| `exists_ne_zero_smul_dX_of_uniformizer` (4191) | same name, `P1/PerfectField.lean:34` | public |
| `scoped instance instDCoordGeneratesPerfectField` (4211) | same name, `P1/PerfectField.lean:52` | scoped, elaboration-only |
| `P1PrincipalPartTwoPlaceCancelMOne` (3946) | `AlgebraicCurve.P1PrincipalPartTwoPlaceCancelMOne`, `P1/TwoPlace.lean:34` | `def : Prop`, statement verbatim |

`P1PrincipalPartTwoPlaceCancelMOne`'s effective signature from `#check` is
`(K) [Field K] [DecidableEq (RatFunc K)] [HasCanonicalLocalResidueKStar K (RatFunc K)]
{ω₀} (hω₀) → Prop` — exactly the pin's. The pfbase section's extra
`[HasCanonicalDivisor]`/`[Nontrivial Ω]`/`[HasPrincipalDivisors]` are not used by the body
and so are not bound by the port copy either.

### 3.3 the `p1PlaceInfty` twins (27 ADAPT rows, from the 3.2f audit §3.2)

The pfbase prelude repeats the master engine under the pin's `placeInfty` spelling; the port
has it under `p1PlaceInfty`, with
`RationalFunctionField.placeInfty_eq_p1PlaceInfty : placeInfty K = p1PlaceInfty K` by `rfl`
(`P1/Core.lean`). The new module states every new declaration at the pin's `placeInfty`
(so the checker text is verbatim) and the proofs use the port's `p1PlaceInfty`-stated lemmas
by definitional equality:

| pin row | port home |
|---|---|
| `pow_X_mul_mem_of_ne_placeInfty` | `P1/EnginePrelude.lean:402` (at `p1PlaceInfty`) |
| `p1PrincipalPartAtom_mem_of_ne_finitePlace` | `P1/UnitNormalForm.lean:346` (at `p1PlaceInfty`) |
| `finitePlace_ne_placeInfty` | `P1/EnginePrelude.lean:445` (at `p1PlaceInfty`) |
| `two_le_ord_placeInfty_p1PrincipalPartAtom` | `P1/DivisorAction.lean:397` (at `p1PlaceInfty`) |
| `ordDifferential_placeInfty_D_ratFuncX` | `P1/Differential.lean:93` (at `p1PlaceInfty`) |
| `placeInfty_ne_ofHeightOneSpectrum`, `eq_ofHeightOneSpectrum_or_eq_placeInfty`, `ord_placeInfty`, `ord_placeInfty_X`, … | `PrincipalDivisors/RatFuncDegree.lean`, `P1/Dictionary.lean` |

No row needed an explicit `rw [RationalFunctionField.placeInfty_eq_p1PlaceInfty]`: the
`p1PlaceInfty` def is `@[reducible]`, so the alias is transparent to elaboration and to the
proofs' `rw`/`omega` steps. `p1OrdDifferentialPlaceInftyEqNegTwo_D_X`'s pin proof is the
one-line `ordDifferential_placeInfty_D_ratFuncX K hwd`, which type-checks directly at the
`placeInfty` goal.

## 4. KEEP/NEW rows and how they are discharged

### 4.1 atom 3 — the headline (pin 2016/2140)

`P1Tower.trace_localResidue_finitePlace_div_pow_eq_zero` (pin 2016–2138) is the pin's
proof carried verbatim, with two adaptations: the set-3.4 substitute for
`residueTraceCompletionCommute_v2`, and the private bridge for the public
`kwHgfV352_localResidueCompletion` (`§6`). The wrapper (pin 2140) is a one-line application
at the `Thm_` binders. `D_ratFuncX_ne_zero`, `gen`, `minP`, `pbGen`, the valuation
dictionary and `trace_mul_inv_derivative` are all imported from `P1/DivPow.lean`.

### 4.2 pfbase — the 37-row tail

| group | rows (pin ln) | discharge |
|---|---|---|
| scalar/dual reduction, kernel vocabulary | 3574–3668 (`kaehlerResidueTerm_smul_left`, `weilSmul_weilOfKaehler`, `weilOfKaehler_smul_diagonal`, `residueTheorem_iff_of_ne_zero`, `kaehlerResidueFunctional/Kernel`, the span/kernel corollaries) | `Finsupp`/`LinearMap`/`Submodule` glue over the ported `weilOfKaehler`/`weilSmul`/`principalAdele` |
| ℙ¹ named rows | 3682–3723 (`P1PartialFractionSpan`, `P1ResiduePolynomialPart`, `P1ResiduePrincipalPart`, `…of_partialFractions`, `…of_generators_residue`) | the ported `P1*Generators` and `p1PartialFractionSpan_eq_top` |
| kernel/support lemmas | 3752–3777 (`…_iff_finsum`, `…_of_term_zero_compl`, `…_of_singleton`, `…_of_pair`) | `finsum_eq_finsetSum_of_support_subset`, `Finset.sum_pair` |
| named subrows | 3804–3921 (`P1PolynomialResidueAtInfinity`, `P1PrincipalPartTermZeroOffSupport`, `P1PrincipalPartTwoPlaceCancel`, the three composed theorems) | the ported `kaehlerResidueTerm_eq_zero_of_ord_nonneg` + the p1-place twins |
| `MOne`/`MGeTwo` reduction | 3943–4156 (`P1OrdDifferentialPlaceInftyEqNegTwo`, `kaehlerResidueTerm_placeInfty_eq_zero_of_two_le_m`, `P1FinitePlaceTermZeroMGeTwo`, `P1PrincipalPartTwoPlaceCancelMOne` (imported), `p1PrincipalPartTwoPlaceCancel_of_mOne`, `D_ratFuncX_ne_zero`, `p1OrdDifferentialPlaceInftyEqNegTwo_D_X`, `p1PrincipalPartTwoPlaceCancel_dX_of_mOne_mGeTwo`) | `two_le_ord_placeInfty_p1PrincipalPartAtom`, `ordDifferential_placeInfty_D_ratFuncX`, `D_ratFuncX_eq_neg_X_sq_smul_D_inv`, `D_ratFuncX_inv_ne_zero` |
| perfect-field specialisations | 4281–4340 (`…of_two_subrows_of_perfectField`, `…of_mOne_mGeTwo_of_perfectField`, the wrapper) | the imported perfect-field profile + the two 3.2f headlines |

## 5. Mathlib ledger (all confirmed in `v4.34.0`)

| constant | role |
|---|---|
| `finrank_eq_one_iff_of_nonzero'` | the `deg = 1 ⇒ algebraMap` surjectivity re-land |
| `finsum_eq_finsetSum_of_support_subset`, `Finset.sum_pair`, `Finset.sum_eq_single_of_mem`, `Finset.mem_attach` | the kernel/support and singleton-sum steps |
| `Submodule.{span_le, eq_top_iff'}`, `top_unique`, `Set.union_subset` | `residueTheorem_of_{span,union_span}_le_kernel` |
| `LinearMap.{ext, ker}`, `Submodule.mem_span_singleton` | the functional/kernel definition |
| `Polynomial.{rootMultiplicity_X_sub_C, natDegree_lt_natDegree}`, `IsCoprime`, `isCoprime_zero_right` | atom-3's `hP'0`, `hc'`, `htord` |
| `Derivation.map_aeval`, `KaehlerDifferential.map_D` | atom-3's `hcotr` |
| `map_ne_zero_iff`, `IsFractionRing.injective`, `smul_ne_zero_iff`, `neg_ne_zero`, `pow_ne_zero` | atom-3's non-vanishing steps |
| `RatFunc.{X_ne_zero, algebraMap_X}`, `Nat.lt_or_ge`, `Subtype.ext`, `congrArg` | assorted |

No substitute needed a binder change.

## 6. Re-landed `private` pieces and promotion debt

| pin row | pin ln | why re-landed | new home |
|---|---:|---|---|
| `private def gen` | 1446 | module-local in `P1/DivPow.lean:104`; atom-3's proof names it | `P1/DivPowEnding.lean` |
| `kwHgfV352_localResidueCompletion_spec` | 1949 | `P1/DivPow.lean`'s public copy is about that module's `private` def; the Defs public def needs its own bridge | `P1/DivPowEnding.lean` (`…_spec₀`) |
| `kwHgfV352_localResidueCompletion_algebraMap` | 1966 | ditto | `P1/DivPowEnding.lean` (`…_algebraMap₀`) |
| `surjective_algebraMap_residueField_of_deg_eq_one` | 1325 | the port's public copy (`P1/KaehlerIntegral.lean:474`) carries `[CharZero K] [HasCanonicalLocalResidueKStar K (RatFunc K)]` from its `AlgClosedDischarge` section; the atom-3 context has no `CharZero K`, so the pin's copy is re-landed `private` | `P1/DivPowEnding.lean` (`…_of_deg_eq_one'`) |

These are promotion debt, named home `Place/Completion.lean` for the completion-residue pair
(the P3.3 pause item 2 / P3.3a §3.5 debt), and `P1/DivPow.lean` for `gen` / the surjectivity
lemma. `ord_add_eq_min`/`ord_add_eq_left`, `algebraMap_ne_zero`, `isIntegral_gen`,
`ord_neg'` and `uniformizer_ne_zero'` are port-`private` per `port_advise` but were **not**
consumed by either tail, so nothing was re-landed for them.

## 7. Route options and reuse wins

- **R1 — the atom-3 headline is transcription.** The pin's 120-line proof is carried at the
  pin's text; the only port-specific input is the surviving
  `residueTraceCompletionCommute`. Carrying the pin's `placeInfty` spelling and letting
  defeq bridge to the `p1PlaceInfty` engine avoids the whole alias table.
- **R2 — `P1PrincipalPartTwoPlaceCancelMOne` is imported, not re-declared.** The
  `port_advise` `def` false positive would have produced a duplicate-declaration error.
- **R3 — the pfbase reduction is pure `Submodule`/`LinearMap` order theory.** Every non-`def`
  row is `Submodule.{span_le, eq_top_iff'}`, `LinearMap.{ext, mem_ker}`,
  `finsum_eq_finsetSum_of_support_subset`, `Finset.sum_pair`; no mathlib gap.
- **R4 — the perfect-field profile is imported.** `p1DifferentialCoeff*_dX_of_perfectField`
  and the `DCoordGenerates` instance are `P1/PerfectField.lean`'s; pfbase only consumes them.

## 8. API drift (`v4.34.0`) — what the worker changed

| pin call / assumption | `v4.34.0` status | worker action |
|---|---|---|
| `residueTraceCompletionCommute_v2` | dropped twin | use `residueTraceCompletionCommute` (surviving name) |
| `RationalFunctionField.hasPrincipalDivisors` | the port's scoped instance `instHasPrincipalDivisors` (`P1/Differential.lean:20`) | `haveI hPD := instHasPrincipalDivisors` |
| `surjective_algebraMap_residueField_of_deg_eq_one` without `CharZero` (atom-3 pin 1325) | port's public copy has the `AlgClosedDischarge` `[CharZero K]` binder | re-land the pin's copy `private` (`…_of_deg_eq_one'`) |
| `private def gen` (pin 1446) | module-local in `P1/DivPow.lean` | re-land `private` verbatim |
| `kwHgfV352_localResidueCompletion_{spec,algebraMap}` about the Defs def | port copies are about `P1/DivPow.lean`'s `private` def | re-land `private` `…_spec₀`/`…_algebraMap₀` (mirrors `Tate/Agreement.lean:907/928`) |
| `if_pos` (atom-3 `htord`) | deprecated in favour of `ite_eq_left` | kept the pin text; benign deprecation warning |
| `P1OrdDifferentialPlaceInftyEqNegTwo K`, `P1FinitePlaceTermZeroMGeTwo K`, `residueTheorem_ratFunc_of_three_subrows K` calls | the pin's section has explicit `(K)` | made the corresponding sections' `K` explicit; the statement text is unchanged |

The build is otherwise warning-noise only: the `linter.style.haveILetI` suggestions on the
pin's `haveI`s and a handful of unused-section-variable / overlapping-instance warnings from
the port's section-variable spelling. No `sorry`/`admit`/`axiom`/bare `import Mathlib`; no
heartbeat raise.

## 9. Recorded negatives

1. **No mathlib declaration lets any of the 39 new rows be dropped.** Every new name is
   either a bespoke `def : Prop` over pin vocabulary (`kaehlerResidueFunctional`,
   `kaehlerResidueKernel`, `P1PartialFractionSpan`, `P1ResiduePolynomialPart`,
   `P1ResiduePrincipalPart`, `P1PolynomialResidueAtInfinity`,
   `P1PrincipalPartTermZeroOffSupport`, `P1PrincipalPartTwoPlaceCancel`,
   `P1OrdDifferentialPlaceInftyEqNegTwo`, `P1FinitePlaceTermZeroMGeTwo`) or a statement over
   pin vocabulary (`ResidueTheorem`, `kaehlerResidueTerm`, `weilOfKaehler`,
   `p1PrincipalPartAtom`, `placeInfty`). Mathlib supplies the leaves (§5) only.
2. **The `def … : Prop` "in-port" hits are false positives (Correction 1).** The
   `port_advise` `def`-body blind spot's attractors are `FLT.AlgebraicCurve.P1DifferentialCoeffRegularFinite`
   and `EisensteinWeightOne.E1Chi3IsModular`.
3. **`D_ratFuncX_ne_zero` is not a substitution (Correction 3):** atom 3's hypothesis-free
   `P1Tower` copy and pfbase's `hwd`-taking copy are distinct statements.
4. **`scoped instance` rows are invisible to both `port_advise` and the checker
   (Correction 2):** `instNontrivialKaehlerRatFunc` was not needed (the tail takes
   `[Nontrivial Ω[(RatFunc K)⁄K]]`); `instDCoordGeneratesPerfectField` and
   `instHasPrincipalDivisors` are imported/`inferInstance`.
5. **No mathlib "residue functional kernel" abstraction exists.** The pfbase kernel is the
   `LinearMap.ker` of the pin's own `weilOfKaehler ∘ principalAdele`; the whole
   `residueTheorem_iff_kaehlerResidueKernel_eq_top` route is pin-specific.
6. **The port's public `surjective_algebraMap_residueField_of_deg_eq_one` cannot be used
   without `CharZero K`** even though the pin's atom-3 copy is `CharZero`-free; the pin's
   copy is re-landed `private` (§6). A later refactor can widen the public copy by splitting
   its `AlgClosedDischarge` section.

## 10. What this changes for the P3.2g review

**Scope.** `P1/DivPowEnding.lean` 254 ln / 2 checked rows; `P1/PerfectBase.lean` 528 ln /
37 checked rows. Checker **4010 → 4049 identical** (4040 → 4079 checked), still **0
mismatched / 0 missing / 30 own-proof** — the +39 is exactly the two modules' public
surface. Row 2 (set 3.2) is mathematically complete: the three ℙ¹ `trace_localResidue_*`
atoms and `residueTheorem_ratFunc_of_perfectField` all exist.

**Undischarged rows.** None in this set. Both headlines are unconditional at the pin
binders; the checker reports `0 missing`. `#print axioms` on both headlines and on all ten
new `def : Prop`s returns `[propext, Classical.choice, Quot.sound]`.

**Promotion debt.** §6's four re-landed `private` rows; the pre-existing
`P1/DivPow.lean` private `kwHgfV352_localResidueCompletion` / public `_spec`/`_algebraMap`
split (P3.3 pause item 2) is unchanged and blocks a clean single-def refactor.

**SOURCES / PORT_FILES.** The four P3.2f source entries (two `Thm_` wrappers, two `S_`
files) were already appended by 3.2f and are live again; `PORT_FILES` gains
`P1/DivPowEnding.lean` and `P1/PerfectBase.lean` last.
