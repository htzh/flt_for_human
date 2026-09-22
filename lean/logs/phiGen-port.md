# The Φₚ splitting / R1 sub-effort — record

**Status: T5–T9 complete (2026-09-22) — R1 is complete, the cone's (c) is
discharged, and the cone's (b) has its integrality half.** This is the running
record for the sub-effort
[PORTING-PhiGen.md](../PORTING-PhiGen.md) opens: the R1 (level-one q-expansion
principle) sequence that gives the Φₚ splitting cone its one analytic input. It is
separate from the parent `functionFieldGeneration` record ([ffg-port.md](ffg-port.md))
— the parent's cone and this sub-effort share no declaration, and the
sub-effort's topics are not on `ffg-port.md`'s layer table, so the measured cost
lives here rather than as an append there.

The executed plans are
[TOPIC-r1-kernel.md](../topics/phiGenSplitting/TOPIC-r1-kernel.md) (T5),
[TOPIC-jq-model.md](../topics/phiGenSplitting/TOPIC-jq-model.md) (T6),
[TOPIC-hauptmodul.md](../topics/phiGenSplitting/TOPIC-hauptmodul.md) (T7),
[TOPIC-phiGen-descends.md](../topics/phiGenSplitting/TOPIC-phiGen-descends.md)
(T8) and the first cone-algebra topic
[TOPIC-integrality.md](../topics/phiGenSplitting/TOPIC-integrality.md) (T9); the
mathematics of record is
[base/013](../../base/013-riemann-existence-and-the-q-expansion-principle.md) §3,
§4.3, §5.4, §6. FLT is pinned at `aa2d8b3`; mathlib at `v4.34.0`.

## 0. Where the sub-effort stands

| topic | deliverable | status | measure |
|---|---|---|---|
| **T5** | R1's constancy kernel + the `n = 0` corollary, in `FLTForHuman/ModularForms/` | **done**, 1 module, 2 public + 6 private, 333 lines | kernel verbatim; axioms clean |
| **T6** | the analytic model of `jq` (`jq` sums to `E₄³/Δ`; its `SL₂(ℤ)`-invariance) | **done**, 1 module, 2 public + 43 private, 622 lines | both statements verbatim; consumer Zone D bound; axioms clean |
| **T7** | the Hauptmodul form (R1 complete) | **done**, 1 module, 15 public + 16 private, 483 lines | headline + T8 interface verbatim; consumer Zone E bound; axioms clean |
| **T8** | the cone application (the descended coefficients lie in `ℚ[jq]`) | **done**, 3 modules, 8 public + 43 private, 725 lines | four statements verbatim; consumer Zone F bound; axioms clean |
| **T9** | the cone's (b) integrality (descended coefficients are integral; the triangularity descent) | **done**, 1 module, **2 public** + 19 private, 322 lines | Route A shipped (deviation); both statements verbatim; consumer Zone G bound; axioms clean |

R1 = T5–T7 (**complete**); T8 discharges the cone's (c) (**complete**); T9
discharges the integrality half of the cone's (b) (**complete**). The
sub-effort's deliverables are seven files:

| module | lines | decls | FLT source (`aa2d8b3`) |
|---|---|---|---|
| `FLTForHuman/ModularForms/QExpansionPrinciple.lean` | 333 | 2 public + 6 `private` (+1 `example`) | `P2M/Sol/S_ModularCurve_coeff_eq_zero_of_hasSum_of_slash_invariant.lean` (186) |
| `FLTForHuman/ModularForms/JqAnalyticModel.lean` | 622 | 2 public + 43 `private` | `hasSum_jq_qParam` (45), `hasSum_jNum_qParam` (235), `qExpansion_discriminant_eq_X_mul_tprod` (199), `…_map_X_mul_dedekindEtaUnit` (76), `qExpansion_E4_…` (34), `…_E4_cube_div_discriminant_smul` |
| `FLTForHuman/ModularForms/Hauptmodul.lean` | 462 | 15 public + 14 `private` | `hasSum_qParam_mul` (80), `…_laurent` (84), `exists_aeval_jq_sub_holomorphicAtInfty` (84), `mem_adjoin_jq_of_hasSum_of_slash_invariant` (214) |
| `FLTForHuman/ModularForms/Defs/HeckeOperator.lean` | 115 | 4 public + 7 `private` | `Def_ModularForm_HeckeOperator` 11–70 (of 204) |
| `FLTForHuman/ModularForms/HeckeQExpansion.lean` | 100 | 2 public | `hasSum_qParam_heckeMatrix_smul` (54), `…_heckeDiagMatrix_smul` (55) |
| `FLTForHuman/ModularForms/PhiGenDescends.lean` | 510 | 2 public + 36 `private` | `cosetPoly_smul` (244), `…_hasSum_cosetPoly_coeff` (281), `…_mem_adjoin_jq_of_phiGenDescends` (47) |
| `FLTForHuman/ModularCurve/PhiGenIntegrality.lean` | 322 | 2 public + 19 `private` | `PhiGenDescends_intCoeffs` (239), the integrality half of `aeval_jq_intCoeffs_descent` (~108; the file's ~180-line `TPoleOrderLE` block is out of scope) |

## 1. What T5 cost

| | |
|---|---|
| goal rounds | **1** (of the 2 budgeted; checkpoint at 1 not needed) |
| declarations | 2 public, 6 `private`, 1 non-vacuity `example` |
| lines written | 333 total: 95 header/imports, 127 private helper block, 50 kernel, 42 corollary, 19 `example` |
| build | `lake build` 3511 jobs, green, **0 warnings**, no `sorry` |
| `#print axioms` | both public declarations: `propext, Classical.choice, Quot.sound` |
| checker | `151 statements identical, 0 mismatched, 0 missing, 8 own-proof exempted` (150 → 151) |

The module's own proof weight is the 127-line private block plus the ~90 lines of
the two public proofs; the pin is 186 lines. The ratio is not a saving because
the port adds the corollary (ours, no pin counterpart) and a 95-line header, and
because the pin's 186 lines include 13 helpers the port did not need at all.

## 2. The mathlib-first audit, measured

The work order's §2.1 table predicted the pin's 14 helpers would mostly become
public mathlib calls, with only `mdifferentiable` needing a proof. Measured
against the build:

| outcome | count | helpers |
|---|---|---|
| became a public mathlib call (no port code) | **3** | `norm_qParam_lt_one_of_pos` → `Periodic.norm_qParam_lt_one`; `tendsto_atImInfty` → `UpperHalfPlane.tendsto_atImInfty_of_hasSum_qExpansion`; `isBoundedAtImInfty` → `UpperHalfPlane.isBoundedAtImInfty_of_hasSum_qExpansion` |
| dropped as avoidable | **5** | `discFun`, `hasSum_discFun`, `continuousAt_discFun`, `discFun_zero` (the public `cuspFunction` API replaces the disc route); `periodic` (public `UpperHalfPlane.periodic_comp_ofComplex` is the counterpart — topic 7 needs it) |
| needed a proof | **6** | `mdifferentiable` (the expected gap); `hasSum_cuspFunction_punctured` and `hasFPowerSeriesOnBall_update`, mathlib-**private**, re-derived as `mdifferentiable`'s disc-route dependencies; `apply_eq_discFun` and `differentiableOn_discFun`, restated as `apply_eq_cuspFunction` / `differentiableAt_cuspFunction_of_hasSum`; `coeff_unique` (see §2.3) |

So the audit's headline held — the analysis is one mathlib theorem and the
packaging is mostly mathlib — but "only `mdifferentiable` needs proof" was
**off by five**: `mdifferentiable` cannot be stated without the two
mathlib-private disc-route lemmas, so its real dependency tree is three lemmas
(~53 lines of the port), and the two `discFun`-restatements plus `coeff_unique`
account for the rest.

### 2.1 `mdifferentiable`'s share

`mdifferentiable` itself is a 26-line declaration (the pin's is 15), but it is
the only place in the port with real analytic content that mathlib does not
expose, and it exists only because **every public `*_cuspFunction` lemma takes
`MDiff f` as a hypothesis and nothing public derives it from a `HasSum`**. The
three private lemmas it needs are the price of entry. The other five public
mathlib replacements applied on the first try, with the `smul`/`mul` bridge
(`smul_eq_mul` on `ℂ`) as the only friction.

### 2.2 `qExpansion_coeff_unique`: the one substitution that failed

The audit expected the pin's 26-line `coeff_unique` to drop for mathlib's
one-line `UpperHalfPlane.qExpansion_coeff_unique`. It states exactly the required
fact, but its `{F : Type*} [FunLike F ℍ ℂ]` signature instantiates at the bare
function type `ℍ → ℂ` in the kernel, and the resulting unification unfolds
`DFunLike.coe` **5,143,553 times** (`set_option diagnostics true`) — a
deterministic `whnf` heartbeat timeout at the default 200 000 *and* at the
package's 4 000 000. The pin's `coeff_unique`, restated over
`hasFPowerSeriesOnBall_update` and `tendsto_nhds_unique`, has no `FunLike`
quantifier and compiles in seconds. **Recommendation for T6–T8:** when a mathlib
lemma is `FunLike`-generic and the port only has a bare function, pass the
bundled form (`ModularForm`, `SlashInvariantForm`) or expect this blowup; check
the build clock, not just success. This is the only §2.1 substitution that did
not go through.

### 2.3 Did `eq_const_of_weight_zero` deliver?

Yes, exactly as scouted. `ModularForm.eq_const_of_weight_zero` needed only that
`F` be a `ModularForm 𝒮ℒ 0`, whose `[𝒮ℒ.IsArithmetic]` instance exists, and the
three fields were discharged by `hslash` (`hinv` → slash invariance),
`mdifferentiable` (`holo'`) and `isBoundedAtImInfty_of_hasSum_qExpansion`
(`bdd_at_cusps'` after `OnePoint.isBoundedAt_iff_forall_SL2Z`). No assumption
beyond the pin's `hF`/`hinv` was needed, and the resulting `F = const κ` is what
`coeff_unique` compares against the constant presentation `Pi.single 0 κ`.

## 3. The wire test

`mem_adjoin_jq_of_poleOrderLE_zero` (lines 273–314) is the required corollary and
is a genuine cross-module composition, not a restatement:

- it consumes the kernel `coeff_eq_zero_of_hasSum_of_slash_invariant` from the
  same module;
- it consumes the port's own `jq` and `PoleOrderLE`
  (`FLTForHuman/ModularCurve/Defs/`);
- and it performs a real `ℤ → ℕ` conversion: `PoleOrderLE f 0` kills the
  negative coefficients, `Function.Injective.hasSum_iff` (`Nat.cast_injective`)
  restricts the `ℤ`-indexed `HasSum` to `ℕ`, the kernel kills the positive
  coefficients, and `HahnSeries.single 0 (f.coeff 0)`,
  `algebraMap_laurentSeries_eq_single` and `Subalgebra.algebraMap_mem` close.

The **non-vacuity `example`** is in the module itself (`section Example`, lines
315–332), not the consumer: `F = const κ`, `c = Pi.single 0 κ` satisfies both
hypotheses and the kernel's conclusion is `Pi.single 0 κ m = 0` for `m ≠ 0`. The
choice is the module-local one, per the work order's option.

## 4. The corollary's future

`mem_adjoin_jq_of_poleOrderLE_zero` is the `n = 0` case of T7's headline
`mem_adjoin_jq_of_hasSum_of_slash_invariant` (base/013 §5.5), with the pole bound
as an explicit hypothesis instead of the pole-killing lemma
`exists_aeval_jq_sub_holomorphicAtInfty`. When T7 lands it will subsume the
corollary's proof: choose `n`, apply T7, done. The corollary should then survive
as a convenience — it names the constant case, which is the one the Hecke-coset
arguments actually use, and the statement checker's `OWN_PROOFS` entry is already
written — unless T7's own statement makes the special case redundant in every
consumer, in which case it can be removed with its `OWN_PROOFS` entry.

## 5. Decisions carried forward

- **The module lives in `FLTForHuman/ModularForms/`**, not
  `FLTForHuman/ModularCurve/`: the kernel is about modular forms on `ℍ` and
  mentions no modular curve. Recorded rather than chosen silently, per the work
  order.
- **The checker verifies the kernel as a transcribed statement** (wrapper added
  to `SOURCES`) and exempts the corollary explicitly in `OWN_PROOFS`, with the
  reason commented there. After T6 the count is **153** (T5's 151 plus T6's two
  wrappers), 0 mismatched.
- **T6's forward note — resolved.** The `FunLike` trap of §2.2 did *not* appear
  in T6, because the pin's `ModularFormClass.qExpansion_coeff_unique` call is
  already on the bundled `CuspForm.discriminant`; the recommendation to pass
  bundled forms where possible held, but the specific call needed no change.

## 6. T6: the analytic model of `jq`

Module: `FLTForHuman/ModularForms/JqAnalyticModel.lean`, 622 lines, **2 public**
(`hasSum_jq_qParam`, `E4_cube_div_discriminant_smul`, both verbatim from their
pin wrappers) and **43 `private`** declarations. The pin's intermediate
`hasSum_jNum_qParam` is private, as the work order required. One goal round (of 3).

| | |
|---|---|
| goal rounds | **1** (of the 3 budgeted; checkpoint at 1 not needed) |
| declarations | 2 public, 43 `private` |
| lines written | 622 total: ~100 header/imports, ~180 eta-product Taylor series, ~200 gluing, 24 `q⁻¹` step, 23 invariance |
| build | `lake build` 3827 jobs, green, **0 warnings**, no `sorry` |
| `#print axioms` | both public declarations: `propext, Classical.choice, Quot.sound` |
| checker | `153 statements identical, 0 mismatched, 0 missing, 8 own-proof exempted` (151 → 153) |
| consumer | Zone D added and bound; **0 errors**, still one `sorry` (the deferred capstone) |

Pin material is ~589 lines across five files; the port is 622 lines, a ratio of
**1.06** (T5's was 333/186 = 1.79). The audit's *rightness* and its *savings*
diverged again, in the same direction: the mathlib substitutions that landed
(`E_qExpansion_coeff`, `discriminant_eq_q_prod`,
`differentiableOn_tprod_one_sub_pow_pow`, `hasSum_qExpansion`,
`slash_action_eqn''`) did not shrink the port, because the pin's own file is
mostly *glue* — the bridge from mathlib's analytic objects to the port's
`eisenstein4`/`dedekindEtaUnit`/`jNum`, which has no mathlib counterpart.

### 6.1 The audit, measured again

| pin piece | outcome |
|---|---|
| `qExpansion_E4_eq_map_eisenstein4` (34) | mathlib engine `EisensteinSeries.E_qExpansion_coeff`; the port proof is 22 lines (pin 34) |
| `qExpansion_discriminant_eq_X_mul_tprod` (199) | **kept.** `discriminant_cuspFunction_eqOn` gives the value of `cuspFunction 1 Δ`, not the Taylor coefficients of `∏' (1-qⁿ)²⁴`; no mathlib lemma computes those. The pin's `coeff_trunc_eq_coeff_etaPow` + truncated-polynomial/locally-uniform-convergence argument is ported (~180 lines) |
| `qExpansion_discriminant_eq_map_X_mul_dedekindEtaUnit` (76) | reduced to the 8-line `etaPow_eq_map_dedekindEtaUnit`, by the generic `coeff_trunc_eq_coeff_tprod` over `ℤ` |
| `qExpansion_E4` / `discriminant_eq_qParam_mul_gfun` value lemmas | mathlib `discriminant_eq_q_prod`, `differentiableOn_tprod_one_sub_pow_pow 24` |
| `solution` of the `qExpansion_*` files | `ModularFormClass.qExpansion_coeff_unique` on the bundled `CuspForm.discriminant` |
| `hasSum_jNum_qParam`'s engine | `UpperHalfPlane.hasSum_qExpansion` |
| gluing `qJ_eq`, `qJ_mul_Dq`, `cuspFunction_eqOn`, `cuspFunction_{Dq,qJ}`, `qExpansion_{qParam_fun,Dq',qJ}`, `periodic_qJ`, `mdiff_qJ`, `isBoundedAtImInfty_qJ`, `gfun_ne_zero`, `continuousAt_gfun` | **ported** (~200 lines; no mathlib counterpart) |
| `analyticAt_cuspFunction_{Dq,qJ}` | **kept** (pin's `cuspFunction_eqOn` route); mathlib's public `analyticAt_cuspFunction_zero` was audited and would require re-deriving `Periodic`/`MDiff`/`IsBoundedAtImInfty` for `Dq` |
| `tendsto_gfun_qParam` | **kept** (2 lines); mathlib's `tendsto_atImInfty_tprod_one_sub_eta_q_pow` is the neighbouring `eta_q` form |
| `hasSum_jq_qParam` (`q⁻¹` step, 45) | **ported** in 24 lines (`HasSum.mul_left` + `Function.Injective.hasSum_iff` + `coeff_jq_of_lt`) |
| `E4_cube_div_discriminant_smul` | mathlib `SlashInvariantForm.slash_action_eqn''`; 23 lines against the pin's 38 |

So of the five pin files: **one is genuinely replaced** (the 76-line map file
collapses to 8 lines, and the two value lemmas to mathlib calls), **one is
retained in substance** (the 199-line tprod file), and the 235-line gluing file
is ported essentially 1:1. The work order's headline — "the audit's most to
gain" — did not hold: the heaviest file was not replaceable. This is the second
T5-shaped finding for the R1 sequence, and the recommendation for T7 is to price
the *glue*, not the mathlib-replaceable leaves.

### 6.2 Did any mathlib lemma blow up?

No. The `FunLike`/`DFunLike.coe` blow-up of T5 §2.2 did not recur: the one
`qExpansion_coeff_unique` call already passes the bundled `CuspForm.discriminant`.
The only frictions were cosmetic and are recorded in the consumer's friction list
entry 14: `if_neg` → `ite_eq_right` (the T5 drift family) and the
`derivative`/`Polynomial.derivative` ambiguity if `PowerSeries` is opened at
top level.

### 6.3 The wire test

Zone D of `spec/ModularCurveConsumer.lean` composes this module's
`hasSum_jq_qParam` with `Defs/Jq.lean`'s `coeff_jq_neg_one` and
`JqCoefficients.lean`'s `coeff_jq_zero`/`coeff_jq_one`, exhibiting the classical
`j(q) = q⁻¹ + 744 + 196884 q + ⋯` as the coefficients of the realized sum. The
`HasSum` itself does not expose its terms, so the composition is stated as the
`HasSum` plus the three coefficient values — the form the work order names. The
zone also checks `E4_cube_div_discriminant_smul`; the real consumer is T7.

## 7. T7: the Hauptmodul form — R1 complete

Module: `FLTForHuman/ModularForms/Hauptmodul.lean`, 483 lines, **15 public** and
**16 `private`** declarations. The headline
`mem_adjoin_jq_of_hasSum_of_slash_invariant` is verbatim from its pin wrapper;
the other public declarations are the T8 interface (`RealL` + 11 closure lemmas,
`hasSum_qParam_mul`, `hasSum_qParam_mul_laurent`). Pole killing (5 helpers),
`realL_aeval_jq`, the `jt`/`jqC` glue and `mem_adjoin_jq_of_realL_invariant` are
private. One goal round (of 3).

| | |
|---|---|
| goal rounds | **1** (the 3-round budget was for the blow-up risk that never materialised) |
| declarations | 15 public, 16 `private` |
| lines written | 483 total: ~100 header/imports, ~100 Cauchy products, ~120 `RealL` + closure, ~95 pole killing, ~70 glue + headline |
| build | `lake build` 3769 jobs, green, **0 warnings**, no `sorry` |
| `#print axioms` | the headline, both Cauchy lemmas and `RealL.mul`: only `propext, Classical.choice, Quot.sound` |
| checker | `168 statements identical, 0 mismatched, 0 missing, 8 own-proof exempted` (153 → 168) |
| consumer | Zone E added and bound; **0 errors**, still one `sorry` (the deferred capstone) |

### 7.1 Did "glue is 1:1" hold?

Yes — better. **483 port lines against a ~462-line pin, ratio 1.05** (T5 1.79,
T6 1.06). The §2.1 audit predicted that no public mathlib lemma would replace
`RealL`, its closure, `coeff_prod_X_sub_C`, `realL_aeval_jq`, pole killing or the
headline, and that held: the port is a faithful transcription with mathlib only
inside `hasSum_qParam_mul` (the Cauchy-product core:
`tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm` /
`summable_norm_sum_mul_antidiagonal_of_summable_norm`), in the Laurent order
split (`single_order_mul_powerSeriesPart`, `coeff_coe_powerSeries`, …), in the
pole-killing coefficient API (`le_order_iff_forall`,
`coeff_eq_zero_of_lt_order`), and via T5/T6. The only proof with real content
that is entirely ours is `summable_norm_of_hasSum_qParam` (the comparison-radius
argument from a `HasSum` on `ℍ` to absolute summability on the disc).

### 7.2 The exported API

Exactly as scoped. The public closure is `RealL.add`, `.neg`, `.sub`, `.mul`,
`.single`, `.C`, `.one`, `.zero`, `.congr`, `.prod`, `.coeff_prod_X_sub_C`, plus
`hasSum_qParam_mul` and `hasSum_qParam_mul_laurent`. FLT duplicates the `RealL`
block in T8's pin file
(`S_ModularCurve_PhiGen_PhiGenDescends_hasSum_cosetPoly_coeff.lean`); the port
defines it once here, so **T8 imports rather than copies**, and T8's `RealL.mul`
will need exactly the two exported Cauchy lemmas. Nothing else was exported.

### 7.3 Did any mathlib lemma blow up?

No. Nothing is instantiated at a bare function type, and the module typechecked
on the first bounded `lake env lean` (6 s build). The only drift was `if_pos` →
`ite_eq_left` in `hasSum_single_mul_coe_iff`.

**One constraint worth its own entry (checker, not mathematics).** The exported
statements had to be written in the *wrappers'* raw spelling, not the port's
convenient one. The wrappers write `UpperHalfPlane → ℂ` and
`Function.Periodic.qParam`, while the `S_` files write `ℍ` and the local `𝕢`;
these are definitionally equal, but `spec/check_flt_statements.py` is a text diff.
So `RealL` (comparable source: the `S_` file) keeps `ℍ`/`𝕢`, while
`hasSum_qParam_mul{,_laurent}` and the headline (comparable sources: the
wrappers) use the long forms. **Rule for T8 and later: match the wrapper's
spelling for any public declaration the checker verifies.**

### 7.4 The wire test

Zone E of `spec/ModularCurveConsumer.lean` runs the headline on `f = jq` and
`F = E₄³/Δ`, with `hF` from T6's `hasSum_jq_qParam` and `hinv` from T6's
`E4_cube_div_discriminant_smul`, concluding `jq ∈ ℚ[jq]`. The conclusion is
trivial mathematically; the test is that T7's statement *accepts* T6's two
theorems — the whole interface across three modules. It is the R1 completion
check, and `#print axioms` on the headline is clean.

### 7.5 R1 is complete

T5 (kernel) → T6 (realization) → T7 (Hauptmodul) now form a compiled chain:
`coeff_eq_zero_of_hasSum_of_slash_invariant` is applied inside
`mem_adjoin_jq_of_realL_invariant` to the holomorphic remainder of an arbitrary
pole-bounded invariant series, and the realization of the polynomials in `jq` is
T6's. T8 is the cone's algebra and no longer has R1 on its critical path.

## 8. T8: the cone application — (c) discharged

Three new modules, **725 lines**, 8 public and 43 private declarations:
`Defs/HeckeOperator.lean` (115), `HeckeQExpansion.lean` (100),
`PhiGenDescends.lean` (510). The four exported statements —
`hasSum_qParam_heckeMatrix_smul`, `hasSum_qParam_heckeDiagMatrix_smul`,
`cosetPoly_smul`, `PhiGen.mem_adjoin_jq_of_phiGenDescends` — are verbatim from
their wrappers; `hasSum_coeff_of_phiGenDescends` and the whole `ZMod`/`OnePoint`
group theory are private. One goal round (of the 4 budgeted; the documented
T8a/T8b split was not needed).

| | |
|---|---|
| goal rounds | **1** (of the 4 budgeted; checkpoint at 1 not needed) |
| declarations | 8 public, 43 `private` |
| lines written | 725 total: 115 Hecke defs, 100 Hecke q-expansions, 510 coset + descend |
| build | `lake build` 3792 jobs, green, **0 warnings**, no `sorry` |
| `#print axioms` | all 8 public declarations: only `propext, Classical.choice, Quot.sound` |
| checker | `176 statements identical, 0 mismatched, 0 missing, 8 own-proof exempted` (168 → 176) |
| consumer | Zone F added and bound; **0 errors**, still one `sorry` (the deferred capstone) |

### 8.1 Cost, and the dedup payoff

**725 port lines against ~741 of pin content** (681 in the five S files + the
60-line Hecke subset of FLT's 204-line def file) — ratio **0.98**, the
sub-effort's cheapest (T5 1.79, T6 1.06, T7 1.05). The deduplication is what made
it: FLT's `…hasSum_cosetPoly_coeff.lean` copies the `RealL` + closure block
(~90 lines) and the `jt`/`jqC` glue (~17) from T7's file; the port imports T7's
public `RealL`/closure and redefines only ~10 lines of private `jt`/`jqC` glue, so
**~97 lines were never written**. This is the payoff of T7 exporting the API, and
it is the first topic where the deduplication rule visibly moved the ratio.

### 8.2 The Hecke definitions

The minimal subset sufficed, exactly as the `grep -c` survey predicted:
`heckeMatrix` (3 of T8's 5 pin files), `heckeDiagMatrix` (3),
`coe_heckeMatrix_smul` (1), `coe_heckeDiagMatrix_smul` (1) — nothing else. The
port takes `upperTriangularGL`, `heckeMatrix`, `heckeDiagMatrix`, `val_*`,
`det_*`, `denom_*` and `coe_*_smul` (the last four private except the two
`coe_*_smul`, which the next module needs).

**The dropped block is genuinely unused.** `heckeU`, `heckeT`, `coeffHeckeT`,
`coeffHeckeU`, `slash_hecke*`, `σ_hecke*`: **0 occurrences** in T8's five pin
files. Across the cone's other 44 node files, `heckeU`/`heckeT` appear only in the
doc-site toolchain's `attribute [-simp] ModularForm.heckeU_zero …` pragma
(5 files: `ModularPolynomialData_eq_of_prime`, `PhiGen_splits_of_prime`,
`PhiGen_splits_prime_at_slot`, `exists_phiIrreducible_evalSymm`,
`finrank_adjoin_jqN_eq_of_prime`) and `coeffHeckeT`/`coeffHeckeU`/`slash_hecke*`/
`σ_hecke*` are 0. So the cone's remaining pieces do **not** need the Hecke
operators; a later effort that does extends the module then.

### 8.3 Did the `ZMod`/`OnePoint` group theory behave?

The predicted `FunLike` trap did not occur, but a different mathlib-facing issue
did, and it is the interesting finding:

- **The `mapGL`-entry transparency issue.** The pin's `@[scoped simp]
  mapGL_apply` (and every explicit restatement, `mapGL_coe_matrix`,
  `Matrix.SpecialLinearGroup.map_apply_coe`, `RingHom.mapMatrix_apply`,
  `Matrix.map_apply` in isolation) failed to rewrite the entries of the anonymous
  `SL(2,ℤ)` matrix `⟨!![…], _⟩` produced by `refine`, with Lean reporting "target
  expression is not type-correct under the implicit transparency level". The fix
  is mathlib's own `set_option backward.isDefEq.respectTransparency.types false`
  before the four commutation lemmas (the same directive `Discriminant.lean`
  uses); with it, the default `simp [hp, Matrix.mul_apply, Fin.sum_univ_two]`
  reduces the entries and `mapGL_apply` is not needed at all. **Not a heartbeat
  blow-up** — the typecheck is 6.4 s.
- **Explicit `(p := p)` for `redMatrix`.** In `heckeRep_mul` the `Fact p.Prime`
  instance stayed stuck on an unresolved `p` (`Fact (Nat.Prime (?m g'))`) until
  the implicit `p` was given explicitly.
- **`have` vs `haveI` in `sigma_zeta`.** A local `have : IsCyclotomicExtension …`
  is *not* found by instance search where `haveI` is, so the
  `linter.style.haveILetI` warning is disabled locally for that one declaration
  rather than silently weakening the proof. This refines T7's log §7.3: the
  playbook's "prefer `have` for class-typed locals" is not universal.
- `if_pos`/`if_neg` → `ite_eq_left`/`ite_eq_right` four times (T5's drift
  family).

### 8.4 The wire test

Zone F of `spec/ModularCurveConsumer.lean` binds
`PhiGen.mem_adjoin_jq_of_phiGenDescends` plus the T8 interface and the
correspondence, and states the theorem in hypothesis form (so the full signature,
including `PhiGenDescends`, elaborates). There is **no concrete instance**: the
hypothesis `hc : PhiGenDescends ℓ ζ c` is the cone's piece (a), which is not
ported, and the work order forbids inventing one. The node's real consumer is the
cone's (d) `exists_modularPolynomialData_coeff_eq`, also not ported. The internal
chain is nonetheless genuine — `hasSum_coeff_of_phiGenDescends` builds the
realization, T7's headline consumes it, and the two Hecke lemmas plus
`cosetPoly_smul` feed it — and it spans all four R1/cone modules.

### 8.5 The planned sequence is complete

T5–T8 are done; R1 is complete and the cone's (c) is discharged. What remains of
the cone is its other five pieces (see `PORTING-PhiGen.md` §6 and §8's table),
and the one interface node the later pieces reach. The sub-effort's record here
is closed.

## 9. T9: the cone's (b) integrality — Route A shipped

One new module, **322 lines**, **2 public** and 19 `private` declarations:
`FLTForHuman/ModularCurve/PhiGenIntegrality.lean`. The two public statements —
`PhiGen.PhiGenDescends.intCoeffs` and `PhiGen.aeval_jq_intCoeffs_descent` — are
verbatim from their `Theorems/` wrappers. It also promoted T7's two private
triangularity lemmas into `Defs/` (below). One goal round (of the 3 budgeted,
including the round-1 checkpoint).

| | |
|---|---|
| goal rounds | **1** (of the 3 budgeted; checkpoint at 1 not needed) |
| declarations | **2 public**, 19 `private` (of which 1 is the named wire test) |
| lines written | 322 total: ~60 header/imports, ~157 Route A bridges, ~30 the `intCoeffs` statement, ~75 triangularity descent + wire test |
| build | `lake build` 3839 jobs, green, **0 warnings**, no `sorry` |
| `#print axioms` | both public declarations: only `propext, Classical.choice, Quot.sound` |
| checker | `180 statements identical, 0 mismatched, 0 missing, 8 own-proof exempted` (178 → 180) |
| consumer | Zone G added and bound; **0 errors**, still one `sorry` (the deferred capstone) |

### 9.1 Route A vs Route B — A shipped, in round 1

The work order's deviation protocol asked for a Route A spike first (the first
deliberate route deviation in the sub-effort). The spike was written in
`Scratch.lean` and the route **closed**: Route A shipped, decided in round 1.

The three stop-early risks the work order named were all cleared by the spike:

- **`coeffMap`/`HahnSeries.map` commuting with `qExpand`** — already public as
  `coeffMap_qExpand`; the spike used it unchanged.
- **`coeffMap` commuting with `qTwist` and the `𝒪`-unit lift of `ζ`** — both
  worked. `coeffMap_qTwist` is a coefficientwise computation; the unit is the
  explicit `Units.mkOfMulEqOne` of `ζ ^ e` and its inverse (each a root of
  `X ^ ℓ - 1`), so mathlib synthesized the `Units` structure with no fight.
- **`jq_ℤ` reachable from `Defs/Jq.lean` without unfolding `jNumQ`** — reachable:
  `jqZ := single (-1) 1 * ofPowerSeries ℤ ℤ jNum`, and `coeffMap (algebraMap ℤ K)
  jqZ = coeffEmb K jq` is a two-line `map_mul` computation.

**Did the route-check's predicted saving materialize?** Partly. FLT's replaced
closure machinery is:

| FLT block | pin lines | Route A replacement |
|---|---|---|
| `CoeffsIntegral` + `zero/one/neg/mul/qExpand/qTwist` | 41 | `jqZ`, `coeffMap_ofPowerSeries`, `coeffMap_qTwist`, `coeffMap_jqZ`, `jqO`, `coeffMap_jqO`, `conjO`, `coeffMap_conjO`, `phiProdO`, `map_phiProdO` (~90 lines, 10 declarations) |
| `coeffsIntegral_coeff_X_sub_C/_mul/_prod` | 42 | ring structure (`map_phiProdO` + `Polynomial.map`) |
| two manual root-of-unity lemmas | 24 | `mem_integralClosure_of_pow_eq_one` + `zetaUnit`/`coeffMap_zetaUnit` (~20 lines) |

So the 83 lines of closure + polynomial-coefficient machinery became ~90 lines of
bridging lemmas: **no line saving**, but the bridges are reusable ring-hom
bookkeeping rather than a bespoke predicate, and the two root-of-unity lemmas
shrank. The prediction that `IsPrimitiveRoot.isIntegral` would be the
root-of-unity call did **not** hold: the hypothesis is only `ζ ^ ℓ = 1`, not
primitivity, so `IsPrimitiveRoot.isIntegral` does not apply directly; the port
uses `X ^ ℓ - 1` (`mem_integralClosure_of_pow_eq_one`), the same monic-polynomial
argument as the pin but in one generic lemma. This is the audit's one negative
result, and it is the kind of "rightness ≠ savings" outcome T6 also recorded.

### 9.2 The cost

**322 port lines against ~347 of in-scope pin content** (the 239-line
`intCoeffs` file plus the ~108-line integrality half of the descent file; the
descent file's ~180-line `TPoleOrderLE` block belongs to the pole-bound topic and
is not ported). Ratio **0.93**, the sub-effort's first sub-1.0 ratio below T8's
0.98 (T5 1.79, T6 1.06, T7 1.05, T8 0.98). Two structural notes on the
denominator: the 322 includes a ~60-line header, and Route A's bridges are
counted in full against pin blocks the pin itself duplicates in 9 files.

### 9.3 The dedup

`coeff_aeval_jq_neg` and `poleOrderLE_aeval_jq` were **private and unused** in
T7's `Hauptmodul.lean`; deleting them shrinks that module by **25 lines** (482 →
462, net of a 5-line header note; 16 → 14 private declarations). More important,
the pin repeats `coeff_aeval_jq_neg` privately in
**9** `S_` files — (b), (d), (e), the 895-line block and others — so every
remaining cone topic now has a clean public entry point instead of a private
copy. `coeff_aeval_jq_neg` lives in `Defs/Jq.lean` (with `jq`); T9's second
statement uses it directly. `poleOrderLE_aeval_jq` needs `PoleOrderLE`, which is
defined in `Defs/PhiGen.lean`, and `Defs/PhiGen.lean` imports `Defs/Jq.lean`
through `Defs/Fields`/`Defs/Polynomial`, so it was promoted into
`Defs/PhiGen.lean` rather than `Defs/Jq.lean` as the work order's letter said —
a structural necessity, not a choice. Both promoted lemmas are verified against
`P2M/Sol/S_ModularCurve_exists_aeval_jq_sub_holomorphicAtInfty.lean`, where the
pin has them public; the checker rose 176 → 178 on the promotion and 178 → 180 on
the two wrappers.

### 9.4 The wire test

Zone G of `spec/ModularCurveConsumer.lean` binds both public statements and
states them in hypothesis form. `PhiGenDescends.intCoeffs` has **no concrete
instance**: its hypothesis `hc : PhiGenDescends ℓ ζ c` is the cone's piece (a),
which is not ported, and the work order forbids inventing one; its real consumer
is (d)'s `exists_modularPolynomialData_coeff_eq`, also not ported.
`aeval_jq_intCoeffs_descent` *does* have the concrete `P = X` instance (taking
`hP := intCoeffs_jq` and concluding `X.coeff 1 = 1 ∈ ℤ`), and it is named
`aeval_jq_intCoeffs_descent_X` inside the module, where the private helper
`intCoeffs_jq` is in scope — the module's public surface is held at exactly the
two wrappers, so the instance cannot live in the consumer without exporting a
third declaration.

### 9.5 What T9 leaves

The cone's (b) still owes the pole bounds (T10): `phiProd_conj_coeff_eq_zero_of_le`
and the `TPoleOrderLE` closure block — the ~180 lines this topic deliberately did
not port. The promoted `poleOrderLE_aeval_jq` is T10's shared entry point. Then
the 328-block and assembly (T11) consumes both `PhiGenDescends.intCoeffs` and
`aeval_jq_intCoeffs_descent`.
