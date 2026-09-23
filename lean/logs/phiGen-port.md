# The Φₚ splitting / R1 sub-effort — record

**Status: T5–T13 complete (2026-09-22) — the Φₚ splitting cone is closed.** R1 is
complete, the cone's (c) is discharged, the cone's (b) is complete in both halves,
the cone's construction (a) + the 328 block + (d) is built, the datum's properties
(positivity, irreducibility, symmetry, existence) are proved, and the cone's
headline `PhiGen.splits_prime_at_slot` is a ported theorem: all 44 nodes below it
are public. This is the running record for the sub-effort
[PORTING-PhiGen.md](../topics/PORTING-PhiGen.md) opens: the R1 (level-one q-expansion
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
(T8), the first cone-algebra topic
[TOPIC-integrality.md](../topics/phiGenSplitting/TOPIC-integrality.md) (T9),
[TOPIC-pole-bounds.md](../topics/phiGenSplitting/TOPIC-pole-bounds.md) (T10) and
[TOPIC-datum-assembly.md](../topics/phiGenSplitting/TOPIC-datum-assembly.md)
(T11) and
[TOPIC-irreducibility-symmetry.md](../topics/phiGenSplitting/TOPIC-irreducibility-symmetry.md)
(T12); the
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
| **T10** | the cone's (b) pole bounds + the shared `TPoleOrderLE` prelude | **done**, 1 module + `Defs/PhiGen.lean`, 25 public + 18 private, 497 lines | FLT's script ported verbatim (no deviation); both statements verbatim; prelude promoted for T11; consumer Zone H bound; axioms clean |
| **T11** | the construction: (a) descent + the 328 block + (d) assembly | **done**, 3 modules, **8 public** + 25 private, 701 lines | all eight statements verbatim; `evalAtJ_injective` by the mathlib route; consumer Zone I bound end-to-end; axioms clean |
| **T12** | the properties: positivity + the 895 block + symmetry/existence | **done**, 3 modules, **19 public** + 93 private, 1670 lines | all statements verbatim; the 895 block written once; `evalAtJ_eq_aeval_map` promoted to `Defs/Jq`; consumer Zone J bound (first unconditional wire); axioms clean |

R1 = T5–T7 (**complete**); T8 discharges the cone's (c) (**complete**); T9 and
T10 discharge the two halves of the cone's (b) (**complete**); T11 builds the
construction (**complete**); T12 proves its properties (**complete**). The
sub-effort's deliverables are fourteen files (plus the shared-block addition to
`Defs/PhiGen.lean` and the `evalAtJ_eq_aeval_map` promotion in `Defs/Jq.lean`):

| module | lines | decls | FLT source (`aa2d8b3`) |
|---|---|---|---|
| `FLTForHuman/ModularForms/QExpansionPrinciple.lean` | 333 | 2 public + 6 `private` (+1 `example`) | `P2M/Sol/S_ModularCurve_coeff_eq_zero_of_hasSum_of_slash_invariant.lean` (186) |
| `FLTForHuman/ModularForms/JqAnalyticModel.lean` | 622 | 2 public + 43 `private` | `hasSum_jq_qParam` (45), `hasSum_jNum_qParam` (235), `qExpansion_discriminant_eq_X_mul_tprod` (199), `…_map_X_mul_dedekindEtaUnit` (76), `qExpansion_E4_…` (34), `…_E4_cube_div_discriminant_smul` |
| `FLTForHuman/ModularForms/Hauptmodul.lean` | 462 | 15 public + 14 `private` | `hasSum_qParam_mul` (80), `…_laurent` (84), `exists_aeval_jq_sub_holomorphicAtInfty` (84), `mem_adjoin_jq_of_hasSum_of_slash_invariant` (214) |
| `FLTForHuman/ModularForms/Defs/HeckeOperator.lean` | 115 | 4 public + 7 `private` | `Def_ModularForm_HeckeOperator` 11–70 (of 204) |
| `FLTForHuman/ModularForms/HeckeQExpansion.lean` | 100 | 2 public | `hasSum_qParam_heckeMatrix_smul` (54), `…_heckeDiagMatrix_smul` (55) |
| `FLTForHuman/ModularForms/PhiGenDescends.lean` | 510 | 2 public + 36 `private` | `cosetPoly_smul` (244), `…_hasSum_cosetPoly_coeff` (281), `…_mem_adjoin_jq_of_phiGenDescends` (47) |
| `FLTForHuman/ModularCurve/PhiGenIntegrality.lean` | 322 | 2 public + 19 `private` | `PhiGenDescends_intCoeffs` (239), the integrality half of `aeval_jq_intCoeffs_descent` (~108; the file's ~180-line `TPoleOrderLE` block is out of scope) |
| `FLTForHuman/ModularCurve/PhiGenPoleBounds.lean` | 310 | 2 public + 16 `private` | `phiProd_conj_coeff_eq_zero_of_le` (391; the `_zero_lead` twin is byte-equivalent) |
| `FLTForHuman/ModularCurve/Defs/PhiGen.lean` (T10 addition) | +187 (287 → 489 total) | 23 public + 2 `private` | the shared `TPoleOrderLE` prelude, repeated in twelve pin `S_` files |
| `FLTForHuman/ModularCurve/PhiGenDescent.lean` | 339 | 1 public + 18 `private` | `exists_phiGenDescends` (315) |
| `FLTForHuman/ModularCurve/PhiGenDescendsStructure.lean` | 161 | 5 public + 2 `private` | the 328 block (×7 copies, 84 distinctive; the ~170-line prelude is T10's) |
| `FLTForHuman/ModularCurve/ModularPolynomialAssembly.lean` | 201 | 2 public + 5 `private` | `exists_modularPolynomialData_coeff_eq` (191) |
| `FLTForHuman/ModularCurve/JqCoeffPositivity.lean` | 425 | 2 public + 27 `private` | `one_le_coeff_jq` (386) |
| `FLTForHuman/ModularCurve/ModularPolynomialIrreducible.lean` | 1070 | 15 public + 62 `private` | the 895 block (×5 copies; plus `swapBivar_eq_of_evalSymm`, 95) |
| `FLTForHuman/ModularCurve/ModularPolynomialProperties.lean` | 175 | 2 public + 4 `private` | `evalSymm_of_coeff_evalAtJ_eq` (124), `exists_phiIrreducible_evalSymm` (62) |
| `FLTForHuman/ModularCurve/Defs/Jq.lean` (T12 addition) | +12 | 1 public | `evalAtJ_eq_aeval_map`, with T11's two private copies and the block's `_rat` copy removed |

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

## 10. T10: the cone's (b) pole bounds — the prelude promoted

One new module, **310 lines, 2 public** and 16 `private` declarations
(`FLTForHuman/ModularCurve/PhiGenPoleBounds.lean`), plus the shared prelude,
**187 lines, 23 public** and 2 `private` declarations, added to
`FLTForHuman/ModularCurve/Defs/PhiGen.lean` (287 → 489). The two public statements
— `PhiGen.phiProd_conj_coeff_zero_lead` and
`PhiGen.phiProd_conj_coeff_eq_zero_of_le` — are verbatim from their `Theorems/`
wrappers. **No route deviation**: FLT's script is pure coefficient algebra and
compiled as transcribed. One goal round (of the 2 budgeted; the round-1
checkpoint was not needed).

| | |
|---|---|
| goal rounds | **1** (of the 2 budgeted) |
| declarations | module **2 public**, 16 `private` (incl. 2 named wire tests); prelude **23 public**, 2 `private` |
| lines written | **497**: 187 the shared prelude in `Defs/PhiGen.lean`, 310 the module (~60 header, ~205 the leading-coefficient/bound chain, ~12 the two wire tests) |
| build | `lake build` 3840 jobs, green, **0 warnings**, no `sorry` |
| `#print axioms` | both public declarations: only `propext, Classical.choice, Quot.sound` |
| checker | `205 statements identical (11 promoted from pin-private declarations), 0 mismatched, 0 missing, 8 own-proof exempted` (180 → 205) |
| consumer | Zone H added and bound; **0 errors**, still one `sorry` (the deferred capstone) |

### 10.1 The dedup — the six copies, measured

The prelude the pin repeats is the closure
(`mono`/`zero`/`one`/`neg`/`add`/`mul`/`qTwist`/`qExpand`, `of_jSimplePole`), the
`jq`-pole facts (`jSimplePole_jqK`, `tPoleOrderLE_coeffEmb_iff`,
`tPoleOrderLE_of_qExpand`), the conjugate bounds (`conjPoleBound`,
`conjPoleBound_zero`/`_succ`, `sum_conjPoleBound`, `tPoleOrderLE_conj_zero`/`_succ`/
`_conj`), the polynomial-coefficient bound `tPoleOrderLE_coeff_X_sub_C` and
`phiProd_def`. That is **146 lines** in the representative
`S_ModularCurve_PhiGen_phiProd_conj_coeff_eq_zero_of_le.lean` (lines 24–169), and
the two 391-line `phiProd_conj` twins and the five 328-line `PhiGenDescends`
copies are the **six developments** the work order names.

**Measured, the duplication is larger than the work order's "six".** A grep for
the prelude's marker (`tPoleOrderLE_coeff_X_sub_C`) finds it in **twelve** `S_`
files: the six developments above, plus five single-theorem files that each carry
the whole prelude (`S_…_aeval_jq_intCoeffs_descent`, `S_…_intCoeffs_jq_pow`,
`S_…_tPoleOrderLE_coeffEmb_iff`, `S_…_tPoleOrderLE_of_qExpand`,
`S_…_tPoleOrderLE_phiProd_conj_of_ne_zero` — the last three have `Thm_` wrappers,
so they are exported nodes, not dead files). So the prelude would have cost
**≈ 12 × 146 = 1,752 lines** if written per `S_` file (**≈ 6 × 146 = 876** across
the six byte-duplicate developments). The 328-only coefficient sub-block
(`tPoleOrderLE_coeff_mul`/`_prod`/`_phiProd_coeff`, ~45 lines) appears in **nine**
files, another ≈405 duplicated lines. The port writes the whole union **once**,
187 lines, and because that single copy carries the 328-only sub-block as well,
**T11 imports it with no additions.** T11's `PhiGenDescends.poleOrderLE` needs
`tPoleOrderLE_phiProd_coeff` and `.mono`, both now public in `Defs/PhiGen`; only
the 328 block's own theorems remain T11's work.

### 10.2 The cost

**497 port lines against the 391-line representative pin file, ratio 1.27** — the
sub-effort's highest (T5 1.79, T6 1.06, T7 1.05, T8 0.98, T9 0.93). Two structural
reasons, both real and both in the port's favour: the 187-line prelude is the
*union* of six pin copies (the 391 file omits the 328-only coefficient bounds), so
the denominator under-counts the deduplicated content; and the module carries a
~60-line header and two wire tests that the pin's 391 lines do not. Priced against
the deduplicated six-copy content (146 × 6 prelude lines once, plus the 391 file's
distinctive ~222 lines), the port is comfortably under 1:1.

### 10.3 `pow_sum_range_isPrimitiveRoot` — the audit's near-miss, closed

The work order flagged this as the audit's one near-miss: mathlib's
`IsPrimitiveRoot.geom_sum_eq_zero` is the *sum* `∑ ζ^i = 0`, while FLT needs the
*product* `z ^ (∑ i ∈ range ℓ, i) = (-1)^(ℓ+1)`. **The pin's case split was ported
whole** (`rcases hℓ.eq_two_or_odd' with rfl | hodd`), and mathlib supplied every
step inside it: `Nat.Prime.eq_two_or_odd'` for the split,
`IsPrimitiveRoot.eq_neg_one_of_two_right` for `ℓ = 2`, `IsPrimitiveRoot.pow_eq_one`
and `Finset.sum_range_id_mul_two` for the odd case, and `Even.neg_one_pow` for the
final sign. No re-derivation was needed, but no single mathlib lemma replaces the
statement — the `geom_sum` name is a trap, exactly as the work order warned, and
`prod_inv_pow_isPrimitiveRoot` (its `Fin`-indexed inverse form) is FLT's own.

### 10.4 The wire test, the checker, and the consumer

Both exports take `hζ : IsPrimitiveRoot (ζ : K) ℓ` over an arbitrary field, so
unlike T9's `intCoeffs` they have a **concrete instance**: `K = ℂ`, `ℓ = 2`,
`ζ = -1` via `IsPrimitiveRoot.neg_one`, carried out and named
`wire_zero_lead` (leading coefficient `= 1`) and `wire_eq_zero_of_le`
(`q ^ (-6)` coefficient of `(phiProd …).coeff 1` vanishes) inside the module. The
public surface is held at exactly the two wrappers. `Fact (Nat.Prime 2)` has no
global mathlib instance, so it is passed explicitly as `(hℓ := ⟨Nat.prime_two⟩)`
rather than with `haveI` (the style linter flags the latter).

**The checker needed one real extension.** FLT keeps the closure
`mono`/`neg`/`mul`/`qTwist`/`qExpand` and `conjPoleBound`/`tPoleOrderLE_conj`
`private` in all six files (several are exposed only through the `p2m_export`
alias, which a text differ cannot follow), and the generic last components
`neg`/`mul`/`qTwist`/`qExpand` already name *unrelated* public declarations in
`SOURCES` (`RealL.neg`, the `qTwist` def, …). So `spec/check_flt_statements.py`
now keeps a second source map of the pin's `private` declarations, keyed by the
port declaration's **dotted** name, and consults it only when the public
last-name lookup does not reproduce the statement; the port writes those methods
as `theorem TPoleOrderLE.neg` and the pin writes
`private theorem _root_.ModularCurve.PhiGen.TPoleOrderLE.neg`, so both reduce to
`TPoleOrderLE.neg`. The result: **11 of T10's 25 new statements are verified
against the pin's own `private` statements** rather than exempted, and the
checker reports them separately. It was tested non-vacuously (a mutated
`sum_conjPoleBound` is caught). The checker moved **180 → 205**.

The consumer gained Zone H: both exports bound, both in hypothesis form. Error
count still **0**; the single remaining `sorry` is the Zone A capstone. (The
look-ahead [TOPIC-datum-assembly.md](../topics/phiGenSplitting/TOPIC-datum-assembly.md)
for T11, written while this topic was in flight, plans its core bindings in
"Zone H"; this topic's own work order names Zone H, so **T11 takes Zone I**.)

### 10.5 What T10 leaves

The cone's (b) is complete: T9's `PhiGenDescends.intCoeffs` /
`aeval_jq_intCoeffs_descent` supply the integrality, and T10's two exports supply
the pole bounds, with the shared prelude public. **T11 is next**: the 328 block
(`c_top`/`c_eq_zero`/`poleOrderLE`/`sum_mul_jqN_pow_eq_zero`/`evalAtJ_injective`)
and the (d) assembly (`exists_modularPolynomialData_coeff_eq`, `eq_of_prime`). It
imports the whole prelude from `Defs/PhiGen.lean`; it does **not** need this
module's sharp `tPoleOrderLE_phiProd_coeff_of_ne_zero` (it uses the weaker
`tPoleOrderLE_phiProd_coeff`).

## 11. T11: the construction — descent, the 328 block, the datum

Three new modules, **701 lines**, **8 public** and 25 `private` declarations:

- `FLTForHuman/ModularCurve/PhiGenDescent.lean` (339 lines, 1 public + 18
  private) — (a)'s `PhiGen.exists_phiGenDescends`;
- `FLTForHuman/ModularCurve/PhiGenDescendsStructure.lean` (161 lines, 5 public + 2
  private) — the 328 block: `PhiGenDescends.c_top`, `.c_eq_zero`, `.poleOrderLE`,
  `.sum_mul_jqN_pow_eq_zero`, `evalAtJ_injective`;
- `FLTForHuman/ModularCurve/ModularPolynomialAssembly.lean` (201 lines, 2 public +
  5 private) — (d)'s `exists_modularPolynomialData_coeff_eq` and
  `splits_of_coeff_evalAtJ_eq`.

All eight public statements are the pin wrappers verbatim. One goal round (of the
4 budgeted; no checkpoint needed).

| | |
|---|---|
| goal rounds | **1** (of the 4 budgeted) |
| declarations | **8 public**, 25 `private` |
| lines written | **701**: 339 descent, 161 structure, 201 assembly |
| build | `lake build` 2594 jobs, green, **0 warnings**, no `sorry` |
| `#print axioms` | all eight: only `propext, Classical.choice, Quot.sound` |
| checker | `213 statements identical (11 promoted from pin-private), 0 mismatched, 0 missing` (205 → 213) |
| consumer | Zone I added and bound, with the first **end-to-end** wire test; **0 errors**, one `sorry` |

### 11.1 The dedup and the mathlib reuse

- **The 328 block.** Shipped in **seven** pin files (`7 × 328 = 2,296` lines); its
  distinctive content is 84 lines, the ~170-line prelude is T10's, so the port
  writes the block once at 161 lines (including a ~35-line header). The prelude's
  twelve-carrier count is T10's finding (log §10.1).
- **`evalAtJ_injective` by the mathlib route — closed first try.** The work order's
  §4.2 substitution worked exactly as hoped:
  `transcendental_iff_injective.mp transcendental_jq` composed with
  `Polynomial.map_injective _ Int.cast_injective` through the six-line
  `evalAtJ_eq_aeval_map` bridge. The pin's private 19-line `aeval_jq_eq_zero` is
  **not** ported; the port's own public `aeval_jq_eq_zero` (from `Defs/Jq.lean`,
  the `Thm_ModularCurve_aeval_jq_eq_zero` interface) is untouched and remains the
  named form of the same fact.
- **`coeff_aeval_jq_neg` is T9's.** The assembly pin's private copy was dropped and
  the `Defs/Jq.lean` lemma imported.
- **T12 imports `evalAtJ_injective`.** It is public in the structure module, so the
  895 block drops its private copy (the work order's §6). `coeff_coeffEmb_jq_of_lt`
  was likewise not ported — T10's block already carries the `jq`-pole facts.
- **`splits_of_coeff_evalAtJ_eq` is written once**, in the assembly module, and
  feeds both (e) and (f).

### 11.2 The cost

**701 port lines against ~590 deduplicated pin lines** — (a)'s 315, the block's
84 distinctive lines and the assembly's 191 — ratio **1.19** (T5 1.79, T6 1.06,
T7 1.05, T8 0.98, T9 0.93, T10 1.27). The excess is the three ~35–60-line module
headers plus the descent's 18 small private helpers (the pin makes most of them
public; the tight public surface is worth the extra private bridging).

### 11.3 The division, and the dependency finding

The work order's §4 cut is confirmed and was necessary: the blueprint's old T11
(the 328 block plus the whole 502-line (d) bucket) is **not executable as one
unit**. `evalSymm_of_coeff_evalAtJ_eq` imports T12's 895 block,
`exists_phiIrreducible_evalSymm` imports (a) + T8 + T9 + the assembly + the 895
block, and `finrank`/`eq_of_prime` sit downstream again. T11 therefore stopped at
the assembly; the symmetry/existence/uniqueness tail is T12/T13's, cut by
mathematical object (construction → properties → consequence). PORTING-PhiGen §6
Option 1's "circularity" worry is misplaced for the same reason: the assembly gets
degree `ℓ+1` from `c_top`/`c_eq_zero`, and `finrank` from the *other*,
irreducible datum.

### 11.4 The variable convention (the work order's §8 stop-early risk)

The assembled datum is `Φ = ∑_{k ≤ ℓ+1} Polynomial.C (Q k) * Polynomial.X ^ k`
with `C : Polynomial ℤ →+* Polynomial (Polynomial ℤ)` and `X` the **outer**
variable, so `Φ.coeff k = Q k` is the `Y^k` coefficient; the port's
`ModularPolynomialData.eval_eq_zero` (`Φ.eval₂ evalAtJ (jqN ℓ) = 0`) reads exactly
that outer variable. The pin's `hΦcoeff : evalAtJ (Φ.coeff k) = c k` and the
`Polynomial.eval₂_eq_sum_range' evalAtJ … (jqN ℓ)` step carried over verbatim —
**no rebinding was needed**. The three other stop-early items did not bite:
`Polynomial.lifts`' API matched, `tPoleOrderLE_of_qExpand`'s direction is T10's
export direction, and `IsCyclotomicExtension.exists_isPrimitiveRoot` needed only
the `haveI` instances the pin's `exists_phiIrreducible_evalSymm` already installs.

### 11.5 What T11 leaves

**T12 is next** — the properties: `one_le_coeff_jq` (386), the 895 block
(894 ×3, whose exports are `phiIrreducible_of_splits`,
`transposeToAdjoin_monic_of_qExpansion`, `evalSymm_of_splits`, plus the hidden
`aeval_jq_ne_jqN`/`jqN_not_mem_adjoin_jq`), `evalSymm_of_coeff_evalAtJ_eq` (124)
and `exists_phiIrreducible_evalSymm` (62). It imports T11's public
`evalAtJ_injective` and `exists_phiGenDescends`, T10's prelude and both pole-bound
exports, T9 and T8. **T13** then closes the cone: `finrank_adjoin_jqN_eq_of_prime`,
`ModularPolynomialData.eq_of_prime`, `splits_of_prime` and `splits_prime_at_slot`.

## 12. T12: the properties — the 895 block, once

Three new modules, **1670 lines**, **19 public** and 93 `private` declarations:

- `FLTForHuman/ModularCurve/JqCoeffPositivity.lean` (425 lines, 2 public + 27
  private) — `one_le_coeff_jq` and `coeff_jq_ne_zero`;
- `FLTForHuman/ModularCurve/ModularPolynomialIrreducible.lean` (1070 lines, 15
  public + 62 private) — the 895 block, once;
- `FLTForHuman/ModularCurve/ModularPolynomialProperties.lean` (175 lines, 2 public
  + 4 private) — `evalSymm_of_coeff_evalAtJ_eq` and the capstone
  `exists_phiIrreducible_evalSymm`.

Plus the `Defs/Jq.lean` promotion of `evalAtJ_eq_aeval_map` (T11's two private
copies and the block's `_rat` copy removed; T11 rebuilt green). All public
statements are the `Theorems/` wrappers verbatim, or the `S_` files' own public
declarations for the four non-wrapper exports. One goal round (of the 2–3
budgeted).

| | |
|---|---|
| goal rounds | **1** (of the 2–3 budgeted) |
| declarations | **19 public**, 93 `private` |
| lines written | **1670**: 425 positivity, 1070 block, 175 properties (+12 the `Defs/Jq` promotion) |
| build | `lake build` 3817 jobs, green, **0 warnings**, no `sorry` |
| `#print axioms` | all nineteen public declarations: only `propext, Classical.choice, Quot.sound` |
| checker | `233 statements identical (11 promoted from pin-private), 0 mismatched, 0 missing` (213 → 233) |
| consumer | Zone J added and bound, with the first **unconditional** wire test; **0 errors**, one `sorry` |

### 12.1 The dedup — the 895 block ships five times

`PORTING-PhiGen.md` §2's table recorded the 895-line block as **×3** (its three
graph nodes `evalSymm_of_splits`, `phiIrreducible_of_splits`,
`transposeToAdjoin_monic_of_qExpansion`). Measured, it ships in **five** files:
the two hidden exports `swapBivar_monic_of_coeff_bounds` and
`ModularPolynomialData.evalSymm_of_irreducible` each have their own ~894-line copy
too. So the pin spends **≈ 4,475** lines on one development; the port writes it
once at 1070 (including a ~55-line header and the ~60-line `SepFibre` block for
`swapBivar_eq_of_evalSymm`). The three reuse items landed: `conj_injective` and
`evalAtJGen_injective` are written once and public, `evalAtJ_injective` is T11's,
`coeff_aeval_jq_neg` is T9's, and `evalAtJ_eq_aeval_map` moved to `Defs/Jq.lean`
with all three copies deleted. T12's public `evalAtJ_injective` is what T13's
`eq_of_prime` will import. Post-close, the module was trimmed to **1023 lines /
57 private**; the redundancy found and removed is recorded in §16.

### 12.2 The cost

**1670 port lines against 1467 deduplicated pin lines** (386 + 895 + 124 + 62),
ratio **1.14** (T5 1.79, T6 1.06, T7 1.05, T8 0.98, T9 0.93, T10 1.27, T11 1.19).
The block itself is the largest single artefact of the sub-effort; three module
headers (~150 lines total) account for most of the excess over 1:1.

### 12.3 `one_le_coeff_jq`'s route — the substitution closed, the estimate did not

The work order's §3.1.9 mathlib substitution **did close**, in the two places it
could:

| piece | pin | port replacement |
|---|---|---|
| `coeff_prod_one_sub_X_pow_eq_coeff_one` (40-line induction) | `PowerSeries.coeff_mul_prod_one_sub_of_lt_order` + `order_X_pow` | one mathlib call in a 10-line wrapper |
| `geomSeries` + `one_sub_X_pow_mul_geomSeries` + its `coeff_*` lemmas (~45 lines) | `PowerSeries.expand d hd (PowerSeries.mk 1)` | `mk_one_mul_one_sub_eq_one` + `coeff_expand` |

`PowerSeries.coeff_prod_one_sub_X_pow_eventually_eq` was inspected but not used:
it relates the partial product to `pentagonalSeries`, and reaching the *specific*
truncation `∏_{i < n+1}` from it still needs the tail-coefficient argument, so the
pin's `coeff_etaProd_eq_coeff_partialProd` (`Tendsto` to a discrete limit) was
ported. The truncation-stable `coeff_inv_congr` and the `one_le_coeff_partialGeom_pow`
split are local. **Net: the predicted 190–250 lines (ratio ≈ 0.5–0.65) did not
materialise** — the module is 425 lines (≈370 of code) against the 386-line pin,
ratio ≈ 1.1. This is the T6/T9 "the audit's rightness and its savings diverge"
outcome: the two substitutions are real, but the irreplaceable truncation machinery
they do not cover dominates the file.

### 12.4 The shape issues

- **The fraction-field instances are scoped.** `Algebra (Algebra.adjoin F S)
  (adjoin F S)` and `IsFractionRing` are mathlib's **scoped** instances in
  `IntermediateField.algebraAdjoinAdjoin`; the pin activated them through its
  `p2m_open "… IntermediateField.algebraAdjoinAdjoin"`, which the port's textual
  translation dropped. The fix is an explicit
  `open scoped IntermediateField.algebraAdjoinAdjoin`. This was the only real
  blocker and it cost one build.
- **`IsIntegrallyClosed adjoinJq` needed no instance.** The pin's private scoped
  `UniqueFactorizationMonoid adjoinJq` (from `transcendental_jq.uniqueFactorizationMonoid_adjoin`)
  plus mathlib's UFD → integrally-closed path sufficed for
  `Monic.irreducible_iff_irreducible_map_fraction_map`; the instance stays in scope
  in the same module, as the work order's §8 asked.
- **Vieta matched `v4.34.0`.** `Polynomial.eq_of_natDegree_lt_card_of_eval_eq`
  (with the `eval`/`max`-degree side condition) and
  `Polynomial.prod_X_sub_C_coeff_card_pred` elaborated in the pin's spelling; no
  reshaping was needed. `Polynomial.degree_sub_lt` is deprecated in favour of
  `Polynomial.degree_sub_lt_left`. The `haveI` style linter fired once (the
  cyclotomic instances in `aeval_jq_ne_jqN`) and was disabled locally.
- **Wrapper spellings again.** Two public declarations verified against a
  `Theorems/` wrapper had been written with the `S_` file's section variables
  (`aeval_jqN_toAdjoin`, `minpoly_jqN_eq`); the checker flagged both, and explicit
  wrapper binders fixed them. The T7-log §7.3 rule — *match the wrapper, not the
  `S_` file, for any public declaration the checker verifies* — holds for the
  fourth topic running.

### 12.5 What T12 leaves

**T13 is next and last.** It consumes `exists_phiIrreducible_evalSymm` (for
`finrank_adjoin_jqN_eq_of_prime` and `eq_of_prime`) and T11's public
`evalAtJ_injective`, and delivers `finrank_adjoin_jqN_eq_of_prime`,
`ModularPolynomialData.eq_of_prime`, `splits_of_prime` and
`splits_prime_at_slot` — the cone's exported statement.

## 13. T13: the consequence — uniqueness, the degree, and the cone closed

Two new modules, **407 lines**, **4 public** and 12 `private` declarations:

- `FLTForHuman/ModularCurve/ModularPolynomialUniqueness.lean` (133 lines, 2 public
  + 4 private) — `ModularCurve.finrank_adjoin_jqN_eq_of_prime` and
  `ModularCurve.ModularPolynomialData.eq_of_prime`;
- `FLTForHuman/ModularCurve/PhiGenSplits.lean` (274 lines, 2 public + 8 private) —
  `ModularCurve.PhiGen.splits_of_prime` and the cone's headline
  `ModularCurve.PhiGen.splits_prime_at_slot`.

All four public statements are the pin wrappers verbatim, and this is the first
topic whose public surface matched the wrappers on the first build (the T7 §7.3
rule was applied by construction, not debugged). One goal round (of the 1–2
budgeted); module 2's first build had no proof errors, only linter clean-up.

| | |
|---|---|
| goal rounds | **1** (of the 1–2 budgeted) |
| declarations | **4 public**, 12 `private` (+5 public in `Defs/Cyclotomic.lean`) |
| lines written | **407** (133 + 274) + `Defs/Cyclotomic.lean` (58) |
| build | `lake build` 3863 jobs, green, **0 warnings**, no `sorry` |
| `#print axioms` | all four: only `propext, Classical.choice, Quot.sound` |
| checker | `242 statements identical (11 promoted from pin-private), 0 mismatched, 0 missing` (233 → 237 → 242) |
| consumer | Zone K added and bound, with the cone's end-to-end capstone wire; **0 errors**, one `sorry` (the FFG capstone) |

### 13.1 The dedup — the prelude was already ported, and ~200 lines were dead

The two big pin files (353 + 288 lines) share a ~95-line `TS` prelude of 16
declarations. **Eleven are already public in the port**: `Defs/TS.lean` carries
`TS` and its ten lemmas verbatim, and `Defs/Laurent.lean` carries
`coeffEmb_qExpand`. T13 needed only three 1–3-line bridges (`iota_jq`,
`conj_zero_eq`, `conj_succ_eq`), written once.

The larger find is that **neither exported theorem uses ~200 lines of the pin's
prelude**:

- in `splits_of_prime`: `iota_jqN`, `qTwist_iota_of_pow_eq_one`,
  `qTwistEquiv`/`qTwistEquiv_apply`/`coe_qTwistEquiv`, `qTwist_TS_one_cycle`,
  `phiProd_conj_eq`, `roots_phiProd_conj`, `roots_phiProd_conj_nodup`, and the
  whole `phiAtSeed` block (8 declarations, 214–257);
- in `splits_prime_at_slot`: the roots API `prod_form_ne_zero`,
  `roots_prime_at_slot`, `roots_prime_at_slot_nodup`,
  `roots_prime_at_slot_roots_nodup`, `isRoot_prime_at_slot_iff` (the theorem ends
  at line 180; the block is a self-contained description for other consumers).

None is a node of the 44-node closure; they exist so the two 607-line
`*_of_isPrimitiveRoot` char-`p` variants (byte-identical to each other, over
`jqModC`, which the port has not ported) can share a body. T13 drops them.

### 13.2 The cost

**407 port lines against 766 deduplicated pin lines** (52 + 73 + 353 + 288),
ratio **0.53** — the sub-effort's cheapest, and the first below 0.93. The two
modules' headers account for most of the difference above the ~350 live pin
lines.

### 13.3 The capstone wire, and the cone closed

Zone K instantiates the headline at `K = CyclotomicField 2 ℚ`, `N = p = 2`,
`e = 1`, `u = 1` — the first genuine application of `splits_prime_at_slot` with no
unported hypothesis — and binds `eq_of_prime` (two data at `p = 2` agree) and
`finrank_adjoin_jqN_eq_of_prime` (`[ℚ(j)(j(q^2)) : ℚ(j)] = 3`).

With T13 landed, **all 44 nodes below `PhiGen.splits_prime_at_slot` are public and
every wrapper is verified**. The consumer's remaining `sorry` — the unconditional
`FunctionFieldGeneration N` — is the FFG `Inputs` gap, not this cone's: the seven
`Inputs` fields of `PORTING-FFG.md` §7.8 (T14–T19) can now be proved with
`splits_prime_at_slot` as a theorem rather than an input.

### 13.4 Promotions, and one carried forward

- **Done.** The cyclotomic roots (`exists_isPrimitiveRoot_cyclotomicField`,
  `cycUnit`, `cycUnit_spec`, `cycUnit_pow`, `isPrimitiveRoot_pow_div`) were
  private twins in this topic's module and in
  `FunctionFieldGeneration/Spine.lean`; T13 promoted them to the new public
  `Defs/Cyclotomic.lean` and deleted both private copies. The checker verifies
  them against the two pin `splits_*` `S_` files, which is why the count is 242
  rather than 237.
- **Carried forward.** `coeffMap_qTwist` remains private in `PhiGenSplits.lean`,
  duplicating the *more general* private copy in `PhiGenIntegrality.lean` (and
  T11's `PhiGenDescent.lean` copy is a genuinely different statement, with an
  explicit `v`/`huv`). Promoting the general form to `Defs/Twist.lean` and
  rewriting its three consumers is a dedicated cleanup of T9/T11's surfaces, not
  part of the capstone; it is recorded here so it is not lost.

### 13.5 What T13 leaves

The cone is closed. Nothing of the plan remains to be executed; it is retired to
[topics/PORTING-PhiGen.md](../topics/PORTING-PhiGen.md), and the parent FFG effort
(PORTING-FFG §7.8's T14–T19) proceeds from here, with `splits_prime_at_slot` now
a ported theorem.

## 14. Closing review: math clarity and clutter reduction

The cone is closed and the plan retired to
[topics/PORTING-PhiGen.md](../topics/PORTING-PhiGen.md). This section is the
sub-effort's closing review: what the port made clear, what duplication it
removed, and what did not go to plan.

### 14.1 Math clarity

The pin's cone is one 44-node closure whose doc-site graph explains *what depends
on what* but not *what any of it means*. The port's decomposition gave it six
separable mathematical pieces, each now a named module with a one-page account:

| piece | mathematics | topic | module(s) |
|---|---|---|---|
| (a) | coefficients of the conjugate product descend to `ℚ((q))` | T11 | `PhiGenDescent.lean` |
| (b) | integrality (`intCoeffs`) and the pole bounds | T9, T10 | `PhiGenIntegrality.lean`, `PhiGenPoleBounds.lean` |
| (c) | membership in `ℚ[jq]` — the level-one q-expansion principle, the one analytic input | T5–T8 | `ModularForms/*`, `PhiGenDescends.lean` |
| (d) | assembly into a datum; degree, symmetry, existence, uniqueness | T11, T12, T13 | `ModularPolynomialAssembly.lean`, `ModularPolynomialIrreducible.lean`, `ModularPolynomialProperties.lean`, `ModularPolynomialUniqueness.lean` |
| (e) | the 328 block plus irreducibility/symmetry | T11, T12 | `PhiGenDescendsStructure.lean`, `ModularPolynomialIrreducible.lean` |
| (f) | the splitting statement and its wrapper | T13 | `PhiGenSplits.lean` |

What the port made explicit that the pin left implicit:

- **The dependency order is a partial order, not the pin's file order.** T11's
  work order found that the old "T11 = 328 + the whole (d) bucket" straddles four
  waves: the 328 block and assembly are upstream of (e), while symmetry,
  existence, `finrank` and `eq_of_prime` are downstream of it and of (a). The
  construction → properties → consequence cut is what made the topic executable.
- **`eq_of_prime` is load-bearing, not bookkeeping.** It is the step that
  identifies the *caller's* datum with the one assembled from the descended
  family; without it `splits_of_prime` would only prove the identity for the
  constructed datum. Reading the 73-line file as a side lemma misses the
  structure of the whole proof.
- **Where positivity actually enters.** `one_le_coeff_jq` is stated for all `n`,
  but the whole cone uses it only at `n = ℓ` (`coeff_sum_conj_succ_ne_zero`); the
  strength of the statement is understood, and `coeff_jq_ne_zero` names the
  weaker form.
- **The old Option 1 "circularity" worry is resolved.** PORTING-PhiGen §6 feared
  that the degree `ℓ+1` came from the degree it was proving. It does not: the
  assembly reads `ℓ+1` off the explicit product (`c_top`, `c_eq_zero`), while
  `finrank_adjoin_jqN_eq_of_prime` reads it off the *other*, irreducible datum
  T12 constructs. There is no cycle, only a missing prerequisite.
- **base/006 §6.3 compresses two facts into one.** Its "pole bound plus
  holomorphy makes each coefficient a polynomial in `j`" is, in the Lean, a
  hypothesis (`mem_adjoin_jq_of_phiGenDescends`, piece (c), the analytic input)
  and a separate degree bound; a reader following the prose walks past a third of
  the cone. It is flagged in PORTING-PhiGen §7.

The measurements corrected three of the plan's own counts: the `TPoleOrderLE`
prelude is carried by **twelve** pin files, not six; the 895-line block ships
**five** times, not three (two hidden exports have their own copies); the 328
block ships in **seven** files, not five. And T13 found that **~200 lines** of
the `splits_*` files' prelude are dead for their exported theorems — they exist
for the char-`p` variants outside the cone.

The mathlib-first audit's character stayed the same throughout: **negative on
statements, positive on primitives**. No mathlib lemma replaces an export, but
the useful substitutions were still worth finding — T5's three, T12's two
(`coeff_mul_prod_one_sub_of_lt_order`, `PowerSeries.expand` +
`mk_one_mul_one_sub_eq_one`), and T13 needed none at all. The near-misses were all
of one shape, hypothesis-versus-conclusion: `pow_sum_range_isPrimitiveRoot` is the
*product* of powers of a primitive root where mathlib has the *sum*;
`IsPrimitiveRoot.isIntegral` needs primitivity where the cone only has
`ζ ^ ℓ = 1`; the partition generating functions give no `1 ≤ coeff` lemma. Each
is recorded so the next reader does not repeat the search.

### 14.2 Clutter reduction

The pin ships three developments repeatedly; the port writes each once. Measured:

| shared development | pin copies | pin lines shipped | port | duplicate lines not written |
|---|---|---|---|---|
| the 895 block (irreducibility/symmetry) | **5** | ~4,475 | 1,023 | ~3,452 |
| the 328 block (the descended family's shape) | **7** | 2,296 | 161 | ~2,135 |
| the `TPoleOrderLE` prelude | **12** carriers | ~2,040 | 202 (`Defs/PhiGen.lean`) | ~1,838 |
| T13's shared `TS` prelude + dead code | 2 (+ variants) | ~641 | 274 | ~367 |
| `coeff_aeval_jq_neg` | 9 private copies | ~144 | 1 (`Defs/Jq.lean`) | ~128 |
| T7's `RealL`/glue, duplicated into T8 | 2 | ~97 | imported | ~97 |
| the cyclotomic roots | spine + T13 + 2 pin files | ~140 | 58 (`Defs/Cyclotomic.lean`) | ~82 |
| `evalAtJ_eq_aeval_map` | 3 private copies | ~18 | 1 (`Defs/Jq.lean`) | ~12 |

(The first three rows overlap — the 328 block's shipped count includes the
prelude — so the aggregate is a conservative "several thousand pin lines the port
never wrote", consistent with PORTING-PhiGen §2's 9,304 → 5,811 measurement, now
corrected upward by the ×5 and ×12 findings.) The point is not the line saving:
it is that each of these is now one declaration with one proof, in dependency
order, so a later topic imports it instead of carrying a copy that can drift.

The promotions did the same for the *outbound* interface: `coeff_aeval_jq_neg`
and `poleOrderLE_aeval_jq` (T9), `evalAtJ_eq_aeval_map` (T12), the cyclotomic
roots (T13), and finally the two analytic exports §2.1 named
(`qExpansion_discriminant_eq_map_X_mul_dedekindEtaUnit`,
`qExpansion_E4_eq_map_eisenstein4`), which raised the checked out-of-cone
interface coverage to 94% and the checker to **244** statements. The one
promotion deliberately left open is `coeffMap_qTwist` (§13.4).

### 14.3 What did not go to plan

Honest accounting, so the next effort prices its topics better:

- **Ratios above 1 for the cone-algebra topics** (T10 1.27, T11 1.19, T12 1.14)
  against 0.93–1.06 for the analytic ones. The excess is not mathematics: it is
  module headers, a deliberately tight public surface, and private bridging
  helpers. Lines are not effort, but they *are* surface, and the port chose the
  smaller surface every time.
- **Two of T12's three mathlib substitutions landed, the third did not save
  lines.** `coeff_prod_one_sub_X_pow_eventually_eq` reaches `pentagonalSeries`,
  not the specific finite truncation the proof needs, so the pin's truncation
  machinery was ported; the positivity module came in at ratio ≈1.1, not the
  predicted 0.5–0.65.
- **The wrapper-binding rule took several topics to internalize.** It recurred
  through T12 (the consumer's notes count the T12 case as the "fourth time") and
  was restated in the T10–T12 work orders; T13 is the first topic to apply it from
  the start. Public declarations verified against a `Theorems/` wrapper must carry
  the wrapper's binders, not the `S_` file's section variables. It is written down
  in T7's log §7.3, in every later work order, and now in the playbook's §7.4.
- **One promotion deferred** (`coeffMap_qTwist`), because its three copies are not
  the same statement.

### 14.4 How to read the cone now

- the mathematics: [math/010](../../math/010-function-field-generation.md) §3, and
  [base/006](../../base/006-the-modular-equation.md) §3 and §6;
- the analytic input: [base/013](../../base/013-riemann-existence-and-the-q-expansion-principle.md);
- the decisions and sizes: the retired plan
  [topics/PORTING-PhiGen.md](../topics/PORTING-PhiGen.md);
- the per-topic work orders and their measured outcomes: the nine files in
  [topics/phiGenSplitting/](../topics/phiGenSplitting/), and §5–§13 here;
- the interface: the 44 nodes are public; `splits_prime_at_slot` is a theorem.

## 15. Post-close follow-up: the cyclotomic root now sources from mathlib

The 2026-09-22 bridge audit ([audit-prelude-bridges.md](audit-prelude-bridges.md)
§a.1) found the one genuine mathlib collision T13 left: `Defs/Cyclotomic.lean`'s
five declarations were a re-proof of `IsCyclotomicExtension.zeta`/`zeta_spec`/
`zeta_pow` and `IsPrimitiveRoot.pow`. They are now mathlib-sourced, with every
statement untouched:

| declaration | was | now |
|---|---|---|
| `exists_isPrimitiveRoot_cyclotomicField` | `IsCyclotomicExtension.exists_isPrimitiveRoot` | `⟨zeta N ℚ _, zeta_spec N ℚ _⟩` |
| `cycUnit` | `.choose_spec.isUnit … \|>.unit` | `(zeta_spec N ℚ _).isUnit … \|>.unit` |
| `cycUnit_spec` | `.choose_spec` | `rw [cycUnit, IsUnit.unit_spec]` + `zeta_spec` |
| `cycUnit_pow` | `(cycUnit_spec N).pow_eq_one` | unchanged (`zeta_pow` is the equally short alternative) |
| `isPrimitiveRoot_pow_div` | 9 lines of `pow_of_dvd`/`div_div_self` | 2 lines of `IsPrimitiveRoot.pow` + `Nat.div_mul_cancel` |

**Verification.** `lake build` green (3869 jobs), the statement checker
**288 identical, 0 mismatched, 0 missing** (unchanged — the statements are the
pin's verbatim), `#print axioms` clean. The route was checked in `Scratch.lean`
first; the section/`variable` form was rejected because
`spec/check_flt_statements.py` parses declarations textually, so the binders must
stay on each declaration line.

**Honest measurement.** `Defs/Cyclotomic.lean` went **70 → 78 lines**, of which 12
are the new header note, so the proof content is **−4 net**: the one `haveI`
instance argument `zeta` needs costs about what the shortened proofs save, and
the pin's redundant `haveI : NeZero ((N : ℕ) : ℚ)` is dropped (mathlib synthesizes
it from `[NeZero N]`). The larger gain is mathlib alignment — `cycUnit` is now
defeq to mathlib's chosen root — and the removal of the re-proof; the audit's
"≈18 lines" was per pin copy, and the pin carries 40 of them.

## 16. Post-close review: T12's private layer, and mathlib for `swapBivar`

A review of `ModularPolynomialIrreducible.lean` — prompted by the "large file
with a lot of private theorems" smell — found five private declarations that were
redundant and three proofs that re-derived mathlib. Public statements are
untouched; the change is confined to private helpers and proof bodies.

| deleted / collapsed | replacement |
|---|---|
| `coeff_aeval_jq_of_lt` (~8 lines) | `Defs/PhiGen.lean`'s `poleOrderLE_aeval_jq` — literally the same body |
| `coeff_aeval_jq_neg_natDegree` (~13) | `Defs/Jq.lean`'s `coeff_aeval_jq_neg P le_rfl` (T11 already used this form) |
| `qEmbedT_eq_coeffEmb_qExpand` (~5) | `Defs/Laurent.lean`'s `coeffEmb_qExpand` |
| `ev_eq_evalEval` (~3) | `Polynomial.eval₂_eval₂RingHom_apply` |
| `map_ev` (~5) | naturality `Polynomial.map_mapRingHom_evalEval` |
| `ev_int` (8-line `map_id` proof) | two mathlib calls, restated `A`-generic so it absorbs `map_ev`'s job |
| `swapBivar_eval₂` (~20) | `Bivariate.aevalAeval_swap`, via the private bridge `swapBivar_eq_swap` |
| `swapBivar_C` (~12) | `Bivariate.swap_C`, via the same bridge |

The `SepFibre`/`SepFibreMain` sections became `SwapBivarGlue`/`EvalSymmSwap`:
`swapBivar_eq_swap` is the one conversion helper, and the `ev`/`aevalAeval` glue
lives beside it so the transpose and symmetry proofs can cite mathlib. **No `Defs`
API change** — `swapBivar`, `swapBivar_X`, `swapBivar_C_X` and `swapInner` stay,
and `swapInner` remains in use by `swapBivar`'s own definition.

**The instance wrinkle.** `EvalSymm` evaluates with
`(Polynomial.aeval (R := ℤ) x).toRingHom`, while mathlib's `aevalAeval` is
indexed by an `Algebra ℤ` instance, and at `LaurentSeries ℚ` the
`powerSeriesAlgebra` and `Ring.toIntAlgebra` structures are propositionally but
not definitionally equal — so a direct `aevalAeval` rewrite does not unify. The
`ev` layer (`eval₂RingHom (Int.castRingHom A)`) plus `aeval_toRingHom_eq` (proved
by `RingHom.ext_int`, instance-agnostic) is the meeting point. It is
load-bearing, not duplication, and is the reason the review did *not* delete the
whole `ev` section.

| | |
|---|---|
| module | **1070 → 1023 lines**; 15 public + **57** private (was 62; the one `private scoped instance` excluded) |
| T12 total | **1670 → 1623 lines**; private **93 → 88**; port/pin ratio **1.14 → 1.11** |
| build | `lake build` green, no `sorry` |
| `#print axioms` | clean on all public declarations |
| checker | 0 mismatched, 0 missing (the removed declarations are private helpers, not public statements) |

This is §14.2's point applied recursively: those promotions removed *pin* copies,
and this pass removed the *port's own* copies of what it had promoted. The five
deletions were all reuse misses the §3.1 list had not named — including the two
coefficient lemmas, where T11 wrote the short public form and T12 re-proved it
privately.

