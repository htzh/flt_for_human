# The Φₚ splitting / R1 sub-effort — record

**Status: T5 complete (2026-09-21).** This is the running record for the
sub-effort [PORTING-PhiGen.md](../PORTING-PhiGen.md) opens: the R1 (level-one
q-expansion principle) sequence that gives the Φₚ splitting cone its one analytic
input. It is separate from the parent `functionFieldGeneration` record
([ffg-port.md](ffg-port.md)) — the parent's cone and this sub-effort share no
declaration, and the sub-effort's first topic is not on `ffg-port.md`'s layer
table, so the measured cost lives here rather than as an append there.

The executed plan is
[TOPIC-r1-kernel.md](../topics/phiGenSplitting/TOPIC-r1-kernel.md); the
mathematics of record is
[base/013](../../base/013-riemann-existence-and-the-q-expansion-principle.md) §3,
§5.4, §6. FLT is pinned at `aa2d8b3`; mathlib at `v4.34.0`.

## 0. Where the sub-effort stands

| topic | deliverable | status | measure |
|---|---|---|---|
| **T5** | R1's constancy kernel + the `n = 0` corollary, in `FLTForHuman/ModularForms/` | **done**, 1 module, 2 public + 6 private, 333 lines | kernel verbatim; checker 151; axioms clean |
| T6 | the analytic model of `jq` | not started | — |
| T7 | the Hauptmodul form | not started | — |
| T8 | the cone application (Hecke translates) | not started | — |

R1 = T5–T7; T8 is the cone's (c). The topic's whole deliverable is one file:

| module | lines | decls | FLT source (`aa2d8b3`) |
|---|---|---|---|
| `FLTForHuman/ModularForms/QExpansionPrinciple.lean` | 333 | 2 public + 6 `private` (+1 `example`) | `P2M/Sol/S_ModularCurve_coeff_eq_zero_of_hasSum_of_slash_invariant.lean` (186) |

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
  to `SOURCES`; the verified count is 151) and exempts the corollary explicitly
  in `OWN_PROOFS`, with the reason commented there.
- **T6 should check mathlib first**, and specifically watch the `FunLike` trap of
  §2.2 when comparing a `HasSum` presentation of `jq` with a mathlib `qExpansion`
  presentation.
