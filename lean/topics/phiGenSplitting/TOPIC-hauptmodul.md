# Topic 7: the Hauptmodul form

**Status: done (2026-09-22), one goal round — R1 is complete.** The module is
`FLTForHuman/ModularForms/Hauptmodul.lean`, green with 0 warnings and no `sorry`;
the measured cost and the audit accounting are in
[logs/phiGen-port.md](../../logs/phiGen-port.md) §7. The next topic is T8, the
cone application ([PORTING-PhiGen.md](../PORTING-PhiGen.md) §5); this topic's
`RealL` closure and `hasSum_qParam_mul{,_laurent}` are its interface. This file is
kept as the executed plan. Third topic of the Φ_p
splitting / R1 sub-effort. The plan is
[PORTING-PhiGen.md](../PORTING-PhiGen.md); the mathematics is
[base/013](../../../base/013-riemann-existence-and-the-q-expansion-principle.md)
§5.3–§5.5. T5 (the kernel) and T6 (the analytic model of `jq`) are executed; their
records are [TOPIC-r1-kernel.md](TOPIC-r1-kernel.md),
[TOPIC-jq-model.md](TOPIC-jq-model.md) and
[logs/phiGen-port.md](../../logs/phiGen-port.md).

> **Build discipline — read this first.** Every build is bounded and a blow-up is
> quarantined, not waited on. Measured with mathlib prebuilt: a green
> `lake env lean <module>` of this size is **~4 s**, `lake build <module>` with
> deps cached **~2–5 s**, and a `whnf`/heartbeat timeout at the default cap
> **errors in ~15–20 s** — it does not hang.
>
> - Run every build under a bound: `timeout 60 lake env lean <file>`,
>   `timeout 120 lake build <module>`. Non-return at 60 s is a blow-up.
> - **Quarantine immediately.** On a timeout, comment the declaration out and
>   bisect, or reproduce in the gitignored `Scratch.lean` with
>   `set_option diagnostics true`. Do not re-run the same file hoping for a
>   different result.
> - **Never raise `maxHeartbeats`.** The cap already fails in under 20 s; raising
>   it turns that into an unbounded wait. The usual cause is a `FunLike`-quantified
>   lemma instantiated at a bare function type (`DFunLike.coe` unfolds without
>   bound) — restate it over the concrete function instead. T5's log §2.2 has the
>   worked example.

**Audience.** A fresh session taking this topic. Read, in this order:

1. [PORTING-PhiGen.md](../PORTING-PhiGen.md) §3–§5 — the cone, the R1/R2
   split, and this topic's place in the sequence;
2. [base/013](../../../base/013-riemann-existence-and-the-q-expansion-principle.md)
   §5.3 (pole killing), §5.4 (the constancy kernel), §5.5 (the headline);
3. [TOPIC-jq-model.md](TOPIC-jq-model.md) and
   [logs/phiGen-port.md](../../logs/phiGen-port.md) §6 — the interface this topic
   consumes and the "price the glue, not the mathlib-replaceable leaves" warning;
4. [porting-playbook.md](../../porting-playbook.md) §3, especially §3.9 and
   §3.11.

**Goal.** One new module, `FLTForHuman/ModularForms/Hauptmodul.lean` (mathlib plus
the port's `Defs/`), green, zero warnings, zero `sorry`. The headline, verbatim
from its wrapper:

```lean
theorem ModularCurve.mem_adjoin_jq_of_hasSum_of_slash_invariant
    (f : LaurentSeries ℚ) (F : UpperHalfPlane → ℂ)
    (hF : ∀ τ : UpperHalfPlane, HasSum (fun m : ℤ => ((f.coeff m : ℚ) : ℂ) *
        Function.Periodic.qParam 1 (τ : ℂ) ^ m) (F τ))
    (hinv : ∀ (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (τ : UpperHalfPlane), F (γ • τ) = F τ) :
    f ∈ Algebra.adjoin ℚ {ModularCurve.jq}
```

"a level-one modular function that is holomorphic on `ℍ` and has a pole of order
at most `n` at the cusp is a polynomial in `j` of degree at most `n`" — R1's
Hauptmodul form, and the completion of R1.

Because T8 consumes them, also **public** (this is the topic's one deliberate
divergence from "helpers private"):

- `RealL` and its closure block — `add`, `neg`, `sub`, `mul`, `single`, `C`,
  `one`, `zero`, `congr`, `prod`, `coeff_prod_X_sub_C`;
- `hasSum_qParam_mul`, `hasSum_qParam_mul_laurent`.

Everything else — the pole-killing block, `realL_aeval_jq`, the `jt`/`jqC` glue,
`mem_adjoin_jq_of_realL_invariant` — is an implementation detail and goes
**private**. In particular **do not edit** `QExpansionPrinciple.lean` (T5): its
`mem_adjoin_jq_of_poleOrderLE_zero` is the `n = 0` case, survives as a convenience,
and [logs/phiGen-port.md](../../logs/phiGen-port.md) §4 records the decision.

## 1. Why this topic, and what is settled

R1 has two forms. T5 delivered the kernel (an arbitrary holomorphic invariant
`q`-series is constant); T6 gave `jq` an analytic realization. T7 is the form
that is actually consumed: an arbitrary pole-bounded realized invariant series is
a *polynomial* in `jq`. Its proof is the pin's three-step argument — kill the
pole with a polynomial in `jq`, apply the kernel to the remainder, read off the
sum — and it closes R1.

- **Settled: this is the glue topic.** T6's log §6 warned explicitly: price the
  glue, not the mathlib-replaceable leaves. T7 is almost entirely glue. The audit
  in §2.1 finds **no** public mathlib statement for `RealL`, its closure, the
  pole-killing lemma, or the headline; mathlib supplies only the Cauchy-product
  core inside `hasSum_qParam_mul{,_laurent}` and the `HahnSeries`/`qParam` API
  around it. Expect roughly 1:1 against the ~462-line pin.
- **Settled: export the T8 interface.** FLT *duplicates* the `RealL` block across
  this topic's pin file and T8's
  (`S_ModularCurve_PhiGen_PhiGenDescends_hasSum_cosetPoly_coeff.lean` defines its
  own `RealL` and closure). The port does it once, here, public, and T8 imports
  it — the "deduplicate at the source" rule of [porting-playbook.md](../../porting-playbook.md)
  §2. Say so in the module header.
- **Settled: the headline's statement is the pin's, verbatim.** Its wrapper
  exists, so `spec/check_flt_statements.py` verifies it. Add the wrapper to
  `SOURCES`. The newly public `RealL`/`hasSum_qParam_mul*` also have `Thm_`
  wrappers — verify them too (`hasSum_qParam_mul_laurent`'s wrapper statement is
  in the pin at the `solution`).
- **Settled: T5's kernel is consumed here, and T6's declarations too.** The
  headline calls `coeff_eq_zero_of_hasSum_of_slash_invariant` (T5) on the
  remainder, and the `RealL` block's `realL_jqC`/`realL_aeval_jq` call
  `hasSum_jq_qParam` and `E4_cube_div_discriminant_smul` (T6). So the module
  imports `QExpansionPrinciple` and `JqAnalyticModel`.
- **Settled: T8 is not this session's business.**

## 2. The scouted inventory

Four pin files, ~462 lines:

| pin file | lines | content |
|---|---|---|
| `S_ModularCurve_hasSum_qParam_mul.lean` | 80 | products of power-series `q`-expansions on `ℍ` (Cauchy product) |
| `S_ModularCurve_hasSum_qParam_mul_laurent.lean` | 84 | the Laurent case, via `single_mul` and the order split |
| `S_ModularCurve_exists_aeval_jq_sub_holomorphicAtInfty.lean` | 84 | pole killing: the triangularity of `j`'s powers |
| `S_ModularCurve_mem_adjoin_jq_of_hasSum_of_slash_invariant.lean` | 214 | `RealL`, its closure, `realL_aeval_jq`, and the headline |

Declaration inventory, with the two files that hold the API T8 will reuse:

| declaration | pin lines | size |
|---|---|---|
| `norm_qParam_lt_one_of_pos` | mul 18–21 | 4 |
| `summable_norm_of_hasSum_qParam` | mul 22–45 | 24 |
| `hasSum_qParam_mul'` | mul 46–78 | 33 |
| `hasSum_single_mul_coe_iff` | laurent 22–43 | 22 |
| `hasSum_qParam_mul_laurent'` | laurent 44–82 | 39 |
| `poleOrderLE_iff_le_order` | hol 14–17 | 4 |
| `exists_poleOrderLE` | hol 18–20 | 3 |
| `poleOrderLE_aeval_jq` | hol 21–29 | 9 |
| `coeff_aeval_jq_neg` | hol 30–46 | 17 |
| `poleOrderLE_sub_aeval_jq_succ` | hol 47–58 | 12 |
| `exists_aeval_jq_sub_holomorphicAtInfty'` | hol 59–78 | 20 |
| `RealL` (`add`/`neg`/`sub`/`mul`/`single`/`C`/`one`/`zero`/`congr`/`prod`) | mem 30–78 | ~52 |
| `coeff_prod_X_sub_C` | mem 79–117 | 39 |
| `jt`, `castC`, `jqC`, `jqC_coeff`, `realL_jqC`, `jt_smul` | mem 118–134 | ~17 |
| `realL_aeval_jq` | mem 135–154 | 20 |
| `mem_adjoin_jq_of_realL_invariant` (the headline body) | mem 155–210 | 56 |

### 2.1 The mathlib-first audit

Audited against our pinned `v4.34.0`. **This topic is the glue**: unlike T5 and
T6, there is almost nothing for mathlib to replace. What it does supply:

| pin piece | mathlib `v4.34.0` | verdict |
|---|---|---|
| `norm_qParam_lt_one_of_pos` | `Periodic.norm_qParam_lt_one` / `norm_qParam_lt_iff` | replace (4 lines) |
| `summable_norm_of_hasSum_qParam` | none — the bridge from a `HasSum` on `ℍ` to absolute summability | port |
| `hasSum_qParam_mul'` | the Cauchy-product **core**: `tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm`, `summable_norm_sum_mul_antidiagonal_of_summable_norm` (Analysis/Normed/Ring/InfiniteSum) | port the wrapper; the core is mathlib's |
| `hasSum_single_mul_coe_iff` | `HahnSeries.single_mul_single`, `single_mul`; the shift is `Function.Injective.hasSum_iff` | port |
| `hasSum_qParam_mul_laurent'` | `HahnSeries` order API: `single_order_mul_powerSeriesPart`, `coeff_eq_zero_of_lt_order`, `le_order_iff_forall`; plus the two above | port |
| `RealL` and its closure | none; mathlib has `UpperHalfPlane.cuspFunction_mul` for the *cusp function*, not the pointwise `HasSum` predicate | **port** |
| `coeff_prod_X_sub_C` | none | **port** |
| `realL_aeval_jq` | none; it is the induction that `P(jq)` is realized by `P(jt)` | **port**; uses T6 |
| `exists_aeval_jq_sub_holomorphicAtInfty` + its five helpers | `HahnSeries` order/coefficient lemmas (`coeff_eq_zero_of_lt_order`, `le_order_iff_forall`); the triangularity of `j`'s powers is the port's | **port** |
| `mem_adjoin_jq_of_realL_invariant` | none; T5's kernel plus this topic's pole killing | **port** |

**Headline.** No public mathlib lemma replaces any of the four pieces that carry
the mathematics (`RealL`, pole killing, `realL_aeval_jq`, the headline). The
audit's value here is negative information — it tells the session *not* to hunt
for mathlib analogues and to budget the port as a port. The `FunLike` trap is not
expected (nothing is instantiated at a bare function type), but the discipline
stands.

**Post-execution note (2026-09-22).** The audit held exactly: no blow-up, and the
module typechecked on the first bounded `lake env lean`. The port is **483 lines**
against the ~462-line pin (ratio 1.05), 15 public and 16 private declarations —
the "glue is 1:1" prediction. The one drift was `if_pos` → `ite_eq_left` in
`hasSum_single_mul_coe_iff`. Two things worth carrying to T8: (i) the exported
`RealL` closure came out exactly as scoped (T8 can import all of it), and
(ii) **a statement-checker constraint, not a mathematical one**: public
statements had to be written in the *wrappers'* raw spelling (`UpperHalfPlane → ℂ`
and `Function.Periodic.qParam`), while `RealL` — whose comparable source is the
`S_` file — keeps `ℍ` and the local `𝕢`; the checker's diff is textual. Full
accounting in [logs/phiGen-port.md](../../logs/phiGen-port.md) §7.

## 3. What is different about this topic

- **It exports an API, not just a result.** The `RealL` block is FLT-duplicated
  and T8 needs it; the port exports it once. This is the first topic in the
  sub-effort whose interface is as important as its theorem.
- **It combines both earlier topics.** The kernel is T5's, the realization is
  T6's; the headline is the first statement that genuinely spans the sub-effort.
  A failure here is a failure of the interface, which is exactly what the
  cross-module wire test (§4) is for.
- **It closes R1.** After T7, R1 is done; T8 is the cone's application, not R1.
- **`PoleOrderLE` is the port's** (`Defs/PhiGen.lean`), as is
  `algebraMap_laurentSeries_eq_single` and `coeffMap_*` (`Defs/Laurent.lean`).
  The headline's last step (`algebraMap … + Polynomial.aeval jq P ∈ adjoin`) uses
  mathlib's `Subalgebra.add_mem` / `algebraMap_mem` /
  `Polynomial.aeval_mem_adjoin_singleton`.

## 4. Verification and the wire test

Beyond `lake build` green / 0 warnings / no `sorry`:

1. **`#print axioms`** on the public declarations: only `propext,
   Classical.choice, Quot.sound`.
2. **Statement checker.** Add the headline's wrapper and the
   `hasSum_qParam_mul*` wrappers to `SOURCES`; verified count rises
   accordingly with 0 mismatched; `PORT_FILES` gains the module.
3. **The cross-module wire test.** Apply the headline to `f = jq` with
   `F = jt`: the realization is T6's `hasSum_jq_qParam` and the invariance T6's
   `E4_cube_div_discriminant_smul`, so the headline must give
   `jq ∈ Algebra.adjoin ℚ {jq}`. It is trivial mathematically but exercises the
   whole hypothesis chain across three modules; a `example` in the module or the
   consumer, named in the report. (T5's `mem_adjoin_jq_of_poleOrderLE_zero` is
   the `n = 0` case of the same theorem; do not edit T5's module.)
4. **Nothing half-finished in the library**: experiment in the gitignored
   `Scratch.lean`.

## 5. Budget

**3 goal rounds, checkpoint at 1; expect ~1:1.** The pin is ~462 lines and §2.1
finds no replaceable leaves; T6 measured 622/589 = 1.06 for the same reason. The
port is plausibly 400–550 lines over ~15 public and ~10 private declarations, so
larger than T5 or T6. Round 1 should build the `RealL` block and
`hasSum_qParam_mul_laurent` first (they are pure glue and de-risk the rest), then
the headline.

Stop early on: `hasSum_qParam_mul_laurent`'s order split needing a `HahnSeries`
lemma that is private; the pole-killing induction not going through at the
`q^{-n}` coefficient; or `RealL`'s `mul` case forcing a restatement of the
predicate.

## 6. Definition of done

- [x] `FLTForHuman/ModularForms/Hauptmodul.lean`: the headline public, verbatim
      from its wrapper; `RealL` + closure and `hasSum_qParam_mul{,_laurent}`
      public (the T8 interface, with a header note that FLT duplicates the block);
      pole killing, `realL_aeval_jq`, the `jt`/`jqC` glue and
      `mem_adjoin_jq_of_realL_invariant` private.
- [x] `lake build` green, 0 warnings, no `sorry`.
- [x] `#print axioms` clean.
- [x] `spec/check_flt_statements.py`: the wrappers added to `SOURCES` (153 → 168),
      0 mismatched; `PORT_FILES` gains the module.
- [x] the cross-module wire test from §4 recorded, with its form named (consumer
      Zone E).
- [x] `PORTING-PhiGen.md` §5 marks T7 done (R1 complete) and names T8; the log
      gains T7's cost and the audit accounting; README module table gains the
      module.
- [x] report in the §7 shape.

## 7. Reporting back

1. **The cost, and whether "glue is 1:1" held** — rounds, declarations, lines,
   port/pin ratio; T5 was 1.79, T6 1.06. T7 was predicted to be the glue extreme.
2. **The exported API** — did T8's needs (`RealL` closure,
   `hasSum_qParam_mul_laurent`) come out as expected, or did the port need more?
   This is the interface T8 cannot change.
3. **Did any mathlib lemma blow up?** If so, name it and the restatement.

## 8. Where this sits: the sub-effort sequence (R1 = T5–T7; T8 = the cone)

For orientation only — do not start T8.

| topic | deliverable | pin material | pin lines |
|---|---|---|---|
| 5 (done) | the constancy kernel + the `n = 0` corollary | `coeff_eq_zero_of_hasSum_of_slash_invariant` | 186 |
| 6 (done) | the analytic model of `jq` | `qExpansion_*`, `hasSum_jNum_qParam`, `hasSum_jq_qParam`, `E4_cube_div_discriminant_smul` | ~589 |
| 7 (done) | the Hauptmodul form: `RealL` + closure, pole killing, `mem_adjoin_jq_of_hasSum_of_slash_invariant` | `hasSum_qParam_mul{,_laurent}`, `exists_aeval_jq_sub_holomorphicAtInfty`, `mem_adjoin_jq_of_hasSum_of_slash_invariant` | ~462 |
| 8 | the cone application: the descended coefficients lie in `ℚ[jq]` | the Hecke translates, `cosetPoly_smul`, `hasSum_cosetPoly_coeff`, `mem_adjoin_jq_of_phiGenDescends` | ~680 |

R1 is topics 5–7; **T7 completes it**. T8 is the cone's (c), and it imports this
module's `RealL` closure and `hasSum_qParam_mul_laurent` rather than duplicating
them.
