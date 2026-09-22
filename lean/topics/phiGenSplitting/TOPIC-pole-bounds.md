# Topic 10: the pole bounds — the other half of (b)

**Status: done (2026-09-22), one goal round — the cone's (b) is complete.** The
module is `FLTForHuman/ModularCurve/PhiGenPoleBounds.lean`, green with 0 warnings
and no `sorry`, and the shared `TPoleOrderLE` prelude (23 public declarations) is
now public in `Defs/PhiGen.lean`. **No route deviation: FLT's script compiled as
transcribed.** The measured cost, the dedup count and the closed audit near-miss
are in [logs/phiGen-port.md](../../logs/phiGen-port.md) §10. This file is kept as
the executed plan. The plan is
[PORTING-PhiGen.md](../../PORTING-PhiGen.md); the mathematics is
[math/010](../../../math/010-function-field-generation.md) §3 and
[base/006](../../../base/006-the-modular-equation.md) §6 step 3; **T11 (the 328
block and the (d) assembly) is next and imports the promoted prelude.**

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
>
> **Deviation protocol.** T9's Route A worked but bought no line saving (log §9.1),
> so this topic has **no planned deviation**: port FLT's `TPoleOrderLE` script,
> which is pure coefficient algebra and known to compile. If a mathlib
> substitution looks attractive, follow the same rule T9 did — spike it in
> `Scratch.lean` under `timeout 60`, keep it only if it closes by the round-1
> checkpoint, and record the outcome either way.

**Audience.** A fresh session taking this topic. Read, in this order:

1. [PORTING-PhiGen.md](../../PORTING-PhiGen.md) §5 (the sequence) and §6 (the
   remaining-cone estimate, whose (b) row this topic closes);
2. [math/010](../../../math/010-function-field-generation.md) §3 — where the pole
   bound enters the datum assembly;
3. [TOPIC-integrality.md](TOPIC-integrality.md) and
   [logs/phiGen-port.md](../../logs/phiGen-port.md) §9 — the immediately preceding
   topic, its route experiment and its dedup;
4. [porting-playbook.md](../../porting-playbook.md) §2 (deduplicate at the
   source), §3.9 and §3.11.

**Goal.** Two things:

1. a **shared `TPoleOrderLE` block** added to `Defs/PhiGen.lean` (public), because
   the pin repeats it in the `phiProd_conj_coeff_eq_zero_of_le` file **and in all
   five copies of the 328 block** — this is T11's entry point;
2. one new module, `FLTForHuman/ModularCurve/PhiGenPoleBounds.lean`, with the two
   pin statements verbatim from their wrappers:

```lean
theorem ModularCurve.PhiGen.phiProd_conj_coeff_zero_lead {K : Type*} [Field K] [Algebra ℚ K]
    (ℓ : ℕ) [hℓ : Fact (Nat.Prime ℓ)] (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) ℓ) :
    ((phiProd ℓ (conj ℓ ζ)).coeff 0).coeff (-((ℓ * ℓ + ℓ : ℕ) : ℤ)) = 1

theorem ModularCurve.PhiGen.phiProd_conj_coeff_eq_zero_of_le {K : Type*} [Field K] [Algebra ℚ K]
    (ℓ : ℕ) [hℓ : Fact (Nat.Prime ℓ)] (ζ : Kˣ) (k : ℕ) (hk : k ≠ 0) (m : ℕ)
    (hm : ℓ * ℓ + ℓ ≤ m) : ((phiProd ℓ (conj ℓ ζ)).coeff k).coeff (-(m : ℤ)) = 0
```

The first is the **leading coefficient of the constant term**: the pole of
`phiProd`'s degree-0 coefficient is exactly `q^{-(ℓ²+ℓ)}` with residue `1`. The
second bounds every non-constant coefficient to the same order. Together with
T9's integrality they make the candidate product a degree-`(ℓ+1)` integer datum —
what (d) assembles.

## 1. Why this topic, and what is settled

- **Settled: the shared block is the point.** The `TPoleOrderLE` closure
  (`mono`, `zero`, `one`, `neg`, `add`, `mul`, `qTwist`, `qExpand`,
  `of_jSimplePole`), the conjugate bounds (`conjPoleBound`,
  `tPoleOrderLE_conj_zero/_succ/_conj`) and the coefficient bounds
  (`tPoleOrderLE_coeff_X_sub_C`, `_mul`, `_prod`, `_phiProd_coeff`) are a ~180-line
  block that the pin copies into the `phiProd_conj` file **and** each of the five
  328-block files. The port writes it once, public, in `Defs/PhiGen.lean` (beside
  the `TPoleOrderLE` definition T9's `poleOrderLE_aeval_jq` already sits next to).
  **T11 then imports it.**
- **Settled: the shared `jq`-pole facts come with it.** `jSimplePole_jqK` (or the
  pin's `jSimplePole_jqK_carrier` spelling), `tPoleOrderLE_coeffEmb_iff` and
  `tPoleOrderLE_of_qExpand` live in the 328 block and are needed by this topic's
  `tPoleOrderLE_phiProd_conj_of_ne_zero`. Port them with the block.
- **Settled: prerequisites are in place.** `Defs/PhiGen.lean` already has
  `PoleOrderLE`, `TPoleOrderLE`, `JSimplePole`, `conj`, `phiProd`, `qExpand`,
  `qTwist`, `coeffEmb`, and T9's promoted `poleOrderLE_aeval_jq`; `Defs/Jq.lean`
  has `jq`, `coeff_jq_neg_one`, `coeff_jq_of_lt`. No analysis, no Hecke, no new
  mathlib route is needed.
- **Settled: the two statements are the pin's, verbatim**, so both wrappers go in
  `SOURCES` and are verified, in the wrappers' spelling.
- **Settled: T11 is out of scope.** The 328 block's own theorems (`PhiGenDescends.c_top`,
  `c_eq_zero`, `poleOrderLE`, `sum_mul_jqN_pow_eq_zero`) and `evalAtJ_injective`
  are T11, as is the (d) assembly. This topic ported the *prelude* they need.

## 2. The scouted inventory

| pin file | lines | content |
|---|---|---|
| `S_ModularCurve_PhiGen_phiProd_conj_coeff_eq_zero_of_le.lean` | 391 | the shared `TPoleOrderLE` prelude (~145) + the pole bounds (~246) |
| `S_ModularCurve_PhiGen_phiProd_conj_coeff_zero_lead.lean` | 391 | the **same file**, exported name flipped (verified duplicate) |
| `S_ModularCurve_PhiGen_PhiGenDescends_c_eq_zero.lean` and its 4 copies | 328 ×5 | the same prelude again + the 328 block (T11) |

Shared prelude, to `Defs/PhiGen.lean`:

| declaration | pin lines | size |
|---|---|---|
| `TPoleOrderLE.mono`, `tPoleOrderLE_zero`, `_one`, `TPoleOrderLE.neg` | 36–58 | ~19 |
| `TPoleOrderLE.add`, `.mul`, `.qTwist`, `.qExpand` | 59–102 | ~44 |
| `tPoleOrderLE_of_jSimplePole`, `jSimplePole_jqK`, `tPoleOrderLE_coeffEmb_iff`, `tPoleOrderLE_of_qExpand` | 103–107, 328-file 33–56 | ~30 |
| `conjPoleBound`, `conjPoleBound_zero/_succ`, `sum_conjPoleBound` | 108–122 | ~14 |
| `tPoleOrderLE_conj_zero`, `_succ`, `_conj` | 123–149 | ~27 |
| `tPoleOrderLE_coeff_X_sub_C`, `_mul`, `_prod`, `_phiProd_coeff` | 150–166, 328-file 183–223 | ~60 |

Pole-bound module (the distinctive part):

| declaration | pin lines | size |
|---|---|---|
| `coeff_coeffEmb_jq_neg_one`, `coeff_coeffEmb_jq_of_lt` | 27–35 | 9 |
| `tPoleOrderLE_prod` | 171–180 | 10 |
| `coeff_mul_lead`, `coeff_prod_lead` | 181–215 | 35 |
| `pow_sum_range_isPrimitiveRoot`, `prod_inv_pow_isPrimitiveRoot` | 216–241 | 26 |
| `phiProd_coeff_zero_eq_prod_neg`, `conj_zero_coeff_lead`, `conj_succ_coeff_lead` | 242–263 | 22 |
| `phiProd_coeff_zero_lead` | 264–290 | 27 |
| `tPoleOrderLE_coeff_prod_X_sub_C_card` | 291–331 | 41 |
| `tPoleOrderLE_phiProd_coeff_of_ne_zero` | 332–356 | 25 |
| `jSimplePole_jqK_carrier` | 357–360 | 4 |
| `phiProd_conj_coeff_zero_lead`, `tPoleOrderLE_phiProd_conj_of_ne_zero`, `phiProd_conj_coeff_eq_zero_of_le` | 361–387 | 27 |

### 2.1 The mathlib-first audit

Audited against `v4.34.0`. **This is a glue topic, like T7**: mathlib supplies the
coefficient/order primitives, not the FLT statements.

| pin piece | mathlib `v4.34.0` | verdict |
|---|---|---|
| the `TPoleOrderLE` closure (`mono`/`zero`/`one`/`neg`/`add`/`mul`/`qTwist`/`qExpand`) | `HahnSeries.coeff_add`, `coeff_neg`, `coeff_mul`, `HahnSeries.coeff_zero`, `coeff_one`; the port's own `qExpand_coeff_*`/`qTwist_coeff` | port (coefficientwise, ~90 lines, written once) |
| `jSimplePole_jqK`, `coeff_coeffEmb_jq_neg_one/of_lt` | the port's `coeff_jq_neg_one`, `coeff_jq_of_lt`, `coeffEmb_coeff` | trivial |
| `conjPoleBound` + `tPoleOrderLE_conj_*` | none | port |
| `coeff_mul_lead`, `coeff_prod_lead` | `HahnSeries.coeff_mul` + the order API (`le_order_iff_forall`, `coeff_eq_zero_of_lt_order`) | port |
| `pow_sum_range_isPrimitiveRoot` | **no direct lemma** — the nearest are `IsPrimitiveRoot.geom_sum_eq_zero` (`∑ ζ^i = 0`) and the cyclotomic-product API; this is the *product* of powers, $`z^{\ell(\ell-1)/2} = (-1)^{\ell+1}`$ | port (~18) |
| `prod_inv_pow_isPrimitiveRoot` | `Finset.prod_inv_distrib`, `Finset.prod_pow_eq_pow_sum` | port (~8) |
| `phiProd_coeff_zero_eq_prod_neg` | `Polynomial.coeff_zero_eq_eval_zero`, `eval_prod` | port (short) |
| `tPoleOrderLE_coeff_prod_X_sub_C_card`, `tPoleOrderLE_phiProd_coeff_of_ne_zero`, `tPoleOrderLE_phiProd_conj_of_ne_zero` | none | port |
| the two exported statements | none | port |

**Headline.** No public mathlib lemma replaces any export; the audit's value is
again negative — do not hunt for analogues, and do not deviate. The one
interesting near-miss is `pow_sum_range_isPrimitiveRoot`, where mathlib has the
*sum* fact and FLT needs the *product* fact; the work order warns against
concluding, from the name, that `IsPrimitiveRoot.geom_sum_eq_zero` applies — T9's
log §9.1 records exactly that mistake with `IsPrimitiveRoot.isIntegral`.

## 3. What is different about this topic

- **It is the dedup test.** The pin's ~180-line prelude appears in **six** files.
  If this topic exports it once and T11 imports it, that is the largest
  duplication removal in the remaining cone; the report should say how many
  lines the six copies would have cost.
- **It has no route risk.** Unlike T9, the script is FLT's and it compiles. The
  budget is therefore the port itself.
- **It promotes nothing new, but it extends `Defs/PhiGen.lean`.** The `Defs/`
  files are shared with every cone topic; keep the additions in dependency order
  and re-run the affected builds.
- **Its wire test is concrete.** Unlike T9's `intCoeffs`, the exports take
  `hζ : IsPrimitiveRoot (ζ : K) ℓ` over an arbitrary field, so a small `ℓ` over a
  concrete field is instantiable (see §4).

## 4. Verification and the wire test

Beyond `lake build` green / 0 warnings / no `sorry`:

1. **`#print axioms`** on both public declarations: only `propext,
   Classical.choice, Quot.sound`.
2. **Statement checker.** Add both wrappers to `SOURCES`; verified count rises
   from **180**, 0 mismatched; `PORT_FILES` gains the module (the `Defs/PhiGen.lean`
   additions are covered by its existing `PORT_FILES` entry — check).
3. **The wire test.** `phiProd_conj_coeff_zero_lead` is instantiable: pick a small
   `ℓ` (2 or 3), a concrete field and an explicit primitive root —
   `CyclotomicField ℓ ℚ` with the port's/T8's `cycUnit`-style witness, or
   `ℂ` with `Complex.isPrimitiveRoot_exp` — and check the leading coefficient is
   `1`. If the `ℂ` instantiation needs the port's `qExpand`/`qTwist` over `ℂ`
   (they exist), prefer it; otherwise bind both statements in the consumer (Zone
   H) and say which form the wire took. The real consumers are the (d)/(e)
   `evalSymm_*`/`exists_modularPolynomialData_coeff_eq`, not yet ported.
4. **The `Defs/PhiGen.lean` additions.** Build `Defs/PhiGen`, `PhiGenIntegrality`,
   `Hauptmodul` and the new module together; the shared block must not disturb
   T9's module.

## 5. Budget

**2 goal rounds, checkpoint at 1.** Pin content ≈ 391 (the `phiProd_conj` file,
the `_zero_lead` twin is a verified duplicate) + the ~180-line prelude that both
this topic and the 328 block need; the port is plausibly **450–600 lines**, most
of it the shared block and the leading-coefficient computation. T9 measured 0.93
on comparable glue, and T8 measured that lines are not effort, so the budget is
for the leading-coefficient proof (the `pow_sum_range_isPrimitiveRoot` /
`coeff_prod_lead` chain), which is the only part with any surprise in it.

Stop early on: `coeff_prod_lead` needing an order lemma that is private;
`pow_sum_range_isPrimitiveRoot`'s case split on `ℓ = 2` vs odd not matching the
port's `IsPrimitiveRoot` API; or the shared block forcing a `Defs/PhiGen` import
it does not have.

## 6. Definition of done

- [x] the shared `TPoleOrderLE` block public in `Defs/PhiGen.lean`, in dependency
      order, with a header note that FLT repeats it in six files and T11 imports
      it. **187 lines, 23 public + 2 `private` declarations** (the 2 private are
      `coeff_coeffEmb_jq_of_lt`, kept in `Defs/`, and `phiProd_def`; the module
      re-declares the latter privately because the pin does).
- [x] `FLTForHuman/ModularCurve/PhiGenPoleBounds.lean`: both statements public and
      verbatim from their wrappers. **310 lines, 2 public + 16 `private`.**
- [x] `lake build` green, 0 warnings, no `sorry` (3840 jobs).
- [x] `#print axioms` clean (`propext, Classical.choice, Quot.sound`) on both.
- [x] `spec/check_flt_statements.py`: both wrappers in `SOURCES`, 0 mismatched;
      `PORT_FILES` gains the module. **180 → 205, 0 missing; 11 of the new
      statements verified against the pin's `private` declarations** through a new
      dotted-name fallback (`Defs/PhiGen.lean`'s existing `PORT_FILES` entry
      covers the prelude, and the fallback was needed for the pin-private ones).
- [x] the wire item from §4 recorded, with its concrete form named: **`K = ℂ`,
      `ℓ = 2`, `ζ = -1` (`IsPrimitiveRoot.neg_one`)**, named `wire_zero_lead` /
      `wire_eq_zero_of_le` inside the module (private; the public surface is the
      two wrappers). `#check`s plus both hypothesis forms are in consumer Zone H.
- [x] `PORTING-PhiGen.md` §5 marks T10 done and names T11; §6's (b) row is closed
      with the measured result (819 port lines against 1,266 deduplicated pin);
      the log gains T10's cost (§10); README module table gains the module.
- [x] report in the §7 shape (below, in this file's status block and log §10).

## 7. Reporting back

1. **The dedup** — the ~146-line common prelude appears across **six**
   developments (the `phiProd_conj` development, shipped twice, and the five
   328-block copies) but physically in **twelve** `S_` files, so it would have
   cost **≈1,752 lines** written per `S_` file (**≈876** across the six
   developments); the 328-only coefficient sub-block adds ≈405 more. The port
   writes the union once at 187, and **T11 imports it without additions**.
2. **The cost** — **1 goal round**, 25 + 2 declarations (23 public prelude, 2
   public exports, plus 18 private), **497 lines** (187 + 310), port/pin ratio
   **1.27** (T5 1.79, T6 1.06, T7 1.05, T8 0.98, T9 0.93).
3. **`pow_sum_range_isPrimitiveRoot`** — the pin's `ℓ = 2`-versus-odd case split
   was **ported whole**; mathlib supplied `Nat.Prime.eq_two_or_odd'`,
   `IsPrimitiveRoot.eq_neg_one_of_two_right`, `IsPrimitiveRoot.pow_eq_one`,
   `Finset.sum_range_id_mul_two` and `Even.neg_one_pow`, but **no lemma replaces
   the statement** — `IsPrimitiveRoot.geom_sum_eq_zero` is the sum, not the
   product.

## 8. Where this sits: the remaining cone after T10

| topic | piece | pin | note |
|---|---|---|---|
| **10 (this)** | (b) pole bounds + the shared `TPoleOrderLE` block | 391 + ~180 (dup ×6) | closes (b) with T9 |
| 11 | the 328 block + (d) assembly/uniqueness | 328 (dup ×5) + 502 | `c_top`/`c_eq_zero`/`poleOrderLE`/`sum_mul_jqN_pow_eq_zero`/`evalAtJ_injective`, then `exists_modularPolynomialData_coeff_eq`, `eq_of_prime` |
| 12 | (e) irreducibility/symmetry | 1,281 | the 895-line block ×3 + `one_le_coeff_jq` |
| 13 | (a) descent + (f) the statement | 315 + 394 (+288 seed) | `exists_phiGenDescends`, `splits_of_prime` |

Sizes are the deduplicated pin lines from [PORTING-PhiGen.md](../../PORTING-PhiGen.md)
§6; T8 and T9 both showed they are not effort.
