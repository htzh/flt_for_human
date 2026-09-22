# Topic 9: the integrality of the descended coefficients

**Status: done (2026-09-22), one goal round — the cone's (b) has its integrality
half.** The module is `FLTForHuman/ModularCurve/PhiGenIntegrality.lean`, green with
0 warnings and no `sorry`; **Route A shipped** (the first deliberate route
deviation of the sub-effort), decided in round 1 without needing the fallback.
The measured cost, the route decision and the dedup payoff are in
[logs/phiGen-port.md](../../logs/phiGen-port.md) §9. First cone-algebra topic
after R1; R1 (T5–T7) is complete and the cone's (c) is discharged by T8. The next
topic is T10, the pole bounds, the second half of (b). This file is kept as the
executed plan. The plan is [PORTING-PhiGen.md](../../PORTING-PhiGen.md); the
estimate and route-check are its §6 Option 2, now measured; the mathematics is
[math/010](../../../math/010-function-field-generation.md) §3 and
[base/006](../../../base/006-the-modular-equation.md) §2.

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
> **Deviation protocol — this topic deviates from FLT's tested script.** §2.1
> proposes Route A, which FLT does not use. Do it in `Scratch.lean` first, under
> `timeout 60`, and **fall back to Route B (FLT's route) if Route A has not closed
> by the round-1 checkpoint**. A deviation that is abandoned is a finding, not a
> failure — but an unbounded attempt at one is the failure mode this block exists
> to prevent. Record which route shipped.

**Audience.** A fresh session taking this topic. Read, in this order:

1. [PORTING-PhiGen.md](../../PORTING-PhiGen.md) §5 (the sequence) and §6 Option 2
   (the estimate and the route-check this work order implements);
2. [math/010](../../../math/010-function-field-generation.md) §3 — why the
   modular polynomial's coefficients are integers;
3. [TOPIC-jq-model.md](TOPIC-jq-model.md) and
   [TOPIC-hauptmodul.md](TOPIC-hauptmodul.md) — T6/T7's measured ratios and the
   "price the glue" lesson; [TOPIC-phiGen-descends.md](TOPIC-phiGen-descends.md)
   for the dedup payoff;
4. [porting-playbook.md](../../porting-playbook.md) §2 (deduplicate at the
   source), §3.9 (scratch iteration) and §3.11.

**Goal.** One new module, `FLTForHuman/ModularCurve/PhiGenIntegrality.lean` (or
`ModularForms/Integrality.lean` — the session's choice; the content is algebra on
`LaurentSeries`, not analysis, which argues for `ModularCurve/`), mathlib plus the
port's `Defs/`, green, zero warnings, zero `sorry`, with exactly two public
declarations, verbatim from their wrappers:

```lean
theorem ModularCurve.PhiGen.PhiGenDescends.intCoeffs {K : Type*} [Field K] [Algebra ℚ K]
    {ℓ : ℕ} [hℓ : Fact (Nat.Prime ℓ)] {ζ : Kˣ} {c : ℕ → LaurentSeries ℚ}
    (hc : PhiGenDescends ℓ ζ c) (hζ1 : ζ ^ ℓ = 1) (k : ℕ) : IntCoeffs (c k)

theorem ModularCurve.PhiGen.aeval_jq_intCoeffs_descent (P : Polynomial ℚ)
    (hP : IntCoeffs (Polynomial.aeval jq P)) (k : ℕ) : ∃ z : ℤ, P.coeff k = (z : ℚ)
```

The first says the descended coefficients have **integer `q`-expansion
coefficients**; the second is the triangularity descent, turning that into
"the witnessing polynomial `P ∈ ℚ[X]` is in `ℤ[X]`". Together they are exactly
what (d)'s `exists_modularPolynomialData_coeff_eq` needs to build an element of
`ℤ[X][Y]`.

**Prerequisites, checked (all present).** `IntCoeffs`, `PhiGenDescends`,
`conj`, `phiProd` (`Defs/PhiGen.lean`); `jq`, `jq_pow`, `coeff_jq_pow_self`,
`coeff_jq_pow_of_lt`, `jNum : PowerSeries ℤ` (`Defs/Jq.lean`); `coeffMap`,
`coeffEmb`, `coeffMap_coeff`, `coeffMap_qExpand` (`Defs/Laurent.lean`, the last
is the public interface lemma at indeg 194). Mathlib: `IsPrimitiveRoot.isIntegral`
(RootsOfUnity/Minpoly.lean:41), `HahnSeries.map_mul`/`map_add`/`map_one`,
`mem_integralClosure_iff`, `IsIntegrallyClosed.isIntegral_iff`. **One prerequisite
is private and must be promoted** (below).

## 1. Why this topic, and what is settled

The modular polynomial is a `Polynomial (Polynomial ℤ)`. The candidate product's
descended coefficients are rational (`c k ∈ ℚ[jq]`, T8) but the datum's type
forces them to be integral; that is what (b) supplies and no earlier topic
provides.

- **Settled: the integrality is exactly one of the six cone pieces' first half.**
  (b) is "integrality **and** pole bounds". This topic is the integrality only;
  the pole bounds (`phiProd_conj_coeff_eq_zero_of_le` / `_zero_lead`) and the
  328-block (`c_eq_zero`, `c_top`, `poleOrderLE`, `sum_mul_jqN_pow_eq_zero`,
  `evalAtJ_injective`) are subsequent topics (§8).
- **Settled: promote the shared triangularity first.** T7's `coeff_aeval_jq_neg`
  and `poleOrderLE_aeval_jq` are **private** in
  `FLTForHuman/ModularForms/Hauptmodul.lean` (lines 325, 334). Promote both to
  public lemmas in `Defs/Jq.lean` and point T7's copy at them (a two-line
  refactor). The pin duplicates `coeff_aeval_jq_neg` across **9 files** — (b),
  (d), (e), T7 and others — so this is the single highest-value dedup in the
  remaining cone.
- **Settled: Route A is a deviation, and the deviation protocol applies.** FLT's
  tested script is Route B (§2.1); Route A is the route-check recorded in
  PORTING-PhiGen §6 Option 2. Do A first in `Scratch.lean`; fall back to B at the
  round-1 checkpoint if A has not closed. Either is acceptable; the record is
  which one and why.
- **Settled: the two statements are the pin's, verbatim**, so both wrappers go in
  `SOURCES` and are verified. Per T7 log §7.3, use the **wrapper's spelling**
  (`IntCoeffs`, `PhiGenDescends`, plain names — no `𝕢`/`ℍ` here).
- **Settled: the pin's `aeval_jq_intCoeffs_descent` is 308 lines but only its
  integrality half is in scope.** Its first ~180 lines are a copy of the
  `TPoleOrderLE` closure block that belongs to the pole-bound topic; the pin's
  `intCoeffs` file does not use `TPoleOrderLE` at all (grep: 0). Do **not** port
  that block here.

## 2. The scouted inventory

Two pin files, ~347 lines, of which ~108 is this topic's second statement.

| pin file | lines | content |
|---|---|---|
| `S_ModularCurve_PhiGen_PhiGenDescends_intCoeffs.lean` | 239 | the product's integrality, via `integralClosure ℤ K` |
| `S_ModularCurve_PhiGen_aeval_jq_intCoeffs_descent.lean` | 308 | the triangularity descent (~108) + a duplicated `TPoleOrderLE` block (~180, out of scope) |

Declarations:

| declaration | pin lines | size |
|---|---|---|
| `intCoeffs_jq_pow`, `intCoeffs_jq` | intCoeffs 22–37 | 16 |
| `CoeffsIntegral`, `{zero,one,neg,mul,qExpand,qTwist}` | intCoeffs 45–85 | 41 |
| `intCast_mem_integralClosure`, `val_mem_integralClosure_of_pow_eq_one`, `zpow_val_mem_integralClosure_of_pow_eq_one` | intCoeffs 87–110 | 24 |
| `coeffsIntegral_coeff_X_sub_C`, `coeffsIntegral_coeff_mul`, `coeffsIntegral_coeff_prod` | intCoeffs 112–153 | 42 |
| `coeffsIntegral_jqK`, `coeffsIntegral_conj`, `coeffsIntegral_phiProd_coeff` | intCoeffs 161–187 | 27 |
| `exists_intCast_eq_of_mem` | intCoeffs 195–211 | 17 |
| `PhiGenDescends.intCoeffs` | intCoeffs 215–224 | 10 |
| `IntCoeffs.sub`, `intCoeffs_jq_pow`, `intCoeffs_jq`, `coeff_aeval_jq_neg` | descent 201–253 | ~53 |
| `aeval_jq_intCoeffs_descent` | descent 254–292 | ~39 |

Note the pin's closure block (41 lines) and its three `coeffsIntegral_*`
polynomial lemmas (42 lines) are 83 lines of what Route A is designed to
replace.

### 2.1 The route-check: A (deviation) vs B (FLT's script)

**Route A — `LaurentSeries 𝒪` + `HahnSeries.map` (preferred, deviation).** Let
$`\mathcal{O} = \mathrm{integralClosure}\,\mathbb{Z}\,K`$. Because the port's
`jNum : PowerSeries ℤ`, `jq` lifts to `jq_ℤ : LaurentSeries ℤ`, and

$$`\mathrm{coeffEmb}\,K\,jq = \mathrm{HahnSeries.map}\,(\mathrm{algebraMap}\,\mathcal{O}\,K)\,(\mathrm{HahnSeries.map}\,(\mathrm{algebraMap}\,\mathbb{Z}\,\mathcal{O})\,jq_\mathbb{Z})`$$

Then `HahnSeries.map` is a ring hom, so push it through `qExpand` (the port's
public `coeffMap_qExpand` is exactly this commutation) and `qTwist` (one bridging
lemma) to place every `conj i` in the image; `phiProd`'s coefficients are in the
image by ring structure, and `HahnSeries.map_coeff` reads off
$`(\mathrm{phiProd}.\mathrm{coeff}\,k).\mathrm{coeff}\,n \in \mathcal{O}`$.
`IsPrimitiveRoot.isIntegral` supplies $`\zeta`$'s integrality and the unit lift
needed by `qTwist`. Finally `hc` plus injectivity of `coeffEmb` gives
$`\mathrm{algebraMap}\,\mathbb{Q}\,K\,((c_k).\mathrm{coeff}\,m) \in \mathcal{O}`$,
and `IsIntegrallyClosed.isIntegral_iff` produces the integer.

*Cost:* ~4–6 small bridging lemmas (map composition; map vs `qExpand`/`qTwist`;
the $`\mathcal{O}`$-unit lift of $`\zeta`$). The user's read is that these mathlib
bridges are minor; the risk is in whether the `LaurentSeries 𝒪` bookkeeping
integrates cleanly, hence the spike.
*Gain:* replaces the pin's 41-line closure block and 42-line polynomial-coefficient
block with ring structure, and the two manual root-of-unity lemmas with one
mathlib call.

**Route B — FLT's script (fallback).** The pin's `CoeffsIntegral := ∀ m,
f.coeff m ∈ integralClosure ℤ K` with its six closure lemmas,
`coeffsIntegral_jqK`/`_conj`/`_phiProd_coeff` and `exists_intCast_eq_of_mem`;
swap `IsPrimitiveRoot.isIntegral` in for the pin's two manual root-of-unity
lemmas. This is the 239-line script FLT compiled, and it is known to work.

**Second statement, either route.** `aeval_jq_intCoeffs_descent` is ~20–30 lines
once `coeff_aeval_jq_neg` is public: for `k ≤ P.natDegree`, `P.coeff k` is the
`q^{-k}` coefficient of `aeval jq P` (triangularity) hence an integer by `hP`;
for `k > P.natDegree`, `P.coeff k = 0`. The pin spends ~53 lines on this plus
`IntCoeffs.sub` and `intCoeffs_jq`.

## 3. What is different about this topic

- **It is the first topic that deviates from a compiled FLT script on purpose.**
  T5–T8 each deviated only where an audit found a mathlib substitute; here the
  *route* itself is new. The deviation protocol at the top exists for this.
- **It is pure algebra.** No `ℍ`, no `HasSum`, no `ModularForm` — `LaurentSeries`,
  `Polynomial`, `integralClosure`. The friction is expected to be `HahnSeries.map`
  commuting with the port's `qExpand`/`qTwist`, not analysis.
- **It promotes a shared lemma first.** `coeff_aeval_jq_neg` is duplicated in 9
  pin files; this topic makes it public in `Defs/` and refactors T7. That refactor
  touches a completed module, so keep it minimal and re-run T7's checker entries.
- **It has no concrete instance.** `intCoeffs` takes `hc : PhiGenDescends ℓ ζ c`,
  which only the cone's (a) can produce; there is no such value yet. The wire test
  is therefore a `#check`/consumer binding plus the second statement's concrete
  instantiation — do not invent an `hc`.

## 4. Verification and the wire test

Beyond `lake build` green / 0 warnings / no `sorry`:

1. **`#print axioms`** on both public declarations: only `propext,
   Classical.choice, Quot.sound`.
2. **Statement checker.** Add both wrappers to `SOURCES`; verified count rises
   from **176**, 0 mismatched; `PORT_FILES` gains the module; the promoted
   `Defs/Jq.lean` lemmas are port statements too (they are T7's, already covered
   by `Defs/Jq.lean`'s `PORT_FILES` entry — check).
3. **The wire test.** `aeval_jq_intCoeffs_descent` has a concrete instance: take
   `P = X`, so `aeval jq X = jq`, `hP := intCoeffs_jq`, and the conclusion is
   `X.coeff 1 = 1 ∈ ℤ`; do it as an `example` and name it. `intCoeffs` itself is
   bound in the consumer (Zone G) with `#check`, and the report should state that
   its real consumer is (d)'s `exists_modularPolynomialData_coeff_eq`, not yet
   ported.
4. **T7's refactor.** After promoting the two lemmas, `lake build
   FLTForHuman.ModularForms.Hauptmodul` must stay green, and T7's checker entries
   must stay 0-mismatched.
5. **The route decision.** Record which of A/B shipped and the round it was
   decided; if A was abandoned, record the declaration at which it stalled.

## 5. Budget

**2 goal rounds, checkpoint at 1.** Pin ~347, of which the second statement is
~108 and the out-of-scope `TPoleOrderLE` block is ~180; Route A is designed to
replace ~83 pin lines of closure machinery with ring structure plus ~4–6 bridging
lemmas. The port is plausibly **250–400 lines**. T8 measured the point the user
made — line counts do not translate into effort (741 pin → 725 port, one round) —
so the budget is set by the *route risk*, not the lines: round 1 is the Route A
spike, and the fallback to B is a success path, not a stop.

Stop early on: `HahnSeries.map` not commuting with the port's `qExpand`/`qTwist`
without a restatement; the `𝒪`-unit lift of `ζ` needing a `Units` instance that
mathlib will not synthesize; or `intCoeffs_jq_pow`'s lift `jq_ℤ` not being
reachable from `Defs/Jq.lean`'s definition without unfolding `jNumQ`.

## 6. Definition of done

- [x] `coeff_aeval_jq_neg` and `poleOrderLE_aeval_jq` public in `Defs/`;
      T7's `Hauptmodul.lean` points at them (still green). **Structural
      deviation:** `poleOrderLE_aeval_jq` needs `PoleOrderLE`, defined in
      `Defs/PhiGen.lean` (which imports `Defs/Jq.lean`), so it was promoted into
      `Defs/PhiGen.lean`; `coeff_aeval_jq_neg` went to `Defs/Jq.lean` as planned.
- [x] the new module `FLTForHuman/ModularCurve/PhiGenIntegrality.lean`: both
      statements public and verbatim from their wrappers, with the route decision
      (**A**) and its reason in the header.
- [x] `lake build` green, 0 warnings, no `sorry`.
- [x] `#print axioms` clean (`propext, Classical.choice, Quot.sound`).
- [x] `spec/check_flt_statements.py`: both wrappers in `SOURCES`, 0 mismatched
      (176 → 180, with the promotion at 178); `PORT_FILES` gains the module.
- [x] the wire item from §4 recorded, with the `P = X` instantiation named
      (`aeval_jq_intCoeffs_descent_X`, private in the module because the public
      surface is held at exactly the two wrappers); consumer Zone G bound.
- [x] `PORTING-PhiGen.md` §5 adds T9 as the next cone topic and marks it done;
      §6's estimate table's (b) row is updated with the *measured* result (the
      route-check is resolved); the log gains T9's cost (§9); the README module
      table gains the module.
- [x] report in the §7 shape (below, in this file's status block and log §9).

## 7. Reporting back

1. **Route A vs B** — which shipped, in which round, and whether the ~83 lines of
   replaced closure machinery were the saving the route-check predicted. A
   fallback to B with the stall point named is the most useful answer.
2. **The cost** — rounds, declarations, lines, port/pin ratio (T5 1.79, T6 1.06,
   T7 1.05, T8 0.98).
3. **The dedup** — did promoting `coeff_aeval_jq_neg` to `Defs/` shrink T7's
   module and give later topics a clean entry point? (The pin repeats it in 9
   files; this is the number to keep.)

## 8. Where this sits: the remaining cone after T9

| topic | piece | pin | note |
|---|---|---|---|
| **9 (this)** | (b) integrality | ~347 | two statements + the shared-triangularity promotion |
| 10 | (b) pole bounds | 391 (dup ×2) | `phiProd_conj_coeff_eq_zero_of_le` + the `TPoleOrderLE` closure block |
| 11 | (b)/(d) the 328-block + assembly | 328 (dup ×5) + 502 | `c_top`/`c_eq_zero`/`poleOrderLE`, then `exists_modularPolynomialData_coeff_eq`, `eq_of_prime` |
| 12 | (e) irreducibility/symmetry | 1,281 | the 895-line block ×3 + `one_le_coeff_jq` |
| 13 | (a) descent + (f) the statement | 315 + 394 (+288 seed) | `exists_phiGenDescends`, `splits_of_prime` |

The sizes are the deduplicated pin lines from [PORTING-PhiGen.md](../../PORTING-PhiGen.md)
§6, and T8 taught that they are not effort: T8's 741 pin lines took one round and
produced a 0.98 ratio. Budget each by route risk and shape variety, not lines.
