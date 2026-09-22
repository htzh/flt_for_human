# Blueprint: the Φₚ splitting cone — `PhiGen.splits_prime_at_slot`

**Status: analysis done; T5 (R1's constancy kernel) and T6 (the analytic model of
`jq`) landed, T7 next (2026-09-22).** This file is the math-content inventory of
the 44-node cone below
`ModularCurve.PhiGen.splits_prime_at_slot`, the measurement that the headline
line count overstates it by ~1.6×, and the plan for the next topic: isolating
the cone's one genuinely analytic input, the **level-one q-expansion principle**.
That input's mathematics is now written up in
[base/013](../base/013-riemann-existence-and-the-q-expansion-principle.md) (the
R1/R2 separation and the exact declaration chain); this file is the port-side
companion — sizes, work orders, re-route options — and §5 records T5's measured
outcome. The topic is sketched here as work orders because it is already more
than one; if it grows, it splits out into
`topics/phiGenSplitting/TOPIC-*.md` and this file keeps only the decision.

Companion records:

- [math/010](../math/010-function-field-generation.md) — the mathematics of the
  target. Its §3 is the splitting statement, §4 the descent.
- [base/013](../base/013-riemann-existence-and-the-q-expansion-principle.md) —
  the mathematics of record for the analytic input. It separates the two
  Riemann-existence facts (R1, level-one q-expansion; R2, degree and
  connectedness at level `N`), shows R2's algebraic substitute, and walks the
  exact declaration chain this note plans. §3–§4 here are the port-side summary
  of it; do not re-derive it.
- [base/006](../base/006-the-modular-equation.md) — the modular equation in
  prose: §3 the cover and the two invariances, §6 the five-step Lean route.
- [PORTING-FFG.md](PORTING-FFG.md) — the parent effort. Its §7.1 cuts this cone,
  §7.6 already deduplicates the *remainder*'s line counts, and §7.7 records that
  the cone gates all 7 remaining `Inputs` fields.
- [logs/ffg-port.md](logs/ffg-port.md) — the parent effort's record.
- [porting-playbook.md](porting-playbook.md) — the reusable method. §7.3's
  "cost tracks the route, not the subtree" is the cautionary tale this note uses.
- [../studies/flt-ffg-field-theory.md](../studies/flt-ffg-field-theory.md) — the
  segment survey.

FLT line numbers and paths are against `anthropics/fermats-last-theorem@aa2d8b3`.
mathlib is our pinned `v4.34.0`.

## 0. Scope and status

**What this note is.** A blueprint in the `PORTING-FFG.md` sense: a measurement,
a content decomposition, a decision on the next topic, and the uncertainties.
It is not a faithful-port plan. Nothing here proposes porting the cone as it
stands.

**What is settled by the analysis.**

1. `splits_prime_at_slot` is a wrapper; the cone is `PhiGen.splits_of_prime`
   together with its 43-node closure (the wrapper's only other premise is
   `coeffMap_qExpand`).
2. The cone's own files are **9,304 `S_` lines across 44 nodes**, but three
   developments are the same file shipped 3×/5×/2×; **deduplicated it is 37
   developments / 5,811 lines**, a 1.60× inflation. The "11,034 lines" of
   PORTING-FFG §7.1 is a structural file count, not content.
3. The mathematics is **not one analytic block**. It decomposes into six pieces
   (§3), of which exactly one — the level-one q-expansion principle, a 1,909-line
   bucket, about a third of the cone — uses analysis on ℍ. The irreducible
   analytic step inside that bucket is a 186-line constancy lemma resting on
   mathlib's `ModularForm.eq_const_of_weight_zero`. The other five pieces are
   Laurent-series algebra, Galois descent, integrality, and the
   minimal-polynomial bookkeeping of the modular polynomial.
4. **The next topic is (c), the level-one q-expansion principle.** It is the one
   input with no mathlib-free substitute in the cone, and isolating it as a
   standalone theorem is what lets the algebra of (a)/(b)/(d)/(e) be re-routed
   (§5, §6). [base/013](../base/013-riemann-existence-and-the-q-expansion-principle.md)
   supplies the mathematics: R1 is the analytic input, specialized to `X(1)`;
   R2 is reconstructed algebraically by (a)/(d)/(e). This note keeps the port
   side — sizes, work orders, re-route options.

**What is not settled.** Whether (c) as a standalone theorem actually shortens
the algebra. The *statement* question is settled: base/013 §6 recommends naming
R1's kernel and stating the headline on top, which is §5's c1/c2. And the
analytic cost is now known to be small: base/013 §5.4 reduces the whole bucket's
analysis to one mathlib theorem, so the open risk is plumbing, not mathematics.

## 1. The cone in one page

The dependency shape, from the doc-site graph, is:

```text
splits_prime_at_slot                     288 lines, wrapper (twist + dilation)
  ← coeffMap_qExpand                     15
  ← splits_of_prime                      353      the real content
      ← coeffMap_qExpand
      ← ModularPolynomialData.eq_of_prime           uniqueness of Φ_ℓ
      ← PhiGen.exists_phiGenDescends      315      (a) descent to ℚ((q))
      ← PhiGen.PhiGenDescends.intCoeffs   239      (b) integrality
      ← PhiGen.mem_adjoin_jq_of_phiGenDescends     (c) membership in ℚ[j]
      ← PhiGen.exists_modularPolynomialData_coeff_eq  (d) build the datum
      ← PhiGen.splits_of_coeff_evalAtJ_eq 41       (f) read off the splitting
```

`splits_prime_at_slot` itself proves nothing about the modular equation: it
introduces `TS K e u = qExpand K e (qTwist u (coeffEmb K jq))`, checks that `TS`
is injective in `(e, u)` from its `q⁻ᵉ` coefficient, and reduces the twisted,
dilated slot statement to the untwisted `splits_of_prime`
([S file, line 143](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_PhiGen_splits_prime_at_slot.lean#L143)).
So PORTING-FFG §7.7 is right that the cone is one gate, but the gate's own
content is `splits_of_prime`, and the wrapper is pure bookkeeping.

`PORTING-FFG.md` §7.7 gives the three ways forward — port the subtree, make Φₚ
an eighth `Inputs` field, or re-route a field so it never needs Φₚ. This note is
about the *third*: what of the cone has to exist before a re-route is possible,
and at what size.

## 2. What the lines actually are

The measurement, re-derived from the pinned tree (the 44-node transitive
closure under `splits_prime_at_slot`, matching `meta.below = 44`):

| quantity | value |
|---|---|
| nodes below the slot | 44 |
| `Thm_` wrappers (their own lines) | 310 |
| `S_` proof modules (their own lines) | 9,304 |
| shared definitions + `P2M/Util` + the slot's own seed | 1,216 |
| headline as PORTING-FFG states it | 94 files / 11,034 lines |

The `S_` modules are not 44 developments. The doc-site toolchain emits one `S_`
file per exported theorem, each containing the *whole* shared development with
only the `private`/public keyword flipped; a pairwise diff of the normalized
bodies (imports, namespaces, `p2m_*` lines and the `solution` tail removed)
finds exactly three duplicate groups and no others:

| block | copies | nodes | savings |
|---|---|---|---|
| 895 lines | **×3** | `evalSymm_of_splits`, `phiIrreducible_of_splits`, `transposeToAdjoin_monic_of_qExpansion` | 1,790 |
| 328 lines | **×5** | `PhiGenDescends.{c_eq_zero,c_top,poleOrderLE,sum_mul_jqN_pow_eq_zero}`, `evalAtJ_injective` | 1,312 |
| 391 lines | **×2** | `phiProd_conj_coeff_eq_zero_of_le`, `phiProd_conj_coeff_zero_lead` | 391 |

So:

- **37 distinct `S_` developments, 5,811 lines** — inflation **1.60×**;
- adding the wrappers, the seed, the definitions and `Util` gives ≈ **7.3k
  deduplicated**, against the headline 11,034. (The definitions are shared with
  the whole project, so attributing all of them is itself an overcount.)
- this is the same phenomenon PORTING-FFG §7.6 documents for the remainder
  (`minpoly_jqN_map_eq_prod_slots` ≡ `jqN_prime_not_mem_full`, etc.); it was not
  previously measured for this cone.

**Consequence for pricing.** Any estimate that starts from "11,034 lines" is
high by ~1.5×, and — more important — the three duplicated blocks are the three
*hardest-looking* single files in the cone. The 895-line block is not one
theorem's proof; it is a shared module that exports three graph nodes and hides
several more results (§3(e)).

## 3. The mathematical content, decomposed

Six separable pieces. "Bucket" is the deduplicated sum over the piece's node
files; the representative is the most characteristic declaration, and its own
file is often much smaller (the analytic bucket's headline,
`mem_adjoin_jq_of_phiGenDescends`, is 47 lines and carries 1,909 lines of
closure).

| piece | what it proves | representative | ≈ bucket | analysis on ℍ? |
|---|---|---|---|---|
| (a) | coefficients of `phiProd` descend to `ℚ((q))` | `exists_phiGenDescends` | 315 | no |
| (b) | the descended family is integral, monic, degree `ℓ+1`, pole ≤ `ℓ+1` | `intCoeffs`, `aeval_jq_intCoeffs_descent`, `phiProd_conj_coeff_*`, the 328-block | 1,270 | no |
| (c) | the descended family lies in `ℚ[j]` — **R1** | `mem_adjoin_jq_of_phiGenDescends`, then the Hecke and `HasSum` modules | 1,909 | **yes** |
| (d) | assembly + uniqueness of the level-`ℓ` modular polynomial | `exists_modularPolynomialData_coeff_eq`, `eq_of_prime`, `finrank_adjoin_jqN_eq_of_prime`, `exists_phiIrreducible_evalSymm` | 500 | no (inherits c) |
| (e) | irreducibility, symmetry, non-membership | `one_le_coeff_jq` plus the 895-line block | 1,280 | no |
| (f) | the splitting statement and its wrapper | `splits_of_prime`, `splits_of_coeff_evalAtJ_eq` | 400 | no |

In [base/013](../base/013-riemann-existence-and-the-q-expansion-principle.md)'s
notation, **(c) is R1** — the level-one q-expansion principle — and **(a), (d),
(e) are the algebraic substitute for R2**, the degree/connectedness statement
about `X₀(N) → X(1)`. The whole cone is thus "R2 by algebra, R1 by analysis",
and only the R1 bucket leaves the algebraic world.

The six buckets sum to ≈5,675; the remaining ≈136 lines are the small interface
nodes (`coeffMap_qExpand`, `coeffEmb_*`, `dedekindPsi_prime`, `aeval_jq_eq_zero`,
`transcendental_jq`, `E4_cube_div_discriminant_smul`). The slot's own 288-line
seed is outside the 44 and not counted here.

### (a) Twist and Galois descent — pure algebra

[`exists_phiGenDescends`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_PhiGen_exists_phiGenDescends.lean#L278)
shows each coefficient of `phiProd ℓ (conj ℓ ζ)` is fixed by the nome twist
$`q \mapsto \zeta_\ell q`$ (which fixes the $`q^{\ell^2}`$ slot and cycles the
$`\ell`$ finite-slope slots), hence lies in the range of `qExpand`; and is fixed
by every $`\sigma_a : \zeta_\ell \mapsto \zeta_\ell^a`$, hence is rational.
Intersecting the two ranges gives $`c_k \in \mathbb{Q}((q))`$. No analysis. This
is base/006 §6.2 verbatim.

### (b) Integrality and pole bounds — formal Laurent series

`PhiGenDescends.intCoeffs` (integral closedness of $`\mathbb{Z}`$ in the
cyclotomic field), `aeval_jq_intCoeffs_descent` (integrality descent for
polynomials in $`j`$), `phiProd_conj_coeff_*` (pole bounds for the product's
coefficients), and the 328-line block: `c_top`, `c_eq_zero`, `poleOrderLE`,
`sum_mul_jqN_pow_eq_zero` (the descended family is monic, has degree $`\ell+1`$,
pole order $`\le \ell+1`$, and annihilates $`j(q^\ell)`$), plus
`evalAtJ_injective`. Still no analysis — `intCoeffs_jq` uses the eta product, not
the upper half-plane.

### (c) The level-one q-expansion principle — the analytic input

See §4. This is the only piece that touches $`\mathbb{H}`$, and the only piece
whose removal leaves the cone provable in principle by algebra alone.

### (d) Assembly and uniqueness of the modular polynomial

[`exists_modularPolynomialData_coeff_eq`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_PhiGen_exists_modularPolynomialData_coeff_eq.lean#L130)
turns $`\{c_k\}`$ into an integer bivariate polynomial of degree $`\ell+1`$ and
checks it is a `ModularPolynomialData`;
[`eq_of_prime`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_ModularPolynomialData_eq_of_prime.lean#L53)
identifies any datum with it via
$`\mathrm{toAdjoin} = \mathrm{minpoly}_{\mathbb{Q}(j)}(j(q^\ell))`$, whose degree
$`\ell+1`$ is `finrank_adjoin_jqN_eq_of_prime`. That degree, in turn, comes from
`exists_phiIrreducible_evalSymm`, which re-runs (a)–(c) and then (e). So (d) is
algebra but it *inherits (c)*.

### (e) Irreducibility, symmetry, non-membership — the 895-line block

One shared module exports three graph nodes but contains about nine top-level
results: `evalAtJGen_injective`, `aeval_jq_ne_jqN`
([line 340](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_PhiGen_evalSymm_of_splits.lean#L340)),
`jqN_not_mem_adjoin_jq`
([line 352](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_PhiGen_evalSymm_of_splits.lean#L352)),
`phiIrreducible_of_splits`, `transposeToAdjoin_monic_of_qExpansion`,
`evalSymm_of_splits`, and the Vieta/refutation lemmas behind them. The
non-membership results belong to math/010 §5–§6's subject matter but are not
exposed as graph nodes, so the cone silently contains more mathematics than its
node list shows.

### (f) The statement and its wrapper

`splits_of_prime` assembles (a)–(e) into
$`\Phi_\ell(j(q^\ell), Y) = (Y - j(q^{\ell^2}))\prod_b (Y - j(\zeta_\ell^b q))`$;
`splits_of_coeff_evalAtJ_eq` is the 41-line coefficient comparison that turns the
descended family into the factorisation; `splits_prime_at_slot` is the
$`TS`$-bookkeeping wrapper.

## 4. The analytic kernel (c), precisely

The chain, bottom-up:

1. **`hasSum_jq_qParam`, `hasSum_jNum_qParam`, `qExpansion_*`** — the formal
   $`q`$-series of $`j`$, $`E_4`$, $`\Delta`$ are the `HasSum` of their
   $`q`$-expansions on $`\mathbb{H}`$, with $`j = E_4^3/\Delta`$.
2. **`RealL` and its closure** — a hand-rolled predicate saying a Laurent series
   is realized by a function on $`\mathbb{H}`$; closed under
   `+ - *` and finite products (`hasSum_qParam_mul{,_laurent}`). The predicate
   carries a general period $`h`$ because the Hecke translates change it;
   $`h = 1`$ is used only at the final constancy step (base/013 §5.1).
3. **Hecke translates** — `hasSum_qParam_heckeMatrix_smul` and
   `hasSum_qParam_heckeDiagMatrix_smul`: the substitutions
   $`\tau \mapsto (\tau+b)/\ell`$ and $`\tau \mapsto \ell\tau`$ act on the
   $`q`$-expansion by the corresponding coefficient twist, and `cosetPoly_smul`
   plus `PhiGenDescends.hasSum_cosetPoly_coeff` show the product's coefficients
   are $`\mathrm{SL}_2(\mathbb{Z})`$-invariant. This is *why level one suffices*:
   the Hecke-coset construction makes the descended coefficients level-one
   invariant, so the level-$`N`$ q-expansion principle — which would need the
   compactness and connectedness of $`X_0(N)`$ — is never invoked
   (base/013 §4.3, §6).
4. **`exists_aeval_jq_sub_holomorphicAtInfty`** — pure Laurent algebra: $`j`$
   has a simple pole, so a series with pole order $`\le n`$ differs from a
   polynomial in $`j`$ of degree $`\le n`$ by something holomorphic at $`\infty`$.
5. **[`coeff_eq_zero_of_hasSum_of_slash_invariant`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_coeff_eq_zero_of_hasSum_of_slash_invariant.lean)**
   — the analytic step: a holomorphic, $`\mathrm{SL}_2(\mathbb{Z})`$-invariant
   $`q`$-series is constant. The Lean packages $`F`$ as a
   `ModularForm 𝒮ℒ 0` and appeals to mathlib's
   `ModularForm.eq_const_of_weight_zero`.
6. **[`mem_adjoin_jq_of_hasSum_of_slash_invariant`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_mem_adjoin_jq_of_hasSum_of_slash_invariant.lean#L155)**
   — combine 4 and 5: $`f \in \mathbb{Q}((q))`$ with an invariant realization
   implies $`f \in \mathbb{Q}[j]`$. `mem_adjoin_jq_of_phiGenDescends` applies it
   to each $`c_k`$.

**What this is classically.** Step 5 is R1 of
[base/013](../base/013-riemann-existence-and-the-q-expansion-principle.md), the
level-one *q-expansion principle*: a holomorphic, bounded,
$`\mathrm{SL}_2(\mathbb{Z})`$-invariant function on $`\mathbb{H}`$ is constant,
equivalently the only holomorphic weight-zero level-one modular form is
constant. Classically it is Liouville on the compact curve $`X(1)`$ — the
Hauptmodul property of $`j`$ — and it is what proves a coefficient that is *a
priori* a rational function of $`j`$ is actually a *polynomial*, the property the
datum assembly in (d) needs.

**The framing question is settled by base/013.** math/010 §4's "circuitous
without Riemann existence" refers to **R2** — the degree-$`\psi(M)`$ statement
about $`X_0(M) \to X(1)`$ — which the cone replaces by the root list and the
unique-common-root principle, i.e. by (a), (d) and (e). **(c) is the different,
level-one statement R1**, and base/013 §6 establishes that the two have different
status: R2 is not an analytic input of the formal proof, while R1 has no known
algebraic substitute. So (c) is the right next topic, and the earlier caution
("pin which statement is meant before starting") is discharged. base/013 §5.4
also localizes the analysis inside the 1,909-line bucket: the analytic content is
the single mathlib theorem `ModularForm.eq_const_of_weight_zero`; the rest is
bookkeeping turning `HasSum` on $`\mathbb{H}`$ into a power series on the disc
and back.

## 5. The topic sequence: R1 in four work orders

**Decided (2026-09-21).** R1 is not one work order. Sized from the pin's own file
lengths and the parent effort's calibration (its topics came in at 207–494 port
lines, one goal round each), it is **three topics**, with the cone application a
fourth:

| topic | deliverable | pin material | pin lines | work order |
|---|---|---|---|---|
| **T5 (done)** | the constancy kernel, plus the `n = 0` corollary | `coeff_eq_zero_of_hasSum_of_slash_invariant` | 186 | [TOPIC-r1-kernel.md](topics/phiGenSplitting/TOPIC-r1-kernel.md) |
| **T6 (done)** | the analytic model of `jq` | `qExpansion_*`, `hasSum_jNum_qParam`, `hasSum_jq_qParam`, `E4_cube_div_discriminant_smul` | ~589 | [TOPIC-jq-model.md](topics/phiGenSplitting/TOPIC-jq-model.md) |
| **T7 (next)** | the Hauptmodul form | `hasSum_qParam_mul{,_laurent}`, `exists_aeval_jq_sub_holomorphicAtInfty`, `mem_adjoin_jq_of_hasSum_of_slash_invariant` | ~462 | [TOPIC-hauptmodul.md](topics/phiGenSplitting/TOPIC-hauptmodul.md) |
| T8 | the cone application: the descended coefficients lie in `ℚ[jq]` | the Hecke translates, `cosetPoly_smul`, `hasSum_cosetPoly_coeff`, `mem_adjoin_jq_of_phiGenDescends` | ~680 | — |

R1 = T5–T7; T8 is the cone's (c) and needs all three. The split is by
mathematical object, not by file: T5 is generic modular-form analysis with no
`jq` in it; T6 is the formal↔analytic bridge for `jq`; T7 is the pole-bounded
membership statement that completes R1; T8 is the Hecke-coset consumer.

**T5 is done** (2026-09-21, one goal round). Its work order was
[topics/phiGenSplitting/TOPIC-r1-kernel.md](topics/phiGenSplitting/TOPIC-r1-kernel.md),
now the executed plan. It delivered `coeff_eq_zero_of_hasSum_of_slash_invariant` —
R1's minimal named form, per base/013 §6 — in the new
`FLTForHuman/ModularForms/` area, plus the own-proof corollary
`mem_adjoin_jq_of_poleOrderLE_zero` (the `n = 0` end of T7's headline and the wire
test). The analytic risk was as low as base/013 §5.4 said: the content is
mathlib's `ModularForm.eq_const_of_weight_zero`, and the §2.1 audit held — of the
pin's 14 helpers, `tendsto_atImInfty`, `isBoundedAtImInfty` and
`norm_qParam_lt_one_of_pos` became public mathlib calls, `discFun` and its four
lemmas and `periodic` were dropped, and only `mdifferentiable` needed a proof
(plus its two mathlib-private disc-route dependencies, re-derived). One audited
substitution did **not** go through: `UpperHalfPlane.qExpansion_coeff_unique`
states the pin's `coeff_unique` but its `{F : Type*} [FunLike F ℍ ℂ]` signature
instantiates at the bare function type `ℍ → ℂ` and unfolds `DFunLike.coe`
~5.1M times (a deterministic `whnf` timeout at both the default 200 000 and the
package's 4 000 000 heartbeat caps), so the pin's 26-line argument was ported
instead. The port is 332 lines over two public declarations and six private
helpers; `#print axioms` on both public declarations is clean, the statement
checker is at 151 (up 1, 0 mismatched), and the measured cost is in
[logs/phiGen-port.md](logs/phiGen-port.md).

**T6 is done** (2026-09-22, one goal round). Its work order was
[topics/phiGenSplitting/TOPIC-jq-model.md](topics/phiGenSplitting/TOPIC-jq-model.md),
now the executed plan. It delivered `hasSum_jq_qParam` (the realization T7
consumes) and `E4_cube_div_discriminant_smul` in
`FLTForHuman/ModularForms/JqAnalyticModel.lean`, with the intermediate
`hasSum_jNum_qParam` private. The audit came out the opposite way from T5's in
one respect and the same way in another: `EisensteinSeries.E_qExpansion_coeff`,
`ModularForm.discriminant_eq_q_prod`, `differentiableOn_tprod_one_sub_pow_pow`
and `hasSum_qExpansion` all delivered, but **`discriminant_cuspFunction_eqOn` did
not replace the pin's 199-line eta-product file** — it gives the value of
`cuspFunction 1 Δ`, not the Taylor coefficients of `∏' (1-qⁿ)²⁴`, and mathlib has
no lemma for the latter, so the pin's truncated-polynomial/locally-uniform
argument was ported. The `FunLike` trap did not appear, because the pin's
`qExpansion_coeff_unique` call is already on the bundled `CuspForm.discriminant`.
The port is 622 lines over, again, two public declarations; `#print axioms` on
both is clean, the checker moved 151 → 153, and the consumer gained Zone D (the
`jq` model composed with the `jq`-coefficient module). T5's philosophy held: a
622-line port against a ~589-line pin, so the audit's *rightness* and its
*savings* again diverged. Measured cost and the audit table are in
[logs/phiGen-port.md](logs/phiGen-port.md) §3.

**T7 is next: the Hauptmodul form.** Its work order is written and audited:
[topics/phiGenSplitting/TOPIC-hauptmodul.md](topics/phiGenSplitting/TOPIC-hauptmodul.md).
It consumes T6's `hasSum_jq_qParam` and `E4_cube_div_discriminant_smul`, and T5's
kernel `coeff_eq_zero_of_hasSum_of_slash_invariant` on the remainder, so all of
its analytic inputs already exist. Its audit came out as the T6 log predicted —
**this is the glue topic**: no public mathlib lemma replaces `RealL`, its
closure, the pole-killing `exists_aeval_jq_sub_holomorphicAtInfty`, or the
headline; mathlib supplies only the Cauchy-product core inside
`hasSum_qParam_mul{,_laurent}` and the `HahnSeries`/`qParam` API around it. The
pin is ~462 lines, and the port is expected at roughly 1:1 (T5 was 1.79, T6
1.06). One deliberate divergence: T7 **exports** `RealL` + closure and
`hasSum_qParam_mul{,_laurent}` public, because FLT duplicates the `RealL` block
in T8's pin file and T8 should import T7's instead of re-deriving it. T7
completes R1.

**Cost honesty.** The cone's own `jq`-coefficients precedent is the warning:
math/010 priced the `744`/`196884` coefficients against the same 11,034-line
cluster and they turned out to be a 237-line standalone file. (c)'s 1,909 lines
are a *route* count, not a proof budget, and base/013 lowers the analytic risk to
near zero — the analysis is one mathlib theorem. The budget is the bookkeeping
(T5, T7) and the realization (T6); T8 is the largest and the one to measure
first.

**Success test.** `#print axioms` clean; the kernel is a single named declaration
whose statement a reader can compare with the classical q-expansion principle;
the `n = 0` corollary is a genuine cross-module composition over the port's
`jq`/`PoleOrderLE`.

## 6. If (c) lands: the algebra re-route options

All speculative; none is a plan. They are the reason (c) is the interesting
topic rather than a faithful port of the cone.

- **Option 0 — unchanged.** (a),(b),(d),(e) are ported as FLT has them and (c)
  drops in. *Cost:* the rest of the cone. *Gain:* none beyond the analytic
  sorry's removal. Not recommended.
- **Option 1 — weaken (d).** With (c) available, prove the candidate product is
  itself a `ModularPolynomialData` and use the degree $`\ell+1`$; but that degree
  currently comes from `exists_phiIrreducible_evalSymm`, which already uses (c)
  and (e). *Risk:* circularity; must be checked against a direct degree source.
  *Potential:* if `finrank_adjoin_jqN_eq_of_prime` can be obtained from the
  candidate instead of from an independently constructed irreducible datum, (d)
  and part of (e) collapse.
- **Option 2 — replace (b)'s integrality route.** `PhiGenDescends.intCoeffs`
  goes through `integralClosure ℤ K` and its own eta-product integrality. A
  general "q-expansion integrality" lemma over the port's `Defs/Jq.lean`
  vocabulary might discharge it more directly. *Tradeoff:* touches the 239-line
  integrality file and the 308-line descent file; unknown whether it is shorter.
- **Option 3 — strengthen (c) and skip the descended family.** *Constrained by
  base/013 §6:* any restatement that drops the realization on $`\mathbb{H}`$ is
  false. `f = 1 + q` is a nonconstant power series in $`\mathbb{Q}((q))`$, hence
  not a polynomial in `jq`, and it is the `HasSum` hypothesis that rules it out.
  Adding twist- and Galois-invariance does not repair it either: `q^ℓ` is
  twist-fixed, rational and holomorphic at $`\infty`$, yet not in
  $`\mathbb{Z}[j]`$. So a strengthened (c) must keep the realization, at which
  point it is close to the existing headline and there is little to gain.
  *Recommend against.*
- **Option 4 — re-route the *caller*.** PORTING-FFG §7.7's third way: make Φₚ an
  eighth `Inputs` field and prove the seven fields from it. This note does not
  change that arithmetic; it only says the field's *content* is (f) and that (c)
  is what a later re-route would need.
- **Ruled out: FLT's algebraic Riemann–Roch.** The `AlgebraicCurve` layer proves
  a Riemann–Roch for function fields with *no analysis at all* — via adic
  completions and Tate residues, or via Stichtenoth's repartition route
  ([studies/flt-function-field-theory-and-mathlib.md §13](../studies/flt-function-field-theory-and-mathlib.md)).
  It is still not a substitute for (c), for three measured reasons: it is absent
  from this cone (0 `AlgebraicCurve` nodes); using it would be circular, because
  FLT's modular `CurveModel`s are built and proved *downstream* of
  `functionFieldGeneration` and cite `splits_prime_at_slot`
  ([studies/flt-ffg-field-theory.md §7](../studies/flt-ffg-field-theory.md));
  and it is orthogonal in kind — RR is a dimension count on an *algebraic* curve,
  while R1 is the *analytic* constancy-and-realization statement on `X(1)`. To
  apply RR one must already have the algebraic model of `X(1)` and know that the
  q-series is a function on it, which is the analytic comparison R1 supplies; the
  one independent curve model, the automorphic field over `ℂ`, is unbridged to
  the q-expansion side. The studies locate the missing analysis exactly where
  base/013 does: Riemann existence and a complex model of `X₀(N)` compared with
  the q-expansion field — not the algebraic theory of curves.

**Shared tradeoff.** The parent effort's measured lesson is that cost tracks the
route, not the subtree. None of Options 1–3 should be started before the
corresponding node's own proof lines and helpers are counted (PORTING-FFG §2's
standing rule).

## 7. Correspondence with the notes

- **math/010 §3** states the splitting and gives the classical root description
  ($`p+1`$ cyclic isogenies). It is accurate and is the statement of record.
- **base/013** is the mathematics of record for (c): §3 names R1 and R2, §4
  shows R2's algebraic substitute, §5 walks the exact declaration chain, and §6
  answers the specialization question. §3–§4 here are the port-side summary and
  should not be read in place of it.
- **base/006 §3** gives the cover, the monodromy and the two invariances —
  exactly (a) — and explicitly says the proofs "expand in the nome, they never
  use loops".
- **base/006 §6** gives the five-step Lean route. Step 1 builds the conjugate
  product (the `phiProd`/`conj` vocabulary of (f)); step 2 is the descent (a);
  step 3 spans (b), (c) and the assembly half of (d); step 4 is `eq_of_prime`;
  step 5 is the general-`N` induction, which is on the FFG side, not this cone.
- **Compression to flag.** base/006 §6.3 says the pole bound "together with
  holomorphy makes each coefficient a polynomial in $`j(q)`$ rather than a
  rational function". In the Lean these are two independent facts:
  `exists_modularPolynomialData_coeff_eq` *takes*
  $`c_k \in \mathbb{Q}[j]`$ as a hypothesis, and the pole bound only bounds the
  degree of the witnessing polynomial. The membership is (c): its *analysis* is
  one mathlib theorem, but the bucket it sits in is 1,909 lines, a third of the
  cone, because of the realization and Hecke-coset bookkeeping around it. A
  reader following base/006 §6.3 literally would walk past that third.
- **Hidden results.** The 895-line block contains `aeval_jq_ne_jqN` and
  `jqN_not_mem_adjoin_jq`, which are §5–§6 subject matter but are not graph
  nodes. A re-route should decide deliberately whether to expose them.

## 8. Open questions and uncertainties

- **Is (c) the right "Riemann existence" statement? — answered by base/013 §6:
  yes, R1 specialized to `X(1)`.** R2 (degree `ψ(N)`, connectedness) has an
  algebraic substitute in the cone and is not an analytic input of the formal
  proof. What remains is only to pick R1's minimal form (c1).
- **Does (c) actually unblock a shorter algebra?** Untested, but base/013 lowers
  the stakes: the analysis is one mathlib theorem, so the re-route options of §6
  are about saving algebra, not about analytic cost. §6 lists four; the first act
  after c2–c4 is to count the affected nodes' proof lines before committing.
- **Should `PORTING-FFG.md` §7.1's 11,034 be corrected?** Recommend a one-line
  pointer to §2 of this note rather than editing the parent's number, which is
  correct as a structural file count.
- **Where does (c) live?** `FLTForHuman/ModularCurve/` (as a cone-specific
  result) or `FLTForHuman/FieldTheory/` (if stated generically)? Recommendation:
  `ModularCurve/`, since the statement mentions `jq`.
- **Is `RealL` worth porting?** c1's open choice. The closure lemmas are ~200
  lines of plumbing; `HasSum` directly may remove the need.
- **The interface tier.** PORTING-FFG §2.1 records `hasSum_qParam_mul_laurent`
  (indeg 24) as an unexposed ≥5-indegree declaration. If (c) is ported, it may
  also discharge that interface item; check before building it separately.
- **mathlib version drift.** base/013 cites mathlib `v4.33.0` (FLT's pin); the
  port is on `v4.34.0`. The declarations it names all exist in v4.34.0 — only the
  private `levelOne_nonpos_wt_const` moved (line 89 → 91). Re-pin any citation to
  `v4.34.0` when the topic starts.

## 9. Links

FLT sources at the pinned sha `aa2d8b3`:

- [Theorems/Thm_ModularCurve_PhiGen_splits_prime_at_slot.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularCurve_PhiGen_splits_prime_at_slot.lean) — the exported statement
- [P2M/Sol/S_ModularCurve_PhiGen_splits_prime_at_slot.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_PhiGen_splits_prime_at_slot.lean) — the wrapper
- [P2M/Sol/S_ModularCurve_PhiGen_splits_of_prime.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_PhiGen_splits_of_prime.lean) — the assembly
- [Definitions/Def_ModularCurve_PhiGen.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularCurve_PhiGen.lean) — `qTwist`, `cosetSubst`, `conj`, `phiProd`, `PhiGenDescends`
- [P2M/Sol/S_ModularCurve_PhiGen_exists_phiGenDescends.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_PhiGen_exists_phiGenDescends.lean) — (a)
- [P2M/Sol/S_ModularCurve_mem_adjoin_jq_of_hasSum_of_slash_invariant.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_mem_adjoin_jq_of_hasSum_of_slash_invariant.lean) — (c)
- [P2M/Sol/S_ModularCurve_coeff_eq_zero_of_hasSum_of_slash_invariant.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_coeff_eq_zero_of_hasSum_of_slash_invariant.lean) — the analytic step
- [P2M/Sol/S_ModularCurve_PhiGen_evalSymm_of_splits.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_PhiGen_evalSymm_of_splits.lean) — the 895-line shared block

Companion notes: [math/010](../math/010-function-field-generation.md),
[base/013](../base/013-riemann-existence-and-the-q-expansion-principle.md) (the
mathematics of the analytic input),
[base/006](../base/006-the-modular-equation.md),
[base/005](../base/005-cyclic-isogenies-and-level.md),
[base/004](../base/004-the-j-invariant.md),
[base/003](../base/003-no-level-2-weight-2-cusp-forms.md).

Background: F. Diamond and J. Shurman, *A First Course in Modular Forms*,
GTM 228, §5.2; S. Lang, *Elliptic Functions*, GTM 112, Ch. 5; G. Shimura,
*Introduction to the Arithmetic Theory of Automorphic Functions*, Ch. 6.

## Appendix A. The 44-node closure

Nodes with a `dup` marker are byte-equivalent bodies to the representative
(pairwise diff 0 after removing imports, namespaces and the `solution` tail);
their lines are counted once in §2.

| node | what it proves | `S_` lines | note |
|---|---|---|---|
| `ModularCurve.E4_cube_div_discriminant_smul` | SL₂(ℤ)-invariance of E₄³/Δ | 38 | |
| `ModularCurve.ModularPolynomialData.eq_of_prime` | Uniqueness of prime-level modular polynomial data | 73 | |
| `ModularCurve.ModularPolynomialData.transposeToAdjoin_monic_of_qExpansion` | Transpose of Φ monic of degree ψ(N) over ℚ(j) | 894 | (dup ×3) |
| `ModularCurve.PhiGen.PhiGenDescends.c_eq_zero` | Vanishing of descended coefficients above degree ℓ+1 | 328 | (rep ×5) |
| `ModularCurve.PhiGen.PhiGenDescends.c_top` | Descended coefficient family has top coefficient 1 | 328 | (dup ×5) |
| `ModularCurve.PhiGen.PhiGenDescends.hasSum_cosetPoly_coeff` | Formal descent data give q-expansions of the Hecke coset polynomial | 281 | |
| `ModularCurve.PhiGen.PhiGenDescends.intCoeffs` | Integrality of the descended coefficients of Φ_ℓ | 239 | |
| `ModularCurve.PhiGen.PhiGenDescends.poleOrderLE` | Pole order at most ℓ+1 for descended coefficients | 328 | (dup ×5) |
| `ModularCurve.PhiGen.PhiGenDescends.sum_mul_jqN_pow_eq_zero` | Descended coefficients annihilate j(q^ℓ) | 328 | (dup ×5) |
| `ModularCurve.PhiGen.aeval_jq_intCoeffs_descent` | Integrality descent for polynomials in j | 308 | |
| `ModularCurve.PhiGen.evalAtJ_injective` | Injectivity of evaluation at j(q) | 328 | (dup ×5) |
| `ModularCurve.PhiGen.evalSymm_of_coeff_evalAtJ_eq` | Evaluation symmetry of a modular polynomial packet with descended coefficients | 124 | |
| `ModularCurve.PhiGen.evalSymm_of_splits` | Symmetry of Φ_ℓ from its splitting into conjugates | 895 | (rep ×3) |
| `ModularCurve.PhiGen.exists_modularPolynomialData_coeff_eq` | Assembling Φ_ℓ from a descended integral coefficient family | 191 | |
| `ModularCurve.PhiGen.exists_phiGenDescends` | Descent of the coefficients of Φ_ℓ to ℚ((q)) | 315 | |
| `ModularCurve.PhiGen.mem_adjoin_jq_of_phiGenDescends` | Coefficients of the generic level-ℓ modular polynomial lie in ℚ[j] | 47 | |
| `ModularCurve.PhiGen.phiIrreducible_of_splits` | Irreducibility of Φ_ℓ(j,Y) over ℚ(j) from its conjugate factorisation | 895 | (dup ×3) |
| `ModularCurve.PhiGen.phiProd_conj_coeff_eq_zero_of_le` | Pole bound for the non-constant coefficients of phiProd | 391 | (rep ×2) |
| `ModularCurve.PhiGen.phiProd_conj_coeff_zero_lead` | Leading t-coefficient of the constant term of Φ_ℓ | 391 | (dup ×2) |
| `ModularCurve.PhiGen.splits_of_coeff_evalAtJ_eq` | Descended coefficients force Φ to split into conjugates | 41 | |
| `ModularCurve.PhiGen.splits_of_prime` | Prime-level modular polynomial splits over any field with ζₚ | 353 | |
| `ModularCurve.aeval_jq_eq_zero` | A rational polynomial vanishing at j(q) is zero | 28 | |
| `ModularCurve.coeffEmb_injective` | Injectivity of the coefficient embedding ℚ((q)) → L((q)) | 9 | |
| `ModularCurve.coeffEmb_qExpand` | Coefficient extension commutes with q↦ qⁿ | 10 | |
| `ModularCurve.coeffMap_injective` | Coefficientwise map on Laurent series preserves injectivity | 10 | |
| `ModularCurve.coeffMap_qExpand` | Coefficientwise maps commute with q↦ qⁿ | 15 | |
| `ModularCurve.coeff_eq_zero_of_hasSum_of_slash_invariant` | SL₂(ℤ)-invariance plus holomorphic q-expansion forces constancy | 186 | |
| `ModularCurve.cosetPoly_smul` | SL₂(ℤ)-invariance of the Hecke coset polynomial at ℓ | 244 | |
| `ModularCurve.dedekindPsi_prime` | Value of `dedekindPsi` at a prime: ψ(p)=p+1 | 13 | |
| `ModularCurve.exists_aeval_jq_sub_holomorphicAtInfty` | Killing the pole at q=0 by a polynomial in j(q) | 84 | |
| `ModularCurve.exists_phiIrreducible_evalSymm` | Existence of an irreducible symmetric modular polynomial Φ_ℓ | 62 | |
| `ModularCurve.finrank_adjoin_jqN_eq_of_prime` | Degree ℓ+1 of ℚ(j)(j(q^ℓ)) over ℚ(j) | 52 | |
| `ModularCurve.hasSum_jNum_qParam` | qE₄³/Δ is the sum of its q-series | 235 | |
| `ModularCurve.hasSum_jq_qParam` | Formal q-series j(q) sums to E₄³/Δ | 45 | |
| `ModularCurve.hasSum_qParam_heckeDiagMatrix_smul` | q_ℓ-expansion of F(ℓτ) is A(q^{ℓ^2}) | 55 | |
| `ModularCurve.hasSum_qParam_heckeMatrix_smul` | Twisted q-expansion at period ℓ under τ↦(τ+b)/ℓ | 54 | |
| `ModularCurve.hasSum_qParam_mul` | Products of convergent q-expansions on H | 80 | |
| `ModularCurve.hasSum_qParam_mul_laurent` | Cauchy product of Laurent q-expansions on H | 84 | |
| `ModularCurve.mem_adjoin_jq_of_hasSum_of_slash_invariant` | q-expansion principle at level one: invariance implies f∈ℚ[j] | 214 | |
| `ModularCurve.one_le_coeff_jq` | Every nonnegative q-coefficient of j is at least 1 | 386 | |
| `ModularCurve.qExpansion_E4_eq_map_eisenstein4` | q-expansion of E₄ equals 1+240sumσ₃(n)qⁿ | 34 | |
| `ModularCurve.qExpansion_discriminant_eq_X_mul_tprod` | q-expansion of Δ as a formal product | 199 | |
| `ModularCurve.qExpansion_discriminant_eq_map_X_mul_dedekindEtaUnit` | q-expansion of Δ as integral series qprod(1-qⁿ)²⁴ | 76 | |
| `ModularCurve.transcendental_jq` | Transcendence of the q-expansion j(q) over ℚ | 13 | |
| **total (44 nodes)** | | **9304** | 5,811 deduplicated |
