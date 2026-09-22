# Blueprint: the Φₚ splitting cone — `PhiGen.splits_prime_at_slot`

> **Retired (2026-09-22).** This plan was written and executed top-level; with the
> cone closed it lives here in `topics/` as the record of the decision and its
> measured cost, per `README.md`'s "Where things live". The topic work orders and
> the sub-effort's log ([../logs/phiGen-port.md](../logs/phiGen-port.md), §14 for
> the closing review) are its companions.

**Status: T5–T13 landed — the Φₚ splitting cone is closed (2026-09-22).** R1 is
complete, the cone's (c) is discharged, the construction (a) + the 328 block + (d)
is built, the datum's properties (positivity, irreducibility, symmetry, existence)
are proved, and the headline `PhiGen.splits_prime_at_slot` is a ported theorem: all
44 nodes below it are public. This file is the math-content inventory
of the 44-node cone below `ModularCurve.PhiGen.splits_prime_at_slot`, the
measurement that the headline line count overstates it by ~1.6×, and the plan for
the remaining cone algebra. The analytic input's mathematics is written up in
[base/013](../../base/013-riemann-existence-and-the-q-expansion-principle.md) (the
R1/R2 separation and the exact declaration chain); this file is the port-side
companion — sizes, work orders, re-route options — and §5 records the sequence
with each topic's measured outcome. **T13, the consequence (uniqueness and the
splitting), was the last topic and it is done.** What began
as a plan for one analytic input is now a nine-topic executed chain plus the
final consequence topic; each step that grew split out into
`topics/phiGenSplitting/TOPIC-*.md`, and this file keeps the decisions.

Companion records:

- [math/010](../../math/010-function-field-generation.md) — the mathematics of the
  target. Its §3 is the splitting statement, §4 the descent.
- [base/013](../../base/013-riemann-existence-and-the-q-expansion-principle.md) —
  the mathematics of record for the analytic input. It separates the two
  Riemann-existence facts (R1, level-one q-expansion; R2, degree and
  connectedness at level `N`), shows R2's algebraic substitute, and walks the
  exact declaration chain this note plans. §3–§4 here are the port-side summary
  of it; do not re-derive it.
- [base/006](../../base/006-the-modular-equation.md) — the modular equation in
  prose: §3 the cover and the two invariances, §6 the five-step Lean route.
- [PORTING-FFG.md](PORTING-FFG.md) — the parent effort. Its §7.1 cuts this cone,
  §7.6 already deduplicates the *remainder*'s line counts, and §7.7 records that
  the cone gates all 7 remaining `Inputs` fields.
- [logs/ffg-port.md](../logs/ffg-port.md) — the parent effort's record.
- [porting-playbook.md](../porting-playbook.md) — the reusable method. §7.3's
  "cost tracks the route, not the subtree" is the cautionary tale this note uses.
- [../studies/flt-ffg-field-theory.md](../../studies/flt-ffg-field-theory.md) — the
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
   (§5, §6). [base/013](../../base/013-riemann-existence-and-the-q-expansion-principle.md)
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
| 895 lines | **×5** | `evalSymm_of_splits`, `phiIrreducible_of_splits`, `transposeToAdjoin_monic_of_qExpansion` (the three graph nodes) plus the hidden exports `swapBivar_monic_of_coeff_bounds` and `ModularPolynomialData.evalSymm_of_irreducible` | 3,580 |
| 328 lines | **×7** | `PhiGenDescends.{c_eq_zero,c_top,poleOrderLE,sum_mul_jqN_pow_eq_zero}`, `evalAtJ_injective` (the five graph nodes) plus `tPoleOrderLE_coeffEmb_iff` and `tPoleOrderLE_of_qExpand` | 1,968 |
| 391 lines | **×2** | `phiProd_conj_coeff_eq_zero_of_le`, `phiProd_conj_coeff_zero_lead` | 391 |

(The `×3`/`×5` in this table count the **graph nodes**; T10 measured the 328 body in
seven `S_` files and the `TPoleOrderLE` prelude in twelve, and T12 measured the 895
block in five. The corrections are in logs §10 and §12.)

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

In [base/013](../../base/013-riemann-existence-and-the-q-expansion-principle.md)'s
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
[base/013](../../base/013-riemann-existence-and-the-q-expansion-principle.md), the
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

## 5. The topic sequence: R1, then the cone

**Decided (2026-09-21).** R1 is not one work order. Sized from the pin's own file
lengths and the parent effort's calibration (its topics came in at 207–494 port
lines, one goal round each), it is **three topics**, with the cone application a
fourth:

| topic | deliverable | pin material | pin lines | work order |
|---|---|---|---|---|
| **T5 (done)** | the constancy kernel, plus the `n = 0` corollary | `coeff_eq_zero_of_hasSum_of_slash_invariant` | 186 | [TOPIC-r1-kernel.md](phiGenSplitting/TOPIC-r1-kernel.md) |
| **T6 (done)** | the analytic model of `jq` | `qExpansion_*`, `hasSum_jNum_qParam`, `hasSum_jq_qParam`, `E4_cube_div_discriminant_smul` | ~589 | [TOPIC-jq-model.md](phiGenSplitting/TOPIC-jq-model.md) |
| **T7 (done)** | the Hauptmodul form | `hasSum_qParam_mul{,_laurent}`, `exists_aeval_jq_sub_holomorphicAtInfty`, `mem_adjoin_jq_of_hasSum_of_slash_invariant` | ~462 | [TOPIC-hauptmodul.md](phiGenSplitting/TOPIC-hauptmodul.md) |
| **T8 (done)** | the cone application: the descended coefficients lie in `ℚ[jq]` | the Hecke translates, `cosetPoly_smul`, `hasSum_cosetPoly_coeff`, `mem_adjoin_jq_of_phiGenDescends` | ~681 | [TOPIC-phiGen-descends.md](phiGenSplitting/TOPIC-phiGen-descends.md) |

R1 = T5–T7; T8 is the cone's (c) and needs all three. The split is by
mathematical object, not by file: T5 is generic modular-form analysis with no
`jq` in it; T6 is the formal↔analytic bridge for `jq`; T7 is the pole-bounded
membership statement that completes R1; T8 is the Hecke-coset consumer.

**T5 is done** (2026-09-21, one goal round). Its work order was
[topics/phiGenSplitting/TOPIC-r1-kernel.md](phiGenSplitting/TOPIC-r1-kernel.md),
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
[logs/phiGen-port.md](../logs/phiGen-port.md).

**T6 is done** (2026-09-22, one goal round). Its work order was
[topics/phiGenSplitting/TOPIC-jq-model.md](phiGenSplitting/TOPIC-jq-model.md),
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
[logs/phiGen-port.md](../logs/phiGen-port.md) §3.

**T7 is done** (2026-09-22, one goal round) — **R1 is complete.** Its work order
was
[topics/phiGenSplitting/TOPIC-hauptmodul.md](phiGenSplitting/TOPIC-hauptmodul.md),
now the executed plan. It delivered the headline
`mem_adjoin_jq_of_hasSum_of_slash_invariant` in
`FLTForHuman/ModularForms/Hauptmodul.lean`, composing T5's kernel with this
topic's pole killing and T6's realization, and **exported** `RealL` + closure and
`hasSum_qParam_mul{,_laurent}` as T8's interface (FLT duplicates the `RealL`
block in T8's pin file; the port does it once). The audit came out exactly as
predicted — this is the glue topic: no public mathlib lemma replaces `RealL`, its
closure, pole killing, or the headline; mathlib supplies only the Cauchy-product
core and the `HahnSeries`/`qParam` API. The port is 483 lines against the
462-line pin (ratio 1.05, T5 was 1.79, T6 1.06), over 15 public and 16 private
declarations. No blow-up; the only drift was `if_pos` → `ite_eq_left`. The
checker moved 153 → 168 (the `RealL` block and the headline are verified as
transcribed statements), the consumer gained Zone E (the wire test runs the
headline on `jq` with T6's two theorems as its hypotheses), and R1's analytic
input is now a complete, compiled chain. The measured cost is in
[logs/phiGen-port.md](../logs/phiGen-port.md) §7.

**T8 is done** (2026-09-22, one goal round) — **the planned sequence is complete
and the cone's (c) is discharged.** Its work order was
[topics/phiGenSplitting/TOPIC-phiGen-descends.md](phiGenSplitting/TOPIC-phiGen-descends.md),
now the executed plan. It delivered `PhiGen.mem_adjoin_jq_of_phiGenDescends` over
three new modules — `Defs/HeckeOperator.lean`, `HeckeQExpansion.lean` and
`PhiGenDescends.lean` — plus the Hecke/coset interface
(`hasSum_qParam_heckeMatrix_smul`, `hasSum_qParam_heckeDiagMatrix_smul`,
`cosetPoly_smul`). The audit's headline was positive: mathlib has **no** Hecke
operators, so the topic adds the sub-effort's first definition module, taking only
the 60-line subset the cone uses (the `heckeU`/`heckeT` block is genuinely unused
— 0 occurrences in T8's files, and elsewhere only in the doc-site
`attribute [-simp]` pragma of 5 cone nodes). It imports T7's `RealL`/closure
rather than copying the pin's ~97 duplicated lines. The port is 725 lines, 8
public and 43 private declarations, against ~741 lines of pin content (ratio
0.98 — the sub-effort's cheapest); the predicted `FunLike` trap did not occur, but
a `mapGL`-entry transparency issue did, fixed with mathlib's own
`set_option backward.isDefEq.respectTransparency.types false`. The checker moved
168 → 176; the consumer gained Zone F. The measured cost and the three shape
issues are in [logs/phiGen-port.md](../logs/phiGen-port.md) §8.

**T9 is done** (2026-09-22, one goal round) — **the cone's (b) has its
integrality half.** Its work order was
[topics/phiGenSplitting/TOPIC-integrality.md](phiGenSplitting/TOPIC-integrality.md),
now the executed plan. It delivered `PhiGen.PhiGenDescends.intCoeffs` (the
descended family has integer `q`-expansion coefficients) and
`PhiGen.aeval_jq_intCoeffs_descent` (`IntCoeffs (P(jq))` forces `P ∈ ℤ[X]`) in
`FLTForHuman/ModularCurve/PhiGenIntegrality.lean`, both verbatim from their pin
wrappers. It is the **first deliberate route deviation** in the sub-effort, and
**Route A shipped in round 1**: `jq` and the conjugate family lift to
`LaurentSeries (integralClosure ℤ K)`, and `coeffMap` is pushed through
`qExpand`/`qTwist`/`phiProd`, replacing FLT's `CoeffsIntegral` closure block and
its three polynomial-coefficient lemmas with ring structure. The audit's one
negative result: the work order predicted `IsPrimitiveRoot.isIntegral` would
replace the pin's two manual root-of-unity lemmas, but the hypothesis is only
`ζ ^ ℓ = 1` (not primitivity), so the port uses one generic
`mem_integralClosure_of_pow_eq_one` over `X ^ ℓ - 1` instead. The route-check's
predicted **line** saving did not materialize (83 replaced pin lines became ~90
lines of bridges), but the module is 322 lines against ~347 of in-scope pin
content (ratio 0.93), and it promotes `coeff_aeval_jq_neg` (to `Defs/Jq.lean`)
and `poleOrderLE_aeval_jq` (to `Defs/PhiGen.lean`), which the pin repeats
privately in 9 files. The checker moved 176 → 180 (178 on the promotion); the
consumer gained Zone G (with the named `P = X` instance
`aeval_jq_intCoeffs_descent_X`); the measured cost and the route decision are in
[logs/phiGen-port.md](../logs/phiGen-port.md) §9.

**T10 is done** (2026-09-22, one goal round) — **the cone's (b) is complete.**
Its work order was
[topics/phiGenSplitting/TOPIC-pole-bounds.md](phiGenSplitting/TOPIC-pole-bounds.md),
now the executed plan. It delivered `PhiGen.phiProd_conj_coeff_zero_lead` (the
constant term's leading coefficient: the pole is exactly `q ^ (-(ℓ * ℓ + ℓ))`
with residue `1`) and `PhiGen.phiProd_conj_coeff_eq_zero_of_le` (the same bound
for every non-constant coefficient), both verbatim from their pin wrappers, in
`FLTForHuman/ModularCurve/PhiGenPoleBounds.lean`. It also **promoted the shared
`TPoleOrderLE` prelude** into `Defs/PhiGen.lean`: the closure
(`mono`/`zero`/`one`/`neg`/`add`/`mul`/`qTwist`/`qExpand`, `of_jSimplePole`), the
conjugate bounds (`conjPoleBound`, `tPoleOrderLE_conj_zero/_succ/_conj`) and the
coefficient bounds (`tPoleOrderLE_coeff_X_sub_C`, `_mul`, `_prod`,
`_phiProd_coeff`) — 23 public declarations. The pin copies that prelude across
**six** developments (the `phiProd_conj` development, itself shipped twice, and
all five 328-block copies) — physically in **twelve** `S_` files, so writing
it once is the largest duplication removal of the remaining cone; **T11 imports
it with no additions** (the union, including the 328-only coefficient bounds, is
public). The audit's one near-miss resolved as predicted: mathlib's
`IsPrimitiveRoot.geom_sum_eq_zero` is the *sum* fact, so the pin's *product*
lemma `pow_sum_range_isPrimitiveRoot` ported **whole**, its `ℓ = 2`-versus-odd
case split included, though every step is a mathlib call
(`Nat.Prime.eq_two_or_odd'`, `IsPrimitiveRoot.eq_neg_one_of_two_right`,
`IsPrimitiveRoot.pow_eq_one`, `Finset.sum_range_id_mul_two`, `Even.neg_one_pow`).
The port is 497 Lean lines (187 in `Defs/PhiGen.lean`, 310 in the new module)
against the 391-line representative pin file, ratio **1.27**; unlike T9's
`intCoeffs`, both exports have a concrete instance (`K = ℂ`, `ℓ = 2`, `ζ = -1`,
`IsPrimitiveRoot.neg_one`), named `wire_zero_lead`/`wire_eq_zero_of_le` inside the
module. `#print axioms` on both is clean, the checker moved 180 → 205 (11 of the
new statements are promoted from pin-`private` declarations, verified through a
new dotted-name fallback), and the consumer gained Zone H. Measured cost and the
dedup count are in [logs/phiGen-port.md](../logs/phiGen-port.md) §10.

**T11 is done** (2026-09-22, one goal round) — **the cone's construction is
built.** Its work order was
[topics/phiGenSplitting/TOPIC-datum-assembly.md](phiGenSplitting/TOPIC-datum-assembly.md),
now the executed plan, which re-cut the remainder by mathematical object
(construction → properties → consequence). It delivered three modules:

- `FLTForHuman/ModularCurve/PhiGenDescent.lean` — (a)'s
  `PhiGen.exists_phiGenDescends` (the twist/Galois descent of the product's
  coefficients to `ℚ((q))`);
- `FLTForHuman/ModularCurve/PhiGenDescendsStructure.lean` — the 328 block's five
  shape exports: `PhiGenDescends.c_top`, `.c_eq_zero`, `.poleOrderLE`,
  `.sum_mul_jqN_pow_eq_zero` and `evalAtJ_injective`;
- `FLTForHuman/ModularCurve/ModularPolynomialAssembly.lean` — (d)'s
  `exists_modularPolynomialData_coeff_eq` and `splits_of_coeff_evalAtJ_eq`.

All eight are the pin wrappers verbatim. `evalAtJ_injective` took the planned
mathlib route (`transcendental_jq` + `transcendental_iff_injective` +
`Polynomial.map_injective`), so the pin's private `aeval_jq_eq_zero` is not
ported and T12 imports this public copy instead of the 895 block's private one.
The port is 701 lines (339 + 161 + 201) against ~590 deduplicated pin lines,
ratio **1.19**; `#print axioms` on all eight is clean, the checker moved
205 → 213, and the consumer gained Zone I with the first **end-to-end** wire test
(`K = CyclotomicField ℓ ℚ`: descent → integrality → membership → assembly). The
dependency fact of the work order's §4 was confirmed: the 328 block and the
assembly are upstream of (e), so the blueprint's old T11 (328 + the whole 502-line
(d) bucket) was not one executable unit. Measured cost and the division are in
[logs/phiGen-port.md](../logs/phiGen-port.md) §11.

**T12 is done** (2026-09-22, one goal round) — **the datum has its properties.**
Its work order was
[topics/phiGenSplitting/TOPIC-irreducibility-symmetry.md](phiGenSplitting/TOPIC-irreducibility-symmetry.md),
now the executed plan. It delivered three modules:

- `FLTForHuman/ModularCurve/JqCoeffPositivity.lean` — `one_le_coeff_jq` (every
  regular coefficient of `j(q)` is `≥ 1`), with two of the work order's mathlib
  substitutions closing (`coeff_mul_prod_one_sub_of_lt_order`, and
  `PowerSeries.expand` + `mk_one_mul_one_sub_eq_one`);
- `FLTForHuman/ModularCurve/ModularPolynomialIrreducible.lean` — the 895 block
  written once: `conj_injective`, `aeval_jq_ne_jqN`/`jqN_not_mem_adjoin_jq`,
  `phiIrreducible_of_splits`, `swapBivar_monic_of_coeff_bounds`,
  `transposeToAdjoin_monic_of_qExpansion`, `evalSymm_of_irreducible`,
  `evalSymm_of_splits`, `evalAtJGen_injective`, `swapBivar_eq_of_evalSymm`,
  `aeval_jqN_toAdjoin`, `minpoly_jqN_eq`;
- `FLTForHuman/ModularCurve/ModularPolynomialProperties.lean` —
  `evalSymm_of_coeff_evalAtJ_eq` and the capstone
  `exists_phiIrreducible_evalSymm`.

**The dedup is the cone's largest:** the 895 block ships in **five** pin files
(`5 × 895 ≈ 4,475` lines) — §2's "×3" counted only its three graph nodes and
missed the two hidden exports `swapBivar_monic_of_coeff_bounds` and
`evalSymm_of_irreducible`; the table is corrected. The port writes it once, and
the block's `evalAtJ_injective`/`coeff_aeval_jq_neg`/`evalAtJ_eq_aeval_map_rat`
private copies are T11's, T9's and the new `Defs/Jq.lean` promotion respectively
(T11 rebuilt green after the promotion). The port is 1670 lines (425 + 1070 + 175)
against 1467 deduplicated pin lines, ratio **1.14**; `#print axioms` on all
nineteen public declarations is clean, the checker moved 213 → 233, and the
consumer gained Zone J with the first **unconditional** wire test
(`exists_phiIrreducible_evalSymm` at `ℓ = 2`). Measured cost, the two substitutions
and the shape issues are in [logs/phiGen-port.md](../logs/phiGen-port.md) §12.

**The cone is closed.** R1 (T5–T7), the cone's (c) (T8), the
two halves of (b) (T9, T10), the construction (a) + 328 + (d) (T11), the
properties (T12) and the consequence (T13) are all done:

**T13 is done** (2026-09-22, one goal round) — **the cone is closed.** Its work
order was
[topics/phiGenSplitting/TOPIC-splitting.md](phiGenSplitting/TOPIC-splitting.md),
now the executed plan. It delivered two modules —
`ModularPolynomialUniqueness.lean` (`finrank_adjoin_jqN_eq_of_prime`,
`ModularPolynomialData.eq_of_prime`) and `PhiGenSplits.lean`
(`PhiGen.splits_of_prime`, `PhiGen.splits_prime_at_slot`) — plus a promotion: the
cyclotomic roots moved from the FFG spine's private copies into the public
`Defs/Cyclotomic.lean`. The two pin files' shared `TS` prelude was already ported
(`Defs/TS.lean` + `coeffEmb_qExpand`), and ~200 of their prelude lines are dead
for the exported theorems and were dropped. The port is 407 lines against 766
deduplicated pin lines, ratio **0.53**; the checker moved 233 → 242; the consumer
gained Zone K with the capstone wire (`splits_prime_at_slot` at
`K = CyclotomicField 2 ℚ`, `N = p = 2`, `e = u = 1`). Measured cost and the dedup
are in [logs/phiGen-port.md](../logs/phiGen-port.md) §13.

| topic | piece | deliverable | dedup pin | work order |
|---|---|---|---|---|
| **T9 (done)** | (b) integrality | `intCoeffs`, `aeval_jq_intCoeffs_descent` | ~347 | [TOPIC-integrality.md](phiGenSplitting/TOPIC-integrality.md) |
| **T10 (done)** | (b) pole bounds | `phiProd_conj_coeff_{eq_zero_of_le,zero_lead}` + the shared `TPoleOrderLE` block | 391 + ~180 (dup ×12) | [TOPIC-pole-bounds.md](phiGenSplitting/TOPIC-pole-bounds.md) |
| **T11 (done)** | the construction: (a) + the 328 block + (d) assembly | `exists_phiGenDescends`; `c_top`/`c_eq_zero`/`poleOrderLE`/`sum_mul_jqN_pow_eq_zero`/`evalAtJ_injective`; `exists_modularPolynomialData_coeff_eq`, `splits_of_coeff_evalAtJ_eq` | 315 + 328 (dup ×7, 84 distinctive) + 191 | [TOPIC-datum-assembly.md](phiGenSplitting/TOPIC-datum-assembly.md) |
| **T12 (done)** | the properties: irreducibility/symmetry | `one_le_coeff_jq`; the 895 block's exports (`phiIrreducible_of_splits`, `transposeToAdjoin_monic_of_qExpansion`, `evalSymm_of_splits`); `evalSymm_of_coeff_evalAtJ_eq`; `exists_phiIrreducible_evalSymm` | 386 + 895 (dup ×5) + 124 + 62 | [TOPIC-irreducibility-symmetry.md](phiGenSplitting/TOPIC-irreducibility-symmetry.md) |
| **T13 (done)** | the consequence: uniqueness + the splitting | `finrank_adjoin_jqN_eq_of_prime`, `ModularPolynomialData.eq_of_prime`, `splits_of_prime`, `splits_prime_at_slot` | 52 + 73 + 353 + 288 | [TOPIC-splitting.md](phiGenSplitting/TOPIC-splitting.md) |

The pin-line column is the deduplicated count from the estimate below; **it is not
effort** — T8 measured 741 pin lines in one round at ratio 0.98, T9 347 at 0.93,
T11 590 at 1.19, T12 1467 at 1.14 and T13 766 at 0.53 — so budgets are set by
route risk and shape variety, not lines. §6's re-route menu is now history: the
cone is fully ported, and the parent FFG effort (PORTING-FFG §7.8's T14–T19)
proceeds with `splits_prime_at_slot` as a theorem.

**T12's entry points are now public.** It imports from T11's
`PhiGenDescendsStructure.lean` the public `evalAtJ_injective` (so the 895 block
drops its private copy) and from T10's `Defs/PhiGen.lean` the whole
`TPoleOrderLE` prelude; from T11's `ModularPolynomialAssembly.lean` it imports
`exists_modularPolynomialData_coeff_eq` and `splits_of_coeff_evalAtJ_eq`. T13 then
imports T12's `exists_phiIrreducible_evalSymm`, `evalSymm_of_coeff_evalAtJ_eq` and
T11's `evalAtJ_injective` for `eq_of_prime`.

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

**What is left after (c), measured (2026-09-22; updated after T12).** The
deduplicated cone is
**5,811 lines over 37 developments**; T5–T8 cover **1,956** of it (their 16 nodes
are all singletons), T9–T10 the whole (b) bucket (**1,266**), T11 the
construction — (a)'s 315, the 328 block's 84 distinctive lines and the assembly's
191 — and T12 the properties (386 + 895 + 124 + 62 = **1,467**), so the only
remaining piece is the consequence, **≈519 lines** (52 + 73 + 353, plus the
288-line seed):

| piece | dedup pin | est. port | topics |
|---|---|---|---|
| (a) descent `exists_phiGenDescends` | 315 | **339 shipped** (T11) | **done** |
| (b) integrality + pole bounds | 1,266 | **322 + 497 shipped** (T9 integrality, T10 pole bounds + the shared prelude) | **done** |
| the 328 block (distinctive) + (d) assembly | 84 + 191 | **161 + 201 shipped** (T11) | **done** |
| (e) irreducibility/symmetry + `one_le_coeff_jq` + the (d) tail | 386 + 895 + 124 + 62 | **425 + 1070 + 175 shipped** (T12) | **done** |
| (f) the consequence: `finrank`/`eq_of_prime` + `splits_of_prime` | 52 + 73 + 353 (+288 seed) | 430–500 | T13 |

The (b) row's route-check (Option 2 below) is now fully **resolved**, and the
bucket is closed. T9 shipped Route A for the integrality half in one round: **322
port lines against ~347 of in-scope pin content (ratio 0.93)**, so the predicted
~150–250 lines was pessimistic (the 83 replaced closure/polynomial lines became
~90 lines of reusable `coeffMap` bridges, not a line saving) but the dedup did
land — `coeff_aeval_jq_neg` and `poleOrderLE_aeval_jq` are public in `Defs/`, and
T7 shrank by 25 lines. T10 shipped the pole bounds in one round at **497 port
lines (187 shared prelude in `Defs/PhiGen.lean` + 310 in
`PhiGenPoleBounds.lean`) against the 391-line representative pin file (ratio
1.27)** — higher than T9 because the shared block is the *union* of the six
copies' preludes (the 391 file does not itself carry the 328-only
`tPoleOrderLE_coeff_mul/_prod/_phiProd_coeff`, ~45 lines) and because the module
carries a 60-line header. T11 then closed the construction in one round at **701
port lines (339 + 161 + 201) against 590 deduplicated pin (ratio 1.19)**; the
blueprint's old T11, which bundled the 328 block with the whole 502-line (d)
bucket, was **not executable as one unit** — (d)'s symmetry/existence/uniqueness
tail is downstream of (e), and the work order's §4 fixed the boundary. T12 closed
the properties in one round at **1670 port lines (425 + 1070 + 175) against 1467
deduplicated pin (ratio 1.14)**; its `one_le_coeff_jq` prediction of 190–250 lines
(ratio ≈ 0.5–0.65) **did not hold** — two mathlib substitutions landed, but the
irreplaceable eta-truncation and inverse-comparison machinery dominates, so the
module came in at 1:1 (logs §12.3).

Several pieces are single developments shipped many times by p2m (the 895-line
block **×5**, the 328-line block body ×7, the 391-line block ×2, and the ~170-line
`TPoleOrderLE` prelude ×12); deduplicating at the
source, as T5–T8 did, is what makes the table's numbers the ones to price. The
remaining pieces use **no Hecke operators** (their only `hecke*` occurrence is
the mechanical `attribute [-simp]` line p2m emits), so T8's minimal Hecke subset
needs no extension. The default remains a faithful port at roughly 1:1 — the
same "price the glue, not the mathlib-replaceable leaves" profile as T6/T7 —
unless one of the options below is route-checked and shown shorter.

All speculative; none is a plan. They are the reason (c) was the interesting
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
- **Option 2 — the integrality route: route-checked, shipped, and measured.**
  (Route-checked 2026-09-22; **implemented as T9**, one round, log §9.) The
  integrality is **not avoidable**: the datum's
  type is `Polynomial (Polynomial ℤ)`, and the triangularity forces
  $`P_k`$'s coefficients to be the descended series' negative-degree coefficients
  ($`P_k.\mathrm{coeff}\,m = (c_k).\mathrm{coeff}\,(-m)`$), so the descended
  family must be shown to have integer $`q`$-expansion coefficients. The pin's
  proof of *that* is inflatable in three ways, and the measurement is now in:
  1. ~~`IsPrimitiveRoot.isIntegral` replaces the pin's manual root-of-unity
     lemmas.~~ **Falsified by the spike:** the statement's hypothesis is only
     `ζ ^ ℓ = 1`, not primitivity, so `IsPrimitiveRoot.isIntegral` does not apply.
     Route A uses one generic `mem_integralClosure_of_pow_eq_one` over `X ^ ℓ - 1`
     (the pin's argument, in one lemma instead of two).
  2. **Confirmed.** The pin's coefficient-wise `CoeffsIntegral` predicate and its
     six closure lemmas became a lift to `LaurentSeries (integralClosure ℤ K)`
     plus `coeffMap`/`HahnSeries.map` commutation (~90 lines of bridges in place
     of 83 lines of closure plus the 42-line polynomial-coefficient block).
  3. **Confirmed, with a correction.** The descent
     `IntCoeffs (aeval jq P) → P ∈ ℤ[X]` is the pin's strong induction (~40
     lines), not the ~20 the estimate hoped: triangularity only reads the *top*
     coefficient directly, so the lower coefficients need the induction. The
     `intCoeffs_jq`/`IntCoeffs.sub` helpers were ported.
  The two deduplications did land: `coeff_aeval_jq_neg` (9 pin files) and
  `poleOrderLE_aeval_jq` are public in `Defs/`, T7 shrank 25 lines, and the
  integrality half is **322 port lines against ~347 in-scope pin** (ratio 0.93).
  The predicted ~150–250 was pessimistic; the *whole* (b) bucket is now
  ~950–1,150 rather than the table's 1,330–1,460.
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
  ([studies/flt-function-field-theory-and-mathlib.md §13](../../studies/flt-function-field-theory-and-mathlib.md)).
  It is still not a substitute for (c), for three measured reasons: it is absent
  from this cone (0 `AlgebraicCurve` nodes); using it would be circular, because
  FLT's modular `CurveModel`s are built and proved *downstream* of
  `functionFieldGeneration` and cite `splits_prime_at_slot`
  ([studies/flt-ffg-field-theory.md §7](../../studies/flt-ffg-field-theory.md));
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

Companion notes: [math/010](../../math/010-function-field-generation.md),
[base/013](../../base/013-riemann-existence-and-the-q-expansion-principle.md) (the
mathematics of the analytic input),
[base/006](../../base/006-the-modular-equation.md),
[base/005](../../base/005-cyclic-isogenies-and-level.md),
[base/004](../../base/004-the-j-invariant.md),
[base/003](../../base/003-no-level-2-weight-2-cusp-forms.md).

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
