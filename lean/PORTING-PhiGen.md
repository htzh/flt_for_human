# Blueprint: the Φₚ splitting cone — `PhiGen.splits_prime_at_slot`

**Status: analysis done (2026-09-21); no port started.** This file is the
math-content inventory of the 44-node cone below
`ModularCurve.PhiGen.splits_prime_at_slot`, the measurement that the headline
line count overstates it by ~1.6×, and the plan for the next topic: isolating
the cone's one genuinely analytic input, the **level-one q-expansion principle**
— the Riemann-existence-flavoured step the FLT proof substitutes for the
classical function-theoretic argument. The topic is sketched here as work orders
because it is already more than one; if it grows, it splits out into
`topics/phiGenSplitting/TOPIC-*.md` and this file keeps only the decision.

Companion records:

- [math/010](../math/010-function-field-generation.md) — the mathematics of the
  target. Its §3 is the splitting statement, §4 the descent.
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
   (§5, §6).

**What is not settled.** Whether (c) as a standalone theorem actually simplifies
the algebra, and whether the right statement of (c) is the "holomorphic
invariant q-series is constant" kernel or the full
`mem_adjoin_jq_of_realL_invariant` headline. §5–§6 carry both sides.

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
`mem_adjoin_jq_of_phiGenDescends`, is 47 lines and carries 1,910 lines of
closure).

| piece | what it proves | representative | ≈ bucket | analysis on ℍ? |
|---|---|---|---|---|
| (a) | coefficients of `phiProd` descend to `ℚ((q))` | `exists_phiGenDescends` | 315 | no |
| (b) | the descended family is integral, monic, degree `ℓ+1`, pole ≤ `ℓ+1` | `intCoeffs`, `aeval_jq_intCoeffs_descent`, `phiProd_conj_coeff_*`, the 328-block | 1,270 | no |
| (c) | the descended family lies in `ℚ[j]` | `mem_adjoin_jq_of_phiGenDescends`, then the Hecke and `HasSum` modules | 1,909 | **yes** |
| (d) | assembly + uniqueness of the level-`ℓ` modular polynomial | `exists_modularPolynomialData_coeff_eq`, `eq_of_prime`, `finrank_adjoin_jqN_eq_of_prime`, `exists_phiIrreducible_evalSymm` | 500 | no (inherits c) |
| (e) | irreducibility, symmetry, non-membership | `one_le_coeff_jq` plus the 895-line block | 1,280 | no |
| (f) | the splitting statement and its wrapper | `splits_of_prime`, `splits_of_coeff_evalAtJ_eq` | 400 | no |

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
   `+ - *` and finite products (`hasSum_qParam_mul{,_laurent}`).
3. **Hecke translates** — `hasSum_qParam_heckeMatrix_smul` and
   `hasSum_qParam_heckeDiagMatrix_smul`: the substitutions
   $`\tau \mapsto (\tau+b)/\ell`$ and $`\tau \mapsto \ell\tau`$ act on the
   $`q`$-expansion by the corresponding coefficient twist, and `cosetPoly_smul`
   plus `PhiGenDescends.hasSum_cosetPoly_coeff` show the product's coefficients
   are $`\mathrm{SL}_2(\mathbb{Z})`$-invariant.
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

**What this is classically.** Step 5 is the level-one *q-expansion principle*:
the only holomorphic weight-0 modular form of level one is constant, equivalently
that $`X(1)`$ has genus $`0`$ and the $`q`$-expansion is a coordinate at the
cusp. It is the shadow of the valence formula / Riemann-surface theory of
$`X(1)`$, and it is what proves a coefficient that is *a priori* a rational
function of $`j`$ is actually a *polynomial* — the property the datum assembly
in (d) needs.

**One framing caution, recorded deliberately.** math/010 §4 says the FLT proof is
"circuitous without Riemann existence" in the sense of the classical statement
"$`j`$ is a function of degree $`\psi(M)`$ on $`X_0(M)`$", which the proof
replaces by the root list plus the unique-common-root principle. That is a
*different* gap from (c): it is a degree statement about $`X_0(N) \to X(1)`$,
filled by (a)/(d)/(e), whereas (c) is a statement about $`X(1)`$ itself. Both are
"specialized Riemann existence" statements in spirit, and the next topic should
pin which one it is proving before it starts. The recommendation here is (c),
because (c) is the one with no algebraic substitute and the one whose isolation
is a prerequisite for any re-route.

## 5. The next topic: isolate (c)

**Goal.** One mathlib-only module that states and proves the level-one
q-expansion principle and its corollary for the descended family, with the
analytic step isolated and named, so that the algebra of (a)/(b)/(d)/(e) can be
attempted without it.

Proposed landing spot (name is the session's choice):
`FLTForHuman/ModularCurve/QExpansionPrinciple.lean`, beside
`Defs/PhiGen.lean`.

**Work orders, in dependency order.** (Sketched here; if the topic is picked up
these become `topics/phiGenSplitting/TOPIC-*.md`.)

- **c1 — pick the interface.** Decide between the minimal kernel
  (`holomorphic SL₂(ℤ)-invariant q-series is constant`) and the headline
  (`mem_adjoin_jq_of_realL_invariant`). Recommendation: port the kernel, state
  the headline on top. *Uncertainty:* the FLT `RealL` predicate may be
  avoidable entirely by stating the kernel directly over `HasSum`; measure.
- **c2 — the analytic kernel.** Prove c1's kernel. This is the one genuine
  analysis: package the function as a weight-0 `ModularForm`, use
  `ModularForm.eq_const_of_weight_zero`, and check the boundedness-at-cusps
  obligation. *Tradeoff:* this is a transcription of mathlib-usable material,
  not new mathematics; the value is the *statement* and its placement, not the
  proof.
- **c3 — pole killing.** `exists_aeval_jq_sub_holomorphicAtInfty`; pure Laurent
  algebra, ~84 lines, likely the cheapest work order and already close to the
  port's `Defs/Jq.lean` vocabulary.
- **c4 — the headline.** `mem_adjoin_jq_of_realL_invariant` = c2 + c3.
- **c5 — the coset application.** The Hecke translate lemmas,
  `cosetPoly_smul`, `hasSum_cosetPoly_coeff`, and
  `mem_adjoin_jq_of_phiGenDescends`. *Uncertainty:* whether the Hecke translates
  are needed at all, or whether a more direct realization of the coset product's
  coefficients shortens this. This is the largest and least predictable order.

**Success test.** `#print axioms` clean; the analytic kernel is a single named
declaration whose statement a reader can compare with the classical
q-expansion principle; the consumer
([spec/ModularCurveConsumer.lean](spec/ModularCurveConsumer.lean)) gains a Zone
item binding it.

**Cost honesty.** The cone's own `jq`-coefficients precedent is the warning:
math/010 priced the `744`/`196884` coefficients against this same 11,034-line
cluster and they turned out to be a 237-line standalone file (47× error). (c)'s
1,909 lines are a *route* count, not a proof budget; c2/c3 could be small, or
c5 could be most of the 1,909. The playbook rule applies: route-check each
order before pricing it.

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
- **Option 3 — strengthen (c) and skip the descended family.** If (c) is stated
  for Laurent series directly — "a series fixed by both the twist and the Galois
  action, with pole order $`\le n`$, lies in $`\mathbb{Z}[j]`$" — then the
  intermediate rationality of (a) and the pole bounds of (b) may be avoidable.
  *Tradeoff:* a stronger, less classical statement; the analytic input is no
  longer recognizable as the q-expansion principle, which defeats part of the
  point. Recommend against unless Options 1–2 stall.
- **Option 4 — re-route the *caller*.** PORTING-FFG §7.7's third way: make Φₚ an
  eighth `Inputs` field and prove the seven fields from it. This note does not
  change that arithmetic; it only says the field's *content* is (f) and that (c)
  is what a later re-route would need.

**Shared tradeoff.** The parent effort's measured lesson is that cost tracks the
route, not the subtree. None of Options 1–3 should be started before the
corresponding node's own proof lines and helpers are counted (PORTING-FFG §2's
standing rule).

## 7. Correspondence with the notes

- **math/010 §3** states the splitting and gives the classical root description
  ($`p+1`$ cyclic isogenies). It is accurate and is the statement of record.
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
  degree of the witnessing polynomial. The membership is (c), the analytic
  kernel, and it is 1,909 lines — a third of the cone. A reader following the
  note literally would walk past that third.
- **Hidden results.** The 895-line block contains `aeval_jq_ne_jqN` and
  `jqN_not_mem_adjoin_jq`, which are §5–§6 subject matter but are not graph
  nodes. A re-route should decide deliberately whether to expose them.

## 8. Open questions and uncertainties

- **Is (c) the right "Riemann existence" statement?** See §4's caution. (c) is
  the level-one q-expansion principle; the degree-$`\psi(M)`$ statement math/010
  §4 has in mind is a different gap, filled by (a)/(d)/(e). A session that starts
  the topic should state which it is proving; the recommendation is (c) because
  it has no algebraic substitute.
- **Does (c) actually unblock a shorter algebra?** Untested by design. §6 lists
  four options; the first act of the topic after c2–c4 is to count the affected
  nodes' proof lines before committing.
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
[base/006](../base/006-the-modular-equation.md),
[base/005](../base/005-cyclic-isogenies-and-level.md),
[base/004](../base/004-the-j-invariant.md).

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
