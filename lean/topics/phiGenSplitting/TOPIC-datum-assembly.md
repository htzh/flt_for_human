# Topic 11: the descended family and the modular-polynomial datum

**Status: done (2026-09-22), one goal round — the cone's construction is
complete.** Three modules: `FLTForHuman/ModularCurve/PhiGenDescent.lean` (a),
`PhiGenDescendsStructure.lean` (the 328 block) and
`ModularPolynomialAssembly.lean` (d), green with 0 warnings and no `sorry`; all
eight public statements are the pin wrappers verbatim; `evalAtJ_injective` took
the mathlib `transcendental_jq` route as planned. The measured cost and the
answers to the §10 questions are in
[logs/phiGen-port.md](../../logs/phiGen-port.md) §11. This file is kept as the
executed plan. The plan is [PORTING-PhiGen.md](../../PORTING-PhiGen.md) §5–§6; the
mathematics is [math/010](../../../math/010-function-field-generation.md) §3 and
[base/006](../../../base/006-the-modular-equation.md) §2 and §6 steps 3–4. **T12,
the properties (irreducibility and symmetry), is next.**

**This file began as a look-ahead and is now the topic's work order.** §4.1 fixes
the remaining cone as three topics cut by mathematical object — construction
(T11), properties (T12), consequence (T13); §4.2 is the redundancy-removal and
mathlib-reuse plan. The earlier wave/parallelism cut of the same declarations is
withdrawn.

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

1. [PORTING-PhiGen.md](../../PORTING-PhiGen.md) §3 (b)/(d) and §5 (the sequence);
2. [base/006](../../../base/006-the-modular-equation.md) §2 and §6 steps 3–4 —
   the integrality mechanism, the pole bound, the assembly and the uniqueness;
3. [math/010](../../../math/010-function-field-generation.md) §3 — the modular
   polynomial, its slot description and the splitting;
4. [TOPIC-pole-bounds.md](TOPIC-pole-bounds.md) (T10, the immediate predecessor
   and the prelude this topic imports), [TOPIC-integrality.md](TOPIC-integrality.md)
   (T9) and [logs/phiGen-port.md](../../logs/phiGen-port.md) §9;
5. [porting-playbook.md](../../porting-playbook.md) §2 (deduplicate at the
   source), §3.9 and §3.11.

## 1. The mathematics in one page

Two objects meet in this topic.

**The descended coefficient family.** Fix a prime `ℓ`, a field `K` with an
algebra structure over `ℚ`, and a primitive `ℓ`-th root `ζ ∈ K`. The conjugate
product

$$\mathrm{phiProd}_\ell(\zeta) \\;=\\; \prod_{i : \mathrm{Fin}\\,(\ell+1)}\bigl(X - \mathrm{conj}_i\bigr)$$

is a polynomial in `X` with coefficients in `K((q))`, whose roots are the
`ℓ+1` conjugates of `j` at level `ℓ`:

| root | value in the generic nome `q` |
|---|---|
| the extra / infinity slot | `` $`\mathrm{conj}_0 = j(q^{\ell^2})`$ `` |
| the `ℓ` finite-slope slots | `` $`\mathrm{conj}_{b+1} = \zeta^b\, j(q)`$ `` |

This is the level-`ℓ` splitting of [base/006 §3](../../../base/006-the-modular-equation.md):
with the base point read at `` $`j(q^\ell)`$ ``, the second variable of `` $`\Phi_\ell`$ ``
has exactly these roots. `PhiGenDescends ℓ ζ c` records that each `X`-coefficient
of the product descends to a series `c k ∈ ℚ((q))`, i.e. that it lies in the
subring `` $`\mathbb{Q}((q^\ell))`$ `` and is the level substitution of a series
in the generic nome:

```lean
def PhiGenDescends (c : ℕ → LaurentSeries ℚ) : Prop :=
  ∀ k : ℕ, (phiProd ℓ (conj ℓ ζ)).coeff k = coeffEmb K (qExpand ℚ ℓ (c k))
```

So `c k` is the `Y^k`-coefficient of `` $`\Phi_\ell(j(q), Y)`$ `` — the datum's
coefficient, with the level substitution undone. Piece (a) (this topic)
*produces* such a `c`; T10 proves its pole bounds; T9 proves it is integral; T8
proves its membership in `` $`\mathbb{Q}[j(q)]`$ ``; this topic extracts its
*shape* and assembles it into the polynomial.

**The datum.** `ModularPolynomialData ℓ` is the bundled modular polynomial: a
`` $`\Phi \in \mathbb{Z}[X][Y]`$ ``, monic in `Y`, of `Y`-degree
`` $`\psi(\ell) = \ell + 1`$ ``, vanishing at `` $`(j(q),\, j(q^\ell))`$ `` under
`` $`X \mapsto j(q)`$ `` and `` $`Y \mapsto j(q^\ell)`$ ``. The topic says the
descended family *is* such a datum, and that such a datum is unique.

**What the 328 block extracts from `PhiGenDescends` alone.** All five are
consequences of the product being monic of degree `ℓ+1` with the pole bound of
T10's prelude, plus the fact that the level substitution is injective:

| declaration | mathematics |
|---|---|
| `PhiGenDescends.c_top` | the top coefficient is `1`: `phiProd` is monic, so `c (ℓ+1) = 1`. |
| `PhiGenDescends.c_eq_zero` | above degree `ℓ+1` the coefficients vanish: `natDegree (phiProd) = ℓ+1`. |
| `PhiGenDescends.poleOrderLE` | each `c k` has pole order `≤ ℓ+1` at `q = 0`. In the expanded nome each product coefficient has pole `≤ ℓ²+ℓ` (the extra root contributes `ℓ²`, each of the `ℓ` finite roots contributes `1`); this is exactly T10's `tPoleOrderLE_phiProd_coeff`. Undoing `q ↦ q^ℓ` divides the exponent by `ℓ`, so `` $`\ell^2+\ell = \ell(\ell+1)`$ `` becomes `ℓ+1`. |
| `PhiGenDescends.sum_mul_jqN_pow_eq_zero` | the modular-equation relation `` $`\Phi_\ell(j(q), j(q^\ell)) = 0`$ ``, read in the descended family: `` $`\sum_{k\le \ell+1} c_k\, j(q^\ell)^k = 0`$ ``. The proof applies the level substitution to the sum, which sends `` $`j(q^\ell)`$ `` to the extra root `conj 0`, and evaluates the monic product at its own root. |
| `evalAtJ_injective` | `P ↦ P(j(q))` from `` $`\mathbb{Z}[X]`$ `` to `` $`\mathbb{Q}((q))`$ `` is injective — `j` is transcendental, equivalently `` $`j(q)^d = q^{-d}(1 + 744q + \cdots)`$ `` reads the leading coefficient off the `q^{-d}` coefficient. |

The last one is stated over `ℤ` but is really the triangularity of `j`'s pole;
it is what makes the descent *faithful*, and it is duplicated privately in the
895-line block (T12).

**The assembly (piece (d)).** With `c` in hand, the passage from a family of
series to a polynomial is three steps, each an input already ported or landed by
T9:

1. `hmem : ∀ k, c k ∈ ℚ[jq]` (T8) gives `` $`P_k \in \mathbb{Q}[X]`$ `` with
   `` $`c_k = P_k(j(q))`$ ``;
2. `poleOrderLE` bounds `` $`\deg P_k \le \ell+1`$ `` (the `q^{-d}` coefficient
   of `` $`P(j(q))`$ `` is `` $`P`$ `'s top coefficient);
3. `hint : ∀ k, IntCoeffs (c k)` plus T9's triangularity
   `aeval_jq_intCoeffs_descent` forces `` $`P_k \in \mathbb{Z}[X]`$ ``.

Then `` $`\Phi = \sum_{k\le \ell+1} Q_k(X)\, Y^k`$ `` is the datum:
`c_top` makes it monic, `c_eq_zero`/`hΦdeg` gives degree `ℓ+1`, and
`sum_mul_jqN_pow_eq_zero` is exactly the vanishing at `` $`j(q^\ell)`$ ``. The
exported statement is the assembly in hypothesis form:

```lean
theorem ModularCurve.PhiGen.exists_modularPolynomialData_coeff_eq {K : Type*} [Field K] [Algebra ℚ K]
    {ℓ : ℕ} [hℓ : Fact (Nat.Prime ℓ)] {ζ : Kˣ} {c : ℕ → LaurentSeries ℚ}
    (hc : PhiGenDescends ℓ ζ c) (hint : ∀ k, IntCoeffs (c k))
    (hmem : ∀ k, c k ∈ Algebra.adjoin ℚ {jq}) :
    ∃ data : ModularPolynomialData ℓ, ∀ k, evalAtJ (data.Φ.coeff k) = c k
```

The same file carries the one-line coefficient comparison that turns the datum
back into the product,

```lean
theorem ModularCurve.PhiGen.splits_of_coeff_evalAtJ_eq {K : Type*} [Field K] [Algebra ℚ K]
    {ℓ : ℕ} [hℓ : Fact (Nat.Prime ℓ)] (ζ : Kˣ) {c : ℕ → LaurentSeries ℚ}
    (hc : PhiGenDescends ℓ ζ c) (data : ModularPolynomialData ℓ)
    (hcoeff : ∀ k, evalAtJ (data.Φ.coeff k) = c k) :
    data.Φ.map (((coeffEmb K).comp (qExpand ℚ ℓ)).comp evalAtJ) = phiProd ℓ (conj ℓ ζ)
```

which belongs to piece (f) in the blueprint but lives in this file and is needed
by both the (d) tail and (e).

**Uniqueness and existence (T12/T13).** These four declarations make up 311 of
the (d) bucket's 502 pin lines:

- `eq_of_prime`: any two data at a prime are equal. Both `toAdjoin` images are
  monic, annihilate `` $`j(q^p)`$ `` (so are divisible by its minimal
  polynomial), and have degree `` $`p+1 = \psi(p)`$ ``; a monic polynomial of
  minimal degree annihilating an element *is* its minimal polynomial, so both
  equal `` $`\mathrm{minpoly}_{\mathbb{Q}(j)}(j(q^p))`$ ``. The degree input is
  `finrank_adjoin_jqN_eq_of_prime`.
- `finrank_adjoin_jqN_eq_of_prime`: `` $`[\mathbb{Q}(j)(j(q^\ell)) : \mathbb{Q}(j)] = \ell+1`$ ``,
  from an irreducible datum and `dedekindPsi_prime`.
- `exists_phiIrreducible_evalSymm`: there is an irreducible *symmetric* datum.
  This is the cone's own construction: choose `ζ` in `CyclotomicField ℓ ℚ`
  (mathlib supplies the primitive root), then run (a) descent, (b) integrality,
  (c) membership, (d) assembly, and (e) irreducibility from the splitting.
- `evalSymm_of_coeff_evalAtJ_eq`: symmetry `` $`\Phi(X,Y) = \Phi(Y,X)`$ `` in
  evaluated form. It feeds the splitting identity plus T10's two pole-bound
  exports (the leading pole coefficient `1` of `c 0`, and the vanishing of the
  deeper coefficients of the non-constant family) into the 895-block device
  `transposeToAdjoin_monic_of_qExpansion`, then `evalSymm_of_splits`.

## 2. The scouted inventory

| pin file | lines | content |
|---|---|---|
| `S_ModularCurve_PhiGen_PhiGenDescends_c_top.lean` | 328 | T10's prelude (24–222) + the block (224–314): `coeffEmb_qExpand_injective`, the five exports, `evalAtJ_eq_aeval_map`, `aeval_jq_eq_zero` |
| `S_ModularCurve_PhiGen_PhiGenDescends_c_eq_zero.lean` | 328 | the same file, exported name flipped |
| `S_ModularCurve_PhiGen_PhiGenDescends_poleOrderLE.lean` | 328 | the same file |
| `S_ModularCurve_PhiGen_PhiGenDescends_sum_mul_jqN_pow_eq_zero.lean` | 328 | the same file |
| `S_ModularCurve_PhiGen_evalAtJ_injective.lean` | 328 | the same file |
| `S_ModularCurve_PhiGen_exists_phiGenDescends.lean` | 315 | (a): the twist/Galois descent of `phiProd`'s coefficients — `exists_phiGenDescends` |
| `S_ModularCurve_PhiGen_exists_modularPolynomialData_coeff_eq.lean` | 191 | `natDegree_le_of_poleOrderLE_aeval`, `exists_aeval_jq_eq_of_mem_adjoin`, `PhiGenDescends.exists_intPoly`, `splits_of_coeff_evalAtJ_eq`, `coeff_sum_C_mul_X_pow`, `exists_modularPolynomialData_coeff_eq` |
| `S_ModularCurve_ModularPolynomialData_eq_of_prime.lean` | 73 | `evalAtJGen_injective`, `aeval_jqN_toAdjoin`, `natDegree_toAdjoin`, `toAdjoin_eq_minpoly`, `ModularPolynomialData.eq_of_prime`, `phiIrreducible_of_prime` |
| `S_ModularCurve_finrank_adjoin_jqN_eq_of_prime.lean` | 52 | `aeval_jqN_toAdjoin`, `minpoly_jqN_eq_toAdjoin`, `finrank_adjoin_jqN_eq`, `finrank_adjoin_jqN_eq_of_prime` |
| `S_ModularCurve_exists_phiIrreducible_evalSymm.lean` | 62 | `exists_phiIrreducible_evalSymm` |
| `S_ModularCurve_PhiGen_evalSymm_of_coeff_evalAtJ_eq.lean` | 124 | `coeff_phiProd_coeff`, `c_zero_coeff_lead`, `c_coeff_eq_zero_of_ne_zero`, `c_zero_coeff_eq_zero_of_lt`, `evalSymm_of_coeff_evalAtJ_eq` |

Sizes are the pin's own. The 328-block *body* is shipped in **seven** files — the
five named above plus `S_ModularCurve_PhiGen_tPoleOrderLE_coeffEmb_iff.lean` and
`S_ModularCurve_PhiGen_tPoleOrderLE_of_qExpand.lean`, which flip one of the two
helper exports public instead of one of the five headlines. The ~170-line prelude
it shares with T10 is carried by **twelve** pin files: those seven, T10's two
391-line files, and three siblings (`tPoleOrderLE_phiProd_conj_of_ne_zero`,
`aeval_jq_intCoeffs_descent`, `intCoeffs_jq_pow`). T10's work order says "six
copies"; that counts the prelude's *distinct sites* loosely and undercounts the
carriers by half. The deduplicated core is the distinctive 84 lines of the block
plus the 191-line assembly file.

### 2.1 What is already in the port

| needed | where | status |
|---|---|---|
| `PoleOrderLE`, `TPoleOrderLE`, `JSimplePole`, `IntCoeffs`, `PhiGenDescends`, `conj`, `phiProd`, `EvalSymm`, `PhiIrreducible` | `FLTForHuman/ModularCurve/Defs/PhiGen.lean` | ported (Layer 0b) |
| `ModularPolynomialData`, `modularPolynomialDataOne` | `FLTForHuman/ModularCurve/Defs/Polynomial.lean` | ported |
| `jq`, `jqN`, `evalAtJ`, `dedekindPsi`, `dedekindPsi_prime`, `coeff_aeval_jq_neg` | `FLTForHuman/ModularCurve/Defs/Jq.lean` | ported (promoted by T9) |
| `evalAtJGen`, `ModularPolynomialData.toAdjoin`, `toAdjoin_monic`, `algebraMap_comp_evalAtJGen` | `FLTForHuman/ModularCurve/Defs/Fields.lean` | ported |
| `PhiGenDescends.intCoeffs`, `aeval_jq_intCoeffs_descent` | `FLTForHuman/ModularCurve/PhiGenIntegrality.lean` | T9 done |
| `mem_adjoin_jq_of_phiGenDescends` | `FLTForHuman/ModularForms/PhiGenDescends.lean` | T8 done |
| the `TPoleOrderLE` prelude (`mono`/`zero`/`one`/`neg`/`add`/`mul`/`qTwist`/`qExpand`, `conjPoleBound`, `tPoleOrderLE_conj*`, `tPoleOrderLE_coeff_X_sub_C`/`_mul`/`_prod`, `tPoleOrderLE_phiProd_coeff`, `jSimplePole_jqK`, `tPoleOrderLE_coeffEmb_iff`, `tPoleOrderLE_of_qExpand`), `phiProd_conj_coeff_zero_lead`, `phiProd_conj_coeff_eq_zero_of_le` | `Defs/PhiGen.lean` (+202 lines) + `FLTForHuman/ModularCurve/PhiGenPoleBounds.lean` (310 lines) | **T10, in flight** — both files were written at the time of this look-ahead |
| `exists_phiGenDescends` (a) | — | **this topic (T11)** |
| `one_le_coeff_jq`, `phiIrreducible_of_splits`, `evalSymm_of_splits`, `transposeToAdjoin_monic_of_qExpansion` (e) | — | **T12, not scheduled** |
| `splits_of_prime`, `splits_prime_at_slot` (f) | — | **T13, not scheduled** |

## 3. The mathlib-first audit

Audited against `v4.34.0`. **This is a glue topic in the T7/T9 sense**: mathlib
supplies the coefficient, polynomial and field-theory primitives, not the FLT
statements.

| pin piece | mathlib `v4.34.0` | verdict |
|---|---|---|
| the 328 block's `c_top`/`c_eq_zero` | `phiProd_monic`, `phiProd_natDegree` (already ported); `Function.Injective` of the level substitution from `coeffEmb_injective` + `qExpand_injective` | port (short) |
| `poleOrderLE` | T10's `tPoleOrderLE_phiProd_coeff` + `tPoleOrderLE_coeffEmb_iff` + `tPoleOrderLE_of_qExpand`; `HahnSeries.coeff` algebra | import T10 |
| `sum_mul_jqN_pow_eq_zero` | `Polynomial.eval_eq_sum_range`, `phiProd_eval_conj` (ported), `conj_zero` | port (short) |
| `evalAtJ_injective` | none (this is `jq` transcendence; T8/T12 have private copies) | port once, public |
| `natDegree_le_of_poleOrderLE_aeval`, `exists_aeval_jq_eq_of_mem_adjoin` | `Algebra.adjoin_singleton_eq_range_aeval`; the `q^{-d}`-coefficient reading | port |
| `PhiGenDescends.exists_intPoly` | `Polynomial.lifts`, `Polynomial.lifts_iff_coeff_lifts`, `natDegree_map_eq_of_injective`; T9's `aeval_jq_intCoeffs_descent` | port (glue) |
| `exists_modularPolynomialData_coeff_eq` | `Polynomial.C_mul_X_pow`, `coeff_sum_C_mul_X_pow`, `eval₂_eq_sum_range'`, `natDegree_sum_le_of_forall_le`; `dedekindPsi_prime` | port |
| `splits_of_coeff_evalAtJ_eq` | `Polynomial.ext`, `coeff_map` + `hc`/`hcoeff` | trivial |
| `evalSymm_of_coeff_evalAtJ_eq` | none; **depends on T12's 895 block** (`transposeToAdjoin_monic_of_qExpansion`, `evalSymm_of_splits`) | defer (§4) |
| `exists_phiIrreducible_evalSymm` | `CyclotomicField.isCyclotomicExtension`, `IsCyclotomicExtension.exists_isPrimitiveRoot`, `isGalois`, `finiteDimensional`; assembles (a)–(e) | defer (§4) |
| `finrank_adjoin_jqN_eq`, `eq_of_prime` | `IntermediateField.adjoin.finrank`, `minpoly.eq_of_irreducible_of_monic`, `minpoly.dvd`, `Polynomial.eq_of_monic_of_dvd_of_natDegree_le`, `Polynomial.map_injective` | defer (§4) |

**Headline.** No public mathlib lemma replaces any export. The audit's value is
again negative: do not hunt for analogues. The one *positive* ingredient is
`IsCyclotomicExtension.exists_isPrimitiveRoot`, which is how the pin avoids
assuming a primitive root in `exists_phiIrreducible_evalSymm`; it is genuine
mathlib and should be used as the pin does.

## 4. The dependency facts, and the division they force

The pin's import graph is decisive. Transcribing it:

- the 328-block files import only `Definitions/` plus `coeffMap_qExpand` and
  `coeffEmb_injective` — **self-contained**, upstream of everything;
- `exists_modularPolynomialData_coeff_eq` imports the 328 block, T9's
  `intCoeffs`/`aeval_jq_intCoeffs_descent` and `dedekindPsi_prime` — **core**,
  available once T10 lands;
- `evalSymm_of_coeff_evalAtJ_eq` imports T10's two pole-bound statements **and
  T12's 895 block** (`transposeToAdjoin_monic_of_qExpansion`, `evalSymm_of_splits`);
- `exists_phiIrreducible_evalSymm` imports **this topic's `exists_phiGenDescends`**,
  T9, T8, the assembly, T12's `phiIrreducible_of_splits` and the symmetry lemma;
- `finrank_adjoin_jqN_eq_of_prime` imports `exists_phiIrreducible_evalSymm`;
- `eq_of_prime` imports `finrank_adjoin_jqN_eq_of_prime`,
  `exists_phiIrreducible_evalSymm` and `evalAtJ_injective`.

So the blueprint's T11 (the 328 block plus the 502-line (d) bucket) is not
executable as one unit: its second half is downstream of pieces the sequence
numbers *after* it. That fixes a partial order; it does not by itself fix the
topic boundaries. The corrected prerequisites are:

| declaration | pin | prerequisites |
|---|---|---|
| the 328 block | 328 (×7 copies, 84 distinctive) | Layer 0b, T10's prelude |
| (a) `exists_phiGenDescends` | 315 | Layer 0b, `coeffMap_qExpand` |
| (d) `exists_modularPolynomialData_coeff_eq`, `splits_of_coeff_evalAtJ_eq` | 191 | the 328 block, T9, T10 |
| (e) the 895 block | 894 (×3) | `one_le_coeff_jq` |
| `one_le_coeff_jq` | 386 | Layer 0b |
| `evalSymm_of_coeff_evalAtJ_eq` | 124 | T10's exports, the assembly, the 895 block |
| `exists_phiIrreducible_evalSymm` | 62 | (a), T8, T9, the assembly, the 895 block, the symmetry lemma |
| `finrank_adjoin_jqN_eq_of_prime` | 52 | `exists_phiIrreducible_evalSymm` |
| `eq_of_prime` | 73 | `finrank`, `exists_phiIrreducible_evalSymm`, `evalAtJ_injective` |
| (f) `splits_of_prime`, `splits_prime_at_slot` | 353 + 288 | everything |

This is also why PORTING-PhiGen §6 Option 1's "circularity" worry is misplaced:
the assembly gets the degree `ℓ+1` from the explicit product (`c_top`,
`c_eq_zero`), not from `finrank`, and `finrank` gets it from the *other*,
irreducible datum. There is no cycle; there is a missing prerequisite.

### 4.1 The division: construction, properties, consequence

Three topics remain. The cut is by mathematical object, not by dependency wave or
by what could run in parallel: each topic builds one object, and each proof is
written once.

| topic | object | content | prereq |
|---|---|---|---|
| **T11** | the construction — from the conjugate product to a datum | (a) `exists_phiGenDescends`; the 328 block; `exists_modularPolynomialData_coeff_eq`, `splits_of_coeff_evalAtJ_eq` | T10 (done) |
| **T12** | the properties — irreducibility and symmetry | `one_le_coeff_jq`; the 895 block (`phiIrreducible_of_splits`, `transposeToAdjoin_monic_of_qExpansion`, `evalSymm_of_splits`, plus the hidden `aeval_jq_ne_jqN`/`jqN_not_mem_adjoin_jq`); `evalSymm_of_coeff_evalAtJ_eq`; `exists_phiIrreducible_evalSymm` | T11 |
| **T13** | the consequence — uniqueness and the splitting | `finrank_adjoin_jqN_eq_of_prime`, `ModularPolynomialData.eq_of_prime`; `splits_of_prime`, `splits_prime_at_slot` | T12 |

Why this is the cohesion-maximizing cut:

- **The 895 block stays in one topic.** It is a single shared development
  shipped three times; its three exported nodes and the hidden non-membership
  results come from the same machinery. Cutting (e) by consumer would re-copy
  it — the opposite of the goal.
- **(a) joins the construction.** It produces `PhiGenDescends`, the hypothesis
  the whole 328/assembly chain consumes; proving it beside its consumers avoids
  a separate interface topic.
- **(d)'s symmetry and existence join the properties.** `exists_phiIrreducible_evalSymm`
  is "the assembled datum is irreducible and symmetric"; it consumes both the
  assembly and the 895 block, so it belongs with the block, not with the
  construction.
- **(f) is the consequence**, and `eq_of_prime` is the uniqueness it consumes;
  they are one topic.

An earlier version of this section cut the same declarations by dependency wave
and justified the cut by parallelism. That rationale is withdrawn; the waves are
kept only as the build order, and here they coincide with the mathematical order
(construction → properties → consequence). The alternative — put (e) first
(T11 = the 895 block, T12 = the datum whole) — also respects the partial order;
the cut above is preferred because T11 then starts from the object the cone is
about and (e) reads as a property of what T11 built.

### 4.2 Redundancy removal and mathlib reuse

The standing rule is: prefer the math-motivated route, reuse mathlib, write each
proof once. Concretely for T11:

1. **`evalAtJ_injective` via `transcendental_jq`.** The port already has, in
   `Defs/Jq.lean`, `transcendental_jq : Transcendental ℚ jq`, and mathlib has
   `transcendental_iff_injective : Transcendental R x ↔ Function.Injective (Polynomial.aeval x)`.
   So the pin's private 19-line `aeval_jq_eq_zero` and its coefficient argument
   are redundant: `evalAtJ_injective` follows from injectivity of `aeval jq` on
   `ℚ[X]` composed with `Polynomial.map_injective (Int.castRingHom ℚ) Int.cast_injective`.
   Keep the 6-line `evalAtJ_eq_aeval_map` bridge; drop the rest.
2. **`coeff_aeval_jq_neg` is T9's `Defs/Jq.lean` lemma.** Drop the assembly
   pin's private copy and import it.
3. **The prelude is T10's.** T11 imports it (including `TPoleOrderLE.add`); no
   private copies.
4. **`evalAtJ_injective` is written once, in T11**, and T12's 895 block imports
   it instead of carrying its private copy.
5. **The `attribute [-simp]` pragma** in several pin files is toolchain
   machinery, not mathematics; do not port it.
6. **Route-check first.** The `evalAtJ_injective` substitution is the one place
   where mathlib's `Polynomial.aeval` statement may need the `evalAtJ_eq_aeval_map`
   bridge to line up; spike it in the gitignored `Scratch.lean` under
   `timeout 60` before committing to it. If it does not close quickly, the pin's
   coefficient proof is the fallback — but that is the redundant route and the
   log should say why.

## 5. Verification and the wire test

1. **`#print axioms`** on every public declaration: only
   `propext, Classical.choice, Quot.sound`.
2. **Statement checker.** Add to `SOURCES` eight wrappers: the five block
   wrappers
   (`Thm_ModularCurve_PhiGen_PhiGenDescends_{c_top,c_eq_zero,poleOrderLE,sum_mul_jqN_pow_eq_zero}`,
   `Thm_ModularCurve_PhiGen_evalAtJ_injective`), (a)'s
   `Thm_ModularCurve_PhiGen_exists_phiGenDescends.lean`, and the
   `exists_modularPolynomialData_coeff_eq` and `splits_of_coeff_evalAtJ_eq`
   wrappers. `dedekindPsi_prime`, `coeff_aeval_jq_neg`, `transcendental_jq` and
   `aeval_jq_intCoeffs_descent` are already `SOURCES` entries. T10 left the count
   at **205**; T11 raises it to **213**, 0 mismatched.
3. **`PORT_FILES`** gains T11's three modules.
4. **The wire test — the full construction.** T11 includes (a), so the wire is
   end-to-end and concrete rather than a mere binding. Take
   `K = CyclotomicField ℓ ℚ` and its primitive root (as the pin's
   `exists_phiIrreducible_evalSymm` does), or `ℂ` via
   `Complex.isPrimitiveRoot_exp`; then
   - `hc := PhiGen.exists_phiGenDescends ℓ ζ hζ`;
   - `hint := fun k => hc.intCoeffs hζ.pow_eq_one k` (T9);
   - `hmem := fun k => mem_adjoin_jq_of_phiGenDescends ℓ ζ hζ c hc k` (T8);
   - `data` from `exists_modularPolynomialData_coeff_eq hc hint hmem`, with
     `evalAtJ (data.Φ.coeff k) = c k`.

   That exercises (a) + (b) + (c) + (d) in one concrete instance. Separately
   `evalAtJ_injective` is unconditional: `evalAtJ X ≠ evalAtJ (X * X)` by
   injectivity and the coefficient of `X` in `ℤ[X]`.
5. **Consumer.** Add a new **Zone I** for T11 — T10's work order took Zone H; the
   file is `spec/ModularCurveConsumer.lean`, run by hand, 0 errors.
6. **The `attribute [-simp]` pragma.** Several T11 pin files open with the
   doc-site toolchain's mechanical `attribute [-simp] ModularForm.heckeU_zero …`
   line. It is not mathematics (T8's module header records the finding). Do not
   port it; the port's simp set is clean.

## 6. Dedup

- The 328-block *body* is shipped in seven files (`7 × 328 = 2,296` pin lines);
  its distinctive content is **84 lines** (the ~170-line prelude is T10's and
  moves to `Defs/PhiGen.lean`). Writing both once is the largest single
  removal in the remaining cone.
- The prelude itself is carried by **twelve** pin files, not six. T10's work
  order should be read as "≈170 lines × 12 carriers"; the saving there is T10's
  to report, but T11's §2 is where the correction is recorded.
- `evalAtJ_injective` also appears **privately** in T12's 895-line block (with
  `evalAtJGen_injective`), so T11's public export is T12's entry point.
  `coeff_coeffEmb_jq_of_lt` is just `coeffEmb_coeff` + `coeff_jq_of_lt`; check
  before porting it. `coeff_aeval_jq_neg` (private in the assembly pin) is
  already public from T9.
- **The mathlib route for `evalAtJ_injective`** (§4.2) removes the pin's private
  `aeval_jq_eq_zero` and its 19-line coefficient argument; `transcendental_jq`
  is already public, so ~25 pin lines become a 6-line bridge plus one mathlib
  call.
- **Do not re-declare the prelude.** With it public in `Defs/PhiGen.lean`, T11
  imports `tPoleOrderLE_phiProd_coeff`, `tPoleOrderLE_coeffEmb_iff`,
  `tPoleOrderLE_of_qExpand`, `jSimplePole_jqK`; it keeps none of the pin's
  private copies. T10's in-flight promotion states `tPoleOrderLE_phiProd_coeff`
  at bound `ℓ*ℓ + ℓ`, exactly as the pin (checked in `Defs/PhiGen.lean` while
  T10 was being written), so the block's `hW3.mono (le_of_eq (by ring))` step
  carries over unchanged. T10 also adds `TPoleOrderLE.add`, which the 328-file
  prelude lacked.

## 7. Module split (recommended)

| module | public surface | pin |
|---|---|---|
| `FLTForHuman/ModularCurve/PhiGenDescent.lean` | `PhiGen.exists_phiGenDescends` | (a), 315 |
| `FLTForHuman/ModularCurve/PhiGenDescendsStructure.lean` | `PhiGenDescends.c_top`, `.c_eq_zero`, `.poleOrderLE`, `.sum_mul_jqN_pow_eq_zero`, `evalAtJ_injective` | the 328 block |
| `FLTForHuman/ModularCurve/ModularPolynomialAssembly.lean` | `exists_modularPolynomialData_coeff_eq`, `splits_of_coeff_evalAtJ_eq` | the 191-line (d) file |
| *(T12)* `FLTForHuman/ModularCurve/ModularPolynomialIrreducible.lean` | `one_le_coeff_jq`, the 895 block's exports, `evalSymm_of_coeff_evalAtJ_eq`, `exists_phiIrreducible_evalSymm` | (e) + 311 |
| *(T13)* `FLTForHuman/ModularCurve/ModularPolynomialUniqueness.lean` | `finrank_adjoin_jqN_eq_of_prime`, `ModularPolynomialData.eq_of_prime`, `splits_of_prime`, `splits_prime_at_slot` | (f) + 125 |

The names are suggestions; what matters is §4.1's boundaries. T11's three modules
import T10's `PhiGenPoleBounds.lean`, T9's module and T8's module, and the
structure module exports `evalAtJ_injective`/`coeffEmb_qExpand_injective` for T12.

## 8. Budget

Pin content for **T11** is (a)'s `315`, the block's `84` distinctive lines (the
328-line file is shipped seven times, `2,296` pin lines, but its ~170-line
prelude is T10's) and `191` for the assembly file — about `590` deduplicated pin
lines. Lines are not effort (T8/T9, and the standing note), so the budget is the
two places with shape risk: the variable convention of the assembled `Φ` and
(a)'s twist/Galois invariance. T12 (`386 + 894 + 124 + 62`) and T13
(`52 + 73 + 353 + 288`) are single-object topics; a multi-round budget is
acceptable if that is what the mathematics needs.

**Stop early on:** `exists_modularPolynomialData_coeff_eq`'s `Φ.coeff k`
convention not matching the port's `ModularPolynomialData` (the pin builds `Φ`
in the second variable; the port's `eval_eq_zero` evaluates the second variable
at `jqN`); `Polynomial.lifts` API drift; `tPoleOrderLE_of_qExpand`'s direction
differing from T10's export; the (e) block's `transposeToAdjoin_monic_of_qExpansion`
taking three coefficient hypotheses whose spelling is `PoleOrderLE` vs the port's
`TPoleOrderLE`; or `IsCyclotomicExtension.exists_isPrimitiveRoot` needing
instance management the port's `autoImplicit false` blocks.

**`evalAtJ_injective`: try the mathlib route first.** Per §4.2, use
`transcendental_jq` + mathlib's `transcendental_iff_injective` +
`Polynomial.map_injective`; spike it in the gitignored `Scratch.lean` under
`timeout 60` before adopting it. The pin's 19-line coefficient argument
(`aeval_jq_eq_zero`) is the fallback, and it is the redundant route — record why
in the log if it is used.

## 9. Definition of done (T11)

- [x] `FLTForHuman/ModularCurve/PhiGenDescent.lean`: `PhiGen.exists_phiGenDescends`
      public and verbatim from its wrapper. **339 lines, 1 public + 18 `private`.**
- [x] `FLTForHuman/ModularCurve/PhiGenDescendsStructure.lean`: the five exports
      public and verbatim; `evalAtJ_eq_aeval_map` and `coeffEmb_qExpand_injective`
      kept `private`; `evalAtJ_injective` by the mathlib route of §4.2 (it closed
      first try). **161 lines, 5 public + 2 `private`.**
- [x] `FLTForHuman/ModularCurve/ModularPolynomialAssembly.lean`:
      `exists_modularPolynomialData_coeff_eq` and `splits_of_coeff_evalAtJ_eq`
      public and verbatim. **201 lines, 2 public + 5 `private`.**
- [x] `lake build` green, 0 warnings, no `sorry` (2594 jobs).
- [x] `#print axioms` clean on all eight public declarations.
- [x] `spec/check_flt_statements.py`: the eight wrappers in `SOURCES`, 0
      mismatched; `PORT_FILES` gains the three modules. **205 → 213, 0 missing.**
- [x] the end-to-end wire item from §5.4 recorded and green in Zone I:
      `K = CyclotomicField ℓ ℚ`, `(a)` + `(b)` + `(c)` + `(d)` in one example,
      plus the unconditional `evalAtJ_injective` binding.
- [x] `PORTING-PhiGen.md` §5 marks T10 and T11 done and names T12; §6's (b) row is
      closed with T10's measurement and the (d) row names T11/T12/T13; the log
      gains T11's cost; README module table gains the three modules.
- [x] report in the §10 shape.

## 10. Reporting back

1. **The dedup and the mathlib reuse.** The 328-block body is shipped in seven
   pin files (2,296 lines); its distinctive content is 84 lines and the ~170-line
   prelude stays T10's, so the port writes the block once at 161 lines including a
   ~35-line header. T12 imports `evalAtJ_injective` (public in
   `PhiGenDescendsStructure`) rather than carrying the 895 block's private copy;
   `coeff_coeffEmb_jq_of_lt` was not ported (T10's block already covers it). **The
   `transcendental_jq` route for `evalAtJ_injective` closed on the first try**, so
   the pin's private 19-line `aeval_jq_eq_zero` is not ported; the port's own
   public `aeval_jq_eq_zero` (the `Thm_ModularCurve_aeval_jq_eq_zero` interface)
   is untouched. The prelude-carrier correction (twelve, not six) is recorded in
   T10's log §10.
2. **The cost** — **1 goal round**, 8 public + 25 `private` declarations,
   **701 lines** (339 + 161 + 201), port/pin ratio **701/590 ≈ 1.19** against the
   deduplicated pin (a's 315 + the block's 84 distinctive + the assembly's 191).
3. **The division.** Yes: (a) + the 328 block + the assembly stayed one
   construction topic, and T12/T13 start from the §4.1 properties/consequence cut.
   The dependency fact of §4 was confirmed — the 328 block and the assembly are
   upstream of (e), so they could not have waited for it.
4. **The variable convention.** The pin builds `Φ = ∑_{k ≤ ℓ+1} C (Q k) * X ^ k`
   in the *outer* variable (`Polynomial.C (Q k) : Polynomial (Polynomial ℤ)` with
   `X` the outer generator), i.e. `Φ.coeff k = Q k` is the `Y^k` coefficient, and
   the port's `ModularPolynomialData.eval_eq_zero` (`Φ.eval₂ evalAtJ (jqN ℓ) = 0`)
   reads exactly that outer variable. No rebinding was needed: the `hΦcoeff :
   evalAtJ (Φ.coeff k) = c k` convention and the `eval₂_eq_sum_range'` step
   carried over verbatim.

## 11. Where this sits

The remaining cone is the three-object division of §4.1: **T11** the
construction (this topic), **T12** the properties (irreducibility and symmetry),
**T13** the consequence (uniqueness and the splitting). T10 is done, so T11
starts immediately; T12 and T13 follow in that order.

Sizes are the deduplicated pin lines from
[PORTING-PhiGen.md](../../PORTING-PhiGen.md) §6; T8 and T9 both showed they are
not effort, and the division is by mathematical object rather than by line count.
