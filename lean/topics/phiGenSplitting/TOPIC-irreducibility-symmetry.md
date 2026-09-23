# Topic 12: the properties — irreducibility and symmetry

**Status: done (2026-09-22), one goal round — the cone's datum has its
properties.** Three modules: `FLTForHuman/ModularCurve/JqCoeffPositivity.lean`
(`one_le_coeff_jq`), `ModularPolynomialIrreducible.lean` (the 895 block written
once) and `ModularPolynomialProperties.lean` (`evalSymm_of_coeff_evalAtJ_eq`,
`exists_phiIrreducible_evalSymm`), green with 0 warnings and no `sorry`. The 895
block is shipped in **five** pin files (not three — §2's correction is recorded);
the `evalAtJ_eq_aeval_map` promotion landed and T11 rebuilt green; the end-to-end
wire test is the first **unconditional** capstone. A post-close pass
(2026-09-23) removed five redundant private declarations and routed the
`swapBivar`/`qEmbedT`/`ev` helpers through mathlib, public statements untouched
(§3.2); the block module is now **1023 lines**. The measured cost and the
answers to the §10 questions are in
[logs/phiGen-port.md](../../logs/phiGen-port.md) §12. This file is kept as the
executed plan. The plan is [PORTING-PhiGen.md](../PORTING-PhiGen.md); the
mathematics is
[math/010](../../../math/010-function-field-generation.md) §3 and
[base/006](../../../base/006-the-modular-equation.md) §2 and §6 step 3. **T13,
the consequence (uniqueness and the splitting), is next and is the cone's last
topic.**

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

1. [PORTING-PhiGen.md](../PORTING-PhiGen.md) §3(e) and §5–§6;
2. [base/006 §3 and §6 step 3](../../../base/006-the-modular-equation.md) — the
   splitting, the cover, and why exactly two invariances;
3. [math/010 §3](../../../math/010-function-field-generation.md) — the slot
   description and the modular polynomial;
4. [TOPIC-datum-assembly.md](TOPIC-datum-assembly.md) (T11, the predecessor) and
   [logs/phiGen-port.md](../../logs/phiGen-port.md) §11 — T11's interfaces and the
   dedup/reuse findings it leaves;
5. [porting-playbook.md](../../porting-playbook.md) §2 (deduplicate at the
   source), §3.9 and §3.11.

## 1. The mathematics in one page

Three facts about the level-`ℓ` modular polynomial, all proved from the conjugate
product and one coefficient-positivity input.

### 1.1 The coefficients of `j` are positive

`one_le_coeff_jq : ∀ n, (1 : ℚ) ≤ jq.coeff (n : ℤ)` — every regular coefficient of
`j(q) = q^{-1} + 744 + 196884q + \cdots` is at least `1`. The route is the eta
product, not analysis:

$$j(q) = q^{-1}\\,\mathrm{jNum}(q),\qquad \mathrm{jNum} = E_4^3 \cdot \Delta^{-1}
= E_4^3 \cdot \prod_{d\ge 1}\bigl(1 - q^d\bigr)^{-24}.$$

`E₄³` has nonnegative coefficients (its coefficients are `240·σ₃`-sums, up to the
constant `1`), and `Δ^{-1}` has coefficients at least `1`: the coefficient of
`q^n` counts `24`-coloured partitions of `n`, and the all-`1`s partition
contributes `1`. Multiplying a power series with constant term `1` and
nonnegative coefficients by one with all coefficients `≥ 1` keeps all
coefficients `≥ 1` (the `(0,n)` term of the Cauchy sum), so
`jNum.coeff (n+1) ≥ 1`, and `jq.coeff n = jNum.coeff (n+1)`.

The pin proves this over `PowerSeries ℤ` with a finite-truncation device: the
geometric series `geomSeries d = ∑_{d \mid k} q^k` inverts `1 - q^d`, a finite
partial product of the eta factors agrees with `η` below the truncation order,
and a truncation-stable inverse comparison transports the bound to `Δ^{-1}`.
Mathlib supplies the pieces of a cleaner route: `PowerSeries.coeff_mul_prod_one_sub_of_lt_order`
(a finite eta product agrees with `η` below its order),
`PowerSeries.coeff_prod_one_sub_X_pow_eventually_eq`, and the
`PowerSeries.expand`/`mk_one_mul_one_sub_eq_one` pair for the geometric factor.
§3.1.9 records the substitution and the two facts that have no mathlib
replacement (`coeff_inv_congr`, the truncation-stable inverse comparison).

### 1.2 The datum is irreducible

For a datum `data : ModularPolynomialData ℓ` whose coefficients evaluate to the
descended family, `PhiIrreducible data` says `data.toAdjoin` is irreducible in
`ℚ⟮jq⟯[Y]`. Its `ℓ+1` roots are the conjugates
`j(q^{ℓ²}), j(ζ q), …, j(ζ^{ℓ-1} q)`; the polynomial is monic of degree
`ℓ+1 = ψ(ℓ)`. Irreducibility is proved over the polynomial ring `ℚ[j(q)]` (then
transported to its fraction field `ℚ(j)` by Gauss), by the degree bookkeeping of
any factorisation `Φ = A · B` over `adjoinJq`:

- since `Φ` is monic, `A` and `B` have unit leading coefficients and
  `deg A + deg B = ℓ+1`;
- evaluating at `coeffEmb K jq` shows one of `A(jq)`, `B(jq)` vanishes, because
  `jq` is a root (`eval_swap_eq_zero_of_splits`/`phiProd_eval_conj`);
- a nonzero `D ∈ ℚ[j(q)]` with `D(jq) = 0` has degree `≥ ℓ` — the conjugates are
  distinct (`conj_injective`) and mathlib's
  `Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero` kills a lower-degree
  polynomial with that many roots;
- so the other factor has degree `≤ 1`; and it is a unit, because a degree-`1`
  factor would have a root in `ℚ[j(q)]`, and `j(q^ℓ) ∉ ℚ[j(q)]`.

The last is `jqN_not_mem_adjoin_jq`, and it is where positivity enters:
`aeval_jq_ne_jqN` shows no `P ∈ ℚ[X]` has `P(jq) = j(q^ℓ)`. If one did, the
arithmetic twist `ζ ↦ ζ^b` and the sum over the `ℓ` finite conjugates would make
a rational constant whose `q^{-ℓ}` coefficient is `ℓ · jq.coeff ℓ ≠ 0` on one
side and `0` on the other; `one_le_coeff_jq` at `n = ℓ` supplies the nonvanishing.
(So although the exported positivity statement is for all `n`, the consumers use
it only at `n = ℓ`; see §3.1.)

### 1.3 The datum is symmetric

`EvalSymm Φ` is the evaluated form of `Φ(X,Y) = Φ(Y,X)`. The transpose
`swapBivar Φ` is again monic of degree `ψ(ℓ)` and annihilates `jqN ℓ`; since
`Φ.toAdjoin = minpoly ℚ⟮jq⟯ (jqN ℓ)` (irreducibility), the transpose *is* `Φ`.
Three coefficient-level hypotheses drive the transpose degree count, and they are
exactly the pole bounds T10/T11 supply for the descended family:

- `h0top`: the leading `q^{-ψ(ℓ)}` coefficient of `evalAtJ (Φ.coeff 0)` is `1`;
- `h0le`: all deeper coefficients of `evalAtJ (Φ.coeff 0)` vanish;
- `hk`: for `k ≠ 0`, all coefficients of `evalAtJ (Φ.coeff k)` from `q^{-ψ(ℓ)}`
  down vanish.

`ModularPolynomialData.transposeToAdjoin_monic_of_qExpansion` turns those three
into `(swapBivar Φ).map evalAtJGen` being monic of `natDegree = ψ(ℓ)`; the
symmetry chain then runs `swapBivar Φ = Φ` → `EvalSymm Φ`. The datum-level
statement `evalSymm_of_coeff_evalAtJ_eq` derives `h0top`/`h0le`/`hk` from T10's
`phiProd_conj_coeff_zero_lead` and `phiProd_conj_coeff_eq_zero_of_le`.

### 1.4 Existence

`exists_phiIrreducible_evalSymm ℓ` is the cone's own construction of an
irreducible symmetric datum. It chooses a primitive `ℓ`-th root in
`CyclotomicField ℓ ℚ` (mathlib supplies one), then runs the whole T8–T12 chain:
(a) descent (T11) gives `c`; (b) T9 gives `IntCoeffs`; (c) T8 gives membership in
`ℚ[jq]`; T11's assembly gives `data` with `evalAtJ (data.Φ.coeff k) = c k`; T11's
`splits_of_coeff_evalAtJ_eq` gives the splitting identity; and this topic's
`phiIrreducible_of_splits` and `evalSymm_of_coeff_evalAtJ_eq` give the two
properties. It is a join, not new mathematics.

## 2. The scouted inventory

| pin file | lines | content |
|---|---|---|
| `S_ModularCurve_one_le_coeff_jq.lean` | 386 | `one_le_coeff_jq` |
| `S_ModularCurve_PhiGen_evalSymm_of_splits.lean` | 895 | the shared block, exporting `evalSymm_of_splits` |
| `S_ModularCurve_PhiGen_phiIrreducible_of_splits.lean` | 895 | the same block, exporting `phiIrreducible_of_splits` |
| `S_ModularCurve_ModularPolynomialData_transposeToAdjoin_monic_of_qExpansion.lean` | 894 | the same block, exporting `transposeToAdjoin_monic_of_qExpansion` |
| `S_ModularCurve_swapBivar_monic_of_coeff_bounds.lean` | 894 | the same block, exporting `swapBivar_monic_of_coeff_bounds` |
| `S_ModularCurve_ModularPolynomialData_evalSymm_of_irreducible.lean` | 894 | the same block, exporting `evalSymm_of_irreducible` |
| `S_ModularCurve_PhiGen_evalSymm_of_coeff_evalAtJ_eq.lean` | 124 | `evalSymm_of_coeff_evalAtJ_eq` |
| `S_ModularCurve_exists_phiIrreducible_evalSymm.lean` | 62 | `exists_phiIrreducible_evalSymm` |
| `S_ModularCurve_PhiGen_conj_injective.lean` | 92 | `conj_injective` (also private in the block) |
| `S_ModularCurve_evalAtJGen_injective.lean` | 11 | `evalAtJGen_injective` (also private in the block) |
| `S_ModularCurve_swapBivar_eq_of_evalSymm.lean` | 95 | `swapBivar_eq_of_evalSymm` (the converse direction) |

**The block ships in five files, not three.** `PORTING-PhiGen.md` §2's dedup
table records the 895-line block as ×3 (its three graph nodes); the two hidden
exports `swapBivar_monic_of_coeff_bounds` and
`ModularPolynomialData.evalSymm_of_irreducible` each have their own ~894-line
copy as well. Deduplicated the block is **one ~895-line development**, and the
port writes it once; the ×5 pin structure costs `5 × 895 ≈ 4,475` lines. This is
the same undercount pattern as T10's prelude (logged as six, carried by twelve);
T12 should record the correction.

### 2.1 The public statements (verbatim from their wrappers)

```lean
theorem ModularCurve.one_le_coeff_jq (n : ℕ) : (1 : ℚ) ≤ jq.coeff (n : ℤ)

theorem ModularCurve.PhiGen.phiIrreducible_of_splits {K : Type*} [Field K] [Algebra ℚ K]
    (ℓ : ℕ) [hℓ : Fact (Nat.Prime ℓ)] (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) ℓ)
    (data : ModularPolynomialData ℓ)
    (hsplit : data.Φ.map (((coeffEmb K).comp (qExpand ℚ ℓ)).comp evalAtJ) = phiProd ℓ (conj ℓ ζ)) :
    PhiIrreducible data

theorem ModularCurve.PhiGen.evalSymm_of_splits {K : Type*} [Field K] [Algebra ℚ K]
    (ℓ : ℕ) [hℓ : Fact (Nat.Prime ℓ)] (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) ℓ)
    (data : ModularPolynomialData ℓ)
    (hsplit : data.Φ.map (((coeffEmb K).comp (qExpand ℚ ℓ)).comp evalAtJ) = phiProd ℓ (conj ℓ ζ))
    (hTmonic : ((swapBivar data.Φ).map evalAtJGen).Monic)
    (hTdeg : ((swapBivar data.Φ).map evalAtJGen).natDegree ≤ dedekindPsi ℓ) :
    EvalSymm data.Φ

theorem ModularCurve.ModularPolynomialData.transposeToAdjoin_monic_of_qExpansion
    {N : ℕ} [NeZero N] (data : ModularPolynomialData N)
    (h0top : (evalAtJ (data.Φ.coeff 0)).coeff (-(dedekindPsi N : ℤ)) = 1)
    (h0le : ∀ m : ℕ, dedekindPsi N < m → (evalAtJ (data.Φ.coeff 0)).coeff (-(m : ℤ)) = 0)
    (hk : ∀ k, k ≠ 0 → ∀ m : ℕ, dedekindPsi N ≤ m →
      (evalAtJ (data.Φ.coeff k)).coeff (-(m : ℤ)) = 0) :
    ((swapBivar data.Φ).map evalAtJGen).Monic ∧
      ((swapBivar data.Φ).map evalAtJGen).natDegree = dedekindPsi N

theorem ModularCurve.PhiGen.evalSymm_of_coeff_evalAtJ_eq {K : Type*} [Field K] [Algebra ℚ K]
    {ℓ : ℕ} [hℓ : Fact (Nat.Prime ℓ)] {ζ : Kˣ} {c : ℕ → LaurentSeries ℚ}
    (hζ : IsPrimitiveRoot (ζ : K) ℓ) (hc : PhiGenDescends ℓ ζ c)
    (data : ModularPolynomialData ℓ) (hcoeff : ∀ k, evalAtJ (data.Φ.coeff k) = c k) :
    EvalSymm data.Φ

theorem ModularCurve.exists_phiIrreducible_evalSymm (ℓ : ℕ) [hℓ : Fact (Nat.Prime ℓ)] :
    ∃ data : ModularPolynomialData ℓ, PhiIrreducible data ∧ EvalSymm data.Φ
```

The hidden results with wrappers are also public: `evalAtJGen_injective`,
`swapBivar_monic_of_coeff_bounds`,
`ModularPolynomialData.evalSymm_of_irreducible`, `swapBivar_eq_of_evalSymm`,
`conj_injective`, `ModularPolynomialData.aeval_jqN_toAdjoin`,
`ModularPolynomialData.minpoly_jqN_eq`, and the block's
`evalSymm_of_swapBivar_eq`, `eval_swap_eq_zero_of_splits`, `aeval_jq_ne_jqN`,
`jqN_not_mem_adjoin_jq`. `aeval_jq_ne_jqN` and `jqN_not_mem_adjoin_jq` have no
`Thm_` wrapper; like T7's `RealL` block they are transcribed from the `S_` file's
own public declarations.

### 2.2 The block's declaration inventory

Current (after the §3.2 cleanup); the pin's private `coeff_aeval_jq_of_lt` /
`coeff_aeval_jq_neg_natDegree` copies are gone, and the section names are the
port's.

| section | declarations |
|---|---|
| jqN lead | `coeff_jqN_self`, `coeff_jqN_of_lt` |
| injectivity | `evalAtJ_injective` (T11's, private here), `evalAtJGen_injective` (public) |
| distinctness | `coeff_coeffEmb_jq_neg_one`, `conj_zero_coeff_neg_one`, `conj_succ_coeff_neg_one`, `conj_injective` |
| scalar embedding | `ratC`, `ratC_apply`, `coeff_ratC_of_ne`, `coeffMap_jq` |
| pole order | `ne_zero_of_aeval_jq_eq_jqN`, `natDegree_eq_of_aeval_jq_eq_jqN`, `monic_of_aeval_jq_eq_jqN` (the two coefficient lemmas are now T9's public `coeff_aeval_jq_neg` and `poleOrderLE_aeval_jq`) |
| transfer / Vieta / refutation | `zeta_pow_eq_one`, `zeta_pow_zpow_eq_one`, `eval₂_ratC_jqK_of_aeval_jq_eq`, `eval₂_ratC_conj_succ_of_aeval_jq_eq`, `sum_conj_succ_eq_ratC_of_aeval_jq_eq`, `coeff_sum_conj_succ_self`, `coeff_sum_conj_succ_ne_zero`, `aeval_jq_ne_jqN_of_isPrimitiveRoot`, `aeval_jq_ne_jqN`, `jqN_not_mem_adjoin_jq` |
| fraction field | `instUFMAdjoinJq`, `algebraMap_comp_evalAtJAdj`, `ModularPolynomialData.aeval_jqN_toAdjoin`, `ModularPolynomialData.minpoly_jqN_eq` |
| embeddings | `qEmbedT`, `qEmbedT_apply`, `qEmbedT_injective`, `qEmbedT_jq`, `coeffEmb_comp_qExpand_comp_evalAtJ`, `qEmbedT_jqN`, `qTwist_comp_qEmbedT`, `conj_succ_zero`, `adjoinEmbedT`, `adjoinEmbedT_apply`, `adjoinEmbedT_injective`, `adjoinEmbedT_comp_evalAtJAdj` |
| factor analysis | `eval_map_conj_succ_eq_zero`, `le_natDegree_of_eval_map_jqK_eq_zero`, `eval_map_evalAtJAdj_ne_zero`, `isUnit_of_dvd_of_natDegree_le_one` |
| irreducibility | `irreducible_map_evalAtJAdj_of_splits`, `toAdjoin_eq_map_evalAtJAdj`, `phiIrreducible_of_splits_aux`, `phiIrreducible_of_splits` |
| swapBivar glue (§3.2) | `swapBivar_eq_swap`, `ev`, `aeval_toRingHom_eq`, `ev_eq_aevalAeval`, `ev_swap`, `ev_int`, `ev_sub` |
| transpose engine | `swapBivar_eval₂`, `evalSymm_of_swapBivar_eq`, `aeval_jqN_transposeToAdjoin`, `swapBivar_eq_of_irreducible`, `evalSymm_of_irreducible` |
| degree bookkeeping / dictionary | `swapBivar_C`, `degree_swapBivar_lt`, `swapBivar_monic_of_coeff_bounds`, `degree_lt_of_evalAtJ_coeff_eq_zero`, `monic_of_evalAtJ_coeff_eq_one`, `natDegree_le_of_evalAtJ_coeff_eq_zero`, `transposeToAdjoin_monic_of_coeff_bounds`, `transposeToAdjoin_monic_of_qExpansion` |
| symmetry from splitting | `eval_swap_eq_zero_of_splits`, `evalSymm_of_splits_aux`, `evalSymm_of_splits` |
| the converse | `swap_eq_of_evalSymm`, `swapBivar_eq_of_evalSymm` |

## 3. The mathlib-first audit

Audited against `v4.34.0`. This is the cone's largest glue topic: mathlib
supplies the polynomial/factor/field primitives, not the FLT statements.

| pin piece | mathlib `v4.34.0` | verdict |
|---|---|---|
| `one_le_coeff_jq`'s coefficient algebra | `PowerSeries.coeff_mul`, `Finset.single_le_sum`, `PowerSeries.coeff_one`; **`coeff_mul_prod_one_sub_of_lt_order`, `coeff_prod_one_sub_X_pow_eventually_eq`, `PowerSeries.expand` + `mk_one_mul_one_sub_eq_one` replace ~115 pin lines**; `coeff_inv_congr` has no analogue | reuse + port remainder; §3.1.9 |
| `coeff_jqN_self`/`coeff_jqN_of_lt` | `qExpand_coeff_mul`, `qExpand_coeff_of_not_dvd` (ported) + `coeff_jq_neg_one`/`coeff_jq_of_lt` (ported) | port ~13 lines |
| `conj_injective` | `IsPrimitiveRoot.pow_inj`, `Units.ext`, `Fin.cases`; the `q^{-1}`-coefficient separation is the port's | port (short) |
| `aeval_jq_ne_jqN`, `jqN_not_mem_adjoin_jq` | none; uses `Algebra.adjoin_mem_exists_aeval`; the twist-sum is the port's `qTwist` API | port |
| `phiIrreducible_of_splits` | `Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero`, `Polynomial.irreducible_iff_irreducible_map_fraction_map`, `Polynomial.not_isUnit_of_natDegree_pos`, `IsUnit.of_mul_eq_one` | port (glue over mathlib) |
| `swapBivar_monic_of_coeff_bounds` | `Polynomial.as_sum_support_C_mul_X_pow`, `Polynomial.degree_sum_le`, `Polynomial.degree_C_mul_X_pow_le` | port |
| `transposeToAdjoin_monic_of_qExpansion` | `Polynomial.monic_of_natDegree_le_of_coeff_eq_one`, `Polynomial.leadingCoeff_eq_zero`, `Polynomial.map_injective` | port (glue) |
| `swapBivar_eq_of_irreducible`/`evalSymm_of_irreducible` | `minpoly.dvd`, `minpoly.eq_of_irreducible_of_monic`, `Polynomial.eq_of_monic_of_dvd_of_natDegree_le` | port (glue) |
| `evalSymm_of_splits`, `evalSymm_of_coeff_evalAtJ_eq` | none; the `qTwist`/`qEmbedT`/`adjoinEmbedT` automorphism bookkeeping is the port's | port |
| `exists_phiIrreducible_evalSymm` | `CyclotomicField.isCyclotomicExtension`, `IsCyclotomicExtension.exists_isPrimitiveRoot`, `isGalois`, `finiteDimensional`; assembles T8–T12 | port (glue) |

**Headline.** No public mathlib lemma replaces any export. The two positive
ingredients are `Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero` (the
root-counting step of the irreducibility engine) and
`IsCyclotomicExtension.exists_isPrimitiveRoot` (which removes the primitive-root
hypothesis from `exists_phiIrreducible_evalSymm`). The audit's value is again
negative elsewhere.

### 3.1 Redundancy removal and mathlib reuse

T11's log left one acknowledged duplication and this topic inherits several more.
T12 should pay them down rather than carry them:

1. **Promote `evalAtJ_eq_aeval_map` to `Defs/Jq.lean`.** The six-line bridge
   `evalAtJ Q = Polynomial.aeval jq (Q.map (Int.castRingHom ℚ))` is `private` in
   **both** T11 modules (`PhiGenDescendsStructure.lean`,
   `ModularPolynomialAssembly.lean`), and the 895 block carries its own private
   `evalAtJ_eq_aeval_map_rat` copy. Promote it next to `evalAtJ`, delete the two
   private copies, and import it in T12. One lemma, three copies removed.
2. **Reuse T11's `evalAtJ_injective`.** The block's private copy is redundant;
   T11 exports it publicly precisely for this.
3. **Derive `evalAtJGen_injective` from T11's `evalAtJ_injective`.** The pin's
   `eq_of_prime` file already shows the two-line proof:
   `(h.of_comp)` after `algebraMap_comp_evalAtJGen` (`Defs/Fields.lean`), rather
   than a second coefficient argument.
4. **Reuse T9's `coeff_aeval_jq_neg`.** The block re-proves it privately; drop it.
5. **Reuse `Defs/Jq.lean`'s `aeval_jq_eq_zero`/`transcendental_jq`** rather than
   the block's private refutation of the same fact (the block uses
   `transcendental_jq` directly in its private `evalAtJ_injective`, so this is
   already the T11 route).
6. **Derive `coeff_jqN_self`/`coeff_jqN_of_lt`** from the port's
   `qExpand_coeff_mul` + `coeff_jq_neg_one` and `qExpand_coeff_of_not_dvd` +
   `coeff_jq_of_lt` — exactly what the pin's own 13 lines do; do not invent a new
   route.
7. **Reuse `Defs/Fields.lean`'s `toAdjoin`/`toAdjoin_monic`**; derive
   `aeval_jqN_toAdjoin` from `ModularPolynomialData.eval_eq_zero`.
8. **Write `conj_injective` once and export it.** The pin ships it both privately
   in the block and as its own 92-line node; the port makes it public in the block
   module and covers both.
9. **`one_le_coeff_jq`'s infrastructure has a verified mathlib shortcut (~115 of
   its 386 pin lines).** The pin hand-builds the finite eta-product truncation
   (`coeff_one_sub_X_pow_of_lt`, `coeff_prod_one_sub_X_pow_eq_coeff_one`,
   `coeff_prod_one_sub_pow_le`, `coeff_etaProd_eq_coeff_partialProd`, lines
   19–128) and the geometric series `geomSeries` (137–181). Mathlib `v4.34.0`
   already has, publicly (and the pin's own `v4.33.0` too — this is route reuse,
   not drift):
   - `PowerSeries.coeff_mul_prod_one_sub_of_lt_order` (with
     `PowerSeries.order_X_pow`) — a finite eta product agrees with `η` below the
     truncation order;
   - `PowerSeries.coeff_prod_one_sub_X_pow_eventually_eq` (import
     `Mathlib.Combinatorics.Enumerative.Pentagonal.PowerSeries`, already used by
     `JqCoefficients.lean`);
   - `PowerSeries.expand`, `coeff_expand`, `expand_X`, `expand_one_apply` (import
     `Mathlib.RingTheory.PowerSeries.Expand`) and
     `PowerSeries.mk_one_mul_one_sub_eq_one` (import `…WellKnown`) — define
     `geomSeries d := PowerSeries.expand d hd (PowerSeries.mk 1)` and get
     `(1 - X^d) * geomSeries d = 1` in one step.

   The scouting pass `#check`-verified these read-only. **Do not route through
   `Nat.Partition`/Glaisher** — there is no `1 ≤ coeff` partition lemma and that
   route is longer. Local facts with no mathlib replacement stay:
   `coeff_mul_congr`, `coeff_pow_congr` and `coeff_inv_congr` (the
   truncation-stable inverse comparison, together ~44 lines and the only brittle
   `Finset` work), plus the `one_le_coeff_partialGeom_pow` split (~20 lines).
   Estimated port: **190–250 lines against the 386-line pin (ratio ≈ 0.5–0.65)**,
   the cheapest sub-piece of T12. Keep the public statement
   `(1 : ℚ) ≤ jq.coeff (n : ℤ)` as the pin has it — it is the graph node and the
   `hpos` signature the block threads — and add the one-line corollary
   `coeff_jq_ne_zero`; the block mathematically uses only `hpos ℓ`.
10. **Do not port the `attribute [-simp]` pragma** the doc-site toolchain emits
    (T8's module header records the finding).

### 3.2 Post-close cleanup (2026-09-23)

A review of the 1070-line module against the "large file with a lot of private
theorems" smell found five private declarations that could be deleted outright
and three proofs that were re-deriving mathlib. Landed; **no public statement
changed.**

- **Two reuse misses the §3.1 list did not name.** `coeff_aeval_jq_of_lt` is
  T9's public `poleOrderLE_aeval_jq` under another name (the bodies were
  identical), and `coeff_aeval_jq_neg_natDegree` is `coeff_aeval_jq_neg P le_rfl`.
  Both deleted; the three call sites now name the `Defs` lemmas. T11's
  `ModularPolynomialAssembly.lean` already wrote `coeff_aeval_jq_neg P le_rfl`,
  so T12 was the outlier.
- **`qEmbedT_eq_coeffEmb_qExpand` deleted.** It is `Defs/Laurent.lean`'s
  `coeffEmb_qExpand` read through the definition of `qEmbedT`;
  `coeffEmb_comp_qExpand_comp_evalAtJ` now cites that lemma directly.
- **The `ev` layer collapses onto mathlib.** `ev_eq_evalEval` is
  `Polynomial.eval₂_eval₂RingHom_apply`; `ev_int` is
  `Polynomial.map_mapRingHom_evalEval`; `map_ev` is the same naturality. They
  were deleted or inlined, and `ev_int` was restated in the `A`-generic form
  `ev Φ (a : A) (b : A) = ((Φ.evalEval a b : ℤ) : A)`, so that one bridge does
  the work the old `ev_int` + `map_ev` split between them.
- **`swapBivar` is mathlib's `Bivariate.swap`, cited privately.** A new
  `SwapBivarGlue` section holds the single bridge
  `swapBivar_eq_swap : swapBivar Φ = Bivariate.swap Φ`. From it,
  `swapBivar_eval₂` (≈20 lines → 3) is `Bivariate.aevalAeval_swap` and
  `swapBivar_C` (≈12 lines → 2) is `Bivariate.swap_C`. The old `SepFibre`
  section is gone: its `ev`/`aevalAeval` glue moved up beside the bridge, and
  `swap_eq_of_evalSymm` sits in `EvalSymmSwap`. **No `Defs` API changes** —
  `swapBivar`, `swapBivar_X`, `swapBivar_C_X` and `swapInner` are untouched.

One wrinkle worth recording: `EvalSymm` evaluates with
`(Polynomial.aeval (R := ℤ) x).toRingHom`, while mathlib's `aevalAeval` is
indexed by an `Algebra ℤ` instance; at `LaurentSeries ℚ` the `powerSeriesAlgebra`
and `Ring.toIntAlgebra` structures are propositionally, not definitionally,
equal, so a direct `aevalAeval` rewrite does not unify. The `ev` layer
(`eval₂RingHom (Int.castRingHom A)`) plus `aeval_toRingHom_eq` (proved by
`RingHom.ext_int`, instance-agnostic) is the neutral ground where the two meet —
which is why `ev`/`ev_eq_aevalAeval` survive as load-bearing rather than as
redundancy.

**Net:** `ModularPolynomialIrreducible.lean` **1070 → 1023 lines**; private
declarations (theorem/def/abbrev, excluding the one `private scoped instance`)
**62 → 57**; the three T12 modules total **1670 → 1623 lines**. `lake build`
green, no `sorry`, `#print axioms` clean, statement checker 0 mismatched /
0 missing.

## 4. Dependencies and the division

T12 consumes, in order: T11's `exists_phiGenDescends`, the 328 block and
assembly; T10's prelude and two pole-bound exports; T9's
`intCoeffs`/`aeval_jq_intCoeffs_descent`; T8's
`mem_adjoin_jq_of_phiGenDescends`; and `Defs/`'s `toAdjoin`, `evalAtJGen`,
`adjoinJq`, `jAdj`, `evalAtJAdj`, `swapBivar`, `EvalSymm`, `PhiIrreducible`.

It leaves T13 the *consequence*: `finrank_adjoin_jqN_eq_of_prime`,
`ModularPolynomialData.eq_of_prime`, `splits_of_prime` and
`splits_prime_at_slot`. The interface T12 hands over is
`exists_phiIrreducible_evalSymm` (for `finrank` and `eq_of_prime`) plus T11's
`evalAtJ_injective` (for `eq_of_prime`).

The pin's `exists_phiIrreducible_evalSymm` is the join of (a)–(e), exactly as
§4.1 of the T11 work order predicted: it imports T11's `exists_phiGenDescends`,
T9's `intCoeffs`, T8's `mem_adjoin_jq_of_phiGenDescends`, T11's assembly and
`splits_of_coeff_evalAtJ_eq`, and T12's own `phiIrreducible_of_splits` and
`evalSymm_of_coeff_evalAtJ_eq`. Do not try to hoist any of it earlier.

## 5. Verification and the wire test

1. **`#print axioms`** on every public declaration: only
   `propext, Classical.choice, Quot.sound`.
2. **Statement checker.** Add the `Theorems/` wrappers for the four main exports
   and the auxiliary wrapper-bearing results. Thirteen in all:
   `Thm_ModularCurve_one_le_coeff_jq`,
   `Thm_ModularCurve_PhiGen_phiIrreducible_of_splits`,
   `Thm_ModularCurve_PhiGen_evalSymm_of_splits`,
   `Thm_ModularCurve_ModularPolynomialData_transposeToAdjoin_monic_of_qExpansion`,
   `Thm_ModularCurve_PhiGen_evalSymm_of_coeff_evalAtJ_eq`,
   `Thm_ModularCurve_exists_phiIrreducible_evalSymm`,
   `Thm_ModularCurve_evalAtJGen_injective`,
   `Thm_ModularCurve_swapBivar_monic_of_coeff_bounds`,
   `Thm_ModularCurve_ModularPolynomialData_evalSymm_of_irreducible`,
   `Thm_ModularCurve_swapBivar_eq_of_evalSymm`,
   `Thm_ModularCurve_PhiGen_conj_injective`,
   `Thm_ModularCurve_aeval_jqN_toAdjoin`,
   `Thm_ModularCurve_ModularPolynomialData_minpoly_jqN_eq` (check the exact
   wrapper filename for the last two). Add
   `P2M/Sol/S_ModularCurve_PhiGen_evalSymm_of_splits.lean` as the comparable copy
   for the transcribed non-wrapper declarations (`aeval_jq_ne_jqN`,
   `jqN_not_mem_adjoin_jq`, `evalSymm_of_swapBivar_eq`,
   `eval_swap_eq_zero_of_splits`), and
   `P2M/Sol/S_ModularCurve_one_le_coeff_jq.lean` for `coeff_jq_ne_zero`. T11 left
   the count at **213**; T12's thirteen wrappers raise it to **226**, 0
   mismatched.
3. **`PORT_FILES`** gains T12's three modules; `Defs/Jq.lean` gains the
   `evalAtJ_eq_aeval_map` promotion (its `SOURCES` coverage is already there).
4. **The wire test — the first unconditional capstone.** T12's exports need no
   unported hypothesis:
   - `exists_phiIrreducible_evalSymm ℓ` at a concrete prime (`ℓ = 2` or `3`)
     gives a genuine `data` with `PhiIrreducible data ∧ EvalSymm data.Φ`; the
     consumer can destructure it and check the interface T13 will consume.
   - `one_le_coeff_jq` is unconditional: combine it with T11's/JqCoefficients'
     `coeff_jq_zero` (or `coeff_jq_one`) for a concrete numeric instance.
   - `conj_injective` and `aeval_jq_ne_jqN` are unconditional given `ζ`/`hζ`;
     instantiate over `CyclotomicField ℓ ℚ` as in the pin.
5. **Consumer.** Add **Zone J** for T12 (T11 took Zone I); the file is
   `spec/ModularCurveConsumer.lean`, run by hand, 0 errors.
6. **Re-run T11's builds** after the `Defs/Jq.lean` promotion and the deletion of
   its two private copies; `Defs/` is shared, so check
   `PhiGenDescendsStructure`, `ModularPolynomialAssembly`, `PhiGenDescent` and
   the T9/T10 modules.

## 6. Dedup

- **The 895 block is shipped five times** (`5 × 895 ≈ 4,475` pin lines); the port
  writes it once. `PORTING-PhiGen.md` §2's "×3" is a correction to record, like
  T10's prelude count.
- `conj_injective` and `evalAtJGen_injective` each have a standalone node and a
  private copy in the block; write once and export.
- `evalAtJ_eq_aeval_map`'s three copies collapse to one `Defs/Jq.lean` lemma
  (§3.1.1).
- `evalAtJ_injective`, `coeff_aeval_jq_neg`, `aeval_jq_eq_zero`,
  `transcendental_jq` are T9/T11's; the block keeps no copies.

## 7. Module split (recommended)

| module | public surface | pin |
|---|---|---|
| `FLTForHuman/ModularCurve/JqCoeffPositivity.lean` | `one_le_coeff_jq` (and `coeff_jq_ne_zero` if useful) | 386 |
| `FLTForHuman/ModularCurve/ModularPolynomialIrreducible.lean` | `phiIrreducible_of_splits`, `evalSymm_of_splits`, `ModularPolynomialData.transposeToAdjoin_monic_of_qExpansion`, `evalAtJGen_injective`, `swapBivar_monic_of_coeff_bounds`, `ModularPolynomialData.evalSymm_of_irreducible`, `swapBivar_eq_of_evalSymm`, `conj_injective`, `aeval_jq_ne_jqN`, `jqN_not_mem_adjoin_jq`, `ModularPolynomialData.aeval_jqN_toAdjoin`, `ModularPolynomialData.minpoly_jqN_eq` | the 895 block |
| `FLTForHuman/ModularCurve/ModularPolynomialProperties.lean` | `evalSymm_of_coeff_evalAtJ_eq`, `exists_phiIrreducible_evalSymm` | 124 + 62 |
| `FLTForHuman/ModularCurve/Defs/Jq.lean` (edit) | promote `evalAtJ_eq_aeval_map` | — |

The names are suggestions. Keep the block's private helpers `private`; the public
surface is the ten declarations above plus the four T12 wrappers.

## 8. Budget and stop-early

Deduplicated pin content is `386 + 895 + 124 + 62 ≈ 1,467` lines. With the
positivity shortcut (§3.1.9, ~190–250 port lines for the 386-line pin) and the
block written once (~900–950 lines with headers), the module total is plausibly
**1,100–1,300 lines**. Lines are not effort (T8–T11), so budget **2–3 goal
rounds** and spend them on the three places with genuine shape risk:

- the `adjoinJq`/`adjoinEmbedT`/`qEmbedT`/`evalAtJAdj` subtype-coercion
  bookkeeping in the irreducibility and symmetry chains — T8's `mapGL` finding
  (`set_option backward.isDefEq.respectTransparency.types false`) is the
  precedent;
- the `IsIntegrallyClosed adjoinJq` instance: the pin makes
  `Transcendental.uniqueFactorizationMonoid_adjoin` a `private scoped instance`
  right before the Gauss step, and if T12 splits the file the instance must stay
  in scope where `Monic.irreducible_iff_irreducible_map_fraction_map` is applied
  — keep it a `local instance` in the same module;
- the Vieta step `sum_conj_succ_eq_ratC_of_aeval_jq_eq` (49 lines, the block's
  longest declaration): the pin's call to
  `Polynomial.eq_of_natDegree_lt_card_of_eval_eq` predates the v4.34 signature
  (`eval`, a `max`-degree side condition) and may need reshaping; it is the
  likeliest place for a route tweak.

**Stop early on:**
`Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero`/`eq_of_natDegree_lt_card_of_eval_eq`'s
`Fintype.card`/`eval` side conditions not matching the `Fin ℓ` index type or the
pin's `eval₂` spelling; `prod_X_sub_C_coeff_card_pred`'s coefficient shape in the
Vieta sum; `linear_combination` (used once) not closing without the pin's
`Linarith`/`LinearCombination` imports; `minpoly.dvd`'s integrality side condition
in the symmetry chain; the `CyclotomicField` instances in
`aeval_jq_ne_jqN`/`exists_phiIrreducible_evalSymm`; or the T10 pole-bound triple
`h0top`/`h0le`/`hk` matching `transposeToAdjoin_monic_of_qExpansion`'s spelling.

**Route note.** The port has `Polynomial.irreducible_of_transitive_ringAut`
(`FLTForHuman/FieldTheory/CommonRoot.lean`, from the `functionFieldGeneration`
effort), which proves irreducibility from a base-fixing automorphism cycling the
roots. It is **not** the route to take here: the automorphism cycling the finite
conjugates is the level-`ℓ` nome action (`qTwist ζ` fixes `j(q^ℓ)`, not `j(q)`),
and `PhiIrreducible data` is stated over `ℚ⟪jq⟫` in the *generic* nome, where the
finite roots need fractional powers. The pin's factor-counting argument is the
one that matches the statement; keep it.

## 9. Definition of done

- [x] `FLTForHuman/ModularCurve/JqCoeffPositivity.lean`: `one_le_coeff_jq`
      public and verbatim; `coeff_jq_zero`/`coeff_jq_one` (T11-era
      `JqCoefficients.lean`) still green. **425 lines, 2 public + 27 `private`**
      (the module also exports the one-line `coeff_jq_ne_zero`).
- [x] `FLTForHuman/ModularCurve/ModularPolynomialIrreducible.lean`: the block's
      public surface, all verbatim or transcribed from the pin's public
      declarations; private helpers `private`. **1023 lines, 15 public + 57
      `private`** (was 1070 / 62 before the §3.2 cleanup).
- [x] `FLTForHuman/ModularCurve/ModularPolynomialProperties.lean`:
      `evalSymm_of_coeff_evalAtJ_eq` and `exists_phiIrreducible_evalSymm` public
      and verbatim. **175 lines, 2 public + 4 `private`.**
- [x] `Defs/Jq.lean` gains `evalAtJ_eq_aeval_map`; the two T11 private copies and
      the block's `_rat` copy are deleted; T11 modules rebuilt green.
- [x] `lake build` green, 0 warnings, no `sorry` (3817 jobs).
- [x] `#print axioms` clean on every public declaration.
- [x] `spec/check_flt_statements.py`: thirteen wrappers added plus the two block
      `S_` files, **213 → 233, 0 mismatched, 0 missing**; `PORT_FILES` gains the
      three modules.
- [x] the wire item from §5.4 recorded, green in Zone J.
- [x] `PORTING-PhiGen.md` §5 marks T12 done and names T13; §2's dedup table
      corrects the 895 block to ×5; the log gains T12's cost and the reuse
      outcomes; README module table gains the three modules.
- [x] report in the §10 shape.

## 10. Reporting back

1. **The dedup.** The 895 block ships in **five** pin files (`5 × 895 ≈ 4,475`
   lines) — the three graph nodes plus the two hidden exports
   `swapBivar_monic_of_coeff_bounds` and `evalSymm_of_irreducible`, each with its
   own ~894-line copy; `PORTING-PhiGen.md` §2's "×3" is corrected to ×5. The port
   writes it once. `conj_injective`, `evalAtJGen_injective` and
   `evalAtJ_eq_aeval_map` each landed exactly once (the last promoted to
   `Defs/Jq.lean`, its three copies deleted, T11 rebuilt green).
2. **The cost** — **1 goal round**, 19 public + 93 `private` declarations,
   **1670 lines** (425 + 1070 + 175), port/pin ratio **1670/1467 ≈ 1.14** against
   the deduplicated pin (386 + 895 + 124 + 62). *After the §3.2 cleanup:* 19
   public + 88 `private`, **1623 lines**, ratio **1623/1467 ≈ 1.11**.
3. **`one_le_coeff_jq`'s route.** The two §3.1.9 substitutions **closed**:
   `PowerSeries.coeff_mul_prod_one_sub_of_lt_order` replaced the 40-line
   `coeff_prod_one_sub_X_pow_eq_coeff_one`, and `PowerSeries.expand` +
   `mk_one_mul_one_sub_eq_one` replaced the 45-line `geomSeries` block (including
   all its `coeff_*` lemmas, via `coeff_expand`). But the prediction of
   **190–250 lines (ratio ≈ 0.5–0.65) did not hold**: the pin's eta-truncation
   comparison (`coeff_etaProd_eq_coeff_partialProd`, the `Tendsto`-to-a-discrete
   limit argument) and the truncation-stable inverse comparison
   (`coeff_inv_congr`) have no mathlib replacement and together dominate, so the
   module is 425 lines (≈370 of code) against 386 — ratio ≈ 1.1, essentially 1:1.
   This is the T6/T9 "rightness ≠ savings" outcome again.
4. **The shape issues.** (a) The missing `Algebra (Algebra.adjoin F S) (adjoin F S)`
   and `IsFractionRing` instances are mathlib's **scoped** instances in
   `IntermediateField.algebraAdjoinAdjoin`; the pin activated them with its
   `p2m_open`, and the port needed an explicit
   `open scoped IntermediateField.algebraAdjoinAdjoin`. (b) The
   `IsIntegrallyClosed adjoinJq` instance was not needed: the private scoped
   `UniqueFactorizationMonoid adjoinJq` (from `transcendental_jq`) and mathlib's
   `UniqueFactorizationMonoid` → `IsIntegrallyClosed` path sufficed, and the
   instance stayed in scope where `Monic.irreducible_iff_irreducible_map_fraction_map`
   is applied. (c) The Vieta step's
   `Polynomial.eq_of_natDegree_lt_card_of_eval_eq` (with the `eval`/`max`-degree
   side condition) and `Polynomial.prod_X_sub_C_coeff_card_pred` matched the
   pin's spelling in `v4.34.0`; no reshaping was needed. (d) `Polynomial.degree_sub_lt`
   is deprecated in favour of `Polynomial.degree_sub_lt_left`; the `haveI` style
   linter fired once (the cyclotomic instances) and was disabled locally. (e)
   Public declarations verified against a `Theorems/` wrapper must carry the
   **wrapper's explicit binders**, not the `S_` file's section variables — the
   checker caught exactly this on `aeval_jqN_toAdjoin`/`minpoly_jqN_eq` (the
   T7-log §7.3 rule, restated).

## 11. Where this sits

The remaining cone is the three-object division of the T11 work order's §4.1:
**T11** construction (done), **T12** properties (this topic), **T13** the
consequence — `finrank_adjoin_jqN_eq_of_prime`,
`ModularPolynomialData.eq_of_prime`, `splits_of_prime`, `splits_prime_at_slot`.
T12 hands T13 `exists_phiIrreducible_evalSymm` and T11's `evalAtJ_injective`;
T13 is then the cone's last topic.
