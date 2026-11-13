# `ModularCurve/ModularEquation/` — theory A's notation dictionary

One entry for the whole theory — five subject modules over four support modules — because the code
moves between them and a per-module entry has to be re-homed every time a lemma changes neighbours.
What follows is the vocabulary of the modular-equation cone: the rings, the level embedding and its
readings, the guises of `Φ`, the evaluations of `ℤ[X]`, the exponent discipline, and the names the two
main lines use.

The mathematics: [base/006](../../../../base/006-the-modular-equation.md) (the modular equation and
the cover behind it), [base/013 §3, §6](../../../../base/013-riemann-existence-and-the-q-expansion-principle.md)
(which analytic input the construction uses, and why it is level one), and
[base/014 §4](../../../../base/014-hecke-operators.md) (the Hecke coset that supplies it).

## 1. What each module owns

| module | owns |
|---|---|
| `Support/LevelEmbedding` | `qEmbedT`, `qEmbedT_injective`, its readings (`qEmbedT_eq_coeffEmb_qExpand`, `qEmbedT_jq`, `qEmbedT_jqN`), `evalAtJK` |
| `Support/Descent` | the three range tests the descent applies: `mem_range_qExpand_of_qTwist_eq`, `mem_range_coeffEmb_of_forall_coeffMap_eq`, `mem_range_coeffEmb_qExpand_of_mem_inter`; the contraction `qContract` (private) |
| `Support/PoleBounds` | `tPoleOrderLE_phiProd_coeff`, `phiProd_conj_coeff_zero_lead`, `phiProd_conj_coeff_eq_zero_of_le` |
| `Support/Permutation` | `map_prod_of_perm`, the twist's permutation (`twistPerm`, `qTwist_conj`), the Galois permutation (`galPerm`, `coeffMap_conj`) |
| `Transpose` | `swapBivar`, `swapBivar_monic_of_coeff_bounds`, the q-expansion-to-degree dictionary (`monic_of_evalAtJ_coeff_eq_one`, `natDegree_le_of_evalAtJ_coeff_eq_zero`, `degree_lt_of_evalAtJ_coeff_eq_zero`), `eval_swap_eq_zero_of_splits`, `aeval_jqN_transposeToAdjoin` |
| `Construction` | `exists_phiGenDescends`, `PhiGenDescends.intCoeffs`, `evalAtJ_injective`, `exists_modularPolynomialData_splits` |
| `Existence` | `evalAtJGen_injective`, `conj_injective`, `aeval_jqN_toAdjoin`, `minpoly_jqN_eq`, `phiIrreducible_of_splits`, `coeff_poleBounds_of_splits` (private), `exists_phiIrreducible_evalSymm` |
| `Split` | `eq_of_prime`, `splits_of_prime`, `splits_prime_at_slot`, the slot-root API, and the any-field half |
| `LevelTwo` | `phi_eq_phiTwo` |

The whole theory is threaded on **one identity**, named `hsplit` everywhere:
`Φ.map (evalAtJK K ℓ) = phiProd ℓ (conj ℓ ζ)` (`Transpose:223`, `Existence:583`, `Existence:684`).
`Construction` *produces* it (§6.1); every other module *takes it as a hypothesis*.

## 2. The rings

| ring | notation | what is read there |
|---|---|---|
| `ℤ[X][Y]` | `Polynomial (Polynomial ℤ)` | `Φ` and `swapBivar Φ`; the outer variable is `Y`, the inner one `X`, so `Φ.coeff k : ℤ[X]` is the `Y ^ k` coefficient |
| `ℚ((q))` | `LaurentSeries ℚ` | `jq`, `jqN ℓ`, `evalAtJ (Φ.coeff k)`, the descended family `c k`, and the swapped vanishing `hswap` |
| `K((q))` | `LaurentSeries K`, `K = CyclotomicField ℓ ℚ` | `coeffEmb K`'s images, the conjugates `conj i`, `phiProd ℓ (conj ℓ ζ)`, the level embedding's target |
| `ℚ[j(q)]` | `adjoinJq` | `jAdj`, `evalAtJAdj`, and the irreducibility half's `Φ₀` |
| `ℚ(j(q))` | `ℚ⟮jq⟯` | `jGen`, `evalAtJGen`, `data.toAdjoin`, `minpoly ℚ(j(q)) (j(q ^ ℓ))` |
| the ring of integers of `K` | `integralClosure ℤ K`, containing `zetaRing ζ = ℤ[ζ]` | where the product's coefficients are shown to live (`Construction` §7) |

`ℚ[j(q)]` is the subalgebra `Algebra.adjoin ℚ {jq}`; it appears in the cone's own statements only as
the membership `c k ∈ Algebra.adjoin ℚ {jq}`, which `Construction` consumes.

## 3. The maps

All of them are `→+*`. Three things distinguish them: which slot they act on (`X` of `Φ`, the nome
`q`, or the outer variable `Y`), which coefficient ring they land in, and whether they change the
level.

| map | source → target | action |
|---|---|---|
| `evalAtJ` | `ℤ[X] → ℚ((q))` | `X ↦ j(q)` |
| `evalAtJqN N` | `ℤ[X] → ℚ((q))` | `X ↦ j(q ^ N)` |
| `evalAtJAdj` | `ℤ[X] → ℚ[j(q)]` | `X ↦ j(q)` |
| `evalAtJGen` | `ℤ[X] → ℚ(j(q))` | `X ↦ j(q)` |
| `evalAtJK K N` | `ℤ[X] → K((q))` | `X ↦ j(q ^ N)` |
| `coeffMap f` | `R((q)) → S((q))` | coefficients through `f`, index untouched |
| `coeffEmb L` | `ℚ((q)) → L((q))` | `coeffMap (algebraMap ℚ L)` |
| `qExpand R N` | `R((q)) → R((q))` | `q ↦ q ^ N`: the coefficient at `m` moves to `N * m` |
| `qTwist u` | `R((q)) → R((q))` | `q ↦ u * q`: the coefficient at `m` is multiplied by `u ^ m` |
| `cosetSubst ζ a b` | `R((q)) → R((q))` | `(qExpand R (a * a)).comp (qTwist (ζ ^ (a * b)))` |
| `qEmbedT K N` | `ℚ((q)) → K((q))` | `q ↦ q ^ N` **and** coefficients `ℚ → K` |
| `adjoinEmbedT K N` (private) | `ℚ[j(q)] → K((q))` | the same substitution on the coefficient ring |
| `algebraMap ℚ[j(q)] ℚ(j(q))` | inclusion | the Gauss step of the irreducibility half |

Four identities collapse the spellings, so the picture is smaller than the table:

- `coeffEmb_qExpand` (and its general form `coeffMap_qExpand`): the level change and the embed commute,
  so `qEmbedT K N` is the pin's composite `(coeffEmb K).comp (qExpand ℚ N)` as well — that is
  `qEmbedT_eq_coeffEmb_qExpand`, the one bridge between the two spellings. The descent's own
  statements are written on the right-hand side.
- `evalAtJK_def`: `evalAtJK K N = (qEmbedT K N).comp evalAtJ`.
- `adjoinEmbedT_comp_evalAtJAdj`: `(adjoinEmbedT K ℓ).comp evalAtJAdj = (qEmbedT K ℓ).comp evalAtJ` —
  the two rows `ℤ[X] → ℚ[j(q)] → K((q))` and `ℤ[X] → ℚ((q)) → K((q))` agree.
- `qTwist_qExpand`, `qTwist_comp_qEmbedT`: a twist and a level change commute up to raising the unit.

The `X`-slot image of `j(q ^ N)` is the extra slot: `qEmbedT_jqN : qEmbedT K N (jqN N) = conj N ζ 0`,
i.e. `j(q ^ (N * N))`. That is the point where the datum is evaluated.

## 4. Integrality, and the coefficient index shift

| name | statement |
|---|---|
| `IntCoeffs f` | `∀ m : ℤ, ∃ z : ℤ, f.coeff m = z` — every coefficient is an integer |
| `IntPoleCoeffs f` (private to `Construction`) | `∀ n : ℕ, ∃ z : ℤ, f.coeff (-n) = z` — the polar part only |

`IntCoeffs` is the public predicate (`Defs/PhiGen.lean`); `IntPoleCoeffs` is the sharpening the
assembly uses, because the triangularity of `j` reads only the nonpositive exponents:
`coeff_aeval_jq_neg : (aeval jq P).coeff (-m) = P.coeff m` for `m ≥ P.natDegree`. Hence a rational
polynomial in `j` whose *polar* part is integral is an integer polynomial
(`exists_intPoly_of_intPoleCoeffs`, private in `Construction`), and `intPoleCoeffs_of_intCoeffs` is
the projection from the public predicate.

One rational number is then seen in two rings at two indices. Everything the symmetry half knows about
`Φ`'s coefficients is one of these two statements, instantiated:

| name | statement |
|---|---|
| `coeff_qEmbedT` (private) | `(qEmbedT K ℓ f).coeff (ℓ * m) = algebraMap ℚ K (f.coeff m)` — level change `m ↦ ℓ * m` and embed at once |
| `coeff_eq_coeff_phiProd_of_splits` (private) | `algebraMap ℚ K ((evalAtJ (Φ.coeff k)).coeff m) = ((phiProd ℓ (conj ℓ ζ)).coeff k).coeff (ℓ * m)`, with `hsplit` naming `phiProd`'s coefficient as the level image |

The map from the left to the right is an equality after `algebraMap`, so a vanishing on the right is a
vanishing on the left, and a value `1` on either side is the same value.

## 5. `Φ` in its guises

### 5.1 The two slots are instantiated differently

`Φ` is `ℤ[X][Y]`: the outer variable is `Y`, `X` lives inside the coefficients. So the `Y`-slot is
instantiated by a **value** in the target ring, the `X`-slot by a **ring hom out of `ℤ[X]`**
(equivalently by the image of `X`, since a hom out of `ℤ[X]` is determined by it). `evalAtJ`,
`evalAtJqN`, `evalAtJAdj`, `evalAtJGen`, `evalAtJK` are exactly those algebra structures, one per
target. The presentation is asymmetric because the symmetry argument needs the `Y`-polynomial itself
— monic, of degree `ψ(ℓ)`, `dvd`-comparable, with `minpoly` — so `Y` stays the variable and `X`
becomes coefficients.

`Polynomial.map` and `Polynomial.eval₂` differ in what they do with `Y`:

| form | `X` | `Y` | result |
|---|---|---|---|
| `Φ.map f` | replaced by the evaluation `f` | kept symbolic | `Polynomial (LaurentSeries K)` |
| `Φ.eval₂ f y` | replaced by `f` | replaced by the value `y` | a series |
| `Φ.eval y` | kept | replaced by `y` | `eval₂` with the identity coefficient map |
| `Polynomial.aeval a q` | — | replaced by `a` | `eval₂ C a`, on a polynomial whose `X` is already gone |

### 5.2 The guises

| form | type | reading |
|---|---|---|
| `data.Φ` | `Polynomial (Polynomial ℤ)` | the bivariate; `Y` outer, `X` inner |
| `data.Φ.coeff k` | `ℤ[X]` | the `Y ^ k` coefficient — a polynomial in `X`, not a `q`-coefficient |
| `evalAtJ (data.Φ.coeff k)` | `LaurentSeries ℚ` | that coefficient at `X = j(q)` |
| `(evalAtJ (data.Φ.coeff k)).coeff m` | `ℚ` | its `q ^ m` coefficient |
| `algebraMap ℚ K ((…).coeff m)` | `K` | the same rational, in `K` (§4 relates it to `phiProd` at `ℓ * m`) |
| `data.Φ.map (evalAtJK K ℓ)` | `Polynomial (LaurentSeries K)` | `X` killed at `j(q ^ ℓ)`; equal to `phiProd ℓ (conj ℓ ζ)` — this is `hsplit` |
| `data.Φ.eval₂ evalAtJ (jqN ℓ)` | `LaurentSeries ℚ` | the datum's own relation `Φ(j(q), j(q ^ ℓ)) = 0` (`eval_eq_zero`) |
| `data.Φ.eval₂ (evalAtJqN ℓ) jq` | `LaurentSeries ℚ` | the swapped one `Φ(j(q ^ ℓ), j(q)) = 0` (`hswap`) — from the splitting, not from the datum |
| `Φ₀ = data.Φ.map evalAtJAdj` | `Polynomial ℚ[j(q)]` | the irreducibility half's working guise (`Existence`) |
| `Φ₁ = Φ₀.map (adjoinEmbedT K ℓ)` | `Polynomial (LaurentSeries K)` | the same polynomial at the level-`ℓ` nome; equals `data.Φ.map (evalAtJK K ℓ)` |
| `data.toAdjoin` | `Polynomial ℚ(j(q))` | `data.Φ.map evalAtJGen`, the polynomial the minimal polynomial belongs to |
| `ΦT = swapBivar data.Φ` | `Polynomial (Polynomial ℤ)` | the transpose of the bivariate |
| `T = ΦT.map evalAtJGen` | `Polynomial ℚ(j(q))` | what the minimal-polynomial argument divides and compares |

`Φ₀`, `Φ₁`, `ΦT`, `T` are **local abbreviations** introduced by `set … with h…` inside the proofs; the
named equalities (`hΦ₀`, `hΦ₁`, `hΦT`, `hT`) are how a reader — and the proof — moves between the name
and its expression. There is no global definition for any of them.

### 5.3 The five evaluations of `ℤ[X]`

| name | source → target | value on `X` | where it is read |
|---|---|---|---|
| `evalAtJ` | `ℤ[X] → ℚ((q))` | `j(q)` | `evalAtJ (Φ.coeff k)`, the dictionary lemma |
| `evalAtJqN N` | `ℤ[X] → ℚ((q))` | `j(q ^ N)` | the swapped `Y`-slot |
| `evalAtJK K N` | `ℤ[X] → K((q))` | `j(q ^ N)` | every splitting hypothesis |
| `evalAtJGen` | `ℤ[X] → ℚ(j(q))` | `j(q)` | `data.toAdjoin`, the transpose identity |
| `evalAtJAdj` | `ℤ[X] → ℚ[j(q)]` | `j(q)` | the irreducibility half only |

The names read as `evalAtJ` plus the codomain (`Gen`, `Adj`) or the level (`qN`); `evalAtJqN 1 =
evalAtJ`. Three differ only in codomain, and the inclusions between them are
`algebraMap_comp_evalAtJGen` and `algebraMap_comp_evalAtJAdj` — which is what lets a final equality be
decided in `ℚ(j(q))` and transported down. `evalAtJqN N` is **not** a composite with `qEmbedT`: its
target is `ℚ((q))`; the identity that transports a vanishing down is
`(coeffEmb K) ∘ evalAtJqN N = evalAtJK K N`, and `coeffEmb` is injective.

## 6. The splitting, and what it gives

### 6.1 Where `hsplit` comes from

`Construction` proves `exists_modularPolynomialData_splits (ℓ) (ζ) (hζ)`:
`∃ data, data.Φ.map (evalAtJK (CyclotomicField ℓ ℚ) ℓ) = phiProd ℓ (conj ℓ ζ)`. The shape of its proof
is the assembly: for each `k` an integer polynomial `Q k` with `Q k (jq) = c k` (§4); the sum
`Φ = ∑ k ∈ Finset.range (ℓ + 2), C (Q k) * X ^ k`; and the coefficientwise identity. Monicity, degree
`ψ(ℓ)` and vanishing at `j(q^ℓ)` are then `phiProd`'s own properties (`phiProd_monic`,
`phiProd_natDegree`, `phiProd_eval_conj`), pulled back along the injective level embedding by
`monic_of_map_eq_phiProd`, `natDegree_of_map_eq_phiProd`, `eval₂_eq_zero_of_map_eq_phiProd`
(private). The coefficientwise bridge `∀ k, evalAtJ (Φ.coeff k) = c k` is *not* part of the statement.

### 6.2 What a consumer reads off `hsplit`

| statement | gives |
|---|---|
| `eval_swap_eq_zero_of_splits` | `hswap : data.Φ.eval₂ (evalAtJqN ℓ) jq = 0` — the swapped relation the symmetry step needs |
| `coeff_poleBounds_of_splits` (private) | the three coefficient bounds of §7 |
| `phiIrreducible_of_splits` | `PhiIrreducible data`, via `Φ₀`/`Φ₁` and a root count |
| `minpoly_jqN_eq` | `data.toAdjoin` is `minpoly ℚ(j(q)) (j(q ^ ℓ))` |
| `aeval_jqN_toAdjoin`, `aeval_jqN_transposeToAdjoin` | the (transposed) datum annihilates `j(q ^ ℓ)` in `ℚ(j(q))[Y]` |
| `swapBivar_monic_of_coeff_bounds` | the transpose is monic of degree `ψ(ℓ)`, from those bounds |
| `splits_of_prime`, `splits_prime_at_slot` | the same splitting at a prime level over an arbitrary field, at a general slot `(e, u)` |
| `eq_of_prime` | the datum at a prime is unique, so "the level-`ℓ` datum" is a definite object |

The two symmetry forms are equivalent, and that is a theorem, not a definition: `EvalSymm Φ` is
`∀ x y : ℚ((q)), Φ(x, y) = Φ(y, x)`, while `swapBivar Φ = Φ` is the coefficient statement
`∀ i j, (Φ.coeff i).coeff j = (Φ.coeff j).coeff i`. `evalSymm_of_swapBivar_eq` is the easy direction,
one line from `swapBivar_eval₂`; `swapBivar_eq_of_evalSymm` evaluates `Φᵀ - Φ` at integer points
(`ev_int`) and upgrades the vanishing by two rounds of `Polynomial.eq_zero_of_infinite_isRoot`. The
test ring must contain an infinite ring: over `𝔽_p` the two are not equivalent.

## 7. The exponent discipline

Four normalizations of "the pole order of a coefficient of `Φ`", and which statement carries which.

| exponent | where it is the bound | whose bound |
|---|---|---|
| `ℓ * ℓ + ℓ` | `phiProd.coeff k`, all `k` (`tPoleOrderLE_phiProd_coeff`); attained by `k = 0` | the product, uniform |
| `ℓ * ℓ + ℓ` | the leading term of `phiProd.coeff 0`, with residue `1` (`phiProd_conj_coeff_zero_lead`) | the product |
| `ℓ * ℓ + ℓ` | vanishing at and below, `k ≠ 0` (`phiProd_conj_coeff_eq_zero_of_le`) | the product |
| `ψ(ℓ) = ℓ + 1` | `evalAtJ (Φ.coeff 0)`: value `1` at `-ψ(ℓ)`, nothing below it | `coeff_poleBounds_of_splits` |
| `ψ(ℓ) = ℓ + 1` | `evalAtJ (Φ.coeff k)`, `k ≠ 0`: vanishing **at and below** `-ψ(ℓ)` | `coeff_poleBounds_of_splits` |

The two scales are related by the level change: the product is read at exponent `-(ℓ * m)`, the datum
at `-m`. Only the strictness differs downstream: the "below `-ψ(ℓ)`" version gives
`natDegree ≤ ψ(ℓ)` (`natDegree_le_of_evalAtJ_coeff_eq_zero`), the "at and below" version gives
`< ψ(ℓ)` (`degree_lt_of_evalAtJ_coeff_eq_zero`), which is what `swapBivar_monic_of_coeff_bounds`
requires of every non-constant coefficient. `dedekindPsi_prime` is the arithmetic step `ψ(ℓ) = ℓ + 1`.

## 8. The names in the two main lines

### 8.1 `Construction` (the assembly)

| name | fact |
|---|---|
| `c`, `hc` | the descended family and `PhiGenDescends ℓ ζ c` |
| `hint`, `hmem` | `∀ k, IntCoeffs (c k)` (`PhiGenDescends.intCoeffs`) and `∀ k, c k ∈ ℚ[jq]` (`mem_adjoin_jq_of_phiGenDescends`) |
| `P`, `Q`, `hQeval` | the witness in `ℚ[X]`, the integer polynomial, and `∀ k, evalAtJ (Q k) = c k` |
| `Φ`, `hΦ` | `∑ C (Q k) * X ^ k`, and its defining equation |
| `hΦdeg` | `Φ.natDegree ≤ ℓ + 1`, from the index range |
| `hsplit` | `Φ.map (evalAtJK (CyclotomicField ℓ ℚ) ℓ) = phiProd ℓ (conj ℓ ζ)` |

### 8.2 `Existence` (the capstone)

| name | fact |
|---|---|
| `hsplit` | the splitting hypothesis of §6.1 |
| `hirr` | `PhiIrreducible data`, from `phiIrreducible_of_splits` |
| `hswap` | `Φ(j(q ^ ℓ), j(q)) = 0`, from `eval_swap_eq_zero_of_splits` |
| `h0top`, `h0le`, `hk` | the three bounds of §7, from `coeff_poleBounds_of_splits` |
| `h0monic`, `h0deg` | `(data.Φ.coeff 0).Monic`, of degree `ψ(ℓ)` |
| `ΦT`, `hTmonic`, `hTdeg` | `swapBivar data.Φ`, monic of degree `ψ(ℓ)` by `swapBivar_monic_of_coeff_bounds` |
| `T`, `hTgen` | `ΦT.map evalAtJGen`, monic by `.map` |
| `hann` | `aeval (jqN ℓ) T = 0`, from `aeval_jqN_transposeToAdjoin hswap` |
| `hdvd` | `data.toAdjoin ∣ T`, from `minpoly_jqN_eq` and `minpoly.dvd` |
| `hTeq` | `T = data.toAdjoin`, by `eq_of_monic_of_dvd_of_natDegree_le` |
| `hsymm` | `ΦT = data.Φ`, by `map_injective evalAtJGen evalAtJGen_injective` |
| the conclusion | `evalSymm_of_swapBivar_eq (hΦT.symm.trans hsymm)` |

## 9. Look-alikes

| pair | the one fact that separates them |
|---|---|
| `qExpand ℚ N` / `qExpand K N` | same action on exponents, different coefficient ring |
| `qEmbedT K N` / `(coeffEmb K).comp (qExpand ℚ N)` | equal, by `qEmbedT_eq_coeffEmb_qExpand`; `qExpand K N` alone is neither |
| `qEmbedT K ℓ` / `iota` (`Analytic/Gamma0InvariantCore.lean`) | the same map under two names, one per layer; the equality is `qEmbedT_eq_coeffEmb_qExpand` |
| `evalAtJK K N` / `(qEmbedT K N).comp evalAtJ` / `(coeffEmb K).comp (evalAtJqN N)` | the same map three ways: the port's name, its definition, and the form the swap proof uses |
| `evalAtJqN N` / `evalAtJK K N` | different codomains (`ℚ((q))` / `K((q))`), same value on `X` |
| `evalAtJ` / `evalAtJGen` | same formula, codomain `ℚ((q))` / `ℚ(j(q))` |
| `Φ.coeff k` / `(evalAtJ (Φ.coeff k)).coeff m` | a polynomial in `X` / a rational number |
| `Φ.eval₂ evalAtJ (jqN ℓ)` / `Φ.eval₂ (evalAtJqN ℓ) jq` | the datum's relation / the swapped one, which only the splitting supplies |
| `data.Φ` / `data.toAdjoin` | bivariate over `ℤ` / `X`-evaluated over `ℚ(j(q))` |
| `EvalSymm Φ` / `swapBivar Φ = Φ` | equivalent, but one is an identity of the evaluated function, the other of coefficients; the bridge runs through integer points |
| `jqN ℓ` / `conj 0` / `conj 1` | `j(q ^ ℓ)`, `j(q ^ (ℓ * ℓ))`, `j(q)`: the finite slots are `conj (b.succ)`, the extra one is `conj 0` |
| `ψ(ℓ)` / `ℓ + 1` / `ℓ * ℓ + ℓ` | §7: descended, prime-evaluated, the product's; related by the level change |
| `ℓ` | two jobs at one value: the isogeny order of `Φ_ℓ` (`ψ(ℓ) = ℓ + 1` slots, the level change `q ^ ℓ`) and the cyclotomic level of `K = ℚ(ζ_ℓ)` |

## 10. Where the arithmetic of the integrality sits

`Construction` is the one place where `ℤ[ζ]` enters (`PhiGenDescends.intCoeffs`): the `m`-th
coefficient of `c k` is the `(ℓ * m)`-th coefficient of `phiProd`, read in `K` (`coeffEmb_coeff`,
`qExpand_coeff_mul`); every coefficient of `phiProd` lies in `integralClosure ℤ K` (`coeff_phiProd_mem`,
through `zetaRing_le`, because `ζ ^ ℓ = 1`); and a rational number integral over `ℤ` is an integer
(`IsIntegrallyClosed.isIntegral_iff`). Supporting names: `zetaRing`, `zetaUnitS`, `jqS`, `conjAdjoin`,
`coeffMap_conjAdjoin`, `prod_eq_of_lift`. None of it is analytic — it is the formal `q`-expansion plus
integrality of roots of unity.
