# `ModularCurve/ModularPolynomialProperties.lean` — notation dictionary

The module owns the cone's **symmetry** argument and its capstone
`exists_phiIrreducible_evalSymm`. Irreducibility is one call into `phiIrreducible_of_splits`;
everything else here is the transposed picture — `swapBivar`, the coefficient bounds that make it
monic, the q-expansion dictionary that feeds those bounds, the transposed evaluation read off the
splitting, and the minimal-polynomial step that turns the transpose identity into `EvalSymm` —
followed by the main line that runs it.

Most of the notation exists to keep apart **one polynomial `Φ` in eleven guises** (§6). The maps
that move between the guises are of two kinds: substitutions of the nome — a *level change*
`q ↦ q ^ N` (§2.1) and a *twist* `q ↦ u * q` (§2.4) — and a *coefficient embed* `ℚ → K` (§2.2),
together with the evaluations of `X` (§3). Section 2.3 is the one place where the level change and
the embed meet, and their composite (`qEmbedT`, then `evalAtJK` after `evalAtJ`) is the only map
that does both; §4 is the one place where their
effect on a coefficient is written down; §10 lists the names that look like one another and the one
fact that separates each pair.

Two conventions keep the statements short:

- **One name per map.** Every splitting hypothesis in the cone is stated with `evalAtJK K ℓ`
  (`ℤ[X] → K((q))`, `X ↦ j(q ^ ℓ)`, §2.3). The pin's composite
  `(coeffEmb K).comp (qExpand ℚ ℓ) |>.comp evalAtJ` is that map, and it now survives only inside
  the one derivation that reaches it from the descent (`splits_of_descends`).
- **One name per guise, introduced locally.** Inside a proof a guise is named with
  `set … with h…`, and the defining equation is the way to move between the name and its
  expression — never a global definition. §7 lists this proof's two (`ΦT`, `T`);
  [`ModularPolynomialIrreducible.md`](ModularPolynomialIrreducible.md) §8 lists that proof's two
  (`Φ₀`, `Φ₁`).

Eleven public declarations, seven `private`. The public surface is the transpose engine (§1), the
dictionary (§1, §4), the transposed evaluation (§2.3), the two descent-level statements (§4), and
the capstone (§7); the two statements that the block's own argument does not name —
`splits_of_descends` and `coeff_poleBounds_of_splits` — are the port's, recorded as `own:` in
[`spec/decl_markers.tsv`](../../spec/decl_markers.tsv).

Module: [ModularPolynomialProperties.lean](../../FLTForHuman/ModularCurve/ModularPolynomialProperties.lean)

## 1. The four rings

| ring | notation | what is read there |
|---|---|---|
| `ℤ[X][Y]` | `Polynomial (Polynomial ℤ)` | `Φ` and `swapBivar Φ`; the outer variable is `Y`, the inner one `X`, so `Φ.coeff k : ℤ[X]` is the `Y ^ k` coefficient |
| `ℚ((q))` | `LaurentSeries ℚ` | `jq = j(q)`, `jqN ℓ = j(q ^ ℓ)`, `evalAtJ (Φ.coeff k)`, the descended family `c k`, and the vanishing statements `hswap`, `h0top`, `h0le`, `hk` |
| `K((q))` | `LaurentSeries K`, `K = CyclotomicField ℓ ℚ` | `coeffEmb K`'s images, the conjugates `conj i`, the product `phiProd ℓ (conj ℓ ζ)`, and the level embedding's target |
| `ℚ(j(q))` | `↥ℚ⟮jq⟯` | `data.toAdjoin = Φ.map evalAtJGen`, `minpoly ℚ(j(q)) (j(q ^ ℓ))`, and the transpose after `.map evalAtJGen` |

The subalgebra `ℚ[j(q)]` (`adjoinJq`) is not named here: it occurs only inside T8's membership
statement `c k ∈ Algebra.adjoin ℚ {jq}`, which the main line passes to the assembly.

## 2. The maps

All of them are `→+*`.

### 2.1 Level change: `q ↦ q ^ N`

| name | statement |
|---|---|
| `qExpand R N` | `LaurentSeries R →+* LaurentSeries R`; on exponents, `m ↦ N * m` |
| `qExpand_coeff_mul` | `(qExpand R N f).coeff (N * m) = f.coeff m` — the one coefficient reading |
| `qExpand_coeff_of_not_dvd` | `¬ (N : ℤ) ∣ m` gives `(qExpand R N f).coeff m = 0`; so a level image has no exponent off the multiples of `N` |
| `qExpand_qExpand` | `qExpand R M (qExpand R N f) = qExpand R (M * N) f` — two level changes are one |
| `qExpand_congr`, `qExpand_one_apply`, `qExpand_C`, `qExpandAlg` | the level is a function of `N`; level one is the identity; constants are fixed; the `K`-algebra form |

`qExpand` is the *only* level change in the cone. Everything else that changes a level is a
composite of it with an embed (§2.3) or with a twist (§2.4).

### 2.2 Coefficient embed: `ℚ → K`

| name | statement |
|---|---|
| `coeffMap f` | `LaurentSeries R →+* LaurentSeries S` for `f : R →+* S`; the index is untouched |
| `coeffMap_coeff` | `(coeffMap f x).coeff m = f (x.coeff m)` |
| `coeffEmb L` | `coeffMap (algebraMap ℚ L)`, `ℚ((q)) → L((q))` |
| `coeffEmb_coeff` | `(coeffEmb L x).coeff m = algebraMap ℚ L (x.coeff m)` |
| `coeffMap_injective`, `coeffEmb_injective` | injective as soon as `f` is — the reason a vanishing can be checked in `K((q))` |
| `coeffMap_coeffMap` | two embeds are one, `coeffMap g (coeffMap f x) = coeffMap (g.comp f) x` |
| `coeffMap_coeffEmb`, `coeffMap_coeffEmb_algHom` | a Galois element of `L` fixes `coeffEmb L x`; this is why a descended coefficient is rational (T11) |
| `coeffMap_qExpand` | `coeffMap f (qExpand R n x) = qExpand S n (coeffMap f x)` — the level changes in either ring |
| `coeffEmb_qExpand` | `coeffEmb L (qExpand ℚ n x) = qExpand L n (coeffEmb L x)` — the same, in the shape the cone uses |

### 2.3 The two commute, and their composite is `qEmbedT`

```
                 qExpand ℚ N
      ℚ((q)) ──────────────► ℚ(( q))
         │                       │
 coeffEmb K                     coeffEmb K        coeffEmb_qExpand: the square commutes
         ▼                       ▼
       K((q)) ──────────────► K((q))
                 qExpand K N
```

Read right-then-down (or down-then-right — the same map): that composite is `qEmbedT K N`, the only
map in the cone that changes the level *and* the coefficients. Composed once more with `evalAtJ` it
is `evalAtJK K N`, the `X`-slot substitution of the whole symmetry argument
(`j(q) ↦ j(q ^ N)`, `j(q ^ N) ↦ j(q ^ (N * N))`) and the map every splitting hypothesis is stated
with.

| name | statement |
|---|---|
| `qEmbedT K N` | `(qExpand K N).comp (coeffMap (algebraMap ℚ K))`, `ℚ((q)) → K((q))` |
| `qEmbedT_apply` (**private**) | `qEmbedT K N x = qExpand K N (coeffMap (algebraMap ℚ K) x)` |
| `qEmbedT_injective` | injective; transports a vanishing in `K((q))` back to `ℚ((q))` |
| `qEmbedT_eq_coeffEmb_qExpand` | `qEmbedT K N x = coeffEmb K (qExpand ℚ N x)` — the shape the descent's own statements (`hc`) are written in |
| `qEmbedT_jq` | `qEmbedT K N jq = qExpand K N (coeffEmb K jq)` — the `X`-slot image of `j(q)` |
| `qEmbedT_jqN` | `qEmbedT K N (jqN N) = conj N ζ 0`: the `X`-slot image of `j(q ^ N)` is the `(N, 0)` conjugate `j(q ^ (N * N))` |
| `evalAtJK K N` | `(qEmbedT K N).comp evalAtJ`, `ℤ[X] → K((q))`, `X ↦ j(q ^ N)` |
| `evalAtJK_def`, `evalAtJK_X` | its defining equation, and its value on `X` (`qExpand K N (coeffEmb K jq)`) |
| `adjoinEmbedT K N` (**private**) | the same substitution on the coefficient ring `ℚ[j(q)]`, which is where the irreducibility half reads it; `adjoinEmbedT_comp_evalAtJAdj` (private) makes its two rows agree |

Inside `eval_swap_eq_zero_of_splits` the identity used is one level further:
`(qEmbedT K N).comp (evalAtJqN N) = (qExpand K N).comp (evalAtJK K N)` — on `X`,
`j(q ^ (N * N))` on both sides.

### 2.4 Twist `q ↦ u * q`, and the coset substitution

| name | statement |
|---|---|
| `qTwist u` | `LaurentSeries R →+* LaurentSeries R`; `(qTwist u f).coeff m = u ^ m * f.coeff m` (`qTwist_coeff`) |
| `qTwist_qTwist`, `qTwist_one_apply` | twists compose, and the trivial one is the identity |
| `qTwist_qExpand` | `qTwist v (qExpand R N f) = qExpand R N (qTwist (v ^ N) f)`: a twist and a level change commute up to raising the unit |
| `coeffMap_qTwist` | a twist commutes with an embed when the units match |
| `cosetSubst ζ a b` | `(qExpand K (a * a)).comp (qTwist (ζ ^ (a * b)))` — one level change and one twist, the coset `(a, b)` |
| `conj ℓ ζ i` | the `ℓ + 1` conjugates `j(ζ ^ b * q ^ a)` of `j(q)`, at coset indices `(a, b) = (ℓ, 0)` for `i = 0` and `(1, i - 1)` otherwise |
| `conj_zero`, `conj_succ` | the two shapes: `conj 0 = qExpand K (ℓ * ℓ) (coeffEmb K jq)`, `conj (b.succ) = qTwist (ζ ^ b) (coeffEmb K jq)` |
| `conj_succ_zero` | `conj ℓ ζ 1 = coeffEmb K jq` — the tame twist is trivial, so `j(q)` itself is a conjugate |

`conj 0` is the **extra** slot: it is `j(q ^ (ℓ * ℓ))`, one level change past `jqN ℓ`, not `j(q)`
and not `j(q ^ ℓ)`.

## 3. The five evaluations of `ℤ[X]`

| name | source → target | value on `X` | where it is read |
|---|---|---|---|
| `evalAtJ` | `ℤ[X] → ℚ((q))` | `j(q)` | `evalAtJ (Φ.coeff k)`, `hswap`'s first slot, the dictionary lemma |
| `evalAtJqN N` | `ℤ[X] → ℚ((q))` | `j(q ^ N)` | `hswap`'s `X`-slot |
| `evalAtJK K N` | `ℤ[X] → K((q))` | `j(q ^ N)` | every splitting hypothesis, over `K` |
| `evalAtJGen` | `ℤ[X] → ℚ(j(q))` | `j(q)` | `data.toAdjoin`, `hann`, `hTeq` |
| `evalAtJAdj` | `ℤ[X] → ℚ[j(q)]` | `j(q)` | the irreducibility half only |

The names read as `evalAtJ` plus the codomain (the coefficient field, or `Gen`, `Adj`) or the level
(`qN`). `evalAtJqN 1 = evalAtJ`. Three of the five differ only in their codomain: `evalAtJqN N` and
`evalAtJK K N` agree on every element, the second being the first followed by `coeffEmb K`, and
`evalAtJGen` is `evalAtJAdj` followed by the inclusion into the fraction field
(`algebraMap_comp_evalAtJGen`, `algebraMap_comp_evalAtJAdj`), which is what lets the final equality
be decided in `ℚ(j(q))` and then transported down.

`evalAtJqN N` is **not** `qEmbedT K N` composed with anything: its target is `ℚ((q))`. The
composite `qEmbedT K N ∘ evalAtJ` is `evalAtJK K N`, with target `K((q))`; the identity that
compares them one level up is the `hhom` inside `eval_swap_eq_zero_of_splits` (§2.3).

## 4. The coefficient dictionary

One rational number, seen in two rings at two indices. Everything the symmetry step knows about
`Φ`'s coefficients is one of these two statements, instantiated.

| name | statement |
|---|---|
| `coeff_qEmbedT` (**private**) | `(qEmbedT K ℓ f).coeff (ℓ * m) = algebraMap ℚ K (f.coeff m)` — level change (index `m ↦ ℓ * m`) and embed (scalar `ℚ → K`) at once |
| `coeff_eq_coeff_phiProd_of_splits` (**private**) | `algebraMap ℚ K ((evalAtJ (Φ.coeff k)).coeff m) = ((phiProd ℓ (conj ℓ ζ)).coeff k).coeff ((ℓ : ℤ) * m)` — the same, with `hsplit` naming `phiProd`'s coefficient as the level image |

```
   q ^ (-m)                                    q ^ (-(ℓ * m))
   ℚ, index -m      ── embed + level change ──►      K, index -(ℓ * m)
   (evalAtJ (Φ.coeff k)).coeff (-m)            (phiProd ℓ (conj ℓ ζ)).coeff k .coeff (-(ℓ * m))
```

The map from the left to the right is an equality after `algebraMap`, so a vanishing on the right
is a vanishing on the left, and a value `1` on either side is the same value.

| name | statement |
|---|---|
| `splits_of_descends` | `hc : PhiGenDescends ℓ ζ c` and `hΦ : ∀ k, evalAtJ (Φ.coeff k) = c k` give the splitting `Φ.map (evalAtJK K ℓ) = phiProd ℓ (conj ℓ ζ)` |
| `coeff_poleBounds_of_splits` | from `hζ` and the splitting: the three coefficient bounds of §5, in the shapes `monic_of_evalAtJ_coeff_eq_one`, `natDegree_le_of_evalAtJ_coeff_eq_zero` and `degree_lt_of_evalAtJ_coeff_eq_zero` consume |

## 5. The exponents

Four normalizations of "the pole order of a coefficient of `Φ`", and which statement carries which.

| exponent | where it is the bound | whose bound |
|---|---|---|
| `ℓ * ℓ + ℓ` | `phiProd.coeff k`, all `k` (`tPoleOrderLE_phiProd_coeff`); attained by `k = 0` | T10, uniform |
| `ℓ * ℓ + ℓ` | the leading term of `phiProd.coeff 0`, with residue `1` (`phiProd_conj_coeff_zero_lead`) | T10 |
| `ℓ * ℓ + ℓ` | vanishing at and below for `k ≠ 0` (`phiProd_conj_coeff_eq_zero_of_le`) | T10 |
| `ψ(ℓ) = ℓ + 1` | `evalAtJ (Φ.coeff 0)`: value `1` at `-ψ(ℓ)`, and nothing below it | `coeff_poleBounds_of_splits`, first two conjuncts |
| `ψ(ℓ) = ℓ + 1` | `evalAtJ (Φ.coeff k)`, `k ≠ 0`: vanishing **at and below** `-ψ(ℓ)` | `coeff_poleBounds_of_splits`, third conjunct |

The two scales are related by the level change: the product is read at exponent `-(ℓ * m)`, the
datum at `-m`. The distinction that matters downstream is strictness: `h0le` needs vanishing
*below* `-ψ(ℓ)` (so `natDegree_le_of_evalAtJ_coeff_eq_zero` gives `degree ≤ ψ(ℓ)`), while `hk` needs
vanishing *at and below* it (so `degree_lt_of_evalAtJ_coeff_eq_zero` gives `< ψ(ℓ)`, which is what
`swapBivar_monic_of_coeff_bounds` requires of every non-constant coefficient).

`dedekindPsi_prime` is the arithmetic step `ψ(ℓ) = ℓ + 1`; `hidx` inside
`coeff_poleBounds_of_splits` is the other, `ℓ * (-(ℓ + 1)) = -(ℓ * ℓ + ℓ)`.

## 6. `Φ` in eleven guises

| form | type | reading |
|---|---|---|
| `data.Φ` | `Polynomial (Polynomial ℤ)` | the bivariate; `Y` outer, `X` inner |
| `data.Φ.coeff k` | `ℤ[X]` | the `Y ^ k` coefficient — a polynomial in `X`, not a `q`-coefficient |
| `evalAtJ (data.Φ.coeff k)` | `LaurentSeries ℚ` | that coefficient at `X = j(q)` |
| `(evalAtJ (data.Φ.coeff k)).coeff m` | `ℚ` | its `q ^ m` coefficient |
| `algebraMap ℚ K ((…).coeff m)` | `K` | the same rational, in `K`; §4 relates it to `phiProd`'s coefficient at `ℓ * m` |
| `data.Φ.map (evalAtJK K ℓ)` | `Polynomial (LaurentSeries K)` | `X` killed at `j(q ^ ℓ)`; equals `phiProd ℓ (conj ℓ ζ)` (`hsplit`) |
| `data.Φ.eval₂ evalAtJ (jqN ℓ)` | `LaurentSeries ℚ` | the datum's own relation `Φ(j(q), j(q ^ ℓ)) = 0` (`eval_eq_zero`) |
| `data.Φ.eval₂ (evalAtJqN ℓ) jq` | `LaurentSeries ℚ` | the swapped one `Φ(j(q ^ ℓ), j(q)) = 0` (`hswap`) — the symmetry step's input |
| `data.toAdjoin` | `Polynomial ℚ(j(q))` | `data.Φ.map evalAtJGen`, the polynomial the minimal polynomial belongs to |
| `ΦT` (§7, `set`) | `Polynomial (Polynomial ℤ)` | `swapBivar data.Φ`, the bivariate with the two slots traded |
| `T` (§7, `set`) | `Polynomial ℚ(j(q))` | `ΦT.map evalAtJGen` — what the minimal-polynomial argument divides and compares |

The two `eval₂` rows are the pair of points `(j(q), j(q ^ ℓ))` and `(j(q ^ ℓ), j(q))`: the first is
the datum, the second is what the splitting supplies. They are *not* related by the datum.

## 7. The main line

The proof names two guises with `set … with h…`; the equations `hΦT : ΦT = swapBivar data.Φ` and
`hT : T = ΦT.map evalAtJGen` are how to move between a name and its expression.

| name | fact |
|---|---|
| `hζ1` | `ζ ^ ℓ = 1`, from primitivity; only T9's integrality consumes it |
| `hcoeff` | `∀ k, evalAtJ (data.Φ.coeff k) = c k` — the only bridge between the datum and the descended family |
| `hsplit` | `splits_of_descends hc hcoeff`, in the `evalAtJK` spelling |
| `hirr` | `PhiIrreducible data`, from `phiIrreducible_of_splits` |
| `hswap` | `Φ(j(q ^ ℓ), j(q)) = 0`, from `eval_swap_eq_zero_of_splits` |
| `h0top`, `h0le`, `hk` | the three bounds of §5, from `coeff_poleBounds_of_splits` |
| `h0monic`, `h0deg` | `(data.Φ.coeff 0).Monic`, of degree `ψ(ℓ)` — `monic_of_evalAtJ_coeff_eq_one` on `natDegree_le_of_evalAtJ_coeff_eq_zero h0le` and `h0top` |
| `ΦT` | `swapBivar data.Φ` (`set`) |
| `hTmonic`, `hTdeg` | `ΦT.Monic`, `ΦT.natDegree = ψ(ℓ)` — `swapBivar_monic_of_coeff_bounds` on the previous row and `degree_lt_of_evalAtJ_coeff_eq_zero` on `hk` |
| `T` | `ΦT.map evalAtJGen` (`set`) |
| `hTgen` | `T.Monic`, by `.map` |
| `hann` | `aeval (jqN ℓ) T = 0`, from `aeval_jqN_transposeToAdjoin hswap` |
| `hdvd` | `data.toAdjoin ∣ T`, from `minpoly_jqN_eq hirr` and `minpoly.dvd` |
| `hTeq` | `T = data.toAdjoin`, from `eq_of_monic_of_dvd_of_natDegree_le` — both sides monic of degree `ψ(ℓ)` |
| `hsymm` | `ΦT = data.Φ`, transported down by `map_injective evalAtJGen evalAtJGen_injective` |
| the conclusion | `evalSymm_of_swapBivar_eq (hΦT.symm.trans hsymm)` |

The degree comparison in `hTeq` is the only place the two normalizations must agree: `toAdjoin` has
degree `ψ(ℓ)` because `Φ` is monic in `Y` of that degree, and the transpose has `ψ(ℓ)` by §1.

## 8. Where the three bounds come from

All three are T10 read through §4, and none of them needs the descent's own pole bound
(`PhiGenDescends.poleOrderLE`, T11): the splitting already fixes `Φ`'s coefficients.

| bound | instantiation | T10 input |
|---|---|---|
| `h0top` | `k = 0`, `m = -ψ(ℓ)` | the leading term of `phiProd.coeff 0` at `-(ℓ * ℓ + ℓ)`, with `ℓ * (-(ℓ + 1)) = -(ℓ * ℓ + ℓ)` |
| `h0le` | `k` arbitrary, `m > ψ(ℓ)` | the uniform bound: `m ≥ ℓ + 2` gives `ℓ * m ≥ ℓ * ℓ + 2 * ℓ > ℓ * ℓ + ℓ` |
| `hk` | `k ≠ 0`, `m ≥ ψ(ℓ)` | the vanishing export at `-(ℓ * m)`, since `m ≥ ℓ + 1` gives `ℓ * m ≥ ℓ * ℓ + ℓ` |

`h0le`'s exponent is strictly below `-ψ(ℓ)` and `hk`'s is at and below it; that one exponent of
difference is what makes the constant coefficient the transpose's leading term.

## 9. What comes from the block

| name | module | use here |
|---|---|---|
| `phiIrreducible_of_splits` | `ModularPolynomialIrreducible.lean` | irreducibility of the datum, from its splitting |
| `minpoly_jqN_eq` | same | `data.toAdjoin` is the minimal polynomial of `j(q ^ ℓ)` |
| `evalAtJGen_injective` | same | transports the final equality down to `ℤ[X][Y]` |
| `evalAtJK` (with `evalAtJK_def`/`evalAtJK_X`), `qEmbedT`, `qEmbedT_injective`, `qEmbedT_jq`, `qEmbedT_jqN`, `qEmbedT_eq_coeffEmb_qExpand`, `conj_succ_zero` | same | the level embedding, the splitting's evaluation map, and their readings |
| `splits_of_prime` | `PhiGenSplits.lean` | the same splitting at a prime level over an arbitrary field, in the same `evalAtJK` spelling |
| `tPoleOrderLE_phiProd_coeff`, `phiProd_conj_coeff_zero_lead`, `phiProd_conj_coeff_eq_zero_of_le` | `Defs/PhiGen.lean`, `PhiGenPoleBounds.lean` | T10, the pole bounds of §5 |
| `PhiGenDescends`, `PhiGenDescends.intCoeffs`, `mem_adjoin_jq_of_phiGenDescends`, `exists_phiGenDescends`, `exists_modularPolynomialData_coeff_eq` | `Defs/PhiGen.lean`, `PhiGenIntegrality.lean`, `ModularForms/PhiGenDescends.lean`, `PhiGenDescent.lean`, `ModularPolynomialAssembly.lean` | the descended family, T9's integrality, T8's membership, and the assembly |
| `swapBivar`, `swapInner`, `cosetSubst`, `conj`, `phiProd` | `Defs/PhiGen.lean` | §2.4 and the transpose |
| `ev`, `ev_swap`, `swap_eq_of_evalSymm` | `Defs/BivariateEval.lean` | the coefficient-cast evaluation under `swapBivar_eval₂` and `swapBivar_eq_of_evalSymm` |
| `evalAtJ`, `jq`, `jqN`, `evalAtJqN`, `dedekindPsi`, `dedekindPsi_prime` | `Defs/Jq.lean`, `Defs/DedekindPsi.lean` | the notation of §1 and §3 |
| `qExpand`, `coeffMap`, `coeffEmb`, `coeffEmb_qExpand`, `coeffEmb_coeff` | `Defs/Laurent.lean` | §2.1 and §2.2 |
| `qTwist`, `qTwist_coeff`, `qTwist_qExpand` | `Defs/Twist.lean` | §2.4 |

The symmetry half's own new statements, which the block states inline, are `splits_of_descends`
and `coeff_poleBounds_of_splits`; the module does not name the block's staging nodes
(`transposeToAdjoin_monic_of_qExpansion`, `evalSymm_of_irreducible`, `evalSymm_of_splits`), whose
hypotheses are the transpose's monic and degree facts. See
[`ModularPolynomialIrreducible.md`](ModularPolynomialIrreducible.md) for the other half.

## 10. Look-alikes

| pair | the one fact that separates them |
|---|---|
| `qExpand ℚ N` / `qExpand K N` | the same action on exponents, different coefficient ring; only the `K` version occurs alone, inside `qEmbedT` |
| `qEmbedT K ℓ` / `iota` (`Analytic/Gamma0InvariantCore.lean`) | the same map under two names, one per layer: `iota` is T4's `(coeffEmb K).comp (qExpand ℚ ℓ)`, and `qEmbedT_eq_coeffEmb_qExpand` is the equality. They cannot be one name yet because T4 sits below this module |
| `qEmbedT K N` / `(coeffEmb K).comp (qExpand ℚ N)` | equal, by `qEmbedT_eq_coeffEmb_qExpand`; `qExpand K N` alone is neither |
| `evalAtJK K N` / `(qEmbedT K N).comp evalAtJ` / `(coeffEmb K).comp (evalAtJqN N)` | the same map three ways: the first is the port's name, the second is its definition (`evalAtJK_def`), the third is the reading through `evalAtJqN`; only the first occurs in statements |
| `coeffEmb_qExpand` / `coeffMap_qExpand` | the same square (§2.3); the first is the `ℚ`-into-`L` case, the second the general one |
| `evalAtJqN N` / `evalAtJK K N` | different codomains (`ℚ((q))` / `K((q))`), same value on `X` |
| `ΦT` / `swapBivar data.Φ`, `T` / `(swapBivar data.Φ).map evalAtJGen` | the same, one being the proof's local `set` name and the other its value (`hΦT`, `hT`) |
| `evalAtJ` / `evalAtJGen` | same formula, codomain `ℚ((q))` / `ℚ(j(q))`; `algebraMap_comp_evalAtJGen` relates them |
| `jqN ℓ` / `conj 0` / `conj 1` | `j(q ^ ℓ)`, `j(q ^ (ℓ * ℓ))`, `j(q)`: the finite slots are `conj (b.succ)`, the extra one is `conj 0` |
| `Φ.coeff k` / `(evalAtJ (Φ.coeff k)).coeff m` | a polynomial in `X` / a rational number |
| `Φ.eval₂ evalAtJ (jqN ℓ)` / `Φ.eval₂ (evalAtJqN ℓ) jq` | the datum's relation / the transposed one; only the second comes from the splitting |
| `data.Φ` / `data.toAdjoin` | bivariate over `ℤ` / `X`-evaluated over `ℚ(j(q))` |
| `swapBivar` / `Bivariate.swap` | one private bridge (`swapBivar_eq_swap`), the only door to mathlib's bivariate API |
| `ψ(ℓ)` / `ℓ + 1` / `ℓ * ℓ + ℓ` | §5: descended, prime-evaluated, the product's; related by the level change |
| `PoleOrderLE (c k) (ℓ + 1)` (T11) / T10's exports | not interchangeable: T11's is the descended bound and is strict at the top exponent, T10's export is what `hk` needs at and below it |
| `ℓ` | two jobs at one value: the isogeny order of `Φ_ℓ` (`ψ(ℓ) = ℓ + 1` conjugates, the level change `q ^ ℓ`) and the cyclotomic level of `K = ℚ(ζ_ℓ)`; `dedekindPsi_prime` is where they meet |
