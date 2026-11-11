# `ModularCurve/ModularPolynomialProperties.lean` — notation dictionary

The module owns the cone's **symmetry** argument and its capstone
`exists_phiIrreducible_evalSymm`. Irreducibility is one call into
`phiIrreducible_of_splits`, which stays with the 895 block; everything else here is
the transposed picture — `swapBivar`, the coefficient bounds that make it monic, the
q-expansion dictionary that feeds those bounds, and the minimal-polynomial step that
turns the transpose identity into `EvalSymm` — followed by the main line that runs it.

Eight public declarations, six `private`: the transpose engine of §1, the generic
step of §2, and the capstone. What the argument borrows from the block is listed in
§7.

Module: [ModularPolynomialProperties.lean](../../FLTForHuman/ModularCurve/ModularPolynomialProperties.lean)

## 1. The transpose engine

`swapBivar Φ` is mathlib's `Bivariate.swap` on `ℤ[X][Y]`. One bridge carries the whole
engine, and the two directions of the `EvalSymm` dictionary sit on top of it.

| name | statement |
|---|---|
| `swapBivar_eq_swap` (**private**) | `swapBivar Φ = Bivariate.swap Φ`, as ring homs — the only bridge to mathlib's bivariate API |
| `swapBivar_eval₂` (**private**) | `(swapBivar Φ).eval₂ (aeval x) y = Φ.eval₂ (aeval y) x`: the two slots trade places, i.e. `ev_swap` read through that bridge |
| `swapBivar_C`, `degree_swapBivar_lt` (**private**) | the transpose of a constant, and the degree bound that keeps the transpose's leading term in its `Y ^ 0` coefficient |
| `swapBivar_monic_of_coeff_bounds` | a polynomial whose `Y ^ 0` coefficient is monic of degree `d`, and whose higher coefficients have degree `< d`, has a monic transpose of degree `d` |
| `evalSymm_of_swapBivar_eq` | `swapBivar Φ = Φ` gives `EvalSymm Φ` |
| `swapBivar_eq_of_evalSymm` | the converse, `EvalSymm Φ` gives `swapBivar Φ = Φ`; T13's uniqueness step uses this one |
| `ModularPolynomialData.aeval_jqN_transposeToAdjoin` | the transposed datum annihilates `j(q ^ N)` as soon as the datum does under the swapped evaluation |
| `degree_lt_of_evalAtJ_coeff_eq_zero`, `natDegree_le_of_evalAtJ_coeff_eq_zero`, `monic_of_evalAtJ_coeff_eq_one` | the dictionary: pole bounds on the `q`-expansion read as degree and monicity of the coefficient polynomials |

The coefficient-cast evaluation `ev` and `swap_eq_of_evalSymm`, which
`swapBivar_eval₂` and `swapBivar_eq_of_evalSymm` rest on, are *not* exports here:
they live in `Defs/BivariateEval.lean`, the single home this cone and the `X1`
integrality module share.

## 2. The one generic step

| name | statement |
|---|---|
| `coeff_coeffEmb_qExpand` (**private**) | `(coeffEmb L (qExpand ℚ N f)).coeff (N * m) = algebraMap ℚ L (f.coeff m)` — the level substitution creates and loses no coefficients |

The rule behind the extraction organizes the module: a helper whose statement mentions
`data`, `PhiGenDescends`, `conj` or `phiProd` says what the goal says under another
name, so it belongs in the main line — which is why the dictionary chain
(`monic_of_evalAtJ_coeff_eq_one`, `natDegree_le_of_evalAtJ_coeff_eq_zero`,
`swapBivar_monic_of_coeff_bounds`, `degree_lt_of_evalAtJ_coeff_eq_zero`, then
`.map evalAtJGen`) is written out there rather than packaged. A helper about a general
object may be extracted.

## 3. The objects

| name | meaning |
|---|---|
| `ℓ`, `hℓ : Fact (Nat.Prime ℓ)` | the level; `dedekindPsi_prime` turns `ψ(ℓ)` into `ℓ + 1` at each use |
| `K = CyclotomicField ℓ ℚ` | the field the symmetry is decided over; the level data enters it through `coeffEmb K` |
| `ζ`, `hζ`, `hζ1` | the primitive `ℓ`-th root with its certificate, from `exists_primitiveRoot_cyclotomic`; `hζ1 : ζ ^ ℓ = 1` is what T9's integrality consumes |
| `c`, `hc` | the descended family and its `PhiGenDescends` certificate (T11) |
| `data`, `hcoeff` | the assembled datum, with `hcoeff k : evalAtJ (data.Φ.coeff k) = c k` — the only bridge between the datum and the family |
| `evalAtJ` | `ℤ[X] → ℚ((q))`, `X ↦ j(q)` |
| `evalAtJqN ℓ` | `ℤ[X] → ℚ((q))`, `X ↦ j(q ^ ℓ)` |
| `evalAtJGen` | `ℤ[X] → ℚ(j(q))`, `X ↦ j(q)` |
| `swapBivar Φ` | the `X ↔ Y` swap of §1 |
| `EvalSymm Φ` | evaluated symmetry: `∀ x y, Φ(j(x), y) = Φ(j(y), x)` — the module's target |
| `data.toAdjoin` | `Φ(j(q), Y)` over `ℚ(j(q))`, the polynomial the minimal polynomial belongs to |
| `jqN ℓ` | `j(q ^ ℓ)` |

## 4. The main line

| name | statement |
|---|---|
| `hsplit` | `data.Φ.map (((coeffEmb K).comp (qExpand ℚ ℓ)).comp evalAtJ) = phiProd ℓ (conj ℓ ζ)` — the datum read at `j(q)` is the conjugate product, coefficient by coefficient from `hcoeff` and `hc` |
| `hirr` | `PhiIrreducible data`, from `phiIrreducible_of_splits` |
| `hswap` | `data.Φ.eval₂ (evalAtJqN ℓ) jq = 0` — the datum vanishes at `(j(q ^ ℓ), j(q))`, the transposed evaluation, from `eval_swap_eq_zero_of_splits` |
| `h0top` | the constant term of `Φ(j(q), Y)` has pole order exactly `ψ(ℓ)`, with residue `1` |
| `h0le` | its deeper coefficients vanish — pole order at most `ψ(ℓ)` |
| `hk` | for `k ≠ 0`, the coefficients of `Φ.coeff k` at `j(q)` vanish from `q ^ (-ψ(ℓ))` down — pole order at most `ψ(ℓ) - 1`, one step sharper than `h0le` |
| `h0monic`, `h0deg` | `(data.Φ.coeff 0).Monic`, of degree `ψ(ℓ)` — the constant term read as a polynomial in `X` |
| `hTmonic`, `hTdeg` | `swapBivar data.Φ` is monic of degree `ψ(ℓ)`, from §1's `swapBivar_monic_of_coeff_bounds` |
| `hTmonicGen`, `hTdegGen` | the same two facts after `.map evalAtJGen` |
| `hTeq` | `swapBivar data.Φ = data.Φ` |

## 5. Where the three bounds come from

`h0top` and `hk` read the descent off `hc` itself: `← coeff_coeffEmb_qExpand` moves
the coefficient of `c k` at `m` to the coefficient of its level image at `ℓ * m`,
`← hc k` names that image as `(phiProd …).coeff k`, and T10's
`phiProd_conj_coeff_zero_lead` / `phiProd_conj_coeff_eq_zero_of_le` supply the
coefficient. `h0le` is `hc.poleOrderLE` directly.

The two pole bounds differ by one order, and that is what the transpose needs. The
product's constant term has pole order `ℓ * ℓ + ℓ`, every higher coefficient
`ℓ * ℓ + ℓ - 1`; the descent divides exponents by `ℓ`, so `c 0` has order at most
`ψ(ℓ)` (`h0le`, from `hc.poleOrderLE`) while `c k` for `k ≠ 0` has order at most
`ψ(ℓ) - 1` (`hk`, from T10's `phiProd_conj_coeff_eq_zero_of_le`). The non-strict
bound would give `degree ≤ ψ(ℓ)` for the higher coefficients, and
`swapBivar_monic_of_coeff_bounds` needs `<`; with the sharp bound the constant term
is the strict leading term, which is exactly `h0top`'s residue at the top exponent.

The exponent rescale `ℓ * (-(ℓ + 1)) = -(ℓ * ℓ + ℓ)` is the one arithmetic step, and
it is the level substitution: the product's constant term has pole order
`ℓ * ℓ + ℓ`, and the descent `q ↦ q ^ ℓ` divides it by `ℓ`, leaving the
`ψ(ℓ) = ℓ + 1` of the descended family. That equality of the pole order with the
degree in `Y` is why the constant term carries the transposed polynomial's leading
coefficient.

## 6. Why symmetry closes

| step | fact |
|---|---|
| the datum's minimal polynomial | `minpoly ℚ(j(q)) (j(q ^ ℓ)) = data.toAdjoin`, from `minpoly_jqN_eq` and irreducibility |
| the transpose is a root | `aeval (jqN ℓ) ((swapBivar Φ).map evalAtJGen) = 0`, from `aeval_jqN_transposeToAdjoin` and the vanishing of the datum at `(j(q ^ ℓ), j(q))`: the same vanishing with the two slots swapped |
| hence divisible | `data.toAdjoin ∣ (swapBivar Φ).map evalAtJGen` |
| and equal | both sides are monic of degree `ψ(ℓ)`, so `Polynomial.eq_of_monic_of_dvd_of_natDegree_le` gives the equality in `ℚ(j(q))[Y]` |
| transport down | `Polynomial.map_injective evalAtJGen evalAtJGen_injective` turns it into `swapBivar Φ = Φ` over `ℤ[X][Y]` |
| read as symmetry | `evalSymm_of_swapBivar_eq` converts the transpose identity into `EvalSymm Φ` |

The degree comparison is the only place the two normalizations must agree:
`data.toAdjoin` has degree `ψ(ℓ)` because `Φ` is monic of that degree in `Y`, and the
transpose has `ψ(ℓ)` by §1.

## 7. What comes from the block

| name | use here |
|---|---|
| `phiIrreducible_of_splits` | irreducibility of the datum, from its splitting |
| `eval_swap_eq_zero_of_splits` | the transposed evaluation `Φ(j(q ^ ℓ), j(q)) = 0`, read off the splitting through the level embedding `qEmbedT` |
| `ModularPolynomialData.minpoly_jqN_eq` | `data.toAdjoin` is the minimal polynomial of `j(q ^ ℓ)` |
| `evalAtJGen_injective` | injectivity of the evaluation into `ℚ(j(q))`, which transports the final equality down to `ℤ[X][Y]` |

Those four are the block's irreducibility half; its transpose engine is §1, in this
module, and its notation is [`ModularPolynomialIrreducible.md`](ModularPolynomialIrreducible.md).
