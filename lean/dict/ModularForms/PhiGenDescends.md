# `ModularForms/PhiGenDescends` — the analytic-input dictionary

One entry for T8 and its cone. The difficulty of this module is not any single name but the
**translation scheme** it threads: one object is written as a `q`-series over `ℚ`, over `ℚ(ζ_ℓ)` and
over `ℂ`, and as a function on `ℍ`; at period `1` and at period `ℓ`; with a polynomial index and with a
`q`-exponent. What follows is the map of that scheme — carriers, maps, periods, the two labellings of
the Hecke cosets, the exponent discipline, which `have` in the proof stands for which position, the
shorthand dialect the consumers of this module use for the same objects (§10), and — because almost
none of the cone is original mathematics — which imported theorem does which work (§11).

The mathematics: [base/013 §5, §5.5](../../../base/013-riemann-existence-and-the-q-expansion-principle.md)
(the level-one `q`-expansion principle and what it consumes) and
[base/014 §4](../../../base/014-hecke-operators.md) (the analytic face of the Hecke action and the
coset polynomial). The theory this is the analytic input *for*:
[TOPIC-modular-equation](../../topics/TOPIC-modular-equation.md) §2.1; the floor's own shape:
[TOPIC-analytic-floor](../../topics/TOPIC-analytic-floor.md).

## 1. The carriers

| carrier | Lean type | what lives there |
|---|---|---|
| `ℚ((q))` | `LaurentSeries ℚ` | `jq`, the descended family `c k`, and `f` in T7's headline |
| `K((q))`, `K = ℚ(ζ_ℓ)` | `LaurentSeries (CyclotomicField ℓ ℚ)` | `coeffEmb K jq`, the conjugates `PhiGen.conj i`, the product `phiProd ℓ (conj ℓ ζ)`, and the descent hypothesis `hc` |
| `ℂ((q))` | `LaurentSeries ℂ` | `jqC`, `conjC i`, `castC`-images, and the coefficients of the coset polynomial |
| `ℂ[X]` over `ℂ((q))` | `Polynomial (LaurentSeries ℂ)` | `phiProdC` (private: the σ-image of `phiProd`), i.e. the coset polynomial `∏ i, (X - C (conjC i))` — a polynomial whose *coefficients are series* |
| `ℂ[X]` over `ℂ` | `Polynomial ℂ` | the same shape with every coefficient series evaluated at a point of `ℍ`: `∏ i, (X - C (jt (rep i • τ)))` — a polynomial whose coefficients are numbers |
| functions `ℍ → ℂ` | `UpperHalfPlane → ℂ` | `jt`, the Hecke translates `jt ∘ (rep i • ·)`, and the coset polynomial's `k`-th coefficient as a function of `τ` |

The passage between the last two rows is `RealL.coeff_prod_X_sub_C`, and it is the only place where
a *polynomial over series* becomes a *polynomial over numbers*: for each `i`, a realization of the
series `conjC i` by the number `jt (rep i • τ)` gives a realization of the product's `k`-th coefficient
by the product's `k`-th coefficient at `τ`. Nothing else in the cone evaluates a coefficient at a
point.

`ℚ[j(q)]` is the subalgebra `Algebra.adjoin ℚ {jq}` (`adjoinJq` in `Defs/PhiGen.lean`); it appears
here only as the *target* of the conclusion `c k ∈ Algebra.adjoin ℚ {jq}`, never inside the analytic
part.

## 2. The maps

Every map in the table is a `→+*`; the τ-side has no ring maps, only `jt` and the action `•`.

| map | source → target | action |
|---|---|---|
| `coeffMap f` | `R((q)) → S((q))` | coefficients through `f`, `q`-exponent untouched: `coeffMap_coeff` is `rfl` |
| `coeffEmb L` | `ℚ((q)) → L((q))` | `coeffMap (algebraMap ℚ L)` — the base field moving up |
| `castC` | `ℚ →+* ℂ` | `Rat.castHom ℂ`; the coefficient map of `jqC` |
| `sigma ℓ ζ hζ` | `K →+* ℂ` | the embedding `ζ ↦ expRoot ℓ` (`sigma_zeta`), fixing `ℚ` (`sigma_ratCast'`) |
| `qExpand R N` | `R((q)) → R((q))` | `q ↦ q ^ N`: coefficient `m` moves to `N * m` (`qExpand_coeff_mul`), and vanishes elsewhere (`qExpand_coeff_of_not_dvd`) |
| `qTwist u` | `R((q)) → R((q))` | `q ↦ u * q`: coefficient `m` is multiplied by `u ^ m` (`qTwist_coeff`) |
| `cosetSubst ζ a b` | `R((q)) → R((q))` | `(qExpand R (a * a)).comp (qTwist (ζ ^ (a * b)))` — the conjugate family's uniform spelling |

Three identities collapse the spellings, and they are exactly the three the descent pushes through:

- `coeffMap_qExpand`: extending coefficients and substituting `q ↦ q ^ N` commute. The descent's
  right-hand side is written as `coeffEmb K (qExpand ℚ ℓ (c k))`, so the two orders of the two maps
  never have to be reconciled by hand.
- `coeffMap_qTwist`: the same for a twist, up to matching units (`(v : S) = σ (u : R)`).
- `coeffMap_sigma_coeffEmb` (private): `sigma` composed with `coeffEmb K` is `coeffMap castC`, because
  `sigma` fixes `ℚ`. This is the identity that makes the *cyclotomic* descent and the *complex*
  realization comparable, and in the inlined proof it is one step of the `rw` chain.

## 3. The periods, and what is stated at which one

The nome is `Function.Periodic.qParam h τ = exp (2 * π * I * τ / h)` — `h` is a **period in `τ`**, so
`qParam 1` is the standard `q = e^{2πiτ}` and `qParam ℓ` is the ℓ-th root nome `e^{2πiτ/ℓ}`. It is
periodic in `τ` with period `h` (read back as `z + m * h` by `qParam_left_inv_mod_period`) and never
zero (`qParam_ne_zero`). Three local notations spell it: `𝕢 h` here, in `HeckeQExpansion` and in
`Hauptmodul`; `qParam 1` where the argument is explicit.

`RealL` (public, `ModularForms/Hauptmodul.lean`) is the packaged statement, and `HasSum` is the same
at one point:

| name | form |
|---|---|
| `RealL h A F` | `∀ τ : ℍ, HasSum (fun m : ℤ => A.coeff m * 𝕢 h (τ : ℂ) ^ m) (F τ)` |
| a `HasSum` hypothesis | the same at a fixed `τ`; the pin wrapper's spelling, which `RealL` recovers definitionally |

The general rule for changing the period is one exponent identity, `q_h ^ N = q_(h/N)`:

    RealL h (qExpand R N x) F   ⟺   RealL (h / N) x F

Two instances occur, and they are different:

| instance | `h` | `N` | result | where |
|---|---|---|---|---|
| the descent's drop | `ℓ` | `ℓ` | `RealL 1 x F` — a level-one reading | `realL_one_of_realL_qExpand` |
| the diagonal translate | `ℓ` | `ℓ * ℓ` | `RealL (1/ℓ) x F` — *not* level one | `realL_conjC_zero`, via `heckeDiagMatrix` |

So the drop lemma works precisely because the descent's expansion exponent equals the Hecke period.
The reverse direction, `realL_qExpand_of_realL_one`, exists too
(`ModularCurve/Analytic/Gamma0InvariantCore.lean`); it is the same reindexing, and neither direction
proves a new convergence statement.

Which statement sits at which period:

| statement | series | period | realized by |
|---|---|---|---|
| `hasSum_jq_qParam` | `jqC`'s coefficients | `1` | `E₄ τ ^ 3 / Δ τ` |
| `realL_jqC` | `jqC` | `1` | `jt` |
| `hasSum_qParam_heckeDiagMatrix_smul` | `qExpand ℂ (ℓ * ℓ) jqC` | `ℓ` | `jt (ℓτ)` |
| `hasSum_qParam_heckeMatrix_smul b` | `e^{2πibm/ℓ} · jqC(m)` | `ℓ` | `jt ((τ + b)/ℓ)` |
| `realL_conjC_zero` | `conjC 0` (`= qExpand ℂ (ℓ * ℓ) jqC`) | `ℓ` | `jt ∘ heckeDiagMatrix` |
| `realL_conjC_succ b` | `conjC (b + 1)` (`= σ`-image of `qTwist (ζ ^ b) jq`) | `ℓ` | `jt ∘ heckeMatrix ℓ b` |
| `realL_phiProd_coeff k` | `(phiProdC).coeff k` | `ℓ` | the coset polynomial at `τ` |
| `hreal` in the headline | `c k` | `1` | `F`, the coset polynomial's `k`-th coefficient |

## 4. The Hecke side: matrices, cosets, roots

| object | Lean | reading |
|---|---|---|
| `heckeMatrix p j` | `!![1, j; 0, p]`, `det = p` | `τ ↦ (τ + j)/p` |
| `heckeDiagMatrix p` | `!![p, 0; 0, 1]`, `det = p` | `τ ↦ pτ` |
| `upperTriangularGL a b d` | `!![a, b; 0, d]` | the common constructor; the two above are its cases |
| `mapGL ℝ g` | `SL(2,ℤ) → GL(2,ℝ)` | how an `SL₂(ℤ)` element acts: the `MulAction` is `compHom` along `mapGL` |
| `rep ℓ i` | `Fin (ℓ + 1) → GL(2,ℝ)` | `Fin.cases (heckeDiagMatrix ℓ) (fun b => heckeMatrix ℓ (b : ℕ)) i` — the `ℓ + 1` coset representatives, diagonal slot first |
| `heckeRep p x` | `OnePoint (ZMod p) → GL(2,ℝ)` | the same family labelled by `ℙ¹(𝔽_p)`: `heckeRep p ∞ = heckeDiagMatrix p`, `heckeRep p (j : ZMod p) = heckeMatrix p j.val` |
| `redMatrix p g` | `SL(2,ℤ) → GL(2, ZMod p)` | the action of `g` on `ℙ¹(𝔽_p)`, given explicitly as `!![g 1 1, g 0 1; g 1 0, g 0 0]` |
| `heckeRep_mul` | commutation | for `g ∈ Γ₀(N)` with `¬ p ∣ N`: `heckeRep p x * mapGL ℝ g = mapGL ℝ g' * heckeRep p (redMatrix p g • x)`, for an explicit `g'` with `(N : ℤ) ∣ g' 1 0` (the statement also carries a `wt`-congruence, unused here) |

The same `ℓ + 1` cosets carry two labellings, and each reindexing has a name:

| labelling | used for | reindexing |
|---|---|---|
| `Fin (ℓ + 1)` (`rep`, `rep_zero`, `rep_succ`) | the product and its coefficients, on both sides of `RealL` | `Fin.prod_univ_succ` + `rep_zero`/`rep_succ` splits diagonal slot from the `ℓ` translates |
| `ℙ¹(𝔽_ℓ)` (`heckeRep`, `redMatrix`) | `SL₂(ℤ)`-invariance of the coset polynomial | `cosetPoly_eq_prod_onePoint`, then `Equiv.prod_comp` along `MulAction.toPerm (redMatrix γ)` |

`apply_heckeRep_smul_smul` (private) is the bridge: it moves `γ` across a coset representative by
`heckeRep_mul` instantiated at `N = 1`, and it is the only place the general-`N` form of that
statement is used.

Roots of unity, and the two spellings of one number:

| object | Lean | reading |
|---|---|---|
| `ζ` | `(CyclotomicField ℓ ℚ)ˣ` with `hζ : IsPrimitiveRoot (ζ : K) ℓ` | the abstract primitive root in `K` |
| `expRoot ℓ` | `Complex.exp (2 * π * I / ℓ)` | the same root in `ℂ` (`isPrimitiveRoot_expRoot`) |
| `sigma ℓ ζ hζ` | `K →+* ℂ` | the embedding matching them: `sigma ζ = expRoot ℓ` (`sigma_zeta`) |
| twist exponent | `Complex.exp (2 * π * I * b * m / ℓ)` | the coefficient twist at index `m`, i.e. `sigma (ζ ^ b) ^ m` (`expRoot_pow_zpow`) |

## 5. One number in several positions

The descent and the realization meet at a single rational number, seen in four places. This is the
index discipline the proof actually runs on.

| position | Lean | type |
|---|---|---|
| the polynomial index | `(…).coeff k` | `k : ℕ` — the `X`-degree, unchanged by every map above |
| the `q`-exponent in `K` | `((phiProd …).coeff k).coeff (ℓ * m)` | `ℓ * m : ℤ` — the descent's expansion |
| the `q`-exponent in `ℚ` | `(c k).coeff m` | `m : ℤ` — after the level drop |
| the `q`-exponent at `τ` | the summand at `m` in `hreal` | `m : ℤ`, with nome `qParam 1` |

`hc k` is the statement that rows 2 and 3 are the same number in two rings: `coeffEmb K` applied to
the level-`ℓ` expansion of `c k`. `PhiGenDescends` is exactly that identity, for all `k`.

`PoleOrderLE f n` is the vanishing condition on row 3 (`k < -(n : ℤ) → f.coeff k = 0`); it is
generic in the coefficient type, and every Laurent series has such a bound by well-orderedness of its
support (`exists_poleOrderLE`) — which is why no statement in the cone carries a pole bound as a
hypothesis. `TPoleOrderLE` is the pin's `K`-side spelling of the same predicate
(`tPoleOrderLE_iff_poleOrderLE` is `Iff.rfl`), and it is what `phiProd`'s coefficient bounds are
stated in.

## 6. The T7 interface, and how the headline fills it

`mem_adjoin_jq_of_hasSum_of_slash_invariant f F hF hinv : f ∈ Algebra.adjoin ℚ {jq}` takes exactly
two hypotheses:

| hypothesis | statement | where it comes from here |
|---|---|---|
| `hF` | `RealL 1 (coeffEmb ℂ f) F` — the realization at period `1`, `ℤ`-indexed, **no pole bound**; unfolding it gives `∀ τ, HasSum (fun m : ℤ => ↑(f.coeff m) * 𝕢 1 τ ^ m) (F τ)` | `hreal`, the `have` in the headline |
| `hinv` | `∀ γ τ, F (γ • τ) = F τ` — `SL₂(ℤ)`-invariance on `ℍ` | `cosetPoly_smul ℓ hℓ.out jt jt_smul γ τ`, applied under `coeff k` |

The pole bound is not a hypothesis: T7 recovers it from `f`'s own order, then applies
`exists_aeval_jq_sub_holomorphicAtInfty` (subtract the polynomial in `jq` matching the pole,
triangularity via `poleOrderLE_aeval_jq`) and `coeff_eq_zero_of_hasSum_of_slash_invariant` — a
convergent invariant `q`-series with no negative part and no constant term is zero. That kernel is
stated for a `ℕ`-indexed power series (`c : ℕ → ℂ`), not for a `RealL`; the passage between the
two indices is `hasSum_powerSeries_of_laurent` (`JqAnalyticModel`), the mirror of
`hasSum_laurent_of_powerSeries`, and it is the only place in the cone where the `ℤ`-index and the
`ℕ`-index meet.

`mem_adjoin_jq_of_phiGenDescends` fixes `f := c k` and `F := fun τ => (coset polynomial in
jt (rep i • τ)).coeff k`, so the two hypotheses are supplied independently and the theorem is exactly
"realization + invariance ⇒ membership".

## 7. Where the convergence comes from

`RealL` is a `Prop`, so every `RealL` fact is either proved or transported. The cone has **one seed and
one closure**, and everything else in the chain is a converter:

| kind | name | note |
|---|---|---|
| seed | `hasSum_jq_qParam`, read as `realL_jqC : RealL 1 jqC jt` | the only place a series is summed for the first time: `E₄³/Δ = ∑ jq(m) q^m` on `ℍ`; its anatomy is §11 |
| product closure | `hasSum_qParam_mul`, `hasSum_qParam_mul_laurent`, `RealL.mul`, `RealL.prod`, `RealL.coeff_prod_X_sub_C` | genuinely new convergence: Cauchy product of two-sided series, side condition `0 < h` |
| algebraic closure | `RealL.add`, `neg`, `sub`, `C`, `single`, `one`, `zero`, `aeval` | sums, differences, constants, polynomial substitution; no new analysis. `aeval` is the general form of the pin's `jq`-specific `realL_aeval_jq`: it takes `P` and a realization of the series, and returns the realization of `P` of it |
| transport | `hasSum_qParam_heckeMatrix_smul`, `hasSum_qParam_heckeDiagMatrix_smul`, `realL_one_of_realL_qExpand`, `realL_qExpand_of_realL_one` | the summands are the same terms reindexed, closed by `hA _` or `hinj.hasSum_iff` |
| algebra only | `map_phiProd`, `coeffMap_qExpand`, `coeffMap_sigma_coeffEmb` | ring hom bookkeeping |
| the other analysis | `coeff_eq_zero_of_hasSum_of_slash_invariant` | on T7's side of the interface, not in the production chain |

The positivity `0 < ℓ` first used in the cone is the side condition of the product closure
(`RealL.coeff_prod_X_sub_C (by exact_mod_cast hℓ.out.pos) …`); the primality of `ℓ` is used only for
the arithmetic of the cyclotomic level and the index count.

## 8. The names in the headline

The realization is a `have` inside `mem_adjoin_jq_of_phiGenDescends`, so these are proof-local names:

| name | fact |
|---|---|
| `F`, `hF` | the coset polynomial's `k`-th coefficient as a function of `τ` (`set` from its expression; `hF` is the resulting equation, used to rewrite `F` in the invariance step) |
| `hreal` | `RealL 1 (coeffEmb ℂ (c k)) F` — the period-`1` realization T7's headline consumes |
| `h` | `RealL ℓ ((phiProdC).coeff k)` realized by the coset polynomial (`realL_phiProd_coeff`); after the four-step `rw` chain it is the same fact at `qExpand ℂ ℓ (coeffMap castC (c k))` |
| `h'` | `h` after `realL_one_of_realL_qExpand` and the `Fin (ℓ + 1)` split: the period-`1` statement at a point |
| `hc k` | the descent: `(phiProd …).coeff k = coeffEmb K (qExpand ℚ ℓ (c k))` |
| `γ`, `τ` | the `SL₂(ℤ)`-invariance step, `cosetPoly_smul` under `Polynomial.coeff k` |

## 9. Look-alikes

| pair | the one fact that separates them |
|---|---|
| `jq` / `jt` | the formal series in `ℚ((q))` / its analytic model `E₄³/Δ` on `ℍ`; `realL_jqC` is the bridge |
| `jqC` / `coeffMap castC jq` | the same series, the second spelling exposing the coefficient map |
| `phiProdC` / `(PhiGen.phiProd ℓ (PhiGen.conj ℓ ζ)).map (coeffMap σ)` | the name / the term it abbreviates; `map_phiProd` moves between `phiProdC` and the product of `X - C (conjC i)` |
| `conjC i` / `PhiGen.conj i` | the `ℂ` image along `sigma` / the `K`-series; related by `coeffMap` |
| `RealL h A F` / `HasSum … (F τ)` | the `∀ τ` closure / the same at one point |
| `F` in the headline / `F` in `RealL h A F` | the `set`-name for the coset polynomial's coefficient / the realized function of the predicate; the headline's is proof-local and is the one T7 receives |
| `qParam 1` / `qParam ℓ` | standard nome / ℓ-th root nome; `q_ℓ ^ ℓ = q_1` is the identity that drops the period |
| `qExpand` / `qTwist` | the `q`-*exponent* moves / the coefficient is *multiplied* by `u ^ m`; `cosetSubst` is one of each |
| `qExpand ℂ (ℓ * ℓ)` / `qExpand ℂ ℓ` | the diagonal translate's expansion / the descent's expansion; only the second matches the period `ℓ` and drops to `1` |
| `heckeDiagMatrix` / `heckeMatrix` | `τ ↦ ℓτ` / `τ ↦ (τ + b)/ℓ`; the two cases of `rep` and of `heckeRep` |
| `rep` / `heckeRep` | the same `ℓ + 1` matrices indexed by `Fin (ℓ + 1)` / by `ℙ¹(𝔽_ℓ)` |
| `PoleOrderLE` / `TPoleOrderLE` | the same predicate (the pin's two spellings, related by `Iff.rfl`): the bound T7's interface uses over `ℚ((q))` / the one the descent's coefficient bounds use over `K((q))` |
| `sigma` / `castC` | the cyclotomic embedding, which moves `ζ` / the rational embedding; equal on `ℚ` (`coeffMap_sigma_coeffEmb`) |
| `ζ` / `expRoot ℓ` | the abstract root of unity in `K` / its image `e^{2πi/ℓ}` in `ℂ`; matched by `sigma` |
| `𝕢 1` / `qParam 1` | local notation / the name it abbreviates, in three modules |
| `ℓ` | several jobs at one value: the coset count (`ℓ + 1`), the translate denominator, the twist order (`ζ ^ ℓ = 1`), the expansion exponent, the nome's period, and the cyclotomic level `K = ℚ(ζ_ℓ)` |

## 10. The consumers' shorthand dialect

This module is upstream of the modules that reuse the same mathematics, so it must spell the objects
out; those modules have names for them. Where a reader meets one of the long spellings here — the
σ-image of the conjugate product's coefficient is the extreme case — this is the other spelling:

| here | consumer shorthand | defined in |
|---|---|---|
| `coeffEmb K (qExpand ℚ ℓ x)` | `qEmbedT K ℓ x`; `iota x`; `qExpAlg ℓ x` | `ModularEquation/Support/LevelEmbedding.lean`, `Analytic/Gamma0InvariantCore.lean:635`, `Defs/Laurent.lean:509` |
| `phiProdC` (the σ-image of `phiProd`) | `conjK ℓ ζ f g`, `interpK ℓ ζ f g`; per factor `map_coeffMap_phiProd` (`phiProd ℓ (conj ℓ (σ ζ))`) and `coeffMap_X_sub_C_conj` | `Analytic/Gamma0InvariantCore.lean:257`, `ModularEquation/Split.lean:155` (private), `Support/Permutation.lean:259` |
| `(p.map (coeffMap σ)).coeff k` | `coeffMap σ (p.coeff k)` — the consumers keep the coefficient outside the `map`, via `Polynomial.coeff_map` | everywhere downstream |
| `∏ i : Fin (ℓ + 1), (X - C (H i))` (the shape of `phiProd`) | `conjPoly H` (`Gamma0InvariantCore:98`) | `Analytic/Gamma0InvariantCore.lean` |
| `∏ i, (X - C (jt (rep ℓ i • τ)))` | `conjPoly (fun i => slotJ ℓ i τ)`, the polynomial behind `conjFun ℓ F k` (`:551`) | same |
| `rep ℓ i`, a `GL(2,ℝ)` matrix | `cosetRep ℓ i`, an `SL(2,ℤ)` element (`cosetRep 0 = 1`, `cosetRep (b + 1) = S * T ^ b`), with `jtN τ = jt (heckeDiagMatrix ℓ • τ)` and `slotF`/`slotJ` | same, `:446`–`:457` |
| `realL_conjC i` | `realL_conj`, `realL_slotH` | same |
| `realL_phiProd_coeff` | `RealL.conjPoly_coeff`; weighted variant `RealL.interpPoly_coeff` (`interpPoly H Y = ∑ i, C (H i) * ∏ m ≠ i, (X - C (Y m))`) | same, `:341`, `:323` |
| `map_phiProd` | `interpPoly_map`, `conjPoly_map` | same, `:106`, `:111` |
| `Equiv.prod_comp` inside `cosetPoly_smul'` | `interpPoly_perm`, `conjPoly_perm` | same, `:116`, `:125` |
| `sigma ℓ ζ hζ` (constructed from `hζ`) | a variable `σ : K →+* ℂ` with `hσ : σ ζ = expRoot ℓ` | the module's assembly section |
| `mem_adjoin_jq_of_phiGenDescends` | `mem_adjoin_of_conjK_coeff_eq` / `mem_adjoin_of_interpK_coeff_eq` — the same conclusion from one coefficient hypothesis `(conjK …).coeff k = coeffEmb K (qExpand ℚ ℓ ξ)` | same, `:595`, `:610` |
| `PhiGenDescends ℓ ζ c` | that hypothesis for every `k`, with `ξ` the corresponding `c k` | — |

One difference survives the translation, and it is the one a reader will otherwise take for a
definitional equality: the consumer's root family is `slotH ℓ ζ f g` (the level-one weight `f` at slot
`0`, the twisted `g` elsewhere), not `PhiGen.conj`, so the slot-`0` expansion exponents differ —
`qExpand ℚ ℓ` there (`f(τ)`), `qExpand ℚ (ℓ * ℓ)` here (`j(ℓτ)`, the cusp of `X₀(ℓ)`). Hence
`conjK jq jq ≠ phiProd (PhiGen.conj ℓ ζ)`; only the `b + 1` slots agree, and the correspondence is
shape by shape. The consumer's `interpPoly` is the Lagrange generalization of the plain product that
`phiProd` is.

Since those modules import this one, none of their names can be used here: the translation is one way.

## 11. Provenance: which imported theorem does which work

The cone is mostly adaptation, so this is the section that saves a reader from mistaking glue for
mathematics. For each fact the cone consumes, the theorem that states it, and whose proof it is.

### 11.1 The seed's anatomy

`hasSum_jq_qParam` is `Σ jq(m) q^m = E₄³/Δ` on `ℍ`, in two halves — coefficients (rows 1-3) and
convergence (row 4) — then shifted by `q⁻¹` and reindexed `ℕ → ℤ` (row 5). Rows 1-3 and 4 are `have`s
inside its own proof (named `hcoeff` and `hnum`), not separate declarations, so the chain is readable
in one place.

| fact | Lean theorem | whose work |
|---|---|---|
| `qExpansion 1 E₄ = eisenstein4.map cast` | `qExpansion_E4_eq_map_eisenstein4` (`JqAnalyticModel`) | **mathlib**: `EisensteinSeries.E_qExpansion_coeff` — cotangent partial fractions give `-(2k/B_k) σ (k-1) m`; the port instantiates `k = 4`, `-8/B₄ = 240` |
| `qExpansion 1 Δ = X · dedekindEtaUnit.map cast` | `qExpansion_discriminant_eq_map_X_mul_dedekindEtaUnit` ← `qExpansion_discriminant_eq_X_mul_tprod` | **mathlib**: `ModularForm.discriminant_eq_q_prod` (Euler's product for `η²⁴`); the port adds the `qExpansion`-uniqueness packaging and `etaPow_eq_map_dedekindEtaUnit` |
| `qExpansion 1 (q · j) = jNum.map cast` | `hcoeff`, inlined in `hasSum_jq_qParam` | **port**: `qExpansion_mul` on `qJ * Dq = E₄³`, then cancel `dedekindEtaUnit * dedekindEtaUnitInv = 1`; this is where the lattice sum and the `ℤ`-series are shown to be one series |
| `Σ (qExpansion 1 (q·j))(m) q^m = q · j` | mathlib `UpperHalfPlane.hasSum_qExpansion` | **mathlib**: Taylor at the cusp for a periodic, holomorphic, bounded-at-`i∞` function — the only convergence input of the seed |
| `Σ jq(m) q^m = j` | `hasSum_jq_qParam` (`JqAnalyticModel`), whose convergence step is the `hnum` have; folded as `realL_jqC` (private, duplicated in `Hauptmodul` and here) | **port glue**: `hasSum_laurent_of_powerSeries`, generic in the power series — a realization of `q · F` by `A` gives one of `F` by `q⁻¹ · A` (the `ℕ → ℤ` reindex and the vanishing below `-1` live there) |

Two consequences worth stating plainly: the seed contains no pole cancellation (the pole is the
monomial `q⁻¹` in `jq`'s definition), and the `E₄` row is the only place the lattice sum appears at
all.

### 11.2 `jt`'s two borrowed properties

| fact | Lean theorem | whose work |
|---|---|---|
| `jt (γ • τ) = jt τ` | `E4_cube_div_discriminant_smul` | **mathlib**: `SlashInvariantForm.slash_action_eqn''` for the weight-4 `E₄` and the weight-12 `CuspForm.discriminant`; the port only multiplies and cancels `denom ^ 12`. Weight 4 is discharged when mathlib *builds* `E₄`: `eisensteinSeries_slash_apply` reindexes the sum along `gammaSetEquiv a γ` (change of basis on the lattice), `eisensteinSeriesSIF` closes with `Gamma_mem'`. Weight 12 by `η`'s transformation law, checked on the generators (`discriminant_S_invariant`, `discriminant_T_invariant`, `slash_action_generators_SL2Z`) |
| `jt` realizes `jq` | `hasSum_jq_qParam` | §11.1 |
| `q · jt` is bounded at `i∞`, with limit `1` | `isBoundedAtImInfty_qJ` | **port**: `qJ = E₄³ · (gfun ∘ q)⁻¹` with `gfun q = ∏ (1 - q^n)^24 → 1` |

So the two facts the cone needs from ℍ — invariance and the q-expansion — are both mathlib's, and
neither is re-derived here. `JqAnalyticModel`'s own header carries the same kind of split for its
other declarations (a `mathlib` / `ported` column), which is the place to look before hunting for the
proof of any analytic step in this cone.

### 11.3 What of `jq`'s definition is actually used

`jq` is defined arithmetically (`q⁻¹ · eisenstein4³ · Δ_unit⁻¹`). Split that into three parts and the
cone uses only the first two:

| part | what it gives | used by |
|---|---|---|
| `jNum : PowerSeries ℤ` (integrality) | the polar part of `z · jq ^ d` is integral | `intCoeffs_jq`, `intCoeffs_jq_pow`, `exists_intPoly_of_intPoleCoeffs` (`Construction`): the `ℚ[X] → ℤ[X]` upgrade, which needs the exponent-`0` coefficient too |
| constant term `1` of the unit part | the pole shape `q⁻¹(1 + O(q))` | `coeff_jq_pow_self`, `coeff_jq_pow_of_lt`, `coeff_aeval_jq_neg`, `transcendental_jq`, `exists_aeval_jq_sub_holomorphicAtInfty` — triangularity and injectivity |
| the coefficient values (`744`, `196884`, …) | nothing here | `LevelTwo` (`Φ = Φ₂`) and `ModularCurve/XH/QExpandNorm`, outside this cone |

The integrality of `IntCoeffs jq` itself is construction-level (`HahnSeries.ofPowerSeries_apply_coeff`
+ `PowerSeries.coeff_map`), not a consequence of the matching; what the matching earns is that this
`ℤ`-series *is* the q-expansion of `E₄³/Δ`, i.e. that the Fourier coefficients of `j` are integers.
