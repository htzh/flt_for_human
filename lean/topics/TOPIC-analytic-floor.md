# The analytic floor: the q-expansion principle and the j-line membership

**Status: live support.** Four modules under `FLTForHuman/ModularForms/` supply the only analytic
input the modular-equation argument needs. They are shared by both theories: theory A's `Existence`
consumes the membership lemma, and the level tower's field statements consume the same floor. The
mathematics is [base/013](../../base/013-riemann-existence-and-the-q-expansion-principle.md) and
[base/004 §4](../../base/004-the-j-invariant.md).

The modules have no dictionary; their headers carry the API. This file says what each one is for and
how they stack.

## 1. The constancy kernel — `ModularForms/QExpansionPrinciple`

A holomorphic `SL₂(ℤ)`-invariant `q`-series is constant: if `F : ℍ → ℂ` is presented everywhere by a
power series `∑_{m ≥ 0} c_m q(τ)^m` and is invariant under `SL₂(ℤ)`, then `c_m = 0` for every
`m ≠ 0`.

The analytic content is mathlib's `ModularForm.eq_const_of_weight_zero`; the module is the
bookkeeping that turns a `HasSum` on `ℍ` into a weight-zero level-one modular form. Its headline is
`coeff_eq_zero_of_hasSum_of_slash_invariant`, and it is the *only* genuinely analytic input of the
whole modular-equation development — in particular, the level-one principle suffices and the level-`N`
one is never needed.

## 2. The analytic model of `j` — `ModularForms/JqAnalyticModel`

The formal `jq` of `Defs/Jq` is a `PowerSeries` built from `eisenstein4`, `etaProd` and an
`invOfUnit`; this module is the bridge to mathlib's analytic `ModularForm.E₄` and
`ModularForm.discriminant`. For every `τ : ℍ` the series `jq` sums coefficient by coefficient to
`E₄(τ)^3 / Δ(τ)`, and that model is `SL₂(ℤ)`-invariant.

`hasSum_jq_qParam` is the realization hypothesis the next module consumes; the `q ·` version
`hasSum_jNum_qParam` stays private because its only consumer is `hasSum_jq_qParam` itself.

## 3. The Hauptmodul form — `ModularForms/Hauptmodul`

A pole-bounded, realized, `SL₂(ℤ)`-invariant Laurent series is a polynomial in `jq`. This is the
application of the kernel to the holomorphic remainder: subtract the polynomial in `j` that matches
the pole, using the triangularity of `j`'s powers, and the difference is a holomorphic invariant
`q`-series, hence constant.

The pieces, in reading order:

* `hasSum_qParam_mul` and `hasSum_qParam_mul_laurent` — products of power-series `q`-expansions on
  `ℍ` (the Cauchy product, then the Laurent case via `single_mul` and an order split);
* `exists_aeval_jq_sub_holomorphicAtInfty` — pole killing, i.e. the triangularity of `j`'s powers;
* `mem_adjoin_jq_of_hasSum_of_slash_invariant` — the headline: the series lies in `ℚ[jq]`.

This is the "Hauptmodul" property in the form the cone uses: not that `j` generates the function
field, but that every modular function holomorphic on `ℍ` with a bounded pole at the cusp *is* a
polynomial in `j` of that degree.

## 4. The j-line membership of the descended coefficients — `ModularForms/PhiGenDescends`

The application the three modules above were isolated for. The descended coefficients `c k` of the
conjugate product must lie in `ℚ[jq]`; the obstruction is that they are only `Γ₀(ℓ)`-invariant, while
the Hauptmodul form needs `SL₂(ℤ)`-invariance.

The fix is the Hecke-coset construction: for an invariant function `F`, the coset polynomial
`(X - F(ℓτ)) · ∏_{b < ℓ} (X - F((τ + b)/ℓ))` is invariant, and its coefficients are realized by the
Hecke translates of `jq`. Then the Hauptmodul form puts each coefficient in `ℚ[jq]`. This is why the
level-one q-expansion principle is enough.

The module's exported surface is `hasSum_coeff_of_phiGenDescends` and
`mem_adjoin_jq_of_phiGenDescends`; the second is what theory A's `Construction` imports to build
`exists_modularPolynomialData_splits`, which `Existence` consumes, and what the level tower will use
for its field statements.

## 5. Where this sits in the code

```
ModularForms/PhiGenDescends        the membership: c k ∈ ℚ[jq]
  ├── ModularForms/Hauptmodul      pole-bounded invariant Laurent series = polynomial in jq
  │     ├── ModularForms/JqAnalyticModel    jq = E₄³/Δ on ℍ, SL₂(ℤ)-invariant
  │     └── ModularForms/QExpansionPrinciple   holomorphic invariant q-series is constant
  └── ModularForms/Defs/Hecke*, HeckeQExpansion          (the Hecke-coset machinery)
```

Nothing above depends on the modular polynomial: this floor can be read, used and maintained without
theory A or theory B. That is why it is support and not part of either theory.

## 6. A note on the deleted plan files

Three porting topics in the old `topics/phiGenSplitting/` directory (`TOPIC-hauptmodul`,
`TOPIC-jq-model`, `TOPIC-r1-kernel`) described these modules as executed plans, with build discipline,
pin provenance and cost logs. They were deleted together with the theory-A porting topics because they
are process records, not mathematics; this file replaces the mathematical content. The originals are in
git at `94d9a89^` if a process record is ever wanted again.
