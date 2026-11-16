# `ModularForms` finiteness and integrality — the Hecke-algebra dictionary

One entry for the finiteness/integrality cluster: the vanishing and finite-dimensionality of spaces of
cusp forms (Sturm and its coefficient forms), the integral structure of the Hecke algebra
(`Module.Finite`/`Module.Free` over `ℤ`), and the integral/finiteness of the level tower. The modules
it covers are `ModularForms/{QExpansionOrder,Gamma0TwoIndex,SturmBound,HeckeFiniteAlgebra,
HeckeAlgebra,HeckeOperatorForms,HeckeQCoeff,HeckeFiniteness/{Lattice,Finiteness,Span},
WeightOne/Gamma1IntegralBasis,NebentypusEigenbasis}`,
`ModularForms/Defs/{IntegralStructure,IntegralLattice,HeckeOperator,FormalHeckeOperators}`,
`ModularCurve/HeckeInputs/Integrality.lean` and `ModularCurve/JqIntegralRatios.lean`. The operator's own
definitions are §4: the three presentations of `T_p` and the theorems that identify them.
The record of *why* the route split looks the way it does is
[studies/hecke-finiteness-coverage.md](../../../studies/hecke-finiteness-coverage.md) and
[logs/sturm-bound-port.md](../../logs/sturm-bound-port.md); this entry is only the vocabulary.

## 1. The two questions

| question | what it is | where it lives |
|---|---|---|
| **finiteness** | `q`-expansion coefficients determine a form up to a bound (Sturm), hence `S_k(Γ₀(N))` is finite-dimensional | `SturmBound.lean` |
| **integrality** | the Hecke algebra of `S_k(Γ₀(N))` is a finite, free `ℤ`-module; the level tower's inclusions are integral and finite | `HeckeFiniteness/{Lattice,Finiteness}.lean`, `HeckeFiniteAlgebra.lean`, `HeckeInputs/Integrality.lean` |

They are one cluster because both are the same statement about the coefficient map: Sturm applies it
to the **order** of a `q`-expansion, integrality applies it to the **integrality** of coefficients. A
form is pinned down by finitely many coefficients, and the integral ones span a full-rank lattice on
which Hecke acts.

## 2. Carriers

| object | Lean | reading |
|---|---|---|
| the space | `CuspForm (CongruenceSubgroup.Gamma0 N) k` | weight `k`, level `Γ₀(N)` |
| the lattice | `CuspForm.intLattice N k` | `ℤ`-span of the forms whose `q`-coefficients are all integral (`mem_intLattice_iff` is the `iff`) |
| full rank | `CuspForm.HasIntegralStructure N k` | `Submodule.span ℂ (intLattice N k) = ⊤` |
| the Hecke algebra | `CuspForm.heckeAlgebra N k S` | `Algebra.adjoin ℤ (heckeGenerators N k S) ⊆ Module.End ℂ (CuspForm (Γ₀ N) k)`; generators `T_ℓ` (`ℓ ∉ S`, `ℓ ∤ N`) and `U_q` (`q ∣ N`, `q ∉ S`) |
| the truncation | `CuspForm.qCoeffTrunc N k d` | the first `d` coefficients, as a `ℂ`-linear map to `Fin d → ℂ` |
| the bound | `sturmB N k` (private) | `(k * (Γ₀ N).index).toNat / 12` — the number of coefficients that determine a form |
| tower finiteness | `AlgebraicCurve.FiniteAlong (φ : F →ₐ[K] F')` | `Module.Finite F F'` under the algebra structure along `φ` |
| tower maps | `towerInclBar h`, `towerSubstBar ℓ h`, `heckeAlphaBar`, `heckeBetaBar` | the level inclusions and the `q ↦ q ^ ℓ` / Hecke substitutions of the modular function fields |
| integral `q`-side | `IsIntegralQExp f p` | `f`'s `q`-expansion is the image of the integral power series `p` |

## 3. The top statements

Five families. "pin" = the statement is the pin's; "port" = added by the port.

**3.1 Vanishing / Sturm**

| statement | says | status |
|---|---|---|
| `ModularForm.sturm_bound_of_isArithmetic` | for arithmetic `𝒢` with `1 ∈ 𝒢.strictPeriods`: `q`-order `> k · [𝒮ℒ : 𝒢]/12` forces `f = 0` | pin |
| `ModularForm.sturm_bound_Gamma0` | the `Γ₀(N)` coefficient form: vanishing on `n ≤ k · (Γ₀ N).index / 12` forces `f = 0` | pin |
| `ModularForm.eq_zero_of_lt_order_qExpansion_of_isArithmetic` | the general-period `M` form: order beyond `M · k · [𝒮ℒ : 𝒢]/12` forces `f = 0` | pin |
| `ModularForm.levelOne_eq_zero_of_lt_order_qExpansion` | the level-one case, from mathlib's `sturm_bound_levelOne` | pin |
| `CuspForm.eq_zero_of_qExpansion_coeff_eq_zero`, `CuspForm.Gamma0_eq_zero_of_qExpansion_coeff_eq_zero` | coefficient form: `k · [𝒮ℒ : 𝒢] < 12 d` and `d` vanishing coefficients force `f = 0` | pin (re-derived: see §5) |
| `ModularForm.S2_Gamma0_one_eq_zero`, `ModularForm.S2_Gamma0_2_eq_zero` | `S₂(Γ(1)) = 0` and `S₂(Γ₀(2)) = 0`, the bound being `⌊index/6⌋ = 0` | port |
| inputs | `CongruenceSubgroup.one_mem_strictPeriods_Gamma0`, `Subgroup.IsArithmetic.exists_nat_mem_strictPeriods_conj`, `UpperHalfPlane.qExpansion_coeff_nat_mul`, `UpperHalfPlane.qExpansion_prod`, `Gamma0_two_index_eq_three`, `coe_Gamma_one_eq_SL` | pin / port |

**3.2 Finite dimension**

```lean
CuspForm.qCoeffTrunc (N) [NeZero N] (k : ℤ) (d : ℕ) : CuspForm (Gamma0 N) k →ₗ[ℂ] (Fin d → ℂ)
scoped instance CuspForm.finiteDimensional_Gamma0 : FiniteDimensional ℂ (CuspForm (Gamma0 N) k)
theorem CuspForm.finiteDimensional_cuspForm (N) [NeZero N] (k : ℤ) :
    FiniteDimensional ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) k)
```

The instance is the pin's `scoped instance`; `finiteDimensional_cuspForm` is its published wrapper, and
both are `FiniteDimensional.of_injective` on `qCoeffTrunc` at `d` beyond the Sturm bound.

**3.3 Integral structure → finite Hecke algebra**

| statement | says |
|---|---|
| `CuspForm.mem_intLattice_of_coe_eq_heckeT`, `…heckeU`, `…mem_heckeAlgebra` | `intLattice` is preserved by `T_p`, by `U_p`, and by the whole Hecke algebra |
| `CuspForm.intLattice_fg` | the lattice is a finitely generated `ℤ`-module (truncation `trunc` at `sturmB N k + 1`, injective by Sturm) |
| `CuspForm.intLattice_free_and_finite` | it is moreover free and finite over `ℤ` |
| `CuspForm.HasIntegralStructure.eq_zero_of_forall_mem_intLattice` | full rank + vanishing on the lattice ⇒ the endomorphism is zero |
| `CuspForm.HasIntegralStructure.moduleFinite_heckeAlgebra`, `…moduleFree_heckeAlgebra` | full rank ⇒ `Module.Finite ℤ (heckeAlgebra N k S)` (and `Module.Free`), for `1 ≤ k` |
| `CuspForm.moduleFinite_heckeAlgebra` | `Module.Finite ℤ (heckeAlgebra N k S)` for **every** `k` |
| `CuspForm.moduleFinite_heckeAlgebra_two` | the `k = 2` corollary of the above |
| `CuspForm.fg_toSubmodule_heckeAlgebra` | `FG` form of the `k = 2` statement |
| `CuspForm.finrank_span_heckeAlgebra_eq_finrank` | the weight-`2` Hecke algebra's `ℂ`-span has the dimension of `S₂` |

**3.4 The level tower** (`HeckeInputs/Integrality.lean`, `FiniteAlong` form)

| statement | says |
|---|---|
| `finiteAlong_heckeAlphaBar_of_modularPolynomialData`, `finiteAlong_heckeBetaBar_of_modularPolynomialData` | the two Hecke substitutions are finite along, from `ModularPolynomialData ℓ` (the `β` case also from `EvalSymm data.Φ`) |
| `heckeAlphaBarIntegral_of_modularPolynomialData`, `heckeBetaBarIntegral_of_modularPolynomialData` | the same, integrality form |
| `…_of_prime` (four) | the general forms at `Fact ℓ.Prime`, i.e. with no datum hypothesis |
| `towerInclBar_isIntegral`, `towerSubstBar_isIntegral` | the level inclusion / substitution is integral |
| `towerInclBar_finiteAlong`, `towerSubstBar_finiteAlong` | and finite along |
| `towerInclBar_surjective_of_dvd_dvd` | the antisymmetry that turns divisibility both ways into onto |

**3.5 Integrality of the `q`-side** (`JqIntegralRatios.lean`)

`isIntegralQExp_E4`, `isIntegralQExp_e4cube`, `isIntegralQExp_delta` (the integral power series
`eisenstein4 ^ 3` and `X · dedekindEtaUnit`), `jqModC_mul_delta` and `jqModC_eq_div` (`jqModC = E₄³/Δ`
as a ratio of integral series), `jqModC_mem_intFormRatiosC`, `jqModC_eq_qExpansion_E4_cube_div_discriminant`
(the same identity analytically), `intSeriesC_eq_zero_iff`, `coeffEmb_image_intFormRatiosC`.

**3.6 Applications**

`CuspForm.exists_basis_gamma1_qCoeff_mem_adjoin_exp` (and `_of_even`), `…_mem_range_ratCast`,
`…_slash_mem_range_intCast`: bases of `S_k(Γ₁(N))` whose `q`-coefficients are integral (in `ℤ`, or in
`ℤ[ζ_N]` before slash); `CuspForm.exists_basis_hasNebentypus_qCoeff_hecke_eigen` in
`NebentypusEigenbasis.lean`: the integral eigenbasis.

## 4. The operators: three presentations, one operator

Every integrality statement of §3 is about `T_p`, and the proofs switch presentation three times. The
switches are theorems, not definitions. `T_p` itself mentions no basis of `S_k(Γ₀(N))`, no lattice and
no `q`-expansion: the arithmetic enters through the **integer matrices** of the Hecke correspondence.

**4.1 Slash / matrix form** (`Defs/HeckeOperator.lean`; surface level, `N` absent):

| Lean | reading |
|---|---|
| `heckeMatrix p j : GL (Fin 2) ℝ` | `!![1, j; 0, p]`, the substitution `τ ↦ (τ + j)/p` |
| `heckeDiagMatrix p : GL (Fin 2) ℝ` | `!![p, 0; 0, 1]`, the substitution `τ ↦ p τ` |
| `heckeU k p f` | `∑ j ∈ Finset.range p, f ∣[k] heckeMatrix p j` — the `p` cosets |
| `heckeT k p f` | `heckeU k p f + f ∣[k] heckeDiagMatrix p` — all `p + 1` cosets of the correspondence at `p` |
| `heckeU_def`, `heckeT_eq_heckeU_add`, `heckeT_def` | the definitional rewrites, `rfl` |
| `coeffHeckeT`, `coeffHeckeU` | see 4.2 |

`∣[k]` is the slash action. The two matrix families index the `p + 1` cosets of
`Γ₀(N) · diag(p,1) · Γ₀(N)`; the only choice inside the definition is the transversal `j < p`, and a
`Finset` sum is reordering-invariant. Every entry of both matrices is an integer (`1`, `j`, `0`, `p`;
`p`, `0`, `0`, `1`): that is the ℤ-model of the modular curve, and it is where the arithmetic
integrality of §3.3 comes from. The definitions are total (`p = 0` falls back to `1`), so they are only
used at `p ≠ 0`, i.e. `p.Prime`.

`hecke{T,U}` are functions `ℍ → ℂ`; they become endomorphisms of `S_k(Γ₀(N))` only once the
invariance/analytic/cusp fields are supplied (`HeckeOperatorForms.lean`), and that is where `N` and
`p ∤ N` / `p ∣ N` enter:

| Lean | reading |
|---|---|
| `CuspForm.heckeTLin k hp hpN : Module.End ℂ (CuspForm (Γ₀ N) k)` | the bundled `T_p` |
| `CuspForm.heckeULin k hpN : Module.End ℂ (CuspForm (Γ₀ N) k)` | the bundled `U_p` |
| `coe_heckeTLin_apply`, `coe_heckeULin_apply` | on the underlying function the bundled operator *is* `heckeT k p ⇑f` / `heckeU k p ⇑f` |
| `qExpansion_heckeTLin` | the weight-`2` case: `qExpansion 1` of the bundled `T_p` is `PowerSeries.heckeT p 2` of `qExpansion 1 f` |
| `heckeGenerators`, `heckeAlgebra` | the set of bundled operators and `Algebra.adjoin ℤ` of it (`HeckeAlgebra.lean`) |

**4.2 Coefficient form** (`Defs/HeckeOperator.lean`; the operator's matrix in `q`-coordinates):

| Lean | value at `n` |
|---|---|
| `ModularForm.coeffHeckeU p a n` | `a (n * p)` |
| `ModularForm.coeffHeckeT k p a n` | `a (n * p) + if p ∣ n then p ^ (k - 1) * a (n / p) else 0` |
| `coeffHeckeT_apply` | the `rfl` display of the same |

Two non-zero entries per column, of sizes `1` and `p ^ (k - 1)`: on coefficient sequences the operator
is an integral matrix, and `coeffHeckeT_int` / `coeffHeckeU_int` (`HeckeQCoeff.lean`) are exactly that
statement — `1 ≤ k` is what makes `p ^ (k - 1)` a natural-number power.

**4.3 Formal power-series form** (`Defs/FormalHeckeOperators.lean`; any `CommRing R`, weight a `ℕ`):

| Lean | reading |
|---|---|
| `PowerSeries.heckeU ℓ : R⟦X⟧ →ₗ[R] R⟦X⟧` | `coeff n ↦ coeff (ℓ * n)` |
| `PowerSeries.heckeV ℓ` | `coeff n ↦ if ℓ ∣ n then coeff (n / ℓ) else 0` — the dilation `X ^ n ↦ X ^ (n ℓ)` |
| `PowerSeries.heckeT ℓ k` | `heckeU ℓ + ℓ ^ (k - 1) • heckeV ℓ` |
| `coeff_heckeT`, `coeff_heckeU`, `coeff_heckeV` | the coefficient formulas of 4.2, same shape |
| `heckeU_heckeV` | `U` is a left inverse of `V` for `ℓ ≠ 0` |

**4.4 The bridges** (theorems; nothing here is definitional):

| statement | says | direction |
|---|---|---|
| `ModularFormClass.qCoeff_heckeT`, `…_heckeU` | `qCoeff (heckeT k p f) n = coeffHeckeT k p (qCoeff f) n` | slash → coefficient |
| `ModularFormClass.qExpansion_heckeT_eq_heckeT`, `…_heckeU_eq_heckeU` | `qExpansion 1 (heckeT k p ⇑f) = PowerSeries.heckeT p k (qExpansion 1 ⇑f)` | slash → series |
| `CuspForm.mem_intLattice_of_coe_eq_heckeT`, `…_heckeU` | integral coefficients in ⇒ integral coefficients out | coefficient → lattice |
| `CuspForm.mem_intLattice_of_mem_heckeAlgebra` | the whole algebra preserves `intLattice`, by `Algebra.adjoin_induction` (generators, `algebraMap`, `+`, `·`) | algebra → lattice |

The `qExpansion` bridge casts the weight: `ModularForm.heckeT` takes `k : ℤ`, `PowerSeries.heckeT`
takes `k : ℕ`, and the two are reconciled by `Nat.cast_sub` + `zpow_natCast` inside
`qExpansion_heckeT_eq_heckeT` — the pin's split, kept as is.

So the chain behind §3.3 reads: **slash/matrix (arithmetic) → bundled `End_ℂ` → coefficient formula →
lattice stability → `Module.Finite ℤ (heckeAlgebra N k S)`**. Each arrow is a theorem; only the first
line carries the arithmetic, and it carries it as integer matrices.

Pin provenance of the three presentations, all pinned `aa2d8b3`:
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularForm_HeckeOperator.lean>
(4.1 and 4.2), <https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularForm_HeckeOperatorForms.lean>
(the bundling), <https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_PowerSeries_FormalHeckeOperators.lean>
(4.3), <https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_CuspForm_HeckeAlgebra.lean>
(`heckeGenerators`/`heckeAlgebra`).

**4.5 What is, and is not, a basis choice.** No basis of `S_k(Γ₀(N))` occurs in any of the three
presentations, and none occurs in the finiteness proof: `Module.Finite.of_injective` is applied to
`t ↦ t restricted to intLattice N k`, and a `ℤ`-basis of the lattice is needed only to *display*
`End_ℤ(L)` as a matrix ring. What the presentations do carry is a ℤ-**structure** — integer coset
representatives (4.1), integer coefficient entries `1` and `p ^ (k - 1)` (4.2), a formula valid over any
`CommRing` (4.3). Conjugating by an arbitrary invertible linear map of `S_k(ℂ)` yields another lattice,
which is in general no longer stable under the algebra; the operator itself does not move. That asymmetry
is the content of §3.3, not a convention of presentation.

## 5. Route names

The cluster was scoped under four route names; they are **not** alternative statements, they are
alternative *proofs* of the same tops. Keeping them straight is the difference between a refactor and a
re-port.

| name | what it denotes | state in the tree |
|---|---|---|
| **A** (general) | prove `HasIntegralStructure` in all weights, then `moduleFinite_heckeAlgebra`; its cone is mostly endgame geometry (`HeckeEis`, `ModPForms`, `PeriodPair`) | not needed for the integral structure; the tops are landed by C/C′ |
| **B** (standalone `k = 2`) | FLT's 4,308-line `S_CuspForm_moduleFinite_heckeAlgebra_two.lean` | **not transcribed**; `moduleFinite_heckeAlgebra_two` is a one-line corollary |
| **C** (reusable sub-cone) | Sturm + `intLattice_fg` + `HasIntegralStructure.moduleFinite/Free_heckeAlgebra` | **this is what landed** |
| **C′** (shortcut) | the Γ₁ integral-basis statements + a trace lemma give `HasIntegralStructure` in every weight | scouted; its cone is inside the weight-one branch |
| **norm route** | FLT's `CuspForm.norm`/`normCofactor` (~300 lines) for the coefficient-form Sturm bounds | replaced: re-derived from `sturm_bound_of_isArithmetic`; the level-two instance survives only as `Reserve.ModularForms.LevelTwoCuspVanishing` |
| **Sturm route** | the coefficient-form bounds via `PowerSeries.nat_le_order` + the `relIndex = Nat.card` bridge (`rfl`) | landed in `SturmBound.lean` |

## 6. The boundary into established theory

What this cluster **consumes** and must not re-derive:

| provider | facts | note |
|---|---|---|
| mathlib modular forms | `strictPeriods`, `IsArithmetic`, `relIndex`, `index`, `qExpansion`, `PowerSeries.order`, `ModularForm.sturm_bound_levelOne`, `ModularForm.norm`, `LevelOne.DimensionFormula`, `ModularForm.norm_eq_zero_iff` | the level-one input and the index bookkeeping |
| mathlib algebra | `FiniteDimensional.of_injective`, `Module.Finite`, `Module.Free`, `Submodule.FG`, `IsIntegral`, `IsIntegralClosure`, `Algebra.adjoin` | the finiteness/integrality lemmas themselves |
| the port's **curve layer** (`AlgebraicCurve`) | `FiniteAlong`, `algebraAlong`, `isIntegral_along`, `ModularPolynomialData`, `EvalSymm`, `gens`, `modularFunctionFieldFull` | this cluster is a *consumer* of the curve layer; the tower section is the seam |
| the port's **Hecke layer** | `heckeT`, `heckeU`, `heckeTLin`, `heckeULin`, `heckeAlgebra`, `heckeGenerators`, `qCoeff` | the operators whose integrality is at issue |
| the port's **`q`-expansion hub** | `jqModC`, `IsIntegralQExp`, `intSeriesC`, `intFormRatiosC`, `eisenstein4`, `dedekindEtaUnit`, the `qExpansion_*` identifications | `JqIntegralRatios` is the seam into `ModularCurve/Defs/` |

The mathematical boundary is equally sharp: *nothing here is a new convergence or new curve theorem.*
Vanishing is `HasSum`/`order` bookkeeping on a `q`-expansion already known; integrality is
`Module.Finite` applied to an algebra whose generators are already known to preserve a lattice. A
refactor that finds itself proving analysis or geometry inside this cluster is off the boundary.

## 7. Look-alikes

| pair | the one fact that separates them |
|---|---|
| `intLattice N k` / `qIntegralSet N` | the all-weights `ℤ`-span of integral-coefficient forms / the weight-`2` set of forms with coefficients in `⊥ : Subring ℂ` (`IntegralLattice.lean`, a different pin vocabulary) |
| `HasIntegralStructure N k` / `HasIntegralBasis N` | full rank over `ℂ` of the all-weights lattice / the weight-`2` `Complex`-span of `qIntegralSet` is everything |
| `intLattice_fg` / `HasIntegralStructure` | the lattice is finitely generated / the lattice spans the space |
| Sturm **order** form / **coefficient** form | `(qExpansion 1 f).order` bound / `∀ n < d, coeff n = 0`; related by `PowerSeries.nat_le_order` |
| `sturm_bound_of_isArithmetic` / `sturm_bound_Gamma0` | arithmetic `𝒢` and a strict-period hypothesis / the `Γ₀(N)` index, which makes `1` a strict period |
| `finiteDimensional_Gamma0` ×2 | the 38-consumer sibling instance / `SturmBound.lean`'s file-local `scoped instance` with no consumer outside the file |
| `FiniteAlong φ` / `Module.Finite` | the latter under the algebra-along-`φ` instances; the tower statements are always stated in the former |
| `heckeAlphaBar`/`heckeBetaBar` / `heckeT`/`heckeU` | substitutions of the modular function fields / operators on cusp forms — same matrices, different carriers |
| `moduleFinite_heckeAlgebra_two` / route B's blob | the statement (a corollary here) / the 4,308-line pin proof (deliberately absent) |
| `qCoeff` / `qExpansion` | the coefficient of the bundled form (`ModularFormClass.qCoeff`) / the analytic series of the underlying function |
| `ModularForm.heckeT` / `PowerSeries.heckeT` | slash sums on `ℍ → ℂ` with `k : ℤ` / the formal operator on `R⟦X⟧` with `k : ℕ`; identified only by `qExpansion_heckeT_eq_heckeT` (§4.4) |
| `ModularForm.heckeT` / `CuspForm.heckeTLin` | the surface function / its bundling as `Module.End ℂ`, equal on the underlying function by `coe_heckeTLin_apply` |
| `ModularForm.coeffHeckeT` / `PowerSeries.heckeT` | the two-term coefficient operator on `ℕ → ℂ` (§4.2) / the series operator whose coefficients it computes (§4.3) |
| `heckeGenerators` / `heckeAlgebra` | the `Set (Module.End ℂ …)` of operators / its `Algebra.adjoin ℤ`; membership of a generator is `Algebra.subset_adjoin`, not a definitional unfolding |

## 8. Modules, in reading order

| module | role |
|---|---|
| `QExpansionOrder.lean` | the period-`M` coefficient reindexing and the product order lemma (two `UpperHalfPlane` facts) |
| `Gamma0TwoIndex.lean` | `(Γ₀ 2).index = 3`, the weight-`2` vanishing input |
| `SturmBound.lean` | vanishing and finite dimension: the three Sturm statements, the two coefficient forms, `qCoeffTrunc`, the instance and the wrapper |
| `HeckeAlgebra.lean` | `heckeGenerators`, `heckeAlgebra`, commutativity |
| `Defs/HeckeOperator.lean` | the Hecke matrices (`heckeMatrix`, `heckeDiagMatrix`), the slash-sum operators `heckeU`/`heckeT`, and the coefficient operators `coeffHeckeU`/`coeffHeckeT` (§4.1–4.2) |
| `Defs/FormalHeckeOperators.lean` | the formal `PowerSeries.heckeU`/`heckeV`/`heckeT` over any `CommRing`, and `heckeU_heckeV` (§4.3) |
| `HeckeOperatorForms.lean` | the bundled `heckeTLin`/`heckeULin` and the first `qExpansion` bridge |
| `HeckeQCoeff.lean` | `qCoeff` of the operators (`qCoeff_heckeT`, `qExpansion_heckeT_eq_heckeT`) and `coeffHecke*_int` (§4.4) |
| `HeckeFiniteness/Lattice.lean` | `intLattice` membership, Hecke-stability, `sturmB`/`trunc`, `intLattice_fg`, `intLattice_free_and_finite` |
| `HeckeFiniteness/Finiteness.lean` | the unconditional `moduleFinite_heckeAlgebra`/`moduleFree_heckeAlgebra` and `toSubmodule_heckeAlgebra_fg`; the lattice-embedding injection |
| `HeckeFiniteness/Span.lean` | the eigenform span and `finrank_span_heckeAlgebra_eq_finrank` |
| `HeckeFiniteAlgebra.lean` | the pin's **conditional** facade: `HasIntegralStructure.{moduleFinite,moduleFree}_heckeAlgebra` (they ignore the hypothesis and delegate), `moduleFinite_heckeAlgebra_two`, `fg_toSubmodule_heckeAlgebra`, the eigenvector/existence wrappers |
| `Defs/IntegralStructure.lean`, `Defs/IntegralLattice.lean` | the pin's two definitions (`intLattice`/`HasIntegralStructure`) and the weight-`2` vocabulary |
| `JqIntegralRatios.lean` | the integral `q`-side: `jqModC` as a ratio of integral series |
| `HeckeInputs/Integrality.lean` | the tower: `FiniteAlong`/integrality of `heckeAlphaBar`/`heckeBetaBar` and of the level inclusions |
| `WeightOne/Gamma1IntegralBasis.lean`, `NebentypusEigenbasis.lean` | applications: integral Γ₁ bases, the integral eigenbasis |

## 9. What a refactor of this cluster must preserve

* The Sturm tops are pin statements, verbatim from their `Theorems/` wrappers (see the `spec-pin:`
  headers; e.g. `S_ModularForm_sturm_bound_Gamma0.lean`,
  <https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularForm_sturm_bound_Gamma0.lean>,
  and `S_ModularForm_sturm_bound_of_isArithmetic.lean`,
  <https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularForm_sturm_bound_of_isArithmetic.lean>).
  The `HeckeFiniteAlgebra` headlines are pin statements likewise
  (`S_CuspForm_HasIntegralStructure_moduleFinite_heckeAlgebra.lean`,
  `S_CuspForm_moduleFinite_heckeAlgebra.lean`).
* The **port's own** additions are the freedoms: `qCoeffTrunc`, `sturmB`, `trunc`, `S2_Gamma0_*`,
  `Gamma0_two_index_eq_three`, and the re-derived coefficient-form bounds.
* The three presentations of §4 may not be merged or renamed: `ModularForm.heckeT` (`k : ℤ`, on
  `ℍ → ℂ`) and `PowerSeries.heckeT` (`k : ℕ`, on `R⟦X⟧`) are separate pin declarations with separate
  modules, and the checker's per-name exemption depends on the qualified `PowerSeries.` spelling.
* The boundary in §6 is one-way: this cluster may not invent curve-layer or Hecke-layer vocabulary, and
  the curve layer may not import it.
