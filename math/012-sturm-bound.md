# The Sturm bound

A modular form is determined by finitely many of its Fourier coefficients:
roughly the first `k/12` times the index of its level. This note states the bound
as FLT uses it, explains why it holds, and maps the port. It is the analytic input
of the **finiteness** of the Hecke algebra over `ℤ`
([studies/hecke-finiteness-coverage.md](../studies/hecke-finiteness-coverage.md)
§4): the bound makes the `q`-coefficient truncation injective, so the integral
lattice of cusp forms sits inside a finite free `ℤ`-module.

The Lean port is
[`../lean/FLTForHuman/ModularForms/SturmBound.lean`](../lean/FLTForHuman/ModularForms/SturmBound.lean)
and
[`../lean/FLTForHuman/ModularForms/QExpansionOrder.lean`](../lean/FLTForHuman/ModularForms/QExpansionOrder.lean),
with the measured record in
[../lean/logs/sturm-bound-port.md](../lean/logs/sturm-bound-port.md). Line
citations point at `anthropics/fermats-last-theorem@aa2d8b3`; mathlib citations
at the project pin `v4.34.0`, one minor version on from the `base/` notes.

The mathematics is the same at every level: **level one is the whole content**,
and the arithmetic level is reached by the norm. The level-one end is already in
mathlib; FLT contributes the reduction.

## 1. The statement

For an arithmetic subgroup `𝒢 ≤ GL₂(ℝ)` and a modular form
`f ∈ M_k(𝒢)`, the `q`-expansion at the cusp `∞` is a power series in `q`; its
`order` is the smallest index with a nonzero coefficient. FLT's general form is
([`Thm_ModularForm_sturm_bound_of_isArithmetic.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularForm_sturm_bound_of_isArithmetic.lean)):

```lean
theorem ModularForm.sturm_bound_of_isArithmetic {𝒢 : Subgroup (GL (Fin 2) ℝ)}
    [𝒢.IsArithmetic] {k : ℤ} {f : ModularForm 𝒢 k} (h1 : (1 : ℝ) ∈ 𝒢.strictPeriods)
    (h : (↑((k * 𝒢.relIndex 𝒮ℒ).toNat / 12) : ℕ∞) < (qExpansion 1 f).order) : f = 0
```

and the `Γ₀(N)` form, phrased coefficientwise
([`Thm_ModularForm_sturm_bound_Gamma0.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularForm_sturm_bound_Gamma0.lean)):

```lean
theorem ModularForm.sturm_bound_Gamma0 (N : ℕ) [NeZero N] {k : ℤ}
    (f : ModularForm (CongruenceSubgroup.Gamma0 N) k)
    (h : ∀ n : ℕ, n ≤ (k * (CongruenceSubgroup.Gamma0 N).index).toNat / 12 →
      (qExpansion 1 f).coeff n = 0) : f = 0
```

So: if the expansion vanishes below the bound, the form is zero. The order
formulation and the coefficient formulation are the same statement, since a
power series of order `b` has its coefficients `0, 1, …, b-1` equal to zero.

## 2. Level one is mathlib's theorem

Mathlib proves the level-one bound
([`DimensionFormula.lean`](https://github.com/leanprover-community/mathlib4/blob/v4.34.0/Mathlib/NumberTheory/ModularForms/LevelOne/DimensionFormula.lean)):

```lean
theorem ModularForm.sturm_bound_levelOne {k : ℤ} {f : ModularForm 𝒮ℒ k}
    (h : (↑(k.toNat / 12) : ℕ∞) < (qExpansion 1 f).order) : f = 0
```

Its content is the **dimension formula**, and it is the same mathematics as
[base/003](../base/003-no-level-2-weight-2-cusp-forms.md) §4. Two ingredients:

- **Division by `Δ`.** The discriminant `Δ = η²⁴` is a cusp form of weight `12`
  whose `q`-expansion has order exactly `1` and which is nonzero on `ℍ`, so
  `f ↦ f/Δ` is a `ℂ`-linear equivalence
  `CuspForm.discriminantEquiv : CuspForm 𝒮ℒ k ≃ₗ[ℂ] ModularForm 𝒮ℒ (k - 12)`.
  A cusp form of weight `k < 12` becomes a modular form of negative weight.
- **No negative-weight modular forms.** For `k < 0`, invariance under
  `S = [[0,-1],[1,0]]` reads `f(Sτ) = τ^k f(τ)`, so a constant form would obey
  `c = 2^k c`; combined with the fact that a weight `≤ 0` form is constant (the
  maximum-modulus argument of base/003 §4.2), this gives `f = 0`.

A form of weight `k` whose coefficients below `k/12` vanish therefore lies in the
image of `Δ`-multiplication by a *cusp* form of weight `k - 12` (its quotient is
a modular form vanishing at the cusp), which is zero for `k < 12`; iterating by
`12` handles all `k`. This is exactly `sturm_bound_levelOne`'s route through
`sturm_bound_levelOne_nat` and `levelOne_neg_weight_rank_zero`.

FLT's `levelOne_eq_zero_of_lt_order_qExpansion` is the **period-`M`** form of
this: if the `q`-expansion of period `M` (that is, in `q_M = e^{2πiτ/M}`) has
order beyond `M · (k/12)`, then `F = 0`. The reduction is the coefficient
reindexing: $`(qExpansion (M h) F).coeff n`$ equals
$`(qExpansion h F).coeff (n / M)`$ when $`M \mid n`$, and $`0`$ otherwise —
that is `UpperHalfPlane.qExpansion_coeff_nat_mul`. Taking `h = 1` and
contradicting the order bound gives the level-one lemma the port uses.

## 3. From arithmetic level to level one: the norm

Mathlib's `ModularForm.norm` packages the product of the translates,
$`\mathrm{Norm}(f)(\tau) = \prod_{q \in \mathcal{SL}/\mathcal{G}} (f \mid_k g_q^{-1})(\tau)`$,
of weight $`k \cdot [\mathcal{SL} : \mathcal{G}]`$, and
`ModularForm.norm_eq_zero_iff` says it vanishes only on zero forms. The order of
a finite product of power series over a domain is the sum of the orders, so the
factor of the identity coset alone already bounds the total:
$`\mathrm{order}(qExpansion M f) \le \mathrm{order}(qExpansion M (\mathrm{Norm}(f)))`$.

Now suppose `M · (k · [\mathcal{SL}:\mathcal{G}] / 12) < order(qExpansion M f)`.
The same strict inequality holds for `Norm(f)`, whose weight is
`k · [\mathcal{SL}:\mathcal{G}]`; the level-one period-`M` lemma makes `Norm(f)`
zero, and `norm_eq_zero_iff` makes `f` zero. That is
`ModularForm.eq_zero_of_lt_order_qExpansion_of_isArithmetic`.

## 4. Why a common period `M` is needed

At level one (and for `Γ₀(N)`) the group contains `T = [[1,1],[0,1]]`, so `1` is
a strict period and the expansion in `q = e^{2πiτ}` is the period-`1` one. A
general arithmetic `𝒢` need not contain `T`: its strict periods form `hℤ` for
some `h`, and if `𝒢` contains no unipotent it may have none at all. The translates
appearing in the norm live at *different* levels `γ𝒢γ⁻¹`, so a single period
must work for all of them at once. `Subgroup.IsArithmetic.exists_nat_mem_strictPeriods_conj`
supplies one: let `Λ` be the normal core of `𝒢.comap mapGL` in `SL₂(ℤ)`, of finite
index, and take `M = [SL₂(ℤ) : Λ]`. Then `T^M ∈ Λ`, and `Λ` is normal, so
`γ⁻¹ T^M γ ∈ Γ` for every `γ ∈ SL₂(ℤ)` — that is, `M` is a strict period of every
conjugate `γΓγ⁻¹`. This is the only group theory in the proof.

## 5. The `Γ₀(N)` specialisation

`Γ₀(N)` is a congruence subgroup, so it contains `T`; hence `1 ∈ (Γ₀ N).strictPeriods`
(`CongruenceSubgroup.one_mem_strictPeriods_Gamma0`, from
`Subgroup.strictPeriods_eq_zmultiples_one_of_T_mem`). Its relative index in
`GL₂(ℝ)` against `𝒮ℒ` is its ordinary index in `SL₂(ℤ)`:
`(Γ₀ N).relIndex 𝒮ℒ = (Γ₀ N).index`, because the index in `GL₂` is computed after
pulling back along `mapGL` (`Subgroup.index_comap`) and
`comap_map_eq_self_of_injective` removes the pullback. With those two facts the
general statement becomes the coefficientwise `Γ₀(N)` statement, and the bound
`k · (Γ₀ N).index / 12` is the familiar `k · N ∏_{p ∣ N}(1 + 1/p) / 12`.

## 6. Why finiteness needs it

The bound is what makes a **finite** coefficient vector determine a form. In
`S_CuspForm_intLattice_fg.lean`:

- `sturmB N k = (k · (Γ₀ N).index).toNat / 12`;
- `trunc N k : CuspForm (Γ₀ N) k →ₗ[ℤ] (Fin (sturmB + 1) → ℂ)` is the first
  `sturmB + 1` `q`-coefficients;
- `trunc_injective` is exactly `sturm_bound_Gamma0`: a form truncated to zero
  vanishes;
- the integral lattice `CuspForm.intLattice N k` (the `ℤ`-span of the forms with
  integral `q`-coefficients) therefore embeds into the finite free `ℤ`-module
  `Fin (sturmB + 1) → ℂ`, so it is finitely generated by
  `Submodule.fg_of_fg_map_injective`.

That is `CuspForm.intLattice_fg`, and from it
`HasIntegralStructure.moduleFinite_heckeAlgebra` gives
`Module.Finite ℤ (CuspForm.heckeAlgebra N k S)` — the finiteness target. The
Sturm bound is thus a small but mandatory leaf on the T-side route; the
[coverage study](../studies/hecke-finiteness-coverage.md) §4 prices its whole
cone at 18 nodes and shows it also lies on the expensive general route.

## 7. Key point → declaration map

| Step | Mathematics | Lean declaration | Location |
|---|---|---|---|
| coefficient reindexing | period `M` coefficients are period-`1` ones at `n/M` | `UpperHalfPlane.qExpansion_coeff_nat_mul` | port; [S](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_UpperHalfPlane_qExpansion_coeff_nat_mul.lean) |
| product of expansions | `qExp(∏ Fᵢ) = ∏ qExp(Fᵢ)` | `UpperHalfPlane.qExpansion_prod` | port; [S](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_UpperHalfPlane_qExpansion_prod.lean) |
| `Γ₀(N)` contains `T` | `1 ∈ (Γ₀ N).strictPeriods` | `CongruenceSubgroup.one_mem_strictPeriods_Gamma0` | port; [S](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_CongruenceSubgroup_one_mem_strictPeriods_Gamma0.lean) |
| common period | `M = [SL₂(ℤ) : normalCore]` | `Subgroup.IsArithmetic.exists_nat_mem_strictPeriods_conj` | port; [S](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_Subgroup_IsArithmetic_exists_nat_mem_strictPeriods_conj.lean) |
| level-one, period `M` | mathlib `sturm_bound_levelOne` + reindexing | `ModularForm.levelOne_eq_zero_of_lt_order_qExpansion` | port; [S](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularForm_levelOne_eq_zero_of_lt_order_qExpansion.lean) |
| norm reduction | `order(f) ≤ order(Norm f)`, `norm_eq_zero_iff` | `ModularForm.eq_zero_of_lt_order_qExpansion_of_isArithmetic` | port; [S](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularForm_eq_zero_of_lt_order_qExpansion_of_isArithmetic.lean) |
| the general bound | `k · relIndex 𝒮ℒ / 12` | `ModularForm.sturm_bound_of_isArithmetic` | port; [Thm](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularForm_sturm_bound_of_isArithmetic.lean) |
| the `Γ₀(N)` bound | `k · index / 12` | `ModularForm.sturm_bound_Gamma0` | port; [Thm](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularForm_sturm_bound_Gamma0.lean) |
| level-one engine | dimension formula + negative weight | `ModularForm.sturm_bound_levelOne` | mathlib `v4.34.0` |
| the finiteness use | truncation is injective | `CuspForm.intLattice_fg` | FLT [S](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_CuspForm_intLattice_fg.lean), not yet ported |

## 8. Links

FLT sources at the pinned sha `aa2d8b3`:

- [`S_ModularForm_sturm_bound_of_isArithmetic.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularForm_sturm_bound_of_isArithmetic.lean)
  — the general headline (29 lines).
- [`S_ModularForm_sturm_bound_Gamma0.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularForm_sturm_bound_Gamma0.lean)
  — the `Γ₀(N)` headline (26 lines).
- [`S_ModularForm_eq_zero_of_lt_order_qExpansion_of_isArithmetic.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularForm_eq_zero_of_lt_order_qExpansion_of_isArithmetic.lean)
  — the norm reduction.
- [`S_ModularForm_levelOne_eq_zero_of_lt_order_qExpansion.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularForm_levelOne_eq_zero_of_lt_order_qExpansion.lean)
  — the level-one period-`M` vanishing.
- [`S_Subgroup_IsArithmetic_exists_nat_mem_strictPeriods_conj.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_Subgroup_IsArithmetic_exists_nat_mem_strictPeriods_conj.lean)
  — the common period.
- [`S_CuspForm_intLattice_fg.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_CuspForm_intLattice_fg.lean)
  — the finiteness use.

Mathlib at tag `v4.34.0`:

- [LevelOne/DimensionFormula.lean](https://github.com/leanprover-community/mathlib4/blob/v4.34.0/Mathlib/NumberTheory/ModularForms/LevelOne/DimensionFormula.lean)
  — `sturm_bound_levelOne`, `discriminantEquiv`, the dimension formula.
- [LevelOne/Basic.lean](https://github.com/leanprover-community/mathlib4/blob/v4.34.0/Mathlib/NumberTheory/ModularForms/LevelOne/Basic.lean)
  — negative weight vanishes; the maximum-modulus route.
- [NormTrace.lean](https://github.com/leanprover-community/mathlib4/blob/v4.34.0/Mathlib/NumberTheory/ModularForms/NormTrace.lean)
  — `ModularForm.norm`, `norm_eq_zero_iff`.
- [QExpansion.lean](https://github.com/leanprover-community/mathlib4/blob/v4.34.0/Mathlib/NumberTheory/ModularForms/QExpansion.lean)
  — `qExpansion`, `cuspFunction`, `qExpansion_mul`, `qExpansion_coeff_unique`.
- [Cusps.lean](https://github.com/leanprover-community/mathlib4/blob/v4.34.0/Mathlib/NumberTheory/ModularForms/Cusps.lean)
  — `strictPeriods`, `isCusp_of_mem_strictPeriods`.

Companion project records:

- [base/003 — No level-2 weight-2 cusp forms](../base/003-no-level-2-weight-2-cusp-forms.md)
  — the level-one dimension formula and the maximum-modulus argument, done in
  full.
- [studies/hecke-finiteness-coverage.md](../studies/hecke-finiteness-coverage.md)
  — the finiteness targets and the routes through them.
- [../lean/logs/sturm-bound-port.md](../lean/logs/sturm-bound-port.md) — the
  measured port record.
