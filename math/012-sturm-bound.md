# The Sturm bound

A modular form is determined by finitely many of its Fourier coefficients. This
note does the mathematics: the level-one bound is *division by the discriminant*,
reducing a form of weight $`k`$ to one of weight $`k - 12`$ until the weight is
below $`12`$, where there are no cusp forms; the analytic input is that there are
no modular forms of negative weight. The arithmetic-level bound then follows by
multiplying the form's translates together — the norm — which trades the level for
a factor of the index in the weight. FLT uses the bound to make the coefficient
truncation injective, which is what makes the integral lattice of cusp forms
finitely generated.

The analytic part (§3) is the same argument as
[base/003](../base/003-no-level-2-weight-2-cusp-forms.md) §4.2, which unwinds it to
the maximum-modulus principle; this note does not repeat that, and concentrates on
what the Sturm bound adds. The Lean port is
[`../lean/FLTForHuman/ModularForms/SturmBound.lean`](../lean/FLTForHuman/ModularForms/SturmBound.lean)
and
[`../lean/FLTForHuman/ModularForms/QExpansionOrder.lean`](../lean/FLTForHuman/ModularForms/QExpansionOrder.lean),
with the measured record in
[../lean/logs/sturm-bound-port.md](../lean/logs/sturm-bound-port.md); §9 is the
declaration map, kept to the end. FLT citations are pinned at `aa2d8b3`; mathlib
citations at the project pin `v4.34.0`.

## 1. The statement

Let $`f`$ be a modular form of weight $`k`$ for a finite-index subgroup
$`\Gamma \le \mathrm{SL}_2(\mathbb{Z})`$, holomorphic on $`\mathbb{H}`$ and
bounded at the cusps, with $`q`$-expansion $`f = \sum_{n \ge 0} a_n q^n`$ at
the cusp $`\infty`$. Write $`\mathrm{ord}(f)`$ for the smallest $`n`$ with
$`a_n \ne 0`$. The **Sturm bound** says that if the order is large enough
relative to the weight and the index, the form is zero:

$`\mathrm{ord}(f) \gt  \frac{k \cdot [\mathrm{SL}_2(\mathbb{Z}) : \Gamma]}{12} \;\Longrightarrow\; f = 0`$.

Equivalently: a nonzero form has
$`\mathrm{ord}(f) \le k \cdot [\mathrm{SL}_2(\mathbb{Z}) : \Gamma]/12`$, so its
first $`\lfloor k \cdot [\mathrm{SL}_2(\mathbb{Z}) : \Gamma]/12 \rfloor + 1`$
coefficients are a complete set of invariants. For $`\Gamma = \Gamma_0(N)`$ the
index is $`N \prod_{p \mid N}(1 + 1/p)`$, and the bound reads
$`k\,N\prod_{p \mid N}(1 + 1/p)/12`$.

This is the statement FLT ports, in two forms (the general one in order form, the
$`\Gamma_0(N)`$ one coefficientwise):

```lean
theorem ModularForm.sturm_bound_of_isArithmetic {𝒢 : Subgroup (GL (Fin 2) ℝ)}
    [𝒢.IsArithmetic] {k : ℤ} {f : ModularForm 𝒢 k} (h1 : (1 : ℝ) ∈ 𝒢.strictPeriods)
    (h : (↑((k * 𝒢.relIndex 𝒮ℒ).toNat / 12) : ℕ∞) < (qExpansion 1 f).order) : f = 0

theorem ModularForm.sturm_bound_Gamma0 (N : ℕ) [NeZero N] {k : ℤ}
    (f : ModularForm (CongruenceSubgroup.Gamma0 N) k)
    (h : ∀ n : ℕ, n ≤ (k * (CongruenceSubgroup.Gamma0 N).index).toNat / 12 →
      (qExpansion 1 f).coeff n = 0) : f = 0
```

The mathematics below is level one plus a reduction to it; the $`\Gamma_0(N)`$
form is the specialisation in §7.

## 2. The engine: division by the discriminant

The discriminant $`\Delta(\tau) = \eta(\tau)^{24} = q \prod_{n \ge 1}(1 - q^n)^{24}`$
is the one weight-$`12`$ cusp form we have for free. Three facts make it the
engine of the whole proof.

1. **$`\Delta`$ does not vanish on $`\mathbb{H}`$.** The eta product has no
   zeros on the upper half plane, so $`f/\Delta`$ is holomorphic whenever $`f`$
   is.
2. **$`\Delta`$ has weight $`12`$.** Dividing a weight-$`k`$ form by $`\Delta`$
   gives a function of weight $`k - 12`$: the slash quotient rule is
   $`(f/\Delta)\mid_{k-12}\gamma = (f\mid_k\gamma)/(\Delta\mid_{12}\gamma) = f/\Delta`$
   for $`\gamma \in \mathrm{SL}_2(\mathbb{Z})`$.
3. **$`\Delta`$ has a simple zero at the cusp:** $`\Delta = q \cdot (\text{a unit})`$,
   i.e. $`\mathrm{ord}(\Delta) = 1`$. A higher-order zero would give $`f/\Delta`$
   a pole at the cusp; the order being exactly $`1`$ is what keeps the quotient
   inside modular forms.

Combining 1–3: **division by $`\Delta`$ is a linear isomorphism**
$`S_k(\mathrm{SL}_2(\mathbb{Z})) \cong M_{k-12}(\mathrm{SL}_2(\mathbb{Z}))`$,
$`f \mapsto f/\Delta`$, with inverse $`g \mapsto \Delta g`$. In one direction
$`\Delta g`$ is a cusp form of weight $`k`$ (it vanishes where $`\Delta`$ does);
in the other $`f/\Delta`$ is holomorphic, of weight $`k-12`$, and at the cusp it
has order $`\mathrm{ord}(f) - 1 \ge 0`$ because $`f`$ is a cusp form (order
$`\ge 1`$) and $`\Delta`$ has order $`1`$. The two compositions are the identity
by cancelling the nowhere-zero $`\Delta`$. This is mathlib's
`CuspForm.discriminantEquiv : CuspForm 𝒮ℒ k ≃ₗ[ℂ] ModularForm 𝒮ℒ (k - 12)`.

**The Sturm bound is now an induction on the weight.** Suppose
$`\mathrm{ord}(f) \gt  k/12`$.

- Since $`k/12 \ge 0`$, the constant term vanishes, so $`f`$ is a cusp form.
- Write $`f = \Delta \cdot (f/\Delta)`$. The $`q`$-expansion is multiplicative and
  $`q`$-order is additive, with $`\mathrm{ord}(\Delta) = 1`$; hence
  $`\mathrm{ord}(f/\Delta) = \mathrm{ord}(f) - 1 \gt  k/12 - 1 = (k-12)/12`$.
- If $`k \lt  12`$ then $`k - 12 \lt  0`$ and $`M_{k-12} = 0`$ (§3), so
  $`f/\Delta = 0`$ and $`f = 0`$.
- If $`k \ge 12`$, apply the bound inductively to $`f/\Delta`$, whose weight
  $`k - 12`$ is smaller; then $`f = \Delta \cdot (f/\Delta) = 0`$.

The strong induction terminates because the weight drops by $`12`$ each step. This
is exactly mathlib's `ModularForm.sturm_bound_levelOne_nat`; the coefficient
identity $`\mathrm{ord}(f/\Delta) = \mathrm{ord}(f) - 1`$ is the imported fact
`ModularForm.qExpansion_eq_qExpansion_discriminant_mul` together with
`ModularForm.discriminant_qExpansion_order`.

## 3. The analytic input: there are no negative-weight forms

The induction lands in weight $`k - 12 \lt  0`$, so the proof needs the classical
fact: a modular form of weight $`k \le 0`$ at level one is constant, and one of
weight $`k \lt  0`$ is zero.

**Constant.** For $`\tau \in \mathbb{H}`$, the fundamental domain supplies
$`\gamma = [[a,b],[c,d]] \in \mathrm{SL}_2(\mathbb{Z})`$
with $`\mathrm{Im}(\gamma\tau) \ge 1/2`$ and $`|c\tau + d| \le 1`$. Invariance
gives $`f(\gamma\tau) = (c\tau+d)^k f(\tau)`$, so for $`k \le 0`$,
$`|f(\tau)| = |c\tau+d|^{-k}|f(\gamma\tau)| \le |f(\gamma\tau)|`$. Every value of
$`|f|`$ is therefore dominated by a value at a point of $`\{\mathrm{Im} \ge 1/2\}`$.
In the $`q`$-coordinate $`q = e^{2\pi i\tau}`$ that region is the disc
$`|q| \le e^{-\pi} \lt  1`$, and $`f`$ is a holomorphic function $`G(q)`$ on the
unit disc (it is bounded at the cusp). So $`|G|`$ is dominated on the whole disc
by its values on a smaller closed disc, and the maximum-modulus principle forces
$`G`$ — hence $`f`$ — to be constant. This is the packaged statement
`eq_const_of_exists_le`, with the geometry of $`\mathrm{Im} \ge 1/2`$ and
$`|q| \le e^{-\pi}`$ in `exists_one_half_le_im_smul_and_norm_denom_le` and
`norm_qParam_le_of_one_half_le_im`; base/003 §4.2 unwinds it in full.

**Zero.** The only constant that can be modular of weight $`k \lt  0`$ is $`0`$.
Apply invariance to $`S = [[0,-1],[1,0]]`$, whose
denominator is $`c\tau + d = \tau`$: a constant form $`c`$ satisfies
$`c = f(S\tau) = \tau^k f(\tau) = \tau^k c`$ for every $`\tau`$. At $`\tau = i`$
and $`\tau = 2i`$ this is $`c = i^k c`$ and $`c = (2i)^k c = 2^k c`$, so
$`(2^k - 1)c = 0`$. For $`k \ne 0`$, $`2^k \ne 1`$ (it is $`2^{|k|}`$ or
$`2^{-|k|}`$), so $`c = 0`$. For $`k = 0`$ the argument stops, correctly: the
weight-zero forms are the constants.

This is `levelOne_nonpos_wt_const` and `levelOne_neg_weight_eq_zero`, and it is
the only genuinely analytic input of the Sturm bound.

## 4. Where the number $`12`$ comes from

The weight-$`12`$ discriminant and the Eisenstein series organise the level-one
space. The cusp forms are exactly the image of $`\Delta`$-multiplication (§2), and
for even $`k \ge 4`$ the non-cusp forms are spanned by the single Eisenstein
series $`E_k`$: $`M_k = S_k \oplus \mathbb{C}E_k`$, $`S_k \cong M_{k-12}`$, hence
$`\dim M_k = 1 + \dim M_{k-12}`$. Iterating, and using that $`M_2 = 0`$ (there is
no weight-$`2`$ Eisenstein series for $`\mathrm{SL}_2(\mathbb{Z})`$ — which is why
the level-$`2`$ case of base/003 needs the norm and this note does not),

$`\dim M_k(\mathrm{SL}_2(\mathbb{Z})) = \lfloor k/12 \rfloor`$ when
$`k \equiv 2 \pmod{12}`$, and $`\lfloor k/12 \rfloor + 1`$ otherwise,

for even $`k \ge 0`$; odd weights are killed by $`-1 \in \mathrm{SL}_2(\mathbb{Z})`$.
The dimension grows like $`k/12`$ — the numerology of the bound — and the Sturm
bound is the *injectivity* of the first $`\lfloor k/12\rfloor + 1`$ coefficients,
proved directly by the $`\Delta`$-division of §2. This is mathlib's
`dimension_level_one` and `rank_eq_one_add_rank_cuspForm`.

## 5. Arithmetic level: multiply the translates

For a general finite-index $`\Gamma`$, level one is recovered by the **norm**: the
product of the translates over the cosets of $`\Gamma`$ in
$`\mathrm{SL}_2(\mathbb{Z})`$,

$`\mathrm{Norm}(f)(\tau) = \prod_{q \in \mathrm{SL}_2(\mathbb{Z})/\Gamma} (f \mid_k g_q^{-1})(\tau)`$,

where $`g_q`$ is any representative of the coset $`q`$. Mathlib's
`ModularForm.norm` packages this, and `ModularForm.norm_eq_zero_iff` records the
two facts the reduction needs:

- **The weight multiplies by the index:** each factor has weight $`k`$ and there
  are $`[\mathrm{SL}_2(\mathbb{Z}) : \Gamma]`$ of them, so $`\mathrm{Norm}(f)`$ is
  a level-one form of weight $`k \cdot [\mathrm{SL}_2(\mathbb{Z}) : \Gamma]`$. (The
  determinant bookkeeping is why the slash action carries $`|\det|^{k-1}`$; on
  $`\mathrm{SL}_2`$ it is invisible.)
- **It vanishes only on zero forms:** a finite product of holomorphic functions on
  the connected set $`\mathbb{H}`$ is zero only if one factor is, and a translate
  $`f \mid_k g_q^{-1}`$ is zero only if $`f`$ is — slashing by an invertible
  element is invertible.

The order of a product is the sum of the orders, and the term of the identity
coset is $`f`$ itself, so $`\mathrm{ord}(f) \le \mathrm{ord}(\mathrm{Norm}(f))`$.
Now if $`\mathrm{ord}(f) \gt  k \cdot [\mathrm{SL}_2(\mathbb{Z}) : \Gamma]/12`$, the
same strict inequality holds for the level-one form $`\mathrm{Norm}(f)`$ of weight
$`k \cdot [\mathrm{SL}_2(\mathbb{Z}) : \Gamma]`$; the level-one bound of §2 makes
the norm zero, and the norm vanishes iff $`f`$ does. That is the reduction, and it
is FLT's `ModularForm.eq_zero_of_lt_order_qExpansion_of_isArithmetic`.

The one point the Lean proof has to be careful about is that the $`q`$-order
comparison is made on the expansion of period $`M`$ rather than $`1`$; §6 is why.

## 6. Periods, and why one common $`M`$ is needed

A modular form has a $`q`$-expansion in $`q = e^{2\pi i\tau}`$ only when its group
contains $`T = [[1,1],[0,1]]`$ (or at least a power,
giving a period $`h`$ and an expansion in $`q_h = e^{2\pi i\tau/h}`$). A general
arithmetic $`\Gamma`$ need not contain any unipotent: its strict periods are
$`h\mathbb{Z}`$ for some $`h`$, or $`\{0\}`$. Since the norm's factors live at the
*different* levels $`\gamma\Gamma\gamma^{-1}`$, one period must work for all of
them at once.

The common period is the index of the normal core. Let
$`\Gamma_0 = \Gamma \cap \mathrm{SL}_2(\mathbb{Z})`$ and let $`\Lambda`$ be the
normal core $`\bigcap_{\gamma} \gamma\Gamma_0\gamma^{-1}`$, the largest normal
subgroup of $`\mathrm{SL}_2(\mathbb{Z})`$ contained in $`\Gamma_0`$; it has finite
index. Put $`M = [\mathrm{SL}_2(\mathbb{Z}) : \Lambda]`$. Then
$`T^M \in \Lambda`$ (Lagrange), and $`\Lambda`$ is normal, so for every $`\gamma`$
we have $`\gamma^{-1} T^M \gamma \in \Gamma_0 \subseteq \Gamma`$: that is, $`M`$ is
a strict period of every conjugate $`\gamma\Gamma\gamma^{-1}`$. This is
`Subgroup.IsArithmetic.exists_nat_mem_strictPeriods_conj`; it is the only group
theory in the proof, and its content is exactly "a finite-index subgroup of
$`\mathrm{SL}_2(\mathbb{Z})`$ contains a normal subgroup of finite index containing
a power of $`T`$", i.e. the cusp $`\infty`$ is a cusp of every conjugate at a
common width.

## 7. The $`\Gamma_0(N)`$ specialisation

$`\Gamma_0(N)`$ contains $`T`$, so its strict periods are $`\mathbb{Z}`$ and a
single common period is $`M = 1`$; and its index in $`\mathrm{SL}_2(\mathbb{Z})`$ is
$`[\mathrm{SL}_2(\mathbb{Z}) : \Gamma_0(N)] = N \prod_{p \mid N}(1 + 1/p)`$, which for
$`N = 2`$ is $`3`$ — the index base/003 computes by hand. Substituting $`M = 1`$,
the index and $`q_1 = q`$ into the general statement gives the coefficientwise
form of §1. The Lean bridge is that the relative index of $`\Gamma_0(N)`$ in
$`GL_2(\mathbb{R})`$ against the image $`\mathcal{SL}`$ of
$`\mathrm{SL}_2(\mathbb{Z})`$ equals its ordinary index (`Subgroup.index_comap`
plus `comap_map_eq_self_of_injective`), so the abstract $`\mathcal{SL}`$-normalised
bound becomes the concrete $`(\Gamma_0 N).index`$.

## 8. What the bound is for: finitely many coefficients

The bound is what makes the $`q`$-coefficient truncation **injective**, and
injective truncation is finite generation in disguise. Let
$`B = \lfloor k \cdot [\mathrm{SL}_2(\mathbb{Z}) : \Gamma_0(N)]/12 \rfloor`$ and
$`\mathrm{trunc}(f) = (a_0, a_1, \dots, a_B) \in \mathbb{C}^{B+1}`$. If
$`\mathrm{trunc}(f) = 0`$ then $`f`$ vanishes below the Sturm bound, so $`f = 0`$.
The integral lattice $`\mathrm{intLattice} \subset S_k(\Gamma_0(N))`$ — the
$`\mathbb{Z}`$-span of the forms with integral $`q`$-coefficients — therefore
injects into $`\mathbb{C}^{B+1}`$, and its image lies in the finitely generated
$`\mathbb{Z}`$-module spanned by the $`B+1`$ coordinate vectors; hence
$`\mathrm{intLattice}`$ is finitely generated:

$`\mathrm{intLattice} \hookrightarrow \mathbb{C}^{B+1} \;\Longrightarrow\; \mathrm{intLattice} \text{ is a finitely generated } \mathbb{Z}\text{-module.}`$

That is FLT's `CuspForm.intLattice_fg`, whose proof is literally this: a
$`\mathbb{Z}`$-linear truncation map, its injectivity from `sturm_bound_Gamma0`, and
the containment of its image in the finite span
(`Submodule.fg_of_fg_map_injective`). From it,
`HasIntegralStructure.moduleFinite_heckeAlgebra` gives
`Module.Finite ℤ (heckeAlgebra N k S)` — the finiteness target of the T side. The
Sturm bound is the analytic leaf under that finiteness; the route structure is
priced in [studies/hecke-finiteness-coverage.md](../studies/hecke-finiteness-coverage.md)
§4.

The same injectivity gives finite-dimensionality directly. FLT states the
coefficient-form bounds `CuspForm.eq_zero_of_qExpansion_coeff_eq_zero` (arithmetic
level, $`k \cdot [\mathcal{SL} : \mathcal{G}] \lt 12d`$) and
`CuspForm.Gamma0_eq_zero_of_qExpansion_coeff_eq_zero` in the `section SturmBound`
of `S_CuspForm_finiteDimensional_cuspForm.lean`, then feeds the `Γ₀` one to
`qCoeffTrunc` and `FiniteDimensional.of_injective`, giving
$`\dim_{\mathbb{C}} S_k(\Gamma_0(N)) \le \lfloor k[\mathcal{SL}:\Gamma_0(N)]/12 \rfloor + 1`$.
FLT proves those two bounds through the norm; the port re-derives them from
`sturm_bound_of_isArithmetic` (`relIndex = Nat.card` is `rfl`,
`PowerSeries.nat_le_order` converts vanishing coefficients to the order
hypothesis, and `k < 0` is `ModularForm.isZero_of_neg_weight`). Neither
`CuspForm.norm` nor its ~300-line `norm`/`normCofactor` block is needed; this
answers open question 5 of the coverage study.

## 9. The Lean route map

Everything above is imported from mathlib or transcribed from FLT; no new
mathematics was needed. The declarations, in the order the narrative uses them:

| Mathematics | Declaration | Source |
|---|---|---|
| division by $`\Delta`$ is an isomorphism | `CuspForm.discriminantEquiv` | mathlib `LevelOne/DimensionFormula.lean` |
| $`\mathrm{ord}(\Delta) = 1`$ | `ModularForm.discriminant_qExpansion_order` | mathlib, ibid. |
| $`f = \Delta \cdot (f/\Delta)`$ on $`q`$-expansions | `ModularForm.qExpansion_eq_qExpansion_discriminant_mul` | mathlib, ibid. |
| induction on the weight | `ModularForm.sturm_bound_levelOne_nat`, `sturm_bound_levelOne` | mathlib, ibid. |
| no negative-weight forms | `levelOne_nonpos_wt_const`, `levelOne_neg_weight_eq_zero` | mathlib `LevelOne/Basic.lean` |
| dimension formula | `ModularForm.dimension_level_one`, `rank_eq_one_add_rank_cuspForm` | mathlib `LevelOne/DimensionFormula.lean` |
| norm: weight and zero set | `ModularForm.norm`, `norm_eq_zero_iff` | mathlib `NormTrace.lean` |
| order of a product | `PowerSeries.order_prod` | mathlib |
| period reindexing | `UpperHalfPlane.qExpansion_coeff_nat_mul` | ported, `QExpansionOrder.lean` |
| product of $`q`$-expansions | `UpperHalfPlane.qExpansion_prod` | ported, ibid. |
| common period | `Subgroup.IsArithmetic.exists_nat_mem_strictPeriods_conj` | ported, `SturmBound.lean` |
| level-one period-$`M`$ bound | `ModularForm.levelOne_eq_zero_of_lt_order_qExpansion` | ported, ibid. |
| arithmetic-level bound | `ModularForm.eq_zero_of_lt_order_qExpansion_of_isArithmetic` | ported, ibid. |
| $`\Gamma_0(N)`$ contains $`T`$ | `CongruenceSubgroup.one_mem_strictPeriods_Gamma0` | ported, ibid. |
| the two headlines | `ModularForm.sturm_bound_of_isArithmetic`, `sturm_bound_Gamma0` | ported, ibid. |
| coefficient-form bounds | `CuspForm.eq_zero_of_qExpansion_coeff_eq_zero`, `Gamma0_eq_zero_of_qExpansion_coeff_eq_zero` | ported, ibid. |
| no negative-weight forms, any level | `ModularForm.isZero_of_neg_weight` | mathlib `NormTrace.lean` |
| finiteness use (not yet ported) | `CuspForm.intLattice_fg` | FLT `S_CuspForm_intLattice_fg.lean` |
| finite-dimensionality use (not yet ported) | `CuspForm.finiteDimensional_cuspForm` | FLT `S_CuspForm_finiteDimensional_cuspForm.lean` |

Formal points that do not enter the narrative:

- **The level is $`\mathcal{SL}`$, not $`\mathrm{SL}_2(\mathbb{Z})`$.** Mathlib's
  level-one statements are for the image of $`\mathrm{SL}_2(\mathbb{Z})`$ in
  $`GL_2(\mathbb{R})`$; the $`\Gamma(1)`$-versus-$`\mathcal{SL}`$ bridge is
  `CongruenceSubgroup.Gamma_one_top` plus `Subgroup.comap_map_eq_self_of_injective`.
- **$`q`$-expansions are computed at period $`M`$.** The port keeps the two
  expansion lemmas separate (`qExpansion_coeff_nat_mul` and the period-$`M`$
  level-one bound) precisely so the period bookkeeping stays out of the norm
  argument.
- **Statements are transcribed, not restated.** All eight public Sturm
  declarations are verbatim from their `Theorems/` wrappers, and the two
  coefficient-form bounds are verbatim from their `S_` source (they have no
  wrapper); the checker reports `1,258 identical, 0 mismatched, 0 missing`. The
  only proof-level adaptations are the v4.33 → v4.34 renames `ENat.toNat_coe` →
  `ENat.toNat_natCast`, `if_pos` → `ite_eq_left`, and the deprecation of
  `ModularForm.coe_zero`.

## 10. Links

Mathlib at tag `v4.34.0` (the project pin; the `base/` notes cite `v4.33.0`):

- [LevelOne/DimensionFormula.lean](https://github.com/leanprover-community/mathlib4/blob/v4.34.0/Mathlib/NumberTheory/ModularForms/LevelOne/DimensionFormula.lean)
  — `discriminantEquiv`, the order-`1` expansion of $`\Delta`$, the dimension
  formula, `sturm_bound_levelOne`.
- [LevelOne/Basic.lean](https://github.com/leanprover-community/mathlib4/blob/v4.34.0/Mathlib/NumberTheory/ModularForms/LevelOne/Basic.lean)
  — no negative-weight forms: the maximum-modulus and $`S`$-invariance arguments.
- [Discriminant.lean](https://github.com/leanprover-community/mathlib4/blob/v4.34.0/Mathlib/NumberTheory/ModularForms/Discriminant.lean)
  — $`\Delta = \eta^{24}`$, its nonvanishing and its simple cusp zero.
- [NormTrace.lean](https://github.com/leanprover-community/mathlib4/blob/v4.34.0/Mathlib/NumberTheory/ModularForms/NormTrace.lean)
  — the norm, its weight and its zero set.
- [Cusps.lean](https://github.com/leanprover-community/mathlib4/blob/v4.34.0/Mathlib/NumberTheory/ModularForms/Cusps.lean)
  — strict periods and cusps.

FLT at `aa2d8b3`:

- [`S_ModularForm_sturm_bound_of_isArithmetic.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularForm_sturm_bound_of_isArithmetic.lean)
  and [`S_ModularForm_sturm_bound_Gamma0.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularForm_sturm_bound_Gamma0.lean)
  — the two headlines.
- [`S_ModularForm_eq_zero_of_lt_order_qExpansion_of_isArithmetic.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularForm_eq_zero_of_lt_order_qExpansion_of_isArithmetic.lean)
  — the norm reduction.
- [`S_CuspForm_intLattice_fg.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_CuspForm_intLattice_fg.lean)
  — the finiteness use.
- [`S_CuspForm_finiteDimensional_cuspForm.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_CuspForm_finiteDimensional_cuspForm.lean)
  — the coefficient-form bounds (330–346) and the `normCofactor` proof (151–321)
  the port does not need.

Project records:

- [base/003 — No level-2 weight-2 cusp forms](../base/003-no-level-2-weight-2-cusp-forms.md)
  §4 — the maximum-modulus argument and the dimension formula in full.
- [studies/hecke-finiteness-coverage.md](../studies/hecke-finiteness-coverage.md)
  — the finiteness targets and the routes through them.
- [../lean/logs/sturm-bound-port.md](../lean/logs/sturm-bound-port.md) — the
  measured port record.
