# Modular forms at the mathlib level

Second of the `base/` notes. Note [001](001-field-extensions-and-galois-basics.md)
set out the field-theoretic layer; this one sets out the automorphic layer:
what `CuspForm (CongruenceSubgroup.Gamma0 N) 2` actually is, what a
`q`-expansion is in Lean, and — most importantly — **how much of the classical
theory of Hecke operators is mathlib and how much is the FLT project's own**.
The answer is lopsided and worth stating up front: mathlib has the analytic
definitions, the level-one ring and its dimension formula, and nothing else;
everything arithmetic on the automorphic side (Hecke operators, the Hecke
algebra, newforms, the $`\Gamma_0(N)`$ dimension formula) is FLT code.

The shorthand from note 001 (§2–§6) is assumed: `K ≃ₐ[S] K` for Galois groups,
`ℚ̄` for `AlgebraicClosure ℚ`, and the `#L` citation convention of
[AGENTS.md](../AGENTS.md). Line numbers refer to
`anthropics/fermats-last-theorem@aa2d8b3`; mathlib to tag **v4.33.0**.

## 1. The three-layer definition

Mathlib's modular forms are analytic objects: holomorphic functions on the
upper half plane satisfying a slash-invariance condition. Everything is built
in three steps, each a structure extending the previous one — the first in its
own file ([SlashInvariantForms.lean, lines 32–39, v4.33.0](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/NumberTheory/ModularForms/SlashInvariantForms.lean#L32-L39)),
the other two together ([Basic.lean, lines 73–87, v4.33.0](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/NumberTheory/ModularForms/Basic.lean#L73-L87)):

```lean
structure SlashInvariantForm where          -- Basic.lean / SlashInvariantForms.lean
  toFun : ℍ → ℂ
  slash_action_eq' : ∀ γ ∈ Γ, toFun ∣[k] γ = toFun

structure ModularForm extends SlashInvariantForm Γ k where
  holo' : MDiff (toSlashInvariantForm : ℍ → ℂ)
  bdd_at_cusps' {c : OnePoint ℝ} (hc : IsCusp c Γ) : c.IsBoundedAt toFun k

structure CuspForm extends SlashInvariantForm Γ k where
  holo' : MDiff (toSlashInvariantForm : ℍ → ℂ)
  zero_at_cusps' {c : OnePoint ℝ} (hc : IsCusp c Γ) : c.IsZeroAt toFun k
```

Four things a reader has to internalise:

1. **`ℍ` is a type with a complex structure**, and `ℍ → ℂ` carries `MDiff`
   (mathlib's complex differentiability on manifolds), not `Differentiable`.
   `UpperHalfPlane` is a structure wrapping a `ℂ` with positive imaginary part
   ([UpperHalfPlane/Basic.lean, line 25](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/Analysis/Complex/UpperHalfPlane/Basic.lean#L25)),
   carrying `ChartedSpace ℂ ℍ` and `IsManifold 𝓘(ℂ) ω ℍ`
   ([UpperHalfPlane/Manifold.lean, lines 38, 41](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/Analysis/Complex/UpperHalfPlane/Manifold.lean#L38-L41)).
   The notation `f ∣[k] γ` is *not* a function called `slash`: it is
   `SlashAction.map k γ f`, a scoped notation instantiating a typeclass
   ([SlashActions.lean, lines 36–43](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/NumberTheory/ModularForms/SlashActions.lean#L36-L43)), for which both
   `GL (Fin 2) ℝ` and `SL(2, ℤ)` have instances, with the formula spelled out in
   `ModularForm.slash_apply` ([line 143](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/NumberTheory/ModularForms/SlashActions.lean#L143)).
2. **The level `Γ` is a `Subgroup (GL (Fin 2) ℝ)`**, not of `SL(2, ℤ)`. The
   arithmetic subgroup one writes down first (`CongruenceSubgroup.Gamma0 N :
   Subgroup SL(2, ℤ)`) is pushed into `GL` when used. In the FLT sources this
   appears as a coercion, and occasionally the coercion has to be computed:
   `(↑Γ(1) : Subgroup (GL (Fin 2) ℝ)) = 𝒮ℒ`
   ([S_ModularForm_S2_Gamma0_2_eq_zero.lean, lines 77–80](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularForm_S2_Gamma0_2_eq_zero.lean#L77-L80)).
3. **The weight `k` is an integer**, `ℤ` — not a natural, not a rational. A
   weight-2 form is `CuspForm Γ 2` with `2 : ℤ`.
4. **Promoting a `CuspForm` to a `ModularForm` is a coercion, but a
   non-obvious one.** Since `CuspForm` *repeats* the fields rather than
   extending `ModularForm`, the promotion is built by hand from the class
   instances ([ModularForms/Basic.lean, lines 141–149, v4.33.0](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/NumberTheory/ModularForms/Basic.lean#L141-L149)):

```lean
instance [FunLike F ℍ ℂ] [ModularFormClass F Γ k] : CoeTC F (ModularForm Γ k) :=
  ⟨ModularFormClass.modularForm⟩
```

   plus the instance that makes a `CuspForm` a `ModularFormClass` at all
   ([lines 491–494](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/NumberTheory/ModularForms/Basic.lean#L491-L494)):

```lean
instance (priority := 99) [FunLike F ℍ ℂ] [CuspFormClass F Γ k] : ModularFormClass F Γ k where
  slash_action_eq := SlashInvariantFormClass.slash_action_eq
  holo := CuspFormClass.holo
  bdd_at_cusps f _ hc g hg := (CuspFormClass.zero_at_cusps f hc g hg).boundedAtFilter
```

   So "a cusp form is a modular form" goes *through* the typeclass layer, which
   is why a lemma stated for an abstract `F` with `[ModularFormClass F Γ k]`
   applies to `F = CuspForm Γ k` for free. The same promotion is available as a
   linear map, `CuspForm.toModularFormₗ : CuspForm Γ k →ₗ[ℂ] ModularForm Γ k`
   ([CuspFormSubmodule.lean, lines 46–56](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/NumberTheory/ModularForms/CuspFormSubmodule.lean#L46-L56)),
   injective under `[Γ.HasDetOne]`. What a `CuspForm` coerces to *without* any
   of this is the underlying function `ℍ → ℂ` via `FunLike` — which is how the
   final `f = 0` in §7 is proved: `DFunLike.coe_injective` turns the bundled
   equality into the function equality.

The two structures are also not the only carriers of the property: there are
`ModularFormClass`/`CuspFormClass` typeclasses saying "this type of functions
behaves like a modular form", so that lemmas can be stated for an abstract `F`
with `[CuspFormClass F Γ k]`. FLT uses this heavily (`CuspForm.norm` is proved
at that level of generality), and it is the reason one sees
`(f : F) [FunLike F ℍ ℂ]` binders in the middle of modular-form proofs.

## 2. `Γ₀(N)` and the index bookkeeping

The congruence subgroups are defined in one file
([ModularForms/CongruenceSubgroups.lean, v4.33.0](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/NumberTheory/ModularForms/CongruenceSubgroups.lean)):

| Lean | Math | Line |
|---|---|---|
| `CongruenceSubgroup.Gamma N`, scoped notation `Γ(N)` | $`\Gamma(N) = \ker(\mathrm{SL}_2(\mathbb{Z}) \to \mathrm{SL}_2(\mathbb{Z}/N))`$ | [line 41](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/NumberTheory/ModularForms/CongruenceSubgroups.lean#L41) |
| `CongruenceSubgroup.Gamma0 N` | $`\Gamma_0(N)`$: lower-left entry $`\equiv 0`$ mod $`N`$ | [line 79](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/NumberTheory/ModularForms/CongruenceSubgroups.lean#L79) |
| `CongruenceSubgroup.Gamma1 N` | $`\Gamma_1(N)`$: lower-left $`\equiv 0`$, diagonal $`\equiv 1`$ | [line 131](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/NumberTheory/ModularForms/CongruenceSubgroups.lean#L131) |
| `CongruenceSubgroup.Gamma0Map N : Gamma0 N →* ZMod N` | the map $`\begin{pmatrix} a & b \\ 0 & d \end{pmatrix} \mapsto d`$ | [line 95](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/NumberTheory/ModularForms/CongruenceSubgroups.lean#L95) |

**Mathlib does not know $`[\mathrm{SL}_2(\mathbb{Z}) : \Gamma_0(N)]` for any
$`N`$.** It has the general finite-index machinery (`Subgroup.index`,
`IsFiniteRelIndex`, the `finiteIndex_of_le` lemmas around lines 293–319 of the
same file) but no evaluation for $`\Gamma_0(N)`$. FLT supplies the one case it
needs as a theorem:

```lean
-- S_ModularForm_S2_Gamma0_2_eq_zero.lean, lines 170–173
theorem Gamma0_two_index_eq_three : (CongruenceSubgroup.Gamma0 2).index = 3
```

proved by exhibiting the three cosets through an explicit map to
$`\mathbb{P}^1(\mathbb{F}_2)`$ (the `firstColMod2`/`cosetToProj` block, lines
97–167). The group-theoretic shape of the space
$`S_2(\Gamma_0(N))`$ therefore has to be built by hand in this project.

## 3. `q`-expansions: mathlib's half of the bridge

Everything arithmetic enters through the $`q`$-expansion, and mathlib does have
it ([ModularForms/QExpansion.lean, line 167, v4.33.0](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/NumberTheory/ModularForms/QExpansion.lean#L167)):

```lean
def qExpansion (f : ℍ → ℂ) : PowerSeries ℂ :=
  .mk fun m ↦ (↑m.factorial)⁻¹ * iteratedDeriv m (cuspFunction h f) 0
```

Three points about this definition:

- It is the Taylor expansion of `cuspFunction h f` at $`q = 0`$, where
  $`q = \exp(2\pi i \tau/h)`$ and `h` is a *strict period* of `Γ`. For the
  classical case $`h = 1`$ one writes `qExpansion 1 f`; FLT always does. The
  width is genuinely needed at general level: mathlib proves
  `strictWidthInfty_Gamma0 N = 1` and `strictWidthInfty_Gamma1 N = 1` but
  `strictWidthInfty_Gamma N = N` ([Cusps.lean, lines 447, 452, 472](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/NumberTheory/ModularForms/Cusps.lean#L447-L472)),
  so a form on `Γ(N)` needs `qExpansion N f`, while `Γ₀(N)` and `Γ₁(N)` are
  width 1.
- It requires `h ∈ Γ.strictPeriods` for the theorems, so the `h = 1` case is
  only available for `Γ ⊆ SL(2, ℤ)` — the ambient `GL`-level groups are handled
  by the `[Γ.HasDetPlusMinusOne]` / `[Γ.HasDetOne]` hypotheses. Periodicity in
  $`\tau \mapsto \tau + h`$ is `SlashInvariantForm.vAdd_apply_of_mem_strictPeriods`
  ([Identities.lean, line 26](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/NumberTheory/ModularForms/Identities.lean#L26));
  for level one, `1` is a strict period
  ([LevelOne/Basic.lean, line 68](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/NumberTheory/ModularForms/LevelOne/Basic.lean#L68)).
- The result is a `PowerSeries ℂ`, so the coefficient is `.coeff n`, and the
  whole content of "the $`n`$-th Fourier coefficient of $`f`$" is a one-line
  wrapper. FLT's version is exactly that
  ([Def_FLTPrelim_Modularity.lean, lines 19–20](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_FLTPrelim_Modularity.lean#L19-L20)):

```lean
namespace ModularFormClass
def qCoeff (f : ℍ → ℂ) (n : ℕ) : ℂ :=
  (qExpansion 1 f).coeff n
end ModularFormClass
```

`ModularFormClass.qCoeff` is the single most-used automorphic symbol in the
rest of the project: modularity, level lowering, and the Hecke recursions are
all stated as equations between `qCoeff f n` and an arithmetic quantity.

## 4. What mathlib does *not* have

This is the part that saves the most time if read before grepping. In
mathlib v4.33.0's `Mathlib/NumberTheory/ModularForms/` (39 files) there is:

- **no Hecke operator of any kind** — no `T_p`, no `U_p`, no Hecke algebra, no
  eigenform predicate, no newform/oldform, no Atkin–Lehner. (There *is* a
  group-theoretic `HeckeRing`/`HeckeCoset`/`HeckeCosetModule` in
  [NumberTheory/HeckeRing/Defs.lean](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/NumberTheory/HeckeRing/Defs.lean),
  but it imports nothing about modular forms and has no action on them — the
  name `HeckeAlgebra` does not occur anywhere in mathlib.)
- **no dimension formula for $`\Gamma_0(N)`$** — only level one
  ([DimensionFormulas/LevelOne.lean](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/NumberTheory/ModularForms/DimensionFormulas/LevelOne.lean)
  is an 11-line stub re-exporting
  `Mathlib/NumberTheory/ModularForms/LevelOne/DimensionFormula.lean`, whose
  content is the level-one dimension formula
  `ModularForm.dimension_level_one` at
  [line 248](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/NumberTheory/ModularForms/LevelOne/DimensionFormula.lean#L248),
  the finiteness instance `FiniteDimensional ℂ (ModularForm 𝒮ℒ k)` at
  [line 272](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/NumberTheory/ModularForms/LevelOne/DimensionFormula.lean#L272),
  and the two vanishing lemmas
  [`CuspForm.rank_eq_zero_of_weight_lt_twelve` (line 153)](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/NumberTheory/ModularForms/LevelOne/DimensionFormula.lean#L153)
  and [`levelOne_weight_two_rank_zero` (line 243)](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/NumberTheory/ModularForms/LevelOne/DimensionFormula.lean#L243),
  plus a level-one Sturm bound at
  [line 305](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/NumberTheory/ModularForms/LevelOne/DimensionFormula.lean#L305));
- **no $`\Gamma_0(N)`$ index formula** (see §2), and **no finiteness or
  dimension statement at any level other than $`\mathcal{SL}`$**;
- level one content only: the ring of modular forms and its structure theorem,
  the discriminant as a bundled cusp form `CuspForm.discriminant : CuspForm 𝒮ℒ 12`
  ([Discriminant.lean, line 237](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/NumberTheory/ModularForms/Discriminant.lean#L237)),
  Eisenstein series `E₄`, `E₆` as `ModularForm 𝒮ℒ 4`, `𝒮ℒ 6`
  ([EisensteinSeries/Basic.lean, lines 51, 54](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/NumberTheory/ModularForms/EisensteinSeries/Basic.lean#L51-L54)),
  Jacobi theta, Dedekind eta, Petersson inner product, `LFunction`;
- one caveat on `E₂`: mathlib's `EisensteinSeries.E2` is only the *function*
  `ℍ → ℂ` ([E2/Defs.lean, line 60](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/NumberTheory/ModularForms/EisensteinSeries/E2/Defs.lean#L60)) —
  it is holomorphic and bounded at $`\infty`$ but not slash-invariant, so it is
  **not** a `ModularForm`. There is no identifier `E₂` in mathlib;
- the **norm map** $`S_k(\mathcal{G}) \to S_{k[\mathcal{H}:\mathcal{G}]}(\mathcal{H})`$,
  which is mathlib's one genuinely higher-level tool
  ([ModularForms/NormTrace.lean, lines 64, 108, v4.33.0](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/NumberTheory/ModularForms/NormTrace.lean#L64-L108)):

```lean
protected def SlashInvariantForm.norm [ℋ.HasDetPlusMinusOne] : SlashInvariantForm ℋ (k * Nat.card 𝒬)
...
protected def ModularForm.norm [ℋ.HasDetPlusMinusOne] [ModularFormClass F 𝒢 k] :
    ModularForm ℋ (k * Nat.card 𝒬)
```

Here `𝒬 = ℋ ⧸ (𝒢.subgroupOf ℋ)`, so the weight is multiplied by the *index* of
the smaller level in the larger. Note the asymmetry: mathlib has the norm for
`SlashInvariantForm` and `ModularForm`, and a *trace* (same level, same weight)
for `CuspForm` ([line 94](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/NumberTheory/ModularForms/NormTrace.lean#L94)) —
but no `CuspForm` norm. FLT has to build that itself (§7).

The picture in one line: **mathlib supplies the analytic objects and their
level-one dimensions; FLT supplies everything arithmetic — Hecke operators,
eigenforms, newforms, levels above one.**

## 5. The Hecke layer, as FLT builds it

Mathlib has no Hecke operators, so FLT defines them from explicit matrices on
the upper half plane ([Def_ModularForm_HeckeOperator.lean, lines 11–22, 93–96](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularForm_HeckeOperator.lean#L11-L96)):

```lean
def upperTriangularGL (a b d : ℝ) (had : a * d ≠ 0) : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![a, b; 0, d] ...

def heckeMatrix (p j : ℕ) : GL (Fin 2) ℝ := ... upperTriangularGL 1 j p ...
def heckeDiagMatrix (p : ℕ) : GL (Fin 2) ℝ := ... upperTriangularGL p 0 1 ...

def heckeU (k : ℤ) (p : ℕ) (f : UpperHalfPlane → ℂ) : UpperHalfPlane → ℂ :=
  ∑ j ∈ Finset.range p, f ∣[k] heckeMatrix p j

def heckeT (k : ℤ) (p : ℕ) (f : UpperHalfPlane → ℂ) : UpperHalfPlane → ℂ :=
  heckeU k p f + f ∣[k] heckeDiagMatrix p
```

So the classical sums over coset representatives of the double coset
$`\Gamma \begin{pmatrix} p & 0 \\ 0 & 1 \end{pmatrix} \Gamma`$ are, in Lean,
literally finite sums `∑ j ∈ Finset.range p` of slash actions by the explicit
matrices $`\begin{pmatrix} 1 & j \\ 0 & p \end{pmatrix}`$ and
$`\begin{pmatrix} p & 0 \\ 0 & 1 \end{pmatrix}`$. From there FLT wraps them as
linear maps on the bundled spaces, splitting on whether the prime divides the
level ([Def_ModularForm_HeckeOperatorForms.lean, lines 20 and 34](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularForm_HeckeOperatorForms.lean#L20-L34)):

```lean
def heckeTLin (k : ℤ) (hp : p.Prime) (hpN : ¬ p ∣ N) :
    ModularForm (CongruenceSubgroup.Gamma0 N) k →ₗ[ℂ] ModularForm (CongruenceSubgroup.Gamma0 N) k

def heckeULin (k : ℤ) [NeZero N] (hpN : p ∣ N) :
    ModularForm (CongruenceSubgroup.Gamma0 N) k →ₗ[ℂ] ModularForm (CongruenceSubgroup.Gamma0 N) k
```

(and the `CuspForm` versions below them). The names encode the arithmetic:
`heckeTLin` is $`T_p`$ for $`p \nmid N`$, `heckeULin` is $`U_p`$ for $`p \mid N`$ —
precisely the two cases in the classical eigenform recursions.

**The Hecke algebra is a `Subalgebra` of endomorphisms**
([Def_CuspForm_HeckeAlgebra.lean, lines 14–18](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_CuspForm_HeckeAlgebra.lean#L14-L18)):

```lean
def heckeGenerators : Set (Module.End ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) k)) :=
  {T | ∃ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N), ℓ ∉ S ∧ T = heckeTLin k hℓ hℓN} ∪
    {U | ∃ (q : ℕ) (hqN : q ∣ N), q.Prime ∧ q ∉ S ∧ U = heckeULin k hqN}

def heckeAlgebra : Subalgebra ℤ (Module.End ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) k)) :=
  Algebra.adjoin ℤ (heckeGenerators N k S)
```

with commutativity as an instance
([line 59](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_CuspForm_HeckeAlgebra.lean#L59)), so that the eigenform
decomposition machinery of linear algebra applies. That is the whole reason the
commutativity of $`T_\ell`$'s is proved in this project rather than assumed: it
is what makes "simultaneous eigenform" a meaningful notion to bundle.

## 6. `IsNormalizedEigenform`: the definition the FLT project actually uses

Everything above is infrastructure for one structure
([Def_FLTPrelim_Modularity.lean, lines 28–40](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_FLTPrelim_Modularity.lean#L28-L40)):

```lean
structure IsNormalizedEigenform {N : ℕ} (f : CuspForm (CongruenceSubgroup.Gamma0 N) 2) :
    Prop where
  qCoeff_one : qCoeff f 1 = 1
  qCoeff_mul_of_coprime : ∀ m n : ℕ, m.Coprime n →
    qCoeff f (m * n) = qCoeff f m * qCoeff f n
  qCoeff_prime_pow_of_not_dvd : ∀ p r : ℕ, p.Prime → ¬ p ∣ N →
    qCoeff f (p ^ (r + 2)) = qCoeff f p * qCoeff f (p ^ (r + 1)) - p * qCoeff f (p ^ r)
  qCoeff_prime_pow_of_dvd : ∀ p r : ℕ, p.Prime → p ∣ N →
    qCoeff f (p ^ (r + 2)) = qCoeff f p * qCoeff f (p ^ (r + 1))
```

This is the classical definition of a normalised weight-2 eigenform for
$`\Gamma_0(N)`$, *stated purely as recursions on the `q`-expansion
coefficients* — the Hecke operators themselves never appear. That is deliberate
and it is the single most useful thing to know about the automorphic side of
this project: to use a modularity hypothesis one only ever has to unfold to
the four clauses above.

**Why the recursions are the Hecke eigenform condition.** With the notation
$`f = \sum_m u_m q^m`$ and $`\lambda_p = u_p`$, a direct computation from the
slash definitions of §5 gives the $`q`$-expansions

- $`T_p f = \sum_m (u_{mp} + p^{k-1} u_{m/p}) q^m`$ for $`p \nmid N`$,
- $`U_p f = \sum_m u_{mp} q^m`$ for $`p \mid N`$,

where $`u_{m/p}`$ is read as $`0`$ unless $`p \mid m`$. In weight $`k = 2`$ the
first is $`u_{mp} + p\,u_{m/p}`$, so:
$`T_p f = u_p f`$ at $`m = p^{r+1}`$ is exactly
$`u_p u_{p^{r+1}} = u_{p^{r+2}} + p\,u_{p^r}`$, the third clause read
left-to-right; and $`U_p f = u_p f`$ at the same $`m`$ is exactly the fourth
clause. So the structure says "normalised, and a simultaneous eigenvector of
all the $`T_p`$, $`p \nmid N`$, and $`U_q`$, $`q \mid N`$", with the coprimality
clause encoding multiplicativity of the coefficients. Normalisation
$`u_1 = 1`$ is what makes the eigen*value* equal to $`u_p`$, which is why
`qCoeff f p` can be used as the eigenvalue with no extra data.

The $`U_p`$ computation is the easy one: $`(f \mid_k \begin{pmatrix} 1 & j \\ 0 & p \end{pmatrix})(\tau) = p^{-k} f((\tau+j)/p)`$,
and summing over $`j`$ extracts the $`q`$-coefficients with $`p \mid m`$. For
$`T_p`$ the extra term is $`f \mid_k \begin{pmatrix} p & 0 \\ 0 & 1 \end{pmatrix} = p^{k-1} f(p\tau)`$,
which contributes $`p^{k-1} u_{m/p}`$; the two together give the first display.
The same dictionary is used in the project for the $`\Gamma_1`$ case with a
Dirichlet character (Nebentypus), where the eigenform property is likewise a
coefficient recursion
([Def_CuspForm_PrimitiveFormGamma1.lean, lines 19–26](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_CuspForm_PrimitiveFormGamma1.lean#L19-L26)),
and the rewrite from eigenform-plus-character to the operator equation
`heckeU + ε • slash heckeDiagMatrix = qCoeff · id` is a theorem
([Thm_CuspForm_IsEigenformWith_heckeU_add_smul_slash_heckeDiagMatrix_eq_qCoeff_smul.lean, line 17](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_CuspForm_IsEigenformWith_heckeU_add_smul_slash_heckeDiagMatrix_eq_qCoeff_smul.lean#L17)).

For a human reader the classical statement is: $`f`$ is a normalised
eigenform, `a_p(f) = qCoeff f p`, and the whole arithmetic content of $`f`$ is
its coefficient sequence.

## 7. Where the layer is cashed in

| Use | Mathematical content | Where |
|---|---|---|
| modularity | $`a_\ell(W) = a_\ell(f)`$ for all good $`\ell \nmid N`$ | `IsModularModelOfLevel`, [Def_FLTPrelim_Modularity.lean, lines 93–99](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_FLTPrelim_Modularity.lean#L93-L99) |
| a curve is modular | some integral model is modular *for some level* | `IsModular`, [lines 101–102](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_FLTPrelim_Modularity.lean#L101-L102) |
| the $`a_p`$ on the elliptic side | point count on the reduction: $`a_p = \#\mathbb{F}_p + 1 - \#E(\mathbb{F}_p)`$ | `traceOfFrobenius`, `apOfModel`, [lines 70–80](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_FLTPrelim_Modularity.lean#L70-L80) |
| residual level lowering | congruence of `qCoeff f ℓ` with $`a_\ell(W)`$ **modulo a maximal ideal** $`\mathfrak{m} \ni p`$, not equality | `ModularRepOfLevel`, [Def_FLTPrelim_ModularRep.lean, lines 62–69](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_FLTPrelim_ModularRep.lean#L62-L69) |
| residual modularity of a model | the same congruence with the level as a parameter | `IsResiduallyModularOfLevel`, [lines 75–80](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_FLTPrelim_ModularRep.lean#L75-L80) |
| **the endgame, $`S_2(\Gamma_0(2)) = 0`$** | $`[\mathrm{SL}_2(\mathbb{Z}):\Gamma_0(2)] = 3`$ and the norm multiplies weight by the index, so a weight-2 form would give a level-one form of weight $`2 \cdot 3 = 6 < 12`$, killed by mathlib's dimension formula | `ModularForm.S2_Gamma0_2_eq_zero`, [S file, lines 170–211](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularForm_S2_Gamma0_2_eq_zero.lean#L170-L211) |

The last row is worth expanding, because it is the one place where the
automorphic side of FLT is genuinely short. The proof is three moves
([S_ModularForm_S2_Gamma0_2_eq_zero.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularForm_S2_Gamma0_2_eq_zero.lean)):

1. `CuspForm.norm_eq_zero_iff` ([lines 62–66](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularForm_S2_Gamma0_2_eq_zero.lean#L62-L66)):
   the norm from $`\Gamma_0(2)`$ up to $`\Gamma(1) = \mathrm{SL}_2(\mathbb{Z})`$
   is injective on cusp forms, so it suffices to kill its image. The norm itself
   is project code ([lines 34–51](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularForm_S2_Gamma0_2_eq_zero.lean#L34-L51)):
   it extends mathlib's `ModularForm.norm` and supplies the missing
   `zero_at_cusps'` field, which is where the work is (a product of functions
   tending to zero at the cusps).
2. `Gamma0_two_index_eq_three` ([line 170](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularForm_S2_Gamma0_2_eq_zero.lean#L170))
   plus `card_quotient_eq_three` ([line 176](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularForm_S2_Gamma0_2_eq_zero.lean#L176)):
   the index is 3, so `CuspForm.norm` produces a level-one cusp form of weight
   $`2 \cdot 3 = 6`$ — the arithmetic `hweight` at
   [lines 197–199](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularForm_S2_Gamma0_2_eq_zero.lean#L197-L199).
3. `S6_levelOne_eq_zero` ([lines 86–89](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularForm_S2_Gamma0_2_eq_zero.lean#L86-L89)),
   which is mathlib's `CuspForm.rank_eq_zero_of_weight_lt_twelve` applied at
   $`k = 6`$.

So the project's own contribution here is the index computation and the
injectivity of the norm; the vanishing itself is mathlib's level-one dimension
formula. The classical genus-0 statement "$`X_0(2)`$ has genus 0" is not used
and does not appear.

## 8. Small traps

- **`CuspForm Γ k` has no `ModularForm` as a field**, and the coercion of §1.4
  routes through `ModularFormClass` rather than through a projection. `f = 0`
  for a `CuspForm` is proved by function extensionality after
  `DFunLike.coe_injective`, as at the end of the `S2_Gamma0_2` proof.
- **`qExpansion` takes a bare function `ℍ → ℂ`, not a bundled form**, and it
  needs a strict period `h` and (for the interesting lemmas) hypotheses like
  `[Γ.HasDetPlusMinusOne]`. FLT's `qExpansion 1 f` works because the level is
  coerced into `GL` and `1` is a strict period for the arithmetic subgroups.
- **Do not expect mathlib to have `T_p`.** A grep for `heckeT` in mathlib
  returns nothing; the identifier is FLT's. Conversely, do not expect FLT's
  `heckeT` to be mathlib's `T_p` notation: FLT uses `heckeTLin`/`heckeULin`
  with the "does `p` divide the level" split baked into the name.
- **`↑Γ₀(2) ≠ Γ(1)` as subgroups of `GL (Fin 2) ℝ` unless you coerce**, and the
  coercion needs `CongruenceSubgroup.Gamma_one_top` plus
  `Subgroup.mem_map`/`MonoidHom.mem_range` reasoning (`coe_Gamma_one_eq_SL`,
  [lines 77–80](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularForm_S2_Gamma0_2_eq_zero.lean#L77-L80)).
- **The residual statements are congruences, not equalities.** The Galois-side
  notes (004, 006) meet the automorphic side only through
  `ModularRepOfLevel`'s `a - ((W.apOfModel ℓ : ℤ) : integralClosure ℤ ℂ) ∈ 𝔪`
  clause — an ideal membership, which is why the coefficient comparisons live in
  `integralClosure ℤ ℂ` rather than in `ℂ`.

## 9. Links

File-level pointers; anchored citations are inline above.

FLT sources at the pinned sha `aa2d8b3`:

- [Def_FLTPrelim_Modularity.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_FLTPrelim_Modularity.lean) — `qCoeff`, `IsNormalizedEigenform`, `apOfModel`, `IsModular`
- [Def_FLTPrelim_ModularRep.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_FLTPrelim_ModularRep.lean) — `ModularRepOfLevel`, `IsResiduallyModularOfLevel`
- [Def_ModularForm_HeckeOperator.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularForm_HeckeOperator.lean) — `heckeMatrix`, `heckeDiagMatrix`, `heckeU`, `heckeT`
- [Def_ModularForm_HeckeOperatorForms.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularForm_HeckeOperatorForms.lean) — `heckeTLin`, `heckeULin` on `ModularForm` and `CuspForm`
- [Def_CuspForm_HeckeAlgebra.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_CuspForm_HeckeAlgebra.lean) — `heckeGenerators`, `heckeAlgebra`, commutativity
- [Thm_ModularForm_S2_Gamma0_2_eq_zero.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularForm_S2_Gamma0_2_eq_zero.lean) and [S_ModularForm_S2_Gamma0_2_eq_zero.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularForm_S2_Gamma0_2_eq_zero.lean) — the endgame
- [Def_HeckeGalois_EichlerShimura.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_HeckeGalois_EichlerShimura.lean) — the abstract Hecke algebra `HeckeAlg = MvPolynomial Nat.Primes ℤ` and eigenideals (the bridge to the Galois side)

Mathlib v4.33.0:

- [Modular form and cusp form structures](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/NumberTheory/ModularForms/Basic.lean#L80-L87)
- [Slash invariance](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/NumberTheory/ModularForms/SlashInvariantForms.lean#L34-L44) and [slash actions](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/NumberTheory/ModularForms/SlashActions.lean)
- [`qExpansion`](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/NumberTheory/ModularForms/QExpansion.lean#L167)
- [Congruence subgroups `Γ(N)`, `Γ₀(N)`, `Γ₁(N)`](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/NumberTheory/ModularForms/CongruenceSubgroups.lean#L41-L131)
- [`CuspForm.rank_eq_zero_of_weight_lt_twelve`](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/NumberTheory/ModularForms/LevelOne/DimensionFormula.lean#L153)
- [The norm map on modular/cusp forms](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/NumberTheory/ModularForms/NormTrace.lean#L94-L110)
- [Level-one modular forms, `Δ`, Eisenstein series](https://github.com/leanprover-community/mathlib4/tree/v4.33.0/Mathlib/NumberTheory/ModularForms/LevelOne)

Background:

- F. Diamond and J. Im, *Modular forms and modular curves*, in Seminar on
  Fermat's Last Theorem (the classical Hecke-recursion and eigenform
  dictionary, including the $`T_p`$/`U_p` split by level).
- H. Darmon, F. Diamond, R. Taylor, *Fermat's Last Theorem*, Current
  Developments in Mathematics 1995, §2 — the route PROOF-PATH.md follows.
