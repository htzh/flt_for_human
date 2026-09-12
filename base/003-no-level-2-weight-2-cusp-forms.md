# No level-2 weight-2 cusp forms

Third of the `base/` notes. Note [001](001-field-extensions-and-galois-basics.md)
built the field/Galois vocabulary and note [002](002-modular-forms-basics.md)
built the automorphic one (`SlashInvariantForm`/`CuspForm`, `qExpansion`,
`Γ₀(N)`). This note takes one concrete computation and follows it to the end:

$$S_2(\Gamma_0(2)) = 0,$$

every weight-2 cusp form on $`\Gamma_0(2)`$ is zero. It is the last automorphic
input of the FLT route: after Ribet's level lowering has pushed a nonzero residual
representation down to a level dividing $`2`$, this is the statement that kills
it ([math/008 §5](../math/008-ribet-level-lowering.md)). The companion note
already sketched the Lean mechanism; here we do the mathematics and use the Lean
declarations only as a route map.

The proof has exactly three moves:

1. $`[\mathrm{SL}_2(\mathbb{Z}) : \Gamma_0(2)] = 3`$, counted through the first
   column modulo $`2`$.
2. A **norm** construction turns a nonzero weight-$`k`$ cusp form on any
   finite-index subgroup into a nonzero level-one cusp form of weight
   $`k \cdot [\mathrm{SL}_2(\mathbb{Z}) : \Gamma_0(2)]`$ — here $`2 \cdot 3 = 6`$.
3. $`S_6(\mathrm{SL}_2(\mathbb{Z})) = 0`$, because in fact
   $`S_k(\mathrm{SL}_2(\mathbb{Z})) = 0`$ for every $`k < 12`$.

Move 3 is the only one with analytic content, and it is worth doing honestly: it
reduces to *a holomorphic function on the unit disc whose modulus at every point
is bounded by its modulus at some point of an interior smaller disc is constant*.
Section 4 unwinds it that far.

Line-number citations point at `anthropics/fermats-last-theorem@aa2d8b3`; mathlib
citations point at tag **v4.33.0** (`db584cd6…`). Both are rendered GitHub links,
so the cited region is highlighted on click.

## 1. The statement, and the shape of the contradiction

The headline declaration is

```lean
-- Theorems/Thm_ModularForm_S2_Gamma0_2_eq_zero.lean, line 13
theorem ModularForm.S2_Gamma0_2_eq_zero (f : CuspForm (CongruenceSubgroup.Gamma0 2) 2) : f = 0
```

The same statement at level 1, $`S_2(\mathrm{SL}_2(\mathbb{Z})) = 0`$, holds for
the simpler reason $`2 < 12`$ directly
([`Thm_ModularForm_S2_Gamma0_one_eq_zero.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularForm_S2_Gamma0_one_eq_zero.lean)); level $`2`$ is
the one case where move 2 is needed, because $`2`$ by itself is not $`< 12`$ but
$`2 \cdot 3`$ is.

The contradiction runs as follows. Assume $`0 \ne f \in S_2(\Gamma_0(2))`$.
Move 2 gives a level-one cusp form $`\mathrm{Norm}(f)`$ of weight $`6`$, and
move 2 also says the norm vanishes *only* on zero forms, so
$`\mathrm{Norm}(f) \ne 0`$. Move 3 says every weight-6 level-one cusp form is
zero. Contradiction.

The two project lemmas in which moves 1 and 2 are cashed out are
`Gamma0_two_index_eq_three`
([S file, lines 170–174](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularForm_S2_Gamma0_2_eq_zero.lean#L170-L174))
and `CuspForm.norm_eq_zero_iff`
([S file, lines 62–66](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularForm_S2_Gamma0_2_eq_zero.lean#L62-L66)).
The final assembly is `S2_Gamma0_2_eq_zero'`
([S file, lines 195–206](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularForm_S2_Gamma0_2_eq_zero.lean#L195-L206)):
the norm is built, its weight is computed to be $`6`$, and
`S6_levelOne_eq_zero` kills it.

## 2. Move 1: the index is three

Let
$`\Gamma_0(2) = \{\begin{pmatrix} a & b \\ c & d\end{pmatrix} \in \mathrm{SL}_2(\mathbb{Z}) : c \equiv 0 \bmod 2\}`$
and $`G = \mathrm{SL}_2(\mathbb{Z})`$. The claim is $`[G : \Gamma_0(2)] = 3`$,
equivalently that $`G/\Gamma_0(2)`$ has three elements. The proof exhibits a
bijection

$$G/\Gamma_0(2) \\;\longleftrightarrow\\; (\mathbb{Z}/2)^2 \setminus \\{0\\},$$

the three nonzero vectors. The map is: send a matrix to its **first column**
modulo $`2`$. That is the whole idea; the rest is checking that it is
well-defined, injective and surjective, and each check is a two-line matrix
computation. In the Lean sources this is the block
`firstColMod2`/`cosetToProj`
([S file, lines 94–168](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularForm_S2_Gamma0_2_eq_zero.lean#L94-L168)).

Write $`g = \begin{pmatrix} a & b \\ c & d\end{pmatrix}`$ and let
$`\phi(g) = (a, c) \in (\mathbb{Z}/2)^2`$.

**Step 1: the first column is never zero.** Reducing $`\det g = ad - bc = 1`$
modulo $`2`$ gives $`\bar a \bar d - \bar b \bar c = 1`$ in $`\mathbb{F}_2`$. If
$`\bar a = \bar c = 0`$, the left side is $`0`$, a contradiction. So
$`\phi(g) \ne 0`$. (This is `firstColMod2_ne_zero`, whose input is the
determinant identity `det_eq_one_mod2`; the identity is used again below.)

**Step 2: $`\phi`$ is constant on left cosets.** Let
$`h = \begin{pmatrix} a' & b' \\ c' & d'\end{pmatrix} \in \Gamma_0(2)`$, so
$`\bar c' = 0`$. Its determinant is $`1`$ too, so $`\bar a' \bar d' = 1`$ in
$`\mathbb{F}_2`$; the only invertible element of $`\mathbb{F}_2`$ is $`1`$,
hence $`\bar a' = \bar d' = 1`$. Therefore the first column of $`h`$ is
$`(1, 0)`$, and

$$gh = \begin{pmatrix} a & b \\\\ c & d\end{pmatrix} h
\quad\Longrightarrow\quad
\text{first column of } gh = g \cdot \begin{pmatrix} 1 \\\\ 0\end{pmatrix}
= \text{first column of } g .$$

So $`\phi(gh) = \phi(g)`$ for every $`h \in \Gamma_0(2)`$, which is exactly what
is needed for $`\phi`$ to descend to $`G/\Gamma_0(2)`$. (This is
`firstColMod2_mul_mem`, with `Gamma0_two_diag_eq_one` supplying
$`\bar a' = 1`$.) Note that the Lean quotient `G ⧸ Γ₀(2)` is the set of left
cosets with the relation $`x^{-1}y \in \Gamma_0(2)`$, and right multiplication by
$`\Gamma_0(2)`$ stays inside a left coset, so right-invariance is the correct
side.

**Step 3: injectivity.** Suppose $`\phi(g_1) = \phi(g_2)`$, i.e. $`a_1 \equiv a_2`$
and $`c_1 \equiv c_2`$ mod $`2`$. We must show
$`g_1^{-1} g_2 \in \Gamma_0(2)`$, i.e. that the lower-left entry of the product is
even. Since $`\det g_1 = 1`$,

$$g_1^{-1} = \begin{pmatrix} d_1 & -b_1 \\\\ -c_1 & a_1\end{pmatrix},$$

so the lower-left entry of $`g_1^{-1} g_2`$ is $`(-c_1)a_2 + a_1 c_2`$. Reducing
mod $`2`$ and substituting $`a_1 \equiv a_2 =: a`$, $`c_1 \equiv c_2 =: c`$,

$$-c_1 a_2 + a_1 c_2 \\;\equiv\\; -c\\,a + a\\,c \\;=\\; 0 \pmod 2 .$$

Hence $`g_1^{-1} g_2 \in \Gamma_0(2)`$ and $`g_1, g_2`$ are in the same left
coset. (This is `cosetToProj_injective`; it is the only place where the explicit
inverse matrix is needed.)

**Step 4: surjectivity.** The three nonzero vectors of $`(\mathbb{Z}/2)^2`$ are
realized by

$$I = \begin{pmatrix} 1 & 0 \\\\ 0 & 1\end{pmatrix} \mapsto (1,0), \qquad
S = \begin{pmatrix} 0 & -1 \\\\ 1 & 0\end{pmatrix} \mapsto (0,1), \qquad
\begin{pmatrix} 1 & 0 \\\\ 1 & 1\end{pmatrix} \mapsto (1,1),$$

all three matrices lying in $`\mathrm{SL}_2(\mathbb{Z})`$ (determinant $`1`$).
This is `cosetToProj_surjective`, with the three cases discharged by `decide`.

Putting the four steps together gives the bijection, hence

```lean
-- S_ModularForm_S2_Gamma0_2_eq_zero.lean, lines 170–174
theorem Gamma0_two_index_eq_three : (CongruenceSubgroup.Gamma0 2).index = 3
```

**The same count, geometrically.** $`\mathrm{SL}_2(\mathbb{F}_2)`$ has order
$`6`$ and acts faithfully on the three nonzero vectors, transitively; the
stabilizer of $`(1,0)`$ has order $`2`$, and $`\Gamma_0(2)`$ is exactly its
preimage in $`\mathrm{SL}_2(\mathbb{Z})`$ (with $`\Gamma(2)`$, the reduction
kernel, sitting inside it). Hence the index is the orbit size,
$`6/2 = 3`$. The proof above does not pass to $`\mathrm{SL}_2(\mathbb{F}_2)`$
at all — it computes directly with the first column — but the two counts are the
same count.

## 3. Move 2: the norm multiplies the weight by the index

### The slash action, briefly

The norm is built by **translating** $`f`$ by matrices, so we need the slash
action on functions. Note 002 §1 records that the notation $`f \mid_k \gamma`$ is
the typeclass method `SlashAction.map` rather than a function named `slash`; here
is the formula and the two properties this section uses.

For
$`\gamma = \begin{pmatrix} a & b \\ c & d\end{pmatrix} \in \mathrm{GL}_2(\mathbb{R})`$
and $`z \in \mathbb{H}`$, write $`\gamma z = (az+b)/(cz+d)`$ for the Möbius action
and $`cz+d`$ for the denominator (mathlib's `denom γ z`). Then

$$(f \mid_k \gamma)(z) = \sigma_\gamma\bigl(f(\gamma z)\bigr)\\,|\det\gamma|^{k-1}\\,(cz+d)^{-k},$$

where $`\sigma_\gamma`$ is the identity if $`\det\gamma > 0`$ and complex
conjugation if $`\det\gamma < 0`$ (mathlib's `slash_apply`,
[SlashActions.lean, lines 143–145](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/NumberTheory/ModularForms/SlashActions.lean#L143-L145)).
Two properties are all we use:

1. **Composition.** $`f \mid_k (\gamma\delta) = (f \mid_k \gamma) \mid_k \delta`$,
   i.e. $`\mid_k`$ is a right action (mathlib's `slash_mul`,
   [SlashActions.lean, lines 99–111](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/NumberTheory/ModularForms/SlashActions.lean#L99-L111)).
2. **Invariance *is* the definition of a form.** A weight-$`k`$ form on a subgroup
   $`\Gamma`$ is a function with $`f \mid_k \gamma = f`$ for every
   $`\gamma \in \Gamma`$; that is exactly the field `slash_action_eq'` of
   `SlashInvariantForm`.

For $`\gamma \in \mathrm{SL}_2(\mathbb{Z})`$ the determinant is $`1`$ and
$`\sigma_\gamma`$ is the identity, so the formula collapses to

$$(f \mid_k \gamma)(z) = (cz+d)^{-k} f(\gamma z),$$

and invariance reads $`f(\gamma z) = (cz+d)^k f(z)`$ — the identity used in §4.2
Step B. The $`|\det\gamma|^{k-1}`$ factor is what makes composition hold at
determinants other than $`1`$; everything in this note has determinant $`\pm 1`$,
where it is $`1`$.

### The norm, and its four properties

Let $`\Gamma \le \mathcal{H} \le \mathrm{GL}_2(\mathbb{R})`$ with $`\Gamma`$ of
finite index $`N`$ in $`\mathcal{H}`$, and suppose
$`\mathcal{H} \subset \{\det = \pm 1\}`$ (in the application both groups lie in
$`\mathrm{SL}_2(\mathbb{Z})`$, so this is automatic). For a form $`f`$ of weight
$`k`$ on $`\Gamma`$, define, on the coset space $`\mathcal{H}/\Gamma`$,

$$\mathrm{Norm}(f)(\tau) \\;=\\; \prod_{q \in \mathcal{H}/\Gamma}
\bigl(f \mid_k g_q^{-1}\bigr)(\tau),$$

where $`g_q`$ is any representative of the coset $`q`$ and $`\mid_k`$ is the
slash operator. Four facts.

**(a) It is well-defined.** If $`g'_q = g_q h`$ with $`h \in \Gamma`$, then
$`g_q'^{-1} = h^{-1} g_q^{-1}`$ and $`f \mid_k h^{-1} = f`$ because $`f`$ is
$`\Gamma`$-invariant; the individual factors do not depend on the chosen
representatives. This is the well-definedness built into mathlib's coset
function `SlashInvariantForm.quotientFunc`
([NormTrace.lean, lines 36–41](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/NumberTheory/ModularForms/NormTrace.lean#L36-L41)).

**(b) It is a holomorphic function, and a cusp form.** Each translate of a
holomorphic function is holomorphic, and a finite product of these is holomorphic.
At the cusps, each factor is itself a cusp form (translation preserves the
vanishing condition), and a product of functions tending to $`0`$ tends to
$`0`$; so $`\mathrm{Norm}(f)`$ vanishes at every cusp of $`\mathcal{H}`$. This is
the only point where the project has to add anything to mathlib: mathlib's
`ModularForm.norm` produces a *modular* form
([NormTrace.lean, lines 108–120](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/NumberTheory/ModularForms/NormTrace.lean#L108-L120)),
and the project's `CuspForm.norm`
([S file, lines 34–51](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularForm_S2_Gamma0_2_eq_zero.lean#L34-L51))
supplies the missing `zero_at_cusps'` field.

**(c) It has weight $`kN`$.** Each factor has weight $`k`$ and there are $`N`$
of them, so the product should have weight $`kN`$. The one thing to check is the
determinant bookkeeping. Slashing the product of $`N`$ functions by
$`h \in \mathcal{H}`$ produces a factor $`|\det h|^{N-1}`$ times the product of
the individual slashes:

```lean
-- Mathlib/NumberTheory/ModularForms/SlashActions.lean, lines 245–251
lemma prod_slash : (∏ i ∈ s, f i) ∣[k * #s] g = |g.det.val| ^ (#s - 1 : ℤ) • (∏ i ∈ s, f i ∣[k] g)
```

Because $`\mathcal{H} \subset \{\det = \pm1\}`$ that factor is $`1`$, and the
individual slashes act on the cosets by $`q \mapsto h^{-1} q`$, which permutes
them. So $`\mathrm{Norm}(f) \mid_{kN} h = \mathrm{Norm}(f)`$ — the norm is
level-one. In the application $`\mathcal{H} = \mathrm{SL}_2(\mathbb{Z})`$ and
$`N = 3`$, so a weight-$`2`$ form goes to a weight-$`6`$ form.

**(d) It vanishes only on zero forms.** This is the useful direction. The
function $`\mathrm{Norm}(f)`$ is a finite product of the holomorphic functions
$`\tau \mapsto (f \mid_k g_q^{-1})(\tau)`$. On the connected open set
$`\mathbb{H}`$, a finite product of holomorphic functions is identically zero
only if one factor already is (the zeros of a nonzero holomorphic function are
isolated, so a finite product of such functions cannot vanish on an open set).
And $`f \mid_k g_q^{-1} \equiv 0`$ if and only if $`f \equiv 0`$, because slashing
by an invertible element is invertible. Hence

$$\mathrm{Norm}(f) = 0 \iff f = 0 .$$

This is mathlib's `ModularForm.norm_eq_zero_iff`
([NormTrace.lean, lines 130–137](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/NumberTheory/ModularForms/NormTrace.lean#L130-L137)),
whose nonvanishing half uses exactly the holomorphy-plus-connectedness argument
above (`UpperHalfPlane.prod_eq_zero_iff`,
[Manifold.lean, lines 140–146](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/Analysis/Complex/UpperHalfPlane/Manifold.lean#L140-L146)).
The project's `CuspForm.norm_eq_zero_iff` is the transport of this to cusp forms.
A caution: the norm is *not* a linear map — it is homogeneous of degree $`N`$, so
$`\mathrm{Norm}(cf) = c^N \mathrm{Norm}(f)`$ — but the statement we need is only
the zero-set statement above, and that is what "injective" means here.

Applying (a)–(d) with $`\Gamma = \Gamma_0(2)`$ and
$`\mathcal{H} = \mathrm{SL}_2(\mathbb{Z})`$: a hypothetical nonzero
$`f \in S_2(\Gamma_0(2))`$ gives a nonzero
$`\mathrm{Norm}(f) \in S_6(\mathrm{SL}_2(\mathbb{Z}))`$.

## 4. Move 3: there are no weight-6 cusp forms at level one

Mathlib's theorem is

```lean
-- Mathlib/NumberTheory/ModularForms/LevelOne/DimensionFormula.lean, lines 153–155
lemma CuspForm.rank_eq_zero_of_weight_lt_twelve (hk : k < 12) :
    Module.rank ℂ (CuspForm 𝒮ℒ k) = 0
```

The proof has two parts: shift the *cusp* form of weight $`k`$ down by $`12`$ to a
*modular* form of weight $`k - 12 < 0`$, then show there is no nonzero modular
form of negative weight at level one. We take them in turn.

### 4.1 Division by $`\Delta`$: cusp forms are $`\Delta`$ times modular forms

Let

$$\Delta(z) = \eta(z)^{24} = q \prod_{n \ge 1} (1 - q^n)^{24}, \qquad q = e^{2\pi i z},$$

the modular discriminant. It is a cusp form of weight $`12`$ at level one
([Discriminant.lean, lines 237–252](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/NumberTheory/ModularForms/Discriminant.lean#L237-L252)),
and it has two properties that make it the right tool:

- $`\Delta(z) \ne 0`$ for all $`z \in \mathbb{H}`$
  ([line 123](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/NumberTheory/ModularForms/Discriminant.lean#L123)); this is the nonvanishing of the eta
  product / of the weight-12 cusp form on the upper half plane.
- its $`q`$-expansion has order exactly $`1`$: the product has constant term
  $`1`$, so $`\Delta = q \cdot (\text{a unit power series})`$
  ([`discriminant_qExpansion_coeff_one`, line 212](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/NumberTheory/ModularForms/Discriminant.lean#L212)).

These give a bijection, for every $`k \in \mathbb{Z}`$,

$$\Phi : S_k(\mathrm{SL}_2(\mathbb{Z})) \\;\longrightarrow\\; M_{k-12}(\mathrm{SL}_2(\mathbb{Z})),
\qquad \Phi(f) = \frac{f}{\Delta},$$

with inverse $`g \mapsto \Delta g`$. Let us check the two directions, because this
is where the $`q`$-order matters:

- **$`\Delta g`$ is a cusp form of weight $`k`$.** It is holomorphic (product of
  holomorphic functions), it has weight $`12 + (k-12) = k`$, and it vanishes at
  the cusp because $`\Delta`$ does.
- **$`f/\Delta`$ is a modular form of weight $`k - 12`$.** It is holomorphic
  because $`\Delta`$ has no zeros on $`\mathbb{H}`$; it has weight $`k - 12`$ by
  the quotient rule for the slash action; and at the cusp it is holomorphic too:
  $`\Delta`$ has a *simple* zero (order $`1`$) while the cusp form $`f`$ vanishes
  to order $`\ge 1`$, so the quotient has $`q`$-order $`\text{ord}(f) - 1 \ge 0`$
  and is bounded as $`\mathrm{Im} \to \infty`$. The simplicity of the zero of
  $`\Delta`$ is exactly what this step needs: a higher-order zero would force a
  pole and the division would not stay inside modular forms.
- The two compositions are the identity by cancelling $`\Delta \ne 0`$.

Mathlib packages this as a $`\mathbb{C}`$-linear equivalence
`CuspForm.discriminantEquiv`
([DimensionFormula.lean, lines 63–88](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/NumberTheory/ModularForms/LevelOne/DimensionFormula.lean#L63-L88)),
and the rank statement is then one line
([lines 153–155](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/NumberTheory/ModularForms/LevelOne/DimensionFormula.lean#L153-L155)):
$`S_k`$ has the rank of $`M_{k-12}`$. For $`k = 6`$ this reads

$$S_6(\mathrm{SL}_2(\mathbb{Z})) \\;\cong\\; M_{-6}(\mathrm{SL}_2(\mathbb{Z})).$$

So "no weight-6 cusp forms" becomes "no negative-weight modular forms", and we
now prove the latter.

### 4.2 Why there are no negative-weight modular forms

The statement is: for $`k < 0`$, every level-one modular form of weight $`k`$ is
zero. Mathlib proves the slightly stronger $`k \le 0`$ version "a modular form of
weight $`\le 0`$ is constant", and then discards the constant when $`k < 0`$.

**The one analytic input.** Write $`q = e^{2\pi i z}`$ and define

$$G(q) \\;=\\; f(z) \qquad (q = e^{2\pi i z}).$$

Because a level-one modular form is periodic with period $`1`$, this is a
well-defined function of $`q`$ on the punctured unit disc, holomorphic there; and
because $`f`$ is bounded at the cusp (that is one of the two axioms of a modular
form), $`G`$ extends holomorphically to $`q = 0`$. So $`G`$ is a holomorphic
function on the unit disc $`D(0,1)`$. Mathlib calls it `cuspFunction 1 f`
([QExpansion.lean, lines 77–100](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/NumberTheory/ModularForms/QExpansion.lean#L77-L100));
$`q`$ is exactly the local parameter at the cusp.

**Step A: any $`z`$ can be moved to $`\mathrm{Im} \ge 1/2`$ with
$`|cz + d| \le 1`$.** Let $`z \in \mathbb{H}`$.

- If $`\mathrm{Im}\,z \ge 1/2`$, take $`\gamma = 1`$.
- Otherwise, use the standard fundamental domain: there is
  $`\gamma = \begin{pmatrix} a & b \\ c & d\end{pmatrix} \in \mathrm{SL}_2(\mathbb{Z})`$
  with $`\mathrm{Im}(\gamma z) \ge 1/2`$ (mathlib's `exists_one_half_le_im_smul`,
  from the fact that a fundamental-domain point has
  $`4\,(\mathrm{Im})^2 \ge 3`$,
  [Modular.lean, lines 400–426](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/NumberTheory/Modular.lean#L400-L426)).
  Since $`\mathrm{Im}\,z < 1/2 \le \mathrm{Im}(\gamma z)`$, and Möbius
  transformations satisfy the identity
  $$\mathrm{Im}(\gamma z) = \frac{\mathrm{Im}\\,z}{|cz+d|^2},$$
  we get $`\mathrm{Im}\,z \le \mathrm{Im}(\gamma z)`$, i.e.
  $`1 \le 1/|cz+d|^2`$, i.e. $`|cz+d| \le 1`$.

Both the identity and this package of statements are mathlib's
`exists_one_half_le_im_smul_and_norm_denom_le`
([Modular.lean, lines 993–1003](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/NumberTheory/Modular.lean#L993-L1003)).

**Step B: the value at $`z`$ is dominated by the value at $`\gamma z`$.** Since
$`f`$ is $`\gamma`$-invariant and the slash factor for $`\gamma`$ is
$`(cz+d)^{-k}`$, we have $`f(\gamma z) = (cz+d)^k f(z)`$, i.e.

$$|f(z)| \\;=\\; |cz+d|^{-k}\\,|f(\gamma z)| .$$

Here is where the sign of the weight enters. For $`k \le 0`$, the exponent
$`-k \ge 0`$, and $`0 < |cz+d| \le 1`$ implies $`|cz+d|^{-k} \le 1`$. Hence

$$|f(z)| \\;\le\\; |f(\gamma z)| .$$

**Step C: the dominant point lies in a small disc.** Put $`\xi = \gamma z`$. The
$`q`$-coordinate of $`\xi`$ is $`e^{2\pi i \xi}`$, whose modulus is
$`e^{-2\pi\,\mathrm{Im}\,\xi}`$, and $`\mathrm{Im}\,\xi \ge 1/2`$ gives

$$|e^{2\pi i \xi}| \\;\le\\; e^{-\pi} \\;<\\; 1 .$$

Combining with Step B,

$$|G(e^{2\pi i z})| = |f(z)| \\;\le\\; |f(\xi)| = |G(e^{2\pi i \xi})|,
\qquad |e^{2\pi i \xi}| \le e^{-\pi}.$$

So: for every $`q \in D(0,1)`$ there is $`w`$ in the *closed* disc of radius
$`r = e^{-\pi}`$ with $`|G(q)| \le |G(w)|`$. (Mathlib's
`norm_qParam_le_of_one_half_le_im` is exactly the second displayed inequality,
[UpperHalfPlane/Exp.lean, lines 32–36](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/Analysis/Complex/UpperHalfPlane/Exp.lean#L32-L36).)

**Step D: maximum modulus makes $`G`$ constant.** Let $`r = e^{-\pi}`$. The
function $`|G|`$ is continuous on the compact disc $`\overline{D}(0,r)`$, so it
attains a maximum there, say at $`x`$. Step C says every value of $`|G|`$ on
$`D(0,1)`$ is at most some value on $`\overline{D}(0,r)`$, hence at most
$`|G(x)|`$. Thus $`x`$ is a point of $`D(0,1)`$ where the modulus of the
holomorphic function $`G`$ attains its maximum over the whole disc, so $`G`$ is
constant on $`D(0,1)`$ by the maximum modulus principle. Concretely, the
constant is $`G(0) = f(\text{cusp})`$. This packaged statement is mathlib's

```lean
-- Mathlib/Analysis/Complex/AbsMax.lean, lines 337–348
lemma eq_const_of_exists_le [ProperSpace E] {f : E → F} {r b : ℝ}
    (h_an : DifferentiableOn ℂ f (ball 0 b)) (hr_nn : 0 ≤ r) (hr_lt : r < b)
    (hr : ∀ z, z ∈ (ball 0 b) → ∃ w, w ∈ closedBall 0 r ∧ ‖f z‖ ≤ ‖f w‖) :
    Set.EqOn f (Function.const E (f 0)) (ball 0 b)
```

So $`f`$ is constant on $`\mathbb{H}`$: every $`z`$ has
$`e^{2\pi i z} \in D(0,1)`$, and $`f(z) = G(e^{2\pi i z})`$ is the constant
$`G(0)`$. This is the
"weight $`\le 0`$ implies constant" half, mathlib's
`levelOne_nonpos_wt_const`
([LevelOne/Basic.lean, lines 89–95](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/NumberTheory/ModularForms/LevelOne/Basic.lean#L89-L95)),
whose analytic core is `cuspFunction_eqOn_const_of_nonpos_wt`
([lines 74–87](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/NumberTheory/ModularForms/LevelOne/Basic.lean#L74-L87)).

**Step E: a negative-weight constant is zero.** Suppose $`f`$ is the constant
function $`c`$. Apply invariance under the matrix
$`S = \begin{pmatrix} 0 & -1 \\ 1 & 0\end{pmatrix} \in \mathrm{SL}_2(\mathbb{Z})`$.
For $`S`$ the denominator is
$`cz + d = z`$, so invariance reads $`f(Sz) = z^k f(z)`$, and since $`f`$ is
constant this says $`c = z^k c`$ for every $`z`$. Evaluating at $`z = i`$ and
$`z = 2i`$ (both in $`\mathbb{H}`$), and using $`(2i)^k = 2^k i^k`$, gives

$$c = i^k c, \qquad c = 2^k i^k c = 2^k c .$$

For an integer $`k \ne 0`$, $`2^k \ne 1`$ (it is $`2^{|k|}`$ or $`2^{-|k|}`$), so
$`c = 0`$. For $`k = 0`$ the argument stops, and correctly so: the weight-0
modular forms at level one are exactly the constants. That is the full proof of
`levelOne_neg_weight_eq_zero`
([LevelOne/Basic.lean, lines 97–101](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/NumberTheory/ModularForms/LevelOne/Basic.lean#L97-L101)),
and of the rank-zero statement
`levelOne_neg_weight_rank_zero`
([lines 114–117](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/NumberTheory/ModularForms/LevelOne/Basic.lean#L114-L117)).

**In particular $`M_{-6}(\mathrm{SL}_2(\mathbb{Z})) = 0`$.** By §4.1,
$`S_6(\mathrm{SL}_2(\mathbb{Z})) = 0`$; by §3, a nonzero
$`f \in S_2(\Gamma_0(2))`$ would give a nonzero element of $`S_6`$; so no such
$`f`$ exists, which is $`S_2(\Gamma_0(2)) = 0`$.

## 5. Key point → declaration map

| Step | Mathematics | Lean declaration | Location |
|---|---|---|---|
| cosets by first column mod 2 | $`G/\Gamma_0(2) \leftrightarrow (\mathbb{Z}/2)^2 \setminus \{0\}`$ | `firstColMod2`, `cosetToProj` | [S 94–168](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularForm_S2_Gamma0_2_eq_zero.lean#L94-L168) |
| index | $`[\mathrm{SL}_2(\mathbb{Z}) : \Gamma_0(2)] = 3`$ | `Gamma0_two_index_eq_three` | [S 170–174](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularForm_S2_Gamma0_2_eq_zero.lean#L170-L174) |
| index as a cardinality | $`\#(\Gamma(1)/\Gamma_0(2)) = 3`$ | `card_quotient_eq_three` | [S 176–188](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularForm_S2_Gamma0_2_eq_zero.lean#L176-L188) |
| norm | $`F(\tau) = \prod_q (f \mid_k g_q^{-1})(\tau)`$ | `SlashInvariantForm.norm` / `ModularForm.norm` | [NormTrace 64–70](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/NumberTheory/ModularForms/NormTrace.lean#L64-L70), [108–120](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/NumberTheory/ModularForms/NormTrace.lean#L108-L120) |
| norm of a cusp form | fill in `zero_at_cusps'` | `CuspForm.norm` | [S 34–51](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularForm_S2_Gamma0_2_eq_zero.lean#L34-L51) |
| norm kills only zero | $`\mathrm{Norm}(f) = 0 \iff f = 0`$ | `ModularForm.norm_eq_zero_iff` | [NormTrace 130–137](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/NumberTheory/ModularForms/NormTrace.lean#L130-L137) |
| weight arithmetic | $`2 \cdot 3 = 6`$ | `hweight` | [S 197–199](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularForm_S2_Gamma0_2_eq_zero.lean#L197-L199) |
| $`\Delta`$ shift | $`S_k \cong M_{k-12}`$ | `CuspForm.discriminantEquiv` | [DimensionFormula 63–88](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/NumberTheory/ModularForms/LevelOne/DimensionFormula.lean#L63-L88) |
| no small-weight cusp forms | $`S_k(\mathrm{SL}_2\mathbb{Z}) = 0`$ for $`k < 12`$ | `CuspForm.rank_eq_zero_of_weight_lt_twelve` | [DimensionFormula 153–155](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/NumberTheory/ModularForms/LevelOne/DimensionFormula.lean#L153-L155) |
| max modulus core | constant when dominated by a smaller disc | `eq_const_of_exists_le` | [AbsMax 337–348](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/Analysis/Complex/AbsMax.lean#L337-L348) |
| negative weight is zero | constant $`\Rightarrow`$ zero | `levelOne_neg_weight_eq_zero` | [LevelOne/Basic 97–101](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/NumberTheory/ModularForms/LevelOne/Basic.lean#L97-L101) |
| weight 6 level one | $`S_6(\mathrm{SL}_2\mathbb{Z}) = 0`$ | `S6_levelOne_eq_zero` | [S 86–89](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularForm_S2_Gamma0_2_eq_zero.lean#L86-L89) |
| the theorem | $`S_2(\Gamma_0(2)) = 0`$ | `ModularForm.S2_Gamma0_2_eq_zero` | [Thm 13](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularForm_S2_Gamma0_2_eq_zero.lean#L13) |

## 6. Lean detours (not mathematics)

Reading the S file beside the arguments above, three gaps are purely formal.

- **`Γ(1)` versus `𝒮ℒ`.** Mathlib's level-one statements are about
  $`\mathcal{SL}`$, the image of $`\mathrm{SL}_2(\mathbb{Z})`$ in
  $`\mathrm{GL}_2(\mathbb{R})`$, while the theorem is stated for `Γ(1)`. The
  bridge is `coe_Gamma_one_eq_SL` ([S 77–80](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularForm_S2_Gamma0_2_eq_zero.lean#L77-L80)),
  and `cuspForm_eq_zero_of_subgroup_eq` ([S 82–86](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularForm_S2_Gamma0_2_eq_zero.lean#L82-L86))
  transports a vanishing statement across the equality of subgroups. No
  mathematics happens here.
- **`index` versus `Nat.card` of the quotient.** `Gamma0_two_index_eq_three`
  computes `Subgroup.index`, but the norm needs `Nat.card (ℋ ⧸ Γ)`.
  `card_quotient_eq_three` ([S 176–188](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularForm_S2_Gamma0_2_eq_zero.lean#L176-L188))
  transports the index along `relIndex_map_map_of_injective`,
  `Gamma_one_top` and `relIndex_top_right`; then the `IsFiniteRelIndex`
  instance ([S 190–192](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularForm_S2_Gamma0_2_eq_zero.lean#L190-L192)) records that the
  quotient is finite so `Nat.card` and `Fintype.card` agree.
- **Cusp forms are functions for extensionality purposes.** The end of the proof
  moves between `f = 0` as a bundled cusp form and `(f : ℍ → ℂ) = 0` as a
  function. That is why `CuspForm.norm_eq_zero_iff` is transported through
  `DFunLike.coe_injective` before use, and why the final step is
  `DFunLike.coe_injective (hf0.trans CuspForm.coe_zero.symm)`.

## 7. Links

FLT sources at the pinned sha `aa2d8b3`:

- [P2M/Sol/S_ModularForm_S2_Gamma0_2_eq_zero.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularForm_S2_Gamma0_2_eq_zero.lean) — the whole proof
- [Theorems/Thm_ModularForm_S2_Gamma0_2_eq_zero.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularForm_S2_Gamma0_2_eq_zero.lean) — the exported statement
- [Theorems/Thm_ModularForm_S2_Gamma0_one_eq_zero.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularForm_S2_Gamma0_one_eq_zero.lean) — the level-one analogue
- [P2M/Sol/S_ModularForm_S2_Gamma0_one_eq_zero.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularForm_S2_Gamma0_one_eq_zero.lean) — level one, directly from $`2 < 12`$

Mathlib at tag `v4.33.0`:

- [NormTrace.lean](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/NumberTheory/ModularForms/NormTrace.lean) — trace and norm of a form
- [SlashActions.lean](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/NumberTheory/ModularForms/SlashActions.lean) — the slash action, `prod_slash`
- [LevelOne/DimensionFormula.lean](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/NumberTheory/ModularForms/LevelOne/DimensionFormula.lean) — `discriminantEquiv`, `rank_eq_zero_of_weight_lt_twelve`
- [LevelOne/Basic.lean](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/NumberTheory/ModularForms/LevelOne/Basic.lean) — negative weight vanishes; the maximum-modulus route
- [Discriminant.lean](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/NumberTheory/ModularForms/Discriminant.lean) — $`\Delta = \eta^{24}`$, nonvanishing, $`q`$-order
- [AbsMax.lean](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/Analysis/Complex/AbsMax.lean) — the maximum-modulus principle in the form used
- [UpperHalfPlane/Manifold.lean](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/Analysis/Complex/UpperHalfPlane/Manifold.lean) — `prod_eq_zero_iff` (holomorphy + connectedness)
- [Modular.lean](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/NumberTheory/Modular.lean) — fundamental domain; `exists_one_half_le_im_smul_and_norm_denom_le`
