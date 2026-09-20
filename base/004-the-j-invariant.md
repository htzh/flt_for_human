# The j-invariant: its q-expansion and first properties

Fourth of the `base/` notes. Note [001](001-field-extensions-and-galois-basics.md)
fixed the field/Galois vocabulary, note [002](002-modular-forms-basics.md) the
automorphic one, and note [003](003-no-level-2-weight-2-cusp-forms.md) worked one
vanishing statement down to the maximum-modulus principle. This note turns to the
classical modular $`j`$-invariant.

mathlib has the analytic ingredients — the Eisenstein series $`E_4`$, $`E_6`$ and
the discriminant $`\Delta = \eta^{24}`$ — but no $`j`$. FLT uses them in one
construction of the level-$`N`$ function field, and uses a purely formal
$`q`$-expansion of $`j`$ in another — the one the Hecke argument of
[math/009](../math/009-hecke-jacobian-commute.md) needs. This note is about that
formal series: where its coefficients come from, what the first few are, and
which properties make it the $`j`$-invariant.

The plan:

1. the classical definition, and the two models (analytic and formal) FLT keeps
   of it;
2. the two input series, $`E_4`$ and $`\Delta/q`$;
3. the coefficient computation;
4. why the coefficients are integers;
5. the first properties: weight zero, the pole at the cusp, the disc picture and
   the natural boundary, the special values;
6. the deep properties, stated but not proved.

Line-number citations point at `anthropics/fermats-last-theorem@aa2d8b3`; mathlib
citations point at tag **v4.33.0**. Both are rendered GitHub links, so the cited
region is highlighted on click.

## 1. The classical definition, and its formal shadow

Write $`q = e^{2\pi i \tau}`$ on the upper half plane $`\mathbb{H}`$. The
normalized Eisenstein series and the discriminant have $`q`$-expansions

$$E_4 = 1 + 240 \sum_{n \ge 1} \sigma_3(n) q^n, \qquad
  E_6 = 1 - 504 \sum_{n \ge 1} \sigma_5(n) q^n, \qquad
  \Delta = \frac{E_4^3 - E_6^2}{1728} = q \prod_{n \ge 1} (1 - q^n)^{24},$$

where $`\sigma_k(n) = \sum_{d \mid n} d^k`$. The $`j`$-invariant is the ratio

$$j(\tau) = 1728\frac{E_4(\tau)^3}{E_4(\tau)^3 - E_6(\tau)^2}
         = \frac{E_4(\tau)^3}{\Delta(\tau)} .$$

It is a *modular function* of weight zero: holomorphic on $`\mathbb{H}`$, invariant
under the Möbius action of $`\mathrm{SL}_2(\mathbb{Z})`$, and meromorphic at the
cusp, where it has a simple pole. Its $`q`$-expansion is

$$j(q) = q^{-1} + 744 + 196884 q + 21493760 q^2 + 864299970 q^3
        + 20245856256 q^4 + \cdots .$$

The integrality of these coefficients is a theorem, not a definition; §4 proves
it in the form FLT uses.

Two facts frame everything below.

- **mathlib has the ingredients, not $`j`$.** The analytic objects are
  `ModularForm.E₄ : ModularForm 𝒮ℒ 4` and `E₆` (weights 4 and 6,
  [EisensteinSeries/Basic.lean, lines 51–54](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/NumberTheory/ModularForms/EisensteinSeries/Basic.lean#L51-L54)),
  and the discriminant as a bundled cusp form
  ([Discriminant.lean, line 237](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/NumberTheory/ModularForms/Discriminant.lean#L237)),
  with the product formula $`\Delta(\tau) = q \prod (1-q^n)^{24}`$
  ([line 115](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/NumberTheory/ModularForms/Discriminant.lean#L115))
  and nonvanishing on $`\mathbb{H}`$
  ([line 123](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/NumberTheory/ModularForms/Discriminant.lean#L123)).
  There is no identifier `j` anywhere in mathlib's modular-forms library.
- **FLT has two encodings of $`j`$, connected by $`q`$-expansion.** The
  *analytic* one writes the function on $`\mathbb{H}`$ directly, from mathlib's
  $`E_4`$ and $`\Delta`$:
  `jAnalytic (τ : ℍ) : ℂ := ModularForm.E₄ τ ^ 3 / ModularForm.discriminant τ`
  ([Def_ModularCurve_LevelNFunctionField.lean, line 22](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularCurve_LevelNFunctionField.lean#L22));
  with the Fricke functions it presents the level-$`N`$ function field as a ring
  of functions on $`\mathbb{H}`$. The *formal* one — the encoding this note and
  [math/009](../math/009-hecke-jacobian-commute.md) use — declares the two
  $`q`$-expansions as power series and assembles $`j`$ from them
  ([Def_ModularCurve_X0.lean, lines 111–158](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularCurve_X0.lean#L111-L158)):

```lean
def eisenstein4       : PowerSeries ℤ := PowerSeries.mk fun n =>
  if n = 0 then 1 else 240 * ∑ d ∈ n.divisors, (d : ℤ) ^ 3
def etaProd           : PowerSeries ℤ := ∏' n : ℕ, (1 - PowerSeries.X ^ (n + 1))
def dedekindEtaUnit   : PowerSeries ℤ := etaProd ^ 24
def dedekindEtaUnitInv: PowerSeries ℤ := dedekindEtaUnit.invOfUnit 1
def jNum              : PowerSeries ℤ := eisenstein4 ^ 3 * dedekindEtaUnitInv
def jq                : LaurentSeries ℚ :=
  HahnSeries.single (-1 : ℤ) 1 * HahnSeries.ofPowerSeries ℤ ℚ jNumQ
```

Thus `eisenstein4` is $`E_4`$, `dedekindEtaUnit` is $`\Delta/q`$, `jNum` is
$`q \cdot j`$, and `jq` is $`j`$. Everything the project later needs — the
function field $`\mathbb{Q}(j, j(q^N))`$ of
[math/009](../math/009-hecke-jacobian-commute.md), the cusp valuation, the Hecke
correspondence — is algebra on this one series.

The two encodings are related, not disjoint: an algebra homomorphism from the
fraction field of the analytic ring to Laurent series — the $`q`$-expansion —
carries the analytic generator to `qExpand ℂ N (jqModC ℂ)`, and the formal series
is the case over $`\mathbb{Q}`$, `jqModC ℚ = jq`
([Thm_ModularCurve_LevelN_exists_algHom_laurentSeries_qExpansion.lean, lines 16–18](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularCurve_LevelN_exists_algHom_laurentSeries_qExpansion.lean#L16-L18)).

**Why FLT carries several models.** The function on $`\mathbb{H}`$ and the
Laurent series are not rival definitions of one number; they are two *models* of
a modular curve's function field, and the proof needs both. In the **analytic
model** the elements are genuine functions — `LevelN.ring N = ℂ[jAnalytic, fricke
N v]`, the level-$`N`$ curve with its Fricke/Weber coordinates — so they can be
differentiated, integrated and evaluated; this is the world of the Riemann
surface: the covers $`X(N) \to X(1)`$, their Galois groups acting by slash
operators, fixed fields, regular differentials, orders of vanishing, ramification
at the elliptic points. In the **formal model** the elements are Laurent series —
`modularFunctionField N = ℚ(jq, j(q^N))` for the Hecke curve $`X_0(N)`$,
`levelFunctionField` for the cyclotomic level-$`q`$ structure — so they can be
compared coefficient by coefficient, given a $`q`$-adic valuation and reduced
modulo primes; this is the world of the Hecke operators, the cusp place, the
rational structure and the Galois representations. Neither model alone carries
the proof: a function has no Hecke eigenvalue until it is expanded at the cusp,
and a Laurent series has no Jacobian attached to it. The $`q`$-expansion
homomorphism above is the dictionary between the two worlds, and injectivity of
$`q`$-expansion (§5) is what makes the dictionary faithful.

## 2. The two input series

**$`E_4`$, and its coefficients are given.** FLT defines `eisenstein4` by the
divisor-sum formula, so its coefficients cost nothing to establish:

$$\sigma_3(1), \dots, \sigma_3(6) = 1, 9, 28, 73, 126, 252,$$
$$E_4 = 1 + 240q + 2160q^2 + 6720q^3 + 17520q^4 + 30240q^5 + \cdots .$$

Classically this is the $`q`$-expansion of the weight-4 Eisenstein series, which
is why the name is right; but the formal series is the whole input.

**$`\Delta/q`$, and the one infinite product.** By the product formula
$`\Delta = q \prod_{n \ge 1}(1-q^n)^{24}`$ (mathlib's `discriminant_eq_q_prod`),
the series we need is

$$\frac{\Delta}{q} = \prod_{n \ge 1} (1 - q^n)^{24}
  = 1 - 24q + 252q^2 - 1472q^3 + 4830q^4 - 6048q^5 - 16744q^6 + \cdots .$$

Its coefficients are Ramanujan's $`\tau`$: if
$`\Delta = \sum_{n \ge 1} \tau(n) q^n`$, the coefficient of $`q^{n-1}`$ in
$`\Delta/q`$ is $`\tau(n)`$. FLT calls the product $`\prod (1-q^n)`$ `etaProd`
and its 24th power `dedekindEtaUnit`. This is the only step that looks like
analysis; it is handled formally, as a `tprod` in the $`X`$-adic completion of the
power-series ring, so no convergence in $`q`$ is used. The constant term is `1`,
so $`\Delta/q`$ is a unit of $`\mathbb{Z}[[q]]`$ and has a formal inverse

$$\left(\frac{\Delta}{q}\right)^{-1}
  = 1 + 24q + 324q^2 + 3200q^3 + 25650q^4 + 176256q^5 + \cdots ,$$

computed in FLT as `dedekindEtaUnitInv`.

With these two series, FLT's $`j`$ is

$$\mathrm{jNum} = E_4^3 \cdot \left(\frac{\Delta}{q}\right)^{-1} \in \mathbb{Z}[[q]],
  \qquad jq = q^{-1} \cdot \mathrm{jNum} \in \mathbb{Z}((q)).$$

Note that $`E_6`$ does not appear: the classical formula
$`j = 1728E_4^3/(E_4^3 - E_6^2)`$ is equivalent to $`E_4^3/\Delta`$ by the
definition of $`\Delta`$, and FLT takes the second form.

## 3. Computing the coefficients

Two expansions are needed, then one long division.

**The cube.** Cubing $`E_4`$ and collecting terms (the coefficient of $`q^n`$ is
$`\sum_{i+j+k=n} a_i a_j a_k`$ with $`a_n`$ the coefficient of $`E_4`$) gives

$$E_4^3 = 1 + 720q + 179280q^2 + 16954560q^3 + 396974160q^4
          + 4632858720q^5 + \cdots .$$

**The reciprocal.** Write $`\Delta/q = 1 + \sum_{i \ge 1} p_i q^i`$ with
$`p_1 = -24`$, $`p_2 = 252`$, $`p_3 = -1472`$, $`p_4 = 4830`$,
$`p_5 = -6048`$. Its inverse $`\sum_{n \ge 0} b_n q^n`$ satisfies
$`b_0 = 1`$ and, matching the coefficient of $`q^n`$ in
$`(\Delta/q) \cdot (\Delta/q)^{-1} = 1`$,

$$b_n = -\sum_{i=1}^{n} p_i b_{n-i} \qquad (n \ge 1),$$

so $`b_1 = 24`$, $`b_2 = 324`$, $`b_3 = 3200`$, $`b_4 = 25650`$,
$`b_5 = 176256`$, the series displayed in §2.

**The division.** Now $`\mathrm{jNum} = E_4^3 \cdot (\Delta/q)^{-1}`$, whose
coefficients $`c_n`$ satisfy $`c_n = \sum_{i=0}^{n} a_i b_{n-i}`$ where $`a_n`$ is
the coefficient of $`E_4^3`$:

$$\begin{aligned}
  c_0 &= 1, \\\\
  c_1 &= 720 + 24 \cdot 1 = 744, \\\\
  c_2 &= 179280 + 24 \cdot 720 + 324 \cdot 1 = 196884, \\\\
  c_3 &= 16954560 + 24 \cdot 179280 + 324 \cdot 720 + 3200 \cdot 1
       = 21493760 .
\end{aligned}$$

Equivalently, because $`p_0 = 1`$ and $`E_4^3 = (\Delta/q)\cdot \mathrm{jNum}`$,
one can solve downwards: $`c_n = a_n - \sum_{i=1}^{n} p_i c_{n-i}`$. Both routes
give the same table:

| $`n`$ | $`0`$ | $`1`$ | $`2`$ | $`3`$ | $`4`$ | $`5`$ |
|---|---|---|---|---|---|---|
| coefficient of $`E_4^3`$ | 1 | 720 | 179280 | 16954560 | 396974160 | 4632858720 |
| coefficient of $`\Delta/q`$ | 1 | −24 | 252 | −1472 | 4830 | −6048 |
| $`\mathrm{jNum}`$ | 1 | 744 | 196884 | 21493760 | 864299970 | 20245856256 |

Shifting by $`q^{-1}`$,

$$j(q) = q^{-1} + 744 + 196884q + 21493760q^2 + 864299970q^3
        + 20245856256q^4 + \cdots .$$

The first nontrivial coefficient, $`196884`$, is a famous number; §6 says why.

## 4. Why the coefficients are integers

This is not visible from $`j = E_4^3/\Delta`$, where a division by the complicated
series $`\Delta`$ could produce denominators. In the $`q`$-variable it is
immediate. Both $`E_4`$ and $`\Delta/q = \prod (1-q^n)^{24}`$ lie in
$`\mathbb{Z}[[q]]`$, and $`\Delta/q`$ has constant term $`1`$. Hence
$`\Delta/q`$ is invertible in $`\mathbb{Z}[[q]]`$, and the recursion
$`b_n = -\sum_{i=1}^{n} p_i b_{n-i}`$ keeps the inverse in
$`\mathbb{Z}[[q]]`$: each $`b_n`$ is an integer combination of earlier ones
with the integer coefficients $`p_i`$. Multiplying by $`E_4^3 \in
\mathbb{Z}[[q]]`$ and shifting by $`q^{-1}`$ preserves integrality, with no
denominators anywhere. So

$$jq \in \mathbb{Z}((q)),$$

the classical integrality of the $`j`$-coefficients, obtained here as a formal
consequence of the product formula. The same recursion is the content of FLT's
`dedekindEtaUnit_mul_inv` and `constantCoeff_dedekindEtaUnitInv`.

## 5. First properties

**Weight zero, hence invariance.** $`E_4`$ and $`E_6`$ are modular of weights
$`4`$ and $`6`$: for $`\gamma = \begin{pmatrix} a & b \\ c & d\end{pmatrix} \in
\mathrm{SL}_2(\mathbb{Z})`$,

$$E_4(\gamma\tau) = (c\tau+d)^4 E_4(\tau), \qquad
  E_6(\gamma\tau) = (c\tau+d)^6 E_6(\tau), \qquad
  \Delta(\gamma\tau) = (c\tau+d)^{12} \Delta(\tau).$$

So $`E_4^3`$ and $`\Delta`$ are both of weight $`12`$, and the ratio is weight
$`0`$:

$$j(\gamma\tau) = j(\tau) \qquad \text{for all } \gamma \in \mathrm{SL}_2(\mathbb{Z}).$$

In particular $`j(\tau+1) = j(\tau)`$, which is what makes $`j`$ a function of
$`q = e^{2\pi i \tau}`$ at all, and $`j(-1/\tau) = j(\tau)`$. This is a property
of the classical function; on the formal side the analogous statement is the
substitution identity behind `qExpand`, not an identity between formal series.

**Holomorphic on $`\mathbb{H}`$, simple pole at the cusp.** $`E_4`$ is holomorphic
and $`\Delta(\tau) \ne 0`$ for $`\tau \in \mathbb{H}`$ (mathlib's
`discriminant_ne_zero`), so $`j`$ is holomorphic on $`\mathbb{H}`$. At the cusp,
the $`q`$-expansion opens with $`q^{-1}`$ and has nothing below it:

```lean
-- Def_ModularCurve_X0.lean, lines 182, 186, 190
theorem coeff_jq_neg_one : jq.coeff (-1 : ℤ) = 1
theorem coeff_jq_of_lt {k : ℤ} (hk : k < -1) : jq.coeff k = 0
theorem jq_ne_zero : jq ≠ 0
```

In the local parameter $`q`$, the product $`q \cdot j`$ is holomorphic and
nonzero at $`q = 0`$; equivalently $`jq`$ has $`q`$-adic order $`-1`$
([`order_jq`, Def_ModularCurve_QAdicPlace.lean, line 12](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularCurve_QAdicPlace.lean#L12)).
That order is exactly what lets FLT define the cusp-at-infinity place as a
valuation subring with uniformizer $`j^{-1}`$
([lines 128, 229, 300](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularCurve_QAdicPlace.lean#L128-L300)),
as [math/009 §1](../math/009-hecke-jacobian-commute.md) describes.

This is also the precise sense in which $`j`$ is *not* a modular form in the
library's sense: mathlib's weight-zero modular forms are exactly the constants
(`ModularForm.levelOne_weight_zero_rank_one`,
[LevelOne/Basic.lean, line 109](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/NumberTheory/ModularForms/LevelOne/Basic.lean#L109)),
while $`j`$ is meromorphic with a pole. The classical name for the object is
*modular function*.

**The disc picture, and the natural boundary.** The exponential
$`\tau \mapsto q = e^{2\pi i\tau}`$ maps $`\mathbb{H}`$ onto the punctured open
unit disc $`D^{*} = \{0 \lt |q| \lt 1\}`$, and the periodicity $`j(\tau+1) = j(\tau)`$
is exactly what makes $`j`$ descend to a holomorphic function on $`D^{*}`$. In the
$`q`$-disc the whole function is visible at once: the expansion
$`q^{-1} + 744 + \cdots`$ has radius of convergence $`1`$, with a simple pole at
$`q = 0`$ and no other singularity inside, so $`j`$ is meromorphic on the full
disc $`D`$ and its Laurent expansion determines it — two holomorphic functions on
the connected $`D^{*}`$ with the same expansion agree. Because $`j`$ is a function
of $`q`$, this is a complete description of the function.

**Each value is taken infinitely often.** The disc picture also shows how far
$`j`$ is from injective. $`Y(1) = \mathrm{SL}_2(\mathbb{Z}) \backslash
\mathbb{H}`$ has $`j`$ as a bijection onto $`\mathbb{C}`$, but
$`D^{*} = \mathbb{Z} \backslash \mathbb{H}`$ is only the quotient by translations,
so $`D^{*} \to Y(1)`$ is an infinite-sheeted covering and
$`j : D^{*} \to \mathbb{C}`$ is infinite-to-one: for every $`c \in \mathbb{C}`$
the equation $`j(q) = c`$ has countably infinitely many solutions in $`D^{*}`$.
Near $`q = 0`$ there is exactly one (the local inverse of the pole, since
$`j = q^{-1} \cdot (\text{unit})`$), and the rest accumulate at the boundary: the
$`\mathrm{SL}_2(\mathbb{Z})`$-orbit of a solution $`\tau_c \in \mathbb{H}`$
accumulates at every cusp $`p/q`$, so its $`q`$-values accumulate at every root of
unity on $`|q| = 1`$. The solution set is thus discrete inside $`D^{*}`$, with all
of its accumulation exactly on the unit circle — the natural boundary of the next
paragraph, seen from the fibre side. Nothing here clashes with "zeros are
isolated": isolation is a statement about the *domain*, the identity theorem
forbids accumulation only at an interior point, and an infinite discrete subset
of a bounded domain must therefore accumulate on the boundary.

*The real line is a natural boundary.* No continuation of $`j`$ beyond
$`\mathbb{H}`$ exists, and the reason is the cusps. Every rational
$`p/q \in \mathbb{Q} \subset \mathbb{R}`$ is a cusp of
$`\mathrm{SL}_2(\mathbb{Z})`$, and near a cusp the local parameter $`w`$ gives
$`j = w^{-1} \cdot (\text{a unit in } w)`$, so $`|j(\tau)| \to \infty`$ as
$`\tau`$ approaches the cusp. Since $`\mathbb{Q}`$ is dense in $`\mathbb{R}`$,
every boundary point is a limit of cusps. Suppose $`j`$ extended meromorphically
to a domain $`\Omega`$ containing $`\mathbb{H}`$ and some real $`x`$. Then $`x`$
is interior to $`\Omega`$, so some interval around $`x`$ lies in $`\Omega`$; it
contains infinitely many rationals, and at each of them $`j`$ has a pole. But
poles of a meromorphic function on a domain are isolated, so they cannot
accumulate at the interior point $`x`$. No such $`\Omega`$ exists: the real line
(equivalently, the unit circle $`|q| = 1`$) is a natural boundary, and the
$`q`$-expansion is not the germ of anything larger.

**Why the formal function field is legitimate.** The disc picture has a
consequence that the whole formal development rests on. Classically the map
"modular function $`\mapsto`$ its $`q`$-expansion" is *injective*: a weight-zero
$`\mathrm{SL}_2(\mathbb{Z})`$-invariant $`f`$ descends to $`D^{*}`$, and if its
$`q`$-expansion vanished then $`f`$ would vanish on $`D^{*}`$ by the identity
theorem, hence on $`\mathbb{H}`$. So the $`q`$-expansion embeds the classical
field of modular functions into $`\mathbb{Q}((q))`$, carrying $`j`$ to `jq` (the
bridge of §1). The generation theorem then identifies the image: the level-$`N`$
field of modular functions is generated by $`j(\tau)`$ and $`j(N\tau)`$, so its
image is exactly the subfield generated by `jq` and `qExpand ℚ N jq` — which is
what FLT calls `modularFunctionField N ⊆ ℚ((q))`
([Def_ModularCurve_X0.lean, lines 250–251](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularCurve_X0.lean#L250-L251)).
The formal statement of the generation theorem is `FunctionFieldGeneration M`:
every `qExpand ℚ d jq` with $`d \mid M`$ already lies in the subfield
`ℚ(jq, qExpand ℚ M jq)`
([lines 233–235](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularCurve_X0.lean#L233-L235)).
Injectivity is what lets the formal identities of §1 and
[math/009](../math/009-hecke-jacobian-commute.md) be read back as identities of
functions; without it, agreement of $`q`$-expansions would prove nothing.

**Why $`j(\tau)`$ and $`j(N\tau)`$, and why both.** The map
$`X_0(N) \to X(1)`$, $`\tau \mapsto j(\tau)`$, is a cover of degree
$`\psi(N) = [\mathrm{SL}_2(\mathbb{Z}) : \Gamma_0(N)]`$, so a function of
$`j(\tau)`$ alone sees only the base: it cannot tell apart the $`\psi(N)`$ points
of $`X_0(N)`$ lying over one value of $`j`$. It is of course true that
$`j(\tau)`$ is itself $`\Gamma_0(N)`$-invariant — "level $`1`$ implies level
$`N`$" — but that gives only an inclusion of fields,
$`\mathbb{C}(j(\tau)) \subseteq`$ (level-$`N`$ functions), and the inclusion is
strict for $`N \gt 1`$: its index is $`\psi(N)`$. The second generator is what
moves in the fibre. The classical choice $`j(N\tau)`$ is forced by three properties: it
is $`\Gamma_0(N)`$-invariant, so it really is a function on $`X_0(N)`$; its
$`q`$-expansion is free, just $`j(q)`$ with $`q \mapsto q^N`$, which is why the
formal model can name it at all; and it has a moduli meaning — if
$`E = \mathbb{C}/(\mathbb{Z}+\mathbb{Z}\tau)`$ and $`C`$ is its cyclic subgroup of
order $`N`$, then $`j(N\tau)`$ is the $`j`$-invariant of the quotient $`E/C`$. The
direction of the substitution matters: $`j(N\tau)`$ has period $`1/N`$ — finer
than $`1`$, hence still $`1`$-periodic — so it descends to the $`q`$-disc and has
a genuine $`q`$-expansion $`j(q^N)`$; by contrast $`j(\tau/N)`$ has period
$`N`$, is not $`1`$-periodic, and needs the fractional variable $`q^{1/N}`$. So
$`(j(\tau), j(N\tau))`$ is the pair "$`j`$-invariant of $`E`$, $`j`$-invariant of
$`E/C`$", which is exactly a point of $`X_0(N)`$; the algebraic relation it
satisfies is the modular polynomial
$`\Phi_N(j(\tau), j(N\tau)) = 0`$, of degree $`\psi(N)`$ in each variable. The
Fricke/Atkin–Lehner involution
$`w_N = [[0,-1],[N,0]]`$ interchanges the two
generators: $`j(w_N\tau) = j(N\tau)`$ and $`j(N w_N \tau) = j(\tau)`$. That
symmetry is why neither generator alone suffices and why $`\Phi_N`$ is symmetric
in its two variables. In particular the inclusion does not reverse either:
$`j(N\tau)`$ does not generate $`j(\tau)`$, because $`j(\tau)`$ has degree
$`\psi(N)`$ over $`\mathbb{C}(j(N\tau))`$ — its minimal polynomial there is
$`\Phi_N(X, j(N\tau))`$ — so for $`N \gt 1`$ neither of the two is a rational
function of the other. They are siblings, not parent and child: both have degree
$`\psi(N)`$ over the common base, and only their compositum is the curve. (Honest
$`q`$-expansions exist because $`\Gamma_0(N)`$ contains the translation $`T`$,
forcing period $`1`$. Not every congruence subgroup does: $`\Gamma(N)`$ misses
$`T`$ once $`N \gt 1`$, its cusp at $`\infty`$ has width $`N`$, and the local
parameter there is $`q^{1/N}`$.)

**The special values.** The two elliptic points of $`\mathrm{SL}_2(\mathbb{Z})
\backslash \mathbb{H}`$ carry the two simplest values of $`j`$:

$$j(i) = 1728, \qquad j(\rho) = 0, \qquad \rho = e^{2\pi i/3}.$$

Both follow from one-line symmetry arguments. For $`i`$: the matrix
$`S = [[0,-1],[1,0]]`$ fixes $`i`$, and
$`E_6(-1/\tau) = \tau^6 E_6(\tau)`$; at $`\tau = i`$ this reads
$`E_6(i) = i^6 E_6(i) = -E_6(i)`$, hence $`E_6(i) = 0`$, and then
$`j(i) = 1728 E_4(i)^3 / E_4(i)^3 = 1728`$. For $`\rho`$: the matrix
$`ST = [[0,-1],[1,1]]`$ fixes $`\rho`$, and
$`E_4(ST\tau) = (\tau+1)^4 E_4(\tau)`$; at $`\tau = \rho`$ this reads
$`E_4(\rho) = (\rho+1)^4 E_4(\rho)`$, and $`(\rho+1)^4 = e^{4\pi i/3} \ne 1`$,
so $`E_4(\rho) = 0`$ and $`j(\rho) = 0`$. These are the $`j`$-invariants of the
square lattice $`\mathbb{Z}[i]`$ (extra automorphism of order $`4`$, value
$`1728`$) and the hexagonal lattice $`\mathbb{Z}[\rho]`$ (extra automorphism of
order $`6`$, value $`0`$).

## 6. Beyond this note: the deep properties

The following are classical theorems we do not prove here. They are stated for
orientation and cited; none of them is used by the commutation argument of
[math/009](../math/009-hecke-jacobian-commute.md), which needs only the formal
series.

- **$`j`$ compactifies the modular curve.** Let
  $`Y(1) = \mathrm{SL}_2(\mathbb{Z}) \backslash \mathbb{H}`$ be the open modular
  curve. It has exactly one cusp class — the rationals together with $`\infty`$
  form a single $`\mathrm{SL}_2(\mathbb{Z})`$-orbit — and
  $`X(1) = Y(1) \cup \{\text{cusp}\}`$ is its one-point compactification. Then
  $`j`$ restricts to a bijection $`Y(1) \to \mathbb{C}`$ and extends to a
  bijection $`X(1) \to \mathbb{C} \cup \{\infty\} = \mathbb{P}^1(\mathbb{C})`$
  sending the cusp to $`\infty`$. So $`j`$ identifies the compact modular curve
  with the Riemann sphere and the open curve with the plane; it is a
  *Hauptmodul*, a coordinate on $`X(1)`$ whose only pole is at the cusp. The
  inverse is the classical uniformization: a value $`\lambda \in \mathbb{C}`$ is
  the $`j`$-invariant of a unique class of lattices.
- **$`\mathbb{C}(j)`$ is the field of modular functions.** Because $`j`$ is a
  coordinate on $`X(1) \cong \mathbb{P}^1`$, the meromorphic functions on
  $`X(1)`$ are exactly the rational functions of $`j`$: the function field is
  $`\mathbb{C}(j)`$. Translating back, every function on $`\mathbb{H}`$ that is
  $`\mathrm{SL}_2(\mathbb{Z})`$-invariant and meromorphic on $`\mathbb{H}`$ and
  at the cusps — that is, every modular function of level one — is a rational
  function of $`j`$. This is the classical *definition* of the field of modular
  functions, and it is the level-one case of the generation statement that
  [math/009 §1](../math/009-hecke-jacobian-commute.md) discusses; FLT's formal
  $`\mathbb{Q}(j, j(q^N))`$ is the $`q`$-expansion shadow of it.
- **Complex multiplication.** If $`\tau \in \mathbb{H}`$ is imaginary quadratic,
  then $`j(\tau)`$ is an algebraic integer, and $`\mathbb{Q}(j(\tau))`$ is the
  Hilbert class field of $`\mathbb{Q}(\tau)`$ (Kronecker's *Jugendtraum*). The
  values $`j(i) = 1728`$ and $`j(\rho) = 0`$ of §5 are the first two cases.
- **Monstrous moonshine.** Writing $`j(q) - 744 = \sum_{n \ge -1} c_n q^n`$, the
  numbers $`c_n`$ are the graded dimensions of a representation of the Monster
  group; the first nontrivial one is $`196884 = 196883 + 1`$, the dimension of
  the smallest nontrivial Monster representation plus one (Conway–Norton 1979;
  Borcherds 1992 for the moonshine module).

Background: J. Silverman, *Advanced Topics in the Arithmetic of Elliptic Curves*,
GTM 151, Springer 1994, Ch. I–II (the $`j`$-invariant, uniformization); S. Lang,
*Elliptic Functions*, GTM 112, Springer 1987, Ch. 5 (modular functions and the
Hauptmodul); D. Cox, Primes of the Form $`x^2 + ny^2`$, Wiley 1989 (CM and
class fields); J. Conway and S. Norton, *Monstrous moonshine*, Bull. LMS 11
(1979); R. Borcherds, *Monstrous moonshine and monstrous Lie superalgebras*,
Invent. Math. 109 (1992).

## 7. Key point → declaration map

| Mathematics | Lean declaration | Location |
|---|---|---|
| $`E_4 = 1 + 240\sum \sigma_3(n) q^n`$ | `eisenstein4` | [X0 111](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularCurve_X0.lean#L111) |
| $`\prod (1-q^n)`$ | `etaProd` | [X0 119](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularCurve_X0.lean#L119) |
| $`\Delta/q = \prod (1-q^n)^{24}`$ | `dedekindEtaUnit` | [X0 127](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularCurve_X0.lean#L127) |
| $`(\Delta/q)^{-1}`$ | `dedekindEtaUnitInv` | [X0 132](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularCurve_X0.lean#L132) |
| $`q \cdot j = E_4^3 (\Delta/q)^{-1}`$ | `jNum` | [X0 142](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularCurve_X0.lean#L142) |
| $`j = q^{-1}(q\cdot j)`$ | `jq` | [X0 157](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularCurve_X0.lean#L157) |
| leading term $`q^{-1}`$ | `coeff_jq_neg_one`, `coeff_jq_of_lt` | [X0 182–186](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularCurve_X0.lean#L182-L186) |
| $`j`$ has a simple pole at the cusp | `order_jq` | [QAdicPlace 12](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularCurve_QAdicPlace.lean#L12) |
| $`F_N^{\mathrm{full}} = \mathbb{Q}(j, j(q^N))`$ | `FunctionFieldGeneration` | [X0 233](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularCurve_X0.lean#L233) |
| $`[\mathbb{Q}(j, j(q^N)) : \mathbb{Q}(j)] = \psi(N)`$ | `finrank_adjoin_jqN_eq_dedekindPsi` | [Thm 8](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularCurve_finrank_adjoin_jqN_eq_dedekindPsi.lean#L8) |
| $`w_N`$ exchanges $`j`$ and $`j(q^N)`$ | `frickeInvolution`, `IsFrickeAut` | [AtkinLehner 16–21](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularCurve_AtkinLehner.lean#L16-L21) |
| analytic $`j`$ | `jAnalytic` | [LevelNFunctionField 22](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularCurve_LevelNFunctionField.lean#L22) |
| base-changed formal series | `jqModC`, `jqModC_rat` | [JqCoeff 15](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularCurve_JqCoeff.lean#L15) |
| analytic $`j`$ maps to formal series | `exists_algHom_laurentSeries_qExpansion` | [Thm 16–18](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularCurve_LevelN_exists_algHom_laurentSeries_qExpansion.lean#L16-L18) |
| analytic $`E_4`$, $`E_6`$ | `ModularForm.E₄`, `E₆` | [mathlib 51–54](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/NumberTheory/ModularForms/EisensteinSeries/Basic.lean#L51-L54) |
| $`\Delta = q \prod (1-q^n)^{24}`$ | `discriminant_eq_q_prod` | [mathlib 115](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/NumberTheory/ModularForms/Discriminant.lean#L115) |
| $`\Delta \ne 0`$ on $`\mathbb{H}`$ | `discriminant_ne_zero` | [mathlib 123](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/NumberTheory/ModularForms/Discriminant.lean#L123) |
| weight-zero forms are constant | `levelOne_weight_zero_rank_one` | [mathlib 109](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/NumberTheory/ModularForms/LevelOne/Basic.lean#L109) |

Three §5–§6 points have no row: the disc picture with its natural boundary, the
bijection $`X(1) \cong \mathbb{P}^1`$ behind the Hauptmodul property, and the
injectivity of the $`q`$-expansion that makes the formal function field a faithful
model. None is stated in mathlib or FLT; they are classical complex-analytic
facts, included because they are what make the formal series recognizably *the*
$`j`$-invariant rather than an arbitrary $`q^{-1}`$-series.

## 8. Lean detours (not mathematics)

Four encoding points, none of which changes the mathematics above.

- **Laurent series are Hahn series.** `LaurentSeries ℚ` is `HahnSeries ℤ ℚ`: a
  coefficient function on $`\mathbb{Z}`$ whose support is bounded below. Bounded
  below is exactly "finite pole order at $`q=0`$", and baking it into the type
  makes the series ring a *field* and gives every nonzero series a well-defined
  least exponent (its $`q`$-adic order) with no side conditions to carry. `jq`
  is the element `HahnSeries.single (-1) 1 * ofPowerSeries jNumQ`, i.e.
  $`q^{-1} \cdot \mathrm{jNum}`$.
- **`invOfUnit` is not a field inverse.** $`\Delta/q`$ has constant term $`1`$,
  so it is a unit of the *ring* $`\mathbb{Z}[[q]]`$; `dedekindEtaUnitInv` is
  its formal inverse, and `dedekindEtaUnit_mul_inv` records
  $`(\Delta/q)(\Delta/q)^{-1} = 1`$. This is where integrality of the
  $`j`$-coefficients is actually won (§4).
- **The Euler product is a `tprod`.** `etaProd` is an infinite product in the
  $`X`$-adic completion, and `constantCoeff_etaProd` is read off from continuity
  of `constantCoeff`. No convergence of $`\prod(1-q^n)`$ at a numerical $`q`$ is
  asserted.
- **Two encodings, one bridge.** `jAnalytic` is built from mathlib's analytic
  $`E_4`$ and $`\Delta`$, whereas `eisenstein4` and `etaProd` are FLT's own
  formal series; the one lemma tying the analytic function field to the formal
  world is the $`q`$-expansion homomorphism cited above, and it acts on the
  generator $`j`$ rather than on the individual series. `jNum` is a power series
  over $`\mathbb{Z}`$ and `jNumQ` is its base change
  `jNum.map (Int.castRingHom ℚ)`; `jqModC ℚ = jq` records that the general
  base-changed construction agrees with `jq` over $`\mathbb{Q}`$.

## 9. Links

FLT sources at the pinned sha `aa2d8b3`:

- [Def_ModularCurve_X0.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularCurve_X0.lean) — `eisenstein4`, `etaProd`, `dedekindEtaUnit`, `jNum`, `jq`, the leading-coefficient lemmas
- [Def_ModularCurve_LevelNFunctionField.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularCurve_LevelNFunctionField.lean) — `jAnalytic`, the Fricke generators, the analytic function-field ring
- [Def_ModularCurve_JqCoeff.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularCurve_JqCoeff.lean) — `jqModC`, `jqNModC`
- [Thm_ModularCurve_LevelN_exists_algHom_laurentSeries_qExpansion.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularCurve_LevelN_exists_algHom_laurentSeries_qExpansion.lean) — the $`q`$-expansion bridge
- [Def_ModularCurve_QAdicPlace.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularCurve_QAdicPlace.lean) — `order_jq`, the cusp valuation, the uniformizer
- [Def_ModularCurve_HeckeModule.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularCurve_HeckeModule.lean) — where the series is used

Mathlib at tag `v4.33.0`:

- [EisensteinSeries/Basic.lean](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/NumberTheory/ModularForms/EisensteinSeries/Basic.lean) — `E₄`, `E₆`
- [Discriminant.lean](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/NumberTheory/ModularForms/Discriminant.lean) — `Δ = η²⁴`, the product formula, nonvanishing
- [DedekindEta.lean](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/NumberTheory/ModularForms/DedekindEta.lean) — the eta function
- [LevelOne/Basic.lean](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/NumberTheory/ModularForms/LevelOne/Basic.lean) — weight-zero forms are constant

Companion notes:

- [002 — Modular forms at the mathlib level](002-modular-forms-basics.md) — the layer this note sits on
- [math/009 — The Hecke action on the Jacobian](../math/009-hecke-jacobian-commute.md) — what the series is used for
