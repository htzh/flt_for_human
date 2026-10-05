# Vélu isogenies, the quotient $`j`$-invariant, and the endomorphism ring

Twenty-third of the `math/` notes. The port of the Vélu block
([TOPIC-port-plan.md](../lean/topics/velu/TOPIC-port-plan.md)) has landed its four
headline theorems, together with the chord-formula node they consume and the
torsion promotion the dual column pulled after it. This note is about the
*mathematics* of those statements. They look like four unrelated theorems in a
91 k-line cluster; they are in fact two answers to one question.

The question is: **given an isogeny, what can be computed from its function-field
extension?** Both spines of the cluster answer it, from opposite ends.

* **Spine V (explicit Vélu).** Given a cyclic subgroup $`H \le E`$, write down the
  quotient curve $`E/H`$ and the isogeny $`E \to E/H`$ as rational formulas. The
  payoff is the *quotient* $`j`$-invariant: the map $`H \mapsto j(E/H)`$, hence the
  modular polynomial $`\Phi_N`$ and the moduli interpretation of $`X_0(N)`$.
* **Spine E (isogeny data).** Given an $`F`$-algebra embedding of function fields,
  compute the induced endomorphism of $`E(F)`$ and its *dual, trace and norm*. The
  payoff is the structure of $`\mathrm{End}(E)`$: complex multiplication, the norm
  form of an order in an imaginary quadratic field, and the fact that a generic
  curve has $`\mathrm{End}(E) = \mathbb{Z}`$.

The two meet in §6: the first is what level lowering (Ribet, Čerednik–Drinfeld)
consumes, the second is what Mazur's Eisenstein-ideal argument consumes. Both are
on the shortest citation path from the pin's landing statements to
`fermat_last_theorem`.

Everything is cited against the pinned pin
`anthropics/fermats-last-theorem@aa2d8b3`; mathlib declarations are named at the
port's tag **v4.34.0**. Line anchors are on `blob` links (rendered); the raw
addresses, which carry no anchor, are used only where a proof body is quoted.
Where this prose and the Lean differ, the Lean is right.

The plan:

1. isogenies as extensions of function fields, and the place seam to points;
2. Vélu's explicit formulas: the map, and the function-field isogeny;
3. the quotient $`j`$-invariant and the modular polynomial;
4. the endomorphism ring: dual, trace, norm, and the CM dichotomy;
5. the counting input: $`E[n] \cong (\mathbb{Z}/n)^2`$;
6. who consumes all this in the FLT proof;
7. the Lean and port picture.

## 1. Isogenies as extensions of function fields

Fix a field $`F`$, an elliptic curve $`W`$ over $`F`$ ($`\Delta \ne 0`$), and write

$$K = W.\mathrm{FunctionField} = F(W)$$

for its function field. For Spine E we take $`F`$ algebraically closed of
characteristic $`0`$; for the explicit Vélu formulas characteristic $`0`$ is not
needed, and the general headline is stated characteristic-free.

The translation between geometry and algebra is the pin's
[`Def_AlgebraicCurve_Correspondence.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_Correspondence.lean).
An isogeny $`\varphi : W \to V`$ of elliptic curves over $`F`$ corresponds to an
inclusion of function fields

$$\iota = \varphi^{\ast} : F(V) \hookrightarrow F(W),$$

and the degree is a module rank,

$$\deg \varphi = [F(W) : F(V)] = \texttt{finrankAlong}\ F\ \iota$$

([line 51](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_Correspondence.lean#L51)),
with `FiniteAlong` the statement that $`F(W)`$ is finite over $`F(V)`$ along
$`\iota`$, and `NormFormulaAlong` the statement that the norm on divisors
descends: pushing forward the divisor $`\mathrm{div}(f)`$ gives
$`\mathrm{div}(\mathrm{N}(f))`$
([lines 37 and 43](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_Correspondence.lean#L37-L45)).

Two operations on divisors live here, and it is worth keeping them apart because
the whole of §4 turns on it:

* the **pullback** (function direction), $`\varphi^{\ast} = \iota`$, which is the
  isogeny read on functions;
* the **pushforward** (norm direction), $`\varphi_{\ast}`$, which sends a point
  $`P`$ to $`\varphi(P)`$; and

$$\varphi_{\ast} \circ \varphi^{\ast} = [\deg \varphi] \qquad \text{on divisor classes.}$$

On places, restriction is the pullback of the valuation ring: for a place $`w`$ of
$`F(W)`$, `Place.restrictAlong ι hι w` is the place of $`F(V)`$
([line 204](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_Correspondence.lean#L204)).
This is how "the isogeny sends the point $`P`$ to the point $`Q`$" is stated in the
pin: not by evaluating a formula, but by the identity of places

$$\texttt{placeOfPoint}\ Q = (\texttt{placeOfPoint}\ P).\texttt{restrictAlong}\ \iota .$$

**The seam.** The bridge from divisors to the group law is the gate of
[`Def_WeierstrassCurve_GenusOnePic0.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_WeierstrassCurve_GenusOnePic0.lean):

* `GenusOnePlaceGate W` — a bijection
  $`W.\mathrm{Point} \simeq \mathrm{Place}(F, F(W))`$ whose places all have degree
  one ([line 18](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_WeierstrassCurve_GenusOnePic0.lean#L18));
* `GenusOnePlaceGate.IsCentred W` — at the place of a nonsingular $`(x,y)`$ the
  classes of $`X - x`$ and $`Y - y`$ are non-units
  ([line 14](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_WeierstrassCurve_GenusOnePlaceGateCentred.lean#L14));
* `AbelTheorem W` — a degree-zero divisor is principal exactly when its sum of
  points is zero
  ([line 95](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_WeierstrassCurve_GenusOnePic0.lean#L95)).

Together they upgrade the degree-zero part of the class group to the group of
points,
$`\texttt{genusOnePic0Equiv} : \mathrm{Pic}^0 \simeq_+ W.\mathrm{Point}`$
([line 149](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_WeierstrassCurve_GenusOnePic0.lean#L149)), and with it the
isogeny $`\varphi`$ becomes an honest group homomorphism:

```lean
def pointMapOfPushforward : W.Point →+ V.Point :=
  ((genusOnePic0Equiv V).toAddMonoidHom.comp
      (Pic0.pushforwardAlongHom ι hι hfin hN)).comp
    (genusOnePic0Equiv W).symm.toAddMonoidHom
```

([Def_Isogeny_ConditionalCurrency.lean, lines 102–105](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_Isogeny_ConditionalCurrency.lean#L102-L105)).

Its defining property is the **seam lemma** `pointMapOfPushforward_eq_of_seam`
([line 114](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_Isogeny_ConditionalCurrency.lean#L114-L118)): if a map
$`g`$ of points satisfies $`g(0) = 0`$ and
$`\texttt{placeOfPoint}(g\,P) = (\texttt{placeOfPoint}\,P).\texttt{restrictAlong}\,\iota`$
for all $`P`$, then $`g = \texttt{pointMapOfPushforward}`$. That lemma is the
engine of the whole port: it converts a place-compatibility computation — the only
kind the divisor calculus can do — into the identification of an explicit rational
map with the isogeny.

An `IsogenyEndDatum W` is this data with $`V = W`$: an integral $`F`$-algebra
endomorphism $`\iota`$ of $`K`$ together with its finiteness
([line 149](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_Isogeny_ConditionalCurrency.lean#L149-L157)); its `pointEnd` is
$`\texttt{pointMapOfPushforward}\,\iota`$
([line 161](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_Isogeny_ConditionalCurrency.lean#L161-L165)), and
`isogenyEndSubring W hNs` is the subring of $`\mathrm{End}(W.\mathrm{Point})`$
generated by all the `pointEnd`s
([line 180](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_Isogeny_ConditionalCurrency.lean#L180-L182)). Whether
that subring is *really* the endomorphism ring is one of the two H5 headlines,
and §4 answers it.

## 2. Vélu's explicit formulas

### 2.1 The local data at a point

Let $`W : y^2 + a_1xy + a_3y = x^3 + a_2x^2 + a_4x + a_6`$ and let
$`P = (x_P, y_P)`$ be a point. Vélu's construction is driven by the quantities at
$`P`$ of
[Def_WeierstrassCurve_Velu.lean, lines 10–18](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_WeierstrassCurve_Velu.lean#L10-L18):

```lean
def veluGx (x y : R) : R := 3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y
def veluGy (x y : R) : R := -(2 * y + W.a₁ * x + W.a₃)
def veluT (x y : R) : R := 2 * W.veluGx x y - W.a₁ * W.veluGy x y
def veluU (x y : R) : R := W.veluGy x y ^ 2
def veluW (x y : R) : R := W.veluU x y + x * W.veluT x y
```

$`g^x`$ is the numerator of the tangent-line equation at $`P`$ and $`g^y`$ the
vertical derivative, so that $`(g^x, g^y)`$ is the velocity vector of the group law
at $`P`$. The two combinations that matter are

$$t_P = 2g^x - a_1g^y = 6x_P^2 + b_2x_P + b_4 , \qquad u_P = (g^y)^2 ,$$

and on the curve $`u_P`$ is mathlib's division polynomial,
$`u_P = \Psi_2\mathrm{Sq}(x_P)`$
([`veluU_eq_Ψ₂Sq_eval`, line 23](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_WeierstrassCurve_Velu.lean#L23-L29)). Two facts are used constantly:

* $`t_P`$ depends only on $`x_P`$ (`veluT_eq`), hence is unchanged by
  $`y \mapsto -y - a_1x - a_3`$;
* $`u_P = (g^y)^2`$ is likewise unchanged, and $`u_P = 0`$ exactly at the
  abscissae of $`2`$-torsion, because $`\Psi_2\mathrm{Sq}(x)`$ is the $`2`$-division
  polynomial.

### 2.2 The quotient curve and the quotient map

For a finite set $`S \subseteq F \times F`$ of points, the **Vélu quotient** is the
Weierstrass curve whose first three coefficients are unchanged and whose last two
are shifted by the sums of $`t`$ and $`w`$
([lines 51–66](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_WeierstrassCurve_Velu.lean#L51-L66)):

```lean
def veluQuotient : WeierstrassCurve R where
  a₁ := W.a₁
  a₂ := W.a₂
  a₃ := W.a₃
  a₄ := W.a₄ - 5 * W.veluTSum S
  a₆ := W.a₆ - W.b₂ * W.veluTSum S - 7 * W.veluWSum S
```

and the **quotient map** acts on coordinates by

$$X(P) = x + \sum_{Q \in S}\left(\frac{t_Q}{x - x_Q} + \frac{u_Q}{(x - x_Q)^2}\right),$$

$$Y(P) = y - \sum_{Q \in S}\left( \frac{u_Q\\,(2y + a_1x + a_3)}{(x - x_Q)^3} + \frac{t_Q\bigl(a_1(x - x_Q) + y - y_Q\bigr)}{(x - x_Q)^2} + \frac{a_1u_Q - g^x_Q\\,g^y_Q}{(x - x_Q)^2} \right),$$

the definitions `veluX`/`veluY`
([VeluQuotientMap.lean line 47](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_WeierstrassCurve_VeluQuotientMap.lean#L47-L48),
[VeluPointMap.lean line 51](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_WeierstrassCurve_VeluPointMap.lean#L51-L54)). The
constants $`5`$ and $`7`$ are Vélu's.

**The first headline.** The map lands on the quotient curve:

> `WeierstrassCurve.velu_map_equation_of_oddOrderSummingSet_of_isAlgClosed`
> ([Thm file, line 8](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_WeierstrassCurve_velu_map_equation_of_oddOrderSummingSet_of_isAlgClosed.lean#L8-L15)):
> for an algebraically closed $`L`$ of *arbitrary* characteristic, $`W/L`$
> elliptic, $`Q`$ of order $`2n+1`$, $`S = \texttt{oddOrderSummingSet}\ Q\ n`$,
> and $`(x,y) \in W`$ with $`x`$ avoiding the abscissae in $`S`$,
> $`(X(x),\,Y(x,y))`$ satisfies the equation of $`W.\texttt{veluQuotient}\ S`$.

### 2.3 Why one representative per $`\pm`$ pair

The summing set is exactly one representative from each pair $`\pm kQ`$
([Def_WeierstrassCurve_OddOrderSummingSet.lean, lines 24–27](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_WeierstrassCurve_OddOrderSummingSet.lean#L24-L27)):

```lean
def oddOrderSummingSet (Q : W.toAffine.Point) (n : ℕ) : Finset (F × F) :=
  (Finset.Icc 1 n).image fun k => (k • Q).coordsOrZero
```

If $`Q`$ has order $`2n+1`$, the nontrivial kernel is
$`\{\pm Q, \pm 2Q, \dots, \pm nQ\}`$, of size $`2n`$, and $`S`$ picks one from each
pair. This is legitimate precisely because $`t_Q`$, $`u_Q`$ and $`w_Q`$ are invariant
under $`Q \mapsto -Q`$: the Vélu sums over the whole kernel are twice the sums over
$`S`$, and the standard formulas are written for the representative set. The odd
order is what makes the pairs disjoint from the identity; for a kernel containing
$`2`$-torsion, $`-Q = Q`$ and this bookkeeping fails, which is why the order-two
quotient has its own formulas (`veluQuotient2`, the H2 order-two nodes) and why the
odd case is separated in the pin.

The `IsOddVeluSet` predicate records exactly the three hypotheses the odd-order
argument needs: the points are on the curve, $`g^y \ne 0`$ (no $`2`$-torsion), and
the $`x`$-coordinates are injective on $`S`$
([lines 10–17](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_WeierstrassCurve_VeluQuotientMap.lean#L10-L17)).

### 2.4 The computational core, and how it is aggregated

The atomic case is the singleton $`S = \{(x_0,y_0)\}`$ with $`\Psi_3(x_0) = 0`$,
i.e. a kernel of order $`3`$. There the map identity is *one* polynomial identity,
cleared of denominators:

> `velu_singleton_equation_cleared`
> ([VeluPointMap.lean, lines 28–49](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_WeierstrassCurve_VeluPointMap.lean#L28-L49)):
> for $`(x,y)`$ on $`W`$, $`(x_0,y_0)`$ on $`W`$ with $`\Psi_3(x_0) = 0`$, the
> quantity $`\texttt{veluYNum}^2 + a_1\,\texttt{veluXNum}\,\texttt{veluYNum}\,(x-x_0) + a_3\,\texttt{veluYNum}\,(x-x_0)^3`$
> equals
> $`\texttt{veluXNum}^3 + a_2\texttt{veluXNum}^2(x-x_0)^2 + (a_4 - 5t)(\texttt{veluXNum})(x-x_0)^4 + (a_6 - b_2t - 7w)(x-x_0)^6`$.

The pin proves this by a single `linear_combination` whose coefficient polynomial
fills several hundred lines — the "one enormous `linear_combination`" the subject
study flagged. It is the only genuinely computational identity in the spine; the
rest of the spine is the algebra that propagates it to an arbitrary odd kernel.

The propagation is *not* a term-by-term summation: the denominators
$`(x - x_Q)^k`$ differ from point to point. What makes it work is the *deficit*
$`X(P) - x`$ viewed as a rational function on $`W`$: it has poles precisely at the
points of $`S`$ (with prescribed principal parts $`t_Q/(x-x_Q) + u_Q/(x-x_Q)^2`$) and
is regular elsewhere, including at infinity once the curve is corrected. A rational
function on an elliptic curve with a prescribed divisor is determined up to a
constant, and the order/evaluation calculus of the `AlgebraicCurve` place layer
(`ord`, `evalAt`, `placeOfEquation`, and the H5r-relocated dictionary) is exactly
what turns "the principal parts match" into "the function is the quotient map". That
is the mathematical content of the pin's `veluDeficit`/`VeluDeficitFun*` carrier
chain, of the `veluDeficitIsConstantAt`/`veluDeficitConstancyAt` lemmas, and of the
`evalAt_velu*_placeOfEquation` discharge.

### 2.5 The second headline: the isogeny as a function-field extension

The map identity upgrades to the structural statement:

> `WeierstrassCurve.exists_veluFunctionFieldHom_restrictAlong_placeOfPoint_eq_of_isAlgClosed`
> ([Thm file, line 12](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_WeierstrassCurve_exists_veluFunctionFieldHom_restrictAlong_placeOfPoint_eq_of_isAlgClosed.lean#L12-L40)):
> if $`Q`$ has order $`2n+1`$ and the Vélu quotient $`W' = W.\texttt{veluQuotient}\,S`$
> is elliptic, and both $`W`$ and $`W'`$ carry the place gate, then there are an
> integral $`F`$-algebra map $`\iota : F(W') \to F(W)`$ and a finiteness proof such
> that
> 1. $`\texttt{finrankAlong}\ F\ \iota = 2n+1`$;
> 2. the kernel of $`\texttt{pointMapOfPushforward}\ \iota`$ is
>    $`\langle Q \rangle`$;
> 3. every point of $`\langle Q \rangle`$ restricts to the origin of $`W'`$;
> 4. every nonsingular $`(x,y) \notin \langle Q \rangle`$ maps to the nonsingular
>    Vélu image $`(X(x), Y(x,y))`$ of $`W'`$.

This is Vélu's theorem in the form the rest of the FLT project uses: an isogeny is
an extension of function fields of the predicted degree, with prescribed kernel and
prescribed place restriction. Note the two hypotheses $`\Delta(W') \ne 0`$ and
$`[W'.\mathrm{IsElliptic}]`$: the formulas produce a Weierstrass equation, and one
must know the quotient has not degenerated. That is what the discriminant identity
of the next paragraph is for.

### 2.6 The discriminant identity

Adjacent to the two headlines, and the arithmetic content behind the
$`\Delta \ne 0`$ hypothesis, is

> `WeierstrassCurve.veluQuotient_oddOrderSummingSet_discriminant_prod_veluU_pow`
> ([Thm file, line 8](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_WeierstrassCurve_veluQuotient_oddOrderSummingSet_discriminant_prod_veluU_pow.lean#L8-L11)):

$$\Delta\left(W.\texttt{veluQuotient}\ S\right)\cdot \left(\prod_{P \in S} u_P\right)^{4} = \Delta(W)^{2n+1} , \qquad S = \texttt{oddOrderSummingSet}\ Q\ n .$$

Mathematically: an $`\ell`$-isogeny, $`\ell = 2n+1`$, multiplies the discriminant by
an $`\ell`$-th-power factor, corrected by the fourth power of the product of the
$`u_P`$. Since $`u_P = \Psi_2\mathrm{Sq}(x_P)`$ vanishes exactly at the
$`2`$-torsion abscissae, the correction term is also the statement of where the
quotient can fail to stay smooth, and hence of when $`E/H`$ is again an elliptic
curve. At $`n = 0`$ (the trivial kernel) it reads $`\Delta = \Delta`$.

## 3. The quotient $`j`$-invariant and the modular polynomial

### 3.1 The quotient $`j`$

For a subgroup $`H`$, the pin builds the quotient one prime at a time. If $`H`$ is
cyclic of order $`N = pM`$, it has a unique subgroup $`H[p]`$ of order $`p`$, and

$$E/H \cong (E/H[p]) / \overline{H/H[p]} ,$$

so `cqjIterate` removes the prime factors of $`N`$ successively and
`cyclicQuotientCurve H N` is the result
([Def_WeierstrassCurve_CyclicQuotientJ.lean, lines 137–147](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_WeierstrassCurve_CyclicQuotientJ.lean#L137-L147)).
Its $`j`$-invariant is written out as

```lean
def cyclicQuotientJ (V : WeierstrassCurve L) (H : AddSubgroup V.toAffine.Point) (N : ℕ) : L :=
  (V.cyclicQuotientCurve H N).c₄ ^ 3 / (V.cyclicQuotientCurve H N).Δ
```

which is mathlib's `WeierstrassCurve.j` (defined as $`\Delta^{-1}c_4^3`$) with the
division spelled out.

### 3.2 The modular polynomial as an abstract datum

The pin does not construct $`\Phi_N`$ from the $`q`$-expansion; it takes it as a
datum and proves the properties it needs. `ModularPolynomialData N` is a polynomial
$`\Phi \in \mathbb{Z}[X][Y]`$, monic in $`Y`$, with

$$\deg_Y \Phi = \psi(N) := \sum_{d \mid N,\ d\ \text{squarefree}} \frac{N}{d} = [\mathrm{SL}_2(\mathbb{Z}) : \Gamma_0(N)] ,$$

satisfying $`\Phi(j(q), j(q^N)) = 0`$
([Def_ModularCurve_X0.lean, lines 215–224](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularCurve_X0.lean#L215-L224)).
The degree $`\psi(N)`$ is the number of cyclic subgroups of order $`N`$ in
$`(\mathbb{Z}/N)^2`$; for $`N = p`$ prime it is $`p+1`$.

### 3.3 Kronecker's theorem, sharpened

The classical content is that the roots of $`\Phi_N(j(E),\,Y)`$ are exactly the
quotient $`j`$-invariants:

> `WeierstrassCurve.bijOn_cyclicQuotientJ_isRoot_modularPolynomial_of_transcendental_j`
> ([Thm file, line 19](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_WeierstrassCurve_bijOn_cyclicQuotientJ_isRoot_modularPolynomial_of_transcendental_j.lean#L19-L25)):
> let $`K`$ be a field, $`N \ne 0`$, $`\Phi`$ a modular-polynomial datum of level
> $`N`$, $`L`$ an algebraically closed $`K`$-algebra with $`N \ne 0`$ in $`L`$, and
> $`E/L`$ elliptic with $`j(E)`$ transcendental over $`K`$. Then the map sending a
> cyclic subgroup $`H \le E(L)`$ of order $`N`$ to
> $`E.\texttt{cyclicQuotientJ}\ H\ N`$ is a bijection from those subgroups onto the
> roots in $`L`$ of $`\Phi`$ with the $`X`$-coefficients evaluated at $`j(E)`$
> (inclusion, injectivity, and surjectivity).

Its corollaries are the ones that get used:

* `map_modularPolynomial_j_eq_finprod_X_sub_C_cyclicQuotientJ` — the fibre
  polynomial splits into distinct linear factors, so at every elliptic curve
  $`\Phi_N(j(E),Y) = \prod_{H}(Y - j(E/H))`$ over the cyclic $`H`$ of order $`N`$;
* `ModularPolynomialData.separable_map_eval2RingHom_j_of_transcendental` —
  separability of $`\Phi_N(j(E),Y)`$ for transcendental $`j(E)`$;
* `exists_equiv_addSubgroup_isAddCyclic_isRoot_modularPolynomial_of_transcendental_j`
  — the Galois-equivariant version, matching cyclic subgroups to root slots with
  the action of $`\mathrm{Gal}`$.

### 3.4 Why "transcendental" is the right hypothesis

The bijection is *not* formal, and its failure is exactly complex multiplication.
If $`E`$ has an extra endomorphism, distinct cyclic subgroups can have isomorphic
quotients, so $`H \mapsto j(E/H)`$ is not injective and $`\Phi_N(j(E),Y)`$ acquires a
multiple root. The extreme case is instructive: the fibre of $`X_0(N) \to X_0(1)`$
over $`j_0`$ has $`\psi(N)`$ points counted with multiplicity, and the multiplicity
at $`j(E/H)`$ is $`\gt 1`$ precisely when $`E/H \cong E/H'`$ for two different cyclic
$`H`$, i.e. when a CM structure appears. This is why the sharp statements of the
next section all carry a hypothesis of the form "$`j`$ is not an algebraic integer"
or "$`j`$ is transcendental": they are hypotheses that rule out extra
endomorphisms, which is exactly what §4 proves they do.

## 4. The endomorphism ring

### 4.1 Dual isogenies

For an isogeny $`\varphi : E \to E'`$ of degree $`n`$ there is a dual isogeny
$`\hat\varphi : E' \to E`$ with

$$\hat\varphi \circ \varphi = [n], \qquad \varphi \circ \hat\varphi = [n], \qquad \deg \hat\varphi = \deg \varphi .$$

For an endomorphism $`\varphi`$, the **trace** $`t = \varphi + \hat\varphi`$ is an
integer and the **norm** is $`n = \varphi\hat\varphi = [\deg\varphi]`$; the
endomorphism satisfies its characteristic polynomial

$$\varphi^2 - t\\,\varphi + n = 0 .$$

This is the classical formalism of Silverman, *Arithmetic of Elliptic Curves*,
III.6 (and III.9 for the CM consequences).

The pin isolates the algebra in `Def_DualIsogenyAPI.lean`. The primitive notion is
a dual *pair* ([lines 9–13](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_DualIsogenyAPI.lean#L9-L13)):

```lean
structure IsDualPair (φ : A →+ B) (ψ : B →+ A) (n : ℤ) : Prop where
  comp_left : ∀ a, ψ (φ a) = n • a
  comp_right : ∀ b, φ (ψ b) = n • b
```

and the packaged form is `DualEndData φ`
([lines 83–99](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_DualIsogenyAPI.lean#L83-L99)):

```lean
structure DualEndData (φ : AddMonoid.End A) where
  dual : AddMonoid.End A
  trace : ℤ
  norm : ℤ
  add_dual : φ + dual = (trace : AddMonoid.End A)
  mul_dual : φ * dual = (norm : AddMonoid.End A)
  dual_mul : dual * φ = (norm : AddMonoid.End A)
```

From the axioms the module derives `charPoly`, and — the computation that makes the
structure theorem work — the **norm form**: for $`a, b \in \mathbb{Z}`$ the element
$`a + b\varphi`$ has

$$N(a + b\varphi) = a^2 + t\\,ab + n\\,b^2, \qquad \mathrm{tr}(a + b\varphi) = 2a + tb, \qquad \mathrm{disc}(a + b\varphi) = b^2\\,(t^2 - 4n) ,$$

with dual $`a + b\hat\varphi`$ (`intLinComb`,
[lines 177–190](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_DualIsogenyAPI.lean#L177-L190)). The
`disc` identity is where "everything scales by $`b^2`$" is recorded, and
`intLinComb_disc_neg` turns $`t^2 \lt 4n`$ into $`\mathrm{disc} \lt 0`$ for every
$`b \ne 0`$.

There are also two named residuals, `DualIsogenyExistence` and
`DualAdditivityResidual`
([lines 274–281](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_DualIsogenyAPI.lean#L274-L281)): the first is the existence of a
dual in a subring with nonnegative norm, the second is additivity of the dual. They
are precisely what the two H5 headlines establish, and they are the reason those
headlines exist as separate targets.

### 4.2 The dual realised by the conorm

In the function-field idiom the dual is not an extra construction: it is the other
direction on divisors. The pullback is the isogeny on functions, and the
pushforward is the norm map; the pin proves

$$\texttt{pushforwardAlong}\ \iota\ \left(\texttt{pullbackAlong}\ \iota\ D\right) = (\texttt{finrankAlong}\ F\ \iota) \cdot D ,$$

i.e. $`\varphi_{\ast}\varphi^{\ast} = [\deg\varphi]`$ on divisors
(`es1a1_dual_pushforwardAlong_pullbackAlong`,
[S_…exists_dualEndData…, line 1107](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_WeierstrassCurve_Affine_IsogenyEndDatum_exists_dualEndData_dual_mem_and_norm_eq_finrankAlong.lean#L1107-L1115)).
The dual point map is then the **conorm** on $`\mathrm{Pic}^0`$, `es1a1_conormPic0Hom`,
composed with the two genus-one equivalences (`es1a1_dualPointEnd`,
[line 1136](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_WeierstrassCurve_Affine_IsogenyEndDatum_exists_dualEndData_dual_mem_and_norm_eq_finrankAlong.lean#L1136-L1141)), and the
defining identity becomes $`\texttt{pointEnd}' \cdot \texttt{dualPointEnd} = \deg`$
([line 1149](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_WeierstrassCurve_Affine_IsogenyEndDatum_exists_dualEndData_dual_mem_and_norm_eq_finrankAlong.lean#L1149-L1158)).

Two inputs beyond the divisor identity are needed, and both are already in the
cluster:

* the dual is **unique**: if $`\varphi\psi = [\deg\varphi]`$ then
  $`\psi = \hat\varphi`$ (`kw_dualPointEnd_unique`,
  [line 7955](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_WeierstrassCurve_Affine_IsogenyEndDatum_exists_dualEndData_dual_mem_and_norm_eq_finrankAlong.lean#L7955-L7960)). The proof kills the
  difference on the left and uses that $`[\deg]`$ is surjective on $`E(F)`$ together
  with $`\#\ker = \deg`$ — the divisibility theorem and the card-torsion port of
  §5.
* the **trace witness**: for every datum $`D`$ there is $`t \in \mathbb{Z}`$ with
  $`D.\texttt{pointEnd}' + \texttt{kw\_dualPointEnd}\ D = t`$
  (`KwDualTraceWitness`,
  [line 7962](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_WeierstrassCurve_Affine_IsogenyEndDatum_exists_dualEndData_dual_mem_and_norm_eq_finrankAlong.lean#L7962-L7965)). This is
  the classical integrality of $`\mathrm{tr}\,\varphi`$; the pin obtains it from
  *additivity of the dual*, `kw_hk5f_dualTraceWitness_of_dualAdditivity`
  ([line 8514](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_WeierstrassCurve_Affine_IsogenyEndDatum_exists_dualEndData_dual_mem_and_norm_eq_finrankAlong.lean#L8514)), which is
  the other headline.

### 4.3 The two H5 headlines

**The dual.** With the trace witness in hand, $`\hat\varphi = t - \varphi`$ is a
difference of two elements of the subring, hence lies in it
(`kw_dualInSubring_of_traceWitness`,
[line 7966](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_WeierstrassCurve_Affine_IsogenyEndDatum_exists_dualEndData_dual_mem_and_norm_eq_finrankAlong.lean#L7966-L7976)); and the norm is
$`\deg = \texttt{finrankAlong}`$ by §4.2. That assembles the first headline:

> `WeierstrassCurve.Affine.IsogenyEndDatum.exists_dualEndData_dual_mem_and_norm_eq_finrankAlong`
> ([Thm file, line 15](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_WeierstrassCurve_Affine_IsogenyEndDatum_exists_dualEndData_dual_mem_and_norm_eq_finrankAlong.lean#L15-L21)):
> for $`F`$ algebraically closed of characteristic $`0`$, $`W/F`$ elliptic with the
> place gate, and `hNs` the norm formula for every datum, every `D` admits
> $`DD : \texttt{DualEndData}\ (D.\texttt{pointEnd})`$ with
> $`DD.\texttt{dual} \in \texttt{isogenyEndSubring}\ W\ hNs`$ and
> $`DD.\texttt{norm} = \texttt{finrankAlong}\ F\ D.\iota`$.

In words: *the dual isogeny exists, is again an isogeny-induced endomorphism, and
its degree is the function-field degree*.

**Additivity.** The second headline is the closure of the set of isogeny-induced
endomorphisms under addition:

> `WeierstrassCurve.Affine.IsogenyEndDatum.exists_restrictAlong_placeOfPoint_eq_add`
> ([Thm file, line 13](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_WeierstrassCurve_Affine_IsogenyEndDatum_exists_restrictAlong_placeOfPoint_eq_add.lean#L13-L23)):
> for two data $`D_1, D_2`$ with norm formulas, and
> $`D_1.\texttt{pointEnd} + D_2.\texttt{pointEnd} \ne 0`$, there is a third datum
> $`D_3`$ with

$$(\texttt{placeOfPoint}\ P).\texttt{restrictAlong}\ D_3.\iota = \texttt{placeOfPoint}\left( \texttt{pointEquivPlace}^{-1}\left((\texttt{placeOfPoint}\ P).\texttt{restrictAlong}\ D_1.\iota\right) + \texttt{pointEquivPlace}^{-1}\left((\texttt{placeOfPoint}\ P).\texttt{restrictAlong}\ D_2.\iota\right) \right)$$

> for every point $`P`$.

Mathematically this is chord-and-tangent addition: if $`\varphi_1,\varphi_2`$ are the
two endomorphisms, form the two "$`K`$-points" $`(x_i,y_i) = (\varphi_i(x),\varphi_i(y))`$
in the generic fibre, add them with the group-law formulas, and observe that the
result is again a pair generating the function field over $`F`$, hence again an
isogeny datum. The content is that the *place* compatibility survives the
degeneracies of the addition law — a pole, a vertical chord, a tangent. That is the
separate node

> `WeierstrassCurve.Affine.FunctionField.addX_addY_specialize_at_place`
> ([Thm file, line 12](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_WeierstrassCurve_Affine_FunctionField_addX_addY_specialize_at_place.lean#L12-L31)):
> if $`\lambda, x_3, y_3`$ are the slope and the sum coordinates of the generic
> points $`(x_1,y_1)`$, $`(x_2,y_2)`$, outside the degenerate case
> $`x_1 = x_2 \wedge y_1 = -y_2`$ and with $`x_3 \notin F`$, then for every place
> $`v`$ and every pair $`Q_1, Q_2`$ of $`F`$-points with the place of $`(x_i,y_i)`$
> centred at $`Q_i`$, the place of $`(x_3,y_3)`$ is centred at $`Q_1 + Q_2`$
> (including the case $`Q_1 + Q_2 = 0`$, where it is the place at infinity).

This node is a canonical pin target in its own right — 3,061 lines, not in the
plan's 42-node slice, discovered only because the restrictAlong column of H5
consumes it — and it is the clearest single example of the port's rule that *a
set's declaration list is the route closure of its deliverable, not the cluster
intersection of its files*.

**Closing the ring.** The additivity headline upgrades to the point-level statement
`exists_pointEnd_eq_add`, and then to the statement that the generated subring
contains nothing new:

> `WeierstrassCurve.Affine.IsogenyEndDatum.exists_pointEnd_eq_of_mem_isogenyEndSubring`
> ([Thm file, line 15](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_WeierstrassCurve_Affine_IsogenyEndDatum_exists_pointEnd_eq_of_mem_isogenyEndSubring.lean#L15-L20)):
> every nonzero $`\psi \in \texttt{isogenyEndSubring}\ W\ hNs`$ is
> $`D.\texttt{pointEnd}`$ for some datum $`D`$.

So `isogenyEndSubring` really is the ring of endomorphisms coming from isogenies,
and degree/norm computations can be transferred to an arbitrary nonzero element of
it.

### 4.4 Additivity of the dual

The trace witness is the last piece, and it is where the two H5 columns meet.
`KwDualConormAdditivityAtOne` and `KwDualAdditivityPhiRowGenericW`
([line 8385](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_WeierstrassCurve_Affine_IsogenyEndDatum_exists_dualEndData_dual_mem_and_norm_eq_finrankAlong.lean#L8385),
[line 8558](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_WeierstrassCurve_Affine_IsogenyEndDatum_exists_dualEndData_dual_mem_and_norm_eq_finrankAlong.lean#L8558)) record the
statement that the conorm of a sum is the sum of the conorms — again a
place-compatibility statement, discharged through the `addX_addY_specialize_at_place`
node. The chain is

```text
additivity of pointEnd  ==>  dual additivity  ==>  trace witness  ==>  dual in the subring
```

That is why the DAG in
[TOPIC-H5-engine.md](../lean/topics/velu/TOPIC-H5-engine.md) §2 makes SET-3 (the
dual) import SET-2 (the restrictAlong-add column): mathematically they are one
argument with two conclusions.

### 4.5 The dichotomy: $`\mathrm{End}(E) = \mathbb{Z}`$ or an imaginary quadratic order

With the subring identified, the structure of $`\mathrm{End}(E)`$ follows by pure
algebra:

> `WeierstrassCurve.Affine.IsogenyEndDatum.exists_sq_lt_four_mul_and_forall_exists_finrankAlong_eq`
> ([Thm file, line 15](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_WeierstrassCurve_Affine_IsogenyEndDatum_exists_sq_lt_four_mul_and_forall_exists_finrankAlong_eq.lean#L15-L21)):
> if some datum $`D_0`$ has a `pointEnd` that is not $`P \mapsto m\cdot P`$ for any
> $`m \in \mathbb{Z}`$, then there are $`t, n \in \mathbb{Z}`$ with
> $`t^2 \lt 4n`$ and, for all $`a, b \in \mathbb{Z}`$ with $`b \ne 0`$, a datum
> $`D`$ with

$$\texttt{finrankAlong}\ F\ D.\iota = a^2 + t\\,ab + n\\,b^2 .$$

The mathematics is exactly §4.1:

* The values $`a^2 + tab + nb^2`$ with $`b \ne 0`$ are degrees, hence *positive*;
  so the binary quadratic form $`(a,b) \mapsto a^2 + tab + nb^2`$ is positive
  definite, and its discriminant $`t^2 - 4n`$ is negative. (The case
  $`t^2 = 4n`$ is separately impossible: then $`t`$ is even and
  $`T^2 - tT + n = (T - t/2)^2`$, so $`D_0`$ would be the scalar $`t/2`$.)
* A negative discriminant means $`\mathbb{Z}[D_0]`$ is an order in the imaginary
  quadratic field $`\mathbb{Q}(\sqrt{t^2-4n})`$, and the endomorphism
  $`a + bD_0`$ has norm $`a^2 + tab + nb^2`$ by the norm-form identity of §4.1.
* By `exists_pointEnd_eq_of_mem_isogenyEndSubring`, every such element is a
  `pointEnd`, so its norm is a degree $`\texttt{finrankAlong}`$.

So the conclusion is the classical statement: **a non-integral endomorphism means
complex multiplication by an order in an imaginary quadratic field, and the degree
is the norm form of that order.** The references are Silverman III.9.3 and
*Advanced Topics*, Chapter II.

### 4.6 Generic curves have no complex multiplication

Now the two hypotheses "not an algebraic integer" and "transcendental" earn their
keep:

> `WeierstrassCurve.Affine.IsogenyEndDatum.exists_forall_pointEnd_eq_zsmul_of_not_isIntegral_j`
> and `…_of_transcendental_j`
> ([Thm file](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_WeierstrassCurve_Affine_IsogenyEndDatum_exists_forall_pointEnd_eq_zsmul_of_transcendental_j.lean#L15-L21)):
> if $`j(W)`$ is not integral over $`\mathbb{Z}`$ — in particular if it is
> transcendental over $`\mathbb{Q}`$ — then every datum's `pointEnd` is
> multiplication by an integer.

The proof is short and beautiful, and it shows why the two spines are one subject.
Suppose some $`D_0`$ is non-scalar. By §4.5 choose $`t, n`$ with $`t^2 \lt 4n`$ and
pick $`a, b`$ — the pin's number-theoretic input is
`Int.exists_squarefree_sq_add_mul_add_mul_sq_of_sq_lt_four_mul` — so that

$$N = a^2 + tab + nb^2 \ge 2$$

is **squarefree**. There is then a datum of degree $`N`$, i.e. an isogeny of degree
$`N`$, and its kernel is a subgroup of $`E[N] \cong (\mathbb{Z}/N)^2`$ of order
$`N`$; since $`N`$ is squarefree, such a subgroup is necessarily **cyclic**. So
$`E/\ker \cong E`$, and the modular polynomial relation for the cyclic
$`N`$-isogeny gives

$$\Phi_N\left(j(E), j(E)\right) = 0 .$$

But $`\Phi_N`$ is monic in $`Y`$ of degree $`\psi(N)`$, and for $`N`$ not a square
the diagonal $`\Phi_N(X,X)`$ is a nonzero monic polynomial in $`X`$ with integer
coefficients. Hence $`j(E)`$ is an algebraic integer. Contrapositive: $`j`$ not an
algebraic integer forces $`\mathrm{End}`$ to be as small as possible.

This is the exact point where the Vélu spine (the existence and properties of
$`E/H`$) and the isogeny-data spine (the norm form) are used together: the argument
needs a squarefree value of the norm form, hence the classification, and it needs
$`\Phi_N(j(E),j(E)) = 0`$, hence Vélu.

### 4.7 Kernel rigidity

One more consequence is worth naming, because it is the shape in which the
classification is consumed:

> `WeierstrassCurve.zmultiples_eq_of_veluQuotient_j_eq_of_forall_pointEnd_eq_zsmul`
> ([Thm file, line 16](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_WeierstrassCurve_zmultiples_eq_of_veluQuotient_j_eq_of_forall_pointEnd_eq_zsmul.lean#L16-L35)):
> if every datum acts as an integer (no CM), and $`Q, Q'`$ both have odd order
> $`2n+1`$, and the Vélu quotients have equal nonzero discriminant and equal
> $`j`$-invariant, then $`\langle Q \rangle = \langle Q' \rangle`$.

Classically this is Silverman III.4.11–4.12: for a curve without complex
multiplication, a cyclic subgroup is determined by the isomorphism class of its
quotient. It is the rigidity step that makes $`\Phi_N(j(E),Y)`$ separable, hence the
precise input to `ModularPolynomialData.separable_map_eval2_of_not_isIntegral`
([Thm file, line 16](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularCurve_ModularPolynomialData_separable_map_eval2_of_not_isIntegral.lean#L16-L21)) and thence to the
multiplicity-one statement in §6.

## 5. The counting input: $`E[n] \cong (\mathbb{Z}/n)^2`$

Two statements the port promoted out of H5 deserve their own paragraph, because
they are the *quantitative* half of everything above.

> `WeierstrassCurve.nonempty_torsionBy_addEquiv_zmod_prod_of_isAlgClosed`
> ([Thm file, line 9](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_WeierstrassCurve_nonempty_torsionBy_addEquiv_zmod_prod_of_isAlgClosed.lean#L9-L12)):
> for $`W/F`$ elliptic, $`K`$ an algebraically closed $`F`$-algebra with
> $`(n : K) \ne 0`$, there is an additive isomorphism
> $`\mathbb{Z}/n \times \mathbb{Z}/n \cong W(K)[n]`$.

This is Silverman III.6.4(b): the existence of a *full level-$`n`$ structure*. It is
what makes "$`\#\{\text{cyclic subgroups of order } N\} = \psi(N)`$" meaningful, hence
what makes the degree of $`\Phi_N`$ in §3.2 the right number; and it is what makes a
squarefree-order subgroup of $`E[N]`$ cyclic in §4.6. Its proof splits into the
cardinality theorem $`\#E[d] = d^2`$ for all $`d \mid n`$
(`WeierstrassCurve.card_torsion_of_isAlgClosed`, already ported — see
[math/005](005-card-torsion-p-squared.md)) and a purely group-theoretic lemma
`AddCommGroup.nonempty_zmod_prod_addEquiv_torsionBy_of_card_torsionBy_eq_sq`, which
mathlib does not have.

> `WeierstrassCurve.Affine.Point.exists_zsmul_eq_of_isAlgClosed`
> ([Thm file, line 7](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_WeierstrassCurve_Affine_Point_exists_zsmul_eq_of_isAlgClosed.lean#L7-L9)):
> for $`K`$ algebraically closed and $`n \ne 0`$, multiplication by $`n`$ is
> surjective on $`E(K)`$.

$`E(K)`$ is a divisible group. The pin states it characteristic-free — no
$`[\mathrm{CharZero}\ K]`$ — because the proof is the geometric one: $`[n]`$ is a
non-constant morphism of curves, hence surjective. This is the statement used to
make the dual *unique* in §4.2, and it is on the shortest path to
`frey_no_cofixed_large` through the Weil-pairing route.

## 6. The consumers: how this reaches `fermat_last_theorem`

This is the part the four headlines were ported for. There are two roughly
independent routes, and they are the two halves of the FLT argument that are not
about modular forms.

### 6.1 The Mazur route: irreducibility of $`E_P[p]`$ for $`p \ge 17`$

The dependency chain — each arrow is a citation in the pin — is

```text
exists_dualEndData_dual_mem_and_norm_eq_finrankAlong
  -> exists_sq_lt_four_mul_and_forall_exists_finrankAlong_eq
  -> exists_forall_pointEnd_eq_zsmul_of_not_isIntegral_j
  -> ModularPolynomialData.separable_map_eval2_of_not_isIntegral
  -> ModularCurve.modularPolynomial_rootMultiplicity_jQuotVelu_eq_one
  -> ModularCurve.moduliPointExists_jQuotVelu_of_mult_two
  -> WeierstrassCurve.mazurStepThree_not_inZeroComponentAt
  -> FreyPackage.frey_no_cofixed_large
  -> FreyPackage.Mazur_Frey
  -> FreyPackage.no_frey_package
  -> FLT.fermatLastTheorem
```

(The other branch of the same chain goes through the additivity headline:
`exists_restrictAlong_placeOfPoint_eq_add` -> `exists_pointEnd_eq_add` ->
`exists_pointEnd_eq_of_mem_isogenyEndSubring` ->
`zmultiples_eq_of_veluQuotient_j_eq_of_forall_pointEnd_eq_zsmul`, and rejoins at the
separability statement.)

What is being used, in plain terms:

* **A rational $`p`$-torsion point produces a rational point of $`X_0(p)`$.** If
  $`Q \in W(\mathbb{Q})`$ has order $`p`$ (the Frey-curve situation of Mazur's step
  three), then the pair consisting of $`W`$ and $`\langle Q\rangle`$ is a moduli
  point, realised in the pin as a $`\mathrm{Gal}`$-stable place of
  `modularFunctionFieldBar p` where the two coordinate functions take the values
  $`c_4(W)^3/\Delta(W)`$ and $`c_4(V)^3/\Delta(V)`$, with $`V`$ the Vélu quotient of
  the base change along `oddOrderSummingSet Q ((p-1)/2)`. That is exactly the
  content of `ModularCurve.moduliPointExists_jQuotVelu_of_mult_two`
  ([Thm file, line 14](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularCurve_moduliPointExists_jQuotVelu_of_mult_two.lean#L14-L30)) — and it is
  the **explicit Vélu formulas** of §2 that make the second coordinate computable.

* **The fibre of $`X_0(p) \to X_0(1)`$ at $`j(W)`$ has a simple point there.** This
  is `modularPolynomial_rootMultiplicity_jQuotVelu_eq_one`
  ([Thm file, line 13](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularCurve_modularPolynomial_rootMultiplicity_jQuotVelu_eq_one.lean#L13-L27)): the
  $`j`$-invariant of the Vélu quotient is a **simple** root of
  $`\Phi_p(j(W), Y)`$, the multiplicative-reduction hypotheses at $`2`$ serving to
  exclude the extra endomorphisms that would produce a multiple root. Simple root
  here means exactly "no complex multiplication at this fibre", and that is
  purchased by §4.6 ($`j`$ not integral $`\Rightarrow`$ $`\mathrm{End} = \mathbb{Z}`$)
  plus §4.7 (kernel rigidity), which together give the separability of
  $`\Phi_p(j(W),Y)`$
  (`ModularPolynomialData.separable_map_eval2_of_not_isIntegral`).

* **Mazur's step three.** `mazurStepThree_not_inZeroComponentAt`
  ([Thm file, line 65](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_WeierstrassCurve_mazurStepThree_not_inZeroComponentAt.lean#L65)) is the per-prime
  local statement from Mazur, *Modular curves and the Eisenstein ideal*, III §5:
  a rational point of prime order $`p \notin \{2,3,5,7,13\}`$ that lies off the
  identity component at $`2`$ and $`3`$ lies off it at every prime of multiplicative
  reduction. The multiplicity-one input above is what the modular-curve side of
  that argument needs at the fibre over $`j(W)`$; the pin packages it as "a rational
  moduli place on $`X_0(p)`$ at a Vélu quotient".

That chain is the whole of the `frey_no_cofixed_large` input to PROOF-PATH.md
step 3 — the irreducibility of $`E_P[p]`$ for $`p \ge 17`$, the largest single part
of that step.

### 6.2 The Ribet route: level lowering

The second chain is

```text
velu_map_equation_of_oddOrderSummingSet_of_isAlgClosed
  -> exists_veluFunctionFieldHom_restrictAlong_placeOfPoint_eq_of_isAlgClosed
  -> WeierstrassCurve.exists_fullKernelHom
  -> ModularCurve.placeWidthChar_eq_one_of_restrictAlong_ne
  -> ...  (the ModularCurve width and Hecke-correspondence layer)
  -> ModularCurve.exists_width_comp_sp
  -> ModularCurve.nonempty_jZeroSemistableSpecialization
  -> WeierstrassCurve.isResiduallyModularOfLevel_div_of_isUnramifiedAt_sqf
  -> FreyPackage.level_lowering_odd_prime_of_conductorLevel
  -> FreyPackage.level_lowering_to_two
  -> FreyPackage.no_frey_package
```

Here the Vélu headline enters through `exists_fullKernelHom`
([Thm file, line 13](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_WeierstrassCurve_exists_fullKernelHom.lean#L13-L21)): for any $`Q`$ of order
$`N`$ with $`N`$ invertible, there is $`\varphi : E \to E/\langle Q\rangle`$ with
$`\ker\varphi = \langle Q\rangle`$ and the explicit coordinate formula of §2. The
rest of the chain computes, at the places of the modular curve over the relevant
primes, the **width** — the ramification/level data of the Hecke correspondence
`heckeAlphaC`/`heckeBetaC` — and the condition `placeWidthChar = 1` is exactly "the
isogeny is unramified there". That is the geometric input to Ribet's level-lowering
congruence, in the form PROOF-PATH.md describes as "an odd $`q \ne p`$ at which
$`E_P[p]`$ is unramified".

The other Vélu output on this route is the function-field model of $`X_0(N)`$:

* `WeierstrassCurve.exists_equiv_addSubgroup_isAddCyclic_isRoot_modularPolynomial_of_transcendental_j`
  and
  `ModularCurve.exists_equiv_algHom_modularFunctionFieldFullC_apply_jqN_eq_cyclicQuotientJ`
  — the function field of $`X_0(N)`$, generated over $`\mathbb{Q}`$ by $`j(q)`$ and
  $`j(q^N)`$, is the field generated by the $`j`$-invariants of cyclic quotients;
  embeddings of it correspond to cyclic subgroups;
* the whole `ModularCurve` / `CycSubRootBridge` / `XHDRModelAtP` layer that turns
  that into the moduli interpretation of $`X_0(N)`$ over $`\mathbb{Z}`$, the
  Atkin–Lehner action and the Hecke correspondences.

So the two spines are *not* redundant: the endomorphism-ring half serves
irreducibility, and the explicit-formula half serves level lowering. In the pin's
DAG they are nearly disjoint until the top, which is why the plan could factor the
91 k-line cluster into two columns at all.

### 6.3 The small uses

* `WeierstrassCurve.fifteenIsogenyClassification`
  ([Thm file, line 5](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_WeierstrassCurve_fifteenIsogenyClassification.lean)) is in
  the modularity half (PROOF-PATH.md step 4): if both $`\bar\rho_{W,3}`$ and
  $`\bar\rho_{W,5}`$ were reducible, $`W`$ would carry a rational $`15`$-isogeny, and
  $`c_4^3/\Delta`$ is forced to one of four values, none semistable. It is not on
  the chains above — it goes through the hauptmodul descriptions of $`X_0(3)`$ and
  $`X_0(5)`$ — but it speaks the same moduli language (rational cyclic subgroups,
  quotient $`j`$) and is the reason the "no rational torsion" inputs are available
  where modularity needs them.
* `WeierstrassCurve.Affine.Point.exists_zsmul_eq_of_isAlgClosed` is used by the
  Weil-pairing files that feed `frey_no_cofixed_large`
  (`WeierstrassCurve.Affine.eq_zero_of_forall_transEquiv_eq`,
  `WeierstrassCurve.exists_pairing_torsionBy`,
  `WeierstrassCurve.apply_eq_pow_det_galoisRep_of_pow_eq_one`), i.e. it is the
  divisibility statement behind the perfectness of the Weil pairing.
* `WeierstrassCurve.nonempty_torsionBy_addEquiv_zmod_prod_of_isAlgClosed` has 71
  consumers in the pin: the counts
  `natCard_addSubgroup_isAddCyclic_card_eq_dedekindPsi_of_isAlgClosed` (the number of
  cyclic subgroups is $`\psi(n)`$), the torsion-field constructions, the
  cyclic-subgroup counts stable under $`[i]`$ and $`[\omega]`$ used for the
  Eichler–Deuring supersingular counts, and the dual-end-data headline itself.

### 6.4 A caveat about the hypotheses

Every theorem above is stated under the gate binders
$`[\texttt{GenusOnePlaceGate}\ W]`$, $`[\texttt{GenusOnePlaceGate.IsCentred}\ W]`$,
$`[\texttt{AbelTheorem}\ W]`$, and the H5 headlines additionally assume
`hNs`, the norm formula for every datum. These are genuine mathematical hypotheses
(the place/divisor dictionary and Abel's theorem), not provable in the port; the
pin states them as typeclass parameters and the consumers instantiate them. So the
correct reading of the chain in §6.1 is *conditional on the genus-one place
interface*, exactly as the pin has it. §7 says what the port did with them.

## 7. The Lean and port picture

This section is deliberately short; the mathematics is above.

**The pin's shape.** Every statement is three layers: a ~14-line public
`Theorems/Thm_<stem>.lean` whose proof is
`p2m_exact_reverting @P2MW.S_<stem>.solution`; a proof body `P2M/Sol/S_<stem>.lean`
carrying every helper; and a small `Definitions/Def_*` module carrying the shared
vocabulary. The public interface is fixed — the cluster has ~401 consumers outside
the Deligne–Serre cone — so the port has freedom only in the *proof architecture*,
which is why the plan is a factoring plan
([studies/velu-cluster-structure.md](../studies/velu-cluster-structure.md) §4).

**What landed, and where.** The port's homes, from
[TOPIC-port-plan.md](../lean/topics/velu/TOPIC-port-plan.md) §5:

| home | port module(s) | what it carries |
|---|---|---|
| H1w | `WeierstrassCurve/Place/Dictionary.lean`, `AlgebraicCurve/Defs/PlaceCalculus.lean` | the deferred Weierstrass coordinate-ring place dictionary |
| H2 | `WeierstrassCurve/Velu/{Defs,Formula,Engine,Discharge,OddOrder}.lean` | the explicit-Vélu engine |
| H3 | `WeierstrassCurve/Velu/MapEquation.lean` | both `velu_map_equation_…{,_of_isAlgClosed}` headlines |
| H4 | `WeierstrassCurve/Velu/RestrictAlong.lean` | both `exists_veluFunctionFieldHom_restrictAlong_…{,_of_isAlgClosed}` headlines |
| H5a/H5b | `WeierstrassCurve/GenusOnePlaceGate.lean`, `Isogeny/ConditionalCurrency.lean`, `Isogeny/NatCard.lean` | the place gate, `IsogenyEndDatum`, and the kernel-cardinality bridge |
| H5 | `WeierstrassCurve/Isogeny/DualAPI.lean`, `IsogenyEndDatum/{Engine,RestrictAlongAdd,DualEndData,Vocabulary}.lean` | the dual and additivity headlines, the engine and the seam |
| H5-follow-up | `Algebra/ZModTorsion.lean`, `Elliptic/TorsionZMod.lean` | the promoted torsion statements of §5 |
| H6 | `WeierstrassCurve/Isogeny/BaseChange.lean` | **remaining**: the base-change/tensor column |

**The sibling rule.** Where the pin has a pair $`X`$ / `X_of_Y`, the port transcribes
the *general* member and derives the plain one as a corollary; the plain proof
bodies (12 k and 9.5 k lines) are not transcribed. For the Vélu column the general
member is the `_of_isAlgClosed` one, which is characteristic-free; the plain member
adds the hypothesis `(2 : L) ≠ 0`. For the H5 headlines the general member *is* the
plain one (there is no `_of_` sibling). The rule is not automatic: the plan's §3
records the one pair in the cluster (`natCard_…`) where the suffix hides a genuine
variant.

**Statement fidelity.** The port's checker (`lean/spec/check_flt_statements.py`)
diffs each ported declaration against the pin's statement with the checker's own
normalisation; the target is `0 mismatched / 0 missing`. Its one blind spot is
section `variable`s — a declaration can be "identical" textually while the
elaborated statement is stronger, so moved or ported declarations are probed with
`#check @name` against the pin's section. Axioms are
`[propext, Classical.choice, Quot.sound]`; there is no `sorry`.

**What is deferred.** Two H5 vocabulary nodes
(`exists_pointHom_comp_eq_of_ker_le_of_isCentred` and
`aeval_j_diag_eq_zero_of_finrankAlong_eq`) are deliberately deferred to Phase D on
large unported prerequisites, and H6 (the base-change column) remains. The plan's
remaining budget is 42 nodes / 26,674 net new lines; §5 of the plan lists what is
left.

**The port is fluid.** Module names, line counts and home assignments in the table
above are the port's current state, not a stable interface; the mathematical
statements and all line-number citations in this note are against the pin
`aa2d8b3`. Re-pin and re-measure before trusting a number.

## 8. What this note does not cover

* **The order-two quotient.** `veluQuotient2` and its `Delta_eq` / `cFour_eq` /
  `j` identities, and `exists_addMonoidHom_coe_eq_veluPointMap2`, are the
  characteristic-`2`-friendly twin of §2 and are a Phase B target of the plan.
* **The modular polynomial's construction.** `ModularPolynomialData` is taken as a
  datum here; how $`\Phi_N`$ is built from the $`q`$-expansion, its integrality and
  the level-one generation of the modular function field are
  [math/010](010-function-field-generation.md) and
  [base/006](../base/006-the-modular-equation.md).
* **The $`\ell`$-adic and Galois side.** The Tate module, the characteristic
  polynomial of Frobenius and $`\det\rho = \chi`$ are
  [math/011](011-tate-module.md); this note stays with the endomorphism ring over
  an algebraically closed field.
* **The Hecke/modular-curve machinery** that consumes the cyclic-quotient
  bijection: Hecke correspondences, Atkin–Lehner, the Eisenstein quotient. That is
  the subject of [math/009](009-hecke-jacobian-commute.md) and the `ModularCurve`
  layer of the pin; §6 only records the two entry points.
* **The base-change column (H6)** and the two deferred Phase D nodes.
* **The unconditional status of the gate hypotheses**: the pin does not prove
  `GenusOnePlaceGate` for a general curve, and neither does the port.

## Links

* [math/005 — the $`n`$-torsion of an elliptic curve has $`n^2`$ points](005-card-torsion-p-squared.md)
  — the cardinality theorem that §5 builds on.
* [math/009 — The Hecke action on the Jacobian](009-hecke-jacobian-commute.md) and
  [math/010 — Function field generation for $`X_0(N)`$](010-function-field-generation.md)
  — the modular-curve side that consumes §3.
* [math/011 — The Tate module](011-tate-module.md) — the Galois side of the
  endomorphism ring.
* [base/005 — Cyclic isogenies and congruence level](../base/005-cyclic-isogenies-and-level.md)
  and [base/006 — The modular equation](../base/006-the-modular-equation.md) —
  the classical background for §2 and §3.
* [studies/velu-cluster-structure.md](../studies/velu-cluster-structure.md) — the
  two spines of the cluster and the factoring method; §2.2 is the Vélu spine, §2.3
  the `IsogenyEndDatum` spine.
* [studies/elliptic-weierstrass-tate-scout.md](../studies/elliptic-weierstrass-tate-scout.md)
  — where the cluster was measured and ordered.
* [TOPIC-port-plan.md](../lean/topics/velu/TOPIC-port-plan.md),
  [TOPIC-H2-engine.md](../lean/topics/velu/TOPIC-H2-engine.md),
  [TOPIC-H5-engine.md](../lean/topics/velu/TOPIC-H5-engine.md),
  [TOPIC-torsion-promotion.md](../lean/topics/velu/TOPIC-torsion-promotion.md) —
  the port's operative plan, work orders and record.
* The pin at `aa2d8b3` (rendered links carry `#L` anchors; the raw files are the
  verbatim source):
  * [Thm_WeierstrassCurve_velu_map_equation_of_oddOrderSummingSet_of_isAlgClosed.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_WeierstrassCurve_velu_map_equation_of_oddOrderSummingSet_of_isAlgClosed.lean),
    [Thm_WeierstrassCurve_exists_veluFunctionFieldHom_restrictAlong_placeOfPoint_eq_of_isAlgClosed.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_WeierstrassCurve_exists_veluFunctionFieldHom_restrictAlong_placeOfPoint_eq_of_isAlgClosed.lean);
  * [Thm_WeierstrassCurve_Affine_IsogenyEndDatum_exists_dualEndData_dual_mem_and_norm_eq_finrankAlong.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_WeierstrassCurve_Affine_IsogenyEndDatum_exists_dualEndData_dual_mem_and_norm_eq_finrankAlong.lean),
    [Thm_WeierstrassCurve_Affine_IsogenyEndDatum_exists_restrictAlong_placeOfPoint_eq_add.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_WeierstrassCurve_Affine_IsogenyEndDatum_exists_restrictAlong_placeOfPoint_eq_add.lean),
    [Thm_WeierstrassCurve_Affine_FunctionField_addX_addY_specialize_at_place.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_WeierstrassCurve_Affine_FunctionField_addX_addY_specialize_at_place.lean);
  * [Thm_WeierstrassCurve_bijOn_cyclicQuotientJ_isRoot_modularPolynomial_of_transcendental_j.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_WeierstrassCurve_bijOn_cyclicQuotientJ_isRoot_modularPolynomial_of_transcendental_j.lean),
    [Thm_WeierstrassCurve_veluQuotient_oddOrderSummingSet_discriminant_prod_veluU_pow.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_WeierstrassCurve_veluQuotient_oddOrderSummingSet_discriminant_prod_veluU_pow.lean);
  * [Def_WeierstrassCurve_Velu.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_WeierstrassCurve_Velu.lean),
    [Def_WeierstrassCurve_VeluQuotientMap.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_WeierstrassCurve_VeluQuotientMap.lean),
    [Def_WeierstrassCurve_VeluPointMap.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_WeierstrassCurve_VeluPointMap.lean),
    [Def_WeierstrassCurve_OddOrderSummingSet.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_WeierstrassCurve_OddOrderSummingSet.lean);
  * [Def_DualIsogenyAPI.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_DualIsogenyAPI.lean),
    [Def_Isogeny_ConditionalCurrency.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_Isogeny_ConditionalCurrency.lean),
    [Def_AlgebraicCurve_Correspondence.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_Correspondence.lean),
    [Def_WeierstrassCurve_GenusOnePic0.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_WeierstrassCurve_GenusOnePic0.lean),
    [Def_ModularCurve_X0.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularCurve_X0.lean),
    [Def_WeierstrassCurve_CyclicQuotientJ.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_WeierstrassCurve_CyclicQuotientJ.lean).
* J. H. Silverman, *The Arithmetic of Elliptic Curves*, 2nd ed., GTM 106,
  Springer 2009 — III.4 (Vélu's formulas), III.6 (dual isogenies, torsion), III.9
  and Appendix C §11 (CM); and *Advanced Topics in the Arithmetic of Elliptic
  Curves*, GTM 151, Springer 1994, Chapter II (the norm form of a CM order).
* D. A. Cox, *Primes of the Form $`x^2 + ny^2`$: Fermat, Class Field Theory, and
  Complex Multiplication*, Wiley 1989, §11 — the norm-form/CM background of §4.5–§4.6.
* B. Mazur, *Modular curves and the Eisenstein ideal*, Publ. Math. IHÉS **47**
  (1977), 33–186 — III §5, step three.
