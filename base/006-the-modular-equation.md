# The modular equation: integrality and splitting

Sixth of the `base/` notes. [005](005-cyclic-isogenies-and-level.md) built the lattice
picture — tori $`E_\tau`$, their cyclic isogenies, and the quotient curves — and this note
builds the *modular polynomial* on top of it, supplying the classical language behind
[math/010 §3](../math/010-function-field-generation.md#3-the-modular-polynomial-and-the-roots-of-the-modular-equation).
That section rests on two facts about $`\Phi_N`$:

- **integrality**: there is a monic $`\Phi_N \in \mathbb{Z}[X,Y]`$, of degree
  $`\psi(N)`$ in $`Y`$, with $`\Phi_N(j(\tau), j(N\tau)) = 0`$;
- **splitting**: over a field containing a primitive $`p`$-th root of unity,
  $`\Phi_p`$ factors into linear factors whose roots are the $`j`$-invariants of the
  $`p+1`$ quotients of $`E_\tau`$ by its order-$`p`$ subgroups.

The definition and the splitting are where 005's quotient dictionary is consumed. The aim
here is to make sense of a sentence like

> "the root attached to $`(a,b)`$ is $`j(\zeta_M^{ab} q^{a^2})`$"

and of the surrounding words — *cusp*, *slot*, *coset*, *denominator-square* — that note 010
uses without pausing. We are **not** repeating the proof: the mathematics is the classical
one, the Lean fixes the order of the story, and it is quoted as a route map. §3 ends with
$`p = 3`$ carried out in full, and §4 computes $`\Phi_2`$ by hand as a test of whether
§§1–3 contain enough.

Line-number citations point at `anthropics/fermats-last-theorem@aa2d8b3`; mathlib
citations point at tag **v4.33.0**. Both are rendered GitHub links.

## 1. The modular polynomial

Fix $`N`$ and an elliptic curve $`E`$ with $`j(E) = X`$. Over $`X`$ sit the
$`\psi(N)`$ curves $`E/\mathcal{C}`$, one for each cyclic order-$`N`$ subgroup $`\mathcal{C} \le E`$. Put

$$\Phi_N(X, Y) \\;=\\; \prod_{\mathcal{C}} \bigl(Y - j(E/\mathcal{C})\bigr),$$

the product over the $`\psi(N)`$ cyclic subgroups. On notation: $`X`$ and $`Y`$ are the
*polynomial variables* of $`\Phi_N`$, while the classical names of the modular curves —
$`X(1)`$, $`Y(1)`$, $`X_0(N)`$ — always carry an argument or a subscript (005 §1,
[004 §5](004-the-j-invariant.md)); and $`\mathcal{C}`$ (script) is always a cyclic
subgroup, never the complex plane $`\mathbb{C}`$ (005 §2). This is the **modular polynomial**;
the equation $`\Phi_N(X,Y) = 0`$ is the **modular equation**, and its zero locus is
the image of the modular curve $`X_0(N)`$ in $`X(1) \times X(1)`$:

$$X_0(N) \\;\longrightarrow\\; X(1) \times X(1), \qquad (E, \mathcal{C}) \\;\longmapsto\\;
  \bigl(j(E),\\, j(E/\mathcal{C})\bigr).$$

Since $`E`$ is determined by $`X`$ up to isomorphism and the multiset
$`\{j(E/\mathcal{C})\}`$ depends only on the isomorphism class, the product is a function of
$`X`$: as a polynomial in $`Y`$,

$$\Phi_N(X,Y) \\;=\\; Y^{\psi(N)} - e_1(X)\\,Y^{\psi(N)-1} + \cdots + (-1)^{\psi(N)}e_{\psi(N)}(X),$$

where $`e_k`$ is the $`k`$-th elementary symmetric function of the $`\psi(N)`$
conjugate $`j`$-values. Three structural facts are the whole content of the
classical theory:

- **monic, of degree $`\psi(N)`$ in $`Y`$** — by construction, one linear factor per
  cyclic subgroup;
- **symmetric**: $`\Phi_N(X,Y) = \Phi_N(Y,X)`$ — by duality (005 §2), the Fricke
  involution $`w_N`$ exchanges $`E`$ and $`E/\mathcal{C}`$;
- **integral**: $`\Phi_N \in \mathbb{Z}[X,Y]`$ — this is the nontrivial one, §2.

Because $`\Phi_N(j(\tau), Y)`$ has exactly the $`\psi(N)`$ roots $`j(E_\tau/\mathcal{C})`$, and
because the cosets of $`\Gamma_0(N)`$ form a single Galois orbit (the cover
$`X_0(N) \to X(1)`$ is connected), $`\Phi_N`$ is the minimal polynomial of
$`j(N\tau)`$ over $`\mathbb{C}(j(\tau))`$ and is irreducible there. Its degree is the
degree of the cover:

$$[\mathbb{C}(j(\tau), j(N\tau)) : \mathbb{C}(j(\tau))] \\;=\\; \psi(N).$$

**Level one.** For $`N = 1`$ there is one subgroup, $`\Phi_1(X,Y) = X - Y`$; for
$`N = 2`$ there are three, and §4 computes them.

**A classical companion.** Reducing the integral polynomial modulo a prime $`p`$
gives *Kronecker's congruence*
$`\Phi_p(X,Y) \equiv (X^p - Y)(X - Y^p) \pmod p`$: in characteristic $`p`$ the
$`p+1`$ split roots collapse, because the Frobenius substitution $`q \mapsto q^p`$
turns the $`p`$ twisted roots into one. It is the arithmetic shadow of §3, and FLT
proves it as `ModularCurve.modularPolynomial_kronecker`.

## 2. Why the coefficients are integers

This is the part that is easy to state and easy to misjudge. The roots
$`j(E_\tau/\mathcal{C})`$ are *not* integers — they are transcendental complex numbers. What
is integral is their *symmetric* combination, and the reason is a small, completely
explicit argument with the $`q`$-expansion.

Write $`e_k(j(\tau))`$ for the $`k`$-th coefficient of $`\Phi_N(j(\tau),Y)`$ (up to
sign). Three inputs:

1. **Each conjugate has an algebraic-integer $`q`$-expansion.** The conjugates are
   the values $`j(\gamma\tau)`$ for coset representatives $`\gamma`$; in the nome they
   are $`j(\zeta_N^{\,ab} q^{a^2})`$ (§5). Since $`j(q) \in \mathbb{Z}((q))`$
   ([004 §4](004-the-j-invariant.md)) and $`\zeta_N^{\,ab}`$ is a root of unity,
   hence an algebraic integer, substitution $`q \mapsto \zeta q^e`$ returns
   $`q`$-coefficients in $`\mathbb{Z}[\zeta_N]`$: every conjugate has
   *algebraic-integer* $`q`$-coefficients. A symmetric polynomial in the conjugates,
   such as $`e_k`$, again has algebraic-integer $`q`$-coefficients, and it is fixed
   by the Galois action (which permutes the conjugates), so those coefficients lie
   in $`\mathbb{Q}`$. A rational algebraic integer is an integer, because
   $`\mathbb{Z}`$ is integrally closed in $`\mathbb{Q}`$. Hence every
   $`e_k(j(\tau))`$ has **ordinary integer** $`q`$-coefficients.
2. **Each $`e_k`$ is a polynomial in $`j`$.** It is symmetric in the conjugates, hence
   unchanged when the monodromy permutes the $`\psi(N)`$ points of the fibre of
   $`X_0(N) \to X(1)`$ (the covering-space picture of §3); it is holomorphic on
   $`\mathbb{H}`$ because each conjugate is; and its pole order at the cusp is finite and
   bounded by the classical bidegree of $`\Phi_N`$, namely $`\psi(N)`$. A weight-zero modular
   function that is holomorphic on $`\mathbb{H}`$ and has a pole of order $`\le
   \psi(N)`$ at the cusp is a polynomial in $`j`$ of degree $`\le \psi(N)`$ (this is
   the Hauptmodul property of 005 §1). So
   $`e_k = Q_k(j)`$ with $`Q_k \in \mathbb{C}[X]`$, $`\deg Q_k \le \psi(N)`$.
3. **Integral $`q`$-expansion forces integral coefficients.** A rational polynomial
   $`Q`$ with $`Q(j(q)) \in \mathbb{Z}((q))`$ must have $`Q \in \mathbb{Z}[X]`$.
   Indeed, if $`\deg Q = d`$ then
   $`j(q)^d = q^{-d}\,(1 + 744q + \cdots)`$ has leading term $`q^{-d}`$ with
   coefficient $`1`$, while $`j^k`$ for $`k \lt d`$ contributes nothing to
   $`q^{-d}`$. So the coefficient of $`q^{-d}`$ in $`Q(j(q))`$ is exactly the
   leading coefficient of $`Q`$; it is an integer, so that coefficient is an
   integer. Subtract it and repeat: every coefficient is an integer.

The mechanism in (3) is worth naming: $`j`$ has a **simple pole of residue $`1`** at
the cusp, so the deepest power of $`q`$ in a polynomial in $`j`$ reads off the
top coefficient of the polynomial. Combining (1)–(3),

$$\Phi_N \\;\in\\; \mathbb{Z}[X,Y], \qquad \text{monic in } Y,\\ \deg_Y = \psi(N),$$

and evaluating at $`X = j(\tau)`$, $`Y = j(N\tau)`$ (the $`\mathcal{C} = \langle 1/N\rangle`$
factor, or simply the defining identity) gives the relation

$$\Phi_N\bigl(j(\tau),\\, j(N\tau)\bigr) \\;=\\; 0 .$$

Equivalently: **$`j(N\tau)`$ is integral over $`\mathbb{Z}[j(\tau)]`$**, and
$`\mathbb{Z}[j, j(q^N)]`$ is a finite $`\mathbb{Z}[j]`$-algebra of rank $`\psi(N)`$.
This integral statement — not the explicit polynomial — is what note 010's
`exists_monic_evalAtJ_jqN_eq_zero` produces (by an induction over primes, from the
prime-level $`\Phi_p`$), and what
`exists_phiIrreducible_of_finrank_eq` then turns into an irreducible
`ModularPolynomialData` once the degree $`\psi(N)`$ is known.

## 3. Splitting of the modular equation, and the cover behind it

Let $`p`$ be prime. Reading 005 §2 with $`N = p`$ gives the factorization

$$\Phi_p\bigl(j(\tau),\\, Y\bigr) \\;=\\;
  \bigl(Y - j(p\tau)\bigr)\prod_{b=0}^{p-1}
  \Bigl(Y - j\bigl(\tfrac{\tau+b}{p}\bigr)\Bigr).$$

The right-hand side is a product of $`p+1`$ linear factors, one per cyclic
$`p`$-isogeny: the "extra" root $`j(p\tau)`$ (the line at infinity) and the $`p`$
roots $`j((\tau+b)/p)`$ (the finite-slope lines). This explicit list of roots is the
**splitting of the modular equation**. $`\Phi_p`$ is irreducible over
$`\mathbb{Q}(j)`$, so it does not factor there; the list says that its roots are
indexed by $`b \in \mathbb{Z}/p`$ and resolve into the $`p+1`$ linear factors above
once the fractional nome $`q^{1/p}`$ and the root of unity $`\zeta_p`$ that keeps
track of $`b`$ are available. In the specialization used by note 010 — evaluate
$`X`$ not at the generic $`j(\tau)`$ but at $`j(u^p q^{pe})`$ — both the point and
all the roots are honest Laurent series in $`q`$, and the identity is an equality in
$`K(\!(q)\!)`$ for any field $`K \ni \zeta_p`$.

**Group-theoretic reading.** The $`p+1`$ roots are the lines of
$`\mathbb{F}_p^2`$: one fixed line plus $`p`$ lines carrying the affine label
$`b \in \mathbb{F}_p`$. The labels are permuted by the units of $`\mathbb{F}_p`$,
which is how the cyclotomic field enters; concretely, the substitution
$`q^{1/p} \mapsto \zeta_p q^{1/p}`$ (multiply the nome by $`\zeta_p`$) fixes the
extra root $`j(q^{p^2})`$ and cycles $`j(\zeta_p^{\,b}q^{1/p})`$ through
$`b = 0,\dots,p-1`$. That is exactly the hypothesis of the irreducibility criterion
`Polynomial.irreducible_of_transitive_ringAut`: a monic polynomial that splits with
distinct roots, one root outside the base field and all the others cycled by a
base-field automorphism, is irreducible.

**Nome form, and the two fields.** With $`X = j(\tau)`$ the roots are the
$`j`$-values of 005 §2. Note 010 uses the same identity at the base point
$`\tau' = p\tau`$ — equivalently, after the substitution $`q \mapsto q^p`$ on the nome.
Two fields are then in play, and it pays to keep them apart. The abstract base field is
the rational function field $`\mathbb{Q}(j) \cong \mathrm{RatFunc}\,\mathbb{Q}`$;
concretely it is realized inside the ambient Laurent series ring $`\mathbb{Q}((q))`$ as
the subfield $`\mathbb{Q}(j(q^p))`$ generated by the single *series* $`j(q^p)`$. The
letter $`q`$ is not an element of that field — it is only the uniformizer of the ambient
ring — so the substitutions $`q \mapsto q^p`$ and $`q \mapsto \zeta_p^{\,b}q`$ act on
the ambient ring, not on $`Y(1)`$: they carry the base field *into* larger fields, which
is where the conjugates live. Writing $`q = e^{2\pi i\tau}`$ for the code's variable:

| object | classical | as a series in $`q`$ |
|---|---|---|
| base field | $`\mathbb{Q}(j(p\tau))`$ | $`\mathbb{Q}(j(q^p))`$ |
| the element, $`j(p\tau')`$ | $`j(p^2\tau)`$ | $`j(q^{p^2})`$ |
| the other $`p`$ conjugates, $`j((\tau'+b)/p)`$ | $`j(\tau + b/p)`$ | $`j(\zeta_p^{\,b}q)`$ |

Allowing an arbitrary level datum $`(e,u)`$ — the substitution
$`\tau \mapsto e\tau + \text{const}`$, i.e. $`q \mapsto u q^e`$ — gives the statement
in the exact shape quoted by note 010,

$$\Phi_p\bigl(j(u^p q^{pe}),\\, Y\bigr) \\;=\\;
  \bigl(Y - j(u^{p^2} q^{p^2 e})\bigr)
  \prod_{b=0}^{p-1}\bigl(Y - j(u\\,\zeta_p^{\\,b}\\,q^{e})\bigr),$$

which is Lean's `ModularCurve.PhiGen.splits_prime_at_slot`.

**The roots are distinct, and two coefficients show it.** In the prime case it takes only
two coefficients to see that different cosets give different $`j`$. The code's normal form
is `TS K e u`, which is $`j(uq^e)`$; then

* the coefficient of $`q^{-p^2}`$ is $`1`$ for $`j(q^{p^2})`$ and $`0`$ for every
  $`j(\zeta_p^{\,b}q)`$, so the line at infinity is separated by its pole *order*;
* the coefficient of $`q^{-1}`$ is $`\zeta_p^{-b}`$ for $`j(\zeta_p^{\,b}q)`$, so the
  $`p`$ finite-slope lines are separated by a single residue, distinct because
  $`\zeta_p`$ is primitive.

That is `TS_injective` for these slots, hence `roots_phiProd_conj_nodup`. For general
$`N`$ the same statement holds with the $`\psi(N)`$ slots $`\zeta_N^{\,ab}q^{a^2}`$,
$`ad = N`$ (`minpoly_jqN_map_eq_prod_slots`); the prime case above is the whole mechanism.

**Why this is the operative form.** The classical proof of the generation theorem
uses the Riemann surface $`X_0(N)`$: $`j`$ is a function of degree $`\psi(N)`$, and
the isogeny relation cuts the fibre down to one point. Without Riemann existence,
note 010 instead *lists all roots* and observes that exactly one can be common to
two polynomials. The splitting formula is what makes that list possible; the
"circuitousness" of the formal proof is the price of replacing the geometry by a
root count. The next two subsections describe that geometry — the cover, its monodromy,
and what it proves about algebraicity — so that §6's calculation can be read as the
constructive counterpart.

### The cover $`X_0(p) \to X(1)`$, monodromy, and why exactly two invariances

The group-theoretic reading above is a covering-space statement in disguise, and that
version explains why §6 checks the two symmetries it does.

**The cover.** For prime $`p`$ the affine curve $`\Phi_p(X,Y) = 0`$ is a model of
$`X_0(p)`$, and its projection to the $`X`$-line is the forgetful map
$`[E,L] \mapsto E`$, of degree $`p+1`$: the fibre over a generic $`[E]`$ is the set of
lines $`L \subset E[p]`$. The fibre coordinate is the quotient map
$$Y([E,L]) := j(E/L),$$
so the $`p+1`$ roots of $`\Phi_p(j(\tau),Y)`$ are exactly the values of $`Y`$ on that
fibre — 005 §2's dictionary in one line.

**Loops permute the fibre, not the base.** A loop in $`X(1)`$ that avoids the branch
points $`j = 0, 1728, \infty`$ lifts to a permutation of the $`p+1`$ points above the
base point — the monodromy
$`\pi_1\bigl(X(1) \smallsetminus \{0,1728,\infty\}\bigr) \to S_{p+1}`$. Composed with
$`Y`$ it permutes the roots and fixes $`X`$; so "an action permutes the roots" and "the
indeterminate $`Y`$ is untouched" are the same statement, and a coefficient of
$`\Phi_p`$, being a symmetric function of the roots, is fixed.

**The image is not all of $`S_{p+1}`$.** The cover is the quotient of the Galois cover
$`X(p) \to X(1)`$ (deck group $`\mathrm{PSL}_2(\mathbb{F}_p)`$, of degree
$`p(p^2-1)/2`$ for odd $`p`$) by the Borel, and the fibre is
$`\mathbb{P}^1(\mathbb{F}_p)`$; so the monodromy group is
$`\mathrm{PSL}_2(\mathbb{F}_p)`$ acting on the $`p+1`$ lines, by even permutations for
odd $`p`$. For $`p = 3`$ that is $`A_4 \subset S_4`$, of order $`12`$; for $`p = 2`$ it
is all of $`S_3`$ on three points.

**The local monodromies are the substitutions above.** Going once around the cusp
multiplies a $`p`$-th root of the base uniformizer by $`\zeta_p`$; in the normalization
above, where the base field is $`\mathbb{Q}(j(q^p))`$, that is exactly the twist
$`q \mapsto \zeta_p q`$ — the shift $`b \mapsto b+1`$, of order $`p`$, fixing the
infinity slot. Around $`j = 1728`$ and $`j = 0`$ one gets the local monodromies of order
dividing $`2`$ and $`3`$ attached to the elliptic points of $`X(1)`$; at the level of the
universal cover these two are the standard generators of
$`\mathrm{PSL}_2(\mathbb{Z}) = \mathbb{Z}/2 * \mathbb{Z}/3`$, and the three local
monodromies generate the monodromy group.

**Half of the symmetry is arithmetic, not topological.** The diamond
$`\zeta_p \mapsto \zeta_p^a`$ is not a loop: it is
$`\mathrm{Gal}(\mathbb{Q}(\zeta_p)/\mathbb{Q})`$ acting on the coefficients of the slots,
and it supplies the odd permutations — for $`p = 3`$,
$`r_1 \leftrightarrow r_2`$. Loops and diamond together generate
$`\mathrm{PGL}_2(\mathbb{F}_p)`$ ($`S_4`$, of order $`24`$, for $`p = 3`$), whereas the
subgroup fixing the distinguished root is the Borel of order $`p(p-1)`$ ($`6`$ for
$`p = 3`$, generated by shift and diamond). "The symmetries over the base" and "the
symmetries fixing the element" are therefore different groups, and §6 uses the second.

**Why those two invariances.** A coefficient of $`\Phi_p`$ is a single-valued function
on the base, that is a rational function of $`j`$, so the monodromy has to fix it. The
symmetry that must be checked is generated by the substitutions above, so proving a
coefficient fixed by the twist and by the diamond is what single-valuedness demands: the
twist kills the exponents outside $`p\mathbb{Z}`$, making the coefficient a
$`q \mapsto q^p`$ pullback, and the diamond makes it rational. Those are items (i) and
(iii) of §6 — and the reason the proof checks those two rather than all of
$`\mathrm{PGL}_2`$.

### What proves algebraicity of $`Y`$ over $`X`$

**Three inputs, and only one of them is symmetry.** That the roots are algebraic functions
of $`X`$ is a statement about a finite cover, and it is assembled from three separate
facts. *Finiteness*: the index $`[\mathrm{SL}_2(\mathbb{Z}) : \Gamma_0(p)] = p+1`$ gives
finite fibres, and compactifying the curves makes the map proper, so
$`\mathbb{C}(X_0(p))`$ is a finite extension of $`\mathbb{C}(j)`$; this is the step that
forbids a new transcendental generator, and it uses neither the roots nor monodromy.
*Single-valuedness*: monodromy permutes the sheets, so each elementary symmetric function
of the roots is unchanged along any loop, hence is a function of the base point rather
than a multivalued branch. *Growth*: monodromy says nothing about the cusps; one still has
to know that a coefficient is at worst polar at $`\infty`$ and at the elliptic points
before calling it rational in $`j`$, and that comes from the $`q`$-expansions (§6 step 3).
This produces coefficients in $`\mathbb{Q}(j)`$ — the existence of an equation. That the
coefficients are integers rather than merely rational functions of $`j`$ is §2's separate
arithmetic step.

**Symmetry predicts; with the roots in hand, calculation confirms.** The covering-space
argument is *predictive*: it produces a monic polynomial over the base without saying
which one, and in an abstract setting that existence is all one can ask for. Here the
roots are known before the polynomial is — they are the slot list above — so the existence
theory can be replaced by arithmetic. Write down the product
$$\prod_{b=0}^{p-1}\bigl(Y - j(\zeta_p^{\\,b}q)\bigr)\cdot\bigl(Y - j(q^{p^2})\bigr),$$
and check its coefficients directly: the twist permutes the factors, the
$`\zeta_p`$-action permutes them by $`b \mapsto ab`$, and a coefficient fixed by both is a
$`q^p`$ pullback with rational coefficients (items (i)–(ii) of §6 for the pullback, (iii)
for rationality). The symmetry that *predicted* algebraicity is exactly what makes the
check possible: it names the two substitutions a coefficient has to survive. What is left
is to identify the product with the minimal polynomial of $`j(q^{p^2})`$ over
$`\mathbb{Q}(j(q^p))`$, which is the degree and uniqueness step of §6. So the formal proof
never argues that an algebraic equation must exist — it writes the equation down, verifies
its coefficients, and matches it with the minimal polynomial: `phiProd`,
`exists_phiGenDescends`, and at general level `minpoly_jqN_map_eq_prod_slots`.

### $`p = 3`$, concretely: lines, quotients, roots, action

Everything in 005 and in §§1–3 of this note appears in one example — the cover and its
two symmetry substitutions included. Fix $`p = 3`$ and a generic $`\tau`$, and let
$`E_\tau = \mathbb{C}/\Lambda_\tau`$ with $`\Lambda_\tau = \mathbb{Z} + \mathbb{Z}\tau`$
be the base curve.

**Curve, torsion, lines (005 §§1–2).** $`E_\tau[3] = \frac13\Lambda_\tau/\Lambda_\tau`$
is $`(\mathbb{Z}/3)^2`$, with basis
$$e_1 = \frac13, \qquad e_2 = \frac{\tau}{3}.$$
Its four cyclic subgroups are the four lines
$$L_\infty = \langle e_1\rangle, \qquad
  L_b = \langle b\,e_1 + e_2\rangle
      = \Bigl\langle \frac{\tau+b}{3}\Bigr\rangle, \qquad b = 0,1,2,$$
one fixed line plus three carrying an affine label, as in 005 §2; their number is
$`\psi(3) = 1 + 3 = 4`$. The index contrast of 005 §2 is now numeric:
$`[\Lambda_\tau + \mathbb{Z}\frac13 : \Lambda_\tau] = 3`$ — this sum is $`L_\infty`$,
one of the four lines — whereas $`[\frac13\Lambda_\tau : \Lambda_\tau] = 9`$ is all of
$`E_\tau[3]`$. Both are lattices because $`\tau \notin \mathbb{R}`$: the directions
added to $`\Lambda_\tau`$ here are $`\frac13`$ and $`\frac{\tau+b}{3}`$, not an
irrational real number.

**Line → quotient → root (005 §2).** The root attached to a line is the
$`j`$-invariant of the quotient curve $`E_\tau/L`$:

| line $`L`$ | quotient lattice | $`j(E_\tau/L)`$ |
|---|---|---|
| $`L_\infty = \langle\frac13\rangle`$ | $`\mathbb{Z}\frac13 + \mathbb{Z}\tau`$, rescaled by $`3`$ to $`\mathbb{Z} + \mathbb{Z}\,3\tau`$ | $`j(3\tau)`$ |
| $`L_b = \langle\frac{\tau+b}{3}\rangle`$ | $`\Lambda_\tau + \mathbb{Z}\frac{\tau+b}{3} = \mathbb{Z} + \mathbb{Z}\frac{\tau+b}{3}`$ | $`j\bigl(\frac{\tau+b}{3}\bigr)`$ |

A point of $`X_0(3)`$ is a pair (curve, line): the base point $`j(\tau)`$ is the image
of the forgetful map $`(E,L) \mapsto E`$, and each root in the table is the image of
the quotient map $`(E,L) \mapsto E/L`$. By 005 §1 such a pair determines its quotient curve
only up to isomorphism, recorded by $`j`$; the canonical model of 005 §1 (`ofJ` in the
code) represents any of them, so no Weierstrass equation is needed here.

In the second row, $`\tau = 3\cdot\frac{\tau+b}{3} - b`$, so the lattice is already
presented on the basis $`\bigl(1, \frac{\tau+b}{3}\bigr)`$; in the first, rescaling a
lattice changes neither the curve nor $`j`$ (005 §1). So the roots of $`\Phi_3`$ at
$`X = j(\tau)`$ are exactly the four quotients of $`E_\tau`$ by its four order-$`3`$
subgroups:
$$\Phi_3\bigl(j(\tau), Y\bigr) = \bigl(Y - j(3\tau)\bigr)
  \prod_{b=0}^{2}\Bigl(Y - j\bigl(\tfrac{\tau+b}{3}\bigr)\Bigr).$$
No explicit $`\Phi_3`$ is needed: it has degree $`4 = \psi(3)`$ in each variable and
integer coefficients, by §§1–2. The roots are distinct for generic $`\tau`$,
separated as in the coefficient comparison above: in the variable
$`Q = q^{1/3} = e^{2\pi i\tau/3}`$ the root $`j(3\tau) = j(Q^9)`$ has a pole $`Q^{-9}`$,
while each $`j\bigl(\frac{\tau+b}{3}\bigr) = j(\zeta_3^{\,b}Q)`$ has a simple pole
$`Q^{-1}`$ with residue $`\zeta_3^{-b}`$.

**A matrix moves lines, hence roots.** Write $`r_\infty = j(3\tau)`$ and
$`r_b = j\bigl(\frac{\tau+b}{3}\bigr)`$. Modulo scalars,
$`\mathrm{GL}_2(\mathbb{F}_3)`$ acts on the four lines; since the roots are labelled by
the lines, every matrix permutes the roots by
$$g \cdot r(L) := r(gL).$$

| $`g`$ | on the four lines | on the four roots |
|---|---|---|
| `u = [[1,1],[0,1]]` | $`\infty \mapsto \infty`$, $`b \mapsto b+1`$ | $`r_0 \to r_1 \to r_2 \to r_0`$, $`r_\infty`$ fixed |
| `d = [[-1,0],[0,1]]` | $`\infty \mapsto \infty`$, $`b \mapsto -b`$ | $`r_1 \leftrightarrow r_2`$ |
| `w = [[0,-1],[1,0]]` | $`\infty \leftrightarrow 0`$, $`1 \leftrightarrow 2`$ | $`r_\infty \leftrightarrow r_0`$, $`r_1 \leftrightarrow r_2`$ |

Two of the computations: $`u`$ sends $`b\,e_1 + e_2`$ to
$`b\,e_1 + (e_1 + e_2) = (b+1)e_1 + e_2`$, so the label moves by $`+1`$; and $`w`$
sends it to $`-e_2 + b\,e_1 = e_1 - b\,e_2`$, the line of slope $`-1/b`$, which
exchanges $`\infty \leftrightarrow 0`$ and $`1 \leftrightarrow 2`$. This concerns the
labels only; which permutations are realized over a given base point is a separate
question.

**Which matrices act over the base.** On $`E_\tau`$ itself no line is distinguished, and
the element — the $`j`$-value of the curve itself, as opposed to its conjugates — is
$`r_\infty = j(3\tau)`$. Move the base one
level up, to the curve of $`j`$-value $`j(3\tau)`$ — note 010's base. That curve is
$`E_{3\tau}`$, whose $`3`$-torsion has basis $`\frac13`$ and $`\tau`$; its canonical
line $`\langle\frac13\rangle`$ gives the element $`j(9\tau)`$, and its other three
lines give $`j\bigl(\tau + \frac b3\bigr)`$, $`b = 0,1,2`$ — the slot list above. The
matrices fixing the canonical line, modulo scalars, form the Borel subgroup of order
$`p(p-1) = 6`$, generated by $`u`$ and $`d`$; it is exactly the subgroup of the
symmetries over this base that fixes the element $`j(9\tau)`$ (the full symmetry group
permutes all four roots):

- $`u`$ is the *shift* $`\tau \mapsto \tau + \frac13`$: it fixes $`j(3\tau)`$ because
  $`j(3\tau+1) = j(3\tau)`$, and on the nome it is $`q \mapsto \zeta_3 q`$ (the twist).
  It fixes the element $`j(9\tau)`$ and cycles the other three roots. This is `qTwist`.
- $`d`$ is the *diamond*, the constant-field automorphism
  $`\zeta_3 \mapsto \zeta_3^{-1}`$ (in a basis normalised by the Weil pairing, so its
  determinant is the cyclotomic character). It fixes $`j(9\tau)`$ and $`j(\tau)`$, and
  swaps $`j\bigl(\tau \pm \frac13\bigr)`$. This is the Galois step of the descent.
- $`w`$ swaps the canonical line with another, so it does not preserve the element
  $`j(9\tau)`$; it is a symmetry of the labelling only.

**Under the code's names.** `primCosetReps 3` is the four triples with $`ad = 3`$ and
the coprimality condition, $`(3,0,1), (1,0,3), (1,1,3), (1,2,3)`$; the value attached to
$`(a,b)`$ is $`\zeta_3^{\,ab}q^{a^2}`$, that is $`q^9, q, \zeta_3q, \zeta_3^2q`$;
`phiProd` is $`\prod (X - \text{value})`$ over these four, i.e.
$`(X - q)(X - \zeta_3q)(X - \zeta_3^2q)(X - q^9)`$; `TS K e u` is $`j(uq^e)`$, so
`TS K 9 1` is $`j(q^9)`$ and `TS K 1 ζ_3^b` is $`j(\zeta_3^{\,b}q)`$; `qExpand 3` is
$`q \mapsto q^3`$, and `cosetSubst` composes an expansion with a twist.

**The descent in this example.** The fourth factor $`(X - j(q^9))`$ has integral
coefficients and is fixed by both actions below, so only the three twist factors
matter. Their product is fixed by the twist $`q \mapsto \zeta_3q`$, which permutes the
three factors; hence every coefficient is a series in $`q^3`$, since only exponents
divisible by $`3`$ survive. It is also fixed by $`\zeta_3 \mapsto \zeta_3^{-1}`$, the
nontrivial automorphism of $`\mathbb{Q}(\zeta_3)`$, hence every coefficient is
rational. So every coefficient lies in $`\mathbb{Q}((q^3))`$, i.e. is the
$`q \mapsto q^3`$ pullback of a rational series — exactly the conclusion of
`exists_phiGenDescends` for $`p = 3`$.

## 4. A hand calculation: $`\Phi_2`$

Let us verify that §§1–3 determine the first nontrivial modular polynomial. Take
$`N = p = 2`$. The three order-$`2`$ subgroups of $`E_\tau`$ are generated by
$`1/2`$, $`\tau/2`$, $`(\tau+1)/2`$, so the roots of $`\Phi_2(j(\tau), Y)`$ are

$$r_1 = j(2\tau) = j(q^2), \qquad
  r_2 = j(\tau/2) = j(q^{1/2}), \qquad
  r_3 = j((\tau+1)/2) = j(-q^{1/2}),$$

where $`q = e^{2\pi i\tau}`$ and $`j(-q^{1/2})`$ means the substitution
$`q^{1/2} \mapsto -q^{1/2}`$. Write $`X = j(q)`$. Then

$$\Phi_2(X,Y) \\;=\\; (Y-r_1)(Y-r_2)(Y-r_3) \\;=\\;
  Y^3 - e_1 Y^2 + e_2 Y - e_3,$$

with $`e_1 = r_1+r_2+r_3`$, $`e_2 = r_1r_2+r_1r_3+r_2r_3`$ and
$`e_3 = r_1r_2r_3`$.

By §2 each $`e_k`$ is a polynomial in $`X`$; the pole orders at the cusp are
$`2, 2, 3`$, so $`\deg e_1, \deg e_2 \le 2`$ and $`\deg e_3 \le 3`$. The $`q`$-expansions
begin (using $`j(q) = q^{-1}+744+196884q+21493760q^2+\cdots`$):

$$r_1 = q^{-2} + 744 + 196884 q^2 + \cdots,$$

$$r_2 + r_3 = 1488 + 42987520\\,q + 40491712512\\,q^2 + \cdots,$$

$$r_2r_3 = -q^{-1} + 159768 + \cdots .$$

**Determining $`e_1`$.** Write $`e_1 = aX^2 + bX + c`$. Comparing the coefficients
of $`q^{-2}, q^{-1}, q^0`$:

- $`q^{-2}`$: $`e_1`$ has coefficient $`1`$ (from $`r_1`$), and $`X^2`$ has
  coefficient $`1`$, so $`a = 1`$;
- $`q^{-1}`$: $`e_1`$ has none, while $`X^2 = q^{-2}+1488q^{-1}+\cdots`$ and
  $`X = q^{-1}+\cdots`$, so $`0 = 1488 + b`$, i.e. $`b = -1488`$;
- $`q^0`$: $`e_1`$ has $`744 + 1488 = 2232`$, while $`X^2`$ has
  $`744^2 + 2\cdot196884 = 947304`$ and $`X`$ has $`744`$; hence
  $`c = 2232 - 947304 + 1488\cdot744 = 162000`$.

So

$$e_1 \\;=\\; X^2 - 1488\\,X + 162000 .$$

The same finite comparison (now using $`q^{-1}`$ and $`q^0`$ for $`e_2`$, and
$`q^{-3},\dots,q^0`$ for $`e_3`$) gives

$$e_2 = 1488\\,X^2 + 40773375\\,X + 8748000000,$$

$$e_3 = -X^3 + 162000\\,X^2 - 8748000000\\,X + 157464000000000 .$$

Therefore

$$\begin{aligned}
\Phi_2(X,Y) \\;=\\; & \\;X^3 + Y^3 - X^2Y^2 + 1488\\,(X^2Y + XY^2) \\\\
  & - 162000\\,(X^2 + Y^2) + 40773375\\,XY
    + 8748000000\\,(X + Y) - 157464000000000 .
\end{aligned}$$

This is the classical Kronecker modular polynomial for $`N = 2`$: symmetric in
$`X,Y`$ (visible in the display), monic of degree $`3 = \psi(2)`$ in each variable,
with integer coefficients. Two cheap checks. First, setting $`Y = X`$ singles out the
$`j`$-invariants with a self-$`2`$-isogeny: the quartic $`\Phi_2(X,X)`$ factors as
$`-(X-1728)(X-8000)(X+3375)^2`$, the class-number-one CM points of discriminant
$`-4, -8, -7`$. Second, the leading coefficient of $`e_3`$ is $`-1`$, matching
$`r_1r_2r_3 \sim q^{-2}\cdot(-q^{-1})`$.

One caveat when reading 005 §2's $`p+1`$ quotients as $`p+1`$ *curves*: they are $`p+1`$
quotient maps, and two distinct subgroups can have isomorphic targets — but only at CM
points. The double root above is the case $`X = -3375`$:
$`\Phi_2(-3375,Y) = (Y+3375)^2(Y-16581375)`$, so two of the three quotients are $`E`$
itself. Collisions happen off the diagonal too:
$`\Phi_2(1728,Y) = (Y-1728)(Y-287496)^2`$. The reason this needs CM: if
$`E_\tau/\mathcal{C} \cong E_\tau/\mathcal{C}'`$ for distinct subgroups, then the
composite $`E_\tau \to E_\tau/\mathcal{C} \cong E_\tau/\mathcal{C}' \to E_\tau`$ (last
arrow the dual isogeny) is an endomorphism of degree $`p^2`$ whose kernel is
$`\mathcal{C}`$, not all of $`E_\tau[p]`$, so it is not $`[\pm p]`$ — hence
$`\mathrm{End}(E_\tau)`$ is larger than $`\mathbb{Z}`$. For a non-CM $`E_\tau`$ the
$`p+1`$ targets are pairwise non-isomorphic.

The point of the computation is how little it needed: the quotient dictionary of 005 §2
(so that the three roots are known), the $`q`$-expansion of $`j`$ from
[004](004-the-j-invariant.md), the pole bound of §2 (so that finitely many
coefficients suffice), and integrality (so the coefficients are integers to be read
off). This is the classical route, and it is a fair test that §§1–3 are enough.

## 5. Reading note 010: a short dictionary

The following phrases in [math/010](../math/010-function-field-generation.md) are
the classical words of 005 and §§1–4. The label appearing in them is the upper-triangular
matrix

$$\gamma = \begin{pmatrix} a & b \\\\ 0 & d\end{pmatrix}, \qquad
  ad = M, \qquad 0 \le b \lt d,$$

of determinant $`M`$: an isogeny (Hecke) label, *not* an element of
$`\mathrm{SL}_2(\mathbb{Z})`$ unless $`M = 1`$. The two pieces of data are read off
its entries $`a`$ and $`b`$.

- **"level $`N`$", $`\Gamma_0(N)`$, $`X_0(N)`$.** $`X_0(N)`$ parametrizes pairs
  $`(E, \mathcal{C})`$ of an elliptic curve with a cyclic subgroup of order $`N`$; the map
  $`(E,\mathcal{C}) \mapsto E`$ is the cover $`X_0(N) \to X(1)`$ of degree $`\psi(N)`$. A
  "function of level $`N`$" is a function on $`X_0(N)`$. The point
  $`(E_\tau, \langle 1/N\rangle)`$ has the two $`j`$-coordinates
  $`j(\tau) = j(E_\tau)`$ and $`j(N\tau) = j(E_\tau/\langle 1/N\rangle)`$; these are
  the generators of note 010's theorem.
- **"degeneracy $`X_0(N) \to X(1)`$ and its intermediate levels".** For $`M \mid N`$
  there are forgetful maps $`X_0(N) \to X_0(M)`$ (forget part of the cyclic
  subgroup); note 010's generation theorem says the *function field* sees only the
  two ends, $`\mathbb{Q}(j, j(q^N)) = \mathbb{Q}(X_0(N))`$.
- **"denominator-square $`a^2`$".** The label $`\gamma`$ above acts by
  $`\tau \mapsto (a\tau+b)/d`$. With $`q_1 = e^{2\pi i\tau}`$,
  $`e^{2\pi i (a\tau+b)/d} = \zeta_M^{\,ab}\,q_1^{\,a/d}`$; over the common
  denominator $`M = ad`$ this is $`\zeta_M^{\,ab}\,q_1^{\,a^2/M}`$. So after the
  level-$`M`$ substitution $`q^M = q_1`$ the conjugate is
  $`j(\zeta_M^{\,ab}\,q^{a^2})`$: the exponent $`a^2`$ is the numerator $`a`$ of the
  fractional power $`a/d`$ written over the denominator $`M`$, and the twist
  $`\zeta_M^{\,ab}`$ is the numerator $`b`$. These are the "two pieces of coset data".
- **"right cosets of $`\Gamma_0(M)`$ in $`\mathrm{SL}_2(\mathbb{Z})`$".** Two
  $`\psi(M)`$-element sets are in play here, identified by the isogeny kernel but not
  by the same matrices. The cover $`X_0(M) \to X(1)`$ has fibre the right cosets
  $`\Gamma_0(M)\backslash\mathrm{SL}_2(\mathbb{Z})`$, of size the index $`\psi(M)`$,
  whose representatives are honest unimodular matrices (equivalently: the lines of
  $`(\mathbb{Z}/M)^2`$). The matrices $`\gamma`$ above have determinant $`M`$, so they
  are not among them; with $`\gcd(a,\gcd(b,d)) = 1`$ they are the standard labels of
  the $`\psi(M)`$ $`M`$-isogenies — the Hecke operator $`T_M`$'s representatives —
  which is what the root list of §3 uses, through $`\tau \mapsto (a\tau+b)/d`$. Same
  cardinality and the same $`j`$-values, different matrices. Note 010's slot set
  $`\{(a,b) : a \mid M,\ b \lt M/a,\ \gcd(\gcd(a,b), M/a) = 1\}`$ is exactly this
  label set.
- **"the affine self-map $`\tau \mapsto a^2\tau + ab`$".** This is the same coset
  data written on the level-$`M`$ nome: $`\zeta_M^{\,ab}q^{a^2}`$ is the nome of
  $`a^2\tau+ab`$ (for $`q = e^{2\pi i\tau/M}`$), which is the action of the
  Hecke/coset matrix in the $`q`$-world. For $`M = p`$ it degenerates to the two
  cases of §3: $`a = 1`$ gives the twists $`\zeta_p^{\,b}q`$, and $`a = p`$ gives
  $`q^{p^2}`$.
- **"Hauptmodul", "j separates points".** $`j`$ is a coordinate on
  $`X(1) = \mathbb{P}^1`$: two elliptic curves are isomorphic iff they have the same
  $`j`$ (005 §1). This is what lets a $`q`$-expansion computation be read back as a
  statement about curves.
- **"the extra isogeny relation cuts it down".** The fibre of $`X_0(N) \to X(1)`$
  over $`X`$ has $`\psi(N)`$ points $`j(E/\mathcal{C})`$, but only the one corresponding to
  $`\langle 1/N\rangle`$ satisfies the additional relation that $`E/\mathcal{C}`$ be
  $`N`$-isogenous to $`E`$ in the prescribed way. The splitting formula of §3 is the
  explicit form of that relation.

## 6. The Lean route as a map

The Lean does not *first* define $`\Phi_N`$ by the product over subgroups and then
check integrality. It goes the other way, and this order is worth knowing:

1. **Build the conjugate product.** The polynomial `phiProd` of
   [Def_ModularCurve_PhiGen.lean, lines 257–258](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularCurve_PhiGen.lean#L257-L258)
   is $`\prod_{b \lt p}\bigl(X - j(\zeta_p^{\,b}q)\bigr) \cdot \bigl(X - j(q^{p^2})\bigr)`$,
   written directly from the splitting list of §3.
2. **Descent, in three steps.** Each coefficient of the product must be shown to lie in
   the base, and the prime case uses one permutation and two invariances.
   (i) The twist $`q \mapsto \zeta_pq`$ fixes the infinity slot, since
   $`\zeta_p^{p^2} = 1`$, and cycles the other $`p`$ slots by $`b \mapsto b+1`$; a ring
   hom that permutes the factors fixes the product, so every coefficient is
   twist-invariant (`qTwist_phiProd_coeff`). (ii) A twist-invariant series has no terms
   outside $`p\mathbb{Z}`$, hence is a $`q \mapsto q^p`$ pullback
   (`coeff_eq_zero_of_qTwist_eq`, `mem_range_qExpand_of_qTwist_eq`). (iii) Independently,
   $`\sigma_a : \zeta_p \mapsto \zeta_p^a`$ permutes the slots by $`b \mapsto ab`$, so
   every coefficient is Galois-fixed, hence rational
   (`exists_galoisPerm`, `mem_range_coeffEmb_of_forall_coeffMap_eq`). A coefficient that
   is both a $`q^p`$ pullback and rational is `coeffEmb K (qExpand ℚ p (c k))` for a
   rational $`c`$ (`mem_range_coeffEmb_qExpand_of_mem_inter`) — that is
   `PhiGen.exists_phiGenDescends`
   ([S file, lines 278–297](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_PhiGen_exists_phiGenDescends.lean#L278-L297)).
   Neither invariance suffices alone — the twist leaves coefficients in $`K((q^p))`$,
   Galois leaves them in $`\mathbb{Q}((q))`$ — and "in the base" means "a
   $`q \mapsto q^p`$ pullback" precisely because the base is $`\mathbb{Q}(j(q^p))`$
   (the table in §3). The cover picture in §3 says why these are the right two
   symmetries: the twist is the local monodromy at the cusp, the diamond is the
   arithmetic action on the coefficients.
3. **Pole bound.** The product's pole order at the cusp bounds the degree, which
   together with holomorphy makes each coefficient a *polynomial* in $`j(q)`$
   rather than a rational function; and the residue-$`1`$ pole of $`j`$ converts
   integral $`q`$-coefficients into integral polynomial coefficients (§2). This is
   `exists_modularPolynomialData_coeff_eq`
   ([S file, lines 130–177](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_PhiGen_exists_modularPolynomialData_coeff_eq.lean#L130-L177)).
4. **Uniqueness.** Both the given datum and the constructed one are monic of degree
   $`p+1`$ and annihilate the same element, which has degree $`p+1`$ over the base
   (§3's table records the element and the base in both notations); so they are equal.
   This identifies the product with
   $`\Phi_p`$ — the step that the phrase "the product's own coefficient family is a
   valid modular polynomial datum, hence is *the* datum" abbreviates.
5. **General $`N`$.** Integrality at level $`N`$ follows from the prime case by an
   induction over primes (`exists_monic_evalAtJ_jqN_eq_zero`), and irreducibility /
   degree $`\psi(N)`$ from the minimal polynomial once the degree is known
   (`exists_phiIrreducible_of_finrank_eq`). The slot description
   `minpoly_jqN_map_eq_prod_slots` is the same splitting list iterated over the
   divisor lattice, and is what note 010's §4 descent consumes.

Two features of 005 §2's picture have no counterpart in the code, which is worth knowing
before reading it. There is no $`\mathbb{C}/\Lambda_\tau`$ model, and no quantification
over generators of $`\mathcal{C}`$: the count $`p+1`$ enters as $`\psi`$, through an
abstract group statement — for any additive group whose $`n`$-torsion is additively
equivalent to $`\mathbb{Z}/n \times \mathbb{Z}/n`$, the cyclic subgroups of order
$`n`$ number $`\psi(n)`$
(`AddCommGroup.natCard_isAddCyclic_addSubgroup_eq_dedekindPsi_of_addEquiv_torsionBy`,
proved for the model group and transported) — while the conjugates are indexed by the
canonical list `primCosetReps M` of triples $`(a,b,d)`$ with $`ad = M`$,
$`b \lt d`$, $`\gcd(a,\gcd(b,d)) = 1`$: one representative per coset. For prime
$`\ell`$ the index type is literally `Fin (ℓ + 1)`, slot $`0`$ being the
$`q^{\ell^2}`$ one and slot $`b+1`$ the twist $`\zeta_\ell^{\,b}q`$. So neither
choosing a generator nor reducing one modulo $`M`$ is a step the proof performs: the
normalization $`\zeta_M^{\,ab}q^{a^2}`$ is built into the indexing.

## 7. Key point → declaration map

| Mathematics | Lean declaration | Location |
|---|---|---|
| monic $`\Phi_N \in \mathbb{Z}[X][Y]`$, $`\deg_Y = \psi(N)`$, $`\Phi_N(j,j_N)=0`$ | `ModularPolynomialData` | [X0 215–223](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularCurve_X0.lean#L215-L223) |
| $`j(q^N)`$ integral over $`\mathbb{Z}[j(q)]`$ | `exists_monic_evalAtJ_jqN_eq_zero` | [Thm 8](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularCurve_exists_monic_evalAtJ_jqN_eq_zero.lean#L8) |
| degree $`\psi(N)`$ ⟹ irreducible $`\Phi_N`$ | `exists_phiIrreducible_of_finrank_eq` | [Thm 9](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularCurve_exists_phiIrreducible_of_finrank_eq.lean#L9) |
| prime splitting of $`\Phi_p`$ | `PhiGen.splits_prime_at_slot` | [Thm 10](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularCurve_PhiGen_splits_prime_at_slot.lean#L10) |
| conjugates of $`j(q^M)`$ by coset slots | `minpoly_jqN_map_eq_prod_slots` | [Thm 8](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularCurve_minpoly_jqN_map_eq_prod_slots.lean#L8) |
| $`\psi(M) = [\mathrm{SL}_2(\mathbb{Z}):\Gamma_0(M)]`$ | `ModularCurve.Gamma0_index` | [Thm 10](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularCurve_Gamma0_index.lean#L10) |
| $`\psi(M)`$ slots = coset representatives | `card_primCosetReps_eq_dedekindPsi` | [Thm 8](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularCurve_card_primCosetReps_eq_dedekindPsi.lean#L8) |
| transitive automorphism ⟹ irreducible | `Polynomial.irreducible_of_transitive_ringAut` | [Thm 5](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_Polynomial_irreducible_of_transitive_ringAut.lean#L5) |
| Kronecker congruence $`\Phi_p \equiv (X^p-Y)(X-Y^p) \bmod p`$ | `modularPolynomial_kronecker` | [Thm 9](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularCurve_modularPolynomial_kronecker.lean#L9) |
| $`\Phi_p`$ from the conjugate product | `PhiGen.exists_phiGenDescends` | [S 278–297](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_PhiGen_exists_phiGenDescends.lean#L278-L297) |
| weight-zero invariant $`q`$-series is a polynomial in $`j`$ | `mem_adjoin_jq_of_hasSum_of_slash_invariant` | [Thm 9](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularCurve_mem_adjoin_jq_of_hasSum_of_slash_invariant.lean#L9) |
| weight-zero modular form is constant | `ModularForm.eq_const_of_weight_zero` | [mathlib 164](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/NumberTheory/ModularForms/NormTrace.lean#L164) |

## 8. Links

FLT sources at the pinned sha `aa2d8b3`:

- [Def_ModularCurve_X0.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularCurve_X0.lean) — `jq`, `jqN`, `qExpand`, `dedekindPsi`, `ModularPolynomialData`
- [Def_ModularCurve_PhiGen.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularCurve_PhiGen.lean) — `qTwist`, `cosetSubst`, `conj`, `phiProd`, `EvalSymm`, `IntCoeffs`
- [Thm_ModularCurve_PhiGen_splits_prime_at_slot.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularCurve_PhiGen_splits_prime_at_slot.lean) — the splitting formula
- [Thm_ModularCurve_minpoly_jqN_map_eq_prod_slots.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularCurve_minpoly_jqN_map_eq_prod_slots.lean) — the conjugate list
- [P2M/Sol/S_ModularCurve_PhiGen_exists_phiGenDescends.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_PhiGen_exists_phiGenDescends.lean) — the descent of the conjugate product
- [Theorems/Thm_ModularCurve_exists_monic_evalAtJ_jqN_eq_zero.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularCurve_exists_monic_evalAtJ_jqN_eq_zero.lean) — integrality

Companion notes:

- [004 — The j-invariant](004-the-j-invariant.md) — the series `jq` and its integral $`q`$-expansion
- [005 — Cyclic isogenies, congruence level, and the $`j`$-invariant](005-cyclic-isogenies-and-level.md) — the lattice and quotient dictionary used in §1 and §3
- [math/010 §3](../math/010-function-field-generation.md#3-the-modular-polynomial-and-the-roots-of-the-modular-equation) — the section this note supplements
- [math/009 — The Hecke action on the Jacobian](../math/009-hecke-jacobian-commute.md) — where the modular polynomial is consumed

Background:

- F. Diamond and J. Shurman, *A First Course in Modular Forms*, GTM 228, Springer 2005, §5.2 — the modular equation and the function field of $`X_0(N)`$.
- S. Lang, *Elliptic Functions*, 2nd ed., GTM 112, Springer 1987, Ch. 5, §§2–3 — the modular equation and its roots.
