# The modular equation: isogenies, integrality, and splitting

Fifth of the `base/` notes. [004](004-the-j-invariant.md) built the `j`-invariant and
its `q`-expansion; this note supplies the classical language behind
[math/010 §3](../math/010-function-field-generation.md#3-the-modular-polynomial-and-the-roots-of-the-modular-equation).
That section rests on two facts about the *modular polynomial* $`\Phi_N`$:

- **integrality**: there is a monic $`\Phi_N \in \mathbb{Z}[X,Y]`$, of degree
  $`\psi(N)` in $`Y`$, with $`\Phi_N(j(\tau), j(N\tau)) = 0`$;
- **splitting**: over a field containing a primitive $`p`$-th root of unity,
  $`\Phi_p`$ factors into linear factors whose roots are the $`j`$-invariants of the
  $`p+1`$ quotients of $`E_\tau`$ by its order-$`p`$ subgroups.

The aim is to make sense of a sentence like

> "the $`p+1`$ cyclic $`p`$-isogenies out of $`E_\tau`$ have quotients
> $`E_{p\tau}`$ and $`E_{(\tau+b)/p}`$"

and of the surrounding words — *level*, *cusp*, *coset*, *slot*, *Hauptmodul* — that
note 010 uses without pausing. We are **not** repeating the proof. The mathematics is
the classical one; the Lean fixes the order of the story and is quoted as a route map.
§6 computes $`\Phi_2`$ by hand, as a test of whether §§1–5 contain enough.

Line-number citations point at `anthropics/fermats-last-theorem@aa2d8b3`; mathlib
citations point at tag **v4.33.0**. Both are rendered GitHub links.

## 1. The torus $`E_\tau`$, and what $`j`$ classifies

Fix $`\tau`$ in the upper half plane $`\mathbb{H}`$ and let

$$\Lambda_\tau \\;=\\; \mathbb{Z} + \mathbb{Z}\tau \\;\subset\\; \mathbb{C}, \qquad
  E_\tau \\;=\\; \mathbb{C}/\Lambda_\tau .$$

$`E_\tau`$ is a *complex torus*: a compact Riemann surface which is also a group,
with origin the class of $`0`$. That group structure is what makes it an **elliptic
curve**, and it is why the letter $`E`$ appears throughout note 010 — $`E_\tau`$ is
the elliptic curve whose periods are $`1`$ and $`\tau`$. (Every elliptic curve over
$`\mathbb{C}`$ is of this form; this is the uniformization theorem, and it is the
reason a curve is never far away from an explicit lattice computation.)

**Isomorphism.** The lattice $`\Lambda_\tau`$ depends on the *choice of basis*
$`(1,\tau)`$. Changing the basis by $`\gamma \in \mathrm{SL}_2(\mathbb{Z})`$
replaces $`\tau`$ by $`\gamma\tau = \frac{a\tau+b}{c\tau+d}`$ (here $`a,b,c,d`$ are
the entries of $`\gamma`$), and $`\Lambda_{\gamma\tau}`$ is homothetic
to $`\Lambda_\tau`$; conversely, homothetic lattices give isomorphic tori. So

$$E_\tau \\;\cong\\; E_{\tau'} \quad\Longleftrightarrow\quad
  \tau' = \gamma\tau \\ \text{ for some } \gamma \in \mathrm{SL}_2(\mathbb{Z}).$$

**Moduli.** There is a single function that sees the isomorphism class and nothing
else, the $`j`$-invariant of [004](004-the-j-invariant.md):

$$j(\gamma\tau) = j(\tau), \qquad
  j : \mathrm{SL}_2(\mathbb{Z})\backslash\mathbb{H} \\;\xrightarrow{\\ \sim\\ }\\; \mathbb{C}.$$

The quotient $`Y(1) = \mathrm{SL}_2(\mathbb{Z})\backslash\mathbb{H}`$ is the *moduli
space of elliptic curves*; adding the cusp gives $`X(1) \cong \mathbb{P}^1`$, and
$`j`$ is its *Hauptmodul* — the coordinate, "the function that ranges over moduli".
This gives the three levels at which the same object is described:

| level | object | meaning |
|---|---|---|
| local / marked | $`\tau \in \mathbb{H}`$ | a lattice with a chosen basis $`(1,\tau)`$ |
| global / unmarked | $`E_\tau`$, the class of $`\tau`$ | an elliptic curve up to isomorphism |
| coordinate | $`j(\tau) \in \mathbb{C}`$ | the point of the moduli space it occupies |

"$`E_\tau`$ is a point of the moduli space that $`j`$ ranges over" means exactly
this: as $`\tau`$ varies, $`E_\tau`$ sweeps out the moduli space, and $`j(\tau)`$ is
the coordinate of the swept point. The local coordinate at the cusp,
$`q = e^{2\pi i\tau}`$, is the bridge to the $`q`$-expansions that FLT actually
computes with; the substitution $`\tau \mapsto \gamma\tau`$ becomes the formal,
"slot"-indexed substitution $`q \mapsto \zeta_M^{\,ab} q^{a^2}`$ of §7.

## 2. Subgroups, quotients, cyclic isogenies: why $`p+1`$

On $`E_\tau = \mathbb{C}/\Lambda_\tau`$ the group law is inherited from $`\mathbb{C}`$.
The $`N`$-torsion is

$$E_\tau[N] \\;=\\; \tfrac{1}{N}\Lambda_\tau \big/ \Lambda_\tau
  \\;\cong\\; (\mathbb{Z}/N)^2 .$$

For $`p`$ prime this is a two-dimensional vector space over $`\mathbb{F}_p`$.
Let $`E' = \mathbb{C}/\Lambda'`$ be another complex torus — again an elliptic curve
$`E_{\tau'}`$ for some $`\tau'`$ (so $`E'`$ is the *target*, and it is not fixed in
advance). A **cyclic $`p`$-isogeny out of $`E_\tau`$** is a surjective homomorphism
of complex tori

$$\phi : E_\tau \\;\longrightarrow\\; E',$$

whose kernel is finite of order $`p`$; the target $`E'`$ is the **quotient**. Since
$`p`$ is prime, that kernel is a subgroup of order $`p`$,

$$\mathcal{C} \\;=\\; \langle (m + n\tau)/p \rangle \\;\le\\; E_\tau[p]
  \qquad (m, n \in \mathbb{Z}),$$

where $`\langle x\rangle`$ is the cyclic subgroup *generated by* the single element
$`x`$: the pair $`(m,n)`$ gives the one generator, so $`\mathcal{C}`$ has $`p`$ elements
inside the $`p^2`$-element group $`E_\tau[p]`$, and it is not all of $`E_\tau[p]`$.
Only $`(m,n)`$ modulo $`p`$ matters, so we may take $`0 \le m,n \le p-1`$ with
$`(m,n) \ne (0,0)`$; and multiplying $`(m,n)`$ by a nonzero scalar modulo $`p`$ gives
the same $`\mathcal{C}`$ — the scalar ambiguity for which the subgroups are the
"lines" counted below.
Different generators of the same $`\mathcal{C}`$ give the *same* lattice
$`\Lambda_\tau + \mathbb{Z}(m+n\tau)/p`$, hence the same curve: another generator is
$`k(m+n\tau)/p`$ with $`k`$ a unit modulo $`p`$, and $`ak + bp = 1`$ shows that each
generator lies in the lattice generated by the other together with
$`\Lambda_\tau`$ (using $`p(m+n\tau)/p = m+n\tau \in \Lambda_\tau`$).
$`\phi`$ is the quotient map $`E_\tau \to E_\tau/\mathcal{C}`$, so
$`E' \cong E_\tau/\mathcal{C}`$ is determined by $`\mathcal{C}`$ up to isomorphism.
Conversely every order-$`p`$ subgroup $`\mathcal{C}`$ gives such a quotient, and
$`E_\tau/\mathcal{C}`$ is again a complex torus (a lattice quotient), hence again an
elliptic curve. So the three languages

> cyclic $`p`$-isogeny out of $`E_\tau`$ $`\;\longleftrightarrow\;`$
> order-$`p`$ subgroup $`\mathcal{C} \le E_\tau`$ $`\;\longleftrightarrow\;`$
> quotient $`E_\tau/\mathcal{C}`$

name the same thing. Counting them: $`E_\tau[p]`$ has $`p^2-1`$ nonzero elements,
each order-$`p`$ subgroup contains $`p-1`$ of them, so

$$\\#\\{\text{order-}p\text{ subgroups}\\} \\;=\\; \frac{p^2-1}{p-1} \\;=\\; p+1 .$$

Equivalently, the subgroups are the **lines** of the $`\mathbb{F}_p`$-plane
$`E_\tau[p]`$, of which there are $`p+1`$.

**The quotients, explicitly.** Computing the quotient lattice turns the $`p+1`$ lines
into $`p+1`$ curves of the same shape $`E_{\tau'}`$:

- the line $`n = 0`$, i.e. $`\mathcal{C} = \langle 1/p\rangle`$:
  $`\Lambda_\tau + \tfrac1p\mathbb{Z} = \tfrac1p(\mathbb{Z} + p\tau\mathbb{Z})`$, so
  the quotient is $`E_{p\tau}`$;
- the $`p`$ lines $`n \ne 0`$, normalized to $`\mathcal{C} = \langle(\tau+b)/p\rangle`$ with
  $`b \in \mathbb{F}_p`$: the quotient lattice is
  $`\mathbb{Z} + \tfrac{\tau+b}{p}\mathbb{Z}`$, so the quotient is
  $`E_{(\tau+b)/p}`$.

Thus the quoted sentence is a complete list:

$$E_\tau/\mathcal{C} \\;\in\\; \bigl\\{\\, E_{p\tau} \\,\bigr\\} \\;\cup\\;
  \bigl\\{\\, E_{(\tau+b)/p} \\;:\\; b = 0,1,\dots,p-1 \\,\bigr\\}.$$

The one curve $`E_{p\tau}`$ is the "line at infinity"; the other $`p`$ are indexed by
the slope $`b`$. In the nome $`q = e^{2\pi i\tau}`$ they read

$$j(p\tau) = j(q^p), \qquad
  j\\!\left(\tfrac{\tau+b}{p}\right) = j\\!\left(\zeta_p^{\\,b}\\,q^{1/p}\right),
  \qquad \zeta_p = e^{2\pi i/p},$$

which is where fractional powers of $`q`$ — and the roots of unity of the splitting
formula — first appear.

**Duality.** The quotient map $`E_\tau \to E_\tau/\mathcal{C}`$ has a dual isogeny
$`E_\tau/\mathcal{C} \to E_\tau`$, of the same degree, whose kernel is the dual subgroup. So
"being $`p`$-isogenous" is a symmetric relation; this is the source of the symmetry
$`\Phi_p(X,Y) = \Phi_p(Y,X)`$ below.

**General level.** Replacing "order $`p`$" by "cyclic of order $`N`$" gives the same
story with $`\psi(N)`$ in place of $`p+1`$. The number of cyclic order-$`N`$
subgroups of $`(\mathbb{Z}/N)^2`$ is the Dedekind function

$$\psi(N) \\;=\\; \sum_{\substack{d \mid N \\\\ d\\ \text{squarefree}}} \frac{N}{d}
  \\;=\\; N \prod_{p \mid N}\Bigl(1 + \frac1p\Bigr),$$

the index $`[\mathrm{SL}_2(\mathbb{Z}) : \Gamma_0(N)]`$. For $`N = p`$ this is
$`p+1`$, and the $`p+1`$ subgroups above are the first case.

## 3. The modular polynomial

Fix $`N`$ and an elliptic curve $`E`$ with $`j(E) = X`$. Over $`X`$ sit the
$`\psi(N)`$ curves $`E/\mathcal{C}`$, one for each cyclic order-$`N`$ subgroup $`\mathcal{C} \le E`$. Put

$$\Phi_N(X, Y) \\;=\\; \prod_{\mathcal{C}} \bigl(Y - j(E/\mathcal{C})\bigr),$$

the product over the $`\psi(N)`$ cyclic subgroups. Two conventions, to keep the two
roles of each letter apart. $`X`$ and $`Y`$ are the *polynomial variables* of
$`\Phi_N`$, while the classical names of the modular curves — $`X(1)`$, $`Y(1)`$,
$`X_0(N)`$ — always carry an argument or a subscript (§1, [004 §5](004-the-j-invariant.md)).
And $`\mathcal{C}`$ (script) is always a cyclic subgroup, never the complex plane
$`\mathbb{C}`$ (§2). This is the **modular polynomial**;
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
- **symmetric**: $`\Phi_N(X,Y) = \Phi_N(Y,X)`$ — by duality (§2), the Fricke
  involution $`w_N`$ exchanges $`E`$ and $`E/\mathcal{C}`$;
- **integral**: $`\Phi_N \in \mathbb{Z}[X,Y]`$ — this is the nontrivial one, §4.

Because $`\Phi_N(j(\tau), Y)`$ has exactly the $`\psi(N)`$ roots $`j(E_\tau/\mathcal{C})`$, and
because the cosets of $`\Gamma_0(N)`$ form a single Galois orbit (the cover
$`X_0(N) \to X(1)`$ is connected), $`\Phi_N`$ is the minimal polynomial of
$`j(N\tau)`$ over $`\mathbb{C}(j(\tau))`$ and is irreducible there. Its degree is the
degree of the cover:

$$[\mathbb{C}(j(\tau), j(N\tau)) : \mathbb{C}(j(\tau))] \\;=\\; \psi(N).$$

**Level one.** For $`N = 1`$ there is one subgroup, $`\Phi_1(X,Y) = X - Y`$; for
$`N = 2`$ there are three, and §6 computes them.

**A classical companion.** Reducing the integral polynomial modulo a prime $`p`$
gives *Kronecker's congruence*
$`\Phi_p(X,Y) \equiv (X^p - Y)(X - Y^p) \pmod p`$: in characteristic $`p`$ the
$`p+1`$ split roots collapse, because the Frobenius substitution $`q \mapsto q^p`$
turns the $`p`$ twisted roots into one. It is the arithmetic shadow of §5, and FLT
proves it as `ModularCurve.modularPolynomial_kronecker`.

## 4. Why the coefficients are integers

This is the part that is easy to state and easy to misjudge. The roots
$`j(E_\tau/\mathcal{C})`$ are *not* integers — they are transcendental complex numbers. What
is integral is their *symmetric* combination, and the reason is a small, completely
explicit argument with the $`q`$-expansion.

Write $`e_k(j(\tau))`$ for the $`k`$-th coefficient of $`\Phi_N(j(\tau),Y)`$ (up to
sign). Three inputs:

1. **Each conjugate has an algebraic-integer $`q`$-expansion.** The conjugates are
   the values $`j(\gamma\tau)`$ for coset representatives $`\gamma`$; in the nome they
   are $`j(\zeta_N^{\,ab} q^{a^2})`$ (§7). Since $`j(q) \in \mathbb{Z}((q))`$
   ([004 §4](004-the-j-invariant.md)) and $`\zeta_N^{\,ab}`$ is a root of unity,
   hence an algebraic integer, substitution $`q \mapsto \zeta q^e`$ returns
   $`q`$-coefficients in $`\mathbb{Z}[\zeta_N]`$: every conjugate has
   *algebraic-integer* $`q`$-coefficients. A symmetric polynomial in the conjugates,
   such as $`e_k`$, again has algebraic-integer $`q`$-coefficients, and it is fixed
   by the Galois action (which permutes the conjugates), so those coefficients lie
   in $`\mathbb{Q}`$. A rational algebraic integer is an integer, because
   $`\mathbb{Z}`$ is integrally closed in $`\mathbb{Q}`$. Hence every
   $`e_k(j(\tau))`$ has **ordinary integer** $`q`$-coefficients.
2. **Each $`e_k`$ is a polynomial in $`j`$.** It is symmetric in the conjugates, so
   it is invariant under the monodromy (the Galois action permutes the $`\psi(N)`$
   points of the fibre of $`X_0(N) \to X(1)`$); it is holomorphic on $`\mathbb{H}`$
   because each conjugate is; and its pole order at the cusp is finite and bounded
   by the classical bidegree of $`\Phi_N`$, namely $`\psi(N)`$. A weight-zero modular
   function that is holomorphic on $`\mathbb{H}`$ and has a pole of order $`\le
   \psi(N)`$ at the cusp is a polynomial in $`j`$ of degree $`\le \psi(N)`$ (this is
   the Hauptmodul property of §1). So
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

## 5. Splitting of the modular equation

Let $`p`$ be prime. Reading §2 with $`N = p`$ gives the factorization

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

**Nome form, and the version in note 010.** With $`X = j(\tau)`$ the roots are the
$`j`$-values of §2. Note 010 uses the same identity at the point $`\tau' = p\tau`$
(i.e. after $`\tau \mapsto p\tau`$, or $`q \mapsto q^p`$), which is why its $`X`$
variable is $`j(q^p) = j(p\tau)`$ and its roots are

$$j(p^2\tau) = j(q^{p^2}) \quad\text{and}\quad
  j(\tau + b/p) = j(\zeta_p^{\\,b}q), \qquad b = 0,\dots,p-1 .$$

Allowing an arbitrary level datum $`(e,u)`$ — the substitution
$`\tau \mapsto e\tau + \text{const}`$, i.e. $`q \mapsto u q^e`$ — gives the statement
in the exact shape quoted by note 010,

$$\Phi_p\bigl(j(u^p q^{pe}),\\, Y\bigr) \\;=\\;
  \bigl(Y - j(u^{p^2} q^{p^2 e})\bigr)
  \prod_{b=0}^{p-1}\bigl(Y - j(u\\,\zeta_p^{\\,b}\\,q^{e})\bigr),$$

which is Lean's `ModularCurve.PhiGen.splits_prime_at_slot`.

**Why this is the operative form.** The classical proof of the generation theorem
uses the Riemann surface $`X_0(N)`$: $`j`$ is a function of degree $`\psi(N)`$, and
the isogeny relation cuts the fibre down to one point. Without Riemann existence,
note 010 instead *lists all roots* and observes that exactly one can be common to
two polynomials. The splitting formula is what makes that list possible; the
"circuitousness" of the formal proof is the price of replacing the geometry by a
root count.

## 6. A hand calculation: $`\Phi_2`$

Let us verify that §§1–5 determine the first nontrivial modular polynomial. Take
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

By §4 each $`e_k`$ is a polynomial in $`X`$; the pole orders at the cusp are
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
$`-4, -8, -7`. Second, the leading coefficient of $`e_3`$ is $`-1`$, matching
$`r_1r_2r_3 \sim q^{-2}\cdot(-q^{-1})`$.

One caveat when reading §2's $`p+1`$ quotients as $`p+1`$ *curves*: they are $`p+1`$
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

The point of the computation is how little it needed: the quotient dictionary of §2
(so that the three roots are known), the $`q`$-expansion of $`j`$ from
[004](004-the-j-invariant.md), the pole bound of §4 (so that finitely many
coefficients suffice), and integrality (so the coefficients are integers to be read
off). This is the classical route, and it is a fair test that §§1–5 are enough.

## 7. Reading note 010: a short dictionary

The following phrases in [math/010](../math/010-function-field-generation.md) are
the classical words of §§1–6. The coset representative appearing in them is the
upper-triangular matrix

$$\gamma = \begin{pmatrix} a & b \\\\ 0 & d\end{pmatrix}, \qquad
  ad = M, \qquad 0 \le b \lt d,$$

and the two pieces of coset data are read off its entries $`a`$ and $`b`$.

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
- **"denominator-square $`a^2`$".** The coset representative $`\gamma`$ above acts by
  $`\tau \mapsto (a\tau+b)/d`$. With $`q_1 = e^{2\pi i\tau}`$,
  $`e^{2\pi i (a\tau+b)/d} = \zeta_M^{\,ab}\,q_1^{\,a/d}`$; over the common
  denominator $`M = ad`$ this is $`\zeta_M^{\,ab}\,q_1^{\,a^2/M}`$. So after the
  level-$`M`$ substitution $`q^M = q_1`$ the conjugate is
  $`j(\zeta_M^{\,ab}\,q^{a^2})`$: the exponent $`a^2`$ is the numerator $`a`$ of the
  fractional power $`a/d`$ written over the denominator $`M`$, and the twist
  $`\zeta_M^{\,ab}`$ is the numerator $`b`$. These are the "two pieces of coset data".
- **"right cosets of $`\Gamma_0(M)`$ in $`\mathrm{SL}_2(\mathbb{Z})`$".** The
  matrices $`\gamma`$ above with $`\gcd(a,b,d) = 1`$ are a set of right-coset
  representatives; their number is the index $`\psi(M)`$. Note 010's slot set
  $`\{(a,b) : a \mid M,\ b \lt M/a,\ \gcd(\gcd(a,b), M/a) = 1\}`$ is the same set, and
  the $`\psi(M)`$ roots $`j(\zeta_M^{\,ab}q^{a^2})`$ are the conjugates of
  $`j(q^M)`$.
- **"the affine self-map $`\tau \mapsto a^2\tau + ab`$".** This is the same coset
  data written on the level-$`M`$ nome: $`\zeta_M^{\,ab}q^{a^2}`$ is the nome of
  $`a^2\tau+ab`$ (for $`q = e^{2\pi i\tau/M}`$), which is the action of the
  Hecke/coset matrix in the $`q`$-world. For $`M = p`$ it degenerates to the two
  cases of §5: $`a = 1`$ gives the twists $`\zeta_p^{\,b}q`$, and $`a = p`$ gives
  $`q^{p^2}`$.
- **"Hauptmodul", "j separates points".** $`j`$ is a coordinate on
  $`X(1) = \mathbb{P}^1`$: two elliptic curves are isomorphic iff they have the same
  $`j`$ (§1). This is what lets a $`q`$-expansion computation be read back as a
  statement about curves.
- **"the extra isogeny relation cuts it down".** The fibre of $`X_0(N) \to X(1)`$
  over $`X`$ has $`\psi(N)`$ points $`j(E/\mathcal{C})`$, but only the one corresponding to
  $`\langle 1/N\rangle`$ satisfies the additional relation that $`E/\mathcal{C}`$ be
  $`N`$-isogenous to $`E`$ in the prescribed way. The splitting formula of §5 is the
  explicit form of that relation.

## 8. The Lean route as a map

The Lean does not *first* define $`\Phi_N`$ by the product over subgroups and then
check integrality. It goes the other way, and this order is worth knowing:

1. **Build the conjugate product.** The polynomial `phiProd` of
   [Def_ModularCurve_PhiGen.lean, lines 257–258](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularCurve_PhiGen.lean#L257-L258)
   is $`\prod_{b \lt p}\bigl(X - j(\zeta_p^{\,b}q)\bigr) \cdot \bigl(X - j(q^{p^2})\bigr)`$,
   written directly from the splitting list of §5.
2. **Descent.** Each coefficient of the product is shown to be a base-changed
   rational series in $`q^p`$: it is fixed by the twist $`q \mapsto \zeta_p q`$
   (so only exponents divisible by $`p`$ survive) and by the Galois action on
   $`\mathbb{Q}(\zeta_p)`$ (so it is rational). This is
   `PhiGen.exists_phiGenDescends`
   ([S file, lines 278–297](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_PhiGen_exists_phiGenDescends.lean#L278-L297)).
3. **Pole bound.** The product's pole order at the cusp bounds the degree, which
   together with holomorphy makes each coefficient a *polynomial* in $`j(q)`$
   rather than a rational function; and the residue-$`1`$ pole of $`j`$ converts
   integral $`q`$-coefficients into integral polynomial coefficients (§4). This is
   `exists_modularPolynomialData_coeff_eq`
   ([S file, lines 130–177](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_PhiGen_exists_modularPolynomialData_coeff_eq.lean#L130-L177)).
4. **Uniqueness.** Both the given datum and the constructed one are monic of degree
   $`p+1`$ and annihilate $`j(q^p)`$, and $`j(q^p)`$ has degree $`p+1`$ over
   $`\mathbb{Q}(j)`$; so they are equal. This identifies the product with
   $`\Phi_p`$ — the step that the phrase "the product's own coefficient family is a
   valid modular polynomial datum, hence is *the* datum" abbreviates.
5. **General $`N`$.** Integrality at level $`N`$ follows from the prime case by an
   induction over primes (`exists_monic_evalAtJ_jqN_eq_zero`), and irreducibility /
   degree $`\psi(N)`$ from the minimal polynomial once the degree is known
   (`exists_phiIrreducible_of_finrank_eq`). The slot description
   `minpoly_jqN_map_eq_prod_slots` is the same splitting list iterated over the
   divisor lattice, and is what note 010's §4 descent consumes.

## 9. Key point → declaration map

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

## 10. Links

FLT sources at the pinned sha `aa2d8b3`:

- [Def_ModularCurve_X0.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularCurve_X0.lean) — `jq`, `jqN`, `qExpand`, `dedekindPsi`, `ModularPolynomialData`
- [Def_ModularCurve_PhiGen.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularCurve_PhiGen.lean) — `qTwist`, `cosetSubst`, `conj`, `phiProd`, `EvalSymm`, `IntCoeffs`
- [Thm_ModularCurve_PhiGen_splits_prime_at_slot.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularCurve_PhiGen_splits_prime_at_slot.lean) — the splitting formula
- [Thm_ModularCurve_minpoly_jqN_map_eq_prod_slots.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularCurve_minpoly_jqN_map_eq_prod_slots.lean) — the conjugate list
- [P2M/Sol/S_ModularCurve_PhiGen_exists_phiGenDescends.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_PhiGen_exists_phiGenDescends.lean) — the descent of the conjugate product
- [Theorems/Thm_ModularCurve_exists_monic_evalAtJ_jqN_eq_zero.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularCurve_exists_monic_evalAtJ_jqN_eq_zero.lean) — integrality

Companion notes:

- [004 — The j-invariant](004-the-j-invariant.md) — the series `jq` and its integral $`q`$-expansion
- [math/010 §3](../math/010-function-field-generation.md#3-the-modular-polynomial-and-the-roots-of-the-modular-equation) — the section this note supplements
- [math/009 — The Hecke action on the Jacobian](../math/009-hecke-jacobian-commute.md) — where the modular polynomial is consumed

Background:

- F. Diamond and J. Shurman, *A First Course in Modular Forms*, GTM 228, Springer 2005, §5.2 — the modular equation and the function field of $`X_0(N)`$.
- S. Lang, *Elliptic Functions*, 2nd ed., GTM 112, Springer 1987, Ch. 5, §§2–3 — the modular equation and its roots.
- J. Silverman, *Advanced Topics in the Arithmetic of Elliptic Curves*, GTM 151, Springer 1994, Ch. I — complex tori, isogenies, and the $`j`$-invariant.
