# Elliptic nets, division polynomials, and the invariant of a sequence

Twenty-fifth of the `math/` notes. [005](005-card-torsion-p-squared.md) proved
$`\#E[n](K) = n^2`$ over an algebraically closed field by counting the fibres of
multiplication by $`n`$. The count rests on the classical formula for the
coordinates of $`[n]P`$,

$$[n]P = \left(\frac{\varphi_n(P)}{\psi_n(P)^2},\\ \frac{\omega_n(P)}{\psi_n(P)^3}\right),$$

and that formula is the subject of this note. In the project it is assembled from
three layers: mathlib's division polynomials and their recurrence, the
elliptic-net (`EDS`) core, and the $`\omega`$ construction that mathlib dropped
after v4.30. This note is about the *mathematics* of those layers, and about
where each sits relative to the textbook treatment (Silverman, Ward, Stange).
The Lean encoding is compressed into §7.

The short version, before the machinery:

- The $`n`$-division polynomials $`\psi_n`$ are the canonical normalised
  **elliptic divisibility sequence** (EDS). Every identity about $`\psi_n`$ — the
  addition law, the divisibility, the Tate/Weil pairing formulas — is an instance
  of one relation, the *elliptic-net* relation.
- An EDS is automatically a **divisibility** sequence: $`\psi_n \mid \psi_m`$
  whenever $`n \mid m`$. The quotient $`\psi_m/\psi_n`$ is packaged without
  division as a second sequence, the **complement**. The $`2`$-complement is what
  replaces $`\psi_{2n}/\psi_n`$ in the coordinate formula.
- The $`y`$-coordinate numerator $`\omega_n`$ is where the textbook formula
  divides by $`\psi_n`$ and by $`2`$ (equivalently, in short Weierstrass form, by
  $`y`$). Both divisions are eliminated by the **invariant** of the sequence: a
  quantity whose ratio is independent of the running index $`n`$, and which for
  the division-polynomial EDS is the polynomial $`6X^2+b_2X+b_4`$. That is the
  reason the construction works in every characteristic.

## 1. The classical multiplication formula

Let $`E`$ be an elliptic curve over a field $`K`$, in general Weierstrass form

$$E: y^2 + a_1xy + a_3y = x^3 + a_2x^2 + a_4x + a_6,$$

with the usual

$$b_2 = a_1^2+4a_2,\quad b_4 = 2a_4+a_1a_3,\quad b_6 = a_3^2+4a_6,\quad b_8 = a_1^2a_6+4a_2a_6-a_1a_3a_4+a_2a_3^2-a_4^2.$$

The **division polynomials** are the sequence in
$`\mathbb{Z}[a_1,\dots,a_6][X,Y]`$ with

$$\psi_1 = 1,\qquad \psi_2 = 2Y+a_1X+a_3,\qquad \psi_3 = 3X^4+b_2X^3+3b_4X^2+3b_6X+b_8,$$

$$\psi_4 = \psi_2\\,\bigl(2X^6+b_2X^5+5b_4X^4+10b_6X^3+10b_8X^2+(b_2b_8-b_4b_6)X+b_4b_8-b_6^2\bigr),$$

and, for all $`n`$, Ward's two recurrences

$$\psi_{2n+1} = \psi_{n+2}\\,\psi_n^3 - \psi_{n-1}\\,\psi_{n+1}^3,$$

$$\psi_{2n}\\,\psi_2 = \psi_{n-1}^2\\,\psi_n\\,\psi_{n+2} - \psi_{n-2}\\,\psi_n\\,\psi_{n+1}^2.$$

The $`x`$- and $`y`$-numerators are then

$$\varphi_n = X\psi_n^2 - \psi_{n+1}\psi_{n-1},\qquad
\omega_n = \frac{\psi_{2n}/\psi_n - \psi_n\\,(a_1\varphi_n + a_3\psi_n^2)}{2},$$

and the classical theorem is that for a point $`P = (x,y)`$ with
$`\psi_n(P) \neq 0`$,

$$[n]P = \left(\frac{\varphi_n(P)}{\psi_n(P)^2},\\ \frac{\omega_n(P)}{\psi_n(P)^3}\right).$$

This is Silverman, *AEC*, Exercise 3.7 (and III.6); the same formulas are
collected in [Stange's formulary](https://math.colorado.edu/~kstange/papers/edsformulary.pdf)
§4.1. Two features of the formula are worth separating, because the whole design
of the formalization follows from them.

**The $`x`$-coordinate is a one-variable statement.** On $`E`$ one has
$`\psi_n^2 \equiv \Psi\mathrm{Sq}_n`$ and $`\varphi_n \equiv \Phi_n`$ for
univariate polynomials $`\Psi\mathrm{Sq}_n, \Phi_n \in R[X]`$; that is the form
the fibre count of note 005 actually uses, and it is why the curve layer can be
built from $`R[X]`$ rather than from the coordinate ring.

**The $`y`$-coordinate divides by $`\psi_n`$ and by $`2`$.** Neither division is
available over a general commutative ring, and the second is unavailable in
characteristic $`2`$. In short Weierstrass form the same numerator also has the
shape

$$4y\\,\omega_n = \psi_{n+2}\\,\psi_{n-1}^2 - \psi_{n-2}\\,\psi_{n+1}^2 \quad \text{on } E,$$

which trades the division by $`2`$ for a division by $`y`$ — no better, and worse
at a $`2`$-torsion point. The rest of this note is about removing both divisions.
The tool is the theory of elliptic sequences.

## 2. The recurrence is an elliptic net

The recurrences of §1 are not two unrelated identities: they are the rank-one
case of a single relation. Following Ward and Stange, call a function
$`W : \mathbb{Z} \to R`$ an **elliptic net** if for all $`p,q,r,s`$ the
*elliptic relator*

$$ER(p,q,r,s) = W(p{+}q{+}s)\\,W(p{-}q)\\,W(r{+}s)\\,W(r)
 - W(p{+}r{+}s)\\,W(p{-}r)\\,W(q{+}s)\\,W(q)
 + W(q{+}r{+}s)\\,W(q{-}r)\\,W(p{+}s)\\,W(p)$$

vanishes. Equivalently, with the **elliptic atoms**

$$W_a(p,q) = W\\!\left(\frac{p+q}{2}\right)W\\!\left(\frac{p-q}{2}\right),$$

the *atom relator*

$$ER_a(a,b,c,d) = W_a(a,b)\\,W_a(c,d) - W_a(a,c)\\,W_a(b,d) + W_a(a,d)\\,W_a(b,c)$$

vanishes. The $`s = 0`$ slice is Ward's **elliptic sequence** relation, and with
$`r = 1`$ it becomes the familiar

$$W(n+m)\\,W(n-m)\\,W(1)^2 = W(n+1)\\,W(n-1)\\,W(m)^2 - W(m+1)\\,W(m-1)\\,W(n)^2.$$

An EDS is an elliptic net that is also a **divisibility** sequence (below). The
canonical normalised example is fixed by five initial values

$$W_0 = 0,\quad W_1 = 1,\quad W_2 = b,\quad W_3 = c,\quad W_4 = db,$$

together with

$$W_{2n+1} = W_{n+2}\\,W_n^3 - W_{n-1}\\,W_{n+1}^3,$$

$$W_{2n}\\,W_2 = W_{n-1}^2\\,W_n\\,W_{n+2} - W_{n-2}\\,W_n\\,W_{n+1}^2.$$

The division polynomials are exactly this example:

$$\psi_n = \mathrm{normEDS}(\psi_2,\\ \Psi_3,\\ \mathrm{pre}\Psi_4)_n .$$

Concretely, $`b = \psi_2`$, $`c = \Psi_3`$ and $`d = \mathrm{pre}\Psi_4`$ — the
last because $`\psi_4 = \psi_2\cdot\mathrm{pre}\Psi_4`$. This is not an analogy:
$`\mathrm{normEDS}`$ *is* the definition of $`\psi`$ in mathlib.

Why use a net rather than "a sequence with recurrences"? Three reasons, all
mathematical.

- **The relation is division-free and closed under shifting.** The recurrences of
  §1 mix $`n`$, $`2n`$, $`2n+1`$; the net relation is a single homogeneous cubic
  identity in four indices. Every addition formula (for $`x`$-coordinates, for
  the pairing, for the divisibility) is a specialisation of it.
- **It is symmetric and $`\mathbb{Z}`$-indexed.** Negatives and the oddness
  $`W(-n) = -W(n)`$ come for free, and the parity bookkeeping that makes the
  recurrences awkward disappears into the atoms.
- **It is the right generality.** A net of rank $`\gt 1`$ (several points $`P,Q`$)
  satisfies the *same* relation; the rank-one theory is not a special
  construction. Stange's theory is built on this, and the Tate/Weil pairing
  identities are net identities.

The formalization mirrors this: it proves the net relation once, for the
*universal* EDS over $`\mathbb{Z}[B,C,D]`$, and then transfers it to arbitrary
$`b,c,d`$ by the evaluation map. The universal ring is where $`b`$ and $`c`$ are
non-zero-divisors, so the cancellations that make the divisibility proof work are
legitimate; the general statement is a formal image of it.

## 3. Complement sequences, and divisibility made polynomial

The EDS property is that $`W(k)`$ divides $`W(nk)`$ — for the division
polynomials, $`\psi_n \mid \psi_m`$ whenever $`n \mid m`$. Ward's theorem states
this for integer sequences; over a general commutative ring the content is
*better*: the recurrence exhibits a witness. Define the **complement** sequence
$`D(k,\cdot)`$ by

$$W(k)\\,D(k,n) = W(nk).$$

This is a polynomial recurrence in $`k`$ and $`n`$, not a quotient, and it is
what lets one write $`W(nk)/W(k)`$ anywhere a rational expression would appear.
Its two relevant specialisations are:

- the **$`2`$-complement**, written $`\psi c_n`$ for the division polynomials:

$$\psi_n\\,\psi c_n = \psi_{2n},\qquad
\psi c_n = \mathrm{complEDS}_2(\psi_2,\Psi_3,\mathrm{pre}\Psi_4)_n,$$

  with the explicit shape

$$\psi c_n = \frac{\psi_{n+2}\\,\psi_{n-1}^2 - \psi_{n-2}\\,\psi_{n+1}^2}{\psi_2};$$

- the **general complement** $`D(k,n)`$ for $`k = 3, 6`$, used to clear the
  factors $`W(3)`$, $`W(6)`$ out of the invariant denominator in §4.

The first of these is exactly the numerator that appears in the classical
$`\omega`$ formula of §1: in short Weierstrass form $`4y\omega_n`$ *is* that
numerator, so $`\omega_n = \psi c_n/2`$. Thus

$$\psi c_n = 2\\,\omega_n \quad \text{(short form, characteristic } \neq 2\text{)},$$

and the classical obstruction is visible: the $`y`$-numerator is "half the
2-complement". Over a general ring one cannot take half, so the correct statement
is the *characteristic-free* one of §5, in which the factor $`2`$ is never
removed.

There is a second, subtler use of the complement. The reduced invariant of §4,
$`\mathrm{redInvarDenom}`$, is built by peeling the factors $`W(6)`$, $`W(3)`$,
$`W(2)`$ out of the monomial $`W(m+1)\,W(m)\,W(m-1)`$; which factor divides
which term depends on $`m \bmod 6`$, and each peel is a general complement
$`D(k,\cdot)`$. That mod-$`6`$ case split is exactly the arithmetic of the
divisibility $`W(k) \mid W(n)`$, and it is the only reason the general
complement is needed alongside the $`2`$-complement.

## 4. The invariant of an elliptic sequence

For a sequence $`W`$ and integers $`s,n`$ define

$$\mathrm{invarNum}(s,n) = \bigl(W(n+2s)\\,W(n-s)^2 + W(n+s)^2\\,W(n-2s)\bigr)W(s)^2 + W(n)^3\\,W(2s)^2,$$

$$\mathrm{invarDenom}(s,n) = W(n+s)\\,W(n)\\,W(n-s).$$

The name is justified by the following consequence of the net relation:

$$\mathrm{invarNum}(s,m)\\,\mathrm{invarDenom}(s,n)
 = \mathrm{invarNum}(s,n)\\,\mathrm{invarDenom}(s,m).$$

Equivalently, the ratio

$$\frac{\mathrm{invarNum}(s,n)}{\mathrm{invarDenom}(s,n)}$$

is **independent of $`n`$**. This is the *invariant* of the elliptic sequence: a
quantity attached to the sequence and to $`s`$, not to the running index. (It is
the same phenomenon as the first integral of the Somos-4 recurrence: the
nonlinear recurrence has an algebraic conserved quantity.) The ratio is a
genuine conservation law, and it is what lets one *define* the invariant
without dividing: the pair $`(\mathrm{invarNum}, \mathrm{invarDenom})`$ is a
projective object, and its reduction to a polynomial is a computation rather
than a quotient.

For the normalised EDS the value at $`s = 1`$ is closed:

$$\mathrm{invarNum}(1,m)\\,c = \mathrm{invarDenom}(1,m)\\,(d+b^4),$$

so the ratio is $`(d + b^4)/c`$. This is the invariant of the sequence in terms of
its three parameters $`b,c,d`$. For the division polynomials
$`(b,c,d) = (\psi_2, \Psi_3, \mathrm{pre}\Psi_4)`$, and the key polynomial
identity of the curve layer is

$$\mathrm{pre}\Psi_4 + \Psi_2\mathrm{Sq}^2 = \mathrm{invar}\cdot\Psi_3,
\qquad \mathrm{invar} = 6X^2 + b_2X + b_4 .$$

Since $`\Psi_2\mathrm{Sq} \equiv \psi_2^2`$ and $`\mathrm{pre}\Psi_4 = d`$, this
says $`d + b^4 \equiv \mathrm{invar}\cdot c`$ on the curve, so the invariant of
the division-polynomial EDS is the polynomial

$$\mathrm{invar} = 6X^2 + b_2X + b_4
 = \psi_2\\,(2\lambda + a_1),$$

where $`\lambda`$ is the tangent slope at $`(X,Y)`$,
$`\lambda = (3X^2+2a_2X+a_4-a_1Y)/\psi_2`$. So the invariant is determined by
the $`x`$-coordinate alone; it is a function of the point, not a constant of the
curve. In short Weierstrass form it is $`4\lambda y = 2(3x^2+A)`$ for
$`E : y^2 = x^3+Ax+B`$.

Two remarks.

- The identity $`\mathrm{pre}\Psi_4 + \Psi_2\mathrm{Sq}^2 = \mathrm{invar}\cdot\Psi_3`$
  is a polynomial identity in $`R[X]`$, valid in every characteristic. It is
  what makes the invariant available to the curve layer at all; without it
  $`d + b^4`$ would be a rational function rather than the polynomial
  $`\mathrm{invar}\cdot c`$.
- The invariant that actually appears in the $`\omega`$ construction is the
  **reduced** one, $`\mathrm{redInvarNum}`$ and $`\mathrm{redInvarDenom}`$,
  related to the naive pair by

$$\mathrm{invarNum}(1,m) = \mathrm{redInvarNum}(m)\cdot b,\qquad
\mathrm{invarDenom}(1,m) = \mathrm{redInvarDenom}(m)\cdot b\cdot c,$$

  and satisfying $`\mathrm{redInvarNum}(m) = \mathrm{redInvarDenom}(m)\cdot(d+b^4)`$.
  The reduced denominator is the product of complement values and $`W(m \pm 1)`$
  selected by $`m \bmod 6`$; the case split is exactly the bookkeeping of §3, and
  it is what turns the invariant into a polynomial expression in
  $`\mathrm{normEDS}`$ and $`\mathrm{complEDS}`$ with no $`X,Y`$ in it.

## 5. The $`y`$-coordinate, characteristic-free

With the two divisions of §1 in hand, the construction of the $`y`$-numerator is
forced. The defining property is stated with the factor $`2`$ left in place:

$$2\\,\omega e_n + a_1\\,\varphi_n\\,\psi_n + a_3\\,\psi_n^3 = \psi c_n,$$

or equivalently

$$2\\,\omega e_n = \psi c_n - a_1\\,\varphi_n\\,\psi_n - a_3\\,\psi_n^3.$$

Every ingredient on the right is a polynomial over $`R`$: $`\psi c_n`$ is the
$`2`$-complement of §3, $`\varphi_n`$ is the $`x`$-numerator, and the $`\psi_n`$
are the division polynomials. The left side is *not* solved for $`\omega e_n`$ by
dividing by $`2`$. Instead $`\omega e_n`$ is *defined* by an explicit polynomial
formula built from the reduced invariant and the auxiliary complement sequence,
and the display above is the *theorem* that the formula has the required
property. Over a ring in which $`2`$ is invertible this pins down the classical
$`\omega_n`$ uniquely; in characteristic $`2`$ the classical formula does not
exist and the explicit formula is the canonical replacement.

The same pattern gives every other ingredient of the coordinate formula:

- $`\psi_n`$: the normalised EDS, an integer polynomial recurrence;
- $`\varphi_n = X\psi_n^2 - \psi_{n+1}\psi_{n-1}`$: no division;
- $`\psi c_n = \psi_{2n}/\psi_n`$: a polynomial, by divisibility;
- $`\omega e_n`$: a polynomial satisfying the display, by the invariant.

Nothing divides by $`2`$, by $`\psi_n`$, or by $`y`$; so the multiplication
formula is available over any commutative ring, hence in every characteristic.
This is the precise sense in which "it can work in any characteristic": the
theory is *stated* over a general commutative ring, and the only classical step
that would have obstructed that — the halving in $`\omega_n`$ — is replaced by a
projective/invariant characterisation.

## 6. How this sits in the classical picture

The traditional treatment and the formalized one are the same mathematics with
different choices of what to take as primitive.

- **Textbooks** (Silverman, *AEC*, III.6 and Exercise 3.7) give $`\psi_n`$ by the
  recurrences of §1 and $`\omega_n`$ by the halved formula, usually over a field
  with $`\mathrm{char} \neq 2`$ and frequently in short Weierstrass form. The
  formulas are division-by-$`2`$ statements, and the $`y`$-coordinate is a
  rational function even when the $`x`$-coordinate is polynomial.
- **Ward** (*Memoir on elliptic divisibility sequences*, 1948) isolates the
  sequence itself: integer sequences with the nonlinear recurrence, the
  divisibility theorem, and the elliptic curve attached to a nonsingular EDS.
  The invariant of §4 is Ward's; for the division-polynomial EDS it is the
  polynomial $`6X^2+b_2X+b_4`$ above.
- **Stange** (*Elliptic nets and elliptic curves*, 2011, and the
  [formulary](https://math.colorado.edu/~kstange/papers/edsformulary.pdf))
  recasts EDS as nets, where the recurrence is one relation with no parity
  distinction and the rank is not fixed. This is the version mathlib implements,
  and it is the reason the formal proof can quote one relation instead of two
  recurrences.
- **The formalized curve layer** adds what neither textbook nor memoir needs but
  the FLT application does: all of $`\psi`$, $`\varphi`$, $`\psi c`$, $`\omega e`$
  as polynomials over an arbitrary commutative ring, with the multiplication
  formula valid in characteristic $`2`$ and $`3`$. The FLT arithmetic runs over
  finite fields and the Frey curve's coefficients are integral, so no
  characteristic may be excluded. The invariant is the device that buys this:
  it is the classical invariant of the EDS, used as a division-free *definition*
  of the $`y`$-numerator rather than as a conservation law to be proved after the
  fact.

One consequence is worth stating because it is easy to misread: the theory here
is *not* a characteristic-$`2`$ specialisation. Over $`\mathbb{Z}`$ the identities
of §4 and §5 hold as polynomial identities, and every claim about a specific
field or characteristic is obtained by base change. That is why the universal
EDS over $`\mathbb{Z}[B,C,D]`$ appears in §2: proving over the universal ring is
strictly stronger, and the general case is an evaluation.

## 7. The Lean encoding

Math first, engineering second; this section is the second.

**What mathlib provides (v4.34.0).** `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean`
has the net/EDS vocabulary (`IsEllipticNet`, `IsEllipticSequence`,
`IsEllipticDvdSequence`), the relators (`atom`, `atomRel`, `rel`), the
normalised sequence (`preNormEDS`, `normEDS`), and the two complements
(`complEDS₂`, `complEDS`). `DivisionPolynomial/Basic.lean` has `ψ`, `Ψ`, `Φ`,
`φ`, `ψ₂`, `Ψ₂Sq`, `Ψ₃`, `preΨ₄` and their recurrences. The file's own module
docs list the missing bivariate $`\omega`$ polynomials as a `TODO`, and the
general complement multiplication is present only for $`n = 2`$
(`normEDS_mul_complEDS₂`).

**What the port adds.** `FLTForHuman/Elliptic/` reconstructs exactly the gap:

| file | content |
|---|---|
| `DivisionPolynomial.lean` | `invar`, `ψc`, `invarNum`/`invarDenom`, `complEDSAux`, `redInvarNum`, the transfer lemmas |
| `EDS.lean` | the universal EDS over `ℤ[B,C,D]`, `normEDS_eq_aeval` |
| `EllSequence.lean` | `atom`/`atomRel`/`rel` re-exported at FLT's names, the relator transfer machinery, and `normEDS_isEllipticSequence` |
| `Complement.lean` | the general `normEDS m · complEDS m n = normEDS (n*m)` |
| `RedInvar.lean` | `redInvarDenom`, `invarDenom_eq_redInvarDenom_mul` |
| `Net.lean` | `net_normEDS`, `invar_normEDS`, `invar₂_normEDS`, `redInvar_normEDS` |
| `Omega.lean` | `ωe`, `ωe_spec`, `two_mul_ωe` |

The FLT-to-mathlib map is recorded in
[`lean/logs/card-torsion-port.md`](../lean/logs/card-torsion-port.md) §3. Two
correspondences make the port a reuse rather than a re-derivation: FLT's
`EllSequence.addMulSub` / `rel₄` / `net` are *definitionally* mathlib's `atom` /
`atomRel` / `rel`, and FLT's `compl₂EDS` is *definitionally* mathlib's
`complEDS₂`, so `ψc` is a one-line alias rather than a new sequence. The genuinely
new mathematics is the invariant layer and the characteristic-free $`\omega`$;
its statements are transcribed from the pin
([`Def_WeierstrassCurve_EDSEngine.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_WeierstrassCurve_EDSEngine.lean))
and checked against it by `lean/spec/check_flt_statements.py`.

The proof technique to know, because it recurs throughout the layer: statements
about an arbitrary coefficient ring are proved first over the universal EDS
$`\mathbb{Z}[B,C,D]`$, where $`B`$ and $`C`$ are non-zero-divisors and
cancellation is legal, and are then transported along `aeval`. That is how
`invar₂_normEDS` (§4), `redInvar_normEDS`, and the general multiplicativity of
the complement (§3) are all obtained.

## Links

Pinned pin sources (`aa2d8b3`):

- [`Definitions/Def_WeierstrassCurve_EDSEngine.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_WeierstrassCurve_EDSEngine.lean) — `invarNum` (83), `invarDenom` (87), `invar_of_net` (89), `compl₂EDSAux` (566), `compl₂EDS` (580), `redInvarNum` (844), `redInvarDenom` (856), `net_normEDS` (949), `invar` (1196), `preΨ₄_add_Ψ₂Sq_sq` (1208), `ωe` (1220), `ωe_spec` (1226)
- [`Theorems/Thm_WeierstrassCurve_card_torsion_of_isAlgClosed.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_WeierstrassCurve_card_torsion_of_isAlgClosed.lean) — the consumer ([math/005](005-card-torsion-p-squared.md))
- [`P2M/Sol/S_WeierstrassCurve_card_torsion_of_isAlgClosed.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_WeierstrassCurve_card_torsion_of_isAlgClosed.lean) — the fibre count

mathlib (tag `v4.34.0`):

- [`NumberTheory/EllipticDivisibilitySequence.lean`](https://github.com/leanprover-community/mathlib4/blob/v4.34.0/Mathlib/NumberTheory/EllipticDivisibilitySequence.lean) — `atom` (108), `atomRel` (157), `rel` (266), `preNormEDS` (432), `complEDS₂` (502), `normEDS` (545), `normEDS_mul_complEDS₂` (577), `complEDS` (691)
- [`AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean`](https://github.com/leanprover-community/mathlib4/blob/v4.34.0/Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean) — `ψ₂` (113), `Ψ₂Sq` (117), `Ψ₃` (142), `preΨ₄` (147), `preΨ` (194), `Ψ` (290), `ψ` (401); the missing `ωₙ` is a `TODO` at line 71

Companion notes and records:

- [math/005 — the cardinality of $`E[n]`$](005-card-torsion-p-squared.md) — the consumer of the multiplication formula
- [`lean/logs/card-torsion-port.md`](../lean/logs/card-torsion-port.md) — the port trace and the FLT-to-mathlib table
- [`lean/porting-playbook.md`](../lean/porting-playbook.md) — the reuse/whole-node policy that produced this layer

Background:

- J. Silverman, *The Arithmetic of Elliptic Curves*, GTM 106, 2nd ed., Springer 2009, III.6 and Exercise 3.7.
- M. Ward, *Memoir on elliptic divisibility sequences*, Amer. J. Math. **70** (1948), 31–74.
- K. Stange, *Elliptic nets and elliptic curves*, Algebra Number Theory **5** (2011), 197–229.
- K. Stange, [*Formulary for elliptic divisibility sequences and elliptic nets*](https://math.colorado.edu/~kstange/papers/edsformulary.pdf) (2012).
