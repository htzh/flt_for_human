# The rational function field and principal divisors

**Status: OUTLINE — the mathematical scope and section plan, for review before the
prose is written.**

On a curve, a nonzero function has as many zeros as poles, counted with degree:
$`\deg \mathrm{div}(f) = 0`$. This is the residue theorem in divisor form, and it is
a theorem about curves rather than a formal consequence of the definitions — for an
arbitrary field extension it can fail. Note
[008](008-divisors-and-pic0.md) §3 and §8 therefore states it as a hypothesis and
records that it is discharged for the modular function field; this note explains
*how*, in the form the proof actually uses.

The argument is a two-step reduction. The **base case** is the rational function
field $`K(t)`$, i.e. the projective line, where the places are completely explicit
— finite places from irreducible polynomials, one place at infinity — and the
divisor of a function can be written down. The **transfer** to a general function
field uses the norm: every function field $`F/K`$ of transcendence degree one is a
finite extension of some $`K(t)`$, the norm of a function is a rational function,
and the divisor of the norm is the pushforward of the divisor of the function; so
degree zero on $`F`$ follows from degree zero on $`K(t)`$.

It assumes [015](015-places-and-extensions.md) (extensions and the fibre-centre
dictionary) and [016](016-correspondences-and-exchange.md) §5 (the norm formula).

## 1. The places of $`K(t)`$

- The rational function field $`K(t)`$, as the function field of the projective
  line $`\mathbb{P}^1_K`$, and the two kinds of place.
- **Finite places**: irreducible polynomials $`p \in K[X]`$ correspond to the
  height-one primes of $`K[X]`$, hence to places of $`K(t)`$; the residue field is
  $`K[X]/(p)`$, and the degree of the place is $`\deg p`$. Each $`a \in K`$
  gives a degree-one place, the point $`t = a`$.
- **The place at infinity**: the valuation that measures the order of the pole at
  infinity, i.e. $`-\deg`$ on nonzero rational functions; its residue field is
  $`K`$, so it has degree one.
- **Ostrowski's theorem**: every place of $`K(t)`$ is one of these — a finite place
  at an irreducible polynomial, or the place at infinity. Equivalently, the finite
  places are exactly the places other than infinity, and there is exactly one
  place "above infinity". The proof is the classification of valuations on
  $`K(t)`$ trivial on $`K`$.
- The consequence used constantly: the set of places that are *not* finite consists
  of at most one point, and it is nonempty.

## 2. The order function on $`K(t)`$

- At a finite place $`\mathfrak{p}`$: $`\mathrm{ord}_\mathfrak{p}(f)`$ is the
  multiplicity of $`p`$ in the numerator minus in the denominator, in lowest terms.
  In particular $`\mathrm{ord}_\mathfrak{p}(p) = 1`$.
- At infinity: $`\mathrm{ord}_\infty(f) = -\deg f`$, the negative of the degree of
  the rational function; a polynomial of degree $`n`$ has a pole of order $`n`$ at
  infinity, and a constant has none.
- The compatibility that makes the two descriptions one theory: the order at a
  finite place is $`-\log`$ of the corresponding normalized valuation, and the
  order at infinity is $`-\log`$ of the valuation at infinity; both are normalized
  discrete valuations of $`K(t)`$ trivial on $`K`$.

## 3. Principal divisors on the projective line

- For an irreducible polynomial $`p`$ of degree $`n`$ the divisor of $`p`$, viewed
  as a function on $`\mathbb{P}^1`$, is
  $$\mathrm{div}(p) \;=\; [\mathfrak{p}] \;-\; n\,[\infty],$$
  a zero of order one at the corresponding point and a pole of order $`n`$ at
  infinity. Its degree is $`1 - n \cdot 1 = 0`$.
- For a general polynomial, split into irreducibles and add. For a general rational
  function $`f = g/h`$, use $`\mathrm{div}(f) = \mathrm{div}(g) -
  \mathrm{div}(h)`$; the degree is zero because both sides are.
- The **support is finite**: only the finitely many irreducible factors of the
  numerator or denominator can have nonzero order, together with at most infinity.
  This is the finiteness that makes the divisor a finite sum, and it is why the
  principal divisor is well defined.
- This is the residue theorem for $`\mathbb{P}^1`$: on the projective line every
  nonzero rational function has as many zeros as poles, and it is proved by unique
  factorization rather than by any geometric input.

## 4. Transfer to a general function field

- **Every function field is a finite extension of a rational one.** A function
  field $`F/K`$ (finitely generated, transcendence degree one) contains an element
  $`t`$ transcendental over $`K`$ with $`F`$ finite — and, in characteristic zero,
  separable — over $`K(t)`$. So the base case of §3 reaches every $`F`$ through a
  finite extension.
- **The norm transfers the residue theorem.** For $`f \in F`$, the norm
  $`N_{F/K(t)}(f)`$ lies in $`K(t)`$; the divisor of the norm is the pushforward of
  the divisor of $`f`$; pushforward preserves degree. Hence
  $`\deg \mathrm{div}(f) = \deg \mathrm{div}(N f) = 0`$ once the base case is known.
- **The local computation.** The norm formula of
  [016](016-correspondences-and-exchange.md) §5,
  $$\mathrm{ord}_v\big(N_{F/K(t)} f\big) \;=\;
    \sum_{w \mid v} e(w/v)\, f(w/v)\, \mathrm{ord}_w(f),$$
  is what identifies the divisor of the norm with the pushforward. It is proved
  from the fibre-centre picture of 015 §2–§3: the relative norm of the
  fibre-centre prime is the maximal ideal to the inertia degree, computed prime by
  prime over the factorisation of a principal ideal.
- **Finiteness in the extension** follows the same way: a nonzero function of
  $`F`$ is integral over the local ring at all but finitely many places, so its
  divisor has finite support. Combined with degree zero this is
  `HasPrincipalDivisors`.
- **The adjoin form**: if $`T`$ is a finite set of elements integral over
  $`K(t)`$, then $`K(t)(T)`$ again has the residue theorem — the form in which the
  statement is applied to a field presented by generators.
- A remark on the alternative route: the residue theorem can also be obtained
  without the norm, from the fundamental identity and the degree of a divisor
  directly; the note records why the norm route is the one used.

## 5. How the code says all this

- `HasPrincipalDivisors K F` is a class with one field, asserting that every
  nonzero $`f`$ has a finite-support divisor of degree zero; it is the hypothesis
  under which `Pic0` and the divisor calculus are the geometric objects of 008.
- The base case is a development over `RatFunc K`: the place at infinity is the
  valuation ring of `RatFunc.inftyValuation`; finite places are built from
  height-one primes of `K[X]`; Ostrowski's theorem is mathlib's classification of
  valuations on `K(t)`; the residue degree at a finite place is
  `finrank_quotient_span_eq_natDegree`.
- The transfer is `hasPrincipalDivisors_of_transcendental`: for $`K`$ of
  characteristic zero and $`F`$ finite over $`K(t)`$ with $`t`$ transcendental,
  build the divisor from the finite support and prove degree zero by pushing
  forward to $`K(t)`$ and applying the base case. The local input is the relative
  norm of the fibre-centre prime, `Ideal.relNorm` together with the factorisation
  of a principal ideal.
- Two encoding notes worth recording: the norm computation needs the field to be
  perfect (characteristic zero is enough, and mathlib needs the instance to fire);
  and the base-case degree computation is shipped twice in the project (one
  wrapper is marked `P2M.Dup`), so only one copy has to be read.

### Key point → declaration map

| Mathematics | Lean declaration |
|---|---|
| rational function field | `RatFunc K` |
| the place at infinity | `placeInfty`, `RatFunc.inftyValuation` |
| finite places from irreducible polynomials | `heightOneSpectrumOfIrreducible`, `finitePlace`, `Place.ofHeightOneSpectrum` |
| Ostrowski's classification | `RatFunc.valuation_isEquiv_infty_or_adic`, `eq_ofHeightOneSpectrum_or_eq_placeInfty'` |
| non-finite places form at most one point | `subsingleton_setOf_forall_ne_ofHeightOneSpectrum` |
| and at least one | `exists_forall_ne_ofHeightOneSpectrum`, `toValuationSubring_eq_of_forall_ne_ofHeightOneSpectrum` |
| residue degree at a finite place | `deg_ofHeightOneSpectrum` |
| residue degree at infinity | `deg_eq_one_of_forall_ne_ofHeightOneSpectrum` |
| order at a finite place | `ord_ofHeightOneSpectrum_of_span`, `ord_ofHeightOneSpectrum_eq_neg_log` |
| order at infinity | `ord_eq_neg_intDegree_of_forall_ne_ofHeightOneSpectrum` |
| divisor of a polynomial | `degree_eq_zero_of_forall_eq_ord_algebraMap` |
| divisor of a rational function | `degree_eq_zero_of_forall_eq_ord` |
| finite support | `finite_setOf_ord_ne_zero` |
| relative norm of the fibre-centre prime | `relNorm_fiberCenter` |
| norm of a principal ideal | `relNorm_span_singleton`, `count_normalizedFactors_span_singleton` |
| the local norm formula | `ord_norm_eq_sum_fiberOver` |
| degree zero in a finite extension | `hasPrincipalDivisors_of_finiteDimensional_ratFunc` |
| the transcendental form | `hasPrincipalDivisors_of_transcendental` |
| the adjoin form | `hasPrincipalDivisors_adjoin_of_transcendental` |

## 6. Links

FLT sources at the pinned sha `aa2d8b3`:

- [Def_AlgebraicCurve_RatFuncPlaces.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_RatFuncPlaces.lean) — the finite places, residue degrees, and the classification
- [Def_AlgebraicCurve_RatFuncPlaceInfty.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_RatFuncPlaceInfty.lean) — `placeInfty`
- [Def_AlgebraicCurve_DivisorClassGroup.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_DivisorClassGroup.lean) — `HasPrincipalDivisors`, `Place.ofHeightOneSpectrum`
- [`S_AlgebraicCurve_hasPrincipalDivisors_of_transcendental.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_hasPrincipalDivisors_of_transcendental.lean) — the norm transfer
- [`S_AlgebraicCurve_hasPrincipalDivisors_adjoin_of_transcendental.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_hasPrincipalDivisors_adjoin_of_transcendental.lean) — the adjoin form

Mathlib at tag `v4.33.0`:

- [FieldTheory/RatFunc/Valuation.lean](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/FieldTheory/RatFunc/Valuation.lean) — `RatFunc.inftyValuation`
- [NumberTheory/RatFunc/Ostrowski.lean](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/NumberTheory/RatFunc/Ostrowski.lean) — the classification of valuations on `K(t)`
- [RingTheory/Ideal/Norm/RelNorm.lean](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/RingTheory/Ideal/Norm/RelNorm.lean) — `Ideal.relNorm`
- [RingTheory/AdjoinRoot.lean](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/RingTheory/AdjoinRoot.lean) — `finrank_quotient_span_eq_natDegree`

Companion notes:

- [008 — Divisors, linear equivalence, and Pic⁰](008-divisors-and-pic0.md) §3, §8 — the residue theorem as a hypothesis
- [015 — Places and their extensions](015-places-and-extensions.md) — the fibre-centre dictionary
- [016 — Correspondences and the exchange lemma](016-correspondences-and-exchange.md) §5 — the norm formula
- [009 — Differentials, residues, and Riemann–Roch](009-differentials-residues-riemann-roch.md) — the residue theorem in its other forms
- [math/009](../math/009-hecke-jacobian-commute.md) §5 — where principal divisors enter the Hecke argument
